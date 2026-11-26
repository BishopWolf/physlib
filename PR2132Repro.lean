import PhyslibAlpha.Relativity.General.InitialData.Basic
import PhyslibAlpha.Relativity.General.Modified.FRGravity
import PhyslibAlpha.Relativity.General.Modified.Teleparallel.FLRWTorsion
import PhyslibAlpha.Relativity.Metrics.Pipeline
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Four component tests for Physlib PR 2132, commit 626ada74afc29e16f85da0924c393e00af3ff5cd.
Run as an additional file in that checkout after building the imported modules. -/

open GeneralRelativity GeneralRelativity.Pipeline
open GeneralRelativity.Modified.EinsteinCartan
open GeneralRelativity.Modified.Teleparallel
open GeneralRelativity.Modified.FRGravity
open scoped BigOperators

namespace PR2132Repro
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000

/-! The cylindrical coordinate metric is diag(1,r²,1). Take the point (1,1,1). -/

private def cyl (x : Fin 3 → ℝ) : Tensor2 3 :=
  Matrix.diagonal fun i => if i = 1 then (x 0)^2 else 1

private def unit3 : MetricTensor 3 where
  g := 1
  ginv := 1
  symm := Matrix.isSymm_one
  inv_left := one_mul 1
  inv_right := one_mul 1

private def radialK : Tensor2 3 :=
  Matrix.diagonal fun i => if i = 0 then 1 else 0

private def data3 : InitialData where
  h := unit3
  R3 := RiemannTensor.flat 3
  K := radialK
  Ksymm := Matrix.isSymm_diagonal _

private def dg (u : Fin 3) : Tensor2 3 :=
  fun i j => coordDeriv u (fun x => cyl x i j) (fun _ => 1)

private def rawK (u : Fin 3) : Tensor2 3 :=
  fun i j => coordDeriv u (fun _ => radialK i j) (fun _ => 1)

private lemma cyl_point : cyl (fun _ => 1) = unit3.g := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [cyl, unit3, Matrix.diagonal_apply, Matrix.one_apply]

private lemma dg_entries (u i j : Fin 3) :
    dg u i j = if u = 0 ∧ i = 1 ∧ j = 1 then 2 else 0 := by
  fin_cases u <;> fin_cases i <;> fin_cases j <;>
    norm_num [dg, cyl, coordDeriv, Matrix.diagonal_apply, Function.update, deriv_pow_field]

private lemma raw_zero : rawK = 0 := by
  funext u i j
  simp [rawK, coordDeriv]

private def gamma3 := leviCivitaOfDeriv unit3.ginv dg

private lemma gamma_entries (l u i : Fin 3) :
    gamma3 l u i =
      if l = 0 ∧ u = 1 ∧ i = 1 then -1
      else if l = 1 ∧ ((u = 0 ∧ i = 1) ∨ (u = 1 ∧ i = 0)) then 1 else 0 := by
  fin_cases l <;> fin_cases u <;> fin_cases i <;>
    norm_num [gamma3, leviCivitaOfDeriv, unit3, Fin.sum_univ_three, Matrix.one_apply, dg_entries]

/-- Coordinate formula for ∇ᵤKᵢⱼ, using the PR's Levi-Civita connection. -/
private def covK (u : Fin 3) : Tensor2 3 := fun i j =>
  rawK u i j - (∑ l, gamma3 l u i * radialK l j) - ∑ l, gamma3 l u j * radialK i l

/-- In the cylindrical example the predicate accepts raw derivatives. The radial covariant
momentum at r = 1 is one. -/
lemma adm_reproduction :
    cyl (fun _ => 1) = data3.h.g ∧ data3.IsVacuumData rawK ∧
    data3.momentumConstraint rawK 0 = 0 ∧ data3.momentumConstraint covK 0 = 1 := by
  refine ⟨cyl_point, ⟨?_, ?_⟩, ?_, ?_⟩
  · norm_num [InitialData.hamiltonianConstraint, data3, ricciScalar, ricci_flat,
      metricTrace, unit3, radialK, Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.one_apply]
  · intro i
    simp [InitialData.momentumConstraint, raw_zero]
  · simp [InitialData.momentumConstraint, raw_zero]
  · norm_num [InitialData.momentumConstraint, data3, covK, raw_zero, gamma_entries,
      unit3, radialK, Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.one_apply]

/-! FLRW with a(t) = exp t, evaluated at the spacetime origin. -/

private def sign4 (i : Fin 4) : ℝ := if i = 0 then -1 else 1
private def eta4 : MetricTensor 4 where
  g := Matrix.diagonal sign4
  ginv := Matrix.diagonal sign4
  symm := Matrix.isSymm_diagonal _
  inv_left := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply, sign4, Fin.sum_univ_four]
  inv_right := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply, sign4, Fin.sum_univ_four]

private def dFLRW (u : Fin 4) : Tensor2 4 := fun A j =>
  coordDeriv u (fun y => flrwTetrad Real.exp y A j) 0

private def T4 (k i j : Fin 4) : ℝ :=
  (if i = 0 ∧ k = j ∧ j ≠ 0 then 1 else 0) - (if j = 0 ∧ k = i ∧ i ≠ 0 then 1 else 0)

private lemma flrwInv_one : flrwTetradInv Real.exp 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [flrwTetradInv, Matrix.diagonal_apply, Matrix.one_apply]

private lemma dFLRW_entries (u A j : Fin 4) :
    dFLRW u A j = if u = 0 ∧ A = j ∧ j ≠ 0 then 1 else 0 := by
  fin_cases u <;> fin_cases A <;> fin_cases j <;>
    norm_num [dFLRW, coordDeriv, flrwTetrad, Matrix.diagonal_apply, Function.update, Real.deriv_exp]

private lemma actual_torsion : weitzenbockTorsion (flrwTetradInv Real.exp 0) dFLRW = T4 := by
  rw [flrwInv_one]
  funext k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [weitzenbockTorsion, torsion, weitzenbockConn, Matrix.one_apply,
      Fin.sum_univ_four, dFLRW_entries, T4]

private lemma super_eq (k i j : Fin 4) : superpotential eta4 T4 k i j = -3 * T4 k i j := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [superpotential, torsionTrace, eta4, sign4, T4, Fin.sum_univ_four, Matrix.diagonal_apply]

private lemma lower_eq (k q r : Fin 4) :
    (∑ s, eta4.g k s * T4 s q r) = sign4 k * T4 k q r := by
  simp [eta4, Matrix.diagonal_apply, ite_mul]

private lemma raise_eq (k i j : Fin 4) :
    (∑ q, ∑ r, eta4.ginv i q * eta4.ginv j r * (sign4 k * T4 k q r)) =
      sign4 i * sign4 j * (sign4 k * T4 k i j) := by
  simp [eta4, Matrix.diagonal_apply, ite_mul, mul_ite]

/-- The actual derivative of the PR's comoving tetrad feeds the general PR scalar. -/
lemma torsion_reproduction :
    torsionScalar eta4 (weitzenbockTorsion (flrwTetradInv Real.exp 0) dFLRW) = 18 ∧
    flrwTorsionScalar Real.exp 0 = 6 := by
  constructor
  · rw [actual_torsion]
    unfold torsionScalar
    simp_rw [lower_eq, raise_eq, super_eq]
    norm_num [Fin.sum_univ_four, eta4, sign4, T4, Matrix.diagonal_apply]
  · norm_num [flrwTorsionScalar, Real.deriv_exp]

/-! A shearing coframe E(t) with t the zero-indexed coordinate. -/

private def shear (t : ℝ) : Tensor2 2 := !![1, t; 0, 1]
private def shearInv : Tensor2 2 := !![1, -1; 0, 1]
private def shearFrame : Tetrad 2 where
  e := shear 1
  einv := shearInv
  inv_left := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [shear, shearInv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  inv_right := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [shear, shearInv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

private def dShear (u : Fin 2) : Tensor2 2 := fun A j =>
  coordDeriv u (fun y => shear (y 0) A j) (fun _ => 1)

private lemma shear_deriv (i j : Fin 2) :
    dShear 0 i j = (if i = 0 ∧ j = 1 then 1 else 0) := by
  fin_cases i <;> fin_cases j <;> norm_num [dShear, coordDeriv, shear, Function.update]

/-- The PR contraction and the unique connection matrix solving ∂E = E Γ differ. -/
lemma tetrad_reproduction :
    weitzenbockConn shearFrame.einv dShear 1 0 1 = -1 ∧
    (shearFrame.einv * dShear 0) 1 1 = 0 ∧
    shearFrame.e * (shearFrame.einv * dShear 0) = dShear 0 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [weitzenbockConn, Fin.sum_univ_two, shearFrame, shearInv, shear_deriv]
  · norm_num [Matrix.mul_apply, Fin.sum_univ_two, shearFrame, shearInv, shear_deriv]
  · rw [← Matrix.mul_assoc, shearFrame.inv_left, Matrix.one_mul]

private def volumeDensity (g : Tensor2 4) : ℝ := Real.sqrt |g.det|

private lemma density_values :
    volumeDensity eta4.g = 1 ∧ volumeDensity ((2 : ℝ) • eta4.g) = 4 := by
  have hd : eta4.g.det = -1 := by
    norm_num [eta4, Matrix.det_diagonal, Fin.prod_univ_four, sign4]
  constructor
  · norm_num [volumeDensity, hd]
  · apply (Real.sqrt_eq_iff_eq_sq (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)).2
    norm_num [Matrix.det_smul, hd]

/-- A normalized potential rescales inversely to the four-dimensional volume density. -/
private def rescale (V : ℝ → ℝ) (φ : ℝ) := V φ / φ^2

private lemma rescale_eq_twice (V : ℝ → ℝ) (φ : ℝ) :
    rescale V φ = 2 * einsteinFrameV V φ := by
  by_cases h : φ = 0
  · simp [rescale, einsteinFrameV, h]
  · unfold rescale einsteinFrameV
    field_simp

/-- Check the point values and the plateau using the PR's own convergence theorem. -/
lemma potential_reproduction :
    starobinskyPotential 1 2 = 1/8 ∧
    einsteinFrameV (starobinskyPotential 1) 2 = 1/64 ∧
    rescale (starobinskyPotential 1) 2 = 1/32 ∧
    volumeDensity eta4.g * starobinskyPotential 1 2 =
      volumeDensity ((2 : ℝ) • eta4.g) * rescale (starobinskyPotential 1) 2 ∧
    volumeDensity eta4.g * starobinskyPotential 1 2 ≠
      volumeDensity ((2 : ℝ) • eta4.g) * einsteinFrameV (starobinskyPotential 1) 2 ∧
    ∀ (α : ℝ), α ≠ 0 →
      Filter.Tendsto (rescale (starobinskyPotential α)) Filter.atTop (nhds (1/(8*α))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [starobinskyPotential]
  · norm_num [einsteinFrameV, starobinskyPotential]
  · norm_num [rescale, starobinskyPotential]
  · norm_num [density_values.1, density_values.2, rescale, starobinskyPotential]
  · norm_num [density_values.1, density_values.2, einsteinFrameV, starobinskyPotential]
  · intro α hα
    have h := (starobinsky_plateau α hα).const_mul (2 : ℝ)
    have heq : 2 * (1 / (16*α)) = 1 / (8*α) := by
      field_simp
      ring
    change Filter.Tendsto (fun φ => rescale (starobinskyPotential α) φ) _ _
    rw [← heq]
    simpa only [rescale_eq_twice] using h

#print axioms adm_reproduction
#print axioms torsion_reproduction
#print axioms tetrad_reproduction
#print axioms potential_reproduction

end
end PR2132Repro
