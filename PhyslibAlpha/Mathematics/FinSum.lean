/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic

/-!

# Splitting a sum over `Fin (n + 1)`

A sum over `Fin (n + 1)` written as a sum over `Fin n` plus its last term.

## i. Overview

`Fin.sum_univ_castSucc` splits the sum of a family over `Fin (n + 1)` into the sum over the
first `n` indices and the last term. The packaging here keeps the coercion `⟨·, by omega⟩`
explicit, which is the form needed when a five-dimensional expression is cut into four
directions and one extra direction, as in the Kaluza–Klein metric.

## ii. Key results

- `sum_fin_succ_split` : a sum over `Fin (n + 1)` as a sum over `Fin n` plus the last term.
- `sum_fin5_split` : the case `n = 4`, a sum over `Fin 5` as a sum over `Fin 4` plus the last term.

## iii. Table of contents

- A. Splitting a sum over `Fin (n + 1)`

## iv. References

* T. Kaluza, *Zum Unitätsproblem der Physik* (1921). [ref: Kaluza1921]
* O. Klein, *Quantentheorie und fünfdimensionale Relativitätstheorie* (1926). [ref: Klein1926]

-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Splitting a sum over `Fin (n + 1)`

-/

/-- Split a sum over `Fin (n + 1)` into the sum over the first `n` indices and the last term. -/
lemma sum_fin_succ_split {n : ℕ} (f : Fin (n + 1) → ℝ) :
    (∑ k : Fin (n + 1), f k) = (∑ k : Fin n, f ⟨k.val, by omega⟩) + f ⟨n, by omega⟩ := by
  rw [Fin.sum_univ_castSucc]
  rfl

/-- Split a sum over `Fin 5` into its first four terms and the last term. -/
lemma sum_fin5_split (f : Fin 5 → ℝ) :
    (∑ k : Fin 5, f k) = (∑ k : Fin 4, f ⟨k.val, by omega⟩) + f 4 :=
  sum_fin_succ_split f

end GeneralRelativity
