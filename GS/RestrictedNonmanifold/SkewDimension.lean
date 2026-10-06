module

public import GS.Nonmanifold.SkewCoordinates
public import GS.RestrictedNonmanifold.Parity
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Exact cardinality and parity of the actual skew-coordinate index

The equivalence below counts the `UpperIndex q` used by the project's
row-skew cone, so the numerical parity lemma applies directly to its
actual coordinate space.
-/

noncomputable section

open scoped BigOperators
open GS.Nonmanifold

namespace GS.RestrictedNonmanifold

/-- Group strict-upper-triangular entries by their second coordinate. -/
def upperIndexEquivSigma (q : ℕ) : UpperIndex q ≃ (j : Fin q) × Fin j.val where
  toFun ij := ⟨ij.val.2, ⟨ij.val.1.val, ij.property⟩⟩
  invFun ji := ⟨(⟨ji.2.val, lt_trans ji.2.isLt ji.1.isLt⟩, ji.1), ji.2.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The independent skew-coordinate dimension is the triangular number. -/
theorem card_upperIndex (q : ℕ) :
    Fintype.card (UpperIndex q) = q * (q - 1) / 2 := by
  rw [Fintype.card_congr (upperIndexEquivSigma q), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) q, Finset.sum_range_id]

theorem card_upperIndex_eq_choose (q : ℕ) :
    Fintype.card (UpperIndex q) = q.choose 2 := by
  rw [card_upperIndex, Nat.choose_two_right]

/-- The user's restricted congruences are exactly odd skew dimension. -/
theorem odd_card_upperIndex_iff (q : ℕ) :
    Odd (Fintype.card (UpperIndex q)) ↔ q % 4 = 2 ∨ q % 4 = 3 := by
  rw [card_upperIndex, odd_triangular_iff_mod_four]

theorem odd_card_upperIndex_of_mod_four (q : ℕ)
    (hq : q % 4 = 2 ∨ q % 4 = 3) : Odd (Fintype.card (UpperIndex q)) :=
  (odd_card_upperIndex_iff q).mpr hq

end GS.RestrictedNonmanifold
