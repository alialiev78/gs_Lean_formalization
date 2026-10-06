module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Ring.Parity

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Arithmetic of the restricted skew-coordinate dimension

The independent-coordinate dimension of a skew `q × q` matrix is
`q * (q - 1) / 2`.  The parity restriction `q % 4 = 2 ∨ q % 4 = 3`
is exactly the condition that this dimension is odd.

These are arithmetic results only; they do not assert a topological
nonmanifold obstruction.
-/

namespace GS.RestrictedNonmanifold

/-- The triangular number is odd exactly in residue classes two and three. -/
theorem triangular_mod_two_eq_one_iff (q : ℕ) :
    (q * (q - 1) / 2) % 2 = 1 ↔ q % 4 = 2 ∨ q % 4 = 3 := by
  by_cases hzero : q = 0
  · subst q
    simp
  have hmul := Nat.mul_mod q (q - 1) 4
  have hcases : q % 4 = 0 ∨ q % 4 = 1 ∨ q % 4 = 2 ∨ q % 4 = 3 := by omega
  rcases hcases with h | h | h | h
  · have hprev : (q - 1) % 4 = 3 := by omega
    simp [h, hprev] at hmul
    omega
  · have hprev : (q - 1) % 4 = 0 := by omega
    simp [h, hprev] at hmul
    omega
  · have hprev : (q - 1) % 4 = 1 := by omega
    simp [h, hprev] at hmul
    omega
  · have hprev : (q - 1) % 4 = 2 := by omega
    simp [h, hprev] at hmul
    omega

theorem odd_triangular_iff_mod_four (q : ℕ) :
    Odd (q * (q - 1) / 2) ↔ q % 4 = 2 ∨ q % 4 = 3 := by
  rw [Nat.odd_iff, triangular_mod_two_eq_one_iff]

theorem odd_choose_two_iff_mod_four (q : ℕ) :
    Odd (q.choose 2) ↔ q % 4 = 2 ∨ q % 4 = 3 := by
  rw [Nat.choose_two_right, odd_triangular_iff_mod_four]

end GS.RestrictedNonmanifold
