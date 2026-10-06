module

public import GS.Core

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# A concrete admissible base matrix in the first restricted dimension

The matrix with diagonal entries `-1/3` and off-diagonal entries `2/3`
is orthogonal, has determinant one, and has no zero entries. Thus the
matrix hypotheses of the restricted `q = 3` problem are inhabited.

This file proves admissibility of the base matrix, not the topological
nonmanifold conclusion at that basepoint.
-/

noncomputable section

open Matrix GS
open scoped BigOperators

namespace GS.RestrictedNonmanifold

/-- The half-turn about the line spanned by `(1,1,1)`. -/
def basepointQThree : Mat 3 :=
  !![-(1 / 3), 2 / 3, 2 / 3;
     2 / 3, -(1 / 3), 2 / 3;
     2 / 3, 2 / 3, -(1 / 3)]

theorem basepointQThree_apply (i j : Fin 3) :
    basepointQThree i j = if i = j then -(1 / 3 : ℝ) else 2 / 3 := by
  fin_cases i <;> fin_cases j <;> norm_num [basepointQThree]

theorem basepointQThree_orthogonal : Orthogonal basepointQThree := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [basepointQThree, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem basepointQThree_det : basepointQThree.det = 1 := by
  norm_num [Matrix.det_fin_three, basepointQThree_apply, Fin.ext_iff]

theorem basepointQThree_entries_ne_zero (i j : Fin 3) : basepointQThree i j ≠ 0 := by
  rw [basepointQThree_apply]
  split_ifs <;> norm_num

/-- A witness to every matrix hypothesis appearing at `q = 3`. -/
theorem exists_admissible_q_three :
    ∃ Q₀ : Mat 3, Orthogonal Q₀ ∧ Q₀.det = 1 ∧ ∀ i j, Q₀ i j ≠ 0 :=
  ⟨basepointQThree, basepointQThree_orthogonal, basepointQThree_det,
    basepointQThree_entries_ne_zero⟩

end GS.RestrictedNonmanifold
