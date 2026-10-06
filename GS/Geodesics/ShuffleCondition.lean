module

public import GS.LieAction.Nonoverlap
public import GS.OriginalLocalModel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The exact scalar-shuffle nonoverlap condition

The numeric action is proved for the original scalar permutation, rather than
assumed as an extra convention. In common output coordinates the right block
label is the remainder modulo the number of original right blocks. Consequently
`b₂ ≤ k₁` gives the exact support condition used by the orbit-block geodesics.
-/

noncomputable section
namespace GS.Geodesics
open GS GS.LieAction

private theorem cast_fin_val {m n : ℕ} (h : m = n) (a : Fin m) :
    (cast (congrArg Fin h) a).val = a.val := by
  cases h
  rfl

/-- Exact row-major numeric action of the original perfect shuffle. -/
theorem scalarShuffle_val (k b : ℕ) (i : Fin (k*b)) :
    (scalarShuffle k b i).val = (i.val % b) * k + i.val / b := by
  change (cast (congrArg Fin (Nat.mul_comm b k))
    (finProdFinEquiv ((finProdFinEquiv.symm i).2,
      (finProdFinEquiv.symm i).1))).val = _
  rw [cast_fin_val (Nat.mul_comm b k)]
  change i.val / b + k * (i.val % b) = _
  ac_rfl

/-- The original right block label becomes a remainder in output coordinates. -/
theorem scalarShuffle_symm_block_label (k b : ℕ) (hb : 0 < b)
    (i : Fin (k*b)) :
    ((scalarShuffle k b).symm i).val / b = i.val % k := by
  let j := (scalarShuffle k b).symm i
  have hj : j.val / b < k := (Nat.div_lt_iff_lt_mul hb).mpr j.isLt
  have h := scalarShuffle_val k b j
  rw [show scalarShuffle k b j = i from (scalarShuffle k b).apply_symm_apply i] at h
  change j.val / b = i.val % k
  rw [h]
  simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hj]

/-- The manuscript inequality proves nonoverlap for the actual scalar shuffle. -/
theorem scalarShuffle_noOverlap (b₁ k₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hbk : b₂ ≤ k₁) :
    NoOffDiagonalOverlap (fun i : Fin (k₁*b₁) => i.val / b₁)
      (fun i : Fin (k₁*b₁) => i.val / b₂) (scalarShuffle k₁ b₁) :=
  perfectShuffle_noOverlap b₁ k₁ b₂ rfl hb₁ hb₂ hbk
    (scalarShuffle k₁ b₁) (scalarShuffle_val k₁ b₁)

/-- The same original permutation transported to an explicitly named dimension. -/
def scalarShuffleOfSize {n k b : ℕ} (hN : n = k*b) : Equiv.Perm (Fin n) :=
  (Equiv.cast (congrArg Fin hN)).trans
    ((scalarShuffle k b).trans (Equiv.cast (congrArg Fin hN.symm)))

theorem scalarShuffleOfSize_val {n k b : ℕ} (hN : n = k*b) (i : Fin n) :
    (scalarShuffleOfSize hN i).val = (i.val % b) * k + i.val / b := by
  subst n
  exact scalarShuffle_val k b i

theorem scalarShuffleOfSize_symm_block_label {n k b : ℕ}
    (hN : n = k*b) (hb : 0 < b) (i : Fin n) :
    ((scalarShuffleOfSize hN).symm i).val / b = i.val % k := by
  subst n
  exact scalarShuffle_symm_block_label k b hb i

/-- A directly usable theorem when the ambient dimension is given by `hN`. -/
theorem scalarShuffleOfSize_noOverlap {n : ℕ} (b₁ k₁ b₂ : ℕ)
    (hN : n = k₁*b₁) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hbk : b₂ ≤ k₁) :
    NoOffDiagonalOverlap (fun i : Fin n => i.val / b₁)
      (fun i : Fin n => i.val / b₂) (scalarShuffleOfSize hN) :=
  perfectShuffle_noOverlap b₁ k₁ b₂ hN hb₁ hb₂ hbk
    (scalarShuffleOfSize hN) (scalarShuffleOfSize_val hN)

end GS.Geodesics
