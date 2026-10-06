module

public import GS.Projection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Coordinate-correct overlap halving

The mask is defined in the coordinates of C and P Ω Pᵀ. Its pullback, not the
same array, must be applied to Ω. This module strengthens the original
entrywise conjugated-mask lemma to the entire correction operator.
This module is included in the full build and axiom audit.
-/
noncomputable section
open Matrix
namespace GS.Revision
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Halve exactly the entries selected by p. -/
def halveOn (p : ι → ι → Prop) [DecidableRel p]
    (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  A - (1 / 2 : ℝ) • mask p A

theorem halveOn_apply (p : ι → ι → Prop) [DecidableRel p]
    (A : Matrix ι ι ℝ) (i j : ι) :
    halveOn p A i j = if p i j then A i j / 2 else A i j := by
  by_cases h : p i j <;> simp [halveOn, mask, h] <;> ring

/-- Pull a common-coordinate mask back to the original right-factor coordinates. -/
def pullMask (σ : Equiv.Perm ι) (p : ι → ι → Prop) : ι → ι → Prop :=
  fun i j => p (σ i) (σ j)

instance pullMaskDecidable (σ : Equiv.Perm ι) (p : ι → ι → Prop)
    [DecidableRel p] : DecidableRel (pullMask σ p) :=
  fun i j => inferInstanceAs (Decidable (p (σ i) (σ j)))

/-- Whole-matrix form of Pᵀ(M ⊙ P Ω Pᵀ)P = (Pᵀ M P) ⊙ Ω.
The mask is represented as a predicate, not as a numerical permutation matrix. -/
theorem halveOn_conjugation (σ : Equiv.Perm ι)
    (p : ι → ι → Prop) [DecidableRel p] (A : Matrix ι ι ℝ) :
    permMatrix σ * halveOn (pullMask σ p) A * (permMatrix σ)ᵀ =
      halveOn p (permMatrix σ * A * (permMatrix σ)ᵀ) := by
  classical
  ext i j
  simp only [perm_conjugate_apply, halveOn_apply, pullMask, Equiv.apply_symm_apply]

theorem halveOn_preserves_skew (p : ι → ι → Prop) [DecidableRel p]
    (hp : MaskSymmetric p) (A : Matrix ι ι ℝ) (hA : IsSkew A) :
    IsSkew (halveOn p A) := by
  ext i j
  have he : A j i = -A i j := congrFun (congrFun hA i) j
  change halveOn p A j i = -(halveOn p A i j)
  rw [halveOn_apply, halveOn_apply]
  by_cases h : p i j
  · have h' := (hp i j).mp h
    simp [h, h', he]
    ring
  · have h' : ¬ p j i := fun hh => h ((hp i j).mpr hh)
    simp [h, h', he]

/-- Concrete regression for N=6, b₁=b₂=3, k₁=k₂=2.
These are original right-factor coordinates (0,1) and their common-coordinate
images (0,2); the two masks cannot be identified. -/
def overlapSix (i j : Fin 6) : Prop :=
  i ≠ j ∧ i.val / 3 = j.val / 3 ∧ i.val % 2 = j.val % 2

theorem overlapSix_at_common_pair : overlapSix 0 2 := by
  unfold overlapSix
  decide

theorem overlapSix_not_at_original_pair : ¬ overlapSix 0 1 := by
  unfold overlapSix
  decide

/-- If one of two identical contributions is halved in the wrong coordinates,
the sum is 3/2 times the target rather than the target. -/
theorem untransported_mask_bias (z : ℝ) : z / 2 + z = (3 / 2 : ℝ) * z := by
  ring

end GS.Revision
