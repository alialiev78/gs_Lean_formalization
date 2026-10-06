module

public import GS.GlobalGeometry.FrobeniusProjection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Existence and uniqueness of minimum-norm least-squares lifts

This file constructs the lift: projection onto the image, then removal of the
kernel component. It does not assume a pseudoinverse or the solvability of the
normal equations. Reweighting is an explicit linear equivalence; positive
multiplicities are handled by entrywise square-root scaling.

-/
noncomputable section
open GS GS.GlobalGeometry Matrix
open scoped BigOperators
namespace GS.Revision.LeastSquares
variable {m n : ℕ}

def restrictedKernel (S : Submodule ℝ (Mat m)) (L : Mat m →ₗ[ℝ] Mat n) :
    Submodule ℝ (Mat m) := S ⊓ LinearMap.ker L

/-- An admissible lift of the image projection, orthogonal to the admissible kernel. -/
def Canonical (S : Submodule ℝ (Mat m)) (L : Mat m →ₗ[ℝ] Mat n)
    (Z : Mat n) (a : Mat m) : Prop :=
  a ∈ S ∧ L a = frobProjection (S.map L) Z ∧
    ∀ k ∈ restrictedKernel S L, frobInner a k = 0

/-- Existence uses actual finite-dimensional orthogonal projections twice. -/
theorem existsUnique_canonical (S : Submodule ℝ (Mat m))
    (L : Mat m →ₗ[ℝ] Mat n) (Z : Mat n) : ∃! a, Canonical S L Z a := by
  obtain ⟨a, ha, he⟩ := frobProjection_mem (S.map L) Z
  let K := restrictedKernel S L
  let k := frobProjection K a
  let a₀ := a - k
  have hk : k ∈ K := frobProjection_mem K a
  have hkS : k ∈ S := hk.1
  have hLk : L k = 0 := hk.2
  have ha₀ : a₀ ∈ S := S.sub_mem ha hkS
  have he₀ : L a₀ = frobProjection (S.map L) Z := by
    dsimp [a₀]
    rw [map_sub, hLk, sub_zero, he]
  have hn₀ : ∀ v ∈ K, frobInner a₀ v = 0 := by
    intro v hv
    exact frobProjection_normal K a v hv
  refine ⟨a₀, ⟨ha₀, he₀, hn₀⟩, ?_⟩
  intro b hb
  have hd : b - a₀ ∈ K := by
    refine ⟨S.sub_mem hb.1 ha₀, ?_⟩
    change L (b - a₀) = 0
    rw [map_sub, hb.2.1, he₀, sub_self]
  apply sub_eq_zero.mp
  apply (frobSq_eq_zero_iff _).mp
  change frobInner (b - a₀) (b - a₀) = 0
  rw [frobInner_sub_left, hb.2.2 _ hd, hn₀ _ hd, sub_self]

def canonicalLift (S : Submodule ℝ (Mat m)) (L : Mat m →ₗ[ℝ] Mat n)
    (Z : Mat n) : Mat m :=
  Classical.choose (existsUnique_canonical S L Z).exists

theorem canonical_spec (S : Submodule ℝ (Mat m)) (L : Mat m →ₗ[ℝ] Mat n)
    (Z : Mat n) : Canonical S L Z (canonicalLift S L Z) :=
  Classical.choose_spec (existsUnique_canonical S L Z).exists

theorem canonical_mem (S : Submodule ℝ (Mat m)) (L : Mat m →ₗ[ℝ] Mat n)
    (Z : Mat n) : canonicalLift S L Z ∈ S := (canonical_spec S L Z).1

theorem canonical_image (S : Submodule ℝ (Mat m)) (L : Mat m →ₗ[ℝ] Mat n)
    (Z : Mat n) : L (canonicalLift S L Z) = frobProjection (S.map L) Z :=
  (canonical_spec S L Z).2.1

theorem canonical_horizontal (S : Submodule ℝ (Mat m)) (L : Mat m →ₗ[ℝ] Mat n)
    (Z : Mat n) (k : Mat m) (hk : k ∈ restrictedKernel S L) :
    frobInner (canonicalLift S L Z) k = 0 := (canonical_spec S L Z).2.2 k hk

theorem residual_pythagorean (S : Submodule ℝ (Mat m)) (L : Mat m →ₗ[ℝ] Mat n)
    (Z : Mat n) (b : Mat m) (hb : b ∈ S) :
    frobSq (Z - L b) = frobSq (Z - L (canonicalLift S L Z)) +
      frobSq (L (canonicalLift S L Z) - L b) := by
  simp only [canonical_image]
  exact frobProjection_pythagorean (S.map L) Z (L b) ⟨b, hb, rfl⟩

theorem minimizes_residual (S : Submodule ℝ (Mat m)) (L : Mat m →ₗ[ℝ] Mat n)
    (Z : Mat n) (b : Mat m) (hb : b ∈ S) :
    frobSq (Z - L (canonicalLift S L Z)) ≤ frobSq (Z - L b) := by
  rw [residual_pythagorean S L Z b hb]
  exact le_add_of_nonneg_right (frobSq_nonneg _)

/-- All least-squares minimizers have the same synthesized matrix. -/
theorem same_image_of_same_residual (S : Submodule ℝ (Mat m))
    (L : Mat m →ₗ[ℝ] Mat n) (Z : Mat n) (b : Mat m) (hb : b ∈ S)
    (he : frobSq (Z - L b) = frobSq (Z - L (canonicalLift S L Z))) :
    L b = L (canonicalLift S L Z) := by
  have hp := residual_pythagorean S L Z b hb
  have h0 : frobSq (L (canonicalLift S L Z) - L b) = 0 := by linarith
  exact (sub_eq_zero.mp ((frobSq_eq_zero_iff _).mp h0)).symm

/-- Orthogonality to the kernel selects a genuinely minimum-norm lift. -/
theorem parameter_pythagorean (S : Submodule ℝ (Mat m))
    (L : Mat m →ₗ[ℝ] Mat n) (Z : Mat n) (b : Mat m) (hb : b ∈ S)
    (he : L b = L (canonicalLift S L Z)) :
    frobSq b = frobSq (canonicalLift S L Z) + frobSq (b - canonicalLift S L Z) := by
  have hd : b - canonicalLift S L Z ∈ restrictedKernel S L := by
    refine ⟨S.sub_mem hb (canonical_mem S L Z), ?_⟩
    change L (b - canonicalLift S L Z) = 0
    rw [map_sub, he, sub_self]
  have hn := canonical_horizontal S L Z _ hd
  have hsplit : b = canonicalLift S L Z + (b - canonicalLift S L Z) := by abel
  conv_lhs => rw [hsplit, frobSq_add, hn]
  ring

theorem minimizes_parameter_norm (S : Submodule ℝ (Mat m))
    (L : Mat m →ₗ[ℝ] Mat n) (Z : Mat n) (b : Mat m) (hb : b ∈ S)
    (he : frobSq (Z - L b) = frobSq (Z - L (canonicalLift S L Z))) :
    frobSq (canonicalLift S L Z) ≤ frobSq b := by
  rw [parameter_pythagorean S L Z b hb (same_image_of_same_residual S L Z b hb he)]
  exact le_add_of_nonneg_right (frobSq_nonneg _)

theorem unique_at_minimum_norm (S : Submodule ℝ (Mat m))
    (L : Mat m →ₗ[ℝ] Mat n) (Z : Mat n) (b : Mat m) (hb : b ∈ S)
    (he : frobSq (Z - L b) = frobSq (Z - L (canonicalLift S L Z)))
    (hn : frobSq b = frobSq (canonicalLift S L Z)) : b = canonicalLift S L Z := by
  have hp := parameter_pythagorean S L Z b hb
    (same_image_of_same_residual S L Z b hb he)
  apply sub_eq_zero.mp
  apply (frobSq_eq_zero_iff _).mp
  linarith

/-- This is a true change of parameter metric, not an unweighted average. -/
def weightedLift (S : Submodule ℝ (Mat m)) (L : Mat m →ₗ[ℝ] Mat n)
    (T : Mat m ≃ₗ[ℝ] Mat m) (Z : Mat n) : Mat m :=
  T.symm (canonicalLift (S.map T.toLinearMap) (L.comp T.symm.toLinearMap) Z)

theorem weightedLift_mem (S : Submodule ℝ (Mat m)) (L : Mat m →ₗ[ℝ] Mat n)
    (T : Mat m ≃ₗ[ℝ] Mat m) (Z : Mat n) : weightedLift S L T Z ∈ S := by
  obtain ⟨a, ha, he⟩ := canonical_mem (S.map T.toLinearMap)
    (L.comp T.symm.toLinearMap) Z
  unfold weightedLift
  rw [← he]
  simpa using ha

theorem weightedLift_minimizes_residual (S : Submodule ℝ (Mat m))
    (L : Mat m →ₗ[ℝ] Mat n) (T : Mat m ≃ₗ[ℝ] Mat m)
    (Z : Mat n) (b : Mat m) (hb : b ∈ S) :
    frobSq (Z - L (weightedLift S L T Z)) ≤ frobSq (Z - L b) := by
  have h := minimizes_residual (S.map T.toLinearMap) (L.comp T.symm.toLinearMap)
    Z (T b) ⟨b, hb, rfl⟩
  simpa [weightedLift, LinearMap.comp_apply] using h

theorem weightedLift_minimizes_norm (S : Submodule ℝ (Mat m))
    (L : Mat m →ₗ[ℝ] Mat n) (T : Mat m ≃ₗ[ℝ] Mat m)
    (Z : Mat n) (b : Mat m) (hb : b ∈ S)
    (he : frobSq (Z - L b) = frobSq (Z - L (weightedLift S L T Z))) :
    frobSq (T (weightedLift S L T Z)) ≤ frobSq (T b) := by
  have he' : frobSq (Z - (L.comp T.symm.toLinearMap) (T b)) =
      frobSq (Z - (L.comp T.symm.toLinearMap)
        (canonicalLift (S.map T.toLinearMap) (L.comp T.symm.toLinearMap) Z)) := by
    simpa [weightedLift, LinearMap.comp_apply] using he
  have h := minimizes_parameter_norm (S.map T.toLinearMap) (L.comp T.symm.toLinearMap)
    Z (T b) ⟨b, hb, rfl⟩ he'
  simpa [weightedLift] using h

/-- Uniqueness among all least-squares minimizers at the same weighted norm. -/
theorem weightedLift_unique (S : Submodule ℝ (Mat m))
    (L : Mat m →ₗ[ℝ] Mat n) (T : Mat m ≃ₗ[ℝ] Mat m)
    (Z : Mat n) (b : Mat m) (hb : b ∈ S)
    (he : frobSq (Z - L b) = frobSq (Z - L (weightedLift S L T Z)))
    (hn : frobSq (T b) = frobSq (T (weightedLift S L T Z))) :
    b = weightedLift S L T Z := by
  have he' : frobSq (Z - (L.comp T.symm.toLinearMap) (T b)) =
      frobSq (Z - (L.comp T.symm.toLinearMap)
        (canonicalLift (S.map T.toLinearMap) (L.comp T.symm.toLinearMap) Z)) := by
    simpa [weightedLift, LinearMap.comp_apply] using he
  have hn' : frobSq (T b) =
      frobSq (canonicalLift (S.map T.toLinearMap) (L.comp T.symm.toLinearMap) Z) := by
    simpa [weightedLift] using hn
  have h := unique_at_minimum_norm (S.map T.toLinearMap) (L.comp T.symm.toLinearMap)
    Z (T b) ⟨b, hb, rfl⟩ he' hn'
  apply T.injective
  simpa [weightedLift] using h

/-- Scaling by square roots of positive multiplicities is invertible. -/
def coordinateScale (w : Mat m) (hw : ∀ i j, w i j ≠ 0) : Mat m ≃ₗ[ℝ] Mat m where
  toFun a i j := w i j * a i j
  invFun a i j := a i j / w i j
  left_inv a := by
    ext i j
    change w i j * a i j / w i j = a i j
    field_simp [hw i j]
  right_inv a := by
    ext i j
    change w i j * (a i j / w i j) = a i j
    field_simp [hw i j]
  map_add' a b := by ext i j; exact mul_add _ _ _
  map_smul' r a := by ext i j; change _ * (r * _) = r * (_ * _); ring

theorem coordinateScale_sq (w : Mat m) (hw : ∀ i j, w i j ≠ 0) (a : Mat m) :
    frobSq (coordinateScale w hw a) = ∑ i, ∑ j, (w i j)^2 * (a i j)^2 := by
  unfold frobSq frobInner
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change (w i j * a i j) * (w i j * a i j) = (w i j)^2 * (a i j)^2
  ring

def multiplicityScale (D : Mat m) (hD : ∀ i j, 0 < D i j) : Mat m ≃ₗ[ℝ] Mat m :=
  coordinateScale (fun i j => Real.sqrt (D i j))
    (fun i j => ne_of_gt (Real.sqrt_pos.mpr (hD i j)))

theorem multiplicityScale_sq (D : Mat m) (hD : ∀ i j, 0 < D i j) (a : Mat m) :
    frobSq (multiplicityScale D hD a) = ∑ i, ∑ j, D i j * (a i j)^2 := by
  rw [multiplicityScale, coordinateScale_sq]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Real.sq_sqrt (le_of_lt (hD i j))]

end GS.Revision.LeastSquares
