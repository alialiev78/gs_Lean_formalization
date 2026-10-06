module

public import GS.Unitary.PointProjection
public import GS.UnitaryManifold.TangentBridge

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The point-only projector and the actual manifold tangent space

These statements concern mathlib's tangent space and inclusion derivative
for the inherited-topology orbit atlas. The ambient projector uses the full
real Frobenius geometry, including every overlap direction.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS Matrix GS.UnitaryGeometry
open scoped Topology Manifold
namespace GS.UnitaryManifold
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance projectionHorizontalNormedAddCommGroup :
    NormedAddCommGroup (HorizontalModel b₁ b₂ σ) := inferInstance
local instance projectionHorizontalNormedSpace :
    NormedSpace ℝ (HorizontalModel b₁ b₂ σ) := inferInstance
local instance : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapIsManifold b₁ b₂ σ

theorem pointTangentSpace_eq_preferred (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    pointTangentSpace b₁ b₂ X.val =
      tangentParamSpace b₁ b₂ (preferredFactor σ X).1.val (cPermMatrix σ)
        (preferredFactor σ X).2.valᴴ := by
  rw [← preferredFactor_product b₁ b₂ σ X]
  exact pointTangentSpace_eq_tangentParamSpace b₁ b₂ _ _ _
    (preferredFactor σ X).1.property.1 (preferredFactor σ X).2.property.1.conjTranspose
    (preferredFactor σ X).1.property.2 (preferredFactor σ X).2.property.2.conjTranspose

/-- Fixed points of the ambient projector are exactly actual tangent vectors. -/
theorem pointProjection_fixed_iff_tangent_image
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) (Z : CMat n) :
    pointProjection b₁ b₂ X.val Z = Z ↔
      ∃ v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X,
        mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, CMat n))
          (fun Y : MatrixOrbit b₁ b₂ (cPermMatrix σ) => Y.val) X v = Z := by
  rw [orbit_tangent_image_iff, pointProjection_fixed_iff,
    pointTangentSpace_eq_preferred b₁ b₂ σ X]

/-- Each projected matrix has one and only one intrinsic tangent lift. -/
theorem pointProjection_unique_tangent_lift
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) (Z : CMat n) :
    ∃! v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X,
      mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, CMat n))
        (fun Y : MatrixOrbit b₁ b₂ (cPermMatrix σ) => Y.val) X v =
          pointProjection b₁ b₂ X.val Z := by
  obtain ⟨v, hv⟩ := (pointProjection_fixed_iff_tangent_image b₁ b₂ σ X _).mp
    (pointProjection_idempotent b₁ b₂ X.val Z)
  refine ⟨v, hv, ?_⟩
  intro w hw
  exact overlap_val_mfderiv_injective b₁ b₂ σ X (hw.trans hv.symm)

/-- The least-squares identity is measured with the actual real Frobenius norm. -/
theorem pointProjection_pythagorean_tangent
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) (Z : CMat n)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    let Y : CMat n := mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, CMat n))
      (fun W : MatrixOrbit b₁ b₂ (cPermMatrix σ) => W.val) X v
    cFrobSq (Z - Y) = cFrobSq (Z - pointProjection b₁ b₂ X.val Z) +
      cFrobSq (pointProjection b₁ b₂ X.val Z - Y) := by
  apply pointProjection_pythagorean
  apply (pointProjection_fixed_iff b₁ b₂ X.val _).mp
  exact (pointProjection_fixed_iff_tangent_image b₁ b₂ σ X _).mpr ⟨v, rfl⟩

end GS.UnitaryManifold
