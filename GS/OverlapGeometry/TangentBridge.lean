module

public import GS.OverlapGeometry.OrbitAtlas
public import GS.OverlapGeometry.HorizontalDifferential
public import GS.OverlapGeometry.SmoothMaps
public import GS.Continuation.AmbientProjection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Actual tangent image and orthogonal projection with arbitrary overlap

The manifold is the inherited-topology horizontal slice atlas. The statements
below identify mathlib's actual tangent space and inclusion differential with
the original two-factor generator image, including continuous stabilizers.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.Extensions GS.Continuation
open GS.ManifoldCompletion
open scoped Topology Manifold
namespace GS.OverlapGeometry
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- The preferred factors reconstruct the point, without an overlap restriction. -/
theorem preferredFactor_product (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    product2 (preferredFactor σ X).1.val (permMatrix σ) (preferredFactor σ X).2.valᵀ =
      X.val :=
  congrArg Subtype.val (preferredFactor_spec σ X)

/-- The full generator image equals the image of the actual manifold tangent
space. The source has already been quotiented by its infinitesimal stabilizer. -/
theorem orbit_tangent_image_iff (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (Z : Mat n) :
    (∃ v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X,
      mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, Mat n))
        (fun Y : MatrixOrbit b₁ b₂ (permMatrix σ) => Y.val) X v = Z) ↔
      TwoFactorDirection b₁ b₂ (preferredFactor σ X).1.val (permMatrix σ)
        (preferredFactor σ X).2.valᵀ Z := by
  rw [overlap_val_mfderiv_eq b₁ b₂ σ X]
  have he : (fun h : HorizontalModel b₁ b₂ σ =>
      preferredFactor σ X • horizontalValue b₁ b₂ σ h) =
      (fun h : HorizontalModel b₁ b₂ σ => orbitParam (preferredFactor σ X) (permMatrix σ) h.val) := by
    funext h
    exact (orbitParam_eq_translate (preferredFactor σ X) (permMatrix σ) h.val).symm
  rw [he]
  exact horizontalOrbit_fderiv_zero_range σ (preferredFactor σ X) Z

/-- No new definition of tangent space: this is a statement about the library
mfderiv from the library TangentSpace of the constructed manifold. -/
theorem pointProjection_fixed_iff_tangent_image
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (Z : Mat n) :
    pointProjection b₁ b₂ X.val Z = Z ↔
      ∃ v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X,
        mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, Mat n))
          (fun Y : MatrixOrbit b₁ b₂ (permMatrix σ) => Y.val) X v = Z := by
  rw [orbit_tangent_image_iff]
  rw [← preferredFactor_product b₁ b₂ σ X]
  exact pointProjection_fixed_iff b₁ b₂ σ
    (preferredFactor σ X).1.val (preferredFactor σ X).2.valᵀ Z
    (preferredFactor σ X).1.property.1 (preferredFactor σ X).2.property.1.transpose
    (preferredFactor σ X).1.property.2 (preferredFactor σ X).2.property.2.transpose

/-- Existence and uniqueness of the intrinsic tangent vector represented by
an output of the point-only orthogonal projector. -/
theorem pointProjection_unique_tangent_lift
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (Z : Mat n) :
    ∃! v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X,
      mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, Mat n))
        (fun Y : MatrixOrbit b₁ b₂ (permMatrix σ) => Y.val) X v =
          pointProjection b₁ b₂ X.val Z := by
  have hid : pointProjection b₁ b₂ X.val
      (pointProjection b₁ b₂ X.val Z) = pointProjection b₁ b₂ X.val Z := by
    rw [← preferredFactor_product b₁ b₂ σ X]
    exact pointProjection_idempotent b₁ b₂ σ
      (preferredFactor σ X).1.val (preferredFactor σ X).2.valᵀ Z
      (preferredFactor σ X).1.property.1 (preferredFactor σ X).2.property.1.transpose
      (preferredFactor σ X).1.property.2 (preferredFactor σ X).2.property.2.transpose
  obtain ⟨v, hv⟩ := (pointProjection_fixed_iff_tangent_image b₁ b₂ σ X _).mp hid
  refine ⟨v, hv, ?_⟩
  intro w hw
  exact overlap_val_mfderiv_injective b₁ b₂ σ X (hw.trans hv.symm)

/-- Least-squares certificate against every actual tangent vector. The norm is
explicitly Frobenius, not mathlib's default matrix sup norm. -/
theorem pointProjection_pythagorean_tangent
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (Z : Mat n)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    let Y : Mat n := mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, Mat n))
      (fun W : MatrixOrbit b₁ b₂ (permMatrix σ) => W.val) X v
    frobSq (Z - Y) = frobSq (Z - pointProjection b₁ b₂ X.val Z) +
      frobSq (pointProjection b₁ b₂ X.val Z - Y) := by
  dsimp only
  have hY := (orbit_tangent_image_iff b₁ b₂ σ X _).mp ⟨v, rfl⟩
  have hp := pointProjection_pythagorean b₁ b₂ σ
    (preferredFactor σ X).1.val (preferredFactor σ X).2.valᵀ Z _
    (preferredFactor σ X).1.property.1 (preferredFactor σ X).2.property.1.transpose
    (preferredFactor σ X).1.property.2 (preferredFactor σ X).2.property.2.transpose hY
  simpa only [preferredFactor_product] using hp

/-- Smoothness into the actual overlapping orbit is equivalent to smoothness
of its ambient matrix realization. No smooth choice of factors is required. -/
theorem overlap_contMDiff_iff_contDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → MatrixOrbit b₁ b₂ (permMatrix σ)) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤ f ↔
      ContDiff ℝ ⊤ (fun x => (f x).val) :=
  slice_contMDiff_iff_contDiff (preferredOrbitSlice b₁ b₂ σ)
    (preferredOrbitSlice_covers b₁ b₂ σ) f

end GS.OverlapGeometry
