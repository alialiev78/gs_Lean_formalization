module

public import GS.UnitaryManifold.OrbitAtlas
public import GS.UnitaryManifold.HorizontalDifferential
public import GS.OverlapGeometry.SmoothMaps

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Actual tangent image with arbitrary overlap

The manifold is the inherited-topology horizontal slice atlas. The statements
below identify mathlib's actual tangent space and inclusion differential with
the original two-factor generator image, including continuous stabilizers.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.OverlapGeometry
open scoped Topology Manifold
namespace GS.UnitaryManifold
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance tangentHorizontalNormedAddCommGroup :
    NormedAddCommGroup (HorizontalModel b₁ b₂ σ) := inferInstance
local instance tangentHorizontalNormedSpace :
    NormedSpace ℝ (HorizontalModel b₁ b₂ σ) := inferInstance
local instance : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- The preferred factors reconstruct the point, without an overlap restriction. -/
theorem preferredFactor_product (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    GS.UnitaryGeometry.product2 (preferredFactor σ X).1.val (cPermMatrix σ) (preferredFactor σ X).2.valᴴ =
      X.val :=
  congrArg Subtype.val (preferredFactor_spec σ X)

/-- The full generator image equals the image of the actual manifold tangent
space. The source has already been quotiented by its infinitesimal stabilizer. -/
theorem orbit_tangent_image_iff (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) (Z : CMat n) :
    (∃ v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X,
      mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, CMat n))
        (fun Y : MatrixOrbit b₁ b₂ (cPermMatrix σ) => Y.val) X v = Z) ↔
      Z ∈ tangentParamSpace b₁ b₂ (preferredFactor σ X).1.val (cPermMatrix σ)
        (preferredFactor σ X).2.valᴴ := by
  rw [overlap_val_mfderiv_eq b₁ b₂ σ X]
  have he : (fun h : HorizontalModel b₁ b₂ σ =>
      preferredFactor σ X • horizontalValue b₁ b₂ σ h) =
      (fun h : HorizontalModel b₁ b₂ σ => orbitParam (preferredFactor σ X) (cPermMatrix σ) h.val) := by
    funext h
    exact (orbitParam_eq_translate (preferredFactor σ X) (cPermMatrix σ) h.val).symm
  rw [he]
  exact horizontalOrbit_fderiv_zero_range σ (preferredFactor σ X) Z

/-- Smoothness into the actual overlapping orbit is equivalent to smoothness
of its ambient matrix realization. No smooth choice of factors is required. -/
theorem overlap_contMDiff_iff_contDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤ f ↔
      ContDiff ℝ ⊤ (fun x => (f x).val) :=
  slice_contMDiff_iff_contDiff (preferredOrbitSlice b₁ b₂ σ)
    (preferredOrbitSlice_covers b₁ b₂ σ) f

end GS.UnitaryManifold
