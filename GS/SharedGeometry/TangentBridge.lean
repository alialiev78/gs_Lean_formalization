module

public import GS.SharedGeometry.OrbitAtlas
public import GS.SharedGeometry.HorizontalDifferential
public import GS.SharedGeometry.Projection
public import GS.OverlapGeometry.ManifoldSmoothMaps

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The actual tangent space of the shared matrix orbit

The inclusion derivative of the constructed atlas has exactly the point-based
shared generator range.  The existing coupled projector is consequently the
orthogonal projector onto the full manifold tangent image, not merely onto
velocities with an assumed differentiable factor lift.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.GlobalGeometry
open scoped Topology Manifold
namespace GS.SharedGeometry
variable {n : ℕ} (right left : Pattern n) (P : Mat n)
local instance tangentBridgeChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
local instance tangentBridgeIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

/-- Full image of the actual mathlib manifold differential. -/
theorem orbit_tangent_image_iff (X : MatrixOrbit right left P) (Z : Mat n) :
    (∃ v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X,
      mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, Mat n))
        (fun Y : MatrixOrbit right left P => Y.val) X v = Z) ↔
      Z ∈ pointDirections right left X.val := by
  rw [sharedOrbit_val_mfderiv_eq right left P X]
  have he : (fun h : HorizontalModel right left P =>
      preferredFactor P X • horizontalValue right left P h) =
      (fun h : HorizontalModel right left P => orbitParam (preferredFactor P X) P h.val) := by
    funext h
    exact (orbitParam_eq_translate (preferredFactor P X) P h.val).symm
  rw [he]
  have hg : preferredFactor P X • P = X.val :=
    congrArg Subtype.val (preferredFactor_spec P X)
  have hh := horizontalOrbit_fderiv_zero_range P (preferredFactor P X) Z
  rw [hg] at hh
  constructor
  · rintro ⟨v, hv⟩
    exact hh.mp ⟨v, hv⟩
  · intro hZ
    obtain ⟨v, hv⟩ := hh.mpr hZ
    exact ⟨v, hv⟩

/-- Agreement with the original factor-coordinate direction for any valid
factorization, not only the representative used to centre the chart. -/
theorem tangent_image_iff_sharedDirection (X : MatrixOrbit right left P)
    (L R Z : Mat n)
    (hL : SharedOrthogonalFactor left.size left.label L)
    (hR : SharedOrthogonalFactor right.size right.label R)
    (hX : product2 L P R = X.val) :
    (∃ v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X,
      mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, Mat n))
        (fun Y : MatrixOrbit right left P => Y.val) X v = Z) ↔
      SharedDirection right.size left.size right.label left.label P L R Z := by
  rw [orbit_tangent_image_iff,
    sharedDirection_iff_pointDirections P L R Z hL hR, hX]

/-- The fixed points of the canonical projector are exactly the true tangents. -/
theorem pointProjection_fixed_iff_tangent_image
    (X : MatrixOrbit right left P) (Z : Mat n) :
    pointProjection right left X.val Z = Z ↔
      ∃ v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X,
        mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, Mat n))
          (fun Y : MatrixOrbit right left P => Y.val) X v = Z := by
  rw [orbit_tangent_image_iff]
  constructor
  · intro h
    rw [← h]
    exact pointProjection_mem X.val Z
  · exact pointProjection_of_mem X.val Z

/-- The projected ambient matrix has one and only one actual tangent lift. -/
theorem pointProjection_unique_tangent_lift
    (X : MatrixOrbit right left P) (Z : Mat n) :
    ∃! v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X,
      mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, Mat n))
        (fun Y : MatrixOrbit right left P => Y.val) X v =
          pointProjection right left X.val Z := by
  obtain ⟨v, hv⟩ := (orbit_tangent_image_iff right left P X _).mpr
    (pointProjection_mem X.val Z)
  refine ⟨v, hv, ?_⟩
  intro w hw
  exact sharedOrbit_val_mfderiv_injective right left P X (hw.trans hv.symm)

/-- Least-squares optimality against every true manifold tangent vector. -/
theorem pointProjection_pythagorean_tangent
    (X : MatrixOrbit right left P) (Z : Mat n)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    let Y : Mat n := mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, Mat n))
      (fun W : MatrixOrbit right left P => W.val) X v
    frobSq (Z - Y) = frobSq (Z - pointProjection right left X.val Z) +
      frobSq (pointProjection right left X.val Z - Y) := by
  dsimp only
  exact frobProjection_pythagorean (pointDirections right left X.val) Z _
    ((orbit_tangent_image_iff right left P X _).mp ⟨v, rfl⟩)

/-- The already implemented coupled projection now lands in the full tangent
space of the shared matrix manifold.  Orthogonality of P is required here
only for the original factor-based projector formula. -/
theorem exactSharedProjection_unique_tangent_lift
    (X : MatrixOrbit right left P) (L R Z : Mat n) (hP : Orthogonal P)
    (hL : SharedOrthogonalFactor left.size left.label L)
    (hR : SharedOrthogonalFactor right.size right.label R)
    (hX : product2 L P R = X.val) :
    ∃! v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X,
      mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, Mat n))
        (fun Y : MatrixOrbit right left P => Y.val) X v =
          exactSharedProjection right.size left.size right.label left.label P L R Z := by
  rw [exactSharedProjection_eq_pointProjection P L R Z hP hL hR, hX]
  exact pointProjection_unique_tangent_lift right left P X Z

/-- The intrinsic and ambient smooth-map interfaces agree. -/
theorem sharedOrbit_contMDiff_iff_contDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → MatrixOrbit right left P) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, HorizontalModel right left P)) ⊤ f ↔
      ContDiff ℝ ⊤ (fun x => (f x).val) :=
  GS.OverlapGeometry.slice_contMDiff_iff_contDiff (preferredOrbitSlice right left P)
    (preferredOrbitSlice_covers right left P) f

/-- The same criterion permits a manifold source, including its tangent bundle. -/
theorem sharedOrbit_contMDiff_iff_ambient {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (f : M → MatrixOrbit right left P) :
    ContMDiff I (𝓘(ℝ, HorizontalModel right left P)) ⊤ f ↔
      ContMDiff I (𝓘(ℝ, Mat n)) ⊤ (fun x => (f x).val) :=
  GS.OverlapGeometry.slice_contMDiff_iff_ambient (preferredOrbitSlice right left P)
    (preferredOrbitSlice_covers right left P) I f

end GS.SharedGeometry
