module

public import GS.SharedGeodesics.Orthogonal
public import GS.Geodesics.ShuffleCondition

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The original scalar-shuffle condition with actual within-layer sharing

The ambient dimension is n = k₁ * right.size; both physical block sizes divide
n by construction of Pattern. The inequality left.size ≤ k₁ is sufficient for
the concrete scalar shuffle, not for an arbitrary permutation.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.SharedGeometry
open scoped Topology Manifold
namespace GS.SharedGeodesics
variable {n : ℕ} (right left : Pattern n) (k₁ : ℕ) (hN : n = k₁ * right.size)
local notation "σ" => GS.Geodesics.scalarShuffleOfSize hN
local instance shuffleNormedSpace : NormedSpace ℝ (HorizontalModel right left (permMatrix σ)) := Submodule.normedSpace _
local instance shuffleChartedSpace : ChartedSpace (HorizontalModel right left (permMatrix σ))
    (MatrixOrbit right left (permMatrix σ)) := sharedOrbitChartedSpace right left (permMatrix σ)
local instance shuffleIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left (permMatrix σ))) ⊤
    (MatrixOrbit right left (permMatrix σ)) := sharedOrbitIsManifold right left (permMatrix σ)

theorem scalarShuffle_shared_geodesic (hbk : left.size ≤ k₁)
    (g : Factors right left) (C : Generator left) (Ω : Generator right) (t : ℝ) :
    HasDerivAt (fun s => (orthogonalExpCurve right left σ g C Ω s).val)
      (orthogonalExpVelocity right left σ g C Ω t) t ∧
    HasDerivAt (orthogonalExpVelocity right left σ g C Ω)
      (orthogonalExpAcceleration right left σ g C Ω t) t ∧
    covariantAlong right left (permMatrix σ) (orthogonalExpCurve right left σ g C Ω)
      (orthogonalExpVelocity right left σ g C Ω) t = 0 ∧
    frobSq (orthogonalExpVelocity right left σ g C Ω t) = frobSq C.val + frobSq Ω.val := by
  have hno := GS.Geodesics.scalarShuffleOfSize_noOverlap right.size k₁ left.size hN
    right.positive left.positive hbk
  exact ⟨orthogonalExpCurve_hasDerivAt right left σ g C Ω t,
    orthogonalExpVelocity_hasDerivAt right left σ g C Ω t,
    orthogonalExpCurve_covariantVelocity_zero right left σ hno g C Ω t,
    orthogonalExpCurve_constant_speed right left σ hno g C Ω t⟩

theorem scalarShuffle_shared_exists_geodesic (hbk : left.size ≤ k₁)
    (X : MatrixOrbit right left (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left (permMatrix σ))) X) :
    ∃ (C : Generator left) (Ω : Generator right),
      orthogonalExpCurve right left σ (preferredFactor (permMatrix σ) X) C Ω 0 = X ∧
      mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left (permMatrix σ)))
        (orthogonalExpCurve right left σ (preferredFactor (permMatrix σ) X) C Ω)
        0 (1 : ℝ) = v ∧
      ∀ t : ℝ, covariantAlong right left (permMatrix σ)
        (orthogonalExpCurve right left σ (preferredFactor (permMatrix σ) X) C Ω)
        (orthogonalExpVelocity right left σ (preferredFactor (permMatrix σ) X) C Ω) t = 0 :=
  exists_orthogonalExpCurve_of_tangent right left σ
    (GS.Geodesics.scalarShuffleOfSize_noOverlap right.size k₁ left.size hN
      right.positive left.positive hbk) X v

end GS.SharedGeodesics
