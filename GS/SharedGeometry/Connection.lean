module

public import GS.SharedGeometry.Gradient
public import GS.GlobalGeometry.ProjectedDerivative

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The induced projected connection along shared-orbit curves

The operation below takes values in the actual tangent fibre of the shared
atlas. Its ambient realization is the orthogonal projection of the ordinary
derivative. The pairing and product rules use the induced physical Frobenius
metric; no unweighted metric on the unique blocks is substituted.

This supplies the extrinsic induced-connection interface used by the concrete
geodesic theorem. It is not a registration of a general bundled connection API.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions
open scoped Topology Manifold
namespace GS.SharedGeometry
variable {n : ℕ} (right left : Pattern n) (P : Mat n)
local instance connectionNormedSpace : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _
local instance connectionChartedSpace : ChartedSpace (HorizontalModel right left P) (MatrixOrbit right left P) :=
  sharedOrbitChartedSpace right left P
local instance connectionIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

/-- Projection of the actual ambient derivative into the actual tangent fibre. -/
def covariantAlong (γ : ℝ → MatrixOrbit right left P) (V : ℝ → Mat n) (t : ℝ) :
    TangentSpace (𝓘(ℝ, HorizontalModel right left P)) (γ t) :=
  tangentProjection right left P (γ t) (deriv V t)

@[simp] theorem inclusion_covariantAlong (γ : ℝ → MatrixOrbit right left P)
    (V : ℝ → Mat n) (t : ℝ) :
    inclusionDifferential right left P (γ t) (covariantAlong right left P γ V t) =
      pointProjection right left (γ t).val (deriv V t) :=
  inclusion_tangentProjection right left P (γ t) _

theorem covariantAlong_pairing (γ : ℝ → MatrixOrbit right left P)
    (V : ℝ → Mat n) (t : ℝ)
    (w : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) (γ t)) :
    tangentPairing right left P (γ t) (covariantAlong right left P γ V t) w =
      frobInner (deriv V t) (inclusionDifferential right left P (γ t) w) :=
  tangentProjection_pairing right left P (γ t) _ w

theorem covariantAlong_add (γ : ℝ → MatrixOrbit right left P)
    (V W : ℝ → Mat n) {v w : Mat n} {t : ℝ}
    (hv : HasDerivAt V v t) (hw : HasDerivAt W w t) :
    covariantAlong right left P γ (fun s => V s + W s) t =
      covariantAlong right left P γ V t + covariantAlong right left P γ W t := by
  have hadd : HasDerivAt (fun s => V s + W s) (v+w) t := by
    simpa only [Pi.add_def] using hv.add hw
  simp only [covariantAlong, hadd.deriv, hv.deriv, hw.deriv,
    tangentProjection_add]

theorem covariantAlong_leibniz (γ : ℝ → MatrixOrbit right left P)
    (V : ℝ → Mat n) (a : ℝ → ℝ) {v : Mat n} {a' t : ℝ}
    (hv : HasDerivAt V v t) (ha : HasDerivAt a a' t) :
    covariantAlong right left P γ (fun s => a s • V s) t =
      a' • tangentProjection right left P (γ t) (V t) +
        a t • covariantAlong right left P γ V t := by
  have hsmul : HasDerivAt (fun s => a s • V s) (a t • v + a' • V t) t := by
    simpa only [Pi.smul_def'] using ha.smul hv
  simp only [covariantAlong, hsmul.deriv, hv.deriv,
    tangentProjection_add, tangentProjection_smul]
  exact add_comm _ _

/-- Metric compatibility for actual differentiable ambient representatives of
fields tangent to the shared orbit. Only tangency at the evaluation point is
needed for this pointwise identity. -/
theorem covariantAlong_metric_compatible (γ : ℝ → MatrixOrbit right left P)
    (V W : ℝ → Mat n) {v w : Mat n} {t : ℝ}
    (hv : HasDerivAt V v t) (hw : HasDerivAt W w t)
    (htV : V t ∈ pointDirections right left (γ t).val)
    (htW : W t ∈ pointDirections right left (γ t).val) :
    HasDerivAt (fun s => frobInner (V s) (W s))
      (frobInner (inclusionDifferential right left P (γ t)
          (covariantAlong right left P γ V t)) (W t) +
       frobInner (V t) (inclusionDifferential right left P (γ t)
          (covariantAlong right left P γ W t))) t := by
  have hpV := pointProjection_of_mem (right := right) (left := left) (γ t).val (V t) htV
  have hpW := pointProjection_of_mem (right := right) (left := left) (γ t).val (W t) htW
  have h₁ : frobInner (pointProjection right left (γ t).val v) (W t) =
      frobInner v (W t) := by
    rw [pointProjection_self_adjoint, hpW]
  have h₂ : frobInner (V t) (pointProjection right left (γ t).val w) =
      frobInner (V t) w := by
    rw [← pointProjection_self_adjoint, hpV]
  simpa only [inclusion_covariantAlong, hv.deriv, hw.deriv, h₁, h₂] using
    GS.GlobalGeometry.hasDerivAt_frobInner hv hw

end GS.SharedGeometry
