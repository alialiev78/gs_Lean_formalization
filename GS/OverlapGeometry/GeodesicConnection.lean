module

public import GS.OverlapGeometry.GeodesicDynamics
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Metric compatibility and symmetric Christoffel coefficients

The projected derivative uses the actual tangent fibres and their Frobenius
metric. In the preferred horizontal coordinates, its Christoffel coefficients
come from the genuine second Frechet derivative of the inverse chart. Schwarz's
theorem proves symmetry. A differentiated coordinate metric proves metric
compatibility. These are the local Levi-Civita characterization identities;
registration as a global bundled mathlib connection is a separate interface.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.GlobalGeometry
open GS.LieAction GS.CayleyCharts GS.ManifoldCompletion
open scoped Topology Manifold
namespace GS.OverlapGeometry

variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance connectionHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance connectionChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance connectionIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- Preferred inverse-chart ambient formula, extended by the Cayley expression. -/
def coordinateInclusion (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (h : HorizontalModel b₁ b₂ σ) : Mat n :=
  preferredFactor σ X • horizontalValue b₁ b₂ σ h

theorem coordinateInclusion_smooth (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    ContDiff ℝ ⊤ (coordinateInclusion b₁ b₂ σ X) :=
  (fixed_action_smooth (preferredFactor σ X)).comp (horizontalValue_smooth b₁ b₂ σ)

theorem coordinateInclusion_fderiv (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    fderiv ℝ (coordinateInclusion b₁ b₂ σ X) 0 = inclusionDifferential b₁ b₂ σ X :=
  (overlap_val_mfderiv_eq b₁ b₂ σ X).symm

/-- Christoffel values in the actual tangent fibre, computed from the inverse chart. -/
def coordinateChristoffel (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (u v : HorizontalModel b₁ b₂ σ) :
    TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X :=
  tangentProjection b₁ b₂ σ X
    (fderiv ℝ (fderiv ℝ (coordinateInclusion b₁ b₂ σ X)) 0 u v)

/-- The coordinate torsion vanishes because actual mixed second derivatives commute. -/
theorem coordinateChristoffel_symmetric (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (u v : HorizontalModel b₁ b₂ σ) :
    coordinateChristoffel b₁ b₂ σ X u v = coordinateChristoffel b₁ b₂ σ X v u := by
  unfold coordinateChristoffel
  congr 1
  exact ((coordinateInclusion_smooth b₁ b₂ σ X).contDiffAt.isSymmSndFDerivAt
    (by simp)) u v

theorem coordinateChristoffel_pairing (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (u v w : HorizontalModel b₁ b₂ σ) :
    tangentPairing b₁ b₂ σ X (coordinateChristoffel b₁ b₂ σ X u v) w =
      frobInner (fderiv ℝ (fderiv ℝ (coordinateInclusion b₁ b₂ σ X)) 0 u v)
        (fderiv ℝ (coordinateInclusion b₁ b₂ σ X) 0 w) := by
  rw [coordinateInclusion_fderiv]
  exact tangentProjection_pairing b₁ b₂ σ X _ w

private theorem secondDerivative_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → Mat n) (hφ : ContDiff ℝ ⊤ φ) (u v w : E) :
    HasDerivAt (fun t : ℝ =>
      frobInner (fderiv ℝ φ (t • u) v) (fderiv ℝ φ (t • u) w))
      (frobInner (fderiv ℝ (fderiv ℝ φ) 0 u v) (fderiv ℝ φ 0 w) +
        frobInner (fderiv ℝ φ 0 v) (fderiv ℝ (fderiv ℝ φ) 0 u w)) 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) 0 :=
    ((hφ.contDiffAt.fderiv_right
      (m := (1 : WithTop ℕ∞)) (by simp)).differentiableAt (by simp))
  have hline : HasDerivAt (fun t : ℝ => t • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have hf : HasDerivAt (fun t : ℝ => fderiv ℝ φ (t • u))
      (fderiv ℝ (fderiv ℝ φ) 0 u) 0 := by
    have hd' : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) 0) ((0 : ℝ) • u) := by
      simpa only [zero_smul] using hd.hasFDerivAt
    exact hd'.comp_hasDerivAt 0 hline
  have hv : HasDerivAt (fun t : ℝ => fderiv ℝ φ (t • u) v)
      (fderiv ℝ (fderiv ℝ φ) 0 u v) 0 := by
    simpa using hf.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hw : HasDerivAt (fun t : ℝ => fderiv ℝ φ (t • u) w)
      (fderiv ℝ (fderiv ℝ φ) 0 u w) 0 := by
    simpa using hf.clm_apply (hasDerivAt_const (0 : ℝ) w)
  simpa only [zero_smul] using hasDerivAt_frobInner hv hw

theorem coordinateMetric_hasDerivAt (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (u v w : HorizontalModel b₁ b₂ σ) :
    HasDerivAt (fun t : ℝ =>
      frobInner (fderiv ℝ (coordinateInclusion b₁ b₂ σ X) (t • u) v)
        (fderiv ℝ (coordinateInclusion b₁ b₂ σ X) (t • u) w))
      (tangentPairing b₁ b₂ σ X (coordinateChristoffel b₁ b₂ σ X u v) w +
        tangentPairing b₁ b₂ σ X v (coordinateChristoffel b₁ b₂ σ X u w)) 0 := by
  rw [coordinateChristoffel_pairing,
    tangentPairing_symm b₁ b₂ σ X v (coordinateChristoffel b₁ b₂ σ X u w),
    coordinateChristoffel_pairing]
  rw [frobInner_comm (fderiv ℝ (fderiv ℝ (coordinateInclusion b₁ b₂ σ X)) 0 u w)]
  exact secondDerivative_metric (coordinateInclusion b₁ b₂ σ X)
    (coordinateInclusion_smooth b₁ b₂ σ X) u v w

/-- Metric compatibility for actual tangent fields, with their ambient derivatives. -/
theorem covariantAlong_metric_compatible
    (γ : ℝ → MatrixOrbit b₁ b₂ (permMatrix σ))
    (V W : (s : ℝ) → TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (γ s))
    {v w : Mat n} {t : ℝ}
    (hv : HasDerivAt (fun s => inclusionDifferential b₁ b₂ σ (γ s) (V s)) v t)
    (hw : HasDerivAt (fun s => inclusionDifferential b₁ b₂ σ (γ s) (W s)) w t) :
    HasDerivAt (fun s => tangentPairing b₁ b₂ σ (γ s) (V s) (W s))
      (tangentPairing b₁ b₂ σ (γ t)
        (covariantAlong b₁ b₂ σ γ (fun s => inclusionDifferential b₁ b₂ σ (γ s) (V s)) t)
        (W t) + tangentPairing b₁ b₂ σ (γ t) (V t)
        (covariantAlong b₁ b₂ σ γ (fun s => inclusionDifferential b₁ b₂ σ (γ s) (W s)) t)) t := by
  rw [covariantAlong_pairing,
    tangentPairing_symm b₁ b₂ σ (γ t) (V t),covariantAlong_pairing,hv.deriv,hw.deriv]
  rw [frobInner_comm w (inclusionDifferential b₁ b₂ σ (γ t) (V t))]
  exact hasDerivAt_frobInner hv hw

end GS.OverlapGeometry
