module

public import GS.SpecialUnitarySharing.BundleRetraction
public import GS.SpecialUnitarySharing.Gradient
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Smooth intrinsic gradient sections and the exact shared gradient update

The target here is the actual tangent bundle, not only the matrix realization
of a vector field. To avoid assuming a smooth inverse to the inclusion
differential, we differentiate the smooth map F(X,Z) = R_X(proj_X Z) in its
ambient second variable at zero. This constructs the bundled tangent projector
from mathlib's genuine tangent map. No gradient-section regularity is assumed
in proving the smoothness of F: its matrix value is an explicit exponential formula.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
open scoped Topology Manifold ContDiff
namespace GS.SpecialUnitarySharing
open GS.SpecialUnitarySharing.Orbit
variable {n : ℕ} (right left : Pattern n) (P : CMat n)
local instance : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _
local instance : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
local instance : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

/-- The already constructed pointwise tangent lift, as a continuous linear map. -/
def tangentProjectionCLM (X : MatrixOrbit right left P) :
    CMat n →L[ℝ] HorizontalModel right left P :=
  ({ toFun := tangentProjection right left P X
     map_add' := tangentProjection_add right left P X
     map_smul' := tangentProjection_smul right left P X
   } : CMat n →ₗ[ℝ] HorizontalModel right left P).toContinuousLinearMap

@[simp] theorem tangentProjectionCLM_apply (X : MatrixOrbit right left P) (Z : CMat n) :
    tangentProjectionCLM right left P X Z = tangentProjection right left P X Z := rfl

/-- Ambient-input extension of the retraction, still valued in the exact orbit. -/
def ambientRetraction (p : MatrixOrbit right left P × CMat n) :
    MatrixOrbit right left P :=
  expFibreRetraction right left P p.1 (tangentProjection right left P p.1 p.2)

@[simp] theorem ambientRetraction_val (X : MatrixOrbit right left P) (Z : CMat n) :
    (ambientRetraction right left P (X, Z)).val =
      expStep right left X.val Z 1 := by
  change expStep right left X.val
    (inclusionDifferential right left P X (tangentProjection right left P X Z)) 1 = _
  rw [inclusion_tangentProjection]
  exact expStep_projected right left X.val Z 1

@[simp] theorem ambientRetraction_zero (X : MatrixOrbit right left P) :
    ambientRetraction right left P (X, 0) = X := by
  simp [ambientRetraction]

/-- This proof uses the matrix formula and hence is independent of the desired
smoothness of the tangent projection as a section. -/
theorem ambientRetraction_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, HorizontalModel right left P)) ⊤ (ambientRetraction right left P) := by
  apply (sharedOrbit_contMDiff_iff_ambient right left P
    ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
    (ambientRetraction right left P)).mpr
  have hargs : ContMDiff
      ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n))).prod (𝓘(ℝ, ℝ))) ⊤
      (fun p : MatrixOrbit right left P × CMat n => (p, (1 : ℝ))) :=
    contMDiff_id.prodMk contMDiff_const
  have h := (expStep_contMDiff right left P).comp hargs
  simpa only [ambientRetraction_val] using h

/-- Actual partial manifold derivative in the ambient-vector input. -/
theorem ambientRetraction_partial_mfderiv (X : MatrixOrbit right left P) (Z : CMat n) :
    @Eq (HorizontalModel right left P)
      (mfderiv (𝓘(ℝ, CMat n)) (𝓘(ℝ, HorizontalModel right left P))
        (fun W : CMat n => ambientRetraction right left P (X, W)) 0 Z)
      (tangentProjection right left P X Z) := by
  have hr := (expFibreRetraction_contMDiff right left P X).mdifferentiable (by simp)
  have hc := mfderiv_comp_apply_of_eq (0 : CMat n) (hr 0)
    (tangentProjectionCLM right left P X).mdifferentiableAt
    (map_zero (tangentProjectionCLM right left P X)) Z
  simpa only [Function.comp_def, ambientRetraction, tangentProjectionCLM_apply,
    ContinuousLinearMap.mfderiv_eq, expFibreRetraction_mfderiv_zero,
    ContinuousLinearMap.id_apply] using hc

/-- The same partial derivative written as the full derivative on a vertical vector. -/
theorem ambientRetraction_vertical_mfderiv (X : MatrixOrbit right left P) (Z : CMat n) :
    @Eq (HorizontalModel right left P)
      (mfderiv ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
        (𝓘(ℝ, HorizontalModel right left P)) (ambientRetraction right left P)
        (X, (0 : CMat n)) ((0 : HorizontalModel right left P), Z))
      (tangentProjection right left P X Z) := by
  have he : MDifferentiableAt (𝓘(ℝ, CMat n))
      ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (fun W : CMat n => (X, W)) 0 :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hf := (ambientRetraction_contMDiff right left P).mdifferentiable (by simp)
  have hc := mfderiv_comp_apply_of_eq (0 : CMat n) (hf (X, 0)) he rfl Z
  rw [mfderiv_prod_right] at hc
  exact hc.symm.trans (ambientRetraction_partial_mfderiv right left P X Z)

/-- Smooth vertical vector at (X,0), with ambient input Z. -/
def projectionVerticalInput (p : MatrixOrbit right left P × CMat n) :
    TangentBundle ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (MatrixOrbit right left P × CMat n) :=
  ⟨(p.1, 0), (0, p.2)⟩

set_option maxHeartbeats 1000000 in
theorem projectionVerticalInput_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n))).tangent ⊤
      (projectionVerticalInput right left P) := by
  have hzero : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, HorizontalModel right left P)).tangent ⊤
      (fun p : MatrixOrbit right left P × CMat n =>
        (⟨p.1, 0⟩ : TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P))) :=
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace (𝓘(ℝ, HorizontalModel right left P)))).comp
      contMDiff_fst
  have hvector : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, CMat n)).tangent ⊤
      (fun p : MatrixOrbit right left P × CMat n =>
        (⟨0, p.2⟩ : TangentBundle (𝓘(ℝ, CMat n)) (CMat n))) :=
    (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, CMat n))).comp
      (contMDiff_const.prodMk contMDiff_snd)
  exact (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(ℝ, HorizontalModel right left P)) (I' := 𝓘(ℝ, CMat n))
    (M := MatrixOrbit right left P) (M' := CMat n)).comp (hzero.prodMk hvector)

/-- The projected ambient vector as an element of the TRUE total tangent bundle. -/
def tangentProjectionBundle (p : MatrixOrbit right left P × CMat n) :
    TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P) :=
  ⟨p.1, tangentProjection right left P p.1 p.2⟩

theorem tangentProjectionBundle_eq_tangentMap (p : MatrixOrbit right left P × CMat n) :
    tangentProjectionBundle right left P p =
      tangentMap ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
        (𝓘(ℝ, HorizontalModel right left P)) (ambientRetraction right left P)
        (projectionVerticalInput right left P p) := by
  rcases p with ⟨X, Z⟩
  simp only [tangentProjectionBundle, projectionVerticalInput, tangentMap,
    ambientRetraction_vertical_mfderiv, ambientRetraction_zero]

/-- Joint smoothness of the actual tangent lift, including its varying base. -/
theorem tangentProjectionBundle_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, HorizontalModel right left P)).tangent ⊤
      (tangentProjectionBundle right left P) := by
  have h := ((ambientRetraction_contMDiff right left P).contMDiff_tangentMap (by simp)).comp
    (projectionVerticalInput_contMDiff right left P)
  simpa only [← tangentProjectionBundle_eq_tangentMap] using h

/-- The intrinsic gradient as a section of mathlib's actual tangent bundle. -/
def intrinsicGradientSection (f : CMat n → ℝ) (X : MatrixOrbit right left P) :
    TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P) :=
  ⟨X, intrinsicGradient right left P f X⟩

@[simp] theorem intrinsicGradientSection_proj (f : CMat n → ℝ) (X : MatrixOrbit right left P) :
    (intrinsicGradientSection right left P f X).proj = X := rfl

/-- Finite, smooth and analytic regularity for the ACTUAL gradient section.
Only the loss regularity is an input; the varying-base tangent lift is constructed. -/
theorem intrinsicGradientSection_contMDiff_of_order (f : CMat n → ℝ) {r s : WithTop ℕ∞}
    (hf : ContDiff ℝ s f) (hrs : r + 1 ≤ s) :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P))
      (𝓘(ℝ, HorizontalModel right left P)).tangent r
      (intrinsicGradientSection right left P f) := by
  have hg : ContDiff ℝ r (ambientGradient f) := GS.UnitarySharing.ambientGradient_contDiff_of_loss f hf hrs
  have hpair : ContMDiff (𝓘(ℝ, HorizontalModel right left P))
      ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n))) r
      (fun X : MatrixOrbit right left P => (X, ambientGradient f X.val)) :=
    contMDiff_id.prodMk
      (hg.comp_contMDiff ((sharedOrbit_val_contMDiff right left P).of_le le_top))
  exact ((tangentProjectionBundle_contMDiff right left P).of_le le_top).comp hpair

/-- Analytic-order version, consistent with the original top-order APIs. -/
theorem intrinsicGradientSection_contMDiff (f : CMat n → ℝ) (hf : ContDiff ℝ ⊤ f) :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P))
      (𝓘(ℝ, HorizontalModel right left P)).tangent ⊤
      (intrinsicGradientSection right left P f) :=
  intrinsicGradientSection_contMDiff_of_order right left P f hf (by simp)

/-- A genuinely C-infinity loss suffices; analyticity is not required. -/
theorem intrinsicGradientSection_smooth (f : CMat n → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P))
      (𝓘(ℝ, HorizontalModel right left P)).tangent ∞
      (intrinsicGradientSection right left P f) :=
  intrinsicGradientSection_contMDiff_of_order right left P f hf (by simp)

/-- Exact gradient step with arbitrary real step size. Feasibility is automatic. -/
def gradientUpdate (f : CMat n → ℝ) (p : MatrixOrbit right left P × ℝ) :
    MatrixOrbit right left P :=
  expRetraction right left P ⟨p.1, (-p.2) • intrinsicGradient right left P f p.1⟩

theorem gradientUpdate_eq_ambientRetraction (f : CMat n → ℝ)
    (p : MatrixOrbit right left P × ℝ) :
    gradientUpdate right left P f p =
      ambientRetraction right left P (p.1, (-p.2) • ambientGradient f p.1.val) := by
  simp only [gradientUpdate, ambientRetraction, tangentProjection_smul,
    intrinsicGradient, expRetraction]

/-- Joint regularity of the exact fixed-step update, with the expected loss of
one derivative from the loss. A discrete line-search selector need not be smooth. -/
theorem gradientUpdate_contMDiff_of_order (f : CMat n → ℝ) {r s : WithTop ℕ∞}
    (hf : ContDiff ℝ s f) (hrs : r + 1 ≤ s) :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, HorizontalModel right left P)) r (gradientUpdate right left P f) := by
  have hg : ContDiff ℝ r (ambientGradient f) := GS.UnitarySharing.ambientGradient_contDiff_of_loss f hf hrs
  have ha := hg.comp_contMDiff
    (((sharedOrbit_val_contMDiff right left P).of_le le_top).comp contMDiff_fst)
  have h := ((ambientRetraction_contMDiff right left P).of_le le_top).comp
    (contMDiff_fst.prodMk (contMDiff_snd.neg.smul ha))
  simpa only [← gradientUpdate_eq_ambientRetraction] using h

/-- Analytic-order fixed-step update; no convergence theorem is asserted. -/
theorem gradientUpdate_contMDiff (f : CMat n → ℝ) (hf : ContDiff ℝ ⊤ f) :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, HorizontalModel right left P)) ⊤ (gradientUpdate right left P f) :=
  gradientUpdate_contMDiff_of_order right left P f hf (by simp)

/-- Smooth fixed-step update for an arbitrary C-infinity ambient loss. -/
theorem gradientUpdate_smooth (f : CMat n → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, HorizontalModel right left P)) ∞ (gradientUpdate right left P f) :=
  gradientUpdate_contMDiff_of_order right left P f hf (by simp)

@[simp] theorem gradientUpdate_zero (f : CMat n → ℝ) (X : MatrixOrbit right left P) :
    gradientUpdate right left P f (X, 0) = X := by
  simp [gradientUpdate]

end GS.SpecialUnitarySharing
