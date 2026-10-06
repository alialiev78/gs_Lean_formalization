module

public import GS.UnitarySharing.BundleRetraction
public import GS.UnitarySharing.Gradient
public import GS.Extensions.TangentSections

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Smooth intrinsic gradient sections and the exact shared gradient update

The target here is the actual tangent bundle, not only the matrix realization
of a vector field. To avoid assuming a smooth inverse to the inclusion
differential, we differentiate the smooth map F(X,Z) = R_X(proj_X Z) in its
ambient second variable at zero. This constructs the bundled tangent projector
from mathlib's genuine tangent map. No gradient-section regularity is assumed
in proving the smoothness of F: its matrix value is an explicit Cayley formula.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
open scoped Topology Manifold ContDiff
namespace GS.UnitarySharing
variable {n : ℕ} (right left : Pattern n) (P : CMat n)
local instance gradientSectionNormedSpace : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _
local instance gradientSectionChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
local instance gradientSectionIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
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
  cayleyFibreRetraction right left P p.1 (tangentProjection right left P p.1 p.2)

@[simp] theorem ambientRetraction_val (X : MatrixOrbit right left P) (Z : CMat n) :
    (ambientRetraction right left P (X, Z)).val =
      sharedCayleyValue right left X.val Z 1 := by
  change sharedCayleyValue right left X.val
    (inclusionDifferential right left P X (tangentProjection right left P X Z)) 1 = _
  rw [inclusion_tangentProjection]
  exact sharedCayleyValue_projected X.val Z 1

@[simp] theorem ambientRetraction_zero (X : MatrixOrbit right left P) :
    ambientRetraction right left P (X, 0) = X := by
  simp [ambientRetraction]

-- Preserve the abstract subspace interfaces during elaboration. Their defining
-- terms need not be expanded when comparing manifold and normed-space instances.
attribute [local irreducible] sharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

set_option maxHeartbeats 800000 in
/-- This proof uses the matrix formula and hence is independent of the desired
smoothness of the tangent projection as a section. -/
theorem ambientRetraction_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, HorizontalModel right left P)) ⊤ (ambientRetraction right left P) := by
  apply (sharedOrbit_contMDiff_iff_ambient right left P
    ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
    (ambientRetraction right left P)).mpr
  have hb : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, CMat n)) ⊤ (fun p : MatrixOrbit right left P × CMat n => p.1.val) :=
    ContMDiff.comp
      (g := fun X : MatrixOrbit right left P => X.val)
      (f := fun p : MatrixOrbit right left P × CMat n => p.1)
      (sharedOrbit_val_contMDiff right left P) contMDiff_fst
  have hl := minimumNormLift_contMDiff right left P
  have h := (generatorCayleyValue_smooth right left).comp_contMDiff
    (hb.prodMk_space (hl.prodMk_space (contMDiff_const (c := (1 : ℝ)))))
  have he : (fun p : MatrixOrbit right left P × CMat n =>
      (ambientRetraction right left P p).val) =
      (fun p : MatrixOrbit right left P × CMat n =>
        sharedCayleyValue right left p.1.val p.2 1) := by
    funext p
    rcases p with ⟨X, Z⟩
    exact ambientRetraction_val right left P X Z
  rw [he]
  exact h

/-- Actual partial manifold derivative in the ambient-vector input. -/
theorem ambientRetraction_partial_mfderiv (X : MatrixOrbit right left P) (Z : CMat n) :
    @Eq (HorizontalModel right left P)
      (mfderiv (𝓘(ℝ, CMat n)) (𝓘(ℝ, HorizontalModel right left P))
        (fun W : CMat n => ambientRetraction right left P (X, W)) 0 Z)
      (tangentProjection right left P X Z) := by
  exact GS.Extensions.mfderiv_retraction_precompose_linear
    (𝓘(ℝ, HorizontalModel right left P)) (cayleyFibreRetraction right left P X)
    (tangentProjectionCLM right left P X)
    ((cayleyFibreRetraction_contMDiff right left P X).mdifferentiable (by simp) 0)
    (cayleyFibreRetraction_mfderiv_zero right left P X) Z

/-- The same partial derivative written as the full derivative on a vertical vector. -/
theorem ambientRetraction_vertical_mfderiv (X : MatrixOrbit right left P) (Z : CMat n) :
    @Eq (HorizontalModel right left P)
      (mfderiv ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
        (𝓘(ℝ, HorizontalModel right left P)) (ambientRetraction right left P)
        (X, (0 : CMat n)) ((0 : HorizontalModel right left P), Z))
      (tangentProjection right left P X Z) := by
  have h := GS.Extensions.mfderiv_partial_right
    (𝓘(ℝ, HorizontalModel right left P)) (ambientRetraction right left P) X
    ((ambientRetraction_contMDiff right left P).mdifferentiable (by simp) (X, 0)) Z
  exact h.symm.trans (ambientRetraction_partial_mfderiv right left P X Z)

/-- Smooth vertical vector at (X,0), with ambient input Z. -/
def projectionVerticalInput (p : MatrixOrbit right left P × CMat n) :
    TangentBundle ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (MatrixOrbit right left P × CMat n) :=
  ⟨(p.1, 0), (0, p.2)⟩

theorem projectionVerticalInput_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n))).tangent ⊤
      (projectionVerticalInput right left P) := by
  exact GS.Extensions.contMDiff_vertical_input
    (M := MatrixOrbit right left P) (V := CMat n) (𝓘(ℝ, HorizontalModel right left P))

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
    ambientRetraction_vertical_mfderiv]
  congr 1
  exact (ambientRetraction_zero right left P X).symm

set_option maxHeartbeats 800000 in
/-- Joint smoothness of the actual tangent lift, including its varying base. -/
theorem tangentProjectionBundle_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, HorizontalModel right left P)).tangent ⊤
      (tangentProjectionBundle right left P) := by
  have he : tangentProjectionBundle right left P =
      tangentMap ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
        (𝓘(ℝ, HorizontalModel right left P)) (ambientRetraction right left P) ∘
        projectionVerticalInput right left P := by
    funext p
    exact tangentProjectionBundle_eq_tangentMap right left P p
  rw [he]
  exact ((ambientRetraction_contMDiff right left P).contMDiff_tangentMap (by simp)).comp
    (projectionVerticalInput_contMDiff right left P)

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
  have hg : ContDiff ℝ r (ambientGradient f) := ambientGradient_contDiff_of_loss f hf hrs
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
  cayleyRetraction right left P ⟨p.1, (-p.2) • intrinsicGradient right left P f p.1⟩

theorem gradientUpdate_eq_ambientRetraction (f : CMat n → ℝ)
    (p : MatrixOrbit right left P × ℝ) :
    gradientUpdate right left P f p =
      ambientRetraction right left P (p.1, (-p.2) • ambientGradient f p.1.val) := by
  simp only [gradientUpdate, ambientRetraction, tangentProjection_smul,
    intrinsicGradient, cayleyRetraction]

/-- Joint regularity of the exact fixed-step update, with the expected loss of
one derivative from the loss. A discrete line-search selector need not be smooth. -/
theorem gradientUpdate_contMDiff_of_order (f : CMat n → ℝ) {r s : WithTop ℕ∞}
    (hf : ContDiff ℝ s f) (hrs : r + 1 ≤ s) :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, HorizontalModel right left P)) r (gradientUpdate right left P f) := by
  have hg : ContDiff ℝ r (ambientGradient f) := ambientGradient_contDiff_of_loss f hf hrs
  have ha : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, CMat n)) r
      (fun p : MatrixOrbit right left P × ℝ => ambientGradient f p.1.val) := hg.comp_contMDiff
    (((sharedOrbit_val_contMDiff right left P).of_le le_top).comp contMDiff_fst)
  have hargs : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n))) r
      (fun p : MatrixOrbit right left P × ℝ =>
        (p.1, (-p.2) • ambientGradient f p.1.val)) :=
    contMDiff_fst.prodMk (contMDiff_snd.neg.smul ha)
  have h := ContMDiff.comp
    (g := ambientRetraction right left P)
    (f := fun p : MatrixOrbit right left P × ℝ =>
      (p.1, (-p.2) • ambientGradient f p.1.val))
    ((ambientRetraction_contMDiff right left P).of_le le_top) hargs
  simpa only [Function.comp_def, ← gradientUpdate_eq_ambientRetraction] using h

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

end GS.UnitarySharing
