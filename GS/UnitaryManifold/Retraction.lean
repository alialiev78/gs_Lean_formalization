module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

public import GS.UnitaryManifold.TangentBridge
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A smooth retraction on every fixed unitary tangent fibre

The preferred horizontal Cayley parametrization is globally defined in its
coordinate vector and has the correct derivative at the centre. It therefore
gives a retraction from each actual tangent fibre. All smoothness statements
keep the base point fixed. No smooth dependence of the chosen preferred
factorization on the base point, or total tangent-bundle retraction, is asserted.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS Matrix GS.UnitaryGeometry GS.OverlapGeometry
open scoped Topology Manifold
namespace GS.UnitaryManifold
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance retractionHorizontalNormedAddCommGroup :
    NormedAddCommGroup (HorizontalModel b₁ b₂ σ) := inferInstance
local instance retractionHorizontalNormedSpace :
    NormedSpace ℝ (HorizontalModel b₁ b₂ σ) := Submodule.normedSpace _
local instance retractionChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance retractionIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- The globally defined horizontal Cayley parametrization of a fixed tangent fibre. -/
def fibreRetraction (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    MatrixOrbit b₁ b₂ (cPermMatrix σ) :=
  (preferredOrbitSlice b₁ b₂ σ X).parametrization v

@[simp] theorem fibreRetraction_val (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    (fibreRetraction b₁ b₂ σ X v).val = preferredFactor σ X • horizontalValue b₁ b₂ σ v := rfl

@[simp] theorem fibreRetraction_zero (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    fibreRetraction b₁ b₂ σ X 0 = X := by
  have hh := (preferredOrbitSlice b₁ b₂ σ X).left_inverse X
    (preferredOrbitSlice_covers b₁ b₂ σ X)
  rw [preferredOrbitSlice_coordinates_zero] at hh
  exact hh

theorem fibreRetraction_ambient_contDiff (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    ContDiff ℝ ⊤ (fun v : HorizontalModel b₁ b₂ σ => (fibreRetraction b₁ b₂ σ X v).val) :=
  (preferredOrbitSlice b₁ b₂ σ X).parametrization_smooth

theorem fibreRetraction_contMDiff (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    ContMDiff (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
      (fun v : HorizontalModel b₁ b₂ σ => fibreRetraction b₁ b₂ σ X v) :=
  (overlap_contMDiff_iff_contDiff b₁ b₂ σ _).mpr
    (fibreRetraction_ambient_contDiff b₁ b₂ σ X)

/-- The ambient differential of the retraction is precisely the tangent inclusion. -/
theorem fibreRetraction_ambient_fderiv_zero (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    fderiv ℝ (fun v : HorizontalModel b₁ b₂ σ => (fibreRetraction b₁ b₂ σ X v).val) 0 =
      mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, CMat n))
        (fun Y : MatrixOrbit b₁ b₂ (cPermMatrix σ) => Y.val) X := by
  simpa only [fibreRetraction_val] using (overlap_val_mfderiv_eq b₁ b₂ σ X).symm

set_option maxHeartbeats 800000 in
/-- The intrinsic derivative at zero is the identity on the actual tangent fibre. -/
theorem fibreRetraction_mfderiv_zero_apply
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) (v : HorizontalModel b₁ b₂ σ) :
    @Eq (HorizontalModel b₁ b₂ σ)
      (mfderiv (M := HorizontalModel b₁ b₂ σ) (M' := MatrixOrbit b₁ b₂ (cPermMatrix σ))
        (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
        (fun w : HorizontalModel b₁ b₂ σ => fibreRetraction b₁ b₂ σ X w)
        (0 : HorizontalModel b₁ b₂ σ) v) v := by
  apply overlap_val_mfderiv_injective b₁ b₂ σ X
  have hi := (overlap_val_contMDiff b₁ b₂ σ).mdifferentiable (by simp)
  have hr := (fibreRetraction_contMDiff b₁ b₂ σ X).mdifferentiable (by simp)
  have hc := mfderiv_comp_apply_of_eq (0 : HorizontalModel b₁ b₂ σ)
    (hi X) (hr 0) (fibreRetraction_zero b₁ b₂ σ X) v
  have he : mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, CMat n))
      (fun w : HorizontalModel b₁ b₂ σ => (fibreRetraction b₁ b₂ σ X w).val) 0 =
      mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, CMat n))
        (fun Y : MatrixOrbit b₁ b₂ (cPermMatrix σ) => Y.val) X := by
    rw [mfderiv_eq_fderiv]
    exact fibreRetraction_ambient_fderiv_zero b₁ b₂ σ X
  have hev := congrArg
    (fun D : HorizontalModel b₁ b₂ σ →L[ℝ] CMat n => D v) he
  exact hc.symm.trans hev

theorem fibreRetraction_mfderiv_zero (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    mfderiv (M := HorizontalModel b₁ b₂ σ) (M' := MatrixOrbit b₁ b₂ (cPermMatrix σ))
      (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (fun v : HorizontalModel b₁ b₂ σ => fibreRetraction b₁ b₂ σ X v)
      (0 : HorizontalModel b₁ b₂ σ) = ContinuousLinearMap.id ℝ (HorizontalModel b₁ b₂ σ) := by
  apply ContinuousLinearMap.ext
  intro v
  exact fibreRetraction_mfderiv_zero_apply b₁ b₂ σ X v

/-- Every actual tangent vector is realized by a globally feasible smooth curve. -/
theorem fibreRetraction_curve_velocity (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    HasDerivAt (fun t : ℝ => (fibreRetraction b₁ b₂ σ X (t • v)).val)
      (mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, CMat n))
        (fun Y : MatrixOrbit b₁ b₂ (cPermMatrix σ) => Y.val) X v) 0 := by
  have hp := ((fibreRetraction_ambient_contDiff b₁ b₂ σ X).differentiable (by simp) 0).hasFDerivAt
  rw [fibreRetraction_ambient_fderiv_zero] at hp
  have hl : HasDerivAt (fun t : ℝ => t • (v : HorizontalModel b₁ b₂ σ))
      (v : HorizontalModel b₁ b₂ σ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (F := HorizontalModel b₁ b₂ σ) v
  exact hp.comp_hasDerivAt_of_eq 0 hl (by simp)

end GS.UnitaryManifold
