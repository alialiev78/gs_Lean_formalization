module

public import GS.SpecialUnitarySharing.TangentBridge
public import GS.SpecialUnitarySharing.SmoothProjection
public import GS.SpecialUnitarySharing.SmoothLift
public import GS.SpecialUnitarySharing.ExponentialStep
public import GS.UnitarySharing.TangentBridge

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Smooth SU geometry on the actual special-unitary orbit

The separately constructed SU atlas makes its inclusion in the surrounding U
orbit smooth. Restricting the previously proved U-orbit extensions now gives
smooth projector, canonical lift, and exponential update on the true SU base.
The inclusion is not an identification of the two orbits or tangent spaces.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
open scoped Topology Manifold
namespace GS.SpecialUnitarySharing
open GS.SpecialUnitarySharing.Orbit
variable {n : ℕ} (right left : Pattern n) (P : CMat n)
local instance : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _
local instance : ChartedSpace (HorizontalModel right left P) (MatrixOrbit right left P) :=
  sharedOrbitChartedSpace right left P
local instance : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤ (MatrixOrbit right left P) :=
  sharedOrbitIsManifold right left P
local instance : ChartedSpace (GS.UnitarySharing.HorizontalModel right left P)
    (GS.UnitarySharing.MatrixOrbit right left P) :=
  GS.UnitarySharing.sharedOrbitChartedSpace right left P
local instance : IsManifold (𝓘(ℝ, GS.UnitarySharing.HorizontalModel right left P)) ⊤
    (GS.UnitarySharing.MatrixOrbit right left P) :=
  GS.UnitarySharing.sharedOrbitIsManifold right left P

/-- Smooth inclusion of the smaller SU orbit with its own atlas. -/
theorem toUnitaryOrbit_contMDiff :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P))
      (𝓘(ℝ, GS.UnitarySharing.HorizontalModel right left P)) ⊤
      (toUnitaryOrbit (right := right) (left := left) P) := by
  apply (GS.UnitarySharing.sharedOrbit_contMDiff_iff_ambient right left P
    (𝓘(ℝ, HorizontalModel right left P)) _).mpr
  simpa only [toUnitaryOrbit_val] using sharedOrbit_val_contMDiff right left P

/-- Joint smoothness on the genuine SU orbit, including continuous stabilizers. -/
theorem pointProjection_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, CMat n)) ⊤
      (fun p : MatrixOrbit right left P × CMat n => pointProjection right left p.1.val p.2) := by
  have hi : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      ((𝓘(ℝ, GS.UnitarySharing.HorizontalModel right left P)).prod (𝓘(ℝ, CMat n))) ⊤
      (fun p : MatrixOrbit right left P × CMat n => (toUnitaryOrbit P p.1, p.2)) :=
    ((toUnitaryOrbit_contMDiff right left P).comp contMDiff_fst).prodMk contMDiff_snd
  simpa only [Function.comp_def, toUnitaryOrbit_val] using
    (pointProjection_contMDiff_on_unitary_orbit right left P).comp hi

/-- The minimum physical Frobenius norm lift is smooth on the smaller base. -/
theorem minimumNormLift_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, PairGenerator right left)) ⊤
      (fun p : MatrixOrbit right left P × CMat n => minimumNormLift right left p.1.val p.2) := by
  have hi : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      ((𝓘(ℝ, GS.UnitarySharing.HorizontalModel right left P)).prod (𝓘(ℝ, CMat n))) ⊤
      (fun p : MatrixOrbit right left P × CMat n => (toUnitaryOrbit P p.1, p.2)) :=
    ((toUnitaryOrbit_contMDiff right left P).comp contMDiff_fst).prodMk contMDiff_snd
  simpa only [Function.comp_def, toUnitaryOrbit_val] using
    (minimumNormLift_contMDiff_on_unitary_orbit right left P).comp hi

/-- Smooth finite update as a matrix-valued map on the actual SU base. -/
theorem expStep_contMDiff :
    ContMDiff (((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, CMat n)) ⊤
      (fun p : (MatrixOrbit right left P × CMat n) × ℝ =>
        expStep right left p.1.1.val p.1.2 p.2) := by
  have hi : ContMDiff
      (((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n))).prod (𝓘(ℝ, ℝ)))
      (((𝓘(ℝ, GS.UnitarySharing.HorizontalModel right left P)).prod (𝓘(ℝ, CMat n))).prod (𝓘(ℝ, ℝ))) ⊤
      (fun p : (MatrixOrbit right left P × CMat n) × ℝ =>
        ((toUnitaryOrbit P p.1.1, p.1.2), p.2)) :=
    (((toUnitaryOrbit_contMDiff right left P).comp
      (contMDiff_fst.comp contMDiff_fst)).prodMk
      (contMDiff_snd.comp contMDiff_fst)).prodMk contMDiff_snd
  simpa only [Function.comp_def, toUnitaryOrbit_val] using
    (expStep_contMDiff_on_unitary_orbit right left P).comp hi

/-- Fixed-base smoothness holds for every ambient matrix, independently of any atlas. -/
theorem expStep_fixed_smooth (X : CMat n) :
    ContDiff ℝ ⊤ (fun p : CMat n × ℝ => expStep right left X p.1 p.2) := by
  have hlift : ContDiff ℝ ⊤ (fun p : CMat n × ℝ => minimumNormLift right left X p.1) :=
    (minimumNormLift right left X).contDiff.comp contDiff_fst
  have hA := (specialSkewSpace left).subtypeL.contDiff.comp hlift.fst
  have hB := (specialSkewSpace right).subtypeL.contDiff.comp hlift.snd
  have heA := cMatrixExp_contDiff.comp (contDiff_snd.smul hA)
  have heB := cMatrixExp_contDiff.comp (contDiff_snd.smul hB)
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact smooth_mul_at (smooth_mul_at heA.contDiffAt contDiffAt_const) heB.contDiffAt

/-- Membership in the genuine SU orbit, without using the U atlas. -/
theorem expStep_mem_orbit (X : MatrixOrbit right left P) (Z : CMat n) (t : ℝ) :
    expStep right left X.val Z t ∈ MulAction.orbit (SpecialFactors right left) P :=
  (orbitExpStep right left P X Z t).property

/-- The finite update is smooth also as a map into the SU orbit itself. -/
theorem orbitExpStep_contMDiff :
    ContMDiff (((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, HorizontalModel right left P)) ⊤
      (fun p : (MatrixOrbit right left P × CMat n) × ℝ =>
        orbitExpStep right left P p.1.1 p.1.2 p.2) := by
  apply (sharedOrbit_contMDiff_iff_ambient right left P _ _).mpr
  simpa only [orbitExpStep_val] using expStep_contMDiff right left P

end GS.SpecialUnitarySharing
