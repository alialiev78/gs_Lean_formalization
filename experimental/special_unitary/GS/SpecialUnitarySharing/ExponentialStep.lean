module

public import GS.SpecialUnitarySharing.Exponential
public import GS.SpecialUnitarySharing.Orbit
public import GS.SpecialUnitarySharing.MinimumNormLift
public import GS.SpecialUnitarySharing.SmoothLift
public import GS.SpecialUnitarySharing.SmoothProjection
public import GS.UnitaryManifold.MatrixCalculus

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# A point-only, exact SU shared update

The minimum physical-Frobenius-norm lift of the projected input is exponentiated.
The update preserves the genuine SU orbit, depends only on the point and its
projected direction, and has derivative equal to that direction. Joint smoothness
is proved even on the surrounding U orbit. The identification with the true SU
tangent bundle is established downstream in `TangentBridge` and `Retraction`.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
open scoped Topology Manifold
namespace GS.SpecialUnitarySharing
variable {n : ℕ} (right left : Pattern n)

/-- The entire input matrix is allowed; its normal part is discarded canonically. -/
def expStep (X Z : CMat n) (t : ℝ) : CMat n :=
  let v := minimumNormLift right left X Z
  cExpLine v.1.val t * X * cExpLine v.2.val t

@[simp] theorem expStep_at_zero (X Z : CMat n) : expStep right left X Z 0 = X := by
  simp only [expStep, cExpLine_zero, Matrix.one_mul, Matrix.mul_one]

@[simp] theorem expStep_zero_input (X : CMat n) (t : ℝ) : expStep right left X 0 t = X := by
  unfold expStep
  rw [map_zero]
  change cMatrixExp (t • (0 : CMat n)) * X * cMatrixExp (t • (0 : CMat n)) = X
  simp only [smul_zero, cMatrixExp_zero, Matrix.one_mul, Matrix.mul_one]

/-- Normal input components do not change the exact finite update. -/
theorem expStep_projected (X Z : CMat n) (t : ℝ) :
    expStep right left X (pointProjection right left X Z) t = expStep right left X Z t := by
  unfold expStep
  rw [minimumNormLift_projected]

/-- The point and its SU direction, rather than a chosen factorization, are the data. -/
theorem expStep_equal_projections (X Z W : CMat n)
    (h : pointProjection right left X Z = pointProjection right left X W) (t : ℝ) :
    expStep right left X Z t = expStep right left X W t := by
  rw [← expStep_projected right left X Z, h, expStep_projected]

/-- Exact feasibility in the smaller special-unitary family, at every real step size. -/
theorem expStep_in_family (P X Z : CMat n)
    (hX : Orbit.InSharedA2SU right left P X) (t : ℝ) :
    Orbit.InSharedA2SU right left P (expStep right left X Z t) := by
  exact Orbit.inSharedA2SU_mul P X _ _ hX
    (cExpLine_special left _ (minimumNormLift right left X Z).1.property t)
    (cExpLine_special right _ (minimumNormLift right left X Z).2.property t)

/-- Actual matrix derivative in the original normed space. -/
theorem expStep_hasDerivAt_zero (X Z : CMat n) :
    HasDerivAt (expStep right left X Z) (pointProjection right left X Z) 0 := by
  let v := minimumNormLift right left X Z
  have hd := GS.UnitaryManifold.hasDerivAt_matrix_mul
    (GS.UnitaryManifold.hasDerivAt_matrix_mul (cExpLine_hasDerivAt v.1.val 0)
      (hasDerivAt_const (0 : ℝ) X)) (cExpLine_hasDerivAt v.2.val 0)
  have hs := minimumNormLift_synthesis (right := right) (left := left) X Z
  change v.1.val * X + X * v.2.val = pointProjection right left X Z at hs
  have hd' : HasDerivAt (expStep right left X Z) (v.1.val * X + X * v.2.val) 0 := by
    simpa only [expStep, v, cExpLine_zero, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero] using hd
  rwa [hs] at hd' 

theorem expStep_hasDerivAt_direction (X V : CMat n)
    (hV : V ∈ pointDirections right left X) : HasDerivAt (expStep right left X V) V 0 := by
  simpa only [pointProjection_of_mem X V hV] using expStep_hasDerivAt_zero right left X V

/-- Full physical generators remain tied and trace-free along the chosen update. -/
theorem expStep_realizes_every_direction (P X V : CMat n)
    (hX : Orbit.InSharedA2SU right left P X)
    (hV : V ∈ pointDirections right left X) :
    ∃ γ : ℝ → CMat n,
      γ 0 = X ∧ (∀ t, Orbit.InSharedA2SU right left P (γ t)) ∧ HasDerivAt γ V 0 :=
  ⟨expStep right left X V, expStep_at_zero right left X V,
    expStep_in_family right left P X V hX, expStep_hasDerivAt_direction right left X V hV⟩

/-- Scaling the input equals scaling time; this uses linearity of the canonical lift. -/
theorem expStep_scaled (X Z : CMat n) (a t : ℝ) :
    expStep right left X (a • Z) t = expStep right left X Z (t * a) := by
  unfold expStep
  rw [map_smul]
  change cMatrixExp (t • (a • (minimumNormLift right left X Z).1.val)) * X *
      cMatrixExp (t • (a • (minimumNormLift right left X Z).2.val)) =
    cMatrixExp ((t * a) • (minimumNormLift right left X Z).1.val) * X *
      cMatrixExp ((t * a) • (minimumNormLift right left X Z).2.val)
  simp only [smul_smul]

/-- A real curve in the SU orbit subtype; no alternative topology is imposed. -/
def orbitExpStep (P : CMat n) (X : Orbit.MatrixOrbit right left P) (Z : CMat n) (t : ℝ) :
    Orbit.MatrixOrbit right left P :=
  ⟨expStep right left X.val Z t,
    (Orbit.orbit_iff_inShared P _).mpr
      (expStep_in_family right left P X.val Z ((Orbit.orbit_iff_inShared P X.val).mp X.property) t)⟩

@[simp] theorem orbitExpStep_val (P : CMat n) (X : Orbit.MatrixOrbit right left P)
    (Z : CMat n) (t : ℝ) : (orbitExpStep right left P X Z t).val = expStep right left X.val Z t := rfl

@[simp] theorem orbitExpStep_zero (P : CMat n) (X : Orbit.MatrixOrbit right left P) (Z : CMat n) :
    orbitExpStep right left P X Z 0 = X := by
  apply Subtype.ext
  exact expStep_at_zero right left X.val Z

section SmoothExtension
-- The matrix point belongs to the larger, already charted U orbit in this section.
open GS.UnitarySharing (MatrixOrbit HorizontalModel sharedOrbitChartedSpace sharedOrbitIsManifold)
variable (P : CMat n)
local instance : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _
local instance : ChartedSpace (HorizontalModel right left P) (MatrixOrbit right left P) :=
  sharedOrbitChartedSpace right left P
local instance : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤ (MatrixOrbit right left P) :=
  sharedOrbitIsManifold right left P

/-- A stronger ambient extension theorem; it does not assert an SU atlas. -/
theorem expStep_contMDiff_on_unitary_orbit :
    ContMDiff (((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, CMat n)) ⊤
      (fun p : (MatrixOrbit right left P × CMat n) × ℝ => expStep right left p.1.1.val p.1.2 p.2) := by
  let E := PairGenerator right left
  have hword : ContDiff ℝ ⊤
      (fun p : (E × CMat n) × ℝ =>
        cMatrixExp (p.2 • p.1.1.1.val) * p.1.2 * cMatrixExp (p.2 • p.1.1.2.val)) := by
    have hl : ContDiff ℝ ⊤ (fun p : (E × CMat n) × ℝ => p.1.1.1.val) :=
      (specialSkewSpace left).subtypeL.contDiff.comp ((contDiff_fst.comp contDiff_fst).fst)
    have hr : ContDiff ℝ ⊤ (fun p : (E × CMat n) × ℝ => p.1.1.2.val) :=
      (specialSkewSpace right).subtypeL.contDiff.comp ((contDiff_fst.comp contDiff_fst).snd)
    exact contDiff_iff_contDiffAt.mpr (fun x =>
      smooth_mul_at
        (smooth_mul_at ((cMatrixExp_contDiff.comp (contDiff_snd.smul hl)).contDiffAt)
          ((contDiff_snd.comp contDiff_fst).contDiffAt))
        ((cMatrixExp_contDiff.comp (contDiff_snd.smul hr)).contDiffAt))
  have hlift := (minimumNormLift_contMDiff_on_unitary_orbit right left P).comp contMDiff_fst
  have hX := (GS.UnitarySharing.sharedOrbit_val_contMDiff right left P).comp
    (contMDiff_fst.comp contMDiff_fst)
  simpa only [expStep, cExpLine, E, Function.comp_def] using
    hword.comp_contMDiff ((hlift.prodMk_space hX).prodMk_space contMDiff_snd)
/-- Joint continuity on the genuine SU orbit follows from the smooth U extension.
No manifold instance on the smaller orbit is required for this theorem. -/
theorem expStep_continuous_on_SU_orbit :
    Continuous (fun p : (Orbit.MatrixOrbit right left P × CMat n) × ℝ =>
      expStep right left p.1.1.val p.1.2 p.2) := by
  have hi : Continuous (fun p : (Orbit.MatrixOrbit right left P × CMat n) × ℝ =>
      ((Orbit.toUnitaryOrbit P p.1.1, p.1.2), p.2)) :=
    (((Orbit.toUnitaryOrbit_continuous P).comp (continuous_fst.comp continuous_fst)).prodMk
      (continuous_snd.comp continuous_fst)).prodMk continuous_snd
  exact (expStep_contMDiff_on_unitary_orbit right left P).continuous.comp hi

theorem orbitExpStep_continuous :
    Continuous (fun p : (Orbit.MatrixOrbit right left P × CMat n) × ℝ =>
      orbitExpStep right left P p.1.1 p.1.2 p.2) :=
  (expStep_continuous_on_SU_orbit right left P).subtype_mk _

end SmoothExtension

end GS.SpecialUnitarySharing
