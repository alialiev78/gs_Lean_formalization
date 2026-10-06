module

public import GS.SpecialUnitarySharing.Retraction

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# A canonical smooth retraction on the whole shared tangent bundle

The base is the actual shared matrix orbit, with its inherited-topology atlas.
The retraction is globally defined on mathlib's entire tangent bundle. It
fixes the zero section and its actual manifold differential on every zero
fibre is the identity. Arbitrary overlap and fixed singular carriers are
allowed. This is the exact matrix-exponential update, not a truncated numerical algorithm.
It is not asserted to be the Riemannian exponential map.
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
local instance : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
local instance : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

/-- Actual shared generators, smoothly recovered from the true tangent bundle. -/
def tangentGenerators
    (p : TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P)) :
    PairGenerator right left :=
  minimumNormLift right left p.proj.val (tangentAmbient right left P p)

theorem tangentGenerators_contMDiff :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)).tangent
      (𝓘(ℝ, PairGenerator right left)) ⊤ (tangentGenerators right left P) := by
  exact (minimumNormLift_contMDiff right left P).comp
    ((Bundle.contMDiff_proj (TangentSpace (𝓘(ℝ, HorizontalModel right left P)))).prodMk
      (tangentAmbient_contMDiff right left P))

/-- Reconstruction is stated on the true differential image, not an assumed lift. -/
theorem tangentGenerators_reconstruct
    (p : TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P)) :
    pointMap right left p.proj.val (tangentGenerators right left P p) =
      tangentAmbient right left P p := by
  exact minimumNormLift_reconstruct p.proj.val _
    ((orbit_tangent_image_iff right left P p.proj _).mp ⟨p.2, rfl⟩)

/-- Canonical function on the actual whole tangent bundle. -/
def expRetraction
    (p : TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P)) :
    MatrixOrbit right left P := expFibreRetraction right left P p.proj p.2

@[simp] theorem expRetraction_val
    (p : TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P)) :
    (expRetraction right left P p).val =
      expStep right left p.proj.val (tangentAmbient right left P p) 1 := rfl

/-- Joint smoothness, including the varying base and all tangent fibres. -/
set_option maxHeartbeats 800000 in
theorem expRetraction_contMDiff :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)).tangent
      (𝓘(ℝ, HorizontalModel right left P)) ⊤ (expRetraction right left P) := by
  have hargs : ContMDiff (𝓘(ℝ, HorizontalModel right left P)).tangent
      (((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n))).prod (𝓘(ℝ, ℝ))) ⊤
      (fun p : TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P) =>
        ((p.proj, tangentAmbient right left P p), (1 : ℝ))) :=
    ((Bundle.contMDiff_proj (TangentSpace (𝓘(ℝ, HorizontalModel right left P)))).prodMk
      (tangentAmbient_contMDiff right left P)).prodMk contMDiff_const
  have ha := (expStep_contMDiff right left P).comp hargs
  apply (sharedOrbit_contMDiff_iff_ambient right left P
    (𝓘(ℝ, HorizontalModel right left P)).tangent (expRetraction right left P)).mpr
  simpa only [expRetraction_val] using ha

@[simp] theorem expRetraction_zero_section (X : MatrixOrbit right left P) :
    expRetraction right left P ⟨X, 0⟩ = X := expFibreRetraction_zero right left P X

/-- The genuine manifold derivative of the fibre map, not only a matrix expansion. -/
theorem expRetraction_fibre_mfderiv_zero (X : MatrixOrbit right left P) :
    mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P))
      (fun v : HorizontalModel right left P => expRetraction right left P ⟨X, v⟩)
      (0 : HorizontalModel right left P) = ContinuousLinearMap.id ℝ (HorizontalModel right left P) :=
  expFibreRetraction_mfderiv_zero right left P X

@[simp] theorem expRetraction_scaled (X : MatrixOrbit right left P)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) (t : ℝ) :
    expRetraction right left P ⟨X, t • v⟩ = expTangentStep right left P X v t := by
  change expTangentStep right left P X (t • v) 1 = _
  simpa only [one_mul] using expTangentStep_smul right left P X v t 1

end GS.SpecialUnitarySharing
