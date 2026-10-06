module

public import GS.SharedGeometry.SmoothLift
public import GS.GlobalGeometry.CayleyRetraction

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A point-only shared Cayley update with a canonical generator lift

The update uses the unique minimum-physical-norm generators. It is defined
for every real step length and every ambient input vector, preserves the
original shared orbit, and has initial velocity equal to the exact projected
input. Joint smoothness is asserted on a fixed orbit, not across rank changes.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.GlobalGeometry GS.CayleyCharts GS.Continuation GS.Extensions
open scoped Topology Manifold
namespace GS.SharedGeometry
variable {n : ℕ} {right left : Pattern n}

/-- The normalized Cayley transform preserves all physical block ties. -/
theorem unitCayley_shared (s : Pattern n) (C : Generator s) :
    SharedOrthogonalFactor s.size s.label (unitCayley C.val) :=
  cayley_shared s.positive s.divides
    ((sharedSkewSpace s.size s.label).smul_mem (-1 / 2 : ℝ) C.property)

/-- Auxiliary globally smooth map before the generators are chosen. -/
def generatorCayleyValue (right left : Pattern n)
    (p : Mat n × (PairGenerator right left × ℝ)) : Mat n :=
  unitCayley (p.2.2 • p.2.1.1.val) * p.1 * unitCayley (p.2.2 • p.2.1.2.val)

theorem generatorCayleyValue_smooth (right left : Pattern n) :
    ContDiff ℝ ⊤ (generatorCayleyValue right left) := by
  let E := Mat n × (PairGenerator right left × ℝ)
  have hL : ContDiff ℝ ⊤ (fun p : E => p.2.2 • p.2.1.1.val) :=
    contDiff_snd.snd.smul
      ((sharedSkewSpace (n := n) left.size left.label).subtypeL.contDiff.comp contDiff_snd.fst.fst)
  have hR : ContDiff ℝ ⊤ (fun p : E => p.2.2 • p.2.1.2.val) :=
    contDiff_snd.snd.smul
      ((sharedSkewSpace (n := n) right.size right.label).subtypeL.contDiff.comp contDiff_snd.fst.snd)
  have hcL := unitCayley_smooth_comp _ hL (fun p => isSkew_smul p.2.2 p.2.1.1.property.2.1)
  have hcR := unitCayley_smooth_comp _ hR (fun p => isSkew_smul p.2.2 p.2.1.2.property.2.1)
  exact contDiff_matrix_mul (contDiff_matrix_mul hcL contDiff_fst) hcR

/-- The actual shared group element acting by this update. -/
def generatorCayleyAction (v : PairGenerator right left) (t : ℝ) : Factors right left :=
  (Factor.ofMatrix (unitCayley (t • v.1.val)) (unitCayley_shared left (t • v.1)),
   Factor.ofMatrix ((unitCayley (t • v.2.val))ᵀ)
     (shared_factor_transpose (unitCayley_shared right (t • v.2))))

theorem generatorCayleyAction_value (X : Mat n) (v : PairGenerator right left) (t : ℝ) :
    generatorCayleyAction v t • X = generatorCayleyValue right left (X, (v, t)) := by
  change unitCayley (t • v.1.val) * X * ((unitCayley (t • v.2.val))ᵀ)ᵀ = _
  rw [Matrix.transpose_transpose]
  rfl

/-- The value depends on X,Z,t alone, not on a factor representative. -/
def sharedCayleyValue (right left : Pattern n) (X Z : Mat n) (t : ℝ) : Mat n :=
  generatorCayleyValue right left (X, (minimumNormLift right left X Z, t))

/-- Removing an ambient normal component does not change the exact update. -/
@[simp] theorem sharedCayleyValue_projected (X Z : Mat n) (t : ℝ) :
    sharedCayleyValue right left X (pointProjection right left X Z) t =
      sharedCayleyValue right left X Z t := by
  simp only [sharedCayleyValue, minimumNormLift_projected]

/-- The update depends only on the tangent projection of its ambient input. -/
theorem sharedCayleyValue_eq_of_projection_eq (X Z W : Mat n) (t : ℝ)
    (h : pointProjection right left X Z = pointProjection right left X W) :
    sharedCayleyValue right left X Z t = sharedCayleyValue right left X W t := by
  calc
    sharedCayleyValue right left X Z t =
        sharedCayleyValue right left X (pointProjection right left X Z) t :=
      (sharedCayleyValue_projected X Z t).symm
    _ = sharedCayleyValue right left X (pointProjection right left X W) t :=
      congrArg (fun V : Mat n => sharedCayleyValue right left X V t) h
    _ = sharedCayleyValue right left X W t := sharedCayleyValue_projected X W t

@[simp] theorem sharedCayleyValue_zero_time (X Z : Mat n) :
    sharedCayleyValue right left X Z 0 = X := by simp [sharedCayleyValue, generatorCayleyValue]

@[simp] theorem sharedCayleyValue_zero_vector (X : Mat n) (t : ℝ) :
    sharedCayleyValue right left X 0 t = X := by simp [sharedCayleyValue, generatorCayleyValue]

theorem sharedCayleyValue_smul (X Z : Mat n) (a t : ℝ) :
    sharedCayleyValue right left X (a • Z) t = sharedCayleyValue right left X Z (t * a) := by
  unfold sharedCayleyValue
  rw [map_smul]
  change unitCayley (t • (a • (minimumNormLift right left X Z).1.val)) * X *
      unitCayley (t • (a • (minimumNormLift right left X Z).2.val)) =
    unitCayley ((t * a) • (minimumNormLift right left X Z).1.val) * X *
      unitCayley ((t * a) • (minimumNormLift right left X Z).2.val)
  simp only [smul_smul]

/-- Feasibility holds for all times, not only for a sufficiently small step. -/
theorem sharedCayleyValue_mem_orbit (P : Mat n) (X : MatrixOrbit right left P)
    (Z : Mat n) (t : ℝ) :
    sharedCayleyValue right left X.val Z t ∈ MulAction.orbit (Factors right left) P := by
  obtain ⟨g, hg⟩ := X.property
  refine ⟨generatorCayleyAction (minimumNormLift right left X.val Z) t * g, ?_⟩
  change g • P = X.val at hg
  change (generatorCayleyAction (minimumNormLift right left X.val Z) t * g) • P = _
  rw [mul_smul, hg, generatorCayleyAction_value]
  rfl

/-- Initial matrix velocity equals the canonical full shared tangent projection. -/
theorem sharedCayleyValue_derivative (X Z : Mat n) :
    HasDerivAt (sharedCayleyValue right left X Z) (pointProjection right left X Z) 0 := by
  let v := minimumNormLift right left X Z
  have hL := unitCayley_line_derivative v.1.val v.1.property.2.1
  have hR := unitCayley_line_derivative v.2.val v.2.property.2.1
  have hd := hasDerivAt_matrix_mul
    (hasDerivAt_matrix_mul hL (hasDerivAt_const (0 : ℝ) X)) hR
  have hv : v.1.val * X + X * v.2.val = pointProjection right left X Z :=
    minimumNormLift_synthesis X Z
  unfold sharedCayleyValue generatorCayleyValue
  simpa only [zero_smul, unitCayley_zero, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, add_zero, hv] using hd

/-- At a fixed matrix point, dependence on the ambient velocity and time is smooth. -/
theorem sharedCayleyValue_fixed_smooth (X : Mat n) :
    ContDiff ℝ ⊤ (fun p : Mat n × ℝ => sharedCayleyValue right left X p.1 p.2) := by
  exact (generatorCayleyValue_smooth right left).comp
    (contDiff_const.prodMk (((minimumNormLift right left X).contDiff.comp contDiff_fst).prodMk contDiff_snd))

section OrbitSmoothness
variable (right left : Pattern n) (P : Mat n)
local instance cayleyStepChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
local instance cayleyStepIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

/-- Joint smoothness including the base point, on the whole fixed orbit. -/
theorem sharedCayleyValue_contMDiff :
    ContMDiff (((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, Mat n))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, Mat n)) ⊤ (fun p : (MatrixOrbit right left P × Mat n) × ℝ =>
        sharedCayleyValue right left p.1.1.val p.1.2 p.2) := by
  have hb : ContMDiff
      (((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, Mat n))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, Mat n)) ⊤
      (fun p : (MatrixOrbit right left P × Mat n) × ℝ => p.1.1.val) :=
    (sharedOrbit_val_contMDiff right left P).comp (contMDiff_fst.comp contMDiff_fst)
  have hl : ContMDiff
      (((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, Mat n))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, PairGenerator right left)) ⊤
      (fun p : (MatrixOrbit right left P × Mat n) × ℝ =>
        minimumNormLift right left p.1.1.val p.1.2) :=
    (minimumNormLift_contMDiff right left P).comp contMDiff_fst
  exact (generatorCayleyValue_smooth right left).comp_contMDiff
    (hb.prodMk_space (hl.prodMk_space contMDiff_snd))

end OrbitSmoothness
end GS.SharedGeometry
