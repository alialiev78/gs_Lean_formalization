module

public import GS.UnitarySharing.BundleRetraction
public import GS.UnitarySharing.Gradient
public import GS.RiemannianCompletion.ExponentialStep
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Intrinsic shared descent through the canonical whole-bundle retraction

The curve is the exact point-and-tangent Cayley map. Its negative intrinsic
gradient has loss derivative minus the squared induced Frobenius norm.
Armijo steps exist and geometric backtracking terminates for a nonzero
gradient. These are actual shared-orbit statements for any fixed carrier.
No convergence rate or floating-point implementation theorem is asserted.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.RiemannianCompletion Filter
open scoped Topology Manifold
namespace GS.UnitarySharing
set_option synthInstance.maxHeartbeats 100000
variable {n : ℕ} (right left : Pattern n) (P : CMat n)
local instance descentNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance descentChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
local instance descentIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

/-- The loss derivative along the Cayley curve is the intrinsic metric pairing. -/
theorem loss_along_cayleyTangentStep (f : CMat n → ℝ)
    (X : MatrixOrbit right left P) (hf : DifferentiableAt ℝ f X.val)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    HasDerivAt (fun t => f (cayleyTangentStep right left P X v t).val)
      (tangentPairing right left P X (intrinsicGradient right left P f X) v) 0 := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (cayleyTangentStep_derivative right left P X v)
    (by simp only [cayleyTangentStep_at_zero])
  rw [GS.UnitaryManifold.ambientGradient_represents] at hd
  rw [intrinsicGradient, tangentProjection_pairing]
  simpa only [inclusionDifferential, Function.comp_def] using hd

theorem negative_gradient_loss_derivative (f : CMat n → ℝ)
    (X : MatrixOrbit right left P) (hf : DifferentiableAt ℝ f X.val) :
    HasDerivAt (fun t => f (cayleyTangentStep right left P X (-intrinsicGradient right left P f X) t).val)
      (-tangentPairing right left P X (intrinsicGradient right left P f X) (intrinsicGradient right left P f X)) 0 := by
  have hd := loss_along_cayleyTangentStep right left P f X hf (-intrinsicGradient right left P f X)
  have he : tangentPairing right left P X (intrinsicGradient right left P f X) (-intrinsicGradient right left P f X) =
      -tangentPairing right left P X (intrinsicGradient right left P f X) (intrinsicGradient right left P f X) := by
    rw [show (-intrinsicGradient right left P f X) = (-1 : ℝ) • intrinsicGradient right left P f X by simp,
      tangentPairing_smul_right]
    ring
  rwa [he] at hd

/-- Backtracking has admissible small steps whenever the gradient is nonzero. -/
theorem cayleyTangentStep_armijo (f : CMat n → ℝ)
    (X : MatrixOrbit right left P) (hf : DifferentiableAt ℝ f X.val)
    (hg : intrinsicGradient right left P f X ≠ 0) (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      f (cayleyTangentStep right left P X (-intrinsicGradient right left P f X) t).val <
        f X.val - c * t * tangentPairing right left P X (intrinsicGradient right left P f X)
          (intrinsicGradient right left P f X) := by
  have hh := GS.RiemannianCompletion.armijo_of_negative_derivative
    (negative_gradient_loss_derivative right left P f X hf)
    (tangentPairing_pos right left P X (intrinsicGradient right left P f X) hg) c hc hc1
  simpa only [cayleyTangentStep_at_zero] using hh

/-- Geometric backtracking terminates after finitely many reductions.
No uniform iteration bound is asserted from mere pointwise differentiability. -/
theorem backtracking_terminates (f : CMat n → ℝ)
    (X : MatrixOrbit right left P) (hf : DifferentiableAt ℝ f X.val)
    (hg : intrinsicGradient right left P f X ≠ 0) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ k : ℕ,
      f (cayleyTangentStep right left P X (-intrinsicGradient right left P f X) (α * ρ ^ k)).val <
        f X.val - c * (α * ρ ^ k) * tangentPairing right left P X (intrinsicGradient right left P f X)
          (intrinsicGradient right left P f X) := by
  have hlimit : Tendsto (fun k : ℕ => α * ρ ^ k) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul α
    · exact Filter.Eventually.of_forall (fun k => mul_pos hα (pow_pos hρ k))
  exact (hlimit.eventually (cayleyTangentStep_armijo right left P f X hf hg c hc hc1)).exists

/-- Backtracking expressed directly through the canonical whole-bundle map. -/
theorem cayleyRetraction_backtracking_terminates (f : CMat n → ℝ)
    (X : MatrixOrbit right left P) (hf : DifferentiableAt ℝ f X.val)
    (hg : intrinsicGradient right left P f X ≠ 0) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ k : ℕ,
      f (cayleyRetraction right left P
        ⟨X, (α * ρ ^ k) • (-intrinsicGradient right left P f X)⟩).val <
        f X.val - c * (α * ρ ^ k) * tangentPairing right left P X
          (intrinsicGradient right left P f X) (intrinsicGradient right left P f X) := by
  simpa only [cayleyRetraction_scaled] using
    backtracking_terminates right left P f X hf hg c hc hc1 α ρ hα hρ hρ1

end GS.UnitarySharing
