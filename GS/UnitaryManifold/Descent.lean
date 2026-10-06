module

public import GS.UnitaryManifold.Retraction
public import GS.UnitaryManifold.Gradient
public import GS.RiemannianCompletion.ExponentialStep
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Intrinsic Cayley descent with arbitrary overlap

The negative intrinsic gradient is an actual vector in the tangent space of
the horizontal orbit atlas. Its fixed-base Cayley curve has the negative squared metric
norm as loss derivative, satisfies Armijo decrease for all sufficiently small
positive steps, and permits finite geometric backtracking.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.RiemannianCompletion Filter
open scoped Topology Manifold
namespace GS.UnitaryManifold
set_option synthInstance.maxHeartbeats 100000
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance unitaryDescentHorizontalNormedAddCommGroup :
    NormedAddCommGroup (HorizontalModel b₁ b₂ σ) := inferInstance
local instance unitaryDescentHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance unitaryDescentChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance unitaryDescentIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- A feasible curve on a fixed tangent fibre; the base point is not varied. -/
def fibreRetractionStep (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) (t : ℝ) :
    MatrixOrbit b₁ b₂ (cPermMatrix σ) := fibreRetraction b₁ b₂ σ X (t • v)

@[simp] theorem fibreRetractionStep_at_zero (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    fibreRetractionStep b₁ b₂ σ X v 0 = X := by
  simp [fibreRetractionStep]

/-- The loss derivative along the Cayley curve is the intrinsic metric pairing. -/
theorem loss_along_fibreRetractionStep (f : CMat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    HasDerivAt (fun t => f (fibreRetractionStep b₁ b₂ σ X v t).val)
      (tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) v) 0 := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (fibreRetraction_curve_velocity b₁ b₂ σ X v)
    (by simp only [zero_smul, fibreRetraction_zero])
  rw [ambientGradient_represents] at hd
  rw [intrinsicGradient, tangentProjection_pairing]
  convert hd using 1 <;> rfl

theorem fibre_negative_gradient_loss_derivative (f : CMat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) (hf : DifferentiableAt ℝ f X.val) :
    HasDerivAt (fun t => f (fibreRetractionStep b₁ b₂ σ X (-intrinsicGradient b₁ b₂ σ f X) t).val)
      (-tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) (intrinsicGradient b₁ b₂ σ f X)) 0 := by
  have hd := loss_along_fibreRetractionStep b₁ b₂ σ f X hf (-intrinsicGradient b₁ b₂ σ f X)
  have he : tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) (-intrinsicGradient b₁ b₂ σ f X) =
      -tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) (intrinsicGradient b₁ b₂ σ f X) := by
    rw [show (-intrinsicGradient b₁ b₂ σ f X) = (-1 : ℝ) • intrinsicGradient b₁ b₂ σ f X by simp,
      tangentPairing_smul_right]
    ring
  rwa [he] at hd

/-- Backtracking has admissible small steps whenever the gradient is nonzero. -/
theorem fibreRetractionStep_armijo (f : CMat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (hg : intrinsicGradient b₁ b₂ σ f X ≠ 0) (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      f (fibreRetractionStep b₁ b₂ σ X (-intrinsicGradient b₁ b₂ σ f X) t).val <
        f X.val - c * t * tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X)
          (intrinsicGradient b₁ b₂ σ f X) := by
  have hh := armijo_of_negative_derivative
    (fibre_negative_gradient_loss_derivative b₁ b₂ σ f X hf)
    (tangentPairing_pos b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) hg) c hc hc1
  simpa only [fibreRetractionStep_at_zero] using hh

/-- Geometric backtracking terminates after finitely many reductions.
No uniform iteration bound is asserted from mere pointwise differentiability. -/
theorem fibre_backtracking_terminates (f : CMat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (hg : intrinsicGradient b₁ b₂ σ f X ≠ 0) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ k : ℕ,
      f (fibreRetractionStep b₁ b₂ σ X (-intrinsicGradient b₁ b₂ σ f X) (α * ρ ^ k)).val <
        f X.val - c * (α * ρ ^ k) * tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X)
          (intrinsicGradient b₁ b₂ σ f X) := by
  have hlimit : Tendsto (fun k : ℕ => α * ρ ^ k) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul α
    · exact Filter.Eventually.of_forall (fun k => mul_pos hα (pow_pos hρ k))
  exact (hlimit.eventually (fibreRetractionStep_armijo b₁ b₂ σ f X hf hg c hc hc1)).exists

end GS.UnitaryManifold
