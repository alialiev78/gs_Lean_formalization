module

public import GS.OverlapGeometry.Retraction
public import GS.RiemannianCompletion.ExponentialStep
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Intrinsic Cayley descent with arbitrary overlap

The negative intrinsic gradient is an actual vector in the tangent space of
the horizontal orbit atlas. Its Cayley curve has the negative squared metric
norm as loss derivative, satisfies Armijo decrease for all sufficiently small
positive steps, and permits finite geometric backtracking.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.LieAction GS.CayleyCharts
open GS.ManifoldCompletion GS.RiemannianCompletion Filter
open scoped Topology Manifold
namespace GS.OverlapGeometry
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance descentHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance descentChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance descentIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- The loss derivative along the Cayley curve is the intrinsic metric pairing. -/
theorem loss_along_cayleyTangentStep (f : Mat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    HasDerivAt (fun t => f (cayleyTangentStep b₁ b₂ σ X v t).val)
      (tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) v) 0 := by
  have hd := ambientGradient_chain hf (cayleyTangentStep_derivative b₁ b₂ σ X v)
    (congrArg Subtype.val (cayleyTangentStep_at_zero b₁ b₂ σ X v))
  simpa only [intrinsicGradient, tangentProjection_pairing] using hd

theorem cayley_negative_gradient_loss_derivative (f : Mat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val) :
    HasDerivAt (fun t => f (cayleyTangentStep b₁ b₂ σ X (-intrinsicGradient b₁ b₂ σ f X) t).val)
      (-tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) (intrinsicGradient b₁ b₂ σ f X)) 0 := by
  have hd := loss_along_cayleyTangentStep b₁ b₂ σ f X hf (-intrinsicGradient b₁ b₂ σ f X)
  have he : tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) (-intrinsicGradient b₁ b₂ σ f X) =
      -tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) (intrinsicGradient b₁ b₂ σ f X) := by
    rw [show (-intrinsicGradient b₁ b₂ σ f X) = (-1 : ℝ) • intrinsicGradient b₁ b₂ σ f X by simp,
      tangentPairing_smul_right]
    ring
  rwa [he] at hd

/-- Backtracking has admissible small steps whenever the gradient is nonzero. -/
theorem cayleyTangentStep_armijo (f : Mat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (hg : intrinsicGradient b₁ b₂ σ f X ≠ 0) (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      f (cayleyTangentStep b₁ b₂ σ X (-intrinsicGradient b₁ b₂ σ f X) t).val <
        f X.val - c * t * tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X)
          (intrinsicGradient b₁ b₂ σ f X) := by
  have hh := armijo_of_negative_derivative
    (cayley_negative_gradient_loss_derivative b₁ b₂ σ f X hf)
    (tangentPairing_pos b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) hg) c hc hc1
  simpa only [cayleyTangentStep_at_zero] using hh

/-- Geometric backtracking terminates after finitely many reductions.
No uniform iteration bound is asserted from mere pointwise differentiability. -/
theorem cayley_backtracking_terminates (f : Mat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (hg : intrinsicGradient b₁ b₂ σ f X ≠ 0) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ k : ℕ,
      f (cayleyTangentStep b₁ b₂ σ X (-intrinsicGradient b₁ b₂ σ f X) (α * ρ ^ k)).val <
        f X.val - c * (α * ρ ^ k) * tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X)
          (intrinsicGradient b₁ b₂ σ f X) := by
  have hlimit : Tendsto (fun k : ℕ => α * ρ ^ k) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul α
    · exact Filter.Eventually.of_forall (fun k => mul_pos hα (pow_pos hρ k))
  exact (hlimit.eventually (cayleyTangentStep_armijo b₁ b₂ σ f X hf hg c hc hc1)).exists

end GS.OverlapGeometry
