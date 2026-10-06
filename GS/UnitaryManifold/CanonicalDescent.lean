module

public import GS.UnitaryManifold.BundleRetraction
public import GS.UnitaryManifold.Gradient
public import GS.RiemannianCompletion.ExponentialStep
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Descent through the canonical whole-bundle unitary Cayley retraction

This module leaves the older chosen-chart descent API unchanged.  The curve
used here is the canonical point-and-tangent construction from BundleRetraction,
with its already established actual matrix velocity.  Its negative intrinsic
gradient has loss derivative minus the squared induced metric norm.  Armijo
steps exist and geometric backtracking terminates for a nonzero gradient.

No convergence rate or floating-point implementation theorem is asserted.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.RiemannianCompletion Filter
open scoped Topology Manifold
namespace GS.UnitaryManifold
set_option synthInstance.maxHeartbeats 100000
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance canonicalDescentHorizontalNormedAddCommGroup :
    NormedAddCommGroup (HorizontalModel b₁ b₂ σ) := inferInstance
local instance canonicalDescentHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance canonicalDescentChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance canonicalDescentIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- The loss derivative along the Cayley curve is the intrinsic metric pairing. -/
theorem loss_along_canonicalCayleyStep (f : CMat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    HasDerivAt (fun t => f (canonicalCayleyStep b₁ b₂ σ X v t).val)
      (tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) v) 0 := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (canonicalCayleyStep_derivative b₁ b₂ σ X v)
    (by simp only [canonicalCayleyStep_at_zero])
  rw [ambientGradient_represents] at hd
  rw [intrinsicGradient, tangentProjection_pairing]
  simpa only [inclusionDifferential, Function.comp_def] using hd

theorem canonical_negative_gradient_loss_derivative (f : CMat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) (hf : DifferentiableAt ℝ f X.val) :
    HasDerivAt (fun t => f (canonicalCayleyStep b₁ b₂ σ X (-intrinsicGradient b₁ b₂ σ f X) t).val)
      (-tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) (intrinsicGradient b₁ b₂ σ f X)) 0 := by
  have hd := loss_along_canonicalCayleyStep b₁ b₂ σ f X hf (-intrinsicGradient b₁ b₂ σ f X)
  have he : tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) (-intrinsicGradient b₁ b₂ σ f X) =
      -tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) (intrinsicGradient b₁ b₂ σ f X) := by
    rw [show (-intrinsicGradient b₁ b₂ σ f X) = (-1 : ℝ) • intrinsicGradient b₁ b₂ σ f X by simp,
      tangentPairing_smul_right]
    ring
  rwa [he] at hd

/-- Backtracking has admissible small steps whenever the gradient is nonzero. -/
theorem canonicalCayleyStep_armijo (f : CMat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (hg : intrinsicGradient b₁ b₂ σ f X ≠ 0) (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      f (canonicalCayleyStep b₁ b₂ σ X (-intrinsicGradient b₁ b₂ σ f X) t).val <
        f X.val - c * t * tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X)
          (intrinsicGradient b₁ b₂ σ f X) := by
  have hh := armijo_of_negative_derivative
    (canonical_negative_gradient_loss_derivative b₁ b₂ σ f X hf)
    (tangentPairing_pos b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X) hg) c hc hc1
  simpa only [canonicalCayleyStep_at_zero] using hh

/-- Geometric backtracking terminates after finitely many reductions.
No uniform iteration bound is asserted from mere pointwise differentiability. -/
theorem canonical_backtracking_terminates (f : CMat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (hg : intrinsicGradient b₁ b₂ σ f X ≠ 0) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ k : ℕ,
      f (canonicalCayleyStep b₁ b₂ σ X (-intrinsicGradient b₁ b₂ σ f X) (α * ρ ^ k)).val <
        f X.val - c * (α * ρ ^ k) * tangentPairing b₁ b₂ σ X (intrinsicGradient b₁ b₂ σ f X)
          (intrinsicGradient b₁ b₂ σ f X) := by
  have hlimit : Tendsto (fun k : ℕ => α * ρ ^ k) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul α
    · exact Filter.Eventually.of_forall (fun k => mul_pos hα (pow_pos hρ k))
  exact (hlimit.eventually (canonicalCayleyStep_armijo b₁ b₂ σ f X hf hg c hc hc1)).exists

/-- Exact agreement with evaluation of the new map on the whole tangent bundle. -/
@[simp] theorem cayleyRetraction_scaled (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) (t : ℝ) :
    cayleyRetraction b₁ b₂ σ ⟨X, t • v⟩ = canonicalCayleyStep b₁ b₂ σ X v t := by
  change canonicalCayleyStep b₁ b₂ σ X (t • v) 1 = _
  simpa only [one_mul] using canonicalCayleyStep_smul b₁ b₂ σ X v t 1

/-- Backtracking expressed directly through the canonical whole-bundle map. -/
theorem cayleyRetraction_backtracking_terminates (f : CMat n → ℝ)
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) (hf : DifferentiableAt ℝ f X.val)
    (hg : intrinsicGradient b₁ b₂ σ f X ≠ 0) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ k : ℕ,
      f (cayleyRetraction b₁ b₂ σ
        ⟨X, (α * ρ ^ k) • (-intrinsicGradient b₁ b₂ σ f X)⟩).val <
        f X.val - c * (α * ρ ^ k) * tangentPairing b₁ b₂ σ X
          (intrinsicGradient b₁ b₂ σ f X) (intrinsicGradient b₁ b₂ σ f X) := by
  simpa only [cayleyRetraction_scaled] using
    canonical_backtracking_terminates b₁ b₂ σ f X hf hg c hc hc1 α ρ hα hρ hρ1

end GS.UnitaryManifold
