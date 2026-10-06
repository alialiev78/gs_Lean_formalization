module

public import GS.SpecialUnitarySharing.ExponentialStep
public import GS.UnitarySharing.AmbientDual
public import GS.RiemannianCompletion.ExponentialStep
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Exact feasible descent in the SU matrix family

The real Frechet derivative, the complete SU generator image, and the exact
exponential update give the negative squared projected-gradient derivative.
Armijo and finite backtracking follow for a nonzero projected gradient. This
is an extrinsic optimization theorem on the actual SU family. Its intrinsic
counterpart is established separately in `IntrinsicDescent` using the SU atlas.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold Filter
open scoped Topology Manifold ContDiff
namespace GS.SpecialUnitarySharing
variable {n : ℕ} (right left : Pattern n)

/-- Representative of the derivative restricted to the exact SU generator range. -/
def projectedGradient (f : CMat n → ℝ) (X : CMat n) : CMat n :=
  pointProjection right left X (ambientGradient f X)

theorem projectedGradient_mem (f : CMat n → ℝ) (X : CMat n) :
    projectedGradient right left f X ∈ pointDirections right left X :=
  pointProjection_mem X (ambientGradient f X)

theorem projectedGradient_pairing (f : CMat n → ℝ) (X V : CMat n)
    (hV : V ∈ pointDirections right left X) :
    cFrobInner (projectedGradient right left f X) V = fderiv ℝ f X V := by
  rw [projectedGradient, pointProjection_self_adjoint, pointProjection_of_mem X V hV,
    ambientGradient_represents]

theorem projectedGradient_unique (f : CMat n → ℝ) (X G : CMat n)
    (hG : G ∈ pointDirections right left X)
    (h : ∀ V ∈ pointDirections right left X, cFrobInner G V = fderiv ℝ f X V) :
    G = projectedGradient right left f X := by
  symm
  apply cFrobProjection_unique_normal (pointDirections right left X) (ambientGradient f X)
  · exact hG
  · intro V hV
    rw [cFrobInner_sub_left, ← ambientGradient_represents, h V hV, sub_self]

/-- A first-order certificate against every realizable SU generator direction. -/
theorem projectedGradient_zero_iff (f : CMat n → ℝ) (X : CMat n) :
    projectedGradient right left f X = 0 ↔
      ∀ V ∈ pointDirections right left X, fderiv ℝ f X V = 0 := by
  constructor
  · intro h V hV
    rw [← projectedGradient_pairing right left f X V hV, h, cFrobInner_zero_left]
  · intro h
    apply (cFrobSq_eq_zero_iff _).mp
    exact (projectedGradient_pairing right left f X _ (projectedGradient_mem right left f X)).trans
      (h _ (projectedGradient_mem right left f X))

theorem negative_projectedGradient_loss_derivative (f : CMat n → ℝ) (X : CMat n)
    (hf : DifferentiableAt ℝ f X) :
    HasDerivAt (fun t => f (expStep right left X (-projectedGradient right left f X) t))
      (-cFrobSq (projectedGradient right left f X)) 0 := by
  let G := projectedGradient right left f X
  have hG := projectedGradient_mem right left f X
  have hd := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (expStep_hasDerivAt_direction right left X (-G) ((pointDirections right left X).neg_mem hG))
    (expStep_at_zero right left X (-G))
  have hp : fderiv ℝ f X (-G) = -cFrobSq G := by
    rw [map_neg, ← projectedGradient_pairing right left f X G hG]
    rfl
  simpa only [hp, G] using hd

theorem expStep_armijo (f : CMat n → ℝ) (X : CMat n)
    (hf : DifferentiableAt ℝ f X) (hg : projectedGradient right left f X ≠ 0)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      f (expStep right left X (-projectedGradient right left f X) t) <
        f X - c * t * cFrobSq (projectedGradient right left f X) := by
  have hh := GS.RiemannianCompletion.armijo_of_negative_derivative
    (negative_projectedGradient_loss_derivative right left f X hf)
    (GS.UnitaryManifold.cFrobSq_pos_of_ne_zero hg) c hc hc1
  simpa only [expStep_at_zero] using hh

/-- Finite backtracking AND actual SU feasibility; no asymptotic rate is claimed. -/
theorem feasible_backtracking (P X : CMat n) (hX : Orbit.InSharedA2SU right left P X)
    (f : CMat n → ℝ) (hf : DifferentiableAt ℝ f X)
    (hg : projectedGradient right left f X ≠ 0)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ k : ℕ,
      Orbit.InSharedA2SU right left P
        (expStep right left X (-projectedGradient right left f X) (α * ρ ^ k)) ∧
      f (expStep right left X (-projectedGradient right left f X) (α * ρ ^ k)) <
        f X - c * (α * ρ ^ k) * cFrobSq (projectedGradient right left f X) := by
  have hl : Tendsto (fun k : ℕ => α * ρ ^ k) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul α
    · exact Filter.Eventually.of_forall (fun k => mul_pos hα (pow_pos hρ k))
  obtain ⟨k, hk⟩ := (hl.eventually (expStep_armijo right left f X hf hg c hc hc1)).exists
  exact ⟨k, expStep_in_family right left P X _ hX _, hk⟩

section AmbientSmoothness
open GS.UnitarySharing (MatrixOrbit HorizontalModel sharedOrbitChartedSpace sharedOrbitIsManifold)
variable (P : CMat n)
local instance : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _
local instance : ChartedSpace (HorizontalModel right left P) (MatrixOrbit right left P) :=
  sharedOrbitChartedSpace right left P
local instance : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤ (MatrixOrbit right left P) :=
  sharedOrbitIsManifold right left P

/-- Smooth SU-direction field in the surrounding U orbit. This is not advertised
as a registered section of an as-yet-unbuilt SU tangent bundle. -/
theorem projectedGradient_smooth_on_unitary_orbit (f : CMat n → ℝ)
    (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f) :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, CMat n)) ⊤
      (fun X : MatrixOrbit right left P => projectedGradient right left f X.val) := by
  have hgrad : ContDiff ℝ (⊤ : WithTop ℕ∞) (ambientGradient f) :=
    GS.UnitarySharing.ambientGradient_contDiff_of_loss f hf (by simp)
  exact (pointProjection_contMDiff_on_unitary_orbit right left P).comp
    (contMDiff_id.prodMk_space
      (hgrad.comp_contMDiff (GS.UnitarySharing.sharedOrbit_val_contMDiff right left P)))
end AmbientSmoothness

end GS.SpecialUnitarySharing
