module

public import GS.GlobalGeometry.CayleyRetraction
public import GS.GlobalGeometry.ProjectedDerivative
public import GS.RiemannianCompletion.ExponentialStep
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Projected descent with arbitrary overlap

For independently chosen supported orthogonal factors, the exact matrix
projection gives a feasible Cayley descent curve and finite geometric
backtracking. No no-overlap hypothesis or overlap manifold atlas is needed.
Stationarity here refers to the image of the factor differential.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.RiemannianCompletion Filter
open scoped Topology

namespace GS.GlobalGeometry

variable {n : ℕ}

/-- The ambient gradient projected onto the factor-differential image. -/
def projectedGradient (b₁ b₂ : Fin n → ℕ) (f : Mat n → ℝ) (X : Mat n) : Mat n :=
  pointProjection b₁ b₂ X (ambientGradient f X)

variable (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (L R : Mat n)
variable (hsL : Supported b₂ L) (hsR : Supported b₁ R)
variable (hL : Orthogonal L) (hR : Orthogonal R)
include hsL hsR hL hR

theorem projectedGradient_in_direction (f : Mat n → ℝ) :
    TwoFactorDirection b₁ b₂ L (permMatrix σ) R
      (projectedGradient b₁ b₂ f (product2 L (permMatrix σ) R)) :=
  pointProjection_in_direction b₁ b₂ σ L R _ hsL hsR hL hR

theorem projectedGradient_fixed (f : Mat n → ℝ) :
    let X := product2 L (permMatrix σ) R
    pointProjection b₁ b₂ X (projectedGradient b₁ b₂ f X) =
      projectedGradient b₁ b₂ f X :=
  pointProjection_idempotent b₁ b₂ σ L R _ hsL hsR hL hR

/-- The projected gradient represents the loss derivative on every factor
direction, including directions in overlapping block patterns. -/
theorem projectedGradient_represents (f : Mat n → ℝ) (Y : Mat n)
    (hY : TwoFactorDirection b₁ b₂ L (permMatrix σ) R Y) :
    let X := product2 L (permMatrix σ) R
    frobInner (projectedGradient b₁ b₂ f X) Y = fderiv ℝ f X Y := by
  dsimp only
  rw [projectedGradient, pointProjection_self_adjoint b₁ b₂ σ L R _ Y hsL hsR hL hR,
    (pointProjection_fixed_iff b₁ b₂ σ L R Y hsL hsR hL hR).mpr hY,
    ambientGradient_represents]

theorem projectedGradient_energy (f : Mat n → ℝ) :
    let X := product2 L (permMatrix σ) R
    frobInner (ambientGradient f X) (projectedGradient b₁ b₂ f X) =
      frobSq (projectedGradient b₁ b₂ f X) := by
  dsimp only
  have he := projectedGradient_represents b₁ b₂ σ L R hsL hsR hL hR f _
    (projectedGradient_in_direction b₁ b₂ σ L R hsL hsR hL hR f)
  dsimp only at he
  rw [ambientGradient_represents] at he
  exact he.symm

/-- Zero projected gradient is equivalent to vanishing `fderiv` on the factor
directions. For differentiable losses this is first-order stationarity;
without differentiability, `fderiv` uses mathlib's default zero convention. -/
theorem projectedGradient_eq_zero_iff (f : Mat n → ℝ) :
    let X := product2 L (permMatrix σ) R
    projectedGradient b₁ b₂ f X = 0 ↔
      ∀ Y, TwoFactorDirection b₁ b₂ L (permMatrix σ) R Y → fderiv ℝ f X Y = 0 := by
  dsimp only
  constructor
  · intro hg Y hY
    rw [← projectedGradient_represents b₁ b₂ σ L R hsL hsR hL hR f Y hY,
      hg, frobInner_zero_left]
  · intro hn
    apply pointProjection_zero_of_normal b₁ b₂ σ L R _ hsL hsR hL hR
    intro Y hY
    rw [← ambientGradient_represents]
    exact hn Y hY

theorem overlap_negative_gradient_loss_derivative (f : Mat n → ℝ)
    (hf : DifferentiableAt ℝ f (product2 L (permMatrix σ) R)) :
    let X := product2 L (permMatrix σ) R
    HasDerivAt (fun t => f (pointCayleyStep b₁ b₂ X (-projectedGradient b₁ b₂ f X) t))
      (-frobSq (projectedGradient b₁ b₂ f X)) 0 := by
  dsimp only
  let X := product2 L (permMatrix σ) R
  let g := projectedGradient b₁ b₂ f X
  have hg : pointProjection b₁ b₂ X g = g :=
    projectedGradient_fixed b₁ b₂ σ L R hsL hsR hL hR f
  have hn : pointProjection b₁ b₂ X (-g) = -g := by
    rw [show -g = (-1 : ℝ) • g by simp, pointProjection_smul, hg]
  have hd := pointCayleyStep_derivative b₁ b₂ σ L R (-g) hsL hsR hL hR
  change HasDerivAt (pointCayleyStep b₁ b₂ X (-g)) (pointProjection b₁ b₂ X (-g)) 0 at hd
  rw [hn] at hd
  have hc := ambientGradient_chain hf hd (pointCayleyStep_zero_time b₁ b₂ X (-g))
  have he : frobInner (ambientGradient f X) (-g) = -frobSq g := by
    rw [show -g = (-1 : ℝ) • g by simp, frobInner_smul_right,
      projectedGradient_energy b₁ b₂ σ L R hsL hsR hL hR f]
    ring
  rw [he] at hc
  exact hc

/-- Strict Armijo decrease for all sufficiently small positive steps. -/
theorem overlap_cayley_armijo (f : Mat n → ℝ)
    (hf : DifferentiableAt ℝ f (product2 L (permMatrix σ) R))
    (hg : projectedGradient b₁ b₂ f (product2 L (permMatrix σ) R) ≠ 0)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    let X := product2 L (permMatrix σ) R
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      f (pointCayleyStep b₁ b₂ X (-projectedGradient b₁ b₂ f X) t) <
        f X - c * t * frobSq (projectedGradient b₁ b₂ f X) := by
  have hh := armijo_of_negative_derivative
    (overlap_negative_gradient_loss_derivative b₁ b₂ σ L R hsL hsR hL hR f hf)
    (frobSq_pos_of_ne_zero hg) c hc hc1
  simpa only [pointCayleyStep_zero_time] using hh

/-- Geometric backtracking terminates also in the presence of overlap. -/
theorem overlap_cayley_backtracking (f : Mat n → ℝ)
    (hf : DifferentiableAt ℝ f (product2 L (permMatrix σ) R))
    (hg : projectedGradient b₁ b₂ f (product2 L (permMatrix σ) R) ≠ 0)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    let X := product2 L (permMatrix σ) R
    ∃ k : ℕ,
      f (pointCayleyStep b₁ b₂ X (-projectedGradient b₁ b₂ f X) (α * ρ ^ k)) <
        f X - c * (α * ρ ^ k) * frobSq (projectedGradient b₁ b₂ f X) := by
  have hlimit : Tendsto (fun k : ℕ => α * ρ ^ k) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul α
    · exact Filter.Eventually.of_forall (fun k => mul_pos hα (pow_pos hρ k))
  exact (hlimit.eventually
    (overlap_cayley_armijo b₁ b₂ σ L R hsL hsR hL hR f hf hg c hc hc1)).exists

/-- A local minimum along the feasible projected-gradient curve is stationary.
This conclusion does not assume that the overlap orbit has a formalized atlas. -/
theorem overlap_localMin_stationary (f : Mat n → ℝ)
    (hf : DifferentiableAt ℝ f (product2 L (permMatrix σ) R))
    (hmin : IsLocalMin (fun t : ℝ =>
      f (pointCayleyStep b₁ b₂ (product2 L (permMatrix σ) R)
        (-projectedGradient b₁ b₂ f (product2 L (permMatrix σ) R)) t)) 0) :
    projectedGradient b₁ b₂ f (product2 L (permMatrix σ) R) = 0 := by
  have hz := hmin.hasDerivAt_eq_zero
    (overlap_negative_gradient_loss_derivative b₁ b₂ σ L R hsL hsR hL hR f hf)
  exact (frobSq_eq_zero_iff _).mp (neg_eq_zero.mp hz)

end GS.GlobalGeometry

namespace GS.GlobalGeometry
variable {n : ℕ}

/-- An end-to-end feasible Armijo step in the original scalar-indexed family,
with no overlap restriction. -/
theorem inA2Orth_cayley_backtracking (b₁ b₂ : ℕ) (σ : Equiv.Perm (Fin n))
    (X : Mat n) (hX : InA2Orth b₁ b₂ (permMatrix σ) X) (f : Mat n → ℝ)
    (hf : DifferentiableAt ℝ f X)
    (hg : projectedGradient (fun i => i.val / b₁) (fun i => i.val / b₂) f X ≠ 0)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    let g := projectedGradient (fun i => i.val / b₁) (fun i => i.val / b₂) f X
    ∃ k : ℕ,
      InA2Orth b₁ b₂ (permMatrix σ)
        (pointCayleyStep (fun i => i.val / b₁) (fun i => i.val / b₂) X (-g) (α * ρ ^ k)) ∧
      f (pointCayleyStep (fun i => i.val / b₁) (fun i => i.val / b₂) X (-g) (α * ρ ^ k)) <
        f X - c * (α * ρ ^ k) * frobSq g := by
  have hfeasible := pointCayleyStep_inA2Orth b₁ b₂ (permMatrix σ) X
    (-projectedGradient (fun i => i.val / b₁) (fun i => i.val / b₂) f X) hX
  obtain ⟨R, L, hsR, hsL, hR, hL, rfl⟩ := hX
  obtain ⟨k, hk⟩ := overlap_cayley_backtracking
    (fun i => i.val / b₁) (fun i => i.val / b₂) σ L R hsL hsR hL hR
    f hf hg c hc hc1 α ρ hα hρ hρ1
  exact ⟨k, hfeasible _, hk⟩

/-- Every differentiable constrained local minimum in the original family is
stationary for the exact projected gradient, even when the block patterns overlap. -/
theorem inA2Orth_localMin_stationary (b₁ b₂ : ℕ) (σ : Equiv.Perm (Fin n))
    (X : Mat n) (hX : InA2Orth b₁ b₂ (permMatrix σ) X) (f : Mat n → ℝ)
    (hf : DifferentiableAt ℝ f X)
    (hmin : IsLocalMinOn f {Y | InA2Orth b₁ b₂ (permMatrix σ) Y} X) :
    projectedGradient (fun i => i.val / b₁) (fun i => i.val / b₂) f X = 0 := by
  let β₁ : Fin n → ℕ := fun i => i.val / b₁
  let β₂ : Fin n → ℕ := fun i => i.val / b₂
  let γ := pointCayleyStep β₁ β₂ X (-projectedGradient β₁ β₂ f X)
  have hzero : γ 0 = X := pointCayleyStep_zero_time _ _ _ _
  have hfeasible : ∀ t, InA2Orth b₁ b₂ (permMatrix σ) (γ t) :=
    pointCayleyStep_inA2Orth b₁ b₂ (permMatrix σ) X _ hX
  obtain ⟨R, L, hsR, hsL, hR, hL, hprod⟩ := hX
  have hd : DifferentiableAt ℝ γ 0 := by
    dsimp only [γ]
    rw [hprod]
    exact (pointCayleyStep_derivative β₁ β₂ σ L R _ hsL hsR hL hR).differentiableAt
  have ht : Tendsto γ (𝓝 (0 : ℝ))
      (𝓝[{Y | InA2Orth b₁ b₂ (permMatrix σ) Y}] X) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa only [hzero] using
      (show Tendsto γ (𝓝 (0 : ℝ)) (𝓝 (γ 0)) from hd.continuousAt),
      Filter.Eventually.of_forall hfeasible⟩
  have hcurve : IsLocalMin (fun t => f (γ t)) 0 := by
    have hm' : IsLocalMinOn f {Y | InA2Orth b₁ b₂ (permMatrix σ) Y} (γ 0) := by
      simpa only [hzero] using hmin
    exact hm'.comp_tendsto (by simpa only [hzero] using ht)
  rw [hprod] at hf ⊢
  apply overlap_localMin_stationary β₁ β₂ σ L R hsL hsR hL hR f hf
  simpa only [γ, hprod] using hcurve

end GS.GlobalGeometry
