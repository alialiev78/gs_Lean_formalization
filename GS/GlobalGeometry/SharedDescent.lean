module

public import GS.GlobalGeometry.SharedFactorCurves
public import GS.RiemannianCompletion.ExponentialStep
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Certified descent with actual tied orthogonal factors

A generator lift of the exact shared projection is selected from its proved
existence.  Its matrix-exponential step preserves the actual physical block
ties for every real time when both block sizes are positive and divide the
matrix dimension.  The negative projected ambient gradient has loss slope
minus its squared Frobenius norm; Armijo steps and finite geometric
backtracking follow from differentiability at the base point.

The selected lift need not be unique.  No efficient solver, independence of
factor representation, shared-image manifold, or optimizer convergence rate
is asserted here.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.RiemannianCompletion Filter
open scoped Topology
namespace GS.GlobalGeometry
variable {n : ℕ}

/-- A certified lift of the exact shared core projection. -/
def sharedProjectionGenerators (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P L R Z : Mat n) :
    sharedSkewSpace (n := n) b₂ τ₂ × sharedSkewSpace (n := n) b₁ τ₁ :=
  Classical.choose (frobProjection_mem (sharedCore b₁ b₂ τ₁ τ₂ P) (pull L (P * R) Z))

theorem sharedProjectionGenerators_core (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R Z : Mat n) :
    sharedCoreMap b₁ b₂ τ₁ τ₂ P (sharedProjectionGenerators b₁ b₂ τ₁ τ₂ P L R Z) =
      frobProjection (sharedCore b₁ b₂ τ₁ τ₂ P) (pull L (P * R) Z) :=
  Classical.choose_spec (frobProjection_mem (sharedCore b₁ b₂ τ₁ τ₂ P) (pull L (P * R) Z))

/-- Exponential step from the certified shared generator pair. -/
def sharedExpStep (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P L R Z : Mat n) (t : ℝ) : Mat n :=
  gsExpCurve L P R (sharedProjectionGenerators b₁ b₂ τ₁ τ₂ P L R Z).1.val
    (sharedProjectionGenerators b₁ b₂ τ₁ τ₂ P L R Z).2.val t

@[simp] theorem sharedExpStep_zero (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P L R Z : Mat n) :
    sharedExpStep b₁ b₂ τ₁ τ₂ P L R Z 0 = product2 L P R :=
  gsExpCurve_zero _ _ _ _ _

/-- The image of the actual tied orthogonal factors. -/
def InSharedA2Orth (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : Mat n) : Prop :=
  ∃ L R, SharedOrthogonalFactor b₂ τ₂ L ∧ SharedOrthogonalFactor b₁ τ₁ R ∧
    X = product2 L P R

/-- Every step size preserves the original finite tied block constraints. -/
theorem sharedExpStep_feasible (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hbn₁ : b₁ ∣ n) (hbn₂ : b₂ ∣ n)
    (P L R Z : Mat n) (hL : SharedOrthogonalFactor b₂ τ₂ L)
    (hR : SharedOrthogonalFactor b₁ τ₁ R) (t : ℝ) :
    InSharedA2Orth b₁ b₂ τ₁ τ₂ P (sharedExpStep b₁ b₂ τ₁ τ₂ P L R Z t) := by
  let v := sharedProjectionGenerators b₁ b₂ τ₁ τ₂ P L R Z
  exact ⟨gsExpLeft L v.1.val t, gsExpRight R v.2.val t,
    gsExpLeft_shared b₂ τ₂ hb₂ hbn₂ L v.1.val hL v.1.property t,
    gsExpRight_shared b₁ τ₁ hb₁ hbn₁ R v.2.val hR v.2.property t, rfl⟩

theorem sharedExpStep_derivative (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R Z : Mat n) (hP : Orthogonal P) :
    HasDerivAt (sharedExpStep b₁ b₂ τ₁ τ₂ P L R Z)
      (exactSharedProjection b₁ b₂ τ₁ τ₂ P L R Z) 0 := by
  let v := sharedProjectionGenerators b₁ b₂ τ₁ τ₂ P L R Z
  have he : exactSharedProjection b₁ b₂ τ₁ τ₂ P L R Z =
      tangentParam L P R v.1.val v.2.val := by
    unfold exactSharedProjection
    rw [← sharedProjectionGenerators_core]
    exact lift_sharedCoreMap P L R v.1.val v.2.val hP
  rw [he]
  exact gsExpCurve_initial_derivative L P R v.1.val v.2.val hP

theorem pull_frobInner (L R A B : Mat n) (hL : Orthogonal L) (hR : Orthogonal R) :
    frobInner (pull L R A) (pull L R B) = frobInner A B := by
  unfold pull
  rw [frobInner_right_orthogonal Rᵀ hR.transpose,
    frobInner_left_orthogonal Lᵀ hL.transpose]

theorem exactSharedProjection_normal (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R Z Y : Mat n) (hP : Orthogonal P) (hL : Orthogonal L) (hR : Orthogonal R)
    (hY : SharedDirection b₁ b₂ τ₁ τ₂ P L R Y) :
    frobInner (Z - exactSharedProjection b₁ b₂ τ₁ τ₂ P L R Z) Y = 0 := by
  rw [← pull_frobInner L (P * R) _ Y hL (hP.mul hR)]
  have he : pull L (P * R) (Z - exactSharedProjection b₁ b₂ τ₁ τ₂ P L R Z) =
      pull L (P * R) Z - frobProjection (sharedCore b₁ b₂ τ₁ τ₂ P) (pull L (P * R) Z) := by
    simp only [pull, Matrix.mul_sub, Matrix.sub_mul]
    change pull L (P * R) Z - pull L (P * R)
      (lift L (P * R) (frobProjection (sharedCore b₁ b₂ τ₁ τ₂ P) (pull L (P * R) Z))) = _
    rw [pull_lift L (P * R) _ hL (hP.mul hR)]
    rfl
  rw [he]
  exact frobProjection_normal _ _ _
    ((sharedDirection_iff_core b₁ b₂ τ₁ τ₂ P L R Y hP hL hR).mp hY)

theorem exactSharedProjection_neg (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P L R Z : Mat n) :
    exactSharedProjection b₁ b₂ τ₁ τ₂ P L R (-Z) =
      -exactSharedProjection b₁ b₂ τ₁ τ₂ P L R Z := by
  simp only [exactSharedProjection, pull, lift, Matrix.mul_neg, Matrix.neg_mul, map_neg]

/-- The gradient in the actual image of the tied factor differential. -/
def sharedProjectedGradient (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R : Mat n) (f : Mat n → ℝ) : Mat n :=
  exactSharedProjection b₁ b₂ τ₁ τ₂ P L R (ambientGradient f (product2 L P R))

theorem sharedProjectedGradient_represents (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R : Mat n) (hP : Orthogonal P) (hL : Orthogonal L) (hR : Orthogonal R)
    (f : Mat n → ℝ) (Y : Mat n) (hY : SharedDirection b₁ b₂ τ₁ τ₂ P L R Y) :
    frobInner (sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f) Y =
      fderiv ℝ f (product2 L P R) Y := by
  rw [ambientGradient_represents]
  have hn := exactSharedProjection_normal b₁ b₂ τ₁ τ₂ P L R
    (ambientGradient f (product2 L P R)) Y hP hL hR hY
  rw [frobInner_sub_left] at hn
  exact (sub_eq_zero.mp hn).symm

theorem sharedProjectedGradient_energy (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R : Mat n) (hP : Orthogonal P) (hL : Orthogonal L) (hR : Orthogonal R)
    (f : Mat n → ℝ) :
    frobInner (ambientGradient f (product2 L P R))
      (sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f) =
      frobSq (sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f) := by
  have he := sharedProjectedGradient_represents b₁ b₂ τ₁ τ₂ P L R hP hL hR f
    (sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f)
    (exactSharedProjection_in_direction b₁ b₂ τ₁ τ₂ P L R
      (ambientGradient f (product2 L P R)) hP hL hR)
  rw [ambientGradient_represents] at he
  exact he.symm

/-- Zero projected gradient is exactly stationarity along all shared factor
velocities once the full-block curve equivalence is applied. -/
theorem sharedProjectedGradient_eq_zero_iff (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R : Mat n) (hP : Orthogonal P) (hL : Orthogonal L) (hR : Orthogonal R)
    (f : Mat n → ℝ) :
    sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f = 0 ↔
      ∀ Y, SharedDirection b₁ b₂ τ₁ τ₂ P L R Y → fderiv ℝ f (product2 L P R) Y = 0 := by
  constructor
  · intro hg Y hY
    rw [← sharedProjectedGradient_represents b₁ b₂ τ₁ τ₂ P L R hP hL hR f Y hY,
      hg, frobInner_zero_left]
  · intro hn
    apply (frobSq_eq_zero_iff _).mp
    rw [← sharedProjectedGradient_energy b₁ b₂ τ₁ τ₂ P L R hP hL hR f,
      ← ambientGradient_represents]
    exact hn _ (exactSharedProjection_in_direction b₁ b₂ τ₁ τ₂ P L R _ hP hL hR)

/-- The negative ambient gradient is first exactly projected and then lifted
to a feasible exponential factor update. -/
def sharedDescentStep (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R : Mat n) (f : Mat n → ℝ) : ℝ → Mat n :=
  sharedExpStep b₁ b₂ τ₁ τ₂ P L R (-ambientGradient f (product2 L P R))

@[simp] theorem sharedDescentStep_zero (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R : Mat n) (f : Mat n → ℝ) :
    sharedDescentStep b₁ b₂ τ₁ τ₂ P L R f 0 = product2 L P R :=
  sharedExpStep_zero _ _ _ _ _ _ _ _

theorem sharedDescentStep_feasible (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hbn₁ : b₁ ∣ n) (hbn₂ : b₂ ∣ n)
    (P L R : Mat n) (hL : SharedOrthogonalFactor b₂ τ₂ L)
    (hR : SharedOrthogonalFactor b₁ τ₁ R) (f : Mat n → ℝ) (t : ℝ) :
    InSharedA2Orth b₁ b₂ τ₁ τ₂ P (sharedDescentStep b₁ b₂ τ₁ τ₂ P L R f t) :=
  sharedExpStep_feasible b₁ b₂ τ₁ τ₂ hb₁ hb₂ hbn₁ hbn₂ P L R _ hL hR t

/-- The actual velocity is the negative exact projected gradient. -/
theorem sharedDescentStep_derivative (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R : Mat n) (hP : Orthogonal P) (f : Mat n → ℝ) :
    HasDerivAt (sharedDescentStep b₁ b₂ τ₁ τ₂ P L R f)
      (-sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f) 0 := by
  simpa only [sharedDescentStep, sharedProjectedGradient, exactSharedProjection_neg] using
    sharedExpStep_derivative b₁ b₂ τ₁ τ₂ P L R
      (-ambientGradient f (product2 L P R)) hP

theorem shared_negative_gradient_loss_derivative (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R : Mat n) (hP : Orthogonal P) (hL : Orthogonal L) (hR : Orthogonal R)
    (f : Mat n → ℝ) (hf : DifferentiableAt ℝ f (product2 L P R)) :
    HasDerivAt (fun t => f (sharedDescentStep b₁ b₂ τ₁ τ₂ P L R f t))
      (-frobSq (sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f)) 0 := by
  have hd := sharedExpStep_derivative b₁ b₂ τ₁ τ₂ P L R
    (-ambientGradient f (product2 L P R)) hP
  rw [exactSharedProjection_neg] at hd
  have hc := ambientGradient_chain hf hd (sharedExpStep_zero _ _ _ _ _ _ _ _)
  have he : frobInner (ambientGradient f (product2 L P R))
      (-sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f) =
      -frobSq (sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f) := by
    rw [show -sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f =
      (-1 : ℝ) • sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f by simp,
      frobInner_smul_right, sharedProjectedGradient_energy b₁ b₂ τ₁ τ₂ P L R hP hL hR f]
    ring
  exact he ▸ hc

/-- Strict Armijo decrease for every sufficiently small positive step. -/
theorem shared_descent_armijo (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R : Mat n) (hP : Orthogonal P) (hL : Orthogonal L) (hR : Orthogonal R)
    (f : Mat n → ℝ) (hf : DifferentiableAt ℝ f (product2 L P R))
    (hg : sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f ≠ 0)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      f (sharedDescentStep b₁ b₂ τ₁ τ₂ P L R f t) <
        f (product2 L P R) - c * t * frobSq (sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f) := by
  have hh := armijo_of_negative_derivative
    (shared_negative_gradient_loss_derivative b₁ b₂ τ₁ τ₂ P L R hP hL hR f hf)
    (frobSq_pos_of_ne_zero hg) c hc hc1
  simpa only [sharedDescentStep_zero] using hh

/-- Finite geometric backtracking.  Every trial remains feasible under
`sharedDescentStep_feasible`; pointwise differentiability gives no uniform
bound on the number of reductions. -/
theorem shared_descent_backtracking (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R : Mat n) (hP : Orthogonal P) (hL : Orthogonal L) (hR : Orthogonal R)
    (f : Mat n → ℝ) (hf : DifferentiableAt ℝ f (product2 L P R))
    (hg : sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f ≠ 0)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ k : ℕ,
      f (sharedDescentStep b₁ b₂ τ₁ τ₂ P L R f (α * ρ ^ k)) <
        f (product2 L P R) - c * (α * ρ ^ k) *
          frobSq (sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f) := by
  have hlimit : Tendsto (fun k : ℕ => α * ρ ^ k) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul α
    · exact Filter.Eventually.of_forall (fun k => mul_pos hα (pow_pos hρ k))
  exact (hlimit.eventually
    (shared_descent_armijo b₁ b₂ τ₁ τ₂ P L R hP hL hR f hf hg c hc hc1)).exists

/-- An end-to-end finite backtracking step satisfying both the actual tied
factor constraints and strict Armijo decrease. -/
theorem exists_feasible_shared_armijo_step (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hbn₁ : b₁ ∣ n) (hbn₂ : b₂ ∣ n)
    (P L R : Mat n) (hP : Orthogonal P)
    (hL : SharedOrthogonalFactor b₂ τ₂ L) (hR : SharedOrthogonalFactor b₁ τ₁ R)
    (f : Mat n → ℝ) (hf : DifferentiableAt ℝ f (product2 L P R))
    (hg : sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f ≠ 0)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ k : ℕ,
      InSharedA2Orth b₁ b₂ τ₁ τ₂ P
        (sharedDescentStep b₁ b₂ τ₁ τ₂ P L R f (α * ρ ^ k)) ∧
      f (sharedDescentStep b₁ b₂ τ₁ τ₂ P L R f (α * ρ ^ k)) <
        f (product2 L P R) - c * (α * ρ ^ k) *
          frobSq (sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f) := by
  obtain ⟨k, hk⟩ := shared_descent_backtracking b₁ b₂ τ₁ τ₂ P L R hP hL.2.1 hR.2.1
    f hf hg c hc hc1 α ρ hα hρ hρ1
  exact ⟨k, sharedDescentStep_feasible b₁ b₂ τ₁ τ₂ hb₁ hb₂ hbn₁ hbn₂
    P L R hL hR f (α * ρ ^ k), hk⟩

/-- A local minimum along the feasible negative-gradient curve is stationary. -/
theorem shared_localMin_stationary (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R : Mat n) (hP : Orthogonal P) (hL : Orthogonal L) (hR : Orthogonal R)
    (f : Mat n → ℝ) (hf : DifferentiableAt ℝ f (product2 L P R))
    (hmin : IsLocalMin (fun t : ℝ => f (sharedDescentStep b₁ b₂ τ₁ τ₂ P L R f t)) 0) :
    sharedProjectedGradient b₁ b₂ τ₁ τ₂ P L R f = 0 := by
  have hz := hmin.hasDerivAt_eq_zero
    (shared_negative_gradient_loss_derivative b₁ b₂ τ₁ τ₂ P L R hP hL hR f hf)
  exact (frobSq_eq_zero_iff _).mp (neg_eq_zero.mp hz)

end GS.GlobalGeometry
