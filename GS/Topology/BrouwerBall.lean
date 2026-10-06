module

public import GS.Topology.BrouwerFixedPoint
public import GS.Topology.Brouwer.Brouwer
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Transfer from the standard simplex to a closed ball. The construction embeds
finite-dimensional coordinates in a sufficiently large affine simplex and retracts
that simplex to the closed unit ball by radial clamping. -/
noncomputable section
open scoped BigOperators
namespace GS.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous radial retraction onto the closed unit ball. -/
def unitBallClamp (x : E) : Metric.closedBall (0 : E) 1 :=
  ⟨(max 1 ‖x‖)⁻¹ • x, by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))]
    exact (inv_mul_le_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr
      (by simpa using le_max_right (1 : ℝ) ‖x‖)⟩

theorem continuous_unitBallClamp : Continuous (unitBallClamp (E := E)) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.max continuous_norm).inv₀
    (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) ‖x‖)))).smul
    continuous_id

@[simp] theorem unitBallClamp_coe (x : Metric.closedBall (0 : E) 1) :
    unitBallClamp (x : E) = x := by
  apply Subtype.ext
  have hx := mem_closedBall_zero_iff.mp x.property
  simp [unitBallClamp, max_eq_left hx]

variable [FiniteDimensional ℝ E]

/-- A ball fixed-point theorem follows directly from the positive-dimensional
standard-simplex theorem. The `n = 0` ambient case is included by using `n + 1`
barycentric coordinates. -/
theorem closedBall_fixedPoint_of_simplex
    (simplexFP : ∀ n : ℕ+, ∀ f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n),
      Continuous f → ∃ x, f x = x)
    (f : Metric.closedBall (0 : E) 1 → Metric.closedBall (0 : E) 1)
    (hf : Continuous f) : ∃ x, f x = x := by
  let n := Module.finrank ℝ E
  let e : E ≃L[ℝ] (Fin n → ℝ) := (Module.finBasis ℝ E).equivFunL
  let R : ℝ := ‖(e : E →L[ℝ] (Fin n → ℝ))‖ + 1
  let D : ℝ := 2 * (n + 1) * R
  have hR : 0 < R := by dsimp [R]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hcoord (x : Metric.closedBall (0 : E) 1) (i : Fin n) : |e x i| ≤ R := by
    calc
      |e x i| = ‖e x i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖e x‖ := norm_le_pi_norm (e x) i
      _ ≤ ‖(e : E →L[ℝ] (Fin n → ℝ))‖ * ‖(x : E)‖ := (e : E →L[ℝ] (Fin n → ℝ)).le_opNorm x
      _ ≤ ‖(e : E →L[ℝ] (Fin n → ℝ))‖ * 1 :=
        mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp x.property) (norm_nonneg _)
      _ ≤ R := by dsimp [R]; linarith
  let a : Metric.closedBall (0 : E) 1 → Fin n → ℝ := fun x i => (e x i + R) / D
  have ha0 (x : Metric.closedBall (0 : E) 1) (i : Fin n) : 0 ≤ a x i := by
    dsimp [a]
    exact div_nonneg (by have := (abs_le.mp (hcoord x i)).1; linarith) hD.le
  have ha1 (x : Metric.closedBall (0 : E) 1) : ∑ i, a x i ≤ 1 := by
    have hi (i : Fin n) : a x i ≤ (2 * R) / D := by
      apply div_le_div_of_nonneg_right _ hD.le
      have := (abs_le.mp (hcoord x i)).2
      linarith
    calc
      ∑ i, a x i ≤ ∑ _i : Fin n, (2 * R) / D := Finset.sum_le_sum fun i _ => hi i
      _ = (n : ℝ) * (2 * R) / D := by simp [mul_div_assoc]
      _ ≤ 1 := (div_le_one hD).mpr (by dsimp [D]; nlinarith)
  let enc : Metric.closedBall (0 : E) 1 → stdSimplex ℝ (Fin (n + 1)) := fun x =>
    ⟨Fin.cons (1 - ∑ i, a x i) (a x), by
      constructor
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact sub_nonneg.mpr (ha1 x)
        · exact ha0 x j
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        ring⟩
  have henc : Continuous enc := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Continuous (fun x : Metric.closedBall (0 : E) 1 => 1 - ∑ j, (e (x : E) j + R) / D)
      fun_prop
    · change Continuous (fun x : Metric.closedBall (0 : E) 1 => (e (x : E) j + R) / D)
      fun_prop
  let dec : stdSimplex ℝ (Fin (n + 1)) → E :=
    fun y => e.symm (fun i => D * y.val i.succ - R)
  have hdec : Continuous dec := by
    exact e.symm.continuous.comp (continuous_pi fun i =>
      (continuous_const.mul ((continuous_apply i.succ).comp continuous_subtype_val)).sub
        continuous_const)
  have hdecenc (x : Metric.closedBall (0 : E) 1) : dec (enc x) = (x : E) := by
    apply e.injective
    simp only [dec, ContinuousLinearEquiv.apply_symm_apply]
    apply funext
    intro i
    change D * ((e (x : E) i + R) / D) - R = e (x : E) i
    field_simp
    ring
  let ret : stdSimplex ℝ (Fin (n + 1)) → Metric.closedBall (0 : E) 1 :=
    fun y => unitBallClamp (dec y)
  have hret : Continuous ret := continuous_unitBallClamp.comp hdec
  have hretenc (x : Metric.closedBall (0 : E) 1) : ret (enc x) = x := by
    dsimp [ret]
    rw [hdecenc, unitBallClamp_coe]
  obtain ⟨y, hy⟩ := simplexFP ⟨n + 1, Nat.succ_pos _⟩ (enc ∘ f ∘ ret)
    (henc.comp (hf.comp hret))
  refine ⟨ret y, ?_⟩
  have hh := congrArg ret hy
  simpa only [Function.comp_apply, hretenc] using hh

/-- Brouwer fixed point for every finite-dimensional real normed space, proved
from the combinatorial standard-simplex theorem. -/
instance instBrouwerFixedPoint : BrouwerFixedPoint E where
  brouwer_fixed_point f hf := closedBall_fixedPoint_of_simplex
    (fun n g hg => Brouwer (n := n) g hg) f hf

/-- The unconditional closed-unit-ball fixed-point theorem. -/
theorem brouwer_fixed_point_unitBall
    (f : Metric.closedBall (0 : E) 1 → Metric.closedBall (0 : E) 1)
    (hf : Continuous f) : ∃ x, f x = x :=
  BrouwerFixedPoint.brouwer_fixed_point f hf

end GS.Topology
