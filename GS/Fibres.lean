module

public import GS.Frobenius
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Tactic.FunProp

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The algebra of the original fibre proof

This file retains the manuscript's unit-circle/rank-one parameterization.
No alternative polar-logarithm parameterization is substituted.
It does not identify a neighbourhood of the matrix family with this model;
that analytic/topological bridge is listed as an outstanding goal.

-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS

abbrev CircleVector := Fin 2 → ℝ

def OnCircle (u : CircleVector) : Prop := u 0 ^ 2 + u 1 ^ 2 = 1

def outer {κ : Type*} (u : CircleVector) (z : κ → ℝ) : Matrix (Fin 2) κ ℝ :=
  fun i j => u i * z j

/-- The rank-one parameter map is continuous, without a nonzero hypothesis. -/
theorem continuous_outer {κ : Type*} :
    Continuous (fun p : CircleVector × (κ → ℝ) => outer p.1 p.2) := by
  unfold outer
  fun_prop

theorem onCircle_neg {u : CircleVector} (hu : OnCircle u) : OnCircle (-u) := by
  dsimp [OnCircle] at *
  nlinarith

theorem onCircle_has_nonzero {u : CircleVector} (hu : OnCircle u) : ∃ i, u i ≠ 0 := by
  by_cases h : u 0 = 0
  · refine ⟨1, ?_⟩
    intro h1
    dsimp [OnCircle] at hu
    rw [h, h1] at hu
    norm_num at hu
  · exact ⟨0,h⟩

theorem outer_simultaneous_neg {κ : Type*} (u : CircleVector) (z : κ → ℝ) :
    outer (-u) (-z) = outer u z := by
  ext i j
  simp [outer]

theorem outer_zero_iff {κ : Type*} {u : CircleVector} (hu : OnCircle u) (z : κ → ℝ) :
    outer u z = 0 ↔ z = 0 := by
  constructor
  · intro h
    obtain ⟨i,hi⟩ := onCircle_has_nonzero hu
    funext j
    have he : u i * z j = 0 := congrFun (congrFun h i) j
    exact (mul_eq_zero.mp he).resolve_left hi
  · rintro rfl
    ext i j
    simp [outer]

theorem outer_col_sq {κ : Type*} {u : CircleVector} (hu : OnCircle u)
    (z : κ → ℝ) (j : κ) :
    outer u z 0 j ^ 2 + outer u z 1 j ^ 2 = z j ^ 2 := by
  calc
    outer u z 0 j ^ 2 + outer u z 1 j ^ 2 =
        (u 0 ^ 2 + u 1 ^ 2) * z j ^ 2 := by unfold outer; ring
    _ = z j ^ 2 := by rw [hu]; ring

/-- The circle variable does not change the squared Frobenius radius. -/
theorem frobSq_outer {κ : Type*} [Fintype κ] {u : CircleVector}
    (hu : OnCircle u) (z : κ → ℝ) :
    frobSq (outer u z) = ∑ j, z j ^ 2 := by
  unfold frobSq frobInner
  rw [Fin.sum_univ_two, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [pow_two] using outer_col_sq hu z j

/-- Equality plus one equal nonzero column coefficient fixes both factors. -/
theorem outer_unique_of_column {κ : Type*} {u v : CircleVector} {z w : κ → ℝ}
    (hu : OnCircle u) (h : outer u z = outer v w)
    (j : κ) (hzj : z j ≠ 0) (hj : z j = w j) : u = v ∧ z = w := by
  have huv : u = v := by
    funext i
    have he := congrFun (congrFun h i) j
    change u i * z j = v i * w j at he
    rw [← hj] at he
    exact mul_right_cancel₀ hzj he
  obtain ⟨i,hi⟩ := onCircle_has_nonzero hu
  refine ⟨huv, ?_⟩
  funext k
  have he := congrFun (congrFun h i) k
  change u i * z k = v i * w k at he
  rw [← huv] at he
  exact mul_left_cancel₀ hi he

/-- Nonzero rank-one fibres: exactly the simultaneous sign ambiguity. -/
theorem outer_fibres_nonzero {κ : Type*} {u v : CircleVector} {z w : κ → ℝ}
    (hu : OnCircle u) (hv : OnCircle v) (hz : z ≠ 0) :
    outer u z = outer v w ↔ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w) := by
  constructor
  · intro h
    have hex : ∃ j, z j ≠ 0 := by
      by_contra hn
      apply hz
      funext j
      by_contra hj
      exact hn ⟨j,hj⟩
    obtain ⟨j,hj⟩ := hex
    have he : z j ^ 2 = w j ^ 2 := by
      rw [← outer_col_sq hu z j, h, outer_col_sq hv w j]
    have hp : (z j - w j) * (z j + w j) = 0 := by nlinarith [he]
    rcases mul_eq_zero.mp hp with hp | hp
    · left
      exact outer_unique_of_column hu h j hj (sub_eq_zero.mp hp)
    · right
      have h' : outer u z = outer (-v) (-w) := by
        rw [outer_simultaneous_neg]
        exact h
      apply outer_unique_of_column hu h' j hj
      change z j = -w j
      linarith
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rfl
    · exact outer_simultaneous_neg v w

/-- Explicit failure of uniqueness at the zero stratum. -/
theorem outer_zero_fibre {κ : Type*} (u v : CircleVector) :
    outer u (0 : κ → ℝ) = outer v (0 : κ → ℝ) := by
  ext i j
  simp [outer]

/-- The complete fibre classification includes the collapsed zero stratum.
No choice of a nonzero coordinate is required in the statement. -/
theorem outer_fibres {κ : Type*} {u v : CircleVector} {z w : κ → ℝ}
    (hu : OnCircle u) (hv : OnCircle v) :
    outer u z = outer v w ↔
      (z = 0 ∧ w = 0) ∨ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w) := by
  by_cases hz : z = 0
  · subst z
    have he : outer u (0 : κ → ℝ) = 0 := (outer_zero_iff hu 0).mpr rfl
    rw [he]
    constructor
    · intro h
      exact Or.inl ⟨rfl, (outer_zero_iff hv w).mp h.symm⟩
    · rintro (⟨_, rfl⟩ | ⟨_, hw⟩ | ⟨_, hw⟩)
      · exact ((outer_zero_iff hv 0).mpr rfl).symm
      · exact ((outer_zero_iff hv w).mpr hw.symm).symm
      · have hw0 : w = 0 := neg_eq_zero.mp hw.symm
        exact ((outer_zero_iff hv w).mpr hw0).symm
  · rw [outer_fibres_nonzero hu hv hz]
    simp only [hz, false_and, false_or]

def T (u : CircleVector) : Mat 2 := !![u 0, u 1; u 1, -u 0]

theorem continuous_T : Continuous T := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp [T] <;> fun_prop

theorem T_transpose (u : CircleVector) : (T u)ᵀ = T u := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem T_injective : Function.Injective T := by
  intro u v h
  have h0 : u 0 = v 0 := congrFun (congrFun h 0) 0
  have h1 : u 1 = v 1 := congrFun (congrFun h 0) 1
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem T_sq {u : CircleVector} (hu : OnCircle u) : T u * T u = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;>
    dsimp [OnCircle] at hu <;> nlinarith [hu]

theorem T_orthogonal {u : CircleVector} (hu : OnCircle u) : Orthogonal (T u) := by
  constructor <;> rw [T_transpose, T_sq hu]

theorem T_det {u : CircleVector} (hu : OnCircle u) : Matrix.det (T u) = -1 := by
  rw [Matrix.det_fin_two]
  dsimp [T,OnCircle] at *
  nlinarith

def middleBlock (a b : ℝ) (u : CircleVector) : Mat 2 :=
  ((a+b)/2) • (1 : Mat 2) + ((a-b)/2) • T u

theorem middleBlock_swap (a b : ℝ) (u : CircleVector) :
    middleBlock b a (-u) = middleBlock a b u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [middleBlock,T,Matrix.one_apply] <;> ring

theorem middleBlock_equal (a : ℝ) (u : CircleVector) :
    middleBlock a a u = a • (1 : Mat 2) := by
  ext i j
  simp [middleBlock] <;> ring

theorem middleBlock_trace (a b : ℝ) (u : CircleVector) :
    middleBlock a b u 0 0 + middleBlock a b u 1 1 = a + b := by
  simp [middleBlock,T,Matrix.one_apply]
  ring

/-- The sign argument at the scalar-difference level, used in the fibre proof. -/
theorem middleBlock_eq_sum_and_difference
    (a b a' b' : ℝ) (u v : CircleVector)
    (h : middleBlock a b u = middleBlock a' b' v) :
    a+b=a'+b' ∧ (a-b) • T u = (a'-b') • T v := by
  have hs : a+b=a'+b' := by
    rw [← middleBlock_trace a b u, h, middleBlock_trace]
  refine ⟨hs, ?_⟩
  ext i j
  have he := congrFun (congrFun h i) j
  change ((a+b)/2) * (1 : Mat 2) i j + ((a-b)/2) * T u i j =
    ((a'+b')/2) * (1 : Mat 2) i j + ((a'-b')/2) * T v i j at he
  change (a-b) * T u i j = (a'-b') * T v i j
  rw [hs] at he
  linarith

/-- All two-by-two minors vanish for the rank-one model; this is an algebraic
statement, not yet a theorem about the ambient matrix family's neighbourhood. -/
theorem outer_minor_zero {κ : Type*} (u : CircleVector) (z : κ → ℝ)
    (i j : Fin 2) (k l : κ) :
    outer u z i k * outer u z j l - outer u z i l * outer u z j k = 0 := by
  unfold outer
  ring

/-- The parameter map lands in the actual determinantal cone, expressed with
mathlib's matrix rank (not only by the vanishing of displayed minors). -/
theorem rank_outer_le_one {κ : Type*} [Fintype κ] [DecidableEq κ]
    (u : CircleVector) (z : κ → ℝ) : Matrix.rank (outer u z) ≤ 1 := by
  let U : Matrix (Fin 2) (Fin 1) ℝ := fun i _ => u i
  let Z : Matrix (Fin 1) κ ℝ := fun _ j => z j
  have h : outer u z = U * Z := by
    ext i j
    simp [outer, U, Z, Matrix.mul_apply]
  rw [h]
  exact (Matrix.rank_mul_le_left U Z).trans (by simpa using Matrix.rank_le_card_width U)

end GS
