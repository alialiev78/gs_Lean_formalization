module

public import GS.M4Certificate

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! The computed matrix violates the actual determinant inequality.
A proof script for necessity is supplied separately in M4Necessary.lean.
 -/

noncomputable section
open Matrix
namespace GS.M4

def root6 : ℝ := Real.sqrt 2 * Real.sqrt 3

theorem root6_pos : 0 < root6 := by
  unfold root6
  exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))

theorem root6_sq : root6^2 = 6 := by
  unfold root6
  rw [mul_pow, sqrt2_sq, sqrt3_sq]
  norm_num

def absDetBlock (A : Mat 6) (i j : Fin 3) : ℝ := |detBlock A i j|

def absDetTable : Mat 3 :=
  !![3*root6/16, 1/8, 3/8;
     3*root6/16, 3/8, 1/8;
     1/16, 3*root6/16, 3*root6/16]

theorem absDetTable_Q : absDetBlock Q = absDetTable := by
  ext i j
  have hd := congrFun (congrFun detTable_Q i) j
  unfold absDetBlock
  rw [hd]
  fin_cases i <;> fin_cases j <;>
    simp [detTable,absDetTable,root6,abs_mul,abs_div,
      abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ)),
      abs_of_nonneg (Real.sqrt_nonneg (3 : ℝ))] <;> ring

def determinantObstruction (A : Mat 6) : Prop :=
  let d := absDetBlock A
  (1-d 0 2*d 1 0/d 2 1)*(1-d 0 2*d 2 1/d 1 0) ≥ d 0 0*d 2 2/d 1 1

theorem obstruction_denominator_nonzero :
    absDetBlock Q 2 1 * absDetBlock Q 1 0 * absDetBlock Q 1 1 ≠ 0 := by
  rw [absDetTable_Q]
  change (3*root6/16)*(3*root6/16)*(3/8 : ℝ) ≠ 0
  have h : 0 < (3*root6/16)*(3*root6/16)*(3/8 : ℝ) := by
    have := root6_pos
    positivity
  exact ne_of_gt h

theorem Q_violates_determinantObstruction : ¬ determinantObstruction Q := by
  have ht : root6 ≠ 0 := ne_of_gt root6_pos
  have hr : (3/8 : ℝ)*(3*root6/16)/(3*root6/16) = 3/8 := by
    field_simp [ht] <;> ring
  have hv : (3*root6/16)*(3*root6/16)/(3/8 : ℝ) = 9/16 := by
    nlinarith [root6_sq]
  unfold determinantObstruction
  rw [absDetTable_Q]
  change ¬ ((1-(3/8 : ℝ)*(3*root6/16)/(3*root6/16))*
    (1-(3/8 : ℝ)*(3*root6/16)/(3*root6/16)) ≥
    (3*root6/16)*(3*root6/16)/(3/8 : ℝ))
  rw [hr,hv]
  norm_num

/-- Scalar end of the necessity proof, after the block determinants have been
expressed in terms of absolute matrix entries. -/
theorem scalar_obstruction (a b e f c g : ℝ)
    (ha : a^2+c^2=1) (he : e^2+g^2=1) (hb : b^2 ≤ 1) (hf : f^2 ≤ 1) :
    (1-b^2*e^2)*(1-a^2*f^2) ≥ c^2*g^2 := by
  have ha' : a^2 ≤ 1 := by nlinarith [sq_nonneg c]
  have he' : e^2 ≤ 1 := by nlinarith [sq_nonneg g]
  have haf : 0 ≤ 1-a^2*f^2 := by
    nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hf)]
  have h1 := mul_nonneg
    (mul_nonneg (sq_nonneg e) (sub_nonneg.mpr hb)) haf
  have h2 := mul_nonneg
    (mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hf)) (sub_nonneg.mpr he')
  have hc : c^2=1-a^2 := by linarith
  have hg : g^2=1-e^2 := by linarith
  rw [hc,hg]
  nlinarith [h1,h2]

/-- Explicitly CONDITIONAL: it consumes a separately supplied generic necessity result.
This is not an unconditional theorem that the m=4 factorization is impossible. -/
theorem Q_not_mem_A4Orth_of_necessaryCondition
    (hnecessary : ∀ A : Mat 6, InA4Orth 2 2 2 2 P P P A →
      absDetBlock A 2 1 * absDetBlock A 1 0 * absDetBlock A 1 1 ≠ 0 →
      determinantObstruction A) :
    ¬ InA4Orth 2 2 2 2 P P P Q := by
  intro h
  exact Q_violates_determinantObstruction
    (hnecessary Q h obstruction_denominator_nonzero)

end GS.M4
