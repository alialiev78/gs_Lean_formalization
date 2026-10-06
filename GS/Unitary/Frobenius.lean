module

public import GS.Unitary.Support
public import GS.Frobenius
public import Mathlib.Data.Complex.BigOperators

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! The Frobenius geometry of complex matrices is a real inner product:
`cFrobInner A B = Re (trace (Aᴴ * B))`. In particular, tangent projections
below are real-linear; no complex inner product is silently substituted. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace GS.UnitaryGeometry
variable {n : ℕ}

def cFrobInner (A B : CMat n) : ℝ :=
  ∑ i, ∑ j, ((A i j).re * (B i j).re + (A i j).im * (B i j).im)
def cFrobSq (A : CMat n) : ℝ := cFrobInner A A
def cFrobDistSq (A B : CMat n) : ℝ := cFrobSq (A-B)

theorem cFrobInner_eq_re_trace (A B : CMat n) :
    cFrobInner A B = (Matrix.trace (Aᴴ * B)).re := by
  simp only [cFrobInner, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]
  exact Finset.sum_comm

theorem cFrobInner_comm (A B : CMat n) : cFrobInner A B = cFrobInner B A := by
  unfold cFrobInner
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  ring
@[simp] theorem cFrobInner_zero_left (A : CMat n) : cFrobInner 0 A = 0 := by
  simp [cFrobInner]
@[simp] theorem cFrobInner_zero_right (A : CMat n) : cFrobInner A 0 = 0 := by
  simp [cFrobInner]
theorem cFrobInner_add_left (A B C : CMat n) :
    cFrobInner (A+B) C = cFrobInner A C + cFrobInner B C := by
  simp only [cFrobInner, Matrix.add_apply, Complex.add_re, Complex.add_im, add_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j hj
  ring
theorem cFrobInner_add_right (A B C : CMat n) :
    cFrobInner A (B+C) = cFrobInner A B + cFrobInner A C := by
  rw [cFrobInner_comm, cFrobInner_add_left, cFrobInner_comm B, cFrobInner_comm C]
theorem cFrobInner_neg_left (A B : CMat n) :
    cFrobInner (-A) B = -cFrobInner A B := by
  simp only [cFrobInner, Matrix.neg_apply, Complex.neg_re, Complex.neg_im, neg_mul,
    ← neg_add, Finset.sum_neg_distrib]
theorem cFrobInner_sub_left (A B C : CMat n) :
    cFrobInner (A-B) C = cFrobInner A C - cFrobInner B C := by
  rw [sub_eq_add_neg, cFrobInner_add_left, cFrobInner_neg_left, sub_eq_add_neg]
theorem cFrobInner_sub_right (A B C : CMat n) :
    cFrobInner A (B-C) = cFrobInner A B - cFrobInner A C := by
  rw [cFrobInner_comm, cFrobInner_sub_left, cFrobInner_comm B, cFrobInner_comm C]
theorem cFrobInner_real_smul_left (a : ℝ) (A B : CMat n) :
    cFrobInner (a • A) B = a * cFrobInner A B := by
  simp [cFrobInner, Complex.real_smul, mul_add, mul_assoc, Finset.mul_sum]

theorem cFrobSq_nonneg (A : CMat n) : 0 ≤ cFrobSq A := by
  unfold cFrobSq cFrobInner
  apply Finset.sum_nonneg; intro i hi
  apply Finset.sum_nonneg; intro j hj
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
theorem cFrobSq_eq_zero_iff (A : CMat n) : cFrobSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hr : ∀ i, (∑ j, ((A i j).re * (A i j).re + (A i j).im * (A i j).im)) = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        Finset.sum_nonneg (fun j hj => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)))).mp h i (Finset.mem_univ i)
    ext i j
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      add_nonneg (mul_self_nonneg (A i j).re) (mul_self_nonneg (A i j).im))).mp (hr i) j (Finset.mem_univ j)
    apply Complex.ext <;> simp only [Matrix.zero_apply, Complex.zero_re, Complex.zero_im]
    · nlinarith [mul_self_nonneg (A i j).im, mul_self_nonneg (A i j).re]
    · nlinarith [mul_self_nonneg (A i j).im, mul_self_nonneg (A i j).re]
  · rintro rfl; simp [cFrobSq]
theorem cFrobSq_add (A B : CMat n) :
    cFrobSq (A+B) = cFrobSq A + 2*cFrobInner A B + cFrobSq B := by
  unfold cFrobSq
  rw [cFrobInner_add_left, cFrobInner_add_right, cFrobInner_add_right, cFrobInner_comm B A]
  ring
theorem cFrobSq_sub (A B : CMat n) :
    cFrobSq (A-B) = cFrobSq A - 2*cFrobInner A B + cFrobSq B := by
  unfold cFrobSq
  rw [cFrobInner_sub_left, cFrobInner_sub_right, cFrobInner_sub_right, cFrobInner_comm B A]
  ring

theorem cFrobInner_conjTranspose (A B : CMat n) :
    cFrobInner Aᴴ Bᴴ = cFrobInner A B := by
  simp only [cFrobInner, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.conj_re, Complex.conj_im, neg_mul_neg]
  exact Finset.sum_comm

theorem cFrobInner_eq_zero_of_disjoint (A B : CMat n)
    (h : ∀ i j, A i j = 0 ∨ B i j = 0) : cFrobInner A B = 0 := by
  apply Finset.sum_eq_zero; intro i hi
  apply Finset.sum_eq_zero; intro j hj
  rcases h i j with ha | hb
  · simp [ha]
  · simp [hb]

theorem cFrobInner_mul_left (A B C : CMat n) :
    cFrobInner (A*B) C = cFrobInner B (Aᴴ*C) := by
  simp only [cFrobInner_eq_re_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc]
theorem cFrobInner_left_unitary (U : CMat n) (hU : Unitary U) (A B : CMat n) :
    cFrobInner (U*A) (U*B) = cFrobInner A B := by
  rw [cFrobInner_mul_left, ← Matrix.mul_assoc, hU.1]; simp
theorem cFrobInner_right_unitary (U : CMat n) (hU : Unitary U) (A B : CMat n) :
    cFrobInner (A*U) (B*U) = cFrobInner A B := by
  calc
    _ = cFrobInner (A*U)ᴴ (B*U)ᴴ := (cFrobInner_conjTranspose _ _).symm
    _ = cFrobInner (Uᴴ*Aᴴ) (Uᴴ*Bᴴ) := by rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    _ = cFrobInner Aᴴ Bᴴ := cFrobInner_left_unitary _ hU.conjTranspose _ _
    _ = cFrobInner A B := cFrobInner_conjTranspose _ _

theorem unitary_boundary_isometry (L R : CMat n) (hL : Unitary L) (hR : Unitary R)
    (A B : CMat n) : cFrobDistSq (L*A*R) (L*B*R) = cFrobDistSq A B := by
  have hd : L*A*R-L*B*R = L*(A-B)*R := by rw [Matrix.mul_sub, Matrix.sub_mul]
  unfold cFrobDistSq cFrobSq
  rw [hd, cFrobInner_right_unitary _ hR, cFrobInner_left_unitary _ hL]
end GS.UnitaryGeometry
