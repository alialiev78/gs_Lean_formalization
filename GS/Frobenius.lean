module

public import GS.Core

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Explicit Frobenius geometry. We do NOT use the default norm on `Matrix`,
which need not be the Frobenius norm.  -/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def frobInner (A B : Matrix ι κ ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

def frobSq (A : Matrix ι κ ℝ) : ℝ := frobInner A A

def frobDistSq (A B : Matrix ι κ ℝ) : ℝ := frobSq (A - B)

theorem frobInner_comm (A B : Matrix ι κ ℝ) : frobInner A B = frobInner B A := by
  unfold frobInner
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

@[simp] theorem frobInner_zero_left (A : Matrix ι κ ℝ) : frobInner 0 A = 0 := by
  simp [frobInner]

@[simp] theorem frobInner_zero_right (A : Matrix ι κ ℝ) : frobInner A 0 = 0 := by
  simp [frobInner]

theorem frobInner_add_left (A B C : Matrix ι κ ℝ) :
    frobInner (A + B) C = frobInner A C + frobInner B C := by
  simp [frobInner, add_mul, Finset.sum_add_distrib]

theorem frobInner_add_right (A B C : Matrix ι κ ℝ) :
    frobInner A (B + C) = frobInner A B + frobInner A C := by
  simp [frobInner, mul_add, Finset.sum_add_distrib]

theorem frobInner_sub_left (A B C : Matrix ι κ ℝ) :
    frobInner (A - B) C = frobInner A C - frobInner B C := by
  simp [frobInner, sub_mul, Finset.sum_sub_distrib]

theorem frobInner_sub_right (A B C : Matrix ι κ ℝ) :
    frobInner A (B - C) = frobInner A B - frobInner A C := by
  simp [frobInner, mul_sub, Finset.sum_sub_distrib]

theorem frobInner_neg_left (A B : Matrix ι κ ℝ) :
    frobInner (-A) B = -frobInner A B := by
  simp [frobInner, Finset.sum_neg_distrib]

theorem frobInner_smul_left (a : ℝ) (A B : Matrix ι κ ℝ) :
    frobInner (a • A) B = a * frobInner A B := by
  simp [frobInner, mul_assoc, Finset.mul_sum]

theorem frobSq_nonneg (A : Matrix ι κ ℝ) : 0 ≤ frobSq A := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_self_nonneg _

theorem frobSq_eq_zero_iff (A : Matrix ι κ ℝ) : frobSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hrows : ∀ i, (∑ j, A i j * A i j) = 0 := by
      intro i
      have hn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ ∑ j, A i j * A i j := by
        intro i hi
        exact Finset.sum_nonneg (fun j hj => mul_self_nonneg _)
      exact (Finset.sum_eq_zero_iff_of_nonneg hn).mp h i (Finset.mem_univ i)
    ext i j
    have he : A i j * A i j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (Finset.univ : Finset κ)) =>
        mul_self_nonneg (A i j))).mp (hrows i) j (Finset.mem_univ j)
    exact (mul_self_eq_zero.mp he)
  · rintro rfl
    simp [frobSq, frobInner]

theorem frobSq_add (A B : Matrix ι κ ℝ) :
    frobSq (A + B) = frobSq A + 2 * frobInner A B + frobSq B := by
  unfold frobSq
  rw [frobInner_add_left, frobInner_add_right, frobInner_add_right,
    frobInner_comm B A]
  ring

theorem frobSq_sub (A B : Matrix ι κ ℝ) :
    frobSq (A - B) = frobSq A - 2 * frobInner A B + frobSq B := by
  unfold frobSq
  rw [frobInner_sub_left, frobInner_sub_right, frobInner_sub_right,
    frobInner_comm B A]
  ring

theorem frobInner_transpose (A B : Matrix ι κ ℝ) :
    frobInner Aᵀ Bᵀ = frobInner A B := by
  unfold frobInner
  simp only [Matrix.transpose_apply]
  exact Finset.sum_comm

theorem frobInner_eq_zero_of_disjoint (A B : Matrix ι κ ℝ)
    (h : ∀ i j, A i j = 0 ∨ B i j = 0) : frobInner A B = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rcases h i j with hA | hB
  · rw [hA, zero_mul]
  · rw [hB, mul_zero]

/-- Matrix multiplication adjoint; the finite-sum proof fixes the convention. -/
theorem frobInner_mul_left {ν : Type*} [Fintype ν]
    (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) (C : Matrix ι ν ℝ) :
    frobInner (A * B) C = frobInner B (Aᵀ * C) := by
  classical
  simp only [frobInner, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ i, ∑ j, ∑ k, (A i k * B k j) * C i j) =
        ∑ i, ∑ k, ∑ j, B k j * (A i k * C i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ k, ∑ j, ∑ i, B k j * (A i k * C i j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm

theorem frobInner_left_orthogonal [DecidableEq ι]
    (U : Matrix ι ι ℝ) (hU : Orthogonal U) (A B : Matrix ι κ ℝ) :
    frobInner (U * A) (U * B) = frobInner A B := by
  rw [frobInner_mul_left, ← Matrix.mul_assoc, hU.1]
  simp

theorem frobInner_right_orthogonal [DecidableEq κ]
    (V : Matrix κ κ ℝ) (hV : Orthogonal V) (A B : Matrix ι κ ℝ) :
    frobInner (A * V) (B * V) = frobInner A B := by
  calc
    frobInner (A * V) (B * V) = frobInner (A * V)ᵀ (B * V)ᵀ :=
      (frobInner_transpose _ _).symm
    _ = frobInner (Vᵀ * Aᵀ) (Vᵀ * Bᵀ) := by rw [Matrix.transpose_mul, Matrix.transpose_mul]
    _ = frobInner Aᵀ Bᵀ := frobInner_left_orthogonal _ hV.transpose _ _
    _ = frobInner A B := frobInner_transpose _ _

/-- The genuine global boundary isometry acts on matrices, not pairs of factors. -/
theorem boundary_frobDistSq [DecidableEq ι] [DecidableEq κ]
    (L : Matrix ι ι ℝ) (R : Matrix κ κ ℝ)
    (hL : Orthogonal L) (hR : Orthogonal R) (A B : Matrix ι κ ℝ) :
    frobDistSq (L * A * R) (L * B * R) = frobDistSq A B := by
  have hd : L * A * R - L * B * R = L * (A - B) * R := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  unfold frobDistSq frobSq
  rw [hd, frobInner_right_orthogonal _ hR, frobInner_left_orthogonal _ hL]

end GS
