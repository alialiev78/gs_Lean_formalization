module

public import GS.CS.ColumnGram
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The real thin cosine-sine decomposition

The proof diagonalizes one column Gram matrix and completes the normalized
columns of both blocks. It includes repeated eigenvalues and zero columns.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.CS

theorem gram_diagonal_nonneg {n : ℕ} (A : Mat n) (d : Fin n → ℝ)
    (h : Aᵀ * A = diagonal d) (i : Fin n) : 0 ≤ d i := by
  have hi := congrFun (congrFun h i) i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply_eq] at hi
  rw [← hi]
  exact Finset.sum_nonneg fun j hj => mul_self_nonneg _

/-- Simultaneous orthogonal reduction of two square blocks whose stacked
columns are orthonormal. The sine and cosine parameters are nonnegative. -/
theorem exists_thin_cs {n : ℕ} (A B : Mat n)
    (h : Aᵀ * A + Bᵀ * B = 1) :
    ∃ (U₁ U₂ V : Mat n) (c s : Fin n → ℝ),
      Orthogonal U₁ ∧ Orthogonal U₂ ∧ Orthogonal V ∧
      (∀ i, 0 ≤ c i ∧ 0 ≤ s i ∧ c i ^ 2 + s i ^ 2 = 1) ∧
      A * V = U₁ * diagonal c ∧ B * V = U₂ * diagonal s := by
  have hH : (Aᵀ * A).IsHermitian := by
    simpa using Matrix.isHermitian_conjTranspose_mul_self A
  let V : Mat n := hH.eigenvectorUnitary
  let d : Fin n → ℝ := hH.eigenvalues
  have hV : Orthogonal V := by
    apply Orthogonal.of_transpose_mul
    simpa only [V, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hAV : (A * V)ᵀ * (A * V) = diagonal d := by
    simpa [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, V, d, Matrix.transpose_mul, Matrix.mul_assoc] using
      hH.conjStarAlgAut_star_eigenvectorUnitary
  have hsum : (A * V)ᵀ * (A * V) + (B * V)ᵀ * (B * V) = 1 := by
    calc
      _ = Vᵀ * (Aᵀ * A + Bᵀ * B) * V := by
        simp [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h, Matrix.mul_one, hV.1]
  have hBV : (B * V)ᵀ * (B * V) = diagonal (fun i => 1 - d i) := by
    rw [hAV] at hsum
    have he : (B * V)ᵀ * (B * V) = 1 - diagonal d := eq_sub_of_add_eq' hsum
    rw [he]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  let c : Fin n → ℝ := fun i => Real.sqrt (d i)
  let s : Fin n → ℝ := fun i => Real.sqrt (1 - d i)
  have hc (i) : c i ^ 2 = d i := Real.sq_sqrt (gram_diagonal_nonneg _ _ hAV i)
  have hs (i) : s i ^ 2 = 1 - d i := Real.sq_sqrt (gram_diagonal_nonneg _ _ hBV i)
  obtain ⟨U₁, hU₁, he₁⟩ := exists_orthogonal_mul_diagonal (A * V) c (by
    simpa only [hc] using hAV)
  obtain ⟨U₂, hU₂, he₂⟩ := exists_orthogonal_mul_diagonal (B * V) s (by
    simpa only [hs] using hBV)
  refine ⟨U₁, U₂, V, c, s, hU₁, hU₂, hV, ?_, he₁, he₂⟩
  intro i
  exact ⟨Real.sqrt_nonneg _, Real.sqrt_nonneg _, by rw [hc, hs]; ring⟩

end GS.CS
