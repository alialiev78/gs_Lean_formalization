module

public import GS.UnitaryCS.ColumnGram
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! # Complex thin cosine-sine decomposition via the Hermitian spectral theorem -/

noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate
namespace GS.UnitaryCS

theorem gram_diagonal_nonneg {n : ℕ} (A : CMat n) (d : Fin n → ℝ)
    (h : Aᴴ * A = diagonal (fun i => (d i : ℂ))) (i : Fin n) : 0 ≤ d i := by
  have hi := congrArg Complex.re (congrFun (congrFun h i) i)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq,
    Complex.ofReal_re, Complex.re_sum] at hi
  rw [← hi]
  apply Finset.sum_nonneg
  intro j hj
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (A j i).re, sq_nonneg (A j i).im]

/-- Simultaneous unitary reduction of two square blocks with orthonormal
stacked columns, including repeated eigenvalues and zero columns. -/
theorem exists_thin_cs {n : ℕ} (A B : CMat n)
    (h : Aᴴ * A + Bᴴ * B = 1) :
    ∃ (U₁ U₂ V : CMat n) (c s : Fin n → ℝ),
      Unitary U₁ ∧ Unitary U₂ ∧ Unitary V ∧
      (∀ i, 0 ≤ c i ∧ 0 ≤ s i ∧ c i ^ 2 + s i ^ 2 = 1) ∧
      A * V = U₁ * diagonal (fun i => (c i : ℂ)) ∧
      B * V = U₂ * diagonal (fun i => (s i : ℂ)) := by
  have hH : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  let V : CMat n := hH.eigenvectorUnitary
  let d : Fin n → ℝ := hH.eigenvalues
  have hV : Unitary V := by
    apply IsUnitary.of_conjTranspose_mul
    simpa only [V, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hAV : (A * V)ᴴ * (A * V) = diagonal (fun i => (d i : ℂ)) := by
    simpa [Function.comp_def, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, V, d, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      hH.conjStarAlgAut_star_eigenvectorUnitary
  have hsum : (A * V)ᴴ * (A * V) + (B * V)ᴴ * (B * V) = 1 := by
    calc
      _ = Vᴴ * (Aᴴ * A + Bᴴ * B) * V := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h, Matrix.mul_one, hV.1]
  have hBV : (B * V)ᴴ * (B * V) = diagonal (fun i => ((1 - d i : ℝ) : ℂ)) := by
    rw [hAV] at hsum
    have he : (B * V)ᴴ * (B * V) = 1 - diagonal (fun i => (d i : ℂ)) :=
      eq_sub_of_add_eq' hsum
    rw [he]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  let c : Fin n → ℝ := fun i => Real.sqrt (d i)
  let s : Fin n → ℝ := fun i => Real.sqrt (1 - d i)
  have hc (i) : c i ^ 2 = d i := Real.sq_sqrt (gram_diagonal_nonneg _ _ hAV i)
  have hs (i) : s i ^ 2 = 1 - d i := Real.sq_sqrt (gram_diagonal_nonneg _ _ hBV i)
  have hcC (i) : (c i : ℂ) ^ 2 = (d i : ℂ) := by exact_mod_cast hc i
  have hsC (i) : (s i : ℂ) ^ 2 = ((1-d i : ℝ) : ℂ) := by exact_mod_cast hs i
  obtain ⟨U₁, hU₁, he₁⟩ := exists_unitary_mul_diagonal (A * V) c (by
    simpa only [hcC] using hAV)
  obtain ⟨U₂, hU₂, he₂⟩ := exists_unitary_mul_diagonal (B * V) s (by
    simpa only [hsC] using hBV)
  refine ⟨U₁, U₂, V, c, s, hU₁, hU₂, hV, ?_, he₁, he₂⟩
  intro i
  exact ⟨Real.sqrt_nonneg _, Real.sqrt_nonneg _, by rw [hc, hs]; ring⟩

end GS.UnitaryCS
