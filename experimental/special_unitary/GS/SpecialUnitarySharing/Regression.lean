module

public import GS.SpecialUnitarySharing.ExponentialStep
public import GS.UnitaryManifold.UnitCayley
public import GS.Unitary.TracelessProjection

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Regression statements specific to SU, not merely to U

The usual Cayley transform fails determinant one on a trace-free 3 x 3
skew-Hermitian matrix. Removing the scalar phase from the Lie algebra does
not make the two-factor synthesis injective: a trace-free diagonal stabilizer
already remains at the identity with 2 x 2 blocks.
-/
set_option autoImplicit false
noncomputable section
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
open scoped BigOperators
namespace GS.SpecialUnitarySharing.Regression

/-- A trace-free skew-Hermitian input for which ordinary normalized Cayley fails. -/
def D3 : CMat 3 := Matrix.diagonal ![Complex.I, Complex.I, -2 * Complex.I]

theorem D3_skew : IsSkewHermitian D3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D3, Matrix.diagonal_apply, Matrix.conjTranspose_apply, Complex.ext_iff]

theorem D3_trace : Matrix.trace D3 = 0 := by
  norm_num [D3, Matrix.trace_diagonal, Fin.sum_univ_succ] <;> ring

private theorem D3_denominator_det :
    Matrix.det (1 + (-1 / 2 : ℝ) • D3) = (7 / 4 : ℂ) - Complex.I / 4 := by
  norm_num [Matrix.det_fin_three, D3, Matrix.diagonal_apply, Matrix.one_apply,
    Complex.ext_iff]

private theorem D3_numerator_det :
    Matrix.det (1 - (-1 / 2 : ℝ) • D3) = (7 / 4 : ℂ) + Complex.I / 4 := by
  norm_num [Matrix.det_fin_three, D3, Matrix.diagonal_apply, Matrix.one_apply,
    Complex.ext_iff]

/-- This refutes the naive SU adaptation of `unitCayley_shared`. -/
theorem cayley_does_not_preserve_SU3 : Matrix.det (unitCayley D3) ≠ 1 := by
  intro h
  have ha := admissible_of_isSkew ((-1 / 2 : ℝ) • D3)
    (skewHermitian_real_smul _ D3_skew)
  have he := congrArg Matrix.det (cayley_mul ((-1 / 2 : ℝ) • D3) ha)
  rw [Matrix.det_mul, show cayley ((-1 / 2 : ℝ) • D3) = unitCayley D3 from rfl,
    h, one_mul, D3_denominator_det, D3_numerator_det] at he
  have him := congrArg Complex.im he
  norm_num at him

/-- The replacement exponential has the required determinant, with no time bound. -/
theorem D3_exponential_det_one (t : ℝ) : Matrix.det (cExpLine D3 t) = 1 := by
  apply det_cMatrixExp_eq_one
  · exact skewHermitian_real_smul t D3_skew
  · rw [Matrix.trace_smul, D3_trace, smul_zero]

private def p2 : Pattern 2 :=
  { size := 2, positive := by decide, divides := dvd_rfl, label := fun _ => 0 }

private def D2 : CMat 2 := Matrix.diagonal ![Complex.I, -Complex.I]

private theorem D2_special : D2 ∈ specialSkewSpace p2 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> norm_num [GS.UnitarySharing.Pattern.block, p2] at h
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [D2, Matrix.diagonal_apply, Matrix.conjTranspose_apply, Complex.ext_iff]
  · intro i j i' j' _ _ _ hi hj
    fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
      norm_num [p2, D2, Matrix.diagonal_apply] at *
  · intro i
    fin_cases i <;>
      norm_num [blockMatrix, GS.GlobalGeometry.localBlockIndex, p2, D2,
        Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

/-- A genuine nonzero kernel remains after all physical traces are removed. -/
theorem exists_nonzero_SU_synthesis_kernel :
    ∃ s : Pattern 2, ∃ v : PairGenerator s s,
      v ≠ 0 ∧ pointMap s s (1 : CMat 2) v = 0 := by
  let A : Generator p2 := ⟨D2, D2_special⟩
  refine ⟨p2, (A, -A), ?_, ?_⟩
  · intro h
    have h0 := congrArg (fun v : PairGenerator p2 p2 => v.1.val 0 0) h
    exact Complex.I_ne_zero (by simpa [A, D2] using h0)
  · change D2 * 1 + 1 * (-D2) = 0
    simp

/-- The established single-block trace projection applies to EVERY extracted
block; applying it just once to the ambient factor would be a different condition. -/
theorem blockTraceZero_iff_tracelessPart_fixed {n : ℕ} (s : Pattern n) (A : CMat n) :
    BlockTraceZero s A ↔ ∀ i : Fin n, tracelessPart (blockMatrix s i A) = blockMatrix s i A := by
  constructor
  · intro h i
    exact tracelessPart_fixed (h i)
  · intro h i
    rw [← h i]
    exact tracelessPart_trace _

/-- SU(1) contributes no infinitesimal degree of freedom, even with repeated labels. -/
theorem generator_zero_of_blocksize_one {n : ℕ} (s : Pattern n) (hs : s.size = 1)
    (A : CMat n) (hA : A ∈ specialSkewSpace s) : A = 0 := by
  ext i j
  by_cases hij : i = j
  · subst j
    have ht := hA.2 i
    simpa [blockMatrix, GS.GlobalGeometry.localBlockIndex, hs,
      Matrix.trace, Matrix.diag, Fin.sum_univ_succ] using ht
  · exact hA.1.1 i j (by
      intro h
      apply hij
      apply Fin.ext
      simpa only [GS.UnitarySharing.Pattern.block, hs, Nat.div_one] using h)

/-- Determinant one for each scalar block forces the entire factor to be identity. -/
theorem factor_one_of_blocksize_one {n : ℕ} (s : Pattern n) (hs : s.size = 1)
    (A : CMat n) (hA : SpecialUnitaryFactor s A) : A = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    have hd := hA.2 i
    simpa [blockMatrix, GS.GlobalGeometry.localBlockIndex, hs,
      Matrix.det_fin_one, Matrix.one_apply] using hd
  · simp only [Matrix.one_apply, if_neg hij]
    exact hA.1.1 i j (by
      intro h
      apply hij
      apply Fin.ext
      simpa only [GS.UnitarySharing.Pattern.block, hs, Nat.div_one] using h)

/-- If both layers consist of scalar SU blocks, sharing adds no freedom:
the matrix family is exactly the singleton containing its fixed carrier. -/
theorem inSharedA2SU_iff_eq_of_blocksize_one {n : ℕ}
    (right left : Pattern n) (hr : right.size = 1) (hl : left.size = 1)
    (P X : CMat n) : Orbit.InSharedA2SU right left P X ↔ X = P := by
  constructor
  · rintro ⟨L, R, hL, hR, hX⟩
    rw [factor_one_of_blocksize_one left hl L hL,
      factor_one_of_blocksize_one right hr R hR, Matrix.one_mul, Matrix.mul_one] at hX
    exact hX
  · intro hX
    refine ⟨1, 1, special_factor_one left, special_factor_one right, ?_⟩
    simpa only [Matrix.one_mul, Matrix.mul_one] using hX

end GS.SpecialUnitarySharing.Regression
