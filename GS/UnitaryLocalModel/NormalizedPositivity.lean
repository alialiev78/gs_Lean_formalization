module

public import GS.UnitaryLocalModel.NormalizedFibres

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Positivity of normalized Pauli middle blocks

A positive middle block is the square of a Hermitian matrix with an explicit
inverse. This gives positivity for every sphere axis without choosing an
axis-dependent diagonalizing unitary.
-/
noncomputable section
open Matrix
open scoped ComplexOrder
namespace GS.UnitaryLocalModel

/-- The two Pauli eigenspaces multiply independently. -/
theorem middleBlock_mul (a b c d : ℂ) (u : AxisVector) (hu : OnSphere u) :
    middleBlock a b u * middleBlock c d u = middleBlock (a*c) (b*d) u := by
  have hh : pauli u * pauli u = (1 : CMat 2) := by
    rw [pauli_square, hu]
    simp
  unfold middleBlock
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, hh, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem middleBlock_real_hermitian (r s : ℝ) (u : AxisVector) :
    (middleBlock (r : ℂ) (s : ℂ) u).IsHermitian := by
  change (middleBlock (r : ℂ) (s : ℂ) u)ᴴ = _
  simp [middleBlock, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    pauli_conjTranspose]

/-- Positive real Pauli eigenvalues imply actual matrix positive definiteness. -/
theorem middleBlock_posDef (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (u : AxisVector) (hu : OnSphere u) :
    (middleBlock (r : ℂ) (s : ℂ) u).PosDef := by
  let B := middleBlock (Real.sqrt r : ℂ) (Real.sqrt s : ℂ) u
  let C := middleBlock ((Real.sqrt r : ℂ)⁻¹) ((Real.sqrt s : ℂ)⁻¹) u
  have hbr : (Real.sqrt r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hr))
  have hbs : (Real.sqrt s : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hs))
  have hinv : C*B = 1 := by
    rw [show C*B = middleBlock ((Real.sqrt r : ℂ)⁻¹ * (Real.sqrt r : ℂ))
      ((Real.sqrt s : ℂ)⁻¹ * (Real.sqrt s : ℂ)) u from
        middleBlock_mul _ _ _ _ u hu]
    simp [hbr, hbs, middleBlock_equal]
  have hinj : Function.Injective B.mulVec := by
    intro x y hxy
    have h := congrArg (fun z => C *ᵥ z) hxy
    change C *ᵥ (B *ᵥ x) = C *ᵥ (B *ᵥ y) at h
    simpa only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] using h
  have hsq : Bᴴ*B = middleBlock (r : ℂ) (s : ℂ) u := by
    rw [(middleBlock_real_hermitian (Real.sqrt r) (Real.sqrt s) u).eq]
    change middleBlock (Real.sqrt r : ℂ) (Real.sqrt s : ℂ) u *
      middleBlock (Real.sqrt r : ℂ) (Real.sqrt s : ℂ) u = _
    rw [middleBlock_mul _ _ _ _ u hu]
    simp only [← Complex.ofReal_mul, Real.mul_self_sqrt hr.le, Real.mul_self_sqrt hs.le]
  have hp := (Matrix.PosDef.one : (1 : CMat 2).PosDef).conjTranspose_mul_mul_same hinj
  simpa only [Matrix.mul_one, hsq] using hp

/-- Scalar normalization acts on both eigenvalues. -/
theorem smul_middleBlock (t a b : ℂ) (u : AxisVector) :
    t • middleBlock a b u = middleBlock (t*a) (t*b) u := by
  ext i j
  simp only [middleBlock, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

/-- Positive anchor ratios give the positive blocks required by outer recovery. -/
theorem middleBlock_ratio_posDef (a b c : ℂ) (u : AxisVector) (hu : OnSphere u)
    (ha : ∃ r : ℝ, 0 < r ∧ a/c = r)
    (hb : ∃ s : ℝ, 0 < s ∧ b/c = s) :
    (c⁻¹ • middleBlock a b u).PosDef := by
  obtain ⟨r, hr, ha⟩ := ha
  obtain ⟨s, hs, hb⟩ := hb
  rw [smul_middleBlock]
  rw [show c⁻¹*a = (r : ℂ) by simpa only [div_eq_mul_inv, mul_comm] using ha]
  rw [show c⁻¹*b = (s : ℂ) by simpa only [div_eq_mul_inv, mul_comm] using hb]
  exact middleBlock_posDef r s hr hs u hu

end GS.UnitaryLocalModel
