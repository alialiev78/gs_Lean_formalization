module

public import GS.UnitaryLocalModel.PauliCoordinates

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Exact unitary diagonalization of every Pauli axis, including both poles.
Only existence is asserted: a globally continuous choice is neither used nor
assumed. The simultaneous conjugation formula holds for every pair of scalars. -/
noncomputable section
open GS Matrix GS.UnitaryGeometry GS.UnitaryNonmanifold
namespace GS.UnitaryLocalModel

def axisDiagonal : CMat 2 := diagTwo 1 (-1)

@[simp] theorem axisDiagonal_conjTranspose : axisDiagonalᴴ = axisDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [axisDiagonal,diagTwo,Matrix.conjTranspose_apply]

@[simp] theorem axisDiagonal_square : axisDiagonal*axisDiagonal = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisDiagonal,diagTwo,Matrix.mul_apply,Fin.sum_univ_two]

@[simp] theorem axisDiagonal_trace : Matrix.trace axisDiagonal = 0 := by
  simp [axisDiagonal,diagTwo,Matrix.trace,Fin.sum_univ_two]

theorem diagTwo_axis_formula (a b : ℂ) :
    diagTwo a b = ((a+b)/2) • (1 : CMat 2) + ((a-b)/2) • axisDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [axisDiagonal,diagTwo] <;> ring

theorem conjugated_diagTwo_eq_middle (S : CMat 2) (hS : GS.Unitary S)
    (u : AxisVector) (he : Sᴴ*axisDiagonal*S = pauli u) (a b : ℂ) :
    Sᴴ*diagTwo a b*S = middleBlock a b u := by
  rw [diagTwo_axis_formula]
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,hS.1,he,middleBlock]

theorem exists_axis_of_unitary (S : CMat 2) (hS : GS.Unitary S) :
    ∃ u : AxisVector, OnSphere u ∧
      ∀ a b : ℂ, Sᴴ*diagTwo a b*S = middleBlock a b u := by
  let H := Sᴴ*axisDiagonal*S
  have hh : Hᴴ = H := by
    simp only [H,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
      axisDiagonal_conjTranspose,Matrix.mul_assoc]
  have ht : Matrix.trace H = 0 := by
    change Matrix.trace (Sᴴ*axisDiagonal*S) = 0
    rw [Matrix.trace_mul_comm]
    rw [← Matrix.mul_assoc,hS.2,Matrix.one_mul,axisDiagonal_trace]
  have hs : H*H = 1 := by
    calc
      H*H = Sᴴ*axisDiagonal*(S*Sᴴ)*axisDiagonal*S := by simp only [H,Matrix.mul_assoc]
      _ = 1 := by rw [hS.2,Matrix.mul_one,Matrix.mul_assoc Sᴴ,axisDiagonal_square,
        Matrix.mul_one,hS.1]
  obtain ⟨u,hu,he⟩ := exists_sphere_pauli H hh ht hs
  exact ⟨u,hu,conjugated_diagTwo_eq_middle S hS u he.symm⟩

theorem pauli_axis_anticommutator (u : AxisVector) :
    pauli u*axisDiagonal+axisDiagonal*pauli u = (2*u 0 : ℝ) • (1 : CMat 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Fin.sum_univ_two, pauli, axisDiagonal, diagTwo, Matrix.diagonal_apply,
      Matrix.one_apply, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const] <;>
    norm_num [Complex.real_smul] <;> ring

/-- Every axis admits a unitary diagonalizer. The antipodal pole is handled
explicitly, so no denominator is silently assumed nonzero. -/
theorem exists_unitary_for_axis (u : AxisVector) (hu : OnSphere u) :
    ∃ S : CMat 2, GS.Unitary S ∧ Sᴴ*axisDiagonal*S = pauli u := by
  have hH : pauli u*pauli u = 1 := by rw [pauli_square,hu]; simp
  have hu0 : -1 ≤ u 0 := by
    dsimp [OnSphere] at hu
    nlinarith [sq_nonneg (u 1),sq_nonneg (u 2),sq_nonneg (u 0+1)]
  by_cases hp : u 0 = -1
  · have h1 : u 1 = 0 := by dsimp [OnSphere] at hu; rw [hp] at hu; nlinarith [sq_nonneg (u 2)]
    have h2 : u 2 = 0 := by dsimp [OnSphere] at hu; rw [hp] at hu; nlinarith [sq_nonneg (u 1)]
    refine ⟨!![0,1;1,0],?_,?_⟩
    · constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [axisDiagonal,diagTwo,pauli,hp,h1,h2,Matrix.mul_apply,
          Fin.sum_univ_two,Matrix.conjTranspose_apply]
  · let A := (1 : CMat 2)+pauli u*axisDiagonal
    let r := Real.sqrt (2*(1+u 0))
    have hpos : 0 < 2*(1+u 0) := by have : -1 < u 0 := lt_of_le_of_ne hu0 (Ne.symm hp); linarith
    have hr : 0 < r := Real.sqrt_pos.mpr hpos
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hrs : r^2 = 2*(1+u 0) := Real.sq_sqrt hpos.le
    have hAA : Aᴴ*A = (2*(1+u 0) : ℝ) • (1 : CMat 2) := by
      calc
        Aᴴ*A = (1 : CMat 2)+1+(pauli u*axisDiagonal+axisDiagonal*pauli u) := by
          simp only [A,Matrix.conjTranspose_add,Matrix.conjTranspose_one,
            Matrix.conjTranspose_mul,axisDiagonal_conjTranspose,pauli_conjTranspose,
            Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
          have ht : axisDiagonal*pauli u*(pauli u*axisDiagonal) = (1 : CMat 2) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (pauli u), hH,
              Matrix.one_mul, axisDiagonal_square]
          rw [ht]
          abel
        _ = _ := by
          rw [pauli_axis_anticommutator]
          ext i j
          simp only [Matrix.add_apply,Matrix.smul_apply,Complex.real_smul]
          push_cast
          ring
    let U := (r⁻¹ : ℝ) • A
    have hUleft : Uᴴ*U = 1 := by
      simp only [U,Matrix.conjTranspose_smul,star_trivial,Matrix.smul_mul,Matrix.mul_smul,
        smul_smul,hAA]
      have he : r⁻¹*(r⁻¹*(2*(1+u 0))) = 1 := by rw [← hrs]; field_simp [hr0]
      rw [he,one_smul]
    have hU : GS.Unitary U := ⟨hUleft,mul_eq_one_comm.mp hUleft⟩
    have hHU : pauli u*U = U*axisDiagonal := by
      simp only [U,Matrix.mul_smul,Matrix.smul_mul]
      congr 1
      dsimp [A]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
      rw [← Matrix.mul_assoc, hH, Matrix.one_mul, Matrix.mul_assoc,
        axisDiagonal_square, Matrix.mul_one]
      abel
    refine ⟨Uᴴ,hU.conjTranspose,?_⟩
    rw [Matrix.conjTranspose_conjTranspose,← hHU,Matrix.mul_assoc,hU.2,Matrix.mul_one]

/-- Every point of the sphere yields a simultaneous unitary middle factor. -/
theorem middleBlock_unitary_diagonalization (u : AxisVector) (hu : OnSphere u) :
    ∃ S : CMat 2, GS.Unitary S ∧
      ∀ a b : ℂ, Sᴴ*diagTwo a b*S = middleBlock a b u := by
  obtain ⟨S,hS,he⟩ := exists_unitary_for_axis u hu
  exact ⟨S,hS,conjugated_diagTwo_eq_middle S hS u he⟩

end GS.UnitaryLocalModel
