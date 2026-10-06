module

public import GS.Continuation.ExponentialBasics
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A real orthogonal diagonalizer for the original two-by-two middle block

The result is an existence theorem, not a continuous choice of eigenvectors.
The exceptional point u=(-1,0) is handled explicitly.  No angle, logarithm,
local-coverage hypothesis, or topological nonmanifold assertion is assumed.

-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation
namespace GS.NonmanifoldCompletion

/-- Diagonal two-by-two matrix, with the order of eigenvalues fixed. -/
def diagTwo (a b : ℝ) : Mat 2 := !![a, 0; 0, b]

/-- Algebraic half-angle representatives. Only existence is asserted. -/
theorem exists_half_coordinates (u : CircleVector) (hu : OnCircle u) :
    ∃ c s : ℝ, c^2+s^2=1 ∧ c^2-s^2=u 0 ∧ 2*c*s=u 1 := by
  have hu' : u 0^2+u 1^2=1 := hu
  by_cases hx : u 0 = -1
  · have hy : u 1=0 := by nlinarith [sq_nonneg (u 1)]
    exact ⟨0,1,by norm_num,by norm_num [hx],by norm_num [hy]⟩
  · have hlow : -1 ≤ u 0 := by
      nlinarith [sq_nonneg (u 1), sq_nonneg (u 0+1)]
    have hp : 0 < 2*(1+u 0) := by
      have : -1 < u 0 := lt_of_le_of_ne hlow (Ne.symm hx)
      linarith
    let r := Real.sqrt (2*(1+u 0))
    have hr : 0 < r := Real.sqrt_pos.mpr hp
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hrs : r^2=2*(1+u 0) := Real.sq_sqrt hp.le
    refine ⟨(1+u 0)/r,u 1/r,?_,?_,?_⟩
    · field_simp [hr0]
      nlinarith [hu', hrs]
    · field_simp [hr0]
      nlinarith [hu', hrs, congrArg (fun t : ℝ => t*u 0) hrs]
    · field_simp [hr0]
      nlinarith [congrArg (fun t : ℝ => t*u 1) hrs]

theorem diagTwo_scalar (a b : ℝ) :
    diagTwo a b = ((a+b)/2) • (1 : Mat 2) +
      ((a-b)/2) • diagTwo 1 (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagTwo, Matrix.one_apply] <;> ring

/-- A common orthogonal diagonalizer works for ALL scalar pairs a,b. -/
theorem exists_common_middle_diagonalizer (u : CircleVector) (hu : OnCircle u) :
    ∃ S : Mat 2, Orthogonal S ∧
      ∀ a b : ℝ, middleBlock a b u = S * diagTwo a b * Sᵀ := by
  obtain ⟨c,s,hunit,hdiff,hprod⟩ := exists_half_coordinates u hu
  let v : CircleVector := ![c,s]
  let S := T v
  have hv : OnCircle v := hunit
  have hS : Orthogonal S := T_orthogonal hv
  have hconj : S * diagTwo 1 (-1) * Sᵀ = T u := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [S,v,T,diagTwo,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two] <;>
      nlinarith [hdiff,hprod]
  refine ⟨S,hS,?_⟩
  intro a b
  rw [diagTwo_scalar]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hS.2, hconj]
  rfl

end GS.NonmanifoldCompletion
