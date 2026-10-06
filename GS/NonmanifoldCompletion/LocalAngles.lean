module

public import GS.NonmanifoldCompletion.SpectralTwo
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# An actual small rotation angle for orthogonal two-by-two matrices near I

The angle is arcsin of the lower-left entry. Positivity of both determinant
and upper-left entry selects the branch. The branch domain is open and contains
I for every positive angle bound. No global continuous argument is chosen.

-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation
namespace GS.NonmanifoldCompletion

/-- Concrete local inverse of the angle parametrization near the identity. -/
def localRotationAngle (U : Mat 2) : ℝ := Real.arcsin (U 1 0)

theorem continuous_localRotationAngle : Continuous localRotationAngle := by
  exact Real.continuous_arcsin.comp (by fun_prop)

@[simp] theorem localRotationAngle_one : localRotationAngle (1 : Mat 2) = 0 := by
  simp [localRotationAngle,Matrix.one_apply]

/-- Positive determinant eliminates the reflection component. -/
theorem orthogonal_det_one_of_pos (U : Mat 2) (hU : Orthogonal U)
    (hp : 0 < U.det) : U.det = 1 := by
  have hg := congrArg Matrix.det hU.1
  have hs : U.det^2=1 := by
    simpa [Matrix.det_mul,Matrix.det_transpose,pow_two] using hg
  nlinarith

/-- The determinant-one condition determines the second column. -/
theorem orthogonal2_columns (U : Mat 2) (hU : Orthogonal U) (hd : U.det=1) :
    U 1 1 = U 0 0 ∧ U 0 1 = -U 1 0 := by
  have hc := congrFun (congrFun hU.1 0) 0
  have hp := congrFun (congrFun hU.1 0) 1
  norm_num [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,Fin.sum_univ_two] at hc hp
  have hdet : U 0 0 * U 1 1 - U 0 1 * U 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using hd
  constructor
  · linear_combination U 0 0 * hdet + U 1 0 * hp - U 1 1 * hc
  · linear_combination -(U 1 0) * hdet + U 0 0 * hp - U 0 1 * hc

/-- On the chosen branch, the arcsin formula reconstructs the whole matrix. -/
theorem rotation_localRotationAngle (U : Mat 2) (hU : Orthogonal U)
    (hdet : 0 < U.det) (ha : 0 < U 0 0) :
    rotation (localRotationAngle U) = U := by
  have hd := orthogonal_det_one_of_pos U hU hdet
  obtain ⟨hdiag,hoff⟩ := orthogonal2_columns U hU hd
  have hc := congrFun (congrFun hU.1 0) 0
  norm_num [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,Fin.sum_univ_two] at hc
  have hl : -1 ≤ U 1 0 := by nlinarith [sq_nonneg (U 0 0),sq_nonneg (U 1 0+1)]
  have hr : U 1 0 ≤ 1 := by nlinarith [sq_nonneg (U 0 0),sq_nonneg (U 1 0-1)]
  have hsin : Real.sin (localRotationAngle U) = U 1 0 := Real.sin_arcsin hl hr
  have hnonneg : 0 ≤ 1-(U 1 0)^2 := by nlinarith
  have hsqrt := Real.sq_sqrt hnonneg
  have hcos : Real.cos (localRotationAngle U) = U 0 0 := by
    rw [localRotationAngle,Real.cos_arcsin]
    nlinarith [Real.sqrt_nonneg (1-(U 1 0)^2)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation,hsin,hcos,hdiag,hoff]

def rotationChartDomain (η : ℝ) : Set (Mat 2) :=
  {U | 0 < U.det ∧ 0 < U 0 0 ∧ |localRotationAngle U| < η}

theorem isOpen_rotationChartDomain (η : ℝ) : IsOpen (rotationChartDomain η) := by
  have hdet : IsOpen {U : Mat 2 | 0 < U.det} :=
    isOpen_lt continuous_const (by fun_prop)
  have hentry : IsOpen {U : Mat 2 | 0 < U 0 0} :=
    isOpen_lt continuous_const (by fun_prop)
  have hangle : IsOpen {U : Mat 2 | |localRotationAngle U| < η} :=
    isOpen_lt continuous_localRotationAngle.abs continuous_const
  exact hdet.inter (hentry.inter hangle)

theorem one_mem_rotationChartDomain {η : ℝ} (hη : 0 < η) :
    (1 : Mat 2) ∈ rotationChartDomain η := by
  refine ⟨by simp,by simp,?_⟩
  simpa using hη

end GS.NonmanifoldCompletion
