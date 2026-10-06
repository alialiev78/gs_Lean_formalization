module

public import GS.SpecialUnitarySharing.Exponential
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The actual exponential differential and a local scalar exponential inverse

All norms on the matrix spaces are the original project norms.  The derivative
at zero is obtained from the proved smooth exponential and its genuine line
 derivatives.  A one-dimensional instance of the inverse function theorem gives
an open neighbourhood where scalar exponentiation is injective.  No global
choice of complex logarithm, branch, or determinant root is used.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold Filter Set
open scoped Topology
namespace GS.SpecialUnitarySharing
variable {n : ℕ}

/-- Directional identification of the genuine Frechet derivative. -/
theorem cMatrixExp_fderiv_zero (A : CMat n) :
    fderiv ℝ (@cMatrixExp n) 0 A = A := by
  have hf := (cMatrixExp_contDiff.differentiable (by simp) (0 : CMat n)).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => t • A) A 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const A
  have he : HasDerivAt (fun t : ℝ => cMatrixExp (t • A)) A 0 := by
    simpa only [cExpLine, cExpLine_zero, Matrix.one_mul] using cExpLine_hasDerivAt A 0
  exact (hf.comp_hasDerivAt_of_eq 0 hl (by simp)).unique he

theorem cMatrixExp_hasFDerivAt_zero :
    HasFDerivAt (@cMatrixExp n) (ContinuousLinearMap.id ℝ (CMat n)) 0 := by
  have hf := (cMatrixExp_contDiff.differentiable (by simp) (0 : CMat n)).hasFDerivAt
  convert hf using 1
  ext A
  exact (cMatrixExp_fderiv_zero A).symm

/-- Scalar matrices of size one, as a real continuous linear embedding. -/
def scalarMatrix : ℂ →L[ℝ] CMat 1 :=
  ({ toFun := fun z => fun _ _ => z
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : ℂ →ₗ[ℝ] CMat 1).toContinuousLinearMap

def scalarEntry : CMat 1 →L[ℝ] ℂ :=
  ({ toFun := fun A => A 0 0
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : CMat 1 →ₗ[ℝ] ℂ).toContinuousLinearMap

/-- The ordinary scalar exponential, expressed through the proved matrix series. -/
def scalarExp (z : ℂ) : ℂ := scalarEntry (cMatrixExp (scalarMatrix z))

theorem scalarExp_eq (z : ℂ) : scalarExp z = NormedSpace.exp ℝ z := by
  have hd : scalarMatrix z = Matrix.diagonal (fun _ : Fin 1 => z) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i; subst j
    simp [scalarMatrix]
  unfold scalarExp
  rw [hd, cMatrixExp_eq_exp, Matrix.exp_diagonal ℝ]
  simp [scalarEntry, Pi.exp_def]

@[simp] theorem scalarExp_zero : scalarExp 0 = 1 := by
  rw [scalarExp_eq, NormedSpace.exp_zero]

theorem scalarExp_contDiff : ContDiff ℝ ⊤ scalarExp :=
  scalarEntry.contDiff.comp (cMatrixExp_contDiff.comp scalarMatrix.contDiff)

theorem scalarExp_hasFDerivAt_zero :
    HasFDerivAt scalarExp (ContinuousLinearMap.id ℝ ℂ) 0 := by
  have hm := (@cMatrixExp_hasFDerivAt_zero 1).comp 0 scalarMatrix.hasFDerivAt
  have he := scalarEntry.hasFDerivAt.comp 0 hm
  convert he using 1 <;> rfl

/-- Only the local inverse near zero is used below. -/
def scalarExpChart : OpenPartialHomeomorph ℂ ℂ :=
  scalarExp_contDiff.contDiffAt.toOpenPartialHomeomorph scalarExp
    (f' := ContinuousLinearEquiv.refl ℝ ℂ)
    scalarExp_hasFDerivAt_zero (by simp)

@[simp] theorem scalarExpChart_apply (z : ℂ) : scalarExpChart z = scalarExp z := rfl

theorem scalarExpChart_zero_source : (0 : ℂ) ∈ scalarExpChart.source :=
  scalarExp_contDiff.contDiffAt.mem_toOpenPartialHomeomorph_source
    (f' := ContinuousLinearEquiv.refl ℝ ℂ)
    scalarExp_hasFDerivAt_zero (by simp)

/-- This is genuinely local: exp(z)=1 does not globally imply z=0. -/
theorem trace_zero_of_exp_one {z : ℂ} (hz : z ∈ scalarExpChart.source)
    (he : NormedSpace.exp ℝ z = 1) : z = 0 := by
  apply scalarExpChart.injOn hz scalarExpChart_zero_source
  simpa only [scalarExpChart_apply, scalarExp_eq, NormedSpace.exp_zero] using he

/-- The trace of one physical block, as a real continuous linear map. -/
def blockTraceMap (s : Pattern n) (i : Fin n) : CMat n →L[ℝ] ℂ :=
  ({ toFun := fun A => Matrix.trace (blockMatrix s i A)
     map_add' := by intro A B; rw [blockMatrix_add, Matrix.trace_add]
     map_smul' := by intro a A; rw [blockMatrix_real_smul, Matrix.trace_smul]
   } : CMat n →ₗ[ℝ] ℂ).toContinuousLinearMap

@[simp] theorem blockTraceMap_apply (s : Pattern n) (i : Fin n) (A : CMat n) :
    blockTraceMap s i A = Matrix.trace (blockMatrix s i A) := rfl

end GS.SpecialUnitarySharing
