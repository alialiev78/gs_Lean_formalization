module

public import GS.Unitary.Frobenius
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The real Frobenius dual of complex matrices

Real and imaginary matrix units represent arbitrary real-linear covectors.
The existing matrix norm is preserved: no Frobenius norm or inner-product
instance is installed on the matrix type.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.UnitaryGeometry
open scoped BigOperators
namespace GS.UnitaryManifold
variable {n : ℕ}

/-- A real matrix unit, considered as a complex matrix. -/
def realUnitEntry (i j : Fin n) : CMat n :=
  fun k l => if k = i then if l = j then 1 else 0 else 0

/-- The corresponding imaginary matrix unit. -/
def imagUnitEntry (i j : Fin n) : CMat n :=
  fun k l => if k = i then if l = j then Complex.I else 0 else 0

@[simp] theorem cFrobInner_realUnitEntry_right (Z : CMat n) (i j : Fin n) :
    cFrobInner Z (realUnitEntry i j) = (Z i j).re := by
  classical
  simp [cFrobInner, realUnitEntry, apply_ite]

@[simp] theorem cFrobInner_imagUnitEntry_right (Z : CMat n) (i j : Fin n) :
    cFrobInner Z (imagUnitEntry i j) = (Z i j).im := by
  classical
  simp [cFrobInner, imagUnitEntry, apply_ite]

/-- Real-linear expansion in both kinds of matrix unit. -/
theorem complex_matrix_expansion (Z : CMat n) :
    Z = ∑ i, ∑ j, ((Z i j).re • realUnitEntry i j + (Z i j).im • imagUnitEntry i j) := by
  classical
  apply Matrix.ext
  intro k l
  simp only [Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply]
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single l]
    · simp only [realUnitEntry, imagUnitEntry, if_pos rfl, ite_true, Complex.real_smul,
        mul_one, Complex.re_add_im]
    · intro j hj hne
      simp only [realUnitEntry, imagUnitEntry, if_pos rfl, if_neg (Ne.symm hne), ite_true,
        smul_zero, add_zero]
    · simp
  · intro i hi hne
    apply Finset.sum_eq_zero
    intro j hj
    simp only [realUnitEntry, imagUnitEntry, if_neg (Ne.symm hne), smul_zero, add_zero]
  · simp

theorem cFrobInner_real_smul_right (a : ℝ) (A B : CMat n) :
    cFrobInner A (a • B) = a * cFrobInner A B := by
  rw [cFrobInner_comm A, cFrobInner_real_smul_left, cFrobInner_comm B]

def frobDualLinear (Z : CMat n) : CMat n →ₗ[ℝ] ℝ where
  toFun A := cFrobInner Z A
  map_add' A B := cFrobInner_add_right Z A B
  map_smul' c A := cFrobInner_real_smul_right c Z A

def frobDual (Z : CMat n) : CMat n →L[ℝ] ℝ :=
  (frobDualLinear Z).toContinuousLinearMap

@[simp] theorem frobDual_apply (Z A : CMat n) : frobDual Z A = cFrobInner Z A := rfl

def dualMatrix (D : CMat n →L[ℝ] ℝ) : CMat n :=
  fun i j => ⟨D (realUnitEntry i j), D (imagUnitEntry i j)⟩

theorem functional_eq_cFrobInner (D : CMat n →L[ℝ] ℝ) (A : CMat n) :
    D A = cFrobInner (dualMatrix D) A := by
  calc
    D A = D (∑ i, ∑ j,
        ((A i j).re • realUnitEntry i j + (A i j).im • imagUnitEntry i j)) :=
      congrArg D (complex_matrix_expansion A)
    _ = ∑ i, ∑ j,
        ((A i j).re * D (realUnitEntry i j) + (A i j).im * D (imagUnitEntry i j)) := by
      simp only [map_sum, map_add, map_smul, smul_eq_mul]
    _ = cFrobInner (dualMatrix D) A := by
      unfold cFrobInner dualMatrix
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Complex.re, Complex.im]
      ring

@[simp] theorem frobDual_dualMatrix (D : CMat n →L[ℝ] ℝ) :
    frobDual (dualMatrix D) = D := by
  ext A
  exact (functional_eq_cFrobInner D A).symm

@[simp] theorem dualMatrix_frobDual (Z : CMat n) : dualMatrix (frobDual Z) = Z := by
  ext i j
  apply Complex.ext
  · exact cFrobInner_realUnitEntry_right Z i j
  · exact cFrobInner_imagUnitEntry_right Z i j

/-- The representative of the actual real Frechet derivative. -/
def ambientGradient (f : CMat n → ℝ) (X : CMat n) : CMat n :=
  dualMatrix (fderiv ℝ f X)

theorem ambientGradient_represents (f : CMat n → ℝ) (X A : CMat n) :
    fderiv ℝ f X A = cFrobInner (ambientGradient f X) A :=
  functional_eq_cFrobInner (fderiv ℝ f X) A

theorem ambientGradient_hasFDerivAt (f : CMat n → ℝ) (X : CMat n)
    (hf : DifferentiableAt ℝ f X) :
    HasFDerivAt f (frobDual (ambientGradient f X)) X := by
  simpa only [ambientGradient, frobDual_dualMatrix] using hf.hasFDerivAt

theorem cFrobSq_pos_of_ne_zero {A : CMat n} (hA : A ≠ 0) : 0 < cFrobSq A :=
  lt_of_le_of_ne (cFrobSq_nonneg A) (fun h => hA ((cFrobSq_eq_zero_iff A).mp h.symm))

/-- Joint smoothness of the real Frobenius pairing in the inherited topology. -/
theorem cFrobInner_smooth :
    ContDiff ℝ ⊤ (fun p : CMat n × CMat n => cFrobInner p.1 p.2) := by
  unfold cFrobInner
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  have h₁ : ContDiff ℝ ⊤ (fun p : CMat n × CMat n => p.1 i j) :=
    contDiff_pi.mp (contDiff_pi.mp contDiff_fst i) j
  have h₂ : ContDiff ℝ ⊤ (fun p : CMat n × CMat n => p.2 i j) :=
    contDiff_pi.mp (contDiff_pi.mp contDiff_snd i) j
  exact ((Complex.reCLM.contDiff.comp h₁).mul (Complex.reCLM.contDiff.comp h₂)).add
    ((Complex.imCLM.contDiff.comp h₁).mul (Complex.imCLM.contDiff.comp h₂))

/-- The Frobenius unit ball is bounded for the unchanged matrix supremum norm. -/
theorem matrix_norm_le_one_of_cFrobSq_le_one (A : CMat n) (h : cFrobSq A ≤ 1) :
    ‖A‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro j
  have hrow : (∑ k, ((A i k).re * (A i k).re + (A i k).im * (A i k).im)) ≤ cFrobSq A := by
    unfold cFrobSq cFrobInner
    apply Finset.single_le_sum
      (f := fun k => ∑ l, ((A k l).re * (A k l).re + (A k l).im * (A k l).im))
      (a := i)
    · intro k hk
      exact Finset.sum_nonneg (fun l hl => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
    · exact Finset.mem_univ i
  have he : (A i j).re * (A i j).re + (A i j).im * (A i j).im ≤
      ∑ k, ((A i k).re * (A i k).re + (A i k).im * (A i k).im) :=
    Finset.single_le_sum
      (f := fun k => (A i k).re * (A i k).re + (A i k).im * (A i k).im)
      (fun k hk => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
      (Finset.mem_univ j)
  have hn := Complex.sq_norm (A i j)
  simp only [Complex.normSq_apply] at hn
  nlinarith [norm_nonneg (A i j)]

end GS.UnitaryManifold
