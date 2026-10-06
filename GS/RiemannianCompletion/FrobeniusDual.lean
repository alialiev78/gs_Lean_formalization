module

public import GS.Frobenius
public import GS.Extensions.ProjectionSmooth
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The Frobenius dual and the actual derivative of an ambient loss

This file does not endow Matrix with an InnerProductSpace instance: its inherited
supremum norm is not the Frobenius norm. The scalar product is GS.frobInner.
The matrix representing a continuous linear functional is constructed from
its values on matrix units; no gradient hypothesis is inserted as an axiom.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
open scoped BigOperators
namespace GS.RiemannianCompletion
variable {n : ℕ}

/-- The actual matrix unit with its only nonzero entry at (i,j). -/
def unitEntry (i j : Fin n) : Mat n :=
  fun k l => if k = i then if l = j then 1 else 0 else 0

@[simp] theorem frobInner_unitEntry_right (Z : Mat n) (i j : Fin n) :
    frobInner Z (unitEntry i j) = Z i j := by
  classical
  simp [frobInner, unitEntry]

/-- An equality of actual matrices, not a basis postulate. -/
theorem matrix_expansion (Z : Mat n) :
    Z = ∑ i, ∑ j, Z i j • unitEntry i j := by
  classical
  ext k l
  simp [unitEntry, Matrix.sum_apply, Matrix.smul_apply, eq_comm]

/-- Explicit Frobenius dual, continuous for the original matrix topology. -/
def frobDualLinear (Z : Mat n) : Mat n →ₗ[ℝ] ℝ where
  toFun A := frobInner Z A
  map_add' A B := frobInner_add_right Z A B
  map_smul' c A := by
    change frobInner Z (c • A) = c * frobInner Z A
    rw [frobInner_comm Z, frobInner_smul_left, frobInner_comm A]

def frobDual (Z : Mat n) : Mat n →L[ℝ] ℝ :=
  (frobDualLinear Z).toContinuousLinearMap

@[simp] theorem frobDual_apply (Z A : Mat n) :
    frobDual Z A = frobInner Z A := rfl

/-- Frobenius representative of a functional, defined without differentiability. -/
def dualMatrix (D : Mat n →L[ℝ] ℝ) : Mat n := fun i j => D (unitEntry i j)

theorem functional_eq_frobInner (D : Mat n →L[ℝ] ℝ) (A : Mat n) :
    D A = frobInner (dualMatrix D) A := by
  calc
    D A = D (∑ i, ∑ j, A i j • unitEntry i j) :=
      congrArg D (matrix_expansion A)
    _ = ∑ i, ∑ j, A i j * D (unitEntry i j) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = frobInner (dualMatrix D) A := by
      unfold frobInner dualMatrix
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact mul_comm _ _

@[simp] theorem frobDual_dualMatrix (D : Mat n →L[ℝ] ℝ) :
    frobDual (dualMatrix D) = D := by
  ext A
  exact (functional_eq_frobInner D A).symm

@[simp] theorem dualMatrix_frobDual (Z : Mat n) :
    dualMatrix (frobDual Z) = Z := by
  ext i j
  exact frobInner_unitEntry_right Z i j

/-- The ambient Frobenius gradient is computed from mathlib's real fderiv.
For nondifferentiable functions this follows fderiv's zero convention; all
calculus statements below explicitly assume differentiability. -/
def ambientGradient (f : Mat n → ℝ) (X : Mat n) : Mat n :=
  dualMatrix (fderiv ℝ f X)

theorem ambientGradient_represents (f : Mat n → ℝ) (X A : Mat n) :
    fderiv ℝ f X A = frobInner (ambientGradient f X) A :=
  functional_eq_frobInner (fderiv ℝ f X) A

theorem ambientGradient_hasFDerivAt (f : Mat n → ℝ) (X : Mat n)
    (hf : DifferentiableAt ℝ f X) :
    HasFDerivAt f (frobDual (ambientGradient f X)) X := by
  simpa only [ambientGradient, frobDual_dualMatrix] using hf.hasFDerivAt

/-- A directional derivative along an actual differentiable matrix curve. -/
theorem ambientGradient_chain {f : Mat n → ℝ} {γ : ℝ → Mat n}
    {X V : Mat n} {t : ℝ} (hf : DifferentiableAt ℝ f X)
    (hγ : HasDerivAt γ V t) (hX : γ t = X) :
    HasDerivAt (fun s => f (γ s)) (frobInner (ambientGradient f X) V) t := by
  have hd : HasFDerivAt f (frobDual (ambientGradient f X)) (γ t) := by
    simpa only [hX] using ambientGradient_hasFDerivAt f X hf
  exact hd.comp_hasDerivAt t hγ

/-- Elementary positive-definiteness result used later on the actual tangent
space. It also covers zero-dimensional matrices. -/
theorem frobSq_pos_of_ne_zero {A : Mat n} (hA : A ≠ 0) : 0 < frobSq A :=
  lt_of_le_of_ne (frobSq_nonneg A) (fun h => hA ((frobSq_eq_zero_iff A).mp h.symm))

theorem frobInner_smul_right (a : ℝ) (A B : Mat n) :
    frobInner A (a • B) = a * frobInner A B := by
  rw [frobInner_comm A, frobInner_smul_left, frobInner_comm B]

theorem frobSq_smul (a : ℝ) (A : Mat n) :
    frobSq (a • A) = a ^ 2 * frobSq A := by
  unfold frobSq
  rw [frobInner_smul_left, frobInner_smul_right]
  ring

/-- Joint smoothness of the fixed Frobenius pairing, with the original norms. -/
theorem frobInner_smooth :
    ContDiff ℝ ⊤ (fun p : Mat n × Mat n => frobInner p.1 p.2) := by
  unfold frobInner
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact ((contDiff_pi.mp (contDiff_pi.mp contDiff_fst i) j).mul
    (contDiff_pi.mp (contDiff_pi.mp contDiff_snd i) j))

/-- Smoothness of the coefficient extraction is a bounded linear evaluation
statement. The hypothesis concerns the actual fderiv, not an alleged gradient. -/
theorem ambientGradient_smooth_of_fderiv (f : Mat n → ℝ)
    (hf : ContDiff ℝ ⊤ (fderiv ℝ f)) : ContDiff ℝ ⊤ (ambientGradient f) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact hf.clm_apply contDiff_const

end GS.RiemannianCompletion
