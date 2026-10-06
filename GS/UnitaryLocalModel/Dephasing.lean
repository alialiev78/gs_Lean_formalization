module

public import GS.ComplexAlgebra
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact row and column dephasing of unitary matrices

The distinguished anchor index is arbitrary. Nonzero entries in its row and
column suffice; no assumption is made on the other matrix entries. The output
stays unitary and has positive real anchor ratios relative to the reference.
This is an algebraic ingredient of the local model, not a neighbourhood theorem.
-/
noncomputable section
open Matrix
namespace GS.UnitaryLocalModel

/-- The unit-modulus factor of a nonzero scalar; its value at zero is zero. -/
def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem norm_phase {z : ℂ} (hz : z ≠ 0) : ‖phase z‖ = 1 := by
  simp [phase, norm_div, Complex.norm_real, abs_of_nonneg (norm_nonneg z), hz]

theorem conj_phase_mul_phase {z : ℂ} (hz : z ≠ 0) :
    star (phase z) * phase z = 1 := by
  change (starRingEnd ℂ) (phase z) * phase z = 1
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, norm_phase hz]
  norm_num

theorem phase_mul_conj_phase {z : ℂ} (hz : z ≠ 0) :
    phase z * star (phase z) = 1 := by
  rw [mul_comm]
  exact conj_phase_mul_phase hz

theorem norm_mul_phase (z : ℂ) : (‖z‖ : ℂ) * phase z = z := by
  by_cases hz : z = 0
  · simp [hz, phase]
  · exact mul_div_cancel₀ z (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))

theorem conj_phase_mul (z : ℂ) : star (phase z) * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz, phase]
  · calc
      star (phase z) * z = (‖z‖ : ℂ) * (star (phase z) * phase z) := by
        calc
          star (phase z) * z = star (phase z) * ((‖z‖ : ℂ) * phase z) :=
            congrArg (fun w : ℂ => star (phase z) * w) (norm_mul_phase z).symm
          _ = _ := by ring
      _ = (‖z‖ : ℂ) := by rw [conj_phase_mul_phase hz, mul_one]

variable {q : ℕ}

/-- Both reference and variable matrix are nonzero on the anchor row and column. -/
def AnchorNonzero (Q A : CMat q) (o : Fin q) : Prop :=
  (∀ i, Q i o ≠ 0 ∧ A i o ≠ 0) ∧ (∀ j, Q o j ≠ 0 ∧ A o j ≠ 0)

def rowPhase (Q A : CMat q) (o : Fin q) (i : Fin q) : ℂ := phase (A i o / Q i o)
def colPhase (Q A : CMat q) (o : Fin q) (j : Fin q) : ℂ := phase (A o j / Q o j)

@[simp] theorem rowPhase_anchor (Q A : CMat q) (o : Fin q) :
    rowPhase Q A o o = colPhase Q A o o := rfl

/-- Remove the row and column phases, retaining one anchor phase to avoid
counting the shared row/column gauge twice. -/
def dephase (Q A : CMat q) (o : Fin q) : CMat q := fun i j =>
  star (rowPhase Q A o i) * A i j * star (colPhase Q A o j) * rowPhase Q A o o

theorem diagonal_unitary_of_norm_one (u : Fin q → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    GS.Unitary (Matrix.diagonal u) := by
  have h : (Matrix.diagonal u)ᴴ * Matrix.diagonal u = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      change (starRingEnd ℂ) (u i) * u i = 1
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hu i]
      norm_num
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply, hij]
  exact ⟨h, mul_eq_one_comm.mp h⟩

theorem dephase_eq_diagonal_product (Q A : CMat q) (o : Fin q) :
    dephase Q A o = Matrix.diagonal (fun i => star (rowPhase Q A o i)) * A *
      Matrix.diagonal (fun j => star (colPhase Q A o j) * rowPhase Q A o o) := by
  ext i j
  simp [dephase, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]

theorem dephase_unitary {Q A : CMat q} {o : Fin q}
    (hA : GS.Unitary A) (ha : AnchorNonzero Q A o) : GS.Unitary (dephase Q A o) := by
  have hr : ∀ i, ‖rowPhase Q A o i‖ = 1 := fun i =>
    norm_phase (div_ne_zero (ha.1 i).2 (ha.1 i).1)
  have hc : ∀ j, ‖colPhase Q A o j‖ = 1 := fun j =>
    norm_phase (div_ne_zero (ha.2 j).2 (ha.2 j).1)
  rw [dephase_eq_diagonal_product]
  have hL := diagonal_unitary_of_norm_one (fun i => star (rowPhase Q A o i))
    (fun i => by simpa only [norm_star] using hr i)
  have hR := diagonal_unitary_of_norm_one
    (fun j => star (colPhase Q A o j) * rowPhase Q A o o)
    (fun j => by rw [norm_mul, norm_star, hc j, hr o, mul_one])
  exact (hL.mul hA).mul hR

theorem dephase_anchor_column {Q A : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (i : Fin q) :
    dephase Q A o i o / Q i o = (‖A i o / Q i o‖ : ℂ) := by
  have hz : A o o / Q o o ≠ 0 := div_ne_zero (ha.1 o).2 (ha.1 o).1
  calc
    dephase Q A o i o / Q i o =
      (star (rowPhase Q A o i) * (A i o / Q i o)) *
        (star (phase (A o o / Q o o)) * phase (A o o / Q o o)) := by
      simp only [dephase, rowPhase, colPhase]
      ring
    _ = (‖A i o / Q i o‖ : ℂ) := by
      rw [conj_phase_mul_phase hz, mul_one]
      exact conj_phase_mul _

theorem dephase_anchor_row {Q A : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (j : Fin q) :
    dephase Q A o o j / Q o j = (‖A o j / Q o j‖ : ℂ) := by
  have hz : A o o / Q o o ≠ 0 := div_ne_zero (ha.1 o).2 (ha.1 o).1
  calc
    dephase Q A o o j / Q o j =
      (star (colPhase Q A o j) * (A o j / Q o j)) *
        (star (phase (A o o / Q o o)) * phase (A o o / Q o o)) := by
      simp only [dephase, rowPhase, colPhase]
      ring
    _ = (‖A o j / Q o j‖ : ℂ) := by
      rw [conj_phase_mul_phase hz, mul_one]
      exact conj_phase_mul _

theorem dephase_anchor_column_positive {Q A : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (i : Fin q) :
    ∃ r : ℝ, 0 < r ∧ dephase Q A o i o / Q i o = r :=
  ⟨‖A i o / Q i o‖, norm_pos_iff.mpr (div_ne_zero (ha.1 i).2 (ha.1 i).1),
    dephase_anchor_column ha i⟩

theorem dephase_anchor_row_positive {Q A : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (j : Fin q) :
    ∃ r : ℝ, 0 < r ∧ dephase Q A o o j / Q o j = r :=
  ⟨‖A o j / Q o j‖, norm_pos_iff.mpr (div_ne_zero (ha.2 j).2 (ha.2 j).1),
    dephase_anchor_row ha j⟩

/-- Column phases with their anchor fixed to zero. -/
def zeroAnchorSpace (o : Fin q) : Submodule ℝ (Fin q → ℝ) where
  carrier := {β | β o = 0}
  zero_mem' := rfl
  add_mem' := by intro β γ hβ hγ; simp_all
  smul_mem' := by intro r β hβ; simp_all

/-- The derivative of the anchor constraints along row and column phase directions. -/
def phaseConstraintMap (o : Fin q) :
    ((Fin q → ℝ) × zeroAnchorSpace o) →ₗ[ℝ]
      ((Fin q → ℝ) × ({j : Fin q // j ≠ o} → ℝ)) where
  toFun x := (x.1, fun j => x.1 o + x.2.val j.val)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext j
      change (x.1 o + y.1 o) + (x.2.val j.val + y.2.val j.val) =
        (x.1 o + x.2.val j.val) + (y.1 o + y.2.val j.val)
      ring
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · funext j
      change r * x.1 o + r * x.2.val j.val = r * (x.1 o + x.2.val j.val)
      ring

/-- Every set of infinitesimal anchor constraints is attained, with no
unproved rank assertion or dimensional counting. -/
theorem phaseConstraintMap_surjective (o : Fin q) :
    Function.Surjective (phaseConstraintMap o) := by
  rintro ⟨a, b⟩
  let β : Fin q → ℝ := fun j => if hj : j = o then 0 else b ⟨j, hj⟩ - a o
  have hβ : β ∈ zeroAnchorSpace o := by simp [β, zeroAnchorSpace]
  refine ⟨(a, ⟨β, hβ⟩), ?_⟩
  apply Prod.ext
  · rfl
  · funext j
    change a o + β j.val = b j
    simp [β, j.property]

end GS.UnitaryLocalModel
