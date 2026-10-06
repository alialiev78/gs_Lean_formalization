module

public import GS.Nonmanifold.RankOneGeometry

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A polynomial circle retract of the rank-one link

For W of size 2 x (d+2), rank <= 1 and Frobenius radius one, put G=W W^T.
The map W |-> (G00-G11, 2 G01) takes values in the unit circle.
Its section is [(I+T(v))/2 | 0]. The section is globally continuous; no
continuous choice of a sign for a rank-one factor is needed.

This proves a genuine topological retract, not yet the nontriviality of
singular homology or the local homology obstruction at the cone vertex.
-/
noncomputable section
open Matrix GS GS.Extensions GS.GlobalGeometry
open scoped BigOperators
namespace GS.Nonmanifold

abbrev UnitCircle := {v : CircleVector // OnCircle v}

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def rowGram (W : Matrix (Fin 2) κ ℝ) : Mat 2 :=
  fun i j => ∑ k, W i k * W j k

theorem continuous_rowGram :
    Continuous (rowGram : Matrix (Fin 2) κ ℝ → Mat 2) := by
  unfold rowGram
  fun_prop

theorem rowGram_outer (u : CircleVector) (z : κ → ℝ) (i j : Fin 2) :
    rowGram (outer u z) i j = (u i * u j) * ∑ k, z k^2 := by
  simp only [rowGram, outer, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

def circleCoordinate (W : Matrix (Fin 2) κ ℝ) : CircleVector :=
  ![rowGram W 0 0 - rowGram W 1 1, 2 * rowGram W 0 1]

theorem continuous_circleCoordinate :
    Continuous (circleCoordinate : Matrix (Fin 2) κ ℝ → CircleVector) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [circleCoordinate, rowGram] <;> fun_prop

/-- Rank-one and radius-one conditions suffice for the circle identity. -/
theorem circleCoordinate_onCircle (W : RankOneLink κ) :
    OnCircle (circleCoordinate (W : Matrix (Fin 2) κ ℝ)) := by
  obtain ⟨u,hu,z,he⟩ := exists_unit_outer_of_rank_le_one
    (W : Matrix (Fin 2) κ ℝ) W.property.1
  have hz : ∑ k, z k^2 = 1 := by
    rw [← frobSq_outer hu z, he]
    exact W.property.2
  change (rowGram (W : Matrix (Fin 2) κ ℝ) 0 0 -
      rowGram (W : Matrix (Fin 2) κ ℝ) 1 1)^2 +
      (2 * rowGram (W : Matrix (Fin 2) κ ℝ) 0 1)^2 = 1
  rw [← he]
  simp only [rowGram_outer, hz, mul_one]
  dsimp [OnCircle] at hu
  nlinarith [congrArg (fun x : ℝ => x^2) hu]

def circleRetraction (W : RankOneLink κ) : UnitCircle :=
  ⟨circleCoordinate (W : Matrix (Fin 2) κ ℝ), circleCoordinate_onCircle W⟩

theorem continuous_circleRetraction :
    Continuous (circleRetraction : RankOneLink κ → UnitCircle) := by
  exact (continuous_circleCoordinate.comp continuous_subtype_val).subtype_mk _

/-- A rank-one orthogonal projector determined by a point of the circle. -/
def circleProjector (v : CircleVector) : Mat 2 :=
  !![(1+v 0)/2, v 1/2; v 1/2, (1-v 0)/2]

theorem circleProjector_symmetric (v : CircleVector) :
    (circleProjector v)ᵀ = circleProjector v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [circleProjector]

theorem circleProjector_idempotent (v : UnitCircle) :
    circleProjector v.val * circleProjector v.val = circleProjector v.val := by
  have hv : v.val 0^2 + v.val 1^2 = 1 := v.property
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circleProjector, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [hv]

theorem circleProjector_rank (v : UnitCircle) :
    (circleProjector v.val).rank ≤ 1 := by
  apply rank_le_one_of_two_column_minors
  have hv : v.val 0^2 + v.val 1^2 = 1 := v.property
  intro j k
  fin_cases j <;> fin_cases k <;> simp [circleProjector] <;> nlinarith [hv]

theorem circleProjector_frobSq (v : UnitCircle) :
    frobSq (circleProjector v.val) = 1 := by
  have hv : v.val 0^2 + v.val 1^2 = 1 := v.property
  simp [frobSq, frobInner, circleProjector, Fin.sum_univ_two]
  nlinarith [hv]

/-- Append zero columns, using d+2 rather than a dimension cast. -/
def padTwo (d : ℕ) (A : Mat 2) : Matrix (Fin 2) (Fin (d+2)) ℝ :=
  fun i => Fin.cases (A i 0) (Fin.cases (A i 1) (fun _ : Fin d => 0))

theorem padTwo_frobSq (d : ℕ) (A : Mat 2) :
    frobSq (padTwo d A) = frobSq A := by
  simp [frobSq, frobInner, padTwo, Fin.sum_univ_succ, Fin.sum_univ_two]

theorem padTwo_rowGram (d : ℕ) (A : Mat 2) :
    rowGram (padTwo d A) = A * Aᵀ := by
  ext i j
  simp [rowGram, padTwo, Matrix.mul_apply, Fin.sum_univ_succ,
    Fin.sum_univ_two, Matrix.transpose_apply]

theorem padTwo_rank_le_one (d : ℕ) {A : Mat 2} (hA : A.rank ≤ 1) :
    (padTwo d A).rank ≤ 1 := by
  apply rank_le_one_of_two_column_minors
  intro j k
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  · refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
    · simp [padTwo]
    · change A 0 0 * A 1 1 = A 0 1 * A 1 0
      exact rank_le_one_two_column_minor A hA 0 1
    · simp [padTwo]
  · refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
    · change A 0 1 * A 1 0 = A 0 0 * A 1 1
      exact rank_le_one_two_column_minor A hA 1 0
    · simp [padTwo]
    · simp [padTwo]
  · simp [padTwo]

/-- The section lands in the actual matrix link. -/
def circleSection (d : ℕ) (v : UnitCircle) : RankOneLink (Fin (d+2)) :=
  ⟨padTwo d (circleProjector v.val),
    padTwo_rank_le_one d (circleProjector_rank v),
    by rw [padTwo_frobSq, circleProjector_frobSq]⟩

theorem continuous_circleSection (d : ℕ) : Continuous (circleSection d) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => ?_) j) j
  · fin_cases i <;> simp [circleSection, padTwo, circleProjector]
    · exact (continuous_const.add ((continuous_apply 0).comp continuous_subtype_val)).div_const 2
    · exact ((continuous_apply 1).comp continuous_subtype_val).div_const 2
  · fin_cases i <;> simp [circleSection, padTwo, circleProjector]
    · exact ((continuous_apply 1).comp continuous_subtype_val).div_const 2
    · exact (continuous_const.sub ((continuous_apply 0).comp continuous_subtype_val)).div_const 2
  · exact continuous_const

/-- The central identity: this is a continuous split surjection onto S^1. -/
theorem circleRetraction_section (d : ℕ) (v : UnitCircle) :
    circleRetraction (circleSection d v) = v := by
  apply Subtype.ext
  have hg : rowGram ((circleSection d v).val) = circleProjector v.val := by
    change rowGram (padTwo d (circleProjector v.val)) = circleProjector v.val
    rw [padTwo_rowGram, circleProjector_symmetric, circleProjector_idempotent]
  ext i
  fin_cases i <;>
    simp [circleRetraction, circleCoordinate, hg, circleProjector] <;> ring

theorem circleSection_injective (d : ℕ) : Function.Injective (circleSection d) := by
  intro u v h
  have he := congrArg circleRetraction h
  simpa only [Fin.reduceFinMk, Fin.cases_zero, Fin.cases_succ,circleRetraction_section] using he

theorem circleRetraction_surjective (d : ℕ) :
    Function.Surjective (circleRetraction : RankOneLink (Fin (d+2)) → UnitCircle) := by
  intro v
  exact ⟨circleSection d v, circleRetraction_section d v⟩

/-- An explicit bundle of continuous maps and their retraction identity.
No homology theorem or nonmanifold hypothesis is a field of this structure. -/
structure CircleRetractData (X : Type*) [TopologicalSpace X] where
  sectionMap : UnitCircle → X
  retractionMap : X → UnitCircle
  section_continuous : Continuous sectionMap
  retraction_continuous : Continuous retractionMap
  retraction_section : ∀ v, retractionMap (sectionMap v) = v

def rankOneLinkCircleRetract (d : ℕ) : CircleRetractData (RankOneLink (Fin (d+2))) where
  sectionMap := circleSection d
  retractionMap := circleRetraction
  section_continuous := continuous_circleSection d
  retraction_continuous := continuous_circleRetraction
  retraction_section := circleRetraction_section d

end GS.Nonmanifold
