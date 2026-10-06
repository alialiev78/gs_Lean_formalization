module

public import GS.NonmanifoldClosure.TopologicalClosure

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Topological singularities of the original three-factor GS family

The public statements here use the scalar perfect shuffle and consecutive
block sizes `2, q, 2` from `GS.localFamily`.  A point is non-Euclidean in the
actual subspace topology; no differentiability or homology assumption is
made.

The general theorem does not require determinant one.  An explicit
Householder matrix supplies a non-Euclidean point in every size `2q`, `q ≥ 3`.
Thus the conclusion is instantiated for all dimensions in the theorem, not
only for the first example `q = 3`.
-/

set_option autoImplicit false

noncomputable section

open Matrix GS GS.Nonmanifold GS.NonmanifoldCompletion
open GS.NonmanifoldObstruction GS.NonmanifoldFinal

namespace GS.Results

/-- The rank-at-most-one locus for two rows has a topological singularity at
zero, even after taking a product with any finite-dimensional real space. -/
theorem cone_rankOne_not_euclidean (d e : ℕ) (hd : 2 ≤ d) :
    ¬ EuclideanAtSubset
      {p : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ | p.2.rank ≤ 1} (0, 0) := by
  intro hE
  let S : Set ((Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) :=
    {p | p.2.rank ≤ 1}
  have hz : ((0, 0) : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) ∈ S := by
    simp [S]
  have hsub : EuclideanAt (⟨(0, 0), hz⟩ : S) :=
    (euclideanAtSubset_iff S (0, 0) hz).mp hE
  let h : ConeSpace (Fin e) (Fin d) ≃ₜ S := flattenConeProduct
  apply GS.NonmanifoldTopology.cone_not_euclidean e d hd
  exact (euclideanAt_homeomorph h productZero).mpr hsub

/-- The original GS family is not locally Euclidean at `Q₀ ⊗ I₂` whenever
`q ≥ 3` and the orthogonal matrix `Q₀` has no zero entries.

The determinant-one condition in the original manuscript specification is
unnecessary for this conclusion. -/
theorem gs_not_euclidean_at {q : ℕ} (hq : 3 ≤ q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j ≠ 0) :
    ¬ EuclideanAtSubset (localFamily q) (basePoint Q₀) := by
  intro hEuclidean
  obtain ⟨g⟩ := original_pointed_open_model (by omega) Q₀ hQ₀ hentries
  have hFamily : EuclideanAt (familyBase Q₀ hQ₀) :=
    (euclideanAtSubset_iff (localFamily q) (basePoint Q₀)
      (familyBase Q₀ hQ₀).property).mp hEuclidean
  exact model_not_euclidean_of_cone_goal
    GS.NonmanifoldTopology.coneProductNonManifold q hq
    ((euclideanAt_pointedOpenModel g).mp hFamily)

/-- Reflection perpendicular to the all-ones vector: `I - (2/q) J`.
The formula is defined also for `q = 0`; its uses below assume `q > 0`. -/
def reflectionBase (q : ℕ) : Mat q :=
  fun i j => (if i = j then 1 else 0) - 2 / (q : ℝ)

theorem reflectionBase_apply (q : ℕ) (i j : Fin q) :
    reflectionBase q i j = (if i = j then 1 else 0) - 2 / (q : ℝ) := by
  simp [reflectionBase, Matrix.one_apply]

theorem reflectionBase_symmetric (q : ℕ) :
    (reflectionBase q)ᵀ = reflectionBase q := by
  ext i j
  simp [Matrix.transpose_apply, reflectionBase_apply, eq_comm]

theorem reflectionBase_mul_self (q : ℕ) (hq : 0 < q) :
    reflectionBase q * reflectionBase q = 1 := by
  let C : Mat q := fun _ _ => 2 / (q : ℝ)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hC : C * C = C + C := by
    ext i j
    simp [C, Matrix.mul_apply]
    field_simp [hqR]
    ring
  change (1 - C) * (1 - C) = 1
  simp only [sub_mul, mul_sub, one_mul, mul_one, hC]
  abel

/-- Orthogonality is certified by an exact matrix identity, without numerical
approximation or a dimension-specific computation. -/
theorem reflectionBase_orthogonal (q : ℕ) (hq : 0 < q) :
    Orthogonal (reflectionBase q) := by
  apply Orthogonal.of_transpose_mul
  rw [reflectionBase_symmetric, reflectionBase_mul_self q hq]

theorem reflectionBase_entries_ne_zero (q : ℕ) (hq : 3 ≤ q)
    (i j : Fin q) : reflectionBase q i j ≠ 0 := by
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := by linarith
  rw [reflectionBase_apply]
  split_ifs <;> intro hz
  all_goals field_simp [hq0] at hz
  all_goals linarith

/-- Every dimension in the original determinant-one specification has an
admissible base matrix. Correct the reflection's orientation by multiplying
its first row by its determinant. -/
theorem exists_specialOrthogonal_base (q : ℕ) (hq : 3 ≤ q) :
    ∃ Q₀ : Mat q, Orthogonal Q₀ ∧ Q₀.det = 1 ∧ ∀ i j, Q₀ i j ≠ 0 := by
  let H := reflectionBase q
  have hH : Orthogonal H := reflectionBase_orthogonal q (by omega)
  have hdet : H.det * H.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one]
      using congrArg Matrix.det hH.1
  have hdet0 : H.det ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hdet
    norm_num at hdet
  let j₀ : Fin q := ⟨0, by omega⟩
  let a : Fin q → ℝ := fun i => if i = j₀ then H.det else 1
  let D : Mat q := Matrix.diagonal a
  have ha : (fun i => a i * a i) = (fun _ => (1 : ℝ)) := by
    funext i
    dsimp [a]
    split_ifs
    · exact hdet
    · norm_num
  have hD : Orthogonal D := by
    apply Orthogonal.of_transpose_mul
    change (Matrix.diagonal a)ᵀ * Matrix.diagonal a = 1
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ha]
    exact Matrix.diagonal_one
  have hDdet : D.det = H.det := by
    simp [D, a, Matrix.det_diagonal]
  refine ⟨D * H, hD.mul hH, ?_, ?_⟩
  · rw [Matrix.det_mul, hDdet]
    exact hdet
  · intro i j
    change (Matrix.diagonal a * H) i j ≠ 0
    rw [Matrix.diagonal_mul]
    apply mul_ne_zero
    · dsimp [a]
      split_ifs
      · exact hdet0
      · exact one_ne_zero
    · exact reflectionBase_entries_ne_zero q hq i j

/-- A specific singular point of the original GS set in every size `2q`,
`q ≥ 3`. The first conjunct records that the point belongs to that set. -/
theorem reflectionBase_nonEuclidean (q : ℕ) (hq : 3 ≤ q) :
    basePoint (reflectionBase q) ∈ localFamily q ∧
      ¬ EuclideanAtSubset (localFamily q) (basePoint (reflectionBase q)) := by
  have hQ := reflectionBase_orthogonal q (by omega)
  exact ⟨basePoint_mem_localFamily (reflectionBase q) hQ,
    gs_not_euclidean_at hq (reflectionBase q) hQ
      (reflectionBase_entries_ne_zero q hq)⟩

/-- Every three-factor family of the specified size has a topological
singularity. In particular, it cannot be a topological manifold without
boundary with its induced matrix topology. -/
theorem exists_nonEuclidean_point (q : ℕ) (hq : 3 ≤ q) :
    ∃ M : Mat (q * 2), M ∈ localFamily q ∧
      ¬ EuclideanAtSubset (localFamily q) M :=
  ⟨basePoint (reflectionBase q), reflectionBase_nonEuclidean q hq⟩

/-- The original manuscript's determinant-one hypotheses and its topological
conclusion hold together at some base point for every `q ≥ 3`. -/
theorem exists_specialOrthogonal_nonEuclidean_base (q : ℕ) (hq : 3 ≤ q) :
    ∃ Q₀ : Mat q, Orthogonal Q₀ ∧ Q₀.det = 1 ∧
      (∀ i j, Q₀ i j ≠ 0) ∧
      ¬ EuclideanAtSubset (localFamily q) (basePoint Q₀) := by
  obtain ⟨Q₀, hQ₀, hdet, hentries⟩ := exists_specialOrthogonal_base q hq
  exact ⟨Q₀, hQ₀, hdet, hentries, gs_not_euclidean_at hq Q₀ hQ₀ hentries⟩

end GS.Results
