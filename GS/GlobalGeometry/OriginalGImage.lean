module

public import GS.OriginalLocalModel
public import GS.Extensions.FiniteTopology

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact set-theoretic description of the ORIGINAL g(K)

This module preserves the manuscript's g, K, c, z, u. It proves that the last
component of g(K) is the rank-at-most-one Frobenius ball whose two rows are
vectorized skew matrices. Normalization is an existence argument, NOT a
continuous choice of rank-one factors at the zero matrix.

The remaining reduction from row-skew matrices to exactly d=q(q-1)/2
coordinates, local coverage of the full GS family, and the nonmanifold
obstruction are deliberately NOT claimed here.
-/
noncomputable section
open Matrix GS GS.Extensions
open scoped BigOperators
namespace GS.GlobalGeometry
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Rank <= 1 forces every two-column 2-by-2 determinant to vanish. -/
theorem rank_le_one_two_column_minor (W : Matrix (Fin 2) κ ℝ)
    (hW : W.rank ≤ 1) (j k : κ) : W 0 j * W 1 k = W 0 k * W 1 j := by
  let D : Mat 2 := W.submatrix id ![j,k]
  have hDW : D.rank ≤ W.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
    apply Submodule.finrank_mono
    apply Submodule.span_mono
    rintro x ⟨i, rfl⟩
    exact ⟨![j,k] i, rfl⟩
  have hr : D.rank ≤ 1 := hDW.trans hW
  have hd : D.det = 0 := by
    by_contra hn
    have he : D.rank = 2 := by
      simpa using Matrix.rank_of_isUnit D
        ((Matrix.isUnit_iff_isUnit_det D).mpr (isUnit_iff_ne_zero.mpr hn))
    omega
  simpa only [D, Matrix.det_fin_two, Matrix.submatrix_apply, id_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, sub_eq_zero] using hd

/-- Normalized outer factorization, including W=0. Only the EXISTENCE of
u,z is asserted; uniqueness or continuous selection is not assumed. -/
theorem exists_unit_outer_of_rank_le_one (W : Matrix (Fin 2) κ ℝ)
    (hW : W.rank ≤ 1) : ∃ u : CircleVector, OnCircle u ∧ ∃ z : κ → ℝ, outer u z = W := by
  by_cases hz : ∀ j, W 0 j = 0
  · refine ⟨![0,1], by norm_num [OnCircle], W 1, ?_⟩
    ext i j
    fin_cases i <;> simp [outer, hz]
  · obtain ⟨j,hj⟩ := not_forall.mp hz
    let a := W 1 j / W 0 j
    let r := Real.sqrt (1+a^2)
    have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hrs : r^2 = 1+a^2 := Real.sq_sqrt (by positivity)
    have hrow (k : κ) : W 1 k = a * W 0 k := by
      have hm := rank_le_one_two_column_minor W hW j k
      dsimp [a]
      field_simp [hj]
      nlinarith [hm]
    refine ⟨![1/r,a/r], ?_, fun k => r*W 0 k, ?_⟩
    · change (1/r)^2+(a/r)^2=1
      field_simp [hr0]
      nlinarith [hrs]
    · ext i k
      fin_cases i
      · simp [outer, hr0]
      · change (a / r) * (r * W 0 k) = W 1 k
        rw [hrow k]
        field_simp [hr0]

/-- If both rows of W represent skew matrices, so does the normalized second
outer factor. This proof does not pick a nonzero row; it contracts with u. -/
theorem outer_skew_factor {q : ℕ} (W : Matrix (Fin 2) (Fin q × Fin q) ℝ)
    (u : CircleVector) (hu : OnCircle u) (z : Fin q × Fin q → ℝ)
    (he : outer u z=W) (hrows : ∀ r, IsSkew (fun i j => W r (i,j))) :
    IsSkew (fun i j => z (i,j)) := by
  have hrecover (i j : Fin q) : z (i,j) =
      u 0 * W 0 (i,j)+u 1 * W 1 (i,j) := by
    rw [← he]
    dsimp [outer]
    nlinarith [congrArg (fun x : ℝ => x*z (i,j)) hu]
  change (fun i j => z (j,i)) = -(fun i j => z (i,j))
  ext i j
  have h₀ := congrFun (congrFun (hrows 0) i) j
  have h₁ := congrFun (congrFun (hrows 1) i) j
  change W 0 (j,i) = -W 0 (i,j) at h₀
  change W 1 (j,i) = -W 1 (i,j) at h₁
  simp only [Pi.neg_apply]
  rw [hrecover j i, hrecover i j, h₀, h₁]
  ring

abbrev OriginalImageCoordinates (q : ℕ) :=
  (Fin q → ℝ) × (Fin q → ℝ) × Mat q × Matrix (Fin 2) (Fin q × Fin q) ℝ

/-- A rank cone in the row-skew subspace; no Euclidean dimension is yet asserted. -/
def originalGImageSet (q : ℕ) (η : ℝ) : Set (OriginalImageCoordinates q) :=
  {p | (∀ i, |p.1 i| ≤ η) ∧ (∀ j, |p.2.1 j| ≤ η) ∧
    (∀ j : Fin q, j.val=0 → p.2.1 j=0) ∧ IsSkew p.2.2.1 ∧
    frobSq p.2.2.1 ≤ η^2 ∧
    (∀ r, IsSkew (fun i j => p.2.2.2 r (i,j))) ∧
    p.2.2.2.rank ≤ 1 ∧ frobSq p.2.2.2 ≤ η^2}

/-- Exact image equality, with the ORIGINAL definitions of g and K. -/
theorem originalG_image_eq (q : ℕ) (η : ℝ) :
    originalG '' originalK q η = originalGImageSet q η := by
  ext p
  constructor
  · rintro ⟨⟨ell,r,c,z,u⟩,hp,rfl⟩
    rcases hp with ⟨hell,hr,hr0,hc,hz,hcn,hzn,hu⟩
    refine ⟨hell,hr,hr0,hc,hcn,?_,rank_outer_le_one _ _,?_⟩
    · intro k
      change IsSkew ((u k) • z)
      change zᵀ = -z at hz
      simp only [IsSkew, Matrix.transpose_smul, hz, smul_neg]
    · change frobSq (outer u (fun ij : Fin q × Fin q => z ij.1 ij.2)) ≤ η^2
      rw [frobSq_outer hu]
      simpa only [frobSq, frobInner, Fintype.sum_prod_type, pow_two] using hzn
  · rcases p with ⟨ell,r,c,W⟩
    rintro ⟨hell,hr,hr0,hc,hcn,hrows,hRank,hWn⟩
    obtain ⟨u,hu,z,he⟩ := exists_unit_outer_of_rank_le_one W hRank
    let Z : Mat q := fun i j => z (i,j)
    have hz : IsSkew Z := outer_skew_factor W u hu z he hrows
    have hn : frobSq Z ≤ η^2 := by
      rw [← he, frobSq_outer hu] at hWn
      simpa only [Z, frobSq, frobInner, Fintype.sum_prod_type, pow_two] using hWn
    refine ⟨(ell,r,c,Z,u), ⟨hell,hr,hr0,hc,hz,hcn,hn,hu⟩,?_⟩
    change (ell,r,c,outer u (fun ij => Z ij.1 ij.2))=(ell,r,c,W)
    simpa only [Z] using congrArg (fun A => (ell,r,c,A)) he

end GS.GlobalGeometry
