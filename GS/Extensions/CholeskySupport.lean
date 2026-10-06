module

public import GS.Specifications

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The missing structural implication for an actual Cholesky/QR factor

This module does not merely postulate
preservation of support. It proves it by induction from R^T R, triangularity
and nonzero diagonal, then applies it to the original CholeskySupportGoal.
Permutations of arbitrary triangular matrices are NOT claimed block diagonal.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.Extensions
variable {n : ℕ}

 theorem orthogonal_det_ne_zero {Q : Mat n} (hQ : Orthogonal Q) : Q.det ≠ 0 := by
  intro hz
  have h := congrArg Matrix.det hQ.1
  simp [Matrix.det_mul, Matrix.det_transpose, hz] at h

 theorem upper_diagonal_ne_zero {R : Mat n} (ht : Upper R) (hd : R.det ≠ 0)
    (i : Fin n) : R i i ≠ 0 := by
  have hdet : R.det = ∏ j, R j j := Matrix.det_of_upperTriangular (by
    intro j k hjk
    exact ht hjk)
  rw [hdet] at hd
  exact (Finset.prod_ne_zero_iff.mp hd) i (Finset.mem_univ i)

/-- A triangular Gram factor cannot connect two distinct block labels if its
Gram matrix has no such connections. This is a scalar induction, NOT a claim
that every zero in a Gram matrix is preserved by Cholesky. -/
 theorem upper_supported_of_gram {block : Fin n → ℕ} {R : Mat n}
    (ht : Upper R) (hd : ∀ i, R i i ≠ 0)
    (hg : Supported block (Rᵀ*R)) : Supported block R := by
  have hrows : ∀ m : ℕ, ∀ i : Fin n, i.val = m →
      ∀ j : Fin n, block i ≠ block j → R i j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i him j hij
      have hsum : (Rᵀ*R) i j = R i i * R i j := by
        rw [Matrix.mul_apply]
        change (∑ k : Fin n, R k i * R k j) = R i i * R i j
        apply Finset.sum_eq_single i
        · intro k hk hki
          by_cases hlt : k.val < i.val
          · by_cases hbi : block k = block i
            · have hbj : block k ≠ block j := by simpa only [hbi] using hij
              rw [ih k.val (by omega) k rfl j hbj, mul_zero]
            · rw [ih k.val (by omega) k rfl i hbi, zero_mul]
          · have hgt : i.val < k.val := by
              have hv : k.val ≠ i.val := fun he => hki (Fin.ext he)
              omega
            rw [ht hgt, zero_mul]
        · intro hn
          exact False.elim (hn (Finset.mem_univ i))
      have he : R i i * R i j = 0 := hsum.symm.trans (hg i j hij)
      exact (mul_eq_zero.mp he).resolve_left (hd i)
  intro i j hij
  exact hrows i.val i rfl j hij

 theorem upper_supported_of_gram_det {block : Fin n → ℕ} {R : Mat n}
    (ht : Upper R) (hd : R.det ≠ 0)
    (hg : Supported block (Rᵀ*R)) : Supported block R :=
  upper_supported_of_gram ht (upper_diagonal_ne_zero ht hd) hg

/-- A support class is closed under matrix inverse for invertible matrices.
Both block orders are used, so this is not just a triangular conclusion. -/
 theorem supported_inverse {block : Fin n → ℕ} {A : Mat n}
    (hA : Supported block A) [Invertible A] : Supported block A⁻¹ := by
  have ha : A.BlockTriangular block := supported_blockTriangular hA
  have hat : Aᵀ.BlockTriangular block := supported_blockTriangular hA.transpose
  have hi := Matrix.blockTriangular_inv_of_blockTriangular ha
  have hit := Matrix.blockTriangular_inv_of_blockTriangular hat
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hz := hit (i := j) (j := i) hlt
    simpa only [← Matrix.transpose_nonsing_inv, Matrix.transpose_apply] using hz
  · exact hi hgt

 theorem supported_perm_back {block : Fin n → ℕ} (σ : Equiv.Perm (Fin n))
    {R : Mat n} (hR : Supported (fun i => block (σ i)) R) :
    Supported block (permMatrix σ*R*(permMatrix σ)ᵀ) := by
  intro i j hij
  rw [perm_conjugate_apply]
  apply hR
  simpa only [Equiv.apply_symm_apply] using hij

 theorem permuted_gram_supported {block : Fin n → ℕ} {B : Mat n}
    (hB : Supported block B) (σ : Equiv.Perm (Fin n)) :
    Supported (fun i => block (σ i)) ((permMatrix σ)ᵀ*Bᵀ*B*permMatrix σ) := by
  have hh : Supported block (Bᵀ*B) := hB.transpose.mul hB
  intro i j hij
  have he : ((permMatrix σ)ᵀ*Bᵀ*B*permMatrix σ) i j = (Bᵀ*B) (σ i) (σ j) := by
    rw [perm_transpose]
    simpa only [Matrix.mul_assoc, perm_transpose, Equiv.symm_symm] using
      perm_conjugate_apply σ.symm (Bᵀ*B) i j
  rw [he]
  exact hh _ _ hij

/-- This proves the original Cholesky support specification.
 -/
 theorem choleskySupport : GS.Specifications.CholeskySupportGoal := by
  intro n s B R σ hB hdetB ht hgram
  have hb : B.det ≠ 0 := isUnit_iff_ne_zero.mp hdetB
  have hp : (permMatrix σ).det ≠ 0 := orthogonal_det_ne_zero (perm_orthogonal σ)
  have hr : R.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hgram
    simp only [Matrix.det_mul, Matrix.det_transpose] at hh
    have hn : (permMatrix σ).det * B.det * B.det * (permMatrix σ).det ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hp hb) hb) hp
    exact hn (by simpa only [hz, zero_mul] using hh.symm)
  have hs : Supported (fun i : Fin n => (σ i).val / s.size) (Rᵀ*R) := by
    rw [hgram]
    exact permuted_gram_supported hB σ
  exact supported_perm_back σ (upper_supported_of_gram_det ht hr hs)

/-- Support of the actual Q factor of ordinary QR. The input QR is an ordinary
factorization, with NO support condition on Q or R assumed. -/
 theorem structured_of_ordinary_qr (b : ℕ) (B V R : Mat n)
    (σ : Equiv.Perm (Fin n)) (hB : BlockDiagonal b B)
    (hdetB : IsUnit B.det) (hV : Orthogonal V) (ht : Upper R)
    (hqr : B*permMatrix σ = V*R) :
    BlockDiagonal b (V*(permMatrix σ)ᵀ) ∧
    Orthogonal (V*(permMatrix σ)ᵀ) ∧
    B*permMatrix σ = (V*(permMatrix σ)ᵀ)*permMatrix σ*R := by
  let P := permMatrix σ
  have hp : Orthogonal P := perm_orthogonal σ
  have hb : B.det ≠ 0 := isUnit_iff_ne_zero.mp hdetB
  have hr : R.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hqr
    have hbp : B.det*P.det ≠ 0 := mul_ne_zero hb (orthogonal_det_ne_zero hp)
    exact hbp (by simpa only [Matrix.det_mul, hz, mul_zero] using hh)
  letI : Invertible R := Matrix.invertibleOfIsUnitDet R (isUnit_iff_ne_zero.mpr hr)
  have hgram : Rᵀ*R = Pᵀ*Bᵀ*B*P := by
    calc
      Rᵀ*R = (V*R)ᵀ*(V*R) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Vᵀ V R, hV.1]
        simp
      _ = (B*P)ᵀ*(B*P) := by rw [← hqr]
      _ = Pᵀ*Bᵀ*B*P := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have hs : Supported (fun i : Fin n => (σ i).val / b) R := by
    apply upper_supported_of_gram_det ht hr
    rw [hgram]
    exact permuted_gram_supported hB σ
  have hsinv := supported_inverse hs
  have hback : BlockDiagonal b (P*R⁻¹*Pᵀ) := supported_perm_back σ hsinv
  have hu : V*Pᵀ = B*(P*R⁻¹*Pᵀ) := by
    calc
      V*Pᵀ = (V*(R*R⁻¹))*Pᵀ := by simp
      _ = (B*P)*R⁻¹*Pᵀ := by rw [← Matrix.mul_assoc V R, ← hqr]
      _ = B*(P*R⁻¹*Pᵀ) := by simp only [Matrix.mul_assoc]
  refine ⟨?_, hV.mul hp.transpose, ?_⟩
  · rw [hu]
    exact hB.mul hback
  · calc
      B*P = V*R := hqr
      _ = (V*Pᵀ)*P*R := by simp only [Matrix.mul_assoc, hp.1, Matrix.one_mul]

end GS.Extensions
