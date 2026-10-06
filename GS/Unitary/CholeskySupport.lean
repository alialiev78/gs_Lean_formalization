module

public import GS.Unitary.OrdinaryQR
public import GS.Unitary.Permutations

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Support recovery for the actual complex triangular Gram factor. This
proves support of the unitary factor obtained from ordinary complex QR. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace GS.UnitaryGeometry
variable {n : ℕ}
 theorem upper_diagonal_ne_zero {R : CMat n} (ht : CUpper R) (hd : R.det ≠ 0)
    (i : Fin n) : R i i ≠ 0 := by
  have hdet : R.det = ∏ j, R j j := Matrix.det_of_upperTriangular (by
    intro j k hjk
    exact ht hjk)
  rw [hdet] at hd
  exact (Finset.prod_ne_zero_iff.mp hd) i (Finset.mem_univ i)

/-- A triangular Gram factor cannot connect two distinct block labels if its
Gram matrix has no such connections. This is a scalar induction, NOT a claim
that every zero in a Gram matrix is preserved by Cholesky. -/
 theorem upper_supported_of_gram {block : Fin n → ℕ} {R : CMat n}
    (ht : CUpper R) (hd : ∀ i, R i i ≠ 0)
    (hg : CSupported block (Rᴴ*R)) : CSupported block R := by
  have hrows : ∀ m : ℕ, ∀ i : Fin n, i.val = m →
      ∀ j : Fin n, block i ≠ block j → R i j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i him j hij
      have hsum : (Rᴴ*R) i j = star (R i i) * R i j := by
        rw [Matrix.mul_apply]
        change (∑ k : Fin n, star (R k i) * R k j) = star (R i i) * R i j
        apply Finset.sum_eq_single i
        · intro k hk hki
          by_cases hlt : k.val < i.val
          · by_cases hbi : block k = block i
            · have hbj : block k ≠ block j := by simpa only [hbi] using hij
              rw [ih k.val (by omega) k rfl j hbj, mul_zero]
            · rw [ih k.val (by omega) k rfl i hbi, star_zero, zero_mul]
          · have hgt : i.val < k.val := by
              have hv : k.val ≠ i.val := fun he => hki (Fin.ext he)
              omega
            rw [ht hgt, star_zero, zero_mul]
        · intro hn
          exact False.elim (hn (Finset.mem_univ i))
      have he : star (R i i) * R i j = 0 := hsum.symm.trans (hg i j hij)
      exact (mul_eq_zero.mp he).resolve_left (by simpa using hd i)
  intro i j hij
  exact hrows i.val i rfl j hij

 theorem upper_supported_of_gram_det {block : Fin n → ℕ} {R : CMat n}
    (ht : CUpper R) (hd : R.det ≠ 0)
    (hg : CSupported block (Rᴴ*R)) : CSupported block R :=
  upper_supported_of_gram ht (upper_diagonal_ne_zero ht hd) hg


/-- Support of the actual Q factor of ordinary QR. The input QR is an ordinary
factorization, with NO support condition on Q or R assumed. -/
 theorem structured_of_ordinary_qr (block : Fin n → ℕ) (B V R : CMat n)
    (σ : Equiv.Perm (Fin n)) (hB : CSupported block B)
    (hdetB : IsUnit B.det) (hV : Unitary V) (ht : CUpper R)
    (hqr : B*cPermMatrix σ = V*R) :
    CSupported block (V*(cPermMatrix σ)ᴴ) ∧
    Unitary (V*(cPermMatrix σ)ᴴ) ∧
    B*cPermMatrix σ = (V*(cPermMatrix σ)ᴴ)*cPermMatrix σ*R := by
  let P := cPermMatrix σ
  have hp : Unitary P := cPerm_unitary σ
  have hb : B.det ≠ 0 := isUnit_iff_ne_zero.mp hdetB
  have hr : R.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hqr
    have hbp : B.det*P.det ≠ 0 := mul_ne_zero hb (unitary_det_ne_zero hp)
    exact hbp (by simpa only [Matrix.det_mul, hz, mul_zero] using hh)
  letI : Invertible R := Matrix.invertibleOfIsUnitDet R (isUnit_iff_ne_zero.mpr hr)
  have hgram : Rᴴ*R = Pᴴ*Bᴴ*B*P := by
    calc
      Rᴴ*R = (V*R)ᴴ*(V*R) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Vᴴ V R, hV.1]
        simp
      _ = (B*P)ᴴ*(B*P) := by rw [← hqr]
      _ = Pᴴ*Bᴴ*B*P := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hs : CSupported (fun i : Fin n => block (σ i)) R := by
    apply upper_supported_of_gram_det ht hr
    rw [hgram]
    exact cPermuted_gram_supported hB σ
  have hsinv := cSupported_inverse hs
  have hback : CSupported block (P*R⁻¹*Pᴴ) := cSupported_perm_back σ hsinv
  have hu : V*Pᴴ = B*(P*R⁻¹*Pᴴ) := by
    calc
      V*Pᴴ = (V*(R*R⁻¹))*Pᴴ := by simp
      _ = (B*P)*R⁻¹*Pᴴ := by rw [← Matrix.mul_assoc V R, ← hqr]
      _ = B*(P*R⁻¹*Pᴴ) := by simp only [Matrix.mul_assoc]
  refine ⟨?_, hV.mul hp.conjTranspose, ?_⟩
  · rw [hu]
    exact hB.mul hback
  · calc
      B*P = V*R := hqr
      _ = (V*Pᴴ)*P*R := by simp only [Matrix.mul_assoc, hp.1, Matrix.one_mul]


end GS.UnitaryGeometry
