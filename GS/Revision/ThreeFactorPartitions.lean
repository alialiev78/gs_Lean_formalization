module

public import GS.Extensions.StructuredRQ

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Three-factor orthogonalization with unequal block sizes

The old public theorem uses BlockSpec (one common size per factor). The lower
level Cholesky lemmas already work with arbitrary coordinate labels. We reuse
those lemmas and ordinary QR to obtain the stronger manuscript statement:

* the outer partitions are arbitrary coordinate partitions;
* the middle labels are monotone (consecutive blocks, not necessarily equal);
* both permutations are arbitrary;
* no structured QR/RQ existence hypothesis is supplied by the caller.

This is a complete proof *script*, not a current compiler certificate.

-/
noncomputable section
open GS GS.Extensions Matrix
namespace GS.Revision.Partitions
variable {n : ℕ}

/-- A labelled analogue of structured_of_ordinary_qr. Its proof reuses the
already-developed arbitrary-label triangular Gram-factor induction. -/
theorem supported_of_ordinary_qr (block : Fin n → ℕ) (B V R : Mat n)
    (σ : Equiv.Perm (Fin n)) (hB : Supported block B)
    (hdetB : IsUnit B.det) (hV : Orthogonal V) (ht : Upper R)
    (hqr : B * permMatrix σ = V * R) :
    Supported block (V * (permMatrix σ)ᵀ) ∧
    Orthogonal (V * (permMatrix σ)ᵀ) ∧
    B * permMatrix σ = (V * (permMatrix σ)ᵀ) * permMatrix σ * R := by
  let P := permMatrix σ
  have hp : Orthogonal P := perm_orthogonal σ
  have hb : B.det ≠ 0 := isUnit_iff_ne_zero.mp hdetB
  have hr : R.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hqr
    have hbp : B.det * P.det ≠ 0 := mul_ne_zero hb (orthogonal_det_ne_zero hp)
    exact hbp (by simpa only [Matrix.det_mul, hz, mul_zero] using hh)
  letI : Invertible R := Matrix.invertibleOfIsUnitDet R (isUnit_iff_ne_zero.mpr hr)
  have hgram : Rᵀ * R = Pᵀ * Bᵀ * B * P := by
    calc
      Rᵀ * R = (V * R)ᵀ * (V * R) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Vᵀ V R, hV.1]
        simp
      _ = (B * P)ᵀ * (B * P) := by rw [← hqr]
      _ = Pᵀ * Bᵀ * B * P := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have hs : Supported (fun i => block (σ i)) R := by
    apply upper_supported_of_gram_det ht hr
    rw [hgram]
    exact permuted_gram_supported hB σ
  have hsinv := supported_inverse hs
  have hback : Supported block (P * R⁻¹ * Pᵀ) := supported_perm_back σ hsinv
  have hu : V * Pᵀ = B * (P * R⁻¹ * Pᵀ) := by
    calc
      V * Pᵀ = (V * (R * R⁻¹)) * Pᵀ := by simp
      _ = (B * P) * R⁻¹ * Pᵀ := by rw [← Matrix.mul_assoc V R, ← hqr]
      _ = B * (P * R⁻¹ * Pᵀ) := by simp only [Matrix.mul_assoc]
  refine ⟨?_, hV.mul hp.transpose, ?_⟩
  · rw [hu]
    exact hB.mul hback
  · calc
      B * P = V * R := hqr
      _ = (V * Pᵀ) * P * R := by simp only [Matrix.mul_assoc, hp.1, Matrix.one_mul]

/-- Arbitrary-label structured QR, constructed from ordinary QR. -/
theorem structuredQR (block : Fin n → ℕ) (B : Mat n)
    (σ : Equiv.Perm (Fin n)) (hB : Supported block B) (hdetB : IsUnit B.det) :
    ∃ U R : Mat n, Supported block U ∧ Orthogonal U ∧ Upper R ∧
      B * permMatrix σ = U * permMatrix σ * R := by
  obtain ⟨V, R, hV, ht, he⟩ := exists_ordinary_qr (B * permMatrix σ)
  obtain ⟨hs, ho, hf⟩ := supported_of_ordinary_qr block B V R σ hB hdetB hV ht he
  exact ⟨V * (permMatrix σ)ᵀ, R, hs, ho, ht, hf⟩

/-- Arbitrary-label RQ, obtained from QR by reversal and transposition. -/
theorem structuredRQ (block : Fin n → ℕ) (B : Mat n)
    (σ : Equiv.Perm (Fin n)) (hB : Supported block B) (hdetB : IsUnit B.det) :
    ∃ U R : Mat n, Supported block U ∧ Orthogonal U ∧ Upper R ∧
      permMatrix σ * B = R * permMatrix σ * U := by
  let ρ := reversePerm n
  let P := permMatrix σ
  let J := permMatrix ρ
  let τ := ρ.trans σ.symm
  have hτ : permMatrix τ = Pᵀ * J := by
    simpa only [τ, P, J, perm_transpose] using perm_trans_matrix ρ σ.symm
  have hdt : IsUnit Bᵀ.det := by simpa only [Matrix.det_transpose] using hdetB
  obtain ⟨V, T, hV, hoV, ht, he⟩ := structuredQR block Bᵀ τ hB.transpose hdt
  let U := Vᵀ
  let R := J * Tᵀ * Jᵀ
  have hJJ : J * Jᵀ = 1 := (perm_orthogonal ρ).2
  have hre : P * B = R * P * U := by
    have hh := congrArg (fun X : Mat n => J * Xᵀ) he
    rw [hτ] at hh
    simpa only [R, U, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← Matrix.mul_assoc, hJJ, Matrix.one_mul] using hh
  exact ⟨U, R, hV.transpose, hoV.transpose, upper_reverse_transpose ht, hre⟩

/-- Consecutive blocks may have unequal sizes; monotonicity is sufficient. -/
theorem upper_blockTriangular_monotone (block : Fin n → ℕ)
    (hblock : Monotone block) {R : Mat n} (hR : Upper R) :
    R.BlockTriangular block := by
  intro i j hij
  apply hR
  by_contra hn
  have hle : i ≤ j := Nat.le_of_not_gt hn
  exact (not_lt_of_ge (hblock hle)) hij

def InA3 (b₁ b₂ b₃ : Fin n → ℕ) (P₁ P₂ A : Mat n) : Prop :=
  ∃ B₁ B₂ B₃ : Mat n, Supported b₁ B₁ ∧ Supported b₂ B₂ ∧ Supported b₃ B₃ ∧
    A = product3 B₃ P₂ B₂ P₁ B₁

def InA3Orth (b₁ b₂ b₃ : Fin n → ℕ) (P₁ P₂ A : Mat n) : Prop :=
  ∃ B₁ B₂ B₃ : Mat n, Supported b₁ B₁ ∧ Supported b₂ B₂ ∧ Supported b₃ B₃ ∧
    Orthogonal B₁ ∧ Orthogonal B₂ ∧ Orthogonal B₃ ∧ A = product3 B₃ P₂ B₂ P₁ B₁

/-- Full orthogonalization for unequal consecutive middle blocks and arbitrary
outer coordinate partitions. Structured QR/RQ are conclusions, not assumptions. -/
theorem threeFactorOrthogonalization (b₁ b₂ b₃ : Fin n → ℕ)
    (hb₂ : Monotone b₂) (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : Mat n) :
    InA3 b₁ b₂ b₃ (permMatrix σ₁) (permMatrix σ₂) A ∧ Orthogonal A ↔
      InA3Orth b₁ b₂ b₃ (permMatrix σ₁) (permMatrix σ₂) A := by
  constructor
  · rintro ⟨⟨B₁, B₂, B₃, hB₁, hB₂, hB₃, he⟩, hA⟩
    have hdetA := orthogonal_det_ne_zero hA
    have hprod : B₃.det * (permMatrix σ₂).det * B₂.det *
        (permMatrix σ₁).det * B₁.det ≠ 0 := by
      simpa only [he, product3, Matrix.det_mul] using hdetA
    have hd₁ : IsUnit B₁.det := isUnit_iff_ne_zero.mpr (by
      intro hz
      exact hprod (by simp [hz]))
    have hd₃ : IsUnit B₃.det := isUnit_iff_ne_zero.mpr (by
      intro hz
      exact hprod (by simp [hz]))
    obtain ⟨U₃, R₃, hs₃, ho₃, ht₃, he₃⟩ := structuredQR b₃ B₃ σ₂ hB₃ hd₃
    obtain ⟨U₁, R₁, hs₁, ho₁, ht₁, he₁⟩ := structuredRQ b₁ B₁ σ₁ hB₁ hd₁
    let U₂ := R₃ * B₂ * R₁
    have hp : A = U₃ * permMatrix σ₂ * U₂ * permMatrix σ₁ * U₁ := by
      calc
        A = (B₃ * permMatrix σ₂) * B₂ * (permMatrix σ₁ * B₁) := by
          rw [he]; simp only [product3, Matrix.mul_assoc]
        _ = (U₃ * permMatrix σ₂ * R₃) * B₂ * (R₁ * permMatrix σ₁ * U₁) := by
          rw [he₃, he₁]
        _ = _ := by simp only [U₂, Matrix.mul_assoc]
    have ho₂ : Orthogonal U₂ := middle_orthogonal_of_factorization hA ho₃
      (perm_orthogonal σ₂) (perm_orthogonal σ₁) ho₁ hp
    have ht₂ : U₂.BlockTriangular b₂ :=
      ((upper_blockTriangular_monotone b₂ hb₂ ht₃).mul
        (supported_blockTriangular hB₂)).mul (upper_blockTriangular_monotone b₂ hb₂ ht₁)
    have hs₂ : Supported b₂ U₂ := orthogonal_blockTriangular_supported ho₂ ht₂
    exact ⟨U₁, U₂, U₃, hs₁, hs₂, hs₃, ho₁, ho₂, ho₃, hp⟩
  · rintro ⟨U₁, U₂, U₃, hs₁, hs₂, hs₃, ho₁, ho₂, ho₃, he⟩
    refine ⟨⟨U₁, U₂, U₃, hs₁, hs₂, hs₃, he⟩, ?_⟩
    rw [he]
    exact (((ho₃.mul (perm_orthogonal σ₂)).mul ho₂).mul (perm_orthogonal σ₁)).mul ho₁

end GS.Revision.Partitions
