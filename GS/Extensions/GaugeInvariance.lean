module

public import GS.Extensions.TwoFactorProjection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Factorization independence of the two-factor derivative image and projector

This is the algebraic descent step; it does not assert
that the image has already been equipped with a smooth quotient manifold.
All block conditions, orthogonality and equality of the represented matrices
are explicit hypotheses. No assumption of uniqueness of the factors is made.
-/

noncomputable section
open Matrix
namespace GS.Extensions
variable {n : ℕ}

 theorem tangentParam_gauge (L R P A B C Ω : Mat n)
    (hA : Orthogonal A) (hB : Orthogonal B) (he : A*P*B=P) :
    tangentParam (L*A) P (B*R) C Ω =
      tangentParam L P R (A*C*Aᵀ) (Bᵀ*Ω*B) := by
  have hPB : P*B=Aᵀ*P := by
    have hh := congrArg (fun M : Mat n => Aᵀ*M) he
    simpa only [← Matrix.mul_assoc,hA.1,Matrix.one_mul] using hh
  have hAP : A*P=P*Bᵀ := by
    have hh := congrArg (fun M : Mat n => M*Bᵀ) he
    simpa only [Matrix.mul_assoc,hB.2,Matrix.mul_one] using hh
  unfold tangentParam
  calc
    _ = L*(A*C)*(P*B)*R + L*(A*P)*Ω*B*R := by noncomm_ring
    _ = L*(A*C)*(Aᵀ*P)*R + L*(P*Bᵀ)*Ω*B*R := by rw [hPB,hAP]
    _ = _ := by noncomm_ring

 theorem twoFactorDirection_gauge_forward
    (block₁ block₂ : Fin n → ℕ) (L R P A B X : Mat n)
    (hsA : Supported block₂ A) (hsB : Supported block₁ B)
    (hA : Orthogonal A) (hB : Orthogonal B) (he : A*P*B=P)
    (hX : TwoFactorDirection block₁ block₂ (L*A) P (B*R) X) :
    TwoFactorDirection block₁ block₂ L P R X := by
  obtain ⟨C,Ω,hsC,hkC,hsΩ,hkΩ,hX⟩ := hX
  refine ⟨A*C*Aᵀ,Bᵀ*Ω*B,(hsA.mul hsC).mul hsA.transpose,
    conjugate_skew A C hkC,(hsB.transpose.mul hsΩ).mul hsB,?_,?_⟩
  · simpa only [Matrix.transpose_transpose] using conjugate_skew Bᵀ Ω hkΩ
  · exact hX.trans (tangentParam_gauge L R P A B C Ω hA hB he)

 theorem twoFactorDirection_gauge_iff
    (block₁ block₂ : Fin n → ℕ) (L R P A B X : Mat n)
    (hsA : Supported block₂ A) (hsB : Supported block₁ B)
    (hA : Orthogonal A) (hB : Orthogonal B) (he : A*P*B=P) :
    TwoFactorDirection block₁ block₂ (L*A) P (B*R) X ↔
      TwoFactorDirection block₁ block₂ L P R X := by
  constructor
  · exact twoFactorDirection_gauge_forward block₁ block₂ L R P A B X
      hsA hsB hA hB he
  · intro hX
    have hinv : Aᵀ*P*Bᵀ=P := by
      calc
        Aᵀ*P*Bᵀ = Aᵀ*(A*P*B)*Bᵀ := by rw [he]
        _ = (Aᵀ*A)*P*(B*Bᵀ) := by noncomm_ring
        _ = P := by rw [hA.1,hB.2]; simp
    have hX' : TwoFactorDirection block₁ block₂ ((L*A)*Aᵀ) P (Bᵀ*(B*R)) X := by
      have hBR : Bᵀ*(B*R) = R := by
        rw [← Matrix.mul_assoc, hB.1, Matrix.one_mul]
      simpa only [hBR,Matrix.mul_assoc,hA.2,Matrix.mul_one] using hX
    exact twoFactorDirection_gauge_forward block₁ block₂ (L*A) (B*R) P Aᵀ Bᵀ X
      hsA.transpose hsB.transpose hA.transpose hB.transpose hinv hX'

 theorem twoFactorDirection_factorization_independent
    (block₁ block₂ : Fin n → ℕ) (L R L' R' P X : Mat n)
    (hsL : Supported block₂ L) (hsR : Supported block₁ R)
    (hsL' : Supported block₂ L') (hsR' : Supported block₁ R')
    (hL : Orthogonal L) (hR : Orthogonal R)
    (hL' : Orthogonal L') (hR' : Orthogonal R')
    (hf : product2 L P R=product2 L' P R') :
    TwoFactorDirection block₁ block₂ L P R X ↔
      TwoFactorDirection block₁ block₂ L' P R' X := by
  let A := Lᵀ*L'
  let B := R'*Rᵀ
  have hA : Orthogonal A := hL.transpose.mul hL'
  have hB : Orthogonal B := hR'.mul hR.transpose
  have hsA : Supported block₂ A := hsL.transpose.mul hsL'
  have hsB : Supported block₁ B := hsR'.mul hsR.transpose
  have hLA : L*A=L' := by
    simp only [A,← Matrix.mul_assoc,hL.2,Matrix.one_mul]
  have hBR : B*R=R' := by
    simp only [B,Matrix.mul_assoc,hR.1,Matrix.mul_one]
  have he : A*P*B=P := by
    calc
      A*P*B = Lᵀ*(product2 L' P R')*Rᵀ := by
        simp only [A,B,product2,Matrix.mul_assoc]
      _ = Lᵀ*(product2 L P R)*Rᵀ := by rw [← hf]
      _ = (Lᵀ*L)*P*(R*Rᵀ) := by simp only [product2,Matrix.mul_assoc]
      _ = P := by rw [hL.1,hR.2]; simp
  have hh := (twoFactorDirection_gauge_iff block₁ block₂ L R P A B X
    hsA hsB hA hB he).symm
  simpa only [hLA,hBR] using hh

/-- The exact projector is a function of the represented matrix, even when its
factorization is not unique. This is stronger than factorwise smoothness. -/
 theorem twoFactorProjection_factorization_independent
    (block₁ block₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (L R L' R' Z : Mat n)
    (hsL : Supported block₂ L) (hsR : Supported block₁ R)
    (hsL' : Supported block₂ L') (hsR' : Supported block₁ R')
    (hL : Orthogonal L) (hR : Orthogonal R)
    (hL' : Orthogonal L') (hR' : Orthogonal R')
    (hf : product2 L (permMatrix σ) R=product2 L' (permMatrix σ) R') :
    twoFactorProjection block₁ block₂ σ L R Z =
      twoFactorProjection block₁ block₂ σ L' R' Z := by
  let X := twoFactorProjection block₁ block₂ σ L R Z
  let Y := twoFactorProjection block₁ block₂ σ L' R' Z
  have hx := twoFactorProjection_in_direction block₁ block₂ σ L R Z
  have hy := twoFactorProjection_in_direction block₁ block₂ σ L' R' Z
  have hxy (W : Mat n) := twoFactorDirection_factorization_independent block₁ block₂
    L R L' R' (permMatrix σ) W hsL hsR hsL' hsR' hL hR hL' hR' hf
  have h₁ := twoFactorProjection_pythagorean block₁ block₂ σ L R Z Y hL hR
    ((hxy Y).mpr hy)
  have h₂ := twoFactorProjection_pythagorean block₁ block₂ σ L' R' Z X hL' hR'
    ((hxy X).mp hx)
  change frobSq (Z-Y)=frobSq (Z-X)+frobSq (X-Y) at h₁
  change frobSq (Z-X)=frobSq (Z-Y)+frobSq (Y-X) at h₂
  have hz : frobSq (X-Y)=0 := by
    linarith [frobSq_nonneg (X-Y),frobSq_nonneg (Y-X)]
  exact sub_eq_zero.mp ((frobSq_eq_zero_iff _).mp hz)

end GS.Extensions
