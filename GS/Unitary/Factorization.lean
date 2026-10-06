module

public import GS.Unitary.StructuredQR
public import GS.Unitary.GeometryAlgebra

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Full two- and three-factor unitary factorization

These equivalences are unconditional: complex structured QR and RQ supply the
supported unitary outer factors. The middle factor is then unitary and block
triangular, hence block diagonal. Permutation connectors are arbitrary, and
the statements allow all natural block sizes without extra divisibility
assumptions.
-/

noncomputable section
open Matrix

namespace GS.UnitaryGeometry
variable {n : ℕ}

def CBlockDiagonal (b : ℕ) (A : CMat n) : Prop :=
  CSupported (fun i : Fin n => i.val / b) A

def product3 (B₃ P₂ B₂ P₁ B₁ : CMat n) : CMat n :=
  B₃ * P₂ * B₂ * P₁ * B₁

def CInA2 (b₁ b₂ : ℕ) (P A : CMat n) : Prop :=
  ∃ B₁ B₂, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    A = product2 B₂ P B₁

def CInA2Unitary (b₁ b₂ : ℕ) (P A : CMat n) : Prop :=
  ∃ B₁ B₂, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    Unitary B₁ ∧ Unitary B₂ ∧ A = product2 B₂ P B₁

def CInA3 (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ A = product3 B₃ P₂ B₂ P₁ B₁

def CInA3Unitary (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ Unitary B₁ ∧ Unitary B₂ ∧ Unitary B₃ ∧
    A = product3 B₃ P₂ B₂ P₁ B₁

theorem inA3Unitary_implies_inA3_and_unitary {b₁ b₂ b₃ : ℕ} {P₁ P₂ A : CMat n}
    (hP₁ : Unitary P₁) (hP₂ : Unitary P₂)
    (h : CInA3Unitary b₁ b₂ b₃ P₁ P₂ A) :
    CInA3 b₁ b₂ b₃ P₁ P₂ A ∧ Unitary A := by
  rcases h with ⟨B₁,B₂,B₃,hb₁,hb₂,hb₃,hu₁,hu₂,hu₃,rfl⟩
  exact ⟨⟨B₁,B₂,B₃,hb₁,hb₂,hb₃,rfl⟩,
    (((hu₃.mul hP₂).mul hu₂).mul hP₁).mul hu₁⟩

/-- Cancellation of all unitary factors isolates a unitary middle factor. -/
theorem middle_unitary_of_factorization {Q U₃ P₂ M P₁ U₁ : CMat n}
    (hQ : Unitary Q) (hU₃ : Unitary U₃) (hP₂ : Unitary P₂)
    (hP₁ : Unitary P₁) (hU₁ : Unitary U₁)
    (he : Q = U₃ * P₂ * M * P₁ * U₁) : Unitary M := by
  have hm : M = P₂ᴴ * U₃ᴴ * Q * U₁ᴴ * P₁ᴴ := by
    symm
    calc
      P₂ᴴ * U₃ᴴ * Q * U₁ᴴ * P₁ᴴ =
          (P₂ᴴ * (U₃ᴴ * U₃) * P₂) * M * (P₁ * (U₁ * U₁ᴴ) * P₁ᴴ) := by
        rw [he]
        simp only [Matrix.mul_assoc]
      _ = M := by simp [hU₃.1,hU₁.2,hP₂.1,hP₁.2]
  rw [hm]
  exact (((hP₂.conjTranspose.mul hU₃.conjTranspose).mul hQ).mul
    hU₁.conjTranspose).mul hP₁.conjTranspose

/-- Closing step with explicit QR/RQ witnesses; existence is discharged below. -/
theorem threeFactor_from_structured_QR_RQ {b₁ b₂ b₃ : ℕ}
    (B₁ B₂ B₃ P₁ P₂ Q U₁ U₃ R₁ R₃ : CMat n)
    (hB₂ : CBlockDiagonal b₂ B₂)
    (hU₁ : CBlockDiagonal b₁ U₁) (hU₃ : CBlockDiagonal b₃ U₃)
    (ho₁ : Unitary U₁) (ho₃ : Unitary U₃)
    (hp₁ : Unitary P₁) (hp₂ : Unitary P₂) (hq : Unitary Q)
    (hQ : Q = product3 B₃ P₂ B₂ P₁ B₁)
    (hqr : B₃ * P₂ = U₃ * P₂ * R₃)
    (hrq : P₁ * B₁ = R₁ * P₁ * U₁)
    (ht₁ : CUpper R₁) (ht₃ : CUpper R₃) :
    CInA3Unitary b₁ b₂ b₃ P₁ P₂ Q := by
  let U₂ := R₃ * B₂ * R₁
  have he : Q = U₃ * P₂ * U₂ * P₁ * U₁ := by
    calc
      Q = (B₃ * P₂) * B₂ * (P₁ * B₁) := by
        rw [hQ]; simp only [product3, Matrix.mul_assoc]
      _ = (U₃ * P₂ * R₃) * B₂ * (R₁ * P₁ * U₁) := by rw [hqr,hrq]
      _ = U₃ * P₂ * U₂ * P₁ * U₁ := by simp only [U₂, Matrix.mul_assoc]
  have ho₂ : Unitary U₂ := middle_unitary_of_factorization hq ho₃ hp₂ hp₁ ho₁ he
  have ht₂ : U₂.BlockTriangular (fun i : Fin n => i.val / b₂) :=
    ((cUpper_blockTriangular ht₃).mul (cSupported_blockTriangular hB₂)).mul
      (cUpper_blockTriangular ht₁)
  have hb₂ : CBlockDiagonal b₂ U₂ := unitary_blockTriangular_supported ho₂ ht₂
  exact ⟨U₁,U₂,U₃,hU₁,hb₂,hU₃,ho₁,ho₂,ho₃,he⟩

/-- Every unitary three-factor product has supported unitary factors. -/
theorem threeFactorUnitarization (b₁ b₂ b₃ : ℕ)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : CMat n) :
    CInA3 b₁ b₂ b₃ (cPermMatrix σ₁) (cPermMatrix σ₂) A ∧ Unitary A ↔
      CInA3Unitary b₁ b₂ b₃ (cPermMatrix σ₁) (cPermMatrix σ₂) A := by
  constructor
  · rintro ⟨⟨B₁,B₂,B₃,hb₁,hb₂,hb₃,he⟩,hA⟩
    have hprod : B₃.det * (cPermMatrix σ₂).det * B₂.det *
        (cPermMatrix σ₁).det * B₁.det ≠ 0 := by
      simpa only [he, product3, Matrix.det_mul] using unitary_det_ne_zero hA
    have hdet₁ : IsUnit B₁.det := isUnit_iff_ne_zero.mpr (by
      intro hz
      exact hprod (by simp [hz]))
    have hdet₃ : IsUnit B₃.det := isUnit_iff_ne_zero.mpr (by
      intro hz
      exact hprod (by simp [hz]))
    obtain ⟨U₃,R₃,hu₃,ho₃,ht₃,eq₃⟩ :=
      structuredQR (fun i : Fin n => i.val/b₃) B₃ σ₂ hb₃ hdet₃
    obtain ⟨U₁,R₁,hu₁,ho₁,ht₁,eq₁⟩ :=
      structuredRQ (fun i : Fin n => i.val/b₁) B₁ σ₁ hb₁ hdet₁
    exact threeFactor_from_structured_QR_RQ B₁ B₂ B₃
      (cPermMatrix σ₁) (cPermMatrix σ₂) A U₁ U₃ R₁ R₃ hb₂ hu₁ hu₃ ho₁ ho₃
      (cPerm_unitary σ₁) (cPerm_unitary σ₂) hA he eq₃ eq₁ ht₁ ht₃
  · exact inA3Unitary_implies_inA3_and_unitary (cPerm_unitary σ₁) (cPerm_unitary σ₂)

theorem cSingleton_block_supported {A : CMat n}
    (hA : CBlockDiagonal 1 A) (block : Fin n → ℕ) : CSupported block A := by
  intro i j hij
  apply hA
  simp only [Nat.div_one]
  intro he
  exact hij (congrArg block (Fin.ext he))

/-- The two-factor theorem absorbs the extra singleton unitary left layer. -/
theorem twoFactorUnitarization (b₁ b₂ : ℕ) (σ : Equiv.Perm (Fin n)) (A : CMat n) :
    CInA2 b₁ b₂ (cPermMatrix σ) A ∧ Unitary A ↔
      CInA2Unitary b₁ b₂ (cPermMatrix σ) A := by
  constructor
  · rintro ⟨⟨B₁,B₂,hb₁,hb₂,he⟩,hA⟩
    have hmem : CInA3 b₁ b₂ 1 (cPermMatrix σ)
        (cPermMatrix (Equiv.refl (Fin n))) A := by
      refine ⟨B₁,B₂,1,hb₁,hb₂,CSupported.one,?_⟩
      simpa only [product3,product2,cPerm_refl,Matrix.one_mul] using he
    obtain ⟨U₁,U₂,U₃,hu₁,hu₂,hu₃,ho₁,ho₂,ho₃,hprod⟩ :=
      (threeFactorUnitarization b₁ b₂ 1 σ (Equiv.refl _) A).mp ⟨hmem,hA⟩
    have hu₃' : CBlockDiagonal b₂ U₃ :=
      cSingleton_block_supported hu₃ (fun i => i.val/b₂)
    refine ⟨U₁,U₃*U₂,hu₁,hu₃'.mul hu₂,ho₁,ho₃.mul ho₂,?_⟩
    simpa only [product3,product2,cPerm_refl,Matrix.mul_one,Matrix.mul_assoc] using hprod
  · rintro ⟨B₁,B₂,hb₁,hb₂,ho₁,ho₂,he⟩
    refine ⟨⟨B₁,B₂,hb₁,hb₂,he⟩,?_⟩
    rw [he]
    exact (ho₂.mul (cPerm_unitary σ)).mul ho₁

end GS.UnitaryGeometry
