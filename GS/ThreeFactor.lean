module

public import GS.Core

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Closing the three-factor orthogonalization argument

IMPORTANT: `threeFactor_from_structured_QR_RQ` is a CONDITIONAL theorem.
It does not prove the existence of the structured QR/RQ factorizations.
Those existence goals are declared in `Specifications.lean`, with no axioms.
The unconditional main theorem is GS.Extensions.threeFactorOrthogonalization,
which supplies those existence proofs in GS.Extensions.StructuredRQ.

-/

noncomputable section
open Matrix
namespace GS

def Upper {n : ℕ} (A : Mat n) : Prop := A.BlockTriangular (fun i => i.val)

/-- Ordinary upper triangularity implies upper triangularity in consecutive blocks. -/
theorem upper_blockTriangular {n b : ℕ} {A : Mat n} (h : Upper A) :
    A.BlockTriangular (fun i : Fin n => i.val / b) := by
  intro i j hij
  apply h
  by_contra hn
  have hle : i.val ≤ j.val := Nat.le_of_not_gt hn
  have hdiv : i.val / b ≤ j.val / b := Nat.div_le_div_right hle
  exact (not_lt_of_ge hdiv) hij

theorem supported_blockTriangular {n : ℕ} {block : Fin n → ℕ} {A : Mat n}
    (h : Supported block A) : A.BlockTriangular block := by
  intro i j hij
  exact h i j (Ne.symm (Nat.ne_of_lt hij))

/-- This is the actual finite-matrix triangular obstruction, not a schematic tag. -/
theorem orthogonal_blockTriangular_supported {n : ℕ} {block : Fin n → ℕ}
    {U : Mat n} (hU : Orthogonal U) (htri : U.BlockTriangular block) :
    Supported block U := by
  letI : Invertible U :=
    { invOf := Uᵀ, invOf_mul_self := hU.1, mul_invOf_self := hU.2 }
  have hi : U⁻¹.BlockTriangular block :=
    Matrix.blockTriangular_inv_of_blockTriangular htri
  rw [Matrix.inv_eq_left_inv hU.1] at hi
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hi hlt
  · exact htri hgt

/-- A helper with explicitly supplied inverse identities; useful for metric completion. -/
theorem middle_orthogonal_of_factorization {n : ℕ}
    {Q U₃ P₂ M P₁ U₁ : Mat n}
    (hQ : Orthogonal Q) (hU₃ : Orthogonal U₃) (hP₂ : Orthogonal P₂)
    (hP₁ : Orthogonal P₁) (hU₁ : Orthogonal U₁)
    (he : Q = U₃ * P₂ * M * P₁ * U₁) : Orthogonal M := by
  have hm : M = P₂ᵀ * U₃ᵀ * Q * U₁ᵀ * P₁ᵀ := by
    symm
    calc
      P₂ᵀ * U₃ᵀ * Q * U₁ᵀ * P₁ᵀ =
          (P₂ᵀ * (U₃ᵀ * U₃) * P₂) * M * (P₁ * (U₁ * U₁ᵀ) * P₁ᵀ) := by
        rw [he]
        simp only [Matrix.mul_assoc]
      _ = M := by simp [hU₃.1,hU₁.2,hP₂.1,hP₁.2]
  rw [hm]
  exact (((hP₂.transpose.mul hU₃.transpose).mul hQ).mul hU₁.transpose).mul hP₁.transpose

/-- Conditional closing theorem: structured QR/RQ witnesses are genuine inputs.
The unresolved existence of these witnesses is NOT hidden in the result. -/
theorem threeFactor_from_structured_QR_RQ {n b₁ b₂ b₃ : ℕ}
    (B₁ B₂ B₃ P₁ P₂ Q U₁ U₃ R₁ R₃ : Mat n)
    (hB₂ : BlockDiagonal b₂ B₂)
    (hU₁ : BlockDiagonal b₁ U₁) (hU₃ : BlockDiagonal b₃ U₃)
    (ho₁ : Orthogonal U₁) (ho₃ : Orthogonal U₃)
    (hp₁ : Orthogonal P₁) (hp₂ : Orthogonal P₂) (hq : Orthogonal Q)
    (hQ : Q = product3 B₃ P₂ B₂ P₁ B₁)
    (hqr : B₃ * P₂ = U₃ * P₂ * R₃)
    (hrq : P₁ * B₁ = R₁ * P₁ * U₁)
    (ht₁ : Upper R₁) (ht₃ : Upper R₃) :
    InA3Orth b₁ b₂ b₃ P₁ P₂ Q := by
  let U₂ := R₃ * B₂ * R₁
  have he : Q = U₃ * P₂ * U₂ * P₁ * U₁ := by
    calc
      Q = (B₃ * P₂) * B₂ * (P₁ * B₁) := by
        rw [hQ]; simp only [product3, Matrix.mul_assoc]
      _ = (U₃ * P₂ * R₃) * B₂ * (R₁ * P₁ * U₁) := by rw [hqr,hrq]
      _ = U₃ * P₂ * U₂ * P₁ * U₁ := by simp only [U₂, Matrix.mul_assoc]
  have ho₂ : Orthogonal U₂ := middle_orthogonal_of_factorization hq ho₃ hp₂ hp₁ ho₁ he
  have ht₂ : U₂.BlockTriangular (fun i : Fin n => i.val / b₂) :=
    ((upper_blockTriangular ht₃).mul (supported_blockTriangular hB₂)).mul
      (upper_blockTriangular ht₁)
  have hb₂ : BlockDiagonal b₂ U₂ := orthogonal_blockTriangular_supported ho₂ ht₂
  exact ⟨U₁,U₂,U₃,hU₁,hb₂,hU₃,ho₁,ho₂,ho₃,he⟩

end GS
