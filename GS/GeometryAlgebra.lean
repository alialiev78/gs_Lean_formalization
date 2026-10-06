module

public import GS.Projection
public import Mathlib.Tactic.NoncommRing

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Algebra underlying tangent operations and transport

The Taylor identity is an exact polynomial identity. It is not asserted to be
a proof of existence of an embedded manifold, a quotient retraction, or of a
geodesic. These analytic obligations are separated in the coverage report.

-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS

variable {n : ℕ}

def tangentParam (B₂ P B₁ C Ω : Mat n) : Mat n :=
  B₂ * C * P * B₁ + B₂ * P * Ω * B₁

theorem conjugate_skew (B C : Mat n) (hC : IsSkew C) : IsSkew (B*C*Bᵀ) := by
  unfold IsSkew at *
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hC]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem conjugate_supported (block : Fin n → ℕ) (B C : Mat n)
    (hB : Supported block B) (hC : Supported block C) :
    Supported block (B*C*Bᵀ) := (hB.mul hC).mul hB.transpose

theorem left_right_generator (B C : Mat n) (hB : Orthogonal B) :
    (B*C*Bᵀ)*B = B*C := by
  calc
    (B*C*Bᵀ)*B = B*C*(Bᵀ*B) := by simp only [Matrix.mul_assoc]
    _ = B*C := by rw [hB.1]; simp

theorem tangentParam_factored (B₂ P B₁ C Ω : Mat n) (hP : Orthogonal P) :
    tangentParam B₂ P B₁ C Ω = B₂ * (C + P*Ω*Pᵀ) * (P*B₁) := by
  symm
  calc
    B₂ * (C + P*Ω*Pᵀ) * (P*B₁) =
        B₂*C*P*B₁ + B₂*P*Ω*(Pᵀ*P)*B₁ := by noncomm_ring
    _ = tangentParam B₂ P B₁ C Ω := by
      rw [hP.1]
      simp [tangentParam]

/-- Frobenius norm identity once the nonoverlap inner product is zero. -/
theorem tangentParam_frobSq (B₂ P B₁ C Ω : Mat n)
    (h₂ : Orthogonal B₂) (hP : Orthogonal P) (h₁ : Orthogonal B₁)
    (hcross : frobInner C (P*Ω*Pᵀ) = 0) :
    frobSq (tangentParam B₂ P B₁ C Ω) = frobSq C + frobSq Ω := by
  rw [tangentParam_factored _ _ _ _ _ hP]
  have hbase : frobSq (B₂*(C+P*Ω*Pᵀ)*(P*B₁)) = frobSq (C+P*Ω*Pᵀ) := by
    unfold frobSq
    rw [frobInner_right_orthogonal _ (hP.mul h₁), frobInner_left_orthogonal _ h₂]
  rw [hbase, frobSq_add, hcross]
  have hΩ : frobSq (P*Ω*Pᵀ) = frobSq Ω := by
    unfold frobSq
    rw [frobInner_right_orthogonal _ hP.transpose, frobInner_left_orthogonal _ hP]
  rw [hΩ]
  ring

/-- Literal first-order expansion with its exact quadratic remainder. -/
theorem product2_increment (B₂ P B₁ η₂ η₁ : Mat n) :
    product2 (B₂+η₂) P (B₁+η₁) =
      product2 B₂ P B₁ + (η₂*P*B₁ + B₂*P*η₁) + η₂*P*η₁ := by
  unfold product2
  noncomm_ring

/-- Generic changed-factor identity used before vector-transport projections. -/
theorem transport_core_identity (B₂ B₁ B₂new B₁new P C Ω : Mat n) :
    B₂newᵀ * tangentParam B₂ P B₁ C Ω * B₁newᵀ * Pᵀ =
      (B₂newᵀ*B₂) * C * P * (B₁*B₁newᵀ) * Pᵀ +
      (B₂newᵀ*B₂) * P * Ω * (B₁*B₁newᵀ) * Pᵀ := by
  unfold tangentParam
  noncomm_ring

theorem transition_left (B S : Mat n) (hB : Orthogonal B) : (B*S)ᵀ*B = Sᵀ := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, hB.1]
  simp

theorem transition_right (B S : Mat n) (hB : Orthogonal B) : B*(S*B)ᵀ = Sᵀ := by
  rw [Matrix.transpose_mul, ← Matrix.mul_assoc, hB.2]
  simp

def blockProjection (block : Fin n → ℕ) (A : Mat n) : Mat n :=
  mask (fun i j => block i = block j) A

/-- Source lemma `block_diag_proj`, left multiplication. -/
theorem blockProjection_mul_left (block : Fin n → ℕ) (A B : Mat n)
    (hA : Supported block A) :
    blockProjection block (A*B) = A * blockProjection block B := by
  ext i j
  by_cases hij : block i = block j
  · simp only [blockProjection,mask,hij,if_pos,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hik : block i = block k
    · have hkj : block k = block j := hik.symm.trans hij
      simp [hkj]
    · rw [hA i k hik]
      simp
  · simp only [blockProjection,mask,hij,if_neg,Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hik : block i = block k
    · have hkj : block k ≠ block j := fun h => hij (hik.trans h)
      simp [hkj]
    · rw [hA i k hik]
      simp

/-- Source lemma `block_diag_proj`, right multiplication. -/
theorem blockProjection_mul_right (block : Fin n → ℕ) (A B : Mat n)
    (hB : Supported block B) :
    blockProjection block (A*B) = blockProjection block A * B := by
  ext i j
  by_cases hij : block i = block j
  · simp only [blockProjection,mask,hij,if_pos,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkj : block k = block j
    · have hik : block i = block k := hij.trans hkj.symm
      simp [hik, hkj.symm]
    · rw [hB k j hkj]
      simp
  · simp only [blockProjection,mask,hij,if_neg,Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hkj : block k = block j
    · have hik : block i ≠ block k := fun h => hij (h.trans hkj)
      simp [hik]
    · rw [hB k j hkj]
      simp

/-- The outer factor normalization used in the paper's m=4 construction. -/
theorem gram_completion (C H G L W : Mat n)
    (hC : C*H*Cᵀ=G) (hL : L*Lᵀ=H) (hW : W*G*Wᵀ=1) :
    Orthogonal (W*C*L) := by
  apply Orthogonal.of_mul_transpose
  calc
    (W*C*L)*(W*C*L)ᵀ = W*(C*(L*Lᵀ)*Cᵀ)*Wᵀ := by
      simp only [Matrix.transpose_mul,Matrix.mul_assoc]
    _ = 1 := by rw [hL,hC,hW]

end GS
