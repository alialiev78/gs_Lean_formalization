module

public import GS.Unitary.Support
public import Mathlib.Tactic.NoncommRing

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Real-linear generator algebra for complex unitary factors

All the generator spaces and maps in this module are over `ℝ`: the
skew-Hermitian condition is not preserved by arbitrary complex scaling.
The tangent spaces below are concrete generator images. These algebraic
statements do not assert an embedded manifold or quotient construction.
-/

noncomputable section
open Matrix
open scoped BigOperators

namespace GS.UnitaryGeometry
variable {n : ℕ}

theorem skewHermitian_zero : IsSkewHermitian (0 : CMat n) := by
  simp [IsSkewHermitian]

theorem skewHermitian_add {A B : CMat n}
    (hA : IsSkewHermitian A) (hB : IsSkewHermitian B) :
    IsSkewHermitian (A + B) := by
  change Aᴴ = -A at hA
  change Bᴴ = -B at hB
  simp only [IsSkewHermitian, Matrix.conjTranspose_add, hA, hB, neg_add]

theorem skewHermitian_real_smul (a : ℝ) {A : CMat n}
    (hA : IsSkewHermitian A) : IsSkewHermitian (a • A) := by
  change Aᴴ = -A at hA
  simp only [IsSkewHermitian, Matrix.conjTranspose_smul, star_trivial, hA, smul_neg]

/-- The Lie algebra of unitary matrices is a real vector space. -/
def skewHermitianSpace : Submodule ℝ (CMat n) where
  carrier := {A | IsSkewHermitian A}
  zero_mem' := skewHermitian_zero
  add_mem' := skewHermitian_add
  smul_mem' := skewHermitian_real_smul

@[simp] theorem mem_skewHermitianSpace (A : CMat n) :
    A ∈ skewHermitianSpace ↔ IsSkewHermitian A := Iff.rfl

/-- Block-supported skew-Hermitian generators, with real scalars. -/
def supportedSkewSpace (block : Fin n → ℕ) : Submodule ℝ (CMat n) where
  carrier := {A | CSupported block A ∧ IsSkewHermitian A}
  zero_mem' := ⟨CSupported.zero, skewHermitian_zero⟩
  add_mem' := by
    rintro A B ⟨hsA,hkA⟩ ⟨hsB,hkB⟩
    exact ⟨hsA.add hsB, skewHermitian_add hkA hkB⟩
  smul_mem' := by
    rintro a A ⟨hsA,hkA⟩
    exact ⟨CSupported.real_smul a hsA, skewHermitian_real_smul a hkA⟩

@[simp] theorem mem_supportedSkewSpace (block : Fin n → ℕ) (A : CMat n) :
    A ∈ supportedSkewSpace block ↔ CSupported block A ∧ IsSkewHermitian A := Iff.rfl

theorem conjugate_skewHermitian (B C : CMat n) (hC : IsSkewHermitian C) :
    IsSkewHermitian (B*C*Bᴴ) := by
  unfold IsSkewHermitian at *
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hC]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem conjugate_supported (block : Fin n → ℕ) (B C : CMat n)
    (hB : CSupported block B) (hC : CSupported block C) :
    CSupported block (B*C*Bᴴ) := (hB.mul hC).mul hB.conjTranspose

theorem conjugate_mem_supportedSkewSpace (block : Fin n → ℕ) (B C : CMat n)
    (hB : CSupported block B) (hC : C ∈ supportedSkewSpace block) :
    B*C*Bᴴ ∈ supportedSkewSpace block :=
  ⟨conjugate_supported block B C hB hC.1, conjugate_skewHermitian B C hC.2⟩

/-- Closure under the commutator is the Lie-algebra part of block support. -/
theorem commutator_mem_supportedSkewSpace (block : Fin n → ℕ) (A B : CMat n)
    (hA : A ∈ supportedSkewSpace block) (hB : B ∈ supportedSkewSpace block) :
    A*B - B*A ∈ supportedSkewSpace block := by
  refine ⟨(hA.1.mul hB.1).sub (hB.1.mul hA.1), ?_⟩
  have hkA : Aᴴ = -A := hA.2
  have hkB : Bᴴ = -B := hB.2
  simp only [IsSkewHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    hkA, hkB, neg_mul_neg, neg_sub]

def product2 (B₂ P B₁ : CMat n) : CMat n := B₂ * P * B₁

def tangentParam (B₂ P B₁ C Ω : CMat n) : CMat n :=
  B₂ * C * P * B₁ + B₂ * P * Ω * B₁

theorem left_right_generator (B C : CMat n) (hB : Unitary B) :
    (B*C*Bᴴ)*B = B*C := by
  calc
    (B*C*Bᴴ)*B = B*C*(Bᴴ*B) := by simp only [Matrix.mul_assoc]
    _ = B*C := by rw [hB.1]; simp

theorem tangentParam_factored (B₂ P B₁ C Ω : CMat n) (hP : Unitary P) :
    tangentParam B₂ P B₁ C Ω = B₂ * (C + P*Ω*Pᴴ) * (P*B₁) := by
  symm
  calc
    B₂ * (C + P*Ω*Pᴴ) * (P*B₁) =
        B₂*C*P*B₁ + B₂*P*Ω*(Pᴴ*P)*B₁ := by noncomm_ring
    _ = tangentParam B₂ P B₁ C Ω := by
      rw [hP.1]
      simp [tangentParam]

/-- Exact quadratic Taylor remainder for the two-factor multiplication map. -/
theorem product2_increment (B₂ P B₁ η₂ η₁ : CMat n) :
    product2 (B₂+η₂) P (B₁+η₁) =
      product2 B₂ P B₁ + (η₂*P*B₁ + B₂*P*η₁) + η₂*P*η₁ := by
  unfold product2
  noncomm_ring

theorem transport_core_identity (B₂ B₁ B₂new B₁new P C Ω : CMat n) :
    B₂newᴴ * tangentParam B₂ P B₁ C Ω * B₁newᴴ * Pᴴ =
      (B₂newᴴ*B₂) * C * P * (B₁*B₁newᴴ) * Pᴴ +
      (B₂newᴴ*B₂) * P * Ω * (B₁*B₁newᴴ) * Pᴴ := by
  unfold tangentParam
  noncomm_ring

theorem transition_left (B S : CMat n) (hB : Unitary B) : (B*S)ᴴ*B = Sᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, hB.1]
  simp

theorem transition_right (B S : CMat n) (hB : Unitary B) : B*(S*B)ᴴ = Sᴴ := by
  rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, hB.2]
  simp

/-- The core generator map is real-linear even when the factors are complex. -/
def tangentCoreMap (block₁ block₂ : Fin n → ℕ) (P : CMat n) :
    (supportedSkewSpace block₂ × supportedSkewSpace block₁) →ₗ[ℝ] CMat n where
  toFun v := v.1.val + P*v.2.val*Pᴴ
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add,
      Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' a v := by
    change (a • v.1.val) + P * (a • v.2.val) * Pᴴ =
      a • (v.1.val + P * v.2.val * Pᴴ)
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add]

/-- The sum of both supported generator images; overlap is allowed. -/
def tangentCoreSpace (block₁ block₂ : Fin n → ℕ) (P : CMat n) :
    Submodule ℝ (CMat n) := LinearMap.range (tangentCoreMap block₁ block₂ P)

theorem mem_tangentCoreSpace_iff (block₁ block₂ : Fin n → ℕ) (P W : CMat n) :
    W ∈ tangentCoreSpace block₁ block₂ P ↔
      ∃ C ∈ supportedSkewSpace block₂, ∃ Ω ∈ supportedSkewSpace block₁,
        C + P*Ω*Pᴴ = W := by
  constructor
  · rintro ⟨⟨C,Ω⟩,he⟩
    exact ⟨C,C.property,Ω,Ω.property,he⟩
  · rintro ⟨C,hC,Ω,hΩ,he⟩
    exact ⟨(⟨C,hC⟩,⟨Ω,hΩ⟩),he⟩

theorem tangentCoreSpace_skewHermitian (block₁ block₂ : Fin n → ℕ) (P W : CMat n)
    (hW : W ∈ tangentCoreSpace block₁ block₂ P) : IsSkewHermitian W := by
  rcases (mem_tangentCoreSpace_iff block₁ block₂ P W).mp hW with ⟨C,hC,Ω,hΩ,rfl⟩
  exact skewHermitian_add hC.2 (conjugate_skewHermitian P Ω hΩ.2)

/-- Concrete differential of the factor parametrization on real generator spaces. -/
def tangentParamMap (block₁ block₂ : Fin n → ℕ) (B₂ P B₁ : CMat n) :
    (supportedSkewSpace block₂ × supportedSkewSpace block₁) →ₗ[ℝ] CMat n where
  toFun v := tangentParam B₂ P B₁ v.1.val v.2.val
  map_add' v w := by
    simp only [tangentParam, Prod.fst_add, Prod.snd_add, Submodule.coe_add,
      Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' a v := by
    change tangentParam B₂ P B₁ (a • v.1.val) (a • v.2.val) =
      a • tangentParam B₂ P B₁ v.1.val v.2.val
    simp only [tangentParam, Matrix.mul_smul, Matrix.smul_mul, smul_add]

def tangentParamSpace (block₁ block₂ : Fin n → ℕ) (B₂ P B₁ : CMat n) :
    Submodule ℝ (CMat n) := LinearMap.range (tangentParamMap block₁ block₂ B₂ P B₁)

theorem mem_tangentParamSpace_iff (block₁ block₂ : Fin n → ℕ) (B₂ P B₁ Y : CMat n) :
    Y ∈ tangentParamSpace block₁ block₂ B₂ P B₁ ↔
      ∃ C ∈ supportedSkewSpace block₂, ∃ Ω ∈ supportedSkewSpace block₁,
        tangentParam B₂ P B₁ C Ω = Y := by
  constructor
  · rintro ⟨⟨C,Ω⟩,he⟩
    exact ⟨C,C.property,Ω,Ω.property,he⟩
  · rintro ⟨C,hC,Ω,hΩ,he⟩
    exact ⟨(⟨C,hC⟩,⟨Ω,hΩ⟩),he⟩

theorem tangentParamSpace_eq_core_image (block₁ block₂ : Fin n → ℕ)
    (B₂ P B₁ Y : CMat n) (hP : Unitary P) :
    Y ∈ tangentParamSpace block₁ block₂ B₂ P B₁ ↔
      ∃ W ∈ tangentCoreSpace block₁ block₂ P, B₂*W*(P*B₁) = Y := by
  rw [mem_tangentParamSpace_iff]
  constructor
  · rintro ⟨C,hC,Ω,hΩ,rfl⟩
    refine ⟨C+P*Ω*Pᴴ, ?_, (tangentParam_factored B₂ P B₁ C Ω hP).symm⟩
    exact (mem_tangentCoreSpace_iff block₁ block₂ P _).mpr ⟨C,hC,Ω,hΩ,rfl⟩
  · rintro ⟨W,hW,rfl⟩
    rcases (mem_tangentCoreSpace_iff block₁ block₂ P W).mp hW with ⟨C,hC,Ω,hΩ,rfl⟩
    exact ⟨C,hC,Ω,hΩ,tangentParam_factored B₂ P B₁ C Ω hP⟩

/-- A skew core produces the linearized unitary Gram equation. -/
theorem linearized_unitary_gram (L R W : CMat n) (hL : Unitary L)
    (hW : IsSkewHermitian W) :
    (L*R)ᴴ*(L*W*R) + (L*W*R)ᴴ*(L*R) = 0 := by
  have hW' : Wᴴ = -W := hW
  calc
    (L*R)ᴴ*(L*W*R) + (L*W*R)ᴴ*(L*R) =
        Rᴴ*(Lᴴ*L)*W*R + Rᴴ*Wᴴ*(Lᴴ*L)*R := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hL.1, hW']; simp

theorem tangentParamSpace_linearized_unitary (block₁ block₂ : Fin n → ℕ)
    (B₂ P B₁ Y : CMat n) (h₂ : Unitary B₂) (hP : Unitary P)
    (hY : Y ∈ tangentParamSpace block₁ block₂ B₂ P B₁) :
    (product2 B₂ P B₁)ᴴ*Y + Yᴴ*(product2 B₂ P B₁) = 0 := by
  rcases (tangentParamSpace_eq_core_image block₁ block₂ B₂ P B₁ Y hP).mp hY with
    ⟨W,hW,rfl⟩
  simpa only [product2, Matrix.mul_assoc] using
    linearized_unitary_gram B₂ (P*B₁) W h₂
      (tangentCoreSpace_skewHermitian block₁ block₂ P W hW)

/-- Complex Gram normalization gives both unitary Gram identities. -/
theorem gram_completion (C H G L W : CMat n)
    (hC : C*H*Cᴴ=G) (hL : L*Lᴴ=H) (hW : W*G*Wᴴ=1) :
    Unitary (W*C*L) := by
  have h : (W*C*L)*(W*C*L)ᴴ = 1 := by
    calc
      (W*C*L)*(W*C*L)ᴴ = W*(C*(L*Lᴴ)*Cᴴ)*Wᴴ := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = 1 := by rw [hL,hC,hW]
  exact ⟨mul_eq_one_comm.mp h, h⟩

end GS.UnitaryGeometry
