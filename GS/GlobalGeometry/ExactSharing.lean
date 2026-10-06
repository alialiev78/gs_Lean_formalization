module

public import GS.GlobalGeometry.FrobeniusProjection
public import GS.Continuation.AmbientProjection
public import GS.Extensions.ProjectionSmooth
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact projection with arbitrary within-factor sharing AND overlap

The sharing relation below is the actual equality of local entries in tied
physical blocks. The core subspace is the image of its two concrete Lie-algebra
subspaces under (C,Omega) |-> C + P Omega P^T. Orthogonal projection is
constructed from the complete finite-dimensional subspace, not assumed through
normal equations and not replaced by averaged 1/2 masks.

These are exact generator-image results and smooth formulas in the factors.
No smooth quotient, tangent-bundle identification, efficient pseudoinverse
algorithm, or minimal-norm factor lift is claimed by this module.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation
namespace GS.GlobalGeometry
variable {n : ℕ}

/-- tau assigns a sharing label to each physical block. Labels need not be
consecutive or injective; different factors have independent labellings. -/
def TiedEntries (b : ℕ) (τ : ℕ → ℕ) (A : Mat n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

def sharedSkewSpace (b : ℕ) (τ : ℕ → ℕ) : Submodule ℝ (Mat n) where
  carrier := {A | BlockDiagonal b A ∧ IsSkew A ∧ TiedEntries b τ A}
  zero_mem' := by
    refine ⟨Supported.zero, ?_, ?_⟩
    · simp [IsSkew]
    · intro i j i' j' _ _ _ _ _; rfl
  add_mem' := by
    rintro A B ⟨hsA,hkA,htA⟩ ⟨hsB,hkB,htB⟩
    refine ⟨hsA.add hsB, ?_, ?_⟩
    · change Aᵀ = -A at hkA
      change Bᵀ = -B at hkB
      simp only [IsSkew, Matrix.transpose_add, hkA, hkB, neg_add]
    · intro i j i' j' h h' hτ hi hj
      simp only [Matrix.add_apply, htA i j i' j' h h' hτ hi hj,
        htB i j i' j' h h' hτ hi hj]
  smul_mem' := by
    rintro a A ⟨hs,hk,ht⟩
    refine ⟨Supported.smul a hs, ?_, ?_⟩
    · change Aᵀ = -A at hk
      simp only [IsSkew, Matrix.transpose_smul, hk, smul_neg]
    · intro i j i' j' h h' hτ hi hj
      simp only [Matrix.smul_apply, ht i j i' j' h h' hτ hi hj]

/-- Two actual shared generator spaces, not free parameters for a projector. -/
def sharedCoreMap (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P : Mat n) :
    (sharedSkewSpace (n := n) b₂ τ₂ × sharedSkewSpace (n := n) b₁ τ₁) →ₗ[ℝ] Mat n where
  toFun v := v.1.val + P * v.2.val * Pᵀ
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add,
      Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' a v := by
    change (a • v.1.val) + P * (a • v.2.val) * Pᵀ =
      a • (v.1.val + P * v.2.val * Pᵀ)
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add]

def sharedCore (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P : Mat n) : Submodule ℝ (Mat n) :=
  LinearMap.range (sharedCoreMap b₁ b₂ τ₁ τ₂ P)

theorem mem_sharedCore_iff (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P W : Mat n) :
    W ∈ sharedCore b₁ b₂ τ₁ τ₂ P ↔
      ∃ C ∈ sharedSkewSpace b₂ τ₂, ∃ Ω ∈ sharedSkewSpace b₁ τ₁,
        C + P*Ω*Pᵀ = W := by
  constructor
  · rintro ⟨⟨C,Ω⟩,he⟩
    exact ⟨C,C.property,Ω,Ω.property,he⟩
  · rintro ⟨C,hC,Ω,hΩ,he⟩
    exact ⟨(⟨C,hC⟩,⟨Ω,hΩ⟩),he⟩

/-- Dense exact projection; the fixed core projector can in principle be
precomputed. No arithmetic complexity bound is asserted here. -/
def exactSharedProjection (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R Z : Mat n) : Mat n :=
  lift L (P*R) (frobProjection (sharedCore b₁ b₂ τ₁ τ₂ P) (pull L (P*R) Z))

def SharedDirection (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P L R Y : Mat n) : Prop :=
  ∃ C ∈ sharedSkewSpace b₂ τ₂, ∃ Ω ∈ sharedSkewSpace b₁ τ₁,
    Y = L*C*P*R + L*P*Ω*R

theorem lift_sharedCoreMap (P L R C Ω : Mat n) (hP : Orthogonal P) :
    lift L (P*R) (C+P*Ω*Pᵀ) = L*C*P*R + L*P*Ω*R := by
  simp only [lift, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Pᵀ P R, hP.1]
  simp only [Matrix.one_mul]

theorem sharedDirection_iff_core (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R Y : Mat n) (hP : Orthogonal P) (hL : Orthogonal L) (hR : Orthogonal R) :
    SharedDirection b₁ b₂ τ₁ τ₂ P L R Y ↔
      pull L (P*R) Y ∈ sharedCore b₁ b₂ τ₁ τ₂ P := by
  rw [mem_sharedCore_iff]
  constructor
  · rintro ⟨C,hC,Ω,hΩ,he⟩
    refine ⟨C,hC,Ω,hΩ,?_⟩
    rw [he, ← lift_sharedCoreMap P L R C Ω hP]
    symm
    exact pull_lift L (P*R) _ hL (hP.mul hR)
  · rintro ⟨C,hC,Ω,hΩ,he⟩
    refine ⟨C,hC,Ω,hΩ,?_⟩
    rw [← lift_sharedCoreMap P L R C Ω hP, he]
    exact (lift_pull L (P*R) Y hL (hP.mul hR)).symm

/-- Existence of a genuine solution of the full coupled normal equations. -/
theorem exactSharing_normal_equations (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P Z : Mat n) :
    ∃ C ∈ sharedSkewSpace b₂ τ₂, ∃ Ω ∈ sharedSkewSpace b₁ τ₁,
      C+P*Ω*Pᵀ = frobProjection (sharedCore b₁ b₂ τ₁ τ₂ P) Z ∧
      ∀ D ∈ sharedSkewSpace b₂ τ₂, ∀ E ∈ sharedSkewSpace b₁ τ₁,
        frobInner (Z-(C+P*Ω*Pᵀ)) (D+P*E*Pᵀ) = 0 := by
  obtain ⟨C,hC,Ω,hΩ,he⟩ := (mem_sharedCore_iff b₁ b₂ τ₁ τ₂ P _).mp
    (frobProjection_mem (sharedCore b₁ b₂ τ₁ τ₂ P) Z)
  refine ⟨C,hC,Ω,hΩ,he,?_⟩
  intro D hD E hE
  rw [he]
  exact frobProjection_normal _ Z _
    ((mem_sharedCore_iff b₁ b₂ τ₁ τ₂ P _).mpr ⟨D,hD,E,hE,rfl⟩)

theorem exactSharedProjection_in_direction (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R Z : Mat n) (hP : Orthogonal P) (hL : Orthogonal L) (hR : Orthogonal R) :
    SharedDirection b₁ b₂ τ₁ τ₂ P L R (exactSharedProjection b₁ b₂ τ₁ τ₂ P L R Z) := by
  rw [sharedDirection_iff_core b₁ b₂ τ₁ τ₂ P L R _ hP hL hR]
  unfold exactSharedProjection
  rw [pull_lift L (P*R) _ hL (hP.mul hR)]
  exact frobProjection_mem _ _

theorem pull_frobSq (L R A : Mat n) (hL : Orthogonal L) (hR : Orthogonal R) :
    frobSq (pull L R A) = frobSq A := by
  unfold pull frobSq
  rw [frobInner_right_orthogonal Rᵀ hR.transpose,
    frobInner_left_orthogonal Lᵀ hL.transpose]

theorem exactSharedProjection_pythagorean (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R Z Y : Mat n) (hP : Orthogonal P) (hL : Orthogonal L) (hR : Orthogonal R)
    (hY : SharedDirection b₁ b₂ τ₁ τ₂ P L R Y) :
    frobSq (Z-Y) = frobSq (Z-exactSharedProjection b₁ b₂ τ₁ τ₂ P L R Z) +
      frobSq (exactSharedProjection b₁ b₂ τ₁ τ₂ P L R Z-Y) := by
  have hy := (sharedDirection_iff_core b₁ b₂ τ₁ τ₂ P L R Y hP hL hR).mp hY
  have hh := frobProjection_pythagorean (sharedCore b₁ b₂ τ₁ τ₂ P)
    (pull L (P*R) Z) (pull L (P*R) Y) hy
  have hp : pull L (P*R) (exactSharedProjection b₁ b₂ τ₁ τ₂ P L R Z) =
      frobProjection (sharedCore b₁ b₂ τ₁ τ₂ P) (pull L (P*R) Z) :=
    pull_lift L (P*R) _ hL (hP.mul hR)
  have hsub (A B : Mat n) : pull L (P*R) (A-B) = pull L (P*R) A-pull L (P*R) B := by
    simp only [pull, Matrix.mul_sub, Matrix.sub_mul]
  rw [← hp] at hh
  rw [← hsub, ← hsub, ← hsub] at hh
  simpa only [pull_frobSq L (P*R) _ hL (hP.mul hR)] using hh

theorem exactSharedProjection_minimizes (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R Z Y : Mat n) (hP : Orthogonal P) (hL : Orthogonal L) (hR : Orthogonal R)
    (hY : SharedDirection b₁ b₂ τ₁ τ₂ P L R Y) :
    frobSq (Z-exactSharedProjection b₁ b₂ τ₁ τ₂ P L R Z) ≤ frobSq (Z-Y) := by
  rw [exactSharedProjection_pythagorean b₁ b₂ τ₁ τ₂ P L R Z Y hP hL hR hY]
  exact le_add_of_nonneg_right (frobSq_nonneg _)

theorem exactSharedProjection_smooth (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P : Mat n) :
    ContDiff ℝ ⊤ (fun t : Mat n × Mat n × Mat n =>
      exactSharedProjection b₁ b₂ τ₁ τ₂ P t.1 t.2.1 t.2.2) := by
  unfold exactSharedProjection
  exact contDiff_lift contDiff_fst
    (contDiff_matrix_mul contDiff_const contDiff_snd.fst)
    ((frobProjection_smooth (sharedCore b₁ b₂ τ₁ τ₂ P)).comp
      (contDiff_pull contDiff_fst
        (contDiff_matrix_mul contDiff_const contDiff_snd.fst) contDiff_snd.snd))

end GS.GlobalGeometry
