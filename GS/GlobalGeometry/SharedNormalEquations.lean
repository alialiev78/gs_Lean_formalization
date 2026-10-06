module

public import GS.GlobalGeometry.ExactSharing

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The constrained adjoint and coupled normal equations for actual sharing

The parameter spaces here are the supported skew matrices with the concrete
entry equalities of `TiedEntries`.  The adjoint is projected separately into
these two spaces.  In particular, overlap contributes the conjugated cross
terms to the normal operator; no independent averaging rule is used.

The normal equations below are equivalent to least-squares optimality, and
always have a solution.  Their synthesized matrix is unique even when the
factor generators have a nontrivial kernel.  This file makes no manifold or
local factor-lifting assertion.
-/

noncomputable section
open Matrix GS GS.Extensions
namespace GS.GlobalGeometry
variable {n : ℕ}

/-- A Frobenius multiplication identity without an orthogonality assumption. -/
theorem frobInner_mul_right (A B Z : Mat n) :
    frobInner (A * B) Z = frobInner A (Z * Bᵀ) := by
  rw [← frobInner_transpose (A * B) Z, Matrix.transpose_mul,
    frobInner_mul_left, ← frobInner_transpose A (Z * Bᵀ)]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Coordinates of the adjoint in the actual constrained generator spaces. -/
def sharedCoreAdjoint (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P : Mat n) :
    Mat n →ₗ[ℝ]
      (sharedSkewSpace (n := n) b₂ τ₂ × sharedSkewSpace (n := n) b₁ τ₁) where
  toFun Z :=
    (⟨frobProjection (sharedSkewSpace b₂ τ₂) Z, frobProjection_mem _ _⟩,
     ⟨frobProjection (sharedSkewSpace b₁ τ₁) (Pᵀ * Z * P), frobProjection_mem _ _⟩)
  map_add' A B := by
    apply Prod.ext <;> apply Subtype.ext
    · exact map_add _ _ _
    · simp only [Matrix.mul_add, Matrix.add_mul, map_add]
      rfl
  map_smul' a A := by
    apply Prod.ext <;> apply Subtype.ext
    · exact map_smul _ _ _
    · simp only [Matrix.mul_smul, Matrix.smul_mul, map_smul]
      rfl

/-- Frobenius metric on the two expanded physical generator matrices. -/
def sharedPairInner (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (u v : sharedSkewSpace (n := n) b₂ τ₂ × sharedSkewSpace (n := n) b₁ τ₁) : ℝ :=
  frobInner u.1.val v.1.val + frobInner u.2.val v.2.val

theorem frobInner_projection_of_mem (S : Submodule ℝ (Mat n)) (C Z : Mat n)
    (hC : C ∈ S) : frobInner C (frobProjection S Z) = frobInner C Z := by
  rw [← frobProjection_self_adjoint, frobProjection_of_mem S C hC]

/-- Exact reverse-mode identity for the shared two-factor core derivative. -/
theorem sharedCore_adjoint_identity (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P Z : Mat n)
    (v : sharedSkewSpace (n := n) b₂ τ₂ × sharedSkewSpace (n := n) b₁ τ₁) :
    sharedPairInner b₁ b₂ τ₁ τ₂ v (sharedCoreAdjoint b₁ b₂ τ₁ τ₂ P Z) =
      frobInner (sharedCoreMap b₁ b₂ τ₁ τ₂ P v) Z := by
  change frobInner v.1.val (frobProjection (sharedSkewSpace b₂ τ₂) Z) +
    frobInner v.2.val (frobProjection (sharedSkewSpace b₁ τ₁) (Pᵀ * Z * P)) =
      frobInner (v.1.val + P * v.2.val * Pᵀ) Z
  rw [frobInner_projection_of_mem _ _ _ v.1.property,
    frobInner_projection_of_mem _ _ _ v.2.property, frobInner_add_left,
    frobInner_mul_right, frobInner_mul_left, Matrix.transpose_transpose,
    Matrix.mul_assoc]

/-- The same adjoint gives the reverse derivative of the actual factor
product after transporting the ambient covector to its core coordinates. -/
theorem shared_factor_derivative_adjoint (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R Z : Mat n) (hP : Orthogonal P)
    (v : sharedSkewSpace (n := n) b₂ τ₂ × sharedSkewSpace (n := n) b₁ τ₁) :
    frobInner (L * v.1.val * P * R + L * P * v.2.val * R) Z =
      sharedPairInner b₁ b₂ τ₁ τ₂ v
        (sharedCoreAdjoint b₁ b₂ τ₁ τ₂ P (pull L (P * R) Z)) := by
  rw [sharedCore_adjoint_identity]
  change frobInner (L * v.1.val * P * R + L * P * v.2.val * R) Z =
    frobInner (v.1.val + P * v.2.val * Pᵀ) (pull L (P * R) Z)
  rw [← lift_sharedCoreMap P L R v.1.val v.2.val hP]
  change frobInner (L * (v.1.val + P * v.2.val * Pᵀ) * (P * R)) Z =
    frobInner (v.1.val + P * v.2.val * Pᵀ) (Lᵀ * Z * (P * R)ᵀ)
  rw [frobInner_mul_right, frobInner_mul_left]
  simp only [Matrix.mul_assoc]

theorem sharedPairInner_self_eq_zero_iff (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (v : sharedSkewSpace (n := n) b₂ τ₂ × sharedSkewSpace (n := n) b₁ τ₁) :
    sharedPairInner b₁ b₂ τ₁ τ₂ v v = 0 ↔ v = 0 := by
  constructor
  · intro h
    change frobSq v.1.val + frobSq v.2.val = 0 at h
    have h₁ : frobSq v.1.val = 0 := by
      linarith [frobSq_nonneg v.1.val, frobSq_nonneg v.2.val]
    have h₂ : frobSq v.2.val = 0 := by
      linarith [frobSq_nonneg v.1.val, frobSq_nonneg v.2.val]
    apply Prod.ext <;> apply Subtype.ext
    · exact (frobSq_eq_zero_iff _).mp h₁
    · exact (frobSq_eq_zero_iff _).mp h₂
  · rintro rfl
    simp [sharedPairInner]

/-- The full coupled normal operator, including both cross-factor terms. -/
def sharedNormalOperator (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P : Mat n) :=
  (sharedCoreAdjoint b₁ b₂ τ₁ τ₂ P).comp (sharedCoreMap b₁ b₂ τ₁ τ₂ P)

theorem sharedNormalOperator_energy (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P : Mat n)
    (v : sharedSkewSpace (n := n) b₂ τ₂ × sharedSkewSpace (n := n) b₁ τ₁) :
    sharedPairInner b₁ b₂ τ₁ τ₂ v (sharedNormalOperator b₁ b₂ τ₁ τ₂ P v) =
      frobSq (sharedCoreMap b₁ b₂ τ₁ τ₂ P v) :=
  sharedCore_adjoint_identity b₁ b₂ τ₁ τ₂ P _ v

/-- Under the orthogonal carrier hypothesis the normal operator contains
the two expected overlap cross terms, projected onto the actual tied spaces. -/
theorem shared_normal_equation_iff_coupled (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P Z : Mat n) (hP : Orthogonal P)
    (v : sharedSkewSpace (n := n) b₂ τ₂ × sharedSkewSpace (n := n) b₁ τ₁) :
    sharedNormalOperator b₁ b₂ τ₁ τ₂ P v = sharedCoreAdjoint b₁ b₂ τ₁ τ₂ P Z ↔
      frobProjection (sharedSkewSpace b₂ τ₂) (v.1.val + P * v.2.val * Pᵀ) =
        frobProjection (sharedSkewSpace b₂ τ₂) Z ∧
      frobProjection (sharedSkewSpace b₁ τ₁) (Pᵀ * v.1.val * P + v.2.val) =
        frobProjection (sharedSkewSpace b₁ τ₁) (Pᵀ * Z * P) := by
  have he : Pᵀ * (v.1.val + P * v.2.val * Pᵀ) * P =
      Pᵀ * v.1.val * P + v.2.val := by
    rw [Matrix.mul_add, Matrix.add_mul]
    congr 1
    calc
      Pᵀ * (P * v.2.val * Pᵀ) * P = (Pᵀ * P) * v.2.val * (Pᵀ * P) := by
        simp only [Matrix.mul_assoc]
      _ = v.2.val := by rw [hP.1]; simp
  constructor
  · intro h
    have h₁ := congrArg (fun w : sharedSkewSpace (n := n) b₂ τ₂ ×
        sharedSkewSpace (n := n) b₁ τ₁ => w.1.val) h
    have h₂ := congrArg (fun w : sharedSkewSpace (n := n) b₂ τ₂ ×
        sharedSkewSpace (n := n) b₁ τ₁ => w.2.val) h
    change frobProjection (sharedSkewSpace b₁ τ₁)
      (Pᵀ * (v.1.val + P * v.2.val * Pᵀ) * P) = _ at h₂
    rw [he] at h₂
    exact ⟨h₁, h₂⟩
  · intro h
    apply Prod.ext <;> apply Subtype.ext
    · exact h.1
    · change frobProjection (sharedSkewSpace b₁ τ₁)
        (Pᵀ * (v.1.val + P * v.2.val * Pᵀ) * P) = _
      rw [he]
      exact h.2

/-- The normal operator has exactly the true synthesis kernel. -/
theorem sharedNormalOperator_kernel_iff (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P : Mat n)
    (v : sharedSkewSpace (n := n) b₂ τ₂ × sharedSkewSpace (n := n) b₁ τ₁) :
    sharedNormalOperator b₁ b₂ τ₁ τ₂ P v = 0 ↔
      sharedCoreMap b₁ b₂ τ₁ τ₂ P v = 0 := by
  constructor
  · intro h
    apply (frobSq_eq_zero_iff _).mp
    rw [← sharedNormalOperator_energy, h]
    simp [sharedPairInner]
  · intro h
    simp [sharedNormalOperator, LinearMap.comp_apply, h]

/-- Vanishing of the adjoint is equivalent to orthogonality to every actual
shared direction. -/
theorem sharedCoreAdjoint_eq_zero_iff (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P Z : Mat n) :
    sharedCoreAdjoint b₁ b₂ τ₁ τ₂ P Z = 0 ↔
      ∀ v, frobInner Z (sharedCoreMap b₁ b₂ τ₁ τ₂ P v) = 0 := by
  constructor
  · intro h v
    rw [frobInner_comm, ← sharedCore_adjoint_identity, h]
    simp [sharedPairInner]
  · intro h
    apply (sharedPairInner_self_eq_zero_iff b₁ b₂ τ₁ τ₂ _).mp
    rw [sharedCore_adjoint_identity, frobInner_comm]
    exact h _

/-- Solving the coupled adjoint equation is exactly computing the already
constructed image projection, with no rank or normal-solvability premise. -/
theorem shared_normal_equation_iff_projection (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P Z : Mat n)
    (v : sharedSkewSpace (n := n) b₂ τ₂ × sharedSkewSpace (n := n) b₁ τ₁) :
    sharedNormalOperator b₁ b₂ τ₁ τ₂ P v = sharedCoreAdjoint b₁ b₂ τ₁ τ₂ P Z ↔
      sharedCoreMap b₁ b₂ τ₁ τ₂ P v =
        frobProjection (sharedCore b₁ b₂ τ₁ τ₂ P) Z := by
  have he : sharedNormalOperator b₁ b₂ τ₁ τ₂ P v =
      sharedCoreAdjoint b₁ b₂ τ₁ τ₂ P Z ↔
      sharedCoreAdjoint b₁ b₂ τ₁ τ₂ P
        (Z - sharedCoreMap b₁ b₂ τ₁ τ₂ P v) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact eq_comm
  rw [he, sharedCoreAdjoint_eq_zero_iff]
  constructor
  · intro h
    symm
    apply frobProjection_unique_normal (sharedCore b₁ b₂ τ₁ τ₂ P) Z
      (sharedCoreMap b₁ b₂ τ₁ τ₂ P v) ⟨v, rfl⟩
    rintro W ⟨w, rfl⟩
    exact h w
  · intro h w
    rw [h]
    exact frobProjection_normal _ _ _ ⟨w, rfl⟩

/-- Existence is constructive through finite-dimensional orthogonal projection. -/
theorem exists_shared_normal_solution (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P Z : Mat n) :
    ∃ v, sharedNormalOperator b₁ b₂ τ₁ τ₂ P v =
      sharedCoreAdjoint b₁ b₂ τ₁ τ₂ P Z := by
  obtain ⟨v, hv⟩ := frobProjection_mem (sharedCore b₁ b₂ τ₁ τ₂ P) Z
  exact ⟨v, (shared_normal_equation_iff_projection b₁ b₂ τ₁ τ₂ P Z v).mpr hv⟩

/-- Full least-squares equivalence, not only sufficiency of normal equations. -/
theorem shared_normal_equation_iff_minimizes (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P Z : Mat n)
    (v : sharedSkewSpace (n := n) b₂ τ₂ × sharedSkewSpace (n := n) b₁ τ₁) :
    sharedNormalOperator b₁ b₂ τ₁ τ₂ P v = sharedCoreAdjoint b₁ b₂ τ₁ τ₂ P Z ↔
      ∀ w, frobSq (Z - sharedCoreMap b₁ b₂ τ₁ τ₂ P v) ≤
        frobSq (Z - sharedCoreMap b₁ b₂ τ₁ τ₂ P w) := by
  rw [shared_normal_equation_iff_projection]
  constructor
  · intro h w
    rw [h]
    exact frobProjection_minimizes _ _ _ ⟨w, rfl⟩
  · intro h
    obtain ⟨w, hw⟩ := frobProjection_mem (sharedCore b₁ b₂ τ₁ τ₂ P) Z
    have hmin := h w
    rw [hw] at hmin
    have hp := frobProjection_pythagorean (sharedCore b₁ b₂ τ₁ τ₂ P) Z
      (sharedCoreMap b₁ b₂ τ₁ τ₂ P v) ⟨v, rfl⟩
    have hz : frobSq (frobProjection (sharedCore b₁ b₂ τ₁ τ₂ P) Z -
        sharedCoreMap b₁ b₂ τ₁ τ₂ P v) = 0 := by
      linarith [frobSq_nonneg (frobProjection (sharedCore b₁ b₂ τ₁ τ₂ P) Z -
        sharedCoreMap b₁ b₂ τ₁ τ₂ P v)]
    exact (sub_eq_zero.mp ((frobSq_eq_zero_iff _).mp hz)).symm

end GS.GlobalGeometry
