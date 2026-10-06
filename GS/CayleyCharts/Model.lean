module

public import GS.CayleyCharts.Algebra
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The finite-dimensional coordinate model

The model is the actual submodule of supported skew-symmetric matrices.
It carries the inherited finite-dimensional normed vector-space structure
for the entrywise supremum matrix norm, with the original product topology.
This is NOT a proposed definition of the tangent space of the GS orbit.
A continuous linear map into the model extends chart coordinates to ambient
matrices, making smoothness statements meaningful without assuming a manifold.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
namespace GS.CayleyCharts
variable {n : ℕ}

def modelSpace (block : Fin n → ℕ) : Submodule ℝ (Mat n) where
  carrier := {A | Supported block A ∧ GS.IsSkew A}
  zero_mem' := by constructor <;> simp [Supported, GS.IsSkew]
  add_mem' := by
    intro A B hA hB
    refine ⟨hA.1.add hB.1, ?_⟩
    change (A + B)ᵀ = -(A + B)
    rw [Matrix.transpose_add, hA.2, hB.2, neg_add]
  smul_mem' := by
    intro c A hA
    refine ⟨Supported.smul c hA.1, ?_⟩
    change (c • A)ᵀ = -(c • A)
    rw [Matrix.transpose_smul, show Aᵀ = -A from hA.2, smul_neg]

abbrev Model (block : Fin n → ℕ) := ↥(modelSpace block)

theorem model_supported {block : Fin n → ℕ} (x : Model block) :
    Supported block x.val := x.property.1

theorem model_isSkew {block : Fin n → ℕ} (x : Model block) :
    GS.IsSkew x.val := x.property.2

/-- Every point of the linear coordinate model has a valid Cayley denominator. -/
theorem admissible_model {block : Fin n → ℕ} (x : Model block) :
    admissible x.val := admissible_of_isSkew x.val x.property.2

/-- This is a genuine finite-dimensional real vector space, including the
zero-dimensional case (all blocks of size one). -/
theorem model_finiteDimensional (block : Fin n → ℕ) :
    FiniteDimensional ℝ (Model block) := by infer_instance

/-- Continuous linear inclusion into the original matrix space. -/
def modelInclusion (block : Fin n → ℕ) : Model block →L[ℝ] Mat n :=
  (modelSpace block).subtypeL

@[simp] theorem modelInclusion_apply (block : Fin n → ℕ) (x : Model block) :
    modelInclusion block x = x.val := rfl

/-- The original masked skew part lands in the coordinate model. -/
theorem masked_skew_model (block : Fin n → ℕ) (A : Mat n) :
    GS.blockProjection block (GS.skew A) ∈ modelSpace block := by
  constructor
  · intro i j hij
    simp [GS.blockProjection, GS.mask, hij]
  · ext i j
    change (GS.blockProjection block (GS.skew A)) j i =
      -(GS.blockProjection block (GS.skew A)) i j
    by_cases hij : block i = block j
    · simp only [GS.blockProjection, GS.mask, if_pos hij, if_pos hij.symm, GS.skew]
      ring
    · simp [GS.blockProjection, GS.mask, hij, Ne.symm hij]

def modelProjectionLinear (block : Fin n → ℕ) : Mat n →ₗ[ℝ] Model block where
  toFun A := ⟨GS.blockProjection block (GS.skew A), masked_skew_model block A⟩
  map_add' A B := by
    apply Subtype.ext
    ext i j
    by_cases hij : block i = block j
    · simp [GS.blockProjection, GS.mask, hij, GS.skew]
      <;> ring
    · simp [GS.blockProjection, GS.mask, hij]
  map_smul' c A := by
    apply Subtype.ext
    ext i j
    by_cases hij : block i = block j
    · simp [GS.blockProjection, GS.mask, hij, GS.skew]
      <;> ring
    · simp [GS.blockProjection, GS.mask, hij]

/-- Continuity is obtained from finite-dimensional linearity, not from a
matrix norm being submultiplicative. -/
def modelProjection (block : Fin n → ℕ) : Mat n →L[ℝ] Model block :=
  (modelProjectionLinear block).toContinuousLinearMap

@[simp] theorem modelProjection_val (block : Fin n → ℕ) (A : Mat n) :
    (modelProjection block A).val = GS.blockProjection block (GS.skew A) := rfl

theorem modelProjection_val_of_mem (block : Fin n → ℕ) (A : Mat n)
    (hA : A ∈ modelSpace block) : (modelProjection block A).val = A := by
  rw [modelProjection_val, GS.skew_of_isSkew hA.2]
  exact blockProjection_eq_self block A hA.1

@[simp] theorem modelProjection_inclusion (block : Fin n → ℕ) (x : Model block) :
    modelProjection block x.val = x := by
  apply Subtype.ext
  exact modelProjection_val_of_mem block x.val x.property

theorem modelProjection_smooth (block : Fin n → ℕ) :
    ContDiff ℝ ⊤ (modelProjection block) := (modelProjection block).contDiff

theorem modelInclusion_smooth (block : Fin n → ℕ) :
    ContDiff ℝ ⊤ (modelInclusion block) := (modelInclusion block).contDiff

end GS.CayleyCharts
