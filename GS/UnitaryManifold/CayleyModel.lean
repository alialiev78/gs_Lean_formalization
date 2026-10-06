module

public import GS.UnitaryManifold.CayleyAlgebra
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! The real supported skew-Hermitian coordinate model and its ambient projection. -/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.UnitaryGeometry
namespace GS.UnitaryManifold
variable {n : ℕ}

abbrev modelSpace (block : Fin n → ℕ) := supportedSkewSpace block
abbrev Model (block : Fin n → ℕ) := ↥(modelSpace block)

theorem model_supported {block : Fin n → ℕ} (x : Model block) :
    CSupported block x.val := x.property.1

theorem model_isSkew {block : Fin n → ℕ} (x : Model block) :
    GS.IsSkewHermitian x.val := x.property.2

theorem admissible_model {block : Fin n → ℕ} (x : Model block) :
    admissible x.val := admissible_of_isSkew x.val x.property.2

theorem model_finiteDimensional (block : Fin n → ℕ) :
    FiniteDimensional ℝ (Model block) := by infer_instance

def modelInclusion (block : Fin n → ℕ) : Model block →L[ℝ] CMat n :=
  (modelSpace block).subtypeL

@[simp] theorem modelInclusion_apply (block : Fin n → ℕ) (x : Model block) :
    modelInclusion block x = x.val := rfl

theorem masked_skew_model (block : Fin n → ℕ) (A : CMat n) :
    cBlockProjection block (GS.skewHermitianPart A) ∈ modelSpace block := by
  refine ⟨?_, cMask_isSkewHermitian (fun i j => eq_comm) (isSkewHermitian_skewHermitianPart A)⟩
  intro i j hij
  simp [cBlockProjection, cMask, hij]

def modelProjectionLinear (block : Fin n → ℕ) : CMat n →ₗ[ℝ] Model block where
  toFun A := ⟨cBlockProjection block (GS.skewHermitianPart A), masked_skew_model block A⟩
  map_add' A B := by
    apply Subtype.ext
    exact (maskedSkewHermitianMap (fun i j => block i = block j)).map_add A B
  map_smul' c A := by
    apply Subtype.ext
    exact (maskedSkewHermitianMap (fun i j => block i = block j)).map_smul c A

def modelProjection (block : Fin n → ℕ) : CMat n →L[ℝ] Model block :=
  (modelProjectionLinear block).toContinuousLinearMap

@[simp] theorem modelProjection_val (block : Fin n → ℕ) (A : CMat n) :
    (modelProjection block A).val = cBlockProjection block (GS.skewHermitianPart A) := rfl

theorem modelProjection_val_of_mem (block : Fin n → ℕ) (A : CMat n)
    (hA : A ∈ modelSpace block) : (modelProjection block A).val = A := by
  rw [modelProjection_val, skewHermitianPart_fixed hA.2]
  exact blockProjection_eq_self block A hA.1

@[simp] theorem modelProjection_inclusion (block : Fin n → ℕ) (x : Model block) :
    modelProjection block x.val = x := by
  apply Subtype.ext
  exact modelProjection_val_of_mem block x.val x.property

theorem modelProjection_smooth (block : Fin n → ℕ) :
    ContDiff ℝ ⊤ (modelProjection block) := (modelProjection block).contDiff

theorem modelInclusion_smooth (block : Fin n → ℕ) :
    ContDiff ℝ ⊤ (modelInclusion block) := (modelInclusion block).contDiff

end GS.UnitaryManifold
