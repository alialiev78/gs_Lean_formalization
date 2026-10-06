module

public import GS.SharedGeometry.MinimumNormLift

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Equivariance of the minimum-physical-norm shared lift

Both spatial generators transform by orthogonal conjugation. This preserves
the actual tied generator spaces, their physical Frobenius pairing, and the
synthesis kernel. Uniqueness of the horizontal lift then proves equivariance
without choosing a section of the orbit map.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.GlobalGeometry
namespace GS.SharedGeometry
variable {n : ℕ} {right left : Pattern n}

/-- Conjugation acts separately on the two full shared generator matrices. -/
def generatorAction (g : Factors right left) :
    PairGenerator right left →ₗ[ℝ] PairGenerator right left where
  toFun v :=
    (⟨Factor.matrix g.1 * v.1.val * (Factor.matrix g.1)ᵀ,
      sharedSkew_conjugate left.positive left.divides (Factor.matrix_shared g.1) v.1.property⟩,
     ⟨Factor.matrix g.2 * v.2.val * (Factor.matrix g.2)ᵀ,
      sharedSkew_conjugate right.positive right.divides (Factor.matrix_shared g.2) v.2.property⟩)
  map_add' v w := by
    apply Prod.ext <;> apply Subtype.ext <;>
      simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' a v := by
    apply Prod.ext <;> apply Subtype.ext
    · change Factor.matrix g.1 * (a • v.1.val) * (Factor.matrix g.1)ᵀ =
        a • (Factor.matrix g.1 * v.1.val * (Factor.matrix g.1)ᵀ)
      rw [Matrix.mul_smul, Matrix.smul_mul]
    · change Factor.matrix g.2 * (a • v.2.val) * (Factor.matrix g.2)ᵀ =
        a • (Factor.matrix g.2 * v.2.val * (Factor.matrix g.2)ᵀ)
      rw [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem generatorAction_left (g : Factors right left) (v : PairGenerator right left) :
    (generatorAction g v).1.val = Factor.matrix g.1 * v.1.val * (Factor.matrix g.1)ᵀ := rfl

@[simp] theorem generatorAction_right (g : Factors right left) (v : PairGenerator right left) :
    (generatorAction g v).2.val = Factor.matrix g.2 * v.2.val * (Factor.matrix g.2)ᵀ := rfl

private theorem conjugate_cancel (A C : Mat n) (hA : Orthogonal A) :
    Aᵀ * (A * C * Aᵀ) * A = C := by
  calc
    _ = (Aᵀ * A) * C * (Aᵀ * A) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hA.1]; simp

@[simp] theorem generatorAction_inverse (g : Factors right left) (v : PairGenerator right left) :
    generatorAction g⁻¹ (generatorAction g v) = v := by
  apply Prod.ext <;> apply Subtype.ext
  · change (Factor.matrix g.1)ᵀ * (Factor.matrix g.1 * v.1.val * (Factor.matrix g.1)ᵀ) *
      ((Factor.matrix g.1)ᵀ)ᵀ = v.1.val
    rw [Matrix.transpose_transpose]
    exact conjugate_cancel _ _ (Factor.matrix_orthogonal g.1)
  · change (Factor.matrix g.2)ᵀ * (Factor.matrix g.2 * v.2.val * (Factor.matrix g.2)ᵀ) *
      ((Factor.matrix g.2)ᵀ)ᵀ = v.2.val
    rw [Matrix.transpose_transpose]
    exact conjugate_cancel _ _ (Factor.matrix_orthogonal g.2)

@[simp] theorem generatorAction_inverse_right (g : Factors right left) (v : PairGenerator right left) :
    generatorAction g (generatorAction g⁻¹ v) = v := by
  simpa only [inv_inv] using generatorAction_inverse g⁻¹ v

/-- Intertwining of the actual point-based synthesis maps. -/
theorem pointMap_generatorAction (g : Factors right left) (X : Mat n)
    (v : PairGenerator right left) :
    pointMap right left (g • X) (generatorAction g v) =
      g • pointMap right left X v := by
  let L := Factor.matrix g.1
  let R := Factor.matrix g.2
  have hl : (L * v.1.val * Lᵀ) * (L * X * Rᵀ) = L * (v.1.val * X) * Rᵀ := by
    calc
      _ = L * v.1.val * (Lᵀ * L) * X * Rᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [(Factor.matrix_orthogonal g.1).1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hr : (L * X * Rᵀ) * (R * v.2.val * Rᵀ) = L * (X * v.2.val) * Rᵀ := by
    calc
      _ = L * X * (Rᵀ * R) * v.2.val * Rᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [(Factor.matrix_orthogonal g.2).1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  change (L * v.1.val * Lᵀ) * (L * X * Rᵀ) +
    (L * X * Rᵀ) * (R * v.2.val * Rᵀ) = L * (v.1.val * X + X * v.2.val) * Rᵀ
  rw [hl, hr, Matrix.mul_add, Matrix.add_mul]

theorem generatorInner_action (g : Factors right left) (v w : PairGenerator right left) :
    generatorInner (generatorAction g v) (generatorAction g w) = generatorInner v w := by
  unfold generatorInner
  simp only [generatorAction_left, generatorAction_right]
  rw [frobInner_right_orthogonal _ (Factor.matrix_orthogonal g.1).transpose,
    frobInner_right_orthogonal _ (Factor.matrix_orthogonal g.2).transpose,
    frobInner_left_orthogonal _ (Factor.matrix_orthogonal g.1),
    frobInner_left_orthogonal _ (Factor.matrix_orthogonal g.2)]

theorem generatorEnergy_action (g : Factors right left) (v : PairGenerator right left) :
    generatorEnergy (generatorAction g v) = generatorEnergy v := generatorInner_action g v v

theorem generatorAction_horizontal (g : Factors right left) (X : Mat n)
    (v : PairGenerator right left) (hv : IsHorizontal X v) :
    IsHorizontal (g • X) (generatorAction g v) := by
  intro k hk
  have hb : pointMap right left X (generatorAction g⁻¹ k) = 0 := by
    have he := pointMap_generatorAction g⁻¹ (g • X) k
    rw [inv_smul_smul, hk] at he
    simpa only [action_apply, Matrix.mul_zero, Matrix.zero_mul] using he
  calc
    generatorInner (generatorAction g v) k =
        generatorInner (generatorAction g v) (generatorAction g (generatorAction g⁻¹ k)) := by
          rw [generatorAction_inverse_right]
    _ = generatorInner v (generatorAction g⁻¹ k) := generatorInner_action g v _
    _ = 0 := hv _ hb

/-- The selected lift is independent of all choices made in its existence proof. -/
theorem minimumNormLift_equivariant (g : Factors right left) (X Z : Mat n) :
    minimumNormLift right left (g • X) (g • Z) =
      generatorAction g (minimumNormLift right left X Z) := by
  symm
  apply minimumNormLift_unique
  · rw [pointMap_generatorAction, minimumNormLift_synthesis, pointProjection_equivariant]
  · exact generatorAction_horizontal g X _ (minimumNormLift_horizontal X Z)

/-- Every representative gives the same lift at the same matrix point. -/
theorem minimumNormLift_factor_formula (g : Factors right left) (P Z : Mat n) :
    minimumNormLift right left (g • P) Z =
      generatorAction g (minimumNormLift right left P (g⁻¹ • Z)) := by
  simpa only [smul_inv_smul] using minimumNormLift_equivariant g P (g⁻¹ • Z)

end GS.SharedGeometry
