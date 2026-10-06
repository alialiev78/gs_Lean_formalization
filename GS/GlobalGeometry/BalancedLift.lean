module

public import GS.Continuation.AmbientProjection
public import GS.CayleyCharts.Model
public import GS.Extensions.MatrixCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A canonical, point-only split of a GS tangent direction, including overlap

The original checked pointProjection is unchanged. The left and right orbit
projectors commute on the actual GS family. Subtracting half of their common
part produces supported skew generators directly from (X,Z), without choosing
factors. No no-overlap or sharing hypothesis is hidden here: arbitrary overlap
is allowed, but independent physical blocks are assumed.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local instance] Classical.propDecidable
open Matrix GS GS.Extensions GS.Continuation GS.CayleyCharts
open scoped Topology
namespace GS.GlobalGeometry
variable {n : ℕ}

@[simp] theorem blockSkew_add (b : Fin n → ℕ) (A B : Mat n) :
    blockSkew b (A+B) = blockSkew b A + blockSkew b B := by
  ext i j
  by_cases h : b i = b j <;> simp [blockSkew, maskedSkew, mask, skew, h] <;> ring

@[simp] theorem blockSkew_smul (b : Fin n → ℕ) (a : ℝ) (A : Mat n) :
    blockSkew b (a • A) = a • blockSkew b A := by
  ext i j
  by_cases h : b i = b j <;> simp [blockSkew, maskedSkew, mask, skew, h] <;> ring

@[simp] theorem blockSkew_zero (b : Fin n → ℕ) : blockSkew b (0 : Mat n) = 0 := by
  ext i j
  simp [blockSkew, maskedSkew, mask, skew]

theorem blockSkew_sub (b : Fin n → ℕ) (A B : Mat n) :
    blockSkew b (A-B) = blockSkew b A - blockSkew b B := by
  ext i j
  by_cases h : b i = b j <;> simp [blockSkew, maskedSkew, mask, skew, h] <;> ring

theorem blockSkew_supported (b : Fin n → ℕ) (A : Mat n) :
    Supported b (blockSkew b A) := (masked_skew_model b A).1

theorem blockSkew_skew (b : Fin n → ℕ) (A : Mat n) :
    IsSkew (blockSkew b A) := (masked_skew_model b A).2

theorem maskedSkew_commutes (p q : Fin n → Fin n → Prop)
    (hp : MaskSymmetric p) (hq : MaskSymmetric q) (A : Mat n) :
    maskedSkew p (maskedSkew q A) = maskedSkew q (maskedSkew p A) := by
  rw [maskedSkew_composition p q hq, maskedSkew_composition q p hp]
  ext i j
  simp only [maskedSkew, mask, and_comm]

/-- The common part of the two actual orbit projectors. This is false for
arbitrary unrelated subspace projectors; here the factor-coordinate masks prove it. -/
theorem pointProjectors_commute (b₁ b₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (L R Z : Mat n)
    (hsL : Supported b₂ L) (hsR : Supported b₁ R)
    (hL : Orthogonal L) (hR : Orthogonal R) :
    let X := product2 L (permMatrix σ) R
    leftPointProjection b₂ X (rightPointProjection b₁ X Z) =
      rightPointProjection b₁ X (leftPointProjection b₂ X Z) := by
  classical
  dsimp only
  let P := permMatrix σ
  let W := pull L (P*R) Z
  let p := fun i j : Fin n => b₂ i = b₂ j
  let q := fun i j : Fin n => b₁ (σ.symm i) = b₁ (σ.symm j)
  have hl (A : Mat n) :
      leftPointProjection b₂ (product2 L P R) (lift L (P*R) A) =
        lift L (P*R) (maskedSkew p A) := by
    simpa only [product2, Matrix.mul_assoc, blockSkew, p] using
      leftPointProjection_lift b₂ L (P*R) A hsL hL ((perm_orthogonal σ).mul hR)
  have hr (A : Mat n) :
      rightPointProjection b₁ (product2 L P R) (lift L (P*R) A) =
        lift L (P*R) (maskedSkew q A) :=
    rightPointProjection_lift b₁ σ L R A hsR hL hR
  have hz : Z = lift L (P*R) W :=
    (lift_pull L (P*R) Z hL ((perm_orthogonal σ).mul hR)).symm
  change leftPointProjection b₂ (product2 L P R)
      (rightPointProjection b₁ (product2 L P R) Z) = _
  rw [hz, hr, hl, hl, hr]
  apply congrArg (lift L (P*R))
  ext i j
  by_cases hp : b₂ i = b₂ j <;>
    by_cases hq : b₁ (σ.symm i) = b₁ (σ.symm j) <;>
    simp [maskedSkew, mask, skew, p, q, hp, hq, eq_comm] <;> ring

/-- Left ambient generator, in the Lie algebra of the LEFT physical blocks. -/
def balancedLeft (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) : Mat n :=
  blockSkew b₂ ((Z - (1/2 : ℝ) • rightPointProjection b₁ X Z) * Xᵀ)

/-- Right ambient generator, in the Lie algebra of the RIGHT physical blocks. -/
def balancedRight (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) : Mat n :=
  blockSkew b₁ (Xᵀ * (Z - (1/2 : ℝ) • leftPointProjection b₂ X Z))

theorem balancedLeft_supported (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) :
    Supported b₂ (balancedLeft b₁ b₂ X Z) := blockSkew_supported _ _

theorem balancedRight_supported (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) :
    Supported b₁ (balancedRight b₁ b₂ X Z) := blockSkew_supported _ _

theorem balancedLeft_skew (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) :
    IsSkew (balancedLeft b₁ b₂ X Z) := blockSkew_skew _ _

theorem balancedRight_skew (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) :
    IsSkew (balancedRight b₁ b₂ X Z) := blockSkew_skew _ _

@[simp] theorem balancedLeft_zero (b₁ b₂ : Fin n → ℕ) (X : Mat n) :
    balancedLeft b₁ b₂ X 0 = 0 := by
  simp [balancedLeft, rightPointProjection]

@[simp] theorem balancedRight_zero (b₁ b₂ : Fin n → ℕ) (X : Mat n) :
    balancedRight b₁ b₂ X 0 = 0 := by
  simp [balancedRight, leftPointProjection]

/-- The balanced lift is linear in the ambient direction. -/
@[simp] theorem balancedLeft_smul (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) (a : ℝ) :
    balancedLeft b₁ b₂ X (a • Z) = a • balancedLeft b₁ b₂ X Z := by
  simp [balancedLeft, rightPointProjection, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.sub_mul, blockSkew_sub, smul_sub, smul_smul, mul_comm]

@[simp] theorem balancedRight_smul (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) (a : ℝ) :
    balancedRight b₁ b₂ X (a • Z) = a • balancedRight b₁ b₂ X Z := by
  simp [balancedRight, leftPointProjection, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, blockSkew_sub, smul_sub, smul_smul, mul_comm]

theorem balancedLeft_mul (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) :
    balancedLeft b₁ b₂ X Z * X =
      leftPointProjection b₂ X Z - (1/2 : ℝ) •
        leftPointProjection b₂ X (rightPointProjection b₁ X Z) := by
  simp only [balancedLeft, Matrix.sub_mul, Matrix.smul_mul, blockSkew_sub,
    blockSkew_smul, leftPointProjection]

theorem mul_balancedRight (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) :
    X * balancedRight b₁ b₂ X Z =
      rightPointProjection b₁ X Z - (1/2 : ℝ) •
        rightPointProjection b₁ X (leftPointProjection b₂ X Z) := by
  simp only [balancedRight, Matrix.mul_sub, Matrix.mul_smul, blockSkew_sub,
    blockSkew_smul, rightPointProjection]

/-- The actual checked projector, not a new definition of the tangent space. -/
theorem balanced_reconstruct (b₁ b₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (L R Z : Mat n)
    (hsL : Supported b₂ L) (hsR : Supported b₁ R)
    (hL : Orthogonal L) (hR : Orthogonal R) :
    let X := product2 L (permMatrix σ) R
    balancedLeft b₁ b₂ X Z * X + X * balancedRight b₁ b₂ X Z =
      pointProjection b₁ b₂ X Z := by
  dsimp only
  rw [balancedLeft_mul, mul_balancedRight,
    ← pointProjectors_commute b₁ b₂ σ L R Z hsL hsR hL hR]
  unfold pointProjection
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- All generators are polynomial in (X,Z), including away from the GS orbit. -/
theorem balancedLeft_smooth (b₁ b₂ : Fin n → ℕ) :
    ContDiff ℝ ⊤ (fun t : Mat n × Mat n => balancedLeft b₁ b₂ t.1 t.2) := by
  unfold balancedLeft blockSkew
  exact contDiff_maskedSkew _ (contDiff_matrix_mul
    (contDiff_snd.sub ((contDiff_rightPointProjection b₁ contDiff_fst contDiff_snd).const_smul (1 / 2 : ℝ)))
    (contDiff_matrix_transpose contDiff_fst))

theorem balancedRight_smooth (b₁ b₂ : Fin n → ℕ) :
    ContDiff ℝ ⊤ (fun t : Mat n × Mat n => balancedRight b₁ b₂ t.1 t.2) := by
  unfold balancedRight blockSkew
  exact contDiff_maskedSkew _ (contDiff_matrix_mul
    (contDiff_matrix_transpose contDiff_fst)
    (contDiff_snd.sub ((contDiff_leftPointProjection b₂ contDiff_fst contDiff_snd).const_smul (1 / 2 : ℝ))))

end GS.GlobalGeometry
