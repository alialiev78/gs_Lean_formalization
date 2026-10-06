module

public import GS.CayleyCharts.Transitions
public import GS.LieAction.Stabilizer
public import Mathlib.Data.Nat.Pairing

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Explicit block model for the FULL stabilizer, including overlap

The common right subgroup is not treated as an unspecified closed subgroup.
It is identified with the existing BlockO type for the intersections of the
right blocks and the inverse images of the left blocks. Nat.pair only encodes
the pair of labels in the natural-number label type used by the core definitions.

The isomorphism is the identity on the underlying right matrix. Thus the
Cayley charts apply to positive-dimensional stabilizers as well.
This is NOT a theorem giving a smooth quotient by this stabilizer.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.LieAction
namespace GS.CayleyCharts
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}

/-- Two coordinates share a joint block exactly when BOTH block constraints
permit them to interact. No new reordering of matrix coordinates is used. -/
def jointLabel (block₁ block₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) : Fin n → ℕ :=
  fun i => Nat.pair (block₁ i) (block₂ (σ i))

theorem jointLabel_eq_iff (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    jointLabel block₁ block₂ σ i = jointLabel block₁ block₂ σ j ↔
      block₁ i = block₁ j ∧ block₂ (σ i) = block₂ (σ j) := by
  exact Nat.pair_eq_pair

theorem supported_joint_iff (σ : Equiv.Perm (Fin n)) (A : Mat n) :
    Supported (jointLabel block₁ block₂ σ) A ↔
      Supported block₁ A ∧ Supported (fun i => block₂ (σ i)) A := by
  constructor
  · intro hA
    constructor
    · intro i j hij
      exact hA i j (fun h => hij ((jointLabel_eq_iff σ i j).mp h).1)
    · intro i j hij
      exact hA i j (fun h => hij ((jointLabel_eq_iff σ i j).mp h).2)
  · rintro ⟨hA, hB⟩ i j hij
    by_cases h : block₁ i = block₁ j
    · exact hB i j (fun h' => hij ((jointLabel_eq_iff σ i j).mpr ⟨h, h'⟩))
    · exact hA i j h

/-- Relabel the same right matrix as a joint-block matrix. -/
def commonToJoint (σ : Equiv.Perm (Fin n))
    (T : commonRightSubgroup block₁ block₂ (permMatrix σ) (perm_orthogonal σ)) :
    BlockO (jointLabel block₁ block₂ σ) :=
  ⟨T.val.val, (supported_joint_iff σ T.val.val).mpr
    ⟨T.val.property.1, (common_support_iff σ T.val.val).mp T.property⟩,
    T.val.property.2⟩

def jointToCommon (σ : Equiv.Perm (Fin n))
    (T : BlockO (jointLabel block₁ block₂ σ)) :
    commonRightSubgroup block₁ block₂ (permMatrix σ) (perm_orthogonal σ) := by
  let hs := (supported_joint_iff σ T.val).mp T.property.1
  exact ⟨⟨T.val, hs.1, T.property.2⟩, (common_support_iff σ T.val).mpr hs.2⟩

/-- Exact algebraic description of the stabilizer's right component. -/
def commonJointEquiv (σ : Equiv.Perm (Fin n)) :
    commonRightSubgroup block₁ block₂ (permMatrix σ) (perm_orthogonal σ) ≃*
      BlockO (jointLabel block₁ block₂ σ) where
  toFun := commonToJoint σ
  invFun := jointToCommon σ
  left_inv T := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv T := by apply Subtype.ext; rfl
  map_mul' T S := by apply Subtype.ext; rfl

/-- Both directions are coordinate inclusions between existing subtypes. -/
def commonJointHomeomorph (σ : Equiv.Perm (Fin n)) :
    commonRightSubgroup block₁ block₂ (permMatrix σ) (perm_orthogonal σ) ≃ₜ
      BlockO (jointLabel block₁ block₂ σ) where
  toEquiv := (commonJointEquiv σ).toEquiv
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

/-- Applies for arbitrary permutations and arbitrary overlap. -/
def stabilizerJointEquiv (σ : Equiv.Perm (Fin n)) :
    PointStabilizer block₁ block₂ (permMatrix σ) ≃*
      BlockO (jointLabel block₁ block₂ σ) :=
  (stabilizerRightEquiv (permMatrix σ) (perm_orthogonal σ)).trans (commonJointEquiv σ)

def stabilizerJointHomeomorph (σ : Equiv.Perm (Fin n)) :
    PointStabilizer block₁ block₂ (permMatrix σ) ≃ₜ
      BlockO (jointLabel block₁ block₂ σ) :=
  (stabilizerRightHomeomorph (permMatrix σ) (perm_orthogonal σ)).trans
    (commonJointHomeomorph σ)

@[simp] theorem stabilizerJoint_val (σ : Equiv.Perm (Fin n))
    (h : PointStabilizer block₁ block₂ (permMatrix σ)) :
    (stabilizerJointHomeomorph σ h).val = h.val.2.val := rfl

/-- Explicit open Cayley neighbourhood at an arbitrary stabilizer element. -/
def stabilizerChartSource (σ : Equiv.Perm (Fin n))
    (h : PointStabilizer block₁ block₂ (permMatrix σ)) :
    Set (PointStabilizer block₁ block₂ (permMatrix σ)) :=
  (stabilizerJointHomeomorph σ) ⁻¹' chartSource (stabilizerJointHomeomorph σ h)

theorem stabilizerChartSource_open (σ : Equiv.Perm (Fin n))
    (h : PointStabilizer block₁ block₂ (permMatrix σ)) :
    IsOpen (stabilizerChartSource σ h) :=
  (chartSource_open _).preimage (stabilizerJointHomeomorph σ).continuous

theorem stabilizer_mem_chartSource (σ : Equiv.Perm (Fin n))
    (h : PointStabilizer block₁ block₂ (permMatrix σ)) :
    h ∈ stabilizerChartSource σ h := base_mem_chartSource _

/-- Restrict the inherited-topology homeomorphism to the Cayley source. -/
def stabilizerSourceHomeomorph (σ : Equiv.Perm (Fin n))
    (h : PointStabilizer block₁ block₂ (permMatrix σ)) :
    stabilizerChartSource σ h ≃ₜ chartSource (stabilizerJointHomeomorph σ h) where
  toFun t := ⟨stabilizerJointHomeomorph σ t.val, t.property⟩
  invFun t := ⟨(stabilizerJointHomeomorph σ).symm t.val, by
    change stabilizerJointHomeomorph σ ((stabilizerJointHomeomorph σ).symm t.val) ∈
      chartSource (stabilizerJointHomeomorph σ h)
    simpa only [Homeomorph.apply_symm_apply] using t.property⟩
  left_inv t := by apply Subtype.ext; exact (stabilizerJointHomeomorph σ).symm_apply_apply t.val
  right_inv t := by apply Subtype.ext; exact (stabilizerJointHomeomorph σ).apply_symm_apply t.val
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (stabilizerJointHomeomorph σ).continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (stabilizerJointHomeomorph σ).symm.continuous.comp continuous_subtype_val

/-- Actual open charts on the full stabilizer, not just on a discrete subgroup. -/
def stabilizerChartHomeomorph (σ : Equiv.Perm (Fin n))
    (h : PointStabilizer block₁ block₂ (permMatrix σ)) :
    stabilizerChartSource σ h ≃ₜ parameterDomain (jointLabel block₁ block₂ σ) :=
  (stabilizerSourceHomeomorph σ h).trans
    (blockChartHomeomorph (stabilizerJointHomeomorph σ h))

/-- Matrix reconstruction of the two stabilizer components in these coordinates. -/
def stabilizerParam (σ : Equiv.Perm (Fin n))
    (h : PointStabilizer block₁ block₂ (permMatrix σ))
    (x : Model (jointLabel block₁ block₂ σ)) : Mat n × Mat n :=
  let T := chartInv (stabilizerJointHomeomorph σ h) x
  (permMatrix σ * T * (permMatrix σ)ᵀ, T)

theorem stabilizerParam_smooth_at (σ : Equiv.Perm (Fin n))
    (h : PointStabilizer block₁ block₂ (permMatrix σ))
    (x : Model (jointLabel block₁ block₂ σ))
    (hx : x ∈ parameterDomain (jointLabel block₁ block₂ σ)) :
    ContDiffAt ℝ ⊤ (stabilizerParam σ h) x := by
  have hi := chartInv_smooth_at (stabilizerJointHomeomorph σ h) x hx
  exact (smooth_mul_at (smooth_mul_at contDiffAt_const hi) contDiffAt_const).prodMk hi

/-- The formula is the same stabilizer embedding from the preceding project. -/
theorem stabilizerParam_inverse_matrix (σ : Equiv.Perm (Fin n))
    (h : PointStabilizer block₁ block₂ (permMatrix σ))
    (x : parameterDomain (jointLabel block₁ block₂ σ)) :
    let t := (stabilizerChartHomeomorph σ h).symm x
    (t.val.val.1.val, t.val.val.2.val) = stabilizerParam σ h x.val := by
  rfl

end GS.CayleyCharts
