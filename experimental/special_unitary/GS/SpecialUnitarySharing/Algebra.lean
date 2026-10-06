module

public import GS.SpecialUnitarySharing.BlockAlgebra
public import GS.UnitarySharing.Orbit

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Shared special-unitary factors and their real generator spaces

The factor group is the intersection of the physical block determinant kernels
inside the existing unitary shared factor group. Its topology is inherited.
The special generator algebra is normalized by the larger unitary shared group;
this stronger equivariance will allow reuse of its already constructed local
sections for smooth ambient formulas, without calling the SU orbit a U orbit.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
open GS.UnitarySharing (Factor Factors)
namespace GS.SpecialUnitarySharing
variable {n : ℕ} {s : Pattern n}

/-- Supported, tied, skew-Hermitian, and trace-free in EVERY physical block. -/
def specialSkewSpace (s : Pattern n) : Submodule ℝ (CMat n) where
  carrier := {A | A ∈ GS.UnitarySharing.sharedSkewSpace s.size s.label ∧ BlockTraceZero s A}
  zero_mem' := ⟨(GS.UnitarySharing.sharedSkewSpace s.size s.label).zero_mem,
    blockTraceZero_zero s⟩
  add_mem' := fun hA hB => ⟨(GS.UnitarySharing.sharedSkewSpace s.size s.label).add_mem hA.1 hB.1,
    blockTraceZero_add _ _ hA.2 hB.2⟩
  smul_mem' := fun a _ hA => ⟨(GS.UnitarySharing.sharedSkewSpace s.size s.label).smul_mem a hA.1,
    blockTraceZero_smul a _ hA.2⟩

abbrev Generator (s : Pattern n) := ↥(specialSkewSpace s)
abbrev PairGenerator (right left : Pattern n) := Generator left × Generator right

def SpecialUnitaryFactor (s : Pattern n) (A : CMat n) : Prop :=
  GS.UnitarySharing.SharedUnitaryFactor s.size s.label A ∧ BlockDetOne s A

theorem special_factor_one (s : Pattern n) : SpecialUnitaryFactor s (1 : CMat n) :=
  ⟨⟨CSupported.one, ⟨by simp, by simp⟩, GS.UnitarySharing.TiedEntries.one _ _⟩,
    blockDetOne_one s⟩

theorem special_factor_mul (A B : CMat n) (hA : SpecialUnitaryFactor s A)
    (hB : SpecialUnitaryFactor s B) : SpecialUnitaryFactor s (A * B) :=
  ⟨GS.UnitarySharing.shared_factor_mul s.positive s.divides hA.1 hB.1,
    blockDetOne_mul A B hA.1.1 hA.2 hB.2⟩

theorem special_factor_conjTranspose (A : CMat n) (hA : SpecialUnitaryFactor s A) :
    SpecialUnitaryFactor s Aᴴ :=
  ⟨GS.UnitarySharing.shared_factor_conjTranspose hA.1, blockDetOne_conjTranspose A hA.2⟩

/-- Each physical determinant is one; phases in different blocks cannot cancel. -/
def specialSubgroup (s : Pattern n) : Subgroup (GS.UnitarySharing.Factor s) where
  carrier := {A | BlockDetOne s (Factor.matrix A)}
  one_mem' := blockDetOne_one s
  mul_mem' := by
    intro A B hA hB
    exact blockDetOne_mul _ _ (Factor.matrix_shared A).1 hA hB
  inv_mem' := by
    intro A hA
    exact blockDetOne_conjTranspose _ hA

abbrev SpecialFactor (s : Pattern n) := ↥(specialSubgroup s)
abbrev SpecialFactors (right left : Pattern n) := SpecialFactor left × SpecialFactor right

theorem specialSubgroup_isClosed (s : Pattern n) :
    IsClosed (specialSubgroup s : Set (GS.UnitarySharing.Factor s)) :=
  (isClosed_blockDetOne s).preimage Factor.continuous_matrix

instance specialFactorCompactSpace (s : Pattern n) : CompactSpace (SpecialFactor s) :=
  isCompact_iff_compactSpace.mp (specialSubgroup_isClosed s).isCompact

namespace SpecialFactor

def matrix (Q : SpecialFactor s) : CMat n := Factor.matrix Q.val
@[simp] theorem matrix_one : matrix (1 : SpecialFactor s) = 1 := rfl
@[simp] theorem matrix_mul (Q R : SpecialFactor s) : matrix (Q * R) = matrix Q * matrix R := rfl
@[simp] theorem matrix_inv (Q : SpecialFactor s) : matrix Q⁻¹ = (matrix Q)ᴴ := rfl

theorem matrix_special (Q : SpecialFactor s) : SpecialUnitaryFactor s (matrix Q) :=
  ⟨Factor.matrix_shared Q.val, Q.property⟩

theorem matrix_unitary (Q : SpecialFactor s) : Unitary (matrix Q) :=
  Factor.matrix_unitary Q.val

theorem matrix_injective : Function.Injective (matrix : SpecialFactor s → CMat n) := by
  intro Q R h
  apply Subtype.ext
  exact Factor.matrix_injective h

theorem continuous_matrix : Continuous (matrix : SpecialFactor s → CMat n) :=
  Factor.continuous_matrix.comp continuous_subtype_val

def ofMatrix (A : CMat n) (hA : SpecialUnitaryFactor s A) : SpecialFactor s :=
  ⟨Factor.ofMatrix A hA.1, hA.2⟩
@[simp] theorem matrix_ofMatrix (A : CMat n) (hA : SpecialUnitaryFactor s A) :
    matrix (ofMatrix A hA) = A := rfl

def matrixHomeomorph (s : Pattern n) :
    SpecialFactor s ≃ₜ {A : CMat n // SpecialUnitaryFactor s A} where
  toFun Q := ⟨matrix Q, matrix_special Q⟩
  invFun Q := ofMatrix Q.val Q.property
  left_inv Q := by apply matrix_injective; rfl
  right_inv Q := by apply Subtype.ext; rfl
  continuous_toFun := continuous_matrix.subtype_mk _
  continuous_invFun := ((continuous_subtype_val.subtype_mk _).subtype_mk _).subtype_mk _
end SpecialFactor

/-- The normalizing factor need only be unitary, not determinant one. -/
theorem specialSkew_conjugate (s : Pattern n) (Q A : CMat n)
    (hQ : GS.UnitarySharing.SharedUnitaryFactor s.size s.label Q)
    (hA : A ∈ specialSkewSpace s) : Q * A * Qᴴ ∈ specialSkewSpace s := by
  refine ⟨GS.UnitarySharing.sharedSkew_conjugate s.positive s.divides hQ hA.1, ?_⟩
  intro i
  rw [blockMatrix_mul s i (Q * A) Qᴴ (hQ.1.mul hA.1.1),
    blockMatrix_mul s i Q A hQ.1, blockMatrix_conjTranspose,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    (blockMatrix_unitary s i Q hQ.1 hQ.2.1).1, Matrix.one_mul]
  exact hA.2 i

theorem specialSkew_conjugate_conjTranspose (s : Pattern n) (Q A : CMat n)
    (hQ : GS.UnitarySharing.SharedUnitaryFactor s.size s.label Q)
    (hA : A ∈ specialSkewSpace s) : Qᴴ * A * Q ∈ specialSkewSpace s := by
  simpa only [Matrix.conjTranspose_conjTranspose] using
    specialSkew_conjugate s Qᴴ A (GS.UnitarySharing.shared_factor_conjTranspose hQ) hA

/-- An explicit continuous extension to ambient matrices, used only off the group. -/
def modelProjection (s : Pattern n) : CMat n →L[ℝ] Generator s :=
  ({ toFun := fun A => ⟨cFrobProjection (specialSkewSpace s) A, cFrobProjection_mem _ _⟩
     map_add' := by intro A B; apply Subtype.ext; exact map_add _ A B
     map_smul' := by intro a A; apply Subtype.ext; exact map_smul _ a A
   } : CMat n →ₗ[ℝ] Generator s).toContinuousLinearMap

@[simp] theorem modelProjection_inclusion (A : Generator s) : modelProjection s A.val = A := by
  apply Subtype.ext
  exact cFrobProjection_of_mem _ _ A.property

/-- The scalar unitary phase generator has been removed, not silently retained. -/
theorem imaginary_identity_not_special [NeZero n] (s : Pattern n) :
    (Complex.I • (1 : CMat n)) ∉ specialSkewSpace s := by
  intro h
  have hi := h.2 (0 : Fin n)
  rw [blockMatrix_complex_smul, blockMatrix_one, Matrix.trace_smul, Matrix.trace_one] at hi
  have hb : (s.size : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt s.positive)
  have hz : Complex.I * (s.size : ℂ) = 0 := by simpa only [smul_eq_mul, Fintype.card_fin] using hi
  exact (mul_ne_zero Complex.I_ne_zero hb) hz

end GS.SpecialUnitarySharing
