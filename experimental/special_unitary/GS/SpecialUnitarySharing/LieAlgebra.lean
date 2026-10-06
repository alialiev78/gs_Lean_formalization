module

public import GS.SpecialUnitarySharing.Directions

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Lie closure of the actual SU generator constraints

Support, ties, skew-Hermiticity and each physical block trace are all checked.
The spatial linear fields close under operator commutators, with the reversed
sign on the right factor. This does not by itself construct an integrated SU
orbit atlas or a Frobenius-theorem interface.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
namespace GS.SpecialUnitarySharing
variable {n : ℕ}

def commutator (A B : CMat n) : CMat n := A * B - B * A

theorem commutator_special (s : Pattern n) (A B : CMat n)
    (hA : A ∈ specialSkewSpace s) (hB : B ∈ specialSkewSpace s) :
    commutator A B ∈ specialSkewSpace s := by
  refine ⟨⟨(hA.1.1.mul hB.1.1).sub (hB.1.1.mul hA.1.1), ?_, ?_⟩, ?_⟩
  · change (A * B - B * A)ᴴ = -(A * B - B * A)
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hA.1.2.1, hB.1.2.1]
    noncomm_ring
  · exact (GS.UnitarySharing.TiedEntries.mul s.positive s.divides
      hA.1.1 hB.1.1 hA.1.2.2 hB.1.2.2).add
      (GS.UnitarySharing.TiedEntries.mul s.positive s.divides
        hB.1.1 hA.1.1 hB.1.2.2 hA.1.2.2).neg
  · intro i
    rw [commutator, blockMatrix_sub, blockMatrix_mul s i A B hA.1.1,
      blockMatrix_mul s i B A hB.1.1, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- The sign reversal records that right multiplication is an opposite action. -/
def generatorCommutator {right left : Pattern n} (v w : PairGenerator right left) :
    PairGenerator right left :=
  (⟨commutator v.1.val w.1.val, commutator_special left _ _ v.1.property w.1.property⟩,
   ⟨-commutator v.2.val w.2.val,
     (specialSkewSpace right).neg_mem (commutator_special right _ _ v.2.property w.2.property)⟩)

/-- The ambient linear vector field associated with a fixed generator pair. -/
def spatialField {right left : Pattern n} (v : PairGenerator right left) : CMat n →L[ℝ] CMat n :=
  ({ toFun := fun X => v.1.val * X + X * v.2.val
     map_add' := by
       intro X Y
       simp only [Matrix.mul_add, Matrix.add_mul]
       abel
     map_smul' := by
       intro a X
       simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add]
   } : CMat n →ₗ[ℝ] CMat n).toContinuousLinearMap

theorem spatialField_hasFDerivAt {right left : Pattern n} (v : PairGenerator right left) (X : CMat n) :
    HasFDerivAt (spatialField v) (spatialField v) X := (spatialField v).hasFDerivAt

theorem spatialField_operator_commutator {right left : Pattern n}
    (v w : PairGenerator right left) (X : CMat n) :
    spatialField v (spatialField w X) - spatialField w (spatialField v X) =
      pointMap right left X (generatorCommutator v w) := by
  change v.1.val * (w.1.val * X + X * w.2.val) + (w.1.val * X + X * w.2.val) * v.2.val -
      (w.1.val * (v.1.val * X + X * v.2.val) + (v.1.val * X + X * v.2.val) * w.2.val) =
    (v.1.val * w.1.val - w.1.val * v.1.val) * X +
      X * (-(v.2.val * w.2.val - w.2.val * v.2.val))
  noncomm_ring

theorem spatialField_operator_commutator_mem {right left : Pattern n}
    (v w : PairGenerator right left) (X : CMat n) :
    spatialField v (spatialField w X) - spatialField w (spatialField v X) ∈
      pointDirections right left X := by
  rw [spatialField_operator_commutator]
  exact ⟨generatorCommutator v w, rfl⟩

end GS.SpecialUnitarySharing
