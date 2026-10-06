module

public import GS.UnitarySharing.MinimumNormLift

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Complete real normal equations for unitary shared factors

For D_X(A,B)=AX+XB the physical adjoint is
(proj_left(Z X*), proj_right(X* Z)). Both projections include every repeated
complex entry. All positions, including nonoverlap positions tied to overlap
coordinates, occur in these equations. Singular normal operators are allowed.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry
namespace GS.UnitarySharing
variable {n : ℕ} {right left : Pattern n}

private theorem cFrobInner_mul_right (A B Z : CMat n) :
    cFrobInner (A * B) Z = cFrobInner A (Z * Bᴴ) := by
  rw [← cFrobInner_conjTranspose (A * B) Z, Matrix.conjTranspose_mul,
    cFrobInner_mul_left, ← cFrobInner_conjTranspose A (Z * Bᴴ)]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- The real adjoint for the expanded physical generator metric. -/
def pointAdjoint (right left : Pattern n) (X : CMat n) :
    CMat n →ₗ[ℝ] PairGenerator right left where
  toFun Z :=
    (⟨cFrobProjection (sharedSkewSpace left.size left.label) (Z * Xᴴ), cFrobProjection_mem _ _⟩,
     ⟨cFrobProjection (sharedSkewSpace right.size right.label) (Xᴴ * Z), cFrobProjection_mem _ _⟩)
  map_add' Z W := by
    apply Prod.ext <;> apply Subtype.ext <;>
      simp only [Matrix.add_mul, Matrix.mul_add, map_add, Prod.fst_add, Prod.snd_add,
        Submodule.coe_add]
  map_smul' a Z := by
    apply Prod.ext <;> apply Subtype.ext <;>
      simp only [Matrix.smul_mul, Matrix.mul_smul, map_smul]
    <;> rfl

private theorem pairing_projected (S : Submodule ℝ (CMat n)) (A Z : CMat n)
    (hA : A ∈ S) : cFrobInner A (cFrobProjection S Z) = cFrobInner A Z := by
  rw [← cFrobProjection_self_adjoint, cFrobProjection_of_mem S A hA]

theorem pointAdjoint_identity (X Z : CMat n) (v : PairGenerator right left) :
    generatorInner v (pointAdjoint right left X Z) = cFrobInner (pointMap right left X v) Z := by
  change cFrobInner v.1.val (cFrobProjection (sharedSkewSpace left.size left.label) (Z * Xᴴ)) +
    cFrobInner v.2.val (cFrobProjection (sharedSkewSpace right.size right.label) (Xᴴ * Z)) =
    cFrobInner (v.1.val * X + X * v.2.val) Z
  rw [pairing_projected _ _ _ v.1.property, pairing_projected _ _ _ v.2.property,
    cFrobInner_add_left, cFrobInner_mul_right, cFrobInner_mul_left]

def pointNormalOperator (right left : Pattern n) (X : CMat n) :
    PairGenerator right left →ₗ[ℝ] PairGenerator right left :=
  (pointAdjoint right left X).comp (pointMap right left X)

theorem pointNormalOperator_energy (X : CMat n) (v : PairGenerator right left) :
    generatorInner v (pointNormalOperator right left X v) = cFrobSq (pointMap right left X v) :=
  pointAdjoint_identity X _ v

theorem pointNormalOperator_kernel_iff (X : CMat n) (v : PairGenerator right left) :
    pointNormalOperator right left X v = 0 ↔ pointMap right left X v = 0 := by
  constructor
  · intro h
    apply (cFrobSq_eq_zero_iff _).mp
    rw [← pointNormalOperator_energy, h, generatorInner_zero_right]
  · intro h
    simp [pointNormalOperator, h]

theorem pointAdjoint_zero_iff (X Z : CMat n) :
    pointAdjoint right left X Z = 0 ↔
      ∀ v : PairGenerator right left, cFrobInner Z (pointMap right left X v) = 0 := by
  constructor
  · intro h v
    rw [cFrobInner_comm, ← pointAdjoint_identity, h, generatorInner_zero_right]
  · intro h
    apply (generatorEnergy_eq_zero_iff _).mp
    change generatorInner (pointAdjoint right left X Z) (pointAdjoint right left X Z) = 0
    rw [pointAdjoint_identity, cFrobInner_comm]
    exact h _

/-- The coupled normal equations characterize the full tangent projection. -/
theorem pointNormalEquation_iff_projection (X Z : CMat n) (v : PairGenerator right left) :
    pointNormalOperator right left X v = pointAdjoint right left X Z ↔
      pointMap right left X v = pointProjection right left X Z := by
  have he : pointNormalOperator right left X v = pointAdjoint right left X Z ↔
      pointAdjoint right left X (Z - pointMap right left X v) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact eq_comm
  rw [he, pointAdjoint_zero_iff]
  constructor
  · intro h
    symm
    apply cFrobProjection_unique_normal (pointDirections right left X) Z
      (pointMap right left X v) ⟨v, rfl⟩
    rintro W ⟨w, rfl⟩
    exact h w
  · intro h w
    rw [h]
    exact pointProjection_normal X Z _ ⟨w, rfl⟩

theorem minimumNormLift_solves_normalEquation (X Z : CMat n) :
    pointNormalOperator right left X (minimumNormLift right left X Z) =
      pointAdjoint right left X Z :=
  (pointNormalEquation_iff_projection X Z _).mpr (minimumNormLift_synthesis X Z)

/-- Necessity and sufficiency, not merely a sufficient stationarity condition. -/
theorem pointNormalEquation_iff_minimizes (X Z : CMat n) (v : PairGenerator right left) :
    pointNormalOperator right left X v = pointAdjoint right left X Z ↔
      ∀ w : PairGenerator right left,
        cFrobSq (Z - pointMap right left X v) ≤ cFrobSq (Z - pointMap right left X w) := by
  rw [pointNormalEquation_iff_projection]
  constructor
  · intro h w
    rw [h]
    exact pointProjection_minimizes X Z _ ⟨w, rfl⟩
  · intro h
    have hm := h (minimumNormLift right left X Z)
    rw [minimumNormLift_synthesis] at hm
    have hp := cFrobProjection_pythagorean (pointDirections right left X) Z
      (pointMap right left X v) ⟨v, rfl⟩
    change cFrobSq (Z - pointMap right left X v) =
      cFrobSq (Z - pointProjection right left X Z) +
      cFrobSq (pointProjection right left X Z - pointMap right left X v) at hp
    have hz : cFrobSq (pointProjection right left X Z - pointMap right left X v) = 0 := by
      linarith [cFrobSq_nonneg (pointProjection right left X Z - pointMap right left X v)]
    exact (sub_eq_zero.mp ((cFrobSq_eq_zero_iff _).mp hz)).symm

end GS.UnitarySharing
