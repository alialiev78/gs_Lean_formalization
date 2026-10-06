module

public import GS.SpecialUnitarySharing.Projection
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The canonical minimum-physical-norm lift of an SU direction

The metric on generators is the sum of the Frobenius norms of the two
expanded physical matrices. Repeated blocks therefore carry their actual
multiplicities. No inner product is installed on the entrywise matrix norm.
Instead the kernel projection is constructed in a genuine L2 product of
Frobenius coordinate spaces. Subtracting that projection gives the unique
horizontal lift. All matrices X are allowed; smooth dependence on X is proved
separately on each fixed shared orbit.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry InnerProductSpace
open scoped Topology
open GS.UnitarySharing (Factor Factors action_apply action_cFrobInner actionLinearEquiv)
namespace GS.SpecialUnitarySharing
variable {n : ℕ} {right left : Pattern n}

/-- The physical, multiplicity-weighted pairing; not the chart-coordinate norm. -/
def generatorInner (v w : PairGenerator right left) : ℝ :=
  cFrobInner v.1.val w.1.val + cFrobInner v.2.val w.2.val

def generatorEnergy (v : PairGenerator right left) : ℝ := generatorInner v v

theorem generatorInner_comm (v w : PairGenerator right left) :
    generatorInner v w = generatorInner w v := by
  simp only [generatorInner, cFrobInner_comm]

theorem generatorInner_add_left (u v w : PairGenerator right left) :
    generatorInner (u + v) w = generatorInner u w + generatorInner v w := by
  simp only [generatorInner, Prod.fst_add, Prod.snd_add, Submodule.coe_add,
    cFrobInner_add_left]
  ring

theorem generatorInner_sub_left (u v w : PairGenerator right left) :
    generatorInner (u - v) w = generatorInner u w - generatorInner v w := by
  change cFrobInner (u.1.val - v.1.val) w.1.val +
    cFrobInner (u.2.val - v.2.val) w.2.val = _
  rw [cFrobInner_sub_left, cFrobInner_sub_left]
  unfold generatorInner
  ring

theorem generatorInner_smul_left (a : ℝ) (v w : PairGenerator right left) :
    generatorInner (a • v) w = a * generatorInner v w := by
  change cFrobInner (a • v.1.val) w.1.val + cFrobInner (a • v.2.val) w.2.val = _
  rw [cFrobInner_real_smul_left, cFrobInner_real_smul_left]
  unfold generatorInner
  ring

@[simp] theorem generatorInner_zero_left (v : PairGenerator right left) :
    generatorInner 0 v = 0 := by simp [generatorInner]

@[simp] theorem generatorInner_zero_right (v : PairGenerator right left) :
    generatorInner v 0 = 0 := by rw [generatorInner_comm]; simp

theorem generatorEnergy_nonneg (v : PairGenerator right left) :
    0 ≤ generatorEnergy v := add_nonneg (cFrobSq_nonneg _) (cFrobSq_nonneg _)

@[simp] theorem generatorEnergy_eq_zero_iff (v : PairGenerator right left) :
    generatorEnergy v = 0 ↔ v = 0 :=
by
  constructor
  · intro h
    change cFrobSq v.1.val + cFrobSq v.2.val = 0 at h
    have h₁ : cFrobSq v.1.val = 0 := by
      linarith [cFrobSq_nonneg v.1.val, cFrobSq_nonneg v.2.val]
    have h₂ : cFrobSq v.2.val = 0 := by
      linarith [cFrobSq_nonneg v.1.val, cFrobSq_nonneg v.2.val]
    apply Prod.ext <;> apply Subtype.ext
    · exact (cFrobSq_eq_zero_iff _).mp h₁
    · exact (cFrobSq_eq_zero_iff _).mp h₂
  · rintro rfl
    simp [generatorEnergy, generatorInner]

theorem generatorEnergy_add (v w : PairGenerator right left) :
    generatorEnergy (v + w) = generatorEnergy v + generatorEnergy w +
      2 * generatorInner v w := by
  change cFrobSq (v.1.val + w.1.val) + cFrobSq (v.2.val + w.2.val) = _
  rw [cFrobSq_add, cFrobSq_add]
  unfold generatorEnergy generatorInner
  unfold cFrobSq
  ring

abbrev GeneratorHilbert (n : ℕ) := WithLp 2 (CFrobCoordinates n × CFrobCoordinates n)

/-- Linear encoding preserving the physical pairing, with no change to the
existing topology or norm instances on shared generators. -/
def generatorEncoding (right left : Pattern n) :
    PairGenerator right left →ₗ[ℝ] GeneratorHilbert n :=
  let L := (encodeCFrob.comp (specialSkewSpace left).subtype).comp
    (LinearMap.fst ℝ (Generator left) (Generator right))
  let R := (encodeCFrob.comp (specialSkewSpace right).subtype).comp
    (LinearMap.snd ℝ (Generator left) (Generator right))
  (WithLp.linearEquiv 2 ℝ (CFrobCoordinates n × CFrobCoordinates n)).symm.toLinearMap.comp
    (L.prod R)

theorem generatorEncoding_inner (v w : PairGenerator right left) :
    ⟪generatorEncoding right left v, generatorEncoding right left w⟫_ℝ =
      generatorInner v w := by
  change ⟪encodeCFrob v.1.val, encodeCFrob w.1.val⟫_ℝ +
    ⟪encodeCFrob v.2.val, encodeCFrob w.2.val⟫_ℝ = _
  rw [encodeCFrob_inner, encodeCFrob_inner]
  rfl

theorem generatorEncoding_injective : Function.Injective (generatorEncoding right left) := by
  intro v w h
  apply sub_eq_zero.mp
  apply (generatorEnergy_eq_zero_iff (v - w)).mp
  change generatorInner (v - w) (v - w) = 0
  rw [← generatorEncoding_inner, map_sub, h, sub_self]
  simp

private def encodedPointKernel (X : CMat n) : Submodule ℝ (GeneratorHilbert n) :=
  (pointMap right left X).ker.map (generatorEncoding right left)

private theorem exists_encoded_kernel_projection (X : CMat n)
    (v : PairGenerator right left) :
    ∃ k : PairGenerator right left,
      pointMap right left X k = 0 ∧ generatorEncoding right left k =
        ((encodedPointKernel (right := right) (left := left) X).orthogonalProjection
          (generatorEncoding right left v) : GeneratorHilbert n) := by
  exact ((encodedPointKernel (right := right) (left := left) X).orthogonalProjection
    (generatorEncoding right left v)).property

private def kernelPart (X : CMat n) (v : PairGenerator right left) :
    PairGenerator right left := Classical.choose (exists_encoded_kernel_projection X v)

private theorem kernelPart_mem (X : CMat n) (v : PairGenerator right left) :
    pointMap right left X (kernelPart X v) = 0 :=
  (Classical.choose_spec (exists_encoded_kernel_projection X v)).1

private theorem encode_kernelPart (X : CMat n) (v : PairGenerator right left) :
    generatorEncoding right left (kernelPart X v) =
      ((encodedPointKernel (right := right) (left := left) X).orthogonalProjection
        (generatorEncoding right left v) : GeneratorHilbert n) :=
  (Classical.choose_spec (exists_encoded_kernel_projection X v)).2

/-- The exact orthogonality condition for the full shared synthesis kernel. -/
def IsHorizontal (X : CMat n) (v : PairGenerator right left) : Prop :=
  ∀ k : PairGenerator right left, pointMap right left X k = 0 → generatorInner v k = 0

private theorem sub_kernelPart_horizontal (X : CMat n) (v : PairGenerator right left) :
    IsHorizontal X (v - kernelPart X v) := by
  intro k hk
  have hk' : generatorEncoding right left k ∈
      encodedPointKernel (right := right) (left := left) X := ⟨k, hk, rfl⟩
  have h := Submodule.orthogonalProjectionFn_inner_eq_zero
    (K := encodedPointKernel (right := right) (left := left) X)
    (generatorEncoding right left v) (generatorEncoding right left k) hk'
  rw [Submodule.orthogonalProjectionFn_eq] at h
  rw [← generatorEncoding_inner, map_sub, encode_kernelPart]
  exact h

theorem horizontal_lift_unique (X : CMat n) (v w : PairGenerator right left)
    (hv : IsHorizontal X v) (hw : IsHorizontal X w)
    (h : pointMap right left X v = pointMap right left X w) : v = w := by
  have hk : pointMap right left X (v - w) = 0 := by rw [map_sub, h, sub_self]
  apply sub_eq_zero.mp
  apply (generatorEnergy_eq_zero_iff (v - w)).mp
  change generatorInner (v - w) (v - w) = 0
  rw [generatorInner_sub_left, hv _ hk, hw _ hk, sub_self]

/-- Existence is derived from finite-dimensional orthogonal projection. -/
theorem exists_horizontal_lift (X Z : CMat n) :
    ∃ v : PairGenerator right left,
      pointMap right left X v = pointProjection right left X Z ∧ IsHorizontal X v := by
  obtain ⟨v, hv⟩ := pointProjection_mem (right := right) (left := left) X Z
  refine ⟨v - kernelPart X v, ?_, sub_kernelPart_horizontal X v⟩
  rw [map_sub, kernelPart_mem, sub_zero]
  exact hv

private def selectedLift (right left : Pattern n) (X Z : CMat n) : PairGenerator right left :=
  Classical.choose (exists_horizontal_lift (right := right) (left := left) X Z)

private theorem selectedLift_synthesis (X Z : CMat n) :
    pointMap right left X (selectedLift right left X Z) = pointProjection right left X Z :=
  (Classical.choose_spec (exists_horizontal_lift (right := right) (left := left) X Z)).1

private theorem selectedLift_horizontal (X Z : CMat n) :
    IsHorizontal X (selectedLift right left X Z) :=
  (Classical.choose_spec (exists_horizontal_lift (right := right) (left := left) X Z)).2

/-- The canonical minimum-physical-norm lift of the projected ambient vector.
It is linear and continuous in Z; it is NOT asserted smooth across arbitrary
ambient rank changes in X. -/
def minimumNormLift (right left : Pattern n) (X : CMat n) :
    CMat n →L[ℝ] PairGenerator right left :=
  ({ toFun := selectedLift right left X
     map_add' := by
       intro Z W
       apply horizontal_lift_unique X
       · exact selectedLift_horizontal X (Z + W)
       · intro k hk
         rw [generatorInner_add_left, selectedLift_horizontal X Z k hk,
           selectedLift_horizontal X W k hk, add_zero]
       · simp only [map_add, selectedLift_synthesis]
     map_smul' := by
       intro a Z
       apply horizontal_lift_unique X
       · exact selectedLift_horizontal X (a • Z)
       · intro k hk
         rw [generatorInner_smul_left, selectedLift_horizontal X Z k hk, mul_zero]
       · simp only [map_smul, selectedLift_synthesis, RingHom.id_apply]
   } : CMat n →ₗ[ℝ] PairGenerator right left).toContinuousLinearMap

theorem minimumNormLift_synthesis (X Z : CMat n) :
    pointMap right left X (minimumNormLift right left X Z) =
      pointProjection right left X Z := selectedLift_synthesis X Z

theorem minimumNormLift_horizontal (X Z : CMat n) :
    IsHorizontal X (minimumNormLift right left X Z) := selectedLift_horizontal X Z

theorem minimumNormLift_unique (X Z : CMat n) (v : PairGenerator right left)
    (hv : pointMap right left X v = pointProjection right left X Z)
    (hh : IsHorizontal X v) : v = minimumNormLift right left X Z :=
  horizontal_lift_unique X v _ hh (minimumNormLift_horizontal X Z)
    (hv.trans (minimumNormLift_synthesis X Z).symm)

/-- Exact reconstruction of every allowed SU generator direction. -/
theorem minimumNormLift_reconstruct (X V : CMat n)
    (hV : V ∈ pointDirections right left X) :
    pointMap right left X (minimumNormLift right left X V) = V := by
  rw [minimumNormLift_synthesis, pointProjection_of_mem X V hV]

/-- Removing the ambient normal component does not change the selected generators. -/
@[simp] theorem minimumNormLift_projected (X Z : CMat n) :
    minimumNormLift right left X (pointProjection right left X Z) =
      minimumNormLift right left X Z := by
  apply minimumNormLift_unique X Z
  · rw [minimumNormLift_synthesis, pointProjection_idempotent]
  · exact minimumNormLift_horizontal X _

/-- Every other lift differs by a kernel vector and has the indicated excess energy. -/
theorem minimumNormLift_pythagorean (X Z : CMat n) (v : PairGenerator right left)
    (hv : pointMap right left X v = pointProjection right left X Z) :
    generatorEnergy v = generatorEnergy (minimumNormLift right left X Z) +
      generatorEnergy (v - minimumNormLift right left X Z) := by
  have hk : pointMap right left X (v - minimumNormLift right left X Z) = 0 := by
    rw [map_sub, hv, minimumNormLift_synthesis, sub_self]
  have he : v = minimumNormLift right left X Z + (v - minimumNormLift right left X Z) := by abel
  conv_lhs => rw [he]
  rw [generatorEnergy_add, minimumNormLift_horizontal X Z _ hk]
  ring

theorem minimumNormLift_minimizes (X Z : CMat n) (v : PairGenerator right left)
    (hv : pointMap right left X v = pointProjection right left X Z) :
    generatorEnergy (minimumNormLift right left X Z) ≤ generatorEnergy v := by
  rw [minimumNormLift_pythagorean X Z v hv]
  exact le_add_of_nonneg_right (generatorEnergy_nonneg _)

theorem minimumNormLift_unique_minimizer (X Z : CMat n) (v : PairGenerator right left)
    (hv : pointMap right left X v = pointProjection right left X Z)
    (hmin : generatorEnergy v ≤ generatorEnergy (minimumNormLift right left X Z)) :
    v = minimumNormLift right left X Z := by
  have hp := minimumNormLift_pythagorean X Z v hv
  have hz : generatorEnergy (v - minimumNormLift right left X Z) = 0 := by
    linarith [generatorEnergy_nonneg (v - minimumNormLift right left X Z)]
  exact sub_eq_zero.mp ((generatorEnergy_eq_zero_iff _).mp hz)

end GS.SpecialUnitarySharing
