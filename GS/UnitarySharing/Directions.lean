module

public import GS.UnitarySharing.Orbit

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Factor-independent infinitesimal directions for shared layers

The point map (A,B) |-> A X + X B is defined directly from X.  Conjugation
closure of the tied generator spaces identifies its range with the old
factor-coordinate formula for every valid factorization.  Thus the range
and the set of realized tied-factor velocities do not depend on that choice.

`pointDirections` is deliberately not called a tangent bundle.  The full
shared-orbit atlas and identification with its manifold differential are
constructed in the later atlas and tangent-bridge modules.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
namespace GS.UnitarySharing
variable {n : ℕ} {right left : Pattern n}

abbrev PairGenerator (right left : Pattern n) := Generator left × Generator right

/-- Spatial left and right generators; the plus sign absorbs the sign of
transposition in the group action. -/
def pointMap (right left : Pattern n) (X : CMat n) :
    PairGenerator right left →ₗ[ℝ] CMat n where
  toFun v := v.1.val * X + X * v.2.val
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add,
      Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' a v := by
    change (a • v.1.val) * X + X * (a • v.2.val) =
      a • (v.1.val * X + X * v.2.val)
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_add]

def pointDirections (right left : Pattern n) (X : CMat n) : Submodule ℝ (CMat n) :=
  LinearMap.range (pointMap right left X)

theorem mem_pointDirections_iff (X Y : CMat n) :
    Y ∈ pointDirections right left X ↔
      ∃ A ∈ sharedSkewSpace left.size left.label,
        ∃ B ∈ sharedSkewSpace right.size right.label, Y = A * X + X * B := by
  constructor
  · rintro ⟨⟨A, B⟩, h⟩
    exact ⟨A.val, A.property, B.val, B.property, h.symm⟩
  · rintro ⟨A, hA, B, hB, h⟩
    exact ⟨(⟨A, hA⟩, ⟨B, hB⟩), h.symm⟩

/-- Complete synthesis: equalities between repeated entries do not remove
nonoverlap residuals from a coupled least-squares problem. -/
def SharedDirection (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P L R Y : CMat n) : Prop :=
  ∃ C ∈ sharedSkewSpace b₂ τ₂, ∃ Ω ∈ sharedSkewSpace b₁ τ₁,
    Y = L * C * P * R + L * P * Ω * R

/-- Changing from body generators to spatial generators preserves all ties. -/
theorem sharedDirection_iff_pointDirections (P L R Y : CMat n)
    (hL : SharedUnitaryFactor left.size left.label L)
    (hR : SharedUnitaryFactor right.size right.label R) :
    SharedDirection right.size left.size right.label left.label P L R Y ↔
      Y ∈ pointDirections right left (GS.UnitaryGeometry.product2 L P R) := by
  rw [mem_pointDirections_iff]
  constructor
  · rintro ⟨C, hC, Ω, hΩ, hY⟩
    refine ⟨L * C * Lᴴ, sharedSkew_conjugate left.positive left.divides hL hC,
      Rᴴ * Ω * R, sharedSkew_conjugate_conjTranspose right.positive right.divides hR hΩ, ?_⟩
    have hl : (L * C * Lᴴ) * (L * P * R) = L * C * P * R := by
      calc
        _ = L * C * (Lᴴ * L) * P * R := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL.2.1.1]; simp only [Matrix.mul_one]
    have hr : (L * P * R) * (Rᴴ * Ω * R) = L * P * Ω * R := by
      calc
        _ = L * P * (R * Rᴴ) * Ω * R := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hR.2.1.2]; simp only [Matrix.mul_one]
    simpa only [GS.UnitaryGeometry.product2, hl, hr] using hY
  · rintro ⟨A, hA, B, hB, hY⟩
    refine ⟨Lᴴ * A * L,
      sharedSkew_conjugate_conjTranspose left.positive left.divides hL hA,
      R * B * Rᴴ, sharedSkew_conjugate right.positive right.divides hR hB, ?_⟩
    have hl : L * (Lᴴ * A * L) * P * R = A * (L * P * R) := by
      calc
        _ = (L * Lᴴ) * A * (L * P * R) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL.2.1.2]; simp only [Matrix.one_mul]
    have hr : L * P * (R * B * Rᴴ) * R = (L * P * R) * B := by
      calc
        _ = (L * P * R) * B * (Rᴴ * R) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hR.2.1.1, Matrix.mul_one]
    simpa only [GS.UnitaryGeometry.product2, hl, hr] using hY

/-- Equality of direction predicates is pointwise, even with shared overlap. -/
theorem sharedDirection_factor_independent (P L R L' R' Y : CMat n)
    (hL : SharedUnitaryFactor left.size left.label L)
    (hR : SharedUnitaryFactor right.size right.label R)
    (hL' : SharedUnitaryFactor left.size left.label L')
    (hR' : SharedUnitaryFactor right.size right.label R')
    (hX : GS.UnitaryGeometry.product2 L P R = GS.UnitaryGeometry.product2 L' P R') :
    SharedDirection right.size left.size right.label left.label P L R Y ↔
      SharedDirection right.size left.size right.label left.label P L' R' Y := by
  rw [sharedDirection_iff_pointDirections P L R Y hL hR,
    sharedDirection_iff_pointDirections P L' R' Y hL' hR', hX]

/-- The kernel is the actual infinitesimal stabilizer equation. -/
theorem pointMap_kernel_iff (X : CMat n) (v : PairGenerator right left) :
    pointMap right left X v = 0 ↔ v.1.val * X = -(X * v.2.val) := by
  change v.1.val * X + X * v.2.val = 0 ↔ _
  exact add_eq_zero_iff_eq_neg

/-- At an unitary point the left kernel generator is determined by the right. -/
theorem pointMap_kernel_iff_conjugate (X : CMat n) (hX : Unitary X)
    (v : PairGenerator right left) :
    pointMap right left X v = 0 ↔ v.1.val = -(X * v.2.val * Xᴴ) := by
  rw [pointMap_kernel_iff]
  constructor
  · intro h
    have he := congrArg (fun A : CMat n => A * Xᴴ) h
    simpa only [Matrix.mul_assoc, hX.2, Matrix.mul_one, Matrix.neg_mul] using he
  · intro h
    rw [h]
    calc
      -(X * v.2.val * Xᴴ) * X = -(X * v.2.val * (Xᴴ * X)) := by
        simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(X * v.2.val) := by rw [hX.1, Matrix.mul_one]

/-- The direction spaces transform under the actual shared group action. -/
theorem action_mem_pointDirections (g : Factors right left) (X Y : CMat n)
    (hY : Y ∈ pointDirections right left X) :
    g • Y ∈ pointDirections right left (g • X) := by
  obtain ⟨A, hA, B, hB, hY⟩ := (mem_pointDirections_iff X Y).mp hY
  let L := Factor.matrix g.1
  let R := Factor.matrix g.2
  have hL := Factor.matrix_shared g.1
  have hR := Factor.matrix_shared g.2
  apply (mem_pointDirections_iff (g • X) (g • Y)).mpr
  refine ⟨L * A * Lᴴ, sharedSkew_conjugate left.positive left.divides hL hA,
    R * B * Rᴴ, sharedSkew_conjugate right.positive right.divides hR hB, ?_⟩
  have hl : (L * A * Lᴴ) * (L * X * Rᴴ) = L * (A * X) * Rᴴ := by
    calc
      _ = L * A * (Lᴴ * L) * X * Rᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hL.2.1.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hr : (L * X * Rᴴ) * (R * B * Rᴴ) = L * (X * B) * Rᴴ := by
    calc
      _ = L * X * (Rᴴ * R) * B * Rᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR.2.1.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  change L * Y * Rᴴ = (L * A * Lᴴ) * (L * X * Rᴴ) +
    (L * X * Rᴴ) * (R * B * Rᴴ)
  rw [hY, hl, hr, Matrix.mul_add, Matrix.add_mul]

/-- A genuine linear equivalence, not just an equality of dimensions. -/
def directionActionEquiv (g : Factors right left) (X : CMat n) :
    pointDirections right left X ≃ₗ[ℝ] pointDirections right left (g • X) where
  toFun Y := ⟨g • Y.val, action_mem_pointDirections g X Y.val Y.property⟩
  invFun Y := ⟨g⁻¹ • Y.val, by
    simpa only [inv_smul_smul] using
      action_mem_pointDirections g⁻¹ (g • X) Y.val Y.property⟩
  left_inv Y := by
    apply Subtype.ext
    exact inv_smul_smul g Y.val
  right_inv Y := by
    apply Subtype.ext
    exact smul_inv_smul g Y.val
  map_add' Y Z := by
    apply Subtype.ext
    exact (actionLinearEquiv g).map_add Y.val Z.val
  map_smul' a Y := by
    apply Subtype.ext
    exact (actionLinearEquiv g).map_smul a Y.val

/-- Sharing may change the dimension, but does not create a rank jump along
one two-factor orbit.  Identifying this with manifold dimension is separate. -/
theorem finrank_pointDirections_action (g : Factors right left) (X : CMat n) :
    Module.finrank ℝ (pointDirections right left (g • X)) =
      Module.finrank ℝ (pointDirections right left X) :=
  (LinearEquiv.finrank_eq (directionActionEquiv g X)).symm

theorem finrank_pointDirections_constant (P : CMat n) (X : MatrixOrbit right left P) :
    Module.finrank ℝ (pointDirections right left X.val) =
      Module.finrank ℝ (pointDirections right left P) := by
  obtain ⟨g, hg⟩ := X.property
  rw [← hg]
  exact finrank_pointDirections_action g P

end GS.UnitarySharing
