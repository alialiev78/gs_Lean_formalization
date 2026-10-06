module

public import GS.SharedGeometry.Orbit

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
shared-orbit atlas and identification with its manifold differential remain
separate tasks.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.GlobalGeometry
namespace GS.SharedGeometry
variable {n : ℕ} {right left : Pattern n}

abbrev PairGenerator (right left : Pattern n) := Generator left × Generator right

/-- Spatial left and right generators; the plus sign absorbs the sign of
transposition in the group action. -/
def pointMap (right left : Pattern n) (X : Mat n) :
    PairGenerator right left →ₗ[ℝ] Mat n where
  toFun v := v.1.val * X + X * v.2.val
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add,
      Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' a v := by
    change (a • v.1.val) * X + X * (a • v.2.val) =
      a • (v.1.val * X + X * v.2.val)
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_add]

def pointDirections (right left : Pattern n) (X : Mat n) : Submodule ℝ (Mat n) :=
  LinearMap.range (pointMap right left X)

theorem mem_pointDirections_iff (X Y : Mat n) :
    Y ∈ pointDirections right left X ↔
      ∃ A ∈ sharedSkewSpace left.size left.label,
        ∃ B ∈ sharedSkewSpace right.size right.label, Y = A * X + X * B := by
  constructor
  · rintro ⟨⟨A, B⟩, h⟩
    exact ⟨A.val, A.property, B.val, B.property, h.symm⟩
  · rintro ⟨A, hA, B, hB, h⟩
    exact ⟨(⟨A, hA⟩, ⟨B, hB⟩), h.symm⟩

/-- Changing from body generators to spatial generators preserves all ties. -/
theorem sharedDirection_iff_pointDirections (P L R Y : Mat n)
    (hL : SharedOrthogonalFactor left.size left.label L)
    (hR : SharedOrthogonalFactor right.size right.label R) :
    SharedDirection right.size left.size right.label left.label P L R Y ↔
      Y ∈ pointDirections right left (product2 L P R) := by
  rw [mem_pointDirections_iff]
  constructor
  · rintro ⟨C, hC, Ω, hΩ, hY⟩
    refine ⟨L * C * Lᵀ, sharedSkew_conjugate left.positive left.divides hL hC,
      Rᵀ * Ω * R, sharedSkew_conjugate_transpose right.positive right.divides hR hΩ, ?_⟩
    have hl : (L * C * Lᵀ) * (L * P * R) = L * C * P * R := by
      calc
        _ = L * C * (Lᵀ * L) * P * R := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL.2.1.1]; simp only [Matrix.mul_one]
    have hr : (L * P * R) * (Rᵀ * Ω * R) = L * P * Ω * R := by
      calc
        _ = L * P * (R * Rᵀ) * Ω * R := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hR.2.1.2]; simp only [Matrix.mul_one]
    simpa only [product2, hl, hr] using hY
  · rintro ⟨A, hA, B, hB, hY⟩
    refine ⟨Lᵀ * A * L,
      sharedSkew_conjugate_transpose left.positive left.divides hL hA,
      R * B * Rᵀ, sharedSkew_conjugate right.positive right.divides hR hB, ?_⟩
    have hl : L * (Lᵀ * A * L) * P * R = A * (L * P * R) := by
      calc
        _ = (L * Lᵀ) * A * (L * P * R) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL.2.1.2]; simp only [Matrix.one_mul]
    have hr : L * P * (R * B * Rᵀ) * R = (L * P * R) * B := by
      calc
        _ = (L * P * R) * B * (Rᵀ * R) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hR.2.1.1, Matrix.mul_one]
    simpa only [product2, hl, hr] using hY

/-- Equality of direction predicates is pointwise, even with shared overlap. -/
theorem sharedDirection_factor_independent (P L R L' R' Y : Mat n)
    (hL : SharedOrthogonalFactor left.size left.label L)
    (hR : SharedOrthogonalFactor right.size right.label R)
    (hL' : SharedOrthogonalFactor left.size left.label L')
    (hR' : SharedOrthogonalFactor right.size right.label R')
    (hX : product2 L P R = product2 L' P R') :
    SharedDirection right.size left.size right.label left.label P L R Y ↔
      SharedDirection right.size left.size right.label left.label P L' R' Y := by
  rw [sharedDirection_iff_pointDirections P L R Y hL hR,
    sharedDirection_iff_pointDirections P L' R' Y hL' hR', hX]

/-- Every point-based direction is an actual differentiable shared-factor
velocity, with the prescribed base factors, not merely a formal generator. -/
theorem sharedFactorVelocity_iff_pointDirections (P L R Y : Mat n)
    (hL : SharedOrthogonalFactor left.size left.label L)
    (hR : SharedOrthogonalFactor right.size right.label R) :
    SharedFactorVelocity right.size left.size right.label left.label P L R Y ↔
      Y ∈ pointDirections right left (product2 L P R) := by
  rw [sharedFactorVelocity_iff_direction right.size left.size right.label left.label
    right.positive left.positive right.divides left.divides P L R Y hL hR]
  exact sharedDirection_iff_pointDirections P L R Y hL hR

/-- The kernel is the actual infinitesimal stabilizer equation. -/
theorem pointMap_kernel_iff (X : Mat n) (v : PairGenerator right left) :
    pointMap right left X v = 0 ↔ v.1.val * X = -(X * v.2.val) := by
  change v.1.val * X + X * v.2.val = 0 ↔ _
  exact add_eq_zero_iff_eq_neg

/-- At an orthogonal point the left kernel generator is determined by the right. -/
theorem pointMap_kernel_iff_conjugate (X : Mat n) (hX : Orthogonal X)
    (v : PairGenerator right left) :
    pointMap right left X v = 0 ↔ v.1.val = -(X * v.2.val * Xᵀ) := by
  rw [pointMap_kernel_iff]
  constructor
  · intro h
    have he := congrArg (fun A : Mat n => A * Xᵀ) h
    simpa only [Matrix.mul_assoc, hX.2, Matrix.mul_one, Matrix.neg_mul] using he
  · intro h
    rw [h]
    calc
      -(X * v.2.val * Xᵀ) * X = -(X * v.2.val * (Xᵀ * X)) := by
        simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(X * v.2.val) := by rw [hX.1, Matrix.mul_one]

/-- The direction spaces transform under the actual shared group action. -/
theorem action_mem_pointDirections (g : Factors right left) (X Y : Mat n)
    (hY : Y ∈ pointDirections right left X) :
    g • Y ∈ pointDirections right left (g • X) := by
  obtain ⟨A, hA, B, hB, hY⟩ := (mem_pointDirections_iff X Y).mp hY
  let L := Factor.matrix g.1
  let R := Factor.matrix g.2
  have hL := Factor.matrix_shared g.1
  have hR := Factor.matrix_shared g.2
  apply (mem_pointDirections_iff (g • X) (g • Y)).mpr
  refine ⟨L * A * Lᵀ, sharedSkew_conjugate left.positive left.divides hL hA,
    R * B * Rᵀ, sharedSkew_conjugate right.positive right.divides hR hB, ?_⟩
  have hl : (L * A * Lᵀ) * (L * X * Rᵀ) = L * (A * X) * Rᵀ := by
    calc
      _ = L * A * (Lᵀ * L) * X * Rᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hL.2.1.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hr : (L * X * Rᵀ) * (R * B * Rᵀ) = L * (X * B) * Rᵀ := by
    calc
      _ = L * X * (Rᵀ * R) * B * Rᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR.2.1.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  change L * Y * Rᵀ = (L * A * Lᵀ) * (L * X * Rᵀ) +
    (L * X * Rᵀ) * (R * B * Rᵀ)
  rw [hY, hl, hr, Matrix.mul_add, Matrix.add_mul]

/-- A genuine linear equivalence, not just an equality of dimensions. -/
def directionActionEquiv (g : Factors right left) (X : Mat n) :
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
theorem finrank_pointDirections_action (g : Factors right left) (X : Mat n) :
    Module.finrank ℝ (pointDirections right left (g • X)) =
      Module.finrank ℝ (pointDirections right left X) :=
  (LinearEquiv.finrank_eq (directionActionEquiv g X)).symm

theorem finrank_pointDirections_constant (P : Mat n) (X : MatrixOrbit right left P) :
    Module.finrank ℝ (pointDirections right left X.val) =
      Module.finrank ℝ (pointDirections right left P) := by
  obtain ⟨g, hg⟩ := X.property
  rw [← hg]
  exact finrank_pointDirections_action g P

end GS.SharedGeometry
