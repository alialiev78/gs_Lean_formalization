module

public import GS.SpecialUnitarySharing.Algebra
public import GS.UnitarySharing.Directions

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# SU infinitesimal directions inside the ambient unitary shared orbit

`pointDirections` uses trace zero in each physical block. The action in this
file is deliberately the LARGER unitary shared action: it normalizes the SU
algebras. Thus the rank is constant on each U orbit, a fact stronger than
constancy on each SU orbit. No SU manifold or tangent bundle is assumed here.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
open GS.UnitarySharing (Factor Factors action_apply actionLinearEquiv)
namespace GS.SpecialUnitarySharing
variable {n : ℕ} {right left : Pattern n}

def pointMap (right left : Pattern n) (X : CMat n) :
    PairGenerator right left →ₗ[ℝ] CMat n where
  toFun v := v.1.val * X + X * v.2.val
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' a v := by
    change (a • v.1.val) * X + X * (a • v.2.val) = a • (v.1.val * X + X * v.2.val)
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_add]

def pointDirections (right left : Pattern n) (X : CMat n) : Submodule ℝ (CMat n) :=
  LinearMap.range (pointMap right left X)

theorem mem_pointDirections_iff (X Y : CMat n) :
    Y ∈ pointDirections right left X ↔
      ∃ A ∈ specialSkewSpace left, ∃ B ∈ specialSkewSpace right, Y = A * X + X * B := by
  constructor
  · rintro ⟨⟨A, B⟩, h⟩
    exact ⟨A.val, A.property, B.val, B.property, h.symm⟩
  · rintro ⟨A, hA, B, hB, h⟩
    exact ⟨(⟨A, hA⟩, ⟨B, hB⟩), h.symm⟩

def SharedDirection (right left : Pattern n) (P L R Y : CMat n) : Prop :=
  ∃ C ∈ specialSkewSpace left, ∃ Ω ∈ specialSkewSpace right,
    Y = L * C * P * R + L * P * Ω * R

theorem sharedDirection_iff_pointDirections (P L R Y : CMat n)
    (hL : GS.UnitarySharing.SharedUnitaryFactor left.size left.label L)
    (hR : GS.UnitarySharing.SharedUnitaryFactor right.size right.label R) :
    SharedDirection right left P L R Y ↔ Y ∈ pointDirections right left (product2 L P R) := by
  rw [mem_pointDirections_iff]
  constructor
  · rintro ⟨C, hC, Ω, hΩ, hY⟩
    refine ⟨L * C * Lᴴ, specialSkew_conjugate left L C hL hC,
      Rᴴ * Ω * R, specialSkew_conjugate_conjTranspose right R Ω hR hΩ, ?_⟩
    have hl : (L * C * Lᴴ) * (L * P * R) = L * C * P * R := by
      calc
        _ = L * C * (Lᴴ * L) * P * R := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL.2.1.1]; simp only [Matrix.mul_one]
    have hr : (L * P * R) * (Rᴴ * Ω * R) = L * P * Ω * R := by
      calc
        _ = L * P * (R * Rᴴ) * Ω * R := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hR.2.1.2]; simp only [Matrix.mul_one]
    simpa only [product2, hl, hr] using hY
  · rintro ⟨A, hA, B, hB, hY⟩
    refine ⟨Lᴴ * A * L, specialSkew_conjugate_conjTranspose left L A hL hA,
      R * B * Rᴴ, specialSkew_conjugate right R B hR hB, ?_⟩
    have hl : L * (Lᴴ * A * L) * P * R = A * (L * P * R) := by
      calc
        _ = (L * Lᴴ) * A * (L * P * R) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL.2.1.2]; simp only [Matrix.one_mul]
    have hr : L * P * (R * B * Rᴴ) * R = (L * P * R) * B := by
      calc
        _ = (L * P * R) * B * (Rᴴ * R) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hR.2.1.1, Matrix.mul_one]
    simpa only [product2, hl, hr] using hY

theorem sharedDirection_factor_independent (P L R L' R' Y : CMat n)
    (hL : SpecialUnitaryFactor left L) (hR : SpecialUnitaryFactor right R)
    (hL' : SpecialUnitaryFactor left L') (hR' : SpecialUnitaryFactor right R')
    (hX : product2 L P R = product2 L' P R') :
    SharedDirection right left P L R Y ↔ SharedDirection right left P L' R' Y := by
  rw [sharedDirection_iff_pointDirections P L R Y hL.1 hR.1,
    sharedDirection_iff_pointDirections P L' R' Y hL'.1 hR'.1, hX]

theorem pointMap_kernel_iff (X : CMat n) (v : PairGenerator right left) :
    pointMap right left X v = 0 ↔ v.1.val * X = -(X * v.2.val) := by
  change v.1.val * X + X * v.2.val = 0 ↔ _
  exact add_eq_zero_iff_eq_neg

/-- SU directions are a subspace of the actual unitary orbit's tangent image. -/
theorem pointDirections_le_unitary (X : CMat n) :
    pointDirections right left X ≤ GS.UnitarySharing.pointDirections right left X := by
  rintro Y ⟨v, rfl⟩
  exact ⟨(⟨v.1.val, v.1.property.1⟩, ⟨v.2.val, v.2.property.1⟩), rfl⟩

/-- The larger unitary group preserves the determinant-one infinitesimal constraints. -/
theorem action_mem_pointDirections (g : Factors right left) (X Y : CMat n)
    (hY : Y ∈ pointDirections right left X) :
    g • Y ∈ pointDirections right left (g • X) := by
  obtain ⟨A, hA, B, hB, hY⟩ := (mem_pointDirections_iff X Y).mp hY
  let L := Factor.matrix g.1
  let R := Factor.matrix g.2
  have hL := Factor.matrix_shared g.1
  have hR := Factor.matrix_shared g.2
  apply (mem_pointDirections_iff (g • X) (g • Y)).mpr
  refine ⟨L * A * Lᴴ, specialSkew_conjugate left L A hL hA,
    R * B * Rᴴ, specialSkew_conjugate right R B hR hB, ?_⟩
  have hl : (L * A * Lᴴ) * (L * X * Rᴴ) = L * (A * X) * Rᴴ := by
    calc
      _ = L * A * (Lᴴ * L) * X * Rᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hL.2.1.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hr : (L * X * Rᴴ) * (R * B * Rᴴ) = L * (X * B) * Rᴴ := by
    calc
      _ = L * X * (Rᴴ * R) * B * Rᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR.2.1.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  change L * Y * Rᴴ = (L * A * Lᴴ) * (L * X * Rᴴ) + (L * X * Rᴴ) * (R * B * Rᴴ)
  rw [hY, hl, hr, Matrix.mul_add, Matrix.add_mul]

def directionActionEquiv (g : Factors right left) (X : CMat n) :
    pointDirections right left X ≃ₗ[ℝ] pointDirections right left (g • X) where
  toFun Y := ⟨g • Y.val, action_mem_pointDirections g X Y.val Y.property⟩
  invFun Y := ⟨g⁻¹ • Y.val, by simpa only [inv_smul_smul] using
    action_mem_pointDirections g⁻¹ (g • X) Y.val Y.property⟩
  left_inv Y := by apply Subtype.ext; exact inv_smul_smul g Y.val
  right_inv Y := by apply Subtype.ext; exact smul_inv_smul g Y.val
  map_add' Y Z := by apply Subtype.ext; exact (actionLinearEquiv g).map_add Y.val Z.val
  map_smul' a Y := by apply Subtype.ext; exact (actionLinearEquiv g).map_smul a Y.val

theorem finrank_pointDirections_action (g : Factors right left) (X : CMat n) :
    Module.finrank ℝ (pointDirections right left (g • X)) =
      Module.finrank ℝ (pointDirections right left X) :=
  (LinearEquiv.finrank_eq (directionActionEquiv g X)).symm

end GS.SpecialUnitarySharing
