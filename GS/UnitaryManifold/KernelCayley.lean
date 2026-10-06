module

public import GS.UnitaryManifold.OrbitDifferential

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Integrating the infinitesimal stabilizer

For arbitrary overlapping block partitions, every vector in the kernel of the
orbit differential integrates to an actual stabilizer element using the factor
Cayley chart. No discreteness or no-overlap assumption is used.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry
open scoped Topology

namespace GS.UnitaryManifold

variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}

theorem cayley_intertwine (A B P : CMat n) (hA : admissible A)
    (hB : admissible B) (h : A * P = P * B) :
    cayley A * P = P * cayley B := by
  apply GS.UnitaryManifold.cancel_right (1 + B) _ _ hB
  have hp : P * (1 + B) = (1 + A) * P := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
    rw [h]
  calc
    cayley A * P * (1 + B) = cayley A * (P * (1 + B)) := Matrix.mul_assoc _ _ _
    _ = cayley A * ((1 + A) * P) := by rw [hp]
    _ = (1 - A) * P := by rw [← Matrix.mul_assoc, cayley_mul A hA]
    _ = P * (1 - B) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      rw [h]
    _ = P * cayley B * (1 + B) := by rw [Matrix.mul_assoc, cayley_mul B hB]

theorem orbitParam_kernel_iff_intertwine (P : CMat n)
    (v : PairModel block₁ block₂) :
    fderiv ℝ (orbitParam (1 : FactorGroup block₁ block₂) P) 0 v = 0 ↔
      v.1.val * P = P * v.2.val := by
  rw [orbitParam_fderiv_zero]
  change GS.UnitaryGeometry.tangentParam (1 : CMat n) P (1 : CMat n)ᴴ
    ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) = 0 ↔ _
  simp only [GS.UnitaryGeometry.tangentParam, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul]
  constructor
  · intro h
    have hz : (-2 : ℝ) • (v.1.val * P - P * v.2.val) = 0 := by
      simpa only [smul_sub, sub_eq_add_neg, smul_add, smul_neg, neg_smul, neg_add_rev, neg_neg] using h
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  · intro h
    rw [h, ← add_smul]
    norm_num

theorem kernel_factorLift_stabilizes (P : CMat n) (v : PairModel block₁ block₂)
    (hv : fderiv ℝ (orbitParam (1 : FactorGroup block₁ block₂) P) 0 v = 0) :
    factorLift (1 : FactorGroup block₁ block₂) v • P = P := by
  have he := cayley_intertwine v.1.val v.2.val P
    (admissible_model v.1) (admissible_model v.2)
    ((orbitParam_kernel_iff_intertwine P v).mp hv)
  have ho := cayley_unitary v.2.val v.2.property.2 (admissible_model v.2)
  rw [action_apply, factorLift_left_val, factorLift_right_val]
  change (chartInv (1 : BlockU block₂) v.1 * P) *
    (chartInv (1 : BlockU block₁) v.2)ᴴ = P
  simp only [chartInv, show (1 : BlockU block₂).val = (1 : CMat n) from rfl,
    show (1 : BlockU block₁).val = (1 : CMat n) from rfl, Matrix.one_mul]
  rw [he, Matrix.mul_assoc, ho.2, Matrix.mul_one]

end GS.UnitaryManifold
