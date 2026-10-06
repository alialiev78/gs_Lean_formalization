module

public import GS.ManifoldCompletion.OrbitDifferential

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
open Matrix GS GS.LieAction GS.CayleyCharts GS.ManifoldCompletion
open scoped Topology Manifold

namespace GS.OverlapGeometry

variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}

theorem cayley_intertwine (A B P : Mat n) (hA : admissible A)
    (hB : admissible B) (h : A * P = P * B) :
    cayley A * P = P * cayley B := by
  apply GS.CayleyCharts.cancel_right (1 + B) _ _ hB
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

theorem orbitParam_kernel_iff_intertwine (P : Mat n)
    (v : PairModel block₁ block₂) :
    fderiv ℝ (orbitParam (1 : FactorGroup block₁ block₂) P) 0 v = 0 ↔
      v.1.val * P = P * v.2.val := by
  rw [orbitParam_fderiv_zero]
  change tangentParam (1 : Mat n) P (1 : Mat n)ᵀ
    ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) = 0 ↔ _
  simp only [tangentParam, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul]
  constructor
  · intro h
    ext i j
    have he := congrFun (congrFun h i) j
    change (-2 : ℝ) * (v.1.val * P) i j + 2 * (P * v.2.val) i j = 0 at he
    linarith
  · intro h
    rw [h]
    ext i j
    change (-2 : ℝ) * (P * v.2.val) i j + 2 * (P * v.2.val) i j = 0
    ring

theorem kernel_factorLift_stabilizes (P : Mat n) (v : PairModel block₁ block₂)
    (hv : fderiv ℝ (orbitParam (1 : FactorGroup block₁ block₂) P) 0 v = 0) :
    factorLift (1 : FactorGroup block₁ block₂) v • P = P := by
  have he := cayley_intertwine v.1.val v.2.val P
    (admissible_model v.1) (admissible_model v.2)
    ((orbitParam_kernel_iff_intertwine P v).mp hv)
  have ho := cayley_orthogonal v.2.val v.2.property.2 (admissible_model v.2)
  rw [action_apply, factorLift_left_val, factorLift_right_val]
  change (chartInv (1 : BlockO block₂) v.1 * P) *
    (chartInv (1 : BlockO block₁) v.2)ᵀ = P
  simp only [chartInv, show (1 : BlockO block₂).val = (1 : Mat n) from rfl,
    show (1 : BlockO block₁).val = (1 : Mat n) from rfl, Matrix.one_mul]
  rw [he, Matrix.mul_assoc, ho.2, Matrix.mul_one]

end GS.OverlapGeometry
