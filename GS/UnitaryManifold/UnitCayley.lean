module

public import GS.UnitaryManifold.CayleyDifferential

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The normalized unitary Cayley transform

The normalization gives derivative equal to the identity. All denominators
are invertible for every skew-Hermitian argument, without a step-size bound.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS Matrix GS.UnitaryGeometry
namespace GS.UnitaryManifold
variable {n : ℕ}

/-- Cayley normalization with derivative +identity at zero. -/
def unitCayley (A : CMat n) : CMat n := cayley ((-1 / 2 : ℝ) • A)

@[simp] theorem unitCayley_zero : unitCayley (0 : CMat n) = 1 := by
  simp [unitCayley]

theorem unitCayley_supported (b : Fin n → ℕ) (A : CMat n)
    (hs : CSupported b A) (hk : IsSkewHermitian A) : CSupported b (unitCayley A) :=
  cayley_supported b _ (hs.real_smul (-1 / 2))
    (admissible_of_isSkew _ (skewHermitian_real_smul _ hk))

theorem unitCayley_unitary (A : CMat n) (hk : IsSkewHermitian A) :
    Unitary (unitCayley A) :=
  cayley_unitary _ (skewHermitian_real_smul _ hk)
    (admissible_of_isSkew _ (skewHermitian_real_smul _ hk))

theorem unitCayley_smooth_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → CMat n) (hs : ContDiff ℝ ⊤ A) (hk : ∀ x, IsSkewHermitian (A x)) :
    ContDiff ℝ ⊤ (fun x => unitCayley (A x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  change ContDiffAt ℝ ⊤ (fun y => cayley ((-1 / 2 : ℝ) • A y)) x
  apply smooth_cayley_comp_at (hs.contDiffAt.const_smul (-1 / 2 : ℝ))
  exact admissible_of_isSkew _ (skewHermitian_real_smul _ (hk x))

/-- The matrix curve differential follows from the already checked Cayley chart. -/
theorem cayley_line_derivative (A : CMat n) (hk : IsSkewHermitian A) :
    HasDerivAt (fun t : ℝ => cayley (t • A)) ((-2 : ℝ) • A) 0 := by
  let u : Model (fun _ : Fin n => 0) := ⟨A, by intro i j hij; exact (hij rfl).elim, hk⟩
  have hd := chartInv_line_hasDerivAt_zero (1 : BlockU (fun _ : Fin n => 0)) u
  simpa only [chartInv, blockU_one_val, Matrix.one_mul, Submodule.coe_smul] using hd

theorem unitCayley_line_derivative (A : CMat n) (hk : IsSkewHermitian A) :
    HasDerivAt (fun t : ℝ => unitCayley (t • A)) A 0 := by
  have hd := cayley_line_derivative ((-1 / 2 : ℝ) • A) (skewHermitian_real_smul _ hk)
  have hf : (fun t : ℝ => unitCayley (t • A)) =
      (fun t : ℝ => cayley (t • ((-1 / 2 : ℝ) • A))) := by
    funext t
    unfold unitCayley
    rw [smul_comm]
  rw [hf]
  simpa only [smul_smul, show (-2 : ℝ) * (-1 / 2) = 1 by norm_num, one_smul] using hd

end GS.UnitaryManifold
