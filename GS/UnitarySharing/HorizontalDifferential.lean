module

public import GS.UnitarySharing.ProjectedSlice

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The full differential image after removing the shared stabilizer

The complement has the same differential image as the complete factor model
at every translated centre.  It therefore represents every matrix direction,
including when shared blocks and cross-layer overlap occur simultaneously.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryManifold GS.UnitaryGeometry
open scoped Topology Manifold
namespace GS.UnitarySharing
variable {n : ℕ} {right left : Pattern n}
local instance horizontalDifferentialNormedSpace (P : CMat n) :
    NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _

theorem orbitParam_fderiv_zero_of_kernel (g : Factors right left) (P : CMat n)
    (v : PairGenerator right left)
    (hv : fderiv ℝ (orbitParam (1 : Factors right left) P) 0 v = 0) :
    fderiv ℝ (orbitParam g P) 0 v = 0 := by
  have hi := (orbitParam_kernel_iff_intertwine P v).mp hv
  rw [orbitParam_fderiv_zero]
  simp only [GS.UnitaryGeometry.tangentParam, Matrix.smul_mul, Matrix.mul_smul]
  have he : (Factor.matrix g.1) * v.1.val * P * (Factor.matrix g.2)ᴴ =
      (Factor.matrix g.1) * P * v.2.val * (Factor.matrix g.2)ᴴ := by
    simpa only [Matrix.mul_assoc] using congrArg
      (fun A : CMat n => (Factor.matrix g.1) * A * (Factor.matrix g.2)ᴴ) hi
  rw [he]
  rw [← add_smul]
  norm_num

theorem horizontalOrbit_hasFDerivAt_zero (P : CMat n)
    (g : Factors right left) :
    HasFDerivAt (fun h : HorizontalModel right left P => orbitParam g P h.val)
      ((fderiv ℝ (orbitParam g P) 0).comp
        (HorizontalModel right left P).subtypeL) 0 := by
  have hh := ((orbitParam_smooth g P).differentiable (by simp) 0).hasFDerivAt
  simpa only [map_zero, Function.comp_def] using
    HasFDerivAt.comp (f := fun h : HorizontalModel right left P => h.val)
      (g := orbitParam g P) 0 hh
      (HorizontalModel right left P).subtypeL.hasFDerivAt

theorem horizontalOrbit_fderiv_zero (P : CMat n)
    (g : Factors right left) (h : HorizontalModel right left P) :
    fderiv ℝ (fun h : HorizontalModel right left P => orbitParam g P h.val) 0 h =
      fderiv ℝ (orbitParam g P) 0 h.val := by
  rw [(horizontalOrbit_hasFDerivAt_zero P g).fderiv]
  rfl

theorem horizontalOrbit_fderiv_zero_range (P : CMat n)
    (g : Factors right left) (Z : CMat n) :
    (∃ h : HorizontalModel right left P,
      fderiv ℝ (fun h : HorizontalModel right left P => orbitParam g P h.val) 0 h = Z) ↔
      Z ∈ pointDirections right left (g • P) := by
  rw [← orbitParam_fderiv_zero_range g P Z]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h.val, (horizontalOrbit_fderiv_zero P g h).symm.trans hh⟩
  · rintro ⟨v, hv⟩
    let z := (horizontalKernelEquiv right left P).symm v
    have hz : (z.1.val : PairGenerator right left) + z.2.val = v :=
      (horizontalKernelEquiv right left P).apply_symm_apply v
    have hk : fderiv ℝ (orbitParam g P) 0 z.2.val = 0 :=
      orbitParam_fderiv_zero_of_kernel g P z.2.val z.2.property
    refine ⟨z.1, ?_⟩
    rw [horizontalOrbit_fderiv_zero, ← hv, ← hz, map_add, hk, add_zero]

end GS.UnitarySharing
