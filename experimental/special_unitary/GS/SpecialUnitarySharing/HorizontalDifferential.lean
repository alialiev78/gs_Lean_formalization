module

public import GS.SpecialUnitarySharing.ProjectedSlice

@[expose] public section

set_option backward.isDefEq.respectTransparency false

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
open GS.SpecialUnitarySharing.Orbit
open scoped Topology Manifold
namespace GS.SpecialUnitarySharing
variable {n : ℕ} {right left : Pattern n}

theorem orbitParam_fderiv_zero_of_kernel (g : SpecialFactors right left) (P : CMat n)
    (v : PairGenerator right left)
    (hv : fderiv ℝ (orbitParam (1 : SpecialFactors right left) P) 0 v = 0) :
    fderiv ℝ (orbitParam g P) 0 v = 0 := by
  have hi := (orbitParam_kernel_iff_intertwine P v).mp hv
  rw [orbitParam_fderiv_zero]
  simp only [tangentParam, Matrix.smul_mul, Matrix.mul_smul]
  have he : (SpecialFactor.matrix g.1) * v.1.val * P * (SpecialFactor.matrix g.2)ᴴ =
      (SpecialFactor.matrix g.1) * P * v.2.val * (SpecialFactor.matrix g.2)ᴴ := by
    simpa only [Matrix.mul_assoc] using congrArg
      (fun A : CMat n => (SpecialFactor.matrix g.1) * A * (SpecialFactor.matrix g.2)ᴴ) hi
  rw [he]
  rw [← add_smul]
  norm_num

theorem horizontalOrbit_hasFDerivAt_zero (P : CMat n)
    (g : SpecialFactors right left) :
    HasFDerivAt (fun h : HorizontalModel right left P => orbitParam g P h.val)
      ((fderiv ℝ (orbitParam g P) 0).comp
        (HorizontalModel right left P).subtypeL) 0 := by
  have hh := ((orbitParam_smooth g P).differentiable (by simp) 0).hasFDerivAt
  simpa only [map_zero] using
    HasFDerivAt.comp (f := fun h : HorizontalModel right left P => h.val)
      (g := orbitParam g P) 0 hh
      (HorizontalModel right left P).subtypeL.hasFDerivAt

theorem horizontalOrbit_fderiv_zero (P : CMat n)
    (g : SpecialFactors right left) (h : HorizontalModel right left P) :
    fderiv ℝ (fun h : HorizontalModel right left P => orbitParam g P h.val) 0 h =
      fderiv ℝ (orbitParam g P) 0 h.val := by
  rw [(horizontalOrbit_hasFDerivAt_zero P g).fderiv]
  rfl

theorem horizontalOrbit_fderiv_zero_range (P : CMat n)
    (g : SpecialFactors right left) (Z : CMat n) :
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

end GS.SpecialUnitarySharing
