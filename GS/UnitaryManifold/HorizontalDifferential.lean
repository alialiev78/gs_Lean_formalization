module

public import GS.UnitaryManifold.HorizontalModel
public import GS.UnitaryManifold.KernelCayley

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The horizontal differential has the full orbit tangent image

The discarded kernel directions have zero differential at every translated
factor chart. Consequently restricting to the fixed horizontal model preserves
the entire generator image, for arbitrary overlap.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.OverlapGeometry
open scoped Topology Manifold
namespace GS.UnitaryManifold
variable {n : ℕ} {b₁ b₂ : Fin n → ℕ}

theorem orbitParam_eq_translate (g : FactorGroup b₁ b₂) (P : CMat n)
    (v : PairModel b₁ b₂) :
    orbitParam g P v = g • orbitParam (1 : FactorGroup b₁ b₂) P v := by
  simp only [orbitParam, chartInv, action_apply]
  change g.1.val * cayley v.1.val * P * (g.2.val * cayley v.2.val)ᴴ =
    g.1.val * ((1 * cayley v.1.val) * P * (1 * cayley v.2.val)ᴴ) * g.2.valᴴ
  simp only [Matrix.one_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem orbitParam_fderiv_zero_of_kernel (g : FactorGroup b₁ b₂) (P : CMat n)
    (v : PairModel b₁ b₂)
    (hv : fderiv ℝ (orbitParam (1 : FactorGroup b₁ b₂) P) 0 v = 0) :
    fderiv ℝ (orbitParam g P) 0 v = 0 := by
  have hi := (orbitParam_kernel_iff_intertwine P v).mp hv
  rw [orbitParam_fderiv_zero]
  simp only [GS.UnitaryGeometry.tangentParam, Matrix.smul_mul, Matrix.mul_smul]
  have he : g.1.val * v.1.val * P * g.2.valᴴ =
      g.1.val * P * v.2.val * g.2.valᴴ := by
    simpa only [Matrix.mul_assoc] using congrArg
      (fun A : CMat n => g.1.val * A * g.2.valᴴ) hi
  rw [he]
  rw [← add_smul]
  norm_num

theorem horizontalOrbit_hasFDerivAt_zero (σ : Equiv.Perm (Fin n))
    (g : FactorGroup b₁ b₂) :
    HasFDerivAt (fun h : HorizontalModel b₁ b₂ σ => orbitParam g (cPermMatrix σ) h.val)
      ((fderiv ℝ (orbitParam g (cPermMatrix σ)) 0).comp
        (HorizontalModel b₁ b₂ σ).subtypeL) 0 := by
  have hh := ((orbitParam_smooth g (cPermMatrix σ)).differentiable (by simp) 0).hasFDerivAt
  simpa only [map_zero, Function.comp_def] using
    HasFDerivAt.comp (f := fun h : HorizontalModel b₁ b₂ σ => h.val)
      (g := orbitParam g (cPermMatrix σ)) 0 hh
      (HorizontalModel b₁ b₂ σ).subtypeL.hasFDerivAt

theorem horizontalOrbit_fderiv_zero (σ : Equiv.Perm (Fin n))
    (g : FactorGroup b₁ b₂) (h : HorizontalModel b₁ b₂ σ) :
    fderiv ℝ (fun h : HorizontalModel b₁ b₂ σ => orbitParam g (cPermMatrix σ) h.val) 0 h =
      fderiv ℝ (orbitParam g (cPermMatrix σ)) 0 h.val := by
  rw [(horizontalOrbit_hasFDerivAt_zero σ g).fderiv]
  rfl

theorem horizontalOrbit_fderiv_zero_range (σ : Equiv.Perm (Fin n))
    (g : FactorGroup b₁ b₂) (Z : CMat n) :
    (∃ h : HorizontalModel b₁ b₂ σ,
      fderiv ℝ (fun h : HorizontalModel b₁ b₂ σ => orbitParam g (cPermMatrix σ) h.val) 0 h = Z) ↔
      Z ∈ tangentParamSpace b₁ b₂ g.1.val (cPermMatrix σ) g.2.valᴴ := by
  rw [← orbitParam_fderiv_zero_range g (cPermMatrix σ) Z]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h.val, (horizontalOrbit_fderiv_zero σ g h).symm.trans hh⟩
  · rintro ⟨v, hv⟩
    let z := (horizontalKernelEquiv b₁ b₂ σ).symm v
    have hz : (z.1.val : PairModel b₁ b₂) + z.2.val = v :=
      (horizontalKernelEquiv b₁ b₂ σ).apply_symm_apply v
    have hk : fderiv ℝ (orbitParam g (cPermMatrix σ)) 0 z.2.val = 0 :=
      orbitParam_fderiv_zero_of_kernel g (cPermMatrix σ) z.2.val z.2.property
    refine ⟨z.1, ?_⟩
    rw [horizontalOrbit_fderiv_zero, ← hv, ← hz, map_add, hk, add_zero]

end GS.UnitaryManifold
