module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Product inputs for tangent-section constructions

These generic lemmas keep the manifold model abstract during elaboration.
They apply to both real and complex matrix orbits regarded as real manifolds.
-/

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace GS.Extensions
variable {E H M V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (I : ModelWithCorners ℝ E H)

theorem mfderiv_retraction_precompose_linear
    (R : E → M) (L : V →L[ℝ] E)
    (hR : MDifferentiableAt (𝓘(ℝ, E)) I R 0)
    (hD : mfderiv (𝓘(ℝ, E)) I R 0 = ContinuousLinearMap.id ℝ E)
    (v : V) :
    mfderiv (𝓘(ℝ, V)) I (R ∘ L) 0 v = L v := by
  have h := mfderiv_comp_apply_of_eq (0 : V) hR L.mdifferentiableAt (map_zero L) v
  simpa only [TangentSpace, ContinuousLinearMap.mfderiv_eq, hD, ContinuousLinearMap.id_apply] using h

theorem mfderiv_partial_right (F : M × V → M) (x : M)
    (hF : MDifferentiableAt (I.prod (𝓘(ℝ, V))) I F (x, 0)) (v : V) :
    mfderiv (𝓘(ℝ, V)) I (fun w : V => F (x, w)) 0 v =
      mfderiv (I.prod (𝓘(ℝ, V))) I F (x, 0) (0, v) := by
  have he : MDifferentiableAt (𝓘(ℝ, V)) (I.prod (𝓘(ℝ, V)))
      (fun w : V => (x, w)) 0 :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have h := mfderiv_comp_apply_of_eq (0 : V) hF he rfl v
  simpa only [TangentSpace, mfderiv_prod_right, ContinuousLinearMap.inr_apply, Function.comp_def] using h

theorem contMDiff_vertical_input [IsManifold I ⊤ M] :
    ContMDiff (I.prod (𝓘(ℝ, V))) (I.prod (𝓘(ℝ, V))).tangent ⊤
      (fun p : M × V =>
        (⟨(p.1, 0), (0, p.2)⟩ : TangentBundle (I.prod (𝓘(ℝ, V))) (M × V))) := by
  have hzero : ContMDiff (I.prod (𝓘(ℝ, V))) I.tangent ⊤
      (fun p : M × V => (⟨p.1, 0⟩ : TangentBundle I M)) :=
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_fst
  have hvector : ContMDiff (I.prod (𝓘(ℝ, V))) (𝓘(ℝ, V)).tangent ⊤
      (fun p : M × V => (⟨0, p.2⟩ : TangentBundle (𝓘(ℝ, V)) V)) := by
    have hp : ContMDiff (M' := ModelProd V V)
        (I.prod (𝓘(ℝ, V))) ((𝓘(ℝ, V)).prod (𝓘(ℝ, V))) ⊤
        (fun p : M × V => ((0, p.2) : ModelProd V V)) := by
      rw [← modelWithCornersSelf_prod]
      exact contMDiff_const.prodMk_space contMDiff_snd
    exact (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, V))).comp hp
  exact (contMDiff_equivTangentBundleProd_symm
    (I := I) (I' := 𝓘(ℝ, V)) (M := M) (M' := V)).comp (hzero.prodMk hvector)

end GS.Extensions
