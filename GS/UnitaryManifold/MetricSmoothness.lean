module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Generic smoothness lemmas for a pullback metric

Keeping the ambient and model spaces abstract avoids unfolding concrete matrix
and horizontal-complement instances during tangent-bundle composition.
-/
noncomputable section
open scoped Manifold
namespace GS.UnitaryManifold

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The ambient realization of the derivative is smooth on the total bundle. -/
theorem ambientDerivative_contMDiff [IsManifold I ⊤ M] (f : M → F)
    (hf : ContMDiff I (𝓘(ℝ, F)) ⊤ f) :
    ContMDiff I.tangent (𝓘(ℝ, F)) ⊤
      (fun p : TangentBundle I M => mfderiv I (𝓘(ℝ, F)) f p.proj p.2) := by
  exact (contMDiff_snd_tangentBundle_modelSpace F (𝓘(ℝ, F))).comp
    (hf.contMDiff_tangentMap (by simp))

/-- Compose a smooth ambient pairing with two copies of a smooth map. -/
theorem paired_composition_contMDiff (g : M → F)
    (hg : ContMDiff I (𝓘(ℝ, F)) ⊤ g) (B : F × F → ℝ)
    (hB : ContDiff ℝ ⊤ B) :
    ContMDiff (I.prod I) (𝓘(ℝ, ℝ)) ⊤
      (fun p : M × M => B (g p.1, g p.2)) := by
  exact hB.comp_contMDiff
    ((hg.comp contMDiff_fst).prodMk_space (hg.comp contMDiff_snd))

/-- The diagonal evaluation of a smooth ambient pairing is smooth. -/
theorem diagonal_composition_contMDiff (g : M → F)
    (hg : ContMDiff I (𝓘(ℝ, F)) ⊤ g) (B : F × F → ℝ)
    (hB : ContDiff ℝ ⊤ B) :
    ContMDiff I (𝓘(ℝ, ℝ)) ⊤ (fun p : M => B (g p, g p)) := by
  exact hB.comp_contMDiff (hg.prodMk_space hg)

end GS.UnitaryManifold
