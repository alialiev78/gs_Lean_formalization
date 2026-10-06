module

public import GS.Extensions.OriginalUniform
public import GS.Specifications
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Discharging the local exponential-chart input

The analytic input is mathlib's strict derivative of exp at zero followed by
its inverse function theorem. No injectivity or same-fibres axiom is added.

The auxiliary operator norm is local to the first proof. The exported result
only involves the existing matrix topology, not an identification of that norm
with the Frobenius norm or with the default product norm.
-/

noncomputable section
open Matrix Filter
open scoped Topology
namespace GS.Continuation
open GS.Extensions

/-- The actual matrix exponential is injective on an open neighbourhood of zero.
Uses the v4.19 spelling `NormedSpace.exp`; newer docs omit that argument. -/
theorem exists_open_matrixExp_injective (n : ℕ) :
    ∃ V : Set (Mat n), IsOpen V ∧ (0 : Mat n) ∈ V ∧ Set.InjOn (@matrixExp n) V := by
  letI : SeminormedRing (Mat n) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  have hd : HasStrictFDerivAt (NormedSpace.exp : Mat n → Mat n)
      (ContinuousLinearEquiv.refl ℝ (Mat n) : Mat n →L[ℝ] Mat n) 0 := by
    simpa only [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.one_def] using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Mat n))
  have hleft := hd.eventually_left_inverse
  obtain ⟨V, hsub, hV, hzero⟩ := mem_nhds_iff.mp hleft
  refine ⟨V, hV, hzero, ?_⟩
  intro A hA B hB hab
  have heA := hsub hA
  have heB := hsub hB
  change _ = A at heA
  change _ = B at heB
  have he : NormedSpace.exp A = NormedSpace.exp B := by
    simpa only [matrixExp_eq_exp] using hab
  rw [he] at heA
  exact heA.symm.trans heB

/-- Left multiplication by an orthogonal matrix does not change local
injectivity. In particular this concerns the manuscript's originalPsi. -/
theorem originalPsi_injOn_of_matrixExp {q : ℕ} (Q₀ : Mat q)
    (hQ₀ : Orthogonal Q₀) (V : Set (Mat q))
    (hinj : Set.InjOn (@matrixExp q) V) :
    Set.InjOn (originalPsi Q₀) V := by
  intro A hA B hB he
  apply hinj hA hB
  have hm := congrArg (fun X : Mat q => Q₀ᵀ * X) he
  simpa only [originalPsi, ← Matrix.mul_assoc, hQ₀.1, Matrix.one_mul] using hm

/-- The open chart is constructed, rather than supplied as a hypothesis. -/
theorem exists_open_originalPsi_injective {q : ℕ} (Q₀ : Mat q)
    (hQ₀ : Orthogonal Q₀) :
    ∃ V : Set (Mat q), IsOpen V ∧ (0 : Mat q) ∈ V ∧
      Set.InjOn (originalPsi Q₀) V := by
  obtain ⟨V, hV, hzero, hinj⟩ := exists_open_matrixExp_injective q
  exact ⟨V, hV, hzero, originalPsi_injOn_of_matrixExp Q₀ hQ₀ V hinj⟩

/-- The original f and g have the same fibres on one uniformly small K_eta.
There is no chart, sign, normalization, or fibre hypothesis in this statement.
It does NOT assert that f(K_eta) covers a neighbourhood in the whole GS set. -/
theorem original_same_fibres {q : ℕ} (hq : 0 < q) (Q₀ : Mat q)
    (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ p ∈ originalK q η, ∀ p' ∈ originalK q η,
      originalF Q₀ p = originalF Q₀ p' ↔ originalG p = originalG p' := by
  obtain ⟨V, hV, hzero, hinj⟩ := exists_open_originalPsi_injective Q₀ hQ₀
  exact original_same_fibres_of_open_chart hq Q₀ hentries V hV hzero hinj

/-- Links the preceding result to the unchanged original specification.
Determinant +1 is part of that specification but is not needed for this step. -/
theorem originalSameFibres : GS.Specifications.OriginalSameFibresGoal := by
  intro q hq Q₀ hQ₀ _hdet hentries
  exact original_same_fibres (by omega) Q₀ hQ₀ hentries

end GS.Continuation
