module

public import GS.Topology.SphereApproximationHomotopy
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Nullhomotopy of maps between spheres of increasing dimension

The proof extends a sphere map continuously to the ambient vector space,
approximates the extension by a smooth map near the compact source sphere,
and subtracts a sufficiently small point outside the smooth map's range.
The resulting map never vanishes and hence normalizes to a sphere-valued
map on the entire, contractible ambient vector space.

All approximation and dimension facts are theorems of the pinned mathlib;
no homology or homotopy computation is assumed.
-/

set_option autoImplicit false
noncomputable section

open Set Metric Function
open scoped Topology ContDiff unitInterval

namespace GS.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Smooth approximation, uniformly on a specified compact set. -/
theorem exists_contDiff_dist_lt_on_compact (f : C(E, F)) {K : Set E}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ x ∈ K, dist (g x) (f x) < ε := by
  have hu : UniformContinuousOn f (cthickening 1 K) :=
    hK.cthickening.uniformContinuousOn_of_continuous (by fun_prop)
  rcases Metric.uniformContinuousOn_iff.mp hu (ε / 2) (half_pos hε) with
    ⟨δ, hδ, hfδ⟩
  rcases (map_continuous f).exists_contDiff_dist_le_of_forall_mem_ball_dist_le
    (lt_min one_pos hδ) with ⟨g, hgc, hg⟩
  refine ⟨g, hgc, fun x hx => (hg _ _ fun y hy => ?_).trans_lt (half_lt_self hε)⟩
  rw [mem_ball, lt_min_iff] at hy
  exact hfδ _ (mem_cthickening_of_dist_le _ x _ _ hx hy.1.le) _
    (self_subset_cthickening _ hx) hy.2 |>.le

/-- A continuous map from a smaller real vector space has arbitrarily close,
smooth, nowhere-zero approximations on every compact set. -/
theorem exists_contDiff_ne_zero_dist_lt_on_compact (f : C(E, F))
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F)
    {K : Set E} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ (∀ x, g x ≠ 0) ∧
      ∀ x ∈ K, dist (g x) (f x) < ε := by
  obtain ⟨g, hgc, hg⟩ := exists_contDiff_dist_lt_on_compact f hK (half_pos hε)
  have hdense := (hgc.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).dense_compl_range_of_finrank_lt_finrank hdim
  obtain ⟨y, hy, hyε⟩ := hdense.exists_dist_lt 0 (half_pos hε)
  refine ⟨fun x => g x - y, hgc.sub contDiff_const, ?_, ?_⟩
  · intro x h
    exact hy ⟨x, sub_eq_zero.mp h⟩
  · intro x hx
    calc
      dist (g x - y) (f x) ≤ dist (g x - y) (g x) + dist (g x) (f x) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (by simpa using hyε) (hg x hx)
      _ = ε := add_halves ε

/-- Every map between unit spheres is nullhomotopic if the source ambient
vector space has strictly smaller real dimension than the target.

For spheres `S^k` and `S^m`, the hypothesis is precisely `k < m`.
The assertion concerns arbitrary continuous maps and the usual subspace
topology on the spheres. -/
theorem sphereMap_nullhomotopic_of_finrank_lt
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F)
    (f : C(sphere (0 : E) 1, sphere (0 : F) 1)) : f.Nullhomotopic := by
  let e : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  letI : TietzeExtension F := TietzeExtension.of_homeo e.toHomeomorph
  let fF : C(sphere (0 : E) 1, F) :=
    ⟨fun x => f x, continuous_subtype_val.comp f.continuous⟩
  obtain ⟨f₀, hf₀⟩ := fF.exists_restrict_eq isClosed_sphere
  obtain ⟨g, hgc, hg0, hg⟩ :=
    exists_contDiff_ne_zero_dist_lt_on_compact f₀ hdim (isCompact_sphere (0 : E) 1) zero_lt_one
  let gC : C(E, F) := ⟨g, hgc.continuous⟩
  have hclose : ∀ x : sphere (0 : E) 1, dist (gC.restrict _ x) (f x : F) < 1 := by
    intro x
    have heq : f₀ x = (f x : F) := congrArg (fun h : C(sphere (0 : E) 1, F) => h x) hf₀
    simpa only [ContinuousMap.restrict_apply, gC, ContinuousMap.coe_mk, heq]
      using hg x x.property
  have hfg := homotopic_sphereNormalize_of_dist_lt_one f (gC.restrict _) (fun x => hg0 x) hclose
  have hn : (sphereNormalize gC hg0).Nullhomotopic := by
    simpa using (id_nullhomotopic E).comp_right (sphereNormalize gC hg0)
  obtain ⟨c, hc⟩ := hn.comp_left (⟨Subtype.val, continuous_subtype_val⟩ :
    C(sphere (0 : E) 1, E))
  exact ⟨c, hfg.trans hc⟩

end GS.Topology
