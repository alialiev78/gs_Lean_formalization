module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Tactic.FunProp

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false
noncomputable section
open Set Metric Function
open scoped Topology unitInterval
namespace GS.Topology
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Normalize a continuous, nowhere-zero map to the unit sphere. -/
def sphereNormalize {X : Type*} [TopologicalSpace X] (g : C(X, F))
    (hg : ∀ x, g x ≠ 0) : C(X, sphere (0 : F) 1) := by
  refine ⟨fun x => ⟨‖g x‖⁻¹ • g x, ?_⟩, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr (hg x))),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hg x))]
  · exact ((g.continuous.norm.inv₀ fun x => norm_ne_zero_iff.mpr (hg x)).smul
      g.continuous).subtype_mk _

/-- A map within distance one of a unit vector cannot vanish. -/
theorem ne_zero_of_dist_lt_one {v w : F} (hv : ‖v‖ = 1)
    (h : dist w v < 1) : w ≠ 0 := by
  intro hw
  simpa [hw, hv] using h

/-- Straight-line interpolation stays nonzero when one endpoint is unit length
and the other endpoint is less than distance one away. -/
theorem line_ne_zero_of_dist_lt_one {v w : F} (hv : ‖v‖ = 1)
    (h : dist w v < 1) (t : unitInterval) :
    (1 - (t : ℝ)) • v + (t : ℝ) • w ≠ 0 := by
  apply ne_zero_of_dist_lt_one hv
  exact (convex_ball v 1) (by simp) h (sub_nonneg.mpr t.property.2)
    t.property.1 (sub_add_cancel 1 (t : ℝ))

/-- A continuous approximation within distance one of a sphere map becomes
homotopic to that map after normalization. -/
theorem homotopic_sphereNormalize_of_dist_lt_one {X : Type*} [TopologicalSpace X]
    (f : C(X, sphere (0 : F) 1)) (g : C(X, F)) (hg : ∀ x, g x ≠ 0)
    (hclose : ∀ x, dist (g x) (f x : F) < 1) :
    f.Homotopic (sphereNormalize g hg) := by
  let a : C(unitInterval × X, F) :=
    ⟨fun z => (1 - (z.1 : ℝ)) • (f z.2 : F) + (z.1 : ℝ) • g z.2, by
      fun_prop⟩
  have ha : ∀ z, a z ≠ 0 := by
    intro z
    exact line_ne_zero_of_dist_lt_one
      (mem_sphere_zero_iff_norm.mp (f z.2).property) (hclose z.2) z.1
  refine ⟨{ toContinuousMap := sphereNormalize a ha
            map_zero_left := ?_
            map_one_left := ?_ }⟩
  · intro x
    apply Subtype.ext
    have hf : ‖(f x : F)‖ = 1 := mem_sphere_zero_iff_norm.mp (f x).property
    simp [sphereNormalize, a, hf]
  · intro x
    apply Subtype.ext
    simp [sphereNormalize, a]

end GS.Topology
