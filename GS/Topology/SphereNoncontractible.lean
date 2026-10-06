module

public import GS.Topology.BrouwerBall
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Sphere noncontractibility from the fixed point property of a closed ball

The radial map from the compact cylinder `[0,1] × sphere` to the closed ball
is a quotient map. A contraction of the sphere is constant on its fibres,
so it descends to a continuous retraction. The antipodal map composed with
that retraction has no fixed point.
-/

noncomputable section

open scoped Topology

namespace GS.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev UnitNormSphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1
abbrev UnitNormBall (E : Type*) [NormedAddCommGroup E] := Metric.closedBall (0 : E) 1

def sphereConeMap : C(unitInterval × UnitNormSphere E, UnitNormBall E) where
  toFun p := ⟨(p.1 : ℝ) • (p.2 : E), by
    have hu : ‖(p.2 : E)‖ = 1 := by simpa using p.2.property
    simpa [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg p.1.property.1, hu] using p.1.property.2⟩
  continuous_toFun := by fun_prop

@[simp] theorem sphereConeMap_norm (p : unitInterval × UnitNormSphere E) :
    ‖(sphereConeMap p : E)‖ = (p.1 : ℝ) := by
  have hu : ‖(p.2 : E)‖ = 1 := by simpa using p.2.property
  simp [sphereConeMap, norm_smul, Real.norm_eq_abs, abs_of_nonneg p.1.property.1, hu]

theorem sphereConeMap_surjective (u : UnitNormSphere E) :
    Function.Surjective (sphereConeMap (E := E)) := by
  intro x
  by_cases hx : (x : E) = 0
  · refine ⟨(0, u), ?_⟩
    apply Subtype.ext
    simpa [sphereConeMap] using hx.symm
  · have hn : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let t : unitInterval := ⟨‖(x : E)‖, norm_nonneg _, by
      simpa only [UnitNormBall, Metric.mem_closedBall, dist_zero_right] using x.property⟩
    let v : UnitNormSphere E := ⟨‖(x : E)‖⁻¹ • (x : E), by
      simp [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]⟩
    refine ⟨(t, v), ?_⟩
    apply Subtype.ext
    simp [sphereConeMap, t, v, smul_smul, mul_inv_cancel₀ hn]

theorem homotopy_factors_sphereConeMap (u : UnitNormSphere E)
    (h : ContinuousMap.Homotopy (ContinuousMap.const _ u)
      (ContinuousMap.id (UnitNormSphere E))) :
    Function.FactorsThrough h.toContinuousMap (sphereConeMap (E := E)) := by
  intro a b hab
  have ht : a.1 = b.1 := by
    apply Subtype.ext
    simpa only [sphereConeMap_norm] using congrArg (fun z : UnitNormBall E => ‖(z : E)‖) hab
  by_cases hz : (a.1 : ℝ) = 0
  · have ha : a.1 = 0 := Subtype.ext hz
    have hb : b.1 = 0 := ht.symm.trans ha
    change h (a.1, a.2) = h (b.1, b.2)
    rw [ha, hb]
    exact (h.map_zero_left a.2).trans (h.map_zero_left b.2).symm
  · have hu : a.2 = b.2 := by
      apply Subtype.ext
      have he : (a.1 : ℝ) • (a.2 : E) = (a.1 : ℝ) • (b.2 : E) := by
        simpa only [sphereConeMap, ContinuousMap.coe_mk, ht] using congrArg Subtype.val hab
      have hc := congrArg (fun w : E => (a.1 : ℝ)⁻¹ • w) he
      simpa only [smul_smul, inv_mul_cancel₀ hz, one_smul] using hc
    exact congrArg h (Prod.ext ht hu)

def sphereInclusion : C(UnitNormSphere E, UnitNormBall E) :=
  ContinuousMap.inclusion Metric.sphere_subset_closedBall

theorem exists_sphere_retraction_of_nullhomotopic [ProperSpace E]
    (hc : (ContinuousMap.id (UnitNormSphere E)).Nullhomotopic) :
    ∃ r : C(UnitNormBall E, UnitNormSphere E), r.comp sphereInclusion = ContinuousMap.id _ := by
  obtain ⟨u, ⟨h⟩⟩ := hc
  have hq : _root_.Topology.IsQuotientMap (sphereConeMap (E := E)) :=
    sphereConeMap.continuous.isClosedMap.isQuotientMap
      sphereConeMap.continuous (sphereConeMap_surjective u)
  let r := hq.lift h.symm.toContinuousMap (homotopy_factors_sphereConeMap u h.symm)
  refine ⟨r, ?_⟩
  apply ContinuousMap.ext
  intro v
  have he := ContinuousMap.congr_fun
    (hq.lift_comp h.symm.toContinuousMap (homotopy_factors_sphereConeMap u h.symm)) (1, v)
  change r (sphereInclusion v) = v
  have hi : sphereConeMap (1, v) = sphereInclusion v := by
    apply Subtype.ext
    change (1 : ℝ) • (v : E) = (v : E)
    exact one_smul _ _
  rw [← hi]
  exact he.trans (h.symm.map_one_left v)

theorem sphere_id_not_nullhomotopic_of_fixedPoint [ProperSpace E]
    (hfp : ∀ f : C(UnitNormBall E, UnitNormBall E), ∃ x, f x = x) :
    ¬ (ContinuousMap.id (UnitNormSphere E)).Nullhomotopic := by
  intro hc
  obtain ⟨r, hr⟩ := exists_sphere_retraction_of_nullhomotopic hc
  let f : C(UnitNormBall E, UnitNormBall E) := {
    toFun := fun x => ⟨-(r x : E), by
      have he : ‖(r x : E)‖ = 1 := by simpa using (r x).property
      simp [Metric.mem_closedBall, dist_zero_right, he]⟩,
    continuous_toFun := by fun_prop }
  obtain ⟨x, hx⟩ := hfp f
  have hxe : -(r x : E) = (x : E) := congrArg Subtype.val hx
  have hxn : ‖(x : E)‖ = 1 := by
    rw [← hxe, norm_neg]
    simpa using (r x).property
  let v : UnitNormSphere E := ⟨x, by simpa using hxn⟩
  have hrx : (r x : E) = (x : E) := by
    have hh := congrArg Subtype.val (ContinuousMap.congr_fun hr v)
    simpa [sphereInclusion, v, ContinuousMap.inclusion, Set.inclusion] using hh
  have hzero : (x : E) = 0 := by
    rw [hrx] at hxe
    have he : (2 : ℝ) • (x : E) = 0 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, add_smul, one_smul]
      exact neg_eq_iff_add_eq_zero.mp hxe
    have hz := congrArg (fun z : E => (2 : ℝ)⁻¹ • z) he
    simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
      one_smul, smul_zero] using hz
  simpa [hzero] using hxn

/-- Every Euclidean unit sphere is noncontractible. The fixed-point premise is
discharged by the proved simplex form of Brouwer and its compact-convex transfer. -/
theorem sphere_id_not_nullhomotopic [FiniteDimensional ℝ E] :
    ¬ (ContinuousMap.id (UnitNormSphere E)).Nullhomotopic :=
  sphere_id_not_nullhomotopic_of_fixedPoint
    (fun f => brouwer_fixed_point_unitBall f f.continuous)

theorem not_contractibleSpace_unitNormSphere [FiniteDimensional ℝ E] :
    ¬ ContractibleSpace (UnitNormSphere E) := by
  intro h
  letI := h
  exact sphere_id_not_nullhomotopic (E := E) (id_nullhomotopic (UnitNormSphere E))

end GS.Topology
