module

public import GS.NonmanifoldClosure.PuncturedBall
public import GS.NonmanifoldFinal.EuclideanTransport
public import GS.NonmanifoldFinal.RetractTransport

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Euclidean charts restricted to centered balls

The dimension of a given chart is retained throughout. No dimension-invariance
principle is invoked. Centering and restriction are explicit homeomorphisms.
-/
noncomputable section
open GS.NonmanifoldObstruction GS.NonmanifoldFinal
open scoped Topology
namespace GS.NonmanifoldClosure

variable {X : Type*} [TopologicalSpace X]
abbrev Eucl (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev NormBall (n : ℕ) (r : ℝ) := {z : Eucl n // ‖z‖ < r}

structure OpenEuclideanChart (X : Type*) [TopologicalSpace X] (n : ℕ) where
  source : Set X
  target : Set (Eucl n)
  source_open : IsOpen source
  target_open : IsOpen target
  chart : source ≃ₜ target

/-- Centered charts always have an open source and an actual open norm-ball target. -/
structure CenteredEuclideanChart (X : Type*) [TopologicalSpace X] (x : X) (n : ℕ) where
  source : Set X
  source_open : IsOpen source
  source_point : x ∈ source
  radius : ℝ
  radius_pos : 0 < radius
  chart : source ≃ₜ NormBall n radius
  map_point : ∀ hx : x ∈ source, (chart ⟨x,hx⟩).val = 0

/-- Restriction preserves the stated dimension and the ambient subspace topologies. -/
def OpenEuclideanChart.restrict {n : ℕ} (c : OpenEuclideanChart X n)
    (U : Set X) (hU : IsOpen U) : OpenEuclideanChart X n := by
  let A : Set c.source := Subtype.val ⁻¹' U
  let B : Set c.target := c.chart '' A
  have hA : IsOpen A := hU.preimage continuous_subtype_val
  have hB : IsOpen B := c.chart.isOpenMap A hA
  exact
    { source := c.source ∩ U
      target := Subtype.val '' B
      source_open := c.source_open.inter hU
      target_open := c.target_open.isOpenMap_subtype_val B hB
      chart := ((subtypeOpenIntersection c.source U).symm.trans
        (restrictImage c.chart A)).trans (flattenImage c.target B) }

theorem euclideanAt_iff_chart (x : X) :
    EuclideanAt x ↔ ∃ n, ∃ c : OpenEuclideanChart X n, x ∈ c.source := by
  constructor
  · rintro ⟨U,hU,hx,n,V,hV,⟨h⟩⟩
    exact ⟨n,⟨U,V,hU,hV,h⟩,hx⟩
  · rintro ⟨n,c,hx⟩
    exact ⟨c.source,c.source_open,hx,n,c.target,c.target_open,⟨c.chart⟩⟩

/-- Every chart can be centered at any point of its source. -/
theorem exists_centeredChart {n : ℕ} (c : OpenEuclideanChart X n)
    (x : X) (hx : x ∈ c.source) :
    ∃ b : CenteredEuclideanChart X x n, b.source ⊆ c.source := by
  let a₀ : c.source := ⟨x,hx⟩
  let y : Eucl n := (c.chart a₀).val
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    (c.target_open.mem_nhds (c.chart a₀).property)
  let A : Set c.source := {a | ‖(c.chart a).val - y‖ < r}
  have hA : IsOpen A := isOpen_Iio.preimage
    (((continuous_subtype_val.comp c.chart.continuous).sub continuous_const).norm)
  have ha₀ : a₀ ∈ A := by change ‖y-y‖ < r; simpa using hr
  let j : NormBall n r → c.target := fun z =>
    ⟨y+z.val, hball (by
      rw [Metric.mem_ball, dist_eq_norm]
      change ‖y + z.val - y‖ < r
      simpa only [add_sub_cancel_left] using z.property)⟩
  have hj : Continuous j := (continuous_const.add continuous_subtype_val).subtype_mk _
  let e : A ≃ₜ NormBall n r :=
    { toFun := fun a => ⟨(c.chart a.val).val-y,a.property⟩
      invFun := fun z => ⟨c.chart.symm (j z),by
        change ‖(c.chart (c.chart.symm (j z))).val-y‖ < r
        rw [c.chart.apply_symm_apply]
        change ‖y+z.val-y‖ < r
        simpa only [add_sub_cancel_left] using z.property⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply c.chart.injective
        apply Subtype.ext
        simp only [c.chart.apply_symm_apply]
        change y+((c.chart a.val).val-y) = (c.chart a.val).val
        abel
      right_inv := by
        intro z
        apply Subtype.ext
        simp only [c.chart.apply_symm_apply]
        change y+z.val-y=z.val
        abel
      continuous_toFun :=
        ((continuous_subtype_val.comp (c.chart.continuous.comp continuous_subtype_val)).sub
          continuous_const).subtype_mk _
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact c.chart.symm.continuous.comp hj }
  let S : Set X := Subtype.val '' A
  have hS : IsOpen S := c.source_open.isOpenMap_subtype_val A hA
  have hxS : x ∈ S := ⟨a₀,ha₀,rfl⟩
  let b : CenteredEuclideanChart X x n :=
    { source := S
      source_open := hS
      source_point := hxS
      radius := r
      radius_pos := hr
      chart := (flattenImage c.source A).symm.trans e
      map_point := by
        intro hx'
        change (c.chart ⟨x,hx⟩).val-y=0
        exact sub_self y }
  exact ⟨b,by rintro z ⟨a,ha,rfl⟩; exact a.property⟩

/-- The centered source can additionally be required to lie in any prescribed
open neighborhood. This is used at both the singular and the regular point. -/
theorem exists_centeredChart_within {n : ℕ} (c : OpenEuclideanChart X n)
    (x : X) (hx : x ∈ c.source) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ b : CenteredEuclideanChart X x n, b.source ⊆ c.source ∩ U := by
  exact exists_centeredChart (c.restrict U hU) x ⟨hx,hxU⟩

/-- Removing the chart center gives exactly the punctured ball, not the complement
of an entire singular stratum. -/
def CenteredEuclideanChart.punctured {x : X} {n : ℕ}
    (c : CenteredEuclideanChart X x n) :
    PuncturedIn c.source x ≃ₜ PuncturedNormBall (Eucl n) c.radius where
  toFun p := ⟨(c.chart ⟨p.val,p.property.1⟩).val,
    (c.chart ⟨p.val,p.property.1⟩).property,by
      intro he
      apply p.property.2
      have hh : c.chart ⟨p.val,p.property.1⟩ = c.chart ⟨x,c.source_point⟩ := by
        apply Subtype.ext
        rw [c.map_point,he]
      exact congrArg Subtype.val (c.chart.injective hh)⟩
  invFun z := ⟨(c.chart.symm ⟨z.val,z.property.1⟩).val,
    (c.chart.symm ⟨z.val,z.property.1⟩).property,by
      intro he
      apply z.property.2
      have hh : c.chart.symm ⟨z.val,z.property.1⟩ = ⟨x,c.source_point⟩ :=
        Subtype.ext he
      have hv := congrArg (fun a => (c.chart a).val) hh
      simpa only [c.chart.apply_symm_apply,c.map_point] using hv⟩
  left_inv p := by
    apply Subtype.ext
    exact congrArg (fun a : c.source => a.val)
      (c.chart.symm_apply_apply ⟨p.val,p.property.1⟩)
  right_inv z := by
    apply Subtype.ext
    exact congrArg (fun a : NormBall n c.radius => a.val)
      (c.chart.apply_symm_apply ⟨z.val,z.property.1⟩)
  continuous_toFun :=
    (continuous_subtype_val.comp (c.chart.continuous.comp
      (continuous_subtype_val.subtype_mk _))).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp (c.chart.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _))).subtype_mk _

end GS.NonmanifoldClosure
