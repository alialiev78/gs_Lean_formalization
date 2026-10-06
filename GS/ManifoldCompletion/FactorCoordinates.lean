module

public import GS.CayleyCharts.Atlas
public import GS.CayleyCharts.OrbitCharts

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Total factor reconstruction and fixed right-translation in Cayley coordinates

This file uses the CHECKED Cayley atlas without changing it. The parameter domain
is all of the supported-skew model, as proved in the supplied revision. No
manifold structure on the GS orbit is assumed here.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts Filter Set
open scoped Topology Manifold
namespace GS.ManifoldCompletion
variable {n : ℕ} {block block₁ block₂ : Fin n → ℕ}

/-- The existing total chart inverse agrees everywhere with its matrix formula,
not just in a neighbourhood: all skew matrices are admissible. -/
theorem blockChartInverse_val_everywhere (Q : BlockO block) (x : Model block) :
    (blockChartInverse Q x).val = chartInv Q x :=
  blockChartInverse_val Q x (admissible_model x)

theorem continuous_blockChartInverse (Q : BlockO block) :
    Continuous (blockChartInverse Q) := by
  have hc : Continuous (fun x : Model block => (blockChartInverse Q x).val) := by
    simpa only [blockChartInverse_val_everywhere] using (chartInv_smooth Q).continuous
  exact hc.subtype_mk _

/-- This uses the original factor group and the original matrix topology. -/
def factorLift (g : FactorGroup block₁ block₂) (x : PairModel block₁ block₂) :
    FactorGroup block₁ block₂ :=
  (blockChartInverse g.1 x.1, blockChartInverse g.2 x.2)

@[simp] theorem factorLift_left_val (g : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) :
    (factorLift g x).1.val = chartInv g.1 x.1 :=
  blockChartInverse_val_everywhere g.1 x.1

@[simp] theorem factorLift_right_val (g : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) :
    (factorLift g x).2.val = chartInv g.2 x.2 :=
  blockChartInverse_val_everywhere g.2 x.2

theorem continuous_factorLift (g : FactorGroup block₁ block₂) :
    Continuous (factorLift g) :=
  ((continuous_blockChartInverse g.1).comp continuous_fst).prodMk
    ((continuous_blockChartInverse g.2).comp continuous_snd)

@[simp] theorem factorLift_zero (g : FactorGroup block₁ block₂) :
    factorLift g 0 = g := by
  apply Prod.ext <;> apply Subtype.ext <;> simp

@[simp] theorem factorCoordinates_factorLift (g : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) :
    factorCoordinates g (factorLift g x) = x := by
  apply Prod.ext
  · change chartMap g.1 (factorLift g x).1.val = x.1
    rw [factorLift_left_val]
    exact chartMap_chartInv g.1 x.1 (admissible_model x.1)
  · change chartMap g.2 (factorLift g x).2.val = x.2
    rw [factorLift_right_val]
    exact chartMap_chartInv g.2 x.2 (admissible_model x.2)

theorem factorLift_factorCoordinates (g h : FactorGroup block₁ block₂)
    (hh : h ∈ factorSource g) : factorLift g (factorCoordinates g h) = h := by
  apply Prod.ext
  · apply Subtype.ext
    rw [factorLift_left_val]
    exact chartInv_chartMap g.1 h.1 hh.1
  · apply Subtype.ext
    rw [factorLift_right_val]
    exact chartInv_chartMap g.2 h.2 hh.2

/-- The unique factor represented by a point in a restricted chart target is
precisely the explicit global factorLift, not a new choice function. -/
theorem factorLift_mem_orbitFactorSource (g : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) (hx : x ∈ orbitParameterTarget g) :
    factorLift g x ∈ orbitFactorSource g := by
  let h := (smallFactorChart g).symm ⟨x, hx⟩
  have he : factorCoordinates g h.val = x := by
    rw [← smallFactorChart_apply g h]
    exact congrArg Subtype.val ((smallFactorChart g).apply_symm_apply ⟨x, hx⟩)
  have hbase := factorLift_factorCoordinates g h.val
    ((orbitFactorSource_mem_iff g h.val).mp h.property).1
  rw [he] at hbase
  rw [hbase]
  exact h.property

theorem factorLift_action (g : FactorGroup block₁ block₂) (P : Mat n)
    (x : PairModel block₁ block₂) :
    factorLift g x • P = orbitParam g P x := by
  simp only [action_apply, factorLift_left_val, factorLift_right_val, orbitParam]

/-- The smooth candidate for an ORBIT chart transition near a fixed point.
Here s will be a fixed stabilizer element, not a parameter-dependent choice. -/
def rightTranslateCoordinates (g h s : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) : PairModel block₁ block₂ :=
  factorCoordinates h (factorLift g x * s)

theorem rightTranslateCoordinates_smooth_at (g h s : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) (hx : factorLift g x * s ∈ factorSource h) :
    ContDiffAt ℝ ⊤ (rightTranslateCoordinates g h s) x := by
  have hx₁ : admissible (h.1.valᵀ * (chartInv g.1 x.1 * s.1.val)) := by
    have hh := hx.1
    change admissible (h.1.valᵀ * ((factorLift g x).1.val * s.1.val)) at hh
    simpa only [factorLift_left_val] using hh
  have hx₂ : admissible (h.2.valᵀ * (chartInv g.2 x.2 * s.2.val)) := by
    have hh := hx.2
    change admissible (h.2.valᵀ * ((factorLift g x).2.val * s.2.val)) at hh
    simpa only [factorLift_right_val] using hh
  have hL : ContDiffAt ℝ ⊤ (fun y : PairModel block₁ block₂ =>
      chartMap h.1 (chartInv g.1 y.1 * s.1.val)) x := by
    have hm : ContDiffAt ℝ ⊤ (fun y : PairModel block₁ block₂ =>
        chartInv g.1 y.1 * s.1.val) x :=
      smooth_mul_at ((chartInv_smooth g.1).contDiffAt.comp x contDiffAt_fst)
        contDiffAt_const
    exact ContDiffAt.comp (f := fun y : PairModel block₁ block₂ =>
      chartInv g.1 y.1 * s.1.val) (g := chartMap h.1) x
      (chartMap_smooth_at h.1 _ hx₁) hm
  have hR : ContDiffAt ℝ ⊤ (fun y : PairModel block₁ block₂ =>
      chartMap h.2 (chartInv g.2 y.2 * s.2.val)) x := by
    have hm : ContDiffAt ℝ ⊤ (fun y : PairModel block₁ block₂ =>
        chartInv g.2 y.2 * s.2.val) x :=
      smooth_mul_at ((chartInv_smooth g.2).contDiffAt.comp x contDiffAt_snd)
        contDiffAt_const
    exact ContDiffAt.comp (f := fun y : PairModel block₁ block₂ =>
      chartInv g.2 y.2 * s.2.val) (g := chartMap h.2) x
      (chartMap_smooth_at h.2 _ hx₂) hm
  change ContDiffAt ℝ ⊤ (fun y : PairModel block₁ block₂ =>
    (chartMap h.1 ((factorLift g y).1.val * s.1.val),
      chartMap h.2 ((factorLift g y).2.val * s.2.val))) x
  simpa only [factorLift_left_val, factorLift_right_val] using hL.prodMk hR

/-- Matrix-smooth inverse parametrization on the ENTIRE model; the source
restriction used for an orbit chart is solely for injectivity. -/
theorem orbitParam_smooth (g : FactorGroup block₁ block₂) (P : Mat n) :
    ContDiff ℝ ⊤ (orbitParam g P) := by
  exact contDiff_iff_contDiffAt.mpr (fun x => orbitParam_smooth_at g P x
    ⟨admissible_model x.1, admissible_model x.2⟩)

end GS.ManifoldCompletion
