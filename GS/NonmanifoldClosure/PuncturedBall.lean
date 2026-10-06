module

public import GS.Topology.SectionPair
public import GS.Topology.EuclideanSphere
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Explicit deformation of a punctured norm-ball to a unit sphere

The ambient real normed space may have dimension zero. No nonemptiness
assumption is used: in dimension zero both subtypes are empty.

The homotopy endpoints and the fixed-sphere identity are proved explicitly below.
-/
noncomputable section
open GS.NonmanifoldObstruction
open GS.NonmanifoldFinal
open scoped Topology
namespace GS.NonmanifoldClosure

abbrev NormSphere (E : Type*) [NormedAddCommGroup E] := {x : E // ‖x‖ = 1}
abbrev PuncturedNormBall (E : Type*) [NormedAddCommGroup E] (r : ℝ) :=
  {x : E // ‖x‖ < r ∧ x ≠ 0}

/-- Reconcile norm-equality subtypes with the actual mathlib `Metric.sphere`.
This homeomorphism uses no homology computation or homotopy invariance. -/
def normSphereStandard (n : ℕ) :
    NormSphere (EuclideanSpace ℝ (Fin n)) ≃ₜ UnitSphere (Fin n) :=
  Homeomorph.setCongr (by
    ext x
    change ‖x‖ = 1 ↔ dist x 0 = 1
    rw [dist_zero_right])

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial normalization. Its domain excludes only the origin. -/
def ballNormalize {r : ℝ} (x : PuncturedNormBall E r) : NormSphere E :=
  ⟨‖x.val‖⁻¹ • x.val, by
    have hp : 0 < ‖x.val‖ := norm_pos_iff.mpr x.property.2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    exact inv_mul_cancel₀ (ne_of_gt hp)⟩

def ballSection {r : ℝ} (hr : 0 < r) (v : NormSphere E) :
    PuncturedNormBall E r :=
  ⟨(r / 2) • v.val, by
    have hn : ‖(r / 2) • v.val‖ = r / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), v.property, mul_one]
    refine ⟨by rw [hn]; linarith, ?_⟩
    intro hz
    rw [hz, norm_zero] at hn
    linarith⟩

theorem continuous_ballNormalize (r : ℝ) :
    Continuous (@ballNormalize E _ _ r) := by
  apply Continuous.subtype_mk
  exact ((continuous_norm.comp continuous_subtype_val).inv₀
    (fun x => norm_ne_zero_iff.mpr x.property.2)).smul continuous_subtype_val

theorem continuous_ballSection {r : ℝ} (hr : 0 < r) :
    Continuous (ballSection (E := E) hr) :=
  (continuous_const.smul continuous_subtype_val).subtype_mk _

@[simp] theorem ballNormalize_section {r : ℝ} (hr : 0 < r) (v : NormSphere E) :
    ballNormalize (ballSection hr v) = v := by
  apply Subtype.ext
  have ht : 0 < r / 2 := by linarith
  change ‖(r / 2) • v.val‖⁻¹ • ((r / 2) • v.val) = v.val
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, v.property, mul_one,
    smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul]

@[simp] theorem norm_smul_ballNormalize {r : ℝ} (x : PuncturedNormBall E r) :
    ‖x.val‖ • (ballNormalize x).val = x.val := by
  change ‖x.val‖ • (‖x.val‖⁻¹ • x.val) = x.val
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr x.property.2), one_smul]

def ballSectionPair {r : ℝ} (hr : 0 < r) :
    ContinuousSectionPair (NormSphere E) (PuncturedNormBall E r) where
  sectionMap := ballSection hr
  retractionMap := ballNormalize
  section_continuous := continuous_ballSection hr
  retraction_continuous := continuous_ballNormalize r
  retraction_section := ballNormalize_section hr

/-- Convex interpolation of positive radii, not of arbitrary vectors. -/
def radialRadius {r : ℝ} (p : unitInterval × PuncturedNormBall E r) : ℝ :=
  (1 - (p.1 : ℝ)) * (r / 2) + (p.1 : ℝ) * ‖p.2.val‖

theorem radialRadius_pos {r : ℝ} (hr : 0 < r)
    (p : unitInterval × PuncturedNormBall E r) : 0 < radialRadius p := by
  have h0 := p.1.property.1
  have h1 := p.1.property.2
  have hx : 0 < ‖p.2.val‖ := norm_pos_iff.mpr p.2.property.2
  have ha : 0 ≤ (1 - (p.1 : ℝ)) * (r / 2) :=
    mul_nonneg (by linarith) (by linarith)
  by_cases ht : (p.1 : ℝ) = 0
  · simp [radialRadius, ht]; linarith
  · have hp : 0 < (p.1 : ℝ) * ‖p.2.val‖ :=
      mul_pos (by rcases lt_or_eq_of_le h0 with h | h; exact h; exact (ht h.symm).elim) hx
    dsimp [radialRadius]
    linarith

theorem radialRadius_lt {r : ℝ} (hr : 0 < r)
    (p : unitInterval × PuncturedNormBall E r) : radialRadius p < r := by
  have h0 := p.1.property.1
  have h1 := p.1.property.2
  have hx := p.2.property.1
  by_cases ht : (p.1 : ℝ) = 1
  · simpa [radialRadius, ht] using hx
  · have ht' : (p.1 : ℝ) < 1 := by
      rcases lt_or_eq_of_le h1 with h | h
      · exact h
      · exact (ht h).elim
    have ha : 0 < (1 - (p.1 : ℝ)) * (r / 2) :=
      mul_pos (by linarith) (by linarith)
    have hb : 0 ≤ (p.1 : ℝ) * (r - ‖p.2.val‖) :=
      mul_nonneg h0 (by linarith)
    dsimp [radialRadius]
    nlinarith

def radialDeform {r : ℝ} (hr : 0 < r)
    (p : unitInterval × PuncturedNormBall E r) : PuncturedNormBall E r :=
  ⟨radialRadius p • (ballNormalize p.2).val, by
    have hn : ‖radialRadius p • (ballNormalize p.2).val‖ = radialRadius p := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (radialRadius_pos hr p),
        (ballNormalize p.2).property, mul_one]
    refine ⟨by rw [hn]; exact radialRadius_lt hr p, ?_⟩
    intro hz
    rw [hz, norm_zero] at hn
    linarith [radialRadius_pos hr p]⟩

theorem continuous_radialDeform {r : ℝ} (hr : 0 < r) :
    Continuous (radialDeform (E := E) hr) := by
  apply Continuous.subtype_mk
  have hρ : Continuous (radialRadius : unitInterval × PuncturedNormBall E r → ℝ) := by
    unfold radialRadius
    fun_prop
  exact hρ.smul (continuous_subtype_val.comp
    ((continuous_ballNormalize r).comp continuous_snd))

/-- Normalization followed by the section is homotopic to the identity on the
punctured ball. Together with ballNormalize_section this is a homotopy equivalence. -/
def puncturedBallHomotopy {r : ℝ} (hr : 0 < r) :
    ContinuousMap.Homotopy
      (⟨fun x => ballSection hr (ballNormalize x),
        (continuous_ballSection hr).comp (continuous_ballNormalize r)⟩ :
          C(PuncturedNormBall E r, PuncturedNormBall E r))
      (ContinuousMap.id (PuncturedNormBall E r)) where
  toFun := radialDeform hr
  continuous_toFun := continuous_radialDeform hr
  map_zero_left x := by
    apply Subtype.ext
    simp [radialDeform, radialRadius, ballSection]
  map_one_left x := by
    apply Subtype.ext
    simpa [radialDeform, radialRadius] using norm_smul_ballNormalize x

/-- The deformation fixes the radius-r/2 sphere pointwise. -/
theorem radialDeform_section {r : ℝ} (hr : 0 < r)
    (t : unitInterval) (v : NormSphere E) :
    radialDeform hr (t, ballSection hr v) = ballSection hr v := by
  apply Subtype.ext
  have hn : ‖(ballSection hr v).val‖ = r / 2 := by
    change ‖(r / 2) • v.val‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), v.property, mul_one]
  change radialRadius (t, ballSection hr v) • (ballNormalize (ballSection hr v)).val = _
  rw [ballNormalize_section]
  have hh : radialRadius (t, ballSection hr v) = r / 2 := by
    dsimp [radialRadius]
    rw [hn]
    ring
  rw [hh]
  rfl

end GS.NonmanifoldClosure
