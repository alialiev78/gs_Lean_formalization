module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Curve velocities obstruct differentiable embedded charts

For a subset of a real normed space, a local ambient retraction differentiable
at the base point forces its actual curve velocities to be closed under
addition. We also construct such a retraction from the conventional ambient
flattening chart onto a coordinate subspace. Consequently nonadditive curve
velocities exclude every embedded `C1` chart. No claim about an arbitrary
abstract topological manifold structure is made.
-/

noncomputable section
open Filter
open scoped Topology

namespace GS.UnitaryNonmanifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An actual derivative of an ambient curve locally lying in the subset. -/
def CurveVelocity (S : Set E) (x v : E) : Prop :=
  ∃ f : ℝ → E, f 0 = x ∧ HasDerivAt f v 0 ∧
    ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ S

theorem CurveVelocity.mem {S : Set E} {x v : E}
    (hv : CurveVelocity S x v) : x ∈ S := by
  obtain ⟨f, hf0, _, hfS⟩ := hv
  have h : (0 : ℝ) ∈ {t : ℝ | f t ∈ S} := mem_of_mem_nhds hfS
  change f 0 ∈ S at h
  simpa only [hf0] using h

/-- A local retraction fixes the derivative of every actual feasible curve. -/
theorem CurveVelocity.retraction_fderiv {S : Set E} {x v : E}
    (hv : CurveVelocity S x v) (R : E → E)
    (hlocal : ∀ᶠ y in 𝓝 x, R y ∈ S ∧ (y ∈ S → R y = y))
    (hR : DifferentiableAt ℝ R x) : fderiv ℝ R x v = v := by
  obtain ⟨f, hf0, hfv, hfS⟩ := hv
  have ht : Tendsto f (𝓝 (0 : ℝ)) (𝓝 x) := by
    simpa only [ContinuousAt, hf0] using hfv.continuousAt
  have heq : (fun t => R (f t)) =ᶠ[𝓝 (0 : ℝ)] f := by
    filter_upwards [ht.eventually hlocal, hfS] with t ht hmem
    exact ht.2 hmem
  have hcomp : HasDerivAt (fun t => R (f t)) (fderiv ℝ R x v) 0 :=
    hR.hasFDerivAt.comp_hasDerivAt_of_eq 0 hfv hf0.symm
  exact (hcomp.congr_of_eventuallyEq heq.symm).unique hfv

/-- Differentiable local retractions force additivity of curve velocities. -/
theorem curveVelocity_add_of_local_retraction {S : Set E} {x v w : E}
    (hv : CurveVelocity S x v) (hw : CurveVelocity S x w)
    (R : E → E)
    (hlocal : ∀ᶠ y in 𝓝 x, R y ∈ S ∧ (y ∈ S → R y = y))
    (hR : DifferentiableAt ℝ R x) : CurveVelocity S x (v + w) := by
  have hRx : R x = x := (mem_of_mem_nhds hlocal).2 hv.mem
  have hline : HasDerivAt (fun t : ℝ => x + t • (v + w)) (v + w) 0 := by
    simpa only [zero_add, one_smul, id_eq, Pi.add_apply, Pi.add_def] using
      (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const (v + w))
  have hsum : fderiv ℝ R x (v + w) = v + w := by
    rw [map_add, hv.retraction_fderiv R hlocal hR,
      hw.retraction_fderiv R hlocal hR]
  have hcomp : HasDerivAt (fun t : ℝ => R (x + t • (v + w)))
      (v + w) 0 := by
    simpa only [hsum, Function.comp_def] using
      hR.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have ht : Tendsto (fun t : ℝ => x + t • (v + w))
      (𝓝 (0 : ℝ)) (𝓝 x) := by
    simpa only [ContinuousAt, zero_smul, add_zero] using hline.continuousAt
  exact ⟨fun t => R (x + t • (v + w)), by simpa using hRx, hcomp,
    (ht.eventually hlocal).mono (fun _ h => h.1)⟩

theorem no_differentiable_local_retraction {S : Set E} {x v w : E}
    (hv : CurveVelocity S x v) (hw : CurveVelocity S x w)
    (hsum : ¬ CurveVelocity S x (v + w)) (R : E → E)
    (hlocal : ∀ᶠ y in 𝓝 x, R y ∈ S ∧ (y ∈ S → R y = y)) :
    ¬ DifferentiableAt ℝ R x := by
  intro hR
  exact hsum (curveVelocity_add_of_local_retraction hv hw R hlocal hR)

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A homogeneous closed constraint on linear coordinates also constrains
every actual curve velocity where those coordinates vanish. This applies to
polynomial conditions of any degree, including commutation of block Grams. -/
theorem CurveVelocity.linear_image_mem_of_closed_cone
    {S : Set E} {x v : E} (hv : CurveVelocity S x v)
    (L : E →L[ℝ] F) (C : Set F) (hclosed : IsClosed C)
    (hscale : ∀ (a : ℝ) y, y ∈ C → a • y ∈ C)
    (hS : ∀ y ∈ S, L y ∈ C) (hzero : L x = 0) : L v ∈ C := by
  obtain ⟨f, hf0, hfv, hfS⟩ := hv
  have hder : HasDerivAt (fun t => L (f t)) (L v) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 hfv
  have hbase : L (f 0) = 0 := by rw [hf0, hzero]
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • L (f t))
      (𝓝[≠] (0 : ℝ)) (𝓝 (L v)) := by
    simpa only [zero_add, hbase, sub_zero] using hder.tendsto_slope_zero
  have hmem : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t⁻¹ • L (f t) ∈ C := by
    filter_upwards [hfS.filter_mono nhdsWithin_le_nhds] with t ht
    exact hscale t⁻¹ _ (hS _ ht)
  exact hclosed.mem_of_tendsto hlim hmem

/-- The ambient chart condition for an embedded submanifold, weakened to
differentiability of both coordinate changes at the base point alone. Thus
excluding this condition excludes, in particular, every usual `C1` chart. -/
def HasLocalDifferentiableFlattening (S : Set E) (x : E) : Prop :=
  ∃ e : OpenPartialHomeomorph E (F × G), x ∈ e.source ∧
    (∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) ∧
    DifferentiableAt ℝ e x ∧ DifferentiableAt ℝ e.symm (e x)

/-- Flattening a subset and projecting onto the first coordinate produces an
actual local retraction. The construction needs no inverse-function theorem. -/
theorem exists_local_retraction_of_flattening {S : Set E} {x : E}
    (hx : x ∈ S) (hchart : HasLocalDifferentiableFlattening (F := F) (G := G) S x) :
    ∃ R : E → E, DifferentiableAt ℝ R x ∧
      ∀ᶠ y in 𝓝 x, R y ∈ S ∧ (y ∈ S → R y = y) := by
  obtain ⟨e, hxs, hflat, he, heinv⟩ := hchart
  have hzero : (e x).2 = 0 := (hflat x hxs).mp hx
  let p : E → F × G := fun y => ((e y).1, 0)
  have hpx : p x = e x := by
    apply Prod.ext
    · rfl
    · exact hzero.symm
  have hp : DifferentiableAt ℝ p x :=
    he.fst.prodMk (differentiableAt_const (0 : G))
  have hp_target : ∀ᶠ y in 𝓝 x, p y ∈ e.target := by
    have ht : Tendsto p (𝓝 x) (𝓝 (e x)) := by
      simpa only [ContinuousAt, hpx] using hp.continuousAt
    exact ht.eventually (e.open_target.mem_nhds (e.map_source hxs))
  refine ⟨fun y => e.symm (p y), ?_, ?_⟩
  · exact (hpx.symm ▸ heinv).comp x hp
  · filter_upwards [e.open_source.mem_nhds hxs, hp_target] with y hys hpy
    constructor
    · apply (hflat _ (e.map_target hpy)).mpr
      rw [e.right_inv hpy]
    · intro hy
      have hpy_eq : p y = e y := by
        apply Prod.ext
        · rfl
        · exact ((hflat y hys).mp hy).symm
      rw [hpy_eq, e.left_inv hys]

/-- Nonadditive actual velocities rule out every local embedded `C1` chart,
for arbitrary choices of tangent and normal coordinate spaces. -/
theorem no_local_differentiable_flattening {S : Set E} {x v w : E}
    (hv : CurveVelocity S x v) (hw : CurveVelocity S x w)
    (hsum : ¬ CurveVelocity S x (v + w)) :
    ¬ HasLocalDifferentiableFlattening (F := F) (G := G) S x := by
  intro hchart
  obtain ⟨R, hR, hlocal⟩ := exists_local_retraction_of_flattening hv.mem hchart
  exact no_differentiable_local_retraction hv hw hsum R hlocal hR

end GS.UnitaryNonmanifold
