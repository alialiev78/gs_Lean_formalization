module

public import GS.RiemannianCompletion.Gradient
public import Mathlib.Analysis.Calculus.FDeriv.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Smooth compatible Frobenius coefficients in every orbit chart

These are the actual derivatives of the previously constructed inverse charts.
No regularity of the arbitrarily chosen preferredFactor is assumed. The metric
in an arbitrary chart is obtained by differentiating that chart's smooth matrix
reconstruction; compatibility is proved by differentiating the true transition
identity. Positivity at every point of every chart follows by comparison with
a preferred chart centred at the same matrix.

This file supplies coordinate-level metric regularity. Global smoothness on
the actual tangent bundle is proved in `GS.GlobalGeometry.TangentBundleMetric`.
No identification of chordal and intrinsic distances is asserted.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.ManifoldCompletion Filter Set
open scoped Topology Manifold
namespace GS.RiemannianCompletion
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n))
variable [hno : Fact (NoOffDiagonalOverlap block₁ block₂ σ)]

/-- Actual coordinate change; its extension outside the overlap is not used. -/
def coordinateTransition (g h : FactorGroup block₁ block₂) (x : PairModel block₁ block₂) :=
  orbitCoordinates σ hno.out h (orbitInverse σ g x)

def coordinateOverlap (g h : FactorGroup block₁ block₂) : Set (PairModel block₁ block₂) :=
  {x | x ∈ orbitParameterTarget g ∧ orbitInverse σ g x ∈ orbitChartSource σ h}

theorem coordinateOverlap_open (g h : FactorGroup block₁ block₂) :
    IsOpen (coordinateOverlap σ g h) :=
  (orbitParameterTarget_open g).inter
    ((orbitChartSource_open σ h).preimage (continuous_orbitInverse σ g))

theorem coordinateTransition_smooth (g h : FactorGroup block₁ block₂) :
    ContDiffOn ℝ ⊤ (coordinateTransition σ g h) (coordinateOverlap σ g h) := by
  exact orbitPartialChart_transition_smooth σ hno.out g h

theorem coordinateTransition_differentiable (g h : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) (hx : x ∈ coordinateOverlap σ g h) :
    DifferentiableAt ℝ (coordinateTransition σ g h) x := by
  exact ((coordinateTransition_smooth σ g h x hx).contDiffAt
    ((coordinateOverlap_open σ g h).mem_nhds hx)).differentiableAt (by simp)

theorem coordinateTransition_reconstruct (g h : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) (hx : x ∈ coordinateOverlap σ g h) :
    orbitInverse σ h (coordinateTransition σ g h x) = orbitInverse σ g x :=
  orbitInverse_coordinates σ hno.out h _ hx.2

theorem coordinateTransition_mem_reverse (g h : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) (hx : x ∈ coordinateOverlap σ g h) :
    coordinateTransition σ g h x ∈ coordinateOverlap σ h g := by
  refine ⟨orbitCoordinates_mem_target σ hno.out h _ hx.2, ?_⟩
  rw [coordinateTransition_reconstruct σ g h x hx]
  exact orbitInverse_mem_source σ hno.out g x hx.1

theorem coordinateTransition_inverse (g h : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) (hx : x ∈ coordinateOverlap σ g h) :
    coordinateTransition σ h g (coordinateTransition σ g h x) = x := by
  unfold coordinateTransition
  rw [orbitInverse_coordinates σ hno.out h _ hx.2,
    orbitCoordinates_inverse σ hno.out g x hx.1]

/-- Differentiate the actual inverse law on the open overlap. -/
theorem coordinateTransition_fderiv_leftInverse (g h : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) (hx : x ∈ coordinateOverlap σ g h) :
    (fderiv ℝ (coordinateTransition σ h g) (coordinateTransition σ g h x)).comp
      (fderiv ℝ (coordinateTransition σ g h) x) =
        ContinuousLinearMap.id ℝ (PairModel block₁ block₂) := by
  have ht := coordinateTransition_differentiable σ g h x hx
  have hs := coordinateTransition_differentiable σ h g _
    (coordinateTransition_mem_reverse σ g h x hx)
  have hd := hs.hasFDerivAt.comp x ht.hasFDerivAt
  have he : (fun y => coordinateTransition σ h g (coordinateTransition σ g h y))
      =ᶠ[𝓝 x] (fun y : PairModel block₁ block₂ => y) := by
    filter_upwards [(coordinateOverlap_open σ g h).mem_nhds hx] with y hy
    exact coordinateTransition_inverse σ g h y hy
  have hid := (hasFDerivAt_id (𝕜 := ℝ) x).congr_of_eventuallyEq he
  exact hd.unique hid

theorem coordinateTransition_fderiv_injective (g h : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) (hx : x ∈ coordinateOverlap σ g h) :
    Function.Injective (fderiv ℝ (coordinateTransition σ g h) x) := by
  intro v w he
  have hv := congrArg (fun L : PairModel block₁ block₂ →L[ℝ] PairModel block₁ block₂ => L v)
    (coordinateTransition_fderiv_leftInverse σ g h x hx)
  have hw := congrArg (fun L : PairModel block₁ block₂ →L[ℝ] PairModel block₁ block₂ => L w)
    (coordinateTransition_fderiv_leftInverse σ g h x hx)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hv hw
  exact hv.symm.trans ((congrArg _ he).trans hw)

/-- The chain rule for coordinate representations of the SAME included matrix. -/
theorem chart_reconstruction_fderiv_transition (g h : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) (hx : x ∈ coordinateOverlap σ g h) :
    fderiv ℝ (orbitParam g (permMatrix σ)) x =
      (fderiv ℝ (orbitParam h (permMatrix σ)) (coordinateTransition σ g h x)).comp
        (fderiv ℝ (coordinateTransition σ g h) x) := by
  have hp := ((orbitParam_smooth h (permMatrix σ)).differentiable (by simp)
    (coordinateTransition σ g h x)).hasFDerivAt
  have ht := (coordinateTransition_differentiable σ g h x hx).hasFDerivAt
  have hd := hp.comp x ht
  have he : (fun y => orbitParam h (permMatrix σ) (coordinateTransition σ g h y))
      =ᶠ[𝓝 x] orbitParam g (permMatrix σ) := by
    filter_upwards [(coordinateOverlap_open σ g h).mem_nhds hx] with y hy
    simpa only [orbitInverse_val] using
      congrArg Subtype.val (coordinateTransition_reconstruct σ g h y hy)
  exact (hd.congr_of_eventuallyEq he.symm).fderiv

/-- Injectivity away from chart centres is derived, not silently assumed. -/
theorem chart_reconstruction_fderiv_injective (g : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) (hx : x ∈ orbitParameterTarget g) :
    Function.Injective (fderiv ℝ (orbitParam g (permMatrix σ)) x) := by
  let X := orbitInverse σ g x
  let h := preferredFactor σ X
  have hbase : X ∈ orbitChartSource σ h := by
    change X ∈ (chartAt (PairModel block₁ block₂) X).source
    exact mem_chart_source _ _
  have ho : x ∈ coordinateOverlap σ g h := ⟨hx, hbase⟩
  have hz : coordinateTransition σ g h x = 0 := orbitCoordinates_preferred σ X
  rw [chart_reconstruction_fderiv_transition σ g h x ho, hz]
  exact (orbitParam_fderiv_zero_injective σ hno.out h).comp
    (coordinateTransition_fderiv_injective σ g h x ho)

/-- Coordinate expression of the pullback Frobenius metric. -/
def chartPairing (g : FactorGroup block₁ block₂) (P : Mat n)
    (x v w : PairModel block₁ block₂) : ℝ :=
  frobInner (fderiv ℝ (orbitParam g P) x v) (fderiv ℝ (orbitParam g P) x w)

theorem chartPairing_smooth (g : FactorGroup block₁ block₂) (P : Mat n) :
    ContDiff ℝ ⊤ (fun t : PairModel block₁ block₂ ×
      (PairModel block₁ block₂ × PairModel block₁ block₂) =>
        chartPairing g P t.1 t.2.1 t.2.2) := by
  have hd := smooth_fderiv_of_smooth (orbitParam g P) (orbitParam_smooth g P)
  have hdv : ContDiff ℝ ⊤ (fun t : PairModel block₁ block₂ ×
      (PairModel block₁ block₂ × PairModel block₁ block₂) =>
        fderiv ℝ (orbitParam g P) t.1 t.2.1) :=
    (hd.comp contDiff_fst).clm_apply (contDiff_fst.comp contDiff_snd)
  have hdw : ContDiff ℝ ⊤ (fun t : PairModel block₁ block₂ ×
      (PairModel block₁ block₂ × PairModel block₁ block₂) =>
        fderiv ℝ (orbitParam g P) t.1 t.2.2) :=
    (hd.comp contDiff_fst).clm_apply (contDiff_snd.comp contDiff_snd)
  unfold chartPairing frobInner
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact ((contDiff_apply_apply ℝ ℝ i j).comp hdv).mul
    ((contDiff_apply_apply ℝ ℝ i j).comp hdw)

theorem chartPairing_pos (g : FactorGroup block₁ block₂)
    (x v : PairModel block₁ block₂) (hx : x ∈ orbitParameterTarget g) (hv : v ≠ 0) :
    0 < chartPairing g (permMatrix σ) x v v := by
  apply frobSq_pos_of_ne_zero
  intro he
  apply hv
  apply chart_reconstruction_fderiv_injective σ g x hx
  simpa only [map_zero] using he

/-- Tensor transformation law on every overlap, for the actual chart derivative. -/
theorem chartPairing_transition (g h : FactorGroup block₁ block₂)
    (x v w : PairModel block₁ block₂) (hx : x ∈ coordinateOverlap σ g h) :
    chartPairing g (permMatrix σ) x v w =
      chartPairing h (permMatrix σ) (coordinateTransition σ g h x)
        (fderiv ℝ (coordinateTransition σ g h) x v)
        (fderiv ℝ (coordinateTransition σ g h) x w) := by
  unfold chartPairing
  rw [chart_reconstruction_fderiv_transition σ g h x hx]
  rfl

/-- Link chart coefficients to the actual tangent fiber at the same basepoint. -/
theorem chartPairing_eq_tangentPairing (g : FactorGroup block₁ block₂)
    (x v w : PairModel block₁ block₂) (hx : x ∈ orbitParameterTarget g) :
    let X := orbitInverse σ g x
    let h := preferredFactor σ X
    chartPairing g (permMatrix σ) x v w =
      tangentPairing σ X
        (fderiv ℝ (coordinateTransition σ g h) x v)
        (fderiv ℝ (coordinateTransition σ g h) x w) := by
  dsimp only
  let X := orbitInverse σ g x
  let h := preferredFactor σ X
  have hbase : X ∈ orbitChartSource σ h := by
    change X ∈ (chartAt (PairModel block₁ block₂) X).source
    exact mem_chart_source _ _
  have ho : x ∈ coordinateOverlap σ g h := ⟨hx, hbase⟩
  rw [chartPairing_transition σ g h x v w ho]
  have hz : coordinateTransition σ g h x = 0 := orbitCoordinates_preferred σ X
  rw [hz]
  unfold chartPairing tangentPairing inclusionDifferential
  rw [orbit_val_mfderiv_eq]
  rfl

end GS.RiemannianCompletion
