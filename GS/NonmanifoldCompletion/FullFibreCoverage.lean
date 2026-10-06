module

public import GS.NonmanifoldCompletion.FactorSpace
public import GS.NonmanifoldCompletion.OriginalCoordinates
public import GS.Continuation.CompactCoverageTools

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Coverage of an actual GS neighbourhood by the original compact parametrization

The proof normalizes EACH representative of the full compact fibre, using fixed
local diagonal gauges, local rotation angles, and genuine small logarithms.
It then applies compactness. No normalization or full-fibre coverage assumption
is exposed in the final theorem. The original scalarShuffle, localFamily,
originalF, and originalK definitions are retained.

This theorem supplies `OriginalLocalCoverageGoal` to the final nonmanifold
proof. 
-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation GS.Nonmanifold
open scoped Topology
namespace GS.NonmanifoldCompletion
attribute [local instance] Matrix.normedAddCommGroup

/-- Every full-fibre representative has a parameter neighbourhood whose image
is contained in originalF(K_eta). Gauges are chosen locally, not globally. -/
theorem factor_neighbourhood_in_original_image {q : ℕ} (hq : 0<q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j≠0)
    (η : ℝ) (hη : 0<η) (p : SmallBlockParameters q) (hp : p∈smallFactorSet q)
    (he : smallFactorMap p=basePoint Q₀) :
    ∃ N : Set (SmallBlockParameters q), IsOpen N ∧ p∈N ∧
      ∀ p'∈N, p'∈smallFactorSet q → smallFactorMap p' ∈ originalF Q₀ '' originalK q η := by
  rcases p with ⟨U,A,B,V⟩
  rcases hp with ⟨hU,hA,hB,hV⟩
  obtain ⟨S,D,E,hS,hD,hE,hleft,hright,hAg,hBg⟩ := normalize_scalar_base_fibre hq
    Q₀ A B hentries U V hU hV (smallFactorMap_eq_base_blocks Q₀ _ he)
  obtain ⟨L,hL,hQL,hlog⟩ := exists_open_frob_small_skew_log Q₀ hQ₀ η hη
  let N : Set (SmallBlockParameters q) := {p' |
    (∀ i, p'.1 i*D i*S ∈ rotationChartDomain (η/4)) ∧
    (∀ j, Sᵀ*E j*p'.2.2.2 j ∈ rotationChartDomain (η/4)) ∧
    gaugeMiddle D E 0 p'.2.1 ∈ L ∧ gaugeMiddle D E 1 p'.2.2.1 ∈ L}
  have hNU : IsOpen {p' : SmallBlockParameters q |
      ∀ i, p'.1 i*D i*S ∈ rotationChartDomain (η/4)} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite (fun i => (isOpen_rotationChartDomain (η/4)).preimage (by fun_prop))
  have hNV : IsOpen {p' : SmallBlockParameters q |
      ∀ j, Sᵀ*E j*p'.2.2.2 j ∈ rotationChartDomain (η/4)} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite (fun j => (isOpen_rotationChartDomain (η/4)).preimage (by fun_prop))
  have hNA : IsOpen {p' : SmallBlockParameters q | gaugeMiddle D E 0 p'.2.1 ∈ L} := by
    apply hL.preimage
    unfold gaugeMiddle
    fun_prop
  have hNB : IsOpen {p' : SmallBlockParameters q | gaugeMiddle D E 1 p'.2.2.1 ∈ L} := by
    apply hL.preimage
    unfold gaugeMiddle
    fun_prop
  have hN : IsOpen N := hNU.inter (hNV.inter (hNA.inter hNB))
  have hI : (1 : Mat 2) ∈ rotationChartDomain (η/4) := one_mem_rotationChartDomain (by positivity)
  have hpN : (U,A,B,V)∈N := by
    refine ⟨?_,?_,?_,?_⟩
    · intro i; simpa only [hleft] using hI
    · intro j; simpa only [hright] using hI
    · simpa only [hAg] using hQL
    · simpa only [hBg] using hQL
  refine ⟨N,hN,hpN,?_⟩
  rintro ⟨U',A',B',V'⟩ ⟨hUl,hVr,hAL,hBL⟩ ⟨hU',hA',hB',hV'⟩
  obtain ⟨p',hp',he'⟩ := original_coordinates_of_gauged_near hq Q₀ η hη L hlog
    S D E hS hD hE U' V' A' B' hU' hV' hA' hB' hUl hVr hAL hBL
  exact ⟨p',hp',he'⟩

/-- Compactness turns local image containment at EVERY point of a fibre into
image containment over an actual neighbourhood of its image point. -/
theorem compact_local_fibre_coverage
    {K X : Type*} [TopologicalSpace K] [TopologicalSpace X] [T2Space K] [T2Space X]
    (f : K → X) (hf : Continuous f) (s : Set K) (hs : IsCompact s)
    (x : X) (T : Set X)
    (hlocal : ∀ k∈s, f k=x → ∃ N : Set K, IsOpen N ∧ k∈N ∧
      ∀ k'∈N, k'∈s → f k'∈T) :
    ∃ W : Set X, IsOpen W ∧ x∈W ∧ ∀ y∈W, y∈f '' s → y∈T := by
  let opens : Set (Set K) := {N | IsOpen N ∧ ∀ k∈N, k∈s → f k∈T}
  let O : Set K := ⋃ N∈opens, N
  have hO : IsOpen O := isOpen_iUnion (fun N => isOpen_iUnion (fun hN => hN.1))
  have hfull : ∀ k∈s, f k=x → k∈O := by
    intro k hk he
    obtain ⟨N,hN,hkN,hmap⟩ := hlocal k hk he
    exact Set.mem_iUnion.mpr ⟨N,Set.mem_iUnion.mpr ⟨⟨hN,hmap⟩,hkN⟩⟩
  obtain ⟨W,hW,hx,hcover⟩ := compact_full_fibre_neighbourhood f hf s hs O hO x hfull
  refine ⟨W,hW,hx,?_⟩
  intro y hy himage
  obtain ⟨k,⟨hks,hkO⟩,he⟩ := hcover y hy himage
  obtain ⟨N,hkN⟩ := Set.mem_iUnion.mp hkO
  obtain ⟨hN,hkN⟩ := Set.mem_iUnion.mp hkN
  rw [← he]
  exact hN.2 k hkN hks

/-- FULL open-neighbourhood coverage for the unchanged original parametrization.
The determinant-one condition is unnecessary for this statement. -/
theorem exists_open_original_local_coverage {q : ℕ} (hq : 0<q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j≠0)
    (η : ℝ) (hη : 0<η) :
    ∃ W : Set (Mat (q*2)), IsOpen W ∧ basePoint Q₀∈W ∧
      ∀ M∈localFamily q, M∈W → ∃ p∈originalK q η, originalF Q₀ p=M := by
  obtain ⟨W,hW,hbase,hcover⟩ := compact_local_fibre_coverage (@smallFactorMap q)
    (continuous_smallFactorMap q) (smallFactorSet q) (isCompact_smallFactorSet q)
    (basePoint Q₀) (originalF Q₀ '' originalK q η)
    (factor_neighbourhood_in_original_image hq Q₀ hQ₀ hentries η hη)
  refine ⟨W,hW,hbase,?_⟩
  intro M hM hMW
  have himage : M∈(@smallFactorMap q) '' smallFactorSet q := by
    simpa only [image_smallFactorMap] using hM
  exact hcover M hMW himage

/-- Frobenius-ball form, exactly matching the original requested coverage. -/
theorem original_local_coverage {q : ℕ} (hq : 0<q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j≠0)
    (η : ℝ) (hη : 0<η) :
    ∃ ε : ℝ, 0<ε ∧ ∀ M∈localFamily q,
      frobDistSq M (basePoint Q₀)<ε^2 →
        ∃ p∈originalK q η, originalF Q₀ p=M := by
  obtain ⟨W,hW,hbase,hcover⟩ := exists_open_original_local_coverage hq Q₀ hQ₀ hentries η hη
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hW (basePoint Q₀) hbase
  refine ⟨δ/2,by positivity,?_⟩
  intro M hM hdist
  apply hcover M hM
  apply hball
  change dist M (basePoint Q₀)<δ
  rw [dist_eq_norm]
  have hn : ‖M-basePoint Q₀‖ ≤ δ/2 :=
    matrix_norm_le_of_frobSq_le (by positivity : 0≤δ/2) hdist.le
  linarith

/-- A proof script for the pre-existing specification, not a replacement goal.
Kernel validation of this declaration and its dependencies is still required. -/
theorem originalLocalCoverage : GS.Specifications.OriginalLocalCoverageGoal := by
  intro q hq Q₀ hQ₀ _hdet hentries η hη
  exact original_local_coverage (by omega) Q₀ hQ₀ hentries η hη

end GS.NonmanifoldCompletion
