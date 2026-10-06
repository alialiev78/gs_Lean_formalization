module

public import GS.UnitaryLocalModel.DephasedEuclidean
public import GS.UnitaryLocalModel.FactorDephasing
public import GS.UnitaryLocalModel.TopologyOuter
public import GS.UnitaryLocalModel.AxisConjugation

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Small coordinate neighbourhoods and full factor normalization

The inverse dephased chart supplies genuinely small coordinates for both
middle factors. Their midpoint and half-difference belong to the compact
parameter box, and anchor normalization gives the exact full matrix image.
-/
noncomputable section
open Matrix GS GS.UnitaryNonmanifold Set
open scoped Topology BigOperators
namespace GS.UnitaryLocalModel
variable {q : ℕ}

private theorem midpoint_energy_le {d : ℕ} (a b : Fin d → ℝ) :
    localEnergy (fun i => (a i+b i)/2) ≤ (localEnergy a+localEnergy b)/2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    show ((a i+b i)/2)^2 ≤ ((a i)^2+(b i)^2)/2 by nlinarith [sq_nonneg (a i-b i)])
  simpa only [localEnergy, ← Finset.sum_div, Finset.sum_add_distrib] using h

private theorem half_difference_energy_le {d : ℕ} (a b : Fin d → ℝ) :
    localEnergy (fun i => (a i-b i)/2) ≤ (localEnergy a+localEnergy b)/2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    show ((a i-b i)/2)^2 ≤ ((a i)^2+(b i)^2)/2 by nlinarith [sq_nonneg (a i+b i)])
  simpa only [localEnergy, ← Finset.sum_div, Finset.sum_add_distrib] using h

@[simp] theorem euclideanDephasedCoordinates_base (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    euclideanDephasedCoordinates Q o hQ (dephasedBase Q o hQ) = 0 := by
  simp [euclideanDephasedCoordinates, dephasedCoordinates, dephasedBase,
    unitaryConstraintChart_base]

def smallDephasedSource (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) : Set (DephasedUnitary Q o) :=
  {A | A ∈ dephasedChartSource Q o hQ ∧
    localEnergy (euclideanDephasedCoordinates Q o hQ A) < r^2}

theorem smallDephasedSource_open (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) : IsOpen (smallDephasedSource Q o hQ r) := by
  have hc : Continuous (fun A : dephasedChartSource Q o hQ =>
      euclideanDephasedCoordinates Q o hQ A.val) :=
    continuous_subtype_val.comp (euclideanDephasedChartHomeomorph Q o hQ).continuous
  have he : smallDephasedSource Q o hQ r = Subtype.val ''
      {A : dephasedChartSource Q o hQ |
        localEnergy (euclideanDephasedCoordinates Q o hQ A.val) < r^2} := by
    ext A
    simp only [smallDephasedSource, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hA, he⟩; exact ⟨⟨A,hA⟩,he,rfl⟩
    · rintro ⟨A,he,rfl⟩; exact ⟨A.property,he⟩
  rw [he]
  exact (dephasedChartSource_open Q o hQ).isOpenMap_subtype_val _
    (isOpen_lt ((continuous_localEnergy _).comp hc) continuous_const)

theorem base_mem_smallDephasedSource (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) (hr : 0<r) :
    dephasedBase Q o hQ ∈ smallDephasedSource Q o hQ r := by
  refine ⟨base_mem_dephasedChartSource Q o hQ, ?_⟩
  simpa [euclideanDephasedCoordinates_base, localEnergy] using sq_pos_of_pos hr

/-- All anchor-good factors with sufficiently small dephased inverse coordinates. -/
def smallAnchorFactors (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) : Set (anchorFactorSet Q o) :=
  {p | dephasedFirst Q o p ∈ smallDephasedSource Q o hQ r ∧
    dephasedSecond Q o p ∈ smallDephasedSource Q o hQ r}

def smallFullFactors (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) : Set (SmallFactorSpace q) :=
  Subtype.val '' smallAnchorFactors Q o hQ r

theorem smallFullFactors_open (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) : IsOpen (smallFullFactors Q o hQ r) := by
  apply (anchorFactorSet_open Q o).isOpenMap_subtype_val
  exact ((smallDephasedSource_open Q o hQ r).preimage (continuous_dephasedFirst Q o)).inter
    ((smallDephasedSource_open Q o hQ r).preimage (continuous_dephasedSecond Q o))

/-- The phase-normalized blocks reconstruct the original matrix exactly. -/
theorem smallFullFactors_map_mem (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) (p : SmallFactorSpace q)
    (hp : p ∈ smallFullFactors Q o hQ r) :
    smallFactorValue q p ∈ FullCompactImage (euclideanDephasedParametrization Q o hQ) o r := by
  obtain ⟨p,hp,rfl⟩ := hp
  let a := euclideanDephasedCoordinates Q o hQ (dephasedFirst Q o p)
  let b := euclideanDephasedCoordinates Q o hQ (dephasedSecond Q o p)
  let c : Fin ((q-1)^2) → ℝ := fun i => (a i+b i)/2
  let z : Fin ((q-1)^2) → ℝ := fun i => (a i-b i)/2
  have hca : c+z=a := by ext i; dsimp [c,z]; ring
  have hcb : c-z=b := by ext i; dsimp [c,z]; ring
  have ha : localEnergy a < r^2 := hp.1.2
  have hb : localEnergy b < r^2 := hp.2.2
  have hc : localEnergy c ≤ r^2 := (midpoint_energy_le a b).trans (by linarith)
  have hz : localEnergy z ≤ r^2 := (half_difference_energy_le a b).trans (by linarith)
  have hea := euclideanDephasedParametrization_coordinates Q o hQ
    (dephasedFirst Q o p) hp.1.1
  have heb := euclideanDephasedParametrization_coordinates Q o hQ
    (dephasedSecond Q o p) hp.2.1
  let U := p.val.val.1
  let V := p.val.val.2.2.2
  let A := p.val.val.2.1
  let B := p.val.val.2.2.1
  have hU : ∀ i, Unitary (U i) := p.val.property.1
  have hV : ∀ j, Unitary (V j) := p.val.property.2.2.2
  let L := phaseGaugeLeft U V Q.val A B o
  let R := phaseGaugeRight V Q.val A B o
  have hL : ∀ i, Unitary (L i) := phaseGaugeLeft_unitary U V Q.val A B o hU hV p.property.1 p.property.2
  have hR : ∀ j, Unitary (R j) := phaseGaugeRight_unitary V Q.val A B o hV p.property.1 p.property.2
  have hRo : R o=1 := phaseGaugeRight_anchor V Q.val A B o (hV o) p.property.1 p.property.2
  obtain ⟨u,hu,hdiag⟩ := exists_axis_of_unitary (V o) (hV o)
  let g : OuterFactors q o := outerOfMatrices L R hL hR
  let t : localParameterBox ((q-1)^2) r := ⟨(c,z,u),hc,hz,hu⟩
  refine ⟨(g,t),?_⟩
  apply (blockFamilyHomeomorph q).symm.injective
  change extractBlockFamily (fullCompactMiddle _ o r (g,t)) =
    extractBlockFamily (smallFactorValue q p.val)
  rw [fullCompactMiddle, fullBlockImage, extract_flattenBlockFamily]
  funext i j
  have hn := phase_normalization_block U V Q.val A B o i j (hU i) (hV j)
  have he : L i * middleBlock (dephase Q.val A o i j) (dephase Q.val B o i j) u * R j =
      U i * diagTwo (A i j) (B i j) * V j := by
    rw [← hdiag, ← hn]
    calc
      _ = (L i * (L i)ᴴ) * (U i * diagTwo (A i j) (B i j) * V j) *
          ((R j)ᴴ * R j) := by dsimp only [L,R]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [(hL i).2,(hR j).1]; simp
  have hright : outerRight g = R := outerRight_ofMatrices L R hL hR hRo
  rw [show outerLeft g = L from rfl, hright]
  have hmiddle : chartBlockFamily (euclideanDephasedParametrization Q o hQ) t.val i j =
      middleBlock (dephase Q.val A o i j) (dephase Q.val B o i j) u := by
    change middleBlock (euclideanDephasedParametrization Q o hQ (c+z) i j)
      (euclideanDephasedParametrization Q o hQ (c-z) i j) u = _
    rw [hca,hcb,hea,heb]
    rfl
  rw [hmiddle,he]
  ext k l
  exact (smallFactorMap_block p.val.val i j k l).symm

end GS.UnitaryLocalModel
