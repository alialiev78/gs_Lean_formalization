module

public import GS.UnitaryTopology.LocalTransport
public import GS.UnitaryLocalModel.TopologyNeighbourhood
public import GS.UnitaryLocalModel.TopologyFeasibility
public import GS.UnitaryLocalModel.FullCoverage
public import GS.Results.Nonmanifold
public import GS.Unitary.RealEmbedding

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Topological singularities of the original unitary three-factor family

The local model is proved for the complete scalar-indexed matrix family with
its inherited topology. The dephased chart, the compact quotient, feasibility,
and coverage of every nearby matrix are all instantiated. The topological
obstruction proved here applies to every odd q >= 3.
-/
noncomputable section
open GS GS.UnitaryManifold GS.UnitaryLocalModel GS.UnitaryGeometry
open GS.NonmanifoldFinal GS.NonmanifoldCompletion
open scoped Topology
namespace GS.UnitaryTopology

/-- The distinguished point, viewed inside the actual scalar-indexed family. -/
def unitaryFamilyBase {q : ℕ} (Q : FullUnitary q) (o : Fin q) :
    GS.UnitaryNonmanifold.localFamily q :=
  ⟨scalarBlockBase Q.val,scalarBlockBase_mem_localFamily Q.val Q.property.2 o⟩

/-- Positivity of the actual Euclidean dephased chart is the hypothesis needed
by the complete outer-factor fibre theorem. -/
theorem euclideanDephased_positiveAnchors {q : ℕ} (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    PositiveChartAnchors Q.val o (euclideanDephasedParametrization Q o hQ)
      (euclideanDephasedDomain Q o hQ) := by
  intro y hy
  exact (dephased_constraints_iff Q.val _ o).mp
    (dephasedParametrization_constraints Q o hQ _ hy)

/-- An actual neighbourhood homeomorphism for the whole original matrix family.
Neither a local-model assumption nor a restricted central slice appears here. -/
theorem unitary_matrix_pointed_neighbourhood_model {q : ℕ}
    (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) :
    Nonempty (PointedNeighbourhoodModel (GS.UnitaryNonmanifold.localFamily q)
      (OuterFactors q o × ConeCoordinates ((q-1)^2))
      (unitaryFamilyBase Q o) (identityOuter q o,coneCoordinatesZero ((q-1)^2))) := by
  let ψ := euclideanDephasedParametrization Q o hQ
  let U := euclideanDephasedDomain Q o hQ
  obtain ⟨r,hr,hargs⟩ := exists_parameterBox_in_chart U
    (euclideanDephasedDomain_open Q o hQ) (zero_mem_euclideanDephasedDomain Q o hQ)
  have hunit : ∀ y ∈ U, GS.Unitary (ψ y) := by
    intro y _
    exact dephasedParametrization_unitary Q o hQ _
  have hsub := fullCompactImage_subset_localFamily ψ o U hunit r hargs
  obtain ⟨W,hW,hbaseW,hcoverW⟩ := exists_open_full_compact_coverage Q o hQ r hr
  have hcover : fullCompactSource (GS.UnitaryNonmanifold.localFamily q) ψ o r ∈
      𝓝 (unitaryFamilyBase Q o) := by
    apply Filter.mem_of_superset
      ((hW.preimage continuous_subtype_val).mem_nhds hbaseW)
    intro M hM
    exact hcoverW M.val M.property hM
  exact full_compact_pointed_neighbourhood_model
    (GS.UnitaryNonmanifold.localFamily q) (unitaryFamilyBase Q o) Q.val o ψ U
    (euclideanDephasedParametrization_continuousOn Q o hQ)
    (euclideanDephasedParametrization_injectiveOn Q o hQ)
    (euclideanDephased_positiveAnchors Q o hQ) r hr hargs hsub hcover
    (fullParameterZero q ((q-1)^2) o r)
    (by simp [ψ,unitaryFamilyBase])
    (parameterCone_zero ((q-1)^2))

/-- A genuine topological obstruction for the full complex matrix family. -/
theorem unitary_gs_not_euclidean_at {q : ℕ} (hq : 3≤q) (hodd : Odd q)
    (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) :
    ¬ EuclideanAtSubset (GS.UnitaryNonmanifold.localFamily q) (scalarBlockBase Q.val) := by
  obtain ⟨g⟩ := unitary_matrix_pointed_neighbourhood_model Q o hQ
  have htop := not_euclidean_of_unitary_cone_neighbourhoodModel_odd
    o (identityOuter q o) hq hodd g
  intro he
  exact htop ((euclideanAtSubset_iff (GS.UnitaryNonmanifold.localFamily q)
    (scalarBlockBase Q.val) (unitaryFamilyBase Q o).property).mp he)

/-- The real Householder matrix is also an actual unitary matrix. -/
def unitaryReflection (q : ℕ) (hq : 3≤q) : FullUnitary q :=
  fullUnitary (ofRealMatrix (GS.Results.reflectionBase q))
    (ofRealMatrix_unitary (GS.Results.reflectionBase_orthogonal q (by omega)))

theorem unitaryReflection_entries_ne_zero (q : ℕ) (hq : 3≤q) (i j : Fin q) :
    (unitaryReflection q hq).val i j ≠ 0 := by
  change (GS.Results.reflectionBase q i j : ℂ) ≠ 0
  exact_mod_cast GS.Results.reflectionBase_entries_ne_zero q hq i j

theorem unitaryReflection_anchor (q : ℕ) (hq : 3≤q) (o : Fin q) :
    AnchorNonzero (unitaryReflection q hq).val (unitaryReflection q hq).val o := by
  constructor
  · intro i
    exact ⟨unitaryReflection_entries_ne_zero q hq i o,
      unitaryReflection_entries_ne_zero q hq i o⟩
  · intro j
    exact ⟨unitaryReflection_entries_ne_zero q hq o j,
      unitaryReflection_entries_ne_zero q hq o j⟩

/-- An explicit topologically singular matrix in every odd block count q>=3. -/
theorem unitaryReflection_nonEuclidean (q : ℕ) (hq : 3≤q) (hodd : Odd q) :
    scalarBlockBase (unitaryReflection q hq).val ∈ GS.UnitaryNonmanifold.localFamily q ∧
      ¬ EuclideanAtSubset (GS.UnitaryNonmanifold.localFamily q)
        (scalarBlockBase (unitaryReflection q hq).val) := by
  let o : Fin q := ⟨0,by omega⟩
  exact ⟨(unitaryFamilyBase (unitaryReflection q hq) o).property,
    unitary_gs_not_euclidean_at hq hodd (unitaryReflection q hq) o
      (unitaryReflection_anchor q hq o)⟩

theorem exists_unitary_nonEuclidean_point (q : ℕ) (hq : 3≤q) (hodd : Odd q) :
    ∃ M : CMat (q*2), M ∈ GS.UnitaryNonmanifold.localFamily q ∧
      ¬ EuclideanAtSubset (GS.UnitaryNonmanifold.localFamily q) M :=
  ⟨scalarBlockBase (unitaryReflection q hq).val,unitaryReflection_nonEuclidean q hq hodd⟩

end GS.UnitaryTopology
