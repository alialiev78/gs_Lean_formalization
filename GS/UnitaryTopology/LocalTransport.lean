module

public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import GS.UnitaryTopology.Nonmanifold
public import GS.UnitaryLocalModel.TopologyOuter
public import GS.UnitaryManifold.CayleyCharts

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Transport of the cone obstruction through actual local models

An arbitrary locally Euclidean outer factor can be absorbed into the free
coordinates of the rank-three-row model. Finite tuples of the actual unitary
block groups are locally Euclidean by the existing Cayley charts, with their
inherited matrix topology. The final transfer accepts a proved pointed open
or neighbourhood model; it introduces no nonmanifold hypothesis.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS GS.NonmanifoldFinal GS.NonmanifoldClosure GS.NonmanifoldObstruction
open GS.UnitaryManifold GS.UnitaryLocalModel
open scoped Topology
namespace GS.UnitaryTopology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

/-- A pointed open model can be multiplied by any unchanged topological factor. -/
def pointedOpenModel_prodRight {x : X} {y : Y}
    (g : PointedOpenModel X Y x y) (z : Z) :
    PointedOpenModel (X × Z) (Y × Z) (x,z) (y,z) where
  source := g.source ×ˢ Set.univ
  target := g.target ×ˢ Set.univ
  source_open := g.source_open.prod isOpen_univ
  target_open := g.target_open.prod isOpen_univ
  source_point := ⟨g.source_point,Set.mem_univ z⟩
  target_point := ⟨g.target_point,Set.mem_univ z⟩
  chart := (Homeomorph.Set.prod g.source Set.univ).trans
    ((g.chart.prodCongr (Homeomorph.refl _)).trans
      (Homeomorph.Set.prod g.target Set.univ).symm)
  map_point hx := by
    apply Prod.ext
    · exact g.map_point hx.1
    · rfl

/-- Center a genuine local Euclidean chart while retaining open source and target. -/
theorem exists_pointedEuclideanModel {x : X} (hx : EuclideanAt x) :
    ∃ n, Nonempty (PointedOpenModel X (Eucl n) x 0) := by
  obtain ⟨n,c,hc⟩ := (euclideanAt_iff_chart x).mp hx
  obtain ⟨b,_⟩ := exists_centeredChart c x hc
  refine ⟨n,⟨?_⟩⟩
  exact
  { source := b.source
    target := {z | ‖z‖ < b.radius}
    source_open := b.source_open
    target_open := isOpen_lt continuous_norm continuous_const
    source_point := b.source_point
    target_point := by simpa using b.radius_pos
    chart := b.chart
    map_point := b.map_point }

/-- Finite-dimensional real model coordinates are ordinary Euclidean coordinates. -/
theorem euclideanAt_of_finiteDimensional_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (c : OpenPartialHomeomorph X E) (x : X) (hx : x ∈ c.source) : EuclideanAt x := by
  let n := Module.finrank ℝ E
  let e : E ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  let h : E ≃ₜ Eucl n := e.toHomeomorph.trans
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph
  let p := c.trans h.toOpenPartialHomeomorph
  have hp : x ∈ p.source := ⟨hx,Set.mem_univ _⟩
  exact ⟨p.source,p.open_source,hp,n,p.target,p.open_target,
    ⟨p.toHomeomorphSourceTarget⟩⟩

/-- The finite product Cayley chart is on the original unitary tuple topology. -/
def blockUTuplePartialChart {ι : Type*} [Finite ι] {n : ℕ}
    {b : Fin n → ℕ} (a : ι → BlockU b) :
    OpenPartialHomeomorph (ι → BlockU b) (ι → Model b) :=
  OpenPartialHomeomorph.pi (fun i => blockPartialChart (a i))

theorem blockUTuple_mem_chart {ι : Type*} [Finite ι] {n : ℕ}
    {b : Fin n → ℕ} (a : ι → BlockU b) :
    a ∈ (blockUTuplePartialChart a).source := by
  intro i _
  exact base_mem_chartSource (a i)

theorem blockUTuple_euclideanAt {ι : Type*} [Fintype ι] {n : ℕ}
    {b : Fin n → ℕ} (a : ι → BlockU b) : EuclideanAt a :=
  euclideanAt_of_finiteDimensional_chart (blockUTuplePartialChart a) a
    (blockUTuple_mem_chart a)

/-- Independent left and right outer tuples require no quotient topology. -/
theorem blockUTuple_pair_euclideanAt {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n m : ℕ} {b : Fin n → ℕ} {c : Fin m → ℕ}
    (a : ι → BlockU b) (a' : κ → BlockU c) : EuclideanAt (a,a') :=
  euclideanAt_of_finiteDimensional_chart
    ((blockUTuplePartialChart a).prod (blockUTuplePartialChart a')) (a,a')
    ⟨blockUTuple_mem_chart a,blockUTuple_mem_chart a'⟩

theorem outerFactors_euclideanAt {q : ℕ} {o : Fin q}
    (a : OuterFactors q o) : EuclideanAt a :=
  blockUTuple_pair_euclideanAt a.1 a.2

/-- Pack the outer Euclidean coordinates and the unconstrained cone center. -/
def euclideanConeCoordinates (n d : ℕ) :
    (Eucl n × ConeCoordinates d) ≃ₜ
      ((Fin (n+d) → ℝ) × RankThreeCone (Fin d)) :=
  (((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.prodCongr
      (Homeomorph.refl (ConeCoordinates d))).trans
    (Homeomorph.prodAssoc _ _ _).symm).trans
      ((sumCoordinates.trans (reindexReal finSumFinEquiv)).prodCongr
        (Homeomorph.refl _))

@[simp] theorem euclideanConeCoordinates_zero (n d : ℕ) :
    euclideanConeCoordinates n d (0,coneCoordinatesZero d) = (0,rankThreeZero) := by
  apply Prod.ext
  · funext i
    change Sum.elim (0 : Fin n → ℝ) (0 : Fin d → ℝ) (finSumFinEquiv.symm i) = 0
    cases finSumFinEquiv.symm i <;> rfl
  · rfl

/-- Any genuinely locally Euclidean outer factor preserves the cone obstruction. -/
theorem outer_cone_not_euclidean {A : Type} [TopologicalSpace A]
    (a : A) (ha : EuclideanAt a) (d : ℕ) (hd : 0<d) (hdiv : 4∣d) :
    ¬ EuclideanAt (a,coneCoordinatesZero d) := by
  obtain ⟨n,⟨g⟩⟩ := exists_pointedEuclideanModel ha
  intro he
  have hmodel := (euclideanAt_pointedOpenModel
    (pointedOpenModel_prodRight g (coneCoordinatesZero d))).mp he
  have hflat := euclideanAt_of_homeomorph (euclideanConeCoordinates n d)
    (0,coneCoordinatesZero d) hmodel
  apply rankThreeProduct_not_euclidean_of_four_dvd (n+d) d hd hdiv
  simpa only [euclideanConeCoordinates_zero] using hflat

/-- Transfer through open neighbourhoods of the original full family. -/
theorem not_euclidean_of_outer_cone_openModel
    {F A : Type} [TopologicalSpace F] [TopologicalSpace A]
    {f : F} {a : A} (ha : EuclideanAt a) (d : ℕ) (hd : 0<d) (hdiv : 4∣d)
    (g : PointedOpenModel F (A × ConeCoordinates d) f (a,coneCoordinatesZero d)) :
    ¬ EuclideanAt f :=
  not_euclideanAt_of_pointedOpenModel g (outer_cone_not_euclidean a ha d hd hdiv)

/-- Compact neighbourhood images suffice: the existing interior restriction
produces actual open neighbourhoods before transporting the obstruction. -/
theorem not_euclidean_of_outer_cone_neighbourhoodModel
    {F A : Type} [TopologicalSpace F] [TopologicalSpace A]
    {f : F} {a : A} (ha : EuclideanAt a) (d : ℕ) (hd : 0<d) (hdiv : 4∣d)
    (g : GS.NonmanifoldCompletion.PointedNeighbourhoodModel
      F (A × ConeCoordinates d) f (a,coneCoordinatesZero d)) :
    ¬ EuclideanAt f :=
  not_euclidean_of_outer_cone_openModel ha d hd hdiv (pointedOpenModel g)

/-- Arithmetic specialization used by the unitary q-block local model. -/
theorem not_euclidean_of_outer_cone_neighbourhoodModel_odd
    {F A : Type} [TopologicalSpace F] [TopologicalSpace A]
    {f : F} {a : A} (ha : EuclideanAt a) (q : ℕ) (hq : 3≤q) (hodd : Odd q)
    (g : GS.NonmanifoldCompletion.PointedNeighbourhoodModel
      F (A × ConeCoordinates ((q-1)^2)) f (a,coneCoordinatesZero ((q-1)^2))) :
    ¬ EuclideanAt f := by
  apply not_euclidean_of_outer_cone_neighbourhoodModel ha ((q-1)^2) _ _ g
  · have : 0<q-1 := by omega
    positivity
  · obtain ⟨k,hk⟩ := hodd
    refine ⟨k^2,?_⟩
    have he : q-1=2*k := by omega
    rw [he]
    ring

/-- The concrete outer group used by the full unitary matrix model has already
been checked with its Cayley charts, so no outer-manifold premise remains. -/
theorem not_euclidean_of_unitary_cone_neighbourhoodModel_odd
    {F : Type} [TopologicalSpace F] {f : F}
    {q : ℕ} (o : Fin q) (a : OuterFactors q o) (hq : 3≤q) (hodd : Odd q)
    (g : GS.NonmanifoldCompletion.PointedNeighbourhoodModel
      F (OuterFactors q o × ConeCoordinates ((q-1)^2))
      f (a,coneCoordinatesZero ((q-1)^2))) :
    ¬ EuclideanAt f :=
  not_euclidean_of_outer_cone_neighbourhoodModel_odd
    (outerFactors_euclideanAt a) q hq hodd g

end GS.UnitaryTopology
