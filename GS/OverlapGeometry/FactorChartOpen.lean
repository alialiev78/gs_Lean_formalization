module

public import GS.ManifoldCompletion.FactorCoordinates

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Openness of factor charts and horizontal slice images

The inverse Cayley chart is an open map on the whole supported-skew model.
The final lemma transfers openness through a local product chart whenever its
second coordinate leaves the projected image unchanged. It is used for the
horizontal/stabilizer decomposition of an orbit with overlap.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.ManifoldCompletion Set

namespace GS.OverlapGeometry

variable {n : ℕ} {block block₁ block₂ : Fin n → ℕ}

/-- All supported skew matrices are in the inverse Cayley chart's domain;
consequently its total inverse is an open map. -/
theorem blockChartInverse_isOpenMap (Q : BlockO block) :
    IsOpenMap (blockChartInverse Q) := by
  intro U hU
  exact (blockPartialChart Q).isOpen_image_symm_of_subset_target hU
    (by simp only [blockPartialChart_target, parameterDomain_eq_univ, subset_univ])

/-- The full factor reconstruction is open, including in the presence of
arbitrary overlap between the two block partitions. -/
theorem factorLift_isOpenMap (g : FactorGroup block₁ block₂) :
    IsOpenMap (factorLift g) :=
  (blockChartInverse_isOpenMap g.1).prodMap (blockChartInverse_isOpenMap g.2)

theorem factorLift_mem_factorSource (g : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) : factorLift g x ∈ factorSource g := by
  exact ⟨(blockPartialChart g.1).map_target (by simp),
    (blockPartialChart g.2).map_target (by simp)⟩

theorem factorLift_range (g : FactorGroup block₁ block₂) :
    Set.range (factorLift g) = factorSource g := by
  ext h
  constructor
  · rintro ⟨x, rfl⟩
    exact factorLift_mem_factorSource g x
  · intro hh
    exact ⟨factorCoordinates g h, factorLift_factorCoordinates g h hh⟩

/-- The orbit map composed with factor reconstruction is open, even when the
factor-to-orbit map has a positive-dimensional kernel. -/
theorem factorLift_orbit_isOpenMap (g : FactorGroup block₁ block₂) (P : Mat n) :
    IsOpenMap (fun x : PairModel block₁ block₂ =>
      orbitMapToOrbit block₁ block₂ P (factorLift g x)) :=
  (orbitMapToOrbit_isOpenMap P).comp (factorLift_isOpenMap g)

/-- A local product chart descends to open slice images when the projection is
constant in the second coordinate. Only a representative above every point of
the first-coordinate domain is needed. -/
theorem isOpen_slice_image_of_productChart
    {H K M X : Type*} [TopologicalSpace H] [TopologicalSpace K]
    [TopologicalSpace M] [TopologicalSpace X]
    (e : OpenPartialHomeomorph (H × K) M) (q : M → X) (p : H → X)
    (hq : IsOpenMap q)
    (heq : ∀ z ∈ e.source, q (e z) = p z.1)
    (U : Set H) (hU : IsOpen U)
    (hcover : ∀ h ∈ U, ∃ k : K, (h, k) ∈ e.source) :
    IsOpen (p '' U) := by
  let V : Set (H × K) := e.source ∩ Prod.fst ⁻¹' U
  have hV : IsOpen V := e.open_source.inter (hU.preimage continuous_fst)
  have hopen : IsOpen (q '' (e '' V)) :=
    hq _ (e.isOpen_image_of_subset_source hV inter_subset_left)
  have himage : q '' (e '' V) = p '' U := by
    ext x
    constructor
    · rintro ⟨m, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z.1, hz.2, (heq z hz.1).symm⟩
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨k, hk⟩ := hcover h hh
      exact ⟨e (h, k), ⟨(h, k), ⟨hk, hh⟩, rfl⟩, heq (h, k) hk⟩
  rwa [himage] at hopen

end GS.OverlapGeometry
