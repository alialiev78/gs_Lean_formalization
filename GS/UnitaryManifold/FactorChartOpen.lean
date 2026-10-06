module

public import GS.UnitaryManifold.Factors
public import GS.OverlapGeometry.FactorChartOpen

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
open Matrix GS GS.UnitaryGeometry GS.OverlapGeometry Set

namespace GS.UnitaryManifold

variable {n : ℕ} {block block₁ block₂ : Fin n → ℕ}

/-- All supported skew matrices are in the inverse Cayley chart's domain;
consequently its total inverse is an open map. -/
theorem blockChartInverse_isOpenMap (Q : BlockU block) :
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
theorem factorLift_orbit_isOpenMap (g : FactorGroup block₁ block₂) (P : CMat n) :
    IsOpenMap (fun x : PairModel block₁ block₂ =>
      orbitMapToOrbit block₁ block₂ P (factorLift g x)) :=
  (orbitMapToOrbit_isOpenMap P).comp (factorLift_isOpenMap g)

end GS.UnitaryManifold
