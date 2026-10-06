module

public import GS.UnitaryTopology.EuclideanRetract
public import GS.UnitaryTopology.QuaternionRetraction

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The Clifford retraction with arbitrary Euclidean factors

The singular zero-matrix stratum is retained. The sole deleted point is the
origin of the full product. The Euclidean projection has exactly that zero.
-/
noncomputable section
open Matrix GS GS.UnitaryLocalModel GS.NonmanifoldObstruction
open GS.NonmanifoldFinal GS.NonmanifoldClosure
open scoped Topology
namespace GS.UnitaryTopology

def pairCoordinatesEuclidean (e r : ℕ) :
    ((Fin e → ℝ) × (Fin r × Fin 4 → ℝ)) ≃ₜ Eucl (e+r*4) := by
  have hc : Fintype.card (Fin e ⊕ (Fin r × Fin 4)) = e+r*4 := by simp
  let eqv := (Fintype.equivFin (Fin e ⊕ (Fin r × Fin 4))).trans
    (Equiv.cast (congrArg Fin hc))
  exact (sumCoordinates.trans (reindexReal eqv)).trans
    (EuclideanSpace.equiv (Fin (e+r*4)) ℝ).symm.toHomeomorph

@[simp] theorem pairCoordinatesEuclidean_zero (e r : ℕ) :
    pairCoordinatesEuclidean e r (0,0) = 0 := by
  ext i
  simp [pairCoordinatesEuclidean,sumCoordinates,reindexReal]

def quaternionProductProjection (e r : ℕ)
    (p : (Fin e → ℝ) × RankThreeCone (Fin r × Fin 4)) :
    (Fin e → ℝ) × (Fin r × Fin 4 → ℝ) :=
  (p.1,quaternionContraction p.2.val)

def quaternionProductSection (e r : ℕ)
    (p : (Fin e → ℝ) × (Fin r × Fin 4 → ℝ)) :
    (Fin e → ℝ) × RankThreeCone (Fin r × Fin 4) :=
  (p.1,firstRowSection p.2)

theorem continuous_quaternionProductProjection (e r : ℕ) :
    Continuous (quaternionProductProjection e r) :=
  continuous_fst.prodMk ((continuous_quaternionContraction r).comp
    (continuous_subtype_val.comp continuous_snd))

theorem continuous_quaternionProductSection (e r : ℕ) :
    Continuous (quaternionProductSection e r) :=
  continuous_fst.prodMk (continuous_firstRowSection.comp continuous_snd)

@[simp] theorem quaternionProductProjection_section (e r : ℕ)
    (p : (Fin e → ℝ) × (Fin r × Fin 4 → ℝ)) :
    quaternionProductProjection e r (quaternionProductSection e r p) = p := by
  exact Prod.ext rfl (quaternionContraction_section p.2)

@[simp] theorem quaternionProductSection_zero (e r : ℕ) :
    quaternionProductSection e r (0,0) = (0,rankThreeZero) := by
  exact Prod.ext rfl firstRowSection_zero

theorem quaternionProductProjection_zero_iff (e r : ℕ)
    (p : (Fin e → ℝ) × RankThreeCone (Fin r × Fin 4)) :
    quaternionProductProjection e r p = (0,0) ↔ p = (0,rankThreeZero) := by
  constructor
  · intro h
    apply Prod.ext
    · exact congrArg (fun x : (Fin e → ℝ) × (Fin r × Fin 4 → ℝ) => x.1) h
    · exact (quaternionContraction_zero_iff p.2).mp
        (congrArg (fun x : (Fin e → ℝ) × (Fin r × Fin 4 → ℝ) => x.2) h)
  · rintro rfl
    exact Prod.ext rfl ((quaternionContraction_zero_iff _).mpr rfl)

/-- An explicit isolated-zero Euclidean retract, with no topological premise. -/
def quaternionProductRetract (e r : ℕ) :
    IsolatedEuclideanRetract ((Fin e → ℝ) × RankThreeCone (Fin r × Fin 4))
      (0,rankThreeZero) (e+r*4) where
  sectionMap := quaternionProductSection e r ∘ (pairCoordinatesEuclidean e r).symm
  projectionMap := pairCoordinatesEuclidean e r ∘ quaternionProductProjection e r
  section_continuous := (continuous_quaternionProductSection e r).comp
    (pairCoordinatesEuclidean e r).symm.continuous
  projection_continuous := (pairCoordinatesEuclidean e r).continuous.comp
    (continuous_quaternionProductProjection e r)
  projection_section x := by simp
  section_zero := by
    have hz : (pairCoordinatesEuclidean e r).symm 0 = (0,0) :=
      (pairCoordinatesEuclidean e r).symm_apply_eq.mpr (pairCoordinatesEuclidean_zero e r).symm
    change quaternionProductSection e r ((pairCoordinatesEuclidean e r).symm 0) = _
    rw [hz,quaternionProductSection_zero]
  projection_zero_iff p := by
    change pairCoordinatesEuclidean e r (quaternionProductProjection e r p) = 0 ↔ _
    rw [← pairCoordinatesEuclidean_zero e r,(pairCoordinatesEuclidean e r).injective.eq_iff,
      quaternionProductProjection_zero_iff]

end GS.UnitaryTopology
