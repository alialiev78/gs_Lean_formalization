module

public import GS.SharedGeometry.Differential
public import GS.OverlapGeometry.FactorChartOpen

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Product coordinates on the genuine shared factor group

The existing single-factor charts have full generator-space targets.  Their
product reconstruction is therefore open in the inherited factor topology.
This module also records its ambient differential and the differentiated
coordinate inverse; no orbit atlas is assumed.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.GlobalGeometry GS.CayleyCharts Set Filter
open scoped Topology Manifold
namespace GS.SharedGeometry
variable {n : ℕ} {s right left : Pattern n}

/-- The actual matrix formula for the inverse of a shared factor chart. -/
def matrixReconstruct (Q : Factor s) (v : Generator s) : Mat n :=
  Factor.matrix (reconstruct Q v)

@[simp] theorem matrixReconstruct_zero (Q : Factor s) :
    matrixReconstruct Q 0 = Factor.matrix Q := by
  simp only [matrixReconstruct, reconstruct_zero]

theorem matrixReconstruct_smooth (Q : Factor s) :
    ContDiff ℝ ⊤ (matrixReconstruct Q) := reconstruct_matrix_smooth Q

@[simp] theorem factorCoordinates_matrixReconstruct (Q : Factor s) (v : Generator s) :
    factorCoordinates Q (matrixReconstruct Q v) = v :=
  factorCoordinates_reconstruct Q v

/-- Differentiate the concrete total inverse chart, not an assigned tangent map. -/
theorem matrixReconstruct_fderiv_zero (Q : Factor s) (v : Generator s) :
    fderiv ℝ (matrixReconstruct Q) 0 v =
      (-2 : ℝ) • (Factor.matrix Q * v.val) := by
  have hi := ((matrixReconstruct_smooth Q).differentiable (by simp) 0).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  exact (hi.comp_hasDerivAt_of_eq 0 hl (by simp)).unique
    (reconstruct_line_hasDerivAt_zero Q v)

/-- The ambient coordinate extension is a left inverse of the actual inverse-
chart derivative at every generator, not only at the chart centre. -/
theorem coordinateDerivative_reconstruct (Q : Factor s) (v : Generator s) :
    (fderiv ℝ (factorCoordinates Q) (matrixReconstruct Q v)).comp
      (fderiv ℝ (matrixReconstruct Q) v) =
        ContinuousLinearMap.id ℝ (Generator s) := by
  have hr := ((matrixReconstruct_smooth Q).differentiable (by simp) v).hasFDerivAt
  have hc := ((factorCoordinates_smooth_at Q (matrixReconstruct Q v)
    (reconstruct_mem_source Q v)).differentiableAt (by simp)).hasFDerivAt
  have he : (fun w : Generator s => factorCoordinates Q (matrixReconstruct Q w)) =
      (id : Generator s → Generator s) := by
    funext w
    exact factorCoordinates_matrixReconstruct Q w
  have hd := hc.comp v hr
  change HasFDerivAt (fun w : Generator s =>
    factorCoordinates Q (matrixReconstruct Q w)) _ v at hd
  rw [he] at hd
  exact hd.unique (hasFDerivAt_id v)

/-- Source of the product of the existing single-factor charts. -/
def pairSource (g : Factors right left) : Set (Factors right left) :=
  factorSource g.1 ×ˢ factorSource g.2

def pairCoordinates (g h : Factors right left) : PairGenerator right left :=
  (factorCoordinates g.1 (Factor.matrix h.1),
    factorCoordinates g.2 (Factor.matrix h.2))

theorem pairSource_open (g : Factors right left) : IsOpen (pairSource g) :=
  (factorSource_open g.1).prod (factorSource_open g.2)

@[simp] theorem self_mem_pairSource (g : Factors right left) : g ∈ pairSource g :=
  ⟨base_mem_factorSource g.1, base_mem_factorSource g.2⟩

@[simp] theorem pairCoordinates_factorLift (g : Factors right left)
    (v : PairGenerator right left) : pairCoordinates g (factorLift g v) = v := by
  apply Prod.ext
  · exact factorCoordinates_reconstruct g.1 v.1
  · exact factorCoordinates_reconstruct g.2 v.2

theorem factorLift_pairCoordinates (g h : Factors right left)
    (hh : h ∈ pairSource g) : factorLift g (pairCoordinates g h) = h := by
  apply Prod.ext
  · exact reconstruct_factorCoordinates g.1 h.1 hh.1
  · exact reconstruct_factorCoordinates g.2 h.2 hh.2

@[simp] theorem pairCoordinates_self (g : Factors right left) :
    pairCoordinates g g = 0 := by
  apply Prod.ext <;> exact factorCoordinates_base _

theorem factorLift_mem_pairSource (g : Factors right left)
    (v : PairGenerator right left) : factorLift g v ∈ pairSource g :=
  ⟨reconstruct_mem_source g.1 v.1, reconstruct_mem_source g.2 v.2⟩

theorem reconstruct_isOpenMap (Q : Factor s) : IsOpenMap (reconstruct Q) := by
  intro U hU
  exact (factorPartialChart Q).isOpen_image_symm_of_subset_target hU
    (by change U ⊆ Set.univ; exact Set.subset_univ U)

/-- Positively dimensional stabilizers do not affect openness of reconstruction. -/
theorem factorLift_isOpenMap (g : Factors right left) : IsOpenMap (factorLift g) :=
  (reconstruct_isOpenMap g.1).prodMap (reconstruct_isOpenMap g.2)

theorem factorLift_orbit_isOpenMap (g : Factors right left) (P : Mat n) :
    IsOpenMap (fun v : PairGenerator right left =>
      orbitMapToOrbit right left P (factorLift g v)) :=
  (orbitMapToOrbit_isOpenMap P).comp (factorLift_isOpenMap g)

/-- Smooth linear action of any fixed shared factor pair on ambient matrices. -/
theorem fixed_action_smooth (g : Factors right left) :
    ContDiff ℝ ⊤ (fun A : Mat n => g • A) := by
  apply contDiff_iff_contDiffAt.mpr
  intro A
  exact smooth_mul_at (smooth_mul_at contDiffAt_const contDiffAt_id) contDiffAt_const

/-- A fixed representative is used only to centre a chart.  No continuity
of this choice function is asserted or used. -/
def preferredFactor (P : Mat n) (X : MatrixOrbit right left P) : Factors right left :=
  Classical.choose X.property

@[simp] theorem preferredFactor_spec (P : Mat n) (X : MatrixOrbit right left P) :
    orbitMapToOrbit right left P (preferredFactor P X) = X := by
  apply Subtype.ext
  exact Classical.choose_spec X.property

/-- A total matrix-orbit parametrization; only injectivity will be local. -/
def orbitInverse (P : Mat n) (g : Factors right left) (v : PairGenerator right left) :
    MatrixOrbit right left P := orbitMapToOrbit right left P (factorLift g v)

@[simp] theorem orbitInverse_val (P : Mat n) (g : Factors right left)
    (v : PairGenerator right left) : (orbitInverse P g v).val = orbitParam g P v := rfl

/-- Fixed group translation of the total factor chart. -/
theorem factorLift_eq_mul (g : Factors right left) (v : PairGenerator right left) :
    factorLift g v = g * factorLift (1 : Factors right left) v := by
  apply Prod.ext
  · change reconstruct g.1 v.1 = g.1 * reconstruct (1 : Factor left) v.1
    simp only [reconstruct, one_mul]
  · change reconstruct g.2 v.2 = g.2 * reconstruct (1 : Factor right) v.2
    simp only [reconstruct, one_mul]

/-- This identity is global in the coordinate model. -/
theorem orbitParam_eq_translate (g : Factors right left) (P : Mat n)
    (v : PairGenerator right left) :
    orbitParam g P v = g • orbitParam (1 : Factors right left) P v := by
  unfold orbitParam
  rw [factorLift_eq_mul g v, mul_smul]

end GS.SharedGeometry
