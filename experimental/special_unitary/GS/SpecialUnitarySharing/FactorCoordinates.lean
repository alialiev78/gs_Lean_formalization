module

public import GS.SpecialUnitarySharing.FactorDifferential

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Local product coordinates on the genuine SU shared factor group

Unlike the U Cayley chart, the exponential chart has a proper local target.
All inverse and openness statements carry that target condition explicitly.
The matrix reconstruction itself remains a globally smooth SU-valued map.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold Set Filter
open GS.SpecialUnitarySharing.Orbit
open scoped Topology Manifold
namespace GS.SpecialUnitarySharing
variable {n : ℕ} {s right left : Pattern n}

def matrixReconstruct (Q : SpecialFactor s) (v : Generator s) : CMat n :=
  SpecialFactor.matrix (reconstruct Q v)

@[simp] theorem matrixReconstruct_zero (Q : SpecialFactor s) :
    matrixReconstruct Q 0 = SpecialFactor.matrix Q := by simp [matrixReconstruct]

theorem matrixReconstruct_smooth (Q : SpecialFactor s) :
    ContDiff ℝ ⊤ (matrixReconstruct Q) := reconstruct_matrix_smooth Q

theorem factorCoordinates_matrixReconstruct (Q : SpecialFactor s) (v : Generator s)
    (hv : v ∈ factorTarget s) : factorCoordinates Q (matrixReconstruct Q v) = v :=
  factorCoordinates_reconstruct Q v hv

theorem matrixReconstruct_fderiv_zero (Q : SpecialFactor s) (v : Generator s) :
    fderiv ℝ (matrixReconstruct Q) 0 v = (-2 : ℝ) • (SpecialFactor.matrix Q * v.val) := by
  have hi := ((matrixReconstruct_smooth Q).differentiable (by simp) 0).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  exact (hi.comp_hasDerivAt_of_eq 0 hl (by simp)).unique
    (reconstruct_line_hasDerivAt_zero Q v)

/-- Differentiate a LOCAL inverse identity, not a false global one. -/
theorem coordinateDerivative_reconstruct (Q : SpecialFactor s) (v : Generator s)
    (hv : v ∈ factorTarget s) :
    (fderiv ℝ (factorCoordinates Q) (matrixReconstruct Q v)).comp
      (fderiv ℝ (matrixReconstruct Q) v) = ContinuousLinearMap.id ℝ (Generator s) := by
  have hr := ((matrixReconstruct_smooth Q).differentiable (by simp) v).hasFDerivAt
  have hs := reconstruct_mem_source Q v hv
  have hc := ((factorCoordinates_smooth_at Q (matrixReconstruct Q v) hs.1 hs.2).
    differentiableAt (by simp)).hasFDerivAt
  have he : (fun w : Generator s => factorCoordinates Q (matrixReconstruct Q w)) =ᶠ[𝓝 v]
      (id : Generator s → Generator s) := by
    filter_upwards [(factorTarget_open s).mem_nhds hv] with w hw
    exact factorCoordinates_matrixReconstruct Q w hw
  have hd := hc.comp v hr
  exact (hd.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_id v)

def pairSource (g : SpecialFactors right left) : Set (SpecialFactors right left) :=
  factorSource g.1 ×ˢ factorSource g.2

def pairTarget (right left : Pattern n) : Set (PairGenerator right left) :=
  factorTarget left ×ˢ factorTarget right

def pairCoordinates (g h : SpecialFactors right left) : PairGenerator right left :=
  (factorCoordinates g.1 (SpecialFactor.matrix h.1),
    factorCoordinates g.2 (SpecialFactor.matrix h.2))

theorem pairSource_open (g : SpecialFactors right left) : IsOpen (pairSource g) :=
  (factorSource_open g.1).prod (factorSource_open g.2)

theorem pairTarget_open (right left : Pattern n) : IsOpen (pairTarget right left) :=
  (factorTarget_open left).prod (factorTarget_open right)

@[simp] theorem self_mem_pairSource (g : SpecialFactors right left) : g ∈ pairSource g :=
  ⟨base_mem_factorSource g.1, base_mem_factorSource g.2⟩

@[simp] theorem zero_mem_pairTarget (right left : Pattern n) :
    (0 : PairGenerator right left) ∈ pairTarget right left :=
  ⟨zero_mem_factorTarget left, zero_mem_factorTarget right⟩

theorem pairCoordinates_factorLift (g : SpecialFactors right left) (v : PairGenerator right left)
    (hv : v ∈ pairTarget right left) : pairCoordinates g (factorLift g v) = v :=
  Prod.ext (factorCoordinates_reconstruct g.1 v.1 hv.1)
    (factorCoordinates_reconstruct g.2 v.2 hv.2)

theorem factorLift_pairCoordinates (g h : SpecialFactors right left) (hh : h ∈ pairSource g) :
    factorLift g (pairCoordinates g h) = h :=
  Prod.ext (reconstruct_factorCoordinates g.1 h.1 hh.1)
    (reconstruct_factorCoordinates g.2 h.2 hh.2)

theorem pairCoordinates_mem_target (g h : SpecialFactors right left) (hh : h ∈ pairSource g) :
    pairCoordinates g h ∈ pairTarget right left :=
  ⟨factorCoordinates_mem_target g.1 h.1 hh.1, factorCoordinates_mem_target g.2 h.2 hh.2⟩

theorem factorLift_mem_pairSource (g : SpecialFactors right left) (v : PairGenerator right left)
    (hv : v ∈ pairTarget right left) : factorLift g v ∈ pairSource g :=
  ⟨reconstruct_mem_source g.1 v.1 hv.1, reconstruct_mem_source g.2 v.2 hv.2⟩

@[simp] theorem pairCoordinates_self (g : SpecialFactors right left) : pairCoordinates g g = 0 :=
  Prod.ext (factorCoordinates_base g.1) (factorCoordinates_base g.2)

def pairPartialChart (g : SpecialFactors right left) :
    OpenPartialHomeomorph (SpecialFactors right left) (PairGenerator right left) where
  toFun := pairCoordinates g
  invFun := factorLift g
  source := pairSource g
  target := pairTarget right left
  map_source' h hh := pairCoordinates_mem_target g h hh
  map_target' v hv := factorLift_mem_pairSource g v hv
  left_inv' h hh := factorLift_pairCoordinates g h hh
  right_inv' v hv := pairCoordinates_factorLift g v hv
  open_source := pairSource_open g
  open_target := pairTarget_open right left
  continuousOn_toFun := by
    intro h hh
    have hl := ((factorCoordinates_smooth_at g.1 (SpecialFactor.matrix h.1)
      hh.1.1 hh.1.2).continuousAt.comp
      (SpecialFactor.continuous_matrix.comp continuous_fst).continuousAt)
    have hr := ((factorCoordinates_smooth_at g.2 (SpecialFactor.matrix h.2)
      hh.2.1 hh.2.2).continuousAt.comp
      (SpecialFactor.continuous_matrix.comp continuous_snd).continuousAt)
    exact (hl.prodMk hr).continuousWithinAt
  continuousOn_invFun := (continuous_factorLift g).continuousOn

/-- Only sets contained in the local exponential chart target are used. -/
theorem factorLift_image_open (g : SpecialFactors right left)
    (V : Set (PairGenerator right left)) (hV : IsOpen V) (hsub : V ⊆ pairTarget right left) :
    IsOpen (factorLift g '' V) :=
  (pairPartialChart g).isOpen_image_symm_of_subset_target hV hsub

theorem factorLift_orbit_image_open (g : SpecialFactors right left) (P : CMat n)
    (V : Set (PairGenerator right left)) (hV : IsOpen V) (hsub : V ⊆ pairTarget right left) :
    IsOpen ((fun v => orbitMapToOrbit right left P (factorLift g v)) '' V) := by
  have h := (orbitMapToOrbit_isOpenMap P) _ (factorLift_image_open g V hV hsub)
  simpa only [Set.image_image, Function.comp_def] using h

theorem fixed_action_smooth (g : SpecialFactors right left) :
    ContDiff ℝ ⊤ (fun A : CMat n => g • A) := by
  apply contDiff_iff_contDiffAt.mpr
  intro A
  exact smooth_mul_at (smooth_mul_at contDiffAt_const contDiffAt_id) contDiffAt_const

def preferredFactor (P : CMat n) (X : MatrixOrbit right left P) : SpecialFactors right left :=
  Classical.choose X.property

@[simp] theorem preferredFactor_spec (P : CMat n) (X : MatrixOrbit right left P) :
    orbitMapToOrbit right left P (preferredFactor P X) = X := by
  apply Subtype.ext
  exact Classical.choose_spec X.property

def orbitInverse (P : CMat n) (g : SpecialFactors right left) (v : PairGenerator right left) :
    MatrixOrbit right left P := orbitMapToOrbit right left P (factorLift g v)

@[simp] theorem orbitInverse_val (P : CMat n) (g : SpecialFactors right left)
    (v : PairGenerator right left) : (orbitInverse P g v).val = orbitParam g P v := rfl

theorem factorLift_eq_mul (g : SpecialFactors right left) (v : PairGenerator right left) :
    factorLift g v = g * factorLift (1 : SpecialFactors right left) v := by
  apply Prod.ext <;> simp only [factorLift, reconstruct, one_mul, Prod.fst_mul, Prod.snd_mul,
    Prod.fst_one, Prod.snd_one]

theorem orbitParam_eq_translate (g : SpecialFactors right left) (P : CMat n)
    (v : PairGenerator right left) : orbitParam g P v = g • orbitParam 1 P v := by
  unfold orbitParam
  rw [factorLift_eq_mul g v, MulAction.mul_smul]

end GS.SpecialUnitarySharing
