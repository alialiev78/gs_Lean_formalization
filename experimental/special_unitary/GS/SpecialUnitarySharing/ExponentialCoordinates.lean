module

public import GS.SpecialUnitarySharing.ExponentialDifferential
public import GS.UnitarySharing.FactorCoordinates

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Local inverse coordinates for shared exponentials

Apply the inverse function theorem in the existing U-sharing generator space
and Cayley coordinates.  The scaling -2 makes the differential the identity,
matching the project's Cayley convention.  The resulting neighbourhood is
shrunk so exponentials are Cayley-admissible, all inverse formulas are smooth,
and every physical trace belongs to the injectivity neighbourhood of scalar
exponentiation.  Determinant one then forces each trace to be zero.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold Filter Set
open scoped Topology
namespace GS.SpecialUnitarySharing
variable {n : ℕ}

/-- Exponential coordinates in the larger unitary generator space. -/
def unitaryExpParam (s : Pattern n) (A : GS.UnitarySharing.Generator s) : CMat n :=
  cMatrixExp ((-2 : ℝ) • A.val)

theorem unitaryExpParam_shared (s : Pattern n) (A : GS.UnitarySharing.Generator s) :
    GS.UnitarySharing.SharedUnitaryFactor s.size s.label (unitaryExpParam s A) := by
  have ha := (GS.UnitarySharing.sharedSkewSpace (n := n) s.size s.label).smul_mem
    (-2 : ℝ) A.property
  have hm := cMatrixExp_mem_sharedMatrixSpace s ((-2 : ℝ) • A.val) ⟨ha.1, ha.2.2⟩
  exact ⟨hm.1, cMatrixExp_unitary _ ha.2.1, hm.2⟩

@[simp] theorem unitaryExpParam_zero (s : Pattern n) : unitaryExpParam s 0 = 1 := by
  simp [unitaryExpParam]

theorem unitaryExpParam_smooth (s : Pattern n) : ContDiff ℝ ⊤ (unitaryExpParam s) :=
  cMatrixExp_contDiff.comp
    (contDiff_const.smul (GS.UnitarySharing.sharedSkewSpace (n := n) s.size s.label).subtypeL.contDiff)

theorem unitaryExpParam_line_deriv (s : Pattern n) (A : GS.UnitarySharing.Generator s) :
    HasDerivAt (fun t : ℝ => unitaryExpParam s (t • A)) ((-2 : ℝ) • A.val) 0 := by
  have he := cExpLine_hasDerivAt ((-2 : ℝ) • A.val) 0
  simpa only [unitaryExpParam, Submodule.coe_smul, cExpLine, cExpLine_zero,
    Matrix.one_mul, smul_comm] using he

def unitaryExpCoordinates (s : Pattern n) (A : GS.UnitarySharing.Generator s) :
    GS.UnitarySharing.Generator s :=
  GS.UnitarySharing.factorCoordinates (1 : GS.UnitarySharing.Factor s) (unitaryExpParam s A)

@[simp] theorem unitaryExpCoordinates_zero (s : Pattern n) : unitaryExpCoordinates s 0 = 0 := by
  simpa only [unitaryExpCoordinates, unitaryExpParam_zero, GS.UnitarySharing.Factor.matrix_one]
    using GS.UnitarySharing.factorCoordinates_base (1 : GS.UnitarySharing.Factor s)

theorem unitaryExpCoordinates_smooth_zero (s : Pattern n) :
    ContDiffAt ℝ ⊤ (unitaryExpCoordinates s) 0 := by
  have hc := GS.UnitarySharing.factorCoordinates_smooth_at
    (1 : GS.UnitarySharing.Factor s) (1 : CMat n)
    (by simpa using (admissible_one (n := n)))
  have hc' : ContDiffAt ℝ ⊤
      (GS.UnitarySharing.factorCoordinates (1 : GS.UnitarySharing.Factor s))
      (unitaryExpParam s 0) := by simpa only [unitaryExpParam_zero] using hc
  exact hc'.comp 0 (unitaryExpParam_smooth s).contDiffAt

theorem unitaryExpCoordinates_fderiv_zero (s : Pattern n)
    (A : GS.UnitarySharing.Generator s) :
    fderiv ℝ (unitaryExpCoordinates s) 0 A = A := by
  have hc := (GS.UnitarySharing.factorCoordinates_smooth_at
    (1 : GS.UnitarySharing.Factor s) (1 : CMat n)
    (by simpa using (admissible_one (n := n)))).differentiableAt (by simp)
  have hinv := congrArg (fun D : GS.UnitarySharing.Generator s →L[ℝ]
      GS.UnitarySharing.Generator s => D A)
    (GS.UnitarySharing.coordinateDerivative_reconstruct (1 : GS.UnitarySharing.Factor s) 0)
  have he : fderiv ℝ (GS.UnitarySharing.factorCoordinates (1 : GS.UnitarySharing.Factor s)) 1
      ((-2 : ℝ) • A.val) = A := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      GS.UnitarySharing.matrixReconstruct_zero, GS.UnitarySharing.Factor.matrix_one,
      GS.UnitarySharing.matrixReconstruct_fderiv_zero, Matrix.one_mul] using hinv
  have ha := hc.hasFDerivAt.comp_hasDerivAt_of_eq 0 (unitaryExpParam_line_deriv s A)
    (unitaryExpParam_zero s)
  rw [he] at ha
  have hf := ((unitaryExpCoordinates_smooth_zero s).differentiableAt (by simp)).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => t • A) A 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const A
  exact (hf.comp_hasDerivAt_of_eq 0 hl (by simp)).unique ha

theorem unitaryExpCoordinates_hasFDerivAt_zero (s : Pattern n) :
    HasFDerivAt (unitaryExpCoordinates s)
      (ContinuousLinearMap.id ℝ (GS.UnitarySharing.Generator s)) 0 := by
  have hf := ((unitaryExpCoordinates_smooth_zero s).differentiableAt (by simp)).hasFDerivAt
  convert hf using 1
  ext A
  exact (unitaryExpCoordinates_fderiv_zero s A).symm

def unitaryExpCoordinateChart (s : Pattern n) :
    OpenPartialHomeomorph (GS.UnitarySharing.Generator s) (GS.UnitarySharing.Generator s) :=
  (unitaryExpCoordinates_smooth_zero s).toOpenPartialHomeomorph (unitaryExpCoordinates s)
    (f' := ContinuousLinearEquiv.refl ℝ (GS.UnitarySharing.Generator s))
    (unitaryExpCoordinates_hasFDerivAt_zero s) (by simp)

@[simp] theorem unitaryExpCoordinateChart_apply (s : Pattern n)
    (A : GS.UnitarySharing.Generator s) :
    unitaryExpCoordinateChart s A = unitaryExpCoordinates s A := rfl

theorem unitaryExpCoordinateChart_zero_source (s : Pattern n) :
    (0 : GS.UnitarySharing.Generator s) ∈ (unitaryExpCoordinateChart s).source :=
  (unitaryExpCoordinates_smooth_zero s).mem_toOpenPartialHomeomorph_source
    (f' := ContinuousLinearEquiv.refl ℝ (GS.UnitarySharing.Generator s))
    (unitaryExpCoordinates_hasFDerivAt_zero s) (by simp)

theorem unitaryExpCoordinateChart_zero_target (s : Pattern n) :
    (0 : GS.UnitarySharing.Generator s) ∈ (unitaryExpCoordinateChart s).target := by
  simpa only [unitaryExpCoordinateChart_apply, unitaryExpCoordinates_zero] using
    (unitaryExpCoordinateChart s).map_source (unitaryExpCoordinateChart_zero_source s)

theorem unitaryExpCoordinateChart_inverse_zero (s : Pattern n) :
    (unitaryExpCoordinateChart s).symm 0 = 0 := by
  simpa only [unitaryExpCoordinateChart_apply, unitaryExpCoordinates_zero] using
    (unitaryExpCoordinateChart s).left_inv (unitaryExpCoordinateChart_zero_source s)

theorem unitaryExpCoordinateChart_inverse_smooth_zero (s : Pattern n) :
    ContDiffAt ℝ ⊤ (unitaryExpCoordinateChart s).symm 0 := by
  have hi := (unitaryExpCoordinates_smooth_zero s).to_localInverse
    (f' := ContinuousLinearEquiv.refl ℝ (GS.UnitarySharing.Generator s))
    (unitaryExpCoordinates_hasFDerivAt_zero s) (by simp)
  simpa only [unitaryExpCoordinates_zero] using hi

/-- Finite simultaneous small-trace and Cayley conditions. -/
def goodExpDomain (s : Pattern n) : Set (GS.UnitarySharing.Generator s) :=
  {A | admissible (unitaryExpParam s A) ∧
    ∀ i : Fin n, blockTraceMap s i ((-2 : ℝ) • A.val) ∈ scalarExpChart.source}

theorem goodExpDomain_open (s : Pattern n) : IsOpen (goodExpDomain s) := by
  have ht : IsOpen {A : GS.UnitarySharing.Generator s |
      ∀ i : Fin n, blockTraceMap s i ((-2 : ℝ) • A.val) ∈ scalarExpChart.source} := by
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact scalarExpChart.open_source.preimage
      ((blockTraceMap s i).continuous.comp
        (continuous_const.smul continuous_subtype_val))
  exact (admissible_open.preimage (unitaryExpParam_smooth s).continuous).inter ht

theorem goodExpDomain_zero (s : Pattern n) :
    (0 : GS.UnitarySharing.Generator s) ∈ goodExpDomain s := by
  refine ⟨?_, ?_⟩
  · simpa using (admissible_one (n := n))
  · intro i
    simpa only [Submodule.coe_zero, smul_zero, map_zero] using scalarExpChart_zero_source

/-- Data supplied by IFT, not assumptions on an alleged SU manifold. -/
structure ExpCoordinateData (s : Pattern n) where
  domain image : Set (GS.UnitarySharing.Generator s)
  inverse : GS.UnitarySharing.Generator s → GS.UnitarySharing.Generator s
  domain_open : IsOpen domain
  image_open : IsOpen image
  zero_domain : 0 ∈ domain
  zero_image : 0 ∈ image
  inverse_zero : inverse 0 = 0
  good : domain ⊆ goodExpDomain s
  map_domain : ∀ A ∈ domain, unitaryExpCoordinates s A ∈ image
  map_image : ∀ B ∈ image, inverse B ∈ domain
  left_inverse : ∀ A ∈ domain, inverse (unitaryExpCoordinates s A) = A
  right_inverse : ∀ B ∈ image, unitaryExpCoordinates s (inverse B) = B
  inverse_smooth : ∀ B ∈ image, ContDiffAt ℝ ⊤ inverse B

theorem exists_expCoordinateData (s : Pattern n) : Nonempty (ExpCoordinateData s) := by
  let e := unitaryExpCoordinateChart s
  have hs : ∀ᶠ z in 𝓝 (0 : GS.UnitarySharing.Generator s), ContDiffAt ℝ ⊤ e.symm z :=
    (unitaryExpCoordinateChart_inverse_smooth_zero s).eventually (by simp)
  obtain ⟨W, hWsub, hWopen, hWzero⟩ := mem_nhds_iff.mp
    (inter_mem (e.open_target.mem_nhds (unitaryExpCoordinateChart_zero_target s)) hs)
  let D := e.source ∩ goodExpDomain s
  have hD : IsOpen D := e.open_source.inter (goodExpDomain_open s)
  have hD0 : (0 : GS.UnitarySharing.Generator s) ∈ D :=
    ⟨unitaryExpCoordinateChart_zero_source s, goodExpDomain_zero s⟩
  let J := W ∩ e '' D
  have hJ : IsOpen J := hWopen.inter (e.isOpen_image_of_subset_source hD (fun _ h => h.1))
  have hJ0 : (0 : GS.UnitarySharing.Generator s) ∈ J := by
    refine ⟨hWzero, 0, hD0, ?_⟩
    exact unitaryExpCoordinates_zero s
  let V := e.symm '' J
  have hJsub : J ⊆ e.target := fun _ h => (hWsub h.1).1
  have hV : IsOpen V := e.symm.isOpen_image_of_subset_source hJ hJsub
  have hV0 : (0 : GS.UnitarySharing.Generator s) ∈ V :=
    ⟨0, hJ0, unitaryExpCoordinateChart_inverse_zero s⟩
  refine ⟨⟨V, J, e.symm, hV, hJ, hV0, hJ0,
    unitaryExpCoordinateChart_inverse_zero s, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro A ⟨B, hB, rfl⟩
    obtain ⟨C, hC, hCB⟩ := hB.2
    rw [← hCB, e.left_inv hC.1]
    exact hC.2
  · rintro A ⟨B, hB, rfl⟩
    change e (e.symm B) ∈ J
    rw [e.right_inv (hJsub hB)]
    exact hB
  · intro B hB
    exact ⟨B, hB, rfl⟩
  · rintro A ⟨B, hB, rfl⟩
    change e.symm (e (e.symm B)) = e.symm B
    rw [e.right_inv (hJsub hB)]
  · intro B hB
    exact e.right_inv (hJsub hB)
  · intro B hB
    exact (hWsub hB.1).2

def expCoordinateData (s : Pattern n) : ExpCoordinateData s :=
  Classical.choice (exists_expCoordinateData s)

/-- Determinant one removes the local scalar winding in EACH physical block. -/
theorem traceFree_of_local_special_exp (s : Pattern n) (A : GS.UnitarySharing.Generator s)
    (hA : A ∈ (expCoordinateData s).domain)
    (hdet : BlockDetOne s (unitaryExpParam s A)) : BlockTraceZero s A.val := by
  intro i
  have hscaled := (GS.UnitarySharing.sharedSkewSpace (n := n) s.size s.label).smul_mem
    (-2 : ℝ) A.property
  have he := hdet i
  rw [unitaryExpParam, blockMatrix_cMatrixExp s i _ hscaled.1,
    det_cMatrixExp_of_skew _ (blockMatrix_skew s i _ hscaled.2.1)] at he
  have hz := trace_zero_of_exp_one (((expCoordinateData s).good hA).2 i) he
  have hz' : (-2 : ℝ) • Matrix.trace (blockMatrix s i A.val) = 0 := by
    simpa only [blockTraceMap_apply, blockMatrix_real_smul, Matrix.trace_smul] using hz
  exact (smul_eq_zero.mp hz').resolve_left (by norm_num)

end GS.SpecialUnitarySharing
