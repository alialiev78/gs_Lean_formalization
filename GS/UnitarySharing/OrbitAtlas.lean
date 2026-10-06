module

public import GS.UnitarySharing.LocalProduct
public import GS.UnitarySharing.ProjectedSlice
public import GS.OverlapGeometry.FactorChartOpen
public import GS.Extensions.OrbitSlices

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The shared two-factor matrix orbit in its inherited topology

A local product decomposition separates horizontal directions from the
stabilizer. The orbit map is open, so the horizontal slice has relatively open
image. Its ambient smooth inverse gives an atlas on the original matrix
subtype topology. The factors are the concrete shared subgroups.  No disjoint-support hypothesis,
discrete-stabilizer premise, orbit-lifting premise, or pre-existing manifold
instance on the matrix image is supplied.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryManifold Set Filter
open GS.OverlapGeometry (SmoothSlice sliceChartedSpace slice_isManifold
  slice_val_contMDiff slice_val_mfderiv_eq slice_val_mfderiv_injective
  isOpen_slice_image_of_productChart)
open scoped Topology Manifold

namespace GS.UnitarySharing
variable {n : ℕ} (right left : Pattern n) (P : CMat n)
local instance orbitAtlasNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance orbitAtlasKernelNormedSpace : NormedSpace ℝ (OrbitKernel right left P) :=
  Submodule.normedSpace _
attribute [local irreducible] sharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

def productFactors (z : HorizontalModel right left P × OrbitKernel right left P) :
    Factors right left :=
  factorLift 1 z.1.val * factorLift 1 z.2.val

theorem productFactors_continuous : Continuous (productFactors right left P) :=
  ((continuous_factorLift 1).comp (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_factorLift 1).comp (continuous_subtype_val.comp continuous_snd))

def goodProductDomain : Set (HorizontalModel right left P × OrbitKernel right left P) :=
  productFactors right left P ⁻¹' pairSource (1 : Factors right left)

theorem goodProductDomain_open : IsOpen (goodProductDomain right left P) :=
  (pairSource_open 1).preimage (productFactors_continuous right left P)

def goodProductChart :
    OpenPartialHomeomorph (HorizontalModel right left P × OrbitKernel right left P)
      (PairGenerator right left) :=
  (sliceProductChart right left P).restrOpen (goodProductDomain right left P)
    (goodProductDomain_open right left P)

theorem goodProductChart_zero_source :
    (0 : HorizontalModel right left P × OrbitKernel right left P) ∈
      (goodProductChart right left P).source := by
  refine ⟨sliceProductChart_zero_mem_source right left P, ?_⟩
  change factorLift (1 : Factors right left) 0 * factorLift 1 0 ∈ pairSource 1
  simpa using self_mem_pairSource (1 : Factors right left)

theorem goodProductChart_orbit (z : HorizontalModel right left P × OrbitKernel right left P)
    (hz : z ∈ (goodProductChart right left P).source) :
    orbitMapToOrbit right left P
      (factorLift 1 (goodProductChart right left P z)) = horizontalPoint right left P z.1 := by
  apply Subtype.ext
  change factorLift 1 (sliceProduct right left P z) • P = _
  have hz' : factorLift (1 : Factors right left) z.1.val * factorLift 1 z.2.val ∈
      pairSource 1 := hz.2
  have hk : (fderiv ℝ (orbitParam (1 : Factors right left) P) 0) z.2.val = 0 := by
    simpa only [orbitDerivative] using
      (show orbitDerivative right left P z.2.val = 0 from z.2.property)
  rw [sliceProduct, factorProductCoordinates_eq,
    factorLift_pairCoordinates 1 _ hz', mul_smul,
    (factorLift_stabilizes_iff_kernel P z.2.val).mpr hk]
  rfl

/-- The horizontal parameter neighbourhood where the product decomposition
and the ambient inverse are simultaneously valid. -/
def horizontalChartDomain : Set (HorizontalModel right left P) :=
  (projectedSliceData right left P).domain ∩
    (fun h => (h, (0 : OrbitKernel right left P))) ⁻¹' (goodProductChart right left P).source

theorem horizontalChartDomain_open : IsOpen (horizontalChartDomain right left P) :=
  (projectedSliceData right left P).open_domain.inter
    ((goodProductChart right left P).open_source.preimage
      (continuous_id.prodMk continuous_const))

theorem horizontalChartDomain_zero : (0 : HorizontalModel right left P) ∈
    horizontalChartDomain right left P :=
  ⟨(projectedSliceData right left P).zero_mem, goodProductChart_zero_source right left P⟩

/-- Relative openness is proved by the group orbit map and the product IFT,
not assumed as part of a putative manifold structure. -/
theorem horizontalChartImage_open :
    IsOpen (horizontalPoint right left P '' horizontalChartDomain right left P) := by
  apply isOpen_slice_image_of_productChart (goodProductChart right left P)
    (fun x => orbitMapToOrbit right left P (factorLift 1 x))
    (horizontalPoint right left P) (factorLift_orbit_isOpenMap 1 P)
    (goodProductChart_orbit right left P) _ (horizontalChartDomain_open right left P)
  intro h hh
  exact ⟨0, hh.2⟩

/-- A concrete ambient smooth slice at the carrier matrix. -/
def baseOrbitSlice :
    SmoothSlice (E := HorizontalModel right left P)
      (MulAction.orbit (Factors right left) P) :=
  GS.Extensions.smoothSliceOfParametrization
    (horizontalPoint right left P) (projectedSliceData right left P).coordinates
    (horizontalChartDomain right left P) (horizontalValue_smooth right left P)
    (horizontalChartDomain_open right left P) (horizontalChartImage_open right left P)
    (fun h hh => (projectedSliceData right left P).coordinates_smooth h hh.1)
    (fun h hh => (projectedSliceData right left P).left_inverse h hh.1)

/-- Translation of points of the orbit in its inherited topology. -/
def orbitTranslate (g : Factors right left) (X : MatrixOrbit right left P) :
    MatrixOrbit right left P :=
  ⟨g • X.val, by
    obtain ⟨h, hh⟩ := X.property
    exact ⟨g * h, by simpa only [mul_smul, hh]⟩⟩

@[simp] theorem orbitTranslate_val (g : Factors right left)
    (X : MatrixOrbit right left P) :
    (orbitTranslate right left P g X).val = g • X.val := rfl

theorem orbitTranslate_continuous (g : Factors right left) :
    Continuous (orbitTranslate right left P g) :=
  (continuous_subtype_val.const_smul g).subtype_mk _

@[simp] theorem orbitTranslate_inv (g : Factors right left)
    (X : MatrixOrbit right left P) :
    orbitTranslate right left P g⁻¹ (orbitTranslate right left P g X) = X := by
  apply Subtype.ext
  exact inv_smul_smul g X.val

@[simp] theorem orbitTranslate_inv' (g : Factors right left)
    (X : MatrixOrbit right left P) :
    orbitTranslate right left P g (orbitTranslate right left P g⁻¹ X) = X := by
  apply Subtype.ext
  exact smul_inv_smul g X.val

/-- Translate the constructed slice from the carrier matrix to an
arbitrary point, without changing the common horizontal model. -/
def translatedOrbitSlice (g : Factors right left) :
    SmoothSlice (E := HorizontalModel right left P)
      (MulAction.orbit (Factors right left) P) :=
  GS.Extensions.translateSmoothSlice (baseOrbitSlice right left P)
    (fun A => g • A) (fun A => g⁻¹ • A)
    (orbitTranslate right left P g) (orbitTranslate right left P g⁻¹)
    (orbitTranslate_val right left P g) (orbitTranslate_val right left P g⁻¹)
    (orbitTranslate_inv' right left P g) (orbitTranslate_inv right left P g)
    (fixed_action_smooth g) (fixed_action_smooth g⁻¹)
    (orbitTranslate_continuous right left P g⁻¹)

theorem translatedOrbitSlice_centre_mem (g : Factors right left) :
    orbitMapToOrbit right left P g ∈ (translatedOrbitSlice right left P g).source := by
  have he : orbitTranslate right left P g⁻¹
      (orbitMapToOrbit right left P g) = horizontalPoint right left P 0 := by
    apply Subtype.ext
    change g⁻¹ • (g • P) = (horizontalPoint right left P 0).val
    rw [inv_smul_smul, horizontalPoint_val, horizontalValue_zero]
  change orbitTranslate right left P g⁻¹ _ ∈
    horizontalPoint right left P '' horizontalChartDomain right left P
  rw [he]
  exact ⟨0, horizontalChartDomain_zero right left P, rfl⟩

theorem translatedOrbitSlice_centre_coordinates (g : Factors right left) :
    (translatedOrbitSlice right left P g).coordinates
      (orbitMapToOrbit right left P g).val = 0 := by
  change (projectedSliceData right left P).coordinates (g⁻¹ • (g • P)) = 0
  rw [inv_smul_smul]
  simpa only [horizontalValue_zero] using
    (projectedSliceData right left P).left_inverse 0 (projectedSliceData right left P).zero_mem

def preferredOrbitSlice (X : MatrixOrbit right left P) :
    SmoothSlice (E := HorizontalModel right left P)
      (MulAction.orbit (Factors right left) P) :=
  translatedOrbitSlice right left P (preferredFactor P X)

theorem preferredOrbitSlice_covers (X : MatrixOrbit right left P) :
    X ∈ (preferredOrbitSlice right left P X).source := by
  have hh := translatedOrbitSlice_centre_mem right left P (preferredFactor P X)
  simpa only [preferredFactor_spec, preferredOrbitSlice] using hh

theorem preferredOrbitSlice_coordinates_zero (X : MatrixOrbit right left P) :
    (preferredOrbitSlice right left P X).coordinates X.val = 0 := by
  have hh := translatedOrbitSlice_centre_coordinates right left P (preferredFactor P X)
  simpa only [preferredFactor_spec, preferredOrbitSlice] using hh

/-- The shared orbit atlas in its original matrix-subtype topology.  This
is an explicit structure, not a global instance changing older geometries. -/
def sharedOrbitChartedSpace :
    ChartedSpace (HorizontalModel right left P) (MatrixOrbit right left P) :=
  sliceChartedSpace (preferredOrbitSlice right left P) (preferredOrbitSlice_covers right left P)

theorem sharedOrbitIsManifold :
    letI := sharedOrbitChartedSpace right left P
    IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤ (MatrixOrbit right left P) :=
  slice_isManifold (preferredOrbitSlice right left P) (preferredOrbitSlice_covers right left P)

theorem sharedOrbit_val_contMDiff :
    letI := sharedOrbitChartedSpace right left P
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, CMat n)) ⊤
      (fun X : MatrixOrbit right left P => X.val) :=
  slice_val_contMDiff (preferredOrbitSlice right left P) (preferredOrbitSlice_covers right left P)

theorem sharedOrbit_val_mfderiv_eq (X : MatrixOrbit right left P) :
    letI := sharedOrbitChartedSpace right left P
    mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, CMat n))
      (fun Y : MatrixOrbit right left P => Y.val) X =
        fderiv ℝ (fun h : HorizontalModel right left P =>
          preferredFactor P X • horizontalValue right left P h) 0 := by
  letI := sharedOrbitChartedSpace right left P
  have hh := slice_val_mfderiv_eq (preferredOrbitSlice right left P)
    (preferredOrbitSlice_covers right left P) X
  rw [preferredOrbitSlice_coordinates_zero] at hh
  simpa only [preferredOrbitSlice, translatedOrbitSlice, baseOrbitSlice,
    GS.Extensions.translateSmoothSlice, GS.Extensions.smoothSliceOfParametrization,
    orbitTranslate_val, horizontalPoint_val] using hh

theorem sharedOrbit_val_mfderiv_injective (X : MatrixOrbit right left P) :
    letI := sharedOrbitChartedSpace right left P
    Function.Injective (mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, CMat n))
      (fun Y : MatrixOrbit right left P => Y.val) X) :=
  slice_val_mfderiv_injective (preferredOrbitSlice right left P)
    (preferredOrbitSlice_covers right left P) X

/-- The manuscript's shared two-factor family itself has the constructed
smooth structure.  The source is the original matrix subtype, not an abstract
replacement topology or an assumed quotient manifold. -/
theorem inSharedA2Unitary_admits_manifold :
    ∃ cs : ChartedSpace (HorizontalModel right left P)
        {X : CMat n // GS.UnitarySharing.InSharedA2Unitary
          right.size left.size right.label left.label P X},
      letI := cs
      IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
        {X : CMat n // GS.UnitarySharing.InSharedA2Unitary
          right.size left.size right.label left.label P X} := by
  have hh : ∃ cs : ChartedSpace (HorizontalModel right left P)
      ↥(MulAction.orbit (Factors right left) P),
      letI := cs
      IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
        ↥(MulAction.orbit (Factors right left) P) :=
    ⟨sharedOrbitChartedSpace right left P, sharedOrbitIsManifold right left P⟩
  rw [orbit_set_eq_inShared (right := right) (left := left) P] at hh
  exact hh

end GS.UnitarySharing
