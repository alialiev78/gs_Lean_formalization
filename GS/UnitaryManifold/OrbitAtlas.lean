module

public import GS.UnitaryManifold.LocalProduct
public import GS.UnitaryManifold.ProjectedSlice
public import GS.UnitaryManifold.FactorChartOpen
public import GS.UnitaryManifold.SliceTransport

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The actual two-factor orbit is a manifold with arbitrary overlap

A local product decomposition separates horizontal directions from the
stabilizer. The orbit map is open, so the horizontal slice has relatively open
image. Its ambient smooth inverse gives an atlas on the original matrix
subtype topology. No condition excluding overlap is imposed.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.OverlapGeometry Set Filter
open scoped Topology Manifold

namespace GS.UnitaryManifold
set_option synthInstance.maxHeartbeats 100000
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))

/-- Cache the inherited instances when assembling the dependent slice structure. -/
local instance horizontalNormedAddCommGroup :
    NormedAddCommGroup (HorizontalModel b₁ b₂ σ) := inferInstance
local instance horizontalNormedSpace :
    NormedSpace ℝ (HorizontalModel b₁ b₂ σ) := inferInstance

def productFactors (z : HorizontalModel b₁ b₂ σ × OrbitKernel b₁ b₂ σ) :
    FactorGroup b₁ b₂ :=
  factorLift 1 z.1.val * factorLift 1 z.2.val

theorem productFactors_continuous : Continuous (productFactors b₁ b₂ σ) :=
  ((continuous_factorLift 1).comp (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_factorLift 1).comp (continuous_subtype_val.comp continuous_snd))

def goodProductDomain : Set (HorizontalModel b₁ b₂ σ × OrbitKernel b₁ b₂ σ) :=
  productFactors b₁ b₂ σ ⁻¹' factorSource (1 : FactorGroup b₁ b₂)

theorem goodProductDomain_open : IsOpen (goodProductDomain b₁ b₂ σ) :=
  (factorSource_open 1).preimage (productFactors_continuous b₁ b₂ σ)

def goodProductChart :
    OpenPartialHomeomorph (HorizontalModel b₁ b₂ σ × OrbitKernel b₁ b₂ σ)
      (PairModel b₁ b₂) :=
  (sliceProductChart b₁ b₂ σ).restrOpen (goodProductDomain b₁ b₂ σ)
    (goodProductDomain_open b₁ b₂ σ)

theorem goodProductChart_zero_source :
    (0 : HorizontalModel b₁ b₂ σ × OrbitKernel b₁ b₂ σ) ∈
      (goodProductChart b₁ b₂ σ).source := by
  refine ⟨sliceProductChart_zero_mem_source b₁ b₂ σ, ?_⟩
  change factorLift (1 : FactorGroup b₁ b₂) 0 * factorLift 1 0 ∈ factorSource 1
  simpa using self_mem_factorSource (1 : FactorGroup b₁ b₂)

theorem goodProductChart_orbit (z : HorizontalModel b₁ b₂ σ × OrbitKernel b₁ b₂ σ)
    (hz : z ∈ (goodProductChart b₁ b₂ σ).source) :
    orbitMapToOrbit b₁ b₂ (cPermMatrix σ)
      (factorLift 1 (goodProductChart b₁ b₂ σ z)) = horizontalPoint b₁ b₂ σ z.1 := by
  apply Subtype.ext
  change factorLift 1 (sliceProduct b₁ b₂ σ z) • cPermMatrix σ = _
  have hz' : factorLift (1 : FactorGroup b₁ b₂) z.1.val * factorLift 1 z.2.val ∈
      factorSource 1 := hz.2
  rw [sliceProduct, factorProductCoordinates_eq,
    factorLift_factorCoordinates 1 _ hz', mul_smul,
    kernel_factorLift_stabilizes (cPermMatrix σ) z.2.val z.2.property]
  rfl

/-- The horizontal parameter neighbourhood where the product decomposition
and the ambient inverse are simultaneously valid. -/
def horizontalChartDomain : Set (HorizontalModel b₁ b₂ σ) :=
  (projectedSliceData b₁ b₂ σ).domain ∩
    (fun h => (h, (0 : OrbitKernel b₁ b₂ σ))) ⁻¹' (goodProductChart b₁ b₂ σ).source

theorem horizontalChartDomain_open : IsOpen (horizontalChartDomain b₁ b₂ σ) :=
  (projectedSliceData b₁ b₂ σ).open_domain.inter
    ((goodProductChart b₁ b₂ σ).open_source.preimage
      (continuous_id.prodMk continuous_const))

theorem horizontalChartDomain_zero : (0 : HorizontalModel b₁ b₂ σ) ∈
    horizontalChartDomain b₁ b₂ σ :=
  ⟨(projectedSliceData b₁ b₂ σ).zero_mem, goodProductChart_zero_source b₁ b₂ σ⟩

/-- Relative openness is proved by the group orbit map and the product IFT,
not assumed as part of a putative manifold structure. -/
theorem horizontalChartImage_open :
    IsOpen (horizontalPoint b₁ b₂ σ '' horizontalChartDomain b₁ b₂ σ) := by
  apply isOpen_slice_image_of_productChart (goodProductChart b₁ b₂ σ)
    (fun x => orbitMapToOrbit b₁ b₂ (cPermMatrix σ) (factorLift 1 x))
    (horizontalPoint b₁ b₂ σ) (factorLift_orbit_isOpenMap 1 (cPermMatrix σ))
    (goodProductChart_orbit b₁ b₂ σ) _ (horizontalChartDomain_open b₁ b₂ σ)
  intro h hh
  exact ⟨0, hh.2⟩

/-- A concrete ambient smooth slice at the permutation matrix. -/
def baseOrbitSlice :
    SmoothSlice (E := HorizontalModel b₁ b₂ σ)
      (MulAction.orbit (FactorGroup b₁ b₂) (cPermMatrix σ)) where
  source := horizontalPoint b₁ b₂ σ '' horizontalChartDomain b₁ b₂ σ
  target := horizontalChartDomain b₁ b₂ σ
  coordinates := (projectedSliceData b₁ b₂ σ).coordinates
  parametrization := horizontalPoint b₁ b₂ σ
  open_source := horizontalChartImage_open b₁ b₂ σ
  open_target := horizontalChartDomain_open b₁ b₂ σ
  coordinates_smooth := by
    rintro X ⟨h, hh, rfl⟩
    rw [horizontalPoint_val]
    exact (projectedSliceData b₁ b₂ σ).coordinates_smooth h hh.1
  parametrization_smooth := by
    simpa only [horizontalPoint_val] using horizontalValue_smooth b₁ b₂ σ
  maps_source := by
    rintro X ⟨h, hh, rfl⟩
    simpa only [horizontalPoint_val, (projectedSliceData b₁ b₂ σ).left_inverse h hh.1]
      using hh
  maps_target := fun h hh => ⟨h, hh, rfl⟩
  left_inverse := by
    rintro X ⟨h, hh, rfl⟩
    rw [horizontalPoint_val, (projectedSliceData b₁ b₂ σ).left_inverse h hh.1]
  right_inverse := by
    intro h hh
    rw [horizontalPoint_val]
    exact (projectedSliceData b₁ b₂ σ).left_inverse h hh.1

/-- Translation of points of the orbit in its inherited topology. -/
def orbitTranslate (g : FactorGroup b₁ b₂) (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    MatrixOrbit b₁ b₂ (cPermMatrix σ) :=
  ⟨g • X.val, by
    obtain ⟨h, hh⟩ := X.property
    exact ⟨g * h, by simpa only [mul_smul, hh]⟩⟩

@[simp] theorem orbitTranslate_val (g : FactorGroup b₁ b₂)
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    (orbitTranslate b₁ b₂ σ g X).val = g • X.val := rfl

theorem orbitTranslate_continuous (g : FactorGroup b₁ b₂) :
    Continuous (orbitTranslate b₁ b₂ σ g) :=
  (continuous_subtype_val.const_smul g).subtype_mk _

@[simp] theorem orbitTranslate_inv (g : FactorGroup b₁ b₂)
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    orbitTranslate b₁ b₂ σ g⁻¹ (orbitTranslate b₁ b₂ σ g X) = X := by
  apply Subtype.ext
  exact inv_smul_smul g X.val

@[simp] theorem orbitTranslate_inv' (g : FactorGroup b₁ b₂)
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    orbitTranslate b₁ b₂ σ g (orbitTranslate b₁ b₂ σ g⁻¹ X) = X := by
  apply Subtype.ext
  exact smul_inv_smul g X.val

/-- The fixed ambient action, with its inherited continuous linear structure. -/
def actionContinuousLinearEquiv (g : FactorGroup b₁ b₂) : CMat n ≃L[ℝ] CMat n where
  toLinearEquiv := actionLinearEquiv g
  continuous_toFun := continuous_id.const_smul g
  continuous_invFun := continuous_id.const_smul g⁻¹

/-- Translation acts by a homeomorphism of the original orbit subtype. -/
def orbitTranslateHomeomorph (g : FactorGroup b₁ b₂) :
    MatrixOrbit b₁ b₂ (cPermMatrix σ) ≃ₜ MatrixOrbit b₁ b₂ (cPermMatrix σ) where
  toFun := orbitTranslate b₁ b₂ σ g
  invFun := orbitTranslate b₁ b₂ σ g⁻¹
  left_inv := orbitTranslate_inv b₁ b₂ σ g
  right_inv := orbitTranslate_inv' b₁ b₂ σ g
  continuous_toFun := orbitTranslate_continuous b₁ b₂ σ g
  continuous_invFun := orbitTranslate_continuous b₁ b₂ σ g⁻¹

/-- Translate the constructed slice using the proved generic transport lemma.
The compatibility with the ambient action is definitional in both directions. -/
def translatedOrbitSlice (g : FactorGroup b₁ b₂) :
    SmoothSlice (E := HorizontalModel b₁ b₂ σ)
      (MulAction.orbit (FactorGroup b₁ b₂) (cPermMatrix σ)) :=
  (baseOrbitSlice b₁ b₂ σ).transportLinear
    (actionContinuousLinearEquiv b₁ b₂ g)
    (orbitTranslateHomeomorph b₁ b₂ σ g) (fun _ => rfl) (fun _ => rfl)

theorem translatedOrbitSlice_centre_mem (g : FactorGroup b₁ b₂) :
    orbitMapToOrbit b₁ b₂ (cPermMatrix σ) g ∈ (translatedOrbitSlice b₁ b₂ σ g).source := by
  have he : orbitTranslate b₁ b₂ σ g⁻¹
      (orbitMapToOrbit b₁ b₂ (cPermMatrix σ) g) = horizontalPoint b₁ b₂ σ 0 := by
    apply Subtype.ext
    change g⁻¹ • (g • cPermMatrix σ) = (horizontalPoint b₁ b₂ σ 0).val
    rw [inv_smul_smul, horizontalPoint_val, horizontalValue_zero]
  change orbitTranslate b₁ b₂ σ g⁻¹ _ ∈
    horizontalPoint b₁ b₂ σ '' horizontalChartDomain b₁ b₂ σ
  rw [he]
  exact ⟨0, horizontalChartDomain_zero b₁ b₂ σ, rfl⟩

theorem translatedOrbitSlice_centre_coordinates (g : FactorGroup b₁ b₂) :
    (translatedOrbitSlice b₁ b₂ σ g).coordinates
      (orbitMapToOrbit b₁ b₂ (cPermMatrix σ) g).val = 0 := by
  change (projectedSliceData b₁ b₂ σ).coordinates (g⁻¹ • (g • cPermMatrix σ)) = 0
  rw [inv_smul_smul, ← horizontalValue_zero b₁ b₂ σ]
  exact (projectedSliceData b₁ b₂ σ).left_inverse 0 (projectedSliceData b₁ b₂ σ).zero_mem

def preferredOrbitSlice (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    SmoothSlice (E := HorizontalModel b₁ b₂ σ)
      (MulAction.orbit (FactorGroup b₁ b₂) (cPermMatrix σ)) :=
  translatedOrbitSlice b₁ b₂ σ (preferredFactor σ X)

theorem preferredOrbitSlice_covers (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    X ∈ (preferredOrbitSlice b₁ b₂ σ X).source := by
  have hh := translatedOrbitSlice_centre_mem b₁ b₂ σ (preferredFactor σ X)
  simpa only [preferredFactor_spec, preferredOrbitSlice] using hh

theorem preferredOrbitSlice_coordinates_zero (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    (preferredOrbitSlice b₁ b₂ σ X).coordinates X.val = 0 := by
  have hh := translatedOrbitSlice_centre_coordinates b₁ b₂ σ (preferredFactor σ X)
  simpa only [preferredFactor_spec, preferredOrbitSlice] using hh

/-- An atlas on the actual orbit with its inherited matrix topology, for
arbitrary overlapping partitions. The explicit atlas exposes the chosen real
horizontal model and avoids installing an unrelated global charted-space instance.
The kernel includes diagonal phase gauges even without off-diagonal overlap. -/
def overlapChartedSpace :
    ChartedSpace (HorizontalModel b₁ b₂ σ) (MatrixOrbit b₁ b₂ (cPermMatrix σ)) :=
  sliceChartedSpace (preferredOrbitSlice b₁ b₂ σ) (preferredOrbitSlice_covers b₁ b₂ σ)

theorem overlapIsManifold :
    letI := overlapChartedSpace b₁ b₂ σ
    IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤ (MatrixOrbit b₁ b₂ (cPermMatrix σ)) :=
  slice_isManifold (preferredOrbitSlice b₁ b₂ σ) (preferredOrbitSlice_covers b₁ b₂ σ)

theorem overlap_val_contMDiff :
    letI := overlapChartedSpace b₁ b₂ σ
    ContMDiff (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, CMat n)) ⊤
      (fun X : MatrixOrbit b₁ b₂ (cPermMatrix σ) => X.val) :=
  slice_val_contMDiff (preferredOrbitSlice b₁ b₂ σ) (preferredOrbitSlice_covers b₁ b₂ σ)

theorem overlap_val_mfderiv_eq (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    letI := overlapChartedSpace b₁ b₂ σ
    mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, CMat n))
      (fun Y : MatrixOrbit b₁ b₂ (cPermMatrix σ) => Y.val) X =
        fderiv ℝ (fun h : HorizontalModel b₁ b₂ σ =>
          preferredFactor σ X • horizontalValue b₁ b₂ σ h) 0 := by
  letI := overlapChartedSpace b₁ b₂ σ
  have hh := slice_val_mfderiv_eq (preferredOrbitSlice b₁ b₂ σ)
    (preferredOrbitSlice_covers b₁ b₂ σ) X
  rw [preferredOrbitSlice_coordinates_zero] at hh
  convert hh using 1 <;> rfl

theorem overlap_val_mfderiv_injective (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    letI := overlapChartedSpace b₁ b₂ σ
    Function.Injective (mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, CMat n))
      (fun Y : MatrixOrbit b₁ b₂ (cPermMatrix σ) => Y.val) X) :=
  slice_val_mfderiv_injective (preferredOrbitSlice b₁ b₂ σ)
    (preferredOrbitSlice_covers b₁ b₂ σ) X

/-- The statement on the manuscript's original two-factor matrix set. The
topology is exactly the inherited topology of that set. -/
theorem inA2Unitary_admits_manifold (c₁ c₂ : ℕ) (σ : Equiv.Perm (Fin n)) :
    ∃ cs : ChartedSpace
        (HorizontalModel (fun i : Fin n => i.val / c₁) (fun i : Fin n => i.val / c₂) σ)
        {X : CMat n // CInA2Unitary c₁ c₂ (cPermMatrix σ) X},
      letI := cs
      IsManifold
        (𝓘(ℝ, HorizontalModel (fun i : Fin n => i.val / c₁) (fun i : Fin n => i.val / c₂) σ))
        ⊤ {X : CMat n // CInA2Unitary c₁ c₂ (cPermMatrix σ) X} := by
  have hh : ∃ cs : ChartedSpace
      (HorizontalModel (fun i : Fin n => i.val / c₁) (fun i : Fin n => i.val / c₂) σ)
      (MatrixOrbit (fun i : Fin n => i.val / c₁) (fun i : Fin n => i.val / c₂) (cPermMatrix σ)),
      letI := cs
      IsManifold
        (𝓘(ℝ, HorizontalModel (fun i : Fin n => i.val / c₁) (fun i : Fin n => i.val / c₂) σ))
        ⊤ (MatrixOrbit (fun i : Fin n => i.val / c₁) (fun i : Fin n => i.val / c₂) (cPermMatrix σ)) :=
    ⟨overlapChartedSpace _ _ σ, overlapIsManifold _ _ σ⟩
  change ∃ cs : ChartedSpace
      (HorizontalModel (fun i : Fin n => i.val / c₁) (fun i : Fin n => i.val / c₂) σ)
      ↥(MulAction.orbit (FactorGroup (fun i : Fin n => i.val / c₁)
        (fun i : Fin n => i.val / c₂)) (cPermMatrix σ)),
      letI := cs
      IsManifold
        (𝓘(ℝ, HorizontalModel (fun i : Fin n => i.val / c₁) (fun i : Fin n => i.val / c₂) σ))
        ⊤ ↥(MulAction.orbit (FactorGroup (fun i : Fin n => i.val / c₁)
          (fun i : Fin n => i.val / c₂)) (cPermMatrix σ)) at hh
  rw [orbit_set_eq_inA2Unitary c₁ c₂ (cPermMatrix σ)] at hh
  exact hh

end GS.UnitaryManifold
