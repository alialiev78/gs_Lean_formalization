module

public import GS.OverlapGeometry.LocalProduct
public import GS.OverlapGeometry.ProjectedSlice
public import GS.OverlapGeometry.FactorChartOpen
public import GS.OverlapGeometry.SliceAtlas

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
open Matrix GS GS.LieAction GS.CayleyCharts GS.ManifoldCompletion Set Filter
open scoped Topology Manifold

namespace GS.OverlapGeometry
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))

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
    orbitMapToOrbit b₁ b₂ (permMatrix σ)
      (factorLift 1 (goodProductChart b₁ b₂ σ z)) = horizontalPoint b₁ b₂ σ z.1 := by
  apply Subtype.ext
  change factorLift 1 (sliceProduct b₁ b₂ σ z) • permMatrix σ = _
  have hz' : factorLift (1 : FactorGroup b₁ b₂) z.1.val * factorLift 1 z.2.val ∈
      factorSource 1 := hz.2
  rw [sliceProduct, factorProductCoordinates_eq,
    factorLift_factorCoordinates 1 _ hz', mul_smul,
    kernel_factorLift_stabilizes (permMatrix σ) z.2.val z.2.property]
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
    (fun x => orbitMapToOrbit b₁ b₂ (permMatrix σ) (factorLift 1 x))
    (horizontalPoint b₁ b₂ σ) (factorLift_orbit_isOpenMap 1 (permMatrix σ))
    (goodProductChart_orbit b₁ b₂ σ) _ (horizontalChartDomain_open b₁ b₂ σ)
  intro h hh
  exact ⟨0, hh.2⟩

/-- A concrete ambient smooth slice at the permutation matrix. -/
def baseOrbitSlice :
    SmoothSlice (E := HorizontalModel b₁ b₂ σ)
      (MulAction.orbit (FactorGroup b₁ b₂) (permMatrix σ)) where
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
def orbitTranslate (g : FactorGroup b₁ b₂) (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    MatrixOrbit b₁ b₂ (permMatrix σ) :=
  ⟨g • X.val, by
    obtain ⟨h, hh⟩ := X.property
    exact ⟨g * h, by simpa only [mul_smul, hh]⟩⟩

@[simp] theorem orbitTranslate_val (g : FactorGroup b₁ b₂)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    (orbitTranslate b₁ b₂ σ g X).val = g • X.val := rfl

theorem orbitTranslate_continuous (g : FactorGroup b₁ b₂) :
    Continuous (orbitTranslate b₁ b₂ σ g) :=
  (continuous_subtype_val.const_smul g).subtype_mk _

@[simp] theorem orbitTranslate_inv (g : FactorGroup b₁ b₂)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    orbitTranslate b₁ b₂ σ g⁻¹ (orbitTranslate b₁ b₂ σ g X) = X := by
  apply Subtype.ext
  exact inv_smul_smul g X.val

@[simp] theorem orbitTranslate_inv' (g : FactorGroup b₁ b₂)
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    orbitTranslate b₁ b₂ σ g (orbitTranslate b₁ b₂ σ g⁻¹ X) = X := by
  apply Subtype.ext
  exact smul_inv_smul g X.val

/-- Translate the constructed slice from the permutation matrix to an
arbitrary point, without changing the common horizontal model. -/
def translatedOrbitSlice (g : FactorGroup b₁ b₂) :
    SmoothSlice (E := HorizontalModel b₁ b₂ σ)
      (MulAction.orbit (FactorGroup b₁ b₂) (permMatrix σ)) where
  source := orbitTranslate b₁ b₂ σ g⁻¹ ⁻¹' (baseOrbitSlice b₁ b₂ σ).source
  target := (baseOrbitSlice b₁ b₂ σ).target
  coordinates := fun A => (baseOrbitSlice b₁ b₂ σ).coordinates (g⁻¹ • A)
  parametrization := fun h => orbitTranslate b₁ b₂ σ g
    ((baseOrbitSlice b₁ b₂ σ).parametrization h)
  open_source := (baseOrbitSlice b₁ b₂ σ).open_source.preimage
    (orbitTranslate_continuous b₁ b₂ σ g⁻¹)
  open_target := (baseOrbitSlice b₁ b₂ σ).open_target
  coordinates_smooth := by
    intro X hX
    exact ((baseOrbitSlice b₁ b₂ σ).coordinates_smooth
      (orbitTranslate b₁ b₂ σ g⁻¹ X) hX).comp X.val
      (fixed_action_smooth g⁻¹).contDiffAt
  parametrization_smooth :=
    (fixed_action_smooth g).comp (baseOrbitSlice b₁ b₂ σ).parametrization_smooth
  maps_source := fun X hX => (baseOrbitSlice b₁ b₂ σ).maps_source
    (orbitTranslate b₁ b₂ σ g⁻¹ X) hX
  maps_target := by
    intro h hh
    change orbitTranslate b₁ b₂ σ g⁻¹
      (orbitTranslate b₁ b₂ σ g ((baseOrbitSlice b₁ b₂ σ).parametrization h)) ∈
        (baseOrbitSlice b₁ b₂ σ).source
    rw [orbitTranslate_inv]
    exact (baseOrbitSlice b₁ b₂ σ).maps_target h hh
  left_inverse := by
    intro X hX
    change orbitTranslate b₁ b₂ σ g ((baseOrbitSlice b₁ b₂ σ).parametrization
      ((baseOrbitSlice b₁ b₂ σ).coordinates
        (orbitTranslate b₁ b₂ σ g⁻¹ X).val)) = X
    rw [(baseOrbitSlice b₁ b₂ σ).left_inverse _ hX, orbitTranslate_inv']
  right_inverse := by
    intro h hh
    change (baseOrbitSlice b₁ b₂ σ).coordinates
      (g⁻¹ • (g • ((baseOrbitSlice b₁ b₂ σ).parametrization h).val)) = h
    rw [inv_smul_smul]
    exact (baseOrbitSlice b₁ b₂ σ).right_inverse h hh

theorem translatedOrbitSlice_centre_mem (g : FactorGroup b₁ b₂) :
    orbitMapToOrbit b₁ b₂ (permMatrix σ) g ∈ (translatedOrbitSlice b₁ b₂ σ g).source := by
  have he : orbitTranslate b₁ b₂ σ g⁻¹
      (orbitMapToOrbit b₁ b₂ (permMatrix σ) g) = horizontalPoint b₁ b₂ σ 0 := by
    apply Subtype.ext
    change g⁻¹ • (g • permMatrix σ) = (horizontalPoint b₁ b₂ σ 0).val
    rw [inv_smul_smul, horizontalPoint_val, horizontalValue_zero]
  change orbitTranslate b₁ b₂ σ g⁻¹ _ ∈
    horizontalPoint b₁ b₂ σ '' horizontalChartDomain b₁ b₂ σ
  rw [he]
  exact ⟨0, horizontalChartDomain_zero b₁ b₂ σ, rfl⟩

theorem translatedOrbitSlice_centre_coordinates (g : FactorGroup b₁ b₂) :
    (translatedOrbitSlice b₁ b₂ σ g).coordinates
      (orbitMapToOrbit b₁ b₂ (permMatrix σ) g).val = 0 := by
  change (projectedSliceData b₁ b₂ σ).coordinates (g⁻¹ • (g • permMatrix σ)) = 0
  rw [inv_smul_smul, ← horizontalValue_zero b₁ b₂ σ]
  exact (projectedSliceData b₁ b₂ σ).left_inverse 0 (projectedSliceData b₁ b₂ σ).zero_mem

def preferredOrbitSlice (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    SmoothSlice (E := HorizontalModel b₁ b₂ σ)
      (MulAction.orbit (FactorGroup b₁ b₂) (permMatrix σ)) :=
  translatedOrbitSlice b₁ b₂ σ (preferredFactor σ X)

theorem preferredOrbitSlice_covers (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    X ∈ (preferredOrbitSlice b₁ b₂ σ X).source := by
  have hh := translatedOrbitSlice_centre_mem b₁ b₂ σ (preferredFactor σ X)
  simpa only [preferredFactor_spec, preferredOrbitSlice] using hh

theorem preferredOrbitSlice_coordinates_zero (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    (preferredOrbitSlice b₁ b₂ σ X).coordinates X.val = 0 := by
  have hh := translatedOrbitSlice_centre_coordinates b₁ b₂ σ (preferredFactor σ X)
  simpa only [preferredFactor_spec, preferredOrbitSlice] using hh

/-- An atlas on the actual orbit with its inherited matrix topology, for
arbitrary overlapping partitions. It is explicit rather than a global instance
so the no-overlap atlas can coexist with this smaller horizontal model. -/
def overlapChartedSpace :
    ChartedSpace (HorizontalModel b₁ b₂ σ) (MatrixOrbit b₁ b₂ (permMatrix σ)) :=
  sliceChartedSpace (preferredOrbitSlice b₁ b₂ σ) (preferredOrbitSlice_covers b₁ b₂ σ)

theorem overlapIsManifold :
    letI := overlapChartedSpace b₁ b₂ σ
    IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤ (MatrixOrbit b₁ b₂ (permMatrix σ)) :=
  slice_isManifold (preferredOrbitSlice b₁ b₂ σ) (preferredOrbitSlice_covers b₁ b₂ σ)

theorem overlap_val_contMDiff :
    letI := overlapChartedSpace b₁ b₂ σ
    ContMDiff (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, Mat n)) ⊤
      (fun X : MatrixOrbit b₁ b₂ (permMatrix σ) => X.val) :=
  slice_val_contMDiff (preferredOrbitSlice b₁ b₂ σ) (preferredOrbitSlice_covers b₁ b₂ σ)

theorem overlap_val_mfderiv_eq (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    letI := overlapChartedSpace b₁ b₂ σ
    mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, Mat n))
      (fun Y : MatrixOrbit b₁ b₂ (permMatrix σ) => Y.val) X =
        fderiv ℝ (fun h : HorizontalModel b₁ b₂ σ =>
          preferredFactor σ X • horizontalValue b₁ b₂ σ h) 0 := by
  letI := overlapChartedSpace b₁ b₂ σ
  have hh := slice_val_mfderiv_eq (preferredOrbitSlice b₁ b₂ σ)
    (preferredOrbitSlice_covers b₁ b₂ σ) X
  rw [preferredOrbitSlice_coordinates_zero] at hh
  simpa only [preferredOrbitSlice, translatedOrbitSlice, baseOrbitSlice,
    orbitTranslate_val, horizontalPoint_val] using hh

theorem overlap_val_mfderiv_injective (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    letI := overlapChartedSpace b₁ b₂ σ
    Function.Injective (mfderiv (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (𝓘(ℝ, Mat n))
      (fun Y : MatrixOrbit b₁ b₂ (permMatrix σ) => Y.val) X) :=
  slice_val_mfderiv_injective (preferredOrbitSlice b₁ b₂ σ)
    (preferredOrbitSlice_covers b₁ b₂ σ) X

/-- The statement on the manuscript's original two-factor matrix set. The
topology is exactly the inherited topology of that set. -/
theorem inA2Orth_admits_manifold (c₁ c₂ : ℕ) (σ : Equiv.Perm (Fin n)) :
    ∃ cs : ChartedSpace
        (HorizontalModel (fun i : Fin n => i.val / c₁) (fun i : Fin n => i.val / c₂) σ)
        {X : Mat n // InA2Orth c₁ c₂ (permMatrix σ) X},
      letI := cs
      IsManifold
        (𝓘(ℝ, HorizontalModel (fun i : Fin n => i.val / c₁) (fun i : Fin n => i.val / c₂) σ))
        ⊤ {X : Mat n // InA2Orth c₁ c₂ (permMatrix σ) X} := by
  have hh : ∃ cs : ChartedSpace
      (HorizontalModel (fun i : Fin n => i.val / c₁) (fun i : Fin n => i.val / c₂) σ)
      (MatrixOrbit (fun i : Fin n => i.val / c₁) (fun i : Fin n => i.val / c₂) (permMatrix σ)),
      letI := cs
      IsManifold
        (𝓘(ℝ, HorizontalModel (fun i : Fin n => i.val / c₁) (fun i : Fin n => i.val / c₂) σ))
        ⊤ (MatrixOrbit (fun i : Fin n => i.val / c₁) (fun i : Fin n => i.val / c₂) (permMatrix σ)) :=
    ⟨overlapChartedSpace _ _ σ, overlapIsManifold _ _ σ⟩
  change ∃ cs : ChartedSpace
      (HorizontalModel (fun i : Fin n => i.val / c₁) (fun i : Fin n => i.val / c₂) σ)
      ↥(MulAction.orbit (FactorGroup (fun i : Fin n => i.val / c₁)
        (fun i : Fin n => i.val / c₂)) (permMatrix σ)),
      letI := cs
      IsManifold
        (𝓘(ℝ, HorizontalModel (fun i : Fin n => i.val / c₁) (fun i : Fin n => i.val / c₂) σ))
        ⊤ ↥(MulAction.orbit (FactorGroup (fun i : Fin n => i.val / c₁)
          (fun i : Fin n => i.val / c₂)) (permMatrix σ)) at hh
  rw [orbit_set_eq_inA2Orth c₁ c₂ (permMatrix σ)] at hh
  exact hh

end GS.OverlapGeometry
