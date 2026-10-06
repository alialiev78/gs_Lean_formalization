module

public import GS.SpecialUnitarySharing.ExponentialCoordinates
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The inherited-topology manifold of shared special-unitary factors

The chart coordinates are in the actual blockwise traceless generator space.
An inverse in the larger U chart is first constructed by IFT; determinant one
then forces its physical traces to vanish.  This proves that the chart covers
an open neighbourhood in the WHOLE SU factor group.  No SU manifold instance
or local surjectivity assumption is used in that construction.

Reconstruction is globally defined by exp(-2 A), but the chart target is only
an open neighbourhood of zero.  In particular, neither global injectivity nor
global openness of the exponential is asserted.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold Set Filter
open scoped Topology Manifold
namespace GS.SpecialUnitarySharing
variable {n : ℕ} {s : Pattern n}

/-- The actual inclusion of trace-free coordinates into unitary coordinates. -/
def generatorInclusion (s : Pattern n) : Generator s →L[ℝ] GS.UnitarySharing.Generator s :=
  ({ toFun := fun A => ⟨A.val, A.property.1⟩
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } :
       Generator s →ₗ[ℝ] GS.UnitarySharing.Generator s).toContinuousLinearMap

@[simp] theorem generatorInclusion_val (A : Generator s) :
    (generatorInclusion s A).val = A.val := rfl

def factorTarget (s : Pattern n) : Set (Generator s) :=
  generatorInclusion s ⁻¹' (expCoordinateData s).domain

theorem factorTarget_open (s : Pattern n) : IsOpen (factorTarget s) :=
  (expCoordinateData s).domain_open.preimage (generatorInclusion s).continuous

@[simp] theorem zero_mem_factorTarget (s : Pattern n) : (0 : Generator s) ∈ factorTarget s := by
  simpa only [factorTarget, Set.mem_preimage, map_zero] using (expCoordinateData s).zero_domain

/-- Ambient formula for the Cayley coordinate of the matrix centred at Q. -/
def centeredCoordinates (Q : SpecialFactor s) (M : CMat n) : GS.UnitarySharing.Generator s :=
  GS.UnitarySharing.factorCoordinates (1 : GS.UnitarySharing.Factor s)
    ((SpecialFactor.matrix Q)ᴴ * M)

def factorSource (Q : SpecialFactor s) : Set (SpecialFactor s) :=
  {V | admissible ((SpecialFactor.matrix Q)ᴴ * SpecialFactor.matrix V) ∧
    centeredCoordinates Q (SpecialFactor.matrix V) ∈ (expCoordinateData s).image}

/-- A total ambient extension; on the source projection removes nothing. -/
def factorCoordinates (Q : SpecialFactor s) (M : CMat n) : Generator s :=
  modelProjection s ((expCoordinateData s).inverse (centeredCoordinates Q M)).val

/-- Every coordinate, including those outside the local chart, gives an SU factor. -/
def reconstruct (Q : SpecialFactor s) (A : Generator s) : SpecialFactor s :=
  Q * SpecialFactor.ofMatrix (cMatrixExp ((-2 : ℝ) • A.val))
    (cMatrixExp_special s _ ((specialSkewSpace s).smul_mem (-2 : ℝ) A.property))

@[simp] theorem reconstruct_matrix (Q : SpecialFactor s) (A : Generator s) :
    SpecialFactor.matrix (reconstruct Q A) =
      SpecialFactor.matrix Q * cMatrixExp ((-2 : ℝ) • A.val) := rfl

@[simp] theorem reconstruct_zero (Q : SpecialFactor s) : reconstruct Q 0 = Q := by
  apply SpecialFactor.matrix_injective
  simp only [reconstruct_matrix, Submodule.coe_zero, smul_zero, cMatrixExp_zero, Matrix.mul_one]

@[simp] theorem centeredCoordinates_base (Q : SpecialFactor s) :
    centeredCoordinates Q (SpecialFactor.matrix Q) = 0 := by
  unfold centeredCoordinates
  rw [(SpecialFactor.matrix_unitary Q).1]
  simpa only [GS.UnitarySharing.Factor.matrix_one] using
    GS.UnitarySharing.factorCoordinates_base (1 : GS.UnitarySharing.Factor s)

@[simp] theorem factorCoordinates_base (Q : SpecialFactor s) :
    factorCoordinates Q (SpecialFactor.matrix Q) = 0 := by
  simp only [factorCoordinates, centeredCoordinates_base,
    (expCoordinateData s).inverse_zero, Submodule.coe_zero, map_zero]

@[simp] theorem base_mem_factorSource (Q : SpecialFactor s) : Q ∈ factorSource Q := by
  refine ⟨?_, ?_⟩
  · rw [(SpecialFactor.matrix_unitary Q).1]
    exact admissible_one
  · simpa only [centeredCoordinates_base] using (expCoordinateData s).zero_image

theorem centeredCoordinates_smooth_at (Q : SpecialFactor s) (M : CMat n)
    (hM : admissible ((SpecialFactor.matrix Q)ᴴ * M)) :
    ContDiffAt ℝ ⊤ (centeredCoordinates Q) M := by
  have hc := GS.UnitarySharing.factorCoordinates_smooth_at
    (1 : GS.UnitarySharing.Factor s) ((SpecialFactor.matrix Q)ᴴ * M)
    (by simpa only [GS.UnitarySharing.Factor.matrix_one, Matrix.conjTranspose_one,
      Matrix.one_mul] using hM)
  exact hc.comp M (smooth_mul_at contDiffAt_const contDiffAt_id)

/-- Source openness is proved before installing any SU charted-space instance. -/
theorem factorSource_open (Q : SpecialFactor s) : IsOpen (factorSource Q) := by
  rw [isOpen_iff_mem_nhds]
  intro V hV
  have hm : Continuous (fun U : SpecialFactor s => (SpecialFactor.matrix Q)ᴴ *
      SpecialFactor.matrix U) :=
    GS.UnitaryManifold.continuous_matrix_product continuous_const SpecialFactor.continuous_matrix
  have had := (admissible_open.preimage hm).mem_nhds hV.1
  have hc := (centeredCoordinates_smooth_at Q (SpecialFactor.matrix V) hV.1).continuousAt.comp
    SpecialFactor.continuous_matrix.continuousAt
  have hi := hc.preimage_mem_nhds ((expCoordinateData s).image_open.mem_nhds hV.2)
  exact inter_mem had hi

private theorem cayley_unitaryCoordinates (s : Pattern n) (M : CMat n)
    (hM : GS.UnitarySharing.SharedUnitaryFactor s.size s.label M) (ha : admissible M) :
    cayley (GS.UnitarySharing.factorCoordinates (1 : GS.UnitarySharing.Factor s) M).val = M := by
  let U := GS.UnitarySharing.Factor.ofMatrix M hM
  have hs : U ∈ GS.UnitarySharing.factorSource (1 : GS.UnitarySharing.Factor s) := by
    change admissible ((1 : CMat n)ᴴ * M)
    simpa only [Matrix.conjTranspose_one, Matrix.one_mul] using ha
  have hc := GS.UnitarySharing.factorCoordinates_val (1 : GS.UnitarySharing.Factor s) U hs
  have hc' : (GS.UnitarySharing.factorCoordinates (1 : GS.UnitarySharing.Factor s) M).val =
      cayley M := by
    simpa only [U, GS.UnitarySharing.Factor.matrix_ofMatrix,
      GS.UnitarySharing.Factor.matrix_one, Matrix.conjTranspose_one, Matrix.one_mul] using hc
  rw [hc', cayley_involutive M ha]

/-- Inverse IFT coordinates reconstruct the entire centred factor. -/
theorem inverseCoordinates_reconstruct_center (Q V : SpecialFactor s)
    (hV : V ∈ factorSource Q) :
    unitaryExpParam s ((expCoordinateData s).inverse
      (centeredCoordinates Q (SpecialFactor.matrix V))) =
        (SpecialFactor.matrix Q)ᴴ * SpecialFactor.matrix V := by
  let A := (expCoordinateData s).inverse (centeredCoordinates Q (SpecialFactor.matrix V))
  have hA := (expCoordinateData s).map_image _ hV.2
  have he := (expCoordinateData s).right_inverse _ hV.2
  have hm := (special_factor_mul _ _
    (special_factor_conjTranspose _ (SpecialFactor.matrix_special Q))
    (SpecialFactor.matrix_special V)).1
  calc
    unitaryExpParam s A = cayley (unitaryExpCoordinates s A).val :=
      (cayley_unitaryCoordinates s _ (unitaryExpParam_shared s A)
        ((expCoordinateData s).good hA).1).symm
    _ = cayley (centeredCoordinates Q (SpecialFactor.matrix V)).val := by rw [he]
    _ = (SpecialFactor.matrix Q)ᴴ * SpecialFactor.matrix V :=
      cayley_unitaryCoordinates s _ hm hV.1

theorem inverseCoordinates_special (Q V : SpecialFactor s) (hV : V ∈ factorSource Q) :
    ((expCoordinateData s).inverse (centeredCoordinates Q (SpecialFactor.matrix V))).val
      ∈ specialSkewSpace s := by
  let A := (expCoordinateData s).inverse (centeredCoordinates Q (SpecialFactor.matrix V))
  refine ⟨A.property, traceFree_of_local_special_exp s A
    ((expCoordinateData s).map_image _ hV.2) ?_⟩
  rw [inverseCoordinates_reconstruct_center Q V hV]
  exact (special_factor_mul _ _
    (special_factor_conjTranspose _ (SpecialFactor.matrix_special Q))
    (SpecialFactor.matrix_special V)).2

theorem factorCoordinates_val (Q V : SpecialFactor s) (hV : V ∈ factorSource Q) :
    (factorCoordinates Q (SpecialFactor.matrix V)).val =
      ((expCoordinateData s).inverse (centeredCoordinates Q (SpecialFactor.matrix V))).val :=
  cFrobProjection_of_mem _ _ (inverseCoordinates_special Q V hV)

theorem factorCoordinates_inclusion (Q V : SpecialFactor s) (hV : V ∈ factorSource Q) :
    generatorInclusion s (factorCoordinates Q (SpecialFactor.matrix V)) =
      (expCoordinateData s).inverse (centeredCoordinates Q (SpecialFactor.matrix V)) := by
  apply Subtype.ext
  exact factorCoordinates_val Q V hV

theorem factorCoordinates_mem_target (Q V : SpecialFactor s) (hV : V ∈ factorSource Q) :
    factorCoordinates Q (SpecialFactor.matrix V) ∈ factorTarget s := by
  change generatorInclusion s _ ∈ (expCoordinateData s).domain
  rw [factorCoordinates_inclusion Q V hV]
  exact (expCoordinateData s).map_image _ hV.2

theorem centered_reconstruct (Q : SpecialFactor s) (A : Generator s) :
    (SpecialFactor.matrix Q)ᴴ * SpecialFactor.matrix (reconstruct Q A) =
      unitaryExpParam s (generatorInclusion s A) := by
  rw [reconstruct_matrix, ← Matrix.mul_assoc, (SpecialFactor.matrix_unitary Q).1,
    Matrix.one_mul]
  rfl

theorem centeredCoordinates_reconstruct (Q : SpecialFactor s) (A : Generator s) :
    centeredCoordinates Q (SpecialFactor.matrix (reconstruct Q A)) =
      unitaryExpCoordinates s (generatorInclusion s A) := by
  unfold centeredCoordinates unitaryExpCoordinates
  rw [centered_reconstruct]

theorem reconstruct_mem_source (Q : SpecialFactor s) (A : Generator s)
    (hA : A ∈ factorTarget s) : reconstruct Q A ∈ factorSource Q := by
  refine ⟨?_, ?_⟩
  · rw [centered_reconstruct]
    exact ((expCoordinateData s).good hA).1
  · rw [centeredCoordinates_reconstruct]
    exact (expCoordinateData s).map_domain _ hA

theorem factorCoordinates_reconstruct (Q : SpecialFactor s) (A : Generator s)
    (hA : A ∈ factorTarget s) :
    factorCoordinates Q (SpecialFactor.matrix (reconstruct Q A)) = A := by
  unfold factorCoordinates
  rw [centeredCoordinates_reconstruct, (expCoordinateData s).left_inverse _ hA]
  exact modelProjection_inclusion A

theorem reconstruct_factorCoordinates (Q V : SpecialFactor s) (hV : V ∈ factorSource Q) :
    reconstruct Q (factorCoordinates Q (SpecialFactor.matrix V)) = V := by
  apply SpecialFactor.matrix_injective
  rw [reconstruct_matrix, factorCoordinates_val Q V hV]
  change SpecialFactor.matrix Q * unitaryExpParam s
    ((expCoordinateData s).inverse (centeredCoordinates Q (SpecialFactor.matrix V))) = _
  rw [inverseCoordinates_reconstruct_center Q V hV, ← Matrix.mul_assoc,
    (SpecialFactor.matrix_unitary Q).2, Matrix.one_mul]

theorem reconstruct_matrix_smooth (Q : SpecialFactor s) :
    ContDiff ℝ ⊤ (fun A : Generator s => SpecialFactor.matrix (reconstruct Q A)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro A
  exact smooth_mul_at contDiffAt_const
    ((unitaryExpParam_smooth s).comp (generatorInclusion s).contDiff).contDiffAt

theorem continuous_reconstruct (Q : SpecialFactor s) : Continuous (reconstruct Q) :=
  (((reconstruct_matrix_smooth Q).continuous.subtype_mk _).subtype_mk _).subtype_mk _

theorem factorCoordinates_smooth_at (Q : SpecialFactor s) (M : CMat n)
    (ha : admissible ((SpecialFactor.matrix Q)ᴴ * M))
    (hi : centeredCoordinates Q M ∈ (expCoordinateData s).image) :
    ContDiffAt ℝ ⊤ (factorCoordinates Q) M := by
  have hc := centeredCoordinates_smooth_at Q M ha
  have hv := (GS.UnitarySharing.sharedSkewSpace (n := n) s.size s.label).subtypeL.contDiff.contDiffAt
  exact (modelProjection s).contDiff.contDiffAt.comp M
    (hv.comp M (((expCoordinateData s).inverse_smooth _ hi).comp M hc))

/-- Both domains are open in their original topologies; the target is local. -/
def factorPartialChart (Q : SpecialFactor s) : OpenPartialHomeomorph (SpecialFactor s) (Generator s) where
  toFun V := factorCoordinates Q (SpecialFactor.matrix V)
  invFun := reconstruct Q
  source := factorSource Q
  target := factorTarget s
  map_source' V hV := factorCoordinates_mem_target Q V hV
  map_target' A hA := reconstruct_mem_source Q A hA
  left_inv' V hV := reconstruct_factorCoordinates Q V hV
  right_inv' A hA := factorCoordinates_reconstruct Q A hA
  open_source := factorSource_open Q
  open_target := factorTarget_open s
  continuousOn_toFun := by
    intro V hV
    exact ((factorCoordinates_smooth_at Q (SpecialFactor.matrix V) hV.1 hV.2).continuousAt.comp
      SpecialFactor.continuous_matrix.continuousAt).continuousWithinAt
  continuousOn_invFun := (continuous_reconstruct Q).continuousOn

instance specialFactorChartedSpace (s : Pattern n) : ChartedSpace (Generator s) (SpecialFactor s) where
  atlas := Set.range factorPartialChart
  chartAt := factorPartialChart
  mem_chart_source := base_mem_factorSource
  chart_mem_atlas Q := ⟨Q, rfl⟩

theorem factorPartialChart_transition_smooth (Q V : SpecialFactor s) :
    ContDiffOn ℝ ⊤ ((factorPartialChart Q).symm.trans (factorPartialChart V))
      ((factorPartialChart Q).symm.trans (factorPartialChart V)).source := by
  intro A hA
  change A ∈ factorTarget s ∧ reconstruct Q A ∈ factorSource V at hA
  exact ((factorCoordinates_smooth_at V (SpecialFactor.matrix (reconstruct Q A))
    hA.2.1 hA.2.2).comp A (reconstruct_matrix_smooth Q).contDiffAt).contDiffWithinAt

/-- The manifold instance belongs to the smaller SU group, not to the U group. -/
instance specialFactorIsManifold (s : Pattern n) :
    IsManifold (𝓘(ℝ, Generator s)) ⊤ (SpecialFactor s) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ Set.range factorPartialChart at he
  change e' ∈ Set.range factorPartialChart at he'
  obtain ⟨Q, rfl⟩ := he
  obtain ⟨V, rfl⟩ := he'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ] using factorPartialChart_transition_smooth Q V

theorem factor_matrix_contMDiff (s : Pattern n) :
    ContMDiff (𝓘(ℝ, Generator s)) (𝓘(ℝ, CMat n)) ⊤
      (SpecialFactor.matrix : SpecialFactor s → CMat n) := by
  intro Q
  rw [contMDiffAt_iff]
  refine ⟨SpecialFactor.continuous_matrix.continuousAt, ?_⟩
  change ContDiffWithinAt ℝ ⊤
    (fun A : Generator s => SpecialFactor.matrix (reconstruct Q A))
    (Set.range (id : Generator s → Generator s))
    (factorCoordinates Q (SpecialFactor.matrix Q))
  exact (reconstruct_matrix_smooth Q).contDiffAt.contDiffWithinAt

section Source
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiffAt_factor_of_matrix {f : M → SpecialFactor s} {x : M}
    (hf : ContMDiffAt I (𝓘(ℝ, CMat n)) ⊤ (fun y => SpecialFactor.matrix (f y)) x) :
    ContMDiffAt I (𝓘(ℝ, Generator s)) ⊤ f x := by
  rw [contMDiffAt_iff_target]
  refine ⟨tendsto_subtype_rng.mpr (tendsto_subtype_rng.mpr (tendsto_subtype_rng.mpr hf.continuousAt)), ?_⟩
  change ContMDiffAt I (𝓘(ℝ, Generator s)) ⊤
    (fun y => factorCoordinates (f x) (SpecialFactor.matrix (f y))) x
  exact ContDiffAt.comp_contMDiffAt (I := I)
    (g := factorCoordinates (f x)) (f := fun y => SpecialFactor.matrix (f y))
    (factorCoordinates_smooth_at (f x) (SpecialFactor.matrix (f x))
      (base_mem_factorSource (f x)).1 (base_mem_factorSource (f x)).2) hf

theorem contMDiff_factor_of_matrix {f : M → SpecialFactor s}
    (hf : ContMDiff I (𝓘(ℝ, CMat n)) ⊤ (fun y => SpecialFactor.matrix (f y))) :
    ContMDiff I (𝓘(ℝ, Generator s)) ⊤ f := fun x => contMDiffAt_factor_of_matrix (hf x)

theorem contMDiff_factor_iff_matrix {f : M → SpecialFactor s} :
    ContMDiff I (𝓘(ℝ, Generator s)) ⊤ f ↔
      ContMDiff I (𝓘(ℝ, CMat n)) ⊤ (fun y => SpecialFactor.matrix (f y)) := by
  constructor
  · intro hf
    exact (factor_matrix_contMDiff s).comp hf
  · exact contMDiff_factor_of_matrix
end Source

/-- Exponential reconstruction is open only on its chart target. -/
theorem reconstruct_image_open (Q : SpecialFactor s) (V : Set (Generator s))
    (hV : IsOpen V) (hsub : V ⊆ factorTarget s) : IsOpen (reconstruct Q '' V) :=
  (factorPartialChart Q).isOpen_image_symm_of_subset_target hV hsub

/-- Group multiplication is smooth for the tied factor atlas itself. -/
theorem factor_mul_contMDiff (s : Pattern n) :
    ContMDiff ((𝓘(ℝ, Generator s)).prod (𝓘(ℝ, Generator s)))
      (𝓘(ℝ, Generator s)) ⊤ (fun p : SpecialFactor s × SpecialFactor s => p.1 * p.2) := by
  apply contMDiff_factor_of_matrix
  have hl : ContMDiff ((𝓘(ℝ, Generator s)).prod (𝓘(ℝ, Generator s)))
      (𝓘(ℝ, CMat n)) ⊤ (fun p : SpecialFactor s × SpecialFactor s => SpecialFactor.matrix p.1) :=
    (factor_matrix_contMDiff s).comp contMDiff_fst
  have hr : ContMDiff ((𝓘(ℝ, Generator s)).prod (𝓘(ℝ, Generator s)))
      (𝓘(ℝ, CMat n)) ⊤ (fun p : SpecialFactor s × SpecialFactor s => SpecialFactor.matrix p.2) :=
    (factor_matrix_contMDiff s).comp contMDiff_snd
  have hm : ContDiff ℝ ⊤ (fun p : CMat n × CMat n => p.1 * p.2) :=
    contDiff_iff_contDiffAt.mpr (fun _ => smooth_mul_at contDiffAt_fst contDiffAt_snd)
  simpa only [SpecialFactor.matrix_mul] using hm.comp_contMDiff (hl.prodMk_space hr)

theorem factor_inv_contMDiff (s : Pattern n) :
    ContMDiff (𝓘(ℝ, Generator s)) (𝓘(ℝ, Generator s)) ⊤
      (fun Q : SpecialFactor s => Q⁻¹) := by
  apply contMDiff_factor_of_matrix
  have ht : ContDiff ℝ ⊤ (fun A : CMat n => Aᴴ) :=
    contDiff_iff_contDiffAt.mpr (fun _ => smooth_conjTranspose_at contDiffAt_id)
  simpa only [SpecialFactor.matrix_inv] using ht.comp_contMDiff (factor_matrix_contMDiff s)

instance specialFactorContMDiffMul (s : Pattern n) :
    ContMDiffMul (𝓘(ℝ, Generator s)) ⊤ (SpecialFactor s) where
  toIsManifold := specialFactorIsManifold s
  contMDiff_mul := factor_mul_contMDiff s

/-- Genuine mathlib Lie-group structure on the concrete compact subgroup. -/
instance specialFactorLieGroup (s : Pattern n) : LieGroup (𝓘(ℝ, Generator s)) ⊤ (SpecialFactor s) where
  toContMDiffMul := specialFactorContMDiffMul s
  contMDiff_inv := factor_inv_contMDiff s

theorem reconstruct_contMDiff (Q : SpecialFactor s) :
    ContMDiff (𝓘(ℝ, Generator s)) (𝓘(ℝ, Generator s)) ⊤ (reconstruct Q) :=
  contMDiff_factor_of_matrix (reconstruct_matrix_smooth Q).contMDiff

end GS.SpecialUnitarySharing
