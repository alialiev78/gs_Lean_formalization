module

public import GS.UnitarySharing.Factors
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A Cayley atlas on the actual shared factor group

The chart model is the concrete subspace of supported tied skew-Hermitian matrices.
The source uses the existing matrix topology, and its inverse is defined on
the entire model.  Transition functions are restrictions of rational ambient
matrix formulas.  This establishes the factor manifold, not yet the shared
matrix-orbit manifold or its tangent bundle.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
open scoped Topology Manifold
namespace GS.UnitarySharing
variable {n : ℕ} {s : Pattern n}

/-- A total continuous linear extension of the shared chart coordinates. -/
def modelProjection (s : Pattern n) : CMat n →L[ℝ] Generator s :=
  ({ toFun := fun A => ⟨cFrobProjection (sharedSkewSpace s.size s.label) A,
        cFrobProjection_mem _ _⟩
     map_add' := by
       intro A B
       apply Subtype.ext
       exact map_add _ A B
     map_smul' := by
       intro a A
       apply Subtype.ext
       exact map_smul _ a A } : CMat n →ₗ[ℝ] Generator s).toContinuousLinearMap

@[simp] theorem modelProjection_val (s : Pattern n) (A : CMat n) :
    (modelProjection s A).val = cFrobProjection (sharedSkewSpace s.size s.label) A := rfl

theorem modelProjection_val_of_mem (s : Pattern n) (A : CMat n)
    (hA : A ∈ sharedSkewSpace s.size s.label) : (modelProjection s A).val = A :=
  cFrobProjection_of_mem _ _ hA

@[simp] theorem modelProjection_inclusion (C : Generator s) :
    modelProjection s C.val = C := by
  apply Subtype.ext
  exact modelProjection_val_of_mem s C.val C.property

/-- Open neighbourhood of Q inside the inherited shared-factor topology. -/
def factorSource (Q : Factor s) : Set (Factor s) :=
  {U | admissible ((Factor.matrix Q)ᴴ * Factor.matrix U)}

def factorCoordinates (Q : Factor s) (A : CMat n) : Generator s :=
  modelProjection s (cayley ((Factor.matrix Q)ᴴ * A))

/-- All shared skew coordinates reconstruct valid shared unitary factors. -/
def reconstruct (Q : Factor s) (C : Generator s) : Factor s :=
  Q * Factor.ofMatrix (cayley C.val) (cayley_shared s.positive s.divides C.property)

@[simp] theorem reconstruct_matrix (Q : Factor s) (C : Generator s) :
    Factor.matrix (reconstruct Q C) = Factor.matrix Q * cayley C.val := rfl

theorem factorSource_open (Q : Factor s) : IsOpen (factorSource Q) :=
  admissible_open.preimage
    (GS.UnitaryManifold.continuous_matrix_product continuous_const Factor.continuous_matrix)

@[simp] theorem base_mem_factorSource (Q : Factor s) : Q ∈ factorSource Q := by
  change admissible ((Factor.matrix Q)ᴴ * Factor.matrix Q)
  rw [(Factor.matrix_unitary Q).1]
  exact admissible_one

theorem centered_reconstruct (Q : Factor s) (C : Generator s) :
    (Factor.matrix Q)ᴴ * Factor.matrix (reconstruct Q C) = cayley C.val := by
  rw [reconstruct_matrix, ← Matrix.mul_assoc, (Factor.matrix_unitary Q).1,
    Matrix.one_mul]

theorem reconstruct_mem_source (Q : Factor s) (C : Generator s) :
    reconstruct Q C ∈ factorSource Q := by
  change admissible ((Factor.matrix Q)ᴴ * Factor.matrix (reconstruct Q C))
  rw [centered_reconstruct]
  exact admissible_cayley C.val (admissible_of_isSkew C.val C.property.2.1)

theorem centered_cayley_shared (Q U : Factor s) (hU : U ∈ factorSource Q) :
    cayley ((Factor.matrix Q)ᴴ * Factor.matrix U) ∈ sharedSkewSpace s.size s.label :=
  cayley_sharedSkew s.positive s.divides
    (shared_factor_mul s.positive s.divides
      (shared_factor_conjTranspose (Factor.matrix_shared Q)) (Factor.matrix_shared U)) hU

theorem factorCoordinates_val (Q U : Factor s) (hU : U ∈ factorSource Q) :
    (factorCoordinates Q (Factor.matrix U)).val =
      cayley ((Factor.matrix Q)ᴴ * Factor.matrix U) :=
  modelProjection_val_of_mem s _ (centered_cayley_shared Q U hU)

@[simp] theorem factorCoordinates_reconstruct (Q : Factor s) (C : Generator s) :
    factorCoordinates Q (Factor.matrix (reconstruct Q C)) = C := by
  unfold factorCoordinates
  rw [centered_reconstruct,
    cayley_involutive C.val (admissible_of_isSkew C.val C.property.2.1)]
  exact modelProjection_inclusion C

theorem reconstruct_factorCoordinates (Q U : Factor s) (hU : U ∈ factorSource Q) :
    reconstruct Q (factorCoordinates Q (Factor.matrix U)) = U := by
  apply Factor.matrix_injective
  rw [reconstruct_matrix, factorCoordinates_val Q U hU, cayley_involutive _ hU,
    ← Matrix.mul_assoc, (Factor.matrix_unitary Q).2, Matrix.one_mul]

@[simp] theorem reconstruct_zero (Q : Factor s) : reconstruct Q 0 = Q := by
  apply Factor.matrix_injective
  simp only [reconstruct_matrix, Submodule.coe_zero, cayley_zero, Matrix.mul_one]

@[simp] theorem factorCoordinates_base (Q : Factor s) :
    factorCoordinates Q (Factor.matrix Q) = 0 := by
  unfold factorCoordinates
  rw [(Factor.matrix_unitary Q).1, cayley_one, map_zero]

theorem factorCoordinates_smooth_at (Q : Factor s) (A : CMat n)
    (hA : admissible ((Factor.matrix Q)ᴴ * A)) :
    ContDiffAt ℝ ⊤ (factorCoordinates Q) A :=
  (modelProjection s).contDiff.contDiffAt.comp A
    (smooth_cayley_comp_at (smooth_mul_at contDiffAt_const contDiffAt_id) hA)

theorem reconstruct_matrix_smooth (Q : Factor s) :
    ContDiff ℝ ⊤ (fun C : Generator s => Factor.matrix (reconstruct Q C)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro C
  exact smooth_mul_at contDiffAt_const
    (smooth_cayley_comp_at
      (sharedSkewSpace (n := n) s.size s.label).subtypeL.contDiff.contDiffAt
      (admissible_of_isSkew C.val C.property.2.1))

theorem continuous_reconstruct (Q : Factor s) : Continuous (reconstruct Q) :=
  ((reconstruct_matrix_smooth Q).continuous.subtype_mk _).subtype_mk _

/-- A total extension on each side, with an open source and full linear target. -/
def factorPartialChart (Q : Factor s) : OpenPartialHomeomorph (Factor s) (Generator s) where
  toFun U := factorCoordinates Q (Factor.matrix U)
  invFun := reconstruct Q
  source := factorSource Q
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' C _ := reconstruct_mem_source Q C
  left_inv' U hU := reconstruct_factorCoordinates Q U hU
  right_inv' C _ := factorCoordinates_reconstruct Q C
  open_source := factorSource_open Q
  open_target := isOpen_univ
  continuousOn_toFun := by
    intro U hU
    exact ((factorCoordinates_smooth_at Q (Factor.matrix U) hU).continuousAt.comp
      Factor.continuous_matrix.continuousAt).continuousWithinAt
  continuousOn_invFun := (continuous_reconstruct Q).continuousOn

/-- The charted-space structure does not alter the existing topology. -/
instance factorChartedSpace (s : Pattern n) : ChartedSpace (Generator s) (Factor s) where
  atlas := Set.range factorPartialChart
  chartAt := factorPartialChart
  mem_chart_source := base_mem_factorSource
  chart_mem_atlas Q := ⟨Q, rfl⟩

theorem factorPartialChart_transition_smooth (Q U : Factor s) :
    ContDiffOn ℝ ⊤ ((factorPartialChart Q).symm.trans (factorPartialChart U))
      ((factorPartialChart Q).symm.trans (factorPartialChart U)).source := by
  intro C hC
  change C ∈ (Set.univ : Set (Generator s)) ∧ reconstruct Q C ∈ factorSource U at hC
  exact ((factorCoordinates_smooth_at U (Factor.matrix (reconstruct Q C)) hC.2).comp C
    (reconstruct_matrix_smooth Q).contDiffAt).contDiffWithinAt

/-- Smooth factor geometry is proved from the rational transitions.  This
instance does not claim that the two-factor image has already been charted. -/
instance factorIsManifold (s : Pattern n) : IsManifold (𝓘(ℝ, Generator s)) ⊤ (Factor s) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ Set.range factorPartialChart at he
  change e' ∈ Set.range factorPartialChart at he'
  obtain ⟨Q, rfl⟩ := he
  obtain ⟨U, rfl⟩ := he'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ] using factorPartialChart_transition_smooth Q U

/-- The smooth inclusion uses the inherited matrix topology. -/
theorem factor_matrix_contMDiff (s : Pattern n) :
    ContMDiff (𝓘(ℝ, Generator s)) (𝓘(ℝ, CMat n)) ⊤
      (Factor.matrix : Factor s → CMat n) := by
  intro Q
  rw [contMDiffAt_iff]
  refine ⟨Factor.continuous_matrix.continuousAt, ?_⟩
  change ContDiffWithinAt ℝ ⊤
    (fun x : Generator s => Factor.matrix (reconstruct Q x))
    (Set.range (id : Generator s → Generator s))
    (factorCoordinates Q (Factor.matrix Q))
  exact (reconstruct_matrix_smooth Q).contDiffAt.contDiffWithinAt

section Source
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- A criterion for maps valued in this explicitly constructed factor atlas. -/
theorem contMDiffAt_factor_of_matrix {f : M → Factor s} {x : M}
    (hf : ContMDiffAt I (𝓘(ℝ, CMat n)) ⊤ (fun y => Factor.matrix (f y)) x) :
    ContMDiffAt I (𝓘(ℝ, Generator s)) ⊤ f x := by
  rw [contMDiffAt_iff_target]
  refine ⟨tendsto_subtype_rng.mpr (tendsto_subtype_rng.mpr hf.continuousAt), ?_⟩
  change ContMDiffAt I (𝓘(ℝ, Generator s)) ⊤
    (fun y => factorCoordinates (f x) (Factor.matrix (f y))) x
  exact ContDiffAt.comp_contMDiffAt (I := I)
    (g := factorCoordinates (f x)) (f := fun y => Factor.matrix (f y))
    (factorCoordinates_smooth_at (f x) (Factor.matrix (f x))
      (base_mem_factorSource (f x))) hf

theorem contMDiff_factor_of_matrix {f : M → Factor s}
    (hf : ContMDiff I (𝓘(ℝ, CMat n)) ⊤ (fun y => Factor.matrix (f y))) :
    ContMDiff I (𝓘(ℝ, Generator s)) ⊤ f := by
  intro x
  exact contMDiffAt_factor_of_matrix (hf x)

theorem contMDiff_factor_iff_matrix {f : M → Factor s} :
    ContMDiff I (𝓘(ℝ, Generator s)) ⊤ f ↔
      ContMDiff I (𝓘(ℝ, CMat n)) ⊤ (fun y => Factor.matrix (f y)) := by
  constructor
  · intro hf
    exact (factor_matrix_contMDiff s).comp hf
  · exact contMDiff_factor_of_matrix
end Source

/-- Group multiplication is smooth for the tied factor atlas itself. -/
theorem factor_mul_contMDiff (s : Pattern n) :
    ContMDiff ((𝓘(ℝ, Generator s)).prod (𝓘(ℝ, Generator s)))
      (𝓘(ℝ, Generator s)) ⊤ (fun p : Factor s × Factor s => p.1 * p.2) := by
  apply contMDiff_factor_of_matrix
  have hl : ContMDiff ((𝓘(ℝ, Generator s)).prod (𝓘(ℝ, Generator s)))
      (𝓘(ℝ, CMat n)) ⊤ (fun p : Factor s × Factor s => Factor.matrix p.1) :=
    (factor_matrix_contMDiff s).comp contMDiff_fst
  have hr : ContMDiff ((𝓘(ℝ, Generator s)).prod (𝓘(ℝ, Generator s)))
      (𝓘(ℝ, CMat n)) ⊤ (fun p : Factor s × Factor s => Factor.matrix p.2) :=
    (factor_matrix_contMDiff s).comp contMDiff_snd
  have hm : ContDiff ℝ ⊤ (fun p : CMat n × CMat n => p.1 * p.2) :=
    contDiff_iff_contDiffAt.mpr (fun _ => smooth_mul_at contDiffAt_fst contDiffAt_snd)
  simpa only [Factor.matrix_mul, Function.comp_def] using hm.comp_contMDiff (hl.prodMk_space hr)

theorem factor_inv_contMDiff (s : Pattern n) :
    ContMDiff (𝓘(ℝ, Generator s)) (𝓘(ℝ, Generator s)) ⊤
      (fun Q : Factor s => Q⁻¹) := by
  apply contMDiff_factor_of_matrix
  have ht : ContDiff ℝ ⊤ (fun A : CMat n => Aᴴ) :=
    contDiff_iff_contDiffAt.mpr (fun _ => smooth_conjTranspose_at contDiffAt_id)
  simpa only [Factor.matrix_inv, Function.comp_def] using ht.comp_contMDiff (factor_matrix_contMDiff s)

instance factorContMDiffMul (s : Pattern n) :
    ContMDiffMul (𝓘(ℝ, Generator s)) ⊤ (Factor s) where
  toIsManifold := factorIsManifold s
  contMDiff_mul := factor_mul_contMDiff s

/-- Genuine mathlib Lie-group structure on the concrete compact subgroup. -/
instance factorLieGroup (s : Pattern n) : LieGroup (𝓘(ℝ, Generator s)) ⊤ (Factor s) where
  toContMDiffMul := factorContMDiffMul s
  contMDiff_inv := factor_inv_contMDiff s

theorem reconstruct_contMDiff (Q : Factor s) :
    ContMDiff (𝓘(ℝ, Generator s)) (𝓘(ℝ, Generator s)) ⊤ (reconstruct Q) :=
  contMDiff_factor_of_matrix (reconstruct_matrix_smooth Q).contMDiff

end GS.UnitarySharing
