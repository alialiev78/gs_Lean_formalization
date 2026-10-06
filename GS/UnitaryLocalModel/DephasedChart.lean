module

public import GS.UnitaryLocalModel.DephasedDifferential

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# An actual local chart on the dephased unitary slice

The real implicit function theorem is applied to the proved surjective anchor
constraint derivative. Positivity is an open restriction. All unitary and
slice spaces retain their inherited matrix topology.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryManifold Set
open scoped Topology
namespace GS.UnitaryLocalModel
variable {q : ℕ}

/-- The strict inequalities defining the positive branch of the anchor slice. -/
def AnchorPositive (Q A : CMat q) (o : Fin q) : Prop :=
  (∀ i, 0 < (A i o / Q i o).re) ∧ (∀ j, 0 < (A o j / Q o j).re)

theorem anchorPositive_open (Q : CMat q) (o : Fin q) :
    IsOpen {A : CMat q | AnchorPositive Q A o} := by
  have hc : ∀ i : Fin q, IsOpen {A : CMat q | 0 < (A i o / Q i o).re} := by
    intro i
    exact isOpen_lt continuous_const
      ((Complex.continuous_re).comp (((continuous_apply o).comp (continuous_apply i)).div_const _))
  have hr : ∀ j : Fin q, IsOpen {A : CMat q | 0 < (A o j / Q o j).re} := by
    intro j
    exact isOpen_lt continuous_const
      ((Complex.continuous_re).comp (((continuous_apply j).comp (continuous_apply o)).div_const _))
  convert (isOpen_iInter_of_finite hc).inter (isOpen_iInter_of_finite hr) using 1
  ext A
  simp [AnchorPositive]

theorem anchorPositive_self (Q : CMat q) (o : Fin q)
    (hQ : AnchorNonzero Q Q o) : AnchorPositive Q Q o := by
  constructor
  · intro i; simp [div_self (hQ.1 i).1]
  · intro j; simp [div_self (hQ.2 j).1]

theorem anchorImag_eq_zero_iff (Q A : CMat q) (o : Fin q) :
    anchorImag Q o A = 0 ↔
      (∀ i, (A i o / Q i o).im = 0) ∧ (∀ j, (A o j / Q o j).im = 0) := by
  constructor
  · intro h
    have hc : ∀ i, (A i o / Q i o).im = 0 := fun i =>
      congrArg (fun p : AnchorCoordinates o => p.1 i) h
    refine ⟨hc, ?_⟩
    intro j
    by_cases hj : j = o
    · subst j; exact hc o
    · exact congrArg (fun p : AnchorCoordinates o => p.2 ⟨j,hj⟩) h
  · rintro ⟨hc,hr⟩
    apply Prod.ext
    · funext i; exact hc i
    · funext j; exact hr j.val

theorem complex_positive_real_iff (z : ℂ) :
    (∃ r : ℝ, 0 < r ∧ z = r) ↔ z.im = 0 ∧ 0 < z.re := by
  constructor
  · rintro ⟨r,hr,rfl⟩; exact ⟨rfl,hr⟩
  · rintro ⟨hi,hr⟩
    refine ⟨z.re,hr,?_⟩
    apply Complex.ext
    · rfl
    · exact hi

theorem dephased_constraints_iff (Q A : CMat q) (o : Fin q) :
    anchorImag Q o A = 0 ∧ AnchorPositive Q A o ↔
      (∀ i, ∃ r : ℝ, 0 < r ∧ A i o / Q i o = r) ∧
      (∀ j, ∃ r : ℝ, 0 < r ∧ A o j / Q o j = r) := by
  rw [anchorImag_eq_zero_iff]
  constructor
  · rintro ⟨⟨hic,hir⟩,hpc,hpr⟩
    exact ⟨fun i => (complex_positive_real_iff _).mpr ⟨hic i,hpc i⟩,
      fun j => (complex_positive_real_iff _).mpr ⟨hir j,hpr j⟩⟩
  · rintro ⟨hc,hr⟩
    exact ⟨⟨fun i => ((complex_positive_real_iff _).mp (hc i)).1,
      fun j => ((complex_positive_real_iff _).mp (hr j)).1⟩,
      (fun i => ((complex_positive_real_iff _).mp (hc i)).2),
      (fun j => ((complex_positive_real_iff _).mp (hr j)).2)⟩

/-- An iterated matrix subtype; no topology is transported to this space. -/
abbrev DephasedUnitary (Q : FullUnitary q) (o : Fin q) :=
  {A : FullUnitary q // anchorImag Q.val o A.val = 0 ∧ AnchorPositive Q.val A.val o}

abbrev DephasedModel (Q : FullUnitary q) (o : Fin q) :=
  ↥(LinearMap.ker (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o))

/-- The actual implicit-function chart of the Cayley constraint map. -/
def constraintChart (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    OpenPartialHomeomorph (FullSkewModel q) (AnchorCoordinates o × DephasedModel Q o) :=
  (anchorConstraints_hasStrictFDerivAt Q o).implicitToOpenPartialHomeomorph
    (anchorConstraints Q o) (anchorDerivative Q o) (anchorDerivative_range Q o hQ)

@[simp] theorem constraintChart_fst (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (x : FullSkewModel q) :
    (constraintChart Q o hQ x).1 = anchorConstraints Q o x :=
  (anchorConstraints_hasStrictFDerivAt Q o).implicitToOpenPartialHomeomorph_fst
    (anchorDerivative_range Q o hQ) x

@[simp] theorem constraintChart_zero (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : constraintChart Q o hQ 0 = (0,0) := by
  unfold constraintChart
  rw [HasStrictFDerivAt.implicitToOpenPartialHomeomorph_self, anchorConstraints_zero Q o hQ]

theorem zero_mem_constraintChart_source (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : (0 : FullSkewModel q) ∈ (constraintChart Q o hQ).source :=
  (anchorConstraints_hasStrictFDerivAt Q o).mem_implicitToOpenPartialHomeomorph_source
    (anchorDerivative_range Q o hQ)

/-- First pass to Cayley coordinates, then straighten the constraints, and
restrict to the open positive branch. -/
def unitaryConstraintChart (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    OpenPartialHomeomorph (FullUnitary q) (AnchorCoordinates o × DephasedModel Q o) :=
  ((blockPartialChart Q).trans (constraintChart Q o hQ)).restrOpen
    {A | AnchorPositive Q.val A.val o}
    ((anchorPositive_open Q.val o).preimage continuous_subtype_val)

theorem unitaryConstraintChart_source_iff (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : FullUnitary q) :
    A ∈ (unitaryConstraintChart Q o hQ).source ↔
      A ∈ chartSource Q ∧ chartMap Q A.val ∈ (constraintChart Q o hQ).source ∧
        AnchorPositive Q.val A.val o := by
  change (A ∈ chartSource Q ∧ chartMap Q A.val ∈ (constraintChart Q o hQ).source) ∧
    AnchorPositive Q.val A.val o ↔ _
  tauto

theorem base_mem_unitaryConstraintChart_source (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : Q ∈ (unitaryConstraintChart Q o hQ).source := by
  apply (unitaryConstraintChart_source_iff Q o hQ Q).mpr
  exact ⟨base_mem_chartSource Q, by simpa using zero_mem_constraintChart_source Q o hQ,
    anchorPositive_self Q.val o hQ⟩

@[simp] theorem unitaryConstraintChart_base (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : unitaryConstraintChart Q o hQ Q = (0,0) := by
  change constraintChart Q o hQ (chartMap Q Q.val) = _
  rw [chartMap_base, constraintChart_zero]

theorem unitaryConstraintChart_fst (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : FullUnitary q)
    (hA : A ∈ (unitaryConstraintChart Q o hQ).source) :
    (unitaryConstraintChart Q o hQ A).1 = anchorImag Q.val o A.val := by
  change (constraintChart Q o hQ (chartMap Q A.val)).1 = _
  rw [constraintChart_fst]
  unfold anchorConstraints
  rw [chartInv_chartMap Q A ((unitaryConstraintChart_source_iff Q o hQ A).mp hA).1]

/-- Open coordinates on the zero constraint level. -/
def dephasedChartDomain (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : Set (DephasedModel Q o) :=
  {y | (0,y) ∈ (unitaryConstraintChart Q o hQ).target}

def dephasedParametrization (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (y : DephasedModel Q o) : CMat q :=
  ((unitaryConstraintChart Q o hQ).symm (0,y)).val

theorem dephasedChartDomain_open (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : IsOpen (dephasedChartDomain Q o hQ) :=
  (unitaryConstraintChart Q o hQ).open_target.preimage (continuous_const.prodMk continuous_id)

theorem zero_mem_dephasedChartDomain (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : (0 : DephasedModel Q o) ∈ dephasedChartDomain Q o hQ := by
  change (0, 0) ∈ (unitaryConstraintChart Q o hQ).target
  simpa only [unitaryConstraintChart_base] using (unitaryConstraintChart Q o hQ).map_source
    (base_mem_unitaryConstraintChart_source Q o hQ)

@[simp] theorem dephasedParametrization_zero (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : dephasedParametrization Q o hQ 0 = Q.val := by
  have h := (unitaryConstraintChart Q o hQ).left_inv
    (base_mem_unitaryConstraintChart_source Q o hQ)
  rw [unitaryConstraintChart_base] at h
  exact congrArg Subtype.val h

theorem dephasedParametrization_unitary (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (y : DephasedModel Q o) :
    Unitary (dephasedParametrization Q o hQ y) :=
  ((unitaryConstraintChart Q o hQ).symm (0,y)).property.2

theorem dephasedParametrization_constraints (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (y : DephasedModel Q o)
    (hy : y ∈ dephasedChartDomain Q o hQ) :
    anchorImag Q.val o (dephasedParametrization Q o hQ y) = 0 ∧
      AnchorPositive Q.val (dephasedParametrization Q o hQ y) o := by
  have hs := (unitaryConstraintChart Q o hQ).map_target hy
  refine ⟨?_, ((unitaryConstraintChart_source_iff Q o hQ _).mp hs).2.2⟩
  unfold dephasedParametrization
  rw [← unitaryConstraintChart_fst Q o hQ _ hs]
  exact congrArg Prod.fst ((unitaryConstraintChart Q o hQ).right_inv hy)

theorem dephasedParametrization_continuousOn (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    ContinuousOn (dephasedParametrization Q o hQ) (dephasedChartDomain Q o hQ) := by
  exact continuous_subtype_val.continuousOn.comp
    ((unitaryConstraintChart Q o hQ).continuousOn_symm.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ h => h))
    (fun _ _ => Set.mem_univ _)

theorem dephasedParametrization_injectiveOn (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    Set.InjOn (dephasedParametrization Q o hQ) (dephasedChartDomain Q o hQ) := by
  intro y hy z hz he
  have he' : (unitaryConstraintChart Q o hQ).symm (0,y) =
      (unitaryConstraintChart Q o hQ).symm (0,z) := Subtype.ext he
  have hh := congrArg (unitaryConstraintChart Q o hQ) he'
  rw [(unitaryConstraintChart Q o hQ).right_inv hy,
    (unitaryConstraintChart Q o hQ).right_inv hz] at hh
  exact congrArg Prod.snd hh

end GS.UnitaryLocalModel
