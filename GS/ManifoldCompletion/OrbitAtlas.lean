module

public import GS.ManifoldCompletion.FactorCoordinates

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Smooth atlas on the actual two-factor orbit in the non-overlap case

The source topology is inherited from matrices, unchanged. For the key
transition theorem we fix ONE stabilizer element at the basepoint. On a nearby
open set it sends the first factor lift into the second injectivity sheet.
Uniqueness on that sheet identifies the two lifts. The transition is consequently
a fixed right-translation in the already checked factor coordinates.

Neither a smooth quotient theorem nor differentiability of a chosen section is
assumed. This file does not cover a positive-dimensional overlap stabilizer.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts Filter Set
open scoped Topology Manifold
namespace GS.ManifoldCompletion
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}

/-- Global reconstruction into the original matrix orbit. Its matrix value is
smooth; restricting to a chart target makes it one-to-one. -/
def orbitInverse (σ : Equiv.Perm (Fin n)) (g : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) : MatrixOrbit block₁ block₂ (permMatrix σ) :=
  orbitMapToOrbit block₁ block₂ (permMatrix σ) (factorLift g x)

@[simp] theorem orbitInverse_val (σ : Equiv.Perm (Fin n))
    (g : FactorGroup block₁ block₂) (x : PairModel block₁ block₂) :
    (orbitInverse σ g x).val = orbitParam g (permMatrix σ) x :=
  factorLift_action g (permMatrix σ) x

theorem continuous_orbitInverse (σ : Equiv.Perm (Fin n))
    (g : FactorGroup block₁ block₂) : Continuous (orbitInverse σ g) :=
  (continuous_orbitMapToOrbit (permMatrix σ)).comp (continuous_factorLift g)

/-- Only the forward map needs an arbitrary extension outside its open source.
No theorem uses that extension to prove regularity off the source. -/
def orbitCoordinates (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g : FactorGroup block₁ block₂)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) : PairModel block₁ block₂ := by
  classical
  exact if hX : X ∈ orbitChartSource σ g then
    (orbitChartHomeomorph σ hn g ⟨X, hX⟩).val else 0

theorem orbitCoordinates_of_mem (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g : FactorGroup block₁ block₂)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (hX : X ∈ orbitChartSource σ g) :
    orbitCoordinates σ hn g X = (orbitChartHomeomorph σ hn g ⟨X, hX⟩).val := by
  simp [orbitCoordinates, hX]

theorem orbitCoordinates_mem_target (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g : FactorGroup block₁ block₂)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (hX : X ∈ orbitChartSource σ g) :
    orbitCoordinates σ hn g X ∈ orbitParameterTarget g := by
  rw [orbitCoordinates_of_mem σ hn g X hX]
  exact (orbitChartHomeomorph σ hn g ⟨X, hX⟩).property

/-- The old homeomorphism's inverse equals the explicit reconstruction. -/
theorem orbitInverse_eq_chart_symm (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) (hx : x ∈ orbitParameterTarget g) :
    orbitInverse σ g x = ((orbitChartHomeomorph σ hn g).symm ⟨x, hx⟩).val := by
  apply Subtype.ext
  rw [orbitInverse_val]
  exact (orbitChartHomeomorph_inverse_matrix σ hn g ⟨x, hx⟩).symm

theorem orbitInverse_mem_source (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) (hx : x ∈ orbitParameterTarget g) :
    orbitInverse σ g x ∈ orbitChartSource σ g := by
  rw [orbitInverse_eq_chart_symm σ hn g x hx]
  exact ((orbitChartHomeomorph σ hn g).symm ⟨x, hx⟩).property

theorem orbitCoordinates_inverse (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) (hx : x ∈ orbitParameterTarget g) :
    orbitCoordinates σ hn g (orbitInverse σ g x) = x := by
  rw [orbitCoordinates_of_mem σ hn g _ (orbitInverse_mem_source σ hn g x hx)]
  have he : (⟨orbitInverse σ g x, orbitInverse_mem_source σ hn g x hx⟩ :
      orbitChartSource σ g) = (orbitChartHomeomorph σ hn g).symm ⟨x, hx⟩ :=
    Subtype.ext (orbitInverse_eq_chart_symm σ hn g x hx)
  rw [he, (orbitChartHomeomorph σ hn g).apply_symm_apply]

theorem orbitInverse_coordinates (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g : FactorGroup block₁ block₂)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (hX : X ∈ orbitChartSource σ g) :
    orbitInverse σ g (orbitCoordinates σ hn g X) = X := by
  rw [orbitCoordinates_of_mem σ hn g X hX]
  rw [orbitInverse_eq_chart_symm σ hn g _
    (orbitChartHomeomorph σ hn g ⟨X, hX⟩).property]
  simpa using congrArg Subtype.val
    ((orbitChartHomeomorph σ hn g).symm_apply_apply ⟨X, hX⟩)

/-- Evaluation of the forward chart on any factorization in its injectivity
source. This supplies the essential link for the transition proof. -/
theorem orbitCoordinates_on_factors (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g h : FactorGroup block₁ block₂)
    (hh : h ∈ orbitFactorSource g) :
    orbitCoordinates σ hn g (orbitMapToOrbit block₁ block₂ (permMatrix σ) h) =
      factorCoordinates g h := by
  have hsource : orbitMapToOrbit block₁ block₂ (permMatrix σ) h ∈
      orbitChartSource σ g := ⟨h, hh, rfl⟩
  rw [orbitCoordinates_of_mem σ hn g _ hsource]
  let e := restrictedOrbitHomeomorph σ hn g
  have he : e ⟨h, hh⟩ = ⟨orbitMapToOrbit block₁ block₂ (permMatrix σ) h, hsource⟩ :=
    Subtype.ext rfl
  have hi : e.symm ⟨orbitMapToOrbit block₁ block₂ (permMatrix σ) h, hsource⟩ =
      ⟨h, hh⟩ := by rw [← he, e.symm_apply_apply]
  change (smallFactorChart g
    (e.symm ⟨orbitMapToOrbit block₁ block₂ (permMatrix σ) h, hsource⟩)).val = _
  rw [hi]
  exact smallFactorChart_apply g ⟨h, hh⟩

def orbitPartialChart (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g : FactorGroup block₁ block₂) :
    OpenPartialHomeomorph (MatrixOrbit block₁ block₂ (permMatrix σ))
      (PairModel block₁ block₂) where
  toFun := orbitCoordinates σ hn g
  invFun := orbitInverse σ g
  source := orbitChartSource σ g
  target := orbitParameterTarget g
  map_source' := orbitCoordinates_mem_target σ hn g
  map_target' := orbitInverse_mem_source σ hn g
  left_inv' := orbitInverse_coordinates σ hn g
  right_inv' := orbitCoordinates_inverse σ hn g
  open_source := orbitChartSource_open σ g
  open_target := orbitParameterTarget_open g
  continuousOn_toFun := by
    apply continuousOn_iff_continuous_restrict.mpr
    have hc := continuous_subtype_val.comp (orbitChartHomeomorph σ hn g).continuous
    exact hc.congr (fun X => (orbitCoordinates_of_mem σ hn g X.val X.property).symm)
  continuousOn_invFun := (continuous_orbitInverse σ g).continuousOn

/-- The main new result: smooth transition functions of the ORBIT charts.
The fixed s may depend on the basepoint, but it is held constant on the
neighbourhood used to prove ContDiffAt. -/
theorem orbitPartialChart_transition_smooth (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) (g h : FactorGroup block₁ block₂) :
    ContDiffOn ℝ ⊤ ((orbitPartialChart σ hn g).symm.trans (orbitPartialChart σ hn h))
      ((orbitPartialChart σ hn g).symm.trans (orbitPartialChart σ hn h)).source := by
  intro x hx
  change x ∈ orbitParameterTarget g ∧ orbitInverse σ g x ∈ orbitChartSource σ h at hx
  obtain ⟨b, hb, hbx⟩ := hx.2
  let s : FactorGroup block₁ block₂ := (factorLift g x)⁻¹ * b
  have hs : s ∈ PointStabilizer block₁ block₂ (permMatrix σ) := by
    apply (orbit_fibre_iff (permMatrix σ) (factorLift g x) b).mp
    exact congrArg Subtype.val hbx.symm
  have hfix : s • permMatrix σ = permMatrix σ := hs
  have hxs : factorLift g x * s = b := by simp [s]
  have hnear : ∀ᶠ y in 𝓝 x, factorLift g y * s ∈ orbitFactorSource h :=
    ((continuous_factorLift g).mul continuous_const).continuousAt.eventually
      ((orbitFactorSource_open h).mem_nhds (by simpa only [Pi.mul_apply, mul_inv_cancel_left] using hb))
  have he : (fun y => orbitCoordinates σ hn h (orbitInverse σ g y)) =ᶠ[𝓝 x]
      rightTranslateCoordinates g h s := by
    filter_upwards [hnear] with y hy
    have horbit : orbitMapToOrbit block₁ block₂ (permMatrix σ) (factorLift g y * s) =
        orbitInverse σ g y := by
      apply Subtype.ext
      change (factorLift g y * s) • permMatrix σ = factorLift g y • permMatrix σ
      rw [mul_smul, hfix]
    rw [← horbit, orbitCoordinates_on_factors σ hn h _ hy]
    rfl
  have hdom : factorLift g x * s ∈ factorSource h := by
    rw [hxs]
    exact ((orbitFactorSource_mem_iff h b).mp hb).1
  exact ((rightTranslateCoordinates_smooth_at g h s x hdom).congr_of_eventuallyEq
    he).contDiffWithinAt

/-- Select a centre for the preferred chart only. Smoothness does not depend
on continuity of this choice: the entire family of charts is in the atlas. -/
def preferredFactor (σ : Equiv.Perm (Fin n))
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) : FactorGroup block₁ block₂ :=
  Classical.choose (surjective_orbitMapToOrbit (permMatrix σ) X)

theorem preferredFactor_spec (σ : Equiv.Perm (Fin n))
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    orbitMapToOrbit block₁ block₂ (permMatrix σ) (preferredFactor σ X) = X :=
  Classical.choose_spec (surjective_orbitMapToOrbit (permMatrix σ) X)

/-- A charted space on the existing orbit subtype, not a transferred topology.
Fact makes the no-overlap condition explicit in typeclass use. -/
instance orbitChartedSpace (block₁ block₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    [hno : Fact (NoOffDiagonalOverlap block₁ block₂ σ)] :
    ChartedSpace (PairModel block₁ block₂) (MatrixOrbit block₁ block₂ (permMatrix σ)) where
  atlas := Set.range (orbitPartialChart σ hno.out)
  chartAt X := orbitPartialChart σ hno.out (preferredFactor σ X)
  mem_chart_source X := by
    change X ∈ orbitChartSource σ (preferredFactor σ X)
    have hh := base_mem_orbitChartSource σ (preferredFactor σ X)
    simpa only [preferredFactor_spec] using hh
  chart_mem_atlas X := ⟨preferredFactor σ X, rfl⟩

/-- Analytic, hence smooth, structure on the actual non-overlap GS orbit.
No IsManifold assumption on the orbit occurs in this construction. -/
instance orbitIsManifold (block₁ block₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    [hno : Fact (NoOffDiagonalOverlap block₁ block₂ σ)] :
    IsManifold (𝓘(ℝ, PairModel block₁ block₂)) ⊤
      (MatrixOrbit block₁ block₂ (permMatrix σ)) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ Set.range (orbitPartialChart σ hno.out) at he
  change e' ∈ Set.range (orbitPartialChart σ hno.out) at he'
  obtain ⟨g, rfl⟩ := he
  obtain ⟨h, rfl⟩ := he'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ] using orbitPartialChart_transition_smooth σ hno.out g h

/-- The usual countability and separation conditions are inherited from the
finite-dimensional real matrix space, not assumed in the manifold construction. -/
theorem orbit_secondCountable_t2 (block₁ block₂ : Fin n → ℕ) (P : Mat n) :
    SecondCountableTopology (MatrixOrbit block₁ block₂ P) ∧
      T2Space (MatrixOrbit block₁ block₂ P) := by
  constructor <;> infer_instance

/-- The model has finite real dimension, including zero-dimensional edge cases. -/
theorem pairModel_finiteDimensional (block₁ block₂ : Fin n → ℕ) :
    FiniteDimensional ℝ (PairModel block₁ block₂) := by infer_instance

/-- State the result on the manuscript's exact subtype InA2Orth. Rewriting the
proved equality of sets does not alter its inherited topology. -/
theorem inA2Orth_admits_manifold (b₁ b₂ : ℕ) (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap (fun i : Fin n => i.val / b₁)
      (fun i : Fin n => i.val / b₂) σ) :
    ∃ cs : ChartedSpace
        (PairModel (fun i : Fin n => i.val / b₁) (fun i : Fin n => i.val / b₂))
        {X : Mat n // InA2Orth b₁ b₂ (permMatrix σ) X},
      letI := cs
      IsManifold
        (𝓘(ℝ, PairModel (fun i : Fin n => i.val / b₁) (fun i : Fin n => i.val / b₂)))
        ⊤ {X : Mat n // InA2Orth b₁ b₂ (permMatrix σ) X} := by
  letI : Fact (NoOffDiagonalOverlap (fun i : Fin n => i.val / b₁)
      (fun i : Fin n => i.val / b₂) σ) := ⟨hn⟩
  have h : ∃ cs : ChartedSpace
      (PairModel (fun i : Fin n => i.val / b₁) (fun i : Fin n => i.val / b₂))
      (MatrixOrbit (fun i : Fin n => i.val / b₁) (fun i : Fin n => i.val / b₂)
        (permMatrix σ)),
      letI := cs
      IsManifold
        (𝓘(ℝ, PairModel (fun i : Fin n => i.val / b₁) (fun i : Fin n => i.val / b₂)))
        ⊤ (MatrixOrbit (fun i : Fin n => i.val / b₁) (fun i : Fin n => i.val / b₂)
          (permMatrix σ)) := by
    refine ⟨orbitChartedSpace _ _ σ, ?_⟩
    exact orbitIsManifold _ _ σ
  change ∃ cs : ChartedSpace
      (PairModel (fun i : Fin n => i.val / b₁) (fun i : Fin n => i.val / b₂))
      ↥(MulAction.orbit (FactorGroup (fun i : Fin n => i.val / b₁)
        (fun i : Fin n => i.val / b₂)) (permMatrix σ)),
      letI := cs
      IsManifold
        (𝓘(ℝ, PairModel (fun i : Fin n => i.val / b₁) (fun i : Fin n => i.val / b₂)))
        ⊤ ↥(MulAction.orbit (FactorGroup (fun i : Fin n => i.val / b₁)
          (fun i : Fin n => i.val / b₂)) (permMatrix σ)) at h
  rw [orbit_set_eq_inA2Orth b₁ b₂ (permMatrix σ)] at h
  exact h

end GS.ManifoldCompletion
