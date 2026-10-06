module

public import GS.Nonmanifold.RankOneGeometry
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# An independent differential obstruction, without sphere homology

At the vertex, the set of velocities of differentiable curves in the rank-one
cone is exactly the cone itself and is not closed under addition. Consequently
there is no local ambient retraction to the cone product differentiable at zero.

This is NOT a replacement for the topological NonManifoldGoal. It is a separate
unconditional differential statement. The implication from general embedded
submanifold machinery is not asserted here without its own formalization.
-/
noncomputable section
open Matrix GS GS.Extensions GS.GlobalGeometry GS.Nonmanifold Filter
open scoped Topology
namespace GS.NonmanifoldClosure

-- Use the coordinate sup norm, whose topology is the existing matrix product
-- topology; mathlib deliberately does not install a global matrix norm.
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
abbrev TwoRow (κ : Type*) := Matrix (Fin 2) κ ℝ

/-- Velocities are actual derivatives of curves in the actual rank cone. -/
def ConeVelocity (v : TwoRow κ) : Prop :=
  ∃ f : ℝ → TwoRow κ, f 0=0 ∧ HasDerivAt f v 0 ∧
    ∀ᶠ t in 𝓝 (0 : ℝ), (f t).rank ≤ 1

/-- A closed cone contains the normalized slopes and therefore the limiting derivative. -/
theorem derivative_rank_le_one {f : ℝ → TwoRow κ} {v : TwoRow κ}
    (hzero : f 0=0) (hder : HasDerivAt f v 0)
    (hcone : ∀ᶠ t in 𝓝 (0 : ℝ), (f t).rank ≤ 1) : v.rank ≤ 1 := by
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • f t) (𝓝[≠] (0 : ℝ)) (𝓝 v) := by
    simpa only [zero_add,hzero,sub_zero] using hder.tendsto_slope_zero
  have hmem : ∀ᶠ t in 𝓝[≠] (0 : ℝ), (t⁻¹ • f t).rank ≤ 1 := by
    filter_upwards [hcone.filter_mono nhdsWithin_le_nhds] with t ht
    exact rank_smul_le_one t⁻¹ ht
  exact isClosed_rankOne.mem_of_tendsto hlim hmem

theorem coneVelocity_iff (v : TwoRow κ) : ConeVelocity v ↔ v.rank ≤ 1 := by
  constructor
  · rintro ⟨f,hzero,hder,hcone⟩
    exact derivative_rank_le_one hzero hder hcone
  · intro hv
    refine ⟨fun t => t • v,by simp,?_,?_⟩
    · simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    · exact Filter.Eventually.of_forall (fun t => rank_smul_le_one t hv)

def rowZeroUnit (j : κ) : TwoRow κ := outer ![1,0] (fun k => if k=j then 1 else 0)
def rowOneUnit (k : κ) : TwoRow κ := outer ![0,1] (fun j => if j=k then 1 else 0)

theorem unit_sum_not_rank_one (j k : κ) (hjk : j ≠ k) :
    ¬ (rowZeroUnit j + rowOneUnit k).rank ≤ 1 := by
  intro h
  have hm := rank_le_one_two_column_minor _ h j k
  norm_num [rowZeroUnit,rowOneUnit,outer,hjk,Ne.symm hjk] at hm

/-- Two genuine curve velocities whose sum cannot be a curve velocity. -/
theorem coneVelocities_not_additive (j k : κ) (hjk : j ≠ k) :
    ConeVelocity (rowZeroUnit j) ∧ ConeVelocity (rowOneUnit k) ∧
      ¬ ConeVelocity (rowZeroUnit j + rowOneUnit k) := by
  refine ⟨(coneVelocity_iff _).mpr (rank_outer_le_one _ _),
    (coneVelocity_iff _).mpr (rank_outer_le_one _ _),?_⟩
  exact fun h => unit_sum_not_rank_one j k hjk ((coneVelocity_iff _).mp h)

variable {ι : Type*} [Fintype ι]
abbrev ConeAmbient (ι κ : Type*) := (ι → ℝ) × TwoRow κ

/-- It is impossible even to retract the matrix component differentiably.
The local fixed-point and rank conditions hold on a full ambient neighborhood. -/
theorem no_differentiable_matrix_retraction (j k : κ) (hjk : j ≠ k)
    (f : ConeAmbient ι κ → TwoRow κ)
    (hlocal : ∀ᶠ p in 𝓝 (0 : ConeAmbient ι κ),
      (f p).rank ≤ 1 ∧ (p.2.rank ≤ 1 → f p=p.2)) :
    ¬ DifferentiableAt ℝ f 0 := by
  intro hdiff
  let D := fderiv ℝ f 0
  have hD : HasFDerivAt f D 0 := hdiff.hasFDerivAt
  have hf0 : f 0=0 := (mem_of_mem_nhds hlocal).2 (by simp)
  have lineDeriv (v : TwoRow κ) :
      HasDerivAt (fun t : ℝ => t • ((0 : ι → ℝ),v)) ((0 : ι → ℝ),v) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const ((0 : ι → ℝ),v)
  have compDeriv (v : TwoRow κ) :
      HasDerivAt (fun t : ℝ => f (t • ((0 : ι → ℝ),v))) (D (0,v)) 0 := by
    exact hD.comp_hasDerivAt_of_eq 0 (lineDeriv v) (by simp)
  have localOnLine (v : TwoRow κ) :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        (f (t • ((0 : ι → ℝ),v))).rank ≤ 1 ∧
        ((t • v).rank ≤ 1 → f (t • ((0 : ι → ℝ),v))=t • v) := by
    have ht : Tendsto (fun t : ℝ => t • ((0 : ι → ℝ),v))
        (𝓝 (0 : ℝ)) (𝓝 (0 : ConeAmbient ι κ)) := by
      simpa [ContinuousAt] using (lineDeriv v).continuousAt
    exact ht.eventually hlocal
  have fixesDerivative (v : TwoRow κ) (hv : v.rank ≤ 1) : D (0,v)=v := by
    have heq : (fun t : ℝ => t • v) =ᶠ[𝓝 (0 : ℝ)]
        (fun t : ℝ => f (t • ((0 : ι → ℝ),v))) := by
      filter_upwards [localOnLine v] with t ht
      exact (ht.2 (rank_smul_le_one t hv)).symm
    have hh := (compDeriv v).congr_of_eventuallyEq heq
    have hline : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    exact hh.unique hline
  let A := rowZeroUnit j
  let B := rowOneUnit k
  have hA : D (0,A)=A := fixesDerivative A (rank_outer_le_one _ _)
  have hB : D (0,B)=B := fixesDerivative B (rank_outer_le_one _ _)
  have hsum : D (0,A+B)=A+B := by
    calc
      D (0,A+B) = D ((0,A)+(0,B)) := by congr 1; simp
      _ = D (0,A)+D (0,B) := D.map_add _ _
      _ = A+B := by rw [hA,hB]
  have hzero : (fun t : ℝ => f (t • ((0 : ι → ℝ),A+B))) 0=0 := by
    simpa using hf0
  have hder : HasDerivAt (fun t : ℝ => f (t • ((0 : ι → ℝ),A+B))) (A+B) 0 := by
    simpa only [hsum] using compDeriv (A+B)
  have hcone : ∀ᶠ t in 𝓝 (0 : ℝ),
      (f (t • ((0 : ι → ℝ),A+B))).rank ≤ 1 :=
    (localOnLine (A+B)).mono (fun _ h => h.1)
  exact unit_sum_not_rank_one j k hjk (derivative_rank_le_one hzero hder hcone)

/-- Applied to the second component, the preceding theorem excludes an actual
local ambient retraction differentiable at the vertex. -/
theorem no_differentiable_local_retraction (j k : κ) (hjk : j ≠ k)
    (R : ConeAmbient ι κ → ConeAmbient ι κ)
    (hlocal : ∀ᶠ p in 𝓝 (0 : ConeAmbient ι κ),
      (R p).2.rank ≤ 1 ∧ (p.2.rank ≤ 1 → R p=p)) :
    ¬ DifferentiableAt ℝ R 0 := by
  intro hR
  apply no_differentiable_matrix_retraction j k hjk (fun p => (R p).2) ?_ hR.snd
  filter_upwards [hlocal] with p hp
  exact ⟨hp.1,fun h => congrArg Prod.snd (hp.2 h)⟩

end GS.NonmanifoldClosure
