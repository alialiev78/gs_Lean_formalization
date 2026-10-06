module

public import GS.NonmanifoldFinal.HomologyRetracts
public import GS.Topology.EuclideanSphere
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Actual positive-degree homology computations for ambient dimensions 0 and 1

The zero-dimensional ambient sphere is empty. The one-dimensional ambient
sphere has exactly the two coordinates +1 and -1. Its finiteness is proved
before applying mathlib's theorem for totally disconnected spaces.

This does NOT compute H_1(S^1): S^1 has ambient dimension 2.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits GS.NonmanifoldFinal
namespace GS.NonmanifoldClosure

/-- Extract the elementary module statement from a categorical zero object. -/
theorem module_subsingleton_of_isZero (M : ModuleCat ℤ) (h : IsZero M) : Subsingleton M := by
  have hid : (𝟙 M) = 0 := h.eq_of_src _ _
  have hz (x : M) : x=0 := by
    exact congrArg (fun f : M ⟶ M => f x) hid
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The sphere in a one-dimensional Euclidean space has exactly two possible coordinates. -/
theorem sphere_one_coordinate (x : UnitSphere (Fin 1)) :
    x.val 0=1 ∨ x.val 0= -1 := by
  have hn : ‖x.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hs : (x.val 0)^2=1 := by
    have he := EuclideanSpace.real_norm_sq_eq x.val
    rw [hn] at he
    simpa only [Fin.sum_univ_one, one_pow] using he.symm
  have hp : (x.val 0-1)*(x.val 0+1)=0 := by nlinarith
  rcases mul_eq_zero.mp hp with h | h
  · left; linarith
  · right; linarith

/-- Construct finiteness rather than treating the sphere as discretely topologized. -/
theorem finite_sphere_one : Finite (UnitSphere (Fin 1)) := by
  classical
  let f : UnitSphere (Fin 1) → Bool := fun x => decide (x.val 0=1)
  apply Finite.of_injective f
  intro x y hxy
  have he : x.val 0=y.val 0 := by
    rcases sphere_one_coordinate x with hx | hx <;>
      rcases sphere_one_coordinate y with hy | hy
    · rw [hx,hy]
    · have hf : f x ≠ f y := by norm_num [f,hx,hy]
      exact (hf hxy).elim
    · have hf : f x ≠ f y := by norm_num [f,hx,hy]
      exact (hf hxy).elim
    · rw [hx,hy]
  apply Subtype.ext
  ext i
  fin_cases i
  exact he

/-- Positive homology of the empty ambient-zero sphere. -/
theorem sphere_zero_positive_homology (k : ℕ) (hk : 0 < k) :
    Subsingleton (IntegralHomology k (UnitSphere (Fin 0))) := by
  have hz := AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) k (ModuleCat.of ℤ ℤ) (TopCat.of (UnitSphere (Fin 0))) (by omega)
  exact module_subsingleton_of_isZero _ hz

/-- Positive homology of S^0. This is an actual sphere computation, without
SphereHomologyProfile as an argument. -/
theorem sphere_one_positive_homology (k : ℕ) (hk : 0 < k) :
    Subsingleton (IntegralHomology k (UnitSphere (Fin 1))) := by
  letI : Finite (UnitSphere (Fin 1)) := finite_sphere_one
  letI : DiscreteTopology (UnitSphere (Fin 1)) := inferInstance
  have hz := AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) k (ModuleCat.of ℤ ℤ) (TopCat.of (UnitSphere (Fin 1))) (by omega)
  exact module_subsingleton_of_isZero _ hz

/-- The off-top obligation in ambient dimensions <=1 is discharged. -/
theorem low_sphere_positive_homology (n k : ℕ) (hn : n ≤ 1) (hk : 0 < k) :
    Subsingleton (IntegralHomology k (UnitSphere (Fin n))) := by
  have h : n=0 ∨ n=1 := by omega
  rcases h with rfl | rfl
  · exact sphere_zero_positive_homology k hk
  · exact sphere_one_positive_homology k hk

end GS.NonmanifoldClosure
