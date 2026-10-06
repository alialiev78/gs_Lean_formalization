module

public import GS.UnitaryLocalModel.PauliCoordinates
public import GS.Frobenius

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact fibres of the real three-row rank-one parametrization

These are the sphere fibres required by the unitary local model. The sign
identification and collapsed zero fibre are proved, including all degeneracies.
-/
noncomputable section
open Matrix GS
open scoped BigOperators
namespace GS.UnitaryLocalModel

def sphereOuter {κ : Type*} (u : AxisVector) (z : κ → ℝ) : Matrix (Fin 3) κ ℝ :=
  fun i j => u i * z j

/-- The rank-one parameter map is continuous, without a nonzero hypothesis. -/
theorem continuous_sphereOuter {κ : Type*} :
    Continuous (fun p : AxisVector × (κ → ℝ) => sphereOuter p.1 p.2) := by
  unfold sphereOuter
  fun_prop

theorem onSphere_neg {u : AxisVector} (hu : OnSphere u) : OnSphere (-u) := by
  dsimp [OnSphere] at *
  nlinarith

theorem onSphere_has_nonzero {u : AxisVector} (hu : OnSphere u) : ∃ i, u i ≠ 0 := by
  by_contra hn
  push_neg at hn
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  simp [OnSphere, h0, h1, h2] at hu

theorem sphereOuter_simultaneous_neg {κ : Type*} (u : AxisVector) (z : κ → ℝ) :
    sphereOuter (-u) (-z) = sphereOuter u z := by
  ext i j
  simp [sphereOuter]

theorem sphereOuter_zero_iff {κ : Type*} {u : AxisVector} (hu : OnSphere u) (z : κ → ℝ) :
    sphereOuter u z = 0 ↔ z = 0 := by
  constructor
  · intro h
    obtain ⟨i,hi⟩ := onSphere_has_nonzero hu
    funext j
    have he : u i * z j = 0 := congrFun (congrFun h i) j
    exact (mul_eq_zero.mp he).resolve_left hi
  · rintro rfl
    ext i j
    simp [sphereOuter]

theorem sphereOuter_col_sq {κ : Type*} {u : AxisVector} (hu : OnSphere u)
    (z : κ → ℝ) (j : κ) :
    sphereOuter u z 0 j ^ 2 + sphereOuter u z 1 j ^ 2 + sphereOuter u z 2 j ^ 2 = z j ^ 2 := by
  calc
    sphereOuter u z 0 j ^ 2 + sphereOuter u z 1 j ^ 2 + sphereOuter u z 2 j ^ 2 =
        (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) * z j ^ 2 := by unfold sphereOuter; ring
    _ = z j ^ 2 := by rw [hu]; ring

/-- The sphere variable does not change the squared Frobenius radius. -/
theorem frobSq_sphereOuter {κ : Type*} [Fintype κ] {u : AxisVector}
    (hu : OnSphere u) (z : κ → ℝ) :
    frobSq (sphereOuter u z) = ∑ j, z j ^ 2 := by
  unfold frobSq frobInner
  rw [Fin.sum_univ_succ, Fin.sum_univ_two]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  nlinarith [sphereOuter_col_sq hu z j]

/-- Equality plus one equal nonzero column coefficient fixes both factors. -/
theorem sphereOuter_unique_of_column {κ : Type*} {u v : AxisVector} {z w : κ → ℝ}
    (hu : OnSphere u) (h : sphereOuter u z = sphereOuter v w)
    (j : κ) (hzj : z j ≠ 0) (hj : z j = w j) : u = v ∧ z = w := by
  have huv : u = v := by
    funext i
    have he := congrFun (congrFun h i) j
    change u i * z j = v i * w j at he
    rw [← hj] at he
    exact mul_right_cancel₀ hzj he
  obtain ⟨i,hi⟩ := onSphere_has_nonzero hu
  refine ⟨huv, ?_⟩
  funext k
  have he := congrFun (congrFun h i) k
  change u i * z k = v i * w k at he
  rw [← huv] at he
  exact mul_left_cancel₀ hi he

/-- Nonzero rank-one fibres: exactly the simultaneous sign ambiguity. -/
theorem sphereOuter_fibres_nonzero {κ : Type*} {u v : AxisVector} {z w : κ → ℝ}
    (hu : OnSphere u) (hv : OnSphere v) (hz : z ≠ 0) :
    sphereOuter u z = sphereOuter v w ↔ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w) := by
  constructor
  · intro h
    have hex : ∃ j, z j ≠ 0 := by
      by_contra hn
      apply hz
      funext j
      by_contra hj
      exact hn ⟨j,hj⟩
    obtain ⟨j,hj⟩ := hex
    have he : z j ^ 2 = w j ^ 2 := by
      rw [← sphereOuter_col_sq hu z j, h, sphereOuter_col_sq hv w j]
    have hp : (z j - w j) * (z j + w j) = 0 := by nlinarith [he]
    rcases mul_eq_zero.mp hp with hp | hp
    · left
      exact sphereOuter_unique_of_column hu h j hj (sub_eq_zero.mp hp)
    · right
      have h' : sphereOuter u z = sphereOuter (-v) (-w) := by
        rw [sphereOuter_simultaneous_neg]
        exact h
      apply sphereOuter_unique_of_column hu h' j hj
      change z j = -w j
      linarith
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rfl
    · exact sphereOuter_simultaneous_neg v w

/-- Explicit failure of uniqueness at the zero stratum. -/
theorem sphereOuter_zero_fibre {κ : Type*} (u v : AxisVector) :
    sphereOuter u (0 : κ → ℝ) = sphereOuter v (0 : κ → ℝ) := by
  ext i j
  simp [sphereOuter]

/-- The complete fibre classification includes the collapsed zero stratum.
No choice of a nonzero coordinate is required in the statement. -/
theorem sphereOuter_fibres {κ : Type*} {u v : AxisVector} {z w : κ → ℝ}
    (hu : OnSphere u) (hv : OnSphere v) :
    sphereOuter u z = sphereOuter v w ↔
      (z = 0 ∧ w = 0) ∨ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w) := by
  by_cases hz : z = 0
  · subst z
    have he : sphereOuter u (0 : κ → ℝ) = 0 := (sphereOuter_zero_iff hu 0).mpr rfl
    rw [he]
    constructor
    · intro h
      exact Or.inl ⟨rfl, (sphereOuter_zero_iff hv w).mp h.symm⟩
    · rintro (⟨_, rfl⟩ | ⟨_, hw⟩ | ⟨_, hw⟩)
      · exact ((sphereOuter_zero_iff hv 0).mpr rfl).symm
      · exact ((sphereOuter_zero_iff hv w).mpr hw.symm).symm
      · have hw0 : w = 0 := neg_eq_zero.mp hw.symm
        exact ((sphereOuter_zero_iff hv w).mpr hw0).symm
  · rw [sphereOuter_fibres_nonzero hu hv hz]
    simp only [hz, false_and, false_or]


end GS.UnitaryLocalModel
