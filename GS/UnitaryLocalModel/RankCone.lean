module

public import GS.UnitaryLocalModel.OuterFibres
public import GS.GlobalGeometry.OriginalGImage

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The actual three-row determinantal cone

The Pauli-sphere outer map has image exactly the matrices of real rank at most
one. The result includes the zero matrix and uses mathlib's matrix rank.
-/
noncomputable section
open Matrix GS
open scoped BigOperators
namespace GS.UnitaryLocalModel

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem rank_sphereOuter_le_one (u : AxisVector) (z : κ → ℝ) :
    Matrix.rank (sphereOuter u z) ≤ 1 := by
  let U : Matrix (Fin 3) (Fin 1) ℝ := fun i _ => u i
  let Z : Matrix (Fin 1) κ ℝ := fun _ j => z j
  have h : sphereOuter u z = U * Z := by
    ext i j
    simp [sphereOuter, U, Z, Matrix.mul_apply]
  rw [h]
  exact (Matrix.rank_mul_le_left U Z).trans (by simpa using Matrix.rank_le_card_width U)

theorem rank_le_one_minor (W : Matrix (Fin 3) κ ℝ) (hW : W.rank ≤ 1)
    (i k : Fin 3) (j l : κ) : W i j * W k l = W i l * W k j := by
  let R : Matrix (Fin 2) (Fin 3) ℝ := fun a b =>
    if ![i,k] a = b then 1 else 0
  have he : R * W = W.submatrix ![i,k] id := by
    ext a b
    simp [R, Matrix.mul_apply]
  have hr : (W.submatrix ![i,k] id).rank ≤ 1 := by
    rw [← he]
    exact (Matrix.rank_mul_le_right R W).trans hW
  simpa using GS.GlobalGeometry.rank_le_one_two_column_minor
    (W.submatrix ![i,k] id) hr j l

theorem exists_sphereOuter_of_rank_le_one (W : Matrix (Fin 3) κ ℝ)
    (hW : W.rank ≤ 1) :
    ∃ u : AxisVector, OnSphere u ∧ ∃ z : κ → ℝ, sphereOuter u z = W := by
  classical
  by_cases hzero : W = 0
  · refine ⟨fun i => if i = 0 then 1 else 0, by norm_num [OnSphere], 0, ?_⟩
    rw [hzero]
    ext i j
    simp [sphereOuter]
  have hex : ∃ i j, W i j ≠ 0 := by
    by_contra hn
    apply hzero
    ext i j
    by_contra hij
    exact hn ⟨i,j,hij⟩
  obtain ⟨i₀,j₀,hij⟩ := hex
  let v : AxisVector := fun i => W i j₀
  let r := Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)
  have hv : 0 < v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    have hi : v i₀ ≠ 0 := hij
    have hs := sq_pos_of_ne_zero hi
    fin_cases i₀ <;> dsimp at hs <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1),
      sq_nonneg (v 2)]
  have hr : 0 < r := Real.sqrt_pos.mpr hv
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrs : r ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := Real.sq_sqrt hv.le
  let u : AxisVector := fun i => v i / r
  let z : κ → ℝ := fun j => r * W i₀ j / W i₀ j₀
  refine ⟨u, ?_, z, ?_⟩
  · change (v 0/r)^2 + (v 1/r)^2 + (v 2/r)^2 = 1
    field_simp [hr0]
    nlinarith [hrs]
  · ext i j
    have hm := rank_le_one_minor W hW i i₀ j j₀
    change (W i j₀ / r) * (r * W i₀ j / W i₀ j₀) = W i j
    field_simp [hr0, hij]
    nlinarith [hm]

theorem rank_le_one_iff_sphereOuter (W : Matrix (Fin 3) κ ℝ) :
    W.rank ≤ 1 ↔ ∃ u : AxisVector, OnSphere u ∧
      ∃ z : κ → ℝ, sphereOuter u z = W := by
  constructor
  · exact exists_sphereOuter_of_rank_le_one W
  · rintro ⟨u, _, z, rfl⟩
    exact rank_sphereOuter_le_one u z

end GS.UnitaryLocalModel
