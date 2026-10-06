module

public import GS.Nonmanifold.RankOneGeometry

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Removing the redundant coordinates from the manuscript's row-skew cone

The actual g(K) has two rows indexed by q x q matrix entries, each a skew
matrix. This file constructs the coordinate homeomorphism to two rows indexed
only by strict-upper-triangular entries. Rank-at-most-one is preserved both
ways. This is a homeomorphism, NOT an assertion that unweighted upper entries
preserve the Frobenius norm. Closed Frobenius balls become the corresponding
ellipsoidal constraints until a separately proved normalization is applied.
-/
noncomputable section
open Matrix GS GS.Extensions GS.GlobalGeometry
open scoped BigOperators
namespace GS.Nonmanifold

/-- Independent coordinates of a real skew q x q matrix. -/
abbrev UpperIndex (q : ℕ) := {ij : Fin q × Fin q // ij.1 < ij.2}

def packSkew {q : ℕ} (A : Mat q) : UpperIndex q → ℝ :=
  fun ij => A ij.val.1 ij.val.2

def unpackSkew {q : ℕ} (x : UpperIndex q → ℝ) : Mat q := fun i j =>
  if h : i < j then x ⟨(i,j),h⟩
  else if h : j < i then -x ⟨(j,i),h⟩ else 0

theorem unpackSkew_isSkew {q : ℕ} (x : UpperIndex q → ℝ) :
    IsSkew (unpackSkew x) := by
  ext i j
  change unpackSkew x j i = -unpackSkew x i j
  by_cases hij : i < j
  · have hji : ¬ j < i := not_lt.mpr (le_of_lt hij)
    simp [unpackSkew, hij, hji]
  · by_cases hji : j < i
    · simp [unpackSkew, hij, hji]
    · simp [unpackSkew, hij, hji]

theorem pack_unpackSkew {q : ℕ} (x : UpperIndex q → ℝ) :
    packSkew (unpackSkew x) = x := by
  funext ij
  simp [packSkew, unpackSkew, ij.property]

theorem unpack_packSkew {q : ℕ} {A : Mat q} (hA : IsSkew A) :
    unpackSkew (packSkew A) = A := by
  ext i j
  have he := congrFun (congrFun hA i) j
  change A j i = -A i j at he
  by_cases hij : i < j
  · simp [unpackSkew, packSkew, hij]
  · by_cases hji : j < i
    · simp [unpackSkew, packSkew, hij, hji, he]
    · have h : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      have hd : A i i = 0 := by linarith [he]
      simp [unpackSkew, packSkew, hd]

theorem unpackSkew_smul {q : ℕ} (t : ℝ) (x : UpperIndex q → ℝ) :
    unpackSkew (t • x) = t • unpackSkew x := by
  ext i j
  by_cases hij : i < j <;> by_cases hji : j < i <;>
    simp [unpackSkew, hij, hji]

theorem unpackSkew_add {q : ℕ} (x y : UpperIndex q → ℝ) :
    unpackSkew (x+y) = unpackSkew x + unpackSkew y := by
  ext i j
  by_cases hij : i < j <;> by_cases hji : j < i <;>
    simp [unpackSkew, hij, hji, neg_add, add_comm]

theorem continuous_packSkew (q : ℕ) : Continuous (@packSkew q) := by
  unfold packSkew
  fun_prop

theorem continuous_unpackSkew (q : ℕ) : Continuous (@unpackSkew q) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : i < j <;> by_cases hji : j < i <;>
    simp [unpackSkew, hij, hji] <;> fun_prop

/-- An explicit homeomorphism of the skew subspace with its independent coordinates. -/
def skewCoordinatesHomeomorph (q : ℕ) :
    {A : Mat q // IsSkew A} ≃ₜ (UpperIndex q → ℝ) where
  toFun := fun A => packSkew A.val
  invFun := fun x => ⟨unpackSkew x, unpackSkew_isSkew x⟩
  left_inv := by
    intro A
    apply Subtype.ext
    exact unpack_packSkew A.property
  right_inv := pack_unpackSkew
  continuous_toFun := (continuous_packSkew q).comp continuous_subtype_val
  continuous_invFun := (continuous_unpackSkew q).subtype_mk _

def packRows {q : ℕ} (W : Matrix (Fin 2) (Fin q × Fin q) ℝ) :
    Matrix (Fin 2) (UpperIndex q) ℝ := fun r ij => W r ij.val

def unpackRows {q : ℕ} (Z : Matrix (Fin 2) (UpperIndex q) ℝ) :
    Matrix (Fin 2) (Fin q × Fin q) ℝ := fun r ij => unpackSkew (Z r) ij.1 ij.2

theorem pack_unpackRows {q : ℕ} (Z : Matrix (Fin 2) (UpperIndex q) ℝ) :
    packRows (unpackRows Z) = Z := by
  funext r
  exact pack_unpackSkew (Z r)

theorem unpack_packRows {q : ℕ} (W : Matrix (Fin 2) (Fin q × Fin q) ℝ)
    (hW : ∀ r, IsSkew (fun i j => W r (i,j))) :
    unpackRows (packRows W) = W := by
  ext r ij
  exact congrFun (congrFun (unpack_packSkew (hW r)) ij.1) ij.2

theorem unpackRows_isSkew {q : ℕ} (Z : Matrix (Fin 2) (UpperIndex q) ℝ) (r : Fin 2) :
    IsSkew (fun i j => unpackRows Z r (i,j)) := unpackSkew_isSkew (Z r)

theorem packRows_rank_le_one {q : ℕ} (W : Matrix (Fin 2) (Fin q × Fin q) ℝ)
    (hW : W.rank ≤ 1) : (packRows W).rank ≤ 1 := by
  apply rank_le_one_of_two_column_minors
  intro j k
  exact rank_le_one_two_column_minor W hW j.val k.val

theorem unpackRows_outer {q : ℕ} (u : CircleVector) (z : UpperIndex q → ℝ) :
    unpackRows (outer u z) = outer u (fun ij => unpackSkew z ij.1 ij.2) := by
  ext r ij
  have he := congrFun (congrFun (unpackSkew_smul (u r) z) ij.1) ij.2
  exact he

theorem unpackRows_rank_le_one {q : ℕ} (Z : Matrix (Fin 2) (UpperIndex q) ℝ)
    (hZ : Z.rank ≤ 1) : (unpackRows Z).rank ≤ 1 := by
  obtain ⟨u,hu,z,he⟩ := exists_unit_outer_of_rank_le_one Z hZ
  rw [← he, unpackRows_outer]
  exact rank_outer_le_one _ _

theorem packRows_rank_iff {q : ℕ} (W : Matrix (Fin 2) (Fin q × Fin q) ℝ)
    (hW : ∀ r, IsSkew (fun i j => W r (i,j))) :
    (packRows W).rank ≤ 1 ↔ W.rank ≤ 1 := by
  constructor
  · intro hr
    have hh := unpackRows_rank_le_one (packRows W) hr
    simpa only [unpack_packRows W hW] using hh
  · exact packRows_rank_le_one W

theorem continuous_packRows (q : ℕ) : Continuous (@packRows q) := by
  unfold packRows
  fun_prop

theorem continuous_unpackRows (q : ℕ) : Continuous (@unpackRows q) := by
  apply continuous_pi
  intro r
  apply continuous_pi
  intro ij
  exact (continuous_apply ij.2).comp ((continuous_apply ij.1).comp
    ((continuous_unpackSkew q).comp (continuous_apply r)))

abbrev RowSkewRankCone (q : ℕ) :=
  {W : Matrix (Fin 2) (Fin q × Fin q) ℝ //
    (∀ r, IsSkew (fun i j => W r (i,j))) ∧ W.rank ≤ 1}

/-- The exact row-skew cone in g(K) has no extra rank constraint after packing. -/
def rowSkewConeHomeomorph (q : ℕ) :
    RowSkewRankCone q ≃ₜ {Z : Matrix (Fin 2) (UpperIndex q) ℝ // Z.rank ≤ 1} where
  toFun := fun W => ⟨packRows W.val, packRows_rank_le_one W.val W.property.2⟩
  invFun := fun Z => ⟨unpackRows Z.val,
    unpackRows_isSkew Z.val, unpackRows_rank_le_one Z.val Z.property⟩
  left_inv := by
    intro W
    apply Subtype.ext
    exact unpack_packRows W.val W.property.1
  right_inv := by
    intro Z
    apply Subtype.ext
    exact pack_unpackRows Z.val
  continuous_toFun := ((continuous_packRows q).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_unpackRows q).comp continuous_subtype_val).subtype_mk _

/-- Three independent skew coordinates, available for every q >= 3. -/
def threeUpperIndices (q : ℕ) (hq : 3 ≤ q) : Fin 3 → UpperIndex q :=
  ![⟨(⟨0,by omega⟩,⟨1,by omega⟩), Nat.zero_lt_succ 0⟩,
    ⟨(⟨0,by omega⟩,⟨2,by omega⟩), Nat.zero_lt_succ 1⟩,
    ⟨(⟨1,by omega⟩,⟨2,by omega⟩), Nat.lt_succ_self 1⟩]

theorem threeUpperIndices_injective (q : ℕ) (hq : 3 ≤ q) :
    Function.Injective (threeUpperIndices q hq) := by
  intro i j h
  have he := congrArg (fun x : UpperIndex q => (x.val.1.val,x.val.2.val)) h
  fin_cases i <;> fin_cases j <;> simp_all [threeUpperIndices]

theorem three_le_card_upperIndex (q : ℕ) (hq : 3 ≤ q) :
    3 ≤ Fintype.card (UpperIndex q) := by
  have h := Fintype.card_le_of_injective _ (threeUpperIndices_injective q hq)
  simpa using h

end GS.Nonmanifold
