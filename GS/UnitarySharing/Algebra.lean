module

public import GS.GlobalGeometry.SharedAlgebra
public import GS.UnitaryManifold.CayleySmooth
public import GS.UnitaryManifold.BlockGroup
public import GS.Unitary.FrobeniusProjection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Complex complete-block sharing as a real star algebra

The equality predicate is imposed on actual complex entries. Positive complete
physical blocks have the same finite local index set, so products preserve all
within-layer ties. Inverse closure is derived by finite-dimensional real linear
algebra. Neither skew-Hermitian generators nor the Cayley chart discard phases.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
open GS.GlobalGeometry (localBlockIndex localBlockIndex_div localBlockIndex_mod)
open scoped BigOperators Topology
namespace GS.UnitarySharing
variable {n b : ℕ} {τ : ℕ → ℕ} {A B C : CMat n}

/-- Labels tie full complex blocks within one layer, never across layers. -/
def TiedEntries (b : ℕ) (τ : ℕ → ℕ) (A : CMat n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

namespace TiedEntries
theorem zero (b : ℕ) (τ : ℕ → ℕ) : TiedEntries b τ (0 : CMat n) := by
  intro i j i' j' _ _ _ _ _
  rfl

theorem one (b : ℕ) (τ : ℕ → ℕ) : TiedEntries b τ (1 : CMat n) := by
  intro i j i' j' hij hij' _ hi hj
  have he : i = j ↔ i' = j' := by
    constructor
    · intro h
      subst j
      apply Fin.ext
      have hm : i'.val % b = j'.val % b := hi.symm.trans hj
      have hdi := Nat.mod_add_div i'.val b
      have hdj := Nat.mod_add_div j'.val b
      rw [hm, hij'] at hdi
      omega
    · intro h
      subst j'
      apply Fin.ext
      have hm : i.val % b = j.val % b := hi.trans hj.symm
      have hdi := Nat.mod_add_div i.val b
      have hdj := Nat.mod_add_div j.val b
      rw [hm, hij] at hdi
      omega
  simp only [Matrix.one_apply, he]

theorem add (hA : TiedEntries b τ A) (hB : TiedEntries b τ B) :
    TiedEntries b τ (A + B) := by
  intro i j i' j' h h' hτ hi hj
  simp only [Matrix.add_apply, hA i j i' j' h h' hτ hi hj,
    hB i j i' j' h h' hτ hi hj]

theorem smul (a : ℝ) (hA : TiedEntries b τ A) : TiedEntries b τ (a • A) := by
  intro i j i' j' h h' hτ hi hj
  simp only [Matrix.smul_apply, hA i j i' j' h h' hτ hi hj]

theorem neg (hA : TiedEntries b τ A) : TiedEntries b τ (-A) := by
  simpa only [neg_one_smul] using hA.smul (-1)

theorem conjTranspose (hA : TiedEntries b τ A) : TiedEntries b τ Aᴴ := by
  intro i j i' j' h h' hτ hi hj
  exact congrArg star (hA j i j' i' h.symm h'.symm
    (by simpa only [← h, ← h'] using hτ) hj hi)

end TiedEntries

/-- Matrix multiplication within a full physical block is a sum over its local
coordinates. -/
theorem mul_apply_localBlockIndex (hb : 0 < b) (hbn : b ∣ n)
    (hA : CSupported (fun i => i.val / b) A) (i j : Fin n) :
    (A * B) i j = ∑ k : Fin b,
      A i (localBlockIndex hb hbn i k) * B (localBlockIndex hb hbn i k) j := by
  classical
  rw [Matrix.mul_apply]
  let s : Finset (Fin n) := Finset.univ.filter (fun k => k.val / b = i.val / b)
  have hrestrict : (∑ k : Fin n, A i k * B k j) = ∑ k ∈ s, A i k * B k j := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hk
    have hk' : i.val / b ≠ k.val / b := by
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
        eq_comm] using hk
    rw [hA i k hk', zero_mul]
  rw [hrestrict]
  apply Finset.sum_bij (fun k _ => (⟨k.val % b, Nat.mod_lt _ hb⟩ : Fin b))
  · intro k hk
    exact Finset.mem_univ _
  · intro k hk l hl he
    have hk' : k.val / b = i.val / b := (Finset.mem_filter.mp hk).2
    have hl' : l.val / b = i.val / b := (Finset.mem_filter.mp hl).2
    have he' : k.val % b = l.val % b := congrArg Fin.val he
    apply Fin.ext
    have hkd := Nat.mod_add_div k.val b
    have hld := Nat.mod_add_div l.val b
    rw [hk', he'] at hkd
    rw [hl'] at hld
    omega
  · intro k _
    refine ⟨localBlockIndex hb hbn i k, ?_, ?_⟩
    · simp [s]
    · exact Fin.ext (localBlockIndex_mod hb hbn i k)
  · intro k hk
    have hk' : k.val / b = i.val / b := (Finset.mem_filter.mp hk).2
    have he : localBlockIndex hb hbn i ⟨k.val % b, Nat.mod_lt _ hb⟩ = k := by
      apply Fin.ext
      simp only [localBlockIndex, ← hk']
      exact Nat.div_add_mod' _ _
    rw [he]

namespace TiedEntries

theorem mul (hb : 0 < b) (hbn : b ∣ n)
    (hAs : CSupported (fun i => i.val / b) A) (_hBs : CSupported (fun i => i.val / b) B)
    (hA : TiedEntries b τ A) (hB : TiedEntries b τ B) :
    TiedEntries b τ (A * B) := by
  intro i j i' j' hij hij' hτ hi hj
  rw [mul_apply_localBlockIndex hb hbn hAs, mul_apply_localBlockIndex hb hbn hAs]
  apply Finset.sum_congr rfl
  intro k _
  have hleft : A i (localBlockIndex hb hbn i k) =
      A i' (localBlockIndex hb hbn i' k) := by
    apply hA
    · simp
    · simp
    · exact hτ
    · exact hi
    · simp
  have hright : B (localBlockIndex hb hbn i k) j =
      B (localBlockIndex hb hbn i' k) j' := by
    apply hB
    · simpa using hij
    · simpa using hij'
    · simpa using hτ
    · simp
    · exact hj
  rw [hleft, hright]


end TiedEntries

theorem isClosed_tiedEntries (b : ℕ) (τ : ℕ → ℕ) :
    IsClosed {A : CMat n | TiedEntries b τ A} := by
  simp only [TiedEntries, Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_iInter fun i' => isClosed_iInter fun j' =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_iInter fun _ =>
          isClosed_eq (by fun_prop) (by fun_prop)

/-- Expanded physical matrices, with their real vector space structure. -/
def sharedMatrixSpace (b : ℕ) (τ : ℕ → ℕ) : Submodule ℝ (CMat n) where
  carrier := {A | CSupported (fun i => i.val / b) A ∧ TiedEntries b τ A}
  zero_mem' := ⟨CSupported.zero, TiedEntries.zero b τ⟩
  add_mem' := fun hA hB => ⟨hA.1.add hB.1, hA.2.add hB.2⟩
  smul_mem' := fun a _ hA => ⟨CSupported.real_smul a hA.1, hA.2.smul a⟩

def sharedSkewSpace (b : ℕ) (τ : ℕ → ℕ) : Submodule ℝ (CMat n) where
  carrier := {A | CSupported (fun i => i.val / b) A ∧ IsSkewHermitian A ∧ TiedEntries b τ A}
  zero_mem' := ⟨CSupported.zero, by simp [IsSkewHermitian], TiedEntries.zero b τ⟩
  add_mem' := fun hA hB =>
    ⟨hA.1.add hB.1, skewHermitian_add hA.2.1 hB.2.1, hA.2.2.add hB.2.2⟩
  smul_mem' := fun a _ hA =>
    ⟨CSupported.real_smul a hA.1, skewHermitian_real_smul a hA.2.1, hA.2.2.smul a⟩

theorem one_mem_sharedMatrixSpace (b : ℕ) (τ : ℕ → ℕ) :
    (1 : CMat n) ∈ sharedMatrixSpace b τ := ⟨CSupported.one, TiedEntries.one b τ⟩

theorem mul_mem_sharedMatrixSpace (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ sharedMatrixSpace b τ) (hB : B ∈ sharedMatrixSpace b τ) :
    A * B ∈ sharedMatrixSpace b τ :=
  ⟨hA.1.mul hB.1, TiedEntries.mul hb hbn hA.1 hB.1 hA.2 hB.2⟩

theorem conjTranspose_mem_sharedMatrixSpace (hA : A ∈ sharedMatrixSpace b τ) :
    Aᴴ ∈ sharedMatrixSpace b τ := ⟨hA.1.conjTranspose, hA.2.conjTranspose⟩

def SharedUnitaryFactor (b : ℕ) (τ : ℕ → ℕ) (A : CMat n) : Prop :=
  CSupported (fun i => i.val / b) A ∧ Unitary A ∧ TiedEntries b τ A

/-- Inverse closure is derived from finite-dimensional linear algebra, not
postulated as a property of the sharing predicate. -/
theorem sharedMatrixSpace_inverse (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ sharedMatrixSpace b τ) (hdet : A.det ≠ 0) :
    A⁻¹ ∈ sharedMatrixSpace b τ := by
  let S := sharedMatrixSpace (n := n) b τ
  let m : S →ₗ[ℝ] S :=
    { toFun := fun X => ⟨A * X.val, mul_mem_sharedMatrixSpace hb hbn hA X.property⟩
      map_add' := by
        intro X Y
        apply Subtype.ext
        exact Matrix.mul_add A X.val Y.val
      map_smul' := by
        intro a X
        apply Subtype.ext
        change A * (a • X.val) = a • (A * X.val)
        simp only [Matrix.mul_smul] }
  have hm : Function.Injective m := by
    intro X Y h
    apply Subtype.ext
    exact GS.UnitaryManifold.cancel_left A X.val Y.val hdet (congrArg Subtype.val h)
  obtain ⟨X, hX⟩ := (LinearMap.injective_iff_surjective.mp hm)
    (⟨1, one_mem_sharedMatrixSpace b τ⟩ : S)
  have hAX : A * X.val = 1 := congrArg Subtype.val hX
  have he : X.val = A⁻¹ := by
    apply GS.UnitaryManifold.cancel_left A X.val A⁻¹ hdet
    rw [hAX, GS.UnitaryManifold.mul_inv A hdet]
  rw [← he]
  exact X.property

/-- The original rational Cayley transform preserves all physical block ties. -/
theorem cayley_mem_sharedMatrixSpace (hb : 0 < b) (hbn : b ∣ n)
    (hA : A ∈ sharedMatrixSpace b τ) (ha : admissible A) :
    cayley A ∈ sharedMatrixSpace b τ := by
  have hplus : 1 + A ∈ sharedMatrixSpace b τ :=
    (sharedMatrixSpace b τ).add_mem (one_mem_sharedMatrixSpace b τ) hA
  have hminus : 1 - A ∈ sharedMatrixSpace b τ :=
    (sharedMatrixSpace b τ).sub_mem (one_mem_sharedMatrixSpace b τ) hA
  exact mul_mem_sharedMatrixSpace hb hbn hminus
    (sharedMatrixSpace_inverse hb hbn hplus ha)

/-- Every shared skew generator gives an actual shared unitary factor. -/
theorem cayley_shared (hb : 0 < b) (hbn : b ∣ n)
    (hC : C ∈ sharedSkewSpace b τ) :
    SharedUnitaryFactor b τ (cayley C) := by
  have ha := admissible_of_isSkew C hC.2.1
  have hm := cayley_mem_sharedMatrixSpace hb hbn ⟨hC.1, hC.2.2⟩ ha
  exact ⟨hm.1, cayley_unitary C hC.2.1 ha, hm.2⟩

/-- Inverse Cayley coordinates of a shared unitary factor obey the same ties. -/
theorem cayley_sharedSkew (hb : 0 < b) (hbn : b ∣ n)
    (hA : SharedUnitaryFactor b τ A) (ha : admissible A) :
    cayley A ∈ sharedSkewSpace b τ := by
  have hm := cayley_mem_sharedMatrixSpace hb hbn ⟨hA.1, hA.2.2⟩ ha
  exact ⟨hm.1, cayley_isSkew A hA.2.1 ha, hm.2⟩

theorem shared_factor_conjTranspose (hA : SharedUnitaryFactor b τ A) :
    SharedUnitaryFactor b τ Aᴴ :=
  ⟨hA.1.conjTranspose, hA.2.1.conjTranspose, hA.2.2.conjTranspose⟩

theorem shared_factor_mul (hb : 0 < b) (hbn : b ∣ n)
    (hA : SharedUnitaryFactor b τ A) (hB : SharedUnitaryFactor b τ B) :
    SharedUnitaryFactor b τ (A * B) :=
  ⟨hA.1.mul hB.1, hA.2.1.mul hB.2.1,
    TiedEntries.mul hb hbn hA.1 hB.1 hA.2.2 hB.2.2⟩

/-- Conjugation by an actual shared factor preserves the generator space. -/
theorem sharedSkew_conjugate (hb : 0 < b) (hbn : b ∣ n)
    (hA : SharedUnitaryFactor b τ A) (hC : C ∈ sharedSkewSpace b τ) :
    A * C * Aᴴ ∈ sharedSkewSpace b τ := by
  have hm : A * C * Aᴴ ∈ sharedMatrixSpace b τ :=
    mul_mem_sharedMatrixSpace hb hbn
      (mul_mem_sharedMatrixSpace hb hbn ⟨hA.1, hA.2.2⟩ ⟨hC.1, hC.2.2⟩)
      ⟨hA.1.conjTranspose, hA.2.2.conjTranspose⟩
  refine ⟨hm.1, ?_, hm.2⟩
  change (A * C * Aᴴ)ᴴ = -(A * C * Aᴴ)
  have hskew : Cᴴ = -C := hC.2.1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hskew,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

/-- The reverse conjugation is a separate useful form of the same result. -/
theorem sharedSkew_conjugate_conjTranspose (hb : 0 < b) (hbn : b ∣ n)
    (hA : SharedUnitaryFactor b τ A) (hC : C ∈ sharedSkewSpace b τ) :
    Aᴴ * C * A ∈ sharedSkewSpace b τ := by
  simpa only [Matrix.conjTranspose_conjTranspose] using
    sharedSkew_conjugate hb hbn (shared_factor_conjTranspose hA) hC

end GS.UnitarySharing
