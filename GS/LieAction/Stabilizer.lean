module

public import GS.LieAction.Action
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Stabilizer of P and the exact factorization ambiguity

All stabilizers in this file are mathlib's MulAction.stabilizer. The
isomorphism with the common right block subgroup is constructive. P is allowed
to be any orthogonal matrix in the first part; permutations are needed only
for the coordinate-support characterization at the end.

-/

noncomputable section
open Matrix
namespace GS.LieAction
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}

abbrev PointStabilizer (block₁ block₂ : Fin n → ℕ) (P : Mat n) :=
  MulAction.stabilizer (FactorGroup block₁ block₂) P

/-- The left factor is completely determined by the right factor at the
stabilizer. Both directions use the actual orthogonality equations. -/
theorem stabilizer_iff (P : Mat n) (hP : Orthogonal P)
    (g : FactorGroup block₁ block₂) :
    g ∈ PointStabilizer block₁ block₂ P ↔
      g.1.val = P * g.2.val * Pᵀ := by
  change g.1.val * P * g.2.valᵀ = P ↔ _
  constructor
  · intro hg
    calc
      g.1.val = (g.1.val * P * g.2.valᵀ) * g.2.val * Pᵀ := by
        symm
        calc
          _ = g.1.val * (P * (g.2.valᵀ * g.2.val) * Pᵀ) := by
            simp only [Matrix.mul_assoc]
          _ = g.1.val := by rw [g.2.property.2.1]; simp [hP.2]
      _ = P * g.2.val * Pᵀ := by rw [hg]
  · intro hg
    rw [hg]
    calc
      (P * g.2.val * Pᵀ) * P * g.2.valᵀ =
          P * g.2.val * (Pᵀ * P) * g.2.valᵀ := by simp only [Matrix.mul_assoc]
      _ = P := by rw [hP.1]; simp [Matrix.mul_assoc, g.2.property.2.2]

/-- Fibres are right cosets of the actual stabilizer, with the convention
(g h) • P = g • (h • P). -/
theorem orbit_fibre_iff (P : Mat n) (g h : FactorGroup block₁ block₂) :
    orbitMap block₁ block₂ P g = orbitMap block₁ block₂ P h ↔
      g⁻¹ * h ∈ PointStabilizer block₁ block₂ P := by
  change g • P = h • P ↔ (g⁻¹ * h) • P = P
  constructor
  · intro he
    rw [mul_smul, ← he, inv_smul_smul]
  · intro he
    have he' := congrArg (fun X : Mat n => g • X) he
    have hh : h • P = g • P := by
      simpa only [mul_smul, smul_inv_smul] using he'
    exact hh.symm

/-- Right factors whose conjugates also obey the left block constraints. -/
def commonRightSubgroup (block₁ block₂ : Fin n → ℕ) (P : Mat n)
    (hP : Orthogonal P) : Subgroup (BlockO block₁) where
  carrier := {T | Supported block₂ (P * T.val * Pᵀ)}
  one_mem' := by simpa [hP.2] using (GS.Supported.one (block := block₂))
  mul_mem' := by
    intro A B hA hB
    change Supported block₂ (P * (A.val * B.val) * Pᵀ)
    have he : P * (A.val * B.val) * Pᵀ =
        (P * A.val * Pᵀ) * (P * B.val * Pᵀ) := by
      calc
        _ = P * A.val * (Pᵀ * P) * B.val * Pᵀ := by
          rw [hP.1]; simp [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [he]
    exact hA.mul hB
  inv_mem' := by
    intro A hA
    change Supported block₂ (P * A.valᵀ * Pᵀ)
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      using hA.transpose

/-- Construct a stabilizer element from its right component. -/
def stabilizerFromRight (P : Mat n) (hP : Orthogonal P)
    (T : commonRightSubgroup block₁ block₂ P hP) :
    PointStabilizer block₁ block₂ P := by
  let g : FactorGroup block₁ block₂ :=
    (⟨P * T.val.val * Pᵀ, T.property,
       (hP.mul T.val.property.2).mul hP.transpose⟩, T.val)
  exact ⟨g, (stabilizer_iff P hP g).mpr rfl⟩

/-- Recover the common right factor from a stabilizer element. -/
def rightFromStabilizer (P : Mat n) (hP : Orthogonal P)
    (g : PointStabilizer block₁ block₂ P) :
    commonRightSubgroup block₁ block₂ P hP := by
  refine ⟨g.val.2, ?_⟩
  change Supported block₂ (P * g.val.2.val * Pᵀ)
  rw [← (stabilizer_iff P hP g.val).mp g.property]
  exact g.val.1.property.1

/-- Algebraic stabilizer theorem with the right factor as coordinate. -/
def stabilizerRightEquiv (P : Mat n) (hP : Orthogonal P) :
    PointStabilizer block₁ block₂ P ≃*
      commonRightSubgroup block₁ block₂ P hP where
  toFun := rightFromStabilizer P hP
  invFun := stabilizerFromRight P hP
  left_inv g := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact ((stabilizer_iff P hP g.val).mp g.property).symm
    · rfl
  right_inv T := by
    apply Subtype.ext
    rfl
  map_mul' g h := by
    apply Subtype.ext
    rfl

/-- The stabilizer is closed in the compact topological factor group. -/
theorem closed_stabilizer (P : Mat n) :
    IsClosed (PointStabilizer block₁ block₂ P : Set (FactorGroup block₁ block₂)) := by
  change IsClosed {g : FactorGroup block₁ block₂ | g • P = P}
  exact isClosed_eq (continuous_orbitMap block₁ block₂ P) continuous_const

instance stabilizerCompactSpace (P : Mat n) :
    CompactSpace (PointStabilizer block₁ block₂ P) :=
  isCompact_iff_compactSpace.mp (closed_stabilizer P).isCompact

/-- The explicit group isomorphism is also a homeomorphism for the inherited
matrix topologies. It is not asserted to be a diffeomorphism here. -/
def stabilizerRightHomeomorph (P : Mat n) (hP : Orthogonal P) :
    PointStabilizer block₁ block₂ P ≃ₜ
      commonRightSubgroup block₁ block₂ P hP where
  toEquiv := (stabilizerRightEquiv P hP).toEquiv
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_snd.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      have hT : Continuous (fun T : commonRightSubgroup block₁ block₂ P hP => T.val.val) :=
        continuous_subtype_val.comp continuous_subtype_val
      exact continuous_matrix_product
        (continuous_matrix_product continuous_const hT) continuous_const
    · exact continuous_subtype_val

/-- Conjugating by a permutation transports the labels; it does not discard
any off-block constraint. -/
theorem common_support_iff (σ : Equiv.Perm (Fin n)) (T : Mat n) :
    Supported block₂ (permMatrix σ * T * (permMatrix σ)ᵀ) ↔
      Supported (fun i => block₂ (σ i)) T := by
  constructor
  · intro hs i j hij
    have he := hs (σ i) (σ j) hij
    simpa only [perm_conjugate_apply, Equiv.symm_apply_apply] using he
  · intro hs i j hij
    rw [perm_conjugate_apply]
    exact hs (σ.symm i) (σ.symm j) (by simpa using hij)

theorem commonRight_mem_iff (σ : Equiv.Perm (Fin n)) (T : BlockO block₁) :
    T ∈ commonRightSubgroup block₁ block₂ (permMatrix σ) (perm_orthogonal σ) ↔
      Supported (fun i => block₂ (σ i)) T.val :=
  common_support_iff σ T.val

end GS.LieAction
