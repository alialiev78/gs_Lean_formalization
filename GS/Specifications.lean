module

public import GS.ThreeFactor
public import GS.OriginalLocalModel
public import GS.M4Necessary

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Theorem specifications -- definitions alone are not proofs

The Goal definitions specify propositions; definitions alone do not prove them.
The final two theorems link the m=4 proofs to their specifications. Extensions,
Continuation, and NonmanifoldClosure prove the other original specifications.
The public interface is `GSResults`; the scope is described in docs/RESULTS.md.
The suffix `Goal` labels a specification, not an assertion that it is proved.
-/

noncomputable section
open Matrix
namespace GS.Specifications

/-- Original m=2 equality, for actual matrices and actual permutations. -/
def TwoFactorOrthogonalizationGoal : Prop :=
  ∀ (n : ℕ) (s₁ s₂ : BlockSpec n) (σ : Equiv.Perm (Fin n)) (A : Mat n),
    InA2 s₁.size s₂.size (permMatrix σ) A ∧ Orthogonal A ↔
      InA2Orth s₁.size s₂.size (permMatrix σ) A

/-- The main arbitrary-permutation m=3 specification. -/
def ThreeFactorOrthogonalizationGoal : Prop :=
  ∀ (n : ℕ) (s₁ s₂ s₃ : BlockSpec n)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : Mat n),
    InA3 s₁.size s₂.size s₃.size (permMatrix σ₁) (permMatrix σ₂) A ∧ Orthogonal A ↔
      InA3Orth s₁.size s₂.size s₃.size (permMatrix σ₁) (permMatrix σ₂) A

/-- Structured QR existence, including all required support properties. -/
def StructuredQRGoal : Prop :=
  ∀ (n : ℕ) (s : BlockSpec n) (B : Mat n) (σ : Equiv.Perm (Fin n)),
    BlockDiagonal s.size B → IsUnit B.det →
      ∃ U R : Mat n, BlockDiagonal s.size U ∧ Orthogonal U ∧ Upper R ∧
        B * permMatrix σ = U * permMatrix σ * R

/-- The right-sided RQ counterpart. -/
def StructuredRQGoal : Prop :=
  ∀ (n : ℕ) (s : BlockSpec n) (B : Mat n) (σ : Equiv.Perm (Fin n)),
    BlockDiagonal s.size B → IsUnit B.det →
      ∃ U R : Mat n, BlockDiagonal s.size U ∧ Orthogonal U ∧ Upper R ∧
        permMatrix σ * B = R * permMatrix σ * U

/-- The two existence goals suffice for the full arbitrary-permutation m=3
statement. They remain explicit hypotheses; neither is assumed as an axiom. -/
theorem threeFactorOrthogonalization_of_structured
    (hqr : StructuredQRGoal) (hrq : StructuredRQGoal) :
    ThreeFactorOrthogonalizationGoal := by
  intro n s₁ s₂ s₃ σ₁ σ₂ A
  constructor
  · rintro ⟨⟨B₁, B₂, B₃, hb₁, hb₂, hb₃, he⟩, hA⟩
    have hdetA : A.det ≠ 0 := by
      intro hz
      have hgram := congrArg Matrix.det hA.1
      simp [Matrix.det_mul, Matrix.det_transpose, hz] at hgram
    have hprod : B₃.det * (permMatrix σ₂).det * B₂.det *
        (permMatrix σ₁).det * B₁.det ≠ 0 := by
      simpa only [he, product3, Matrix.det_mul] using hdetA
    have hdet₁ : IsUnit B₁.det := isUnit_iff_ne_zero.mpr (by
      intro hz
      exact hprod (by simp [hz]))
    have hdet₃ : IsUnit B₃.det := isUnit_iff_ne_zero.mpr (by
      intro hz
      exact hprod (by simp [hz]))
    obtain ⟨U₃, R₃, hu₃, ho₃, ht₃, eq₃⟩ := hqr n s₃ B₃ σ₂ hb₃ hdet₃
    obtain ⟨U₁, R₁, hu₁, ho₁, ht₁, eq₁⟩ := hrq n s₁ B₁ σ₁ hb₁ hdet₁
    exact threeFactor_from_structured_QR_RQ B₁ B₂ B₃
      (permMatrix σ₁) (permMatrix σ₂) A U₁ U₃ R₁ R₃ hb₂ hu₁ hu₃ ho₁ ho₃
      (perm_orthogonal σ₁) (perm_orthogonal σ₂) hA he eq₃ eq₁ ht₁ ht₃
  · exact inA3Orth_implies_inA3_and_orthogonal (perm_orthogonal σ₁)
      (perm_orthogonal σ₂)

/-- The concrete support statement for a Cholesky factor. This does not identify
Cholesky with the symmetric positive square root. -/
def CholeskySupportGoal : Prop :=
  ∀ (n : ℕ) (s : BlockSpec n) (B R : Mat n) (σ : Equiv.Perm (Fin n)),
    BlockDiagonal s.size B → IsUnit B.det → Upper R →
    Rᵀ*R = (permMatrix σ)ᵀ*Bᵀ*B*permMatrix σ →
      BlockDiagonal s.size (permMatrix σ * R * (permMatrix σ)ᵀ)

/-- All original f/g fibres on a uniformly small closed parameter domain. -/
def OriginalSameFibresGoal : Prop :=
  ∀ (q : ℕ), 3 ≤ q → ∀ (Q₀ : Mat q),
    Orthogonal Q₀ → Q₀.det=1 → (∀ i j, Q₀ i j ≠ 0) →
    ∃ η : ℝ, 0 < η ∧ ∀ p ∈ originalK q η, ∀ p' ∈ originalK q η,
      originalF Q₀ p = originalF Q₀ p' ↔ originalG p = originalG p'

/-- Uniform local coverage, not merely a claim about the selected image branch. -/
def OriginalLocalCoverageGoal : Prop :=
  ∀ (q : ℕ), 3 ≤ q → ∀ (Q₀ : Mat q),
    Orthogonal Q₀ → Q₀.det=1 → (∀ i j, Q₀ i j ≠ 0) →
    ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧
      ∀ M ∈ localFamily q, frobDistSq M (basePoint Q₀) < ε^2 →
        ∃ p ∈ originalK q η, originalF Q₀ p = M

/-- The topological, not just differentiable, nonmanifold assertion. -/
def NonManifoldGoal : Prop :=
  ∀ (q : ℕ), 3 ≤ q → ∀ (Q₀ : Mat q),
    Orthogonal Q₀ → Q₀.det=1 → (∀ i j, Q₀ i j ≠ 0) →
      ¬ EuclideanAtSubset (localFamily q) (basePoint Q₀)

/-- The cone product obstruction after the local model. It is proved in
`GS.NonmanifoldTopology.coneProductNonManifold` using a topological argument;
the optional sphere-homology computation is not needed. -/
def ConeProductNonManifoldGoal : Prop :=
  ∀ (d e : ℕ), 3 ≤ d →
    ¬ EuclideanAtSubset
      ({p : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ | Matrix.rank p.2 ≤ 1})
      (0,0)

/-- Necessary block-determinant inequality, not inferred from its violation. -/
def FourFactorNecessaryConditionGoal : Prop :=
  ∀ Q : Mat 6, InA4Orth 2 2 2 2 M4.P M4.P M4.P Q →
    let d := fun i j => |M4.detBlock Q i j|
    d 2 1 * d 1 0 * d 1 1 ≠ 0 →
      (1-d 0 2*d 1 0/d 2 1)*(1-d 0 2*d 2 1/d 1 0) ≥ d 0 0*d 2 2/d 1 1

/-- Full nonmembership specification. A proof script is linked below. -/
def FourFactorCounterexampleGoal : Prop :=
  InA4 2 2 2 2 M4.P M4.P M4.P M4.Q ∧ Orthogonal M4.Q ∧
    ¬ InA4Orth 2 2 2 2 M4.P M4.P M4.P M4.Q

/-- Positive membership alone; nonmembership is supplied by the separate theorem below. -/
theorem fourFactor_positive_membership :
    InA4 2 2 2 2 M4.P M4.P M4.P M4.Q ∧ Orthogonal M4.Q :=
  ⟨M4.Q_mem_A4, M4.Q_orthogonal⟩

/-- Full m=4 proof linked to its specification.  -/
theorem fourFactorCounterexample_draft : FourFactorCounterexampleGoal := M4.counterexample

theorem fourFactorNecessaryCondition_draft : FourFactorNecessaryConditionGoal :=
  M4.necessaryCondition

end GS.Specifications
