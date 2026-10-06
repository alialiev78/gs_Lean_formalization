module

public import GS.Specifications
public import GS.Revision.ThreeFactorPartitions
public import GS.Revision.M4Neighborhood

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Revised theorem targets and explicit status boundaries

A definition whose name ends in Goal is only a proposition specification.
The two revised algebraic goals below have proof scripts. The all-parity
rank-one nonmanifold goal remains an OPEN specification. The conditional
comparison theorem does not count as a proof of either nonmanifold goal.

-/
noncomputable section
open GS Matrix
namespace GS.Revision.Specifications

/-- Unlike the old BlockSpec formulation, consecutive blocks need not be equal. -/
def ThreeFactorUnequalBlocksGoal : Prop :=
  ∀ (n : ℕ) (b₁ b₂ b₃ : Fin n → ℕ), Monotone b₂ →
    ∀ (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : Mat n),
      Partitions.InA3 b₁ b₂ b₃ (permMatrix σ₁) (permMatrix σ₂) A ∧ Orthogonal A ↔
        Partitions.InA3Orth b₁ b₂ b₃ (permMatrix σ₁) (permMatrix σ₂) A

theorem threeFactorUnequalBlocks : ThreeFactorUnequalBlocksGoal := by
  intro n b₁ b₂ b₃ hb₂ σ₁ σ₂ A
  exact Partitions.threeFactorOrthogonalization b₁ b₂ b₃ hb₂ σ₁ σ₂ A

/-- No denominator-nonvanishing restriction, unlike the old ratio goal. -/
def FourFactorPolynomialGoal : Prop :=
  ∀ A : Mat 6, InA4Orth 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P A →
    0 ≤ GS.Revision.M4.obstructionPolynomial (GS.M4.absDetBlock A)

theorem fourFactorPolynomial : FourFactorPolynomialGoal := GS.Revision.M4.necessary

/-- OPEN: this is the revised topological obstruction for all a,b ≥ 2, with
no parity hypothesis. It includes arbitrary Euclidean factors. -/
def GeneralRankOneNonManifoldGoal : Prop :=
  ∀ (a b s : ℕ), 2 ≤ a → 2 ≤ b →
    ¬ EuclideanAtSubset
      ({p : (Fin s → ℝ) × Matrix (Fin a) (Fin b) ℝ | Matrix.rank p.2 ≤ 1}) (0, 0)

/-- Only a comparison between specifications, with its hypothesis visible. -/
theorem oldConeGoal_of_general (h : GeneralRankOneNonManifoldGoal) :
    GS.Specifications.ConeProductNonManifoldGoal := by
  intro d e hd
  exact h 2 d e (by omega) (by omega)

end GS.Revision.Specifications
