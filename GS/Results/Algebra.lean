module

public import GS.Extensions.StructuredRQ
public import GS.Revision.Specifications

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Public algebraic results

This module is the entry point for the factorization results. The original
specification aliases below are unconditional proofs; the specification
definitions are propositions, not additional assumptions.

The proof dependencies are organized as follows:

* `Extensions.CholeskySupport` recovers support from a triangular Gram factor.
* `Extensions.OrdinaryQR` constructs QR and proves its structured variant.
* `Extensions.StructuredRQ` proves RQ, then the three- and two-factor equalities.
* `M4Necessary` proves the determinant obstruction and its explicit counterexample.
* `Revision.ThreeFactorPartitions` allows unequal consecutive middle blocks.
* `Revision.M4Polynomial` and `Revision.M4Neighborhood` remove the denominator
  condition and obtain an open neighborhood excluded from the orthogonal class.

These names consolidate existing proofs; they do not assert new mathematics.
All block and permutation hypotheses remain in the displayed specifications.
-/

namespace GS.Results.Algebra

/-- Any orthogonal matrix in the two-factor class admits an orthogonal
factorization with the same block sizes and the same permutation. -/
theorem twoFactorOrthogonalization : Specifications.TwoFactorOrthogonalizationGoal :=
  Extensions.twoFactorOrthogonalization

/-- Three-factor orthogonalization for arbitrary permutations and the original
equal-size block specification for each layer. -/
theorem threeFactorOrthogonalization : Specifications.ThreeFactorOrthogonalizationGoal :=
  Extensions.threeFactorOrthogonalization

/-- Structured QR for an invertible block-diagonal matrix. The orthogonal factor
has the original block support, and the remaining factor is upper triangular. -/
theorem structuredQR : Specifications.StructuredQRGoal :=
  Extensions.structuredQR

/-- Structured RQ with the same support and invertibility conditions as QR. -/
theorem structuredRQ : Specifications.StructuredRQGoal :=
  Extensions.structuredRQ

/-- A triangular Gram factor inherits the permuted block support. No
identification with the symmetric positive square root is used. -/
theorem choleskySupport : Specifications.CholeskySupportGoal :=
  Extensions.choleskySupport

/-- The original ratio obstruction for four orthogonal factors. Its explicit
denominator nonvanishing assumption is part of the specification. -/
theorem fourFactorNecessaryCondition : Specifications.FourFactorNecessaryConditionGoal :=
  GS.M4.necessaryCondition

/-- The explicit six-dimensional matrix has a structured four-factor
factorization and is orthogonal, but has no such orthogonal factorization. -/
theorem fourFactorCounterexample : Specifications.FourFactorCounterexampleGoal :=
  GS.M4.counterexample

/-- Set-level form of the counterexample: four orthogonal structured factors
give a proper subset of the orthogonal matrices with four structured factors. -/
theorem fourFactorStrictInclusion :
    {A : Mat 6 | InA4Orth 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P A} ⊂
      {A : Mat 6 | InA4 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P A ∧ Orthogonal A} := by
  constructor
  · intro A hA
    obtain ⟨B₁, B₂, B₃, B₄, hb₁, hb₂, hb₃, hb₄, ho₁, ho₂, ho₃, ho₄, he⟩ := hA
    refine ⟨⟨B₁, B₂, B₃, B₄, hb₁, hb₂, hb₃, hb₄, he⟩, ?_⟩
    rw [he]
    exact ((((((ho₄.mul GS.M4.P_orthogonal).mul ho₃).mul
      GS.M4.P_orthogonal).mul ho₂).mul GS.M4.P_orthogonal).mul ho₁)
  · intro h
    exact GS.M4.Q_not_mem_A4Orth (h ⟨GS.M4.Q_mem_A4, GS.M4.Q_orthogonal⟩)

/-- The stronger three-factor result permits arbitrary outer coordinate
partitions and unequal consecutive middle blocks (monotone middle labels). -/
theorem threeFactorUnequalBlocks : Revision.Specifications.ThreeFactorUnequalBlocksGoal :=
  Revision.Specifications.threeFactorUnequalBlocks

/-- A necessary polynomial inequality for four orthogonal factors, valid even
when the denominators in the original ratio inequality vanish. -/
theorem fourFactorPolynomial : Revision.Specifications.FourFactorPolynomialGoal :=
  Revision.Specifications.fourFactorPolynomial

/-- The four-factor obstruction holds on an open neighborhood of the explicit
counterexample in the ambient matrix space. -/
theorem fourFactorOpenExclusion :
    ∃ U : Set (Mat 6), IsOpen U ∧ GS.M4.Q ∈ U ∧
      ∀ A ∈ U, ¬ InA4Orth 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P A :=
  Revision.M4.open_exclusion_neighborhood

end GS.Results.Algebra
