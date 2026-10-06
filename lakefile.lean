import Lake
open Lake DSL

package gs_formalization where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

lean_lib GS where
  roots := #[`GS, `GSExtensions, `GSContinuation, `GSLieAction, `GSCayleyCharts,
    `GSRevisionAlgebra, `GSRevision, `GSNonmanifold,
    `GSNonmanifoldMembership, `GSNonmanifoldCoverage, `GSNonmanifoldCompletion,
    `GSNonmanifoldSphereRetract, `GSNonmanifoldOpenGerms, `GSHomologyFunctor,
    `GSNonmanifoldBridge, `GSNonmanifoldHomology, `GSNonmanifoldBallHomology,
    `GSNonmanifoldClosure, `GSDifferentiableObstruction, `GSManifoldCompletion,
    `GSNonmanifoldTopology, `GSResults]
  globs := #[.submodules `GS, .one `GS, .one `GSExtensions, .one `GSContinuation,
    .one `GSLieAction, .one `GSCayleyCharts, .one `GSRevisionAlgebra, .one `GSRevision, .one `GSNonmanifold, .one `GSNonmanifoldMembership,
    .one `GSNonmanifoldCoverage, .one `GSNonmanifoldCompletion,
    .one `GSNonmanifoldSphereRetract, .one `GSNonmanifoldOpenGerms,
    .one `GSHomologyFunctor, .one `GSNonmanifoldBridge, .one `GSNonmanifoldHomology,
    .one `GSNonmanifoldBallHomology, .one `GSNonmanifoldClosure,
    .one `GSDifferentiableObstruction, .one `GSManifoldCompletion,
    .one `GSNonmanifoldTopology, .one `GSResults]

-- The default entry point includes all project modules and the unconditional
-- nonmanifold theorem. `lake build GS` also verifies the full source collection.
@[default_target]
lean_lib GSChecked where
  roots := #[`GSChecked]
  globs := #[.one `GSChecked]

lean_lib Challenge where
  roots := #[`Challenge]

lean_lib Solution where
  roots := #[`Solution]
