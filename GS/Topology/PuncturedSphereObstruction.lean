module

public import GS.NonmanifoldClosure.PuncturedBall
public import GS.Topology.SphereApproximation
public import GS.Topology.SphereNoncontractible
public import GS.Topology.BrouwerFixedPoint

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Sphere retractions determine the dimension of a punctured ball

Radial normalization turns a strict section pair for a punctured ball into a
homotopy section pair for its sphere. If the two sphere dimensions differ,
one of its two maps goes from a lower-dimensional sphere to a higher-dimensional
sphere and is nullhomotopic. The composite identity would then be nullhomotopic,
contradicting the closed-ball fixed-point theorem.

No homology computations or invariance-of-domain theorem are used.
-/

noncomputable section

open GS.NonmanifoldClosure GS.NonmanifoldFinal GS.NonmanifoldObstruction

namespace GS.Topology

/-- Radial conversion preserves the section identity up to an explicit homotopy. -/
theorem sphere_retract_ball_dimension_of_fixedPoint (m n : ℕ)
    [BrouwerFixedPoint (EuclideanSpace ℝ (Fin m))]
    {r : ℝ} (hr : 0 < r)
    (p : ContinuousSectionPair (UnitSphere (Fin m))
      (PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r)) : n = m := by
  let a : C(UnitSphere (Fin m), PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r) :=
    ⟨p.sectionMap, p.section_continuous⟩
  let b : C(PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r, UnitSphere (Fin m)) :=
    ⟨p.retractionMap, p.retraction_continuous⟩
  let v : C(PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r, UnitSphere (Fin n)) :=
    (⟨normSphereStandard n, (normSphereStandard n).continuous⟩ :
      C(NormSphere (EuclideanSpace ℝ (Fin n)), UnitSphere (Fin n))).comp
      ⟨ballNormalize, continuous_ballNormalize r⟩
  let w : C(UnitSphere (Fin n), PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r) :=
    (⟨ballSection hr, continuous_ballSection hr⟩ :
      C(NormSphere (EuclideanSpace ℝ (Fin n)),
        PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r)).comp
      ⟨(normSphereStandard n).symm, (normSphereStandard n).symm.continuous⟩
  let s := v.comp a
  let t := b.comp w
  have hid : ContinuousMap.Homotopic (t.comp s) (ContinuousMap.id (UnitSphere (Fin m))) := by
    refine ⟨{
      toFun := fun z => b (radialDeform hr (z.1, a z.2))
      continuous_toFun := b.continuous.comp
        ((continuous_radialDeform hr).comp (continuous_fst.prodMk (a.continuous.comp continuous_snd)))
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro x
      change b (radialDeform hr (0, a x)) = b (w (v (a x)))
      congr 1
      change radialDeform hr (0, a x) =
        ballSection hr ((normSphereStandard n).symm
          ((normSphereStandard n) (ballNormalize (a x))))
      rw [Homeomorph.symm_apply_apply]
      exact (puncturedBallHomotopy hr).map_zero_left (a x)
    · intro x
      change b (radialDeform hr (1, a x)) = x
      have he : radialDeform hr (1, a x) = a x :=
        (puncturedBallHomotopy hr).map_one_left (a x)
      exact (congrArg b he).trans (p.retraction_section x)
  by_contra hne
  have hnull : (t.comp s).Nullhomotopic := by
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · exact (sphereMap_nullhomotopic_of_finrank_lt
        (by simpa using hnm) t).comp_left s
    · exact (sphereMap_nullhomotopic_of_finrank_lt
        (by simpa using hmn) s).comp_right t
  obtain ⟨c, hc⟩ := hnull
  have hId : (ContinuousMap.id (UnitSphere (Fin m))).Nullhomotopic :=
    ⟨c, hid.symm.trans hc⟩
  exact sphere_id_not_nullhomotopic_of_fixedPoint
    (fun f => BrouwerFixedPoint.brouwer_fixed_point f f.continuous) hId

/-- Unconditional dimension equality, using the proved closed-ball Brouwer theorem. -/
theorem sphere_retract_ball_dimension (m n : ℕ) {r : ℝ} (hr : 0 < r)
    (p : ContinuousSectionPair (UnitSphere (Fin m))
      (PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r)) : n = m :=
  sphere_retract_ball_dimension_of_fixedPoint m n hr p

end GS.Topology
