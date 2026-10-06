module

public import GS.UnitaryNonmanifold.ExplicitCurves
public import GS.UnitaryNonmanifold.ScalarBridge
public import GS.UnitaryNonmanifold.RetractionObstruction

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A certified smoothness counterexample for three unitary GS factors

For the original six-by-six scalar-shuffle family with block sizes 2,3,2,
two feasible smooth curves have velocities whose sum cannot be the velocity
of any differentiable feasible curve. Consequently the set admits neither
a local differentiable ambient retraction nor an embedded differentiable
flattening chart at the displayed rational base point.

This is a smooth embedded-submanifold obstruction. No claim of topological
nonmanifoldness is made for the complex family.
-/

noncomputable section
open Matrix Filter GS.UnitaryGeometry
open scoped Topology
namespace GS.UnitaryNonmanifold
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def witnessCurveA : ℝ → CMat 6 :=
  sandwichCurve 1 (fun t => ofRealMatrix (rotate01 t))
def witnessCurveB : ℝ → CMat 6 :=
  sandwichCurve (ofRealMatrix witnessH) (fun t => ofRealMatrix (rotate02 t))
def witnessVelocityA : CMat 6 := sandwichVelocity 1 (ofRealMatrix skew01)
def witnessVelocityB : CMat 6 := sandwichVelocity (ofRealMatrix witnessH) (ofRealMatrix skew02)

theorem sandwichCurve_mem (H : CMat 2) (R : ℝ → CMat 3)
    (hH : Unitary H) (hR : ∀ t, Unitary (R t)) (t : ℝ) :
    sandwichCurve H R t ∈ localFamily 3 := by
  apply (mem_localFamily_iff_BlockSandwich _).mpr
  exact sandwichMatrix_mem _ _ _ hH
    ((ofRealMatrix_unitary witnessQ_orthogonal).mul (hR t))
    ((ofRealMatrix_unitary witnessQ_orthogonal).mul (hR (-t)))

theorem witnessCurveA_zero : witnessCurveA 0 = witnessBase := by
  apply sandwichCurve_zero _ _ Unitary.one
  simp

theorem witnessCurveB_zero : witnessCurveB 0 = witnessBase := by
  apply sandwichCurve_zero _ _ (ofRealMatrix_unitary witnessH_orthogonal)
  simp

theorem witnessVelocityA_feasible :
    CurveVelocity (localFamily 3) witnessBase witnessVelocityA := by
  refine ⟨witnessCurveA, witnessCurveA_zero, ?_, ?_⟩
  · exact derivative_sandwichCurve 1 (derivative_ofRealMatrix derivative_rotate01)
  · exact Filter.Eventually.of_forall (fun t => sandwichCurve_mem _ _ Unitary.one
      (fun s => ofRealMatrix_unitary (rotate01_orthogonal s)) t)

theorem witnessVelocityB_feasible :
    CurveVelocity (localFamily 3) witnessBase witnessVelocityB := by
  refine ⟨witnessCurveB, witnessCurveB_zero, ?_, ?_⟩
  · exact derivative_sandwichCurve _ (derivative_ofRealMatrix derivative_rotate02)
  · exact Filter.Eventually.of_forall (fun t => sandwichCurve_mem _ _
      (ofRealMatrix_unitary witnessH_orthogonal)
      (fun s => ofRealMatrix_unitary (rotate02_orthogonal s)) t)

@[simp] theorem cBlock_add {q : ℕ} (A B : CMat (q*2)) (i j : Fin q) :
    cBlock (A+B) i j = cBlock A i j + cBlock B i j := rfl

theorem witnessBase_gram00 : rowGram (q := 3) witnessBase 0 0 = (1/9 : ℂ) • 1 := by
  rw [rowGram, cBlock_witnessBase]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ofRealMatrix,witnessQ,Matrix.mul_apply, Matrix.conjTranspose_apply,Matrix.one_apply,
      Fin.sum_univ_succ]

theorem witnessBase_gram01 : rowGram (q := 3) witnessBase 0 1 = (4/9 : ℂ) • 1 := by
  rw [rowGram, cBlock_witnessBase]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ofRealMatrix,witnessQ,Matrix.mul_apply, Matrix.conjTranspose_apply,Matrix.one_apply,
      Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
/-- Exact rational arithmetic certificate for the nonlinear velocity obstruction. -/
theorem witness_sum_gram_noncommutation :
    gramVelocity (q := 3) witnessBase (witnessVelocityA+witnessVelocityB) 0 0 *
      gramVelocity (q := 3) witnessBase (witnessVelocityA+witnessVelocityB) 0 1 ≠
    gramVelocity (q := 3) witnessBase (witnessVelocityA+witnessVelocityB) 0 1 *
      gramVelocity (q := 3) witnessBase (witnessVelocityA+witnessVelocityB) 0 0 := by
  intro he
  have hentry := congrFun (congrFun he 0) 1
  simp only [gramVelocity,cBlock_add (q := 3),witnessVelocityA,witnessVelocityB,
    sandwichVelocity,cBlock_sandwichMatrix (q := 3),cBlock_witnessBase] at hentry
  norm_num [ofRealMatrix,witnessQ,witnessH,skew01,skew02,diagTwo,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,
    Fin.sum_univ_succ] at hentry


/-- The sum of two genuine feasible velocities is not a feasible velocity. -/
theorem witnessVelocity_sum_not_feasible :
    ¬ CurveVelocity (localFamily 3) witnessBase (witnessVelocityA+witnessVelocityB) := by
  rintro ⟨f,hf0,hf,hmem⟩
  have hmem' : ∀ᶠ t in 𝓝 (0 : ℝ), BlockSandwich (f t) :=
    hmem.mono (fun _ ht => (mem_localFamily_iff_BlockSandwich _).mp ht)
  have hj : rowGram (q := 3) (f 0) 0 0 = (1/9 : ℂ) • 1 := by
    rw [hf0]; exact witnessBase_gram00
  have hk : rowGram (q := 3) (f 0) 0 1 = (4/9 : ℂ) • 1 := by
    rw [hf0]; exact witnessBase_gram01
  have hcomm := curve_gramVelocities_commute (q := 3) hf hmem' 0 0 1 (1/9) (4/9) hj hk
  rw [hf0] at hcomm
  exact witness_sum_gram_noncommutation hcomm

theorem witnessBase_mem : witnessBase ∈ localFamily 3 := by
  rw [← witnessCurveA_zero]
  exact sandwichCurve_mem _ _ Unitary.one
    (fun s => ofRealMatrix_unitary (rotate01_orthogonal s)) 0

/-- No local ambient retraction onto the original unitary GS set can be
differentiable at this rational base point. -/
theorem unitary_three_no_differentiable_local_retraction
    (R : CMat 6 → CMat 6)
    (hlocal : ∀ᶠ Y in 𝓝 witnessBase,
      R Y ∈ localFamily 3 ∧ (Y ∈ localFamily 3 → R Y = Y)) :
    ¬ DifferentiableAt ℝ R witnessBase :=
  no_differentiable_local_retraction witnessVelocityA_feasible witnessVelocityB_feasible
    witnessVelocity_sum_not_feasible R hlocal

/-- The original unitary GS set is not an embedded differentiable submanifold
at this point, for any choice of tangent and normal coordinate spaces. -/
theorem unitary_three_no_local_differentiable_flattening
    (F G : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] :
    ¬ HasLocalDifferentiableFlattening (F := F) (G := G) (localFamily 3) witnessBase :=
  no_local_differentiable_flattening witnessVelocityA_feasible witnessVelocityB_feasible
    witnessVelocity_sum_not_feasible

end GS.UnitaryNonmanifold
