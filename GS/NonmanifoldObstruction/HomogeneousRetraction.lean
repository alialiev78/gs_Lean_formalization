module

public import GS.Nonmanifold.RadialCone

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A norm-preserving plane retract of the WHOLE two-row rank-one cone

The old circle retraction is defined only on the link. The maps below extend
it over the vertex. This distinction matters when an additional Euclidean
factor is present: removing the marked point does NOT remove the entire
zero-matrix stratum.

All norms occurring in the identities are the explicit sums of squares below.
They are not identified with the default matrix norm. This module does not
assert a homology computation or a nonmanifold theorem.
-/
noncomputable section
open Matrix GS GS.Extensions GS.GlobalGeometry GS.Nonmanifold Filter
open scoped BigOperators Topology
namespace GS.NonmanifoldObstruction

abbrev RankCone (κ : Type*) [Fintype κ] [DecidableEq κ] :=
  {W : Matrix (Fin 2) κ ℝ // W.rank ≤ 1}

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def coneZero : RankCone κ := ⟨0, by simp⟩

def planeSq (v : CircleVector) : ℝ := v 0 ^ 2 + v 1 ^ 2

def planeRadius (v : CircleVector) : ℝ := Real.sqrt (planeSq v)

theorem planeSq_nonneg (v : CircleVector) : 0 ≤ planeSq v := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem planeSq_eq_zero_iff (v : CircleVector) : planeSq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h0 : v 0 = 0 := by dsimp [planeSq] at h; nlinarith [sq_nonneg (v 1)]
    have h1 : v 1 = 0 := by dsimp [planeSq] at h; nlinarith [sq_nonneg (v 0)]
    ext i
    fin_cases i <;> simp [h0, h1]
  · rintro rfl
    simp [planeSq]

theorem planeRadius_nonneg (v : CircleVector) : 0 ≤ planeRadius v := Real.sqrt_nonneg _

theorem planeRadius_sq (v : CircleVector) : planeRadius v ^ 2 = planeSq v :=
  Real.sq_sqrt (planeSq_nonneg v)

theorem planeRadius_eq_zero_iff (v : CircleVector) : planeRadius v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply (planeSq_eq_zero_iff v).mp
    rw [← planeRadius_sq, h]
    norm_num
  · rintro rfl
    simp [planeRadius, planeSq]

theorem continuous_planeRadius : Continuous planeRadius := by
  unfold planeRadius planeSq
  fun_prop

/-- The quadratic Gram identity, valid on the actual rank cone. -/
theorem circleCoordinate_sq (W : Matrix (Fin 2) κ ℝ) (hW : W.rank ≤ 1) :
    planeSq (circleCoordinate W) = frobSq W ^ 2 := by
  obtain ⟨u, hu, z, hz⟩ := exists_unit_outer_of_rank_le_one W hW
  rw [← hz, frobSq_outer hu z]
  change (rowGram (outer u z) 0 0 - rowGram (outer u z) 1 1)^2 +
    (2 * rowGram (outer u z) 0 1)^2 = (∑ j, z j^2)^2
  simp only [rowGram_outer]
  calc
    _ = (u 0^2 + u 1^2)^2 * (∑ j, z j^2)^2 := by ring
    _ = _ := by rw [show u 0^2 + u 1^2 = 1 from hu]; ring

/-- Division is total in Lean. At W=0 the numerator is zero, hence the value
is zero. Continuity at this point is proved separately, not by div-continuity. -/
def coneToPlane (W : RankCone κ) : CircleVector :=
  fun i => circleCoordinate W.val i / frobeniusRadius W.val

@[simp] theorem coneToPlane_zero : coneToPlane (coneZero : RankCone κ) = 0 := by
  ext i
  simp [coneToPlane, coneZero, circleCoordinate, rowGram, frobeniusRadius, frobSq, frobInner]

/-- Radius preservation is stronger than boundedness; it excludes new zeros. -/
theorem coneToPlane_sq (W : RankCone κ) : planeSq (coneToPlane W) = frobSq W.val := by
  by_cases hz : W.val = 0
  · have he : W = coneZero := Subtype.ext hz
    rw [he, coneToPlane_zero]
    simp [planeSq, coneZero, frobSq, frobInner]
  · have hr := frobeniusRadius_ne_zero hz
    have hg := circleCoordinate_sq W.val W.property
    have hn := frobeniusRadius_sq W.val
    dsimp [planeSq, coneToPlane] at hg ⊢
    field_simp [hr]
    nlinarith [congrArg (fun a : ℝ => frobSq W.val * a) hn]

theorem coneToPlane_eq_zero_iff (W : RankCone κ) :
    coneToPlane W = 0 ↔ W = coneZero := by
  constructor
  · intro h
    apply Subtype.ext
    apply (frobSq_eq_zero_iff W.val).mp
    rw [← coneToPlane_sq, h]
    simp [planeSq]
  · rintro rfl
    exact coneToPlane_zero

/-- Each component tends to zero with the Frobenius radius. -/
theorem abs_coneToPlane_le (W : RankCone κ) (i : Fin 2) :
    |coneToPlane W i| ≤ frobeniusRadius W.val := by
  have hn := coneToPlane_sq W
  have hr := frobeniusRadius_sq W.val
  have hp := frobeniusRadius_nonneg W.val
  have hs : (coneToPlane W i)^2 ≤ frobSq W.val := by
    fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one, id_eq] <;>
      dsimp [planeSq] at hn <;> nlinarith [sq_nonneg (coneToPlane W 0),
      sq_nonneg (coneToPlane W 1)]
  nlinarith [sq_abs (coneToPlane W i), abs_nonneg (coneToPlane W i)]

/-- In particular continuous on the zero-matrix stratum of every product. -/
theorem continuous_coneToPlane : Continuous (coneToPlane : RankCone κ → CircleVector) := by
  apply continuous_iff_continuousAt.mpr
  intro W
  apply continuousAt_pi.mpr
  intro i
  by_cases hz : W.val = 0
  · have hW : W = coneZero := Subtype.ext hz
    subst W
    have hr : Tendsto (fun Z : RankCone κ => frobeniusRadius Z.val)
        (𝓝 coneZero) (𝓝 0) := by
      have hc : Continuous (fun Z : RankCone κ => frobeniusRadius Z.val) :=
        continuous_frobeniusRadius.comp continuous_subtype_val
      have he : frobeniusRadius (coneZero : RankCone κ).val = 0 := by
        simp [coneZero, frobeniusRadius, frobSq, frobInner]
      simpa only [ContinuousAt, he] using hc.continuousAt (x := coneZero)
    have hneg : Tendsto (fun Z : RankCone κ => -frobeniusRadius Z.val)
        (𝓝 coneZero) (𝓝 0) := by simpa using hr.neg
    change Tendsto (fun Z : RankCone κ => coneToPlane Z i) (𝓝 coneZero)
      (𝓝 (coneToPlane coneZero i))
    rw [coneToPlane_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg hr
      (fun Z => (abs_le.mp (abs_coneToPlane_le Z i)).1)
      (fun Z => (abs_le.mp (abs_coneToPlane_le Z i)).2)
  · exact ((continuous_apply i).comp
      (continuous_circleCoordinate.comp continuous_subtype_val)).continuousAt.div
      (continuous_frobeniusRadius.comp continuous_subtype_val).continuousAt
      (frobeniusRadius_ne_zero hz)

/-- Homogeneous extension of the projector section: eigenvalues are 0 and |v|.
No direction v/|v| is chosen, so this expression is continuous also at v=0. -/
def planeMatrix (v : CircleVector) : Mat 2 :=
  !![(planeRadius v + v 0)/2, v 1/2;
     v 1/2, (planeRadius v - v 0)/2]

theorem planeMatrix_symmetric (v : CircleVector) : (planeMatrix v)ᵀ = planeMatrix v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeMatrix]

theorem planeMatrix_rank (v : CircleVector) : (planeMatrix v).rank ≤ 1 := by
  apply rank_le_one_of_two_column_minors
  have h := planeRadius_sq v
  dsimp [planeSq] at h
  intro j k
  fin_cases j <;> fin_cases k <;> simp [planeMatrix] <;> nlinarith [h]

theorem planeMatrix_sq (v : CircleVector) :
    planeMatrix v * planeMatrix v = planeRadius v • planeMatrix v := by
  have h := planeRadius_sq v
  dsimp [planeSq] at h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [h]

theorem planeMatrix_frobSq (v : CircleVector) : frobSq (planeMatrix v) = planeSq v := by
  have h := planeRadius_sq v
  dsimp [planeSq] at h ⊢
  simp [frobSq, frobInner, planeMatrix, Fin.sum_univ_two]
  nlinarith [h]

def planeToCone (d : ℕ) (v : CircleVector) : RankCone (Fin (d+2)) :=
  ⟨padTwo d (planeMatrix v), padTwo_rank_le_one d (planeMatrix_rank v)⟩

theorem continuous_planeToCone (d : ℕ) : Continuous (planeToCone d) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => ?_) j) j
  · fin_cases i
    · exact (continuous_planeRadius.add (continuous_apply 0)).div_const 2
    · exact (continuous_apply 1).div_const 2
  · fin_cases i
    · exact (continuous_apply 1).div_const 2
    · exact (continuous_planeRadius.sub (continuous_apply 0)).div_const 2
  · exact continuous_const

@[simp] theorem planeToCone_zero (d : ℕ) : planeToCone d 0 = coneZero := by
  apply Subtype.ext
  ext i j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => ?_) j) j
  all_goals fin_cases i <;>
    simp [planeToCone, planeMatrix, planeRadius, planeSq, padTwo, coneZero] <;> rfl

theorem planeToCone_sq (d : ℕ) (v : CircleVector) :
    frobSq (planeToCone d v).val = planeSq v := by
  change frobSq (padTwo d (planeMatrix v)) = planeSq v
  rw [padTwo_frobSq, planeMatrix_frobSq]

theorem planeToCone_radius (d : ℕ) (v : CircleVector) :
    frobeniusRadius (planeToCone d v).val = planeRadius v := by
  simp [frobeniusRadius, planeToCone_sq, planeRadius]

theorem circleCoordinate_planeToCone (d : ℕ) (v : CircleVector) :
    circleCoordinate (planeToCone d v).val = planeRadius v • v := by
  have hg : rowGram (planeToCone d v).val = planeRadius v • planeMatrix v := by
    change rowGram (padTwo d (planeMatrix v)) = _
    rw [padTwo_rowGram, planeMatrix_symmetric, planeMatrix_sq]
  ext i
  fin_cases i <;> simp [circleCoordinate, hg, planeMatrix] <;> ring

/-- The retraction identity, including the origin. -/
theorem coneToPlane_planeToCone (d : ℕ) (v : CircleVector) :
    coneToPlane (planeToCone d v) = v := by
  by_cases hv : v = 0
  · subst v
    simp
  · have hr : planeRadius v ≠ 0 := fun h => hv ((planeRadius_eq_zero_iff v).mp h)
    ext i
    change circleCoordinate (planeToCone d v).val i /
      frobeniusRadius (planeToCone d v).val = v i
    rw [circleCoordinate_planeToCone, planeToCone_radius]
    change planeRadius v * v i / planeRadius v = v i
    field_simp [hr]

theorem planeToCone_injective (d : ℕ) : Function.Injective (planeToCone d) := by
  intro v w h
  have hh := congrArg coneToPlane h
  simpa only [coneToPlane_planeToCone] using hh

end GS.NonmanifoldObstruction
