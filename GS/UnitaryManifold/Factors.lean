module

public import GS.UnitaryManifold.CayleyCharts
public import GS.UnitaryManifold.OrbitTopology
public import GS.Unitary.Permutations

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Two-factor Cayley reconstruction and its actual matrix orbit. -/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.UnitaryGeometry
open scoped Topology
namespace GS.UnitaryManifold
variable {n : ℕ} {block block₁ block₂ : Fin n → ℕ}

abbrev PairModel (block₁ block₂ : Fin n → ℕ) := Model block₂ × Model block₁

def factorSource (g : FactorGroup block₁ block₂) : Set (FactorGroup block₁ block₂) :=
  chartSource g.1 ×ˢ chartSource g.2

def factorCoordinates (g h : FactorGroup block₁ block₂) : PairModel block₁ block₂ :=
  (chartMap g.1 h.1.val, chartMap g.2 h.2.val)

theorem factorSource_open (g : FactorGroup block₁ block₂) : IsOpen (factorSource g) :=
  (chartSource_open g.1).prod (chartSource_open g.2)

@[simp] theorem self_mem_factorSource (g : FactorGroup block₁ block₂) :
    g ∈ factorSource g := ⟨base_mem_chartSource g.1, base_mem_chartSource g.2⟩

/-- This uses the original factor group and the original matrix topology. -/
def factorLift (g : FactorGroup block₁ block₂) (x : PairModel block₁ block₂) :
    FactorGroup block₁ block₂ :=
  (blockChartInverse g.1 x.1, blockChartInverse g.2 x.2)

@[simp] theorem factorLift_left_val (g : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) :
    (factorLift g x).1.val = chartInv g.1 x.1 :=
  blockChartInverse_val_everywhere g.1 x.1

@[simp] theorem factorLift_right_val (g : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) :
    (factorLift g x).2.val = chartInv g.2 x.2 :=
  blockChartInverse_val_everywhere g.2 x.2

theorem continuous_factorLift (g : FactorGroup block₁ block₂) :
    Continuous (factorLift g) :=
  ((continuous_blockChartInverse g.1).comp continuous_fst).prodMk
    ((continuous_blockChartInverse g.2).comp continuous_snd)

@[simp] theorem factorLift_zero (g : FactorGroup block₁ block₂) :
    factorLift g 0 = g := by
  apply Prod.ext <;> apply Subtype.ext <;> simp

@[simp] theorem factorCoordinates_factorLift (g : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) :
    factorCoordinates g (factorLift g x) = x := by
  apply Prod.ext
  · change chartMap g.1 (factorLift g x).1.val = x.1
    rw [factorLift_left_val]
    exact chartMap_chartInv g.1 x.1 (admissible_model x.1)
  · change chartMap g.2 (factorLift g x).2.val = x.2
    rw [factorLift_right_val]
    exact chartMap_chartInv g.2 x.2 (admissible_model x.2)

theorem factorLift_factorCoordinates (g h : FactorGroup block₁ block₂)
    (hh : h ∈ factorSource g) : factorLift g (factorCoordinates g h) = h := by
  apply Prod.ext
  · apply Subtype.ext
    rw [factorLift_left_val]
    exact chartInv_chartMap g.1 h.1 hh.1
  · apply Subtype.ext
    rw [factorLift_right_val]
    exact chartInv_chartMap g.2 h.2 hh.2


/-- The original matrix formula with the group inverse in the right factor. -/
def orbitParam (g : FactorGroup block₁ block₂) (P : CMat n)
    (x : PairModel block₁ block₂) : CMat n :=
  chartInv g.1 x.1 * P * (chartInv g.2 x.2)ᴴ

theorem factorLift_action (g : FactorGroup block₁ block₂) (P : CMat n)
    (x : PairModel block₁ block₂) :
    factorLift g x • P = orbitParam g P x := by
  simp only [action_apply, factorLift_left_val, factorLift_right_val, orbitParam]

theorem orbitParam_smooth (g : FactorGroup block₁ block₂) (P : CMat n) :
    ContDiff ℝ ⊤ (orbitParam g P) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact smooth_mul_at
    (smooth_mul_at ((chartInv_smooth g.1).contDiffAt.comp x contDiffAt_fst)
      contDiffAt_const)
    (smooth_conjTranspose_at ((chartInv_smooth g.2).contDiffAt.comp x contDiffAt_snd))

def orbitInverse (σ : Equiv.Perm (Fin n)) (g : FactorGroup block₁ block₂)
    (x : PairModel block₁ block₂) : MatrixOrbit block₁ block₂ (cPermMatrix σ) :=
  orbitMapToOrbit block₁ block₂ (cPermMatrix σ) (factorLift g x)

@[simp] theorem orbitInverse_val (σ : Equiv.Perm (Fin n))
    (g : FactorGroup block₁ block₂) (x : PairModel block₁ block₂) :
    (orbitInverse σ g x).val = orbitParam g (cPermMatrix σ) x :=
  factorLift_action g (cPermMatrix σ) x

end GS.UnitaryManifold
