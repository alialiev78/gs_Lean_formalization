module

public import GS.UnitaryLocalModel.OuterFibres

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact fibres of the complex middle blocks

The coefficients are complex, but the common Pauli axis is real. Therefore the
only nonzero ambiguity is simultaneous interchange of the two middle matrices
and reversal of the sphere axis. The zero difference collapses the whole sphere.
-/
noncomputable section
open Matrix
namespace GS.UnitaryLocalModel
open GS.UnitaryGeometry

def realify {κ : Type*} (z : κ → ℂ) : κ × Fin 2 → ℝ :=
  fun p => if p.2 = 0 then (z p.1).re else (z p.1).im

theorem realify_injective {κ : Type*} : Function.Injective (@realify κ) := by
  intro z w h
  funext j
  apply Complex.ext
  · simpa [realify] using congrFun h (j,0)
  · simpa [realify] using congrFun h (j,1)

@[simp] theorem realify_zero {κ : Type*} : realify (0 : κ → ℂ) = 0 := by
  funext p
  simp [realify]

@[simp] theorem realify_neg {κ : Type*} (z : κ → ℂ) :
    realify (-z) = -realify z := by
  funext p
  by_cases h : p.2 = 0 <;> simp [realify,h]

def complexOuter {κ : Type*} (u : AxisVector) (z : κ → ℂ) : Matrix (Fin 3) κ ℂ :=
  fun i j => (u i : ℂ) * z j

theorem complexOuter_eq_iff {κ : Type*} (u v : AxisVector) (z w : κ → ℂ) :
    complexOuter u z = complexOuter v w ↔
      sphereOuter u (realify z) = sphereOuter v (realify w) := by
  constructor
  · intro h
    ext i p
    have hh := congrFun (congrFun h i) p.1
    by_cases hp : p.2 = 0
    · simpa [sphereOuter,realify,hp,complexOuter] using congrArg Complex.re hh
    · simpa [sphereOuter,realify,hp,complexOuter] using congrArg Complex.im hh
  · intro h
    ext i j
    apply Complex.ext
    · have hh := congrFun (congrFun h i) (j,0)
      simpa [sphereOuter,realify,complexOuter] using hh
    · have hh := congrFun (congrFun h i) (j,1)
      simpa [sphereOuter,realify,complexOuter] using hh

theorem complexOuter_fibres {κ : Type*} {u v : AxisVector} {z w : κ → ℂ}
    (hu : OnSphere u) (hv : OnSphere v) :
    complexOuter u z = complexOuter v w ↔
      (z = 0 ∧ w = 0) ∨ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w) := by
  rw [complexOuter_eq_iff, sphereOuter_fibres hu hv]
  have hz : realify z = 0 ↔ z = 0 := by
    rw [← realify_zero, realify_injective.eq_iff]
  have hw : realify w = 0 ↔ w = 0 := by
    rw [← realify_zero, realify_injective.eq_iff]
  have hzw : realify z = realify w ↔ z = w := realify_injective.eq_iff
  have hn : realify z = -realify w ↔ z = -w := by
    rw [← realify_neg, realify_injective.eq_iff]
  rw [hz,hw,hzw,hn]

def axisCoefficient (H : CMat 2) : Fin 3 → ℂ :=
  ![H 0 0 - H 1 1, H 0 1 + H 1 0, Complex.I * (H 0 1 - H 1 0)]

theorem middleBlock_trace (a b : ℂ) (u : AxisVector) :
    Matrix.trace (middleBlock a b u) = a+b := by
  simp [Matrix.trace,Fin.sum_univ_two,middleBlock,pauli]
  ring

theorem middleBlock_axisCoefficient (a b : ℂ) (u : AxisVector) :
    axisCoefficient (middleBlock a b u) = fun i => (u i : ℂ) * (a-b) := by
  funext i
  fin_cases i <;> simp [axisCoefficient,middleBlock,pauli] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem middleBlock_family_fibres {κ : Type*} (a b c d : κ → ℂ)
    {u v : AxisVector} (hu : OnSphere u) (hv : OnSphere v) :
    (∀ j, middleBlock (a j) (b j) u = middleBlock (c j) (d j) v) ↔
      (a = b ∧ c = d ∧ a = c) ∨
      (u = v ∧ a = c ∧ b = d) ∨ (u = -v ∧ a = d ∧ b = c) := by
  constructor
  · intro h
    have hsum (j : κ) : a j + b j = c j + d j := by
      simpa only [middleBlock_trace] using congrArg Matrix.trace (h j)
    have ho : complexOuter u (a-b) = complexOuter v (c-d) := by
      ext i j
      have hh := congrFun (congrArg axisCoefficient (h j)) i
      simpa only [middleBlock_axisCoefficient,complexOuter,Pi.sub_apply] using hh
    rcases (complexOuter_fibres hu hv).mp ho with hz | hp | hn
    · obtain ⟨hab,hcd⟩ := hz
      have hab' : a = b := sub_eq_zero.mp hab
      have hcd' : c = d := sub_eq_zero.mp hcd
      refine Or.inl ⟨hab',hcd',?_⟩
      funext j
      have hs := hsum j
      rw [hab',hcd'] at hs
      have hh : b j = d j := by linear_combination (1/2 : ℂ) * hs
      simpa [hab',hcd'] using hh
    · obtain ⟨huv,hdiff⟩ := hp
      have ha : a = c := by
        funext j
        have hs := hsum j
        have hd : a j - b j = c j - d j := congrFun hdiff j
        linear_combination (1/2 : ℂ) * hs + (1/2 : ℂ) * hd
      have hb : b = d := by
        funext j
        have hs := hsum j
        rw [ha] at hs
        exact add_left_cancel hs
      exact Or.inr (Or.inl ⟨huv,ha,hb⟩)
    · obtain ⟨huv,hdiff⟩ := hn
      have ha : a = d := by
        funext j
        have hs := hsum j
        have hd : a j - b j = -(c j - d j) := congrFun hdiff j
        linear_combination (1/2 : ℂ) * hs + (1/2 : ℂ) * hd
      have hb : b = c := by
        funext j
        have hs := hsum j
        rw [ha] at hs
        linear_combination hs
      exact Or.inr (Or.inr ⟨huv,ha,hb⟩)
  · rintro (⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩)
    · intro j
      rw [middleBlock_equal,middleBlock_equal]
    · intro j
      rfl
    · intro j
      exact middleBlock_simultaneous_swap _ _ _

end GS.UnitaryLocalModel
