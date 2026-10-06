module

public import GS.UnitaryLocalModel.MiddleFibres

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Fibres after an injective chart of the dephased unitary slice

These statements certify the nonlinear change from two middle matrices to a
centre and a difference. The local version requires injectivity only on the
chart domain and membership of all four arguments in that domain. Neither
version assumes or asserts the construction of the dephased slice chart.
-/
noncomputable section
open Matrix
namespace GS.UnitaryLocalModel
open GS.UnitaryGeometry

def chartMiddle {d : ℕ} {κ : Type*} (ψ : (Fin d → ℝ) → (κ → ℂ))
    (c z : Fin d → ℝ) (u : AxisVector) : κ → CMat 2 :=
  fun j => middleBlock (ψ (c+z) j) (ψ (c-z) j) u

private theorem centre_difference_unique {d : ℕ} (c z c' z' : Fin d → ℝ)
    (hplus : c+z=c'+z') (hminus : c-z=c'-z') : c=c' ∧ z=z' := by
  constructor <;> funext j
  · have hp := congrFun hplus j
    have hm := congrFun hminus j
    simp only [Pi.add_apply,Pi.sub_apply] at hp hm
    linarith
  · have hp := congrFun hplus j
    have hm := congrFun hminus j
    simp only [Pi.add_apply,Pi.sub_apply] at hp hm
    linarith

private theorem difference_zero {d : ℕ} (c z : Fin d → ℝ)
    (he : c+z=c-z) : z=0 := by
  funext j
  have hh := congrFun he j
  simp only [Pi.add_apply,Pi.sub_apply] at hh
  change z j = 0
  linarith

/-- Exact fibres of the nonlinear matrix parametrization, with the collapsed
zero sphere retained. No differentiability assumption is used in this lemma. -/
theorem chartMiddle_fibres_on {d : ℕ} {κ : Type*}
    (ψ : (Fin d → ℝ) → (κ → ℂ)) (U : Set (Fin d → ℝ)) (hψ : Set.InjOn ψ U)
    (c z c' z' : Fin d → ℝ) {u v : AxisVector}
    (hcp : c+z ∈ U) (hcm : c-z ∈ U)
    (hcp' : c'+z' ∈ U) (hcm' : c'-z' ∈ U)
    (hu : OnSphere u) (hv : OnSphere v) :
    chartMiddle ψ c z u = chartMiddle ψ c' z' v ↔
      c=c' ∧ sphereOuter u z = sphereOuter v z' := by
  constructor
  · intro h
    have he : ∀ j, middleBlock (ψ (c+z) j) (ψ (c-z) j) u =
        middleBlock (ψ (c'+z') j) (ψ (c'-z') j) v := fun j => congrFun h j
    rcases (middleBlock_family_fibres _ _ _ _ hu hv).mp he with hz | hp | hn
    · obtain ⟨hzz,hzz',hcc⟩ := hz
      have hz0 := difference_zero c z (hψ hcp hcm hzz)
      have hz'0 := difference_zero c' z' (hψ hcp' hcm' hzz')
      subst z
      subst z'
      have hc : c=c' := by simpa using hψ hcp hcp' hcc
      exact ⟨hc, sphereOuter_zero_fibre u v⟩
    · obtain ⟨huv,hplus,hminus⟩ := hp
      obtain ⟨hc,hz⟩ := centre_difference_unique c z c' z'
        (hψ hcp hcp' hplus) (hψ hcm hcm' hminus)
      subst c'
      subst z'
      subst v
      exact ⟨rfl,rfl⟩
    · obtain ⟨huv,hplus,hminus⟩ := hn
      have hp : c+z=c'+(-z') := by
        simpa only [sub_eq_add_neg] using hψ hcp hcm' hplus
      have hm : c-z=c'-(-z') := by simpa using hψ hcm hcp' hminus
      obtain ⟨hc,hz⟩ := centre_difference_unique c z c' (-z') hp hm
      rw [hc,huv,hz]
      exact ⟨rfl,sphereOuter_simultaneous_neg v z'⟩
  · rintro ⟨rfl,h⟩
    rcases (sphereOuter_fibres hu hv).mp h with hz | hp | hn
    · obtain ⟨rfl,rfl⟩ := hz
      funext j
      simp [chartMiddle,middleBlock_equal]
    · obtain ⟨rfl,rfl⟩ := hp
      rfl
    · obtain ⟨rfl,rfl⟩ := hn
      funext j
      simp only [chartMiddle,← sub_eq_add_neg,sub_neg_eq_add]
      exact middleBlock_simultaneous_swap _ _ _

/-- The unrestricted version is the special case of an injective map on the
entire coordinate space. For a local chart use `chartMiddle_fibres_on`. -/
theorem chartMiddle_fibres {d : ℕ} {κ : Type*}
    (ψ : (Fin d → ℝ) → (κ → ℂ)) (hψ : Function.Injective ψ)
    (c z c' z' : Fin d → ℝ) {u v : AxisVector}
    (hu : OnSphere u) (hv : OnSphere v) :
    chartMiddle ψ c z u = chartMiddle ψ c' z' v ↔
      c=c' ∧ sphereOuter u z = sphereOuter v z' := by
  exact chartMiddle_fibres_on ψ Set.univ (fun _ _ _ _ h => hψ h)
    c z c' z' (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) hu hv

end GS.UnitaryLocalModel
