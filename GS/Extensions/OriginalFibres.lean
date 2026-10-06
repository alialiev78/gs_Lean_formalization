module

public import GS.Extensions.OriginalCompact
public import GS.Extensions.TransportedProjection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Missing algebra and angle recovery in the ORIGINAL f/g fibre proof

The central result gives actual equality of f/g
fibres under explicit local analytic hypotheses: bounded angles, scalar sign
normalization, and injectivity of originalPsi on a set containing c ± z.
Those hypotheses are NOT claimed established uniformly on some K_eta here.
In particular no smoothness of the singular matrix family is assumed.
-/

noncomputable section
open Matrix
namespace GS.Extensions

 theorem middleFamily_fibres {q : ℕ} (A B A' B' : Mat q) (u v : CircleVector)
    (hu : OnCircle u) (hv : OnCircle v)
    (h : ∀ i j, middleBlock (A i j) (B i j) u =
      middleBlock (A' i j) (B' i j) v) :
    (A=B ∧ A'=B' ∧ A=A') ∨
      (u=v ∧ A=A' ∧ B=B') ∨ (u=-v ∧ A=B' ∧ B=A') := by
  have hs : ∀ i j, A i j+B i j=A' i j+B' i j :=
    fun i j => (middleBlock_eq_sum_and_difference _ _ _ _ u v (h i j)).1
  have hout : outer u (fun ij : Fin q × Fin q => A ij.1 ij.2-B ij.1 ij.2) =
      outer v (fun ij : Fin q × Fin q => A' ij.1 ij.2-B' ij.1 ij.2) := by
    ext r ij
    have he := (middleBlock_eq_sum_and_difference _ _ _ _ u v (h ij.1 ij.2)).2
    fin_cases r
    · have hh := congrFun (congrFun he 0) 0
      simpa [outer,T,mul_comm] using hh
    · have hh := congrFun (congrFun he 0) 1
      simpa [outer,T,mul_comm] using hh
  rcases (outer_fibres hu hv).mp hout with ⟨h₀,h₀'⟩ | ⟨huv,hd⟩ | ⟨huv,hd⟩
  · left
    have hab : A=B := by
      ext i j
      have hh := congrFun h₀ (i,j)
      change A i j-B i j=0 at hh
      linarith
    have hab' : A'=B' := by
      ext i j
      have hh := congrFun h₀' (i,j)
      change A' i j-B' i j=0 at hh
      linarith
    refine ⟨hab,hab',?_⟩
    ext i j
    have hh := hs i j
    rw [hab,hab'] at hh
    rw [hab,hab']
    linarith
  · right; left
    refine ⟨huv,?_,?_⟩ <;> ext i j
    all_goals
      have hh := congrFun hd (i,j)
      change A i j-B i j=A' i j-B' i j at hh
      linarith [hs i j]
  · right; right
    refine ⟨huv,?_,?_⟩ <;> ext i j
    all_goals
      have hh := congrFun hd (i,j)
      change A i j-B i j=-(A' i j-B' i j) at hh
      linarith [hs i j]

 theorem sandwich_trace (a b l r : ℝ) (u : CircleVector) :
    (rotation l * middleBlock a b u * rotation r) 0 0 +
      (rotation l * middleBlock a b u * rotation r) 1 1 =
        (a+b)*Real.cos (l+r) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  simp [rotation,middleBlock,T,Matrix.one_apply,Real.cos_add]
  ring

 theorem sandwich_skew_entry (a b l r : ℝ) (u : CircleVector) :
    (rotation l * middleBlock a b u * rotation r) 1 0 -
      (rotation l * middleBlock a b u * rotation r) 0 1 =
        (a+b)*Real.sin (l+r) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  simp [rotation,middleBlock,T,Matrix.one_apply,Real.sin_add]
  ring

 theorem scaled_trig_unique (s s' θ θ' : ℝ)
    (hprod : 0 < s*s')
    (hθ : θ ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2))
    (hθ' : θ' ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2))
    (hc : s*Real.cos θ=s'*Real.cos θ')
    (hs : s*Real.sin θ=s'*Real.sin θ') : θ=θ' := by
  have hnorm (a t : ℝ) :
      (a*Real.cos t)^2+(a*Real.sin t)^2=a^2 := by
    calc
      _ = a^2*(Real.sin t^2+Real.cos t^2) := by ring
      _ = a^2 := by rw [Real.sin_sq_add_cos_sq]; ring
  have he : s^2=s'^2 := by
    calc
      s^2 = (s*Real.cos θ)^2+(s*Real.sin θ)^2 := (hnorm s θ).symm
      _ = (s'*Real.cos θ')^2+(s'*Real.sin θ')^2 := by rw [hc,hs]
      _ = s'^2 := hnorm s' θ'
  have hfac : (s-s')*(s+s')=0 := by nlinarith [he]
  have heq : s=s' := by
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · have hh : s'=-s := by linarith
      rw [hh] at hprod
      nlinarith [sq_nonneg s]
  have hne : s ≠ 0 := by intro h; simp [h] at hprod
  have hsin : Real.sin θ=Real.sin θ' := by
    rw [← heq] at hs
    exact mul_left_cancel₀ hne hs
  exact Real.injOn_sin hθ hθ' hsin

 theorem positive_common_sign (s s' q : ℝ)
    (h : 0<s*q) (h' : 0<s'*q) : 0<s*s' := by
  rcases mul_pos_iff.mp h with ⟨hs,hq⟩ | ⟨hs,hq⟩ <;>
    rcases mul_pos_iff.mp h' with ⟨hs',hq'⟩ | ⟨hs',hq'⟩
  · exact mul_pos hs hs'
  · linarith
  · linarith
  · exact mul_pos_of_neg_of_neg hs hs'

/-- Recover the sum of angles from two scalar matrix invariants. This is an
alternative proof of the polar-factor step, not a new parameterization. It
requires no assertion that the original M_ij is symmetric or positive definite. -/
 theorem sandwich_angle_unique (a b a' b' l r l' r' q₀ : ℝ) (u v : CircleVector)
    (h : rotation l * middleBlock a b u * rotation r =
      rotation l' * middleBlock a' b' v * rotation r')
    (hp : 0<(a+b)*q₀) (hp' : 0<(a'+b')*q₀)
    (ht : l+r ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2))
    (ht' : l'+r' ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2)) : l+r=l'+r' := by
  apply scaled_trig_unique (a+b) (a'+b') (l+r) (l'+r')
    (positive_common_sign _ _ _ hp hp') ht ht'
  · have hh := congrArg (fun X : Mat 2 => X 0 0+X 1 1) h
    simpa only [sandwich_trace] using hh
  · have hh := congrArg (fun X : Mat 2 => X 1 0-X 0 1) h
    simpa only [sandwich_skew_entry] using hh

 theorem symmetric_coordinates_injective {q : ℕ} (c z c' w : Mat q)
    (hplus : c+z=c'+w) (hminus : c-z=c'-w) : c=c' ∧ z=w := by
  constructor <;> ext i j
  all_goals
    have hp := congrFun (congrFun hplus i) j
    have hm := congrFun (congrFun hminus i) j
    change c i j+z i j=c' i j+w i j at hp
    change c i j-z i j=c' i j-w i j at hm
    linarith

 theorem originalF_block_eq {q : ℕ} (Q₀ : Mat q)
    (ell r ell' r' : Fin q → ℝ) (c z c' w : Mat q) (u v : CircleVector)
    (h : originalF Q₀ (ell,r,c,z,u)=originalF Q₀ (ell',r',c',w,v)) (i j : Fin q) :
    rotation (ell i) * middleBlock (originalPsi Q₀ (c+z) i j)
      (originalPsi Q₀ (c-z) i j) u * rotation (r j) =
    rotation (ell' i) * middleBlock (originalPsi Q₀ (c'+w) i j)
      (originalPsi Q₀ (c'-w) i j) v * rotation (r' j) := by
  ext s t
  have he := congrFun (congrFun h (finProdFinEquiv (i,s))) (finProdFinEquiv (j,t))
  simpa only [originalF, Equiv.symm_apply_apply] using he

/-- Explicit local analytic input. No statement of equal fibres is hidden here.
The set V is a matrix-exponential chart domain supplied by a later analytic
lemma. The angles and signs are the ones in the original manuscript. -/
 def NormalizedOriginal {q : ℕ} (Q₀ : Mat q) (V : Set (Mat q))
    (p : OriginalParameters q) : Prop :=
  let (ell,r,c,z,u) := p
  OnCircle u ∧
    (∀ j : Fin q, j.val=0 → r j=0) ∧
    (∀ i j, ell i+r j ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2)) ∧
    (∀ i j, 0 < (originalPsi Q₀ (c+z) i j+originalPsi Q₀ (c-z) i j)*Q₀ i j) ∧
    c+z ∈ V ∧ c-z ∈ V

 theorem original_same_fibres_normalized {q : ℕ} (hq : 0<q) (Q₀ : Mat q)
    (V : Set (Mat q)) (hinj : Set.InjOn (originalPsi Q₀) V)
    (p p' : OriginalParameters q)
    (hp : NormalizedOriginal Q₀ V p) (hp' : NormalizedOriginal Q₀ V p') :
    originalF Q₀ p=originalF Q₀ p' ↔ originalG p=originalG p' := by
  rcases p with ⟨ell,r,c,z,u⟩
  rcases p' with ⟨ell',r',c',w,v⟩
  rcases hp with ⟨hu,hr₀,ht,hpos,hplus,hminus⟩
  rcases hp' with ⟨hv,hr₀',ht',hpos',hplus',hminus'⟩
  constructor
  · intro hF
    have hblocks := originalF_block_eq Q₀ ell r ell' r' c z c' w u v hF
    have hangles : ∀ i j, ell i+r j=ell' i+r' j := by
      intro i j
      exact sandwich_angle_unique _ _ _ _ _ _ _ _ (Q₀ i j) u v
        (hblocks i j) (hpos i j) (hpos' i j) (ht i j) (ht' i j)
    let j₀ : Fin q := ⟨0,hq⟩
    have hell : ell=ell' := by
      funext i
      have hh := hangles i j₀
      rw [hr₀ j₀ rfl,hr₀' j₀ rfl] at hh
      simpa only [add_zero] using hh
    have hright : r=r' := by
      funext j
      have hh := hangles j₀ j
      rw [hell] at hh
      exact add_left_cancel hh
    subst ell'
    subst r'
    have hm : ∀ i j,
        middleBlock (originalPsi Q₀ (c+z) i j) (originalPsi Q₀ (c-z) i j) u =
        middleBlock (originalPsi Q₀ (c'+w) i j) (originalPsi Q₀ (c'-w) i j) v := by
      intro i j
      exact lift_injective (rotation (ell i)) (rotation (r j))
        (rotation_orthogonal _) (rotation_orthogonal _) (hblocks i j)
    have hf := middleFamily_fibres (originalPsi Q₀ (c+z)) (originalPsi Q₀ (c-z))
      (originalPsi Q₀ (c'+w)) (originalPsi Q₀ (c'-w)) u v hu hv hm
    apply (originalG_fibres ell r ell r c z c' w u v hu hv).mpr
    rcases hf with ⟨hAB,hAB',hAA'⟩ | ⟨huv,hAA',hBB'⟩ | ⟨huv,hAB',hBA'⟩
    · have hBB' := hAB.symm.trans (hAA'.trans hAB')
      obtain ⟨hc,hz⟩ := symmetric_coordinates_injective c z c' w
        (hinj hplus hplus' hAA') (hinj hminus hminus' hBB')
      have hzz := hinj hplus hminus hAB
      have hz₀ : z=0 := by
        ext i j
        have hh := congrFun (congrFun hzz i) j
        change c i j+z i j=c i j-z i j at hh
        change z i j=0
        linarith
      exact ⟨rfl,rfl,hc,Or.inl ⟨hz₀,hz.symm.trans hz₀⟩⟩
    · obtain ⟨hc,hz⟩ := symmetric_coordinates_injective c z c' w
        (hinj hplus hplus' hAA') (hinj hminus hminus' hBB')
      exact ⟨rfl,rfl,hc,Or.inr (Or.inl ⟨huv,hz⟩)⟩
    · have h₁ := hinj hplus hminus' hAB'
      have h₂ := hinj hminus hplus' hBA'
      obtain ⟨hc,hz⟩ := symmetric_coordinates_injective c z c' (-w)
        (by simpa only [sub_eq_add_neg] using h₁)
        (by simpa only [sub_neg_eq_add] using h₂)
      exact ⟨rfl,rfl,hc,Or.inr (Or.inr ⟨huv,hz⟩)⟩
  · exact originalF_eq_of_originalG_eq Q₀ ell r ell' r' c z c' w u v hu hv

/-- Compact-image equivalence with elementary local conditions, instead of a
same-fibres hypothesis. Still requires a uniform analytic choice of V and eta. -/
 theorem original_compact_homeomorphism_of_normalized {q : ℕ} (hq : 0<q)
    (Q₀ : Mat q) (η : ℝ) (V : Set (Mat q))
    (hinj : Set.InjOn (originalPsi Q₀) V)
    (hnorm : ∀ p ∈ originalK q η, NormalizedOriginal Q₀ V p) :
    ∃ h : Set.range (fun p : ↥(originalK q η) => originalF Q₀ p.val) ≃ₜ
        Set.range (fun p : ↥(originalK q η) => originalG p.val),
      ∀ p : ↥(originalK q η),
        h ⟨originalF Q₀ p.val, ⟨p,rfl⟩⟩ = ⟨originalG p.val, ⟨p,rfl⟩⟩ := by
  apply original_compact_homeomorphism Q₀ η
  intro p hp p' hp'
  exact (original_same_fibres_normalized hq Q₀ V hinj p p'
    (hnorm p hp) (hnorm p' hp')).mp

end GS.Extensions
