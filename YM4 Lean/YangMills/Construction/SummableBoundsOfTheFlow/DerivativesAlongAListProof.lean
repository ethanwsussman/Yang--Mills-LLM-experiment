import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongAList
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.IteratedDerivative
variable {E E' W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup W] [NormedSpace ℝ W]
theorem derivAlong_congr_eventually (f g : E → W) (x : E) (l : List E) (hfg : f =ᶠ[𝓝 x] g) :
    derivAlong f l =ᶠ[𝓝 x] derivAlong g l := by
  induction l with
  | nil => exact hfg
  | cons v l ih =>
    have := ih.fderiv (𝕜 := ℝ)
    filter_upwards [ih.eventuallyEq_nhds, this] with y _ hy
    simp only [derivAlong]
    rw [hy]
theorem derivAlong_append (f : E → W) (l l' : List E) :
    derivAlong f (l ++ l') = derivAlong (derivAlong f l') l := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext x
    simp only [List.cons_append, derivAlong, ih]
theorem contDiffAt_derivAlong (f : E → W) (x : E) (n : ℕ) (l : List E)
    (hf : ContDiffAt ℝ ((n + l.length : ℕ) : WithTop ℕ∞) f x) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (derivAlong f l) x := by
  induction l generalizing n with
  | nil => simpa [derivAlong] using hf
  | cons v l ih =>
    have h1 : ContDiffAt ℝ ((n + 1 + l.length : ℕ) : WithTop ℕ∞) f x := by
      have : n + 1 + l.length = n + (v :: l).length := by simp; ring
      rw [this]; exact hf
    have h2 := ih (n + 1) h1
    have h3 : ContDiffAt ℝ (n : WithTop ℕ∞) (fderiv ℝ (derivAlong f l)) x :=
      h2.fderiv_right (by norm_cast)
    exact h3.clm_apply contDiffAt_const
theorem contDiffAt_eventually_near (f : E → W) (x : E) (n : ℕ) (hf : ContDiffAt ℝ (n : WithTop ℕ∞) f x) :
    ∀ᶠ y in 𝓝 x, ContDiffAt ℝ (n : WithTop ℕ∞) f y :=
  hf.eventually (by simp)
theorem iteratedFDeriv_eventuallyEq_derivAlong (f : E → W) (x : E) (n : ℕ) (v : Fin n → E)
    (hf : ContDiffAt ℝ (n : WithTop ℕ∞) f x) :
    (fun y => iteratedFDeriv ℝ n f y v) =ᶠ[𝓝 x] derivAlong f (List.ofFn v) := by
  induction n generalizing x with
  | zero =>
    refine Filter.Eventually.of_forall fun y => ?_
    simp [derivAlong]
  | succ n ih =>
    have hev := contDiffAt_eventually_near f x (n + 1) hf
    filter_upwards [hev.eventually_nhds] with y hy
    have hy0 : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f y := hy.self_of_nhds
    have hn : ContDiffAt ℝ (n : WithTop ℕ∞) f y := hy0.of_le (by norm_cast; omega)
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) y :=
      hy0.differentiableAt_iteratedFDeriv (by norm_cast; omega)
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ]
    simp only [derivAlong]
    have e := (ih y (Fin.tail v) hn)
    have hfe := e.fderiv_eq (𝕜 := ℝ)
    have : derivAlong f (List.ofFn fun i => v i.succ) = derivAlong f (List.ofFn (Fin.tail v)) := rfl
    rw [this, ← hfe]
    have hap := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) W (Fin.tail v)).hasFDerivAt
      (x := iteratedFDeriv ℝ n f y)).comp y hd.hasFDerivAt
    have hderiv : fderiv ℝ (fun y => iteratedFDeriv ℝ n f y (Fin.tail v)) y = _ := hap.fderiv
    rw [show (fun y => iteratedFDeriv ℝ n f y (Fin.tail v)) =
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) W (Fin.tail v)) ∘ iteratedFDeriv ℝ n f from rfl] at *
    rw [hderiv]
    rfl
theorem fderiv_apply_clm_const {G : E → E' →L[ℝ] W} {y v : E} (w : E') (hG : DifferentiableAt ℝ G y) :
    fderiv ℝ (fun x => G x w) y v = fderiv ℝ G y v w := by
  have := (hG.hasFDerivAt.clm_apply (hasFDerivAt_const w y)).fderiv
  rw [this]
  simp
theorem differentiableAt_derivAlong (f : E → W) (y : E) (l : List E)
    (hf : ContDiffAt ℝ ((1 + l.length : ℕ) : WithTop ℕ∞) f y) : DifferentiableAt ℝ (derivAlong f l) y :=
  (contDiffAt_derivAlong f y 1 l hf).differentiableAt (by simp)
theorem derivAlong_perm_eventually (f : E → W) (x : E) (l l' : List E) (hperm : l.Perm l')
    (hf : ContDiffAt ℝ (l.length : WithTop ℕ∞) f x) :
    derivAlong f l =ᶠ[𝓝 x] derivAlong f l' := by
  induction hperm generalizing x with
  | nil => exact Filter.EventuallyEq.rfl
  | @cons a l₁ l₂ hperm ih =>
    filter_upwards [(contDiffAt_eventually_near f x _ hf).eventually_nhds] with y hy
    have hy1 : ContDiffAt ℝ (l₁.length : WithTop ℕ∞) f y :=
      hy.self_of_nhds.of_le (by norm_cast; simp)
    have e := ih y hy1
    simp only [derivAlong]
    rw [e.fderiv_eq]
  | @swap a b l =>
    filter_upwards [contDiffAt_eventually_near f x _ hf] with y hy
    have hF : ContDiffAt ℝ (2 : WithTop ℕ∞) (derivAlong f l) y := by
      have : ContDiffAt ℝ ((2 + l.length : ℕ) : WithTop ℕ∞) f y := by
        have e : 2 + l.length = (b :: a :: l).length := by simp; ring
        rw [e]; exact hy
      simpa using contDiffAt_derivAlong f y 2 l this
    have hd : DifferentiableAt ℝ (fderiv ℝ (derivAlong f l)) y :=
      (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
    have hs := (hF.isSymmSndFDerivAt (by simp)) a b
    simp only [derivAlong]
    rw [fderiv_apply_clm_const _ hd, fderiv_apply_clm_const _ hd]
    exact hs.symm
  | @trans l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ =>
    have e₁ := ih₁ x hf
    have e₂ := ih₂ x (by rw [← h₁.length_eq]; exact hf)
    exact e₁.trans e₂
theorem derivAlong_add_eventually (f g : E → W) (x : E) (l : List E)
    (hf : ContDiffAt ℝ (l.length : WithTop ℕ∞) f x) (hg : ContDiffAt ℝ (l.length : WithTop ℕ∞) g x) :
    derivAlong (fun y => f y + g y) l =ᶠ[𝓝 x] fun y => derivAlong f l y + derivAlong g l y := by
  induction l generalizing x with
  | nil => exact Filter.EventuallyEq.rfl
  | cons v l ih =>
    filter_upwards [(contDiffAt_eventually_near f x _ hf).eventually_nhds,
      (contDiffAt_eventually_near g x _ hg).eventually_nhds] with y hfy hgy
    have hf0 := hfy.self_of_nhds
    have hg0 := hgy.self_of_nhds
    have hf1 : ContDiffAt ℝ (l.length : WithTop ℕ∞) f y := hf0.of_le (by norm_cast; simp)
    have hg1 : ContDiffAt ℝ (l.length : WithTop ℕ∞) g y := hg0.of_le (by norm_cast; simp)
    have e := ih y hf1 hg1
    have d1 := differentiableAt_derivAlong f y l (by rw [add_comm]; simpa using hf0)
    have d2 := differentiableAt_derivAlong g y l (by rw [add_comm]; simpa using hg0)
    simp only [derivAlong]
    rw [e.fderiv_eq, fderiv_fun_add d1 d2]
    rfl
theorem derivAlong_smul_eventually (c : ℝ) (f : E → W) (x : E) (l : List E)
    (hf : ContDiffAt ℝ (l.length : WithTop ℕ∞) f x) :
    derivAlong (fun y => c • f y) l =ᶠ[𝓝 x] fun y => c • derivAlong f l y := by
  induction l generalizing x with
  | nil => exact Filter.EventuallyEq.rfl
  | cons v l ih =>
    filter_upwards [(contDiffAt_eventually_near f x _ hf).eventually_nhds] with y hfy
    have hf0 := hfy.self_of_nhds
    have hf1 : ContDiffAt ℝ (l.length : WithTop ℕ∞) f y := hf0.of_le (by norm_cast; simp)
    have e := ih y hf1
    have d1 := differentiableAt_derivAlong f y l (by rw [add_comm]; simpa using hf0)
    simp only [derivAlong]
    rw [e.fderiv_eq, fderiv_fun_const_smul d1]
    rfl
theorem derivAlong_smul_slot (f : E → W) (x : E) (l l' : List E) (c : ℝ) (v : E)
    (hf : ContDiffAt ℝ ((l ++ v :: l').length : WithTop ℕ∞) f x) :
    derivAlong f (l ++ (c • v) :: l') x = c • derivAlong f (l ++ v :: l') x := by
  have hlen : (l ++ (c • v) :: l').length = (l ++ v :: l').length := by simp
  rw [(derivAlong_perm_eventually f x _ _ (List.perm_middle (a := c • v) (l₁ := l) (l₂ := l'))
      (by rw [hlen]; exact hf)).self_of_nhds,
    (derivAlong_perm_eventually f x _ _ (List.perm_middle (a := v) (l₁ := l) (l₂ := l')) hf).self_of_nhds]
  simp only [derivAlong, map_smul]
theorem derivAlong_add_slot (f : E → W) (x : E) (l l' : List E) (v v' : E)
    (hf : ContDiffAt ℝ ((l ++ v :: l').length : WithTop ℕ∞) f x) :
    derivAlong f (l ++ (v + v') :: l') x = derivAlong f (l ++ v :: l') x + derivAlong f (l ++ v' :: l') x := by
  have h1 : (l ++ (v + v') :: l').length = (l ++ v :: l').length := by simp
  have h2 : (l ++ v' :: l').length = (l ++ v :: l').length := by simp
  rw [(derivAlong_perm_eventually f x _ _ (List.perm_middle (a := v + v') (l₁ := l) (l₂ := l'))
      (by rw [h1]; exact hf)).self_of_nhds,
    (derivAlong_perm_eventually f x _ _ (List.perm_middle (a := v) (l₁ := l) (l₂ := l')) hf).self_of_nhds,
    (derivAlong_perm_eventually f x _ _ (List.perm_middle (a := v') (l₁ := l) (l₂ := l'))
      (by rw [h2]; exact hf)).self_of_nhds]
  simp only [derivAlong, map_add]
theorem derivAlong_comp_affine_eventually (f : E → W) (A : E' →L[ℝ] E) (x₀ : E) (t : E') (l : List E')
    (hf : ContDiffAt ℝ (l.length : WithTop ℕ∞) f (x₀ + A t)) :
    derivAlong (fun s => f (x₀ + A s)) l =ᶠ[𝓝 t] fun s => derivAlong f (l.map A) (x₀ + A s) := by
  have hc : Continuous fun s : E' => x₀ + A s := by fun_prop
  induction l generalizing t with
  | nil => exact Filter.EventuallyEq.rfl
  | cons v l ih =>
    have hev := hc.continuousAt.eventually (contDiffAt_eventually_near f _ _ hf)
    filter_upwards [hev.eventually_nhds] with s hs
    have h0 := hs.self_of_nhds
    have h1 : ContDiffAt ℝ (l.length : WithTop ℕ∞) f (x₀ + A s) := h0.of_le (by norm_cast; simp)
    have e := ih s h1
    have d : DifferentiableAt ℝ (derivAlong f (l.map A)) (x₀ + A s) :=
      differentiableAt_derivAlong f _ _ (by rw [List.length_map, add_comm]; simpa using h0)
    have ha : HasFDerivAt (fun t : E' => x₀ + A t) A s := A.hasFDerivAt.const_add x₀
    have := (d.hasFDerivAt.comp s ha).fderiv
    simp only [derivAlong, List.map_cons]
    rw [e.fderiv_eq]
    change fderiv ℝ ((derivAlong f (l.map A)) ∘ fun t : E' => x₀ + A t) s v = _
    rw [this]
    rfl
theorem derivAlongRulesHold_proof : DerivAlongRulesHold := by
  refine ⟨fun E W _ _ _ _ => ⟨derivAlong_congr_eventually, derivAlong_append, contDiffAt_derivAlong,
    ?_, ?_, ?_, ?_, derivAlong_smul_slot, derivAlong_add_slot⟩, ?_⟩
  · intro f x n v hf
    exact (iteratedFDeriv_eventuallyEq_derivAlong f x n v hf).self_of_nhds
  · intro f x l l' hperm hf
    exact (derivAlong_perm_eventually f x l l' hperm hf).self_of_nhds
  · intro f g x l hf hg
    exact (derivAlong_add_eventually f g x l hf hg).self_of_nhds
  · intro c f x l hf
    exact (derivAlong_smul_eventually c f x l hf).self_of_nhds
  · intro E E' W _ _ _ _ _ _ f A x₀ t l hf
    exact (derivAlong_comp_affine_eventually f A x₀ t l hf).self_of_nhds
end YangMills.Construction.IteratedDerivative
end
