import YangMills.Construction.ColdChainAtEveryLevel.MixedDerivativesOfAHolomorphicFunction
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace YangMills.Construction.Analytic
variable {k : ℕ}
def complexPartialDeriv : List (Fin k) → ((Fin k → ℂ) → ℂ) → (Fin k → ℂ) → ℂ
  | [], g => g
  | i :: ls, g => fun ζ => fderiv ℂ (complexPartialDeriv ls g) ζ (Pi.single i 1)
def realPartialDeriv : List (Fin k) → ((Fin k → ℝ) → ℝ) → (Fin k → ℝ) → ℝ
  | [], h => h
  | i :: ls, h => fun x => deriv (fun τ : ℝ => realPartialDeriv ls h (x + τ • Pi.single i 1)) 0
def complexify (x : Fin k → ℝ) : Fin k → ℂ := fun l => (x l : ℂ)
theorem sum_norm_add_smul_single_le (ζ : Fin k → ℂ) (i : Fin k) (τ : ℂ) :
    ∑ l, ‖(ζ + τ • (Pi.single i 1 : Fin k → ℂ)) l‖ ≤ ∑ l, ‖ζ l‖ + ‖τ‖ := by
  classical
  have h1 : ∀ l, ‖(ζ + τ • (Pi.single i 1 : Fin k → ℂ)) l‖ ≤ ‖ζ l‖ + (if l = i then ‖τ‖ else 0) := by
    intro l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    refine (norm_add_le _ _).trans ?_
    split_ifs <;> simp
  refine (Finset.sum_le_sum fun l _ => h1 l).trans ?_
  rw [Finset.sum_add_distrib]
  simp
theorem isOpen_sum_norm_lt (r : ℝ) : IsOpen {ζ : Fin k → ℂ | ∑ l, ‖ζ l‖ < r} :=
  isOpen_lt (by fun_prop) continuous_const
theorem complexPartialDeriv_bound (g : (Fin k → ℂ) → ℂ) {r M ρ : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M)
    (han : ∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r → AnalyticAt ℂ g ζ)
    (hb : ∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r → ‖g ζ‖ ≤ M) (ls : List (Fin k)) :
    ∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r - ls.length * ρ →
      AnalyticAt ℂ (complexPartialDeriv ls g) ζ ∧ ‖complexPartialDeriv ls g ζ‖ ≤ M / ρ ^ ls.length := by
  induction ls with
  | nil =>
    intro ζ hζ
    simp only [List.length_nil, Nat.cast_zero, zero_mul, sub_zero] at hζ
    exact ⟨han ζ hζ, by simpa [complexPartialDeriv] using hb ζ hζ⟩
  | cons i ls ih =>
    intro ζ hζ
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hζ
    set G := complexPartialDeriv ls g with hG
    have hsmall : ∑ l, ‖ζ l‖ < r - ls.length * ρ := by nlinarith
    have hGa := (ih ζ hsmall).1
    refine ⟨?_, ?_⟩
    · exact ((ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1 : Fin k → ℂ)).analyticAt _).comp hGa.fderiv
    · set f : ℂ → ℂ := fun τ => G (ζ + τ • Pi.single i 1) with hf
      have hin : ∀ τ : ℂ, ‖τ‖ ≤ ρ → ∑ l, ‖(ζ + τ • (Pi.single i 1 : Fin k → ℂ)) l‖ < r - ls.length * ρ := by
        intro τ hτ
        have := sum_norm_add_smul_single_le ζ i τ
        nlinarith
      have hline : ∀ τ : ℂ, HasDerivAt (fun τ : ℂ => ζ + τ • (Pi.single i 1 : Fin k → ℂ))
          (Pi.single i 1) τ := by
        intro τ
        have := ((hasDerivAt_id τ).smul_const (Pi.single i 1 : Fin k → ℂ)).const_add ζ
        simpa using this
      have hdiff : DifferentiableOn ℂ f (Metric.closedBall 0 ρ) := by
        intro τ hτ
        have hτ' : ‖τ‖ ≤ ρ := by simpa using hτ
        have h1 := (ih _ (hin τ hτ')).1.differentiableAt
        exact ((h1.hasFDerivAt.comp_hasDerivAt τ (hline τ)).differentiableAt).differentiableWithinAt
      have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 0) hρ (hdiff.diffContOnCl_ball le_rfl)
        (C := M / ρ ^ ls.length) (fun τ hτ => by
          have hτ' : ‖τ‖ = ρ := by simpa using hτ
          exact (ih _ (hin τ hτ'.le)).2)
      have hder : deriv f 0 = fderiv ℂ G ζ (Pi.single i 1) := by
        have e0 : ζ + (0 : ℂ) • (Pi.single i 1 : Fin k → ℂ) = ζ := by simp
        have h1 : HasFDerivAt G (fderiv ℂ G ζ) (ζ + (0 : ℂ) • (Pi.single i 1 : Fin k → ℂ)) := by
          rw [e0]
          exact hGa.differentiableAt.hasFDerivAt
        exact (h1.comp_hasDerivAt (0 : ℂ) (hline 0)).deriv
      rw [hder] at hc
      show ‖fderiv ℂ G ζ (Pi.single i 1)‖ ≤ M / ρ ^ (ls.length + 1)
      refine hc.trans (le_of_eq ?_)
      rw [pow_succ]
      field_simp
theorem complexify_add_smul_single (x : Fin k → ℝ) (i : Fin k) (τ : ℝ) :
    complexify (x + τ • Pi.single i 1) = complexify x + (τ : ℂ) • Pi.single i 1 := by
  classical
  funext l
  simp only [complexify, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> simp
theorem complexPartialDeriv_complexify_eq (g : (Fin k → ℂ) → ℂ) (h : (Fin k → ℝ) → ℝ) (ls : List (Fin k))
    (han : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), AnalyticAt ℂ g (complexify x))
    (hre : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), g (complexify x) = (h x : ℂ)) :
    ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), AnalyticAt ℂ (complexPartialDeriv ls g) (complexify x) ∧
      complexPartialDeriv ls g (complexify x) = (realPartialDeriv ls h x : ℂ) := by
  induction ls with
  | nil => exact han.and hre
  | cons i ls ih =>
    filter_upwards [ih.eventually_nhds] with x hx
    obtain ⟨⟨hGa, -⟩, -⟩ := And.intro hx.self_of_nhds hx
    set G := complexPartialDeriv ls g with hG
    set H := realPartialDeriv ls h with hH
    refine ⟨((ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1 : Fin k → ℂ)).analyticAt _).comp hGa.fderiv, ?_⟩
    show fderiv ℂ G (complexify x) (Pi.single i 1) = ((deriv (fun τ : ℝ => H (x + τ • Pi.single i 1)) 0 : ℝ) : ℂ)
    have hline : HasDerivAt (fun τ : ℂ => complexify x + τ • (Pi.single i 1 : Fin k → ℂ)) (Pi.single i 1) ((0 : ℝ) : ℂ) := by
      have := ((hasDerivAt_id ((0 : ℝ) : ℂ)).smul_const (Pi.single i 1 : Fin k → ℂ)).const_add (complexify x)
      simpa using this
    have e0 : complexify x + (((0 : ℝ) : ℂ)) • (Pi.single i 1 : Fin k → ℂ) = complexify x := by simp
    have hf : HasFDerivAt G (fderiv ℂ G (complexify x)) (complexify x + (((0 : ℝ) : ℂ)) • (Pi.single i 1 : Fin k → ℂ)) := by
      rw [e0]
      exact hGa.differentiableAt.hasFDerivAt
    have hc : HasDerivAt (fun τ : ℝ => G (complexify x + (τ : ℂ) • (Pi.single i 1 : Fin k → ℂ)))
        (fderiv ℂ G (complexify x) (Pi.single i 1)) 0 :=
      (hf.comp_hasDerivAt ((0 : ℝ) : ℂ) hline).comp_ofReal
    have hcont : Tendsto (fun τ : ℝ => x + τ • (Pi.single i 1 : Fin k → ℝ)) (𝓝 0) (𝓝 x) := by
      have : Continuous fun τ : ℝ => x + τ • (Pi.single i 1 : Fin k → ℝ) := by fun_prop
      simpa using this.tendsto 0
    have hev : ∀ᶠ τ : ℝ in 𝓝 0, G (complexify x + (τ : ℂ) • (Pi.single i 1 : Fin k → ℂ)) =
        (H (x + τ • Pi.single i 1) : ℂ) := by
      filter_upwards [hcont.eventually hx] with τ hτ
      rw [← complexify_add_smul_single]
      exact hτ.2
    have hre' : HasDerivAt (fun τ : ℝ => (G (complexify x + (τ : ℂ) • (Pi.single i 1 : Fin k → ℂ))).re)
        (fderiv ℂ G (complexify x) (Pi.single i 1)).re 0 :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
    have him' : HasDerivAt (fun τ : ℝ => (G (complexify x + (τ : ℂ) • (Pi.single i 1 : Fin k → ℂ))).im)
        (fderiv ℂ G (complexify x) (Pi.single i 1)).im 0 :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
    have hH' : HasDerivAt (fun τ : ℝ => H (x + τ • Pi.single i 1))
        (fderiv ℂ G (complexify x) (Pi.single i 1)).re 0 := by
      refine hre'.congr_of_eventuallyEq ?_
      filter_upwards [hev] with τ hτ
      rw [hτ]
      simp
    have h0 : HasDerivAt (fun τ : ℝ => (G (complexify x + (τ : ℂ) • (Pi.single i 1 : Fin k → ℂ))).im) 0 0 := by
      refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with τ hτ
      rw [hτ]
      simp
    have him0 := him'.unique h0
    rw [hH'.deriv]
    exact Complex.ext (by simp) (by simpa using him0)
theorem iteratedFDeriv_single_eq_realPartialDeriv (f : (Fin k → ℝ) → ℝ) {x₀ : Fin k → ℝ} (hf : AnalyticAt ℝ f x₀)
    (n : ℕ) (w : Fin n → Fin k) :
    ∀ᶠ x in 𝓝 x₀, iteratedFDeriv ℝ n f x (fun l => Pi.single (w l) 1) = realPartialDeriv (List.ofFn w) f x := by
  induction n with
  | zero =>
    refine Eventually.of_forall fun x => ?_
    simp [realPartialDeriv, iteratedFDeriv_zero_apply]
  | succ n ih =>
    have h1 := ih fun i => w i.succ
    filter_upwards [h1.eventually_nhds, hf.eventually_analyticAt] with x hx hfx
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ]
    show _ = deriv (fun τ : ℝ => realPartialDeriv (List.ofFn fun i => w i.succ) f (x + τ • Pi.single (w 0) 1)) 0
    set v : Fin n → (Fin k → ℝ) := fun l => Pi.single (w l.succ) 1 with hv
    have ht : Fin.tail (fun l : Fin (n + 1) => (Pi.single (w l) 1 : Fin k → ℝ)) = v := by
      funext l
      rfl
    rw [ht]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x :=
      (hfx.contDiffAt (n := ((n + 1 : ℕ) : WithTop ℕ∞))).differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
    have hline : HasDerivAt (fun τ : ℝ => x + τ • (Pi.single (w 0) 1 : Fin k → ℝ)) (Pi.single (w 0) 1) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single (w 0) 1 : Fin k → ℝ)).const_add x
      simpa using this
    have e0 : x + (0 : ℝ) • (Pi.single (w 0) 1 : Fin k → ℝ) = x := by simp
    have hf' : HasFDerivAt (iteratedFDeriv ℝ n f) (fderiv ℝ (iteratedFDeriv ℝ n f) x)
        (x + (0 : ℝ) • (Pi.single (w 0) 1 : Fin k → ℝ)) := by
      rw [e0]
      exact hd.hasFDerivAt
    have hc := hf'.comp_hasDerivAt (0 : ℝ) hline
    have hap : HasDerivAt (fun τ : ℝ => iteratedFDeriv ℝ n f (x + τ • Pi.single (w 0) 1) v)
        (fderiv ℝ (iteratedFDeriv ℝ n f) x (Pi.single (w 0) 1) v) 0 :=
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => (Fin k → ℝ)) ℝ v).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc)
    have hcont : Tendsto (fun τ : ℝ => x + τ • (Pi.single (w 0) 1 : Fin k → ℝ)) (𝓝 0) (𝓝 x) := by
      have : Continuous fun τ : ℝ => x + τ • (Pi.single (w 0) 1 : Fin k → ℝ) := by fun_prop
      simpa using this.tendsto 0
    have hcg : HasDerivAt (fun τ : ℝ => realPartialDeriv (List.ofFn fun i => w i.succ) f (x + τ • Pi.single (w 0) 1))
        (fderiv ℝ (iteratedFDeriv ℝ n f) x (Pi.single (w 0) 1) v) 0 := by
      refine hap.congr_of_eventuallyEq ?_
      filter_upwards [hcont.eventually hx] with τ hτ
      exact hτ.symm
    exact hcg.deriv.symm
theorem realPartialDeriv_of_update_invariant (h : (Fin k → ℝ) → ℝ) (i : Fin k)
    (hP : ∀ x (t : ℝ), h (Function.update x i t) = h x) (ls : List (Fin k)) :
    (∀ x (t : ℝ), realPartialDeriv ls h (Function.update x i t) = realPartialDeriv ls h x) ∧
      (i ∈ ls → ∀ x, realPartialDeriv ls h x = 0) := by
  classical
  induction ls with
  | nil => exact ⟨hP, fun h => by simp at h⟩
  | cons j ls ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hconst : ∀ x, (fun τ : ℝ => realPartialDeriv ls h (x + τ • Pi.single i 1)) =
        fun _ => realPartialDeriv ls h x := by
      intro x
      funext τ
      have : x + τ • (Pi.single i 1 : Fin k → ℝ) = Function.update x i (x i + τ) := by
        funext l
        by_cases hl : l = i
        · subst hl
          simp
        · simp [hl]
      rw [this, ih1]
    have hstep : ∀ x (t : ℝ), realPartialDeriv (j :: ls) h (Function.update x i t) =
        realPartialDeriv (j :: ls) h x := by
      intro x t
      show deriv (fun τ : ℝ => realPartialDeriv ls h (Function.update x i t + τ • Pi.single j 1)) 0 =
        deriv (fun τ : ℝ => realPartialDeriv ls h (x + τ • Pi.single j 1)) 0
      by_cases hj : j = i
      · subst hj
        have e1 : (fun τ : ℝ => realPartialDeriv ls h (Function.update x j t + τ • Pi.single j 1)) =
            fun _ => realPartialDeriv ls h x := by
          funext τ
          have : Function.update x j t + τ • Pi.single j 1 =
              Function.update x j (t + τ) := by
            funext l
            by_cases hl : l = j
            · subst hl
              simp
            · simp [hl]
          rw [this, ih1]
        have e2 : (fun τ : ℝ => realPartialDeriv ls h (x + τ • Pi.single j 1)) =
            fun _ => realPartialDeriv ls h x := by
          funext τ
          have : x + τ • (Pi.single j 1 : Fin k → ℝ) = Function.update x j (x j + τ) := by
            funext l
            by_cases hl : l = j
            · subst hl
              simp
            · simp [hl]
          rw [this, ih1]
        rw [e1, e2]
      · have e1 : (fun τ : ℝ => realPartialDeriv ls h (Function.update x i t + τ • Pi.single j 1)) =
            fun τ => realPartialDeriv ls h (x + τ • Pi.single j 1) := by
          funext τ
          have : Function.update x i t + τ • (Pi.single j 1 : Fin k → ℝ) =
              Function.update (x + τ • Pi.single j 1) i t := by
            funext l
            by_cases hl : l = i
            · subst hl
              simp [Ne.symm hj]
            · simp [hl]
          rw [this, ih1]
        rw [e1]
    refine ⟨hstep, fun hi x => ?_⟩
    show deriv (fun τ : ℝ => realPartialDeriv ls h (x + τ • Pi.single j 1)) 0 = 0
    by_cases hj : j = i
    · subst hj
      rw [hconst x]
      simp
    · have hi' : i ∈ ls := by
        rcases List.mem_cons.1 hi with h' | h'
        · exact absurd h'.symm hj
        · exact h'
      have e : (fun τ : ℝ => realPartialDeriv ls h (x + τ • Pi.single j 1)) = fun _ => 0 := by
        funext τ
        exact ih2 hi' _
      rw [e]
      simp
theorem sum_norm_update_zero_le (ζ : Fin k → ℂ) (i : Fin k) :
    ∑ l, ‖Function.update ζ i 0 l‖ ≤ ∑ l, ‖ζ l‖ := by
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hl : l = i
  · subst hl
    simp
  · simp [hl]
theorem cauchyMixedDerivativeDifferenceProperty_holds : CauchyMixedDerivativeDifferenceProperty := by
  intro k m w i₀ g h r M hr han hre hb
  classical
  set i := w i₀ with hi
  have h0r : ∑ l, ‖(0 : Fin k → ℂ) l‖ < r := by simpa using hr
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb 0 h0r)
  set πc : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ) :=
    ContinuousLinearMap.pi fun l => if l = i then 0 else ContinuousLinearMap.proj l with hπc
  set πr : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearMap.pi fun l => if l = i then 0 else ContinuousLinearMap.proj l with hπr
  have eπc : ∀ ζ, πc ζ = Function.update ζ i 0 := by
    intro ζ
    funext l
    by_cases hl : l = i
    · subst hl
      simp [hπc]
    · simp [hπc, hl]
  have eπr : ∀ x, πr x = Function.update x i 0 := by
    intro x
    funext l
    by_cases hl : l = i
    · subst hl
      simp [hπr]
    · simp [hπr, hl]
  set ιL : (Fin k → ℝ) →L[ℝ] (Fin k → ℂ) :=
    ContinuousLinearMap.pi fun l => Complex.ofRealCLM.comp (ContinuousLinearMap.proj l) with hιL
  have eι : ∀ x, ιL x = complexify x := fun x => rfl
  set G : (Fin k → ℂ) → ℂ := fun ζ => g ζ - g (πc ζ) with hG
  set h₀ : (Fin k → ℝ) → ℝ := fun x => h (πr x) with hh₀
  set H : (Fin k → ℝ) → ℝ := fun x => h x - h₀ x with hH
  have hGa : ∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r → AnalyticAt ℂ G ζ := by
    intro ζ hζ
    have h1 : AnalyticAt ℂ g (πc ζ) := han _ (by
      rw [eπc]
      exact lt_of_le_of_lt (sum_norm_update_zero_le ζ i) hζ)
    exact (han ζ hζ).sub (h1.comp (πc.analyticAt ζ))
  have hGb : ∀ ζ : Fin k → ℂ, ∑ l, ‖ζ l‖ < r → ‖G ζ‖ ≤ M := by
    intro ζ hζ
    simp only [hG, eπc]
    exact hb ζ hζ
  have hι0 : complexify (0 : Fin k → ℝ) = 0 := by
    funext l
    simp [complexify]
  have hπ0 : πr 0 = 0 := map_zero _
  have hreι : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), g (complexify x) = (h x : ℂ) := hre
  have hιπ : ∀ x, complexify (πr x) = πc (complexify x) := by
    intro x
    rw [eπr, eπc]
    funext l
    by_cases hl : l = i
    · subst hl
      simp [complexify]
    · simp [complexify, hl]
  have hπt : Tendsto πr (𝓝 0) (𝓝 0) := by
    have := πr.continuous.tendsto 0
    rwa [hπ0] at this
  have hreG : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), G (complexify x) = (H x : ℂ) := by
    filter_upwards [hreι, hπt.eventually hreι] with x h1 h2
    simp only [hG, hH, hh₀]
    rw [h1, ← hιπ, h2]
    push_cast
    rfl
  have hιt : Tendsto complexify (𝓝 (0 : Fin k → ℝ)) (𝓝 0) := by
    have := ιL.continuous.tendsto 0
    rw [map_zero] at this
    rw [hι0] at *
    exact this.congr eι
  have hball : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), ∑ l, ‖complexify x l‖ < r :=
    hιt.eventually ((isOpen_sum_norm_lt r).mem_nhds h0r)
  have hGι : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), AnalyticAt ℂ G (complexify x) := by
    filter_upwards [hball] with x hx
    exact hGa _ hx
  have hga0 : AnalyticAt ℂ g (ιL 0) := by
    rw [map_zero]
    exact han 0 h0r
  have hha : AnalyticAt ℝ h 0 := by
    have h1 : AnalyticAt ℝ (fun x => (g (ιL x)).re) 0 :=
      (Complex.reCLM.analyticAt _).comp ((hga0.restrictScalars).comp (ιL.analyticAt 0))
    refine h1.congr ?_
    filter_upwards [hreι] with x hx
    rw [eι, hx]
    simp
  have hh₀a : AnalyticAt ℝ h₀ 0 := by
    have h1 : AnalyticAt ℝ h (πr 0) := by
      rw [hπ0]
      exact hha
    exact h1.comp (πr.analyticAt 0)
  have hHa : AnalyticAt ℝ H 0 := hha.sub hh₀a
  set L := List.ofFn w with hLd
  have hlen : L.length = m := by simp [hLd]
  set v : Fin m → (Fin k → ℝ) := fun l => Pi.single (w l) 1 with hv
  have e1 : iteratedFDeriv ℝ m h 0 v = iteratedFDeriv ℝ m H 0 v + iteratedFDeriv ℝ m h₀ 0 v := by
    have e : h = H + h₀ := by
      funext x
      simp [hH]
    have := iteratedFDeriv_add_apply (i := m) (x := (0 : Fin k → ℝ)) (f := H) (g := h₀) (𝕜 := ℝ)
      hHa.contDiffAt hh₀a.contDiffAt
    rw [← e] at this
    rw [this]
    rfl
  have e2 : iteratedFDeriv ℝ m h₀ 0 v = 0 := by
    have h1 := (iteratedFDeriv_single_eq_realPartialDeriv h₀ hh₀a m w).self_of_nhds
    have hP : ∀ x (t : ℝ), h₀ (Function.update x i t) = h₀ x := by
      intro x t
      simp only [hh₀, eπr, Function.update_idem]
    have hmem : i ∈ L := by
      rw [hLd, List.mem_ofFn]
      exact ⟨i₀, rfl⟩
    rw [show iteratedFDeriv ℝ m h₀ 0 v = realPartialDeriv (List.ofFn w) h₀ 0 from h1]
    exact (realPartialDeriv_of_update_invariant h₀ i hP L).2 hmem 0
  have e3 : iteratedFDeriv ℝ m H 0 v = realPartialDeriv L H 0 :=
    (iteratedFDeriv_single_eq_realPartialDeriv H hHa m w).self_of_nhds
  have e4 := (complexPartialDeriv_complexify_eq G H L hGι hreG).self_of_nhds
  set ρ : ℝ := r / ((m : ℝ) + 1) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hin : ∑ l, ‖complexify (0 : Fin k → ℝ) l‖ < r - L.length * ρ := by
    rw [hι0, hlen]
    have h1 : r - m * ρ = ρ := by
      rw [hρ]
      field_simp
      ring
    rw [h1]
    simpa using hρ0
  have e5 := (complexPartialDeriv_bound G hρ0 hM hGa hGb L _ hin).2
  rw [e4.2, Complex.norm_real, Real.norm_eq_abs, hlen] at e5
  rw [e1, e2, add_zero, e3]
  refine e5.trans (le_of_eq ?_)
  rw [hρ, div_pow, div_pow]
  field_simp
end YangMills.Construction.Analytic
end
