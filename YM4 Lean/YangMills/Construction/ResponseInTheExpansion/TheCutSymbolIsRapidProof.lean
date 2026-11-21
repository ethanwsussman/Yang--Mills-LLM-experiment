import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.ResponseInTheExpansion.TheCutSymbolIsRapid
import Mathlib
set_option autoImplicit false
open scoped SchwartzMap ContDiff Topology
noncomputable section
namespace YangMills.Construction.LatticeFourier
private abbrev Coord4 := Fin 4 → ℝ
private def oneSubExpNegDiv : ℂ → ℂ := dslope (fun w => 1 - Complex.exp (-w)) 0
private lemma differentiable_oneSubExpNegDiv : Differentiable ℂ oneSubExpNegDiv := by
  have h : DifferentiableOn ℂ oneSubExpNegDiv Set.univ :=
    (Complex.differentiableOn_dslope Filter.univ_mem).2
      (Differentiable.differentiableOn (by fun_prop))
  exact differentiableOn_univ.1 h
private lemma contDiff_oneSubExpNegDiv_ofReal :
    ContDiff ℝ ∞ (fun s : ℝ => oneSubExpNegDiv (s : ℂ)) :=
  ((differentiable_oneSubExpNegDiv.contDiff (n := ∞)).restrict_scalars ℝ).comp
    Complex.ofRealCLM.contDiff
private lemma oneSubExpNegDiv_ofReal (s : ℝ) (hs : s ≠ 0) :
    oneSubExpNegDiv (s : ℂ) = (((1 - Real.exp (-s)) / s : ℝ) : ℂ) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  unfold oneSubExpNegDiv
  rw [dslope_of_ne _ hs', slope_def_field]
  simp
private def expNegMulInv (s : ℝ) : ℝ := Real.exp (-s) * s⁻¹
private lemma iteratedDeriv_expNegMulInv (n : ℕ) : ∃ P : Polynomial ℝ, ∀ s : ℝ, 0 < s →
    iteratedDeriv n expNegMulInv s = Real.exp (-s) * P.eval s⁻¹ := by
  induction n with
  | zero => exact ⟨Polynomial.X, fun s _ => by simp [expNegMulInv]⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨-P - Polynomial.X ^ 2 * Polynomial.derivative P, fun s hs => ?_⟩
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv n expNegMulInv =ᶠ[𝓝 s] fun u => Real.exp (-u) * P.eval u⁻¹ := by
      filter_upwards [Ioi_mem_nhds hs] with u hu using hP u hu
    rw [hev.deriv_eq]
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-s)) s := by
      simpa using (hasDerivAt_neg s).exp
    have h2 : HasDerivAt (fun u : ℝ => P.eval u⁻¹)
        ((Polynomial.derivative P).eval s⁻¹ * (-(s ^ 2)⁻¹)) s :=
      (P.hasDerivAt s⁻¹).comp s (hasDerivAt_inv hs.ne')
    have h3 : HasDerivAt (fun u : ℝ => Real.exp (-u) * P.eval u⁻¹) _ s := h1.mul h2
    rw [h3.deriv]
    simp only [Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X]
    field_simp
    ring
private lemma abs_iteratedDeriv_expNegMulInv_le (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, δ ≤ s →
      |iteratedDeriv n expNegMulInv s| ≤ K * Real.exp (-s) := by
  obtain ⟨P, hP⟩ := iteratedDeriv_expNegMulInv n
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := δ⁻¹)).exists_bound_of_continuousOn
    (f := fun y => P.eval y) P.continuous.continuousOn
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0 ⟨le_rfl, by positivity⟩)
  refine ⟨K, hK0, fun s hs => ?_⟩
  have hs0 : 0 < s := hδ.trans_le hs
  rw [hP s hs0, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact hK s⁻¹ ⟨by positivity, inv_anti₀ hδ hs⟩
private lemma exists_schwartz_eq_expNegMulInv (δ : ℝ) (hδ : 0 < δ) :
    ∃ J : 𝓢(ℝ, ℝ), ∀ s : ℝ, δ ≤ s → J s = Real.exp (-s) * s⁻¹ := by
  let β : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, by positivity, by linarith⟩
  set b : ℝ → ℝ := fun s => 1 - β s with hb
  have hβs : ContDiff ℝ ∞ (fun s => β s) := β.contDiff
  have hbs : ContDiff ℝ ∞ b := contDiff_const.sub hβs
  have hbt : b.HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const (1 : ℝ)).sub
      (β.hasCompactSupport.hasTemperateGrowth hβs)
  set J : ℝ → ℝ := fun s => if 0 < s then b s * expNegMulInv s else 0 with hJ
  have hb0 : ∀ u : ℝ, 0 < u → u ≤ δ / 2 → b u = 0 := by
    intro u hu hu2
    have : β u = 1 := β.one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos hu]
      exact hu2)
    simp [hb, this]
  have hJlow : ∀ u : ℝ, u < δ / 2 → J u = 0 := by
    intro u hu
    by_cases h0 : 0 < u
    · simp [hJ, h0, hb0 u h0 hu.le]
    · simp [hJ, h0]
  have hVs : ∀ s : ℝ, 0 < s → ContDiffAt ℝ ∞ expNegMulInv s := by
    intro s hs
    exact ((Real.contDiff_exp.comp contDiff_neg).contDiffAt).mul (contDiffAt_inv ℝ hs.ne')
  have hevlow : ∀ s : ℝ, s < δ / 2 → J =ᶠ[𝓝 s] fun _ => 0 := by
    intro s hs
    filter_upwards [Iio_mem_nhds hs] with u hu using hJlow u hu
  have hevhigh : ∀ s : ℝ, 0 < s → J =ᶠ[𝓝 s] b * expNegMulInv := by
    intro s hs
    filter_upwards [Ioi_mem_nhds hs] with u hu
    simp [hJ, show 0 < u from hu]
  have hJs : ContDiff ℝ ∞ J := by
    rw [contDiff_iff_contDiffAt]
    intro s
    rcases lt_or_ge s (δ / 2) with hs | hs
    · exact contDiffAt_const.congr_of_eventuallyEq (hevlow s hs)
    · have hs0 : 0 < s := by linarith
      exact (hbs.contDiffAt.mul (hVs s hs0)).congr_of_eventuallyEq (hevhigh s hs0)
  have hdecay : ∀ (k n : ℕ), ∃ C : ℝ, ∀ x : ℝ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J x‖ ≤ C := by
    intro k n
    obtain ⟨l, Cb, hCb, hbb⟩ := hbt.norm_iteratedFDeriv_le_uniform n
    have hVb : ∀ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, δ / 2 ≤ s →
        |iteratedDeriv m expNegMulInv s| ≤ K * Real.exp (-s) :=
      fun m => abs_iteratedDeriv_expNegMulInv_le (δ / 2) (by positivity) m
    choose K hK0 hK using hVb
    set S : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cb * K (n - i) with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by
      have := hK0 (n - i)
      positivity
    refine ⟨S * ((k + l).factorial * Real.exp 1), fun s => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    rcases lt_or_ge s (δ / 2) with hs | hs
    · rw [(hevlow s hs).iteratedDeriv_eq n]
      simp only [iteratedDeriv_const]
      have : ‖(if n = 0 then (0 : ℝ) else 0)‖ = 0 := by simp
      rw [this, mul_zero]
      positivity
    · have hs0 : 0 < s := by linarith
      have habs : ‖s‖ = s := by rw [Real.norm_eq_abs, abs_of_pos hs0]
      rw [(hevhigh s hs0).iteratedDeriv_eq n, iteratedDeriv_mul
        (hbs.contDiffAt.of_le (mod_cast le_top)) ((hVs s hs0).of_le (mod_cast le_top))]
      have hterm : ∀ i ∈ Finset.range (n + 1),
          ‖(n.choose i : ℝ) * iteratedDeriv i b s * iteratedDeriv (n - i) expNegMulInv s‖ ≤
            (n.choose i : ℝ) * Cb * K (n - i) * ((1 + s) ^ l * Real.exp (-s)) := by
        intro i hi
        have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have h1 := hbb i hin s
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, habs] at h1
        have h2 := hK (n - i) s hs
        rw [norm_mul, norm_mul, Real.norm_natCast,
          Real.norm_eq_abs (iteratedDeriv (n - i) expNegMulInv s)]
        calc (n.choose i : ℝ) * ‖iteratedDeriv i b s‖ * |iteratedDeriv (n - i) expNegMulInv s|
            ≤ (n.choose i : ℝ) * (Cb * (1 + s) ^ l) * (K (n - i) * Real.exp (-s)) := by gcongr
          _ = _ := by ring
      have hsum : ‖∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * iteratedDeriv i b s * iteratedDeriv (n - i) expNegMulInv s‖ ≤
          S * ((1 + s) ^ l * Real.exp (-s)) := by
        refine (norm_sum_le _ _).trans ?_
        rw [hS, Finset.sum_mul]
        exact Finset.sum_le_sum hterm
      have hfac : (1 + s) ^ (k + l) * Real.exp (-s) ≤ (k + l).factorial * Real.exp 1 := by
        have h3 := Real.pow_div_factorial_le_exp (1 + s) (by positivity) (k + l)
        have h4 : Real.exp (1 + s) = Real.exp 1 * Real.exp s := Real.exp_add _ _
        rw [div_le_iff₀ (by positivity), h4] at h3
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
        calc _ ≤ _ := h3
          _ = _ := by ring
      calc ‖s‖ ^ k * ‖∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * iteratedDeriv i b s * iteratedDeriv (n - i) expNegMulInv s‖
          ≤ (1 + s) ^ k * (S * ((1 + s) ^ l * Real.exp (-s))) := by
            rw [habs]
            have : s ≤ 1 + s := by linarith
            gcongr
        _ = S * ((1 + s) ^ (k + l) * Real.exp (-s)) := by ring
        _ ≤ S * ((k + l).factorial * Real.exp 1) := mul_le_mul_of_nonneg_left hfac hS0
  refine ⟨⟨J, hJs, hdecay⟩, fun s hs => ?_⟩
  have hs0 : 0 < s := hδ.trans_le hs
  have hβ0 : β s = 0 := β.zero_of_le_dist (by
    show δ ≤ dist s 0
    rw [Real.dist_eq, sub_zero, abs_of_pos hs0]
    exact hs)
  show J s = _
  simp [hJ, hs0, hb, hβ0, expNegMulInv]
private lemma hasTemperateGrowth_sum_sq : Function.HasTemperateGrowth (fun p : Coord4 => ∑ i, p i ^ 2) :=
  Function.HasTemperateGrowth.sum fun i _ =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i).hasTemperateGrowth).pow 2
private lemma sq_le_sum_sq (p : Coord4) (i : Fin 4) : p i ^ 2 ≤ ∑ j, p j ^ 2 := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.sq_apply_le_sumSq <;> assumption
private lemma norm_le_sum_sq_bound :
    ∃ (k : ℕ) (C : ℝ), ∀ x : Coord4, ‖x‖ ≤ C * (1 + ‖∑ i, x i ^ 2‖) ^ k := by
  refine ⟨1, 1, fun x => ?_⟩
  have hs : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Real.norm_of_nonneg hs, pow_one, one_mul]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have := sq_le_sum_sq x i
  nlinarith [sq_nonneg (|x i| - 1), sq_abs (x i), abs_nonneg (x i)]
theorem cutoffSymbolSchwartz : cutoffSymbolSchwartzStatement := by
  intro χ hχ hnear hfar a b
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hnear
  have hone : ∀ p : Coord4, ∑ i, p i ^ 2 < ρ ^ 2 → χ p = 1 := by
    intro p hp
    refine hball ?_
    rw [dist_zero_right]
    refine (pi_norm_lt_iff hρ).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact abs_lt_of_sq_lt_sq ((sq_le_sum_sq p i).trans_lt hp) hρ.le
  obtain ⟨J, hJ⟩ := exists_schwartz_eq_expNegMulInv (ρ ^ 2) (by positivity)
  set sq : Coord4 → ℝ := fun p => ∑ i, p i ^ 2 with hsq
  have hsqs : ContDiff ℝ ∞ sq := by
    refine ContDiff.sum fun i _ => ?_
    exact (contDiff_apply ℝ ℝ i).pow 2
  have hzero : ∀ p : Coord4, p ∉ Metric.closedBall (0 : Coord4) 1 → χ p = 0 := by
    intro p hp
    have hp1 : 1 < ‖p‖ := by simpa using hp
    have hex : ∃ i, 1 < |p i| := by
      by_contra hno
      simp only [not_exists, not_lt] at hno
      exact absurd ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
        rw [Real.norm_eq_abs]; exact hno i) (not_le.2 hp1)
    obtain ⟨i, hi⟩ := hex
    refine hfar p ?_
    have h3 := sq_le_sum_sq p i
    nlinarith [sq_abs (p i)]
  have hχc : HasCompactSupport χ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Coord4) 1) hzero
  set f1 : Coord4 → ℂ := fun p => (χ p : ℂ) * ((p a * p b : ℝ) : ℂ) * oneSubExpNegDiv (sq p : ℂ)
    with hf1
  have hf1s : ContDiff ℝ ∞ f1 := by
    have h1 : ContDiff ℝ ∞ (fun p : Coord4 => (χ p : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
    have h2 : ContDiff ℝ ∞ (fun p : Coord4 => ((p a * p b : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ a).mul (contDiff_apply ℝ ℝ b))
    exact (h1.mul h2).mul (contDiff_oneSubExpNegDiv_ofReal.comp hsqs)
  have hf1c : HasCompactSupport f1 :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Coord4) 1) fun p hp => by
      simp [hf1, hzero p hp]
  set gr : Coord4 → ℝ := fun p => (1 - χ p) * (p a * p b) with hgr
  have hgrt : gr.HasTemperateGrowth :=
    ((Function.HasTemperateGrowth.const (1 : ℝ)).sub (hχc.hasTemperateGrowth hχ)).mul
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) a).hasTemperateGrowth).mul
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) b).hasTemperateGrowth))
  have hgt : (fun p : Coord4 => ((gr p : ℝ) : ℂ)).HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth.comp hgrt
  let f3 : 𝓢(Coord4, ℂ) := SchwartzMap.bilinLeftCLM (𝕜 := ℝ)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ) hgt
    (SchwartzMap.compCLM ℝ hasTemperateGrowth_sum_sq norm_le_sum_sq_bound J)
  have hf3 : ∀ p, f3 p = (J (sq p) : ℝ) • ((gr p : ℝ) : ℂ) := fun p => rfl
  refine ⟨hf1c.toSchwartzMap hf1s - f3, fun p => ?_⟩
  have e0 : (hf1c.toSchwartzMap hf1s - f3) p = f1 p - f3 p := rfl
  rw [e0, hf3]
  show _ = (((χ p - Real.exp (-sq p)) * (p a * p b) / sq p : ℝ) : ℂ)
  have hs0 : 0 ≤ sq p := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hs0.eq_or_lt with hs | hs
  · have hpa : p a = 0 := by
      have := sq_le_sum_sq p a
      have h2 : p a ^ 2 ≤ 0 := by rw [hs]; exact this
      nlinarith [sq_nonneg (p a)]
    simp [hf1, hgr, hpa, ← hs]
  · have hne : sq p ≠ 0 := hs.ne'
    simp only [hf1, oneSubExpNegDiv_ofReal _ hne]
    rcases lt_or_ge (sq p) (ρ ^ 2) with hlt | hge
    · have h1 : χ p = 1 := hone p hlt
      simp only [hgr, h1]
      push_cast
      simp
      field_simp
    · have h1 := hJ (sq p) hge
      rw [h1]
      simp only [hgr, Complex.real_smul]
      push_cast
      have hne' : ((sq p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
      field_simp
      ring
end YangMills.Construction.LatticeFourier
