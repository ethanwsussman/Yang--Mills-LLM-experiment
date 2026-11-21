import YangMills.Construction.ColdChainAtEveryLevel.HolomorphicFixedPoint
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace YangMills.Construction.Analytic
namespace IsComplexCoordNorm
variable {m : ℕ} {Y : (Fin m → ℂ) → ℝ}
theorem apply_zero (hY : IsComplexCoordNorm Y) : Y 0 = 0 := by
  have := hY.smul_real 0 0
  simpa using this
theorem apply_neg (hY : IsComplexCoordNorm Y) (t : Fin m → ℂ) : Y (-t) = Y t := by
  have := hY.smul_real (-1) t
  simpa using this
theorem sum_le (hY : IsComplexCoordNorm Y) {ι : Type} (s : Finset ι) (f : ι → Fin m → ℂ) :
    Y (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Y (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hY.apply_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hY.triangle _ _).trans (by linarith)
theorem exists_le_mul_norm (hY : IsComplexCoordNorm Y) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, Y t ≤ C * ‖t‖ := by
  classical
  refine ⟨∑ i, (Y (Pi.single i 1) + Y (Pi.single i Complex.I)), ?_, fun t => ?_⟩
  · exact Finset.sum_nonneg fun i _ => add_nonneg (hY.nonneg _) (hY.nonneg _)
  · have hdecomp : t = ∑ i, ((((t i).re : ℝ) : ℂ) • (Pi.single i 1 : Fin m → ℂ) +
        (((t i).im : ℝ) : ℂ) • (Pi.single i Complex.I : Fin m → ℂ)) := by
      funext l
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      rw [Finset.sum_eq_single l]
      · simp [Complex.re_add_im]
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    calc Y t = Y (∑ i, ((((t i).re : ℝ) : ℂ) • (Pi.single i 1 : Fin m → ℂ) +
          (((t i).im : ℝ) : ℂ) • (Pi.single i Complex.I : Fin m → ℂ))) := by rw [← hdecomp]
      _ ≤ ∑ i, Y ((((t i).re : ℝ) : ℂ) • (Pi.single i 1 : Fin m → ℂ) +
          (((t i).im : ℝ) : ℂ) • (Pi.single i Complex.I : Fin m → ℂ)) := hY.sum_le _ _
      _ ≤ ∑ i, (Y (Pi.single i 1) + Y (Pi.single i Complex.I)) * ‖t‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hre : |(t i).re| ≤ ‖t‖ := (Complex.abs_re_le_norm _).trans (norm_le_pi_norm t i)
        have him : |(t i).im| ≤ ‖t‖ := (Complex.abs_im_le_norm _).trans (norm_le_pi_norm t i)
        refine (hY.triangle _ _).trans ?_
        rw [hY.smul_real, hY.smul_real, add_mul]
        have e1 := hY.nonneg (Pi.single i 1)
        have e2 := hY.nonneg (Pi.single i Complex.I)
        nlinarith [mul_le_mul_of_nonneg_right hre e1, mul_le_mul_of_nonneg_right him e2]
      _ = (∑ i, (Y (Pi.single i 1) + Y (Pi.single i Complex.I))) * ‖t‖ := by
        rw [Finset.sum_mul]
theorem continuous (hY : IsComplexCoordNorm Y) : Continuous Y := by
  obtain ⟨C, hC, hup⟩ := hY.exists_le_mul_norm
  have : LipschitzWith ⟨C, hC⟩ Y := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, dist_eq_norm]
    have h1 : Y x ≤ Y y + Y (x - y) := by
      have := hY.triangle y (x - y)
      simpa using this
    have h2 : Y y ≤ Y x + Y (y - x) := by
      have := hY.triangle x (y - x)
      simpa using this
    have h3 : Y (y - x) = Y (x - y) := by
      rw [← neg_sub, hY.apply_neg]
    have h4 := hup (x - y)
    change |Y x - Y y| ≤ C * ‖x - y‖
    refine abs_le.2 ⟨?_, ?_⟩ <;> linarith
  exact this.continuous
theorem exists_mul_norm_le (hY : IsComplexCoordNorm Y) : ∃ c : ℝ, 0 < c ∧ ∀ t, c * ‖t‖ ≤ Y t := by
  by_cases hne : (Metric.sphere (0 : Fin m → ℂ) 1).Nonempty
  · obtain ⟨x, hx, hmin⟩ := (isCompact_sphere (0 : Fin m → ℂ) 1).exists_isMinOn hne
      hY.continuous.continuousOn
    have hx1 : ‖x‖ = 1 := by simpa using hx
    have hx0 : 0 < Y x := by
      refine lt_of_le_of_ne (hY.nonneg x) fun h => ?_
      have := hY.eq_zero x h.symm
      rw [this, norm_zero] at hx1
      exact zero_ne_one hx1
    refine ⟨Y x, hx0, fun t => ?_⟩
    by_cases ht : t = 0
    · simp [ht, hY.nonneg]
    · have hn : 0 < ‖t‖ := norm_pos_iff.2 ht
      have hu : (((‖t‖⁻¹ : ℝ) : ℂ) • t) ∈ Metric.sphere (0 : Fin m → ℂ) 1 := by
        simp [norm_smul, hn.ne']
      have h1 : Y x ≤ Y (((‖t‖⁻¹ : ℝ) : ℂ) • t) := hmin hu
      rw [hY.smul_real, abs_of_pos (inv_pos.2 hn)] at h1
      have h2 : Y x * ‖t‖ ≤ ‖t‖⁻¹ * Y t * ‖t‖ := mul_le_mul_of_nonneg_right h1 hn.le
      have h3 : ‖t‖⁻¹ * Y t * ‖t‖ = Y t := by field_simp
      linarith
  · refine ⟨1, one_pos, fun t => ?_⟩
    by_cases ht : t = 0
    · simp [ht, hY.nonneg]
    · exfalso
      apply hne
      have hn : 0 < ‖t‖ := norm_pos_iff.2 ht
      exact ⟨((‖t‖⁻¹ : ℝ) : ℂ) • t, by simp [norm_smul, hn.ne']⟩
theorem exists_fixedPoint_of_contraction (hY : IsComplexCoordNorm Y) {R : ℝ}
    (f : (Fin m → ℂ) → (Fin m → ℂ)) (h0 : Y (f 0) ≤ R / 4) (hR : 0 < R)
    (hc : ∀ t t', Y t ≤ R → Y t' ≤ R → Y (f t - f t') ≤ (1 / 2) * Y (t - t')) :
    ∃ t, Y t ≤ 2 * Y (f 0) ∧ f t = t ∧
      ∀ C : Set (Fin m → ℂ), IsClosed C → 0 ∈ C → (∀ t ∈ C, Y t ≤ R → f t ∈ C) → t ∈ C := by
  set b := Y (f 0) with hb
  have hb0 : 0 ≤ b := hY.nonneg _
  set x : ℕ → (Fin m → ℂ) := fun n => f^[n] 0 with hx
  have hstep : ∀ n, x (n + 1) = f (x n) := fun n => Function.iterate_succ_apply' f n 0
  have hind : ∀ n, Y (x (n + 1) - x n) ≤ (1 / 2) ^ n * b ∧ Y (x n) ≤ 2 * b * (1 - (1 / 2) ^ n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · have : x 1 = f 0 := rfl
        have h2 : x 0 = 0 := rfl
        rw [this, h2]
        simp [hb]
      · have h2 : x 0 = 0 := rfl
        rw [h2]
        simp [hY.apply_zero]
    | succ n ih =>
      obtain ⟨i1, i2⟩ := ih
      have hp : (0 : ℝ) < (1 / 2) ^ n := by positivity
      have hp1 : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have y1 : Y (x (n + 1)) ≤ 2 * b * (1 - (1 / 2) ^ (n + 1)) := by
        have := hY.triangle (x n) (x (n + 1) - x n)
        simp only [add_sub_cancel] at this
        rw [pow_succ]
        nlinarith
      refine ⟨?_, y1⟩
      have b1 : Y (x n) ≤ R := by nlinarith
      have b2 : Y (x (n + 1)) ≤ R := by
        have : ((1 : ℝ) / 2) ^ (n + 1) > 0 := by positivity
        nlinarith
      rw [hstep (n + 1), hstep n]
      refine (hc _ _ ?_ b1).trans ?_
      · rw [← hstep n]; exact b2
      · rw [← hstep n, pow_succ]
        nlinarith
  obtain ⟨c, hc0, hlow⟩ := hY.exists_mul_norm_le
  have hcau : CauchySeq x := by
    refine cauchySeq_of_le_geometric (1 / 2) (b / c) (by norm_num) fun n => ?_
    rw [dist_comm, dist_eq_norm]
    have h1 := (hlow (x (n + 1) - x n)).trans (hind n).1
    rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
    nlinarith
  obtain ⟨t, ht⟩ := cauchySeq_tendsto_of_complete hcau
  have hcont := hY.continuous
  have hYt : Y t ≤ 2 * b := by
    refine le_of_tendsto ((hcont.tendsto t).comp ht) (Eventually.of_forall fun n => ?_)
    have hp : (0 : ℝ) < (1 / 2) ^ n := by positivity
    have := (hind n).2
    simp only [Function.comp]
    nlinarith
  have hxb : ∀ n, Y (x n) ≤ R := by
    intro n
    have hp : (0 : ℝ) < (1 / 2) ^ n := by positivity
    have := (hind n).2
    nlinarith
  have hfix : Y (f t - t) ≤ 0 := by
    have hlim1 : Tendsto (fun n => Y (f t - x (n + 1))) atTop (𝓝 (Y (f t - t))) := by
      have h1 : Tendsto (fun n => x (n + 1)) atTop (𝓝 t) := ht.comp (tendsto_add_atTop_nat 1)
      exact (hcont.tendsto _).comp (tendsto_const_nhds.sub h1)
    have hlim2 : Tendsto (fun n => (1 / 2) * Y (t - x n)) atTop (𝓝 ((1 / 2) * Y (t - t))) :=
      ((hcont.tendsto _).comp (tendsto_const_nhds.sub ht)).const_mul _
    have hle : ∀ n, Y (f t - x (n + 1)) ≤ (1 / 2) * Y (t - x n) := by
      intro n
      rw [hstep]
      exact hc _ _ (hYt.trans (by linarith)) (hxb n)
    have := le_of_tendsto_of_tendsto' hlim1 hlim2 hle
    simpa [hY.apply_zero] using this
  refine ⟨t, hYt, ?_, fun C hC h0C hinv => ?_⟩
  · have := hY.eq_zero _ (le_antisymm hfix (hY.nonneg _))
    exact sub_eq_zero.1 this
  · have hxC : ∀ n, x n ∈ C := by
      intro n
      induction n with
      | zero => exact h0C
      | succ n ih =>
        rw [hstep]
        exact hinv _ ih (hxb n)
    exact hC.mem_of_tendsto ht (Eventually.of_forall hxC)
end IsComplexCoordNorm
theorem holomorphicFixedPointProperty_holds : HolomorphicFixedPointProperty := by
  intro m k Y Φ Ω R hR hΩ hY han h0 hlip
  classical
  have hex : ∀ ζ ∈ Ω, ∃ t, Y t ≤ 2 * Y (Φ (0, ζ)) ∧ Φ (t, ζ) = t ∧
      ∀ C : Set (Fin m → ℂ), IsClosed C → 0 ∈ C → (∀ t ∈ C, Y t ≤ R → Φ (t, ζ) ∈ C) → t ∈ C := fun ζ hζ =>
    hY.exists_fixedPoint_of_contraction (fun t => Φ (t, ζ)) (h0 ζ hζ) hR (fun t t' ht ht' => hlip ζ hζ t t' ht ht')
  set w : (Fin k → ℂ) → (Fin m → ℂ) := fun ζ => if h : ζ ∈ Ω then (hex ζ h).choose else 0 with hw
  have hw1 : ∀ ζ ∈ Ω, Y (w ζ) ≤ 2 * Y (Φ (0, ζ)) ∧ Φ (w ζ, ζ) = w ζ ∧
      ∀ C : Set (Fin m → ℂ), IsClosed C → 0 ∈ C → (∀ t ∈ C, Y t ≤ R → Φ (t, ζ) ∈ C) → w ζ ∈ C := by
    intro ζ hζ
    simp only [hw, dif_pos hζ]
    exact (hex ζ hζ).choose_spec
  have hwR : ∀ ζ ∈ Ω, Y (w ζ) ≤ R / 2 := fun ζ hζ => (hw1 ζ hζ).1.trans (by linarith [h0 ζ hζ])
  have huniq : ∀ ζ ∈ Ω, ∀ t, Y t ≤ R → Φ (t, ζ) = t → t = w ζ := by
    intro ζ hζ t ht hf
    have h1 := hlip ζ hζ t (w ζ) ht ((hwR ζ hζ).trans (by linarith))
    rw [hf, (hw1 ζ hζ).2.1] at h1
    have h2 := hY.nonneg (t - w ζ)
    have : Y (t - w ζ) = 0 := by linarith
    exact sub_eq_zero.1 (hY.eq_zero _ this)
  refine ⟨w, fun ζ₀ hζ₀ => ⟨?_, (hw1 ζ₀ hζ₀).2.1, (hw1 ζ₀ hζ₀).1, (hw1 ζ₀ hζ₀).2.2⟩⟩
  set t₀ := w ζ₀ with ht₀
  have hYt₀ : Y t₀ ≤ R / 2 := hwR ζ₀ hζ₀
  have hΦ : AnalyticAt ℂ Φ (t₀, ζ₀) := han ζ₀ hζ₀ t₀ (hYt₀.trans (by linarith))
  set G : (Fin m → ℂ) × (Fin k → ℂ) → (Fin m → ℂ) × (Fin k → ℂ) := fun q => (q.1 - Φ q, q.2) with hGd
  have hG : AnalyticAt ℂ G (t₀, ζ₀) := (analyticAt_fst.sub hΦ).prod analyticAt_snd
  set D := fderiv ℂ Φ (t₀, ζ₀) with hDd
  have hD : HasFDerivAt Φ D (t₀, ζ₀) := hΦ.differentiableAt.hasFDerivAt
  have hG' : HasFDerivAt G (((ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → ℂ)) - D).prod
      (ContinuousLinearMap.snd ℂ (Fin m → ℂ) (Fin k → ℂ))) (t₀, ζ₀) :=
    (hasFDerivAt_fst.sub hD).prodMk hasFDerivAt_snd
  set G' := ((ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → ℂ)) - D).prod
      (ContinuousLinearMap.snd ℂ (Fin m → ℂ) (Fin k → ℂ)) with hG'd
  have hcontr : ∀ h : Fin m → ℂ, Y (D (h, 0)) ≤ (1 / 2) * Y h := by
    intro h
    have hlim := hD.lim ((h, 0) : (Fin m → ℂ) × (Fin k → ℂ))
      (c := fun n : ℕ => (((n : ℝ) + 1 : ℝ) : ℂ)) (l := atTop) (by
        have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
          tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
        refine h1.congr fun n => ?_
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)])
    have hcY := hY.continuous.tendsto (D (h, 0))
    have hlim2 := hcY.comp hlim
    refine le_of_tendsto hlim2 ?_
    have hev : ∀ᶠ n : ℕ in atTop, R / 2 + (((n : ℝ) + 1)⁻¹) * Y h ≤ R := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
      have h2 : Tendsto (fun n : ℕ => R / 2 + ((n : ℝ) + 1)⁻¹ * Y h) atTop (𝓝 (R / 2 + 0 * Y h)) :=
        tendsto_const_nhds.add (h1.mul_const _)
      have h3 : R / 2 + 0 * Y h < R := by linarith
      exact (h2.eventually (gt_mem_nhds h3)).mono fun n hn => hn.le
    filter_upwards [hev] with n hn
    simp only [Function.comp]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have e1 : ((t₀, ζ₀) : (Fin m → ℂ) × (Fin k → ℂ)) +
        ((((n : ℝ) + 1 : ℝ) : ℂ))⁻¹ • ((h, 0) : (Fin m → ℂ) × (Fin k → ℂ)) =
        (t₀ + (((((n : ℝ) + 1)⁻¹ : ℝ)) : ℂ) • h, ζ₀) := by
      ext <;> simp
    rw [e1, hY.smul_real, abs_of_pos hpos]
    have hb : Y (t₀ + (((((n : ℝ) + 1)⁻¹ : ℝ)) : ℂ) • h) ≤ R := by
      refine (hY.triangle _ _).trans ?_
      rw [hY.smul_real, abs_of_pos (by positivity)]
      linarith
    have h1 := hlip ζ₀ hζ₀ _ t₀ hb (hYt₀.trans (by linarith))
    have e2 : t₀ + (((((n : ℝ) + 1)⁻¹ : ℝ)) : ℂ) • h - t₀ = (((((n : ℝ) + 1)⁻¹ : ℝ)) : ℂ) • h := by
      abel
    rw [e2, hY.smul_real, abs_of_pos (by positivity)] at h1
    calc ((n : ℝ) + 1) * Y (Φ (t₀ + (((((n : ℝ) + 1)⁻¹ : ℝ)) : ℂ) • h, ζ₀) - Φ (t₀, ζ₀))
        ≤ ((n : ℝ) + 1) * ((1 / 2) * (((n : ℝ) + 1)⁻¹ * Y h)) :=
          mul_le_mul_of_nonneg_left h1 hpos.le
      _ = (1 / 2) * Y h := by field_simp
  have hinj : Function.Injective (G' : ((Fin m → ℂ) × (Fin k → ℂ)) →ₗ[ℂ] ((Fin m → ℂ) × (Fin k → ℂ))) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨h, η⟩ hz
    have hz' : G' (h, η) = 0 := hz
    have e1 : h - D (h, η) = 0 := congrArg Prod.fst hz'
    have e2 : η = 0 := congrArg Prod.snd hz'
    subst e2
    have e3 : D (h, 0) = h := (sub_eq_zero.1 e1).symm
    have h1 := hcontr h
    rw [e3] at h1
    have h2 := hY.nonneg h
    have h3 : Y h = 0 := by linarith
    rw [hY.eq_zero h h3]
    rfl
  set i : ((Fin m → ℂ) × (Fin k → ℂ)) ≃L[ℂ] ((Fin m → ℂ) × (Fin k → ℂ)) :=
    (LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv with hi
  have hiG : (i : ((Fin m → ℂ) × (Fin k → ℂ)) →L[ℂ] ((Fin m → ℂ) × (Fin k → ℂ))) = G' :=
    ContinuousLinearMap.ext fun x => rfl
  have hstrict : HasStrictFDerivAt G (i : ((Fin m → ℂ) × (Fin k → ℂ)) →L[ℂ] ((Fin m → ℂ) × (Fin k → ℂ)))
      (t₀, ζ₀) := by
    rw [hiG, ← hG'.fderiv]
    exact hG.hasStrictFDerivAt
  set e := hstrict.toOpenPartialHomeomorph G with he
  have hsrc : (t₀, ζ₀) ∈ e.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hcoe : (e : _ → _) = G := hstrict.toOpenPartialHomeomorph_coe
  have hG0 : G (t₀, ζ₀) = (0, ζ₀) := by
    simp only [hGd]
    rw [(hw1 ζ₀ hζ₀).2.1]
    simp [ht₀]
  have hsym : AnalyticAt ℂ e.symm (e (t₀, ζ₀)) :=
    e.analyticAt_symm' (i := i) hsrc (by rw [hcoe]; exact hG)
      (by rw [hcoe, hG'.fderiv, hiG])
  have he0 : e (t₀, ζ₀) = (0, ζ₀) := by rw [hcoe]; exact hG0
  rw [he0] at hsym
  have hline : AnalyticAt ℂ (fun ζ : Fin k → ℂ => (((0 : Fin m → ℂ), ζ) : (Fin m → ℂ) × (Fin k → ℂ))) ζ₀ :=
    analyticAt_const.prod analyticAt_id
  have hcomp : AnalyticAt ℂ (fun ζ => e.symm (0, ζ)) ζ₀ := AnalyticAt.fun_comp (g := e.symm) hsym hline
  have hfirst : AnalyticAt ℂ (fun ζ => (e.symm (0, ζ)).1) ζ₀ := analyticAt_fst.fun_comp hcomp
  have hat : (e.symm (0, ζ₀)).1 = t₀ := by
    rw [← he0, e.left_inv hsrc]
  have hYc : ContinuousAt (fun ζ => Y (e.symm (0, ζ)).1) ζ₀ :=
    hY.continuous.continuousAt.comp hfirst.continuousAt
  have hlt : ∀ᶠ ζ in 𝓝 ζ₀, Y (e.symm (0, ζ)).1 < R := by
    refine hYc.eventually_lt continuousAt_const ?_
    simp only [hat]
    linarith
  have htar : ∀ᶠ ζ in 𝓝 ζ₀, (((0 : Fin m → ℂ), ζ) : (Fin m → ℂ) × (Fin k → ℂ)) ∈ e.target := by
    have h1 : e.target ∈ 𝓝 (((0 : Fin m → ℂ), ζ₀) : (Fin m → ℂ) × (Fin k → ℂ)) := by
      rw [← he0]
      exact e.open_target.mem_nhds (e.map_source hsrc)
    exact hline.continuousAt.eventually h1
  refine hfirst.congr ?_
  filter_upwards [hlt, htar, hΩ.mem_nhds hζ₀] with ζ h1 h2 h3
  have h4 : e (e.symm (0, ζ)) = (0, ζ) := e.right_inv h2
  rw [hcoe] at h4
  have h5 : (e.symm (0, ζ)).1 - Φ (e.symm (0, ζ)) = 0 := congrArg Prod.fst h4
  have h6 : (e.symm (0, ζ)).2 = ζ := congrArg Prod.snd h4
  have h7 : Φ ((e.symm (0, ζ)).1, ζ) = (e.symm (0, ζ)).1 := by
    have : (((e.symm (0, ζ)).1, ζ) : (Fin m → ℂ) × (Fin k → ℂ)) = e.symm (0, ζ) := by
      ext1
      · rfl
      · exact h6.symm
    rw [this]
    exact (sub_eq_zero.1 h5).symm
  exact huniq ζ h3 _ h1.le h7
end YangMills.Construction.Analytic
end
