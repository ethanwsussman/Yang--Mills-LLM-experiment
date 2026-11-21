import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.LawOnABoxOfTheFlow.DecayOfASymbol
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Function Metric
namespace YangMills.Construction
namespace LimitForms
private lemma hasDerivAt_iterate_fwdDiff (h : ℝ) (hh : 0 ≤ h) :
    ∀ (N : ℕ) (g g' : ℝ → ℂ) (t : ℝ),
      (∀ s ∈ Icc t (t + N * h), HasDerivAt g (g' s) s) →
      HasDerivAt ((fwdDiff h)^[N] g) ((fwdDiff h)^[N] g' t) t := by
  intro N
  induction N with
  | zero => intro g g' t hd; simpa using hd t (by simp)
  | succ N ih =>
    intro g g' t hd
    simp only [iterate_succ_apply]
    refine ih (fwdDiff h g) (fwdDiff h g') t ?_
    intro s hs
    have h1 : s + h ∈ Icc t (t + ((N + 1 : ℕ) : ℝ) * h) := by
      constructor
      · linarith [hs.1]
      · push_cast; linarith [hs.2]
    have h2 : s ∈ Icc t (t + ((N + 1 : ℕ) : ℝ) * h) := by
      constructor
      · exact hs.1
      · push_cast; linarith [hs.2]
    exact ((hd (s + h) h1).comp_add_const s h).sub (hd s h2)
private lemma norm_iterate_fwdDiff_le (h : ℝ) (hh : 0 ≤ h) :
    ∀ (N : ℕ) (g : ℕ → ℝ → ℂ) (t B : ℝ),
      (∀ j < N, ∀ s ∈ Icc t (t + N * h), HasDerivAt (g j) (g (j + 1) s) s) →
      (∀ s ∈ Icc t (t + N * h), ‖g N s‖ ≤ B) →
      ‖(fwdDiff h)^[N] (g 0) t‖ ≤ h ^ N * B := by
  intro N
  induction N with
  | zero => intro g t B _ hB; simpa using hB t (by simp)
  | succ N ih =>
    intro g t B hd hB
    rw [iterate_succ_apply']
    have hder : ∀ s ∈ Icc t (t + h),
        HasDerivWithinAt ((fwdDiff h)^[N] (g 0)) ((fwdDiff h)^[N] (g 1) s) (Icc t (t + h)) s := by
      intro s hs
      refine (hasDerivAt_iterate_fwdDiff h hh N (g 0) (g 1) s ?_).hasDerivWithinAt
      intro u hu
      refine hd 0 (by omega) u ⟨by linarith [hs.1, hu.1], ?_⟩
      push_cast
      linarith [hs.2, hu.2]
    have hψ : ∀ s ∈ Ico t (t + h), ‖(fwdDiff h)^[N] (g 1) s‖ ≤ h ^ N * B := by
      intro s hs
      refine ih (fun j => g (j + 1)) s B (fun j hj u hu => hd (j + 1) (by omega) u ⟨by linarith [hs.1, hu.1], ?_⟩)
        (fun u hu => hB u ⟨by linarith [hs.1, hu.1], ?_⟩)
      · push_cast; linarith [hs.2, hu.2]
      · push_cast; linarith [hs.2, hu.2]
    have key := norm_image_sub_le_of_norm_deriv_le_segment' hder hψ (t + h) (right_mem_Icc.2 (by linarith))
    have e : fwdDiff h ((fwdDiff h)^[N] (g 0)) t = (fwdDiff h)^[N] (g 0) (t + h) - (fwdDiff h)^[N] (g 0) t := rfl
    rw [e]
    calc _ ≤ h ^ N * B * (t + h - t) := key
      _ = h ^ (N + 1) * B := by ring
private lemma integral_norm_zpow_closedBall (n : ℕ) (hn : 1 ≤ n) (ρ : ℝ) (hρ : 0 < ρ) :
    IntegrableOn (fun q : Fin 4 → ℝ => ‖q‖ ^ ((n : ℤ) - 4)) (closedBall 0 ρ) ∧
    ∫ q in closedBall (0 : Fin 4 → ℝ) ρ, ‖q‖ ^ ((n : ℤ) - 4) =
      4 * (volume : Measure (Fin 4 → ℝ)).real (ball 0 1) * (ρ ^ n / n) := by
  set f : ℝ → ℝ := (Iic ρ).indicator (fun y => y ^ ((n : ℤ) - 4)) with hf
  have h1 : (fun q : Fin 4 → ℝ => f ‖q‖) =
      (closedBall (0 : Fin 4 → ℝ) ρ).indicator (fun q => ‖q‖ ^ ((n : ℤ) - 4)) := by
    ext q
    by_cases hq : ‖q‖ ≤ ρ
    · simp [hf, hq]
    · simp [hf, hq]
  have hk : ∀ y ∈ Ioi (0 : ℝ), y ^ 3 • f y = (Ioc 0 ρ).indicator (fun y => y ^ (n - 1)) y := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    by_cases hq : y ≤ ρ
    · have : y ^ 3 * y ^ ((n : ℤ) - 4) = y ^ (n - 1) := by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        have : ((k + 1 : ℕ) : ℤ) - 4 = (k : ℤ) - 3 := by push_cast; ring
        rw [this, zpow_sub₀ hy'.ne']
        simp only [zpow_natCast, Nat.add_sub_cancel]
        have : y ^ ((3 : ℤ)) = y ^ 3 := by norm_cast
        rw [this]
        field_simp
      simp [hf, hq, hy', this]
    · simp [hf, hq, hy']
  have hint : IntegrableOn (Ioc 0 ρ |>.indicator (fun y : ℝ => y ^ (n - 1))) (Ioi 0) :=
    (((continuous_pow (n - 1)).integrableOn_Ioc (a := 0) (b := ρ)).integrable_indicator
      measurableSet_Ioc).integrableOn
  have hint' : Integrable (fun q : Fin 4 → ℝ => f ‖q‖) volume := by
    rw [integrable_fun_norm_addHaar volume]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact hint.congr_fun (fun y hy => (hk y hy).symm) measurableSet_Ioi
  constructor
  · rw [h1] at hint'
    exact (integrable_indicator_iff measurableSet_closedBall).1 hint'
  · rw [← integral_indicator measurableSet_closedBall, ← h1, integral_fun_norm_addHaar]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => hk y hy),
      setIntegral_indicator measurableSet_Ioc]
    have : Ioi (0 : ℝ) ∩ Ioc 0 ρ = Ioc 0 ρ := inter_eq_right.2 (fun y hy => hy.1)
    rw [this, ← intervalIntegral.integral_of_le hρ.le, integral_pow]
    have hn' : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      have : n - 1 + 1 = n := by omega
      exact_mod_cast this
    have hn'' : n - 1 + 1 = n := by omega
    rw [hn', hn'']
    simp [zero_pow (show n ≠ 0 by omega)]
    ring
private lemma integral_inv_pow_five_compl_closedBall (ρ : ℝ) (hρ : 0 < ρ) :
    IntegrableOn (fun q : Fin 4 → ℝ => (‖q‖ ^ 5)⁻¹) (closedBall 0 ρ)ᶜ ∧
    ∫ q in (closedBall (0 : Fin 4 → ℝ) ρ)ᶜ, (‖q‖ ^ 5)⁻¹ =
      4 * (volume : Measure (Fin 4 → ℝ)).real (ball 0 1) * ρ⁻¹ := by
  set f : ℝ → ℝ := (Ioi ρ).indicator (fun y => (y ^ 5)⁻¹) with hf
  have h1 : (fun q : Fin 4 → ℝ => f ‖q‖) =
      (closedBall (0 : Fin 4 → ℝ) ρ)ᶜ.indicator (fun q => (‖q‖ ^ 5)⁻¹) := by
    ext q
    by_cases hq : ‖q‖ ≤ ρ
    · simp [hf, hq]
    · simp [hf, hq, not_le.1 hq]
  have hk : ∀ y ∈ Ioi (0 : ℝ), y ^ 3 • f y = (Ioi ρ).indicator (fun y => y ^ (-2 : ℝ)) y := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    by_cases hq : ρ < y
    · have : y ^ 3 * (y ^ 5)⁻¹ = y ^ (-2 : ℝ) := by
        rw [Real.rpow_neg hy'.le]
        norm_num
        field_simp
      simp [hf, hq, this]
    · simp [hf, hq]
  have hint : IntegrableOn ((Ioi ρ).indicator (fun y : ℝ => y ^ (-2 : ℝ))) (Ioi 0) :=
    ((integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hρ).integrable_indicator
      measurableSet_Ioi).integrableOn
  have hint' : Integrable (fun q : Fin 4 → ℝ => f ‖q‖) volume := by
    rw [integrable_fun_norm_addHaar volume]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact hint.congr_fun (fun y hy => (hk y hy).symm) measurableSet_Ioi
  constructor
  · rw [h1] at hint'
    exact (integrable_indicator_iff measurableSet_closedBall.compl).1 hint'
  · rw [← integral_indicator measurableSet_closedBall.compl, ← h1, integral_fun_norm_addHaar]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => hk y hy),
      setIntegral_indicator measurableSet_Ioi]
    have : Ioi (0 : ℝ) ∩ Ioi ρ = Ioi ρ := inter_eq_right.2 (Ioi_subset_Ioi hρ.le)
    rw [this, integral_Ioi_rpow_of_lt (by norm_num) hρ]
    have : ρ ^ (-2 + 1 : ℝ) = ρ⁻¹ := by
      norm_num
      exact Real.rpow_neg_one ρ
    rw [this]
    simp
    ring
private lemma mem_brillouinBox_iff (p : Fin 4 → ℝ) :
    p ∈ brillouinBox ↔ ∀ l, -Real.pi ≤ p l ∧ p l ≤ Real.pi := by
  simp only [brillouinBox, mem_Icc, Pi.le_def, forall_and]
private lemma closedBall_subset_brillouinBox (r : ℝ) (hr : r ≤ Real.pi) :
    closedBall (0 : Fin 4 → ℝ) r ⊆ brillouinBox := by
  intro p hp
  rw [mem_closedBall_zero_iff] at hp
  rw [mem_brillouinBox_iff]
  intro l
  have := abs_le.1 (((norm_le_pi_norm p l).trans hp).trans hr)
  exact this
private lemma measurableSet_brillouinBox : MeasurableSet brillouinBox := measurableSet_Icc
private lemma insertNth_add_single (i : Fin 4) (t s : ℝ) (q : Fin 3 → ℝ) :
    (Fin.insertNth i t q : Fin 4 → ℝ) + Pi.single i s = Fin.insertNth i (t + s) q := by
  ext l
  rcases Fin.eq_self_or_eq_succAbove i l with rfl | ⟨k, rfl⟩
  · simp
  · simp [Fin.succAbove_ne]
private lemma integral_brillouinBox_eq_slices (i : Fin 4) (G : (Fin 4 → ℝ) → ℂ)
    (hG : IntegrableOn G brillouinBox) :
    ∫ p in brillouinBox, G p = ∫ q : Fin 3 → ℝ,
      (Icc (fun _ => -Real.pi) (fun _ => Real.pi) : Set (Fin 3 → ℝ)).indicator
        (fun q => ∫ t in Icc (-Real.pi) Real.pi, G (Fin.insertNth i t q)) q := by
  have mp := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) i with he
  have hG' : Integrable (brillouinBox.indicator G) := (integrable_indicator_iff measurableSet_brillouinBox).2 hG
  have hint : Integrable (fun y => brillouinBox.indicator G (e.symm y)) (volume : Measure (ℝ × (Fin 3 → ℝ))) :=
    ((mp.symm e).integrable_comp_emb e.symm.measurableEmbedding).2 hG'
  rw [← integral_indicator measurableSet_brillouinBox, ← (mp.symm e).integral_comp' (brillouinBox.indicator G),
    Measure.volume_eq_prod, integral_prod_symm _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  have hs : ∀ t, e.symm (t, q) = Fin.insertNth i t q := fun t => rfl
  have hmem : ∀ t, (Fin.insertNth i t q : Fin 4 → ℝ) ∈ brillouinBox ↔
      t ∈ Icc (-Real.pi) Real.pi ∧ q ∈ (Icc (fun _ => -Real.pi) (fun _ => Real.pi) : Set (Fin 3 → ℝ)) := by
    intro t
    rw [mem_brillouinBox_iff, i.forall_iff_succAbove]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, mem_Icc, Pi.le_def,
      forall_and]
  simp only [hs]
  by_cases hq : q ∈ (Icc (fun _ => -Real.pi) (fun _ => Real.pi) : Set (Fin 3 → ℝ))
  · rw [indicator_of_mem hq, ← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ Icc (-Real.pi) Real.pi
    · simp only [indicator_of_mem ht, indicator_of_mem ((hmem t).2 ⟨ht, hq⟩)]
    · simp only [indicator_of_notMem ht, indicator_of_notMem (fun h => ht ((hmem t).1 h).1)]
  · rw [indicator_of_notMem hq]
    have : ∀ t, brillouinBox.indicator G (Fin.insertNth i t q) = 0 := fun t =>
      indicator_of_notMem (fun h => hq ((hmem t).1 h).2) _
    simp [this]
private lemma integral_brillouinBox_shift (i : Fin 4) (F : (Fin 4 → ℝ) → ℂ)
    (hper : ∀ p, F (p + Pi.single i (2 * Real.pi)) = F p)
    (hF : IntegrableOn F brillouinBox) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 2 * Real.pi) :
    IntegrableOn (fun p => F (p + Pi.single i s)) brillouinBox ∧
      ∫ p in brillouinBox, F (p + Pi.single i s) = ∫ p in brillouinBox, F p := by
  set T : Fin 4 → ℝ := Pi.single i (2 * Real.pi) with hT
  set v : Fin 4 → ℝ := Pi.single i s with hv
  have hU : IntegrableOn F (brillouinBox ∪ (fun p => p + (-T)) ⁻¹' brillouinBox) := by
    refine hF.union ?_
    have h2 := ((measurePreserving_add_right volume (-T)).integrableOn_comp_preimage
      (measurableEmbedding_addRight (-T))).2 hF
    refine h2.congr_fun (fun p _ => ?_) ((measurable_add_const (-T)) measurableSet_brillouinBox)
    have := hper (p + -T)
    simpa using this.symm
  have hI : IntegrableOn (fun p => F (p + v)) brillouinBox := by
    have h2 := ((measurePreserving_add_right volume v).integrableOn_comp_preimage
      (measurableEmbedding_addRight v)).2 hU
    refine h2.mono_set ?_
    intro p hp
    rw [mem_brillouinBox_iff] at hp
    have hpi := Real.pi_pos
    by_cases hc : p i + s ≤ Real.pi
    · left
      rw [mem_brillouinBox_iff]
      intro l
      by_cases hl : l = i
      · subst hl
        have := hp l
        simp only [hv, Pi.add_apply, Pi.single_eq_same]
        constructor <;> linarith [this.1]
      · have := hp l
        simpa [hv, Pi.single_eq_of_ne hl] using this
    · right
      show p + v + -T ∈ brillouinBox
      rw [mem_brillouinBox_iff]
      intro l
      by_cases hl : l = i
      · subst hl
        have := hp l
        simp only [hv, hT, Pi.add_apply, Pi.neg_apply, Pi.single_eq_same]
        constructor <;> linarith [this.2, not_le.1 hc]
      · have := hp l
        simpa [hv, hT, Pi.single_eq_of_ne hl] using this
  refine ⟨hI, ?_⟩
  rw [integral_brillouinBox_eq_slices i _ hI, integral_brillouinBox_eq_slices i _ hF]
  congr 1
  ext q
  congr 1
  ext q'
  set φ : ℝ → ℂ := fun t => F (Fin.insertNth i t q') with hφ
  have hper' : Function.Periodic φ (2 * Real.pi) := by
    intro t
    simp only [hφ]
    rw [← insertNth_add_single, hper]
  have h3 : ∀ t, F ((Fin.insertNth i t q' : Fin 4 → ℝ) + v) = φ (t + s) := by
    intro t
    simp only [hφ, hv]
    rw [insertNth_add_single]
  simp only [h3]
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    intervalIntegral.integral_comp_add_right φ s]
  have h4 := hper'.intervalIntegral_add_eq (-Real.pi + s) (-Real.pi)
  have e1 : -Real.pi + s + 2 * Real.pi = Real.pi + s := by ring
  have e2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [e1, e2] at h4
  exact h4
private def planeWave (w p : Fin 4 → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((∑ l, p l * w l : ℝ) : ℂ))
private lemma norm_planeWave (w p : Fin 4 → ℝ) : ‖planeWave w p‖ = 1 := by
  rw [planeWave, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _
abbrev _root_.YangMills.DeltaSharedProofs.p501034 := @norm_planeWave
private lemma continuous_planeWave (w : Fin 4 → ℝ) : Continuous (planeWave w) := by
  unfold planeWave
  fun_prop
private lemma planeWave_add_single (w p : Fin 4 → ℝ) (i : Fin 4) (s : ℝ) :
    planeWave w (p + Pi.single i s) =
      planeWave w p * Complex.exp (Complex.I * ((s * w i : ℝ) : ℂ)) := by
  have : ∑ l, (p + Pi.single i s : Fin 4 → ℝ) l * w l = ∑ l, p l * w l + s * w i := by
    simp [add_mul, Finset.sum_add_distrib, Pi.single_apply]
  rw [planeWave, planeWave, this, ← Complex.exp_add]
  congr 1
  push_cast
  ring
private lemma planeWave_neg_mul (w p : Fin 4 → ℝ) : planeWave (-w) p * planeWave w p = 1 := by
  rw [planeWave, planeWave, ← Complex.exp_add]
  have : ∑ l, p l * (-w) l = -∑ l, p l * w l := by simp
  rw [this]
  simp
private lemma integrableOn_mul_planeWave {S : Set (Fin 4 → ℝ)} {g : (Fin 4 → ℝ) → ℂ}
    (w : Fin 4 → ℝ) (hg : IntegrableOn g S) : IntegrableOn (fun p => g p * planeWave w p) S := by
  refine Integrable.mono hg
    (hg.aestronglyMeasurable.mul (continuous_planeWave w).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => ?_)
  simp [norm_planeWave]
private lemma integrableOn_of_mul_planeWave {S : Set (Fin 4 → ℝ)} {g : (Fin 4 → ℝ) → ℂ}
    (w : Fin 4 → ℝ) (hg : IntegrableOn (fun p => g p * planeWave w p) S) : IntegrableOn g S := by
  have := integrableOn_mul_planeWave (-w) hg
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only
  rw [mul_assoc, mul_comm (planeWave w p), planeWave_neg_mul, mul_one]
private def IsQuasiPeriodic (κ : ℂ) (i : Fin 4) (f : (Fin 4 → ℝ) → ℂ) : Prop :=
  ∀ p, f (p + Pi.single i (2 * Real.pi)) * κ = f p
private lemma fwdDiff_quasiPeriodic_integral (w : Fin 4 → ℝ) (i : Fin 4) (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 2 * Real.pi)
    (hminus : Complex.exp (Complex.I * ((h * w i : ℝ) : ℂ)) = -1)
    (f : (Fin 4 → ℝ) → ℂ)
    (hQ : IsQuasiPeriodic (Complex.exp (Complex.I * ((2 * Real.pi * w i : ℝ) : ℂ))) i f)
    (hI : IntegrableOn f brillouinBox) :
    IsQuasiPeriodic (Complex.exp (Complex.I * ((2 * Real.pi * w i : ℝ) : ℂ))) i (fwdDiff (Pi.single i h) f) ∧
    IntegrableOn (fwdDiff (Pi.single i h) f) brillouinBox ∧
    ∫ p in brillouinBox, fwdDiff (Pi.single i h) f p * planeWave w p =
      -2 * ∫ p in brillouinBox, f p * planeWave w p := by
  set v : Fin 4 → ℝ := Pi.single i h with hv
  set F : (Fin 4 → ℝ) → ℂ := fun p => f p * planeWave w p with hFdef
  have hFper : ∀ p, F (p + Pi.single i (2 * Real.pi)) = F p := by
    intro p
    simp only [hFdef]
    rw [planeWave_add_single, ← mul_assoc, mul_right_comm, hQ p]
  have hFI : IntegrableOn F brillouinBox := integrableOn_mul_planeWave w hI
  obtain ⟨hs1, hs2⟩ := integral_brillouinBox_shift i F hFper hFI h h0 h1
  have hFv : ∀ p, F (p + v) = -(f (p + v) * planeWave w p) := by
    intro p
    simp only [hFdef, hv]
    rw [planeWave_add_single, hminus]
    ring
  have hfv1 : IntegrableOn (fun p => f (p + v) * planeWave w p) brillouinBox := by
    have := hs1.neg
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.neg_apply]
    rw [hFv]
    ring
  have hfv : IntegrableOn (fun p => f (p + v)) brillouinBox := integrableOn_of_mul_planeWave w hfv1
  refine ⟨?_, hfv.sub hI, ?_⟩
  · intro p
    simp only [fwdDiff]
    rw [sub_mul, add_right_comm, hQ (p + v), hQ p]
  · have e1 : ∀ p, fwdDiff v f p * planeWave w p = -F (p + v) - F p := by
      intro p
      rw [hFv]
      simp only [fwdDiff, hFdef]
      ring
    simp only [e1]
    have hn : IntegrableOn (fun p => -F (p + v)) brillouinBox := hs1.neg
    rw [integral_sub hn hFI, integral_neg, hs2]
    ring
private lemma iterate_fwdDiff_quasiPeriodic_integral (w : Fin 4 → ℝ) (i : Fin 4) (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 2 * Real.pi)
    (hminus : Complex.exp (Complex.I * ((h * w i : ℝ) : ℂ)) = -1)
    (f : (Fin 4 → ℝ) → ℂ)
    (hQ : IsQuasiPeriodic (Complex.exp (Complex.I * ((2 * Real.pi * w i : ℝ) : ℂ))) i f)
    (hI : IntegrableOn f brillouinBox) (N : ℕ) :
    IsQuasiPeriodic (Complex.exp (Complex.I * ((2 * Real.pi * w i : ℝ) : ℂ))) i
        ((fwdDiff (Pi.single i h))^[N] f) ∧
    IntegrableOn ((fwdDiff (Pi.single i h))^[N] f) brillouinBox ∧
    ∫ p in brillouinBox, (fwdDiff (Pi.single i h))^[N] f p * planeWave w p =
      (-2) ^ N * ∫ p in brillouinBox, f p * planeWave w p := by
  induction N with
  | zero => exact ⟨hQ, hI, by simp⟩
  | succ N ih =>
    obtain ⟨a1, a2, a3⟩ := ih
    obtain ⟨b1, b2, b3⟩ := fwdDiff_quasiPeriodic_integral w i h h0 h1 hminus _ a1 a2
    rw [iterate_succ_apply']
    refine ⟨b1, b2, ?_⟩
    rw [b3, a3]
    ring
private lemma integral_norm_fwdDiff_closedBall_le (i : Fin 4) (h : ℝ) (h0 : 0 ≤ h) (r : ℝ) (f : (Fin 4 → ℝ) → ℂ)
    (hI : IntegrableOn f (closedBall 0 (r + h))) :
    IntegrableOn (fwdDiff (Pi.single i h) f) (closedBall 0 r) ∧
    ∫ p in closedBall (0 : Fin 4 → ℝ) r, ‖fwdDiff (Pi.single i h) f p‖ ≤
      2 * ∫ p in closedBall (0 : Fin 4 → ℝ) (r + h), ‖f p‖ := by
  set v : Fin 4 → ℝ := Pi.single i h with hv
  have hvn : ‖v‖ ≤ h := by
    rw [pi_norm_le_iff_of_nonneg h0]
    intro l
    by_cases hl : l = i
    · subst hl
      simp [hv, abs_of_nonneg h0]
    · simp [hv, Pi.single_eq_of_ne hl, h0]
  have hsub : closedBall (0 : Fin 4 → ℝ) r ⊆ (fun p => p + v) ⁻¹' closedBall 0 (r + h) := by
    intro p hp
    rw [mem_closedBall_zero_iff] at hp
    simp only [mem_preimage, mem_closedBall_zero_iff]
    exact (norm_add_le _ _).trans (by linarith)
  have hsubb : closedBall (0 : Fin 4 → ℝ) r ⊆ closedBall 0 (r + h) :=
    closedBall_subset_closedBall (by linarith)
  have hpre : IntegrableOn (fun p => f (p + v)) ((fun p => p + v) ⁻¹' closedBall 0 (r + h)) :=
    ((measurePreserving_add_right volume v).integrableOn_comp_preimage
      (measurableEmbedding_addRight v)).2 hI
  have hsmall := hI.mono_set hsubb
  have hv1 := hpre.mono_set hsub
  refine ⟨hv1.sub hsmall, ?_⟩
  have e1 : ∫ p in closedBall (0 : Fin 4 → ℝ) r, ‖f (p + v)‖ ≤
      ∫ p in closedBall (0 : Fin 4 → ℝ) (r + h), ‖f p‖ := by
    have e2 := (measurePreserving_add_right volume v).setIntegral_preimage_emb
      (measurableEmbedding_addRight v) (fun q => ‖f q‖) (closedBall 0 (r + h))
    rw [← e2]
    exact setIntegral_mono_set hpre.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (LE.le.eventuallyLE hsub)
  have e3 : ∫ p in closedBall (0 : Fin 4 → ℝ) r, ‖f p‖ ≤
      ∫ p in closedBall (0 : Fin 4 → ℝ) (r + h), ‖f p‖ :=
    setIntegral_mono_set hI.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (LE.le.eventuallyLE hsubb)
  calc ∫ p in closedBall (0 : Fin 4 → ℝ) r, ‖fwdDiff v f p‖
      ≤ ∫ p in closedBall (0 : Fin 4 → ℝ) r, (‖f (p + v)‖ + ‖f p‖) := by
        refine integral_mono (hv1.sub hsmall).norm (hv1.norm.add hsmall.norm) fun p => ?_
        exact norm_sub_le _ _
    _ = (∫ p in closedBall (0 : Fin 4 → ℝ) r, ‖f (p + v)‖) +
        ∫ p in closedBall (0 : Fin 4 → ℝ) r, ‖f p‖ := integral_add hv1.norm hsmall.norm
    _ ≤ _ := by linarith
private lemma integral_norm_iterate_fwdDiff_closedBall_le (i : Fin 4) (h : ℝ) (h0 : 0 ≤ h) (N : ℕ) :
    ∀ (r : ℝ) (f : (Fin 4 → ℝ) → ℂ), IntegrableOn f (closedBall 0 (r + N * h)) →
    IntegrableOn ((fwdDiff (Pi.single i h))^[N] f) (closedBall 0 r) ∧
    ∫ p in closedBall (0 : Fin 4 → ℝ) r, ‖(fwdDiff (Pi.single i h))^[N] f p‖ ≤
      2 ^ N * ∫ p in closedBall (0 : Fin 4 → ℝ) (r + N * h), ‖f p‖ := by
  induction N with
  | zero => intro r f hf; simpa using hf
  | succ N ih =>
    intro r f hf
    have e : r + ((N + 1 : ℕ) : ℝ) * h = r + N * h + h := by push_cast; ring
    rw [e] at hf ⊢
    obtain ⟨b1, b2⟩ := integral_norm_fwdDiff_closedBall_le i h h0 (r + N * h) f hf
    obtain ⟨c1, c2⟩ := ih r _ b1
    rw [iterate_succ_apply]
    refine ⟨c1, c2.trans ?_⟩
    calc _ ≤ (2 : ℝ) ^ N * (2 * ∫ p in closedBall (0 : Fin 4 → ℝ) (r + N * h + h), ‖f p‖) := by gcongr
      _ = _ := by ring
private lemma update_add_single (p : Fin 4 → ℝ) (i : Fin 4) (t s : ℝ) :
    update p i t + Pi.single i s = update p i (t + s) := by
  ext l
  by_cases hl : l = i
  · subst hl; simp
  · simp [hl]
private lemma iterate_fwdDiff_update (p : Fin 4 → ℝ) (i : Fin 4) (h : ℝ) (N : ℕ) :
    ∀ (f : (Fin 4 → ℝ) → ℂ) (t : ℝ), (fwdDiff (Pi.single i h))^[N] f (update p i t) =
      (fwdDiff h)^[N] (fun t => f (update p i t)) t := by
  induction N with
  | zero => intro f t; rfl
  | succ N ih =>
    intro f t
    have e : (fun t => fwdDiff (Pi.single i h) f (update p i t)) =
        fwdDiff h (fun t => f (update p i t)) := by
      funext s
      simp only [fwdDiff]
      rw [update_add_single]
    rw [iterate_succ_apply, iterate_succ_apply, ih, e]
private lemma hasDerivAt_iteratedDeriv_of_contDiffAt (φ : ℝ → ℂ) (s : ℝ) (N j : ℕ) (hj : j < N)
    (h : ContDiffAt ℝ N φ s) :
    HasDerivAt (iteratedDeriv j φ) (iteratedDeriv (j + 1) φ s) s := by
  have h1 := h.differentiableAt_iteratedFDeriv (m := j) (by exact_mod_cast hj)
  have h2 : iteratedDeriv j φ = fun x => (iteratedFDeriv ℝ j φ x) (fun _ => 1) := by
    ext x
    exact iteratedDeriv_eq_iteratedFDeriv
  have h3 : DifferentiableAt ℝ (iteratedDeriv j φ) s := by
    rw [h2]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℝ) ℂ
      (fun _ => 1)).differentiableAt.comp s h1
  rw [iteratedDeriv_succ]
  exact h3.hasDerivAt
private lemma norm_iterate_fwdDiff_le_far (a : (Fin 4 → ℝ) → ℂ) (κ : ℂ) (hκ : ‖κ‖ = 1) (i : Fin 4)
    (hQ : IsQuasiPeriodic κ i a)
    (hsm : ∀ (j : ℕ) (p : Fin 4 → ℝ), p ∈ brillouinBox → p ≠ 0 → ContDiffAt ℝ j a p)
    (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hN : ∀ p : Fin 4 → ℝ, p ∈ brillouinBox → p ≠ 0 →
      ‖iteratedDeriv N (fun t : ℝ => a (update p i t)) (p i)‖ ≤ B * (‖p‖ ^ 5)⁻¹)
    (h : ℝ) (h0 : 0 ≤ h) (hNh : N * h ≤ Real.pi / 8) (p : Fin 4 → ℝ) (hp : p ∈ brillouinBox)
    (hρ : 2 * (N * h) < ‖p‖) :
    ‖(fwdDiff (Pi.single i h))^[N] a p‖ ≤ h ^ N * (32 * B * (‖p‖ ^ 5)⁻¹) := by
  set φ : ℝ → ℂ := fun t => a (update p i t) with hφ
  have hpi := Real.pi_pos
  have hNh0 : 0 ≤ (N : ℝ) * h := by positivity
  have hpn : 0 < ‖p‖ := by linarith
  have hpπ : ‖p‖ ≤ Real.pi :=
    (pi_norm_le_iff_of_nonneg hpi.le).2 (fun l => abs_le.2 ((mem_brillouinBox_iff p).1 hp l))
  have hκ0 : κ ≠ 0 := by
    intro h
    simp [h] at hκ
  have hred : ∀ s ∈ Icc (-Real.pi) Real.pi, ‖p‖ / 2 ≤ ‖update p i s‖ →
      ContDiffAt ℝ N φ s ∧ ‖iteratedDeriv N φ s‖ ≤ 32 * B * (‖p‖ ^ 5)⁻¹ := by
    intro s hs hn
    have hqb : update p i s ∈ brillouinBox := by
      rw [mem_brillouinBox_iff]
      intro l
      by_cases hl : l = i
      · subst hl
        simpa using hs
      · simpa [update_of_ne hl] using (mem_brillouinBox_iff p).1 hp l
    have hq0 : update p i s ≠ 0 := by
      intro h
      rw [h] at hn
      simp at hn
      linarith
    refine ⟨ContDiffAt.comp s (hsm N _ hqb hq0) (contDiff_update _ p i).contDiffAt, ?_⟩
    have h1 := hN _ hqb hq0
    have e : (fun t => a (update (update p i s) i t)) = φ := by
      funext t
      simp [hφ]
    have e2 : update p i s i = s := by simp
    rw [e, e2] at h1
    refine h1.trans ?_
    have h3 : (‖p‖ / 2) ^ 5 ≤ ‖update p i s‖ ^ 5 := by gcongr
    have h4 : (‖update p i s‖ ^ 5)⁻¹ ≤ ((‖p‖ / 2) ^ 5)⁻¹ := inv_anti₀ (by positivity) h3
    have h5 : ((‖p‖ / 2) ^ 5)⁻¹ = 32 * (‖p‖ ^ 5)⁻¹ := by
      field_simp
      norm_num
    calc B * (‖update p i s‖ ^ 5)⁻¹ ≤ B * (32 * (‖p‖ ^ 5)⁻¹) :=
          mul_le_mul_of_nonneg_left (h5 ▸ h4) hB
      _ = _ := by ring
  have hline : ∀ s ∈ Icc (p i) (p i + N * h),
      ContDiffAt ℝ N φ s ∧ ‖iteratedDeriv N φ s‖ ≤ 32 * B * (‖p‖ ^ 5)⁻¹ := by
    intro s hs
    have hpib := (mem_brillouinBox_iff p).1 hp i
    by_cases hc : s ≤ Real.pi
    · refine hred s ⟨by linarith [hs.1, hpib.1], hc⟩ ?_
      have hd : ‖p - update p i s‖ ≤ N * h := by
        rw [pi_norm_le_iff_of_nonneg hNh0]
        intro l
        by_cases hl : l = i
        · subst hl
          simp only [Pi.sub_apply, update_self, Real.norm_eq_abs]
          rw [abs_le]
          constructor <;> linarith [hs.1, hs.2]
        · simpa [update_of_ne hl] using hNh0
      have h7 : ‖p‖ ≤ ‖p - update p i s‖ + ‖update p i s‖ := by
        have := norm_add_le (p - update p i s) (update p i s)
        simpa using this
      linarith
    · have hc' : Real.pi < s := not_le.1 hc
      have hs' : s - 2 * Real.pi ∈ Icc (-Real.pi) Real.pi := by
        constructor <;> linarith [hs.2, hpib.2]
      have hn : ‖p‖ / 2 ≤ ‖update p i (s - 2 * Real.pi)‖ := by
        have h8 := norm_le_pi_norm (update p i (s - 2 * Real.pi)) i
        simp only [update_self, Real.norm_eq_abs] at h8
        have h9 : Real.pi / 2 ≤ |s - 2 * Real.pi| := by
          rw [abs_of_nonpos (by linarith [hs.2, hpib.2])]
          linarith [hs.2, hpib.2]
        linarith
      obtain ⟨c1, c2⟩ := hred _ hs' hn
      have hφs : φ = fun t => κ⁻¹ * φ (t - 2 * Real.pi) := by
        funext t
        have h10 := hQ (update p i (t - 2 * Real.pi))
        rw [update_add_single, sub_add_cancel] at h10
        simp only [hφ]
        rw [← h10]
        field_simp
      have c0 : ContDiffAt ℝ N (fun t => φ (t - 2 * Real.pi)) s :=
        ContDiffAt.comp (g := φ) (f := fun t : ℝ => t - 2 * Real.pi) s c1
          (contDiffAt_id.sub contDiffAt_const)
      have c1' : ContDiffAt ℝ N (fun t => κ⁻¹ * φ (t - 2 * Real.pi)) s :=
        contDiffAt_const.mul c0
      have e : iteratedDeriv N φ s = κ⁻¹ * iteratedDeriv N φ (s - 2 * Real.pi) := by
        conv_lhs => rw [hφs]
        rw [iteratedDeriv_const_mul_field κ⁻¹ (fun t => φ (t - 2 * Real.pi)),
          iteratedDeriv_comp_sub_const]
      refine ⟨hφs ▸ c1', ?_⟩
      rw [e, norm_mul, norm_inv, hκ, inv_one, one_mul]
      exact c2
  have e1 := iterate_fwdDiff_update p i h N a (p i)
  rw [update_eq_self] at e1
  rw [e1]
  have key := norm_iterate_fwdDiff_le h h0 N (fun j => iteratedDeriv j φ) (p i) (32 * B * (‖p‖ ^ 5)⁻¹)
    (fun j hj s hs => hasDerivAt_iteratedDeriv_of_contDiffAt φ s N j hj (hline s hs).1)
    (fun s hs => (hline s hs).2)
  simpa [iteratedDeriv_zero] using key
private lemma norm_le_sqrt_sum (x : Fin 4 → ℝ) : ‖x‖ ≤ Real.sqrt (∑ l, x l ^ 2) := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
private lemma sqrt_sum_le (x : Fin 4 → ℝ) : Real.sqrt (∑ l, x l ^ 2) ≤ 2 * ‖x‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
private lemma integrableOn_brillouinBox_of_bound (n : ℕ) (hn : 1 ≤ n) (B₀ : ℝ) (a : (Fin 4 → ℝ) → ℂ)
    (hcont : ∀ p : Fin 4 → ℝ, p ∈ brillouinBox → p ≠ 0 → ContinuousAt a p)
    (h0b : ∀ p : Fin 4 → ℝ, p ∈ brillouinBox → p ≠ 0 → ‖a p‖ ≤ B₀ * ‖p‖ ^ ((n : ℤ) - 4)) :
    IntegrableOn a brillouinBox := by
  have hsub : brillouinBox ⊆ closedBall (0 : Fin 4 → ℝ) Real.pi := by
    intro p hp
    rw [mem_closedBall_zero_iff]
    exact (pi_norm_le_iff_of_nonneg Real.pi_pos.le).2
      (fun l => abs_le.2 ((mem_brillouinBox_iff p).1 hp l))
  have hg := ((integral_norm_zpow_closedBall n hn Real.pi Real.pi_pos).1.mono_set hsub).const_mul B₀
  have hc : ContinuousOn a (brillouinBox \ {0}) := fun p hp =>
    (hcont p hp.1 hp.2).continuousWithinAt
  have hm : AEStronglyMeasurable a (volume.restrict brillouinBox) := by
    have h1 : AEStronglyMeasurable a (volume.restrict (brillouinBox \ {0})) :=
      hc.aestronglyMeasurable (measurableSet_brillouinBox.diff (measurableSet_singleton 0))
    rwa [Measure.restrict_congr_set
      (sdiff_null_ae_eq_self (measure_singleton (0 : Fin 4 → ℝ)))] at h1
  refine Integrable.mono' hg hm ?_
  rw [ae_restrict_iff' measurableSet_brillouinBox]
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : Fin 4 → ℝ))] with q hq hqs
  exact h0b q hqs hq
private lemma integral_norm_closedBall_le (n : ℕ) (hn : 1 ≤ n) (B₀ : ℝ) (a : (Fin 4 → ℝ) → ℂ)
    (hI : IntegrableOn a brillouinBox)
    (h0b : ∀ p : Fin 4 → ℝ, p ∈ brillouinBox → p ≠ 0 → ‖a p‖ ≤ B₀ * ‖p‖ ^ ((n : ℤ) - 4))
    (R : ℝ) (hR : 0 < R) (hRπ : R ≤ Real.pi) :
    ∫ p in closedBall (0 : Fin 4 → ℝ) R, ‖a p‖ ≤
      B₀ * (4 * (volume : Measure (Fin 4 → ℝ)).real (ball 0 1) * (R ^ n / n)) := by
  obtain ⟨g1, g2⟩ := integral_norm_zpow_closedBall n hn R hR
  rw [← g2, ← integral_const_mul]
  refine setIntegral_mono_on_ae (hI.mono_set (closedBall_subset_brillouinBox R hRπ)).norm
    (g1.const_mul B₀) measurableSet_closedBall ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : Fin 4 → ℝ))] with q hq hqs
  exact h0b q (closedBall_subset_brillouinBox R hRπ hqs) hq
private lemma exp_I_mul_half_period (x : ℝ) (hx : x ≠ 0) :
    Complex.exp (Complex.I * (((Real.pi / |x|) * x : ℝ) : ℂ)) = -1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · have : (Real.pi / |x|) * x = -Real.pi := by
      rw [abs_of_neg h]
      field_simp
    rw [this]
    push_cast
    rw [mul_neg, Complex.exp_neg, mul_comm, Complex.exp_pi_mul_I]
    norm_num
  · have : (Real.pi / |x|) * x = Real.pi := by
      rw [abs_of_pos h]
      field_simp
    rw [this, mul_comm, Complex.exp_pi_mul_I]
private lemma norm_integral_planeWave_le (n : ℕ) (hn : 1 ≤ n) (B₀ B₁ : ℝ) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (a : (Fin 4 → ℝ) → ℂ) (w : Fin 4 → ℝ) (i : Fin 4)
    (hQ : IsQuasiPeriodic (Complex.exp (Complex.I * ((2 * Real.pi * w i : ℝ) : ℂ))) i a)
    (hsm : ∀ (j : ℕ) (p : Fin 4 → ℝ), p ∈ brillouinBox → p ≠ 0 → ContDiffAt ℝ j a p)
    (hI : IntegrableOn a brillouinBox)
    (h0b : ∀ p : Fin 4 → ℝ, p ∈ brillouinBox → p ≠ 0 → ‖a p‖ ≤ B₀ * ‖p‖ ^ ((n : ℤ) - 4))
    (hN : ∀ p : Fin 4 → ℝ, p ∈ brillouinBox → p ≠ 0 →
      ‖iteratedDeriv (n + 1) (fun t : ℝ => a (update p i t)) (p i)‖ ≤ B₁ * (‖p‖ ^ 5)⁻¹)
    (hw : 8 * ((n : ℝ) + 1) ≤ |w i|) :
    ‖∫ p in brillouinBox, a p * planeWave w p‖ ≤
      (B₀ * (4 * (volume : Measure (Fin 4 → ℝ)).real (ball 0 1)) * (3 * ((n : ℝ) + 1)) ^ n +
        32 * B₁ * (4 * (volume : Measure (Fin 4 → ℝ)).real (ball 0 1))) * (Real.pi / |w i|) ^ n := by
  set V : ℝ := 4 * (volume : Measure (Fin 4 → ℝ)).real (ball 0 1) with hV
  have hpi := Real.pi_pos
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hwpos : 0 < |w i| := by linarith
  have hw0 : w i ≠ 0 := abs_pos.1 hwpos
  set h : ℝ := Real.pi / |w i| with hh
  have hpos : 0 < h := by positivity
  set N : ℕ := n + 1 with hNdef
  have hNr : (N : ℝ) = (n : ℝ) + 1 := by simp [hNdef]
  have hNh : (N : ℝ) * h ≤ Real.pi / 8 := by
    rw [hNr, hh, mul_div_assoc', div_le_div_iff₀ hwpos (by norm_num)]
    nlinarith
  have hN1 : (1 : ℝ) ≤ N := by rw [hNr]; linarith
  have hh1 : h ≤ Real.pi / 8 := by nlinarith
  have hh2 : h ≤ 2 * Real.pi := by linarith
  obtain ⟨-, d2, d3⟩ := iterate_fwdDiff_quasiPeriodic_integral w i h hpos.le hh2 (exp_I_mul_half_period (w i) hw0) a hQ hI N
  set Δ : (Fin 4 → ℝ) → ℂ := (fwdDiff (Pi.single i h))^[N] a with hΔ
  set ρ : ℝ := 2 * ((N : ℝ) * h) with hρ
  have hρpos : 0 < ρ := by positivity
  have hR : ρ + N * h ≤ Real.pi := by
    simp only [hρ]
    linarith
  have hρπ : ρ ≤ Real.pi := by simp only [hρ]; linarith
  have hsubρ := closedBall_subset_brillouinBox ρ hρπ
  obtain ⟨n1, n2⟩ := integral_norm_iterate_fwdDiff_closedBall_le i h hpos.le N ρ a (hI.mono_set (closedBall_subset_brillouinBox _ hR))
  have n3 := integral_norm_closedBall_le n hn B₀ a hI h0b (ρ + N * h) (by positivity) hR
  have near : ∫ p in closedBall (0 : Fin 4 → ℝ) ρ, ‖Δ p‖ ≤
      2 ^ N * (B₀ * (V * ((ρ + N * h) ^ n / n))) :=
    n2.trans (by gcongr)
  obtain ⟨f1, f2⟩ := integral_inv_pow_five_compl_closedBall ρ hρpos
  have hsubc : brillouinBox \ closedBall (0 : Fin 4 → ℝ) ρ ⊆ (closedBall 0 ρ)ᶜ := fun p hp => hp.2
  have far : ∫ p in brillouinBox \ closedBall (0 : Fin 4 → ℝ) ρ, ‖Δ p‖ ≤
      h ^ N * (32 * B₁) * (V * ρ⁻¹) := by
    rw [← f2]
    have g1 : IntegrableOn (fun q : Fin 4 → ℝ => h ^ N * (32 * B₁) * (‖q‖ ^ 5)⁻¹)
        (closedBall 0 ρ)ᶜ := f1.const_mul _
    calc ∫ p in brillouinBox \ closedBall (0 : Fin 4 → ℝ) ρ, ‖Δ p‖
        ≤ ∫ p in brillouinBox \ closedBall (0 : Fin 4 → ℝ) ρ, h ^ N * (32 * B₁) * (‖p‖ ^ 5)⁻¹ := by
          refine setIntegral_mono_on (d2.mono_set Set.sdiff_subset).norm (g1.mono_set hsubc)
            (measurableSet_brillouinBox.diff measurableSet_closedBall) ?_
          intro p hp
          have hp2 : ρ < ‖p‖ := by
            have := hp.2
            rwa [mem_closedBall_zero_iff, not_le] at this
          have := norm_iterate_fwdDiff_le_far a _ (by rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _) i hQ hsm
            N B₁ hB₁ hN h hpos.le hNh p hp.1 hp2
          calc ‖Δ p‖ ≤ h ^ N * (32 * B₁ * (‖p‖ ^ 5)⁻¹) := this
            _ = _ := by ring
      _ ≤ ∫ p in (closedBall (0 : Fin 4 → ℝ) ρ)ᶜ, h ^ N * (32 * B₁) * (‖p‖ ^ 5)⁻¹ := by
          refine setIntegral_mono_set g1 (Filter.Eventually.of_forall fun p => ?_)
            (LE.le.eventuallyLE hsubc)
          show (0 : ℝ) ≤ _
          positivity
      _ = _ := integral_const_mul _ _
  have hsplit : ∫ p in brillouinBox, ‖Δ p‖ =
      (∫ p in closedBall (0 : Fin 4 → ℝ) ρ, ‖Δ p‖) +
        ∫ p in brillouinBox \ closedBall (0 : Fin 4 → ℝ) ρ, ‖Δ p‖ := by
    have := integral_inter_add_sdiff (μ := volume) (f := fun p => ‖Δ p‖) (s := brillouinBox)
      (t := closedBall (0 : Fin 4 → ℝ) ρ) measurableSet_closedBall d2.norm
    rw [inter_eq_right.2 hsubρ] at this
    exact this.symm
  have htop : ‖∫ p in brillouinBox, Δ p * planeWave w p‖ ≤ ∫ p in brillouinBox, ‖Δ p‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp [norm_planeWave]
  rw [d3, norm_mul, norm_pow, norm_neg] at htop
  simp only [Complex.norm_ofNat] at htop
  set X : ℝ := ‖∫ p in brillouinBox, a p * planeWave w p‖ with hX
  have htotal : 2 ^ N * X ≤ 2 ^ N * (B₀ * (V * ((ρ + N * h) ^ n / n))) +
      h ^ N * (32 * B₁) * (V * ρ⁻¹) := by
    rw [hsplit] at htop
    linarith
  have e1 : ρ + N * h = 3 * (n + 1) * h := by
    simp only [hρ]
    rw [hNr]
    ring
  have e2 : h ^ N * ρ⁻¹ ≤ h ^ n := by
    have hNne : (N : ℝ) ≠ 0 := by linarith
    have hp : h ^ N = h ^ n * h := pow_succ h n
    have : h ^ N * ρ⁻¹ = h ^ n * (2 * (N : ℝ))⁻¹ := by
      rw [hp, hρ]
      field_simp
    rw [this]
    have h8 : (2 * (N : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    exact mul_le_of_le_one_right (pow_pos hpos n).le h8
  have e3 : (ρ + N * h) ^ n / n ≤ (3 * ((n : ℝ) + 1)) ^ n * h ^ n := by
    rw [e1, mul_pow]
    exact div_le_self (by positivity) hn0
  have h2N : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have e4 : 2 ^ N * X ≤ 2 ^ N * (B₀ * (V * ((3 * ((n : ℝ) + 1)) ^ n * h ^ n))) +
      32 * B₁ * V * h ^ n := by
    refine htotal.trans ?_
    have q1 : B₀ * (V * ((ρ + N * h) ^ n / n)) ≤ B₀ * (V * ((3 * ((n : ℝ) + 1)) ^ n * h ^ n)) := by
      gcongr
    have q2 : h ^ N * (32 * B₁) * (V * ρ⁻¹) ≤ 32 * B₁ * V * h ^ n := by
      calc h ^ N * (32 * B₁) * (V * ρ⁻¹) = 32 * B₁ * V * (h ^ N * ρ⁻¹) := by ring
        _ ≤ _ := by gcongr
    have q3 := mul_le_mul_of_nonneg_left q1 (by positivity : (0 : ℝ) ≤ 2 ^ N)
    linarith
  have e5 : 0 ≤ 32 * B₁ * V * h ^ n := by positivity
  have e6 : 2 ^ N * X ≤ 2 ^ N * (B₀ * (V * ((3 * ((n : ℝ) + 1)) ^ n * h ^ n)) + 32 * B₁ * V * h ^ n) := by
    rw [mul_add]
    nlinarith
  have e7 := le_of_mul_le_mul_left e6 (by positivity)
  calc X ≤ _ := e7
    _ = _ := by ring
private theorem symbolKernelDecay_aux (m : ℤ) (Cj : ℕ → ℝ) (hm : -4 < m) : ∃ C : ℝ,
    ∀ (a : (Fin 4 → ℝ) → ℂ) (w : Fin 4 → ℝ),
    (∀ (i : Fin 4) (p : Fin 4 → ℝ), a (p + Pi.single i (2 * Real.pi)) *
      Complex.exp (Complex.I * ((2 * Real.pi * w i : ℝ) : ℂ)) = a p) →
    (∀ (j : ℕ) (p : Fin 4 → ℝ), p ∈ brillouinBox → p ≠ 0 → ContDiffAt ℝ j a p) →
    (∀ (l : Fin 4) (j : ℕ) (p : Fin 4 → ℝ), p ∈ brillouinBox → p ≠ 0 →
      ‖iteratedDeriv j (fun t : ℝ => a (Function.update p l t)) (p l)‖ ≤
        Cj j * Real.sqrt (momentumNormSq p) ^ (m - (j : ℤ))) →
    ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ ^ 4 * ∫ p in brillouinBox, a p *
        Complex.exp (Complex.I * ((∑ l, p l * w l : ℝ) : ℂ))‖ ≤
      C * (1 + Real.sqrt (∑ l, w l ^ 2)) ^ (-4 - m) := by
  obtain ⟨n, hnm⟩ : ∃ n : ℕ, (n : ℤ) = m + 4 := ⟨(m + 4).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hn : 1 ≤ n := by omega
  have hm' : m = (n : ℤ) - 4 := by omega
  set V : ℝ := 4 * (volume : Measure (Fin 4 → ℝ)).real (ball 0 1) with hV
  have hpi := Real.pi_pos
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set B₀ : ℝ := |Cj 0| * 2 ^ n with hB₀d
  set B₁ : ℝ := |Cj (n + 1)| with hB₁d
  have hB₀ : 0 ≤ B₀ := by positivity
  have hB₁ : 0 ≤ B₁ := abs_nonneg _
  set A : ℝ := B₀ * V * (3 * ((n : ℝ) + 1)) ^ n + 32 * B₁ * V with hA
  set S : ℝ := B₀ * (V * Real.pi ^ n) with hS
  have hS0 : 0 ≤ S := by positivity
  refine ⟨A * (3 * Real.pi) ^ n + S * (1 + 16 * ((n : ℝ) + 1)) ^ n, ?_⟩
  intro a w hper hsm hder
  have h0b : ∀ p : Fin 4 → ℝ, p ∈ brillouinBox → p ≠ 0 → ‖a p‖ ≤ B₀ * ‖p‖ ^ ((n : ℤ) - 4) := by
    intro p hp hp0
    have h1 := hder 0 0 p hp hp0
    simp only [iteratedDeriv_zero, update_eq_self, Nat.cast_zero, sub_zero] at h1
    have hs1 : ‖p‖ ≤ Real.sqrt (momentumNormSq p) := norm_le_sqrt_sum p
    have hs2 : Real.sqrt (momentumNormSq p) ≤ 2 * ‖p‖ := sqrt_sum_le p
    have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp0
    set e := Real.sqrt (momentumNormSq p) with he
    have he0 : 0 < e := by linarith
    have key : e ^ m ≤ 2 ^ n * ‖p‖ ^ m := by
      rcases le_or_gt 0 m with hm0 | hm0
      · have k1 : e ^ m ≤ (2 * ‖p‖) ^ m := zpow_le_zpow_left₀ hm0 he0.le hs2
        have k2 : (2 : ℝ) ^ m ≤ 2 ^ n := by
          rw [← zpow_natCast]
          exact zpow_le_zpow_right₀ (by norm_num) (by omega)
        rw [mul_zpow] at k1
        refine k1.trans ?_
        gcongr
      · have k1 : e ^ m ≤ ‖p‖ ^ m := by
          have k2 : ‖p‖ ^ (-m) ≤ e ^ (-m) := zpow_le_zpow_left₀ (by omega) hpn.le hs1
          have k3 := inv_anti₀ (by positivity) k2
          simpa [zpow_neg] using k3
        have k4 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        have k5 : 0 < ‖p‖ ^ m := zpow_pos hpn m
        nlinarith
    calc ‖a p‖ ≤ Cj 0 * e ^ m := h1
      _ ≤ |Cj 0| * e ^ m := by gcongr; exact le_abs_self _
      _ ≤ |Cj 0| * (2 ^ n * ‖p‖ ^ m) := by gcongr
      _ = B₀ * ‖p‖ ^ ((n : ℤ) - 4) := by rw [hB₀d, hm']; ring
  have hNb : ∀ (i : Fin 4) (p : Fin 4 → ℝ), p ∈ brillouinBox → p ≠ 0 →
      ‖iteratedDeriv (n + 1) (fun t : ℝ => a (update p i t)) (p i)‖ ≤ B₁ * (‖p‖ ^ 5)⁻¹ := by
    intro i p hp hp0
    have h1 := hder i (n + 1) p hp hp0
    have hex : m - ((n + 1 : ℕ) : ℤ) = -5 := by push_cast; omega
    rw [hex] at h1
    have hs1 : ‖p‖ ≤ Real.sqrt (momentumNormSq p) := norm_le_sqrt_sum p
    have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp0
    set e := Real.sqrt (momentumNormSq p) with he
    have k1 : e ^ (-5 : ℤ) ≤ (‖p‖ ^ 5)⁻¹ := by
      have k2 : ‖p‖ ^ 5 ≤ e ^ 5 := by gcongr
      have k3 := inv_anti₀ (by positivity) k2
      have : e ^ (-5 : ℤ) = (e ^ 5)⁻¹ := by
        rw [zpow_neg]
        norm_cast
      rw [this]
      exact k3
    calc _ ≤ Cj (n + 1) * e ^ (-5 : ℤ) := h1
      _ ≤ |Cj (n + 1)| * e ^ (-5 : ℤ) := by gcongr; exact le_abs_self _
      _ ≤ B₁ * (‖p‖ ^ 5)⁻¹ := by gcongr
  have hI : IntegrableOn a brillouinBox :=
    integrableOn_brillouinBox_of_bound n hn B₀ a (fun p hp hp0 => (hsm 0 p hp hp0).continuousAt) h0b
  obtain ⟨i, hi⟩ := Finite.exists_max (fun l => |w l|)
  have hwn : ‖w‖ ≤ |w i| :=
    (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 (fun l => by simpa using hi l)
  set W : ℝ := Real.sqrt (∑ l, w l ^ 2) with hW
  have hW2 : W ≤ 2 * |w i| := (sqrt_sum_le w).trans (by linarith)
  have hexp : (-4 - m) = -(n : ℤ) := by omega
  rw [hexp, zpow_neg, zpow_natCast]
  set Y : ℝ := ((1 + W) ^ n)⁻¹ with hY
  have hleft : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ ^ 4 * ∫ p in brillouinBox, a p *
      Complex.exp (Complex.I * ((∑ l, p l * w l : ℝ) : ℂ))‖ ≤
      ‖∫ p in brillouinBox, a p * planeWave w p‖ := by
    rw [norm_mul]
    have h2 : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ ^ 4‖ ≤ 1 := by
      rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
      exact pow_le_one₀ (by positivity) this
    exact mul_le_of_le_one_left (norm_nonneg _) h2
  refine hleft.trans ?_
  by_cases hbig : 8 * ((n : ℝ) + 1) ≤ |w i|
  · have hest := norm_integral_planeWave_le n hn B₀ B₁ hB₀ hB₁ a w i (hper i) hsm hI h0b (hNb i) hbig
    have hwpos : 0 < |w i| := by linarith
    have h3 : Real.pi / |w i| ≤ 3 * Real.pi * (1 + W)⁻¹ := by
      rw [div_le_iff₀ hwpos]
      have : 1 + W ≤ 3 * |w i| := by linarith
      have h4 : (1 + W)⁻¹ * (1 + W) = 1 := inv_mul_cancel₀ (by positivity)
      have h5 : 0 < (1 + W)⁻¹ := by positivity
      have h6 : 1 ≤ (1 + W)⁻¹ * (3 * |w i|) := by
        calc 1 = (1 + W)⁻¹ * (1 + W) := h4.symm
          _ ≤ _ := by gcongr
      calc Real.pi = Real.pi * 1 := by ring
        _ ≤ Real.pi * ((1 + W)⁻¹ * (3 * |w i|)) := by gcongr
        _ = _ := by ring
    have h6 : (Real.pi / |w i|) ^ n ≤ (3 * Real.pi) ^ n * Y := by
      calc (Real.pi / |w i|) ^ n ≤ (3 * Real.pi * (1 + W)⁻¹) ^ n := by gcongr
        _ = _ := by rw [mul_pow, inv_pow]
    have h7 : 0 ≤ S * (1 + 16 * ((n : ℝ) + 1)) ^ n * Y := by positivity
    calc _ ≤ A * (Real.pi / |w i|) ^ n := hest
      _ ≤ A * ((3 * Real.pi) ^ n * Y) := by gcongr
      _ ≤ (A * (3 * Real.pi) ^ n + S * (1 + 16 * ((n : ℝ) + 1)) ^ n) * Y := by nlinarith
  · have hsmall : |w i| < 8 * ((n : ℝ) + 1) := not_le.1 hbig
    have h1 : ‖∫ p in brillouinBox, a p * planeWave w p‖ ≤ S := by
      refine (norm_integral_le_integral_norm _).trans ?_
      simp only [norm_mul, norm_planeWave, mul_one]
      have hsub : brillouinBox ⊆ closedBall (0 : Fin 4 → ℝ) Real.pi := by
        intro p hp
        rw [mem_closedBall_zero_iff]
        exact (pi_norm_le_iff_of_nonneg hpi.le).2 (fun l => abs_le.2 ((mem_brillouinBox_iff p).1 hp l))
      have h2 : closedBall (0 : Fin 4 → ℝ) Real.pi ⊆ brillouinBox := closedBall_subset_brillouinBox _ le_rfl
      have h3 : (closedBall (0 : Fin 4 → ℝ) Real.pi) = brillouinBox := Subset.antisymm h2 hsub
      have h4 := integral_norm_closedBall_le n hn B₀ a hI h0b Real.pi hpi le_rfl
      rw [h3] at h4
      refine h4.trans ?_
      have h5 : Real.pi ^ n / n ≤ Real.pi ^ n := div_le_self (by positivity) hn0
      simp only [hS]
      gcongr
    have h8 : (1 + W) ^ n ≤ (1 + 16 * ((n : ℝ) + 1)) ^ n := by
      have : 1 + W ≤ 1 + 16 * ((n : ℝ) + 1) := by linarith
      gcongr
    have h9 : 1 ≤ (1 + 16 * ((n : ℝ) + 1)) ^ n * Y := by
      rw [hY, ← div_eq_mul_inv, one_le_div (by positivity)]
      exact h8
    have h10 : 0 ≤ A * (3 * Real.pi) ^ n * Y := by positivity
    have h11 : S ≤ S * ((1 + 16 * ((n : ℝ) + 1)) ^ n * Y) := le_mul_of_one_le_right hS0 h9
    calc _ ≤ S := h1
      _ ≤ (A * (3 * Real.pi) ^ n + S * (1 + 16 * ((n : ℝ) + 1)) ^ n) * Y := by nlinarith
theorem symbolKernelDecay : symbolKernelDecayStatement :=
  fun m Cj hm => symbolKernelDecay_aux m Cj hm
end LimitForms
end YangMills.Construction
end
