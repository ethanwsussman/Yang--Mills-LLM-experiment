import YangMills.Construction.PeriodicOperators.NormOfTheSymbolProof
import YangMills.Construction.LawByMomentsOfTheFlow.FarLevelNearTheScale
import YangMills.Construction.LawByMomentsOfTheFlow.GapOfTheSupportsFromBelow
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAlongTheTelescopeProof
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAtTheLastFarLevelInALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.ScoresInALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.ScoresOfAStepAreReadFromAbove
import YangMills.Construction.LawByMomentsOfTheFlow.TheFlowAboveTheWindow
import YangMills.Construction.LawByMomentsOfTheFlow.VariablesAreFarAtLiveStates
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open MomentMethod LevelTestFunctions TestFunctions TorusLumps TorusFields WeightedResponses HullTrees ChainNoise FreeEnergies RenormalizationStepParameters
section Moments
variable {T : TranslatedLaws}
private theorem add_pow_le_two_pow_mul (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (q : ℕ) : (x + y) ^ q ≤ 2 ^ q * x ^ q + 2 ^ q * y ^ q := by apply _root_.YangMills.SharedProofs.p63544 <;> assumption
private theorem aemeasurable_ofReal_pow {X : T.Family} (hX : TranslatedLaws.HasBoundedMoments X) (i : ℕ) (q : ℕ) (c : ℝ) :
    AEMeasurable (fun ω => ENNReal.ofReal (c * |X i ω| ^ q)) (T.μ i) :=
  ENNReal.measurable_ofReal.comp_aemeasurable (((hX.aemeasurable i).abs.pow_const q).const_mul c)
private theorem hasBoundedMoments_add {X Y : T.Family} (hX : TranslatedLaws.HasBoundedMoments X) (hY : TranslatedLaws.HasBoundedMoments Y) :
    TranslatedLaws.HasBoundedMoments (T := T) (fun i ω => X i ω + Y i ω) where
  aemeasurable i := (hX.aemeasurable i).add (hY.aemeasurable i)
  moment_bound q := by
    obtain ⟨C₁, h₁⟩ := hX.moment_bound q
    obtain ⟨C₂, h₂⟩ := hY.moment_bound q
    refine ⟨2 ^ q * |C₁| + 2 ^ q * |C₂|, fun i => ?_⟩
    have h2 : (0 : ℝ) ≤ 2 ^ q := by positivity
    have e : ∀ Z : T.Family, ∫⁻ ω, ENNReal.ofReal (2 ^ q * |Z i ω| ^ q) ∂(T.μ i) =
        ENNReal.ofReal (2 ^ q) * ∫⁻ ω, ENNReal.ofReal (|Z i ω| ^ q) ∂(T.μ i) := by
      intro Z
      simp_rw [ENNReal.ofReal_mul h2]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    calc ∫⁻ ω, ENNReal.ofReal (|X i ω + Y i ω| ^ q) ∂(T.μ i)
        ≤ ∫⁻ ω, (ENNReal.ofReal (2 ^ q * |X i ω| ^ q) + ENNReal.ofReal (2 ^ q * |Y i ω| ^ q)) ∂(T.μ i) := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          exact (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) q).trans
            (add_pow_le_two_pow_mul _ _ (abs_nonneg _) (abs_nonneg _) q)
      _ = ∫⁻ ω, ENNReal.ofReal (2 ^ q * |X i ω| ^ q) ∂(T.μ i) + ∫⁻ ω, ENNReal.ofReal (2 ^ q * |Y i ω| ^ q) ∂(T.μ i) :=
          lintegral_add_left' (aemeasurable_ofReal_pow hX i q _) _
      _ = ENNReal.ofReal (2 ^ q) * ∫⁻ ω, ENNReal.ofReal (|X i ω| ^ q) ∂(T.μ i) +
            ENNReal.ofReal (2 ^ q) * ∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ q) ∂(T.μ i) := by rw [e X, e Y]
      _ ≤ ENNReal.ofReal (2 ^ q) * ENNReal.ofReal |C₁| + ENNReal.ofReal (2 ^ q) * ENNReal.ofReal |C₂| := by
          gcongr
          · exact (h₁ i).trans (ENNReal.ofReal_le_ofReal (le_abs_self _))
          · exact (h₂ i).trans (ENNReal.ofReal_le_ofReal (le_abs_self _))
      _ = _ := by
          rw [← ENNReal.ofReal_mul h2, ← ENNReal.ofReal_mul h2,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
private theorem hasBoundedMoments_const (hT : T.IsPreserving) (a : ℕ → ℝ) (b : ℝ) (ha : ∀ i, |a i| ≤ b) :
    TranslatedLaws.HasBoundedMoments (T := T) (fun i _ => a i) where
  aemeasurable _ := aemeasurable_const
  moment_bound q := by
    refine ⟨b ^ q, fun i => ?_⟩
    have := hT.isProbability i
    calc ∫⁻ _, ENNReal.ofReal (|a i| ^ q) ∂(T.μ i) = ENNReal.ofReal (|a i| ^ q) := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) (ha i) q)
private theorem hasBoundedMoments_sum (hT : T.IsPreserving) {ι : Type} (s : Finset ι) {X : ι → T.Family}
    (hX : ∀ a ∈ s, TranslatedLaws.HasBoundedMoments (X a)) :
    TranslatedLaws.HasBoundedMoments (T := T) (fun i ω => ∑ a ∈ s, X a i ω) := by apply _root_.YangMills.SharedProofs.p71872 <;> assumption
private theorem hasBoundedMoments_prod (hT : T.IsPreserving) {ι : Type} (s : Finset ι) {X : ι → T.Family}
    (hX : ∀ a ∈ s, TranslatedLaws.HasBoundedMoments (X a)) :
    TranslatedLaws.HasBoundedMoments (T := T) (fun i ω => ∏ a ∈ s, X a i ω) := by apply _root_.YangMills.SharedProofs.p24142 <;> assumption
end Moments
section Limit
variable {T : TranslatedLaws} {J : Type} {X : J → T.Family} {P : Measure (TranslateValues J)}
private theorem ae_le_of_eventually_le (hL : IsJointLimitLaw T X P) {I : Type} [Fintype I] (ι : I → J) (φ : (I → ℝ) → ℝ) (hφ : Continuous φ)
    (h : ∀ᶠ i in atTop, ∀ᵐ ω ∂(T.μ i), φ (fun c => X (ι c) i ω) ≤ 0) :
    ∀ᵐ v ∂P, φ (fun c => v (ι c, 0)) ≤ 0 := by apply _root_.YangMills.SharedProofs.p13419 <;> assumption
private theorem ae_eq_of_eventually_eq (hL : IsJointLimitLaw T X P) {I : Type} [Fintype I] (ι : I → J) (φ ψ : (I → ℝ) → ℝ) (hφ : Continuous φ)
    (hψ : Continuous ψ) (h : ∀ᶠ i in atTop, ∀ᵐ ω ∂(T.μ i), φ (fun c => X (ι c) i ω) = ψ (fun c => X (ι c) i ω)) :
    ∀ᵐ v ∂P, φ (fun c => v (ι c, 0)) = ψ (fun c => v (ι c, 0)) := by
  have h1 := ae_le_of_eventually_le hL ι (fun x => |φ x - ψ x|) (hφ.sub hψ).abs (h.mono fun i hi => by
    filter_upwards [hi] with ω hω
    simp [hω])
  filter_upwards [h1] with v hv
  have := abs_nonpos_iff.mp hv
  linarith
private theorem ae_eq_zero_of_tendsto (hL : IsJointLimitLaw T X P) (j : J) (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (h : ∀ i ω, X j i ω = a i) (hT : T.IsPreserving) : ∀ᵐ v ∂P, v (j, 0) = 0 := by
  have hP := hL.isProbability
  obtain ⟨G, hGd⟩ : ∃ G : (Fin 1 → ℝ) → ℝ, G = fun w => min 1 |w 0| := ⟨_, rfl⟩
  have hG : Continuous G := by
    rw [hGd]
    exact continuous_const.min (continuous_apply 0).abs
  have hG0 : ∀ w, 0 ≤ G w := fun w => by
    rw [hGd]
    exact le_min zero_le_one (abs_nonneg _)
  have hG1 : ∀ w, G w ≤ 1 := fun w => by
    rw [hGd]
    exact min_le_left _ _
  have hlim := hL.tendsto 1 (fun _ => (j, 0)) G hG ⟨1, fun w => by rw [abs_of_nonneg (hG0 w)]; exact hG1 w⟩
  have hval : ∀ i, ∫ ω, G (fun _ => TranslatedLaws.translate (X j) 0 i ω) ∂(T.μ i) = min 1 |a i| := fun i => by
    have := hT.isProbability i
    have e : ∀ ω, G (fun _ => TranslatedLaws.translate (X j) 0 i ω) = min 1 |a i| := fun ω => by
      rw [hGd]
      show min 1 |X j i ω| = _
      rw [h]
    simp [e]
  simp_rw [hval] at hlim
  have h0 : Tendsto (fun i => min 1 |a i|) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).min ha.abs
    simpa using this
  have hz := tendsto_nhds_unique hlim h0
  have hm : Measurable fun v : TranslateValues J => G (fun _ => v (j, 0)) :=
    hG.measurable.comp (measurable_pi_lambda _ fun _ => measurable_pi_apply _)
  have hint : Integrable (fun v : TranslateValues J => G (fun _ => v (j, 0))) P :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 _)]
      exact hG1 _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun v => hG0 _) hint).1 hz
  filter_upwards [hae] with v hv
  have hv' : G (fun _ => v (j, 0)) = 0 := hv
  rw [hGd] at hv'
  simp only at hv'
  rcases min_choice (1 : ℝ) |v (j, 0)| with h1 | h1
  · rw [h1] at hv'
    norm_num at hv'
  · rw [h1] at hv'
    exact abs_eq_zero.mp hv'
private theorem shiftInvariantSigma_le : shiftInvariantSigma J ≤ (inferInstance : MeasurableSpace (TranslateValues J)) := inf_le_right
private theorem abs_invariantCondExp_le [IsFiniteMeasure P] {f g : TranslateValues J → ℝ} (hf : Integrable f P) (hg : Integrable g P)
    (h : ∀ᵐ v ∂P, |f v| ≤ g v) :
    ∀ᵐ v ∂P, |invariantCondExp P f v| ≤ invariantCondExp P g v := by
  have h1 : invariantCondExp P f ≤ᵐ[P] invariantCondExp P g := condExp_mono hf hg (h.mono fun v hv => (le_abs_self _).trans hv)
  have h2 : invariantCondExp P (-f) ≤ᵐ[P] invariantCondExp P g := condExp_mono hf.neg hg (h.mono fun v hv => (neg_le_abs _).trans hv)
  have h3 : invariantCondExp P (-f) =ᵐ[P] -invariantCondExp P f := condExp_neg f (shiftInvariantSigma J)
  filter_upwards [h1, h2, h3] with v a b c
  rw [c] at b
  exact abs_le.mpr ⟨by simpa using neg_le_of_neg_le b, a⟩
end Limit
section Numbers
private theorem linear_le_eps_pow_add (L : ℝ) (hL : 1 < L) (ε A : ℝ) (hε : 0 < ε) (hA : 0 ≤ A) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ m : ℕ, A * m ≤ ε * L ^ m + C₂ := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 1 hL
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (A + 1) by positivity))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨A * N, by positivity, fun m => ?_⟩
  have hLm : 0 < L ^ m := by positivity
  rcases Nat.lt_or_ge m N with h | h
  · have h1 : (m : ℝ) ≤ N := by exact_mod_cast h.le
    have hp : 0 ≤ ε * L ^ m := by positivity
    nlinarith
  · have h1 := hN m h
    rw [pow_one, div_lt_div_iff₀ hLm (by positivity)] at h1
    have hp : (0 : ℝ) ≤ A * N := by positivity
    nlinarith
abbrev _root_.YangMills.SharedProofs.p107442 := @linear_le_eps_pow_add
private theorem sum_half_pow_le_sub (s t : ℕ) (h : t ≤ s) :
    ∑ u ∈ Finset.range t, (1 / 2 : ℝ) ^ (s - u) ≤ (1 / 2 : ℝ) ^ (s - t) - (1 / 2 : ℝ) ^ s := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ]
    have h1 := ih (by omega)
    have h2 : (1 / 2 : ℝ) ^ (s - t) = (1 / 2) * (1 / 2 : ℝ) ^ (s - (t + 1)) := by
      have h3 : s - t = (s - (t + 1)) + 1 := by omega
      rw [h3, pow_succ]
      ring_nf
    linarith
abbrev _root_.YangMills.SharedProofs.p34912 := @sum_half_pow_le_sub
private theorem sum_half_pow_le_one (s t : ℕ) (h : t ≤ s) : ∑ u ∈ Finset.range t, (1 / 2 : ℝ) ^ (s - u) ≤ 1 := by
  have h5 := sum_half_pow_le_sub s t h
  have h6 : (1 / 2 : ℝ) ^ (s - t) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h7 : 0 ≤ (1 / 2 : ℝ) ^ s := by positivity
  linarith
private theorem sum_exp_terms_le_exp (L c rt E : ℝ) (hL : 2 ≤ L) (hc : 0 < c) (hrt : 0 < rt) (hE : 0 ≤ E) :
    ∃ ε W₀ : ℝ, 0 < ε ∧ 0 ≤ W₀ ∧ ∀ w : ℝ, W₀ ≤ w → ∀ (s t : ℕ) (D : ℕ → ℝ), t ≤ s →
      (∀ u < t, c * L ^ (s - u) - 12 ≤ D u) →
      (∀ u < t, L ^ (s - u) ≤ w → 2 ^ 10 * w ≤ D u) →
      ∑ u ∈ Finset.range t, Real.exp (E * Real.log L * ((s - u : ℕ) : ℝ)) * Real.exp (-(rt * D u / 2 ^ 8)) ≤
        Real.exp (-(ε * w)) := by
  have hL1 : 1 < L := by linarith
  have hlog : 0 < Real.log L := Real.log_pos hL1
  obtain ⟨γ, hγd⟩ : ∃ γ : ℝ, γ = rt * c / 2 ^ 8 := ⟨_, rfl⟩
  have hγ : 0 < γ := by
    rw [hγd]
    positivity
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = E * Real.log L + Real.log 2 := ⟨_, rfl⟩
  have hb : 0 ≤ b := by
    rw [hbd]
    positivity
  obtain ⟨C₃, hC₃, h3⟩ := linear_le_eps_pow_add L hL1 rt b hrt hb
  obtain ⟨C₄, hC₄, h4⟩ := linear_le_eps_pow_add L hL1 (γ / 4) b (by positivity) hb
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = min rt (γ / 4) := ⟨_, rfl⟩
  have hε : 0 < ε := by
    rw [hεd]
    exact lt_min hrt (by positivity)
  have hε1 : ε ≤ rt := by
    rw [hεd]
    exact min_le_left _ _
  have hε2 : ε ≤ γ / 4 := by
    rw [hεd]
    exact min_le_right _ _
  refine ⟨ε, max (C₃ / rt) ((12 * rt / 2 ^ 8 + C₄) / (γ / 2)), hε, le_max_of_le_left (by positivity), ?_⟩
  intro w hw s t D hts h1 h2
  have hw1 : C₃ / rt ≤ w := (le_max_left _ _).trans hw
  have hw2 : (12 * rt / 2 ^ 8 + C₄) / (γ / 2) ≤ w := (le_max_right _ _).trans hw
  have hw0 : 0 ≤ w := le_trans (by positivity) hw1
  have hw1' : C₃ ≤ w * rt := (div_le_iff₀ hrt).mp hw1
  have hw2' : 12 * rt / 2 ^ 8 + C₄ ≤ w * (γ / 2) := (div_le_iff₀ (by positivity)).mp hw2
  have hterm : ∀ u ∈ Finset.range t, Real.exp (E * Real.log L * ((s - u : ℕ) : ℝ)) * Real.exp (-(rt * D u / 2 ^ 8)) ≤
      Real.exp (-(ε * w)) * (1 / 2 : ℝ) ^ (s - u) := by
    intro u hu
    have hut := Finset.mem_range.mp hu
    have hH1 := h1 u hut
    have hH2 := h2 u hut
    obtain ⟨e, he⟩ : ∃ e : ℕ, e = s - u := ⟨_, rfl⟩
    rw [← he] at hH1 hH2 ⊢
    have key : ε * w + b * e ≤ rt * D u / 2 ^ 8 := by
      rcases le_or_gt (L ^ e) w with hle | hgt
      · have hD := hH2 hle
        have h5 := h3 e
        have h6 : rt * L ^ e ≤ rt * w := mul_le_mul_of_nonneg_left hle hrt.le
        have h7 : ε * w ≤ rt * w := mul_le_mul_of_nonneg_right hε1 hw0
        have h8 : rt * (2 ^ 10 * w) ≤ rt * D u := mul_le_mul_of_nonneg_left hD hrt.le
        have h9 : 0 ≤ rt * w := by positivity
        linarith
      · have h5 := h4 e
        have h6 : rt * (c * L ^ e - 12) ≤ rt * D u := mul_le_mul_of_nonneg_left hH1 hrt.le
        have h7 : ε * w ≤ γ / 4 * L ^ e :=
          (mul_le_mul_of_nonneg_right hε2 hw0).trans (mul_le_mul_of_nonneg_left hgt.le (by positivity))
        have h8 : w * (γ / 2) ≤ L ^ e * (γ / 2) := mul_le_mul_of_nonneg_right hgt.le (by positivity)
        have h9 : γ * L ^ e = rt * c * L ^ e / 2 ^ 8 := by
          rw [hγd]
          ring
        linarith
    have e2 : (1 / 2 : ℝ) ^ e = Real.exp ((e : ℝ) * (-Real.log 2)) := by
      rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num), one_div]
    rw [e2, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hbd] at key
    nlinarith
  calc ∑ u ∈ Finset.range t, Real.exp (E * Real.log L * ((s - u : ℕ) : ℝ)) * Real.exp (-(rt * D u / 2 ^ 8))
      ≤ ∑ u ∈ Finset.range t, Real.exp (-(ε * w)) * (1 / 2 : ℝ) ^ (s - u) := Finset.sum_le_sum hterm
    _ = Real.exp (-(ε * w)) * ∑ u ∈ Finset.range t, (1 / 2 : ℝ) ^ (s - u) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(ε * w)) * 1 := mul_le_mul_of_nonneg_left (sum_half_pow_le_one s t hts) (Real.exp_pos _).le
    _ = Real.exp (-(ε * w)) := mul_one _
private theorem sum_exp_terms_bounded (L c rt E : ℝ) (hL : 2 ≤ L) (hc : 0 < c) (hrt : 0 < rt) (hE : 0 ≤ E) :
    ∃ A₅ : ℝ, 0 ≤ A₅ ∧ ∀ (s t : ℕ) (D : ℕ → ℝ), t ≤ s → (∀ u < t, c * L ^ (s - u) - 12 ≤ D u) →
      ∑ u ∈ Finset.range t, Real.exp (E * Real.log L * ((s - u : ℕ) : ℝ)) * Real.exp (-(rt * D u / 2 ^ 8)) ≤ A₅ := by
  have hL1 : 1 < L := by linarith
  have hlog : 0 < Real.log L := Real.log_pos hL1
  obtain ⟨γ, hγd⟩ : ∃ γ : ℝ, γ = rt * c / 2 ^ 8 := ⟨_, rfl⟩
  have hγ : 0 < γ := by
    rw [hγd]
    positivity
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = E * Real.log L + Real.log 2 := ⟨_, rfl⟩
  have hb : 0 ≤ b := by
    rw [hbd]
    positivity
  obtain ⟨C₃, hC₃, h3⟩ := linear_le_eps_pow_add L hL1 γ b hγ hb
  refine ⟨Real.exp (C₃ + 12 * rt / 2 ^ 8), (Real.exp_pos _).le, fun s t D hts h1 => ?_⟩
  have hterm : ∀ u ∈ Finset.range t, Real.exp (E * Real.log L * ((s - u : ℕ) : ℝ)) * Real.exp (-(rt * D u / 2 ^ 8)) ≤
      Real.exp (C₃ + 12 * rt / 2 ^ 8) * (1 / 2 : ℝ) ^ (s - u) := by
    intro u hu
    have hH1 := h1 u (Finset.mem_range.mp hu)
    obtain ⟨e, he⟩ : ∃ e : ℕ, e = s - u := ⟨_, rfl⟩
    rw [← he] at hH1 ⊢
    have h5 := h3 e
    have h6 : rt * (c * L ^ e - 12) ≤ rt * D u := mul_le_mul_of_nonneg_left hH1 hrt.le
    have h9 : γ * L ^ e = rt * c * L ^ e / 2 ^ 8 := by
      rw [hγd]
      ring
    have e2 : (1 / 2 : ℝ) ^ e = Real.exp ((e : ℝ) * (-Real.log 2)) := by
      rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num), one_div]
    rw [e2, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hbd] at h5
    nlinarith
  calc _ ≤ ∑ u ∈ Finset.range t, Real.exp (C₃ + 12 * rt / 2 ^ 8) * (1 / 2 : ℝ) ^ (s - u) := Finset.sum_le_sum hterm
    _ = Real.exp (C₃ + 12 * rt / 2 ^ 8) * ∑ u ∈ Finset.range t, (1 / 2 : ℝ) ^ (s - u) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (C₃ + 12 * rt / 2 ^ 8) * 1 := mul_le_mul_of_nonneg_left (sum_half_pow_le_one s t hts) (Real.exp_pos _).le
    _ = _ := mul_one _
private theorem le_rpow_inv_natCast (a x : ℝ) (n : ℕ) (hn : n ≠ 0) (ha : 0 ≤ a) (h : a ^ n ≤ x) :
    a ≤ x ^ (((n : ℕ) : ℝ))⁻¹ := by
  have h1 := Real.rpow_le_rpow (by positivity) h (by positivity : (0 : ℝ) ≤ ((n : ℕ) : ℝ)⁻¹)
  rwa [Real.pow_rpow_inv_natCast ha hn] at h1
private theorem mul_sum_exp_terms_le (L c rt B A E : ℝ) (hL : 2 ≤ L) (hc : 0 < c) (hrt : 0 < rt) (hB : 0 < B)
    (hA : 0 ≤ A) (hE : 0 ≤ E) :
    ∃ X₁ : ℝ, ∀ x : ℝ, X₁ ≤ x → ∀ (s t : ℕ) (D : ℕ → ℝ), t ≤ s →
      (∀ u < t, c * L ^ (s - u) - 12 ≤ D u) →
      (∀ u < t, 4 * B * ((s - u : ℕ) : ℝ) ≤ x → 2 ^ 10 * (x ^ ((1 : ℝ) / 100) / 2) ≤ D u) →
      A * ∑ u ∈ Finset.range t, Real.exp (E * Real.log L * ((s - u : ℕ) : ℝ)) * Real.exp (-(rt * D u / 2 ^ 8)) ≤
        Real.exp (-(x ^ ((1 : ℝ) / 200))) := by
  obtain ⟨ε, W₀, hε, hW₀, hT⟩ := sum_exp_terms_le_exp L c rt E hL hc hrt hE
  obtain ⟨l, hld⟩ : ∃ l : ℝ, l = Real.log (A + 1) := ⟨_, rfl⟩
  have hl : 0 ≤ l := by
    rw [hld]
    exact Real.log_nonneg (by linarith)
  obtain ⟨V, hVd⟩ : ∃ V : ℝ, V = 4 / ε + 4 * l / ε + 1 := ⟨_, rfl⟩
  have hV1 : 1 ≤ V := by
    have h1 : 0 ≤ 4 / ε := by positivity
    have h2 : 0 ≤ 4 * l / ε := by positivity
    rw [hVd]
    linarith
  refine ⟨max (max (V ^ 200) ((2 * W₀) ^ 100)) (max 1 ((2 * B) ^ 2)), ?_⟩
  intro x hx s t D hts h1 h2
  have hxV : V ^ 200 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxW : (2 * W₀) ^ 100 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx1 : 1 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxB : (2 * B) ^ 2 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨v, hvd⟩ : ∃ v : ℝ, v = x ^ ((1 : ℝ) / 200) := ⟨_, rfl⟩
  have hv : V ≤ v := by
    have h3 := le_rpow_inv_natCast V x 200 (by norm_num) (by linarith) hxV
    rw [hvd]
    have h4 : (((200 : ℕ) : ℝ))⁻¹ = (1 : ℝ) / 200 := by norm_num
    rwa [h4] at h3
  have hv1 : 1 ≤ v := hV1.trans hv
  have hsq : x ^ ((1 : ℝ) / 100) = v ^ 2 := by
    rw [hvd, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  obtain ⟨w, hwd⟩ : ∃ w : ℝ, w = x ^ ((1 : ℝ) / 100) / 2 := ⟨_, rfl⟩
  have hwW : W₀ ≤ w := by
    have h3 := le_rpow_inv_natCast (2 * W₀) x 100 (by norm_num) (by positivity) hxW
    have h4 : (((100 : ℕ) : ℝ))⁻¹ = (1 : ℝ) / 100 := by norm_num
    rw [h4] at h3
    rw [hwd]
    linarith
  have hz : 2 * B ≤ x ^ ((1 : ℝ) / 2) := by
    have h3 := le_rpow_inv_natCast (2 * B) x 2 (by norm_num) (by positivity) hxB
    have h4 : (((2 : ℕ) : ℝ))⁻¹ = (1 : ℝ) / 2 := by norm_num
    rwa [h4] at h3
  have hzz : x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) = x := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  have hroot : x ^ ((1 : ℝ) / 100) ≤ x ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hz0 : 0 ≤ x ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hx0 _
  have hpre : ∀ u < t, L ^ (s - u) ≤ w → 2 ^ 10 * w ≤ D u := by
    intro u hut hle
    rw [hwd] at hle ⊢
    apply h2 u hut
    have h3 : ((s - u : ℕ) : ℝ) ≤ L ^ (s - u) := by
      have h4 : ((s - u : ℕ) : ℝ) ≤ 2 ^ (s - u) := by
        have h5 : s - u + 1 ≤ 2 ^ (s - u) := Nat.lt_two_pow_self
        have h6 : ((s - u + 1 : ℕ) : ℝ) ≤ ((2 ^ (s - u) : ℕ) : ℝ) := by exact_mod_cast h5
        push_cast at h6
        linarith
      exact h4.trans (pow_le_pow_left₀ (by norm_num) hL _)
    have h4 : ((s - u : ℕ) : ℝ) ≤ x ^ ((1 : ℝ) / 2) / 2 := by linarith
    have h5 : 4 * B * ((s - u : ℕ) : ℝ) ≤ 4 * B * (x ^ ((1 : ℝ) / 2) / 2) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h6 : 2 * B * x ^ ((1 : ℝ) / 2) ≤ x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hz hz0
    linarith
  have hsum := hT w hwW s t D hts h1 hpre
  have hAe : A ≤ Real.exp l := by
    rw [hld, Real.exp_log (by linarith)]
    linarith
  have hEv : 4 + 4 * l ≤ ε * v := by
    have h3 := mul_le_mul_of_nonneg_left hv hε.le
    have h4 : ε * V = 4 + 4 * l + ε := by
      rw [hVd]
      field_simp
    linarith
  have hexp : l + -(ε * w) ≤ -v := by
    have h3 : (4 + 4 * l) * v ≤ ε * v * v := mul_le_mul_of_nonneg_right hEv (by linarith)
    have h4 : l ≤ l * v := le_mul_of_one_le_right hl hv1
    have h5 : w = v ^ 2 / 2 := by rw [hwd, hsq]
    rw [h5]
    nlinarith
  rw [← hvd]
  calc A * ∑ u ∈ Finset.range t, Real.exp (E * Real.log L * ((s - u : ℕ) : ℝ)) * Real.exp (-(rt * D u / 2 ^ 8))
      ≤ A * Real.exp (-(ε * w)) := mul_le_mul_of_nonneg_left hsum hA
    _ ≤ Real.exp l * Real.exp (-(ε * w)) := mul_le_mul_of_nonneg_right hAe (Real.exp_pos _).le
    _ = Real.exp (l + -(ε * w)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-v) := Real.exp_le_exp.mpr hexp
end Numbers
section Bounds
variable {Λ : MomentParameters}
private def partialSum (t u : ℕ) (i : Fin Λ.k) : SampleObservable Λ := fun S w =>
  responseAtLevel u i S w + ∑ j ∈ Finset.Ico u t, centredStepScore j i S w
private def partialProduct (t u : ℕ) (B : Finset (Fin Λ.k)) : SampleObservable Λ := fun S w => ∏ i ∈ B, partialSum t u i S w
private def tailProduct (t u : ℕ) (I : Finset (Fin Λ.k)) : SampleObservable Λ := fun S w =>
  ∏ i ∈ I, ∑ j ∈ Finset.Ico (u + 1) t, centredStepScore j i S w
private def responseProductAt (u : ℕ) (J : Finset (Fin Λ.k)) : SampleObservable Λ := fun S w => ∏ i ∈ J, responseAtLevel u i S w
private def kappaOffset (c : Fin Λ.k → ℝ) (i : Fin Λ.k) : SampleObservable Λ := fun S _ => S.kappaAtLast i - c i
private theorem natCast_le_two_pow (e : ℕ) : (e : ℝ) ≤ 2 ^ e := by
  have h5 : e + 1 ≤ 2 ^ e := Nat.lt_two_pow_self
  have h6 : ((e + 1 : ℕ) : ℝ) ≤ ((2 ^ e : ℕ) : ℝ) := by exact_mod_cast h5
  push_cast at h6
  linarith
private theorem abs_tailProduct_le {S' : MomentPoint Λ} {A₂ : ℝ} (hA : 0 ≤ A₂) (hC : 0 ≤ Λ.response.C₀) (hL : (2 : ℝ) ≤ Λ.stepParams.side)
    (hsc : ∀ j < S'.data.scaleLevel, ∀ (i : Fin Λ.k) (w : MarkedSample Λ.stepParams S'.data.windowLevel (S'.data.period Λ.stepParams.side)),
      |centredStepScore j i S' w| ≤ 2 * (Λ.response.C₀ * ((S'.data.supportSites Λ.stepParams.side j i).card : ℝ)))
    (hs : ∀ j ≤ S'.data.scaleLevel, ∀ i : Fin Λ.k,
      ((S'.data.supportSites Λ.stepParams.side j i).card : ℝ) ≤ A₂ * (Λ.stepParams.side : ℝ) ^ (4 * (S'.data.scaleLevel - j)))
    {t u : ℕ} (hut : u < t) (hts : t ≤ S'.data.scaleLevel) (I : Finset (Fin Λ.k)) (hI : I.card ≤ 8)
    (w : MarkedSample Λ.stepParams S'.data.windowLevel (S'.data.period Λ.stepParams.side)) :
    |tailProduct t u I S' w| ≤ ((1 + 2 * Λ.response.C₀ * A₂) * ((Λ.stepParams.side : ℝ) ^ (S'.data.scaleLevel - u)) ^ 5) ^ 8 := by
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (Λ.stepParams.side : ℝ) ^ (S'.data.scaleLevel - u) := ⟨_, rfl⟩
  rw [← hP]
  have hP1 : 1 ≤ P := hP ▸ one_le_pow₀ (by linarith)
  have hcount : ((Finset.Ico (u + 1) t).card : ℝ) ≤ P := by
    rw [Nat.card_Ico]
    have h1 : t - (u + 1) ≤ S'.data.scaleLevel - u := by omega
    have h2 : ((t - (u + 1) : ℕ) : ℝ) ≤ ((S'.data.scaleLevel - u : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 := natCast_le_two_pow (S'.data.scaleLevel - u)
    have h4 : (2 : ℝ) ^ (S'.data.scaleLevel - u) ≤ P := hP ▸ pow_le_pow_left₀ (by norm_num) hL _
    linarith
  have hterm : ∀ i : Fin Λ.k, |∑ j ∈ Finset.Ico (u + 1) t, centredStepScore j i S' w| ≤ (1 + 2 * Λ.response.C₀ * A₂) * P ^ 5 := by
    intro i
    have hone : ∀ j ∈ Finset.Ico (u + 1) t, |centredStepScore j i S' w| ≤ 2 * (Λ.response.C₀ * (A₂ * P ^ 4)) := by
      intro j hj
      have hj' := Finset.mem_Ico.mp hj
      refine (hsc j (by omega) i w).trans ?_
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hC) (by norm_num)
      refine (hs j (by omega) i).trans (mul_le_mul_of_nonneg_left ?_ hA)
      have e : P ^ 4 = (Λ.stepParams.side : ℝ) ^ (4 * (S'.data.scaleLevel - u)) := by
        rw [hP, ← pow_mul, mul_comm]
      rw [e]
      exact pow_le_pow_right₀ (by linarith) (by omega)
    calc |∑ j ∈ Finset.Ico (u + 1) t, centredStepScore j i S' w| ≤ ∑ j ∈ Finset.Ico (u + 1) t, |centredStepScore j i S' w| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.Ico (u + 1) t, 2 * (Λ.response.C₀ * (A₂ * P ^ 4)) := Finset.sum_le_sum hone
      _ = ((Finset.Ico (u + 1) t).card : ℝ) * (2 * (Λ.response.C₀ * (A₂ * P ^ 4))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ P * (2 * (Λ.response.C₀ * (A₂ * P ^ 4))) := mul_le_mul_of_nonneg_right hcount (by positivity)
      _ ≤ (1 + 2 * Λ.response.C₀ * A₂) * P ^ 5 := by
          have : 0 ≤ P ^ 5 := by positivity
          nlinarith
  have hρ1 : 1 ≤ (1 + 2 * Λ.response.C₀ * A₂) * P ^ 5 := by
    have h1 : 1 ≤ P ^ 5 := one_le_pow₀ hP1
    have h2 : 1 ≤ 1 + 2 * Λ.response.C₀ * A₂ := by nlinarith [mul_nonneg hC hA]
    exact one_le_mul_of_one_le_of_one_le h2 h1
  unfold tailProduct
  rw [Finset.abs_prod]
  calc ∏ i ∈ I, |∑ j ∈ Finset.Ico (u + 1) t, centredStepScore j i S' w|
      ≤ ∏ _i ∈ I, (1 + 2 * Λ.response.C₀ * A₂) * P ^ 5 :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => hterm i
    _ = ((1 + 2 * Λ.response.C₀ * A₂) * P ^ 5) ^ I.card := by rw [Finset.prod_const]
    _ ≤ _ := pow_le_pow_right₀ hρ1 hI
private theorem stepErrorBound_le {S' : MomentPoint Λ} {A₂ M Cn D : ℝ} (hA : 0 ≤ A₂) (hC : 0 ≤ Λ.response.C₀)
    (hL : (2 : ℝ) ≤ Λ.stepParams.side) (hM : 4 * Λ.response.C₀ * A₂ ≤ M) (hM1 : 1 ≤ M)
    (hs : ∀ j ≤ S'.data.scaleLevel, ∀ i : Fin Λ.k,
      ((S'.data.supportSites Λ.stepParams.side j i).card : ℝ) ≤ A₂ * (Λ.stepParams.side : ℝ) ^ (4 * (S'.data.scaleLevel - j)))
    {u : ℕ} (hu : u ≤ S'.data.scaleLevel) (J : Finset (Fin Λ.k)) (hJ : J.card ≤ 8) (hrt : 0 ≤ Λ.stepParams.rt)
    (hD : D ≤ (S'.data.separation Λ.stepParams.side u : ℝ)) :
    S'.stepErrorBound Cn u J ≤ |Cn| * (8 * (A₂ * ((Λ.stepParams.side : ℝ) ^ (S'.data.scaleLevel - u)) ^ 4)) *
      Real.exp (-(Λ.stepParams.rt * D / 2 ^ 7)) * (M * ((Λ.stepParams.side : ℝ) ^ (S'.data.scaleLevel - u)) ^ 4) ^ 8 := by
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (Λ.stepParams.side : ℝ) ^ (S'.data.scaleLevel - u) := ⟨_, rfl⟩
  rw [← hP]
  have hP1 : 1 ≤ P := hP ▸ one_le_pow₀ (by linarith)
  have hcard : ∀ i : Fin Λ.k, ((S'.data.supportSites Λ.stepParams.side u i).card : ℝ) ≤ A₂ * P ^ 4 := fun i => by
    refine (hs u hu i).trans (le_of_eq ?_)
    rw [hP, ← pow_mul, mul_comm 4]
  have h1 : ∑ i ∈ J, ((S'.data.supportSites Λ.stepParams.side u i).card : ℝ) ≤ 8 * (A₂ * P ^ 4) := by
    calc _ ≤ ∑ _i ∈ J, A₂ * P ^ 4 := Finset.sum_le_sum fun i _ => hcard i
      _ = (J.card : ℝ) * (A₂ * P ^ 4) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hJ) (by positivity)
  have hMP : 1 ≤ M * P ^ 4 := one_le_mul_of_one_le_of_one_le hM1 (one_le_pow₀ hP1)
  have h2 : ∏ i ∈ J, (4 * (Λ.response.C₀ * ((S'.data.supportSites Λ.stepParams.side u i).card : ℝ))) ≤ (M * P ^ 4) ^ 8 := by
    calc _ ≤ ∏ _i ∈ J, (M * P ^ 4) := by
          refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
          have h3 := mul_le_mul_of_nonneg_left (hcard i) hC
          have h4 : 4 * Λ.response.C₀ * A₂ * P ^ 4 ≤ M * P ^ 4 := mul_le_mul_of_nonneg_right hM (by positivity)
          nlinarith
      _ = (M * P ^ 4) ^ J.card := by rw [Finset.prod_const]
      _ ≤ _ := pow_le_pow_right₀ hMP hJ
  have h3 : Real.exp (-(Λ.stepParams.rt * (S'.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 7)) ≤
      Real.exp (-(Λ.stepParams.rt * D / 2 ^ 7)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hD hrt
    have h4 : (0 : ℝ) < 2 ^ 7 := by norm_num
    linarith
  have h0 : 0 ≤ ∑ i ∈ J, ((S'.data.supportSites Λ.stepParams.side u i).card : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hp0 : 0 ≤ ∏ i ∈ J, (4 * (Λ.response.C₀ * ((S'.data.supportSites Λ.stepParams.side u i).card : ℝ))) :=
    Finset.prod_nonneg fun i _ => by positivity
  unfold MomentPoint.stepErrorBound
  calc Cn * (∑ i ∈ J, ((S'.data.supportSites Λ.stepParams.side u i).card : ℝ)) *
        Real.exp (-(Λ.stepParams.rt * (S'.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 7)) *
        ∏ i ∈ J, (4 * (Λ.response.C₀ * ((S'.data.supportSites Λ.stepParams.side u i).card : ℝ)))
      ≤ |Cn| * (∑ i ∈ J, ((S'.data.supportSites Λ.stepParams.side u i).card : ℝ)) *
        Real.exp (-(Λ.stepParams.rt * (S'.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 7)) *
        ∏ i ∈ J, (4 * (Λ.response.C₀ * ((S'.data.supportSites Λ.stepParams.side u i).card : ℝ))) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) h0) (Real.exp_pos _).le) hp0
    _ ≤ _ := by
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h3 (Real.exp_pos _).le (by positivity)) h2 hp0 (by positivity)
private theorem card_offsetCube (ρ : ℕ) : ((offsetCube ρ).card : ℝ) = (2 * (ρ : ℝ) + 1) ^ 4 := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolNorm.card_intCube <;> assumption
private theorem card_offsetCube_supportRadius_le (S' : MomentPoint Λ) (hL : (2 : ℝ) ≤ Λ.stepParams.side) {u : ℕ} {P : ℝ}
    (hP : (Λ.stepParams.side : ℝ) ^ (S'.data.scaleLevel - u) ≤ P) :
    ((offsetCube (S'.supportRadius u)).card : ℝ) ≤ (2 * |Λ.R| + 7) ^ 4 * P ^ 4 := by
  rw [card_offsetCube]
  have hL1 : 1 ≤ (Λ.stepParams.side : ℝ) ^ (S'.data.scaleLevel - u) := one_le_pow₀ (by linarith)
  have hP1 : 1 ≤ P := hL1.trans hP
  have h1 : ((S'.supportRadius u : ℕ) : ℝ) ≤ |Λ.R| * P + 3 := by
    unfold MomentPoint.supportRadius
    push_cast
    have h2 : (⌈Λ.R * (Λ.stepParams.side : ℝ) ^ (S'.data.scaleLevel - u)⌉₊ : ℝ) ≤ |Λ.R| * P + 1 := by
      have h3 : Λ.R * (Λ.stepParams.side : ℝ) ^ (S'.data.scaleLevel - u) ≤ |Λ.R| * P :=
        (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)).trans (mul_le_mul_of_nonneg_left hP (abs_nonneg _))
      have h4 := Nat.ceil_lt_add_one (a := |Λ.R| * P) (by positivity)
      have h5 : (⌈Λ.R * (Λ.stepParams.side : ℝ) ^ (S'.data.scaleLevel - u)⌉₊ : ℝ) ≤ (⌈|Λ.R| * P⌉₊ : ℝ) := by
        exact_mod_cast Nat.ceil_mono h3
      linarith
    linarith
  have h6 : 2 * ((S'.supportRadius u : ℕ) : ℝ) + 1 ≤ (2 * |Λ.R| + 7) * P := by
    nlinarith [abs_nonneg Λ.R]
  calc (2 * ((S'.supportRadius u : ℕ) : ℝ) + 1) ^ 4 ≤ ((2 * |Λ.R| + 7) * P) ^ 4 := pow_le_pow_left₀ (by positivity) h6 4
    _ = _ := mul_pow _ _ _
end Bounds
section Field
variable {Λ : MomentParameters} {S : MomentPoint Λ}
private def restrictLaw (F : LimitLawAtPoint S) (φ : ℕ → ℕ) (hφ : StrictMono φ) : LimitLawAtPoint S :=
  { F with
    exponents := F.exponents ∘ φ
    strictMono_exponents := F.strictMono_exponents.comp hφ
    points := F.points ∘ φ
    points_eq := fun i => F.points_eq (φ i)
    hasBoundedMoments := fun j => ⟨fun i => (F.hasBoundedMoments j).aemeasurable (φ i), fun q => by
      obtain ⟨C, h⟩ := (F.hasBoundedMoments j).moment_bound q
      exact ⟨C, fun i => h (φ i)⟩⟩
    isJointLimitLaw := ⟨F.isJointLimitLaw.isProbability, fun l a G hG hb =>
      (F.isJointLimitLaw.tendsto l a G hG hb).comp hφ.tendsto_atTop⟩ }
private def extendLaw (F : LimitLawAtPoint S) {J' : Type} [Countable J'] (g' : J' → SampleObservable Λ)
    (hm : ∀ j, TranslatedLaws.HasBoundedMoments (sampleFamily F.rule F.points F.period (g' j))) (sub : ℕ → ℕ) (hsub : StrictMono sub)
    (P' : Measure (TranslateValues (F.Index ⊕ J')))
    (hL : IsJointLimitLaw ((translatedTori F.points F.period).subsequence sub)
      (fun j i => Sum.elim (fun j => sampleFamily F.rule F.points F.period (F.observables j))
        (fun j => sampleFamily F.rule F.points F.period (g' j)) j (sub i)) P') :
    LimitLawAtPoint S where
  rule := F.rule
  rule_admissible := F.rule_admissible
  period := F.period
  one_le_period := F.one_le_period
  exponents := F.exponents ∘ sub
  strictMono_exponents := F.strictMono_exponents.comp hsub
  points := F.points ∘ sub
  points_eq := fun i => F.points_eq (sub i)
  Index := F.Index ⊕ J'
  countable_index := by
    haveI := F.countable_index
    infer_instance
  observables := Sum.elim F.observables g'
  hasBoundedMoments := by
    rintro (j | j)
    · exact ⟨fun i => (F.hasBoundedMoments j).aemeasurable (sub i), fun q => by
        obtain ⟨C, h⟩ := (F.hasBoundedMoments j).moment_bound q
        exact ⟨C, fun i => h (sub i)⟩⟩
    · exact ⟨fun i => (hm j).aemeasurable (sub i), fun q => by
        obtain ⟨C, h⟩ := (hm j).moment_bound q
        exact ⟨C, fun i => h (sub i)⟩⟩
  law := P'
  isJointLimitLaw := by
    have e : (fun (j : F.Index ⊕ J') => sampleFamily F.rule (F.points ∘ sub) F.period (Sum.elim F.observables g' j)) =
        fun j i => Sum.elim (fun j => sampleFamily F.rule F.points F.period (F.observables j))
          (fun j => sampleFamily F.rule F.points F.period (g' j)) j (sub i) := by
      funext j
      cases j <;> rfl
    rw [e]
    exact hL
private inductive TelescopeTerm (k : ℕ)
  | line (u : ℕ) (i : Fin k)
  | product (u : ℕ)
  | rest (u : ℕ) (I : Finset (Fin k))
  | var (u : ℕ) (J : Finset (Fin k))
  | mean (u : ℕ) (J : Finset (Fin k))
  | resp (u : ℕ) (J : Finset (Fin k))
  | size (u : ℕ) (z : Fin 4 → ℤ) (p : ℕ)
  | off (i : Fin k)
  | completed
end Field
section Field
variable {Λ : MomentParameters} {S : MomentPoint Λ}
section Core
variable {t : ℕ} {B : Finset (Fin Λ.k)} {c : Fin Λ.k → ℝ}
private structure TelescopeIndices (F : LimitLawAtPoint S) (t : ℕ) (B : Finset (Fin Λ.k)) (c : Fin Λ.k → ℝ) where
  m : TelescopeTerm Λ.k → F.Index
  line : ∀ u i, u ≤ t → F.observables (m (.line u i)) = partialSum t u i
  product : ∀ u, u ≤ t → F.observables (m (.product u)) = partialProduct t u B
  rest : ∀ u I, F.observables (m (.rest u I)) = tailProduct t u I
  var : ∀ u J, u < t → F.observables (m (.var u J)) = variableProduct u J
  mean : ∀ u J, u < t → J.Nonempty → F.observables (m (.mean u J)) = variableMean u J
  resp : ∀ u J, u ≤ t → F.observables (m (.resp u J)) = responseProductAt u J
  size : ∀ u z p, u ≤ S.data.windowLevel → F.observables (m (.size u z p)) = hullSizePower u z p
  off : ∀ i, F.observables (m (.off i)) = kappaOffset c i
  completed : F.observables (m .completed) = completedProduct c B
variable {F : LimitLawAtPoint S}
private theorem integrable_coord (hM : jointLimitPropertiesStatement) (hk : (translatedTori F.points F.period).IsPreserving) (j : F.Index) :
    Integrable (fun v : TranslateValues F.Index => v (j, 0)) F.law := by apply _root_.YangMills.SharedProofs.p44385 <;> assumption
private theorem integrable_coord_mul (hM : jointLimitPropertiesStatement) (hk : (translatedTori F.points F.period).IsPreserving)
    (j j' : F.Index) :
    Integrable (fun v : TranslateValues F.Index => v (j, 0) * v (j', 0)) F.law := by
  haveI := F.countable_index
  have h := ((hM _ _ _ _ hk F.hasBoundedMoments F.isJointLimitLaw).2.1 2 ![(j, 0), (j', 0)]).1
  simpa [Fin.prod_univ_two] using h
private theorem invariantCondExp_affine_sum_le {J : Type} {P : Measure (TranslateValues J)} [IsProbabilityMeasure P] {ι : Type}
    (s : Finset ι) (f : ι → TranslateValues J → ℝ)
    (hf : ∀ z ∈ s, Integrable (f z) P) (b a e : ℝ) (he : 0 ≤ e) (hb : ∀ z ∈ s, ∀ᵐ v ∂P, invariantCondExp P (f z) v ≤ b) :
    ∀ᵐ v ∂P, invariantCondExp P (fun v => a + e * ∑ z ∈ s, f z v) v ≤ a + e * ((s.card : ℝ) * b) := by
  have hsum : Integrable (fun v => ∑ z ∈ s, f z v) P := integrable_finsetSum _ hf
  have h1 : invariantCondExp P (fun v => ∑ z ∈ s, f z v) =ᵐ[P] ∑ z ∈ s, invariantCondExp P (f z) := by
    have := condExp_finsetSum (μ := P) (s := s) (f := f) hf (shiftInvariantSigma J)
    refine (condExp_congr_ae (ae_of_all _ fun v => ?_)).trans this
    simp
  have h2 : invariantCondExp P (fun v => a + e * ∑ z ∈ s, f z v) =ᵐ[P]
      (fun v => a + e * invariantCondExp P (fun v => ∑ z ∈ s, f z v) v) := by
    have e1 := condExp_add (μ := P) (integrable_const a) (hsum.const_mul e) (shiftInvariantSigma J)
    have e2 := condExp_smul (μ := P) e (fun v => ∑ z ∈ s, f z v) (shiftInvariantSigma J)
    have e3 : P[fun _ : TranslateValues J => a | shiftInvariantSigma J] = fun _ => a := condExp_const shiftInvariantSigma_le a
    unfold invariantCondExp
    filter_upwards [e1, e2] with v h₁ h₂
    have h₁' : P[fun v => a + e * ∑ z ∈ s, f z v | shiftInvariantSigma J] v =
        (P[fun _ : TranslateValues J => a | shiftInvariantSigma J] + P[fun v => e * ∑ z ∈ s, f z v | shiftInvariantSigma J]) v := h₁
    have h₂' : P[fun v => e * ∑ z ∈ s, f z v | shiftInvariantSigma J] v = e * P[fun v => ∑ z ∈ s, f z v | shiftInvariantSigma J] v := by
      have e4 : (fun v => e * ∑ z ∈ s, f z v) = e • (fun v => ∑ z ∈ s, f z v) := rfl
      rw [e4]
      simpa [smul_eq_mul, Pi.smul_apply] using h₂
    rw [h₁', Pi.add_apply, e3, h₂']
  have h3 : ∀ᵐ v ∂P, ∀ z ∈ s, invariantCondExp P (f z) v ≤ b := (ae_ball_iff s.countable_toSet).2 hb
  filter_upwards [h1, h2, h3] with v a₁ a₂ a₃
  rw [a₂, a₁, Finset.sum_apply]
  have : ∑ z ∈ s, invariantCondExp P (f z) v ≤ (s.card : ℝ) * b := by
    simpa using Finset.sum_le_card_nsmul s _ b a₃
  nlinarith [mul_le_mul_of_nonneg_left this he]
private theorem prod_add_sub_prod_add {ι : Type} [DecidableEq ι] (B : Finset ι) (x y q : ι → ℝ) :
    ∏ i ∈ B, (x i + q i) - ∏ i ∈ B, (y i + q i) =
      ∑ J ∈ B.powerset.filter Finset.Nonempty, (∏ i ∈ B \ J, q i) * (∏ i ∈ J, x i - ∏ i ∈ J, y i) := by
  classical
  rw [Finset.prod_add, Finset.prod_add, ← Finset.sum_sub_distrib]
  have h : ∑ J ∈ B.powerset, ((∏ i ∈ J, x i) * ∏ i ∈ B \ J, q i - (∏ i ∈ J, y i) * ∏ i ∈ B \ J, q i) =
      ∑ J ∈ B.powerset.filter Finset.Nonempty, ((∏ i ∈ J, x i) * ∏ i ∈ B \ J, q i - (∏ i ∈ J, y i) * ∏ i ∈ B \ J, q i) := by
    symm
    refine Finset.sum_filter_of_ne fun J _ hne => ?_
    rcases J.eq_empty_or_nonempty with rfl | hJ
    · exact absurd (by simp) hne
    · exact hJ
  rw [h]
  exact Finset.sum_congr rfl fun J _ => by ring
private theorem abs_condMeanAt_step_le (hM : jointLimitPropertiesStatement) (hk : (translatedTori F.points F.period).IsPreserving)
    (ix : TelescopeIndices F t B c)
    (hae : ∀ n (Q : MarkedSample Λ.stepParams (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side) → Prop),
      (∀ᵐ w ∂((F.points n).law (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side)), Q w) →
        ∀ᵐ ω ∂(F.points n).sampleLaw, Q ((F.points n).sampleOf F.rule ω))
    {u : ℕ} (hu : u < t)
    (hV : ∀ n J, ∀ᵐ w ∂((F.points n).law (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side)),
      variableProduct u J (F.points n) w = ∏ i ∈ J, (responseAtLevel u i (F.points n) w + centredStepScore u i (F.points n) w))
    (hK : u + 1 ≤ S.data.windowLevel) (box : Finset (Fin 4 → ℤ)) (a e b : Finset (Fin Λ.k) → ℝ) (he : ∀ J, 0 ≤ e J)
    (hB : ∀ J ∈ B.powerset.filter Finset.Nonempty, ∀ n,
      ∀ᵐ w ∂((F.points n).law (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side)),
      |tailProduct t u (B \ J) (F.points n) w * (variableMean u J (F.points n) w - responseProductAt (u + 1) J (F.points n) w)| ≤
        a J + e J * ∑ z ∈ box, hullSizePower (u + 1) z J.card (F.points n) w)
    (hFar : ∀ J ∈ B.powerset.filter Finset.Nonempty,
      F.condMean (fun v => v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.var u J), 0)) =ᵐ[F.law]
        F.condMean (fun v => v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.mean u J), 0)))
    (hS : ∀ J ∈ B.powerset.filter Finset.Nonempty, ∀ z ∈ box,
      ∀ᵐ v ∂F.law, F.condMeanAt (ix.m (.size (u + 1) z J.card)) v ≤ b J) :
    ∀ᵐ v ∂F.law, |F.condMeanAt (ix.m (.product u)) v - F.condMeanAt (ix.m (.product (u + 1))) v| ≤
      ∑ J ∈ B.powerset.filter Finset.Nonempty, (a J + e J * ((box.card : ℝ) * b J)) := by
  classical
  have hP : IsProbabilityMeasure F.law := F.isJointLimitLaw.isProbability
  have i1 := integrable_coord hM hk
  have i2 := integrable_coord_mul hM hk
  obtain ⟨ne, hne⟩ : ∃ ne, ne = B.powerset.filter Finset.Nonempty := ⟨_, rfl⟩
  rw [← hne] at hB hFar hS ⊢
  have R1 : ∀ᵐ v ∂F.law, v (ix.m (.product u), 0) - v (ix.m (.product (u + 1)), 0) =
      ∑ J ∈ ne, v (ix.m (.rest u (B \ J)), 0) * (v (ix.m (.var u J), 0) - v (ix.m (.resp (u + 1) J), 0)) := by
    have h := ae_eq_of_eventually_eq F.isJointLimitLaw (I := Bool ⊕ (Finset (Fin Λ.k) × Fin 3))
      (Sum.elim (fun x => if x then ix.m (.product u) else ix.m (.product (u + 1)))
        (fun p => (![ix.m (.rest u (B \ p.1)), ix.m (.var u p.1), ix.m (.resp (u + 1) p.1)] : Fin 3 → F.Index) p.2))
      (fun x => x (.inl true) - x (.inl false))
      (fun x => ∑ J ∈ ne, x (.inr (J, 0)) * (x (.inr (J, 1)) - x (.inr (J, 2))))
      (by fun_prop) (by fun_prop) (Eventually.of_forall fun n => ?_)
    · filter_upwards [h] with v hv
      simpa using hv
    · have h0 := hae n _ (ae_all_iff.2 (hV n))
      filter_upwards [h0] with ω hω
      obtain ⟨d, hd⟩ : ∃ d, d = (F.points n).sampleOf F.rule ω := ⟨_, rfl⟩
      replace hω : ∀ J, variableProduct u J (F.points n) d =
          ∏ i ∈ J, (responseAtLevel u i (F.points n) d + centredStepScore u i (F.points n) d) := by
        rw [hd]
        exact hω
      have e1 : ∀ j, sampleFamily F.rule F.points F.period (F.observables j) n ω = F.observables j (F.points n) d := fun j => by
        rw [hd]; rfl
      simp only [Sum.elim_inl, Sum.elim_inr, if_true, e1]
      simp only [Bool.false_eq_true, if_false, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [ix.product u hu.le, ix.product (u + 1) hu]
      have e2 : ∀ J ∈ ne, F.observables (ix.m (.rest u (B \ J))) (F.points n) d *
            (F.observables (ix.m (.var u J)) (F.points n) d - F.observables (ix.m (.resp (u + 1) J)) (F.points n) d) =
          (∏ i ∈ B \ J, ∑ j ∈ Finset.Ico (u + 1) t, centredStepScore j i (F.points n) d) *
            (∏ i ∈ J, (responseAtLevel u i (F.points n) d + centredStepScore u i (F.points n) d) -
              ∏ i ∈ J, responseAtLevel (u + 1) i (F.points n) d) := by
        intro J _
        rw [ix.rest, ix.var u J hu, ix.resp (u + 1) J hu, hω J]
        rfl
      rw [Finset.sum_congr rfl e2, hne, ← prod_add_sub_prod_add]
      refine congrArg₂ _ (Finset.prod_congr rfl fun i _ => ?_) rfl
      show responseAtLevel u i (F.points n) d + ∑ j ∈ Finset.Ico u t, centredStepScore j i (F.points n) d = _
      rw [Finset.sum_eq_sum_Ico_succ_bot hu]
      ring
  have R2 : ∀ J ∈ ne, ∀ᵐ v ∂F.law,
      |v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.mean u J), 0) - v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.resp (u + 1) J), 0)| ≤
        a J + e J * ∑ z ∈ box, v (ix.m (.size (u + 1) z J.card), 0) := by
    intro J hJ
    have hJn : J.Nonempty := (Finset.mem_filter.mp (hne ▸ hJ)).2
    have h := ae_le_of_eventually_le F.isJointLimitLaw (I := Fin 3 ⊕ {z // z ∈ box})
      (Sum.elim (fun l => (![ix.m (.rest u (B \ J)), ix.m (.mean u J), ix.m (.resp (u + 1) J)] : Fin 3 → F.Index) l)
        (fun z => ix.m (.size (u + 1) z.1 J.card)))
      (fun x => |x (.inl 0) * x (.inl 1) - x (.inl 0) * x (.inl 2)| - (a J + e J * ∑ z : {z // z ∈ box}, x (.inr z)))
      (by fun_prop) (Eventually.of_forall fun n => ?_)
    · filter_upwards [h] with v hv
      simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hv
      have e3 := Finset.sum_coe_sort box fun z => v (ix.m (.size (u + 1) z J.card), 0)
      rw [e3] at hv
      linarith
    · have h0 := hae n _ (hB J hJ n)
      filter_upwards [h0] with ω hω
      obtain ⟨d, hd⟩ : ∃ d, d = (F.points n).sampleOf F.rule ω := ⟨_, rfl⟩
      replace hω : |tailProduct t u (B \ J) (F.points n) d *
            (variableMean u J (F.points n) d - responseProductAt (u + 1) J (F.points n) d)| ≤
          a J + e J * ∑ z ∈ box, hullSizePower (u + 1) z J.card (F.points n) d := by
        rw [hd]
        exact hω
      have e1 : ∀ j, sampleFamily F.rule F.points F.period (F.observables j) n ω = F.observables j (F.points n) d := fun j => by
        rw [hd]; rfl
      simp only [Sum.elim_inl, Sum.elim_inr, e1]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [ix.rest, ix.mean u J hu hJn, ix.resp (u + 1) J hu]
      have e3 := Finset.sum_coe_sort box fun z => F.observables (ix.m (.size (u + 1) z J.card)) (F.points n) d
      rw [e3, Finset.sum_congr rfl fun z _ => by rw [ix.size (u + 1) z J.card hK]]
      rw [← mul_sub]
      linarith
  have R3 : ∀ J ∈ ne, ∀ᵐ v ∂F.law, |F.condMean (fun v => v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.mean u J), 0) -
      v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.resp (u + 1) J), 0)) v| ≤ a J + e J * ((box.card : ℝ) * b J) := by
    intro J hJ
    have hsz : ∀ z ∈ box, Integrable (fun v : TranslateValues F.Index => v (ix.m (.size (u + 1) z J.card), 0)) F.law :=
      fun z _ => i1 _
    have h1 := abs_invariantCondExp_le ((i2 _ _).sub (i2 _ _))
      ((integrable_const (a J)).add ((integrable_finsetSum _ hsz).const_mul (e J))) (R2 J hJ)
    have h2 := invariantCondExp_affine_sum_le box (fun z (v : TranslateValues F.Index) => v (ix.m (.size (u + 1) z J.card), 0)) hsz
      (b J) (a J) (e J) (he J) (fun z hz => hS J hJ z hz)
    filter_upwards [h1, h2] with v x₁ x₂
    exact x₁.trans x₂
  have R4 : ∀ J ∈ ne, F.condMean (fun v => v (ix.m (.rest u (B \ J)), 0) * (v (ix.m (.var u J), 0) - v (ix.m (.resp (u + 1) J), 0)))
      =ᵐ[F.law] F.condMean (fun v => v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.mean u J), 0) -
        v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.resp (u + 1) J), 0)) := by
    intro J hJ
    have e1 : (fun v : TranslateValues F.Index => v (ix.m (.rest u (B \ J)), 0) * (v (ix.m (.var u J), 0) - v (ix.m (.resp (u + 1) J), 0))) =
        (fun v => v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.var u J), 0)) -
          fun v => v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.resp (u + 1) J), 0) := by
      funext v
      simp [mul_sub]
    have s1 := condExp_sub (μ := F.law) (i2 (ix.m (.rest u (B \ J))) (ix.m (.var u J)))
      (i2 (ix.m (.rest u (B \ J))) (ix.m (.resp (u + 1) J))) (shiftInvariantSigma F.Index)
    have s2 := condExp_sub (μ := F.law) (i2 (ix.m (.rest u (B \ J))) (ix.m (.mean u J)))
      (i2 (ix.m (.rest u (B \ J))) (ix.m (.resp (u + 1) J))) (shiftInvariantSigma F.Index)
    have hf := hFar J hJ
    unfold LimitLawAtPoint.condMean invariantCondExp at *
    rw [e1]
    filter_upwards [s1, s2, hf] with v a₁ a₂ a₃
    rw [a₁]
    have a₂' := a₂
    simp only [Pi.sub_apply] at a₂' ⊢
    have e2 : (fun v : TranslateValues F.Index => v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.mean u J), 0) -
        v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.resp (u + 1) J), 0)) =
      (fun v => v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.mean u J), 0)) -
        fun v => v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.resp (u + 1) J), 0) := rfl
    rw [e2, a₂', a₃]
  have hint : ∀ J ∈ ne, Integrable (fun v : TranslateValues F.Index =>
      v (ix.m (.rest u (B \ J)), 0) * (v (ix.m (.var u J), 0) - v (ix.m (.resp (u + 1) J), 0))) F.law := by
    intro J _
    have := (i2 (ix.m (.rest u (B \ J))) (ix.m (.var u J))).sub (i2 (ix.m (.rest u (B \ J))) (ix.m (.resp (u + 1) J)))
    refine this.congr (ae_of_all _ fun v => ?_)
    simp [mul_sub]
  have h1 := condExp_sub (μ := F.law) (i1 (ix.m (.product u))) (i1 (ix.m (.product (u + 1)))) (shiftInvariantSigma F.Index)
  have h2 := condExp_congr_ae (μ := F.law) (m := shiftInvariantSigma F.Index) R1
  have h3 := condExp_finsetSum (μ := F.law) (s := ne) hint (shiftInvariantSigma F.Index)
  have h4 : ∀ᵐ v ∂F.law, ∀ J ∈ ne,
      |F.condMean (fun v => v (ix.m (.rest u (B \ J)), 0) * (v (ix.m (.var u J), 0) - v (ix.m (.resp (u + 1) J), 0))) v| ≤
      a J + e J * ((box.card : ℝ) * b J) := by
    refine (ae_ball_iff ne.countable_toSet).2 fun J hJ => ?_
    filter_upwards [R3 J hJ, R4 J hJ] with v x₁ x₂
    rw [x₂]
    exact x₁
  filter_upwards [h1, h2, h3, h4] with v x₁ x₂ x₃ x₄
  have e5 : F.condMeanAt (ix.m (.product u)) v - F.condMeanAt (ix.m (.product (u + 1))) v =
      ∑ J ∈ ne, F.condMean (fun v => v (ix.m (.rest u (B \ J)), 0) * (v (ix.m (.var u J), 0) - v (ix.m (.resp (u + 1) J), 0))) v := by
    have y₁ : F.condMeanAt (ix.m (.product u)) v - F.condMeanAt (ix.m (.product (u + 1))) v =
        (F.law[(fun v => v (ix.m (.product u), 0)) - fun v => v (ix.m (.product (u + 1)), 0) | shiftInvariantSigma F.Index]) v := by
      rw [x₁]
      rfl
    have y₂ : (F.law[(fun v => v (ix.m (.product u), 0)) - fun v => v (ix.m (.product (u + 1)), 0) | shiftInvariantSigma F.Index]) v =
        (F.law[fun v => ∑ J ∈ ne, v (ix.m (.rest u (B \ J)), 0) * (v (ix.m (.var u J), 0) - v (ix.m (.resp (u + 1) J), 0)) |
          shiftInvariantSigma F.Index]) v := x₂
    have y₃ : (F.law[fun v => ∑ J ∈ ne, v (ix.m (.rest u (B \ J)), 0) * (v (ix.m (.var u J), 0) - v (ix.m (.resp (u + 1) J), 0)) |
          shiftInvariantSigma F.Index]) v =
        ∑ J ∈ ne, F.condMean (fun v => v (ix.m (.rest u (B \ J)), 0) * (v (ix.m (.var u J), 0) - v (ix.m (.resp (u + 1) J), 0))) v := by
      have x₃' := x₃
      rw [Finset.sum_apply] at x₃'
      refine Eq.trans ?_ x₃'
      congr 1
      funext w
      simp
    rw [y₁, y₂, y₃]
  rw [e5]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum x₄)
private theorem abs_sub_le_sum_of_steps {f : ℕ → TranslateValues F.Index → ℝ} {d : ℕ → ℝ} (t : ℕ)
    (h : ∀ u < t, ∀ᵐ v ∂F.law, |f u v - f (u + 1) v| ≤ d u) :
    ∀ᵐ v ∂F.law, |f 0 v - f t v| ≤ ∑ u ∈ Finset.range t, d u := by
  induction t with
  | zero => exact ae_of_all _ fun v => by simp
  | succ t ih =>
    filter_upwards [ih fun u hu => h u (by omega), h t (by omega)] with v a b
    rw [Finset.sum_range_succ]
    have := abs_sub_le (f 0 v) (f t v) (f (t + 1) v)
    linarith
private theorem responseAtLevel_lastSeparated {Λ : MomentParameters} (S' : MomentPoint Λ) {u : ℕ} (h : u = S'.lastSeparated)
    (i : Fin Λ.k) (d : MarkedSample Λ.stepParams S'.data.windowLevel (S'.data.period Λ.stepParams.side)) :
    responseAtLevel u i S' d = S'.supportTotal S'.lastSeparated (S'.sideAtLevel S'.lastSeparated) i
      (S'.stateAtLevel S'.lastSeparated S'.lastSeparated_le d) := by
  subst h
  unfold responseAtLevel
  rw [dif_pos S'.lastSeparated_le]
private theorem condMeanAt_top_eq (hk : (translatedTori F.points F.period).IsPreserving) (hM : jointLimitPropertiesStatement)
    (ix : TelescopeIndices F t B c) (hts : ∀ n, (F.points n).lastSeparated = t)
    (j' : F.Index) (hj' : F.observables j' = responseProduct B) :
    F.condMeanAt j' =ᵐ[F.law] F.condMeanAt (ix.m (.product t)) := by
  have h := ae_eq_of_eventually_eq F.isJointLimitLaw (I := Bool) (fun x => if x then j' else ix.m (.product t))
    (fun x => x true) (fun x => x false)
    (by fun_prop) (by fun_prop) (Eventually.of_forall fun n => ae_of_all _ fun ω => ?_)
  · have h' : evalAtZero j' =ᵐ[F.law] evalAtZero (ix.m (.product t)) := by
      filter_upwards [h] with v hv
      simpa [evalAtZero] using hv
    exact condExp_congr_ae h'
  · obtain ⟨d, hd⟩ : ∃ d, d = (F.points n).sampleOf F.rule ω := ⟨_, rfl⟩
    have e1 : ∀ j, sampleFamily F.rule F.points F.period (F.observables j) n ω = F.observables j (F.points n) d := fun j => by
      rw [hd]; rfl
    simp only [if_true, Bool.false_eq_true, if_false, e1]
    rw [hj', ix.product t le_rfl]
    refine Finset.prod_congr rfl fun i _ => ?_
    show _ = responseAtLevel t i (F.points n) d + ∑ j ∈ Finset.Ico t t, centredStepScore j i (F.points n) d
    rw [responseAtLevel_lastSeparated (F.points n) (hts n).symm]
    simp
private theorem condMeanAt_bottom_eq (hk : (translatedTori F.points F.period).IsPreserving) (hM : jointLimitPropertiesStatement)
    (ix : TelescopeIndices F t B c) (hts : ∀ n, (F.points n).lastSeparated = t)
    (hae : ∀ n (Q : MarkedSample Λ.stepParams (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side) → Prop),
      (∀ᵐ w ∂((F.points n).law (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side)), Q w) →
        ∀ᵐ ω ∂(F.points n).sampleLaw, Q ((F.points n).sampleOf F.rule ω))
    (hc : ∀ i, Tendsto (fun m => (F.points m).kappaAtLast i) atTop (𝓝 (c i)))
    (hH : ∀ n i, ∀ᵐ w ∂((F.points n).law (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side)),
      completedObservable (F.points n).tower (F.points n).coeff (F.points n).lastSeparated
          ((F.points n).sideAtLevel (F.points n).lastSeparated) ((F.points n).weight i _)
          ((F.points n).sampleAtLevel (F.points n).lastSeparated (F.points n).lastSeparated_le w) -
          (F.points n).kappa (F.points n).lastSeparated ((F.points n).sideAtLevel (F.points n).lastSeparated) i =
        responseAtLevel 0 i (F.points n) w + ∑ j ∈ Finset.range (F.points n).lastSeparated, centredStepScore j i (F.points n) w) :
    F.condMeanAt (ix.m .completed) =ᵐ[F.law] F.condMeanAt (ix.m (.product 0)) := by
  classical
  have h1 := ae_eq_of_eventually_eq F.isJointLimitLaw (I := Bool ⊕ (Fin Λ.k × Bool))
    (Sum.elim (fun x => if x then ix.m .completed else ix.m (.product 0))
      (fun p => if p.2 then ix.m (.line 0 p.1) else ix.m (.off p.1)))
    (fun x => x (.inl true)) (fun x => ∏ i ∈ B, (x (.inr (i, true)) + x (.inr (i, false))))
    (by fun_prop) (by fun_prop) (Eventually.of_forall fun n => ?_)
  · have h2 := ae_eq_of_eventually_eq F.isJointLimitLaw (I := Bool ⊕ (Fin Λ.k × Bool))
      (Sum.elim (fun x => if x then ix.m .completed else ix.m (.product 0))
        (fun p => if p.2 then ix.m (.line 0 p.1) else ix.m (.off p.1)))
      (fun x => x (.inl false)) (fun x => ∏ i ∈ B, x (.inr (i, true)))
      (by fun_prop) (by fun_prop) (Eventually.of_forall fun n => ae_of_all _ fun ω => ?_)
    · have h3 : ∀ᵐ v ∂F.law, ∀ i, v (ix.m (.off i), 0) = 0 := ae_all_iff.2 fun i =>
        ae_eq_zero_of_tendsto F.isJointLimitLaw (ix.m (.off i)) (fun n => (F.points n).kappaAtLast i - c i)
          (by simpa using (hc i).sub_const (c i)) (fun n ω => by
            show F.observables (ix.m (.off i)) (F.points n) _ = _
            rw [ix.off]
            rfl) hk
      have h' : evalAtZero (ix.m .completed) =ᵐ[F.law] evalAtZero (ix.m (.product 0)) := by
        filter_upwards [h1, h2, h3] with v x₁ x₂ x₃
        simp only [Sum.elim_inl, Sum.elim_inr, if_true, Bool.false_eq_true, if_false, x₃, add_zero] at x₁ x₂
        show v (ix.m .completed, 0) = v (ix.m (.product 0), 0)
        rw [x₁, x₂]
      exact condExp_congr_ae h'
    · obtain ⟨d, hd⟩ : ∃ d, d = (F.points n).sampleOf F.rule ω := ⟨_, rfl⟩
      have e1 : ∀ j, sampleFamily F.rule F.points F.period (F.observables j) n ω = F.observables j (F.points n) d := fun j => by
        rw [hd]; rfl
      simp only [Sum.elim_inl, Sum.elim_inr, if_true, Bool.false_eq_true, if_false, e1]
      rw [ix.product 0 (Nat.zero_le _)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [ix.line 0 i (Nat.zero_le _)]
  · have h0 := hae n _ (ae_all_iff.2 (hH n))
    filter_upwards [h0] with ω hω
    obtain ⟨d, hd⟩ : ∃ d, d = (F.points n).sampleOf F.rule ω := ⟨_, rfl⟩
    replace hω : ∀ i, completedObservable (F.points n).tower (F.points n).coeff (F.points n).lastSeparated
          ((F.points n).sideAtLevel (F.points n).lastSeparated) ((F.points n).weight i _)
          ((F.points n).sampleAtLevel (F.points n).lastSeparated (F.points n).lastSeparated_le d) -
          (F.points n).kappa (F.points n).lastSeparated ((F.points n).sideAtLevel (F.points n).lastSeparated) i =
        responseAtLevel 0 i (F.points n) d + ∑ j ∈ Finset.range (F.points n).lastSeparated, centredStepScore j i (F.points n) d := by
      rw [hd]
      exact hω
    have e1 : ∀ j, sampleFamily F.rule F.points F.period (F.observables j) n ω = F.observables j (F.points n) d := fun j => by
      rw [hd]; rfl
    simp only [Sum.elim_inl, Sum.elim_inr, if_true, Bool.false_eq_true, if_false, e1]
    rw [ix.completed]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ix.line 0 i (Nat.zero_le _), ix.off]
    have h5 := hω i
    have hsum : ∑ j ∈ Finset.range (F.points n).lastSeparated, centredStepScore j i (F.points n) d =
        ∑ j ∈ Finset.Ico 0 t, centredStepScore j i (F.points n) d := by
      rw [hts n, Finset.range_eq_Ico]
    rw [hsum] at h5
    show _ - c i = responseAtLevel 0 i (F.points n) d + ∑ j ∈ Finset.Ico 0 t, centredStepScore j i (F.points n) d +
      ((F.points n).kappa (F.points n).lastSeparated ((F.points n).sideAtLevel (F.points n).lastSeparated) i - c i)
    rw [← h5]
    ring
end Core
private def termObservable (t K : ℕ) (B : Finset (Fin Λ.k)) (c : Fin Λ.k → ℝ) : TelescopeTerm Λ.k → SampleObservable Λ
  | .line u i => if u ≤ t then partialSum t u i else fun _ _ => 0
  | .product u => if u ≤ t then partialProduct t u B else fun _ _ => 0
  | .rest u I => tailProduct t u I
  | .var u J => if u < t then variableProduct u J else fun _ _ => 0
  | .mean u J => if u < t ∧ J.Nonempty then variableMean u J else fun _ _ => 0
  | .resp u J => if u ≤ t then responseProductAt u J else fun _ _ => 0
  | .size u z p => if u ≤ K then hullSizePower u z p else fun _ _ => 0
  | .off i => kappaOffset c i
  | .completed => completedProduct c B
private def TelescopeTerm.encode {k : ℕ} : TelescopeTerm k → ℕ × ℕ × ℕ × Finset (Fin k) × (Fin 4 → ℤ) × Option (Fin k)
  | .line u i => (0, u, 0, ∅, 0, some i)
  | .product u => (1, u, 0, ∅, 0, none)
  | .rest u I => (2, u, 0, I, 0, none)
  | .var u J => (3, u, 0, J, 0, none)
  | .mean u J => (4, u, 0, J, 0, none)
  | .resp u J => (5, u, 0, J, 0, none)
  | .size u z p => (6, u, p, ∅, z, none)
  | .off i => (7, 0, 0, ∅, 0, some i)
  | .completed => (8, 0, 0, ∅, 0, none)
private instance (k : ℕ) : Countable (TelescopeTerm k) := by
  refine Function.Injective.countable (f := TelescopeTerm.encode) ?_
  intro a b h
  cases a <;> cases b <;> simp_all [TelescopeTerm.encode]
private theorem hasBoundedMoments_term {rule : NoiseRule Λ.stepParams} {Sq : ℕ → MomentPoint Λ} {p t K : ℕ} {B : Finset (Fin Λ.k)}
    {c : Fin Λ.k → ℝ} {s : ℕ}
    (hk : (translatedTori Sq p).IsPreserving) (hts : t ≤ s) (hall : ∀ m, t = (Sq m).lastSeparated) {bc : ℝ}
    (hbc : ∀ m i, |(Sq m).kappaAtLast i| ≤ bc)
    (h₁ : ∀ u ≤ s, ∀ i : Fin Λ.k, TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (responseAtLevel u i)))
    (h₂ : ∀ u < s, ∀ i : Fin Λ.k, TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (centredStepScore u i)))
    (h₃ : ∀ u < s, ∀ J : Finset (Fin Λ.k), TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (variableProduct u J)))
    (h₄ : ∀ u ≤ K, ∀ (z : Fin 4 → ℤ) (k : ℕ), TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (hullSizePower u z k)))
    (h₅ : ∀ u, (∀ m, u < (Sq m).lastSeparated) → ∀ J : Finset (Fin Λ.k), J.Nonempty →
      TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (variableMean u J)))
    (h₆ : TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (completedProduct c B))) (a : TelescopeTerm Λ.k) :
    TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (termObservable t K B c a)) := by
  have hzero : TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (fun _ _ => 0 : SampleObservable Λ)) :=
    hasBoundedMoments_const hk (fun _ => 0) 0 (fun _ => by simp)
  have hsteps : ∀ (v : ℕ) (i : Fin Λ.k), TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p
      (fun S w => ∑ j ∈ Finset.Ico v t, centredStepScore j i S w : SampleObservable Λ)) := fun v i =>
    hasBoundedMoments_sum hk _ fun j hj => h₂ j ((Finset.mem_Ico.mp hj).2.trans_le hts) i
  have hline : ∀ u ≤ t, ∀ i, TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (partialSum t u i)) := fun u hu i =>
    hasBoundedMoments_add (h₁ u (hu.trans hts) i) (hsteps u i)
  cases a with
  | line u i =>
    by_cases h : u ≤ t
    · have e : termObservable t K B c (.line u i) = partialSum t u i := if_pos h
      rw [e]
      exact hline u h i
    · have e : termObservable t K B c (.line u i) = fun _ _ => 0 := if_neg h
      rw [e]
      exact hzero
  | product u =>
    by_cases h : u ≤ t
    · have e : termObservable t K B c (.product u) = partialProduct t u B := if_pos h
      rw [e]
      exact hasBoundedMoments_prod hk B fun i _ => hline u h i
    · have e : termObservable t K B c (.product u) = fun _ _ => 0 := if_neg h
      rw [e]
      exact hzero
  | rest u I => exact hasBoundedMoments_prod hk I fun i _ => hsteps (u + 1) i
  | var u J =>
    by_cases h : u < t
    · have e : termObservable t K B c (.var u J) = variableProduct u J := if_pos h
      rw [e]
      exact h₃ u (h.trans_le hts) J
    · have e : termObservable t K B c (.var u J) = fun _ _ => 0 := if_neg h
      rw [e]
      exact hzero
  | mean u J =>
    by_cases h : u < t ∧ J.Nonempty
    · have e : termObservable t K B c (.mean u J) = variableMean u J := if_pos h
      rw [e]
      exact h₅ u (fun m => hall m ▸ h.1) J h.2
    · have e : termObservable t K B c (.mean u J) = fun _ _ => 0 := if_neg h
      rw [e]
      exact hzero
  | resp u J =>
    by_cases h : u ≤ t
    · have e : termObservable t K B c (.resp u J) = responseProductAt u J := if_pos h
      rw [e]
      exact hasBoundedMoments_prod hk J fun i _ => h₁ u (h.trans hts) i
    · have e : termObservable t K B c (.resp u J) = fun _ _ => 0 := if_neg h
      rw [e]
      exact hzero
  | size u z q =>
    by_cases h : u ≤ K
    · have e : termObservable t K B c (.size u z q) = hullSizePower u z q := if_pos h
      rw [e]
      exact h₄ u h z q
    · have e : termObservable t K B c (.size u z q) = fun _ _ => 0 := if_neg h
      rw [e]
      exact hzero
  | off i =>
    exact hasBoundedMoments_const hk (fun m => (Sq m).kappaAtLast i - c i) (bc + |c i|) fun m =>
      (abs_sub _ _).trans (add_le_add (hbc m i) le_rfl)
  | completed => exact h₆
end Field
section ResponsesNearForms
variable {Λ : MomentParameters}
private theorem points_fields {S : MomentPoint Λ} (F : LimitLawAtPoint S) (n : ℕ) :
    (F.points n).data.scaleLevel = S.data.scaleLevel ∧ (F.points n).data.windowLevel = S.data.windowLevel ∧
      (F.points n).β = S.β ∧ (F.points n).tower = S.tower := by
  obtain ⟨hp, hs, h⟩ := F.points_eq n
  rw [h]
  exact ⟨rfl, rfl, rfl, rfl⟩
private theorem exists_subseq_const (f : ℕ → ℕ) (s : ℕ) (h : ∀ n, f n ≤ s) :
    ∃ (t : ℕ) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ n, f (φ n) = t := by
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber (fun n => (⟨f n, Nat.lt_succ_of_le (h n)⟩ : Fin (s + 1)))
  have hinf := Set.infinite_coe_iff.mp hy
  have hfr := Nat.frequently_atTop_iff_infinite.mpr hinf
  obtain ⟨φ, hφ, hP⟩ := Filter.extraction_of_frequently_atTop hfr
  exact ⟨y.1, φ, hφ, fun n => congrArg Fin.val (hP n)⟩
private theorem ae_sampleOf (hAR : ruleDrawsChainStatement) (hf : Λ.stepParams.Admissible) {S : MomentPoint Λ}
    (F : LimitLawAtPoint S) (n : ℕ)
    (Q : MarkedSample Λ.stepParams (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side) → Prop)
    (h : ∀ᵐ w ∂((F.points n).law (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side)), Q w) :
    ∀ᵐ ω ∂(F.points n).sampleLaw, Q ((F.points n).sampleOf F.rule ω) := by
  obtain ⟨-, -, -, hT⟩ := points_fields F n
  have hrule : F.rule.IsAdmissible (F.points n).tower := by
    rw [hT]
    exact F.rule_admissible
  have hL := hf.L_ge
  have hn : 3 ≤ Λ.stepParams.n₀ := le_trans (by norm_num) hf.n₀_ge
  have hs := (F.points n).side_le
  have hm : (F.points n).data.sideExponent ≠ 0 := by
    intro h0
    unfold LevelData.period at hs
    rw [h0] at hs
    simp only [pow_zero, mul_one] at hs
    have : 2 ^ 16 * 3 ≤ Λ.stepParams.side * Λ.stepParams.n₀ := Nat.mul_le_mul hL hn
    omega
  have hdiv : Λ.stepParams.side ∣ (F.points n).data.period Λ.stepParams.side := by
    obtain ⟨m, hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm
    unfold LevelData.period
    rw [hm', pow_succ]
    exact Dvd.dvd.mul_left (Dvd.intro_left _ rfl) _
  have h64 : 64 ≤ (F.points n).data.period Λ.stepParams.side := by
    have : 2 ^ 16 * 3 ≤ Λ.stepParams.side * Λ.stepParams.n₀ := Nat.mul_le_mul hL hn
    omega
  obtain ⟨hmeas, hmap⟩ := hAR Λ.stepParams hf (F.points n).tower F.rule (F.points n).β (F.points n).isCutoff
    (F.points n).marksMeasurable hrule (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side) hdiv h64
  refine ae_of_ae_map (p := Q) (f := fun p : (F.points n).SampleSpace =>
    F.rule.chain (F.points n).tower (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side) p.1 p.2)
    hmeas.aemeasurable ?_
  unfold MomentPoint.sampleLaw
  rw [hmap]
  exact h
private theorem abs_tail_mul_le {S' : MomentPoint Λ} {t u : ℕ} {B J : Finset (Fin Λ.k)} {Cn ρ E : ℝ} (hρ0 : 0 ≤ ρ) (hE0 : 0 ≤ E)
    (hρ : ∀ w, |tailProduct t u (B \ J) S' w| ≤ ρ) (hE : S'.stepErrorBound Cn u J ≤ E)
    (hsp : ∀ᵐ w ∂(S'.law S'.data.windowLevel (S'.data.period Λ.stepParams.side)),
      |variableMean u J S' w - ∏ i ∈ J, responseAtLevel (u + 1) i S' w| ≤
        S'.stepErrorBound Cn u J * ∏ i ∈ J, meanScoreAtLevel (u + 1) i S' w)
    (hN1 : ∀ w i, 1 ≤ meanScoreAtLevel (u + 1) i S' w) (box : Finset (Fin 4 → ℤ))
    (hN : ∀ w, ∏ i ∈ J, meanScoreAtLevel (u + 1) i S' w ≤ 1 + 2 ^ J.card * (1 + ∑ z ∈ box, hullSizePower (u + 1) z J.card S' w)) :
    ∀ᵐ w ∂(S'.law S'.data.windowLevel (S'.data.period Λ.stepParams.side)),
      |tailProduct t u (B \ J) S' w * (variableMean u J S' w - responseProductAt (u + 1) J S' w)| ≤
      (ρ * E) * (1 + 2 ^ J.card) + ((ρ * E) * 2 ^ J.card) * ∑ z ∈ box, hullSizePower (u + 1) z J.card S' w := by
  filter_upwards [hsp] with w hw
  have hN0 : 0 ≤ ∏ i ∈ J, meanScoreAtLevel (u + 1) i S' w := Finset.prod_nonneg fun i _ => zero_le_one.trans (hN1 w i)
  have h1 : |variableMean u J S' w - responseProductAt (u + 1) J S' w| ≤
      E * (1 + 2 ^ J.card * (1 + ∑ z ∈ box, hullSizePower (u + 1) z J.card S' w)) :=
    hw.trans ((mul_le_mul_of_nonneg_right hE hN0).trans (mul_le_mul_of_nonneg_left (hN w) hE0))
  rw [abs_mul]
  calc _ ≤ ρ * (E * (1 + 2 ^ J.card * (1 + ∑ z ∈ box, hullSizePower (u + 1) z J.card S' w))) :=
        mul_le_mul (hρ w) h1 (abs_nonneg _) hρ0
    _ = _ := by ring
private theorem sum_step_terms_le {ι : Type} [DecidableEq ι] {B : Finset ι} (hB : B.card ≤ 8) {K₁ P E₇ G Cs : ℝ} (hK₁ : 0 ≤ K₁)
    (hP : 1 ≤ P) (hE₇ : 0 ≤ E₇) (hG : 0 ≤ G) (hCs : 0 ≤ Cs) (box : Finset ι → ℝ) (hbox : ∀ J, box J ≤ G * P ^ 4) :
    ∑ J ∈ B.powerset.filter Finset.Nonempty, ((K₁ * P ^ 76 * E₇) * (1 + 2 ^ J.card) + ((K₁ * P ^ 76 * E₇) * 2 ^ J.card) * (box J * Cs)) ≤
      2 ^ 8 * (K₁ * 2 ^ 9 * (1 + G * Cs)) * (P ^ 80 * E₇) := by
  have hκ : 0 ≤ K₁ * P ^ 76 * E₇ := by positivity
  have hP4 : 1 ≤ P ^ 4 := one_le_pow₀ hP
  have hterm : ∀ J ∈ B.powerset.filter Finset.Nonempty,
      (K₁ * P ^ 76 * E₇) * (1 + 2 ^ J.card) + ((K₁ * P ^ 76 * E₇) * 2 ^ J.card) * (box J * Cs) ≤
      K₁ * 2 ^ 9 * (1 + G * Cs) * (P ^ 80 * E₇) := by
    intro J hJ
    have hJc : J.card ≤ 8 := (Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hJ).1)).trans hB
    have h2 : (2 : ℝ) ^ J.card ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) hJc
    have h1 : (1 : ℝ) ≤ 2 ^ J.card := one_le_pow₀ (by norm_num)
    have hb : box J * Cs ≤ G * P ^ 4 * Cs := mul_le_mul_of_nonneg_right (hbox J) hCs
    have e1 : (1 + (2 : ℝ) ^ J.card) + 2 ^ J.card * (box J * Cs) ≤ 2 ^ 9 * ((1 + G * Cs) * P ^ 4) := by
      have h3 : (2 : ℝ) ^ J.card * (box J * Cs) ≤ 2 ^ 8 * (G * P ^ 4 * Cs) := by
        by_cases h0 : box J * Cs ≤ 0
        · have : (2 : ℝ) ^ J.card * (box J * Cs) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h0
          have h4 : 0 ≤ (2 : ℝ) ^ 8 * (G * P ^ 4 * Cs) := by positivity
          linarith
        · exact mul_le_mul h2 hb (not_le.mp h0).le (by positivity)
      have h5 : 0 ≤ G * Cs := by positivity
      nlinarith
    calc _ = (K₁ * P ^ 76 * E₇) * ((1 + (2 : ℝ) ^ J.card) + 2 ^ J.card * (box J * Cs)) := by ring
      _ ≤ (K₁ * P ^ 76 * E₇) * (2 ^ 9 * ((1 + G * Cs) * P ^ 4)) := mul_le_mul_of_nonneg_left e1 hκ
      _ = _ := by ring
  have hcard : ((B.powerset.filter Finset.Nonempty).card : ℝ) ≤ 2 ^ 8 := by
    have h1 : (B.powerset.filter Finset.Nonempty).card ≤ 2 ^ B.card :=
      (Finset.card_filter_le _ _).trans (Finset.card_powerset B).le
    have h2 : 2 ^ B.card ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) hB
    exact_mod_cast h1.trans h2
  have hnn : 0 ≤ K₁ * 2 ^ 9 * (1 + G * Cs) * (P ^ 80 * E₇) := by positivity
  calc _ ≤ ∑ _J ∈ B.powerset.filter Finset.Nonempty, K₁ * 2 ^ 9 * (1 + G * Cs) * (P ^ 80 * E₇) := Finset.sum_le_sum hterm
    _ = ((B.powerset.filter Finset.Nonempty).card : ℝ) * (K₁ * 2 ^ 9 * (1 + G * Cs) * (P ^ 80 * E₇)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ 8 * (K₁ * 2 ^ 9 * (1 + G * Cs) * (P ^ 80 * E₇)) := mul_le_mul_of_nonneg_right hcard hnn
    _ = _ := by ring
private theorem abs_condMeanAt_le_of_bound {S : MomentPoint Λ} {F : LimitLawAtPoint S} {t : ℕ} {B : Finset (Fin Λ.k)} {c : Fin Λ.k → ℝ}
    (hM : jointLimitPropertiesStatement) (hk : (translatedTori F.points F.period).IsPreserving) (ix : TelescopeIndices F t B c)
    (hae : ∀ n (Q : MarkedSample Λ.stepParams (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side) → Prop),
      (∀ᵐ w ∂((F.points n).law (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side)), Q w) →
        ∀ᵐ ω ∂(F.points n).sampleLaw, Q ((F.points n).sampleOf F.rule ω))
    (hK : t ≤ S.data.windowLevel) (j' : F.Index) (box : Finset (Fin 4 → ℤ)) (p : ℕ) (a e b : ℝ) (he : 0 ≤ e)
    (hB : ∀ n, ∀ᵐ w ∂((F.points n).law (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side)),
      |F.observables j' (F.points n) w| ≤ a + e * ∑ z ∈ box, hullSizePower t z p (F.points n) w)
    (hS : ∀ z ∈ box, ∀ᵐ v ∂F.law, F.condMeanAt (ix.m (.size t z p)) v ≤ b) :
    ∀ᵐ v ∂F.law, |F.condMeanAt j' v| ≤ a + e * ((box.card : ℝ) * b) := by
  classical
  have hP : IsProbabilityMeasure F.law := F.isJointLimitLaw.isProbability
  have i1 := integrable_coord hM hk
  have R : ∀ᵐ v ∂F.law, |v (j', 0)| ≤ a + e * ∑ z ∈ box, v (ix.m (.size t z p), 0) := by
    have h := ae_le_of_eventually_le F.isJointLimitLaw (I := Unit ⊕ {z // z ∈ box})
      (Sum.elim (fun _ => j') (fun z => ix.m (.size t z.1 p)))
      (fun x => |x (.inl ())| - (a + e * ∑ z : {z // z ∈ box}, x (.inr z)))
      (by fun_prop) (Eventually.of_forall fun n => ?_)
    · filter_upwards [h] with v hv
      simp only [Sum.elim_inl, Sum.elim_inr] at hv
      have e3 := Finset.sum_coe_sort box fun z => v (ix.m (.size t z p), 0)
      rw [e3] at hv
      linarith
    · have h0 := hae n _ (hB n)
      filter_upwards [h0] with ω hω
      obtain ⟨d, hd⟩ : ∃ d, d = (F.points n).sampleOf F.rule ω := ⟨_, rfl⟩
      replace hω : |F.observables j' (F.points n) d| ≤ a + e * ∑ z ∈ box, hullSizePower t z p (F.points n) d := by
        rw [hd]
        exact hω
      have e1 : ∀ j, sampleFamily F.rule F.points F.period (F.observables j) n ω = F.observables j (F.points n) d := fun j => by
        rw [hd]; rfl
      simp only [Sum.elim_inl, Sum.elim_inr, e1]
      have e3 := Finset.sum_coe_sort box fun z => F.observables (ix.m (.size t z p)) (F.points n) d
      rw [e3, Finset.sum_congr rfl fun z _ => by rw [ix.size t z p hK]]
      linarith
  have hsz : ∀ z ∈ box, Integrable (fun v : TranslateValues F.Index => v (ix.m (.size t z p), 0)) F.law := fun z _ => i1 _
  have h1 := abs_invariantCondExp_le (i1 j') ((integrable_const a).add ((integrable_finsetSum _ hsz).const_mul e)) R
  have h2 := invariantCondExp_affine_sum_le box (fun z (v : TranslateValues F.Index) => v (ix.m (.size t z p), 0)) hsz b a e he hS
  filter_upwards [h1, h2] with v x₁ x₂
  exact x₁.trans x₂
private theorem supportRadius_points {S : MomentPoint Λ} (F : LimitLawAtPoint S) (n u : ℕ) :
    (F.points n).supportRadius u = S.supportRadius u := by
  unfold MomentPoint.supportRadius
  rw [(points_fields F n).1]
private theorem bounds_of_indices {S : MomentPoint Λ} {F : LimitLawAtPoint S} {t : ℕ} {B : Finset (Fin Λ.k)} {c : Fin Λ.k → ℝ}
    (hs₁ : 0 ≤ Λ.response.s₁) (hC : 0 ≤ Λ.response.C₀) (hL : (2 : ℝ) ≤ Λ.stepParams.side) (hrt : 0 ≤ Λ.stepParams.rt)
    (hM : jointLimitPropertiesStatement) (hk : (translatedTori F.points F.period).IsPreserving) (ix : TelescopeIndices F t B c)
    (hae : ∀ n (Q : MarkedSample Λ.stepParams (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side) → Prop),
      (∀ᵐ w ∂((F.points n).law (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side)), Q w) →
        ∀ᵐ ω ∂(F.points n).sampleLaw, Q ((F.points n).sampleOf F.rule ω))
    (hts : ∀ n, (F.points n).lastSeparated = t) (htS : t ≤ S.data.scaleLevel) (hsK : S.data.scaleLevel ≤ S.data.windowLevel)
    (hc : ∀ i, Tendsto (fun m => (F.points m).kappaAtLast i) atTop (𝓝 (c i))) (hB8 : B.card ≤ 8)
    {A₂ M₁ Cn Cs : ℝ} (hA₂ : 0 ≤ A₂) (hM₁ : 4 * Λ.response.C₀ * A₂ ≤ M₁) (hM1 : 1 ≤ M₁) (hCs : 0 ≤ Cs) (D : ℕ → ℝ)
    (hD : ∀ n, ∀ u < t, D u ≤ ((F.points n).data.separation Λ.stepParams.side u : ℝ))
    (hsites : ∀ n, ∀ j ≤ (F.points n).data.scaleLevel, ∀ i : Fin Λ.k,
      (((F.points n).data.supportSites Λ.stepParams.side j i).card : ℝ) ≤
        A₂ * (Λ.stepParams.side : ℝ) ^ (4 * ((F.points n).data.scaleLevel - j)))
    (hT₁ : ∀ n i, ∀ᵐ w ∂((F.points n).law (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side)),
      completedObservable (F.points n).tower (F.points n).coeff (F.points n).lastSeparated
          ((F.points n).sideAtLevel (F.points n).lastSeparated) ((F.points n).weight i _)
          ((F.points n).sampleAtLevel (F.points n).lastSeparated (F.points n).lastSeparated_le w) -
          (F.points n).kappa (F.points n).lastSeparated ((F.points n).sideAtLevel (F.points n).lastSeparated) i =
        responseAtLevel 0 i (F.points n) w + ∑ j ∈ Finset.range (F.points n).lastSeparated, centredStepScore j i (F.points n) w)
    (hT₂ : ∀ n, ∀ u < t, ∀ J, ∀ᵐ w ∂((F.points n).law (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side)),
      variableProduct u J (F.points n) w = ∏ i ∈ J, (responseAtLevel u i (F.points n) w + centredStepScore u i (F.points n) w))
    (hV : ∀ n, ∀ u < t, ∀ J : Finset (Fin Λ.k), J.Nonempty →
      ∀ᵐ w ∂((F.points n).law (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side)),
      |variableMean u J (F.points n) w - ∏ i ∈ J, responseAtLevel (u + 1) i (F.points n) w| ≤
        (F.points n).stepErrorBound Cn u J * ∏ i ∈ J, meanScoreAtLevel (u + 1) i (F.points n) w)
    (hZ₁ : ∀ n, ∀ u < (F.points n).data.scaleLevel, ∀ (i : Fin Λ.k)
      (w : MarkedSample Λ.stepParams (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side)),
      |centredStepScore u i (F.points n) w| ≤ 2 * (Λ.response.C₀ * (((F.points n).data.supportSites Λ.stepParams.side u i).card : ℝ)))
    (hZ₂ : ∀ n, ∀ u ≤ (F.points n).data.scaleLevel, ∀ i : Fin Λ.k,
      ∀ᵐ w ∂((F.points n).law (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side)),
      |responseAtLevel u i (F.points n) w| ≤
        Λ.response.C₀ * (((F.points n).data.supportSites Λ.stepParams.side u i).card : ℝ) * meanScoreAtLevel u i (F.points n) w)
    (hN : ∀ n, ∀ u ≤ (F.points n).data.scaleLevel,
      ∀ w : MarkedSample Λ.stepParams (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side),
      (∀ i : Fin Λ.k, 1 ≤ meanScoreAtLevel u i (F.points n) w) ∧ ∀ J : Finset (Fin Λ.k), J.Nonempty →
        ∏ i ∈ J, meanScoreAtLevel u i (F.points n) w ≤
          1 + 2 ^ J.card * (1 + ∑ z ∈ offsetCube ((F.points n).supportRadius u), hullSizePower u z J.card (F.points n) w))
    (hHull : ∀ u ≤ S.data.windowLevel, ∀ (z : Fin 4 → ℤ) (p : ℕ), 1 ≤ p → p ≤ 8 →
      ∀ᵐ v ∂F.law, F.condMeanAt (ix.m (.size u z p)) v ≤ Cs)
    (hSc : ∀ j j' : F.Index, F.observables j = bottomProduct c B → F.observables j' = completedProduct c B →
      F.condMeanAt j =ᵐ[F.law] F.condMeanAt j')
    (hFar : ∀ u < t, ∀ J ∈ B.powerset.filter Finset.Nonempty,
      F.condMean (fun v => v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.var u J), 0)) =ᵐ[F.law]
        F.condMean (fun v => v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.mean u J), 0)))
    (j j' : F.Index) (hj : F.observables j = bottomProduct c B) (hj' : F.observables j' = responseProduct B) :
    (∀ᵐ v ∂F.law, |F.condMeanAt j v - F.condMeanAt j' v| ≤ ∑ u ∈ Finset.range t,
      2 ^ 8 * (((1 + 2 * Λ.response.C₀ * A₂) ^ 8 * (|Cn| * (8 * A₂) * M₁ ^ 8)) * 2 ^ 9 * (1 + (2 * |Λ.R| + 7) ^ 4 * Cs)) *
        (((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u)) ^ 80 * Real.exp (-(Λ.stepParams.rt * D u / 2 ^ 7)))) ∧
    ∀ᵐ v ∂F.law, |F.condMeanAt j' v| ≤ (M₁ * ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - t)) ^ 4) ^ 8 *
      (2 ^ 9 * (1 + (2 * |Λ.R| + 7) ^ 4 * ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - t)) ^ 4 * Cs)) := by
  classical
  have hs : ∀ n, (F.points n).data.scaleLevel = S.data.scaleLevel := fun n => (points_fields F n).1
  obtain ⟨K₁, hK₁d⟩ : ∃ K₁ : ℝ, K₁ = (1 + 2 * Λ.response.C₀ * A₂) ^ 8 * (|Cn| * (8 * A₂) * M₁ ^ 8) := ⟨_, rfl⟩
  have hK₁ : 0 ≤ K₁ := by
    rw [hK₁d]
    have : 0 ≤ 2 * Λ.response.C₀ * A₂ := by positivity
    positivity
  obtain ⟨G, hGd⟩ : ∃ G : ℝ, G = (2 * |Λ.R| + 7) ^ 4 := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by
    rw [hGd]
    positivity
  rw [← hK₁d, ← hGd]
  have hstep : ∀ u < t, ∀ᵐ v ∂F.law, |F.condMeanAt (ix.m (.product u)) v - F.condMeanAt (ix.m (.product (u + 1))) v| ≤
      2 ^ 8 * (K₁ * 2 ^ 9 * (1 + G * Cs)) *
        (((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u)) ^ 80 * Real.exp (-(Λ.stepParams.rt * D u / 2 ^ 7))) := by
    intro u hu
    obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u) := ⟨_, rfl⟩
    have hP1 : 1 ≤ P := hPd ▸ one_le_pow₀ (by linarith)
    obtain ⟨E₇, hE₇d⟩ : ∃ E₇ : ℝ, E₇ = Real.exp (-(Λ.stepParams.rt * D u / 2 ^ 7)) := ⟨_, rfl⟩
    have hE₇ : 0 ≤ E₇ := hE₇d ▸ (Real.exp_pos _).le
    rw [← hPd, ← hE₇d]
    have hκ : ∀ J : Finset (Fin Λ.k), 0 ≤ (K₁ * P ^ 76 * E₇) * 2 ^ J.card := fun J => by positivity
    have hb := abs_condMeanAt_step_le hM hk ix hae hu (fun n J => hT₂ n u hu J) (by omega) (offsetCube (S.supportRadius (u + 1)))
      (fun J => (K₁ * P ^ 76 * E₇) * (1 + 2 ^ J.card)) (fun J => (K₁ * P ^ 76 * E₇) * 2 ^ J.card) (fun _ => Cs) hκ ?_ (hFar u hu) ?_
    · filter_upwards [hb] with v hv
      refine hv.trans ?_
      refine sum_step_terms_le hB8 hK₁ hP1 hE₇ hG0 hCs (fun _ => ((offsetCube (S.supportRadius (u + 1))).card : ℝ)) fun _ => ?_
      rw [hGd]
      refine card_offsetCube_supportRadius_le S hL ?_
      rw [hPd]
      exact pow_le_pow_right₀ (by linarith) (by omega)
    · intro J hJ n
      have hJ' := Finset.mem_filter.mp hJ
      have hJB := Finset.mem_powerset.mp hJ'.1
      have hJc : J.card ≤ 8 := (Finset.card_le_card hJB).trans hB8
      have hI : (B \ J).card ≤ 8 := (Finset.card_le_card Finset.sdiff_subset).trans hB8
      have hρ := fun w => abs_tailProduct_le hA₂ hC hL (hZ₁ n) (hsites n) hu (by rw [hs n]; exact htS) (B \ J) hI w
      have hE := stepErrorBound_le (S' := F.points n) (Cn := Cn) (D := D u) hA₂ hC hL hM₁ hM1 (hsites n) (u := u)
        (by rw [hs n]; omega) J hJc hrt (hD n u hu)
      rw [hs n] at hE
      simp only [hs n] at hρ
      rw [← hPd, ← hE₇d] at hE
      simp only [← hPd] at hρ
      have ht := abs_tail_mul_le (t := t) (u := u) (B := B) (J := J) (Cn := Cn) (S' := F.points n) (by positivity)
        (by positivity : 0 ≤ |Cn| * (8 * (A₂ * P ^ 4)) * E₇ * (M₁ * P ^ 4) ^ 8) hρ hE (hV n u hu J hJ'.2)
        (fun w => (hN n (u + 1) (by rw [hs n]; omega) w).1) (offsetCube (S.supportRadius (u + 1)))
        (fun w => by
          have := (hN n (u + 1) (by rw [hs n]; omega) w).2 J hJ'.2
          rwa [supportRadius_points] at this)
      filter_upwards [ht] with w hw
      have e : ((1 + 2 * Λ.response.C₀ * A₂) * P ^ 5) ^ 8 * (|Cn| * (8 * (A₂ * P ^ 4)) * E₇ * (M₁ * P ^ 4) ^ 8) =
          K₁ * P ^ 76 * E₇ := by
        rw [hK₁d]
        ring
      rw [e] at hw
      exact hw
    · intro J hJ z _
      have hJ' := Finset.mem_filter.mp hJ
      have hJc : J.card ≤ 8 := (Finset.card_le_card (Finset.mem_powerset.mp hJ'.1)).trans hB8
      exact hHull (u + 1) (by omega) z J.card hJ'.2.card_pos hJc
  have hsum := abs_sub_le_sum_of_steps (F := F) (f := fun u => F.condMeanAt (ix.m (.product u))) t hstep
  have e1 : F.condMeanAt j =ᵐ[F.law] F.condMeanAt (ix.m .completed) := hSc j _ hj ix.completed
  have e2 := condMeanAt_bottom_eq hk hM ix hts hae hc hT₁
  have e3 := condMeanAt_top_eq hk hM ix hts j' hj'
  refine ⟨?_, ?_⟩
  · filter_upwards [hsum, e1, e2, e3] with v a₁ a₂ a₃ a₄
    rw [a₂, a₃, a₄]
    exact a₁
  obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - t) := ⟨_, rfl⟩
  have hP1 : 1 ≤ P := hPd ▸ one_le_pow₀ (by linarith)
  rw [← hPd]
  have hMP : 1 ≤ M₁ * P ^ 4 := one_le_mul_of_one_le_of_one_le hM1 (one_le_pow₀ hP1)
  have hQ1 : 1 ≤ (M₁ * P ^ 4) ^ 8 := one_le_pow₀ hMP
  have hQ0 : 0 ≤ (M₁ * P ^ 4) ^ 8 := by positivity
  have hGP : 0 ≤ G * P ^ 4 * Cs := by positivity
  rcases B.eq_empty_or_nonempty with rfl | hBn
  · have h := abs_condMeanAt_le_of_bound hM hk ix hae (htS.trans hsK) j' ∅ 0 1 0 0 le_rfl (fun n => ae_of_all _ fun w => by
      rw [hj']
      simp [responseProduct]) (fun z hz => absurd hz (Finset.notMem_empty z))
    filter_upwards [h] with v hv
    refine hv.trans ?_
    simp only [zero_mul, add_zero, mul_zero]
    have : (1 : ℝ) ≤ 2 ^ 9 * (1 + G * P ^ 4 * Cs) := by nlinarith
    nlinarith
  · have hp1 : 1 ≤ B.card := hBn.card_pos
    obtain ⟨Q, hQd⟩ : ∃ Q : ℝ, Q = (M₁ * P ^ 4) ^ 8 := ⟨_, rfl⟩
    rw [← hQd] at hQ0 hQ1 ⊢
    have h := abs_condMeanAt_le_of_bound hM hk ix hae (htS.trans hsK) j' (offsetCube (S.supportRadius t)) B.card
      (Q * (1 + 2 ^ B.card)) (Q * 2 ^ B.card) Cs (by positivity) ?_
      (fun z _ => hHull t (htS.trans hsK) z B.card hp1 hB8)
    · filter_upwards [h] with v hv
      refine hv.trans ?_
      have hcard : ((offsetCube (S.supportRadius t)).card : ℝ) ≤ G * P ^ 4 := by
        rw [hGd]
        exact card_offsetCube_supportRadius_le S hL hPd.ge
      have h2 : (2 : ℝ) ^ B.card ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) hB8
      have h3 : ((offsetCube (S.supportRadius t)).card : ℝ) * Cs ≤ G * P ^ 4 * Cs := mul_le_mul_of_nonneg_right hcard hCs
      have h4 : (2 : ℝ) ^ B.card * (((offsetCube (S.supportRadius t)).card : ℝ) * Cs) ≤ 2 ^ 9 * (G * P ^ 4 * Cs) := by
        have : (0 : ℝ) ≤ ((offsetCube (S.supportRadius t)).card : ℝ) * Cs := by positivity
        nlinarith
      have e4 : Q * (1 + 2 ^ B.card) + Q * 2 ^ B.card * (((offsetCube (S.supportRadius t)).card : ℝ) * Cs) =
          Q * ((1 + 2 ^ B.card) + 2 ^ B.card * (((offsetCube (S.supportRadius t)).card : ℝ) * Cs)) := by ring
      rw [e4]
      refine mul_le_mul_of_nonneg_left ?_ hQ0
      nlinarith
    · intro n
      have hall : ∀ᵐ w ∂((F.points n).law (F.points n).data.windowLevel ((F.points n).data.period Λ.stepParams.side)),
          ∀ i : Fin Λ.k, |responseAtLevel t i (F.points n) w| ≤
            Λ.response.C₀ * (((F.points n).data.supportSites Λ.stepParams.side t i).card : ℝ) * meanScoreAtLevel t i (F.points n) w :=
        ae_all_iff.2 fun i => hZ₂ n t (by rw [hs n]; exact htS) i
      filter_upwards [hall] with w hw
      have htn : t ≤ (F.points n).data.scaleLevel := by rw [hs n]; exact htS
      obtain ⟨hN1, hNJ⟩ := hN n t htn w
      have hNJ' := hNJ B hBn
      rw [supportRadius_points] at hNJ'
      have e5 : F.observables j' (F.points n) w = ∏ i ∈ B, responseAtLevel t i (F.points n) w := by
        rw [hj']
        refine Finset.prod_congr rfl fun i _ => ?_
        exact (responseAtLevel_lastSeparated (F.points n) (hts n).symm i w).symm
      rw [e5, Finset.abs_prod]
      have hcard : ∀ i : Fin Λ.k, Λ.response.C₀ * (((F.points n).data.supportSites Λ.stepParams.side t i).card : ℝ) ≤ M₁ * P ^ 4 :=
        fun i => by
        have h1 := hsites n t htn i
        rw [hs n] at h1
        have h2 : (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - t)) = P ^ 4 := by
          rw [hPd, ← pow_mul, mul_comm 4]
        rw [h2] at h1
        have h3 := mul_le_mul_of_nonneg_left h1 hC
        have h4 : 4 * Λ.response.C₀ * A₂ * P ^ 4 ≤ M₁ * P ^ 4 := mul_le_mul_of_nonneg_right hM₁ (by positivity)
        nlinarith
      have hprod : ∏ i ∈ B, (Λ.response.C₀ * (((F.points n).data.supportSites Λ.stepParams.side t i).card : ℝ)) ≤ Q := by
        rw [hQd]
        calc _ ≤ ∏ _i ∈ B, (M₁ * P ^ 4) := Finset.prod_le_prod (fun i _ => by positivity) fun i _ => hcard i
          _ = (M₁ * P ^ 4) ^ B.card := by rw [Finset.prod_const]
          _ ≤ _ := pow_le_pow_right₀ hMP hB8
      have hN0 : 0 ≤ ∏ i ∈ B, meanScoreAtLevel t i (F.points n) w := Finset.prod_nonneg fun i _ => zero_le_one.trans (hN1 i)
      calc ∏ i ∈ B, |responseAtLevel t i (F.points n) w|
          ≤ ∏ i ∈ B, (Λ.response.C₀ * (((F.points n).data.supportSites Λ.stepParams.side t i).card : ℝ) *
              meanScoreAtLevel t i (F.points n) w) :=
            Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => hw i
        _ = (∏ i ∈ B, (Λ.response.C₀ * (((F.points n).data.supportSites Λ.stepParams.side t i).card : ℝ))) *
              ∏ i ∈ B, meanScoreAtLevel t i (F.points n) w := Finset.prod_mul_distrib
        _ ≤ Q * (1 + 2 ^ B.card * (1 + ∑ z ∈ offsetCube (S.supportRadius t), hullSizePower t z B.card (F.points n) w)) :=
            mul_le_mul hprod hNJ' hN0 hQ0
        _ = _ := by ring
private theorem norm_le_two_mul_of_abs_le (x : EuclideanFourSpace) (R : ℝ) (h : ∀ a, |x a| ≤ R) : ‖x‖ ≤ 2 * R := by
  have hR : 0 ≤ R := (abs_nonneg _).trans (h 0)
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [Fin.sum_univ_four]
  simp only [Real.norm_eq_abs]
  have h1 : ∀ a, |x a| ^ 2 ≤ R ^ 2 := fun a => pow_le_pow_left₀ (abs_nonneg _) (h a) 2
  nlinarith [h1 0, h1 1, h1 2, h1 3]
abbrev _root_.YangMills.SharedProofs.p52306 := @norm_le_two_mul_of_abs_le
private theorem supDist_le_dist (x y : EuclideanFourSpace) : supDist x y ≤ dist x y := by
  unfold supDist
  apply ciSup_le
  intro a
  rw [EuclideanSpace.dist_eq]
  apply Real.le_sqrt_of_sq_le
  have h1 := Finset.single_le_sum (f := fun i => dist (x i) (y i) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ a)
  simpa [Real.dist_eq, sq_abs] using h1
abbrev _root_.YangMills.SharedProofs.p2932 := @supDist_le_dist
private theorem admissible_of_supAdmissible {k : ℕ} {P : LevelData k} {L : ℕ} [NeZero L] {R d : ℝ}
    (h : P.SupAdmissible L R d) : P.Admissible L (2 * R) d where
  isTestFamily :=
    { lipschitzWith_one := fun i => LipschitzWith.of_dist_le_mul fun x y => by
        rw [NNReal.coe_one, one_mul, Real.dist_eq]
        exact (h.isSupTestFamily.lipschitz i x y).trans (supDist_le_dist x y)
      abs_le_one := h.isSupTestFamily.abs_le_one
      tsupport_subset_closedBall := fun i x hx => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_le_two_mul_of_abs_le x R (h.isSupTestFamily.abs_coord_le i x hx)
      le_dist_of_ne := fun i j hij x hx y hy => (h.isSupTestFamily.le_supDist i j hij x hx y hy).trans (supDist_le_dist x y) }
  scaleLevel_le := h.scaleLevel_le
  support_small := h.support_small
  exists_ne_zero := h.exists_ne_zero
open Classical in
private theorem lastSeparated_spec (S : MomentPoint Λ) :
    S.lastSeparated ≤ S.data.scaleLevel ∧ S.data.SeparatedBelow Λ.stepParams S.β S.lastSeparated := by
  unfold MomentPoint.lastSeparated
  exact ⟨Nat.findGreatest_le _,
    Nat.findGreatest_spec (m := 0) (Nat.zero_le _) fun u hu => absurd hu (Nat.not_lt_zero u)⟩
private theorem hullDecayRate_nonneg {Tb : ParameterAssignment} (h : Tb.Admissible) : 0 ≤ HullTrees.hullDecayRate Tb := by apply _root_.YangMills.SharedProofs.p10157 <;> assumption
private theorem pow_pow_eighty_eq_exp {L : ℝ} (hL : 0 < L) (e : ℕ) : (L ^ e) ^ 80 = Real.exp (80 * Real.log L * (e : ℝ)) := by
  have h : (80 : ℝ) * Real.log L * (e : ℝ) = ((80 * e : ℕ) : ℝ) * Real.log L := by
    push_cast
    ring
  rw [h, Real.exp_nat_mul, Real.exp_log hL, ← pow_mul, mul_comm e]
private theorem measurable_prod_sum {X : Type} [MeasurableSpace X] {ι κ : Type} (I : Finset ι) (s : Finset κ) (f : ι → κ → X → ℝ)
    (h : ∀ i ∈ I, ∀ j ∈ s, Measurable (f i j)) : Measurable fun x => ∏ i ∈ I, ∑ j ∈ s, f i j x :=
  Finset.measurable_fun_prod _ fun i hi => Finset.measurable_fun_sum _ (h i hi)
private theorem bounds_of_const_level {S : MomentPoint Λ} {F : LimitLawAtPoint S} {t : ℕ} {B : Finset (Fin Λ.k)} {c : Fin Λ.k → ℝ}
    (hf : Λ.stepParams.Admissible) (hs₁ : 0 ≤ Λ.response.s₁) (hC : 0 ≤ Λ.response.C₀) (hL : (2 : ℝ) ≤ Λ.stepParams.side)
    (hrt : 0 ≤ Λ.stepParams.rt)
    (hM : jointLimitPropertiesStatement) (hE : jointLimitExtendStatement) (hAR : ruleDrawsChainStatement)
    (hts : ∀ n, (F.points n).lastSeparated = t) (htS : t ≤ S.data.scaleLevel) (hsK : S.data.scaleLevel ≤ S.data.windowLevel)
    (hc : ∀ i, Tendsto (fun m => (F.points m).kappaAtLast i) atTop (𝓝 (c i))) (hB8 : B.card ≤ 8)
    {A₂ M₁ Cn Cs : ℝ} (hA₂ : 0 ≤ A₂) (hM₁ : 4 * Λ.response.C₀ * A₂ ≤ M₁) (hM1 : 1 ≤ M₁) (hCs : 0 ≤ Cs) (D : ℕ → ℝ)
    (hD : ∀ n, ∀ u < t, D u ≤ ((F.points n).data.separation Λ.stepParams.side u : ℝ))
    (hsites : ∀ S' : MomentPoint Λ, ∀ j ≤ S'.data.scaleLevel, ∀ i : Fin Λ.k,
      ((S'.data.supportSites Λ.stepParams.side j i).card : ℝ) ≤ A₂ * (Λ.stepParams.side : ℝ) ^ (4 * (S'.data.scaleLevel - j)))
    (hT₁ : ∀ (S' : MomentPoint Λ) (i : Fin Λ.k) (t' : ℕ) (ht : t' ≤ S'.data.windowLevel),
      ∀ᵐ w ∂(S'.law S'.data.windowLevel (S'.data.period Λ.stepParams.side)),
      completedObservable S'.tower S'.coeff t' (S'.sideAtLevel t') (S'.weight i _) (S'.sampleAtLevel t' ht w) -
          S'.kappa t' (S'.sideAtLevel t') i =
        responseAtLevel 0 i S' w + ∑ j ∈ Finset.range t', centredStepScore j i S' w)
    (hT₂ : ∀ (S' : MomentPoint Λ) (u : ℕ), u < S'.data.windowLevel → ∀ J : Finset (Fin Λ.k),
      ∀ᵐ w ∂(S'.law S'.data.windowLevel (S'.data.period Λ.stepParams.side)),
      variableProduct u J S' w = ∏ i ∈ J, (responseAtLevel u i S' w + centredStepScore u i S' w))
    (hV : ∀ S' : MomentPoint Λ, ∀ u < S'.lastSeparated, ∀ J : Finset (Fin Λ.k), J.Nonempty →
      ∀ᵐ w ∂(S'.law S'.data.windowLevel (S'.data.period Λ.stepParams.side)),
      |variableMean u J S' w - ∏ i ∈ J, responseAtLevel (u + 1) i S' w| ≤
        S'.stepErrorBound Cn u J * ∏ i ∈ J, meanScoreAtLevel (u + 1) i S' w)
    (hZ₁ : ∀ S' : MomentPoint Λ, ∀ u < S'.data.scaleLevel, ∀ (i : Fin Λ.k)
      (w : MarkedSample Λ.stepParams S'.data.windowLevel (S'.data.period Λ.stepParams.side)),
      |centredStepScore u i S' w| ≤ 2 * (Λ.response.C₀ * ((S'.data.supportSites Λ.stepParams.side u i).card : ℝ)))
    (hZ₂ : ∀ S' : MomentPoint Λ, ∀ u ≤ S'.data.scaleLevel, ∀ i : Fin Λ.k,
      ∀ᵐ w ∂(S'.law S'.data.windowLevel (S'.data.period Λ.stepParams.side)),
      |responseAtLevel u i S' w| ≤ Λ.response.C₀ * ((S'.data.supportSites Λ.stepParams.side u i).card : ℝ) * meanScoreAtLevel u i S' w)
    (hN : ∀ S' : MomentPoint Λ, ∀ u ≤ S'.data.scaleLevel,
      ∀ w : MarkedSample Λ.stepParams S'.data.windowLevel (S'.data.period Λ.stepParams.side),
      (∀ i : Fin Λ.k, 1 ≤ meanScoreAtLevel u i S' w) ∧ ∀ J : Finset (Fin Λ.k), J.Nonempty →
        ∏ i ∈ J, meanScoreAtLevel u i S' w ≤ 1 + 2 ^ J.card * (1 + ∑ z ∈ offsetCube (S'.supportRadius u), hullSizePower u z J.card S' w))
    (hHull : ∀ (F : LimitLawAtPoint S) (u : ℕ) (z : Fin 4 → ℤ), u ≤ S.data.windowLevel → ∀ (p : ℕ) (j : F.Index), 1 ≤ p → p ≤ 8 →
      F.observables j = hullSizePower u z p → ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ Cs)
    (hSc : ∀ (F : LimitLawAtPoint S) (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)) (j j' : F.Index),
      F.observables j = bottomProduct c B → F.observables j' = completedProduct c B → F.condMeanAt j =ᵐ[F.law] F.condMeanAt j')
    (hFC : ∀ (F : LimitLawAtPoint S) (u : ℕ) (hu : ∀ i, u + 1 ≤ (F.points i).data.windowLevel)
      (Φ : ∀ i, TorusField ((F.points i).sideAtLevel (u + 1)) →
        CaseFunction ((F.points i).tower.stage u).toStepSetup ((F.points i).sideAtLevel (u + 1)))
      (Rr a : ℕ) (Sz : ℝ) (A : ∀ i, Finset (TorusSite ((F.points i).sideAtLevel (u + 1) * Λ.stepParams.side)))
      (o : ∀ i, TorusSite ((F.points i).sideAtLevel (u + 1) * Λ.stepParams.side))
      (sz : ∀ i, ((F.points i).tower.stage u).labels.Ω → ℝ) (jX jE jR : F.Index),
      (∀ i V, IsQuasiLocalCaseFunction ((F.points i).tower.stage u).toStepSetup (o i) Rr a Sz (A i) (sz i) (Φ i V)) →
      (∀ i, Measurable (caseLift (F.points i).tower u _ (Φ i))) →
      (∀ i, ∀ᵐ x ∂(markedSampleLaw (F.points i).tower (F.points i).β (u + 1) ((F.points i).sideAtLevel (u + 1))),
        CaseIntegrableAtSample (F.points i).tower u _ (Φ i) x) →
      (∃ C : ℝ, ∀ i, ∫⁻ x, ENNReal.ofReal (supportWeightOfSample (F.points i).tower u _ (A i) (sz i) x)
        ∂(markedSampleLaw (F.points i).tower (F.points i).β (u + 1) ((F.points i).sideAtLevel (u + 1))) ≤ ENNReal.ofReal C) →
      (∀ i w, F.observables jX (F.points i) w = caseLift (F.points i).tower u _ (Φ i) ((F.points i).sampleAtLevel (u + 1) (hu i) w)) →
      (∀ i w, F.observables jE (F.points i) w =
        caseMeanAtSample (F.points i).tower u _ (Φ i) ((F.points i).sampleAtLevel (u + 1) (hu i) w)) →
      (∃ C : ℝ, ∀ i w, |F.observables jR (F.points i) w| ≤ C) →
      (∀ i, IsMeasurableAbove (F.points i) (u + 1) (F.observables jR (F.points i))) →
      F.condMean (fun v => v (jR, 0) * v (jX, 0)) =ᵐ[F.law] F.condMean (fun v => v (jR, 0) * v (jE, 0)))
    (hVar : ∀ (u : ℕ), u < S.data.scaleLevel → ∀ J : Finset (Fin Λ.k), ∃ (Rr : ℕ) (Sz C : ℝ),
      ∀ S' : MomentPoint Λ, (∃ m hp hs, S' = S.withSideExponent m hp hs) →
        ∃ A : Finset (TorusSite (S'.sideAtLevel (u + 1) * Λ.stepParams.side)),
        (∀ V, IsQuasiLocalCaseFunction (S'.tower.stage u).toStepSetup (S'.originSite u _) Rr J.card Sz A (S'.resp u).score
          (S'.variableCaseProduct u J V)) ∧
        Measurable (caseLift S'.tower u _ (S'.variableCaseProduct u J)) ∧
        (∀ᵐ x ∂(markedSampleLaw S'.tower S'.β (u + 1) (S'.sideAtLevel (u + 1))),
          CaseIntegrableAtSample S'.tower u _ (S'.variableCaseProduct u J) x) ∧
        ∫⁻ x, ENNReal.ofReal (supportWeightOfSample S'.tower u _ A (S'.resp u).score x)
          ∂(markedSampleLaw S'.tower S'.β (u + 1) (S'.sideAtLevel (u + 1))) ≤ ENNReal.ofReal C)
    (hRead : ∀ (S' : MomentPoint Λ) (v j : ℕ) (i : Fin Λ.k), v ≤ j → IsMeasurableAbove S' v (centredStepScore j i S'))
    (hPL : (∃ b : ℝ, ∀ (m : ℕ) hp hs (i : Fin Λ.k), |(S.withSideExponent m hp hs).kappaAtLast i| ≤ b) ∧
      ∀ (rule : NoiseRule Λ.stepParams) (ms : ℕ → ℕ) (Sq : ℕ → MomentPoint Λ) (p : ℕ), rule.IsAdmissible S.tower → 1 ≤ p →
        StrictMono ms → (∀ i, ∃ hp hs, Sq i = S.withSideExponent (ms i) hp hs) → (translatedTori Sq p).IsPreserving)
    (hMo : ∀ (rule : NoiseRule Λ.stepParams) (ms : ℕ → ℕ) (Sq : ℕ → MomentPoint Λ) (p : ℕ),
      rule.IsAdmissible S.tower → 1 ≤ p → StrictMono ms → (∀ i, ∃ hp hs, Sq i = S.withSideExponent (ms i) hp hs) →
      (∀ u ≤ S.data.scaleLevel, ∀ i : Fin Λ.k, TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (responseAtLevel u i))) ∧
      (∀ u < S.data.scaleLevel, ∀ i : Fin Λ.k, TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (centredStepScore u i))) ∧
      (∀ u < S.data.scaleLevel, ∀ J : Finset (Fin Λ.k), TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (variableProduct u J))) ∧
      (∀ u ≤ S.data.windowLevel, ∀ (z : Fin 4 → ℤ) (k : ℕ),
        TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (hullSizePower u z k))) ∧
      (∀ u, (∀ m, u < (Sq m).lastSeparated) → ∀ J : Finset (Fin Λ.k), J.Nonempty →
        TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (variableMean u J))) ∧
      ∀ (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)), TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (completedProduct c B)))
    (j j' : F.Index) (hj : F.observables j = bottomProduct c B) (hj' : F.observables j' = responseProduct B) :
    (∀ᵐ v ∂F.law, |F.condMeanAt j v - F.condMeanAt j' v| ≤ ∑ u ∈ Finset.range t,
      2 ^ 8 * (((1 + 2 * Λ.response.C₀ * A₂) ^ 8 * (|Cn| * (8 * A₂) * M₁ ^ 8)) * 2 ^ 9 * (1 + (2 * |Λ.R| + 7) ^ 4 * Cs)) *
        (((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u)) ^ 80 * Real.exp (-(Λ.stepParams.rt * D u / 2 ^ 7)))) ∧
    ∀ᵐ v ∂F.law, |F.condMeanAt j' v| ≤ (M₁ * ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - t)) ^ 4) ^ 8 *
      (2 ^ 9 * (1 + (2 * |Λ.R| + 7) ^ 4 * ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - t)) ^ 4 * Cs)) := by
  classical
  obtain ⟨⟨bc, hbc⟩, hKeep⟩ := hPL
  have hbcF : ∀ m i, |(F.points m).kappaAtLast i| ≤ bc := fun m i => by
    obtain ⟨a, b, h⟩ := F.points_eq m
    rw [h]
    exact hbc _ a b i
  have hk : (translatedTori F.points F.period).IsPreserving :=
    hKeep F.rule F.exponents F.points F.period F.rule_admissible F.one_le_period F.strictMono_exponents F.points_eq
  obtain ⟨m₁, m₂, m₃, m₄, m₅, m₆⟩ :=
    hMo F.rule F.exponents F.points F.period F.rule_admissible F.one_le_period F.strictMono_exponents F.points_eq
  have hmem : ∀ a : TelescopeTerm Λ.k,
      TranslatedLaws.HasBoundedMoments (sampleFamily F.rule F.points F.period (termObservable t S.data.windowLevel B c a)) :=
    hasBoundedMoments_term hk htS (fun m => (hts m).symm) hbcF m₁ m₂ m₃ m₄ m₅ (m₆ c B)
  have hcount := F.countable_index
  obtain ⟨sub, P', hsub, hLim, -, htrans⟩ := hE (translatedTori F.points F.period) F.Index (TelescopeTerm Λ.k)
    (fun j => sampleFamily F.rule F.points F.period (F.observables j))
    (fun a => sampleFamily F.rule F.points F.period (termObservable t S.data.windowLevel B c a)) F.law hk F.hasBoundedMoments hmem
    F.isJointLimitLaw
  obtain ⟨bd₁, hbd₁⟩ : ∃ x, x = ∑ u ∈ Finset.range t,
      2 ^ 8 * (((1 + 2 * Λ.response.C₀ * A₂) ^ 8 * (|Cn| * (8 * A₂) * M₁ ^ 8)) * 2 ^ 9 * (1 + (2 * |Λ.R| + 7) ^ 4 * Cs)) *
        (((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u)) ^ 80 * Real.exp (-(Λ.stepParams.rt * D u / 2 ^ 7))) := ⟨_, rfl⟩
  obtain ⟨bd₂, hbd₂⟩ : ∃ x, x = (M₁ * ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - t)) ^ 4) ^ 8 *
      (2 ^ 9 * (1 + (2 * |Λ.R| + 7) ^ 4 * ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - t)) ^ 4 * Cs)) := ⟨_, rfl⟩
  rw [← hbd₁, ← hbd₂]
  let G : LimitLawAtPoint S := extendLaw F (termObservable t S.data.windowLevel B c) hmem sub hsub P' hLim
  have hk₂ : (translatedTori G.points G.period).IsPreserving :=
    hKeep G.rule G.exponents G.points G.period G.rule_admissible G.one_le_period G.strictMono_exponents G.points_eq
  let ix : TelescopeIndices G t B c :=
    { m := fun a => (Sum.inr a : F.Index ⊕ TelescopeTerm Λ.k)
      line := fun u i h => if_pos h
      product := fun u h => if_pos h
      rest := fun u I => rfl
      var := fun u J h => if_pos h
      mean := fun u J h hJ => if_pos ⟨h, hJ⟩
      resp := fun u J h => if_pos h
      size := fun u z p h => if_pos h
      off := fun i => rfl
      completed := rfl }
  have hsG : ∀ n, (G.points n).data.scaleLevel = S.data.scaleLevel := fun n => (points_fields G n).1
  have hKG : ∀ n, (G.points n).data.windowLevel = S.data.windowLevel := fun n => (points_fields G n).2.1
  have htsG : ∀ n, (G.points n).lastSeparated = t := fun n => hts (sub n)
  have hFar : ∀ u < t, ∀ J ∈ B.powerset.filter Finset.Nonempty,
      G.condMean (fun v => v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.var u J), 0)) =ᵐ[G.law]
        G.condMean (fun v => v (ix.m (.rest u (B \ J)), 0) * v (ix.m (.mean u J), 0)) := by
    intro u hu J hJ
    have hus : u < S.data.scaleLevel := hu.trans_le htS
    obtain ⟨Rr, Sz, C₅, hvar⟩ := hVar u hus J
    choose A hA using fun i => hvar (G.points i) ⟨G.exponents i, G.points_eq i⟩
    have hKi : ∀ i, u + 1 ≤ (G.points i).data.windowLevel := fun i => by
      rw [hKG i]
      omega
    refine hFC G u hKi (fun i => (G.points i).variableCaseProduct u J) Rr J.card Sz A (fun i => (G.points i).originSite u _)
      (fun i => ((G.points i).resp u).score)
      (ix.m (.var u J)) (ix.m (.mean u J)) (ix.m (.rest u (B \ J))) (fun i V => (hA i).1 V) (fun i => (hA i).2.1)
      (fun i => (hA i).2.2.1) ⟨C₅, fun i => (hA i).2.2.2⟩ ?_ ?_ ?_ ?_
    · intro i w
      rw [ix.var u J hu]
      exact dif_pos (hKi i)
    · intro i w
      rw [ix.mean u J hu (Finset.mem_filter.mp hJ).2]
      exact dif_pos (hKi i)
    · refine ⟨((1 + 2 * Λ.response.C₀ * A₂) * ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u)) ^ 5) ^ 8, fun i w => ?_⟩
      rw [ix.rest]
      have hI : (B \ J).card ≤ 8 := (Finset.card_le_card Finset.sdiff_subset).trans hB8
      have h := abs_tailProduct_le hA₂ hC hL (hZ₁ _) (hsites _) hu (by rw [hsG i]; exact htS) (B \ J) hI w
      rwa [hsG i] at h
    · intro i
      rw [ix.rest]
      intro d h
      exact @measurable_prod_sum _
        (ResponseInTheExpansion.upperSigma (G.points i).tower (u + 1) d ((G.points i).data.period Λ.stepParams.side)) _ _
        (B \ J) (Finset.Ico (u + 1) t)
        (fun l e w => centredStepScore e l (G.points i) (h ▸ w)) fun l _ e he =>
          hRead (G.points i) (u + 1) e l (Finset.mem_Ico.mp he).1 d h
  have hMain := bounds_of_indices (F := G) hs₁ hC hL hrt hM hk₂ ix (ae_sampleOf hAR hf G) htsG htS hsK
    (fun i => (hc i).comp hsub.tendsto_atTop) hB8 hA₂ hM₁ hM1 hCs D (fun n => hD (sub n)) (fun n => hsites _)
    (fun n i => hT₁ (G.points n) i _ (G.points n).lastSeparated_le)
    (fun n u hu J => hT₂ (G.points n) u (by rw [hKG n]; omega) J)
    (fun n u hu J hJ => hV (G.points n) u (by rw [htsG n]; exact hu) J hJ)
    (fun n => hZ₁ _) (fun n => hZ₂ _) (fun n => hN _)
    (fun u hu z p hp hp8 => hHull G u z hu p (ix.m (.size u z p)) hp hp8 (ix.size u z p hu)) (hSc G c B) hFar
    (Sum.inl j : F.Index ⊕ TelescopeTerm Λ.k) (Sum.inl j' : F.Index ⊕ TelescopeTerm Λ.k) hj hj'
  rw [← hbd₁, ← hbd₂] at hMain
  obtain ⟨b₁, b₂⟩ := hMain
  have hP : IsProbabilityMeasure F.law := F.isJointLimitLaw.isProbability
  have hP₂ : IsProbabilityMeasure G.law := G.isJointLimitLaw.isProbability
  have iF := integrable_coord hM hk
  have iG := integrable_coord hM hk₂
  refine ⟨?_, ?_⟩
  · have e₂ : invariantCondExp P' ((fun v : TranslateValues F.Index => v (j, 0) - v (j', 0)) ∘ leftValues) =ᵐ[P']
        fun v => G.condMeanAt (Sum.inl j : F.Index ⊕ TelescopeTerm Λ.k) v - G.condMeanAt (Sum.inl j' : F.Index ⊕ TelescopeTerm Λ.k) v :=
      condExp_sub (iG (Sum.inl j : F.Index ⊕ TelescopeTerm Λ.k)) (iG (Sum.inl j' : F.Index ⊕ TelescopeTerm Λ.k))
        (shiftInvariantSigma (F.Index ⊕ TelescopeTerm Λ.k))
    have h₃ := htrans (fun v => v (j, 0) - v (j', 0)) (-bd₁) bd₁ ((iF j).sub (iF j')) (by
      have b₁' : ∀ᵐ v ∂P', |G.condMeanAt (Sum.inl j : F.Index ⊕ TelescopeTerm Λ.k) v -
          G.condMeanAt (Sum.inl j' : F.Index ⊕ TelescopeTerm Λ.k) v| ≤ bd₁ := b₁
      filter_upwards [b₁', e₂] with v x y
      rw [y]
      exact abs_le.mp x)
    have e₁ : invariantCondExp F.law (fun v : TranslateValues F.Index => v (j, 0) - v (j', 0)) =ᵐ[F.law]
        fun v => F.condMeanAt j v - F.condMeanAt j' v :=
      condExp_sub (iF j) (iF j') (shiftInvariantSigma F.Index)
    filter_upwards [h₃, e₁] with v x y
    rw [y] at x
    exact abs_le.mpr x
  · have h₃ := htrans (fun v => v (j', 0)) (-bd₂) bd₂ (iF j') (by
      have b₂' : ∀ᵐ v ∂P', |G.condMeanAt (Sum.inl j' : F.Index ⊕ TelescopeTerm Λ.k) v| ≤ bd₂ := b₂
      filter_upwards [b₂'] with v x
      exact abs_le.mp x)
    filter_upwards [h₃] with v x
    exact abs_le.mpr x
private theorem exists_bounds (hDr : Λ.table.Admissible) (hf : Λ.stepParams.Admissible) (hKf : Λ.response.Admissible Λ.stepParams)
    (hrun : AdmissibleStep Λ.stepParams) (hg : 0 < Λ.g) (hy : Λ.stepParams.y₁ ≤ (Λ.g ^ 2)⁻¹)
    (hk2 : 2 ≤ Λ.k) (hk8 : Λ.k ≤ 8) (hd : 0 < Λ.d) (hG : separationLowerBoundStatement) (hW : CouplingFlowAboveWindow)
    (hM : jointLimitPropertiesStatement) (hE : jointLimitExtendStatement) (hAR : ruleDrawsChainStatement)
    (C₂ C₃ C₄ : ℕ → ℝ) (Ch : ℝ) (hCh : 1 ≤ Ch)
    (hS : ∀ S : MomentPoint Λ, ∀ u ≤ S.data.scaleLevel, ∀ i : Fin Λ.k,
      weightNorm Λ.stepParams.side u (S.weight i (fineSide Λ.stepParams.side u (S.levelSide u))) ≤ 1 ∧
        ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) ≤ C₂ 0 * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u)))
    (hT₁ : ∀ (S' : MomentPoint Λ) (i : Fin Λ.k) (t' : ℕ) (ht : t' ≤ S'.data.windowLevel),
      ∀ᵐ w ∂(S'.law S'.data.windowLevel (S'.data.period Λ.stepParams.side)),
      completedObservable S'.tower S'.coeff t' (S'.sideAtLevel t') (S'.weight i _) (S'.sampleAtLevel t' ht w) -
          S'.kappa t' (S'.sideAtLevel t') i =
        responseAtLevel 0 i S' w + ∑ j ∈ Finset.range t', centredStepScore j i S' w)
    (hT₂ : ∀ (S' : MomentPoint Λ) (u : ℕ), u < S'.data.windowLevel → ∀ J : Finset (Fin Λ.k),
      ∀ᵐ w ∂(S'.law S'.data.windowLevel (S'.data.period Λ.stepParams.side)),
      variableProduct u J S' w = ∏ i ∈ J, (responseAtLevel u i S' w + centredStepScore u i S' w))
    (hV : ∀ S' : MomentPoint Λ, ∀ u < S'.lastSeparated, ∀ J : Finset (Fin Λ.k), J.Nonempty →
      ∀ᵐ w ∂(S'.law S'.data.windowLevel (S'.data.period Λ.stepParams.side)),
      |variableMean u J S' w - ∏ i ∈ J, responseAtLevel (u + 1) i S' w| ≤
        S'.stepErrorBound (C₃ 0) u J * ∏ i ∈ J, meanScoreAtLevel (u + 1) i S' w)
    (hZ₁ : ∀ S' : MomentPoint Λ, ∀ u < S'.data.scaleLevel, ∀ (i : Fin Λ.k)
      (w : MarkedSample Λ.stepParams S'.data.windowLevel (S'.data.period Λ.stepParams.side)),
      |centredStepScore u i S' w| ≤ 2 * (Λ.response.C₀ * ((S'.data.supportSites Λ.stepParams.side u i).card : ℝ)))
    (hZ₂ : ∀ S' : MomentPoint Λ, ∀ u ≤ S'.data.scaleLevel, ∀ i : Fin Λ.k,
      ∀ᵐ w ∂(S'.law S'.data.windowLevel (S'.data.period Λ.stepParams.side)),
      |responseAtLevel u i S' w| ≤ Λ.response.C₀ * ((S'.data.supportSites Λ.stepParams.side u i).card : ℝ) * meanScoreAtLevel u i S' w)
    (hN : ∀ S' : MomentPoint Λ, ∀ u ≤ S'.data.scaleLevel,
      ∀ w : MarkedSample Λ.stepParams S'.data.windowLevel (S'.data.period Λ.stepParams.side),
      (∀ i : Fin Λ.k, 1 ≤ meanScoreAtLevel u i S' w) ∧ ∀ J : Finset (Fin Λ.k), J.Nonempty →
        ∏ i ∈ J, meanScoreAtLevel u i S' w ≤ 1 + 2 ^ J.card * (1 + ∑ z ∈ offsetCube (S'.supportRadius u), hullSizePower u z J.card S' w))
    (hNear : ∀ S : MomentPoint Λ, (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - S.lastSeparated) ≤ C₄ 0 * (S.range : ℝ))
    (hH : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (u : ℕ) (z : Fin 4 → ℤ), u ≤ S.data.windowLevel →
      ∀ (k : ℕ) (j : F.Index), 1 ≤ k → F.observables j = hullSizePower u z k →
        ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ Ch ^ k * (k.factorial : ℝ) ^ 6 * Real.exp (-(hullDecayRate Λ.table * S.coupling u / 4)))
    (hSc : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)) (j j' : F.Index),
      F.observables j = bottomProduct c B → F.observables j' = completedProduct c B → F.condMeanAt j =ᵐ[F.law] F.condMeanAt j')
    (hFC : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (u : ℕ) (hu : ∀ i, u + 1 ≤ (F.points i).data.windowLevel)
      (Φ : ∀ i, TorusField ((F.points i).sideAtLevel (u + 1)) →
        CaseFunction ((F.points i).tower.stage u).toStepSetup ((F.points i).sideAtLevel (u + 1)))
      (Rr a : ℕ) (Sz : ℝ) (A : ∀ i, Finset (TorusSite ((F.points i).sideAtLevel (u + 1) * Λ.stepParams.side)))
      (o : ∀ i, TorusSite ((F.points i).sideAtLevel (u + 1) * Λ.stepParams.side))
      (sz : ∀ i, ((F.points i).tower.stage u).labels.Ω → ℝ) (jX jE jR : F.Index),
      (∀ i V, IsQuasiLocalCaseFunction ((F.points i).tower.stage u).toStepSetup (o i) Rr a Sz (A i) (sz i) (Φ i V)) →
      (∀ i, Measurable (caseLift (F.points i).tower u _ (Φ i))) →
      (∀ i, ∀ᵐ x ∂(markedSampleLaw (F.points i).tower (F.points i).β (u + 1) ((F.points i).sideAtLevel (u + 1))),
        CaseIntegrableAtSample (F.points i).tower u _ (Φ i) x) →
      (∃ C : ℝ, ∀ i, ∫⁻ x, ENNReal.ofReal (supportWeightOfSample (F.points i).tower u _ (A i) (sz i) x)
        ∂(markedSampleLaw (F.points i).tower (F.points i).β (u + 1) ((F.points i).sideAtLevel (u + 1))) ≤ ENNReal.ofReal C) →
      (∀ i w, F.observables jX (F.points i) w = caseLift (F.points i).tower u _ (Φ i) ((F.points i).sampleAtLevel (u + 1) (hu i) w)) →
      (∀ i w, F.observables jE (F.points i) w =
        caseMeanAtSample (F.points i).tower u _ (Φ i) ((F.points i).sampleAtLevel (u + 1) (hu i) w)) →
      (∃ C : ℝ, ∀ i w, |F.observables jR (F.points i) w| ≤ C) →
      (∀ i, IsMeasurableAbove (F.points i) (u + 1) (F.observables jR (F.points i))) →
      F.condMean (fun v => v (jR, 0) * v (jX, 0)) =ᵐ[F.law] F.condMean (fun v => v (jR, 0) * v (jE, 0)))
    (hVar : ∀ (S : MomentPoint Λ) (u : ℕ), u < S.data.scaleLevel → ∀ J : Finset (Fin Λ.k), ∃ (Rr : ℕ) (Sz C : ℝ),
      ∀ S' : MomentPoint Λ, (∃ m hp hs, S' = S.withSideExponent m hp hs) →
        ∃ A : Finset (TorusSite (S'.sideAtLevel (u + 1) * Λ.stepParams.side)),
        (∀ V, IsQuasiLocalCaseFunction (S'.tower.stage u).toStepSetup (S'.originSite u _) Rr J.card Sz A (S'.resp u).score
          (S'.variableCaseProduct u J V)) ∧
        Measurable (caseLift S'.tower u _ (S'.variableCaseProduct u J)) ∧
        (∀ᵐ x ∂(markedSampleLaw S'.tower S'.β (u + 1) (S'.sideAtLevel (u + 1))),
          CaseIntegrableAtSample S'.tower u _ (S'.variableCaseProduct u J) x) ∧
        ∫⁻ x, ENNReal.ofReal (supportWeightOfSample S'.tower u _ A (S'.resp u).score x)
          ∂(markedSampleLaw S'.tower S'.β (u + 1) (S'.sideAtLevel (u + 1))) ≤ ENNReal.ofReal C)
    (hRead : ∀ (S' : MomentPoint Λ) (v j : ℕ) (i : Fin Λ.k), v ≤ j → IsMeasurableAbove S' v (centredStepScore j i S'))
    (hPL : ∀ S : MomentPoint Λ, (∃ b : ℝ, ∀ (m : ℕ) hp hs (i : Fin Λ.k), |(S.withSideExponent m hp hs).kappaAtLast i| ≤ b) ∧
      ∀ (rule : NoiseRule Λ.stepParams) (ms : ℕ → ℕ) (Sq : ℕ → MomentPoint Λ) (p : ℕ), rule.IsAdmissible S.tower → 1 ≤ p →
        StrictMono ms → (∀ i, ∃ hp hs, Sq i = S.withSideExponent (ms i) hp hs) → (translatedTori Sq p).IsPreserving)
    (hMo : ∀ (S : MomentPoint Λ) (rule : NoiseRule Λ.stepParams) (ms : ℕ → ℕ) (Sq : ℕ → MomentPoint Λ) (p : ℕ),
      rule.IsAdmissible S.tower → 1 ≤ p → StrictMono ms → (∀ i, ∃ hp hs, Sq i = S.withSideExponent (ms i) hp hs) →
      (∀ u ≤ S.data.scaleLevel, ∀ i : Fin Λ.k, TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (responseAtLevel u i))) ∧
      (∀ u < S.data.scaleLevel, ∀ i : Fin Λ.k, TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (centredStepScore u i))) ∧
      (∀ u < S.data.scaleLevel, ∀ J : Finset (Fin Λ.k), TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (variableProduct u J))) ∧
      (∀ u ≤ S.data.windowLevel, ∀ (z : Fin 4 → ℤ) (k : ℕ),
        TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (hullSizePower u z k))) ∧
      (∀ u, (∀ m, u < (Sq m).lastSeparated) → ∀ J : Finset (Fin Λ.k), J.Nonempty →
        TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (variableMean u J))) ∧
      ∀ (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)), TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p (completedProduct c B))) :
    ∃ (C : ℕ → ℝ) (X₀ : ℝ), Λ.floor ≤ X₀ ∧ ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (c : Fin Λ.k → ℝ),
      (∀ i, Tendsto (fun m => (F.points m).kappaAtLast i) atTop (𝓝 (c i))) → ∀ (B : Finset (Fin Λ.k)) (j j' : F.Index),
        F.observables j = bottomProduct c B → F.observables j' = responseProduct B →
        (X₀ ≤ S.scaleCoupling → ∀ᵐ v ∂F.law, |F.condMeanAt j v - F.condMeanAt j' v| ≤ Real.exp (-(S.scaleCoupling ^ ((1 : ℝ) / 200)))) ∧
        ∀ M : ℕ, S.scaleCoupling ≤ M → ∀ᵐ v ∂F.law, |F.condMeanAt j v| ≤ C M := by
  have hL2 : (2 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by
    have h1 := hf.L_ge
    exact_mod_cast (by omega : 2 ≤ Λ.stepParams.side)
  have hL0 : (0 : ℝ) < (Λ.stepParams.side : ℝ) := by linarith
  obtain ⟨c₀, hc₀, hgap⟩ := hG Λ.stepParams.side hf.L_odd (by have h1 := hf.L_ge; omega) Λ.k hk2 (2 * Λ.R) Λ.d hd
  have hC₀ : 0 ≤ Λ.response.C₀ := by
    rw [hKf.C₀_eq]
    linarith [hf.a_ge, hKf.N₀_nonneg, hKf.Kc_ge]
  have hs₁ : 0 ≤ Λ.response.s₁ := by
    rw [hKf.s₁_eq]
    have : 0 ≤ Λ.stepParams.coupling := by linarith [hf.a_ge]
    positivity
  have hrt := hf.rt_pos
  have hrate := hullDecayRate_nonneg hDr
  obtain ⟨A₂, hA₂d⟩ : ∃ A₂ : ℝ, A₂ = max (C₂ 0) 1 := ⟨_, rfl⟩
  have hA₂1 : 1 ≤ A₂ := hA₂d ▸ le_max_right _ _
  have hA₂0 : 0 ≤ A₂ := by linarith
  have hA₂2 : C₂ 0 ≤ A₂ := hA₂d ▸ le_max_left _ _
  obtain ⟨M₁, hM₁d⟩ : ∃ M₁ : ℝ, M₁ = max (4 * Λ.response.C₀ * A₂) 1 := ⟨_, rfl⟩
  have hM₁1 : 1 ≤ M₁ := hM₁d ▸ le_max_right _ _
  have hM₁2 : 4 * Λ.response.C₀ * A₂ ≤ M₁ := hM₁d ▸ le_max_left _ _
  obtain ⟨Cs, hCsd⟩ : ∃ Cs : ℝ, Cs = Ch ^ 8 * ((Nat.factorial 8 : ℕ) : ℝ) ^ 6 := ⟨_, rfl⟩
  have hCs : 0 ≤ Cs := by
    rw [hCsd]
    positivity
  obtain ⟨G, hGd⟩ : ∃ G : ℝ, G = (2 * |Λ.R| + 7) ^ 4 := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by
    rw [hGd]
    positivity
  obtain ⟨K₃, hK₃⟩ : ∃ K₃ : ℝ, K₃ = 2 ^ 8 * (((1 + 2 * Λ.response.C₀ * A₂) ^ 8 * (|C₃ 0| * (8 * A₂) * M₁ ^ 8)) * 2 ^ 9 *
      (1 + G * Cs)) := ⟨_, rfl⟩
  have hK₃0 : 0 ≤ K₃ := by
    rw [hK₃]
    have : 0 ≤ 2 * Λ.response.C₀ * A₂ := by positivity
    positivity
  obtain ⟨X₁, hX₁⟩ := mul_sum_exp_terms_le (Λ.stepParams.side : ℝ) c₀ Λ.stepParams.rt Λ.stepParams.B K₃ 80 hL2 hc₀ hrt hf.B_pos
    hK₃0 (by norm_num)
  obtain ⟨A₅, hA₅0, hA₅⟩ := sum_exp_terms_bounded (Λ.stepParams.side : ℝ) c₀ Λ.stepParams.rt 80 hL2 hc₀ hrt (by norm_num)
  obtain ⟨Tm, hTm⟩ : ∃ Tm : ℕ → ℝ, Tm = fun M : ℕ => |C₄ 0| * (clusterRange (M : ℝ) : ℝ) + 1 := ⟨_, rfl⟩
  refine ⟨fun M => K₃ * A₅ + (M₁ * Tm M ^ 4) ^ 8 * (2 ^ 9 * (1 + G * Tm M ^ 4 * Cs)), max Λ.floor X₁, le_max_left _ _, ?_⟩
  intro S F c hc B j j' hj hj'
  have hcard : B.card ≤ 8 := by
    have h1 := Finset.card_le_univ B
    rw [Fintype.card_fin] at h1
    omega
  have hrunF := hW Λ.stepParams hrun Λ.g hg hy S.β S.data.windowLevel S.window_le S.passage
  have hsK : S.data.scaleLevel ≤ S.data.windowLevel := S.supAdmissible.scaleLevel_le
  have hx1 : ∀ u ≤ S.data.windowLevel, 1 ≤ S.coupling u := fun u hu => le_trans hf.y₁_ge (hrunF.1 u hu)
  obtain ⟨t, φ, hφ, hφt⟩ := exists_subseq_const (fun n => (F.points n).lastSeparated) S.data.scaleLevel fun n => by
    have h1 := (lastSeparated_spec (F.points n)).1
    rwa [(points_fields F n).1] at h1
  have htS : t ≤ S.data.scaleLevel := by
    have h1 := (lastSeparated_spec (F.points (φ 0))).1
    rw [(points_fields F (φ 0)).1] at h1
    exact (hφt 0).symm.le.trans h1
  obtain ⟨D, hDd⟩ : ∃ D : ℕ → ℝ, D = fun u => max (c₀ * (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u) - 12)
      (2 ^ 10 * (clusterRange (S.coupling u) : ℝ)) := ⟨_, rfl⟩
  have hD0 : ∀ u, 0 ≤ D u := fun u => by
    rw [hDd]
    exact le_max_of_le_right (by positivity)
  have hD : ∀ n, ∀ u < t, D u ≤ (((restrictLaw F φ hφ).points n).data.separation Λ.stepParams.side u : ℝ) := by
    intro n u hut
    obtain ⟨e₁, e₂, e₃, -⟩ := points_fields F (φ n)
    have htn : (F.points (φ n)).lastSeparated = t := hφt n
    have hfar := (lastSeparated_spec (F.points (φ n))).2 u (by rw [htn]; exact hut)
    have h1 := hgap (F.points (φ n)).data (admissible_of_supAdmissible (F.points (φ n)).supAdmissible) u (by rw [e₂]; omega)
    have hz : (Λ.stepParams.side : ℝ) ^ (((F.points (φ n)).data.scaleLevel : ℤ) - (u : ℤ)) =
        (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u) := by
      rw [e₁]
      have h2 : (S.data.scaleLevel : ℤ) - (u : ℤ) = ((S.data.scaleLevel - u : ℕ) : ℤ) := by omega
      rw [h2, zpow_natCast]
    rw [hz] at h1
    rw [hDd]
    refine max_le h1 ?_
    have h2 : (2 : ℝ) ^ 10 * (clusterRange (couplingFlow Λ.stepParams (F.points (φ n)).β u).1 : ℝ) ≤
        ((F.points (φ n)).data.separation Λ.stepParams.side u : ℝ) := by
      exact_mod_cast hfar.1
    rw [e₃] at h2
    exact h2
  have hsites : ∀ S' : MomentPoint Λ, ∀ j ≤ S'.data.scaleLevel, ∀ i : Fin Λ.k,
      ((S'.data.supportSites Λ.stepParams.side j i).card : ℝ) ≤ A₂ * (Λ.stepParams.side : ℝ) ^ (4 * (S'.data.scaleLevel - j)) :=
    fun S' u hu i => (hS S' u hu i).2.trans (mul_le_mul_of_nonneg_right hA₂2 (by positivity))
  have hHull : ∀ (F : LimitLawAtPoint S) (u : ℕ) (z : Fin 4 → ℤ), u ≤ S.data.windowLevel → ∀ (p : ℕ) (j : F.Index), 1 ≤ p → p ≤ 8 →
      F.observables j = hullSizePower u z p → ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ Cs := by
    intro F u z hu p j hp hp8 hgj
    filter_upwards [hH S F u z hu p j hp hgj] with v hv
    refine hv.trans ?_
    rw [hCsd]
    have h1 : Ch ^ p ≤ Ch ^ 8 := pow_le_pow_right₀ hCh hp8
    have h2 : ((p.factorial : ℕ) : ℝ) ^ 6 ≤ ((Nat.factorial 8 : ℕ) : ℝ) ^ 6 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.factorial_le hp8) 6
    have h3 : Real.exp (-(hullDecayRate Λ.table * S.coupling u / 4)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have := mul_nonneg hrate (zero_le_one.trans (hx1 u hu))
      linarith
    calc _ ≤ Ch ^ p * (p.factorial : ℝ) ^ 6 * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = Ch ^ p * (p.factorial : ℝ) ^ 6 := mul_one _
      _ ≤ _ := mul_le_mul h1 h2 (by positivity) (by positivity)
  have R := bounds_of_const_level (S := S) (F := restrictLaw F φ hφ) (t := t) (B := B) (c := c) hf hs₁ hC₀ hL2 hrt.le hM hE hAR
    (fun n => hφt n) htS hsK (fun i => (hc i).comp hφ.tendsto_atTop) hcard hA₂0 hM₁2 hM₁1 hCs D hD hsites hT₁ hT₂ hV hZ₁ hZ₂ hN hHull
    (hSc S) (hFC S) (hVar S) hRead (hPL S) (hMo S) j j' hj hj'
  rw [← hGd, ← hK₃] at R
  obtain ⟨R₁, R₂⟩ := R
  replace R₁ : ∀ᵐ v ∂F.law, |F.condMeanAt j v - F.condMeanAt j' v| ≤ ∑ u ∈ Finset.range t, K₃ *
      (((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u)) ^ 80 * Real.exp (-(Λ.stepParams.rt * D u / 2 ^ 7))) := R₁
  replace R₂ : ∀ᵐ v ∂F.law, |F.condMeanAt j' v| ≤ (M₁ * ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - t)) ^ 4) ^ 8 *
      (2 ^ 9 * (1 + G * ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - t)) ^ 4 * Cs)) := R₂
  have hsum : ∑ u ∈ Finset.range t, K₃ * (((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u)) ^ 80 *
        Real.exp (-(Λ.stepParams.rt * D u / 2 ^ 7))) ≤
      K₃ * ∑ u ∈ Finset.range t, Real.exp (80 * Real.log (Λ.stepParams.side : ℝ) * ((S.data.scaleLevel - u : ℕ) : ℝ)) *
        Real.exp (-(Λ.stepParams.rt * D u / 2 ^ 8)) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => ?_) hK₃0
    rw [pow_pow_eighty_eq_exp hL0]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
    have h1 : 0 ≤ Λ.stepParams.rt * D u := mul_nonneg hrt.le (hD0 u)
    linarith
  refine ⟨fun hx => ?_, fun M hxM => ?_⟩
  · have hxX : X₁ ≤ S.scaleCoupling := (le_max_right _ _).trans hx
    have hxs : 1 ≤ S.scaleCoupling := hx1 _ hsK
    have hx0 : 0 ≤ S.scaleCoupling := by linarith
    have hfin := hX₁ S.scaleCoupling hxX S.data.scaleLevel t D htS (fun u _ => by rw [hDd]; exact le_max_left _ _) (fun u hut h4 => by
      have hus := hut.le.trans htS
      have hmove := hrunF.2 u S.data.scaleLevel hus hsK
      rw [Nat.cast_sub hus] at h4
      have hxu : S.scaleCoupling / 2 ≤ S.coupling u := by
        have h1 := (abs_le.mp hmove).2
        have h2 : S.scaleCoupling = (couplingFlow Λ.stepParams S.β S.data.scaleLevel).1 := rfl
        have h3 : S.coupling u = (couplingFlow Λ.stepParams S.β u).1 := rfl
        rw [← h2, ← h3] at h1
        linarith
      have h5 : (S.scaleCoupling / 2) ^ ((1 : ℝ) / 100) ≤ S.coupling u ^ ((1 : ℝ) / 100) :=
        Real.rpow_le_rpow (by positivity) hxu (by norm_num)
      have h6 : S.scaleCoupling ^ ((1 : ℝ) / 100) / 2 ≤ (S.scaleCoupling / 2) ^ ((1 : ℝ) / 100) := by
        rw [Real.div_rpow hx0 (by norm_num)]
        apply div_le_div_of_nonneg_left (Real.rpow_nonneg hx0 _) (Real.rpow_pos_of_pos (by norm_num) _)
        exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)).trans_eq (Real.rpow_one 2)
      have h7 : S.coupling u ^ ((1 : ℝ) / 100) ≤ (clusterRange (S.coupling u) : ℝ) := Nat.le_ceil _
      have h8 : (2 : ℝ) ^ 10 * (clusterRange (S.coupling u) : ℝ) ≤ D u := by
        rw [hDd]
        exact le_max_right _ _
      linarith)
    filter_upwards [R₁] with v hv
    exact hv.trans (hsum.trans hfin)
  · have hxs : 1 ≤ S.scaleCoupling := hx1 _ hsK
    have hb := hA₅ S.data.scaleLevel t D htS fun u _ => by
      rw [hDd]
      exact le_max_left _ _
    have hP1 : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - t) := one_le_pow₀ (by linarith)
    have hPT : (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - t) ≤ Tm M := by
      have h1 := hNear (F.points (φ 0))
      obtain ⟨e₁, -, e₃, -⟩ := points_fields F (φ 0)
      have htn : (F.points (φ 0)).lastSeparated = t := hφt 0
      have er : (F.points (φ 0)).range = S.range := by
        unfold MomentPoint.range MomentPoint.scaleCoupling MomentPoint.coupling
        rw [e₁, e₃]
      rw [e₁, htn, er] at h1
      have hr : (S.range : ℝ) ≤ (clusterRange (M : ℝ) : ℝ) := by
        have : S.range ≤ clusterRange (M : ℝ) := Nat.ceil_mono (Real.rpow_le_rpow (by linarith) hxM (by norm_num))
        exact_mod_cast this
      rw [hTm]
      have h2 : C₄ 0 * (S.range : ℝ) ≤ |C₄ 0| * (clusterRange (M : ℝ) : ℝ) :=
        (mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_left hr (abs_nonneg _))
      show _ ≤ |C₄ 0| * (clusterRange (M : ℝ) : ℝ) + 1
      linarith
    have hT1 : 1 ≤ Tm M := hP1.trans hPT
    have hmono : (M₁ * ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - t)) ^ 4) ^ 8 *
          (2 ^ 9 * (1 + G * ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - t)) ^ 4 * Cs)) ≤
        (M₁ * Tm M ^ 4) ^ 8 * (2 ^ 9 * (1 + G * Tm M ^ 4 * Cs)) := by
      have hpow : ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - t)) ^ 4 ≤ Tm M ^ 4 := pow_le_pow_left₀ (by linarith) hPT 4
      have hM0 : 0 ≤ M₁ := by linarith
      gcongr
    filter_upwards [R₁, R₂] with v x₁ x₂
    have h3 : |F.condMeanAt j v| ≤ |F.condMeanAt j v - F.condMeanAt j' v| + |F.condMeanAt j' v| := by
      have := abs_add_le (F.condMeanAt j v - F.condMeanAt j' v) (F.condMeanAt j' v)
      simpa using this
    have h4 : |F.condMeanAt j v - F.condMeanAt j' v| ≤ K₃ * A₅ := x₁.trans (hsum.trans (mul_le_mul_of_nonneg_left hb hK₃0))
    linarith [x₂.trans hmono]
private theorem forAllHull_of_forAll {Q : MomentParameters → Prop} (h : ForAllParameters Q) : ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem forAllHull_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁) (h₂ : ForAllHullParameters Q₂) :
    ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem forAllHull_mono {Q₁ Q₂ : MomentParameters → Prop} (h : ForAllHullParameters Q₁)
    (f : ∀ Λ : MomentParameters, Λ.table.Admissible → Λ.response.Admissible Λ.stepParams → Λ.stepParams.Admissible →
      AdmissibleStep Λ.stepParams → 0 < Λ.g → Λ.stepParams.y₁ ≤ (Λ.g ^ 2)⁻¹ →
      2 ≤ Λ.k → Λ.k ≤ 8 → 0 < Λ.d → Q₁ Λ → Q₂ Λ) : ForAllHullParameters Q₂ := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, H⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, hrt, ?_⟩
  intro L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  obtain ⟨M, G⟩ := H L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  refine ⟨M, ?_⟩
  intro Kr k₁ k₂ k₃ k₄ k₅
  obtain ⟨y₀, Y⟩ := G Kr k₁ k₂ k₃ k₄ k₅
  refine ⟨max y₀ Tb.floorMin, ?_⟩
  intro y hy hrow hw g hg hgy k _ hk2 hk8 R d hd
  have hfit : (Tb.stepParameters y).Admissible := d₁.fits y ((le_max_right _ _).trans hy)
  exact f ⟨Tb, Kr, y, g, k, R, d⟩ d₁ (k₄ y) hfit ⟨hfit, hrow, hw⟩ hg hgy hk2 hk8 hd
    (Y y ((le_max_left _ _).trans hy) hrow hw g hg hgy k hk2 hk8 R d hd)
end ResponsesNearForms
theorem lastSeparatedLevelMomentStatement_holds (hM : jointLimitPropertiesStatement) (hE : jointLimitExtendStatement)
    (hAR : ruleDrawsChainStatement) (hG : separationLowerBoundStatement) (hW : CouplingFlowAboveWindow)
    (hS : weightsSitesBelowScaleStatement) (hT : telescopeIdentityStatement) (hV : stepVariableMeanSplitStatement)
    (hZ : telescopeTermBoundsStatement) (hN : meanScoreProductBoundStatement) (hL : farLevelNearScaleStatement)
    (hH : limitHullBoundsStatement) (hSc : limitScoresMeanStatement) (hF : farCopiesConditionalStatement)
    (hVa : stepVariablesQuasiLocalStatement) (hR : stepScoreMeasurableAboveStatement) (hP : largerToriStatement)
    (hMo : telescopeMomentsStatement) : lastSeparatedLevelMomentStatement := by
  unfold weightsSitesBelowScaleStatement ForAllPoints at hS
  unfold telescopeIdentityStatement ForAllPoints at hT
  unfold stepVariableMeanSplitStatement ForAllPoints at hV
  unfold telescopeTermBoundsStatement ForAllPoints at hZ
  unfold meanScoreProductBoundStatement ForAllPoints at hN
  unfold farLevelNearScaleStatement ForAllPoints at hL
  unfold stepScoreMeasurableAboveStatement ForAllPoints at hR
  have h := forAllHull_and (forAllHull_of_forAll hS) (forAllHull_and (forAllHull_of_forAll hT)
    (forAllHull_and (forAllHull_of_forAll hV) (forAllHull_and (forAllHull_of_forAll hZ)
    (forAllHull_and (forAllHull_of_forAll hN) (forAllHull_and (forAllHull_of_forAll hL) (forAllHull_and hH
      (forAllHull_and hSc (forAllHull_and hF (forAllHull_and hVa
      (forAllHull_and (forAllHull_of_forAll hR) (forAllHull_and hP hMo)))))))))))
  refine forAllHull_mono h fun Λ hDr hKf hf hrun hg hy hk2 hk8 hd hh => ?_
  obtain ⟨⟨C₂, _, _, _, _, Q₂⟩, ⟨_, _, _, _, _, Q₃⟩, ⟨C₃, _, _, _, _, Q₄⟩, ⟨_, _, _, _, _, Q₅⟩, ⟨_, _, _, _, _, Q₆⟩,
    ⟨C₄, _, _, _, _, Q₇⟩, ⟨Ch, hCh, Q₈⟩, Q₉, Q₁₀, Q₁₁, ⟨_, _, _, _, _, Q₁₂⟩, Q₁₃, Q₁₄⟩ := hh
  exact exists_bounds hDr hf hKf hrun hg hy hk2 hk8 hd hG hW hM hE hAR C₂ C₃ C₄ Ch hCh Q₂ (fun S => (Q₃ S).1) (fun S => (Q₃ S).2) Q₄
    (fun S => (Q₅ S).1) (fun S => (Q₅ S).2) Q₆ (fun S => (Q₇ S).2.1)
    (fun S F u z hu => (Q₈ S F u z hu).2) Q₉ Q₁₀ Q₁₁ Q₁₂
    (fun S => ⟨(Q₁₃ S).2.1, fun rule ms Sq p a b c d => ((Q₁₃ S).2.2.2 rule ms Sq p a b c d).1⟩) Q₁₄
end YangMills.Construction.MomentLaw
end
