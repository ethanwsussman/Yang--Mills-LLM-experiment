import YangMills.Construction.HilbertSpaces.EnergyDominatesMomentumOnTheCompletionProof
import YangMills.Construction.ReflectionPositiveLimits.FromFivePointInequalitiesToTheConeProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.EuclideanBorel.FunctionalCalculus
theorem enorm_sq_eq_ofReal (z : ℂ) : ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg z), ofReal_norm]
theorem enorm_add_sq_le_two_mul (a b : ℂ) : ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  rw [enorm_sq_eq_ofReal, enorm_sq_eq_ofReal, enorm_sq_eq_ofReal]
  have h : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    nlinarith [norm_add_le a b, norm_nonneg (a + b), norm_nonneg a, norm_nonneg b,
      sq_nonneg (‖a‖ - ‖b‖)]
  calc ENNReal.ofReal (‖a + b‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal h
    _ = 2 * ENNReal.ofReal (‖a‖ ^ 2) + 2 * ENNReal.ofReal (‖b‖ ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        simp
theorem le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by apply _root_.YangMills.Construction.ReflectionPositivity.FivePointCone.ennreal_le_one_add_sq <;> assumption
theorem tendsto_zero_of_tendsto_ofReal_norm_sq {H : Type*} [NormedAddCommGroup H] {u : ℕ → H}
    (h : Tendsto (fun k => ENNReal.ofReal (‖u k‖ ^ 2)) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  have h₂ : Tendsto (fun k => ‖u k‖ ^ 2) atTop (𝓝 0) := by
    have h₁ := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [show ENNReal.toReal 0 = 0 from rfl] at h₁
    exact h₁.congr fun k => ENNReal.toReal_ofReal (by positivity)
  have h₃ := (Real.continuous_sqrt.tendsto 0).comp h₂
  rw [Real.sqrt_zero] at h₃
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (h₃.congr fun k => Real.sqrt_sq (norm_nonneg _))
section Setup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
theorem measurable_cutoff {f : Space n → ℂ} (hf : Measurable f) (k : ℕ) :
    Measurable (cutoff f k) :=
  hf.indicator (measurableSet_le hf.norm measurable_const)
theorem cutoff_apply_of_le {f : Space n → ℂ} {k : ℕ} {y : Space n} (h : ‖f y‖ ≤ k) :
    cutoff f k y = f y :=
  Set.indicator_of_mem (s := {y | ‖f y‖ ≤ k}) h f
theorem cutoff_apply_of_not_le {f : Space n → ℂ} {k : ℕ} {y : Space n} (h : ¬ ‖f y‖ ≤ k) :
    cutoff f k y = 0 :=
  Set.indicator_of_notMem (s := {y | ‖f y‖ ≤ k}) h f
theorem isBoundedMeasurableFn_cutoff {f : Space n → ℂ} (hf : Measurable f) (k : ℕ) :
    IsBoundedMeasurableFn (cutoff f k) := by
  refine ⟨measurable_cutoff hf k, k, fun y => ?_⟩
  by_cases h : ‖f y‖ ≤ k
  · rwa [cutoff_apply_of_le h]
  · rw [cutoff_apply_of_not_le h]; simp
theorem norm_cutoff_le (f : Space n → ℂ) (k : ℕ) (y : Space n) :
    ‖cutoff f k y‖ ≤ ‖f y‖ := by
  by_cases h : ‖f y‖ ≤ k
  · rw [cutoff_apply_of_le h]
  · rw [cutoff_apply_of_not_le h]; simp
theorem enorm_cutoff_sub_le (f : Space n → ℂ) (k : ℕ) (y : Space n) :
    ‖cutoff f k y - f y‖ₑ ≤ ‖f y‖ₑ := by
  by_cases h : ‖f y‖ ≤ k
  · rw [cutoff_apply_of_le h]; simp
  · rw [cutoff_apply_of_not_le h]; simp
theorem eventually_cutoff_eq (f : Space n → ℂ) (y : Space n) :
    ∀ᶠ k : ℕ in atTop, cutoff f k y = f y := by
  filter_upwards [eventually_ge_atTop ⌈‖f y‖⌉₊] with k hk
  exact cutoff_apply_of_le ((Nat.le_ceil _).trans (by exact_mod_cast hk))
theorem boundedFn_add {f g : Space n → ℂ} (hf : IsBoundedMeasurableFn f)
    (hg : IsBoundedMeasurableFn g) : IsBoundedMeasurableFn fun y => f y + g y := by
  obtain ⟨hf, C, hC⟩ := hf
  obtain ⟨hg, D, hD⟩ := hg
  exact ⟨hf.add hg, C + D, fun y => (norm_add_le _ _).trans (add_le_add (hC y) (hD y))⟩
theorem boundedFn_mul {f g : Space n → ℂ} (hf : IsBoundedMeasurableFn f)
    (hg : IsBoundedMeasurableFn g) : IsBoundedMeasurableFn fun y => f y * g y := by apply _root_.YangMills.Construction.PositiveFormReconstruction.CompletionEnergyBound.isBoundedMeasurableFn_mul <;> assumption
theorem boundedFn_const (c : ℂ) : IsBoundedMeasurableFn fun _ : Space n => c :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩
theorem boundedFn_conj {f : Space n → ℂ} (hf : IsBoundedMeasurableFn f) :
    IsBoundedMeasurableFn fun y => conj (f y) := by
  obtain ⟨hf, C, hC⟩ := hf
  refine ⟨Complex.continuous_conj.measurable.comp hf, C, fun y => ?_⟩
  rw [RCLike.norm_conj]
  exact hC y
theorem boundedFn_indicator (Δ : BorelSubset n) :
    IsBoundedMeasurableFn (Δ.1.indicator fun _ => (1 : ℂ)) := by
  refine ⟨measurable_const.indicator Δ.2, 1, fun y => ?_⟩
  by_cases h : y ∈ Δ.1
  · simp [h]
  · simp [h]
structure Hypotheses (E : BorelSubset n → H →L[ℂ] H) : Prop where
  pvm : IsPVM E
  diag : DiagonalMeasureProperties E
  null : NullProperties E
  cross : CrossFormProperties E
  unique : BoundedCalculusUnique E
  calc_ : BoundedCalculusProperties E
  cutoffs : CutoffsConverge E
variable {E : BorelSubset n → H →L[ℂ] H}
theorem Hypotheses.isFiniteMeasure (hE : Hypotheses E) (ψ : H) :
    IsFiniteMeasure (diagonalMeasure E ψ) :=
  ⟨by rw [hE.diag.2.2.1 ψ]; exact ENNReal.ofReal_lt_top⟩
theorem Hypotheses.diagonalMeasure_apply (hE : Hypotheses E) (ψ : H) (Δ : BorelSubset n) :
    diagonalMeasure E ψ Δ.1 = ENNReal.ofReal (‖E Δ ψ‖ ^ 2) :=
  hE.diag.2.1 ψ Δ
theorem ofReal_norm_boundedCalculus_sq (hE : Hypotheses E) {b : Space n → ℂ}
    (hb : IsBoundedMeasurableFn b) (ψ : H) :
    ENNReal.ofReal (‖boundedCalculus E b ψ‖ ^ 2) = ∫⁻ y, ‖b y‖ₑ ^ 2 ∂(diagonalMeasure E ψ) := by
  have := hE.isFiniteMeasure ψ
  have hint : Integrable (fun y => ‖b y‖ ^ 2) (diagonalMeasure E ψ) := by
    obtain ⟨hm, C, hC⟩ := hb
    refine Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable (C ^ 2)
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC y) 2
  rw [hE.calc_.2.2.2 b hb ψ, ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun y => by positivity)]
  exact lintegral_congr fun y => (enorm_sq_eq_ofReal _).symm
theorem boundedCalculus_sub_apply (hE : Hypotheses E) {a b : Space n → ℂ}
    (ha : IsBoundedMeasurableFn a) (hb : IsBoundedMeasurableFn b) (ψ : H) :
    boundedCalculus E a ψ - boundedCalculus E b ψ =
      boundedCalculus E (fun y => a y + (-1) * b y) ψ := by
  rw [(hE.calc_.1 a b (-1) ha hb).1]
  simp [sub_eq_add_neg]
theorem boundedFn_add_neg_mul (hb : IsBoundedMeasurableFn (fun _ : Space n => (-1 : ℂ)))
    {a b : Space n → ℂ} (ha : IsBoundedMeasurableFn a) (hb' : IsBoundedMeasurableFn b) :
    IsBoundedMeasurableFn fun y => a y + (-1) * b y :=
  boundedFn_add ha (boundedFn_mul hb hb')
theorem ofReal_norm_boundedCalculus_sub_sq (hE : Hypotheses E) {a b : Space n → ℂ}
    (ha : IsBoundedMeasurableFn a) (hb : IsBoundedMeasurableFn b) (ψ : H) :
    ENNReal.ofReal (‖boundedCalculus E a ψ - boundedCalculus E b ψ‖ ^ 2) =
      ∫⁻ y, ‖a y - b y‖ₑ ^ 2 ∂(diagonalMeasure E ψ) := by
  rw [boundedCalculus_sub_apply hE ha hb,
    ofReal_norm_boundedCalculus_sq hE (boundedFn_add_neg_mul (boundedFn_const _) ha hb)]
  refine lintegral_congr fun y => ?_
  congr 2
  ring
theorem tendsto_lintegral_cutoff_sub (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f)
    {ψ : H} (h : ψ ∈ sqIntegrableDomain E f) :
    Tendsto (fun k : ℕ => ∫⁻ y, ‖cutoff f k y - f y‖ₑ ^ 2 ∂(diagonalMeasure E ψ)) atTop
      (𝓝 0) := by
  have := tendsto_lintegral_of_dominated_convergence (μ := diagonalMeasure E ψ)
    (F := fun (k : ℕ) y => ‖cutoff f k y - f y‖ₑ ^ 2) (f := fun _ => 0)
    (fun y => ‖f y‖ₑ ^ 2)
    (fun k => ((measurable_cutoff hf k).sub hf).enorm.pow_const 2)
    (fun k => ae_of_all _ fun y => pow_le_pow_left₀ zero_le (enorm_cutoff_sub_le f k y) 2)
    (ne_of_lt h)
    (ae_of_all _ fun y => tendsto_const_nhds.congr' (by
      filter_upwards [eventually_cutoff_eq f y] with k hk
      simp [hk]))
  simpa using this
theorem tendsto_boundedCalculus_cutoff (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f)
    {ψ : H} (h : ψ ∈ sqIntegrableDomain E f) :
    Tendsto (fun k : ℕ => boundedCalculus E (cutoff f k) ψ) atTop
      (𝓝 (spectralIntegral E f ⟨ψ, h⟩)) :=
  tendsto_nhds_limUnder (hE.cutoffs.1 f hf ψ h)
theorem tendsto_boundedCalculus_of_meanSquare (hE : Hypotheses E) {f : Space n → ℂ}
    (hf : Measurable f) {ψ : H} (h : ψ ∈ sqIntegrableDomain E f) {b : ℕ → Space n → ℂ}
    (hb : ∀ k, IsBoundedMeasurableFn (b k))
    (hl : Tendsto (fun k => ∫⁻ y, ‖b k y - f y‖ₑ ^ 2 ∂(diagonalMeasure E ψ)) atTop (𝓝 0)) :
    Tendsto (fun k => boundedCalculus E (b k) ψ) atTop (𝓝 (spectralIntegral E f ⟨ψ, h⟩)) := by
  have h₀ : Tendsto (fun k : ℕ => boundedCalculus E (b k) ψ -
      boundedCalculus E (cutoff f k) ψ) atTop (𝓝 0) := by
    refine tendsto_zero_of_tendsto_ofReal_norm_sq ?_
    have hs : Tendsto (fun k : ℕ => 2 * ∫⁻ y, ‖b k y - f y‖ₑ ^ 2 ∂(diagonalMeasure E ψ) +
        2 * ∫⁻ y, ‖cutoff f k y - f y‖ₑ ^ 2 ∂(diagonalMeasure E ψ)) atTop (𝓝 0) := by
      have h1 := ENNReal.Tendsto.const_mul (a := 2) hl (Or.inr (by norm_num))
      have h2 := ENNReal.Tendsto.const_mul (a := 2) (tendsto_lintegral_cutoff_sub hE hf h)
        (Or.inr (by norm_num))
      simpa using h1.add h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => zero_le)
      fun k => ?_
    rw [ofReal_norm_boundedCalculus_sub_sq hE (hb k) (isBoundedMeasurableFn_cutoff hf k)]
    calc ∫⁻ y, ‖b k y - cutoff f k y‖ₑ ^ 2 ∂(diagonalMeasure E ψ)
        ≤ ∫⁻ y, (2 * ‖b k y - f y‖ₑ ^ 2 + 2 * ‖cutoff f k y - f y‖ₑ ^ 2)
            ∂(diagonalMeasure E ψ) := by
          refine lintegral_mono fun y => ?_
          have := enorm_add_sq_le_two_mul (b k y - f y) (f y - cutoff f k y)
          rw [enorm_sub_rev (f y)] at this
          simpa using this
      _ = _ := by
          have hm1 : Measurable fun y => 2 * ‖b k y - f y‖ₑ ^ 2 :=
            (((hb k).1.sub hf).enorm.pow_const 2).const_mul 2
          rw [lintegral_add_left hm1, lintegral_const_mul' _ _ (by simp),
            lintegral_const_mul' _ _ (by simp)]
  simpa using h₀.add (tendsto_boundedCalculus_cutoff hE hf h)
theorem mem_domain_of_boundedFn (hE : Hypotheses E) {b : Space n → ℂ}
    (hb : IsBoundedMeasurableFn b) (ψ : H) : ψ ∈ sqIntegrableDomain E b := by
  rw [(hE.cutoffs.2 b hb).1]
  exact mem_univ ψ
theorem spectralIntegral_of_boundedFn (hE : Hypotheses E) {b : Space n → ℂ}
    (hb : IsBoundedMeasurableFn b) {ψ : H} (h : ψ ∈ sqIntegrableDomain E b) :
    spectralIntegral E b ⟨ψ, h⟩ = boundedCalculus E b ψ :=
  spectralIntegral_eq_boundedCalculus hE.cutoffs hb ⟨ψ, h⟩
theorem mem_domain_add_smul (hE : Hypotheses E) {f g : Space n → ℂ} (hf : Measurable f)
    (hg : Measurable g) (c : ℂ) {ψ : H} (h₁ : ψ ∈ sqIntegrableDomain E f)
    (h₂ : ψ ∈ sqIntegrableDomain E g) :
    ψ ∈ sqIntegrableDomain E fun y => f y + c * g y := by
  have hc : ∀ y, ‖f y + c * g y‖ₑ ^ 2 ≤ 2 * ‖f y‖ₑ ^ 2 + (2 * ‖c‖ₑ ^ 2) * ‖g y‖ₑ ^ 2 := fun y => by
    have := enorm_add_sq_le_two_mul (f y) (c * g y)
    rw [enorm_mul, mul_pow, ← mul_assoc] at this
    exact this
  refine lt_of_le_of_lt (lintegral_mono hc) ?_
  rw [lintegral_add_left ((hf.enorm.pow_const 2).const_mul 2), lintegral_const_mul' _ _ (by simp),
    lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top])]
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (by simp) h₁, ENNReal.mul_lt_top (by simp [ENNReal.mul_lt_top]) h₂⟩
theorem spectralIntegral_add_smul (hE : Hypotheses E) {f g : Space n → ℂ} (hf : Measurable f)
    (hg : Measurable g) (c : ℂ) {ψ : H} (h₁ : ψ ∈ sqIntegrableDomain E f)
    (h₂ : ψ ∈ sqIntegrableDomain E g)
    (h : ψ ∈ sqIntegrableDomain E fun y => f y + c * g y) :
    spectralIntegral E (fun y => f y + c * g y) ⟨ψ, h⟩ =
      spectralIntegral E f ⟨ψ, h₁⟩ + c • spectralIntegral E g ⟨ψ, h₂⟩ := by
  have hm : Measurable fun y => f y + c * g y := hf.add (measurable_const.mul hg)
  have hbd : ∀ k : ℕ, IsBoundedMeasurableFn fun y => cutoff f k y + c * cutoff g k y :=
    fun k => boundedFn_add (isBoundedMeasurableFn_cutoff hf k)
      (boundedFn_mul (boundedFn_const c) (isBoundedMeasurableFn_cutoff hg k))
  have hl : Tendsto (fun k : ℕ => ∫⁻ y, ‖(cutoff f k y + c * cutoff g k y) -
      (f y + c * g y)‖ₑ ^ 2 ∂(diagonalMeasure E ψ)) atTop (𝓝 0) := by
    have hs : Tendsto (fun k : ℕ => 2 * ∫⁻ y, ‖cutoff f k y - f y‖ₑ ^ 2 ∂(diagonalMeasure E ψ) +
        (2 * ‖c‖ₑ ^ 2) * ∫⁻ y, ‖cutoff g k y - g y‖ₑ ^ 2 ∂(diagonalMeasure E ψ)) atTop
        (𝓝 0) := by
      have h1 := ENNReal.Tendsto.const_mul (a := 2) (tendsto_lintegral_cutoff_sub hE hf h₁)
        (Or.inr (by norm_num))
      have h2 := ENNReal.Tendsto.const_mul (a := 2 * ‖c‖ₑ ^ 2)
        (tendsto_lintegral_cutoff_sub hE hg h₂) (Or.inr (by simp [ENNReal.mul_eq_top]))
      simpa using h1.add h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => zero_le)
      fun k => ?_
    calc ∫⁻ y, ‖(cutoff f k y + c * cutoff g k y) - (f y + c * g y)‖ₑ ^ 2
          ∂(diagonalMeasure E ψ)
        ≤ ∫⁻ y, (2 * ‖cutoff f k y - f y‖ₑ ^ 2 +
            (2 * ‖c‖ₑ ^ 2) * ‖cutoff g k y - g y‖ₑ ^ 2) ∂(diagonalMeasure E ψ) := by
          refine lintegral_mono fun y => ?_
          have := enorm_add_sq_le_two_mul (cutoff f k y - f y) (c * (cutoff g k y - g y))
          rw [enorm_mul, mul_pow, ← mul_assoc] at this
          have he : (cutoff f k y + c * cutoff g k y) - (f y + c * g y) =
              cutoff f k y - f y + c * (cutoff g k y - g y) := by ring
          rw [he]
          exact this
      _ = _ := by
          have hm1 : Measurable fun y => 2 * ‖cutoff f k y - f y‖ₑ ^ 2 :=
            (((measurable_cutoff hf k).sub hf).enorm.pow_const 2).const_mul 2
          rw [lintegral_add_left hm1, lintegral_const_mul' _ _ (by simp),
            lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top])]
  have t₁ := tendsto_boundedCalculus_of_meanSquare hE hm h hbd hl
  have t₂ := (tendsto_boundedCalculus_cutoff hE hf h₁).add
    ((tendsto_boundedCalculus_cutoff hE hg h₂).const_smul c)
  refine tendsto_nhds_unique t₁ (t₂.congr fun k => ?_)
  rw [(hE.calc_.1 _ _ c (isBoundedMeasurableFn_cutoff hf k) (isBoundedMeasurableFn_cutoff hg k)).1]
  rfl
end Setup
section Values
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
  {E : BorelSubset n → H →L[ℂ] H}
theorem enorm_cutoff_le (f : Space n → ℂ) (k : ℕ) (y : Space n) :
    ‖cutoff f k y‖ₑ ≤ ‖f y‖ₑ := by
  by_cases h : ‖f y‖ ≤ k
  · rw [cutoff_apply_of_le h]
  · rw [cutoff_apply_of_not_le h]; simp
theorem tendsto_cutoff_apply (f : Space n → ℂ) (y : Space n) :
    Tendsto (fun k : ℕ => cutoff f k y) atTop (𝓝 (f y)) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [eventually_cutoff_eq f y] with k hk
    exact hk.symm)
theorem tendsto_enorm_sq_cutoff (f : Space n → ℂ) (y : Space n) :
    Tendsto (fun k : ℕ => ‖cutoff f k y‖ₑ ^ 2) atTop (𝓝 (‖f y‖ₑ ^ 2)) :=
  ((ENNReal.continuous_pow 2).tendsto _).comp
    ((continuous_enorm.tendsto _).comp (tendsto_cutoff_apply f y))
theorem ofReal_norm_spectralIntegral_sq (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f)
    {ψ : H} (h : ψ ∈ sqIntegrableDomain E f) :
    ENNReal.ofReal (‖spectralIntegral E f ⟨ψ, h⟩‖ ^ 2) =
      ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(diagonalMeasure E ψ) := by
  have t₁ : Tendsto (fun k : ℕ => ENNReal.ofReal (‖boundedCalculus E (cutoff f k) ψ‖ ^ 2))
      atTop (𝓝 (ENNReal.ofReal (‖spectralIntegral E f ⟨ψ, h⟩‖ ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((tendsto_boundedCalculus_cutoff hE hf h).norm.pow 2)
  have t₂ : Tendsto (fun k : ℕ => ∫⁻ y, ‖cutoff f k y‖ₑ ^ 2 ∂(diagonalMeasure E ψ)) atTop
      (𝓝 (∫⁻ y, ‖f y‖ₑ ^ 2 ∂(diagonalMeasure E ψ))) :=
    tendsto_lintegral_of_dominated_convergence (fun y => ‖f y‖ₑ ^ 2)
      (fun k => (measurable_cutoff hf k).enorm.pow_const 2)
      (fun k => ae_of_all _ fun y => pow_le_pow_left₀ zero_le (enorm_cutoff_le f k y) 2)
      (ne_of_lt h)
      (ae_of_all _ (tendsto_enorm_sq_cutoff f))
  exact tendsto_nhds_unique t₁
    (t₂.congr fun k => (ofReal_norm_boundedCalculus_sq hE (isBoundedMeasurableFn_cutoff hf k) ψ).symm)
theorem norm_spectralIntegral_sq (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f)
    {ψ : H} (h : ψ ∈ sqIntegrableDomain E f) :
    ‖spectralIntegral E f ⟨ψ, h⟩‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 ∂(diagonalMeasure E ψ) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => by positivity)
    (hf.norm.pow_const 2).aestronglyMeasurable]
  have e : ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂(diagonalMeasure E ψ) =
      ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(diagonalMeasure E ψ) :=
    lintegral_congr fun y => (enorm_sq_eq_ofReal _).symm
  rw [e, ← ofReal_norm_spectralIntegral_sq hE hf h, ENNReal.toReal_ofReal (by positivity)]
theorem measurable_add_neg_mul {f g : Space n → ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun y => f y + (-1) * g y :=
  hf.add (measurable_const.mul hg)
theorem spectralIntegral_sub (hE : Hypotheses E) {f g : Space n → ℂ} (hf : Measurable f)
    (hg : Measurable g) {ψ : H} (h₁ : ψ ∈ sqIntegrableDomain E f)
    (h₂ : ψ ∈ sqIntegrableDomain E g) :
    spectralIntegral E f ⟨ψ, h₁⟩ - spectralIntegral E g ⟨ψ, h₂⟩ =
      spectralIntegral E (fun y => f y + (-1) * g y)
        ⟨ψ, mem_domain_add_smul hE hf hg (-1) h₁ h₂⟩ := by
  rw [spectralIntegral_add_smul hE hf hg (-1) h₁ h₂]
  simp [sub_eq_add_neg]
theorem ofReal_norm_spectralIntegral_sub_sq (hE : Hypotheses E) {f g : Space n → ℂ}
    (hf : Measurable f) (hg : Measurable g) {ψ : H} (h₁ : ψ ∈ sqIntegrableDomain E f)
    (h₂ : ψ ∈ sqIntegrableDomain E g) :
    ENNReal.ofReal (‖spectralIntegral E f ⟨ψ, h₁⟩ - spectralIntegral E g ⟨ψ, h₂⟩‖ ^ 2) =
      ∫⁻ y, ‖f y - g y‖ₑ ^ 2 ∂(diagonalMeasure E ψ) := by
  rw [spectralIntegral_sub hE hf hg h₁ h₂,
    ofReal_norm_spectralIntegral_sq hE (measurable_add_neg_mul hf hg)]
  refine lintegral_congr fun y => ?_
  congr 2
  ring
theorem norm_spectralIntegral_sub_sq (hE : Hypotheses E) {f g : Space n → ℂ} (hf : Measurable f)
    (hg : Measurable g) {ψ : H} (h₁ : ψ ∈ sqIntegrableDomain E f)
    (h₂ : ψ ∈ sqIntegrableDomain E g) :
    ‖spectralIntegral E f ⟨ψ, h₁⟩ - spectralIntegral E g ⟨ψ, h₂⟩‖ ^ 2 =
      ∫ y, ‖f y - g y‖ ^ 2 ∂(diagonalMeasure E ψ) := by
  rw [spectralIntegral_sub hE hf hg h₁ h₂,
    norm_spectralIntegral_sq hE (measurable_add_neg_mul hf hg)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  show ‖f y + (-1) * g y‖ ^ 2 = ‖f y - g y‖ ^ 2
  congr 2
  ring
theorem integrable_of_mem_domain (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f)
    {ψ : H} (h : ψ ∈ sqIntegrableDomain E f) : Integrable f (diagonalMeasure E ψ) := by
  have := hE.isFiniteMeasure ψ
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ y, ‖f y‖ₑ ∂(diagonalMeasure E ψ)
      ≤ ∫⁻ y, (1 + ‖f y‖ₑ ^ 2) ∂(diagonalMeasure E ψ) :=
        lintegral_mono fun y => le_one_add_sq _
    _ < ∞ := by
        rw [lintegral_add_left measurable_const, lintegral_const]
        exact ENNReal.add_lt_top.mpr ⟨by simp [measure_lt_top], h⟩
theorem inner_spectralIntegral (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f)
    {ψ : H} (h : ψ ∈ sqIntegrableDomain E f) :
    ⟪ψ, spectralIntegral E f ⟨ψ, h⟩⟫_ℂ = ∫ y, f y ∂(diagonalMeasure E ψ) := by
  have t₁ : Tendsto (fun k : ℕ => ⟪ψ, boundedCalculus E (cutoff f k) ψ⟫_ℂ) atTop
      (𝓝 ⟪ψ, spectralIntegral E f ⟨ψ, h⟩⟫_ℂ) :=
    tendsto_const_nhds.inner (tendsto_boundedCalculus_cutoff hE hf h)
  have t₂ : Tendsto (fun k : ℕ => ∫ y, cutoff f k y ∂(diagonalMeasure E ψ)) atTop
      (𝓝 (∫ y, f y ∂(diagonalMeasure E ψ))) :=
    tendsto_integral_of_dominated_convergence (fun y => ‖f y‖)
      (fun k => (measurable_cutoff hf k).aestronglyMeasurable)
      (integrable_of_mem_domain hE hf h).norm
      (fun k => ae_of_all _ (norm_cutoff_le f k))
      (ae_of_all _ (tendsto_cutoff_apply f))
  exact tendsto_nhds_unique t₁
    (t₂.congr fun k => ((hE.unique _ (isBoundedMeasurableFn_cutoff hf k)).2.2.1 ψ).symm)
theorem domain_add_mem (hE : Hypotheses E) {f : Space n → ℂ} {φ ψ : H}
    (h₁ : φ ∈ sqIntegrableDomain E f) (h₂ : ψ ∈ sqIntegrableDomain E f) :
    φ + ψ ∈ sqIntegrableDomain E f := by
  have hle : diagonalMeasure E (φ + ψ) ≤
      (2 : ℝ≥0∞) • diagonalMeasure E φ + (2 : ℝ≥0∞) • diagonalMeasure E ψ :=
    Measure.le_iff.mpr fun s hs => by
      simpa using hE.diag.2.2.2.2.1 φ ψ ⟨s, hs⟩
  refine lt_of_le_of_lt (lintegral_mono' hle le_rfl) ?_
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (by simp) h₁, ENNReal.mul_lt_top (by simp) h₂⟩
theorem domain_smul_mem (hE : Hypotheses E) {f : Space n → ℂ} (c : ℂ) {ψ : H}
    (h : ψ ∈ sqIntegrableDomain E f) : c • ψ ∈ sqIntegrableDomain E f := by
  show ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(diagonalMeasure E (c • ψ)) < ∞
  rw [hE.diag.2.2.2.1 c ψ, lintegral_smul_measure]
  exact ENNReal.mul_lt_top (by simp) h
theorem domain_zero_mem (hE : Hypotheses E) (f : Space n → ℂ) :
    (0 : H) ∈ sqIntegrableDomain E f := by
  show ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(diagonalMeasure E (0 : H)) < ∞
  have h0 : diagonalMeasure E (0 : H) = 0 := by
    have := hE.diag.2.2.2.1 0 (0 : H)
    simpa using this
  rw [h0]
  simp
def domainSubmodule (hE : Hypotheses E) (f : Space n → ℂ) : Submodule ℂ H where
  carrier := sqIntegrableDomain E f
  add_mem' := domain_add_mem hE
  zero_mem' := domain_zero_mem hE f
  smul_mem' c _ h := domain_smul_mem hE c h
theorem spectralIntegral_map_add (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f)
    {φ ψ : H} (h₁ : φ ∈ sqIntegrableDomain E f) (h₂ : ψ ∈ sqIntegrableDomain E f)
    (h : φ + ψ ∈ sqIntegrableDomain E f) :
    spectralIntegral E f ⟨φ + ψ, h⟩ =
      spectralIntegral E f ⟨φ, h₁⟩ + spectralIntegral E f ⟨ψ, h₂⟩ := by
  refine tendsto_nhds_unique (tendsto_boundedCalculus_cutoff hE hf h)
    (((tendsto_boundedCalculus_cutoff hE hf h₁).add
      (tendsto_boundedCalculus_cutoff hE hf h₂)).congr fun k => ?_)
  rw [map_add]
theorem spectralIntegral_map_smul (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f)
    (c : ℂ) {ψ : H} (h₁ : ψ ∈ sqIntegrableDomain E f) (h : c • ψ ∈ sqIntegrableDomain E f) :
    spectralIntegral E f ⟨c • ψ, h⟩ = c • spectralIntegral E f ⟨ψ, h₁⟩ := by
  refine tendsto_nhds_unique (tendsto_boundedCalculus_cutoff hE hf h)
    (((tendsto_boundedCalculus_cutoff hE hf h₁).const_smul c).congr fun k => ?_)
  rw [map_smul]
def asUnboundedOp (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f) :
    SpectralTheory.UnboundedOp H :=
  ⟨domainSubmodule hE f,
    { toFun := fun ψ => spectralIntegral E f ⟨ψ.1, ψ.2⟩
      map_add' := fun φ ψ => spectralIntegral_map_add hE hf φ.2 ψ.2 (φ + ψ).2
      map_smul' := fun c ψ => spectralIntegral_map_smul hE hf c ψ.2 (c • ψ).2 }⟩
theorem isSpectralIntegralOp_spectralOp (hE : Hypotheses E) {f : Space n → ℂ}
    (hf : Measurable f) : RealizesSpectralIntegral E f (spectralOp E f) :=
  Classical.epsilon_spec (p := RealizesSpectralIntegral E f)
    ⟨asUnboundedOp hE hf, rfl, fun ψ => ⟨ψ.2, rfl⟩⟩
theorem mem_spectralOp_domain_iff (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f)
    {ψ : H} : ψ ∈ (spectralOp E f).domain ↔ ψ ∈ sqIntegrableDomain E f := by
  rw [← (isSpectralIntegralOp_spectralOp hE hf).1]
  rfl
theorem spectralOp_apply (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f)
    (ψ : (spectralOp E f).domain) (h : ψ.1 ∈ sqIntegrableDomain E f) :
    spectralOp E f ψ = spectralIntegral E f ⟨ψ.1, h⟩ := by
  obtain ⟨_, hv⟩ := (isSpectralIntegralOp_spectralOp hE hf).2 ψ
  exact hv.symm
theorem spectralOp_ext (hE : Hypotheses E) {f g : Space n → ℂ} (hf : Measurable f)
    (hg : Measurable g) (hD : sqIntegrableDomain E f = sqIntegrableDomain E g)
    (hv : ∀ (ψ : H) (h₁ : ψ ∈ sqIntegrableDomain E f) (h₂ : ψ ∈ sqIntegrableDomain E g),
      spectralIntegral E f ⟨ψ, h₁⟩ = spectralIntegral E g ⟨ψ, h₂⟩) :
    spectralOp E f = spectralOp E g := by
  refine LinearPMap.ext (SetLike.coe_injective ?_) ?_
  · rw [(isSpectralIntegralOp_spectralOp hE hf).1, (isSpectralIntegralOp_spectralOp hE hg).1, hD]
  · intro x hx hx'
    have h₁ := (mem_spectralOp_domain_iff hE hf).mp hx
    have h₂ := (mem_spectralOp_domain_iff hE hg).mp hx'
    rw [spectralOp_apply hE hf ⟨x, hx⟩ h₁, spectralOp_apply hE hg ⟨x, hx'⟩ h₂]
    exact hv x h₁ h₂
theorem boundedCalculus_comp_apply (hE : Hypotheses E) {a b : Space n → ℂ}
    (ha : IsBoundedMeasurableFn a) (hb : IsBoundedMeasurableFn b) (ψ : H) :
    boundedCalculus E a (boundedCalculus E b ψ) = boundedCalculus E (fun y => a y * b y) ψ := by
  rw [(hE.calc_.1 a b 0 ha hb).2]
  rfl
theorem boundedCalculus_indicator (hE : Hypotheses E) (Δ : BorelSubset n) :
    boundedCalculus E (Δ.1.indicator fun _ => (1 : ℂ)) = E Δ :=
  hE.calc_.2.2.1 Δ
theorem boundedCalculus_one_apply (hE : Hypotheses E) (ψ : H) :
    boundedCalculus E (fun _ => (1 : ℂ)) ψ = ψ := by
  have h := boundedCalculus_indicator hE (⊤ : BorelSubset n)
  rw [hE.pvm.map_top] at h
  have e : ((⊤ : BorelSubset n).1).indicator (fun _ : Space n => (1 : ℂ)) = fun _ => 1 :=
    Set.indicator_univ _
  rw [e] at h
  rw [h]
  rfl
theorem diagonalMeasure_proj (hE : Hypotheses E) (Δ : BorelSubset n) (ψ : H) :
    diagonalMeasure E (E Δ ψ) = (diagonalMeasure E ψ).restrict Δ.1 := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.restrict_apply hs]
  exact hE.diag.2.2.2.2.2 ψ ⟨s, hs⟩ Δ
theorem proj_sublevel_mem_domain (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f)
    (k : ℕ) (ψ : H) : E (sublevelSet hf k) ψ ∈ sqIntegrableDomain E f := by
  show ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(diagonalMeasure E (E (sublevelSet hf k) ψ)) < ∞
  rw [diagonalMeasure_proj hE, ← lintegral_indicator (sublevelSet hf k).2]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_))
    (mem_domain_of_boundedFn hE (isBoundedMeasurableFn_cutoff hf k) ψ)
  by_cases h : ‖f y‖ ≤ k
  · rw [cutoff_apply_of_le h, Set.indicator_of_mem (show y ∈ (sublevelSet hf k).1 from h)]
  · rw [cutoff_apply_of_not_le h, Set.indicator_of_notMem (show y ∉ (sublevelSet hf k).1 from h)]
    simp
theorem spectralIntegral_proj_sublevel (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f)
    (k : ℕ) (ψ : H) :
    spectralIntegral E f ⟨E (sublevelSet hf k) ψ, proj_sublevel_mem_domain hE hf k ψ⟩ =
      boundedCalculus E (cutoff f k) ψ := by
  refine tendsto_nhds_unique (tendsto_boundedCalculus_cutoff hE hf (proj_sublevel_mem_domain hE hf k ψ))
    (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop k] with j hj
  rw [← boundedCalculus_indicator hE, boundedCalculus_comp_apply hE (isBoundedMeasurableFn_cutoff hf j)
    (boundedFn_indicator _)]
  congr 2
  funext y
  by_cases h : ‖f y‖ ≤ k
  · have hj' : ‖f y‖ ≤ j := h.trans (by exact_mod_cast hj)
    rw [cutoff_apply_of_le h, cutoff_apply_of_le hj',
      Set.indicator_of_mem (show y ∈ (sublevelSet hf k).1 from h)]
    simp
  · rw [cutoff_apply_of_not_le h, Set.indicator_of_notMem (show y ∉ (sublevelSet hf k).1 from h)]
    simp
theorem tendsto_proj_sublevel (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f) (ψ : H) :
    Tendsto (fun k : ℕ => E (sublevelSet hf k) ψ) atTop (𝓝 ψ) := by
  have hone : IsBoundedMeasurableFn fun _ : Space n => (1 : ℂ) := boundedFn_const 1
  have h₁ := mem_domain_of_boundedFn hE hone ψ
  have hl : Tendsto (fun k : ℕ => ∫⁻ y, ‖(sublevelSet hf k).1.indicator (fun _ => (1 : ℂ)) y - 1‖ₑ ^ 2
      ∂(diagonalMeasure E ψ)) atTop (𝓝 0) := by
    have := hE.isFiniteMeasure ψ
    have := tendsto_lintegral_of_dominated_convergence (μ := diagonalMeasure E ψ)
      (F := fun (k : ℕ) y => ‖(sublevelSet hf k).1.indicator (fun _ => (1 : ℂ)) y - 1‖ₑ ^ 2)
      (f := fun _ => 0) (fun _ => 1)
      (fun k => (((boundedFn_indicator (sublevelSet hf k)).1.sub measurable_const).enorm.pow_const 2))
      (fun k => ae_of_all _ fun y => by
        by_cases h : y ∈ (sublevelSet hf k).1
        · simp [h]
        · simp [h])
      (by simp [measure_ne_top])
      (ae_of_all _ fun y => tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop ⌈‖f y‖⌉₊] with k hk
        have hy : y ∈ (sublevelSet hf k).1 :=
          show ‖f y‖ ≤ k from (Nat.le_ceil _).trans (by exact_mod_cast hk)
        simp [hy]))
    simpa using this
  have t := tendsto_boundedCalculus_of_meanSquare hE measurable_const h₁
    (fun k => boundedFn_indicator (sublevelSet hf k)) hl
  rw [spectralIntegral_of_boundedFn hE hone h₁, boundedCalculus_one_apply hE] at t
  exact t.congr fun k => by rw [boundedCalculus_indicator hE]
theorem domainProperties (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f) :
    DomainProperties E hf where
  dense := by
    refine (FormsOperators.isDenseSet_iff_dense _).mpr fun ψ => ?_
    exact mem_closure_of_tendsto (tendsto_proj_sublevel hE hf ψ)
      (Eventually.of_forall fun k => proj_sublevel_mem_domain hE hf k ψ)
  isOp := isSpectralIntegralOp_spectralOp hE hf
  value_on_sublevel := fun ψ k _ =>
    ⟨boundedCalculus E (cutoff f k) ψ,
      ⟨proj_sublevel_mem_domain hE hf k ψ, spectralIntegral_proj_sublevel hE hf k ψ⟩,
      ⟨mem_domain_of_boundedFn hE (isBoundedMeasurableFn_cutoff hf k) ψ,
        spectralIntegral_of_boundedFn hE (isBoundedMeasurableFn_cutoff hf k) _⟩⟩
theorem linearityAndNorms (hE : Hypotheses E) {f g : Space n → ℂ} (hf : Measurable f)
    (hg : Measurable g) (c : ℂ) : LinearityAndNorms E f g c := fun ψ h₁ h₂ =>
  ⟨⟨mem_domain_add_smul hE hf hg c h₁ h₂, spectralIntegral_add_smul hE hf hg c h₁ h₂ _⟩,
    norm_spectralIntegral_sub_sq hE hf hg h₁ h₂, norm_spectralIntegral_sq hE hf h₁,
    inner_spectralIntegral hE hf h₁⟩
theorem enorm_conj_eq (z : ℂ) : ‖conj z‖ₑ = ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, RCLike.norm_conj]
theorem domain_conj_eq (f : Space n → ℂ) :
    sqIntegrableDomain E (fun y => conj (f y)) = sqIntegrableDomain E f := by
  ext ψ
  simp only [sqIntegrableDomain, mem_ofPred_eq, enorm_conj_eq]
theorem measurable_conj_comp {f : Space n → ℂ} (hf : Measurable f) :
    Measurable fun y => conj (f y) :=
  Complex.continuous_conj.measurable.comp hf
theorem conj_cutoff (f : Space n → ℂ) (k : ℕ) :
    (fun y => conj (cutoff f k y)) = cutoff (fun y => conj (f y)) k := by
  funext y
  by_cases h : ‖f y‖ ≤ k
  · rw [cutoff_apply_of_le h, cutoff_apply_of_le (f := fun y => conj (f y))
      (by simpa [RCLike.norm_conj] using h)]
  · rw [cutoff_apply_of_not_le h, cutoff_apply_of_not_le (f := fun y => conj (f y))
      (by simpa [RCLike.norm_conj] using h)]
    simp
theorem inner_spectralIntegral_conj (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f)
    {φ ψ : H} (hφ : φ ∈ sqIntegrableDomain E fun y => conj (f y))
    (hψ : ψ ∈ sqIntegrableDomain E f) :
    ⟪φ, spectralIntegral E f ⟨ψ, hψ⟩⟫_ℂ =
      ⟪spectralIntegral E (fun y => conj (f y)) ⟨φ, hφ⟩, ψ⟫_ℂ := by
  have t₁ : Tendsto (fun k : ℕ => ⟪φ, boundedCalculus E (cutoff f k) ψ⟫_ℂ) atTop
      (𝓝 ⟪φ, spectralIntegral E f ⟨ψ, hψ⟩⟫_ℂ) :=
    tendsto_const_nhds.inner (tendsto_boundedCalculus_cutoff hE hf hψ)
  have t₂ : Tendsto (fun k : ℕ =>
      ⟪boundedCalculus E (cutoff (fun y => conj (f y)) k) φ, ψ⟫_ℂ) atTop
      (𝓝 ⟪spectralIntegral E (fun y => conj (f y)) ⟨φ, hφ⟩, ψ⟫_ℂ) :=
    (tendsto_boundedCalculus_cutoff hE (measurable_conj_comp hf) hφ).inner tendsto_const_nhds
  refine tendsto_nhds_unique t₁ (t₂.congr fun k => ?_)
  rw [hE.calc_.2.1 _ (isBoundedMeasurableFn_cutoff hf k) φ ψ, conj_cutoff]
theorem lintegral_le_of_forall_cutoff (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f)
    {φ : H} {C : ℝ≥0∞}
    (hC : ∀ k : ℕ, ∫⁻ y, ‖cutoff f k y‖ₑ ^ 2 ∂(diagonalMeasure E φ) ≤ C) :
    ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(diagonalMeasure E φ) ≤ C := by
  calc ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(diagonalMeasure E φ)
      = ∫⁻ y, liminf (fun k : ℕ => ‖cutoff f k y‖ₑ ^ 2) atTop ∂(diagonalMeasure E φ) :=
        lintegral_congr fun y => (tendsto_enorm_sq_cutoff f y).liminf_eq.symm
    _ ≤ liminf (fun k : ℕ => ∫⁻ y, ‖cutoff f k y‖ₑ ^ 2 ∂(diagonalMeasure E φ)) atTop :=
        lintegral_liminf_le fun k => (measurable_cutoff hf k).enorm.pow_const 2
    _ ≤ liminf (fun _ : ℕ => C) atTop := liminf_le_liminf (Eventually.of_forall hC)
    _ = C := liminf_const C
theorem mem_domain_of_adjoint (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f)
    {φ φ' : H}
    (h : ∀ (χ : H) (hχ : χ ∈ sqIntegrableDomain E f),
      ⟪φ, spectralIntegral E f ⟨χ, hχ⟩⟫_ℂ = ⟪φ', χ⟫_ℂ) :
    φ ∈ sqIntegrableDomain E f := by
  refine lt_of_le_of_lt (lintegral_le_of_forall_cutoff hE hf (C := ENNReal.ofReal (‖φ'‖ ^ 2))
    fun k => ?_) ENNReal.ofReal_lt_top
  have hP := hE.pvm.isOrthoProjection (sublevelSet hf k)
  have hv : boundedCalculus E (fun y => conj (cutoff f k y)) φ = E (sublevelSet hf k) φ' := by
    refine ext_inner_right ℂ fun ψ => ?_
    have h₁ := h _ (proj_sublevel_mem_domain hE hf k ψ)
    rw [spectralIntegral_proj_sublevel hE hf k ψ] at h₁
    exact (hE.calc_.2.1 _ (isBoundedMeasurableFn_cutoff hf k) φ ψ).symm.trans
      (h₁.trans (hP.2 φ' ψ))
  calc ∫⁻ y, ‖cutoff f k y‖ₑ ^ 2 ∂(diagonalMeasure E φ)
      = ∫⁻ y, ‖conj (cutoff f k y)‖ₑ ^ 2 ∂(diagonalMeasure E φ) :=
        lintegral_congr fun y => by rw [enorm_conj_eq]
    _ = ENNReal.ofReal (‖boundedCalculus E (fun y => conj (cutoff f k y)) φ‖ ^ 2) :=
        (ofReal_norm_boundedCalculus_sq hE (boundedFn_conj (isBoundedMeasurableFn_cutoff hf k)) φ).symm
    _ = diagonalMeasure E φ' (sublevelSet hf k).1 := by rw [hv, hE.diagonalMeasure_apply]
    _ ≤ diagonalMeasure E φ' univ := measure_mono (subset_univ _)
    _ = ENNReal.ofReal (‖φ'‖ ^ 2) := hE.diag.2.2.1 φ'
theorem adjointProperties (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f) :
    AdjointProperties E f := by
  have hd : FormsOperators.IsDenselyDefined (spectralOp E f) := by
    unfold FormsOperators.IsDenselyDefined
    rw [(isSpectralIntegralOp_spectralOp hE hf).1]
    exact (domainProperties hE hf).dense
  have hcf := measurable_conj_comp hf
  have key : FormsOperators.adj (spectralOp E f) hd =
      spectralOp E fun y => conj (f y) := by
    refine LinearPMap.ext ?_ ?_
    · ext φ
      constructor
      · intro hφ
        obtain ⟨φ', hφ'⟩ : ∃ φ' : H, ∀ χ : (spectralOp E f).domain,
            ⟪φ, spectralOp E f χ⟫_ℂ = ⟪φ', (χ : H)⟫_ℂ := hφ
        refine (mem_spectralOp_domain_iff hE hcf).mpr ?_
        rw [domain_conj_eq]
        refine mem_domain_of_adjoint hE hf (φ' := φ') fun χ hχ => ?_
        have := hφ' ⟨χ, (mem_spectralOp_domain_iff hE hf).mpr hχ⟩
        rwa [spectralOp_apply hE hf _ hχ] at this
      · intro hφ
        have hc := (mem_spectralOp_domain_iff hE hcf).mp hφ
        show ∃ φ' : H, ∀ χ : (spectralOp E f).domain,
            ⟪φ, spectralOp E f χ⟫_ℂ = ⟪φ', (χ : H)⟫_ℂ
        refine ⟨spectralIntegral E (fun y => conj (f y)) ⟨φ, hc⟩, fun χ => ?_⟩
        have hχ := (mem_spectralOp_domain_iff hE hf).mp χ.2
        rw [spectralOp_apply hE hf χ hχ]
        exact inner_spectralIntegral_conj hE hf hc hχ
    · intro φ h₁ h₂
      have hc := (mem_spectralOp_domain_iff hE hcf).mp h₂
      rw [spectralOp_apply hE hcf ⟨φ, h₂⟩ hc]
      refine FormsOperators.adjValue_unique hd (φ := φ)
        (fun χ => FormsOperators.adj_spec _ hd ⟨φ, h₁⟩ χ) fun χ => ?_
      have hχ := (mem_spectralOp_domain_iff hE hf).mp χ.2
      rw [spectralOp_apply hE hf χ hχ]
      exact inner_spectralIntegral_conj hE hf hc hχ
  refine ⟨⟨hd, key⟩, fun hre => ?_⟩
  have he : (fun y => conj (f y)) = f := funext fun y => Complex.conj_eq_iff_im.mpr (hre y)
  exact ⟨hd, by rw [key, he]⟩
theorem enorm_le_ofReal_of_bound {b : Space n → ℂ} {C : ℝ} (hC : ∀ y, ‖b y‖ ≤ C) (y : Space n) :
    ‖b y‖ₑ ≤ ENNReal.ofReal C := by
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hC y)
theorem mem_domain_boundedFn_mul {b g : Space n → ℂ} (hb : IsBoundedMeasurableFn b) {ψ : H}
    (h : ψ ∈ sqIntegrableDomain E g) :
    ψ ∈ sqIntegrableDomain E fun y => b y * g y := by
  obtain ⟨hm, C, hC⟩ := hb
  have hle : ∀ y, ‖b y * g y‖ₑ ^ 2 ≤ ENNReal.ofReal C ^ 2 * ‖g y‖ₑ ^ 2 := fun y => by
    rw [enorm_mul, mul_pow]
    exact mul_le_mul_left (pow_le_pow_left₀ zero_le (enorm_le_ofReal_of_bound hC y) 2) _
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [lintegral_const_mul' _ _ (by simp)]
  exact ENNReal.mul_lt_top (by simp) h
theorem boundedCalculus_spectralIntegral (hE : Hypotheses E) {b g : Space n → ℂ}
    (hb : IsBoundedMeasurableFn b) (hg : Measurable g) {ψ : H} (h : ψ ∈ sqIntegrableDomain E g)
    (h' : ψ ∈ sqIntegrableDomain E fun y => b y * g y) :
    boundedCalculus E b (spectralIntegral E g ⟨ψ, h⟩) =
      spectralIntegral E (fun y => b y * g y) ⟨ψ, h'⟩ := by
  have hl : Tendsto (fun k : ℕ => ∫⁻ y, ‖b y * cutoff g k y - b y * g y‖ₑ ^ 2
      ∂(diagonalMeasure E ψ)) atTop (𝓝 0) := by
    obtain ⟨hm, C, hC⟩ := hb
    have hs := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C ^ 2)
      (tendsto_lintegral_cutoff_sub hE hg h) (Or.inr (by simp))
    rw [mul_zero] at hs
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => zero_le)
      fun k => ?_
    show _ ≤ ENNReal.ofReal C ^ 2 * _
    rw [← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono fun y => ?_
    rw [← mul_sub, enorm_mul, mul_pow]
    exact mul_le_mul_left (pow_le_pow_left₀ zero_le (enorm_le_ofReal_of_bound hC y) 2) _
  have t₁ := tendsto_boundedCalculus_of_meanSquare hE (hb.1.mul hg) h'
    (fun k => boundedFn_mul hb (isBoundedMeasurableFn_cutoff hg k)) hl
  have t₂ := ((boundedCalculus E b).continuous.tendsto _).comp
    (tendsto_boundedCalculus_cutoff hE hg h)
  exact tendsto_nhds_unique t₂ (t₁.congr fun k => (boundedCalculus_comp_apply hE hb
    (isBoundedMeasurableFn_cutoff hg k) ψ).symm)
theorem diagonalMeasure_spectralIntegral (hE : Hypotheses E) {g : Space n → ℂ}
    (hg : Measurable g) {ψ : H} (h : ψ ∈ sqIntegrableDomain E g) :
    diagonalMeasure E (spectralIntegral E g ⟨ψ, h⟩) =
      (diagonalMeasure E ψ).withDensity fun y => ‖g y‖ₑ ^ 2 := by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs, ← lintegral_indicator hs]
  have hb := boundedFn_indicator (⟨s, hs⟩ : BorelSubset n)
  have h' := mem_domain_boundedFn_mul hb h
  have e := boundedCalculus_spectralIntegral hE hb hg h h'
  rw [boundedCalculus_indicator hE] at e
  have e₂ := hE.diagonalMeasure_apply (spectralIntegral E g ⟨ψ, h⟩) ⟨s, hs⟩
  have hm : Measurable fun y => (⟨s, hs⟩ : BorelSubset n).1.indicator (fun _ => (1 : ℂ)) y * g y :=
    hb.1.mul hg
  rw [e, ofReal_norm_spectralIntegral_sq hE hm] at e₂
  refine e₂.trans (lintegral_congr fun y => ?_)
  by_cases hy : y ∈ s
  · simp [hy]
  · simp [hy]
theorem multiplicativity (hE : Hypotheses E) {f g : Space n → ℂ} (hf : Measurable f)
    (hg : Measurable g) : Multiplicativity E f g := fun ψ hψ => by
  have hμ := diagonalMeasure_spectralIntegral hE hg hψ
  have hI : ∀ u : Space n → ℝ≥0∞, Measurable u →
      ∫⁻ y, u y ∂(diagonalMeasure E (spectralIntegral E g ⟨ψ, hψ⟩)) =
        ∫⁻ y, ‖g y‖ₑ ^ 2 * u y ∂(diagonalMeasure E ψ) := fun u hu => by
    rw [hμ, lintegral_withDensity_eq_lintegral_mul _ (hg.enorm.pow_const 2) hu]
    rfl
  have hiff : spectralIntegral E g ⟨ψ, hψ⟩ ∈ sqIntegrableDomain E f ↔
      ψ ∈ sqIntegrableDomain E fun y => f y * g y := by
    show ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(diagonalMeasure E (spectralIntegral E g ⟨ψ, hψ⟩)) < ∞ ↔
      ∫⁻ y, ‖f y * g y‖ₑ ^ 2 ∂(diagonalMeasure E ψ) < ∞
    rw [hI _ (hf.enorm.pow_const 2)]
    have e : ∀ y, ‖g y‖ₑ ^ 2 * ‖f y‖ₑ ^ 2 = ‖f y * g y‖ₑ ^ 2 := fun y => by
      rw [enorm_mul, mul_pow, mul_comm]
    simp only [e]
  refine ⟨fun Δ => ?_, hiff, fun h => ?_⟩
  · rw [hμ, withDensity_apply _ Δ.2, ← lintegral_indicator Δ.2]
  · have h' := hiff.mp h
    refine ⟨h', ?_⟩
    have hj : ∀ j : ℕ, ψ ∈ sqIntegrableDomain E fun y => cutoff f j y * g y :=
      fun j => mem_domain_boundedFn_mul (isBoundedMeasurableFn_cutoff hf j) hψ
    have t₁ := tendsto_boundedCalculus_cutoff hE hf h
    have t₂ : Tendsto (fun j : ℕ => spectralIntegral E (fun y => cutoff f j y * g y)
        ⟨ψ, hj j⟩ - spectralIntegral E (fun y => f y * g y) ⟨ψ, h'⟩) atTop (𝓝 0) := by
      refine tendsto_zero_of_tendsto_ofReal_norm_sq
        ((tendsto_lintegral_cutoff_sub hE hf h).congr fun j => ?_)
      have hm₁ : Measurable fun y => cutoff f j y * g y :=
        (measurable_cutoff hf j).mul hg
      have hm₂ : Measurable fun y => f y * g y := hf.mul hg
      have hm₃ : Measurable fun y => ‖cutoff f j y - f y‖ₑ ^ 2 :=
        (((measurable_cutoff hf j).sub hf).enorm).pow_const 2
      rw [ofReal_norm_spectralIntegral_sub_sq hE hm₁ hm₂, hI _ hm₃]
      refine lintegral_congr fun y => ?_
      rw [← sub_mul, enorm_mul, mul_pow, mul_comm]
    have t₃ := t₂.add_const (spectralIntegral E (fun y => f y * g y) ⟨ψ, h'⟩)
    simp only [sub_add_cancel, zero_add] at t₃
    exact tendsto_nhds_unique t₃ (t₁.congr fun j =>
      boundedCalculus_spectralIntegral hE (isBoundedMeasurableFn_cutoff hf j) hg hψ (hj j))
end Values
section NullSets
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
  {E : BorelSubset n → H →L[ℂ] H}
theorem ae_of_holdsOffNull (hE : Hypotheses E) {p : Space n → Prop} (h : HoldsOffNull E p)
    (ψ : H) : ∀ᵐ y ∂(diagonalMeasure E ψ), p y := by
  obtain ⟨N, hN, hp⟩ := h
  refine ae_iff.mpr (measure_mono_null (fun y hy => ?_) ((hE.null.1 N).mp hN ψ))
  by_contra hy'
  exact hy (hp y hy')
theorem domain_congr_ae {f g : Space n → ℂ} (hae : ∀ ψ : H, f =ᵐ[diagonalMeasure E ψ] g) :
    sqIntegrableDomain E f = sqIntegrableDomain E g := by
  ext ψ
  show ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(diagonalMeasure E ψ) < ∞ ↔ ∫⁻ y, ‖g y‖ₑ ^ 2 ∂(diagonalMeasure E ψ) < ∞
  rw [lintegral_congr_ae (g := fun y => ‖g y‖ₑ ^ 2) ((hae ψ).mono fun y hy => by simp only [hy])]
theorem spectralIntegral_congr_ae (hE : Hypotheses E) {f g : Space n → ℂ} (hf : Measurable f)
    (hg : Measurable g) {ψ : H} (hae : f =ᵐ[diagonalMeasure E ψ] g)
    (h₁ : ψ ∈ sqIntegrableDomain E f) (h₂ : ψ ∈ sqIntegrableDomain E g) :
    spectralIntegral E f ⟨ψ, h₁⟩ = spectralIntegral E g ⟨ψ, h₂⟩ := by
  have h := ofReal_norm_spectralIntegral_sub_sq hE hf hg h₁ h₂
  have z : ∫⁻ y, ‖f y - g y‖ₑ ^ 2 ∂(diagonalMeasure E ψ) = 0 := by
    rw [lintegral_congr_ae (g := fun _ => 0) (hae.mono fun y hy => by simp [hy])]
    simp
  rw [z, ENNReal.ofReal_eq_zero] at h
  have h₀ : ‖spectralIntegral E f ⟨ψ, h₁⟩ - spectralIntegral E g ⟨ψ, h₂⟩‖ ^ 2 = 0 :=
    le_antisymm h (sq_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h₀))
theorem exists_boundedFn_ae_eq (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f)
    {c : ℝ} (hc : 0 ≤ c) (h : HoldsOffNull E fun y => ‖f y‖ ≤ c) :
    ∃ b : Space n → ℂ, IsBoundedMeasurableFn b ∧ (∀ y, ‖b y‖ ≤ c) ∧
      ∀ ψ : H, b =ᵐ[diagonalMeasure E ψ] f := by
  have hs : MeasurableSet {y | ‖f y‖ ≤ c} := measurableSet_le hf.norm measurable_const
  have hb : ∀ y, ‖({y | ‖f y‖ ≤ c} : Set (Space n)).indicator f y‖ ≤ c := fun y => by
    by_cases hy : ‖f y‖ ≤ c
    · rwa [Set.indicator_of_mem (show y ∈ {y | ‖f y‖ ≤ c} from hy)]
    · rw [Set.indicator_of_notMem (show y ∉ {y | ‖f y‖ ≤ c} from hy)]
      simpa using hc
  refine ⟨_, ⟨hf.indicator hs, c, hb⟩, hb, fun ψ => ?_⟩
  filter_upwards [ae_of_holdsOffNull hE h ψ] with y hy
  exact Set.indicator_of_mem (show y ∈ {y | ‖f y‖ ≤ c} from hy) f
theorem spectralIntegralIs_of_ae_eq (hE : Hypotheses E) {f b : Space n → ℂ}
    (hf : Measurable f) (hb : IsBoundedMeasurableFn b)
    (hae : ∀ ψ : H, b =ᵐ[diagonalMeasure E ψ] f) :
    SpectralIntegralIs E f (boundedCalculus E b) := by
  have hD : sqIntegrableDomain E f = univ := by
    rw [← domain_congr_ae hae, (hE.cutoffs.2 b hb).1]
  refine ⟨hD, fun ψ => ?_⟩
  have h₁ := mem_domain_of_boundedFn hE hb ψ.1
  rw [← spectralIntegral_of_boundedFn hE hb h₁]
  exact spectralIntegral_congr_ae hE hf hb.1 (hae ψ.1).symm ψ.2 h₁
theorem boundedCalculus_congr_ae (hE : Hypotheses E) {a b : Space n → ℂ}
    (ha : IsBoundedMeasurableFn a) (hb : IsBoundedMeasurableFn b) {ψ : H}
    (hae : a =ᵐ[diagonalMeasure E ψ] b) :
    boundedCalculus E a ψ = boundedCalculus E b ψ := by
  have h₁ := mem_domain_of_boundedFn hE ha ψ
  have h₂ := mem_domain_of_boundedFn hE hb ψ
  rw [← spectralIntegral_of_boundedFn hE ha h₁, ← spectralIntegral_of_boundedFn hE hb h₂]
  exact spectralIntegral_congr_ae hE ha.1 hb.1 hae h₁ h₂
theorem norm_boundedCalculus_le (hE : Hypotheses E) {b : Space n → ℂ}
    (hb : IsBoundedMeasurableFn b) {c : ℝ} (hc : 0 ≤ c) (hbc : ∀ y, ‖b y‖ ≤ c) (ψ : H) :
    ‖boundedCalculus E b ψ‖ ≤ c * ‖ψ‖ := by
  have h₁ : ENNReal.ofReal (‖boundedCalculus E b ψ‖ ^ 2) ≤ ENNReal.ofReal ((c * ‖ψ‖) ^ 2) := by
    rw [ofReal_norm_boundedCalculus_sq hE hb]
    calc ∫⁻ y, ‖b y‖ₑ ^ 2 ∂(diagonalMeasure E ψ)
        ≤ ∫⁻ y, ENNReal.ofReal c ^ 2 ∂(diagonalMeasure E ψ) :=
          lintegral_mono fun y => pow_le_pow_left₀ zero_le (enorm_le_ofReal_of_bound hbc y) 2
      _ = ENNReal.ofReal c ^ 2 * ENNReal.ofReal (‖ψ‖ ^ 2) := by
          rw [lintegral_const, hE.diag.2.2.1 ψ]
      _ = ENNReal.ofReal ((c * ‖ψ‖) ^ 2) := by
          rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hc]
  have h₂ := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h₁
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h₂
theorem holdsOffNull_mono {p q : Space n → Prop} (h : HoldsOffNull E p) (hpq : ∀ y, p y → q y) :
    HoldsOffNull E q := by
  obtain ⟨N, hN, hp⟩ := h
  exact ⟨N, hN, fun y hy => hpq y (hp y hy)⟩
theorem essBounded_exists_nonneg {f : Space n → ℂ} (h : EssBounded E f) :
    ∃ c : ℝ, 0 ≤ c ∧ HoldsOffNull E fun y => ‖f y‖ ≤ c := by
  obtain ⟨C, hC⟩ := h
  exact ⟨max C 0, le_max_right _ _, holdsOffNull_mono hC fun y hy => hy.trans (le_max_left _ _)⟩
theorem exists_linearIsometryEquiv_boundedCalculus (hE : Hypotheses E) {b : Space n → ℂ}
    (hb : IsBoundedMeasurableFn b) (h1 : ∀ ψ : H, ∀ᵐ y ∂(diagonalMeasure E ψ), ‖b y‖ = 1) :
    ∃ U : H ≃ₗᵢ[ℂ] H, (∀ ψ, U ψ = boundedCalculus E b ψ) ∧
      ∀ ψ, U.symm ψ = boundedCalculus E (fun y => conj (b y)) ψ := by
  have hcb := boundedFn_conj hb
  have hone : IsBoundedMeasurableFn fun _ : Space n => (1 : ℂ) := boundedFn_const 1
  have m₁ : ∀ ψ, boundedCalculus E b (boundedCalculus E (fun y => conj (b y)) ψ) = ψ :=
    fun ψ => by
      rw [boundedCalculus_comp_apply hE hb hcb, boundedCalculus_congr_ae hE (boundedFn_mul hb hcb)
        hone ((h1 ψ).mono fun y hy => ?_), boundedCalculus_one_apply hE]
      show b y * conj (b y) = 1
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hy]
      simp
  have m₂ : ∀ ψ, boundedCalculus E (fun y => conj (b y)) (boundedCalculus E b ψ) = ψ :=
    fun ψ => by
      rw [boundedCalculus_comp_apply hE hcb hb, boundedCalculus_congr_ae hE (boundedFn_mul hcb hb)
        hone ((h1 ψ).mono fun y hy => ?_), boundedCalculus_one_apply hE]
      show conj (b y) * b y = 1
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hy]
      simp
  have hn : ∀ ψ, ‖boundedCalculus E b ψ‖ = ‖ψ‖ := fun ψ => by
    have h₁ := ofReal_norm_boundedCalculus_sq hE hb ψ
    have h₂ : ∫⁻ y, ‖b y‖ₑ ^ 2 ∂(diagonalMeasure E ψ) = ENNReal.ofReal (‖ψ‖ ^ 2) := by
      rw [lintegral_congr_ae (g := fun _ => 1) ((h1 ψ).mono fun y hy => ?_)]
      · simpa using hE.diag.2.2.1 ψ
      · rw [enorm_sq_eq_ofReal, hy]
        simp
    rw [h₂] at h₁
    have h₃ := (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).mp h₁
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h₃
  refine ⟨⟨LinearEquiv.ofLinearMap (boundedCalculus E b : H →ₗ[ℂ] H)
    (boundedCalculus E (fun y => conj (b y)) : H →ₗ[ℂ] H)
    (LinearMap.ext m₁) (LinearMap.ext m₂), hn⟩, fun ψ => rfl, fun ψ => rfl⟩
theorem essentialProperties (hE : Hypotheses E) {f g : Space n → ℂ} (hf : Measurable f)
    (hg : Measurable g) : EssentialProperties E hf hg where
  eq_of_null := fun hN => by
    have hae : ∀ ψ : H, f =ᵐ[diagonalMeasure E ψ] g := fun ψ => by
      have := ae_of_holdsOffNull hE (p := fun y => f y = g y)
        ⟨disagreementSet hf hg, hN, fun y hy => by
          by_contra h
          exact hy h⟩ ψ
      exact this
    exact spectralOp_ext hE hf hg (domain_congr_ae hae) fun ψ h₁ h₂ =>
      spectralIntegral_congr_ae hE hf hg (hae ψ) h₁ h₂
  bounded := fun c hc h => by
    obtain ⟨b, hb, hbc, hae⟩ := exists_boundedFn_ae_eq hE hf hc h
    exact ⟨boundedCalculus E b, spectralIntegralIs_of_ae_eq hE hf hb hae,
      norm_boundedCalculus_le hE hb hc hbc⟩
  mul := fun h₁ h₂ => by
    obtain ⟨c, hc, hh⟩ := essBounded_exists_nonneg h₁
    obtain ⟨c', hc', hh'⟩ := essBounded_exists_nonneg h₂
    obtain ⟨b, hb, -, hae⟩ := exists_boundedFn_ae_eq hE hf hc hh
    obtain ⟨b', hb', -, hae'⟩ := exists_boundedFn_ae_eq hE hg hc' hh'
    have hm : Measurable fun y => f y * g y := hf.mul hg
    have e₁ : boundedCalculus E (fun y => b y * b' y) =
        boundedCalculus E b * boundedCalculus E b' :=
      (hE.calc_.1 b b' 0 hb hb').2
    have e₂ : boundedCalculus E (fun y => b' y * b y) =
        boundedCalculus E b' * boundedCalculus E b :=
      (hE.calc_.1 b' b 0 hb' hb).2
    refine ⟨boundedCalculus E b, boundedCalculus E b',
      spectralIntegralIs_of_ae_eq hE hf hb hae,
      spectralIntegralIs_of_ae_eq hE hg hb' hae', ?_, ?_⟩
    · rw [← e₁]
      refine spectralIntegralIs_of_ae_eq hE hm (boundedFn_mul hb hb') fun ψ => ?_
      filter_upwards [hae ψ, hae' ψ] with y hy hy'
      rw [hy, hy']
    · rw [← e₂]
      refine spectralIntegralIs_of_ae_eq hE hm (boundedFn_mul hb' hb) fun ψ => ?_
      filter_upwards [hae ψ, hae' ψ] with y hy hy'
      rw [hy, hy', mul_comm]
  nonneg := fun h ψ => by
    rw [show spectralIntegral E f ψ = spectralIntegral E f ⟨ψ.1, ψ.2⟩ from rfl,
      inner_spectralIntegral hE hf ψ.2]
    have hae := ae_of_holdsOffNull hE h ψ.1
    have e : ∫ y, f y ∂(diagonalMeasure E ψ.1) =
        ((∫ y, (f y).re ∂(diagonalMeasure E ψ.1) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (hae.mono fun y hy => ?_)
      exact Complex.ext (by simp) (by simpa using (Complex.le_def.mp hy).2.symm)
    rw [e]
    refine Complex.zero_le_real.mpr (integral_nonneg_of_ae (hae.mono fun y hy => ?_))
    exact (Complex.le_def.mp hy).1
  unitary := fun h => by
    obtain ⟨b, hb, -, hae⟩ := exists_boundedFn_ae_eq hE hf zero_le_one
      (holdsOffNull_mono h fun y hy => hy.le)
    have h1 : ∀ ψ : H, ∀ᵐ y ∂(diagonalMeasure E ψ), ‖b y‖ = 1 := fun ψ => by
      filter_upwards [hae ψ, ae_of_holdsOffNull hE h ψ] with y hy hy'
      rw [hy, hy']
    obtain ⟨U, hU, hU'⟩ := exists_linearIsometryEquiv_boundedCalculus hE hb h1
    have hcae : ∀ ψ : H, (fun y => conj (b y)) =ᵐ[diagonalMeasure E ψ] fun y => conj (f y) :=
      fun ψ => (hae ψ).mono fun y hy => by simp only [hy]
    refine ⟨U, ?_, ?_⟩
    · rw [show (U : H → H) = boundedCalculus E b from funext hU]
      exact spectralIntegralIs_of_ae_eq hE hf hb hae
    · rw [show (U.symm : H → H) = boundedCalculus E (fun y => conj (b y)) from funext hU']
      exact spectralIntegralIs_of_ae_eq hE (measurable_conj_comp hf) (boundedFn_conj hb) hcae
theorem proj_add_proj_compl (hE : Hypotheses E) (Δ : BorelSubset n) (ψ : H) :
    E Δ ψ + E Δᶜ ψ = ψ := by
  have h := (hE.calc_.1 _ _ 1 (boundedFn_indicator Δ) (boundedFn_indicator Δᶜ)).1
  have e : (fun y => Δ.1.indicator (fun _ => (1 : ℂ)) y +
      1 * (Δᶜ : BorelSubset n).1.indicator (fun _ => (1 : ℂ)) y) = fun _ => 1 := by
    funext y
    by_cases hy : y ∈ Δ.1
    · simp [hy]
    · simp [hy]
  rw [e, boundedCalculus_indicator hE, boundedCalculus_indicator hE] at h
  have h₂ := congrArg (fun B : H →L[ℂ] H => B ψ) h
  simp only [add_apply, one_smul] at h₂
  rw [← h₂]
  exact boundedCalculus_one_apply hE ψ
theorem kernel_eq_range_zeroLocus (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f) :
    KernelIsZeroLocusRange E hf := by
  ext ψ
  constructor
  · rintro ⟨h, hv⟩
    have hψ := (mem_spectralOp_domain_iff hE hf).mp h
    rw [spectralOp_apply hE hf ⟨ψ, h⟩ hψ] at hv
    have hn := ofReal_norm_spectralIntegral_sq hE hf hψ
    rw [hv] at hn
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      ENNReal.ofReal_zero] at hn
    have hz := (lintegral_eq_zero_iff (hf.enorm.pow_const 2)).mp hn.symm
    have hc : diagonalMeasure E ψ (zeroLocus hf)ᶜ.1 = 0 := by
      refine measure_mono_null (fun y hy => ?_) (ae_iff.mp hz)
      intro h0
      apply hy
      exact (by simpa using h0 : f y = 0)
    rw [hE.diagonalMeasure_apply, ENNReal.ofReal_eq_zero] at hc
    have hc₀ : E (zeroLocus hf)ᶜ ψ = 0 :=
      norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm hc (sq_nonneg _)))
    have := proj_add_proj_compl hE (zeroLocus hf) ψ
    rw [hc₀, add_zero] at this
    exact ⟨ψ, this⟩
  · rintro ⟨χ, rfl⟩
    have hz : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(diagonalMeasure E (E (zeroLocus hf) χ)) = 0 := by
      rw [diagonalMeasure_proj hE, ← lintegral_indicator (zeroLocus hf).2]
      refine (lintegral_congr fun y => ?_).trans lintegral_zero
      by_cases hy : y ∈ (zeroLocus hf).1
      · have : f y = 0 := hy
        simp [hy, this]
      · simp [hy]
    have hm : E (zeroLocus hf) χ ∈ sqIntegrableDomain E f := by
      show ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(diagonalMeasure E (E (zeroLocus hf) χ)) < ∞
      rw [hz]
      simp
    have hd := (mem_spectralOp_domain_iff hE hf).mpr hm
    refine ⟨hd, ?_⟩
    rw [spectralOp_apply hE hf ⟨_, hd⟩ hm]
    have hn := ofReal_norm_spectralIntegral_sq hE hf hm
    rw [hz, ENNReal.ofReal_eq_zero] at hn
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm hn (sq_nonneg _)))
theorem boundedConvergence (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f) :
    BoundedConvergence E f := by
  intro fs c hfs hc hh ψ
  have hlim : HoldsOffNull E fun y => ‖f y‖ ≤ c := holdsOffNull_mono hh fun y hy =>
    le_of_tendsto hy.2.norm (Eventually.of_forall hy.1)
  have hj : ∀ j, HoldsOffNull E fun y => ‖fs j y‖ ≤ c := fun j =>
    holdsOffNull_mono hh fun y hy => hy.1 j
  have mem_of_bound : ∀ {u : Space n → ℂ}, Measurable u →
      (HoldsOffNull E fun y => ‖u y‖ ≤ c) → ψ ∈ sqIntegrableDomain E u := fun hu h => by
    obtain ⟨b, hb, -, hae⟩ := exists_boundedFn_ae_eq hE hu hc h
    rw [← domain_congr_ae hae]
    exact mem_domain_of_boundedFn hE hb ψ
  have h₀ := mem_of_bound hf hlim
  have hs := fun j => mem_of_bound (hfs j) (hj j)
  refine ⟨h₀, hs, ?_⟩
  have := hE.isFiniteMeasure ψ
  have hl := tendsto_lintegral_of_dominated_convergence (μ := diagonalMeasure E ψ)
    (F := fun (j : ℕ) y => ‖fs j y - f y‖ₑ ^ 2) (f := fun _ => 0)
    (fun _ => ENNReal.ofReal ((2 * c) ^ 2))
    (fun j => ((hfs j).sub hf).enorm.pow_const 2)
    (fun j => by
      filter_upwards [ae_of_holdsOffNull hE hh ψ, ae_of_holdsOffNull hE hlim ψ] with y hy hy'
      rw [enorm_sq_eq_ofReal]
      refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
      calc ‖fs j y - f y‖ ≤ ‖fs j y‖ + ‖f y‖ := norm_sub_le _ _
        _ ≤ 2 * c := by linarith [hy.1 j])
    (by
      rw [lintegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (by
      filter_upwards [ae_of_holdsOffNull hE hh ψ] with y hy
      have h₁ : Tendsto (fun j => fs j y - f y) atTop (𝓝 0) := by
        simpa using hy.2.sub_const (f y)
      have h₂ : Tendsto (fun j => ‖fs j y - f y‖ₑ ^ 2) atTop (𝓝 (‖(0 : ℂ)‖ₑ ^ 2)) :=
        ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp h₁)
      simpa using h₂)
  simp only [lintegral_zero] at hl
  have hz : Tendsto (fun j => spectralIntegral E (fs j) ⟨ψ, hs j⟩ -
      spectralIntegral E f ⟨ψ, h₀⟩) atTop (𝓝 0) :=
    tendsto_zero_of_tendsto_ofReal_norm_sq
      (hl.congr fun j => (ofReal_norm_spectralIntegral_sub_sq hE (hfs j) hf (hs j) h₀).symm)
  simpa using hz.add_const (spectralIntegral E f ⟨ψ, h₀⟩)
theorem commutantProperty (hE : Hypotheses E) {f : Space n → ℂ} (hf : Measurable f) :
    CommutantProperty E f := by
  intro B hB h
  obtain ⟨c, hc, hh⟩ := essBounded_exists_nonneg h
  obtain ⟨b, hb, -, hae⟩ := exists_boundedFn_ae_eq hE hf hc hh
  refine ⟨boundedCalculus E b, spectralIntegralIs_of_ae_eq hE hf hb hae, ?_⟩
  have hmix := (hE.unique b hb).1
  refine ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => ?_
  show ⟪φ, B (boundedCalculus E b ψ)⟫_ℂ = ⟪φ, boundedCalculus E b (B ψ)⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left, hmix, hmix]
  congr 1
  funext Δ
  show ⟪(ContinuousLinearMap.adjoint B) φ, E Δ ψ⟫_ℂ = ⟪φ, E Δ (B ψ)⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_left]
  have := congrArg (fun T : H →L[ℂ] H => T ψ) (hB Δ)
  simp only [mul_apply_eq_comp] at this
  rw [this]
end NullSets
section Images
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n n' : ℕ}
  {E : BorelSubset n → H →L[ℂ] H}
theorem spectralOp_ext_of_two {E' : BorelSubset n' → H →L[ℂ] H} (hE : Hypotheses E)
    (hE' : Hypotheses E') {f : Space n → ℂ} {g : Space n' → ℂ} (hf : Measurable f)
    (hg : Measurable g) (hD : sqIntegrableDomain E f = sqIntegrableDomain E' g)
    (hv : ∀ (ψ : H) (h₁ : ψ ∈ sqIntegrableDomain E f)
      (h₂ : ψ ∈ sqIntegrableDomain E' g),
      spectralIntegral E f ⟨ψ, h₁⟩ = spectralIntegral E' g ⟨ψ, h₂⟩) :
    spectralOp E f = spectralOp E' g := by
  refine LinearPMap.ext (SetLike.coe_injective ?_) ?_
  · rw [(isSpectralIntegralOp_spectralOp hE hf).1, (isSpectralIntegralOp_spectralOp hE' hg).1, hD]
  · intro x hx hx'
    have h₁ := (mem_spectralOp_domain_iff hE hf).mp hx
    have h₂ := (mem_spectralOp_domain_iff hE' hg).mp hx'
    rw [spectralOp_apply hE hf ⟨x, hx⟩ h₁, spectralOp_apply hE' hg ⟨x, hx'⟩ h₂]
    exact hv x h₁ h₂
theorem isPVM_pushforward (hE : Hypotheses E) (κ : Space n → Space n')
    (hκ : Measurable κ) : IsPVM (pushforward E κ hκ) where
  isOrthoProjection := fun Δ => hE.pvm.isOrthoProjection _
  map_top := hE.pvm.map_top
  map_inter := fun Δ Δ' => hE.pvm.map_inter ⟨κ ⁻¹' Δ.1, hκ Δ.2⟩ ⟨κ ⁻¹' Δ'.1, hκ Δ'.2⟩
  isPositiveMeasure := fun ψ => by
    have := hE.isFiniteMeasure ψ
    refine ⟨(diagonalMeasure E ψ).map κ, fun Δ => ⟨measure_ne_top _ _, ?_⟩⟩
    have h := (toMeasure_spec (hE.pvm.isPositiveMeasure ψ) ⟨κ ⁻¹' Δ.1, hκ Δ.2⟩).2
    rw [Measure.real, Measure.map_apply hκ Δ.2]
    exact h
theorem diagonalMeasure_pushforward (hE : Hypotheses E) {κ : Space n → Space n'}
    {hκ : Measurable κ} (hE' : Hypotheses (pushforward E κ hκ)) (ψ : H) :
    diagonalMeasure (pushforward E κ hκ) ψ = (diagonalMeasure E ψ).map κ := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hκ hs, hE'.diagonalMeasure_apply ψ ⟨s, hs⟩,
    show κ ⁻¹' s = (⟨κ ⁻¹' s, hκ hs⟩ : BorelSubset n).1 from rfl, hE.diagonalMeasure_apply]
  rfl
theorem cutoff_comp (h : Space n' → ℂ) (κ : Space n → Space n') (k : ℕ) :
    cutoff (h ∘ κ) k = cutoff h k ∘ κ := by
  funext y
  show cutoff (h ∘ κ) k y = cutoff h k (κ y)
  by_cases hy : ‖h (κ y)‖ ≤ k
  · rw [cutoff_apply_of_le (f := h ∘ κ) hy, cutoff_apply_of_le hy]
    rfl
  · rw [cutoff_apply_of_not_le (f := h ∘ κ) hy, cutoff_apply_of_not_le hy]
theorem boundedFn_comp {h : Space n' → ℂ} (hh : IsBoundedMeasurableFn h)
    {κ : Space n → Space n'} (hκ : Measurable κ) : IsBoundedMeasurableFn (h ∘ κ) := by
  obtain ⟨hm, C, hC⟩ := hh
  exact ⟨hm.comp hκ, C, fun y => hC _⟩
theorem boundedCalculus_pushforward (hE : Hypotheses E) {κ : Space n → Space n'}
    {hκ : Measurable κ} (hE' : Hypotheses (pushforward E κ hκ)) {h : Space n' → ℂ}
    (hh : IsBoundedMeasurableFn h) :
    boundedCalculus (pushforward E κ hκ) h = boundedCalculus E (h ∘ κ) := by
  refine ((hE'.unique h hh).2.2.2 _ fun ψ => ?_).symm
  rw [(hE.unique _ (boundedFn_comp hh hκ)).2.2.1 ψ, diagonalMeasure_pushforward hE hE' ψ,
    integral_map hκ.aemeasurable hh.1.aestronglyMeasurable]
  rfl
theorem spectralOp_pushforward (hE : Hypotheses E) {κ : Space n → Space n'}
    {hκ : Measurable κ} (hE' : Hypotheses (pushforward E κ hκ)) {h : Space n' → ℂ}
    (hh : Measurable h) :
    spectralOp (pushforward E κ hκ) h = spectralOp E (h ∘ κ) := by
  refine spectralOp_ext_of_two hE' hE hh (hh.comp hκ) ?_ fun ψ h₁ h₂ => ?_
  · ext ψ
    show ∫⁻ y, ‖h y‖ₑ ^ 2 ∂(diagonalMeasure (pushforward E κ hκ) ψ) < ∞ ↔
      ∫⁻ y, ‖h (κ y)‖ₑ ^ 2 ∂(diagonalMeasure E ψ) < ∞
    rw [diagonalMeasure_pushforward hE hE' ψ, lintegral_map (hh.enorm.pow_const 2) hκ]
  · refine tendsto_nhds_unique (tendsto_boundedCalculus_cutoff hE' hh h₁)
      ((tendsto_boundedCalculus_cutoff hE (hh.comp hκ) h₂).congr fun k => ?_)
    rw [boundedCalculus_pushforward hE hE' (isBoundedMeasurableFn_cutoff hh k), cutoff_comp]
theorem unitaryConj_apply (U : H ≃ₗᵢ[ℂ] H) (E : BorelSubset n → H →L[ℂ] H) (Δ : BorelSubset n)
    (ψ : H) : unitaryConj U E Δ ψ = U (E Δ (U.symm ψ)) := rfl
theorem inner_apply_linearIsometryEquiv (U : H ≃ₗᵢ[ℂ] H) (a b : H) :
    ⟪a, U b⟫_ℂ = ⟪U.symm a, b⟫_ℂ := by
  rw [← U.inner_map_map (U.symm a) b]
  simp
theorem inner_linearIsometryEquiv_apply (U : H ≃ₗᵢ[ℂ] H) (a b : H) :
    ⟪U a, b⟫_ℂ = ⟪a, U.symm b⟫_ℂ := by
  rw [← U.inner_map_map a (U.symm b)]
  simp
theorem isPVM_unitaryConj (hE : Hypotheses E) (U : H ≃ₗᵢ[ℂ] H) :
    IsPVM (unitaryConj U E) where
  isOrthoProjection := fun Δ => by
    have hP := hE.pvm.isOrthoProjection Δ
    refine ⟨ContinuousLinearMap.ext fun ψ => ?_, fun φ ψ => ?_⟩
    · have := congrArg (fun T : H →L[ℂ] H => T (U.symm ψ)) hP.1
      simp only [mul_apply_eq_comp] at this
      show U (E Δ (U.symm (U (E Δ (U.symm ψ))))) = U (E Δ (U.symm ψ))
      rw [U.symm_apply_apply, this]
    · rw [unitaryConj_apply, unitaryConj_apply, inner_apply_linearIsometryEquiv, hP.2,
        inner_linearIsometryEquiv_apply]
  map_top := by
    refine ContinuousLinearMap.ext fun ψ => ?_
    rw [unitaryConj_apply, hE.pvm.map_top]
    simp
  map_inter := fun Δ Δ' => by
    refine ContinuousLinearMap.ext fun ψ => ?_
    show U (E (Δ ∩ Δ') (U.symm ψ)) = U (E Δ (U.symm (U (E Δ' (U.symm ψ)))))
    rw [U.symm_apply_apply, hE.pvm.map_inter]
    rfl
  isPositiveMeasure := fun ψ => by
    refine ⟨diagonalMeasure E (U.symm ψ), fun Δ => ?_⟩
    have := hE.isFiniteMeasure (U.symm ψ)
    refine ⟨measure_ne_top _ _, ?_⟩
    have h := (toMeasure_spec (hE.pvm.isPositiveMeasure (U.symm ψ)) Δ).2
    show ⟪ψ, U (E Δ (U.symm ψ))⟫_ℂ = _
    rw [inner_apply_linearIsometryEquiv]
    exact h
theorem diagonalMeasure_unitaryConj (hE : Hypotheses E) {U : H ≃ₗᵢ[ℂ] H}
    (hE' : Hypotheses (unitaryConj U E)) (ψ : H) :
    diagonalMeasure (unitaryConj U E) ψ = diagonalMeasure E (U.symm ψ) := by
  refine Measure.ext fun s hs => ?_
  rw [hE'.diagonalMeasure_apply ψ ⟨s, hs⟩, unitaryConj_apply, U.norm_map]
  exact (hE.diagonalMeasure_apply _ ⟨s, hs⟩).symm
theorem boundedCalculus_unitaryConj_apply (hE : Hypotheses E) {U : H ≃ₗᵢ[ℂ] H}
    (hE' : Hypotheses (unitaryConj U E)) {f : Space n → ℂ} (hf : IsBoundedMeasurableFn f)
    (ψ : H) : boundedCalculus (unitaryConj U E) f ψ = U (boundedCalculus E f (U.symm ψ)) := by
  have h : boundedCalculus (unitaryConj U E) f = (U.toContinuousLinearEquiv : H →L[ℂ] H) *
      boundedCalculus E f * (U.symm.toContinuousLinearEquiv : H →L[ℂ] H) := by
    refine ((hE'.unique f hf).2.2.2 _ fun χ => ?_).symm
    show ⟪χ, U (boundedCalculus E f (U.symm χ))⟫_ℂ = _
    rw [inner_apply_linearIsometryEquiv, (hE.unique f hf).2.2.1 (U.symm χ),
      diagonalMeasure_unitaryConj hE hE']
  rw [h]
  rfl
theorem mem_domain_unitaryConj_iff (hE : Hypotheses E) {U : H ≃ₗᵢ[ℂ] H}
    (hE' : Hypotheses (unitaryConj U E)) {f : Space n → ℂ} {ψ : H} :
    ψ ∈ sqIntegrableDomain (unitaryConj U E) f ↔ U.symm ψ ∈ sqIntegrableDomain E f := by
  show ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(diagonalMeasure (unitaryConj U E) ψ) < ∞ ↔
    ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(diagonalMeasure E (U.symm ψ)) < ∞
  rw [diagonalMeasure_unitaryConj hE hE']
theorem spectralOp_unitaryConj (hE : Hypotheses E) {U : H ≃ₗᵢ[ℂ] H}
    (hE' : Hypotheses (unitaryConj U E)) {f : Space n → ℂ} (hf : Measurable f) :
    spectralOp (unitaryConj U E) f =
      FormsOperators.unitaryConjugate U (spectralOp E f) := by
  refine LinearPMap.ext ?_ ?_
  · ext ψ
    rw [mem_spectralOp_domain_iff hE' hf, mem_domain_unitaryConj_iff hE hE']
    show U.symm ψ ∈ sqIntegrableDomain E f ↔
      ψ ∈ (spectralOp E f).domain.map U.toLinearEquiv.toLinearMap
    rw [Submodule.mem_map]
    constructor
    · intro h
      exact ⟨U.symm ψ, (mem_spectralOp_domain_iff hE hf).mpr h, by simp⟩
    · rintro ⟨χ, hχ, rfl⟩
      simpa using (mem_spectralOp_domain_iff hE hf).mp hχ
  · intro x hx hx'
    obtain ⟨χ, hχ, rfl⟩ := Submodule.mem_map.mp hx'
    refine Eq.trans ?_
      (FormsOperators.unitaryConjugate_apply U (spectralOp E f) ⟨χ, hχ⟩).symm
    have h := (mem_spectralOp_domain_iff hE hf).mp hχ
    have h' := (mem_spectralOp_domain_iff hE' hf).mp hx
    rw [spectralOp_apply hE hf ⟨χ, hχ⟩ h, spectralOp_apply hE' hf ⟨_, hx⟩ h']
    refine tendsto_nhds_unique (tendsto_boundedCalculus_cutoff hE' hf h')
      (((U.continuous.tendsto _).comp (tendsto_boundedCalculus_cutoff hE hf h)).congr fun k => ?_)
    rw [boundedCalculus_unitaryConj_apply hE hE' (isBoundedMeasurableFn_cutoff hf k)]
    simp
theorem exists_isMaximalOpenNull (hE : Hypotheses E) : ∃ U, IsMaximalOpenNull E U := by
  classical
  obtain ⟨T, hTc, hTS, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable
    {U | IsOpenNull E U} fun s hs => hs.choose
  have hopen : IsOpen (⋃₀ {U | IsOpenNull E U}) := isOpen_sUnion fun s hs => hs.choose
  let φ : Set (Space n) → BorelSubset n := fun s => if h : MeasurableSet s then ⟨s, h⟩ else ⊥
  have hφ : ∀ (s : Set (Space n)) (h : MeasurableSet s), φ s = ⟨s, h⟩ := fun s h => dif_pos h
  have hnull : IsNull E ⟨⋃₀ {U | IsOpenNull E U}, hopen.measurableSet⟩ := by
    refine hE.null.2.2 (φ '' T) _ (hTc.image φ) ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      obtain ⟨ho, hn⟩ := hTS hs
      rw [hφ s ho.measurableSet]
      exact hn
    · show ⋃₀ {U | IsOpenNull E U} = _
      rw [← hTU, sUnion_eq_biUnion, biUnion_image]
      refine iUnion₂_congr fun s hs => ?_
      obtain ⟨ho, -⟩ := hTS hs
      rw [hφ s ho.measurableSet]
  exact ⟨_, ⟨hopen, hnull⟩, fun U' hU' => subset_sUnion_of_mem hU'⟩
theorem proj_bot (hE : Hypotheses E) : E ⊥ = 0 :=
  (hE.null.1 ⊥).mpr fun ψ => measure_empty
theorem proj_union_apply (hE : Hypotheses E) {A B C : BorelSubset n} (hd : Disjoint A.1 B.1)
    (hC : C.1 = A.1 ∪ B.1) (ψ : H) : E C ψ = E A ψ + E B ψ := by
  have h := (hE.calc_.1 _ _ 1 (boundedFn_indicator A) (boundedFn_indicator B)).1
  have e : (fun y => A.1.indicator (fun _ => (1 : ℂ)) y +
      1 * B.1.indicator (fun _ => (1 : ℂ)) y) = C.1.indicator fun _ => (1 : ℂ) := by
    funext y
    rw [hC]
    by_cases hA : y ∈ A.1
    · have hB : y ∉ B.1 := fun h => Set.disjoint_left.mp hd hA h
      simp [hA, hB]
    · by_cases hB : y ∈ B.1
      · simp [hA, hB]
      · simp [hA, hB]
  rw [e, boundedCalculus_indicator hE, boundedCalculus_indicator hE,
    boundedCalculus_indicator hE] at h
  rw [h]
  simp
theorem enorm_indicator_sub_sq_le_one (A B : Set (Space n)) (y : Space n) :
    ‖A.indicator (fun _ => (1 : ℂ)) y - B.indicator (fun _ => (1 : ℂ)) y‖ₑ ^ 2 ≤ 1 := by
  by_cases hA : y ∈ A
  · by_cases hB : y ∈ B
    · simp [hA, hB]
    · simp [hA, hB]
  · by_cases hB : y ∈ B
    · simp [hA, hB]
    · simp [hA, hB]
theorem tendsto_sum_proj (hE : Hypotheses E) (Δ : ℕ → BorelSubset n)
    (hd : Pairwise fun j k => Disjoint (Δ j).1 (Δ k).1) (U : BorelSubset n)
    (hU : U.1 = ⋃ j, (Δ j).1) (ψ : H) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, E (Δ j) ψ) atTop (𝓝 (E U ψ)) := by
  have hm : ∀ N : ℕ, MeasurableSet (⋃ j ∈ Finset.range N, (Δ j).1) := fun N =>
    Finset.measurableSet_biUnion _ fun j _ => (Δ j).2
  let P : ℕ → BorelSubset n := fun N => ⟨⋃ j ∈ Finset.range N, (Δ j).1, hm N⟩
  have hsum : ∀ N, ∑ j ∈ Finset.range N, E (Δ j) ψ = E (P N) ψ := by
    intro N
    induction N with
    | zero =>
      have e : P 0 = ⊥ := Subtype.ext (by simp [P])
      rw [e, proj_bot hE]
      simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      refine (proj_union_apply hE ?_ ?_ ψ).symm
      · refine Set.disjoint_left.mpr fun y hy hy' => ?_
        obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hy
        exact Set.disjoint_left.mp (hd (Finset.mem_range.mp hj).ne) hyj hy'
      · show ⋃ j ∈ Finset.range (N + 1), (Δ j).1 = (⋃ j ∈ Finset.range N, (Δ j).1) ∪ (Δ N).1
        rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
  have hbU := boundedFn_indicator U
  have hmem := mem_domain_of_boundedFn hE hbU ψ
  have hl : Tendsto (fun N : ℕ => ∫⁻ y, ‖(P N).1.indicator (fun _ => (1 : ℂ)) y -
      U.1.indicator (fun _ => (1 : ℂ)) y‖ₑ ^ 2 ∂(diagonalMeasure E ψ)) atTop (𝓝 0) := by
    have := hE.isFiniteMeasure ψ
    have := tendsto_lintegral_of_dominated_convergence (μ := diagonalMeasure E ψ)
      (F := fun (N : ℕ) y => ‖(P N).1.indicator (fun _ => (1 : ℂ)) y -
        U.1.indicator (fun _ => (1 : ℂ)) y‖ₑ ^ 2) (f := fun _ => 0) (fun _ => 1)
      (fun N => (((boundedFn_indicator (P N)).1.sub hbU.1).enorm.pow_const 2))
      (fun N => ae_of_all _ fun y => enorm_indicator_sub_sq_le_one _ _ y)
      (by simp [measure_ne_top])
      (ae_of_all _ fun y => tendsto_const_nhds.congr' (by
        by_cases hy : y ∈ U.1
        · obtain ⟨j, hj⟩ := mem_iUnion.mp (hU ▸ hy)
          filter_upwards [eventually_gt_atTop j] with N hN
          have hy' : y ∈ (P N).1 := mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hN, hj⟩
          simp [hy, hy']
        · refine Eventually.of_forall fun N => ?_
          have hy' : y ∉ (P N).1 := fun h => by
            obtain ⟨j, -, hj⟩ := mem_iUnion₂.mp h
            exact hy (hU ▸ mem_iUnion.mpr ⟨j, hj⟩)
          simp [hy, hy']))
    simpa using this
  have t := tendsto_boundedCalculus_of_meanSquare hE hbU.1 hmem
    (fun N => boundedFn_indicator (P N)) hl
  rw [spectralIntegral_of_boundedFn hE hbU hmem, boundedCalculus_indicator hE] at t
  exact t.congr fun N => by rw [boundedCalculus_indicator hE, hsum]
end Images
section Coordinates
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
  [NeZero n] {E : BorelSubset n → H →L[ℂ] H}
def toSpectralMeasure (hE : Hypotheses E) : SpectralTheory.SpectralMeasure n H where
  toFun := fun Δ => (E (ofCoordBorel Δ) : H →ₗ[ℂ] H)
  isOrthProj := fun Δ => by
    have hP := hE.pvm.isOrthoProjection (ofCoordBorel Δ)
    exact ⟨LinearMap.ext fun ψ => congrArg (fun T : H →L[ℂ] H => T ψ) hP.1, fun φ ψ => hP.2 φ ψ⟩
  map_univ := by
    have e : ofCoordBorel ⟨univ, MeasurableSet.univ⟩ = (⊤ : BorelSubset n) := Subtype.ext rfl
    rw [e, hE.pvm.map_top]
    rfl
  map_inter := fun Δ Δ' => by
    have e : ofCoordBorel ⟨Δ.1 ∩ Δ'.1, Δ.2.inter Δ'.2⟩ =
        ofCoordBorel Δ ∩ ofCoordBorel Δ' := Subtype.ext rfl
    rw [e, hE.pvm.map_inter]
    rfl
  tendsto_sum := fun Δ hd ψ =>
    tendsto_sum_proj hE (fun j => ofCoordBorel (Δ j))
      (fun j k hjk => (hd hjk).preimage _) _ preimage_iUnion ψ
theorem measurable_ofLp_space : Measurable (WithLp.ofLp : Space n → Fin n → ℝ) :=
  (PiLp.continuous_ofLp 2 _).measurable
theorem diagMeasure_toSpectralMeasure (hE : Hypotheses E) (ψ : H) :
    (toSpectralMeasure hE).diagMeasure ψ = (diagonalMeasure E ψ).map WithLp.ofLp := by
  refine Measure.ext fun s hs => ?_
  rw [(toSpectralMeasure hE).diagMeasure_apply ψ ⟨s, hs⟩,
    Measure.map_apply measurable_ofLp_space hs]
  exact (hE.diagonalMeasure_apply ψ (ofCoordBorel ⟨s, hs⟩)).symm
theorem linearMap_eq_zero_of_inner_self_eq_zero (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (C : D →ₗ[ℂ] H) (h : ∀ ψ : D, ⟪(ψ : H), C ψ⟫_ℂ = 0) (ψ : D) : C ψ = 0 := by
  have hpol : ∀ φ : D, ⟪(φ : H), C ψ⟫_ℂ = 0 := fun φ => by
    have h₁ := h (φ + ψ)
    have h₂ := h (φ + Complex.I • ψ)
    rw [map_add, Submodule.coe_add, inner_add_left, inner_add_right, inner_add_right, h φ, h ψ]
      at h₁
    rw [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul, inner_add_left, inner_add_right,
      inner_add_right, inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right,
      h φ, h ψ] at h₂
    simp only [Complex.conj_I] at h₂
    linear_combination (1 / 2) * h₁ - (Complex.I / 2) * h₂ +
      ((⟪(φ : H), C ψ⟫_ℂ - ⟪(ψ : H), C φ⟫_ℂ) / 2) * Complex.I_sq
  have he : (fun x : H => ⟪x, C ψ⟫_ℂ) = fun _ => 0 :=
    Continuous.ext_on hD (by fun_prop) continuous_const fun x hx => hpol ⟨x, hx⟩
  exact inner_self_eq_zero.mp (congrFun he (C ψ))
theorem coordinateCompatibility (hE : Hypotheses E)
    (hJ : SpectralTheory.RealBorelCalculus) {g : Space n → ℂ}
    (hg : Measurable g) : CoordinateCompatibility E hg := by
  refine ⟨exists_isMaximalOpenNull hE, toSpectralMeasure hE, fun Δ => rfl, fun Δ => ?_,
    fun hre => ?_⟩
  · constructor
    · intro h
      show (E (ofCoordBorel Δ) : H →ₗ[ℂ] H) = 0
      rw [show E (ofCoordBorel Δ) = 0 from h]
      rfl
    · intro h
      exact ContinuousLinearMap.ext fun ψ => LinearMap.congr_fun h ψ
  · have hg' := measurable_realPartOnCoords hg
    obtain ⟨hlin, hinner⟩ := hJ H n (toSpectralMeasure hE) (realPartOnCoords g) hg'
    have hgre : ∀ y, g y = ((g y).re : ℂ) := fun y => Complex.ext rfl (by simpa using hre y)
    have hcomp : ∀ y : Space n, realPartOnCoords g (WithLp.ofLp y) = (g y).re :=
      fun y => by simp [realPartOnCoords]
    have hDom : ((spectralOp E g).domain : Set H) =
        (toSpectralMeasure hE).realDomain (realPartOnCoords g) := by
      rw [(isSpectralIntegralOp_spectralOp hE hg).1]
      ext ψ
      show ∫⁻ y, ‖g y‖ₑ ^ 2 ∂(diagonalMeasure E ψ) < ∞ ↔
        ∫⁻ y, ENNReal.ofReal (realPartOnCoords g y ^ 2)
          ∂((toSpectralMeasure hE).diagMeasure ψ) < ⊤
      have hmeas : Measurable fun y => ENNReal.ofReal (realPartOnCoords g y ^ 2) :=
        ENNReal.measurable_ofReal.comp (hg'.pow_const 2)
      rw [diagMeasure_toSpectralMeasure hE, lintegral_map hmeas measurable_ofLp_space]
      have e : ∀ y, ENNReal.ofReal (realPartOnCoords g (WithLp.ofLp y) ^ 2) =
          ‖g y‖ₑ ^ 2 := fun y => by
        rw [hcomp, enorm_sq_eq_ofReal]
        conv_rhs => rw [hgre y]
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      simp only [e]
    have mem : ∀ ψ : (spectralOp E g).domain,
        ψ.1 ∈ (toSpectralMeasure hE).realDomain (realPartOnCoords g) := fun ψ => by
      rw [← hDom]
      exact ψ.2
    let V : (spectralOp E g).domain →ₗ[ℂ] H :=
      { toFun := fun ψ => (toSpectralMeasure hE).realIntegralApply _ hg' ψ.1
        map_add' := fun φ ψ => (hlin φ.1 (mem φ) ψ.1 (mem ψ) 0).1
        map_smul' := fun c ψ => (hlin ψ.1 (mem ψ) ψ.1 (mem ψ) c).2 }
    have hdense : Dense ((spectralOp E g).domain : Set H) := by
      rw [(isSpectralIntegralOp_spectralOp hE hg).1]
      exact (FormsOperators.isDenseSet_iff_dense _).mp (domainProperties hE hg).dense
    have hzero := linearMap_eq_zero_of_inner_self_eq_zero _ hdense
      (V - (spectralOp E g).toFun) fun ψ => by
        have hψ := (mem_spectralOp_domain_iff hE hg).mp ψ.2
        have h₁ : ⟪(ψ : H), V ψ⟫_ℂ = _ := hinner ψ.1 (mem ψ)
        have h₂ : ⟪(ψ : H), (spectralOp E g).toFun ψ⟫_ℂ = ∫ y, g y ∂(diagonalMeasure E ψ.1) := by
          rw [show (spectralOp E g).toFun ψ = spectralOp E g ψ from rfl,
            spectralOp_apply hE hg ψ hψ, inner_spectralIntegral hE hg hψ]
        rw [LinearMap.sub_apply, inner_sub_right, h₁, h₂, sub_eq_zero]
        have e₁ : (toSpectralMeasure hE).integral ψ.1 (realPartOnCoords g) =
            ∫ y, (g y).re ∂(diagonalMeasure E ψ.1) := by
          show ∫ y, realPartOnCoords g y ∂((toSpectralMeasure hE).diagMeasure ψ.1) = _
          rw [diagMeasure_toSpectralMeasure hE,
            integral_map measurable_ofLp_space.aemeasurable hg'.aestronglyMeasurable]
          exact integral_congr_ae (ae_of_all _ hcomp)
        rw [e₁, ← integral_complex_ofReal]
        exact integral_congr_ae (ae_of_all _ fun y => (hgre y).symm)
    refine SpectralTheory.SpectralMeasure.IsRealIntegralOp.eq_realIntegralOp
      ⟨hDom, fun ψ => ?_⟩
    have := hzero ψ
    rw [LinearMap.sub_apply, sub_eq_zero] at this
    exact this.symm
end Coordinates
theorem statement_holds (h₁ : BoundedBorelCalculusTheorem)
    (h₂ : SpectralTheory.RealBorelCalculus) : Statement := by
  intro n n' _ _ H _ _ _ E hpvm f g hf hg c
  have base : ∀ {m : ℕ}, 1 ≤ m → ∀ E' : BorelSubset m → H →L[ℂ] H, IsPVM E' →
      Hypotheses E' := fun hm E' hp => by
    obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := h₁ _ hm H E' hp
    exact ⟨hp, a₁, a₂, a₃, a₄, a₅, a₆⟩
  have hn : 1 ≤ n := NeZero.one_le
  have hn' : 1 ≤ n' := NeZero.one_le
  have hE := base hn E hpvm
  refine ⟨domainProperties hE hf, linearityAndNorms hE hf hg c, adjointProperties hE hf,
    multiplicativity hE hf hg, essentialProperties hE hf hg, kernel_eq_range_zeroLocus hE hf,
    boundedConvergence hE hf, ?_, ?_, commutantProperty hE hf, coordinateCompatibility hE h₂ hg⟩
  · intro κ hκ
    have hp := isPVM_pushforward hE κ hκ
    exact ⟨hp, fun h hh => spectralOp_pushforward hE (base hn' _ hp) hh⟩
  · intro U
    have hp := isPVM_unitaryConj hE U
    exact ⟨hp, spectralOp_unitaryConj hE (base hn _ hp) hf⟩
end YangMills.Construction.EuclideanBorel.FunctionalCalculus
