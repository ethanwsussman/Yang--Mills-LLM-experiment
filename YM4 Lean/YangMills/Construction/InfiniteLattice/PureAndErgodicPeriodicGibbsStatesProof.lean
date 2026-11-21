import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservables
import YangMills.Construction.InfiniteLattice.InvariantFunctionPassesThroughTheGibbsEquations
import YangMills.Construction.InfiniteLattice.InvariantFunctionsOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.MeasuresOfTheInvariantClassAsLowerTangentsProof
import YangMills.Construction.InfiniteLattice.PureAndErgodicPeriodicGibbsStates
import YangMills.Construction.InfiniteLattice.RulesOfTheGibbsKernelOfTheUnitLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal ComplexOrder ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicGibbsExtremal
theorem ae_eq_const_of_ergodic {μ : Measure (GaugeField (1 : ℝ))}
    (hμ : IsUnitShiftErgodic μ) {f : GaugeField (1 : ℝ) → ℂ}
    (hf : Measurable[shiftInvariantSigma 1] f) : ∃ c : ℂ, f =ᵐ[μ] Function.const _ c := by
  have := hμ.1
  refine Filter.exists_eventuallyEq_const_of_forall_separating MeasurableSet fun S hS => ?_
  have hInv : MeasurableSet[shiftInvariantSigma 1] (f ⁻¹' S) := hf hS
  have hMeas : MeasurableSet (f ⁻¹' S) := hInv.1
  rcases hμ.2.2 _ hInv with h0 | h1
  · right
    exact measure_eq_zero_iff_ae_notMem.mp h0
  · left
    exact (mem_ae_iff_prob_eq_one hMeas).mpr h1
theorem IsBoundedObservable.integrable {μ : Measure (GaugeField (1 : ℝ))} [IsFiniteMeasure μ]
    {f : GaugeField (1 : ℝ) → ℂ} (hf : IsBoundedObservable f) : Integrable f μ := by apply _root_.YangMills.Construction.InfiniteLattice.InvariantGibbsLowerTangent.integrable_of_isBoundedObservable <;> assumption
theorem integral_smul_add_smul {μ₁ μ₂ : Measure (GaugeField (1 : ℝ))} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {f : GaugeField (1 : ℝ) → ℂ} (hf : IsBoundedObservable f) :
    ∫ U, f U ∂(ENNReal.ofReal a • μ₁ + ENNReal.ofReal b • μ₂) =
      (a : ℂ) * ∫ U, f U ∂μ₁ + (b : ℂ) * ∫ U, f U ∂μ₂ := by
  rw [integral_add_measure
    ((IsBoundedObservable.integrable hf).smul_measure ENNReal.ofReal_ne_top)
    ((IsBoundedObservable.integrable hf).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal hb]
  simp [Complex.real_smul]
theorem isBoundedObservable_actOn (hact : SymmetryActionOnObservables)
    (r : LatticeSymmetry (1 : ℝ)) {f : GaugeField (1 : ℝ) → ℂ} (hf : IsBoundedObservable f) :
    IsBoundedObservable (r.actOn f) :=
  (((hact ⟨1, one_pos⟩).2.2.1 r).1 f f hf hf).1
theorem IsBoundedObservable.mul {f g : GaugeField (1 : ℝ) → ℂ} (hf : IsBoundedObservable f)
    (hg : IsBoundedObservable g) : IsBoundedObservable fun U => f U * g U := by
  obtain ⟨hm, C, hC⟩ := hf
  obtain ⟨hm', C', hC'⟩ := hg
  refine ⟨hm.mul hm', C * C', fun U => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hC U) (hC' U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
theorem convex_combination_mem (hker : UnitGibbsKernelRules)
    (hact : SymmetryActionOnObservables) {β : ℝ} (hβ : 0 < β)
    {μ₁ μ₂ : Measure (GaugeField (1 : ℝ))} (h₁ : μ₁ ∈ periodicGibbsUnit β)
    (h₂ : μ₂ ∈ periodicGibbsUnit β) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ENNReal.ofReal t • μ₁ + ENNReal.ofReal (1 - t) • μ₂ ∈ periodicGibbsUnit β := by
  obtain ⟨g₁, P₁, f₁, i₁⟩ := (mem_periodicGibbsUnit_iff β μ₁).mp h₁
  obtain ⟨g₂, P₂, f₂, i₂⟩ := (mem_periodicGibbsUnit_iff β μ₂).mp h₂
  have : IsProbabilityMeasure μ₁ := g₁.1
  have : IsProbabilityMeasure μ₂ := g₂.1
  have hs : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hprob : IsProbabilityMeasure (ENNReal.ofReal t • μ₁ + ENNReal.ofReal (1 - t) • μ₂) := by
    refine ⟨?_⟩
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ht0 hs]
    simp
  refine (mem_periodicGibbsUnit_iff β _).mpr
    ⟨((hker β hβ).2 _ hprob).mpr fun W h F hF => ?_, P₁ ⊓ P₂, ?_, fun v hv A hA => ?_⟩
  · have hFo : IsBoundedObservable F := hF.1
    have hγ := ((hker β hβ).1 W h F hFo).1.1
    rw [integral_smul_add_smul ht0 hs hγ, integral_smul_add_smul ht0 hs hFo,
      ((hker β hβ).2 μ₁ inferInstance).mp g₁ W h F hF,
      ((hker β hβ).2 μ₂ inferInstance).mp g₂ W h F hF]
  · have := f₁
    have := f₂
    infer_instance
  · rw [integral_smul_add_smul ht0 hs (isBoundedObservable_actOn hact _ hA),
      integral_smul_add_smul ht0 hs hA, i₁ v hv.1 A hA, i₂ v hv.2 A hA]
theorem weightedGibbsUnit_indicator_const (μ : Measure (GaugeField (1 : ℝ)))
    {I : Set (GaugeField (1 : ℝ))} (hI : MeasurableSet I) (c : ℝ) :
    weightedGibbsUnit (I.indicator fun _ => (c : ℂ)) μ = ENNReal.ofReal c • μ.restrict I := by
  have h : (fun U => ENNReal.ofReal ((I.indicator (fun _ => (c : ℂ)) U).re)) =
      I.indicator fun _ => ENNReal.ofReal c := by
    funext U
    by_cases hU : U ∈ I <;> simp [hU]
  unfold weightedGibbsUnit FormHilbert.densityMeasure
  rw [h, withDensity_indicator hI, withDensity_const]
theorem normalized_restrict_mem (hfac : ShiftInvariantWeightPassesGibbsEquations)
    {β : ℝ} (hβ : 0 < β) {μ : Measure (GaugeField (1 : ℝ))}
    (hμ : μ ∈ periodicGibbsUnit β) [IsProbabilityMeasure μ]
    {I : Set (GaugeField (1 : ℝ))} (hI : MeasurableSet[shiftInvariantSigma 1] I) (h0 : μ I ≠ 0) :
    ENNReal.ofReal (μ.real I)⁻¹ • μ.restrict I ∈ periodicGibbsUnit β := by
  obtain ⟨-, P, hP⟩ := (mem_periodicGibbsUnit_iff β μ).mp hμ
  have hMeas : MeasurableSet I := hI.1
  have hpos : 0 < μ.real I := ENNReal.toReal_pos h0 (measure_ne_top _ _)
  have hm : Measurable[shiftInvariantSigma 1] (I.indicator fun _ => (((μ.real I)⁻¹ : ℝ) : ℂ)) :=
    Measurable.indicator measurable_const hI
  have hb : ∃ C : ℝ, ∀ U, ‖I.indicator (fun _ => (((μ.real I)⁻¹ : ℝ) : ℂ)) U‖ ≤ C := by
    refine ⟨|(μ.real I)⁻¹|, fun U => ?_⟩
    by_cases hU : U ∈ I
    · simp [hU]
    · simp [hU]
  have hnn : ∀ U, 0 ≤ I.indicator (fun _ => (((μ.real I)⁻¹ : ℝ) : ℂ)) U := by
    intro U
    by_cases hU : U ∈ I
    · simp [hU]
    · simp [hU]
  have hone : ∫ U, I.indicator (fun _ => (((μ.real I)⁻¹ : ℝ) : ℂ)) U ∂μ = 1 := by
    rw [integral_indicator hMeas, setIntegral_const, Complex.real_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hpos.ne']
    simp
  have hmem := ((hfac β hβ μ P hμ hP _ hm hb).2.2 hnn hone).2.2.1
  rwa [weightedGibbsUnit_indicator_const μ hMeas] at hmem
theorem ergodic_of_extremal (hfac : ShiftInvariantWeightPassesGibbsEquations)
    {β : ℝ} (hβ : 0 < β) {μ : Measure (GaugeField (1 : ℝ))}
    (hx : IsExtremalUnitPeriodicGibbs β μ) : IsUnitShiftErgodic μ := by
  obtain ⟨hμ, hext⟩ := hx
  obtain ⟨g, P, hP⟩ := (mem_periodicGibbsUnit_iff β μ).mp hμ
  have : IsProbabilityMeasure μ := g.1
  refine ⟨inferInstance, ⟨P, hP.1, hP.2⟩, fun I hI => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hI0, hI1⟩ := hne
  have hMeas : MeasurableSet I := hI.1
  have hIc : MeasurableSet[shiftInvariantSigma 1] Iᶜ := MeasurableSet.compl hI
  have hc0 : μ Iᶜ ≠ 0 := fun h => hI1 ((prob_compl_eq_zero_iff hMeas).mp h)
  have ht0 : 0 < μ.real I := ENNReal.toReal_pos hI0 (measure_ne_top _ _)
  have hc : 0 < μ.real Iᶜ := ENNReal.toReal_pos hc0 (measure_ne_top _ _)
  have hcompl : μ.real Iᶜ = 1 - μ.real I := probReal_compl_eq_one_sub hMeas
  have ht1 : μ.real I < 1 := by linarith
  have hsum : μ = ENNReal.ofReal (μ.real I) • (ENNReal.ofReal (μ.real I)⁻¹ • μ.restrict I) +
      ENNReal.ofReal (1 - μ.real I) • (ENNReal.ofReal (μ.real Iᶜ)⁻¹ • μ.restrict Iᶜ) := by
    rw [← hcompl, smul_smul, smul_smul, ← ENNReal.ofReal_mul ht0.le, ← ENNReal.ofReal_mul hc.le,
      mul_inv_cancel₀ ht0.ne', mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_smul, one_smul,
      Measure.restrict_add_restrict_compl hMeas]
  have key := hext (μ.real I) ht0 ht1 _ (normalized_restrict_mem hfac hβ hμ hI hI0) _
    (normalized_restrict_mem hfac hβ hμ hIc hc0) hsum
  apply hc0
  rw [← key.1]
  simp [Measure.restrict_apply hMeas.compl]
theorem eq_of_smul_add_eq (hact : SymmetryActionOnObservables)
    (hinv : ShiftInvariantFunctions.InvariantFunctionsTheorem)
    {μ μ₁ ρ : Measure (GaugeField (1 : ℝ))} (hμ : IsUnitShiftErgodic μ)
    (hS : IsShiftInvariant μ) (hS₁ : IsShiftInvariant μ₁) [IsProbabilityMeasure μ₁]
    {t : ℝ} (ht : 0 < t) (hsum : μ = ENNReal.ofReal t • μ₁ + ρ) : μ₁ = μ := by
  have := hμ.1
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, μ₀ = ENNReal.ofReal t • μ₁ := ⟨_, rfl⟩
  rw [← hμ₀] at hsum
  have : IsFiniteMeasure μ₀ := by
    rw [hμ₀]
    exact Measure.smul_finite μ₁ ENNReal.ofReal_ne_top
  have hle : μ₀ ≤ μ := by
    have h : μ₀ ≤ μ₀ + ρ := Measure.le_add_right le_rfl
    rwa [← hsum] at h
  have hac : μ₀ ≪ μ := Measure.absolutelyContinuous_of_le hle
  have hd1 : μ₀.rnDeriv μ ≤ᵐ[μ] 1 := Measure.rnDeriv_le_one_of_le hle
  obtain ⟨g, hg⟩ : ∃ g : GaugeField (1 : ℝ) → ℝ,
      g = fun U => min (μ₀.rnDeriv μ U).toReal 1 := ⟨_, rfl⟩
  have hgm : Measurable g := by
    rw [hg]
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal.min measurable_const
  obtain ⟨G, hG⟩ : ∃ G : GaugeField (1 : ℝ) → ℂ, G = fun U => (g U : ℂ) := ⟨_, rfl⟩
  have hGobs : IsBoundedObservable G := by
    refine ⟨by rw [hG]; exact Complex.measurable_ofReal.comp hgm, 1, fun U => ?_⟩
    have hlo : 0 ≤ g U := by
      rw [hg]
      exact le_min ENNReal.toReal_nonneg zero_le_one
    have hhi : g U ≤ 1 := by
      rw [hg]
      exact min_le_right _ _
    rw [hG]
    simpa [abs_of_nonneg hlo] using hhi
  have hGd : ∀ᵐ U ∂μ, g U = (μ₀.rnDeriv μ U).toReal := by
    filter_upwards [hd1] with U hU
    rw [hg]
    refine min_eq_left ?_
    have : (μ₀.rnDeriv μ U).toReal ≤ (1 : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono ENNReal.one_ne_top hU
    simpa using this
  have hrep : ∀ F : GaugeField (1 : ℝ) → ℂ, ∫ U, F U ∂μ₀ = ∫ U, G U * F U ∂μ := by
    intro F
    rw [← integral_rnDeriv_smul hac]
    refine integral_congr_ae ?_
    filter_upwards [hGd] with U hU
    rw [hG]
    simp [hU, Complex.real_smul]
  have hinv₀ : ∀ (w : LatticePoint (1 : ℝ)) (F : GaugeField (1 : ℝ) → ℂ), IsBoundedObservable F →
      ∫ U, (shift w).actOn F U ∂μ₀ = ∫ U, F U ∂μ₀ := by
    intro w F hF
    rw [hμ₀, integral_smul_measure, integral_smul_measure, hS₁ w F hF]
  have hshift : ∀ w : LatticePoint (1 : ℝ), (shift w).actOn G =ᵐ[μ] G := by
    intro w
    have hinverse : (shift w).IsInverse (shift (-w)) := by
      constructor
      · intro x
        simp [shift]
      · intro x
        simp [shift]
    have hback : ∀ F : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable F →
        (shift w).actOn ((shift (-w)).actOn F) = F := fun F hF =>
      (((((hact ⟨1, one_pos⟩).2.2.2.2.2.2.2.2.2.1 (shift (-w))).2.2 (shift w)
        hinverse).1 F hF).1)
    have hmove : ∀ F : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable F →
        ∫ U, G U * F U ∂μ = ∫ U, (shift w).actOn G U * F U ∂μ := by
      intro F hF
      have hrF := isBoundedObservable_actOn hact (shift (-w)) hF
      calc ∫ U, G U * F U ∂μ = ∫ U, F U ∂μ₀ := (hrep F).symm
        _ = ∫ U, (shift (-w)).actOn F U ∂μ₀ := (hinv₀ (-w) F hF).symm
        _ = ∫ U, G U * (shift (-w)).actOn F U ∂μ := hrep _
        _ = ∫ U, (shift w).actOn
              (fun U' => G U' * (shift (-w)).actOn F U') U ∂μ :=
            (hS w _ (IsBoundedObservable.mul hGobs hrF)).symm
        _ = ∫ U, (shift w).actOn G U * F U ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
            change (shift w).actOn G U *
              (shift w).actOn ((shift (-w)).actOn F) U = _
            rw [hback F hF]
    obtain ⟨D, hD⟩ : ∃ D : GaugeField (1 : ℝ) → ℂ,
        D = fun U => G U - (shift w).actOn G U := ⟨_, rfl⟩
    have hτG := isBoundedObservable_actOn hact (shift w) hGobs
    have hDobs : IsBoundedObservable D := by
      obtain ⟨hm, C, hC⟩ := hGobs
      obtain ⟨hm', C', hC'⟩ := hτG
      refine ⟨by rw [hD]; exact hm.sub hm', C + C', fun U => ?_⟩
      rw [hD]
      exact (norm_sub_le _ _).trans (add_le_add (hC U) (hC' U))
    have hcD : IsBoundedObservable fun U => conj (D U) := by
      obtain ⟨hm, C, hC⟩ := hDobs
      exact ⟨Complex.continuous_conj.measurable.comp hm, C, fun U => by simpa using hC U⟩
    have hzero : ∫ U, D U * conj (D U) ∂μ = 0 := by
      have e := hmove _ hcD
      have hi₁ : Integrable (fun U => G U * conj (D U)) μ :=
        IsBoundedObservable.integrable (IsBoundedObservable.mul hGobs hcD)
      have hi₂ : Integrable (fun U => (shift w).actOn G U * conj (D U)) μ :=
        IsBoundedObservable.integrable (IsBoundedObservable.mul hτG hcD)
      have hsplit : (fun U => D U * conj (D U)) = fun U => G U * conj (D U) -
          (shift w).actOn G U * conj (D U) := by
        funext U
        rw [hD]
        ring
      rw [hsplit, integral_sub hi₁ hi₂, e, sub_self]
    have hPobs := IsBoundedObservable.mul hDobs hcD
    have hint : Integrable (fun U => Complex.normSq (D U)) μ := by
      have h := (IsBoundedObservable.integrable (μ := μ) hPobs).re
      refine h.congr (Filter.Eventually.of_forall fun U => ?_)
      simp [Complex.mul_conj]
    have hre : ∫ U, Complex.normSq (D U) ∂μ = 0 := by
      have h : ((∫ U, Complex.normSq (D U) ∂μ : ℝ) : ℂ) = 0 := by
        rw [← integral_complex_ofReal, ← hzero]
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        exact (Complex.mul_conj _).symm
      exact_mod_cast h
    have hae := (integral_eq_zero_iff_of_nonneg (fun U => Complex.normSq_nonneg _) hint).mp hre
    filter_upwards [hae] with U hU
    have hDU : D U = 0 := Complex.normSq_eq_zero.mp hU
    rw [hD] at hDU
    exact (sub_eq_zero.mp hDU).symm
  obtain ⟨J, hJ, hJe⟩ := (hinv.2 μ).1 ShiftPair.allShifts G hGobs.1
    (fun v _ => hshift v)
  obtain ⟨c, hc⟩ := ae_eq_const_of_ergodic hμ hJ
  have hGc : G =ᵐ[μ] Function.const _ c := hJe.symm.trans hc
  have hdc : μ₀.rnDeriv μ =ᵐ[μ] fun _ => ENNReal.ofReal c.re := by
    filter_upwards [hGc, hGd, hd1] with U h1 h2 h3
    have hgc : g U = c.re := by
      have h := congrArg Complex.re h1
      rw [hG] at h
      simpa using h
    have htop : μ₀.rnDeriv μ U ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top h3
    rw [← hgc, h2, ENNReal.ofReal_toReal htop]
  have hscale : μ₀ = ENNReal.ofReal c.re • μ :=
    calc μ₀ = μ.withDensity (μ₀.rnDeriv μ) := (Measure.withDensity_rnDeriv_eq μ₀ μ hac).symm
      _ = μ.withDensity (fun _ => ENNReal.ofReal c.re) := withDensity_congr_ae hdc
      _ = ENNReal.ofReal c.re • μ := withDensity_const _
  have hconst : ENNReal.ofReal t = ENNReal.ofReal c.re := by
    have h := congrArg (fun m : Measure (GaugeField (1 : ℝ)) => m Set.univ)
      (hμ₀.symm.trans hscale)
    simpa using h
  have htne : ENNReal.ofReal t ≠ 0 := by simpa using ht
  refine Measure.ext fun S _ => ?_
  have h := congrArg (fun m : Measure (GaugeField (1 : ℝ)) => m S) (hμ₀.symm.trans hscale)
  rw [← hconst] at h
  simp only [Measure.smul_apply, smul_eq_mul] at h
  exact (ENNReal.mul_right_inj htne ENNReal.ofReal_ne_top).mp h
theorem extremalErgodicPeriodicGibbs_holds (hact : SymmetryActionOnObservables)
    (hfac : ShiftInvariantWeightPassesGibbsEquations)
    (hinv : ShiftInvariantFunctions.InvariantFunctionsTheorem)
    (hker : UnitGibbsKernelRules) :
    ExtremalErgodicPeriodicGibbsStatement := by
  intro β hβ
  refine ⟨fun μ₁ h₁ μ₂ h₂ t h0 h1 => convex_combination_mem hker hact hβ h₁ h₂ h0 h1,
    fun μ hμ => ⟨?_, ?_⟩,
    fun μ hx => ergodic_of_extremal hfac hβ hx, fun hall μ hμ he => ⟨hμ, ?_⟩⟩
  · intro J hJ _
    have := hμ.1
    obtain ⟨c, hc⟩ := ae_eq_const_of_ergodic hμ hJ
    have hint : ∫ U', J U' ∂μ = c := by
      rw [integral_congr_ae hc]
      simp
    filter_upwards [hc] with U hU
    rw [hU, hint]
    rfl
  · intro B hB
    have := hμ.1
    have hle : shiftInvariantSigma 1 ≤ (inferInstance : MeasurableSpace (GaugeField (1 : ℝ))) :=
      fun _ h => h.1
    have hm : Measurable[shiftInvariantSigma 1] (condExpGiven μ (shiftInvariantSigma 1) B) :=
      stronglyMeasurable_condExp.measurable
    obtain ⟨c, hc⟩ := ae_eq_const_of_ergodic hμ hm
    have hint : ∫ U', B U' ∂μ = c := by
      have h : ∫ U', condExpGiven μ (shiftInvariantSigma 1) B U' ∂μ = ∫ U', B U' ∂μ :=
        integral_condExp hle
      rw [← h, integral_congr_ae hc]
      simp
    filter_upwards [hc] with U hU
    rw [hU, hint]
    rfl
  · intro t h0 h1 μ₁ m₁ μ₂ m₂ hsum
    obtain ⟨g₁, -⟩ := (mem_periodicGibbsUnit_iff β μ₁).mp m₁
    obtain ⟨g₂, -⟩ := (mem_periodicGibbsUnit_iff β μ₂).mp m₂
    have : IsProbabilityMeasure μ₁ := g₁.1
    have : IsProbabilityMeasure μ₂ := g₂.1
    exact ⟨eq_of_smul_add_eq hact hinv he (hall μ hμ) (hall μ₁ m₁) h0 hsum,
      eq_of_smul_add_eq hact hinv he (hall μ hμ) (hall μ₂ m₂) (sub_pos.mpr h1)
        (hsum.trans (add_comm _ _))⟩
end YangMills.Construction.InfiniteLattice.PeriodicGibbsExtremal
