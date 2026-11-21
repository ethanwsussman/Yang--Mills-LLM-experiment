import YangMills.Construction.InfiniteLattice.FunctionsFixedByTheTranslations
import YangMills.Construction.InfiniteLattice.GibbsStatesReadThroughKernelsAndSymmetries
import YangMills.Construction.InfiniteLattice.InvariantDensitiesOfAPeriodicGibbsState
import YangMills.Construction.InfiniteLattice.InvariantFunctionsLongRangeOrderAndErgodicMeasures
import YangMills.Construction.InfiniteLattice.PureMeansErgodicUnderTheTranslations
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.LatticePhases.ExtremalIffShiftErgodic
theorem densityMeasure_indicator {a : ℝ} (ν : Measure (GaugeField a))
    {I : Set (GaugeField a)} (hI : MeasurableSet I) (c : ℝ) :
    densityMeasure ν (I.indicator fun _ => (c : ℂ)) = ENNReal.ofReal c • ν.restrict I := by
  have e : (fun ω => ENNReal.ofReal ((I.indicator (fun _ => (c : ℂ)) ω).re)) =
      I.indicator fun _ => ENNReal.ofReal c := by
    funext ω
    by_cases hω : ω ∈ I <;> simp [hω]
  rw [densityMeasure, e, withDensity_indicator hI, withDensity_const]
theorem restrict_mem_periodicGibbs (hD : InvariantDensityLaws) (S : Setup)
    {ν : Measure (GaugeField S.mesh)} (hν : IsPeriodicGibbs S.β ν)
    {J : Set (GaugeField S.mesh)} (hJ : MeasurableSet[shiftInvariantSigma S.mesh] J) {r : ℝ}
    (hr : 0 < r) (hνJ : ν J = ENNReal.ofReal r) :
    IsPeriodicGibbs S.β (ENNReal.ofReal r⁻¹ • ν.restrict J) := by
  have hJB : MeasurableSet J := hJ.1
  have hm : Measurable[shiftInvariantSigma S.mesh] (J.indicator fun _ => ((r⁻¹ : ℝ) : ℂ)) :=
    Measurable.indicator measurable_const hJ
  have hb : ∃ C : ℝ, ∀ ω, ‖J.indicator (fun _ => ((r⁻¹ : ℝ) : ℂ)) ω‖ ≤ C := by
    refine ⟨r⁻¹, fun ω => ?_⟩
    by_cases hω : ω ∈ J
    · simp [hω, abs_of_pos hr]
    · simp [hω, hr.le]
  have hpos : ∀ ω, (J.indicator (fun _ => ((r⁻¹ : ℝ) : ℂ)) ω).im = 0 ∧
      0 ≤ (J.indicator (fun _ => ((r⁻¹ : ℝ) : ℂ)) ω).re := by
    intro ω
    by_cases hω : ω ∈ J
    · simp [hω, hr.le]
    · simp [hω]
  have hone : ∫ ω, J.indicator (fun _ => ((r⁻¹ : ℝ) : ℂ)) ω ∂ν = 1 := by
    rw [integral_indicator hJB, setIntegral_const]
    have : ν.real J = r := by
      rw [Measure.real, hνJ, ENNReal.toReal_ofReal hr.le]
    rw [this, Complex.real_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one]
  have key : densityMeasure ν
      (J.indicator fun _ => ((r⁻¹ : ℝ) : ℂ)) ∈ periodicGibbsSet S.L S.K S.β :=
    ((hD S ⟨ν, hν⟩ _ hm hb).2.2 hpos hone).2.2
  have e := densityMeasure_indicator ν hJB r⁻¹
  rw [e] at key
  exact key
theorem measure_eq_zero_or_one_of_extremal (hD : InvariantDensityLaws) (S : Setup)
    {ν : Measure (GaugeField S.mesh)} (hext : IsExtremalPeriodicGibbs S.β ν)
    {I : Set (GaugeField S.mesh)} (hI : MeasurableSet[shiftInvariantSigma S.mesh] I) :
    ν I = 0 ∨ ν I = 1 := by
  have hper : IsPeriodicGibbs S.β ν := hext.1
  have hprob : IsProbabilityMeasure ν := hper.1.1
  by_contra hne
  rw [not_or] at hne
  obtain ⟨h0, h1⟩ := hne
  have hIB : MeasurableSet I := hI.1
  have hfin : ν I ≠ ⊤ := measure_ne_top _ _
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (ν I).toReal := ⟨_, rfl⟩
  have hs0 : 0 < s := hs ▸ ENNReal.toReal_pos h0 hfin
  have hlt : ν I < 1 := lt_of_le_of_ne prob_le_one h1
  have hs1 : s < 1 := by
    have := (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).2 hlt
    simpa [hs] using this
  have hνI : ν I = ENNReal.ofReal s := by rw [hs, ENNReal.ofReal_toReal hfin]
  have hνIc : ν Iᶜ = ENNReal.ofReal (1 - s) := by
    rw [prob_compl_eq_one_sub hIB, hνI, ENNReal.ofReal_sub _ hs0.le, ENNReal.ofReal_one]
  have hs1' : 0 < 1 - s := sub_pos.2 hs1
  have m₁ := restrict_mem_periodicGibbs hD S hper hI hs0 hνI
  have m₂ := restrict_mem_periodicGibbs hD S hper
    (@MeasurableSet.compl _ _ (shiftInvariantSigma S.mesh) hI) hs1' hνIc
  have hsplit : ν = ENNReal.ofReal s • (ENNReal.ofReal s⁻¹ • ν.restrict I) +
      ENNReal.ofReal (1 - s) • (ENNReal.ofReal (1 - s)⁻¹ • ν.restrict Iᶜ) := by
    rw [smul_smul, smul_smul, ← ENNReal.ofReal_mul hs0.le, ← ENNReal.ofReal_mul hs1'.le,
      mul_inv_cancel₀ hs0.ne', mul_inv_cancel₀ hs1'.ne', ENNReal.ofReal_one, one_smul, one_smul,
      Measure.restrict_add_restrict_compl hIB]
  have heq := (hext.2 _ _ m₁ m₂ s hs0 hs1 hsplit).1
  have hval : ν I = 1 := by
    conv_lhs => rw [← heq]
    rw [Measure.smul_apply, Measure.restrict_apply hIB, Set.inter_self, hνI, smul_eq_mul,
      ← ENNReal.ofReal_mul (inv_nonneg.2 hs0.le), inv_mul_cancel₀ hs0.ne', ENNReal.ofReal_one]
  exact h1 hval
theorem eq_of_smul_le_of_shiftErgodic (hA : ShiftFixedFunctions.Assertion)
    (hV : InvariantFunctionsAndErgodicity) (S : Setup)
    {ν ν₁ : Measure (GaugeField S.mesh)} (hν : IsShiftErgodic ν)
    [IsProbabilityMeasure ν₁] (hinv₁ : IsShiftInvariant ν₁) {s : ℝ} (hs : 0 < s)
    (hle : ENNReal.ofReal s • ν₁ ≤ ν) : ν₁ = ν := by
  have hprob : IsProbabilityMeasure ν := hν.1
  have hinv : IsShiftInvariant ν := hν.2.1
  obtain ⟨μ, hμdef⟩ : ∃ μ, μ = ENNReal.ofReal s • ν₁ := ⟨_, rfl⟩
  have hμle : μ ≤ ν := hμdef ▸ hle
  have : IsFiniteMeasure μ := by
    rw [hμdef]
    exact Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hac : μ ≪ ν := Measure.absolutelyContinuous_of_le hμle
  have hf : Measurable (μ.rnDeriv ν) := Measure.measurable_rnDeriv _ _
  have hf1 : μ.rnDeriv ν ≤ᵐ[ν] 1 := Measure.rnDeriv_le_one_of_le hμle
  obtain ⟨g, hg⟩ : ∃ g : GaugeField S.mesh → ℝ, g = fun ω => (min (μ.rnDeriv ν ω) 1).toReal :=
    ⟨_, rfl⟩
  have hgm : Measurable g := hg ▸ (hf.min measurable_const).ennreal_toReal
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => by rw [hg]; exact ENNReal.toReal_nonneg
  have hg1 : ∀ ω, g ω ≤ 1 := fun ω => by
    rw [hg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simp)
  have hgf : (fun ω => ENNReal.ofReal (g ω)) =ᵐ[ν] μ.rnDeriv ν := by
    filter_upwards [hf1] with ω hω
    have hω' : μ.rnDeriv ν ω ≤ 1 := hω
    rw [hg]
    simp only [min_eq_left hω']
    exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hω')
  have hμ : ν.withDensity (fun ω => ENNReal.ofReal (g ω)) = μ := by
    rw [withDensity_congr_ae hgf]
    exact Measure.withDensity_rnDeriv_eq _ _ hac
  have hgm' : Measurable fun ω => ENNReal.ofReal (g ω) := hgm.ennreal_ofReal
  obtain ⟨X, hX⟩ : ∃ X : GaugeField S.mesh → ℂ, X = fun ω => (g ω : ℂ) := ⟨_, rfl⟩
  have hXm : Measurable X := hX ▸ Complex.measurable_ofReal.comp hgm
  have hXb : ∀ ω, ‖X ω‖ ≤ 1 := fun ω => by
    rw [hX]
    simpa [abs_of_nonneg (hg0 ω)] using hg1 ω
  have hXo : IsBoundedObservable X := ⟨hXm, 1, hXb⟩
  have mulObs : ∀ {A B : GaugeField S.mesh → ℂ}, IsBoundedObservable A →
      IsBoundedObservable B → IsBoundedObservable fun ω => A ω * B ω := by
    rintro A B ⟨hm, C, hC⟩ ⟨hm', C', hC'⟩
    refine ⟨hm.mul hm', C * C', fun ω => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hC ω) (hC' ω) (norm_nonneg _) ((norm_nonneg _).trans (hC ω))
  have intObs : ∀ {A : GaugeField S.mesh → ℂ}, IsBoundedObservable A → Integrable A ν := by
    rintro A ⟨hm, C, hC⟩
    exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
  have hint : ∀ F : GaugeField S.mesh → ℂ, ∫ ω, F ω ∂μ = ∫ ω, X ω * F ω ∂ν := by
    intro F
    rw [← hμ, integral_withDensity_eq_integral_toReal_smul hgm'
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    show (ENNReal.ofReal (g ω)).toReal • F ω = X ω * F ω
    rw [ENNReal.toReal_ofReal (hg0 ω), Complex.real_smul, hX]
  have hinvμ : ∀ (v : LatticePoint S.mesh) (F : GaugeField S.mesh → ℂ), IsBoundedObservable F →
      ∫ ω, (shift v).actOn F ω ∂μ = ∫ ω, F ω ∂μ := by
    intro v F hF
    rw [hμdef, integral_smul_measure, integral_smul_measure, hinv₁ v F hF]
  have hfix : ∀ v : LatticePoint S.mesh, ∀ᵐ ω ∂ν, (shift v).actOn X ω = X ω := by
    intro v
    obtain ⟨T, hT⟩ : ∃ T : GaugeField S.mesh → ℂ, T = (shift v).actOn X := ⟨_, rfl⟩
    have hTo : IsBoundedObservable T := hT ▸ hXo.actOn (shift v)
    have e₁ : ∫ ω, X ω * T ω ∂ν = ∫ ω, X ω * X ω ∂ν := by
      rw [← hint, ← hint, hT]
      exact hinvμ v X hXo
    have e₂ : ∫ ω, T ω * T ω ∂ν = ∫ ω, X ω * X ω ∂ν := by
      have := hinv v (fun ω => X ω * X ω) (mulObs hXo hXo)
      rw [← this, hT]
      rfl
    obtain ⟨w, hw⟩ : ∃ w : GaugeField S.mesh → ℝ,
        w = fun ω => ‖T ω - X ω‖ ^ 2 := ⟨_, rfl⟩
    have hTreal : ∀ ω, T ω = ((g ((shift v).pullbackField ω) : ℝ) : ℂ) := fun ω => by
      rw [hT, hX]
      rfl
    have hwexp : ∀ ω, ((w ω : ℝ) : ℂ) = T ω * T ω - 2 * (X ω * T ω) + X ω * X ω := by
      intro ω
      have hXω : X ω = ((g ω : ℝ) : ℂ) := by rw [hX]
      rw [hw]
      simp only [hTreal ω, hXω]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      push_cast
      ring
    have i₁ : Integrable (fun ω => T ω * T ω) ν := intObs (mulObs hTo hTo)
    have i₂ : Integrable (fun ω => 2 * (X ω * T ω)) ν := (intObs (mulObs hXo hTo)).const_mul 2
    have i₃ : Integrable (fun ω => T ω * T ω - 2 * (X ω * T ω)) ν := i₁.sub i₂
    have hzero : ∫ ω, ((w ω : ℝ) : ℂ) ∂ν = 0 := by
      simp only [hwexp]
      rw [integral_add i₃ (intObs (mulObs hXo hXo)), integral_sub i₁ i₂, integral_const_mul, e₁, e₂]
      ring
    have hwint : Integrable w ν := by
      have : Integrable (fun ω => ((w ω : ℝ) : ℂ)) ν := by
        simp only [hwexp]
        exact i₃.add (intObs (mulObs hXo hXo))
      exact this.re
    have hw0 : 0 ≤ᵐ[ν] w := ae_of_all _ fun ω => by rw [hw]; positivity
    have hzero' : ∫ ω, w ω ∂ν = 0 := by
      rw [integral_complex_ofReal] at hzero
      exact_mod_cast hzero
    have hae := (integral_eq_zero_iff_of_nonneg_ae hw0 hwint).1 hzero'
    filter_upwards [hae] with ω hω
    have hω' : ‖T ω - X ω‖ ^ 2 = 0 := by
      have : w ω = 0 := hω
      rwa [hw] at this
    have := sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 hω'))
    rw [← hT]
    exact this
  let ρ : ProbMeasure (GaugeField S.mesh) := (⟨ν, hprob⟩ : ProbabilityMeasure (GaugeField S.mesh))
  have hb := (hA S).2 ρ X hXm fun v => (ProbMeasure.holdsAS_iff ρ _).2 (hfix v)
  obtain ⟨-, -, hJm, hJae⟩ := hb
  obtain ⟨c, hc⟩ := ((hV S).2.2 ρ hν).1 _ hJm
  have hXc : ∀ᵐ ω ∂ν, X ω = c := by
    filter_upwards [(ProbMeasure.holdsAS_iff ρ _).1 hJae, (ProbMeasure.holdsAS_iff ρ _).1 hc]
      with ω h₁ h₂
    rw [← h₁, h₂]
  have hgc : (fun ω => ENNReal.ofReal (g ω)) =ᵐ[ν] fun _ => ENNReal.ofReal c.re := by
    filter_upwards [hXc] with ω hω
    have : g ω = c.re := by
      rw [← hω, hX]
      simp
    rw [this]
  have hμc : μ = ENNReal.ofReal c.re • ν := by
    rw [← hμ, withDensity_congr_ae hgc, withDensity_const]
  have hmass : ENNReal.ofReal s = ENNReal.ofReal c.re := by
    have := congrArg (fun m : Measure (GaugeField S.mesh) => m Set.univ) (hμdef.symm.trans hμc)
    simpa using this
  have hs0 : ENNReal.ofReal s ≠ 0 := by simpa using hs
  ext E hE
  have := congrArg (fun m : Measure (GaugeField S.mesh) => m E) (hμdef.symm.trans hμc)
  simp only [Measure.smul_apply, smul_eq_mul, ← hmass] at this
  exact (ENNReal.mul_right_inj hs0 ENNReal.ofReal_ne_top).1 this
theorem extremal_of_shiftErgodic (hA : ShiftFixedFunctions.Assertion)
    (hG : GibbsKernelsAndSymmetries.Assertion)
    (hV : InvariantFunctionsAndErgodicity) (S : Setup)
    {ν : Measure (GaugeField S.mesh)} (hper : IsPeriodicGibbs S.β ν)
    (hν : IsShiftErgodic ν) : IsExtremalPeriodicGibbs S.β ν := by
  refine ⟨hper, fun ν₁ ν₂ p₁ p₂ t ht0 ht1 hsplit => ?_⟩
  have h₁ : IsProbabilityMeasure ν₁ := p₁.1.1
  have h₂ : IsProbabilityMeasure ν₂ := p₂.1.1
  have inv : ∀ (m : Measure (GaugeField S.mesh)) [IsProbabilityMeasure m],
      IsPeriodicGibbs S.β m → IsShiftInvariant m := by
    intro m hm p
    let ρ : ProbMeasure (GaugeField S.mesh) :=
      (⟨m, hm⟩ : ProbabilityMeasure (GaugeField S.mesh))
    exact (((hG S S.β S.β_pos).2.1 ρ p).2.1)
  have le₁ : ENNReal.ofReal t • ν₁ ≤ ν := by
    rw [hsplit]
    exact Measure.le_add_right le_rfl
  have le₂ : ENNReal.ofReal (1 - t) • ν₂ ≤ ν := by
    rw [hsplit]
    exact Measure.le_add_left le_rfl
  exact ⟨eq_of_smul_le_of_shiftErgodic hA hV S hν (inv ν₁ p₁) ht0 le₁,
    eq_of_smul_le_of_shiftErgodic hA hV S hν (inv ν₂ p₂) (sub_pos.2 ht1) le₂⟩
theorem extremalIffShiftErgodic (hA : ShiftFixedFunctions.Assertion)
    (hD : InvariantDensityLaws)
    (hG : GibbsKernelsAndSymmetries.Assertion)
    (hV : InvariantFunctionsAndErgodicity) : ExtremalIffShiftErgodicStatement := by
  intro S
  have inv : ∀ ν : Measure (GaugeField S.mesh), IsPeriodicGibbs S.β ν →
      IsProbabilityMeasure ν ∧ IsShiftInvariant ν := by
    intro ν hper
    have hprob : IsProbabilityMeasure ν := hper.1.1
    let ρ : ProbMeasure (GaugeField S.mesh) :=
      (⟨ν, hprob⟩ : ProbabilityMeasure (GaugeField S.mesh))
    exact ⟨hprob, ((hG S S.β S.β_pos).2.1 ρ hper).2.1⟩
  have main : ∀ ν : Measure (GaugeField S.mesh), IsPeriodicGibbs S.β ν →
      (IsExtremalPeriodicGibbs S.β ν ↔ IsShiftErgodic ν) := by
    intro ν hper
    exact ⟨fun hp => ⟨(inv ν hper).1, (inv ν hper).2, fun I hI =>
      measure_eq_zero_or_one_of_extremal hD S hp hI⟩, extremal_of_shiftErgodic hA hG hV S hper⟩
  refine ⟨fun ν hν => main ν hν, ?_⟩
  ext ν
  constructor
  · rintro ⟨hper, -, herg⟩
    exact ⟨hper, (main ν hper).2 herg⟩
  · rintro ⟨hper, hext⟩
    exact ⟨hper, (inv ν hper).2, (main ν hper).1 hext⟩
end YangMills.Construction.LatticePhases.ExtremalIffShiftErgodic
