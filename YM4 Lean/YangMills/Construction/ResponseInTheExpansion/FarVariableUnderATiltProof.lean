import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfCoresProof
import YangMills.Construction.ClusterExpansionOfAStep.ConditionalLawsOfAWeight
import YangMills.Construction.ClusterExpansionOfAStep.TwoSystemsOfTheGasProof
import YangMills.Construction.ResponseInTheExpansion.FarSpinsMoveAVariableProof
import YangMills.Construction.FreeEnergiesOfTheFlow.SupportsOverAStepDefs
import YangMills.Construction.ResponseInTheExpansion.TiltsOfTheGas
import Mathlib
import YangMills.Construction.ResponseInTheExpansion.ScoreOfAClassIsPaid
import YangMills.Construction.ResponseInTheExpansion.TiltOfALawOfSpins
set_option autoImplicit false

noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages TorusFields StepSettings RenormalizationStepParameters StepGas FreeEnergies WeightedResponses
def GasSupportMeanUnderTilt : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧
    ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∀ K : ResponseParameters, ∃ y₀ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y₀ ≤ y →
    ∀ (R : StepSetup) (A : ResponseSetup R), A.responseParams = K → OnStepParameters T y A →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (Q : Finset (TorusSite n))
      (B : Finset (TorusSite (n * R.params.side))) (e : ℝ) (Yt : G.Config → ℝ) (D : ℕ),
      weightNorm R.params.side (R.depth + 1) f ≤ 1 → (upperSites f).Nonempty →
      2 ^ 10 * R.range ≤ D → 8 < D → Q.Nonempty → (∀ Y ∈ upperSites f, ∀ Y' ∈ Q, D ≤ supDist Y Y') →
      (∀ y ∈ lowerSites f, y ∉ B) → 1 ≤ e → IsGasTilt G A.score Q B e Yt →
      Integrable (gasSupportMean A G f) (tiltedGibbsLaw G Yt) ∧
      Integrable (gasSupportMean A G f) (G.gibbsLaw ∅) ∧
      |∫ σ, gasSupportMean A G f σ ∂(tiltedGibbsLaw G Yt) - G.expectation ∅ (gasSupportMean A G f)| ≤
        C * e * (K.C₀ * ((lowerSites f).card : ℝ)) *
          meanSiteScore (coarseLabelScore K.s₁ A.score) (upperSites f) G.state.1 G.state.2 *
          Real.exp (-(R.params.rt * D / 2 ^ 7))
end YangMills.Construction.ResponseInTheExpansion
end

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction
open Dobrushin StepGas StepSettings StepCosts RenormalizationStepParameters TorusFields TorusLumps CoreColumns BlockOffsets
  WeightedResponses ResponseInTheExpansion FreeEnergies LinearResponse
open BlockAverages hiding unitStep
namespace TiltedGasResponse
set_option linter.unusedSectionVars false
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
section Labels
theorem spinLabelScore_nonneg {s : R.labels.Ω → ℝ} (hs : ∀ w, 0 ≤ s w) (i : G.GasSpin)
    (y : TorusSite (n * R.params.side)) (v : G.SpinValue i) :
    0 ≤ spinLabelScore s G i y v := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.spinLabelScore_nonneg <;> assumption
theorem measurable_spinLabelScore {s : R.labels.Ω → ℝ} (hb : Measurable s) (i : G.GasSpin)
    (y : TorusSite (n * R.params.side)) :
    Measurable (spinLabelScore s G i y) := by
  classical
  unfold spinLabelScore
  refine Measurable.sumElim measurable_const ?_
  by_cases h : y ∈ i.1.2
  · simp only [h, dite_true]
    have h1 : Measurable fun w : G.SpinState i => (w.1 : SupportState i.1).2.1 :=
      measurable_fst.comp (measurable_snd.comp measurable_subtype_coe)
    exact hb.comp ((measurable_pi_apply _).comp h1)
  · simp only [h, dite_false]
    exact measurable_const
theorem spinLabelScore_vacant (s : R.labels.Ω → ℝ) (i : G.GasSpin) (y : TorusSite (n * R.params.side)) :
    spinLabelScore s G i y (G.pairConstraint.vacant i) = 0 := rfl
theorem spinLabelScore_of_not_mem {s : R.labels.Ω → ℝ} {i : G.GasSpin} {y : TorusSite (n * R.params.side)}
    (hy : y ∉ i.1.2) (v : G.SpinValue i) :
    spinLabelScore s G i y v = 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.spinLabelScore_eq_zero_of_not_mem <;> assumption
theorem sum_spinLabelScore_le_spinScore {A : ResponseSetup R} (hs : ∀ w, 0 ≤ A.score w)
    (B : Finset (TorusSite (n * R.params.side))) (i : G.GasSpin)
    (v : G.SpinValue i) : ∑ y ∈ B, spinLabelScore A.score G i y v ≤ spinScore A i v := by
  classical
  rcases v with u | w
  · simp [spinLabelScore, _root_.YangMills.Construction.WeightedResponses.spinScore]
  · have e1 : ∑ y ∈ B, spinLabelScore A.score G i y (Sum.inr w) =
        ∑ y ∈ B.filter (· ∈ i.1.2), spinLabelScore A.score G i y (Sum.inr w) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun y _ => ?_
      split_ifs with h
      · rfl
      · exact spinLabelScore_of_not_mem h _
    have e2 : spinScore A i (Sum.inr w) = ∑ y ∈ i.1.2, spinLabelScore A.score G i y (Sum.inr w) := by
      show ∑ z : i.1.2, A.score (w.1.2.1 z) = _
      rw [← Finset.sum_coe_sort i.1.2]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp [spinLabelScore, z.2]
    rw [e1, e2]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => (Finset.mem_filter.mp hy).2) fun y _ _ =>
      spinLabelScore_nonneg hs i y _
end Labels
section Tail
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
theorem lintegral_single_spin_le (hP : MeanOfProductStatement) (A : PairConstraint S) (m : ∀ i, Measure (S i))
    [∀ i, SigmaFinite (m i)] {W : (∀ i, S i) → ℝ} {z : I → ℝ} (hW : A.IsActivityBounded m W z)
    [IsProbabilityMeasure (A.gibbsLaw m W)] (i : I) {ψ : S i → ℝ} (hm : Measurable ψ) (h0 : ∀ v, 0 ≤ ψ v)
    (habs : ψ (A.vacant i) = 0) {e : ℝ} (he : 0 ≤ e)
    (hex : ∀ σ, A.IsAdmissible σ → ∫⁻ s in {A.vacant i}ᶜ, ENNReal.ofReal (ψ s) *
        A.weightDensity W (Function.update σ i s) ∂m i ≤
      ENNReal.ofReal e * A.weightDensity W (Function.update σ i (A.vacant i))) :
    ∫⁻ σ, ENNReal.ofReal (ψ (σ i)) ∂A.gibbsLaw m W ≤ ENNReal.ofReal e := by
  classical
  set g : ∀ j, S j → ℝ := Function.update (fun _ _ => (1 : ℝ)) i (fun v => 1 + ψ v) with hg
  set ee : I → ℝ := Function.update (fun _ => (0 : ℝ)) i e with hee
  have gi : ∀ v, g i v = 1 + ψ v := fun v => by simp [hg]
  have gj : ∀ j, j ≠ i → ∀ v, g j v = 1 := fun j hj v => by simp [hg, Function.update_of_ne hj]
  have ei : ee i = e := by simp [hee]
  have ej : ∀ j, j ≠ i → ee j = 0 := fun j hj => by simp [hee, Function.update_of_ne hj]
  have key := hP I S A m W z hW g ee
    (fun j => by
      by_cases hj : j = i
      · subst hj
        have : g j = fun v => 1 + ψ v := funext gi
        rw [this]
        exact measurable_const.add hm
      · have : g j = fun _ => 1 := funext (gj j hj)
        rw [this]
        exact measurable_const)
    (fun j v => by
      by_cases hj : j = i
      · subst hj
        rw [gi]
        linarith [h0 v]
      · rw [gj j hj])
    (fun j => by
      by_cases hj : j = i
      · subst hj
        rw [gi, habs, add_zero]
      · rw [gj j hj])
    (fun j => by
      by_cases hj : j = i
      · subst hj
        rw [ei]
        exact he
      · rw [ej j hj])
    (fun j σ hσ => by
      by_cases hj : j = i
      · subst hj
        rw [ei]
        refine le_trans (le_of_eq ?_) (hex σ hσ)
        refine lintegral_congr fun s => ?_
        rw [gi]
        congr 2
        ring
      · rw [ej j hj]
        simp only [ENNReal.ofReal_zero, zero_mul, nonpos_iff_eq_zero]
        have : ∀ s, ENNReal.ofReal (g j s - 1) = 0 := fun s => by rw [gj j hj]; simp
        simp [this])
  have e1 : ∀ σ : ∀ j, S j, ∏ j, ENNReal.ofReal (g j (σ j)) = 1 + ENNReal.ofReal (ψ (σ i)) := by
    intro σ
    rw [Finset.prod_eq_single i]
    · rw [gi, ENNReal.ofReal_add zero_le_one (h0 _), ENNReal.ofReal_one]
    · intro j _ hj
      rw [gj j hj]
      simp
    · exact fun hn => absurd (Finset.mem_univ i) hn
  have e2 : ∏ j, (1 + ee j) = 1 + e := by
    rw [Finset.prod_eq_single i]
    · rw [ei]
    · intro j _ hj
      rw [ej j hj]
      simp
    · exact fun hn => absurd (Finset.mem_univ i) hn
  simp only [e1] at key
  rw [e2, lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    ENNReal.ofReal_add zero_le_one he, ENNReal.ofReal_one] at key
  exact (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp key
end Tail
section Mass
variable {T : ParameterAssignment} {A : ResponseSetup R} {s : R.labels.Ω → ℝ} {Q : Finset (TorusSite n)}
  {B : Finset (TorusSite (n * R.params.side))} {e : ℝ} {Yt : G.Config → ℝ}
theorem isAdmissible_update_vacant {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ) (i : G.GasSpin) :
    G.pairConstraint.IsAdmissible (Function.update σ i (G.pairConstraint.vacant i)) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.isAdmissible_update_vacant <;> assumption
theorem lintegral_tilted_density_le (hs : ∀ w, 0 ≤ A.score w) {c : ℝ}
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (spinScore A i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    (ht : IsGasTilt G A.score Q B e Yt) (i : G.GasSpin) {ψ : G.SpinValue i → ℝ} {Cψ : ℝ} (hC : 0 ≤ Cψ)
    (hψ0 : ∀ v, 0 ≤ ψ v)
    (hψ : ∀ v, ψ v * Real.exp (∑ y ∈ B, spinLabelScore A.score G i y v) ≤ Cψ * Real.exp (spinScore A i v))
    {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ) :
    ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (ψ v) *
        G.pairConstraint.weightDensity (fun σ => G.weight σ * Yt σ) (Function.update σ i v)
          ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (3 * Cψ * G.spinActivity c i) *
        G.pairConstraint.weightDensity (fun σ => G.weight σ * Yt σ)
          (Function.update σ i (G.pairConstraint.vacant i)) := by
  classical
  have hadm := isAdmissible_update_vacant hσ i
  set σ₀ := Function.update σ i (G.pairConstraint.vacant i) with hσ₀
  set y₀ := Yt σ₀ with hy₀
  have hy0 : 0 < y₀ := ht.pos _ hadm
  have hz0 : 0 ≤ G.spinActivity c i := hw.activity_nonneg i
  have point : ∀ v, ENNReal.ofReal (ψ v) *
      G.pairConstraint.weightDensity (fun σ => G.weight σ * Yt σ) (Function.update σ i v) ≤
      ENNReal.ofReal (3 * Cψ * y₀) * (ENNReal.ofReal (Real.exp (spinScore A i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v)) := by
    intro v
    unfold PairConstraint.weightDensity
    by_cases ha : G.pairConstraint.IsAdmissible (Function.update σ i v)
    · rw [if_pos ha, if_pos ha]
      have hwt := hw.pos_of_admissible _ ha
      have hr := ht.update_le σ i v ha
      rw [← ENNReal.ofReal_mul (hψ0 v), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have k1 : ψ v * Yt (Function.update σ i v) ≤ 3 * y₀ * (Cψ * Real.exp (spinScore A i v)) := by
        calc ψ v * Yt (Function.update σ i v) ≤
              ψ v * (3 * Real.exp (∑ y ∈ B, spinLabelScore A.score G i y v) * y₀) :=
              mul_le_mul_of_nonneg_left hr (hψ0 v)
          _ = 3 * y₀ * (ψ v * Real.exp (∑ y ∈ B, spinLabelScore A.score G i y v)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hψ v) (by positivity)
      calc ψ v * (G.weight (Function.update σ i v) * Yt (Function.update σ i v))
          = G.weight (Function.update σ i v) * (ψ v * Yt (Function.update σ i v)) := by ring
        _ ≤ G.weight (Function.update σ i v) * (3 * y₀ * (Cψ * Real.exp (spinScore A i v))) :=
            mul_le_mul_of_nonneg_left k1 hwt.le
        _ = _ := by ring
    · rw [if_neg ha, if_neg ha]
      simp
  calc _ ≤ ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (3 * Cψ * y₀) *
          (ENNReal.ofReal (Real.exp (spinScore A i v)) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i v)) ∂(G.referenceMeasure ∅ i) :=
        lintegral_mono point
    _ = ENNReal.ofReal (3 * Cψ * y₀) * ∫⁻ v in {G.pairConstraint.vacant i}ᶜ,
          ENNReal.ofReal (Real.exp (spinScore A i v)) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (3 * Cψ * y₀) * (ENNReal.ofReal (G.spinActivity c i) *
          G.pairConstraint.weightDensity G.weight σ₀) := by
        gcongr
        exact paid i σ hσ
    _ = _ := by
        unfold PairConstraint.weightDensity
        rw [if_pos hadm, if_pos hadm, ← ENNReal.ofReal_mul hz0, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
theorem isActivityBounded_tilt (hs : ∀ w, 0 ≤ A.score w) {c : ℝ}
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (spinScore A i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    (ht : IsGasTilt G A.score Q B e Yt) :
    G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) (fun σ => G.weight σ * Yt σ)
      fun i => 3 * G.spinActivity c i := by
  refine ⟨hw.measurableSet_admissible, hw.measurable.mul ht.measurable,
    fun σ h => mul_pos (hw.pos_of_admissible σ h) (ht.pos σ h),
    hw.measurableSet_vacant, hw.measure_vacant, fun i => by have := hw.activity_nonneg i; positivity,
    fun i σ hσ => ?_⟩
  have := lintegral_tilted_density_le hs hw paid ht i (ψ := fun _ => 1) (Cψ := 1) zero_le_one
    (fun _ => zero_le_one)
    (fun v => by
      simp only [one_mul]
      exact Real.exp_le_exp.mpr (sum_spinLabelScore_le_spinScore hs B i v)) hσ
  simpa using this
theorem isGasTilt_one (he : 0 ≤ e) : IsGasTilt G s Q ∅ e (fun _ => 1) where
  measurable := measurable_const
  pos _ _ := one_pos
  update_le _ _ _ _ := by simp
  abs_update_sub_le _ _ _ _ _ _ _ := by
    simp only [sub_self, abs_zero, mul_one]
    exact mul_nonneg he (Real.exp_pos _).le
end Mass
section Means
variable {free : Finset (TorusBond (n * R.params.side))}
theorem chartDensity_eq_zero {s : ChartSetting R n} {η : FreeCoords s.free} (h : ¬ s.InBalls η) :
    chartDensity s η = 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.chartDensity_eq_zero <;> assumption
theorem settingMean_liveCaseFunction {s : ChartSetting R n}
    (hl : ∀ η, s.InBalls η → IsLiveState R.params R.coupling R.labelWeight (s.field η) s.support s.labelling)
    (bad : Finset (TorusBond (n * R.params.side))) (F : CaseFunction R n) :
    settingMean s bad (liveCaseFunction F) =
      weightedMean (chartDensity s) fun η => F (s.field η) s.support s.labelling bad s.bases := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.settingMean_liveCase <;> assumption
theorem integrable_mul_chartDensity {s : ChartSetting R n} (hd : Integrable (chartDensity s))
    {g : FreeCoords s.free → ℝ} (hg : Measurable g) {Q : ℝ} (hQ : ∀ η, s.InBalls η → |g η| ≤ Q) :
    Integrable fun η => g η * chartDensity s η := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.integrable_mul_chartDensity <;> assumption
theorem abs_weightedMean_le {s : ChartSetting R n} (hd : Integrable (chartDensity s))
    (hm : 0 < ∫ η, chartDensity s η)
    {g : FreeCoords s.free → ℝ} {Q : ℝ} (hQ : ∀ η, s.InBalls η → |g η| ≤ Q) :
    |weightedMean (chartDensity s) g| ≤ Q := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.abs_weightedMean_le <;> assumption
end Means
section Atoms
def siteResponseMean (A : ResponseSetup R) (G : GasGround R n)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (y : TorusSite (n * R.params.side))
    (σ : G.Config) : ℝ :=
  settingMean (configSetting G σ) (G.badBondsOf σ)
    (liveCaseFunction fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f)
def bondScoreMean (G : GasGround R n) (c : TorusBond n) (σ : G.Config) : ℝ :=
  settingMean (configSetting G σ) (G.badBondsOf σ)
    (liveCaseFunction fun W _ _ _ b => bondScore R.params R.coupling W G.coarse b c)
def configSiteScore (A : ResponseSetup R) (G : GasGround R n) (y : TorusSite (n * R.params.side))
    (σ : G.Config) : ℝ :=
  siteScore A.score (configSetting G σ).support (configSetting G σ).labelling y
structure TiltSetup (A : ResponseSetup R) (G : GasGround R n) : Prop where
  admissibleResponse : A.IsAdmissible
  params_admissible : R.params.Admissible
  side_odd : Odd R.params.side
  hullExpansion : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
    R.clusterFactor R.siteDensity
  isBlockSide : IsBlockTorusSide R.params (n * R.params.side)
  n₀_le : R.params.n₀ ≤ n
  functional_trivial_pos : 0 < R.functional (n * R.params.side) (trivialField (n * R.params.side))
  isAdmissible_setting : ∀ σ, G.pairConstraint.IsAdmissible σ → (configSetting G σ).IsAdmissible
  density_integrable : ∀ σ, G.pairConstraint.IsAdmissible σ →
    Integrable (chartDensity (configSetting G σ)) ∧ 0 < ∫ η, chartDensity (configSetting G σ) η
  settingsAgree : LocalSettingsAgree
  measurable_settingMean : ∀ F : CaseFunction R n, (∀ (Yt : Finset (TorusSite (n * R.params.side)))
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => F p.1 Yt p.2 bad b) →
    open Classical in Measurable fun σ : G.Config =>
      if G.pairConstraint.IsAdmissible σ then settingMean (configSetting G σ) (G.badBondsOf σ) F else 0
  coupling_ge : 1 ≤ R.params.coupling
  C₀_ge : 12 + 40 * R.params.coupling ≤ A.responseParams.C₀
  abs_bondScore_le : ∀ (W : TorusField (n * R.params.side)) (V : TorusField n) (b : BaseChoice R.params.side n)
    (c : TorusBond n), |bondScore R.params R.coupling W V b c| ≤ 2
  measurable_bondScore : ∀ (b : BaseChoice R.params.side n) (c : TorusBond n),
    Measurable fun p : TorusField (n * R.params.side) × TorusField n =>
      bondScore R.params R.coupling p.1 p.2 b c
  chart_close : ∀ (s s' : ChartSetting R n) (Y : TorusSite n) (m : ℕ), s.IsAdmissible → s'.IsAdmissible →
    SettingsAgreeNear s s' Y Y m →
    (R.range : ℝ) / (4 * R.params.side) ≤ m →
    (∀ o, o ∈ centredCube R.params.side →
      ∀ h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)),
      |chartResponse A s (fineSite R.params.side Y 0 o) h - chartResponse A s' (fineSite R.params.side Y 0 o) h| ≤
        (1 + chartSiteScore A s (fineSite R.params.side Y 0 o)) * Real.exp (-(R.params.rt * m / 2 ^ 5)) *
          weightNorm R.params.side R.depth h) ∧
    ∀ c : (Fin 4 → ℤ) × Fin 4, IsBondAtOrigin c →
      |chartBondScore s (bondFrom Y c) - chartBondScore s' (bondFrom Y c)| ≤ Real.exp (-(R.params.rt * m / 2 ^ 5))
variable {A : ResponseSetup R}
theorem TiltSetup.isLiveState (h : TiltSetup A G) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    (η : FreeCoords (configSetting G σ).free) (hη : (configSetting G σ).InBalls η) :
    IsLiveState R.params R.coupling R.labelWeight ((configSetting G σ).field η) (configSetting G σ).support
      (configSetting G σ).labelling := by
  have hs := h.isAdmissible_setting σ hσ
  have hh : IsHullState R.params (clusterRange R.coupling) ((configSetting G σ).field η)
      (configSetting G σ).support := hs.isHull η hη
  refine ⟨hh, ?_⟩
  rw [h.hullExpansion.form (n * R.params.side) h.isBlockSide _ _ _ hh]
  have hΦ : 0 < ∏ X ∈ chainComponents (clusterRange R.coupling) (configSetting G σ).support,
      R.clusterFactor (n * R.params.side) ((configSetting G σ).field η) (configSetting G σ).support
        (configSetting G σ).labelling X := by
    refine Finset.prod_pos fun X hX => ?_
    exact lt_of_le_of_ne (h.hullExpansion.factor_nonneg (n * R.params.side) h.isBlockSide _ _ _ X)
      (Ne.symm (hs.factor_ne_zero η hη X hX))
  have := h.functional_trivial_pos
  positivity
theorem TiltSetup.configSiteScore_nonneg (h : TiltSetup A G) (y : TorusSite (n * R.params.side)) (σ : G.Config) :
    0 ≤ configSiteScore A G y σ :=
  siteScore_nonneg h.admissibleResponse.price.nonneg _ _ _
theorem TiltSetup.siteResponseMean_eq (h : TiltSetup A G) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (y : TorusSite (n * R.params.side)) :
    siteResponseMean A G f y σ = chartResponse A (configSetting G σ) y f :=
  settingMean_liveCaseFunction (fun η hη => h.isLiveState hσ η hη) _ _
theorem TiltSetup.bondScoreMean_eq (h : TiltSetup A G) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    (c : TorusBond n) :
    bondScoreMean G c σ = chartBondScore (configSetting G σ) c :=
  settingMean_liveCaseFunction (fun η hη => h.isLiveState hσ η hη) _ _
theorem TiltSetup.abs_centeredHullResponse_le (h : TiltSetup A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (y : TorusSite (n * R.params.side))
    (η : FreeCoords (configSetting G σ).free) (hη : (configSetting G σ).InBalls η) :
    |centeredHullResponse A.cold A.hull (n * R.params.side) y ((configSetting G σ).field η)
        (configSetting G σ).support (configSetting G σ).labelling f| ≤
      A.responseParams.C₀ + configSiteScore A G y σ := by
  have h1 := h.admissibleResponse.bounds.size_hull (n * R.params.side) h.isBlockSide y _ _ _
    (h.isLiveState hσ η hη) f
  have hC : 0 ≤ A.responseParams.C₀ := by
    have h3 := h.coupling_ge
    have h4 := h.C₀_ge
    linarith
  have h2 : 0 ≤ A.responseParams.C₀ + configSiteScore A G y σ := add_nonneg hC (h.configSiteScore_nonneg y σ)
  calc _ ≤ _ := h1
    _ ≤ (A.responseParams.C₀ + configSiteScore A G y σ) * 1 := mul_le_mul_of_nonneg_left hsz h2
    _ = _ := mul_one _
theorem setGap_le {X X' : Finset (TorusSite n)} {y y' : TorusSite n} (hy : y ∈ X) (hy' : y' ∈ X') :
    setGap X X' ≤ _root_.YangMills.Construction.TorusFields.supDist y y' :=
  Nat.sInf_le ⟨y, hy, y', hy', rfl⟩
theorem exists_setGap_eq {X X' : Finset (TorusSite n)} (hX : X.Nonempty) (hX' : X'.Nonempty) :
    ∃ y ∈ X, ∃ y' ∈ X', _root_.YangMills.Construction.TorusFields.supDist y y' = setGap X X' := by apply _root_.YangMills.Construction.CoreColumns.setGap_attained <;> assumption
theorem core_nonempty (j : G.GasSpin) : j.1.core.Nonempty := by apply _root_.YangMills.Construction.StepGas.core_nonempty_of_gasSpin <;> assumption
theorem TiltSetup.settingsAgreeNear_update_vacant (h : TiltSetup A G) (σ : G.Config) (j : G.GasSpin)
    {Y : TorusSite n} {m : ℕ} (hg : m + 2 ≤ setGap {Y} j.1.core) :
    SettingsAgreeNear (configSetting G σ) (configSetting G (Function.update σ j (G.pairConstraint.vacant j)))
      Y Y m := by
  classical
  obtain ⟨a, ha⟩ := core_nonempty j
  have h1 : setGap {Y} j.1.core ≤ _root_.YangMills.Construction.TorusFields.supDist Y a := setGap_le (Finset.mem_singleton_self Y) ha
  have h2 := SettingShifts.two_mul_supDist_le Y a
  refine h.settingsAgree R n G σ _ Y m h.side_odd (by omega) fun i hi => ?_
  obtain ⟨e, he, hc⟩ := hi
  by_cases hij : i = j
  · subst hij
    exfalso
    have h3 : setGap {Y} i.1.core ≤ _root_.YangMills.Construction.TorusFields.supDist Y (Y + siteOfInt e) := setGap_le (Finset.mem_singleton_self Y) hc
    have h4 : _root_.YangMills.Construction.TorusFields.supDist Y (Y + siteOfInt e) ≤ m := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le Y e m fun l => by
      have h1 : |e l| ≤ (m : ℤ) := he l
      rw [Int.abs_eq_natAbs] at h1
      omega
    omega
  · rw [Function.update_of_ne hij]
theorem TiltSetup.measurableSet_isLiveState (h : TiltSetup A G) (Yt : Finset (TorusSite (n * R.params.side))) :
    MeasurableSet {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) |
      IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} := by
  classical
  have hb := (h.hullExpansion.borel (n * R.params.side) h.isBlockSide Yt).1
  have e : {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) |
      IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} =
      (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        if IsHullState R.params (clusterRange R.coupling) p.1 Yt then
          R.labelWeight (n * R.params.side) p.1 Yt p.2 else 0) ⁻¹' Set.Ioi 0 := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi, IsLiveState]
    by_cases hh : IsHullState R.params (clusterRange R.coupling) p.1 Yt
    · simp [hh]
    · simp [hh]
  rw [e]
  exact hb measurableSet_Ioi
theorem TiltSetup.measurable_liveCase_hull (h : TiltSetup A G)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (y : TorusSite (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      liveCaseFunction (R := R) (n := n)
        (fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f) p.1 Yt p.2 bad b := by
  classical
  have h1 := h.admissibleResponse.bounds.hull_borel (n * R.params.side) h.isBlockSide y Yt f
  have h2 := h.measurableSet_isLiveState Yt
  have h3 : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then
        A.cold (n * R.params.side) y (trivialField (n * R.params.side)) f else 0 :=
    Measurable.ite h2 measurable_const measurable_const
  have h4 := h1.sub h3
  have e : (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      liveCaseFunction (R := R) (n := n)
        (fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f) p.1 Yt p.2 bad b) =
      ((fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then
          A.hull (n * R.params.side) y p.1 Yt p.2 f else 0) -
      fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then
          A.cold (n * R.params.side) y (trivialField (n * R.params.side)) f else 0) := by
    funext p
    simp only [Pi.sub_apply, liveCaseFunction]
    by_cases hl : IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2
    · simp only [if_pos hl]
      rfl
    · simp only [if_neg hl, sub_zero]
  rw [e]
  exact h4
theorem TiltSetup.measurable_liveCase_bondScore (h : TiltSetup A G) (c : TorusBond n)
    (Yt : Finset (TorusSite (n * R.params.side)))
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      liveCaseFunction (R := R) (n := n) (fun W _ _ _ b => bondScore R.params R.coupling W G.coarse b c)
        p.1 Yt p.2 bad b := by
  classical
  have h1 : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      bondScore R.params R.coupling p.1 G.coarse b c := by
    have h2 : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => (p.1, G.coarse) :=
      measurable_fst.prodMk measurable_const
    have h3 := (h.measurable_bondScore b c).comp h2
    exact h3
  exact Measurable.ite (h.measurableSet_isLiveState Yt) h1 measurable_const
theorem TiltSetup.measurable_siteResponseMean (h : TiltSetup A G)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (y : TorusSite (n * R.params.side)) :
    open Classical in Measurable fun σ =>
      if G.pairConstraint.IsAdmissible σ then siteResponseMean A G f y σ else 0 :=
  h.measurable_settingMean _ fun Yt bad b => h.measurable_liveCase_hull f y Yt bad b
theorem TiltSetup.measurable_bondScoreMean (h : TiltSetup A G) (c : TorusBond n) :
    open Classical in Measurable fun σ => if G.pairConstraint.IsAdmissible σ then bondScoreMean G c σ else 0 :=
  h.measurable_settingMean _ fun Yt bad b => h.measurable_liveCase_bondScore c Yt bad b
theorem TiltSetup.integrable_hull_mul_chartDensity (h : TiltSetup A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (y : TorusSite (n * R.params.side)) :
    Integrable fun η => centeredHullResponse A.cold A.hull (n * R.params.side) y ((configSetting G σ).field η)
      (configSetting G σ).support (configSetting G σ).labelling f * chartDensity (configSetting G σ) η := by
  classical
  set s := configSetting G σ with hs
  set g : FreeCoords s.free → ℝ := fun η => liveCaseFunction (R := R) (n := n)
    (fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f)
    (s.field η) s.support s.labelling (G.badBondsOf σ) s.bases with hg
  have hm : Measurable g := by
    have h1 := h.measurable_liveCase_hull f y s.support (G.badBondsOf σ) s.bases
    have h2 : Measurable fun η : FreeCoords s.free => (s.field η, s.labelling) :=
      (ClusterExpansionOfAStep.ChartSetting.measurable_field s).prodMk measurable_const
    have h3 := h1.comp h2
    exact h3
  have hgeq : ∀ η, s.InBalls η →
      g η = centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η) s.support s.labelling f :=
    fun η hη => by
      simp only [hg, liveCaseFunction]
      exact if_pos (h.isLiveState hσ η hη)
  have hi := integrable_mul_chartDensity (h.density_integrable σ hσ).1 hm
    (Q := A.responseParams.C₀ + configSiteScore A G y σ) fun η hη => by
      rw [hgeq η hη]
      exact h.abs_centeredHullResponse_le hσ hsz y η hη
  refine hi.congr (Filter.Eventually.of_forall fun η => ?_)
  by_cases hη : s.InBalls η
  · show g η * _ = _
    rw [hgeq η hη]
  · have h0 : chartDensity (configSetting G σ) η = 0 := chartDensity_eq_zero hη
    show g η * _ = _ * _
    rw [h0, mul_zero, mul_zero]
theorem TiltSetup.integrable_bondScore_mul_chartDensity (h : TiltSetup A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) (c : TorusBond n) :
    Integrable fun η => bondScore R.params R.coupling ((configSetting G σ).field η) (configSetting G σ).coarse
      (configSetting G σ).bases c * chartDensity (configSetting G σ) η := by
  set s := configSetting G σ with hs
  have hm : Measurable fun η : FreeCoords s.free => bondScore R.params R.coupling (s.field η) s.coarse s.bases c := by
    have h2 : Measurable fun η : FreeCoords s.free => (s.field η, s.coarse) :=
      (ClusterExpansionOfAStep.ChartSetting.measurable_field s).prodMk measurable_const
    have h3 := (h.measurable_bondScore s.bases c).comp h2
    exact h3
  exact integrable_mul_chartDensity (h.density_integrable σ hσ).1 hm (Q := 2) fun η _ =>
    h.abs_bondScore_le _ _ _ _
theorem weightedMean_centeredSupportResponse {s : ChartSetting R n}
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)}
    (bad : Finset (TorusBond (n * R.params.side))) (hdi : Integrable (chartDensity s))
    (hdm : 0 < ∫ η, chartDensity s η)
    (ih : ∀ y, Integrable fun η => centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η) s.support
      s.labelling f * chartDensity s η)
    (is : ∀ c, Integrable fun η => bondScore R.params R.coupling (s.field η) s.coarse s.bases c * chartDensity s η) :
    weightedMean (chartDensity s)
        (fun η => centeredSupportResponse A s.coarse f (s.field η) s.support s.labelling bad s.bases) =
      ∑ y ∈ lowerSites f, weightedMean (chartDensity s)
          (fun η => centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η) s.support s.labelling f) +
        R.params.coupling / 2 * A.coeff * ∑ Y ∈ upperSites f, blockMean R.params.side (R.depth + 1) n Y f *
          ∑ i : Fin 4, (weightedMean (chartDensity s)
              (fun η => bondScore R.params R.coupling (s.field η) s.coarse s.bases (Y, i)) +
            weightedMean (chartDensity s)
              (fun η => bondScore R.params R.coupling (s.field η) s.coarse s.bases (Y - unitStep n i, i))) -
        caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.weightedMean_centeredSupportResponse <;> assumption
theorem TiltSetup.gasSupportMean_eq (h : TiltSetup A G) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1) :
    gasSupportMean A G f σ = ∑ y ∈ lowerSites f, siteResponseMean A G f y σ +
      R.params.coupling / 2 * A.coeff * ∑ Y ∈ upperSites f, blockMean R.params.side (R.depth + 1) n Y f *
        ∑ i : Fin 4, (bondScoreMean G (Y, i) σ + bondScoreMean G (Y - unitStep n i, i) σ) -
      caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) := by
  classical
  obtain ⟨hdi, hdm⟩ := h.density_integrable σ hσ
  have e0 : gasSupportMean A G f σ = weightedMean (chartDensity (configSetting G σ)) fun η =>
      centeredSupportResponse A (configSetting G σ).coarse f ((configSetting G σ).field η)
        (configSetting G σ).support (configSetting G σ).labelling (G.badBondsOf σ) (configSetting G σ).bases :=
    settingMean_liveCaseFunction (fun η hη => h.isLiveState hσ η hη) _ _
  have e2 : ∀ y, weightedMean (chartDensity (configSetting G σ))
      (fun η => centeredHullResponse A.cold A.hull (n * R.params.side) y
        ((configSetting G σ).field η) (configSetting G σ).support (configSetting G σ).labelling f) =
        siteResponseMean A G f y σ :=
    fun y => (settingMean_liveCaseFunction (s := configSetting G σ) (fun η hη => h.isLiveState hσ η hη)
      (G.badBondsOf σ)
      (fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f)).symm
  have e3 : ∀ c, weightedMean (chartDensity (configSetting G σ))
      (fun η => bondScore R.params R.coupling ((configSetting G σ).field η)
        (configSetting G σ).coarse (configSetting G σ).bases c) = bondScoreMean G c σ :=
    fun c => (settingMean_liveCaseFunction (s := configSetting G σ) (fun η hη => h.isLiveState hσ η hη)
      (G.badBondsOf σ)
      (fun W _ _ _ b => bondScore R.params R.coupling W G.coarse b c)).symm
  rw [e0, weightedMean_centeredSupportResponse (G.badBondsOf σ) hdi hdm
    (fun y => h.integrable_hull_mul_chartDensity hσ hsz y)
    (fun c => h.integrable_bondScore_mul_chartDensity hσ c)]
  rw [Finset.sum_congr rfl fun y _ => e2 y]
  congr 3
  refine Finset.sum_congr rfl fun Y _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [e3, e3]
def siteLabelSum (A : ResponseSetup R) (G : GasGround R n) (y : TorusSite (n * R.params.side)) (σ : G.Config) : ℝ :=
  ∑ i, spinLabelScore A.score G i y (σ i)
theorem TiltSetup.configSiteScore_le (h : TiltSetup A G) (y : TorusSite (n * R.params.side)) (σ : G.Config) :
    configSiteScore A G y σ ≤ recordedSiteScore A G y + siteLabelSum A G y σ :=
  siteScore_configSetting_le h.admissibleResponse.price.nonneg σ y
theorem TiltSetup.abs_siteResponseMean_le (h : TiltSetup A G) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (y : TorusSite (n * R.params.side)) :
    |siteResponseMean A G f y σ| ≤ A.responseParams.C₀ + configSiteScore A G y σ := by
  obtain ⟨hdi, hdm⟩ := h.density_integrable σ hσ
  have e : siteResponseMean A G f y σ = weightedMean (chartDensity (configSetting G σ))
      (fun η => centeredHullResponse A.cold A.hull (n * R.params.side) y
        ((configSetting G σ).field η) (configSetting G σ).support (configSetting G σ).labelling f) :=
    settingMean_liveCaseFunction (s := configSetting G σ) (fun η hη => h.isLiveState hσ η hη) (G.badBondsOf σ)
      (fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f)
  rw [e]
  exact abs_weightedMean_le hdi hdm fun η hη => h.abs_centeredHullResponse_le hσ hsz y η hη
theorem TiltSetup.abs_bondScoreMean_le (h : TiltSetup A G) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    (c : TorusBond n) :
    |bondScoreMean G c σ| ≤ 2 := by
  obtain ⟨hdi, hdm⟩ := h.density_integrable σ hσ
  have e : bondScoreMean G c σ = weightedMean (chartDensity (configSetting G σ))
      (fun η => bondScore R.params R.coupling ((configSetting G σ).field η)
        G.coarse (configSetting G σ).bases c) :=
    settingMean_liveCaseFunction (s := configSetting G σ) (fun η hη => h.isLiveState hσ η hη) (G.badBondsOf σ)
      (fun W _ _ _ b => bondScore R.params R.coupling W G.coarse b c)
  rw [e]
  exact abs_weightedMean_le hdi hdm fun η _ => h.abs_bondScore_le _ _ _ _
theorem update_vacant_eq {σ σ' : G.Config} {j : G.GasSpin} (hd : ∀ k, k ≠ j → σ k = σ' k) :
    Function.update σ j (G.pairConstraint.vacant j) = Function.update σ' j (G.pairConstraint.vacant j) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.update_vacant_eq <;> assumption
theorem TiltSetup.abs_siteResponseMean_sub_le (h : TiltSetup A G) {σ σ' : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) (hσ' : G.pairConstraint.IsAdmissible σ')
    {j : G.GasSpin} (hd : ∀ k, k ≠ j → σ k = σ' k) {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)}
    (hsz : weightNorm R.params.side R.depth f ≤ 1) {y : TorusSite (n * R.params.side)} {m : ℕ}
    (hm : (R.range : ℝ) / (4 * R.params.side) ≤ m)
    (hg : m + 2 ≤ setGap {parentBlock R.params.side y} j.1.core) :
    |siteResponseMean A G f y σ - siteResponseMean A G f y σ'| ≤
      (2 + configSiteScore A G y σ + configSiteScore A G y σ') * Real.exp (-(R.params.rt * m / 2 ^ 5)) := by
  obtain ⟨o, ho, hyo⟩ := exists_fineSite_of_parentBlock h.side_odd (parentBlock R.params.side y) y rfl
  set σ₀ := Function.update σ j (G.pairConstraint.vacant j) with hσ₀
  have h0 : G.pairConstraint.IsAdmissible σ₀ := isAdmissible_update_vacant hσ j
  have a1 := h.settingsAgreeNear_update_vacant (A := A) σ j hg
  have a2 := h.settingsAgreeNear_update_vacant (A := A) σ' j hg
  rw [← update_vacant_eq hd] at a2
  have b1 := (h.chart_close _ _ _ m (h.isAdmissible_setting σ hσ) (h.isAdmissible_setting _ h0) a1 hm).1 o ho f
  have b2 := (h.chart_close _ _ _ m (h.isAdmissible_setting σ' hσ') (h.isAdmissible_setting _ h0) a2 hm).1 o ho f
  rw [← hyo] at b1 b2
  rw [h.siteResponseMean_eq hσ, h.siteResponseMean_eq hσ']
  set E := Real.exp (-(R.params.rt * m / 2 ^ 5)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have c1 : (1 + chartSiteScore A (configSetting G σ) y) * E * weightNorm R.params.side R.depth f ≤
      (1 + configSiteScore A G y σ) * E := by
    have : 0 ≤ (1 + configSiteScore A G y σ) * E := mul_nonneg (by linarith [h.configSiteScore_nonneg y σ]) hE0
    calc _ ≤ (1 + configSiteScore A G y σ) * E * 1 := mul_le_mul_of_nonneg_left hsz this
      _ = _ := mul_one _
  have c2 : (1 + chartSiteScore A (configSetting G σ') y) * E * weightNorm R.params.side R.depth f ≤
      (1 + configSiteScore A G y σ') * E := by
    have : 0 ≤ (1 + configSiteScore A G y σ') * E := mul_nonneg (by linarith [h.configSiteScore_nonneg y σ']) hE0
    calc _ ≤ (1 + configSiteScore A G y σ') * E * 1 := mul_le_mul_of_nonneg_left hsz this
      _ = _ := mul_one _
  calc _ ≤ |chartResponse A (configSetting G σ) y f - chartResponse A (configSetting G σ₀) y f| +
        |chartResponse A (configSetting G σ') y f - chartResponse A (configSetting G σ₀) y f| := by
        rw [abs_sub_comm (chartResponse A (configSetting G σ') y f)]
        exact abs_sub_le _ _ _
    _ ≤ (1 + configSiteScore A G y σ) * E + (1 + configSiteScore A G y σ') * E :=
        add_le_add (b1.trans c1) (b2.trans c2)
    _ = _ := by ring
theorem TiltSetup.abs_bondScoreMean_sub_le (h : TiltSetup A G) {σ σ' : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) (hσ' : G.pairConstraint.IsAdmissible σ')
    {j : G.GasSpin} (hd : ∀ k, k ≠ j → σ k = σ' k) {Y : TorusSite n} {m : ℕ}
    (hm : (R.range : ℝ) / (4 * R.params.side) ≤ m) (hg : m + 2 ≤ setGap {Y} j.1.core)
    {c : (Fin 4 → ℤ) × Fin 4} (hc : IsBondAtOrigin c) :
    |bondScoreMean G (bondFrom Y c) σ - bondScoreMean G (bondFrom Y c) σ'| ≤
      2 * Real.exp (-(R.params.rt * m / 2 ^ 5)) := by
  set σ₀ := Function.update σ j (G.pairConstraint.vacant j) with hσ₀
  have h0 : G.pairConstraint.IsAdmissible σ₀ := isAdmissible_update_vacant hσ j
  have a1 := h.settingsAgreeNear_update_vacant (A := A) σ j hg
  have a2 := h.settingsAgreeNear_update_vacant (A := A) σ' j hg
  rw [← update_vacant_eq hd] at a2
  have b1 := (h.chart_close _ _ _ m (h.isAdmissible_setting σ hσ) (h.isAdmissible_setting _ h0) a1 hm).2 c hc
  have b2 := (h.chart_close _ _ _ m (h.isAdmissible_setting σ' hσ') (h.isAdmissible_setting _ h0) a2 hm).2 c hc
  rw [h.bondScoreMean_eq hσ, h.bondScoreMean_eq hσ']
  calc _ ≤ |chartBondScore (configSetting G σ) (bondFrom Y c) - chartBondScore (configSetting G σ₀) (bondFrom Y c)| +
        |chartBondScore (configSetting G σ') (bondFrom Y c) -
          chartBondScore (configSetting G σ₀) (bondFrom Y c)| := by
        rw [abs_sub_comm (chartBondScore (configSetting G σ') (bondFrom Y c))]
        exact abs_sub_le _ _ _
    _ ≤ _ := by linarith
end Atoms
section Compare
variable {A : ResponseSetup R} {s : R.labels.Ω → ℝ} {Q : Finset (TorusSite n)}
  {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ} {Yt : G.Config → ℝ}
def columnRate (R : StepSetup) : ℝ := R.params.rt / 2 ^ 6
def tiltNearFactor (R : StepSetup) : ℝ :=
  Real.exp (2 * columnRate R * ((R.range : ℝ) / (4 * R.params.side) + 3))
def localNearFactor (R : StepSetup) : ℝ :=
  Real.exp (columnRate R * ((R.range : ℝ) / (4 * R.params.side) + 4))
def tiltDistance (G : GasGround R n) (c e : ℝ) (Q : Finset (TorusSite n)) (i : G.GasSpin) : ℝ :=
  8 * e * G.spinActivity c i * tiltNearFactor R * Real.exp (-(2 * columnRate R * (setGap Q i.1.core : ℝ)))
theorem setGap_le_setGap_singleton {Y : TorusSite n} (hY : Y ∈ Q) (i : G.GasSpin) :
    setGap Q i.1.core ≤ setGap {Y} i.1.core := by
  obtain ⟨y, hy, a, ha, e⟩ := exists_setGap_eq (X := {Y}) (Finset.singleton_nonempty Y) (core_nonempty i)
  rw [← e, Finset.mem_singleton.mp hy]
  exact setGap_le hY ha
theorem tilt_dichotomy (ht : IsGasTilt G s Q B e Yt) (he : 1 ≤ e) (hrt : 0 < R.params.rt)
    {z : G.GasSpin → ℝ} (hz : z = G.spinActivity c) (hz0 : ∀ i, 0 ≤ z i) (i : G.GasSpin) :
    2 * (z i + 3 * z i) ≤ tiltDistance G c e Q i ∨ ∃ e' : ℝ, 0 ≤ e' ∧ e' ≤ 1 ∧
      8 * e' * z i ≤ tiltDistance G c e Q i ∧
      ∀ (σ : G.Config) (v : G.SpinValue i), G.pairConstraint.IsAdmissible (Function.update σ i v) →
        v ≠ G.pairConstraint.vacant i →
        |Yt (Function.update σ i v) - Yt (Function.update σ i (G.pairConstraint.vacant i))| ≤
          e' * Yt (Function.update σ i (G.pairConstraint.vacant i)) := by
  set l := setGap Q i.1.core with hl
  set m := l - 2 with hm
  set L4 : ℝ := (R.range : ℝ) / (4 * R.params.side) with hL4
  have hL40 : 0 ≤ L4 := by positivity
  have hrp : 0 < columnRate R := by unfold columnRate; positivity
  have hz' : G.spinActivity c i = z i := by rw [hz]
  have hb : tiltDistance G c e Q i =
      8 * e * z i * (tiltNearFactor R * Real.exp (-(2 * columnRate R * (l : ℝ)))) := by
    unfold tiltDistance
    rw [hz']
    ring
  have hBbl : 2 ≤ l → Real.exp (-(R.params.rt * m / 2 ^ 5)) ≤
      tiltNearFactor R * Real.exp (-(2 * columnRate R * (l : ℝ))) := by
    intro h2
    unfold tiltNearFactor
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e1 : (l : ℝ) = m + 2 := by
      have : l = m + 2 := by omega
      rw [this]
      push_cast
      ring
    have e2 : R.params.rt = 2 ^ 6 * columnRate R := by unfold columnRate; ring
    rw [e1, e2]
    have : 0 ≤ columnRate R * L4 := by positivity
    nlinarith
  by_cases hc : 2 ≤ l ∧ L4 ≤ m ∧ e * Real.exp (-(R.params.rt * m / 2 ^ 5)) ≤ 1
  · obtain ⟨h2, hmr, he1⟩ := hc
    refine Or.inr ⟨e * Real.exp (-(R.params.rt * m / 2 ^ 5)), by positivity, he1, ?_, fun σ v ha _ => ?_⟩
    · rw [hb]
      have := hBbl h2
      have h8 : 0 ≤ 8 * e * z i := by have := hz0 i; positivity
      calc 8 * (e * Real.exp (-(R.params.rt * m / 2 ^ 5))) * z i
          = 8 * e * z i * Real.exp (-(R.params.rt * m / 2 ^ 5)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this h8
    · exact ht.abs_update_sub_le σ i v m ha hmr fun Y hY => by
        have := setGap_le_setGap_singleton hY i
        omega
  · left
    have hkey : 1 ≤ e * (tiltNearFactor R * Real.exp (-(2 * columnRate R * (l : ℝ)))) := by
      by_cases h2 : 2 ≤ l ∧ L4 ≤ m
      · have h3 : 1 < e * Real.exp (-(R.params.rt * m / 2 ^ 5)) := by
          by_contra hn
          exact hc ⟨h2.1, h2.2, not_lt.mp hn⟩
        have h4 := hBbl h2.1
        have : e * Real.exp (-(R.params.rt * m / 2 ^ 5)) ≤
            e * (tiltNearFactor R * Real.exp (-(2 * columnRate R * (l : ℝ)))) :=
          mul_le_mul_of_nonneg_left h4 (by linarith)
        linarith
      · have h3 : (l : ℝ) ≤ L4 + 3 := by
          by_cases h5 : 2 ≤ l
          · have h6 : (m : ℝ) < L4 := by
              by_contra hn
              exact h2 ⟨h5, not_lt.mp hn⟩
            have e1 : (l : ℝ) = m + 2 := by
              have : l = m + 2 := by omega
              rw [this]
              push_cast
              ring
            linarith
          · have : (l : ℝ) ≤ 2 := by
              have : l ≤ 2 := by omega
              exact_mod_cast this
            linarith
        have h4 : 1 ≤ tiltNearFactor R * Real.exp (-(2 * columnRate R * (l : ℝ))) := by
          unfold tiltNearFactor
          rw [← Real.exp_add]
          apply Real.one_le_exp
          nlinarith
        nlinarith
    rw [hb]
    have h8 : 0 ≤ 8 * z i := by have := hz0 i; positivity
    calc 2 * (z i + 3 * z i) = 8 * z i * 1 := by ring
      _ ≤ 8 * z i * (e * (tiltNearFactor R * Real.exp (-(2 * columnRate R * (l : ℝ))))) :=
          mul_le_mul_of_nonneg_left hkey h8
      _ = _ := by ring
theorem le_setGap_add_diameter {Y : TorusSite n} {D : ℕ} (hQ : Q.Nonempty) (hD : ∀ Y' ∈ Q, D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y')
    (i : G.GasSpin) :
    D ≤ setGap {Y} i.1.core + siteDiameter i.1.core + setGap Q i.1.core := by
  obtain ⟨y, hy, a, ha, e₁⟩ := exists_setGap_eq (X := {Y}) (Finset.singleton_nonempty Y) (core_nonempty i)
  obtain ⟨Y', hY', a', ha', e₂⟩ := exists_setGap_eq hQ (core_nonempty i)
  rw [Finset.mem_singleton.mp hy] at e₁
  have h1 := hD Y' hY'
  have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle Y a Y'
  have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle a a' Y'
  have h4 : _root_.YangMills.Construction.TorusFields.supDist a a' ≤ siteDiameter i.1.core := by
    unfold siteDiameter
    exact (Finset.le_sup (f := fun z => _root_.YangMills.Construction.TorusFields.supDist a z) ha').trans
      (Finset.le_sup (f := fun y => i.1.core.sup fun z => _root_.YangMills.Construction.TorusFields.supDist y z) ha)
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm a' Y'] at h3
  omega
theorem coreWeight_mul_le_aux {N g l dm Dr r z e b : ℝ} (hN : 1 ≤ N) (hg : 0 ≤ g) (hl : 0 ≤ l) (hdm : 0 ≤ dm)
    (hr : 0 ≤ r) (hz : 0 ≤ z) (he : 0 ≤ e) (hb : 0 ≤ b) (hD : Dr ≤ g + dm + l) (rt : ℝ)
    (hrt : r ≤ 2 ^ 6 * rt / 2 ^ 6) :
    N * Real.exp (-(r * g)) * (8 * e * z * b * Real.exp (-(2 * r * l))) ≤
      (8 * e * b * Real.exp (-(3 / 4 * r * Dr))) * (z * N ^ 4 * Real.exp (2 * rt * dm)) *
        Real.exp (-(r / 4 * g)) := by
  have hN4 : N ≤ N ^ 4 := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ 4 := pow_le_pow_right₀ hN (by norm_num)
  have hexp : Real.exp (-(r * g)) * Real.exp (-(2 * r * l)) ≤
      Real.exp (-(3 / 4 * r * Dr)) * Real.exp (2 * rt * dm) * Real.exp (-(r / 4 * g)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : 3 / 4 * r * Dr ≤ 3 / 4 * r * (g + dm + l) := by
      apply mul_le_mul_of_nonneg_left hD (by positivity)
    have h2 : r * dm ≤ rt * dm := by
      have : r ≤ rt := by linarith
      exact mul_le_mul_of_nonneg_right this hdm
    have h3 : 0 ≤ r * l := mul_nonneg hr hl
    have h4 : 0 ≤ r * dm := mul_nonneg hr hdm
    nlinarith
  have hpos : 0 ≤ 8 * e * z * b := by positivity
  calc N * Real.exp (-(r * g)) * (8 * e * z * b * Real.exp (-(2 * r * l)))
      = (8 * e * z * b) * N * (Real.exp (-(r * g)) * Real.exp (-(2 * r * l))) := by ring
    _ ≤ (8 * e * z * b) * N ^ 4 * (Real.exp (-(3 / 4 * r * Dr)) * Real.exp (2 * rt * dm) *
          Real.exp (-(r / 4 * g))) := by
        have h0 : 0 ≤ Real.exp (-(r * g)) * Real.exp (-(2 * r * l)) := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left hN4 hpos) hexp h0 (by positivity)
    _ = _ := by ring
theorem sum_coreWeight_mul_tiltDistance_le (hgas : GasSumNearBlockBound) (hfit : R.params.Admissible)
    (hc0 : 0 < c) (hcf : R.params.RangeFloor c)
    (hy : R.params.y₁ ≤ R.coupling) (he : 0 ≤ e) (hrt : 0 < R.params.rt) {Y : TorusSite n} {D : ℕ}
    (hQ : Q.Nonempty) (hD : ∀ Y' ∈ Q, D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y') (hz0 : ∀ i, 0 ≤ G.spinActivity c i) :
    ∑ i, G.coreWeightFrom Y i * tiltDistance G c e Q i ≤
      (8 * e * tiltNearFactor R * Real.exp (-(3 / 4 * columnRate R * D))) * Real.exp (-(8 * c * R.coupling)) *
        (2 / (1 - Real.exp (-(columnRate R / 4 / 4)))) ^ 4 := by
  have hrp : 0 < columnRate R := by unfold columnRate; positivity
  have hBb : 0 ≤ tiltNearFactor R := (Real.exp_pos _).le
  refine hgas R n G c (columnRate R / 4) _ Y Finset.univ _ hfit hc0 hcf hy (by positivity) (by positivity)
    fun i _ => ?_
  have hN : (1 : ℝ) ≤ (i.1.core.card : ℝ) := by exact_mod_cast (core_nonempty i).card_pos
  have hg := le_setGap_add_diameter (i := i) hQ hD
  have hg' : (D : ℝ) ≤ (setGap {Y} i.1.core : ℝ) + (i.1.coreDiam : ℝ) + (setGap Q i.1.core : ℝ) := by
    exact_mod_cast hg
  have := coreWeight_mul_le_aux (r := columnRate R) (z := G.spinActivity c i) (e := e) (b := tiltNearFactor R)
    hN (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hrp.le (hz0 i) he hBb hg' R.params.rt (by unfold columnRate; linarith [hrt])
  have hrpd : R.params.rt / 2 ^ 6 = columnRate R := rfl
  simpa [GasGround.coreWeightFrom, coreWeight, tiltDistance, mul_assoc, hrpd] using this
end Compare
section Local
variable {A : ResponseSetup R} {Q : Finset (TorusSite n)} {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ}
  {Yt : G.Config → ℝ}
theorem coreWeightFrom_pos (Y : TorusSite n) (j : G.GasSpin) : 0 < G.coreWeightFrom Y j := by apply _root_.YangMills.Construction.GasComparison.coreWeightFrom_pos <;> assumption
theorem oscillationBound_of_far (hrt : 0 < R.params.rt) {Y : TorusSite n} {H : G.Config → ℝ} {Mb Mf : ℝ}
    (hMb : 0 ≤ Mb) (hMf : 0 ≤ Mf)
    (hb : ∀ σ, |H σ| ≤ Mb)
    (hfar : ∀ (j : G.GasSpin) (σ σ' : G.Config), G.pairConstraint.IsAdmissible σ →
      G.pairConstraint.IsAdmissible σ' →
      (∀ k, k ≠ j → σ k = σ' k) → ∀ m : ℕ, (R.range : ℝ) / (4 * R.params.side) ≤ m →
      m + 2 ≤ setGap {Y} j.1.core →
      |H σ - H σ'| ≤ Mf * Real.exp (-(R.params.rt * m / 2 ^ 5))) :
    G.pairConstraint.OscillationBound H fun j => (2 * Mb + Mf) * localNearFactor R * G.coreWeightFrom Y j := by
  have hrp : 0 < columnRate R := by unfold columnRate; positivity
  have hBs : 0 < localNearFactor R := Real.exp_pos _
  refine ⟨fun j => mul_nonneg (by positivity) (coreWeightFrom_pos Y j).le, fun j σ σ' hσ hσ' hd => ?_⟩
  set g := setGap {Y} j.1.core with hg
  set L4 : ℝ := (R.range : ℝ) / (4 * R.params.side) with hL4
  have hL40 : 0 ≤ L4 := by positivity
  have hN : (1 : ℝ) ≤ (j.1.core.card : ℝ) := by exact_mod_cast (core_nonempty j).card_pos
  have hseen : Real.exp (-(columnRate R * (g : ℝ))) ≤ G.coreWeightFrom Y j := by
    show _ ≤ (j.1.core.card : ℝ) * Real.exp (-(R.params.rt / 2 ^ 6 * (setGap {Y} j.1.core : ℝ)))
    have : columnRate R = R.params.rt / 2 ^ 6 := rfl
    rw [← this, ← hg]
    nlinarith [Real.exp_pos (-(columnRate R * (g : ℝ)))]
  by_cases hc : 2 ≤ g ∧ L4 ≤ ((g - 2 : ℕ) : ℝ)
  · have e1 : (g : ℝ) = ((g - 2 : ℕ) : ℝ) + 2 := by
      have : g = (g - 2) + 2 := by omega
      conv_lhs => rw [this]
      push_cast
      ring
    have h1 := hfar j σ σ' hσ hσ' hd (g - 2) hc.2 (by omega)
    have h2 : Real.exp (-(R.params.rt * ((g - 2 : ℕ) : ℝ) / 2 ^ 5)) ≤
        localNearFactor R * Real.exp (-(columnRate R * (g : ℝ))) := by
      unfold localNearFactor
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have e2 : R.params.rt = 2 ^ 6 * columnRate R := by unfold columnRate; ring
      rw [e1, e2]
      have : 0 ≤ columnRate R * L4 := by positivity
      have h3 : 0 ≤ columnRate R * ((g - 2 : ℕ) : ℝ) := by positivity
      push_cast
      nlinarith
    calc _ ≤ _ := h1
      _ ≤ Mf * (localNearFactor R * G.coreWeightFrom Y j) := mul_le_mul_of_nonneg_left (h2.trans
          (mul_le_mul_of_nonneg_left hseen hBs.le)) hMf
      _ ≤ _ := by
          have : 0 ≤ localNearFactor R * G.coreWeightFrom Y j :=
            mul_nonneg hBs.le (coreWeightFrom_pos Y j).le
          nlinarith
  · have h3 : (g : ℝ) ≤ L4 + 2 := by
      by_cases h5 : 2 ≤ g
      · have h6 : ((g - 2 : ℕ) : ℝ) < L4 := by
          by_contra hn
          exact hc ⟨h5, not_lt.mp hn⟩
        have e1 : (g : ℝ) = ((g - 2 : ℕ) : ℝ) + 2 := by
          have : g = (g - 2) + 2 := by omega
          conv_lhs => rw [this]
          push_cast
          ring
        linarith
      · have : (g : ℝ) ≤ 2 := by
          have : g ≤ 2 := by omega
          exact_mod_cast this
        linarith
    have h4 : 1 ≤ localNearFactor R * Real.exp (-(columnRate R * (g : ℝ))) := by
      unfold localNearFactor
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    have h5 : 1 ≤ localNearFactor R * G.coreWeightFrom Y j :=
      h4.trans (mul_le_mul_of_nonneg_left hseen hBs.le)
    calc |H σ - H σ'| ≤ |H σ| + |H σ'| := abs_sub _ _
      _ ≤ 2 * Mb := by linarith [hb σ, hb σ']
      _ ≤ (2 * Mb + Mf) * 1 := by linarith
      _ ≤ (2 * Mb + Mf) * (localNearFactor R * G.coreWeightFrom Y j) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = _ := by ring
theorem abs_integral_sub_tilted_le (hT : TiltedGibbsComparison) (hgas : GasSumNearBlockBound)
    (hfit : R.params.Admissible)
    (hc0 : 0 < c) (hcf : R.params.RangeFloor c) (hy : R.params.y₁ ≤ R.coupling) (hrt : 0 < R.params.rt)
    (he : 1 ≤ e)
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (cols : G.HasSmallColumns (fun j => j.1.Touches ∅) c hw)
    (ht : IsGasTilt G A.score Q B e Yt)
    (hw' : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) (fun σ => G.weight σ * Yt σ)
      fun i => 3 * G.spinActivity c i)
    (hz1 : ∀ i, G.spinActivity c i ≤ 1) {Y : TorusSite n} {D : ℕ} (hQ : Q.Nonempty)
    (hD : ∀ Y' ∈ Q, D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y')
    {H : G.Config → ℝ} {Mb Mf : ℝ} (hMb : 0 ≤ Mb) (hMf : 0 ≤ Mf) (hm : Measurable H) (hb : ∀ σ, |H σ| ≤ Mb)
    (hfar : ∀ (j : G.GasSpin) (σ σ' : G.Config), G.pairConstraint.IsAdmissible σ →
      G.pairConstraint.IsAdmissible σ' →
      (∀ k, k ≠ j → σ k = σ' k) → ∀ m : ℕ, (R.range : ℝ) / (4 * R.params.side) ≤ m →
      m + 2 ≤ setGap {Y} j.1.core →
      |H σ - H σ'| ≤ Mf * Real.exp (-(R.params.rt * m / 2 ^ 5))) :
    |∫ σ, H σ ∂(G.gibbsLaw ∅) - ∫ σ, H σ ∂(tiltedGibbsLaw G Yt)| ≤
      (2 * Mb + Mf) * localNearFactor R * (2 * ((8 * e * tiltNearFactor R *
        Real.exp (-(3 / 4 * columnRate R * D))) * Real.exp (-(8 * c * R.coupling)) *
        (2 / (1 - Real.exp (-(columnRate R / 4 / 4)))) ^ 4)) := by
  have hz0 := hw.activity_nonneg
  have he0 : 0 ≤ e := by linarith
  have hBb : 0 ≤ tiltNearFactor R := (Real.exp_pos _).le
  have hb0 : ∀ i, 0 ≤ tiltDistance G c e Q i := fun i => by
    have := hz0 i
    unfold tiltDistance
    positivity
  obtain ⟨a, ha0, hsum, hcmp⟩ := hT G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasure ∅) G.weight Yt
    (G.spinActivity c) (fun i => 3 * G.spinActivity c i) hw hw' (G.influenceMatrix c) (tiltDistance G c e Q)
    (G.coreWeightFrom Y) ht.pos hz1 cols.influenceMatrix_nonneg hb0 (coreWeightFrom_pos Y) cols.kernel_le
    (fun j => by
      have h1 := cols.column_le Y j
      have h2 := cols.exp_le_half
      have h3 := coreWeightFrom_pos Y j
      calc _ ≤ _ := h1
        _ ≤ G.coreWeightFrom Y j * (1 / 2) := mul_le_mul_of_nonneg_left h2 h3.le
        _ = _ := by ring)
    (fun i => tilt_dichotomy ht he hrt rfl hz0 i)
  have hosc := oscillationBound_of_far hrt hMb hMf hb hfar
  have hres := hcmp H _ hm ⟨Mb, hb⟩ hosc
  have hBs : 0 ≤ localNearFactor R := (Real.exp_pos _).le
  have hss := sum_coreWeight_mul_tiltDistance_le hgas hfit hc0 hcf hy he0 hrt hQ hD (G := G) (Y := Y) (e := e) hz0
  calc |∫ σ, H σ ∂(G.gibbsLaw ∅) - ∫ σ, H σ ∂(tiltedGibbsLaw G Yt)| ≤ _ := hres
    _ = (2 * Mb + Mf) * localNearFactor R * ∑ i, G.coreWeightFrom Y i * a i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ (2 * Mb + Mf) * localNearFactor R * (2 * ∑ i, G.coreWeightFrom Y i * tiltDistance G c e Q i) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
end Local
section Cut
variable {A : ResponseSetup R} {Q : Finset (TorusSite n)} {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ}
  {Yt : G.Config → ℝ}
def spinTail (A : ResponseSetup R) (G : GasGround R n) (y : TorusSite (n * R.params.side)) (M k : ℝ)
    (i : G.GasSpin) (v : G.SpinValue i) : ℝ :=
  open Classical in if k < spinLabelScore A.score G i y v then M + spinLabelScore A.score G i y v else 0
theorem measurable_spinTail (hb : Measurable A.score) (y : TorusSite (n * R.params.side)) (M k : ℝ)
    (i : G.GasSpin) :
    Measurable (spinTail A G y M k i) := by
  classical
  unfold spinTail
  have hl := measurable_spinLabelScore (G := G) hb i y
  exact Measurable.ite (measurableSet_lt measurable_const hl) (measurable_const.add hl) measurable_const
theorem spinTail_nonneg (hs : ∀ w, 0 ≤ A.score w) {y : TorusSite (n * R.params.side)} {M k : ℝ} (hM : 0 ≤ M)
    (i : G.GasSpin) (v : G.SpinValue i) : 0 ≤ spinTail A G y M k i v := by
  classical
  unfold spinTail
  split_ifs
  · exact add_nonneg hM (spinLabelScore_nonneg hs i y v)
  · exact le_rfl
theorem add_le_exp_tail {M k l : ℝ} (hM : 0 ≤ M) (hk : 0 ≤ k) (hl : k < l) :
    M + l ≤ 2 * (M + 1) * Real.exp (-(k / 2)) * Real.exp l := by
  have h1 : 1 + l / 2 ≤ Real.exp (l / 2) := by linarith [Real.add_one_le_exp (l / 2)]
  have h2 : Real.exp (l / 2) ≤ Real.exp (-(k / 2)) * Real.exp l := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have h3 : M + l ≤ (M + 1) * (2 * (1 + l / 2)) := by nlinarith
  calc M + l ≤ (M + 1) * (2 * (1 + l / 2)) := h3
    _ ≤ (M + 1) * (2 * Real.exp (l / 2)) := by gcongr
    _ ≤ (M + 1) * (2 * (Real.exp (-(k / 2)) * Real.exp l)) := by gcongr
    _ = _ := by ring
theorem lintegral_spinTail_le (hP : MeanOfProductStatement) (hs : ∀ w, 0 ≤ A.score w)
    (hbA : Measurable A.score)
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (spinScore A i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    (ht : IsGasTilt G A.score Q B e Yt)
    (hw' : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) (fun σ => G.weight σ * Yt σ)
      fun i => 3 * G.spinActivity c i)
    [IsProbabilityMeasure (tiltedGibbsLaw G Yt)] {y : TorusSite (n * R.params.side)} (hy : y ∉ B) {M k : ℝ}
    (hM : 0 ≤ M) (hk : 0 ≤ k) (i : G.GasSpin) :
    ∫⁻ σ, ENNReal.ofReal (spinTail A G y M k i (σ i)) ∂(tiltedGibbsLaw G Yt) ≤
      ENNReal.ofReal (3 * (2 * (M + 1) * Real.exp (-(k / 2))) * G.spinActivity c i) := by
  classical
  have hz := hw.activity_nonneg i
  have hC : 0 ≤ 2 * (M + 1) * Real.exp (-(k / 2)) := by positivity
  have hprob : IsProbabilityMeasure
      (G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) fun σ => G.weight σ * Yt σ) :=
    inferInstanceAs (IsProbabilityMeasure (tiltedGibbsLaw G Yt))
  refine lintegral_single_spin_le hP G.pairConstraint (G.referenceMeasure ∅) hw' i
    (measurable_spinTail hbA y M k i)
    (spinTail_nonneg hs hM i) ?_ (by positivity) fun σ hσ => ?_
  · unfold spinTail
    rw [if_neg]
    rw [spinLabelScore_vacant]
    exact not_lt.mpr hk
  · refine lintegral_tilted_density_le hs hw paid ht i hC (spinTail_nonneg hs hM i) (fun v => ?_) hσ
    unfold spinTail
    split_ifs with hl
    · have h1 := add_le_exp_tail hM hk hl
      have h2 : spinLabelScore A.score G i y v + ∑ y' ∈ B, spinLabelScore A.score G i y' v ≤ spinScore A i v := by
        have := sum_spinLabelScore_le_spinScore hs (insert y B) i v
        rwa [Finset.sum_insert hy] at this
      have h3 : Real.exp (spinLabelScore A.score G i y v) * Real.exp (∑ y' ∈ B, spinLabelScore A.score G i y' v) ≤
          Real.exp (spinScore A i v) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr h2
      calc _ ≤ (2 * (M + 1) * Real.exp (-(k / 2)) * Real.exp (spinLabelScore A.score G i y v)) *
            Real.exp (∑ y' ∈ B, spinLabelScore A.score G i y' v) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = (2 * (M + 1) * Real.exp (-(k / 2))) * (Real.exp (spinLabelScore A.score G i y v) *
            Real.exp (∑ y' ∈ B, spinLabelScore A.score G i y' v)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 hC
    · rw [zero_mul]
      positivity
theorem tiltedGibbsLaw_one : tiltedGibbsLaw G (fun _ => (1 : ℝ)) = G.gibbsLaw ∅ := by
  unfold tiltedGibbsLaw
  simp only [mul_one]
  rfl
theorem spinTail_of_not_mem {y : TorusSite (n * R.params.side)} {M k : ℝ} (hk : 0 ≤ k) {i : G.GasSpin}
    (hy : y ∉ i.1.2) (v : G.SpinValue i) :
    spinTail A G y M k i v = 0 := by
  classical
  unfold spinTail
  rw [spinLabelScore_of_not_mem hy, if_neg (not_lt.mpr hk)]
theorem spinLabelScore_eq_zero_of_ne (hrr : 0 ≤ R.range) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    {y : TorusSite (n * R.params.side)}
    {s : R.labels.Ω → ℝ} {i j : G.GasSpin} (hij : i ≠ j) (hi : spinLabelScore s G i y (σ i) ≠ 0) :
    spinLabelScore s G j y (σ j) = 0 := by
  classical
  by_contra hj
  have present : ∀ {k : G.GasSpin}, spinLabelScore s G k y (σ k) ≠ 0 → σ k ≠ Sum.inl () ∧ y ∈ k.1.2 := by
    intro k hk
    refine ⟨fun h => hk (by rw [h]; rfl), ?_⟩
    by_contra hn
    exact hk (spinLabelScore_of_not_mem hn _)
  obtain ⟨pi, yi⟩ := present hi
  obtain ⟨hTransposeNorm, yj⟩ := present hj
  rcases hσ i j hij with h | h | h
  · exact pi h
  · exact hTransposeNorm h
  · have := h y (Finset.mem_union_right _ yi) y (Finset.mem_union_right _ yj)
    simp [_root_.YangMills.Construction.TorusFields.supDist_self] at this
end Cut
section Pieces
variable {A : ResponseSetup R} {Q : Finset (TorusSite n)} {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ}
  {Yt : G.Config → ℝ}
def truncatedResponse (A : ResponseSetup R) (G : GasGround R n)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (y : TorusSite (n * R.params.side)) (k : ℝ) (σ : G.Config) : ℝ :=
  open Classical in
  if G.pairConstraint.IsAdmissible σ ∧ siteLabelSum A G y σ ≤ k then siteResponseMean A G f y σ else 0
def admissibleBondScore (G : GasGround R n) (c : TorusBond n) (σ : G.Config) : ℝ :=
  open Classical in if G.pairConstraint.IsAdmissible σ then bondScoreMean G c σ else 0
theorem measurable_siteLabelSum (hb : Measurable A.score) (y : TorusSite (n * R.params.side)) :
    Measurable (siteLabelSum A G y) :=
  Finset.measurable_fun_sum _ fun i _ => (measurable_spinLabelScore hb i y).comp (measurable_pi_apply i)
theorem TiltSetup.measurable_truncatedResponse (h : TiltSetup A G)
    (hset : MeasurableSet {σ : G.Config | G.pairConstraint.IsAdmissible σ})
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (y : TorusSite (n * R.params.side)) (k : ℝ) :
    Measurable (truncatedResponse A G f y k) := by
  classical
  have e : truncatedResponse A G f y k = fun σ => if siteLabelSum A G y σ ≤ k then
      (if G.pairConstraint.IsAdmissible σ then siteResponseMean A G f y σ else 0) else 0 := by
    funext σ
    unfold truncatedResponse
    by_cases h1 : G.pairConstraint.IsAdmissible σ <;> by_cases h2 : siteLabelSum A G y σ ≤ k <;> simp [h1, h2]
  rw [e]
  exact Measurable.ite (measurableSet_le (measurable_siteLabelSum h.admissibleResponse.price.borel y)
    measurable_const) (h.measurable_siteResponseMean f y) measurable_const
theorem TiltSetup.measurable_admissibleBondScore (h : TiltSetup A G)
    (hset : MeasurableSet {σ : G.Config | G.pairConstraint.IsAdmissible σ})
    (c : TorusBond n) : Measurable (admissibleBondScore G c) := by
  classical
  exact h.measurable_bondScoreMean c
theorem abs_admissibleBondScore_le (h : TiltSetup A G) (c : TorusBond n) (σ : G.Config) :
    |admissibleBondScore G c σ| ≤ 2 := by
  classical
  unfold admissibleBondScore
  split_ifs with hσ
  · exact h.abs_bondScoreMean_le hσ c
  · simp
theorem TiltSetup.recordedSiteScore_nonneg (h : TiltSetup A G) (y : TorusSite (n * R.params.side)) :
    0 ≤ recordedSiteScore A G y :=
  siteScore_nonneg h.admissibleResponse.price.nonneg _ _ _
theorem TiltSetup.C₀_nonneg (h : TiltSetup A G) : 0 ≤ A.responseParams.C₀ := by
  have h3 := h.coupling_ge
  have h4 := h.C₀_ge
  linarith
theorem TiltSetup.abs_truncatedResponse_le (h : TiltSetup A G)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (y : TorusSite (n * R.params.side)) {k : ℝ} (hk : 0 ≤ k) (σ : G.Config) :
    |truncatedResponse A G f y k σ| ≤ A.responseParams.C₀ + recordedSiteScore A G y + k := by
  classical
  unfold truncatedResponse
  have h0 := h.C₀_nonneg
  have h1 := h.recordedSiteScore_nonneg y
  split_ifs with hc
  · have a := h.abs_siteResponseMean_le hc.1 hsz y
    have b := h.configSiteScore_le y σ
    linarith [hc.2]
  · simp only [abs_zero]
    linarith
theorem siteLabelSum_eq_of_far {y : TorusSite (n * R.params.side)} {σ σ' : G.Config} {j : G.GasSpin}
    (hd : ∀ k, k ≠ j → σ k = σ' k)
    (hy : y ∉ j.1.2) : siteLabelSum A G y σ = siteLabelSum A G y σ' := by
  unfold siteLabelSum
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = j
  · subst hi
    rw [spinLabelScore_of_not_mem hy, spinLabelScore_of_not_mem hy]
  · rw [hd i hi]
theorem TiltSetup.abs_truncatedResponse_sub_le (h : TiltSetup A G)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (y : TorusSite (n * R.params.side)) {k : ℝ} (hk0 : 0 ≤ k) (j : G.GasSpin) (σ σ' : G.Config)
    (hσ : G.pairConstraint.IsAdmissible σ)
    (hσ' : G.pairConstraint.IsAdmissible σ') (hd : ∀ l, l ≠ j → σ l = σ' l) (m : ℕ)
    (hm : (R.range : ℝ) / (4 * R.params.side) ≤ m)
    (hg : m + 2 ≤ setGap {parentBlock R.params.side y} j.1.core) :
    |truncatedResponse A G f y k σ - truncatedResponse A G f y k σ'| ≤
      (2 + 2 * (recordedSiteScore A G y + k)) * Real.exp (-(R.params.rt * m / 2 ^ 5)) := by
  classical
  have hyj : y ∉ j.1.2 := by
    intro hy
    have h1 : parentBlock R.params.side y ∈ j.1.core :=
      GasSupport.parentBlock_mem_core (Finset.mem_union_right _ hy)
    have h2 := setGap_le (Finset.mem_singleton_self (parentBlock R.params.side y)) h1
    rw [_root_.YangMills.Construction.TorusFields.supDist_self] at h2
    omega
  have hT := siteLabelSum_eq_of_far (A := A) hd hyj
  unfold truncatedResponse
  by_cases hk : siteLabelSum A G y σ ≤ k
  · rw [if_pos ⟨hσ, hk⟩, if_pos ⟨hσ', hT ▸ hk⟩]
    have h1 := h.abs_siteResponseMean_sub_le hσ hσ' hd hsz hm hg
    have s1 := h.configSiteScore_le y σ
    have s2 := h.configSiteScore_le y σ'
    have hE : 0 ≤ Real.exp (-(R.params.rt * m / 2 ^ 5)) := (Real.exp_pos _).le
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ hE)
    rw [← hT] at s2
    linarith
  · rw [if_neg fun hh => hk hh.2, if_neg fun hh => hk (hT ▸ hh.2)]
    simp only [sub_self, abs_zero]
    have h0 := h.recordedSiteScore_nonneg y
    have hE : 0 ≤ Real.exp (-(R.params.rt * m / 2 ^ 5)) := (Real.exp_pos _).le
    exact mul_nonneg (by linarith) hE
theorem TiltSetup.abs_sub_truncatedResponse_le (h : TiltSetup A G)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (y : TorusSite (n * R.params.side)) {k : ℝ} (hk : 0 ≤ k) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) :
    |siteResponseMean A G f y σ - truncatedResponse A G f y k σ| ≤
      ∑ i, spinTail A G y (A.responseParams.C₀ + recordedSiteScore A G y) k i (σ i) := by
  classical
  have hs := h.admissibleResponse.price.nonneg
  have hM : 0 ≤ A.responseParams.C₀ + recordedSiteScore A G y := add_nonneg h.C₀_nonneg (h.recordedSiteScore_nonneg y)
  have hsum0 : 0 ≤ ∑ i, spinTail A G y (A.responseParams.C₀ + recordedSiteScore A G y) k i (σ i) :=
    Finset.sum_nonneg fun i _ => spinTail_nonneg hs hM i _
  unfold truncatedResponse
  by_cases hT : siteLabelSum A G y σ ≤ k
  · rw [if_pos ⟨hσ, hT⟩, sub_self, abs_zero]
    exact hsum0
  · rw [if_neg fun hh => hT hh.2, sub_zero]
    have hTk := not_le.mp hT
    obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, spinLabelScore A.score G i y (σ i) ≠ 0 := by
      by_contra hn
      push_neg at hn
      have : siteLabelSum A G y σ = 0 := Finset.sum_eq_zero hn
      linarith
    have hr0 : 0 ≤ R.range := Nat.zero_le _
    have hone : siteLabelSum A G y σ = spinLabelScore A.score G i y (σ i) := by
      unfold siteLabelSum
      rw [Finset.sum_eq_single i]
      · intro j _ hj
        exact spinLabelScore_eq_zero_of_ne hr0 hσ (Ne.symm hj) hi
      · exact fun hn => absurd (Finset.mem_univ i) hn
    have h1 := h.abs_siteResponseMean_le hσ hsz y
    have h2 := h.configSiteScore_le y σ
    have h3 : spinTail A G y (A.responseParams.C₀ + recordedSiteScore A G y) k i (σ i) =
        A.responseParams.C₀ + recordedSiteScore A G y + siteLabelSum A G y σ := by
      unfold spinTail
      rw [if_pos (hone ▸ hTk), hone]
    have h4 := Finset.single_le_sum
      (f := fun i => spinTail A G y (A.responseParams.C₀ + recordedSiteScore A G y) k i (σ i))
      (fun i _ => spinTail_nonneg hs hM i _) (Finset.mem_univ i)
    simp only [h3] at h4
    linarith
theorem sum_spinActivity_at_site_le (hgas : GasSumNearBlockBound) (hfit : R.params.Admissible) (hc0 : 0 < c)
    (hcf : R.params.RangeFloor c)
    (hy : R.params.y₁ ≤ R.coupling) (hrt : 0 < R.params.rt) (hz0 : ∀ i, 0 ≤ G.spinActivity c i)
    (y : TorusSite (n * R.params.side)) :
    (open Classical in ∑ i : G.GasSpin, if y ∈ i.1.2 then G.spinActivity c i else 0) ≤
      Real.exp (-(8 * c * R.coupling)) * (2 / (1 - Real.exp (-(columnRate R / 4 / 4)))) ^ 4 := by
  classical
  have hrp : 0 < columnRate R := by unfold columnRate; positivity
  have := hgas R n G c (columnRate R / 4) 1 (parentBlock R.params.side y)
    (Finset.univ.filter fun i : G.GasSpin => y ∈ i.1.2)
    (fun i => G.spinActivity c i) hfit hc0 hcf hy (by positivity) zero_le_one (fun i hi => by
      have hyi : y ∈ i.1.2 := (Finset.mem_filter.mp hi).2
      have h1 : parentBlock R.params.side y ∈ i.1.core :=
        GasSupport.parentBlock_mem_core (Finset.mem_union_right _ hyi)
      have h2 : setGap {parentBlock R.params.side y} i.1.core = 0 := by
        have := setGap_le (Finset.mem_singleton_self (parentBlock R.params.side y)) h1
        rw [_root_.YangMills.Construction.TorusFields.supDist_self] at this
        omega
      rw [h2]
      have hN : (1 : ℝ) ≤ (i.1.core.card : ℝ) := by exact_mod_cast (core_nonempty i).card_pos
      have hN4 : (1 : ℝ) ≤ (i.1.core.card : ℝ) ^ 4 := one_le_pow₀ hN
      have hE : 1 ≤ Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ)) := Real.one_le_exp (by positivity)
      have hz := hz0 i
      simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one, one_mul]
      have : 1 ≤ (i.1.core.card : ℝ) ^ 4 * Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ)) := by nlinarith
      nlinarith)
  rw [← Finset.sum_filter]
  simpa using this
theorem integral_spinTail_le (hP : MeanOfProductStatement) (hgas : GasSumNearBlockBound) (h : TiltSetup A G)
    (hc0 : 0 < c) (hcf : R.params.RangeFloor c) (hy₁ : R.params.y₁ ≤ R.coupling) (hrt : 0 < R.params.rt)
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (spinScore A i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    (ht : IsGasTilt G A.score Q B e Yt)
    (hw' : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) (fun σ => G.weight σ * Yt σ)
      fun i => 3 * G.spinActivity c i)
    [IsProbabilityMeasure (tiltedGibbsLaw G Yt)] {y : TorusSite (n * R.params.side)} (hy : y ∉ B) {M k : ℝ}
    (hM : 0 ≤ M) (hk : 0 ≤ k) :
    Integrable (fun σ : G.Config => ∑ i, spinTail A G y M k i (σ i)) (tiltedGibbsLaw G Yt) ∧
      ∫ σ, ∑ i, spinTail A G y M k i (σ i) ∂(tiltedGibbsLaw G Yt) ≤
        3 * (2 * (M + 1) * Real.exp (-(k / 2))) *
          (Real.exp (-(8 * c * R.coupling)) * (2 / (1 - Real.exp (-(columnRate R / 4 / 4)))) ^ 4) := by
  classical
  have hs := h.admissibleResponse.price.nonneg
  have hbA := h.admissibleResponse.price.borel
  have hz0 := hw.activity_nonneg
  have hC : 0 ≤ 3 * (2 * (M + 1) * Real.exp (-(k / 2))) := by positivity
  set ee : G.GasSpin → ℝ := fun i =>
    3 * (2 * (M + 1) * Real.exp (-(k / 2))) * if y ∈ i.1.2 then G.spinActivity c i else 0 with hee
  have hee0 : ∀ i, 0 ≤ ee i := fun i => by
    have := hz0 i
    simp only [hee]
    split_ifs <;> positivity
  have one : ∀ i : G.GasSpin, ∫⁻ σ, ENNReal.ofReal (spinTail A G y M k i (σ i)) ∂(tiltedGibbsLaw G Yt) ≤
      ENNReal.ofReal (ee i) := by
    intro i
    by_cases hyi : y ∈ i.1.2
    · have := lintegral_spinTail_le hP hs hbA hw paid ht hw' hy hM hk i
      simpa [hee, hyi] using this
    · have hz : ∀ σ : G.Config, spinTail A G y M k i (σ i) = 0 := fun σ => spinTail_of_not_mem hk hyi _
      simp [hz]
  have hm : ∀ i : G.GasSpin, Measurable fun σ : G.Config => spinTail A G y M k i (σ i) := fun i =>
    (measurable_spinTail hbA y M k i).comp (measurable_pi_apply i)
  have hgm : Measurable fun σ : G.Config => ∑ i, spinTail A G y M k i (σ i) :=
    Finset.measurable_fun_sum _ fun i _ => hm i
  have hg0 : ∀ σ : G.Config, 0 ≤ ∑ i, spinTail A G y M k i (σ i) := fun σ =>
    Finset.sum_nonneg fun i _ => spinTail_nonneg hs hM i _
  have hlin : ∫⁻ σ, ENNReal.ofReal (∑ i, spinTail A G y M k i (σ i)) ∂(tiltedGibbsLaw G Yt) ≤
      ENNReal.ofReal (∑ i, ee i) := by
    have e1 : ∀ σ : G.Config, ENNReal.ofReal (∑ i, spinTail A G y M k i (σ i)) =
        ∑ i, ENNReal.ofReal (spinTail A G y M k i (σ i)) := fun σ =>
      ENNReal.ofReal_sum_of_nonneg fun i _ => spinTail_nonneg hs hM i _
    simp only [e1]
    rw [lintegral_finset_sum _ fun i _ => (hm i).ennreal_ofReal, ENNReal.ofReal_sum_of_nonneg fun i _ => hee0 i]
    exact Finset.sum_le_sum fun i _ => one i
  have hint : Integrable (fun σ : G.Config => ∑ i, spinTail A G y M k i (σ i)) (tiltedGibbsLaw G Yt) := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hg0)]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  have hee_sum : ∑ i, ee i ≤ 3 * (2 * (M + 1) * Real.exp (-(k / 2))) *
      (Real.exp (-(8 * c * R.coupling)) * (2 / (1 - Real.exp (-(columnRate R / 4 / 4)))) ^ 4) := by
    simp only [hee]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (sum_spinActivity_at_site_le hgas h.params_admissible hc0 hcf hy₁ hrt hz0 y) hC
  have hs0 : 0 ≤ ∑ i, ee i := Finset.sum_nonneg fun i _ => hee0 i
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0) hgm.aestronglyMeasurable]
  refine le_trans ?_ hee_sum
  exact ENNReal.toReal_le_of_le_ofReal hs0 hlin
end Pieces
section Expansion
variable {A : ResponseSetup R}
theorem integral_gasSupportMean_eq (h : TiltSetup A G)
    (hset : MeasurableSet {σ : G.Config | G.pairConstraint.IsAdmissible σ})
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (ν : Measure G.Config)
    [IsProbabilityMeasure ν] (hadm : ∀ᵐ σ ∂ν, G.pairConstraint.IsAdmissible σ) {k : ℝ} (hk : 0 ≤ k)
    (hRi : ∀ y ∈ lowerSites f,
      Integrable (fun σ => siteResponseMean A G f y σ - truncatedResponse A G f y k σ) ν) :
    Integrable (gasSupportMean A G f) ν ∧ ∫ σ, gasSupportMean A G f σ ∂ν =
      ∑ y ∈ lowerSites f, (∫ σ, truncatedResponse A G f y k σ ∂ν +
          ∫ σ, (siteResponseMean A G f y σ - truncatedResponse A G f y k σ) ∂ν) +
        R.params.coupling / 2 * A.coeff * ∑ Y ∈ upperSites f, blockMean R.params.side (R.depth + 1) n Y f *
          ∑ i : Fin 4, (∫ σ, admissibleBondScore G (Y, i) σ ∂ν +
            ∫ σ, admissibleBondScore G (Y - unitStep n i, i) σ ∂ν) -
        caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) := by
  classical
  have iC : ∀ y, Integrable (truncatedResponse A G f y k) ν := fun y =>
    Integrable.of_bound (h.measurable_truncatedResponse hset f y k).aestronglyMeasurable
      (A.responseParams.C₀ + recordedSiteScore A G y + k)
      (Filter.Eventually.of_forall fun σ => by
        rw [Real.norm_eq_abs]
        exact h.abs_truncatedResponse_le hsz y hk σ)
  have iG : ∀ c, Integrable (admissibleBondScore G c) ν := fun c =>
    Integrable.of_bound (h.measurable_admissibleBondScore hset c).aestronglyMeasurable 2
      (Filter.Eventually.of_forall fun σ => by
        rw [Real.norm_eq_abs]
        exact abs_admissibleBondScore_le h c σ)
  set F1 : G.Config → ℝ := fun σ => ∑ y ∈ lowerSites f,
    (truncatedResponse A G f y k σ + (siteResponseMean A G f y σ - truncatedResponse A G f y k σ)) with hF1
  set F2 : G.Config → ℝ := fun σ => ∑ Y ∈ upperSites f, blockMean R.params.side (R.depth + 1) n Y f *
    ∑ i : Fin 4, (admissibleBondScore G (Y, i) σ + admissibleBondScore G (Y - unitStep n i, i) σ) with hF2
  have iB : ∀ Y, Integrable (fun σ => ∑ i : Fin 4,
      (admissibleBondScore G (Y, i) σ + admissibleBondScore G (Y - unitStep n i, i) σ)) ν :=
    fun Y => integrable_finset_sum _ fun i _ => (iG _).add (iG _)
  have i1 : Integrable F1 ν := integrable_finset_sum _ fun y hy => (iC y).add (hRi y hy)
  have i2 : Integrable F2 ν := integrable_finset_sum _ fun Y _ => (iB Y).const_mul _
  have i3 : Integrable (fun σ => F1 σ + R.params.coupling / 2 * A.coeff * F2 σ) ν := i1.add (i2.const_mul _)
  set vv := caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) with hvv
  have heq : gasSupportMean A G f =ᵐ[ν] fun σ => F1 σ + R.params.coupling / 2 * A.coeff * F2 σ - vv := by
    filter_upwards [hadm] with σ hσ
    rw [h.gasSupportMean_eq hσ hsz]
    simp only [hF1, hF2, add_sub_cancel]
    congr 3
    refine Finset.sum_congr rfl fun Y _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [admissibleBondScore, if_pos hσ]
  refine ⟨(i3.sub (integrable_const vv)).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_sub i3 (integrable_const vv), integral_add i1 (i2.const_mul _),
    integral_const_mul, integral_const, probReal_univ, one_smul]
  have e1 : ∫ σ, F1 σ ∂ν = ∑ y ∈ lowerSites f, (∫ σ, truncatedResponse A G f y k σ ∂ν +
      ∫ σ, (siteResponseMean A G f y σ - truncatedResponse A G f y k σ) ∂ν) := by
    have ia : ∀ y ∈ lowerSites f, Integrable (fun σ => truncatedResponse A G f y k σ +
        (siteResponseMean A G f y σ - truncatedResponse A G f y k σ)) ν := fun y hy => (iC y).add (hRi y hy)
    have t := integral_finset_sum (μ := ν) (lowerSites f) ia
    refine t.trans (Finset.sum_congr rfl fun y hy => ?_)
    exact integral_add (iC y) (hRi y hy)
  have e2 : ∫ σ, F2 σ ∂ν = ∑ Y ∈ upperSites f, blockMean R.params.side (R.depth + 1) n Y f *
      ∑ i : Fin 4, (∫ σ, admissibleBondScore G (Y, i) σ ∂ν +
        ∫ σ, admissibleBondScore G (Y - unitStep n i, i) σ ∂ν) := by
    rw [hF2, integral_finset_sum _ fun Y _ => (iB Y).const_mul _]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [integral_const_mul]
    congr 1
    have ia : ∀ i ∈ (Finset.univ : Finset (Fin 4)), Integrable (fun σ => admissibleBondScore G (Y, i) σ +
        admissibleBondScore G (Y - unitStep n i, i) σ) ν := fun i _ => (iG _).add (iG _)
    have t := integral_finset_sum (μ := ν) (Finset.univ : Finset (Fin 4)) ia
    refine t.trans (Finset.sum_congr rfl fun i _ => ?_)
    exact integral_add (iG _) (iG _)
  rw [e1, e2]
theorem abs_expansion_sub_le {κ₁ κ₂ : Type} (As : Finset κ₁) (Ap : Finset κ₂) (a b r r' t₁ : κ₁ → ℝ)
    (u v u' v' : κ₂ → Fin 4 → ℝ) (hh : κ₂ → ℝ) (cc vv t₂ : ℝ)
    (h1 : ∀ y ∈ As, |a y - b y| + |r y| + |r' y| ≤ t₁ y)
    (h2 : ∀ Y ∈ Ap, ∀ i, |u Y i - v Y i| ≤ t₂ ∧ |u' Y i - v' Y i| ≤ t₂) (hhat : ∀ Y ∈ Ap, |hh Y| ≤ 1)
    (ht₂ : 0 ≤ t₂) :
    |(∑ y ∈ As, (a y + r y) + cc * ∑ Y ∈ Ap, hh Y * ∑ i : Fin 4, (u Y i + u' Y i) - vv) -
        (∑ y ∈ As, (b y + r' y) + cc * ∑ Y ∈ Ap, hh Y * ∑ i : Fin 4, (v Y i + v' Y i) - vv)| ≤
      ∑ y ∈ As, t₁ y + |cc| * (Ap.card * (8 * t₂)) := by
  have e : (∑ y ∈ As, (a y + r y) + cc * ∑ Y ∈ Ap, hh Y * ∑ i : Fin 4, (u Y i + u' Y i) - vv) -
        (∑ y ∈ As, (b y + r' y) + cc * ∑ Y ∈ Ap, hh Y * ∑ i : Fin 4, (v Y i + v' Y i) - vv) =
      ∑ y ∈ As, ((a y - b y) + r y - r' y) +
        cc * ∑ Y ∈ Ap, hh Y * ∑ i : Fin 4, ((u Y i - v Y i) + (u' Y i - v' Y i)) := by
    have s1 : ∑ y ∈ As, ((a y - b y) + r y - r' y) = ∑ y ∈ As, (a y + r y) - ∑ y ∈ As, (b y + r' y) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    have s2 : ∑ Y ∈ Ap, hh Y * ∑ i : Fin 4, ((u Y i - v Y i) + (u' Y i - v' Y i)) =
        ∑ Y ∈ Ap, hh Y * ∑ i : Fin 4, (u Y i + u' Y i) - ∑ Y ∈ Ap, hh Y * ∑ i : Fin 4, (v Y i + v' Y i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun Y _ => ?_
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [s1, s2]
    ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y hy => ?_)
    have h3 := h1 y hy
    have h4 := abs_add_le (a y - b y) (r y)
    have h5 := abs_sub (a y - b y + r y) (r' y)
    linarith
  · rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ Y ∈ Ap, |hh Y * ∑ i : Fin 4, ((u Y i - v Y i) + (u' Y i - v' Y i))| ≤ 8 * t₂ := by
      intro Y hY
      rw [abs_mul]
      have a1 : |∑ i : Fin 4, ((u Y i - v Y i) + (u' Y i - v' Y i))| ≤ 8 * t₂ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc _ ≤ ∑ _i : Fin 4, (2 * t₂) := Finset.sum_le_sum fun i _ => by
              have b1 := (h2 Y hY i).1
              have b2 := (h2 Y hY i).2
              have b3 := abs_add_le (u Y i - v Y i) (u' Y i - v' Y i)
              linarith
          _ = 8 * t₂ := by simp; ring
      calc _ ≤ 1 * (8 * t₂) := mul_le_mul (hhat Y hY) a1 (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    calc _ ≤ ∑ _Y ∈ Ap, 8 * t₂ := Finset.sum_le_sum this
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
end Expansion
section Core
variable {A : ResponseSetup R} {Q : Finset (TorusSite n)} {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ}
  {Yt : G.Config → ℝ}
theorem parentBlock_mem_weightSupportSites {L t n : ℕ} [NeZero L] [NeZero n]
    (f : PlaquetteWeight (fineSide L (t + 1) n)) {y : TorusSite (n * L)}
    (hy : y ∈ weightSupportSites L t (n * L) f) : parentBlock L y ∈ weightSupportSites L (t + 1) n f := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.parentBlock_mem_weightSupportSites <;> assumption
theorem image_parentBlock_weightSupportSites {L t n : ℕ} [NeZero L] [NeZero n]
    (f : PlaquetteWeight (fineSide L (t + 1) n)) :
    (open Classical in (weightSupportSites L t (n * L) f).image (parentBlock L)) =
      weightSupportSites L (t + 1) n f := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.image_parentBlock_weightSupportSites <;> assumption
theorem coarseSiteScore_nonneg (h : TiltSetup A G) (h₁ : 0 ≤ A.responseParams.s₁) (Y : TorusSite n) :
    0 ≤ coarseSiteScore A G.state Y :=
  siteScore_nonneg (fun w => by
    rcases w with u | st
    · exact h₁
    · show 0 ≤ coarseLabelScore A.responseParams.s₁ A.score (Sum.inr st)
      simp only [coarseLabelScore]
      refine add_nonneg h₁ (Finset.sum_nonneg fun o _ => ?_)
      rcases st.siteLabel o with u | a
      · simp
      · exact h.admissibleResponse.price.nonneg a) _ _ _
theorem sum_recordedSiteScore_le (h : TiltSetup A G) (h₁ : 0 ≤ A.responseParams.s₁)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (hne : (upperSites f).Nonempty) :
    1 ≤ meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites f) G.state.1 G.state.2 ∧
    ∑ y ∈ lowerSites f, recordedSiteScore A G y ≤ ((lowerSites f).card : ℝ) *
      (meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites f) G.state.1 G.state.2 - 1) := by
  classical
  have h0 := sum_recordedSiteScore_le_parentBlocks (G := G) h.admissibleResponse.price.nonneg h₁ (lowerSites f)
  have hpar : parentBlocks (lowerSites f) = upperSites f := image_parentBlock_weightSupportSites f
  rw [hpar] at h0
  set Sa := ∑ Y ∈ upperSites f, coarseSiteScore A G.state Y with hSa
  have hSa0 : 0 ≤ Sa := Finset.sum_nonneg fun Y _ => coarseSiteScore_nonneg h h₁ Y
  have hcp : ((upperSites f).card : ℝ) ≤ ((lowerSites f).card : ℝ) := by
    have : (upperSites f).card ≤ (lowerSites f).card := by
      rw [← hpar]
      exact Finset.card_image_le
    exact_mod_cast this
  have e1 : meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites f) G.state.1 G.state.2 =
      1 + ((upperSites f).card : ℝ)⁻¹ * Sa := rfl
  rw [e1]
  refine ⟨by have : 0 ≤ ((upperSites f).card : ℝ)⁻¹ * Sa := by positivity
             linarith, ?_⟩
  refine h0.trans ?_
  have e2 : Sa = ((upperSites f).card : ℝ) * (((upperSites f).card : ℝ)⁻¹ * Sa) := by
    field_simp
  have hq : 0 ≤ ((upperSites f).card : ℝ)⁻¹ * Sa := by positivity
  calc Sa = ((upperSites f).card : ℝ) * (((upperSites f).card : ℝ)⁻¹ * Sa) := e2
    _ ≤ ((lowerSites f).card : ℝ) * (((upperSites f).card : ℝ)⁻¹ * Sa) := mul_le_mul_of_nonneg_right hcp hq
    _ = _ := by ring
theorem final_bound_aux {K₁ N W e k T E4 S₁ S₂ Th Bd cc Ac xx : ℝ} (hK : 0 ≤ K₁) (hN : 1 ≤ N) (hW : 0 ≤ W)
    (he : 1 ≤ e)
    (hk : 0 ≤ k) (hE4 : 0 ≤ E4) (hT : T = E4 * Real.exp (-(k / 8))) (hS₁ : S₁ ≤ K₁ * (2 + k) * N)
    (hS₂ : S₂ ≤ 2 * K₁ * N) (hTh : Th ≤ 16 * e * W * T) (hTh0 : 0 ≤ Th) (hBd : Bd ≤ E4)
    (hS₁0 : 0 ≤ S₁) (hS₂0 : 0 ≤ S₂) (hBd0 : 0 ≤ Bd) (hxx : xx ≤ 4 * S₁ * Th + 12 * S₂ * Bd * W)
    (hcc : cc * Ac ≤ K₁) :
    xx + cc * (Ac * (8 * (6 * Th))) ≤ 1432 * W * e * K₁ * N * E4 := by
  have hex : k * Real.exp (-(k / 8)) ≤ 8 := by
    have h1 : k / 8 + 1 ≤ Real.exp (k / 8) := Real.add_one_le_exp _
    have h2 : Real.exp (-(k / 8)) * Real.exp (k / 8) = 1 := by rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos (-(k / 8))
    nlinarith
  have hx1 : Real.exp (-(k / 8)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  set q := Real.exp (-(k / 8)) with hq
  have hThE : Th ≤ 16 * e * W * (E4 * q) := by rw [← hT]; exact hTh
  have a1 : 4 * S₁ * Th ≤ 4 * (K₁ * (2 + k) * N) * (16 * e * W * (E4 * q)) := by
    have : 0 ≤ K₁ * (2 + k) * N := by positivity
    calc 4 * S₁ * Th ≤ 4 * (K₁ * (2 + k) * N) * Th := by gcongr
      _ ≤ _ := by gcongr
  have a2 : 12 * S₂ * Bd * W ≤ 12 * (2 * K₁ * N) * E4 * W := by
    have b1 : S₂ * Bd ≤ (2 * K₁ * N) * E4 := mul_le_mul hS₂ hBd hBd0 (by positivity)
    calc 12 * S₂ * Bd * W = 12 * (S₂ * Bd) * W := by ring
      _ ≤ 12 * ((2 * K₁ * N) * E4) * W := by gcongr
      _ = _ := by ring
  have a3 : cc * (Ac * (8 * (6 * Th))) ≤ 48 * (K₁ * N) * (16 * e * W * (E4 * q)) := by
    have b1 : cc * (Ac * (8 * (6 * Th))) = 48 * (cc * Ac) * Th := by ring
    rw [b1]
    have b2 : cc * Ac ≤ K₁ * N := hcc.trans (by nlinarith)
    calc 48 * (cc * Ac) * Th ≤ 48 * (K₁ * N) * Th := by gcongr
      _ ≤ _ := by gcongr
  set P := K₁ * N * W * E4 with hP
  have hbr : 64 * e * (2 + k) * q + 24 + 768 * e * q ≤ 1432 * e := by
    have c1 : (2 + k) * q ≤ 10 := by nlinarith
    have c2 : 64 * e * ((2 + k) * q) ≤ 64 * e * 10 := by gcongr
    have c3 : 768 * e * q ≤ 768 * e * 1 := by gcongr
    nlinarith
  have hfin : (64 * e * (2 + k) * q + 24 + 768 * e * q) * P ≤ 1432 * e * P := by gcongr
  have e5 : 1432 * W * e * K₁ * N * E4 = 1432 * e * P := by
    rw [hP]
    ring
  rw [e5]
  linarith
theorem exp_split_rate {rt Dr : ℝ} :
    Real.exp (-(3 / 4 * (rt / 2 ^ 6) * Dr)) =
      Real.exp (-(rt * Dr / 2 ^ 7)) * Real.exp (-(rt * Dr / 2 ^ 5 / 8)) := by
  rw [← Real.exp_add]
  congr 1
  ring
theorem recorded_sum_aux {cA C k N Ss : ℝ} (hC : 1 ≤ C) (hN : 1 ≤ N) (hk : 0 ≤ k) (hcA : 0 ≤ cA)
    (hSs : Ss ≤ cA * (N - 1)) :
    cA * (C + k + 1) + Ss ≤ (C * cA) * (2 + k) * N ∧ cA * (C + 1) + Ss ≤ 2 * (C * cA) * N := by
  have a0 : 1 ≤ C * N := by nlinarith
  have a1 : C ≤ C * N := by nlinarith
  have a2 : N ≤ C * N := by nlinarith
  have a3 : k ≤ C * k * N := by nlinarith
  have h1 : C + k + N ≤ C * (2 + k) * N := by nlinarith
  have h2 : C + N ≤ 2 * C * N := by nlinarith
  constructor
  · calc cA * (C + k + 1) + Ss ≤ cA * (C + k + 1) + cA * (N - 1) := by linarith
      _ = cA * (C + k + N) := by ring
      _ ≤ cA * (C * (2 + k) * N) := mul_le_mul_of_nonneg_left h1 hcA
      _ = _ := by ring
  · calc cA * (C + 1) + Ss ≤ cA * (C + 1) + cA * (N - 1) := by linarith
      _ = cA * (C + N) := by ring
      _ ≤ cA * (2 * C * N) := mul_le_mul_of_nonneg_left h2 hcA
      _ = _ := by ring
set_option maxHeartbeats 4000000 in
theorem abs_tilted_sub_expectation_le (hT : TiltedGibbsComparison) (hP : MeanOfProductStatement)
    (hgas : GasSumNearBlockBound) (h : TiltSetup A G) (hc0 : 0 < c) (hcf : R.params.RangeFloor c)
    (hy₁ : R.params.y₁ ≤ R.coupling)
    (hrt : 0 < R.params.rt) (he : 1 ≤ e)
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (cols : G.HasSmallColumns (fun j => j.1.Touches ∅) c hw)
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (spinScore A i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    (ht : IsGasTilt G A.score Q B e Yt) (hz1 : ∀ i, G.spinActivity c i ≤ 1)
    (hfloor : localNearFactor R * tiltNearFactor R * Real.exp (-(8 * c * R.coupling)) ≤ 1)
    (hE8 : Real.exp (-(8 * c * R.coupling)) ≤ 1)
    (hW0 : 0 ≤ (2 / (1 - Real.exp (-(columnRate R / 4 / 4)))) ^ 4)
    (hC : ActivityConditionalLawsStatement)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (hhat : ∀ Y, |blockMean R.params.side (R.depth + 1) n Y f| ≤ 1) (hne : (upperSites f).Nonempty)
    (hs₁ : 0 ≤ A.responseParams.s₁)
    {D : ℕ} (hQ : Q.Nonempty) (hD : ∀ Y ∈ upperSites f, ∀ Y' ∈ Q, D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y')
    (hB : ∀ y ∈ lowerSites f, y ∉ B) :
    Integrable (gasSupportMean A G f) (tiltedGibbsLaw G Yt) ∧ Integrable (gasSupportMean A G f) (G.gibbsLaw ∅) ∧
      |∫ σ, gasSupportMean A G f σ ∂(tiltedGibbsLaw G Yt) - G.expectation ∅ (gasSupportMean A G f)| ≤
        1432 * (2 / (1 - Real.exp (-(columnRate R / 4 / 4)))) ^ 4 * e *
          (A.responseParams.C₀ * ((lowerSites f).card : ℝ)) *
          meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites f) G.state.1 G.state.2 *
          Real.exp (-(R.params.rt * D / 2 ^ 7)) := by
  classical
  set W := (2 / (1 - Real.exp (-(columnRate R / 4 / 4)))) ^ 4 with hWd
  have hs := h.admissibleResponse.price.nonneg
  have hset : MeasurableSet {σ : G.Config | G.pairConstraint.IsAdmissible σ} := hw.measurableSet_admissible
  have e0 : (0 : ℝ) ≤ e := by linarith
  have hw' := isActivityBounded_tilt hs hw paid ht
  have ht₁ : IsGasTilt G A.score Q ∅ e (fun _ => 1) := isGasTilt_one e0
  have hw₁ := isActivityBounded_tilt hs hw paid ht₁
  obtain ⟨p1, g1, -, -⟩ := hC G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasure ∅) _ _ hw'
  obtain ⟨p2, g2, -, -⟩ := hC G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasure ∅) _ _ hw₁
  have i1 : IsProbabilityMeasure (tiltedGibbsLaw G Yt) := p1
  have i2 : IsProbabilityMeasure (tiltedGibbsLaw G (fun _ => (1 : ℝ))) := p2
  have i3 : IsProbabilityMeasure (G.gibbsLaw ∅) := by
    rw [← tiltedGibbsLaw_one]
    exact i2
  have adm₁ : ∀ᵐ σ ∂(tiltedGibbsLaw G Yt), G.pairConstraint.IsAdmissible σ := g1.ae_admissible
  have adm₂ : ∀ᵐ σ ∂(G.gibbsLaw ∅), G.pairConstraint.IsAdmissible σ := by
    rw [← tiltedGibbsLaw_one]
    exact g2.ae_admissible
  set k : ℝ := R.params.rt * D / 2 ^ 5 with hk
  have hk0 : 0 ≤ k := by positivity
  set T := Real.exp (-(3 / 4 * columnRate R * D)) with hTd
  set E8 := Real.exp (-(8 * c * R.coupling)) with hE8d
  set Th := localNearFactor R * (2 * ((8 * e * tiltNearFactor R * T) * E8 * W)) with hTh
  have hBs0 : 0 < localNearFactor R := Real.exp_pos _
  have hBb0 : 0 < tiltNearFactor R := Real.exp_pos _
  have hE80 : 0 < E8 := Real.exp_pos _
  have hT0 : 0 < T := Real.exp_pos _
  have hTh0 : 0 ≤ Th := by positivity
  have hatom : ∀ {Y : TorusSite n} (_ : ∀ Y' ∈ Q, D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y') {H : G.Config → ℝ} {Mb Mf : ℝ}
      (_ : 0 ≤ Mb) (_ : 0 ≤ Mf)
      (_ : Measurable H) (_ : ∀ σ, |H σ| ≤ Mb)
      (_ : ∀ (j : G.GasSpin) (σ σ' : G.Config), G.pairConstraint.IsAdmissible σ →
        G.pairConstraint.IsAdmissible σ' →
        (∀ k, k ≠ j → σ k = σ' k) → ∀ m : ℕ, (R.range : ℝ) / (4 * R.params.side) ≤ m →
        m + 2 ≤ setGap {Y} j.1.core →
        |H σ - H σ'| ≤ Mf * Real.exp (-(R.params.rt * m / 2 ^ 5))),
      |∫ σ, H σ ∂(tiltedGibbsLaw G Yt) - ∫ σ, H σ ∂(G.gibbsLaw ∅)| ≤ (2 * Mb + Mf) * Th := by
    intro Y hDY H Mb Mf a1 a2 a3 a4 a5
    rw [abs_sub_comm]
    refine (abs_integral_sub_tilted_le hT hgas h.params_admissible hc0 hcf hy₁ hrt he hw cols ht hw' hz1 hQ hDY
      a1 a2 a3 a4 a5).trans (le_of_eq ?_)
    rw [hTh]
    ring
  have hstored := fun y => h.recordedSiteScore_nonneg y
  have hC0 := h.C₀_nonneg
  have hM : ∀ y, 0 ≤ A.responseParams.C₀ + recordedSiteScore A G y := fun y => add_nonneg hC0 (hstored y)
  have hRm : ∀ (ν : Measure G.Config), (∀ᵐ σ ∂ν, G.pairConstraint.IsAdmissible σ) → ∀ y,
      AEStronglyMeasurable (fun σ => siteResponseMean A G f y σ - truncatedResponse A G f y k σ) ν := by
    intro ν hν y
    have h1 := ((h.measurable_siteResponseMean f y).sub
      (h.measurable_truncatedResponse hset f y k)).aestronglyMeasurable (μ := ν)
    refine h1.congr ?_
    filter_upwards [hν] with σ hσ
    simp only [Pi.sub_apply, if_pos hσ]
  set Tb : ℝ → ℝ := fun M => 3 * (2 * (M + 1) * Real.exp (-(k / 2))) * (E8 * W) with hTb
  have hRν : ∀ y ∈ lowerSites f,
      Integrable (fun σ => siteResponseMean A G f y σ - truncatedResponse A G f y k σ) (tiltedGibbsLaw G Yt) ∧
      |∫ σ, (siteResponseMean A G f y σ - truncatedResponse A G f y k σ) ∂(tiltedGibbsLaw G Yt)| ≤
        Tb (A.responseParams.C₀ + recordedSiteScore A G y) := by
    intro y hy
    obtain ⟨gi, gb⟩ := integral_spinTail_le hP hgas h hc0 hcf hy₁ hrt hw paid ht hw' (hB y hy) (hM y) hk0
    have hdom : ∀ᵐ σ ∂(tiltedGibbsLaw G Yt), ‖siteResponseMean A G f y σ - truncatedResponse A G f y k σ‖ ≤
        ∑ i, spinTail A G y (A.responseParams.C₀ + recordedSiteScore A G y) k i (σ i) := by
      filter_upwards [adm₁] with σ hσ
      rw [Real.norm_eq_abs]
      exact h.abs_sub_truncatedResponse_le hsz y hk0 hσ
    refine ⟨gi.mono' (hRm _ adm₁ y) hdom, ?_⟩
    have := norm_integral_le_of_norm_le gi hdom
    rw [Real.norm_eq_abs] at this
    exact this.trans gb
  have hRμ : ∀ y,
      Integrable (fun σ => siteResponseMean A G f y σ - truncatedResponse A G f y k σ) (G.gibbsLaw ∅) ∧
      |∫ σ, (siteResponseMean A G f y σ - truncatedResponse A G f y k σ) ∂(G.gibbsLaw ∅)| ≤
        Tb (A.responseParams.C₀ + recordedSiteScore A G y) := by
    intro y
    obtain ⟨gi, gb⟩ := integral_spinTail_le hP hgas h hc0 hcf hy₁ hrt hw paid ht₁ hw₁ (Finset.notMem_empty y)
      (hM y) hk0
    rw [tiltedGibbsLaw_one] at gi gb
    have hdom : ∀ᵐ σ ∂(G.gibbsLaw ∅), ‖siteResponseMean A G f y σ - truncatedResponse A G f y k σ‖ ≤
        ∑ i, spinTail A G y (A.responseParams.C₀ + recordedSiteScore A G y) k i (σ i) := by
      filter_upwards [adm₂] with σ hσ
      rw [Real.norm_eq_abs]
      exact h.abs_sub_truncatedResponse_le hsz y hk0 hσ
    refine ⟨gi.mono' (hRm _ adm₂ y) hdom, ?_⟩
    have := norm_integral_le_of_norm_le gi hdom
    rw [Real.norm_eq_abs] at this
    exact this.trans gb
  obtain ⟨Iν, Eν⟩ := integral_gasSupportMean_eq h hset hsz (tiltedGibbsLaw G Yt) adm₁ hk0 fun y hy => (hRν y hy).1
  obtain ⟨Iμ, Eμ⟩ := integral_gasSupportMean_eq h hset hsz (G.gibbsLaw ∅) adm₂ hk0 fun y _ => (hRμ y).1
  refine ⟨Iν, Iμ, ?_⟩
  show |∫ σ, gasSupportMean A G f σ ∂(tiltedGibbsLaw G Yt) - ∫ σ, gasSupportMean A G f σ ∂(G.gibbsLaw ∅)| ≤ _
  rw [Eν, Eμ]
  have hguard : ∀ (Y : TorusSite n), (∀ Y' ∈ Q, D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y') → ∀ (cb : (Fin 4 → ℤ) × Fin 4),
      IsBondAtOrigin cb →
      |∫ σ, admissibleBondScore G (bondFrom Y cb) σ ∂(tiltedGibbsLaw G Yt) -
        ∫ σ, admissibleBondScore G (bondFrom Y cb) σ ∂(G.gibbsLaw ∅)| ≤
        (2 * 2 + 2) * Th := by
    intro Y hDY cb hcb
    refine hatom hDY zero_le_two zero_le_two (h.measurable_admissibleBondScore hset _)
      (abs_admissibleBondScore_le h _) fun j σ σ' a b d m hm hg => ?_
    simp only [admissibleBondScore, if_pos a, if_pos b]
    exact h.abs_bondScoreMean_sub_le a b d hm hg hcb
  have diff := abs_expansion_sub_le (lowerSites f) (upperSites f)
    (fun y => ∫ σ, truncatedResponse A G f y k σ ∂(tiltedGibbsLaw G Yt))
    (fun y => ∫ σ, truncatedResponse A G f y k σ ∂(G.gibbsLaw ∅))
    (fun y => ∫ σ, (siteResponseMean A G f y σ - truncatedResponse A G f y k σ) ∂(tiltedGibbsLaw G Yt))
    (fun y => ∫ σ, (siteResponseMean A G f y σ - truncatedResponse A G f y k σ) ∂(G.gibbsLaw ∅))
    (fun y => (2 * (A.responseParams.C₀ + recordedSiteScore A G y + k) +
      (2 + 2 * (recordedSiteScore A G y + k))) * Th +
      (Tb (A.responseParams.C₀ + recordedSiteScore A G y) + Tb (A.responseParams.C₀ + recordedSiteScore A G y)))
    (fun Y i => ∫ σ, admissibleBondScore G (Y, i) σ ∂(tiltedGibbsLaw G Yt))
    (fun Y i => ∫ σ, admissibleBondScore G (Y, i) σ ∂(G.gibbsLaw ∅))
    (fun Y i => ∫ σ, admissibleBondScore G (Y - unitStep n i, i) σ ∂(tiltedGibbsLaw G Yt))
    (fun Y i => ∫ σ, admissibleBondScore G (Y - unitStep n i, i) σ ∂(G.gibbsLaw ∅))
    (fun Y => blockMean R.params.side (R.depth + 1) n Y f) (R.params.coupling / 2 * A.coeff)
    (caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f))
    ((2 * 2 + 2) * Th)
    (fun y hy => by
      have hb := parentBlock_mem_weightSupportSites f hy
      have a1 := hatom (Y := parentBlock R.params.side y) (hD _ hb) (H := truncatedResponse A G f y k)
        (Mb := A.responseParams.C₀ + recordedSiteScore A G y + k) (Mf := 2 + 2 * (recordedSiteScore A G y + k))
        (by linarith [hM y]) (by linarith [hstored y]) (h.measurable_truncatedResponse hset f y k)
        (h.abs_truncatedResponse_le hsz y hk0)
        (fun j σ σ' a b d m hm hg => h.abs_truncatedResponse_sub_le hsz y hk0 j σ σ' a b d m hm hg)
      have a2 := (hRν y hy).2
      have a3 := (hRμ y).2
      linarith)
    (fun Y hY i => by
      have hDY := hD Y hY
      constructor
      · have := hguard Y hDY (0, i) (Or.inl rfl)
        have e1 : bondFrom Y ((0 : Fin 4 → ℤ), i) = (Y, i) := by
          simp only [bondFrom]
          congr 1
          funext l
          simp [siteOfInt]
        rwa [e1] at this
      · have := hguard Y hDY (-(Pi.single i 1), i) (Or.inr rfl)
        have e1 : bondFrom Y ((-(Pi.single i 1) : Fin 4 → ℤ), i) = (Y - unitStep n i, i) := by
          simp only [bondFrom]
          congr 1
          rw [unitStep_eq_siteOfInt, sub_eq_add_neg]
          congr 1
          funext l
          simp [siteOfInt]
        rwa [e1] at this)
    (fun Y _ => hhat Y) (by positivity)
  refine diff.trans ?_
  obtain ⟨hN1, hst⟩ := sum_recordedSiteScore_le h hs₁ f hne
  set N := meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites f) G.state.1 G.state.2 with hN
  set cA := ((lowerSites f).card : ℝ) with hcA
  have hcA1 : (1 : ℝ) ≤ cA := by
    have h1 : (upperSites f).card ≤ (lowerSites f).card := by
      have hpar : (open Classical in (lowerSites f).image (parentBlock R.params.side)) = upperSites f :=
        image_parentBlock_weightSupportSites f
      rw [← hpar]
      exact Finset.card_image_le
    have h2 := hne.card_pos
    have h3 : 1 ≤ (lowerSites f).card := by omega
    show (1 : ℝ) ≤ ((lowerSites f).card : ℝ)
    exact_mod_cast h3
  have hC1 : 1 ≤ A.responseParams.C₀ := by
    have h3 := h.coupling_ge
    have h4 := h.C₀_ge
    linarith only [h3, h4]
  set Ss := ∑ y ∈ lowerSites f, recordedSiteScore A G y with hSs
  have hSs0 : 0 ≤ Ss := Finset.sum_nonneg fun y _ => hstored y
  have hN0 : 0 ≤ N := by linarith
  have hsum1 : ∑ y ∈ lowerSites f, (A.responseParams.C₀ + recordedSiteScore A G y + k + 1) =
      cA * (A.responseParams.C₀ + k + 1) + Ss := by
    have : ∀ y, A.responseParams.C₀ + recordedSiteScore A G y + k + 1 =
        (A.responseParams.C₀ + k + 1) + recordedSiteScore A G y := fun y => by ring
    simp only [this]
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hsum2 : ∑ y ∈ lowerSites f, (A.responseParams.C₀ + recordedSiteScore A G y + 1) =
      cA * (A.responseParams.C₀ + 1) + Ss := by
    have : ∀ y, A.responseParams.C₀ + recordedSiteScore A G y + 1 =
        (A.responseParams.C₀ + 1) + recordedSiteScore A G y := fun y => by ring
    simp only [this]
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hcA0 : 0 ≤ cA := by linarith
  obtain ⟨hn1, hn2⟩ := recorded_sum_aux hC1 hN1 hk0 hcA0 hst
  have hS₁ : ∑ y ∈ lowerSites f, (A.responseParams.C₀ + recordedSiteScore A G y + k + 1) ≤
      (A.responseParams.C₀ * cA) * (2 + k) * N := by
    rw [hsum1]
    exact hn1
  have hS₂ : ∑ y ∈ lowerSites f, (A.responseParams.C₀ + recordedSiteScore A G y + 1) ≤
      2 * (A.responseParams.C₀ * cA) * N := by
    rw [hsum2]
    exact hn2
  set Bd := Real.exp (-(k / 2)) with hBdd
  have hBd0 : 0 ≤ Bd := (Real.exp_pos _).le
  have hTb : ∀ M, 0 ≤ M → Tb M + Tb M ≤ 12 * (M + 1) * Bd * W := by
    intro M hM0
    simp only [hTb]
    have h1 : E8 * W ≤ W := mul_le_of_le_one_left hW0 hE8
    have h2 : 0 ≤ 12 * (M + 1) * Bd := by positivity
    calc _ = 12 * (M + 1) * Bd * (E8 * W) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
  have hxx : ∑ y ∈ lowerSites f, ((2 * (A.responseParams.C₀ + recordedSiteScore A G y + k) +
      (2 + 2 * (recordedSiteScore A G y + k))) * Th +
      (Tb (A.responseParams.C₀ + recordedSiteScore A G y) + Tb (A.responseParams.C₀ + recordedSiteScore A G y))) ≤
      4 * (∑ y ∈ lowerSites f, (A.responseParams.C₀ + recordedSiteScore A G y + k + 1)) * Th +
        12 * (∑ y ∈ lowerSites f, (A.responseParams.C₀ + recordedSiteScore A G y + 1)) * Bd * W := by
    have e1 : 4 * (∑ y ∈ lowerSites f, (A.responseParams.C₀ + recordedSiteScore A G y + k + 1)) * Th +
        12 * (∑ y ∈ lowerSites f, (A.responseParams.C₀ + recordedSiteScore A G y + 1)) * Bd * W =
        ∑ y ∈ lowerSites f, (4 * (A.responseParams.C₀ + recordedSiteScore A G y + k + 1) * Th +
          12 * (A.responseParams.C₀ + recordedSiteScore A G y + 1) * Bd * W) := by
      rw [Finset.sum_add_distrib (s := lowerSites f)
        (f := fun y => 4 * (A.responseParams.C₀ + recordedSiteScore A G y + k + 1) * Th)
        (g := fun y => 12 * (A.responseParams.C₀ + recordedSiteScore A G y + 1) * Bd * W)]
      congr 1
      · rw [← Finset.sum_mul, ← Finset.mul_sum]
      · rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [e1]
    refine Finset.sum_le_sum fun y _ => ?_
    refine add_le_add ?_ (hTb _ (hM y))
    apply mul_le_mul_of_nonneg_right _ hTh0
    linarith [hstored y, hC0]
  have hcc : |R.params.coupling / 2 * A.coeff| * ((upperSites f).card : ℝ) ≤ A.responseParams.C₀ * cA := by
    have ha := h.coupling_ge
    have h1 : |R.params.coupling / 2 * A.coeff| ≤ A.responseParams.C₀ := by
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ R.params.coupling / 2)]
      have h2 := h.admissibleResponse.abs_coeff_le
      have h3 := h.C₀_ge
      have h4 := abs_nonneg A.coeff
      nlinarith only [h2, h3, h4, ha]
    have h2 : ((upperSites f).card : ℝ) ≤ cA := by
      have hpar : (open Classical in (lowerSites f).image (parentBlock R.params.side)) = upperSites f :=
        image_parentBlock_weightSupportSites f
      have : (upperSites f).card ≤ (lowerSites f).card := by
        rw [← hpar]
        exact Finset.card_image_le
      show ((upperSites f).card : ℝ) ≤ ((lowerSites f).card : ℝ)
      exact_mod_cast this
    exact mul_le_mul h1 h2 (Nat.cast_nonneg _) hC0
  have hE4T : T = Real.exp (-(R.params.rt * D / 2 ^ 7)) * Real.exp (-(k / 8)) := exp_split_rate
  have hThle : Th ≤ 16 * e * W * T := by
    have e1 : Th = (16 * e * W * T) * (localNearFactor R * tiltNearFactor R * E8) := by
      rw [hTh]
      ring
    rw [e1]
    have h1 : 0 ≤ 16 * e * W * T := by positivity
    calc _ ≤ (16 * e * W * T) * 1 := mul_le_mul_of_nonneg_left hfloor h1
      _ = _ := mul_one _
  have hBdE : Bd ≤ Real.exp (-(R.params.rt * D / 2 ^ 7)) := by
    apply Real.exp_le_exp.mpr
    have h0 : 0 ≤ R.params.rt * (D : ℝ) := by positivity
    rw [hk]
    linarith only [h0]
  have hfinal := final_bound_aux (K₁ := A.responseParams.C₀ * cA) (N := N) (W := W) (e := e) (k := k) (T := T)
    (E4 := Real.exp (-(R.params.rt * D / 2 ^ 7))) (Th := Th) (Bd := Bd) (cc := |R.params.coupling / 2 * A.coeff|)
    (Ac := ((upperSites f).card : ℝ)) (by positivity) hN1 hW0 he hk0 (Real.exp_pos _).le hE4T hS₁ hS₂ hThle
    hTh0 hBdE
    (Finset.sum_nonneg fun y _ => by linarith [hstored y, hC0])
    (Finset.sum_nonneg fun y _ => by linarith [hstored y, hC0]) hBd0 hxx hcc
  have e6 : (2 * 2 + 2 : ℝ) = 6 := by norm_num
  rw [e6]
  exact hfinal
end Core
section Main
theorem weightLipschitz_le_succ {L : ℕ} [NeZero L] (t : ℕ) {m : ℕ} [NeZero m] (hL : 1 ≤ L) (h : PlaquetteWeight m) :
    weightLipschitz L t h ≤ weightLipschitz L (t + 1) h := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.weightLipschitz_le_succ <;> assumption
theorem weightNorm_le_succ {L : ℕ} [NeZero L] (t : ℕ) {m : ℕ} [NeZero m] (hL : 1 ≤ L) (h : PlaquetteWeight m) :
    weightNorm L t h ≤ weightNorm L (t + 1) h :=
  max_le_max le_rfl (weightLipschitz_le_succ t hL h)
theorem rate_le_floor_aux {rt r L c x : ℝ} (hrt : 0 < rt) (hr : 1 ≤ r) (hL : 1 ≤ L)
    (hcf : (2 ^ 16 + 2 ^ 7 * rt) * r ^ 4 ≤ c * x) (hcx : 0 ≤ c * x) :
    rt / 2 ^ 6 * (r / (4 * L) + 4) + 2 * (rt / 2 ^ 6) * (r / (4 * L) + 3) ≤ 8 * c * x := by
  have h1 : r / (4 * L) ≤ r := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h2 : r ≤ r ^ 4 := by
    calc r = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ 4 := pow_le_pow_right₀ hr (by norm_num)
  have h3 : rt * r ≤ 2 ^ 7 * rt * r ^ 4 := by nlinarith
  have h5 : rt / 2 ^ 6 * (r / (4 * L) + 4) + 2 * (rt / 2 ^ 6) * (r / (4 * L) + 3) ≤ rt * r := by
    have e : rt / 2 ^ 6 * (r / (4 * L) + 4) + 2 * (rt / 2 ^ 6) * (r / (4 * L) + 3) =
        rt / 2 ^ 6 * (3 * (r / (4 * L)) + 10) := by ring
    rw [e]
    have : 3 * (r / (4 * L)) + 10 ≤ 2 ^ 6 * r := by linarith
    calc rt / 2 ^ 6 * (3 * (r / (4 * L)) + 10) ≤ rt / 2 ^ 6 * (2 ^ 6 * r) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  linarith
set_option maxHeartbeats 4000000 in
theorem gasSupportMeanUnderTilt_holds (hcols : ClusterExpansionOfAStep.GasColumnsSmall)
    (hpaid : clusterScoreIntegralBound)
    (htwo : ChartResponseComparison) (hsc : BondScoreProperties) (hT : TiltedGibbsComparison)
    (hgas : GasSumNearBlockBound) (hcf : CouplingFloorExists)
    (hcfg : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hmass : SettingMassEqIntegral)
    (hpot : PotentialFactorization) (hagree : LocalSettingsAgree)
    (hborel : settingMeanMeasurableStatement) (hP : MeanOfProductStatement)
    (hC : ActivityConditionalLawsStatement) (hwn : WeightsCloseToBlockMeans) :
    GasSupportMeanUnderTilt := by
  classical
  obtain ⟨r₁, p₁, H₁⟩ := hcols
  obtain ⟨r₂, p₂, H₂⟩ := hpaid
  obtain ⟨r₃, p₃, H₃⟩ := htwo
  obtain ⟨r₄, p₄, H₄⟩ := hmass
  obtain ⟨r₅, p₅, H₅⟩ := hborel
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (min (r₄ c) (r₅ c)))),
    fun c => lt_min (p₁ c) (lt_min (p₂ c) (lt_min (p₃ c) (lt_min (p₄ c) (p₅ c)))), fun T hT' hrt K => ?_⟩
  have t₁ := hrt.trans (min_le_left _ _)
  have t₂ := (hrt.trans (min_le_right _ _)).trans (min_le_left _ _)
  have t₃ := ((hrt.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have t₄ := (((hrt.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_left _ _)
  have t₅ := (((hrt.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_right _ _)
  obtain ⟨y₁, H₁⟩ := H₁ T hT' t₁
  obtain ⟨y₂, H₂⟩ := H₂ T hT' t₂ K
  obtain ⟨y₃, H₃⟩ := H₃ T hT' t₃ K
  obtain ⟨y₄, H₄⟩ := H₄ T hT' t₄
  obtain ⟨y₅, H₅⟩ := H₅ T hT' t₅ K
  obtain ⟨y₆, H₆⟩ := hcfg T hT'
  have hrt0 := hT'.rt_pos
  have hch : 0 < T.gasRate := by
    have h1 := hT'.cE_pos
    have h2 := hT'.κ_pos
    have h3 := hT'.σ_pos
    unfold ParameterAssignment.gasRate ParameterAssignment.κ₁
    positivity
  obtain ⟨y₇, H₇⟩ := hcf T.gasRate T.side T.rt hch
  obtain ⟨W, hWd⟩ : ∃ W, W = (2 / (1 - Real.exp (-(T.rt / 2 ^ 6 / 4 / 4)))) ^ 4 := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hWd]
    exact Even.pow_nonneg (by decide) _
  refine ⟨max T.floorMin (max y₁ (max y₂ (max y₃ (max y₄ (max y₅ (max y₆ (max y₇ (200 * T.B)))))))), 1432 * W,
    by positivity,
    fun y hy R A hK hAT n _ G hG f Q B e Yt D hsz hne hDr hD8 hQ hD hB he ht => ?_⟩
  have fl : ∀ {a : ℝ}, a ≤ max y₁ (max y₂ (max y₃ (max y₄ (max y₅ (max y₆ (max y₇ (200 * T.B))))))) → a ≤ y :=
    fun h => h.trans ((le_max_right _ _).trans hy)
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hy1 : y₁ ≤ y := fl (le_max_left _ _)
  have hy2 : y₂ ≤ y := fl ((le_max_left _ _).trans (le_max_right _ _))
  have hy3 : y₃ ≤ y := fl ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hy4 : y₄ ≤ y := fl ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_right _ _))))
  have hy5 : y₅ ≤ y := fl ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))))
  have hy6 : y₆ ≤ y := fl ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))))
  have hy7 : y₇ ≤ y := fl ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))))
  have hy8 : 200 * T.B ≤ y := fl ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))))
  have hAT₀ := hAT
  have hOT := hAT.onFamily
  obtain ⟨hR, hρA, hpc, hyx, hstep⟩ := id hOT
  have hx1 : 1 ≤ R.coupling := by
    have h1 : (1 : ℝ) ≤ T.floorMin := by
      have h2 := hT'.yC_ge
      exact h2.trans (le_max_left _ _)
    linarith only [h1, hy0, hyx]
  have hx0 : 0 < R.coupling := by linarith only [hx1]
  have hL : R.params.side = T.side := by rw [hR]; rfl
  have hRrt : R.params.rt = T.rt := by rw [hR]; rfl
  have hRa : R.params.coupling = T.coupling := by rw [hR]; rfl
  have hRσ : R.params.threshold = T.threshold := by rw [hR]; rfl
  have hRy : R.params.y₁ = y := by rw [hR]; rfl
  have hfit : R.params.Admissible := by rw [hR]; exact hT'.fits y hy0
  have hodd : Odd R.params.side := by rw [hL]; exact hT'.L_odd
  have hx' : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAT.abs_sub_le).2
    linarith only [h1, hy8, hyx]
  have hrtR : 0 < R.params.rt := by rw [hRrt]; exact hrt0
  have hn : R.params.n₀ ≤ n := by
    rcases hG with h | h
    · exact h.n₀_le
    · have h1 := h.isBlockSide.2
      have hL1 : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
      nlinarith only [h1, hL1]
  have hRn₀ : R.params.n₀ = T.n₀ := by rw [hR]; rfl
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [mul_comm R.params.side]; exact Nat.mul_le_mul_right _ hn⟩
  have hadm : ∀ σ, G.pairConstraint.IsAdmissible σ → (configSetting G σ).IsAdmissible := fun σ hσ =>
    H₆ y hy6 R hOT hx' n G hG σ hσ
  have hρR : 0 < R.ballRadius := by
    show 0 < R.params.threshold / 64
    rw [hRσ]
    have := hT'.σ_pos
    positivity
  have hρπ : R.anchorRadius + R.ballRadius < Real.pi := by
    have h1 := hT'.chain.2.2.2.2.1
    have h3 := hT'.σ_one
    have h4 := Real.pi_gt_three
    have e : R.ballRadius = T.threshold / 64 := by
      show R.params.threshold / 64 = _
      rw [hRσ]
    rw [hρA, e]
    linarith only [h1, h3, h4]
  have hρA0 : 0 < R.anchorRadius := by
    rw [hρA]
    exact hT'.chain.2.2.2.1
  have hall : G.pairConstraint.IsAdmissible (fun i => G.pairConstraint.vacant i) := fun a b _ =>
    G.pairConstraint.vacant_compatible _ _ _
  have hzero : (configSetting G fun i => G.pairConstraint.vacant i).InBalls 0 := fun b => by
    rw [ClusterExpansionOfAStep.coordNorm_eq_norm]
    simpa using hρR.le
  have hflat := (hpot R hfit hstep.1 hρA0 hρπ n hn _ (hadm _ hall) 0 hzero).1
  have ha1 : 1 ≤ R.params.coupling := by rw [hRa]; exact hT'.a_ge
  have hl := hAT.admissible.params_admissible
  have hc0' : 12 + 40 * R.params.coupling ≤ A.responseParams.C₀ := by
    have h1 := hl.C₀_eq
    have h2 := hl.N₀_nonneg
    have h3 := hl.Kc_ge
    linarith only [h1, h2, h3]
  have st : TiltSetup A G := {
    admissibleResponse := hAT.admissible
    params_admissible := hfit
    side_odd := hodd
    hullExpansion := hstep.1.2
    isBlockSide := hside
    n₀_le := hn
    functional_trivial_pos := hflat
    isAdmissible_setting := hadm
    density_integrable := fun σ hσ => by
      obtain ⟨a1, a2, -⟩ := H₄ y hy4 R hOT n (by rw [← hRn₀]; exact hn) (configSetting G σ) (hadm σ hσ)
      exact ⟨a1, a2⟩
    settingsAgree := hagree
    measurable_settingMean := fun F hF => H₅ y hy5 R A hK hAT n G hG F hF
    coupling_ge := ha1
    C₀_ge := hc0'
    abs_bondScore_le := fun W V b c => (hsc R.params hfit R.coupling n b c).2.2.1 W V
    measurable_bondScore := fun b c => (hsc R.params hfit R.coupling n b c).2.2.2.2
    chart_close := fun s s' Y m hs hs' hag hm => by
      obtain ⟨b1, b2⟩ := ((H₃ y hy3 R A hK hAT).2 n n s s' Y Y m hn hn hs hs').1 hag hm
      exact ⟨fun o ho h => b1 o ho h h fun _ _ _ _ _ => rfl, b2⟩ }
  obtain ⟨hw, cols⟩ := H₁ y hy1 R hOT hx' n G hG fun j => j.1.Touches ∅
  have paid := H₂ y hy2 R A hK hAT n G hG
  have hcfR : R.params.RangeFloor T.gasRate := by
    intro x hx
    have := H₇ x (hy7.trans (hRy ▸ hx))
    rw [hL, hRrt]
    exact this
  have hyR : R.params.y₁ ≤ R.coupling := by rw [hRy]; exact hyx
  have hz1 : ∀ i, G.spinActivity T.gasRate i ≤ 1 := fun i => by
    show Real.exp _ ≤ 1
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ 16 * T.gasRate * R.coupling * (supportUnitCount R.params.side R.range i.1 : ℝ) := by positivity
    linarith only [this]
  have hE8 : Real.exp (-(8 * T.gasRate * R.coupling)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ 8 * T.gasRate * R.coupling := by positivity
    linarith only [this]
  have hfloor : localNearFactor R * tiltNearFactor R * Real.exp (-(8 * T.gasRate * R.coupling)) ≤ 1 := by
    obtain ⟨c1, c2⟩ := hcfR R.coupling hyR
    have hr1 : (1 : ℝ) ≤ (clusterRange R.coupling : ℝ) := by
      have : 1 ≤ clusterRange R.coupling := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hx0 _)
      exact_mod_cast this
    have hL1 : (1 : ℝ) ≤ (R.params.side : ℝ) := by
      have : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
      exact_mod_cast this
    have key := rate_le_floor_aux hrtR hr1 hL1 c2 (by positivity)
    unfold localNearFactor tiltNearFactor columnRate
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have e1 : (R.range : ℝ) = (clusterRange R.coupling : ℝ) := rfl
    rw [e1]
    linarith only [key]
  have hL1 : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hsz' : weightNorm R.params.side R.depth f ≤ 1 := (weightNorm_le_succ R.depth hL1 f).trans hsz
  have hhat : ∀ Y, |blockMean R.params.side (R.depth + 1) n Y f| ≤ 1 := fun Y =>
    ((hwn R.params.side hodd (R.depth + 1) n Y).1 f).trans ((le_max_left _ _).trans hsz)
  have hs₁ : 0 ≤ A.responseParams.s₁ := by
    have h1 := hl.s₁_eq
    have h2 : 0 ≤ A.responseParams.C₀ + 2 := by linarith only [hc0', ha1]
    rw [h1]
    positivity
  have hrpW : (2 / (1 - Real.exp (-(columnRate R / 4 / 4)))) ^ 4 = W := by
    rw [hWd]
    unfold columnRate
    rw [hRrt]
  have hW0' : 0 ≤ (2 / (1 - Real.exp (-(columnRate R / 4 / 4)))) ^ 4 := by rw [hrpW]; exact hW0
  have res := abs_tilted_sub_expectation_le hT hP hgas st hch hcfR hyR hrtR he hw cols paid ht hz1 hfloor hE8 hW0'
    hC hsz' hhat hne hs₁ hQ hD hB
  rw [hrpW, hK] at res
  exact res
end Main
end TiltedGasResponse
namespace ResponseInTheExpansion
theorem gasSupportMeanUnderTilt_proof (hcols : ClusterExpansionOfAStep.GasColumnsSmall)
    (hpaid : clusterScoreIntegralBound)
    (htwo : ChartResponseComparison) (hsc : BondScoreProperties) (hT : TiltedGibbsComparison)
    (hgas : GasSumNearBlockBound) (hcf : CouplingFloorExists)
    (hcfg : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hmass : SettingMassEqIntegral)
    (hpot : PotentialFactorization) (hagree : LocalSettingsAgree)
    (hborel : settingMeanMeasurableStatement) (hP : MeanOfProductStatement)
    (hC : ActivityConditionalLawsStatement) (hwn : WeightsCloseToBlockMeans) :
    GasSupportMeanUnderTilt := by apply _root_.YangMills.Construction.TiltedGasResponse.gasSupportMeanUnderTilt_holds <;> assumption
end ResponseInTheExpansion
end YangMills.Construction
end
