import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfTheGas
import YangMills.Construction.ClusterExpansionOfAStep.ConfigurationsOfTheGasAreSettings
import YangMills.Construction.ClusterExpansionOfAStep.FieldOfASettingIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.GasSumsAtABlockProof
import YangMills.Construction.ClusterExpansionOfAStep.MassOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.PotentialOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.ShiftsOfTwoSettings
import YangMills.Construction.FreeEnergiesOfTheFlow.LabelsOfAConfiguration
import YangMills.Construction.FreeEnergiesOfTheFlow.MeansInTheSettingsAreBorel
import YangMills.Construction.FreeEnergiesOfTheFlow.SupportVariablesHaveTheirSizes
import YangMills.Construction.ResponseInTheExpansion.FarSpinsMoveAVariable
import YangMills.Construction.ResponseInTheExpansion.ResponseInTwoSettings
import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABond
import YangMills.Construction.ResponseInTheExpansion.WeightsNearTheirMeans
import YangMills.Construction.TransfersOffTheWalk.SettingsOfConfigurationsAgree
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction
open Dobrushin FreeEnergies WeightedResponses StepSettings StepGas RenormalizationStepParameters StepCosts TorusFields
  TorusLumps CoreColumns BlockOffsets
open BlockAverages hiding unitStep
namespace ResponseInTheExpansion
namespace FarSpin
set_option linter.unusedSectionVars false
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
theorem spinLabelScore_eq_zero_of_not_mem {s : R.labels.Ω → ℝ} {i : G.GasSpin}
    {y : TorusSite (n * R.params.side)} (hy : y ∉ i.1.2) (v : G.SpinValue i) :
    spinLabelScore s G i y v = 0 := by
  classical
  rcases v with u | w
  · rfl
  · simp [spinLabelScore, hy]
theorem isAdmissible_update_vacant {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ) (i : G.GasSpin) :
    G.pairConstraint.IsAdmissible (Function.update σ i (G.pairConstraint.vacant i)) := by
  intro a b hab
  by_cases ha : a = i
  · subst ha
    rw [Function.update_self, Function.update_of_ne hab.symm]
    exact G.pairConstraint.vacant_compatible _ _ _
  · by_cases hb : b = i
    · subst hb
      rw [Function.update_self, Function.update_of_ne ha]
      exact G.pairConstraint.compatible_symm _ _ _ _ (G.pairConstraint.vacant_compatible _ _ _)
    · rw [Function.update_of_ne ha, Function.update_of_ne hb]
      exact hσ a b hab
section Means
variable {free : Finset (TorusBond (n * R.params.side))}
theorem chartDensity_eq_zero {s : ChartSetting R n} {η : FreeCoords s.free} (h : ¬ s.InBalls η) :
    chartDensity s η = 0 := by
  unfold chartDensity ChartSetting.cutoffProduct
  simp only [ChartSetting.InBalls, not_forall, not_le] at h
  obtain ⟨b, hb⟩ := h
  rw [Finset.prod_eq_zero (Finset.mem_univ b), zero_mul]
  unfold ColdStepAtMirrorFrames.cutoffFactor
  rw [if_neg (not_lt.mpr hb.le)]
theorem chartDensity_nonneg (s : ChartSetting R n) (η : FreeCoords s.free) : 0 ≤ chartDensity s η := by
  unfold chartDensity ChartSetting.cutoffProduct
  refine mul_nonneg (Finset.prod_nonneg fun b _ => ?_) (Real.exp_pos _).le
  unfold ColdStepAtMirrorFrames.cutoffFactor
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl
theorem settingMean_liveCase {s : ChartSetting R n}
    (hl : ∀ η, s.InBalls η → IsLiveState R.params R.coupling R.labelWeight (s.field η) s.support s.labelling)
    (bad : Finset (TorusBond (n * R.params.side))) (F : CaseFunction R n) :
    settingMean s bad (liveCaseFunction F) =
      weightedMean (chartDensity s) fun η => F (s.field η) s.support s.labelling bad s.bases := by
  classical
  unfold settingMean weightedMean
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  by_cases h : s.InBalls η
  · simp only [liveCaseFunction, if_pos (hl η h)]
  · simp only [chartDensity_eq_zero h, mul_zero]
theorem integrable_mul_chartDensity {s : ChartSetting R n} (hd : Integrable (chartDensity s))
    {g : FreeCoords s.free → ℝ} (hg : Measurable g) {Q : ℝ} (hQ : ∀ η, s.InBalls η → |g η| ≤ Q) :
    Integrable fun η => g η * chartDensity s η := by
  refine Integrable.mono' (hd.const_mul Q) (hg.aestronglyMeasurable.mul hd.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (chartDensity_nonneg s η)]
  by_cases h : s.InBalls η
  · exact mul_le_mul_of_nonneg_right (hQ η h) (chartDensity_nonneg s η)
  · simp [chartDensity_eq_zero h]
theorem abs_weightedMean_le {s : ChartSetting R n} (hd : Integrable (chartDensity s))
    (hm : 0 < ∫ η, chartDensity s η) {g : FreeCoords s.free → ℝ} {Q : ℝ}
    (hQ : ∀ η, s.InBalls η → |g η| ≤ Q) :
    |weightedMean (chartDensity s) g| ≤ Q := by
  have hQ0 : 0 ≤ Q ∨ ∀ η, ¬ s.InBalls η := by
    by_cases h : ∃ η, s.InBalls η
    · obtain ⟨η, hη⟩ := h
      exact Or.inl ((abs_nonneg _).trans (hQ η hη))
    · exact Or.inr fun η hη => h ⟨η, hη⟩
  rcases hQ0 with hQ0 | hno
  · unfold weightedMean
    rw [abs_div, abs_of_pos hm, div_le_iff₀ hm]
    have : ‖∫ η, g η * chartDensity s η‖ ≤ ∫ η, Q * chartDensity s η := by
      refine norm_integral_le_of_norm_le (hd.const_mul Q) (Filter.Eventually.of_forall fun η => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (chartDensity_nonneg s η)]
      by_cases h : s.InBalls η
      · exact mul_le_mul_of_nonneg_right (hQ η h) (chartDensity_nonneg s η)
      · simp [chartDensity_eq_zero h]
    rw [integral_const_mul] at this
    simpa [Real.norm_eq_abs] using this
  · exfalso
    have : ∀ η, chartDensity s η = 0 := fun η => chartDensity_eq_zero (hno η)
    simp [this] at hm
theorem weightedMean_sum {s : ChartSetting R n} {κ : Type} (S : Finset κ) (g : κ → FreeCoords s.free → ℝ)
    (hi : ∀ k ∈ S, Integrable fun η => g k η * chartDensity s η) :
    weightedMean (chartDensity s) (fun η => ∑ k ∈ S, g k η) =
      ∑ k ∈ S, weightedMean (chartDensity s) (g k) := by
  unfold weightedMean
  rw [← Finset.sum_div, ← integral_finsetSum S hi]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  simp only [Finset.sum_mul]
theorem weightedMean_add {s : ChartSetting R n} {g₁ g₂ : FreeCoords s.free → ℝ}
    (h₁ : Integrable fun η => g₁ η * chartDensity s η) (h₂ : Integrable fun η => g₂ η * chartDensity s η) :
    weightedMean (chartDensity s) (fun η => g₁ η + g₂ η) =
      weightedMean (chartDensity s) g₁ + weightedMean (chartDensity s) g₂ := by
  unfold weightedMean
  rw [← add_div, ← integral_add h₁ h₂]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  simp only [add_mul]
theorem weightedMean_const_mul {s : ChartSetting R n} (c : ℝ) (g : FreeCoords s.free → ℝ) :
    weightedMean (chartDensity s) (fun η => c * g η) = c * weightedMean (chartDensity s) g := by
  unfold weightedMean
  rw [mul_div_assoc', ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  simp only [mul_assoc]
theorem weightedMean_sub_const {s : ChartSetting R n} (hd : Integrable (chartDensity s))
    (hm : 0 < ∫ η, chartDensity s η) {g : FreeCoords s.free → ℝ}
    (h : Integrable fun η => g η * chartDensity s η) (c : ℝ) :
    weightedMean (chartDensity s) (fun η => g η - c) = weightedMean (chartDensity s) g - c := by
  unfold weightedMean
  have e : ∫ η, (g η - c) * chartDensity s η =
      (∫ η, g η * chartDensity s η) - c * ∫ η, chartDensity s η := by
    rw [← integral_const_mul, ← integral_sub h (hd.const_mul c)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only [sub_mul]
  rw [e, sub_div, mul_div_assoc, div_self hm.ne', mul_one]
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
structure FarSpinSetup (A : ResponseSetup R) (G : GasGround R n) : Prop where
  admissible : A.IsAdmissible
  params_admissible : R.params.Admissible
  side_odd : Odd R.params.side
  hasExpansions : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
    R.clusterFactor R.siteDensity
  isBlockSide : IsBlockTorusSide R.params (n * R.params.side)
  n₀_le : R.params.n₀ ≤ n
  functional_trivial_pos : 0 < R.functional (n * R.params.side) (trivialField (n * R.params.side))
  setting_admissible : ∀ σ, G.pairConstraint.IsAdmissible σ → (configSetting G σ).IsAdmissible
  density_integrable : ∀ σ, G.pairConstraint.IsAdmissible σ → Integrable (chartDensity (configSetting G σ)) ∧
    0 < ∫ η, chartDensity (configSetting G σ) η
  settings_agree : LocalSettingsAgree
  measurable_mean : ∀ F : CaseFunction R n, (∀ (Yt : Finset (TorusSite (n * R.params.side)))
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => F p.1 Yt p.2 bad b) →
    open Classical in Measurable fun σ : G.Config =>
      if G.pairConstraint.IsAdmissible σ then settingMean (configSetting G σ) (G.badBondsOf σ) F else 0
  one_le_coupling : 1 ≤ R.params.coupling
  C₀_ge : 12 + 40 * R.params.coupling ≤ A.responseParams.C₀
  abs_bondScore_le : ∀ (W : TorusField (n * R.params.side)) (V : TorusField n) (b : BaseChoice R.params.side n)
    (c : TorusBond n), |bondScore R.params R.coupling W V b c| ≤ 2
  measurable_bondScore : ∀ (b : BaseChoice R.params.side n) (c : TorusBond n),
    Measurable fun p : TorusField (n * R.params.side) × TorusField n => bondScore R.params R.coupling p.1 p.2 b c
  two_settings : ∀ (s s' : ChartSetting R n) (Y : TorusSite n) (m : ℕ), s.IsAdmissible → s'.IsAdmissible →
    SettingsAgreeNear s s' Y Y m → (R.range : ℝ) / (4 * R.params.side) ≤ m →
    (∀ o, o ∈ centredCube R.params.side →
      ∀ h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)),
      |chartResponse A s (fineSite R.params.side Y 0 o) h - chartResponse A s' (fineSite R.params.side Y 0 o) h| ≤
        (1 + chartSiteScore A s (fineSite R.params.side Y 0 o)) * Real.exp (-(R.params.rt * m / 2 ^ 5)) *
          weightNorm R.params.side R.depth h) ∧
    ∀ c : (Fin 4 → ℤ) × Fin 4, IsBondAtOrigin c →
      |chartBondScore s (bondFrom Y c) - chartBondScore s' (bondFrom Y c)| ≤ Real.exp (-(R.params.rt * m / 2 ^ 5))
variable {A : ResponseSetup R}
theorem FarSpinSetup.isLiveState (h : FarSpinSetup A G) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    (η : FreeCoords (configSetting G σ).free) (hη : (configSetting G σ).InBalls η) :
    IsLiveState R.params R.coupling R.labelWeight ((configSetting G σ).field η) (configSetting G σ).support
      (configSetting G σ).labelling := by
  have hs := h.setting_admissible σ hσ
  have hh : IsHullState R.params (clusterRange R.coupling) ((configSetting G σ).field η)
      (configSetting G σ).support := hs.isHull η hη
  refine ⟨hh, ?_⟩
  rw [h.hasExpansions.form (n * R.params.side) h.isBlockSide _ _ _ hh]
  have hΦ : 0 < ∏ X ∈ chainComponents (clusterRange R.coupling) (configSetting G σ).support,
      R.clusterFactor (n * R.params.side) ((configSetting G σ).field η) (configSetting G σ).support
        (configSetting G σ).labelling X := by
    refine Finset.prod_pos fun X hX => ?_
    exact lt_of_le_of_ne (h.hasExpansions.factor_nonneg (n * R.params.side) h.isBlockSide _ _ _ X)
      (Ne.symm (hs.factor_ne_zero η hη X hX))
  have := h.functional_trivial_pos
  positivity
theorem FarSpinSetup.recordedSiteScore_nonneg (h : FarSpinSetup A G) (y : TorusSite (n * R.params.side)) :
    0 ≤ recordedSiteScore A G y :=
  siteScore_nonneg h.admissible.price.nonneg _ _ _
theorem spinLabelScore_nonneg {s : R.labels.Ω → ℝ} (hs : ∀ w, 0 ≤ s w) (i : G.GasSpin)
    (y : TorusSite (n * R.params.side)) (v : G.SpinValue i) :
    0 ≤ spinLabelScore s G i y v := by
  classical
  rcases v with u | w
  · simp [spinLabelScore]
  · simp only [spinLabelScore, Sum.elim_inr]
    split_ifs
    · exact hs _
    · exact le_rfl
theorem FarSpinSetup.configSiteScore_nonneg (h : FarSpinSetup A G) (y : TorusSite (n * R.params.side))
    (σ : G.Config) : 0 ≤ configSiteScore A G y σ :=
  siteScore_nonneg h.admissible.price.nonneg _ _ _
theorem FarSpinSetup.siteResponseMean_eq (h : FarSpinSetup A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (y : TorusSite (n * R.params.side)) :
    siteResponseMean A G f y σ = chartResponse A (configSetting G σ) y f :=
  settingMean_liveCase (fun η hη => h.isLiveState hσ η hη) _ _
theorem FarSpinSetup.bondScoreMean_eq (h : FarSpinSetup A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) (c : TorusBond n) :
    bondScoreMean G c σ = chartBondScore (configSetting G σ) c :=
  settingMean_liveCase (fun η hη => h.isLiveState hσ η hη) _ _
theorem FarSpinSetup.abs_centeredHullResponse_le (h : FarSpinSetup A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)}
    (hsz : weightNorm R.params.side R.depth f ≤ 1) (y : TorusSite (n * R.params.side))
    (η : FreeCoords (configSetting G σ).free) (hη : (configSetting G σ).InBalls η) :
    |centeredHullResponse A.cold A.hull (n * R.params.side) y ((configSetting G σ).field η)
      (configSetting G σ).support (configSetting G σ).labelling f| ≤
      A.responseParams.C₀ + configSiteScore A G y σ := by
  have h1 := h.admissible.bounds.size_hull (n * R.params.side) h.isBlockSide y _ _ _ (h.isLiveState hσ η hη) f
  have hC : 0 ≤ A.responseParams.C₀ := by
    have h3 := h.one_le_coupling
    have h4 := h.C₀_ge
    linarith
  have h2 : 0 ≤ A.responseParams.C₀ + configSiteScore A G y σ := add_nonneg hC (h.configSiteScore_nonneg y σ)
  calc _ ≤ _ := h1
    _ ≤ (A.responseParams.C₀ + configSiteScore A G y σ) * 1 := mul_le_mul_of_nonneg_left hsz h2
    _ = _ := mul_one _
theorem setGap_le_supDist {X X' : Finset (TorusSite n)} {y y' : TorusSite n} (hy : y ∈ X) (hy' : y' ∈ X') :
    setGap X X' ≤ supDist y y' :=
  Nat.sInf_le ⟨y, hy, y', hy', rfl⟩
theorem core_nonempty (j : G.GasSpin) : j.1.core.Nonempty := by apply _root_.YangMills.Construction.StepGas.core_nonempty_of_gasSpin <;> assumption
theorem FarSpinSetup.settingsAgreeNear_update_vacant (h : FarSpinSetup A G) (σ : G.Config) (j : G.GasSpin)
    {Y : TorusSite n} {m : ℕ} (hg : m + 2 ≤ setGap {Y} j.1.core) :
    SettingsAgreeNear (configSetting G σ) (configSetting G (Function.update σ j (G.pairConstraint.vacant j)))
      Y Y m := by
  classical
  obtain ⟨a, ha⟩ := core_nonempty j
  have h1 : setGap {Y} j.1.core ≤ supDist Y a := setGap_le_supDist (Finset.mem_singleton_self Y) ha
  have h2 := SettingShifts.two_mul_supDist_le Y a
  refine h.settings_agree R n G σ _ Y m h.side_odd (by omega) fun i hi => ?_
  obtain ⟨e, he, hc⟩ := hi
  by_cases hij : i = j
  · subst hij
    exfalso
    have h3 : setGap {Y} i.1.core ≤ supDist Y (Y + siteOfInt e) :=
      setGap_le_supDist (Finset.mem_singleton_self Y) hc
    have h4 : supDist Y (Y + siteOfInt e) ≤ m := supDist_add_siteOfInt_le Y e m fun l => by
      have h1 : |e l| ≤ (m : ℤ) := he l
      rw [Int.abs_eq_natAbs] at h1
      omega
    omega
  · rw [Function.update_of_ne hij]
theorem FarSpinSetup.measurableSet_isLiveState (h : FarSpinSetup A G) (Yt : Finset (TorusSite (n * R.params.side))) :
    MeasurableSet {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) |
      IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} := by
  classical
  have hb := (h.hasExpansions.borel (n * R.params.side) h.isBlockSide Yt).1
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
theorem FarSpinSetup.measurable_centeredHull_case (h : FarSpinSetup A G)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (y : TorusSite (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      liveCaseFunction (R := R) (n := n)
        (fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f) p.1 Yt p.2 bad b := by
  classical
  have h1 := h.admissible.bounds.hull_borel (n * R.params.side) h.isBlockSide y Yt f
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
theorem FarSpinSetup.integrable_centeredHull (h : FarSpinSetup A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)}
    (hsz : weightNorm R.params.side R.depth f ≤ 1) (y : TorusSite (n * R.params.side)) :
    Integrable fun η => centeredHullResponse A.cold A.hull (n * R.params.side) y ((configSetting G σ).field η)
      (configSetting G σ).support (configSetting G σ).labelling f * chartDensity (configSetting G σ) η := by
  classical
  set s := configSetting G σ with hs
  set g : FreeCoords s.free → ℝ := fun η => liveCaseFunction (R := R) (n := n)
    (fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f)
    (s.field η) s.support s.labelling (G.badBondsOf σ) s.bases with hg
  have hm : Measurable g := by
    have h1 := h.measurable_centeredHull_case f y s.support (G.badBondsOf σ) s.bases
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
theorem FarSpinSetup.integrable_bondScore (h : FarSpinSetup A G) {σ : G.Config}
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
        caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) := by
  classical
  have isb : ∀ Y, Integrable fun η => blockBondScores (s.field η) s.coarse s.bases Y * chartDensity s η := by
    intro Y
    unfold blockBondScores
    simp only [Finset.sum_mul, add_mul]
    exact integrable_finsetSum _ fun i _ => (is _).add (is _)
  have ihb : ∀ Y, Integrable fun η =>
      (blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (s.field η) s.coarse s.bases Y) *
        chartDensity s η := by
    intro Y
    refine ((isb Y).const_mul (blockMean R.params.side (R.depth + 1) n Y f)).congr
      (Filter.Eventually.of_forall fun η => ?_)
    simp only [mul_assoc]
  have ihs : Integrable fun η => (∑ y ∈ lowerSites f, centeredHullResponse A.cold A.hull (n * R.params.side) y
      (s.field η) s.support s.labelling f) * chartDensity s η := by
    simp only [Finset.sum_mul]
    exact integrable_finsetSum _ fun y _ => ih y
  have ibs₀ : Integrable fun η => (∑ Y ∈ upperSites f,
      blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (s.field η) s.coarse s.bases Y) *
        chartDensity s η := by
    simp only [Finset.sum_mul]
    exact integrable_finsetSum _ fun Y _ => ihb Y
  have ibs : Integrable fun η => (R.params.coupling / 2 * A.coeff * ∑ Y ∈ upperSites f,
      blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (s.field η) s.coarse s.bases Y) *
        chartDensity s η := by
    refine (ibs₀.const_mul (R.params.coupling / 2 * A.coeff)).congr (Filter.Eventually.of_forall fun η => ?_)
    simp only [mul_assoc]
  have iadd : Integrable fun η => ((∑ y ∈ lowerSites f, centeredHullResponse A.cold A.hull (n * R.params.side) y
      (s.field η) s.support s.labelling f) +
      R.params.coupling / 2 * A.coeff * ∑ Y ∈ upperSites f,
        blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (s.field η) s.coarse s.bases Y) *
          chartDensity s η := by
    refine (ihs.add ibs).congr (Filter.Eventually.of_forall fun η => ?_)
    simp only [Pi.add_apply, add_mul]
  have s1 := weightedMean_sub_const hdi hdm iadd
    (caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f))
  have s2 := weightedMean_add ihs ibs
  have s3 := weightedMean_sum (s := s) (lowerSites f)
    (fun y η => centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η) s.support s.labelling f)
    (fun y _ => ih y)
  have s4 := weightedMean_const_mul (s := s) (R.params.coupling / 2 * A.coeff) (fun η => ∑ Y ∈ upperSites f,
    blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (s.field η) s.coarse s.bases Y)
  have s5 := weightedMean_sum (s := s) (upperSites f)
    (fun Y η => blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (s.field η) s.coarse s.bases Y)
    (fun Y _ => ihb Y)
  have s6 : ∀ Y, weightedMean (chartDensity s)
      (fun η => blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (s.field η) s.coarse s.bases Y) =
      blockMean R.params.side (R.depth + 1) n Y f *
        ∑ i : Fin 4, (weightedMean (chartDensity s)
            (fun η => bondScore R.params R.coupling (s.field η) s.coarse s.bases (Y, i)) +
          weightedMean (chartDensity s)
            (fun η => bondScore R.params R.coupling (s.field η) s.coarse s.bases (Y - unitStep n i, i))) := by
    intro Y
    rw [weightedMean_const_mul]
    congr 1
    have t1 := weightedMean_sum (s := s) (Finset.univ : Finset (Fin 4))
      (fun i η => bondScore R.params R.coupling (s.field η) s.coarse s.bases (Y, i) +
        bondScore R.params R.coupling (s.field η) s.coarse s.bases (Y - unitStep n i, i))
      (fun i _ => by
        refine ((is (Y, i)).add (is (Y - unitStep n i, i))).congr (Filter.Eventually.of_forall fun η => ?_)
        simp only [Pi.add_apply, add_mul])
    have t2 : (fun η => blockBondScores (s.field η) s.coarse s.bases Y) = fun η => ∑ i : Fin 4,
        (bondScore R.params R.coupling (s.field η) s.coarse s.bases (Y, i) +
          bondScore R.params R.coupling (s.field η) s.coarse s.bases (Y - unitStep n i, i)) := rfl
    rw [t2, t1]
    exact Finset.sum_congr rfl fun i _ => weightedMean_add (is _) (is _)
  have e1 : (fun η => centeredSupportResponse A s.coarse f (s.field η) s.support s.labelling bad s.bases) =
      fun η => ((∑ y ∈ lowerSites f, centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η)
          s.support s.labelling f) +
        R.params.coupling / 2 * A.coeff * ∑ Y ∈ upperSites f,
          blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (s.field η) s.coarse s.bases Y) -
        caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) := rfl
  rw [e1, s1, s2, s3, s4, s5, Finset.sum_congr rfl fun Y _ => s6 Y]
theorem FarSpinSetup.gasSupportMean_eq (h : FarSpinSetup A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)}
    (hsz : weightNorm R.params.side R.depth f ≤ 1) :
    gasSupportMean A G f σ = ∑ y ∈ lowerSites f, siteResponseMean A G f y σ +
      R.params.coupling / 2 * A.coeff * ∑ Y ∈ upperSites f, blockMean R.params.side (R.depth + 1) n Y f *
        ∑ i : Fin 4, (bondScoreMean G (Y, i) σ + bondScoreMean G (Y - unitStep n i, i) σ) -
      caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) := by
  classical
  obtain ⟨hdi, hdm⟩ := h.density_integrable σ hσ
  have e0 : gasSupportMean A G f σ = weightedMean (chartDensity (configSetting G σ)) fun η =>
      centeredSupportResponse A (configSetting G σ).coarse f ((configSetting G σ).field η)
        (configSetting G σ).support (configSetting G σ).labelling (G.badBondsOf σ) (configSetting G σ).bases :=
    settingMean_liveCase (fun η hη => h.isLiveState hσ η hη) _ _
  have e2 : ∀ y, weightedMean (chartDensity (configSetting G σ))
      (fun η => centeredHullResponse A.cold A.hull (n * R.params.side) y ((configSetting G σ).field η)
        (configSetting G σ).support (configSetting G σ).labelling f) = siteResponseMean A G f y σ :=
    fun y => (settingMean_liveCase (s := configSetting G σ) (fun η hη => h.isLiveState hσ η hη)
      (G.badBondsOf σ)
      (fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f)).symm
  have e3 : ∀ c, weightedMean (chartDensity (configSetting G σ))
      (fun η => bondScore R.params R.coupling ((configSetting G σ).field η) (configSetting G σ).coarse
        (configSetting G σ).bases c) = bondScoreMean G c σ :=
    fun c => (settingMean_liveCase (s := configSetting G σ) (fun η hη => h.isLiveState hσ η hη)
      (G.badBondsOf σ) (fun W _ _ _ b => bondScore R.params R.coupling W G.coarse b c)).symm
  rw [e0, weightedMean_centeredSupportResponse (G.badBondsOf σ) hdi hdm
    (fun y => h.integrable_centeredHull hσ hsz y) (fun c => h.integrable_bondScore hσ c)]
  rw [Finset.sum_congr rfl fun y _ => e2 y]
  congr 3
  refine Finset.sum_congr rfl fun Y _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [e3, e3]
def spinLabelSum (A : ResponseSetup R) (G : GasGround R n) (y : TorusSite (n * R.params.side)) (σ : G.Config) : ℝ :=
  ∑ i, spinLabelScore A.score G i y (σ i)
theorem FarSpinSetup.configSiteScore_le (h : FarSpinSetup A G) (y : TorusSite (n * R.params.side)) (σ : G.Config) :
    configSiteScore A G y σ ≤ recordedSiteScore A G y + spinLabelSum A G y σ :=
  FreeEnergies.siteScore_configSetting_le h.admissible.price.nonneg σ y
theorem update_vacant_eq {σ σ' : G.Config} {j : G.GasSpin} (hd : ∀ k, k ≠ j → σ k = σ' k) :
    Function.update σ j (G.pairConstraint.vacant j) = Function.update σ' j (G.pairConstraint.vacant j) := by
  funext k
  by_cases hk : k = j
  · subst hk
    simp
  · rw [Function.update_of_ne hk, Function.update_of_ne hk, hd k hk]
theorem FarSpinSetup.abs_siteResponseMean_sub_le (h : FarSpinSetup A G) {σ σ' : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) (hσ' : G.pairConstraint.IsAdmissible σ')
    {j : G.GasSpin} (hd : ∀ k, k ≠ j → σ k = σ' k)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)}
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
  have b1 := (h.two_settings _ _ _ m (h.setting_admissible σ hσ) (h.setting_admissible _ h0) a1 hm).1 o ho f
  have b2 := (h.two_settings _ _ _ m (h.setting_admissible σ' hσ') (h.setting_admissible _ h0) a2 hm).1 o ho f
  rw [← hyo] at b1 b2
  rw [h.siteResponseMean_eq hσ, h.siteResponseMean_eq hσ']
  set E := Real.exp (-(R.params.rt * m / 2 ^ 5)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have c1 : (1 + chartSiteScore A (configSetting G σ) y) * E * weightNorm R.params.side R.depth f ≤
      (1 + configSiteScore A G y σ) * E := by
    have : 0 ≤ (1 + configSiteScore A G y σ) * E :=
      mul_nonneg (by linarith [h.configSiteScore_nonneg y σ]) hE0
    calc _ ≤ (1 + configSiteScore A G y σ) * E * 1 := mul_le_mul_of_nonneg_left hsz this
      _ = _ := mul_one _
  have c2 : (1 + chartSiteScore A (configSetting G σ') y) * E * weightNorm R.params.side R.depth f ≤
      (1 + configSiteScore A G y σ') * E := by
    have : 0 ≤ (1 + configSiteScore A G y σ') * E :=
      mul_nonneg (by linarith [h.configSiteScore_nonneg y σ']) hE0
    calc _ ≤ (1 + configSiteScore A G y σ') * E * 1 := mul_le_mul_of_nonneg_left hsz this
      _ = _ := mul_one _
  calc _ ≤ |chartResponse A (configSetting G σ) y f - chartResponse A (configSetting G σ₀) y f| +
        |chartResponse A (configSetting G σ') y f - chartResponse A (configSetting G σ₀) y f| := by
        rw [abs_sub_comm (chartResponse A (configSetting G σ') y f)]
        exact abs_sub_le _ _ _
    _ ≤ (1 + configSiteScore A G y σ) * E + (1 + configSiteScore A G y σ') * E :=
        add_le_add (b1.trans c1) (b2.trans c2)
    _ = _ := by ring
theorem FarSpinSetup.abs_bondScoreMean_sub_le (h : FarSpinSetup A G) {σ σ' : G.Config}
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
  have b1 := (h.two_settings _ _ _ m (h.setting_admissible σ hσ) (h.setting_admissible _ h0) a1 hm).2 c hc
  have b2 := (h.two_settings _ _ _ m (h.setting_admissible σ' hσ') (h.setting_admissible _ h0) a2 hm).2 c hc
  rw [h.bondScoreMean_eq hσ, h.bondScoreMean_eq hσ']
  calc _ ≤ |chartBondScore (configSetting G σ) (bondFrom Y c) - chartBondScore (configSetting G σ₀) (bondFrom Y c)| +
        |chartBondScore (configSetting G σ') (bondFrom Y c) - chartBondScore (configSetting G σ₀) (bondFrom Y c)| := by
        rw [abs_sub_comm (chartBondScore (configSetting G σ') (bondFrom Y c))]
        exact abs_sub_le _ _ _
    _ ≤ _ := by linarith
end Atoms
section Parents
theorem parentBlock_mem_weightSupportSites {L t n : ℕ} [NeZero L] [NeZero n] (f : PlaquetteWeight (fineSide L (t + 1) n))
    {y : TorusSite (n * L)} (hy : y ∈ weightSupportSites L t (n * L) f) :
    parentBlock L y ∈ weightSupportSites L (t + 1) n f := by
  classical
  simp only [weightSupportSites, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  obtain ⟨p, ⟨ho, c, hc, hb⟩, hf⟩ := hy
  refine ⟨p, ⟨ho, c, hc, ?_⟩, hf⟩
  show c ∈ (sitesInBlocks L {parentBlock L y}).biUnion fun y => fineBlock L t (n * L) y
  exact Finset.mem_biUnion.mpr ⟨y, by simp [sitesInBlocks], hb⟩
theorem image_parentBlock_weightSupportSites {L t n : ℕ} [NeZero L] [NeZero n]
    (f : PlaquetteWeight (fineSide L (t + 1) n)) :
    (open Classical in (weightSupportSites L t (n * L) f).image (parentBlock L)) =
      weightSupportSites L (t + 1) n f := by
  classical
  ext Y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact parentBlock_mem_weightSupportSites f hy
  · intro hY
    simp only [weightSupportSites, Finset.mem_filter, Finset.mem_univ, true_and] at hY
    obtain ⟨p, ⟨ho, c, hc, hb⟩, hf⟩ := hY
    have hb' : c ∈ (sitesInBlocks L {Y}).biUnion fun y => fineBlock L t (n * L) y := hb
    obtain ⟨y, hy, hcy⟩ := Finset.mem_biUnion.mp hb'
    refine ⟨y, ?_, by simpa [sitesInBlocks] using hy⟩
    simp only [weightSupportSites, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨p, ⟨ho, c, hc, hcy⟩, hf⟩
theorem weightLipschitz_le_succ {L : ℕ} [NeZero L] (t : ℕ) {m : ℕ} [NeZero m] (hL : 1 ≤ L) (h : PlaquetteWeight m) :
    weightLipschitz L t h ≤ weightLipschitz L (t + 1) h := by
  unfold weightLipschitz
  refine ciSup_mono (Set.finite_range _).bddAbove fun pp => ?_
  unfold barycentreDist
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  by_cases h0 : (supDist (doubledBarycentre pp.1.1) (doubledBarycentre pp.2.1) : ℝ) = 0
  · simp [h0]
  · have hd : 0 < (supDist (doubledBarycentre pp.1.1) (doubledBarycentre pp.2.1) : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h0)
    have hp : (0 : ℝ) < (L : ℝ) ^ t := by positivity
    have e1 : (supDist (doubledBarycentre pp.1.1) (doubledBarycentre pp.2.1) : ℝ) / (2 * (L : ℝ) ^ (t + 1)) ≤
        (supDist (doubledBarycentre pp.1.1) (doubledBarycentre pp.2.1) : ℝ) / (2 * (L : ℝ) ^ t) := by
      apply div_le_div_of_nonneg_left hd.le (by positivity)
      rw [pow_succ]
      nlinarith
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) e1
theorem weightNorm_le_succ {L : ℕ} [NeZero L] (t : ℕ) {m : ℕ} [NeZero m] (hL : 1 ≤ L) (h : PlaquetteWeight m) :
    weightNorm L t h ≤ weightNorm L (t + 1) h :=
  max_le_max le_rfl (weightLipschitz_le_succ t hL h)
end Parents
section Main
variable {A : ResponseSetup R}
theorem abs_gasSupportMean_sub_le (h : FarSpinSetup A G)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (hhat : ∀ Y, |blockMean R.params.side (R.depth + 1) n Y f| ≤ 1) (hne : (upperSites f).Nonempty)
    {σ₁ σ₀ : G.Config} (h₁ : G.pairConstraint.IsAdmissible σ₁) (h₀ : G.pairConstraint.IsAdmissible σ₀)
    {j : G.GasSpin} (hd : ∀ k, k ≠ j → σ₁ k = σ₀ k) {m : ℕ}
    (hm : (R.range : ℝ) / (4 * R.params.side) ≤ m) (hg : ∀ Y ∈ upperSites f, m + 2 ≤ setGap {Y} j.1.core) :
    |gasSupportMean A G f σ₁ - gasSupportMean A G f σ₀| ≤
      4 * lowerSizeConst A f * spinScore A G (lowerSites f) σ₀ * Real.exp (-(R.params.rt * m / 2 ^ 5)) := by
  classical
  set E := Real.exp (-(R.params.rt * m / 2 ^ 5)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set As := lowerSites f with hAs
  set Ap := upperSites f with hAp
  have hpar : (open Classical in As.image (parentBlock R.params.side)) = Ap :=
    image_parentBlock_weightSupportSites f
  have hcard : Ap.card ≤ As.card := by
    rw [← hpar]
    exact Finset.card_image_le
  have hnA : As.Nonempty := by
    obtain ⟨Y, hY⟩ := hne
    rw [← hpar] at hY
    obtain ⟨y, hy, -⟩ := Finset.mem_image.mp hY
    exact ⟨y, hy⟩
  set sh : TorusSite (n * R.params.side) → ℝ := fun y => recordedSiteScore A G y + spinLabelSum A G y σ₀ with hsh
  have hy_off : ∀ y ∈ As, y ∉ j.1.2 := by
    intro y hy hyj
    have h1 : parentBlock R.params.side y ∈ j.1.core :=
      GasSupport.parentBlock_mem_core (Finset.mem_union_right _ hyj)
    have h2 := setGap_le_supDist (Finset.mem_singleton_self (parentBlock R.params.side y)) h1
    rw [supDist_self] at h2
    have h3 := hg _ (parentBlock_mem_weightSupportSites f hy)
    omega
  have hlab : ∀ y ∈ As, spinLabelSum A G y σ₁ = spinLabelSum A G y σ₀ := by
    intro y hy
    unfold spinLabelSum
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i = j
    · subst hi
      rw [spinLabelScore_eq_zero_of_not_mem (hy_off y hy), spinLabelScore_eq_zero_of_not_mem (hy_off y hy)]
    · rw [hd i hi]
  rw [h.gasSupportMean_eq h₁ hsz, h.gasSupportMean_eq h₀ hsz]
  have site : ∀ y ∈ As, |siteResponseMean A G f y σ₁ - siteResponseMean A G f y σ₀| ≤ (2 + 2 * sh y) * E := by
    intro y hy
    have a := h.abs_siteResponseMean_sub_le h₁ h₀ hd hsz hm (hg _ (parentBlock_mem_weightSupportSites f hy))
    have b1 := h.configSiteScore_le y σ₁
    have b2 := h.configSiteScore_le y σ₀
    rw [hlab y hy] at b1
    refine a.trans (mul_le_mul_of_nonneg_right ?_ hE0)
    simp only [hsh]
    linarith
  have bond : ∀ Y ∈ Ap, ∀ i : Fin 4, |bondScoreMean G (Y, i) σ₁ - bondScoreMean G (Y, i) σ₀| ≤ 2 * E ∧
      |bondScoreMean G (Y - unitStep n i, i) σ₁ - bondScoreMean G (Y - unitStep n i, i) σ₀| ≤ 2 * E := by
    intro Y hY i
    constructor
    · have := h.abs_bondScoreMean_sub_le h₁ h₀ hd hm (hg Y hY) (c := (0, i)) (Or.inl rfl)
      have e1 : bondFrom Y ((0 : Fin 4 → ℤ), i) = (Y, i) := by
        simp only [bondFrom]
        congr 1
        funext l
        simp [siteOfInt]
      rwa [e1] at this
    · have := h.abs_bondScoreMean_sub_le h₁ h₀ hd hm (hg Y hY) (c := (-(Pi.single i 1), i)) (Or.inr rfl)
      have e1 : bondFrom Y ((-(Pi.single i 1) : Fin 4 → ℤ), i) = (Y - unitStep n i, i) := by
        simp only [bondFrom]
        congr 1
        rw [unitStep_eq_siteOfInt, sub_eq_add_neg]
        congr 1
        funext l
        simp [siteOfInt]
      rwa [e1] at this
  set cc := R.params.coupling / 2 * A.coeff with hcc
  set vv := caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) with hvv
  have e1 : (∑ y ∈ As, siteResponseMean A G f y σ₁ + cc * ∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f *
        ∑ i : Fin 4, (bondScoreMean G (Y, i) σ₁ + bondScoreMean G (Y - unitStep n i, i) σ₁) - vv) -
      (∑ y ∈ As, siteResponseMean A G f y σ₀ + cc * ∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f *
        ∑ i : Fin 4, (bondScoreMean G (Y, i) σ₀ + bondScoreMean G (Y - unitStep n i, i) σ₀) - vv) =
      ∑ y ∈ As, (siteResponseMean A G f y σ₁ - siteResponseMean A G f y σ₀) +
        cc * ∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f *
        ∑ i : Fin 4, ((bondScoreMean G (Y, i) σ₁ - bondScoreMean G (Y, i) σ₀) +
          (bondScoreMean G (Y - unitStep n i, i) σ₁ - bondScoreMean G (Y - unitStep n i, i) σ₀)) := by
    have s1 : ∑ y ∈ As, (siteResponseMean A G f y σ₁ - siteResponseMean A G f y σ₀) =
        ∑ y ∈ As, siteResponseMean A G f y σ₁ - ∑ y ∈ As, siteResponseMean A G f y σ₀ :=
      Finset.sum_sub_distrib _ _
    have s2 : ∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f *
        ∑ i : Fin 4, ((bondScoreMean G (Y, i) σ₁ - bondScoreMean G (Y, i) σ₀) +
          (bondScoreMean G (Y - unitStep n i, i) σ₁ - bondScoreMean G (Y - unitStep n i, i) σ₀)) =
        ∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f *
          ∑ i : Fin 4, (bondScoreMean G (Y, i) σ₁ + bondScoreMean G (Y - unitStep n i, i) σ₁) -
        ∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f *
          ∑ i : Fin 4, (bondScoreMean G (Y, i) σ₀ + bondScoreMean G (Y - unitStep n i, i) σ₀) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun Y _ => ?_
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [s1, s2]
    ring
  rw [e1]
  have t1 : |∑ y ∈ As, (siteResponseMean A G f y σ₁ - siteResponseMean A G f y σ₀)| ≤
      ∑ y ∈ As, (2 + 2 * sh y) * E :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum site)
  have t2 : |∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f *
      ∑ i : Fin 4, ((bondScoreMean G (Y, i) σ₁ - bondScoreMean G (Y, i) σ₀) +
        (bondScoreMean G (Y - unitStep n i, i) σ₁ - bondScoreMean G (Y - unitStep n i, i) σ₀))| ≤
      (Ap.card : ℝ) * (16 * E) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ Y ∈ Ap, |blockMean R.params.side (R.depth + 1) n Y f *
        ∑ i : Fin 4, ((bondScoreMean G (Y, i) σ₁ - bondScoreMean G (Y, i) σ₀) +
          (bondScoreMean G (Y - unitStep n i, i) σ₁ - bondScoreMean G (Y - unitStep n i, i) σ₀))| ≤ 16 * E := by
      intro Y hY
      rw [abs_mul]
      have a1 : |∑ i : Fin 4, ((bondScoreMean G (Y, i) σ₁ - bondScoreMean G (Y, i) σ₀) +
          (bondScoreMean G (Y - unitStep n i, i) σ₁ - bondScoreMean G (Y - unitStep n i, i) σ₀))| ≤ 16 * E := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc _ ≤ ∑ _i : Fin 4, (4 * E) := Finset.sum_le_sum fun i _ => by
              have b1 := (bond Y hY i).1
              have b2 := (bond Y hY i).2
              have b3 := abs_add_le (bondScoreMean G (Y, i) σ₁ - bondScoreMean G (Y, i) σ₀)
                (bondScoreMean G (Y - unitStep n i, i) σ₁ - bondScoreMean G (Y - unitStep n i, i) σ₀)
              linarith
          _ = 16 * E := by simp; ring
      calc _ ≤ 1 * (16 * E) := mul_le_mul (hhat Y) a1 (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    calc _ ≤ ∑ _Y ∈ Ap, 16 * E := Finset.sum_le_sum this
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have ha := h.one_le_coupling
  have hC := h.C₀_ge
  have hcc' : |cc| ≤ R.params.coupling := by
    rw [hcc, abs_mul, abs_of_nonneg (by linarith : 0 ≤ R.params.coupling / 2)]
    have h2 := h.admissible.abs_coeff_le
    nlinarith [abs_nonneg A.coeff]
  set Ss := ∑ y ∈ As, sh y with hSs
  have hSs0 : 0 ≤ Ss := Finset.sum_nonneg fun y _ => by
    have a := h.recordedSiteScore_nonneg y
    have b : 0 ≤ spinLabelSum A G y σ₀ := Finset.sum_nonneg fun i _ =>
      spinLabelScore_nonneg h.admissible.price.nonneg i y _
    exact add_nonneg a b
  have hN : spinScore A G As σ₀ = 1 + (As.card : ℝ)⁻¹ * Ss := rfl
  have hNc : (As.card : ℝ) * spinScore A G As σ₀ = As.card + Ss := by
    rw [hN]
    field_simp
  have hsum : ∑ y ∈ As, (2 + 2 * sh y) * E = 2 * (As.card + Ss) * E := by
    rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring
  have hAc : (Ap.card : ℝ) ≤ As.card := by exact_mod_cast hcard
  have t3 : |cc * ∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f *
      ∑ i : Fin 4, ((bondScoreMean G (Y, i) σ₁ - bondScoreMean G (Y, i) σ₀) +
        (bondScoreMean G (Y - unitStep n i, i) σ₁ - bondScoreMean G (Y - unitStep n i, i) σ₀))| ≤
      R.params.coupling * ((As.card : ℝ) * (16 * E)) := by
    rw [abs_mul]
    have u1 : (Ap.card : ℝ) * (16 * E) ≤ (As.card : ℝ) * (16 * E) :=
      mul_le_mul_of_nonneg_right hAc (by positivity)
    exact mul_le_mul hcc' (t2.trans u1) (abs_nonneg _) (by linarith)
  have key : 2 * (As.card + Ss) * E + R.params.coupling * ((As.card : ℝ) * (16 * E)) ≤
      4 * lowerSizeConst A f * spinScore A G As σ₀ * E := by
    have e2 : 4 * lowerSizeConst A f * spinScore A G As σ₀ * E =
        4 * A.responseParams.C₀ * ((As.card : ℝ) * spinScore A G As σ₀) * E := by
      simp only [lowerSizeConst]
      ring
    rw [e2, hNc]
    apply le_of_sub_nonneg
    have e3 : 4 * A.responseParams.C₀ * ((As.card : ℝ) + Ss) * E -
        (2 * (As.card + Ss) * E + R.params.coupling * ((As.card : ℝ) * (16 * E))) =
        ((4 * A.responseParams.C₀ - 2 - 16 * R.params.coupling) * (As.card : ℝ) +
          (4 * A.responseParams.C₀ - 2) * Ss) * E := by ring
    rw [e3]
    have p1 : 0 ≤ 4 * A.responseParams.C₀ - 2 - 16 * R.params.coupling := by linarith
    have p2 : 0 ≤ 4 * A.responseParams.C₀ - 2 := by linarith
    have : 0 ≤ (4 * A.responseParams.C₀ - 2 - 16 * R.params.coupling) * (As.card : ℝ) +
        (4 * A.responseParams.C₀ - 2) * Ss := by positivity
    exact mul_nonneg this hE0
  calc _ ≤ |∑ y ∈ As, (siteResponseMean A G f y σ₁ - siteResponseMean A G f y σ₀)| +
        |cc * ∑ Y ∈ Ap, blockMean R.params.side (R.depth + 1) n Y f *
        ∑ i : Fin 4, ((bondScoreMean G (Y, i) σ₁ - bondScoreMean G (Y, i) σ₀) +
          (bondScoreMean G (Y - unitStep n i, i) σ₁ - bondScoreMean G (Y - unitStep n i, i) σ₀))| :=
        abs_add_le _ _
    _ ≤ ∑ y ∈ As, (2 + 2 * sh y) * E + R.params.coupling * ((As.card : ℝ) * (16 * E)) := add_le_add t1 t3
    _ ≤ _ := by rw [hsum]; exact key
set_option maxHeartbeats 4000000 in
theorem gasSupportMeanFarSpinBound_holds (htwo : ChartResponseComparison) (hsc : BondScoreProperties)
    (hcfg : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hmass : SettingMassEqIntegral)
    (hpot : PotentialFactorization) (hagree : LocalSettingsAgree)
    (hborel : settingMeanMeasurableStatement) (hsv : supportResponseBoundStatement)
    (hwn : WeightsCloseToBlockMeans) :
    GasSupportMeanFarSpinBound := by
  classical
  obtain ⟨r₃, p₃, H₃⟩ := htwo
  obtain ⟨r₄, p₄, H₄⟩ := hmass
  obtain ⟨r₅, p₅, H₅⟩ := hborel
  obtain ⟨r₆, p₆, H₆⟩ := hsv
  refine ⟨fun c => min (r₃ c) (min (r₄ c) (min (r₅ c) (r₆ c))),
    fun c => lt_min (p₃ c) (lt_min (p₄ c) (lt_min (p₅ c) (p₆ c))), fun T hT' hrt K => ?_⟩
  have t₃ := hrt.trans (min_le_left _ _)
  have t₄ := (hrt.trans (min_le_right _ _)).trans (min_le_left _ _)
  have t₅ := ((hrt.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have t₆ := ((hrt.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨y₃, H₃⟩ := H₃ T hT' t₃ K
  obtain ⟨y₄, H₄⟩ := H₄ T hT' t₄
  obtain ⟨y₅, H₅⟩ := H₅ T hT' t₅ K
  obtain ⟨y₆, H₆⟩ := H₆ T hT' t₆ K
  obtain ⟨y₇, -⟩ : ∃ y₇ : ℝ, y₇ = 0 := ⟨0, rfl⟩
  obtain ⟨y₈, H₈⟩ := hcfg T hT'
  refine ⟨max T.floorMin (max y₃ (max y₄ (max y₅ (max y₆ (max y₇ (max y₈ (200 * T.B))))))),
    fun y hy R A hK hAT n _ G hG f hsz hne => ?_⟩
  have fl : ∀ {a : ℝ}, a ≤ max y₃ (max y₄ (max y₅ (max y₆ (max y₇ (max y₈ (200 * T.B)))))) → a ≤ y :=
    fun h => h.trans ((le_max_right _ _).trans hy)
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hy3 : y₃ ≤ y := fl (le_max_left _ _)
  have hy4 : y₄ ≤ y := fl ((le_max_left _ _).trans (le_max_right _ _))
  have hy5 : y₅ ≤ y := fl ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hy6 : y₆ ≤ y :=
    fl ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hy7 : y₇ ≤ y := fl ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))))
  have hy8 : y₈ ≤ y := fl ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))))
  have hy9 : 200 * T.B ≤ y := fl ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))))
  have hOT := hAT.onFamily
  obtain ⟨hR, hρA, hpc, hyx, hstep⟩ := id hOT
  have hL : R.params.side = T.side := by rw [hR]; rfl
  have hRa : R.params.coupling = T.coupling := by rw [hR]; rfl
  have hRσ : R.params.threshold = T.threshold := by rw [hR]; rfl
  have hfit : R.params.Admissible := by rw [hR]; exact hT'.fits y hy0
  have hodd : Odd R.params.side := by rw [hL]; exact hT'.L_odd
  have hx' : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAT.abs_sub_le).2
    linarith only [h1, hy9, hyx]
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
    H₈ y hy8 R hOT hx' n G hG σ hσ
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
  have st : FarSpinSetup A G := {
    admissible := hAT.admissible
    params_admissible := hfit
    side_odd := hodd
    hasExpansions := hstep.1.2
    isBlockSide := hside
    n₀_le := hn
    functional_trivial_pos := hflat
    setting_admissible := hadm
    density_integrable := fun σ hσ => by
      obtain ⟨a1, a2, -⟩ := H₄ y hy4 R hOT n (by rw [← hRn₀]; exact hn) (configSetting G σ) (hadm σ hσ)
      exact ⟨a1, a2⟩
    settings_agree := hagree
    measurable_mean := fun F hF => H₅ y hy5 R A hK hAT n G hG F hF
    one_le_coupling := ha1
    C₀_ge := hc0'
    abs_bondScore_le := fun W V b c => (hsc R.params hfit R.coupling n b c).2.2.1 W V
    measurable_bondScore := fun b c => (hsc R.params hfit R.coupling n b c).2.2.2.2
    two_settings := fun s s' Y m hs hs' hag hm => by
      obtain ⟨b1, b2⟩ := ((H₃ y hy3 R A hK hAT).2 n n s s' Y Y m hn hn hs hs').1 hag hm
      exact ⟨fun o ho h => b1 o ho h h fun _ _ _ _ _ => rfl, b2⟩ }
  have hL1 : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hsz' : weightNorm R.params.side R.depth f ≤ 1 := (weightNorm_le_succ R.depth hL1 f).trans hsz
  have hhat : ∀ Y, |blockMean R.params.side (R.depth + 1) n Y f| ≤ 1 := fun Y =>
    ((hwn R.params.side hodd (R.depth + 1) n Y).1 f).trans ((le_max_left _ _).trans hsz)
  obtain ⟨c1, -, c3⟩ := H₆ y hy6 R A hK hAT n hn G.coarse f hsz hsz' hne
  refine ⟨st.measurable_mean _ c1, fun σ hσ => ?_, fun σ i v m hv hm hg => ?_⟩
  · obtain ⟨hdi, hdm⟩ := st.density_integrable σ hσ
    have e0 : gasSupportMean A G f σ = weightedMean (chartDensity (configSetting G σ)) fun η =>
        centeredSupportResponse A G.coarse f ((configSetting G σ).field η) (configSetting G σ).support
          (configSetting G σ).labelling (G.badBondsOf σ) (configSetting G σ).bases :=
      settingMean_liveCase (fun η hη => st.isLiveState hσ η hη) _ _
    rw [e0]
    refine abs_weightedMean_le hdi hdm fun η hη => ?_
    have b1 := c3 _ _ _ (G.badBondsOf σ) (configSetting G σ).bases (st.isLiveState hσ η hη)
    refine b1.trans ?_
    have hs0 : 0 ≤ 4 * lowerSizeConst A f := by
      have h1 : 0 ≤ A.responseParams.C₀ := by linarith only [hc0', ha1]
      unfold lowerSizeConst
      positivity
    apply mul_le_mul_of_nonneg_left _ hs0
    show 1 + _ ≤ 1 + _
    have hinv : (0 : ℝ) ≤ ((lowerSites f).card : ℝ)⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun y' (_ : y' ∈ lowerSites f) => st.configSiteScore_le y' σ) hinv
    exact add_le_add le_rfl this
  · have h₀ : G.pairConstraint.IsAdmissible (Function.update σ i (G.pairConstraint.vacant i)) := by
      have := isAdmissible_update_vacant hv i
      simpa using this
    exact abs_gasSupportMean_sub_le st hsz' hhat hne hv h₀ (fun k hk => by
      rw [Function.update_of_ne hk, Function.update_of_ne hk]) hm hg
end Main
end FarSpin
theorem gasSupportMeanFarSpinBound_of (htwo : ChartResponseComparison) (hsc : BondScoreProperties)
    (hcfg : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hmass : SettingMassEqIntegral)
    (hpot : PotentialFactorization) (hagree : LocalSettingsAgree)
    (hborel : settingMeanMeasurableStatement) (hsv : supportResponseBoundStatement)
    (hwn : WeightsCloseToBlockMeans) :
    GasSupportMeanFarSpinBound := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.gasSupportMeanFarSpinBound_holds <;> assumption
end ResponseInTheExpansion
end YangMills.Construction
end
