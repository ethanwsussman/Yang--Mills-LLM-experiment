import YangMills.Construction.ResponseInTheExpansion.ClassPartUnderAFarTilt
import YangMills.Construction.ResponseInTheExpansion.FarMeanUnderATilt
import YangMills.Construction.ResponseInTheExpansion.FarVariableUnderATiltProof
import YangMills.Construction.ResponseInTheExpansion.LocalFunctionUnderAFarTilt
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction
open WeightedResponses StepSettings StepGas TorusFields TorusLumps RenormalizationStepParameters CoreColumns BlockOffsets FreeEnergies
  Dobrushin BlockAverages StepCosts
namespace ResponseInTheExpansion
namespace SeparatedMeanUnderTilt
set_option linter.unusedSectionVars false
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
section SpinLabels
private theorem spinLabelScore_vacant (s : R.labels.Ω → ℝ) (i : G.GasSpin) (y : TorusSite (n * R.params.side)) :
    spinLabelScore s G i y (G.pairConstraint.vacant i) = 0 := rfl
private theorem spinLabelScore_of_not_mem {s : R.labels.Ω → ℝ} {i : G.GasSpin} {y : TorusSite (n * R.params.side)}
    (hy : y ∉ i.1.2) (v : G.SpinValue i) :
    spinLabelScore s G i y v = 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.spinLabelScore_eq_zero_of_not_mem <;> assumption
end SpinLabels
section TiltedMass
variable {T : ParameterAssignment} {A : ResponseSetup R} {s : R.labels.Ω → ℝ} {Q : Finset (TorusSite n)}
  {B : Finset (TorusSite (n * R.params.side))} {e : ℝ} {Yt : G.Config → ℝ}
private theorem isAdmissible_update_vacant {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ) (i : G.GasSpin) :
    G.pairConstraint.IsAdmissible (Function.update σ i (G.pairConstraint.vacant i)) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.isAdmissible_update_vacant <;> assumption
private theorem isActivityBounded_tilted (hs : ∀ w, 0 ≤ A.score w) {c : ℝ}
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    (ht : IsGasTilt G A.score Q B e Yt) :
    G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) (fun σ => G.weight σ * Yt σ)
      fun i => 3 * G.spinActivity c i := by apply _root_.YangMills.Construction.TiltedGasResponse.isActivityBounded_tilt <;> assumption
private theorem isGasTilt_one (he : 0 ≤ e) : IsGasTilt G s Q ∅ e (fun _ => 1) where
  measurable := measurable_const
  pos _ _ := one_pos
  update_le _ _ _ _ := by simp
  abs_update_sub_le _ _ _ _ _ _ _ := by
    simp only [sub_self, abs_zero, mul_one]
    exact mul_nonneg he (Real.exp_pos _).le
end TiltedMass
section WeightedMeans
variable {free : Finset (TorusBond (n * R.params.side))}
private theorem chartDensity_eq_zero {s : ChartSetting R n} {η : FreeCoords s.free} (h : ¬ s.InBalls η) :
    chartDensity s η = 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.chartDensity_eq_zero <;> assumption
private theorem settingMean_liveCase {s : ChartSetting R n}
    (hl : ∀ η, s.InBalls η → IsLiveState R.params R.coupling R.labelWeight (s.field η) s.support s.labelling)
    (bad : Finset (TorusBond (n * R.params.side))) (F : CaseFunction R n) :
    settingMean s bad (liveCaseFunction F) =
      weightedMean (chartDensity s) fun η => F (s.field η) s.support s.labelling bad s.bases := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.settingMean_liveCase <;> assumption
private theorem integrable_mul_chartDensity {s : ChartSetting R n} (hd : Integrable (chartDensity s))
    {g : FreeCoords s.free → ℝ} (hg : Measurable g) {Q : ℝ} (hQ : ∀ η, s.InBalls η → |g η| ≤ Q) :
    Integrable fun η => g η * chartDensity s η := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.integrable_mul_chartDensity <;> assumption
private theorem abs_weightedMean_le {s : ChartSetting R n} (hd : Integrable (chartDensity s))
    (hm : 0 < ∫ η, chartDensity s η)
    {g : FreeCoords s.free → ℝ} {Q : ℝ} (hQ : ∀ η, s.InBalls η → |g η| ≤ Q) :
    |weightedMean (chartDensity s) g| ≤ Q := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.abs_weightedMean_le <;> assumption
end WeightedMeans
section SiteMeans
private def siteResponseMean (A : ResponseSetup R) (G : GasGround R n)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (y : TorusSite (n * R.params.side))
    (σ : G.Config) : ℝ :=
  settingMean (configSetting G σ) (G.badBondsOf σ)
    (liveCaseFunction fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f)
private def bondScoreMean (G : GasGround R n) (c : TorusBond n) (σ : G.Config) : ℝ :=
  settingMean (configSetting G σ) (G.badBondsOf σ)
    (liveCaseFunction fun W _ _ _ b => bondScore R.params R.coupling W G.coarse b c)
private def configSiteScore (A : ResponseSetup R) (G : GasGround R n) (y : TorusSite (n * R.params.side))
    (σ : G.Config) : ℝ :=
  siteScore A.score (configSetting G σ).support (configSetting G σ).labelling y
private structure Standing (A : ResponseSetup R) (G : GasGround R n) : Prop where
  resp : A.IsAdmissible
  fit : R.params.Admissible
  odd : Odd R.params.side
  row : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
    R.siteDensity
  side : IsBlockTorusSide R.params (n * R.params.side)
  n0 : R.params.n₀ ≤ n
  flatD : 0 < R.functional (n * R.params.side) (trivialField (n * R.params.side))
  adm : ∀ σ, G.pairConstraint.IsAdmissible σ → (configSetting G σ).IsAdmissible
  dens : ∀ σ, G.pairConstraint.IsAdmissible σ → Integrable (chartDensity (configSetting G σ)) ∧
    0 < ∫ η, chartDensity (configSetting G σ) η
  agree : LocalSettingsAgree
  borel : ∀ F : CaseFunction R n, (∀ (Yt : Finset (TorusSite (n * R.params.side)))
    (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n), Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      F p.1 Yt p.2 bad b) →
    open Classical in Measurable fun σ : G.Config =>
      if G.pairConstraint.IsAdmissible σ then settingMean (configSetting G σ) (G.badBondsOf σ) F else 0
  a_ge : 1 ≤ R.params.coupling
  c0 : 12 + 40 * R.params.coupling ≤ A.responseParams.C₀
  score_le : ∀ (W : TorusField (n * R.params.side)) (V : TorusField n) (b : BaseChoice R.params.side n)
    (c : TorusBond n), |bondScore R.params R.coupling W V b c| ≤ 2
  score_borel : ∀ (b : BaseChoice R.params.side n) (c : TorusBond n),
    Measurable fun p : TorusField (n * R.params.side) × TorusField n => bondScore R.params R.coupling p.1 p.2 b c
  two : ∀ (s s' : ChartSetting R n) (Y : TorusSite n) (m : ℕ), s.IsAdmissible → s'.IsAdmissible →
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
private theorem Standing.isLiveState (h : Standing A G) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    (η : FreeCoords (configSetting G σ).free) (hη : (configSetting G σ).InBalls η) :
    IsLiveState R.params R.coupling R.labelWeight ((configSetting G σ).field η) (configSetting G σ).support
      (configSetting G σ).labelling := by
  have hs := h.adm σ hσ
  have hh : IsHullState R.params (clusterRange R.coupling) ((configSetting G σ).field η)
      (configSetting G σ).support := hs.isHull η hη
  refine ⟨hh, ?_⟩
  rw [h.row.form (n * R.params.side) h.side _ _ _ hh]
  have hΦ : 0 < ∏ X ∈ chainComponents (clusterRange R.coupling) (configSetting G σ).support,
      R.clusterFactor (n * R.params.side) ((configSetting G σ).field η) (configSetting G σ).support
        (configSetting G σ).labelling X := by
    refine Finset.prod_pos fun X hX => ?_
    exact lt_of_le_of_ne (h.row.factor_nonneg (n * R.params.side) h.side _ _ _ X)
      (Ne.symm (hs.factor_ne_zero η hη X hX))
  have := h.flatD
  positivity
private theorem Standing.configSiteScore_nonneg (h : Standing A G) (y : TorusSite (n * R.params.side))
    (σ : G.Config) : 0 ≤ configSiteScore A G y σ :=
  siteScore_nonneg h.resp.price.nonneg _ _ _
private theorem Standing.siteResponseMean_eq (h : Standing A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (y : TorusSite (n * R.params.side)) :
    siteResponseMean A G f y σ = chartResponse A (configSetting G σ) y f :=
  settingMean_liveCase (fun η hη => h.isLiveState hσ η hη) _ _
private theorem Standing.bondScoreMean_eq (h : Standing A G) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    (c : TorusBond n) :
    bondScoreMean G c σ = chartBondScore (configSetting G σ) c :=
  settingMean_liveCase (fun η hη => h.isLiveState hσ η hη) _ _
private theorem Standing.abs_centeredHullResponse_le (h : Standing A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (y : TorusSite (n * R.params.side))
    (η : FreeCoords (configSetting G σ).free) (hη : (configSetting G σ).InBalls η) :
    |centeredHullResponse A.cold A.hull (n * R.params.side) y ((configSetting G σ).field η)
        (configSetting G σ).support (configSetting G σ).labelling f| ≤
      A.responseParams.C₀ + configSiteScore A G y σ := by
  have h1 := h.resp.bounds.size_hull (n * R.params.side) h.side y _ _ _ (h.isLiveState hσ η hη) f
  have hC : 0 ≤ A.responseParams.C₀ := by
    have h3 := h.a_ge
    have h4 := h.c0
    linarith
  have h2 : 0 ≤ A.responseParams.C₀ + configSiteScore A G y σ := add_nonneg hC (h.configSiteScore_nonneg y σ)
  calc _ ≤ _ := h1
    _ ≤ (A.responseParams.C₀ + configSiteScore A G y σ) * 1 := mul_le_mul_of_nonneg_left hsz h2
    _ = _ := mul_one _
private theorem setGap_le {X X' : Finset (TorusSite n)} {y y' : TorusSite n} (hy : y ∈ X) (hy' : y' ∈ X') :
    setGap X X' ≤ supDist y y' :=
  Nat.sInf_le ⟨y, hy, y', hy', rfl⟩
private theorem gasSupport_core_nonempty (j : G.GasSpin) : j.1.core.Nonempty := by apply _root_.YangMills.Construction.StepGas.core_nonempty_of_gasSpin <;> assumption
private theorem Standing.settingsAgree_update_vacant (h : Standing A G) (σ : G.Config) (j : G.GasSpin)
    {Y : TorusSite n} {m : ℕ}
    (hg : m + 2 ≤ setGap {Y} j.1.core) :
    SettingsAgreeNear (configSetting G σ) (configSetting G (Function.update σ j (G.pairConstraint.vacant j)))
      Y Y m := by
  classical
  obtain ⟨a, ha⟩ := gasSupport_core_nonempty j
  have h1 : setGap {Y} j.1.core ≤ supDist Y a := setGap_le (Finset.mem_singleton_self Y) ha
  have h2 := SettingShifts.two_mul_supDist_le Y a
  refine h.agree R n G σ _ Y m h.odd (by omega) fun i hi => ?_
  obtain ⟨e, he, hc⟩ := hi
  by_cases hij : i = j
  · subst hij
    exfalso
    have h3 : setGap {Y} i.1.core ≤ supDist Y (Y + siteOfInt e) :=
      setGap_le (Finset.mem_singleton_self Y) hc
    have h4 : supDist Y (Y + siteOfInt e) ≤ m := supDist_add_siteOfInt_le Y e m fun l => by
      have h1 : |e l| ≤ (m : ℤ) := he l
      rw [Int.abs_eq_natAbs] at h1
      omega
    omega
  · rw [Function.update_of_ne hij]
private theorem Standing.measurableSet_live (h : Standing A G) (Yt : Finset (TorusSite (n * R.params.side))) :
    MeasurableSet {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) |
      IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} := by
  classical
  have hb := (h.row.borel (n * R.params.side) h.side Yt).1
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
private theorem Standing.measurable_hullCase (h : Standing A G)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (y : TorusSite (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      liveCaseFunction (R := R) (n := n)
        (fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f) p.1 Yt p.2 bad b := by
  classical
  have h1 := h.resp.bounds.hull_borel (n * R.params.side) h.side y Yt f
  have h2 := h.measurableSet_live Yt
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
private theorem Standing.measurable_bondScoreCase (h : Standing A G) (c : TorusBond n)
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
    have h3 := (h.score_borel b c).comp h2
    exact h3
  exact Measurable.ite (h.measurableSet_live Yt) h1 measurable_const
private theorem Standing.measurable_siteResponseMean (h : Standing A G)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (y : TorusSite (n * R.params.side)) :
    open Classical in Measurable fun σ =>
      if G.pairConstraint.IsAdmissible σ then siteResponseMean A G f y σ else 0 :=
  h.borel _ fun Yt bad b => h.measurable_hullCase f y Yt bad b
private theorem Standing.measurable_bondScoreMean (h : Standing A G) (c : TorusBond n) :
    open Classical in Measurable fun σ => if G.pairConstraint.IsAdmissible σ then bondScoreMean G c σ else 0 :=
  h.borel _ fun Yt bad b => h.measurable_bondScoreCase c Yt bad b
private theorem Standing.integrable_hull_mul_density (h : Standing A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (y : TorusSite (n * R.params.side)) :
    Integrable fun η => centeredHullResponse A.cold A.hull (n * R.params.side) y ((configSetting G σ).field η)
      (configSetting G σ).support (configSetting G σ).labelling f * chartDensity (configSetting G σ) η := by
  classical
  set s := configSetting G σ with hs
  set g : FreeCoords s.free → ℝ := fun η => liveCaseFunction (R := R) (n := n)
    (fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f) (s.field η) s.support
      s.labelling (G.badBondsOf σ) s.bases with hg
  have hm : Measurable g := by
    have h1 := h.measurable_hullCase f y s.support (G.badBondsOf σ) s.bases
    have h2 : Measurable fun η : FreeCoords s.free => (s.field η, s.labelling) :=
      (ClusterExpansionOfAStep.ChartSetting.measurable_field s).prodMk measurable_const
    have h3 := h1.comp h2
    exact h3
  have hgeq : ∀ η, s.InBalls η →
      g η = centeredHullResponse A.cold A.hull (n * R.params.side) y (s.field η) s.support s.labelling f :=
    fun η hη => by
      simp only [hg, liveCaseFunction]
      exact if_pos (h.isLiveState hσ η hη)
  have hi := integrable_mul_chartDensity (h.dens σ hσ).1 hm (Q := A.responseParams.C₀ + configSiteScore A G y σ)
    fun η hη => by
      rw [hgeq η hη]
      exact h.abs_centeredHullResponse_le hσ hsz y η hη
  refine hi.congr (Filter.Eventually.of_forall fun η => ?_)
  by_cases hη : s.InBalls η
  · show g η * _ = _
    rw [hgeq η hη]
  · have h0 : chartDensity (configSetting G σ) η = 0 := chartDensity_eq_zero hη
    show g η * _ = _ * _
    rw [h0, mul_zero, mul_zero]
private theorem Standing.integrable_bondScore_mul_density (h : Standing A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) (c : TorusBond n) :
    Integrable fun η => bondScore R.params R.coupling ((configSetting G σ).field η) (configSetting G σ).coarse
      (configSetting G σ).bases c * chartDensity (configSetting G σ) η := by
  set s := configSetting G σ with hs
  have hm : Measurable fun η : FreeCoords s.free => bondScore R.params R.coupling (s.field η) s.coarse s.bases c := by
    have h2 : Measurable fun η : FreeCoords s.free => (s.field η, s.coarse) :=
      (ClusterExpansionOfAStep.ChartSetting.measurable_field s).prodMk measurable_const
    have h3 := (h.score_borel s.bases c).comp h2
    exact h3
  exact integrable_mul_chartDensity (h.dens σ hσ).1 hm (Q := 2) fun η _ => h.score_le _ _ _ _
private theorem weightedMean_centeredSupportResponse {s : ChartSetting R n}
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
              (fun η => bondScore R.params R.coupling (s.field η) s.coarse s.bases (Y - TorusFields.unitStep n i, i))) -
        caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.weightedMean_centeredSupportResponse <;> assumption
private theorem Standing.gasSupportMean_eq (h : Standing A G) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1) :
    gasSupportMean A G f σ = ∑ y ∈ lowerSites f, siteResponseMean A G f y σ +
      R.params.coupling / 2 * A.coeff * ∑ Y ∈ upperSites f, blockMean R.params.side (R.depth + 1) n Y f *
        ∑ i : Fin 4, (bondScoreMean G (Y, i) σ + bondScoreMean G (Y - TorusFields.unitStep n i, i) σ) -
      caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) := by
  classical
  obtain ⟨hdi, hdm⟩ := h.dens σ hσ
  have e0 : gasSupportMean A G f σ = weightedMean (chartDensity (configSetting G σ)) fun η =>
      centeredSupportResponse A (configSetting G σ).coarse f ((configSetting G σ).field η)
        (configSetting G σ).support (configSetting G σ).labelling (G.badBondsOf σ) (configSetting G σ).bases :=
    settingMean_liveCase (fun η hη => h.isLiveState hσ η hη) _ _
  have e2 : ∀ y, weightedMean (chartDensity (configSetting G σ)) (fun η => centeredHullResponse A.cold A.hull
      (n * R.params.side) y ((configSetting G σ).field η) (configSetting G σ).support
        (configSetting G σ).labelling f) = siteResponseMean A G f y σ :=
    fun y => (settingMean_liveCase (s := configSetting G σ) (fun η hη => h.isLiveState hσ η hη) (G.badBondsOf σ)
      (fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f)).symm
  have e3 : ∀ c, weightedMean (chartDensity (configSetting G σ)) (fun η => bondScore R.params R.coupling
      ((configSetting G σ).field η) (configSetting G σ).coarse (configSetting G σ).bases c) = bondScoreMean G c σ :=
    fun c => (settingMean_liveCase (s := configSetting G σ) (fun η hη => h.isLiveState hσ η hη) (G.badBondsOf σ)
      (fun W _ _ _ b => bondScore R.params R.coupling W G.coarse b c)).symm
  rw [e0, weightedMean_centeredSupportResponse (G.badBondsOf σ) hdi hdm
    (fun y => h.integrable_hull_mul_density hσ hsz y)
    (fun c => h.integrable_bondScore_mul_density hσ c)]
  rw [Finset.sum_congr rfl fun y _ => e2 y]
  congr 3
  refine Finset.sum_congr rfl fun Y _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [e3, e3]
private def siteLabelSum (A : ResponseSetup R) (G : GasGround R n) (y : TorusSite (n * R.params.side))
    (σ : G.Config) : ℝ :=
  ∑ i, spinLabelScore A.score G i y (σ i)
private theorem Standing.configSiteScore_le (h : Standing A G) (y : TorusSite (n * R.params.side)) (σ : G.Config) :
    configSiteScore A G y σ ≤ recordedSiteScore A G y + siteLabelSum A G y σ :=
  FreeEnergies.siteScore_configSetting_le h.resp.price.nonneg σ y
private theorem Standing.abs_siteResponseMean_le (h : Standing A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (y : TorusSite (n * R.params.side)) :
    |siteResponseMean A G f y σ| ≤ A.responseParams.C₀ + configSiteScore A G y σ := by
  obtain ⟨hdi, hdm⟩ := h.dens σ hσ
  have e : siteResponseMean A G f y σ = weightedMean (chartDensity (configSetting G σ))
      (fun η => centeredHullResponse A.cold A.hull (n * R.params.side) y
        ((configSetting G σ).field η) (configSetting G σ).support (configSetting G σ).labelling f) :=
    settingMean_liveCase (s := configSetting G σ) (fun η hη => h.isLiveState hσ η hη) (G.badBondsOf σ)
      (fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f)
  rw [e]
  exact abs_weightedMean_le hdi hdm fun η hη => h.abs_centeredHullResponse_le hσ hsz y η hη
private theorem Standing.abs_bondScoreMean_le (h : Standing A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) (c : TorusBond n) :
    |bondScoreMean G c σ| ≤ 2 := by
  obtain ⟨hdi, hdm⟩ := h.dens σ hσ
  have e : bondScoreMean G c σ = weightedMean (chartDensity (configSetting G σ))
      (fun η => bondScore R.params R.coupling ((configSetting G σ).field η)
        G.coarse (configSetting G σ).bases c) :=
    settingMean_liveCase (s := configSetting G σ) (fun η hη => h.isLiveState hσ η hη) (G.badBondsOf σ)
      (fun W _ _ _ b => bondScore R.params R.coupling W G.coarse b c)
  rw [e]
  exact abs_weightedMean_le hdi hdm fun η _ => h.score_le _ _ _ _
private theorem update_vacant_eq {σ σ' : G.Config} {j : G.GasSpin} (hd : ∀ k, k ≠ j → σ k = σ' k) :
    Function.update σ j (G.pairConstraint.vacant j) = Function.update σ' j (G.pairConstraint.vacant j) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.update_vacant_eq <;> assumption
private theorem Standing.siteResponseMean_far (h : Standing A G) {σ σ' : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) (hσ' : G.pairConstraint.IsAdmissible σ')
    {j : G.GasSpin} (hd : ∀ k, k ≠ j → σ k = σ' k) {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)}
    (hsz : weightNorm R.params.side R.depth f ≤ 1) {y : TorusSite (n * R.params.side)} {m : ℕ}
    (hm : (R.range : ℝ) / (4 * R.params.side) ≤ m) (hg : m + 2 ≤ setGap {parentBlock R.params.side y} j.1.core) :
    |siteResponseMean A G f y σ - siteResponseMean A G f y σ'| ≤
      (2 + configSiteScore A G y σ + configSiteScore A G y σ') * Real.exp (-(R.params.rt * m / 2 ^ 5)) := by
  obtain ⟨o, ho, hyo⟩ := exists_fineSite_of_parentBlock h.odd (parentBlock R.params.side y) y rfl
  set σ₀ := Function.update σ j (G.pairConstraint.vacant j) with hσ₀
  have h0 : G.pairConstraint.IsAdmissible σ₀ := isAdmissible_update_vacant hσ j
  have a1 := h.settingsAgree_update_vacant (A := A) σ j hg
  have a2 := h.settingsAgree_update_vacant (A := A) σ' j hg
  rw [← update_vacant_eq hd] at a2
  have b1 := (h.two _ _ _ m (h.adm σ hσ) (h.adm _ h0) a1 hm).1 o ho f
  have b2 := (h.two _ _ _ m (h.adm σ' hσ') (h.adm _ h0) a2 hm).1 o ho f
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
private theorem Standing.bondScoreMean_far (h : Standing A G) {σ σ' : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) (hσ' : G.pairConstraint.IsAdmissible σ')
    {j : G.GasSpin} (hd : ∀ k, k ≠ j → σ k = σ' k) {Y : TorusSite n} {m : ℕ}
    (hm : (R.range : ℝ) / (4 * R.params.side) ≤ m) (hg : m + 2 ≤ setGap {Y} j.1.core) {c : (Fin 4 → ℤ) × Fin 4}
    (hc : IsBondAtOrigin c) :
    |bondScoreMean G (bondFrom Y c) σ - bondScoreMean G (bondFrom Y c) σ'| ≤
      2 * Real.exp (-(R.params.rt * m / 2 ^ 5)) := by
  set σ₀ := Function.update σ j (G.pairConstraint.vacant j) with hσ₀
  have h0 : G.pairConstraint.IsAdmissible σ₀ := isAdmissible_update_vacant hσ j
  have a1 := h.settingsAgree_update_vacant (A := A) σ j hg
  have a2 := h.settingsAgree_update_vacant (A := A) σ' j hg
  rw [← update_vacant_eq hd] at a2
  have b1 := (h.two _ _ _ m (h.adm σ hσ) (h.adm _ h0) a1 hm).2 c hc
  have b2 := (h.two _ _ _ m (h.adm σ' hσ') (h.adm _ h0) a2 hm).2 c hc
  rw [h.bondScoreMean_eq hσ, h.bondScoreMean_eq hσ']
  calc _ ≤ |chartBondScore (configSetting G σ) (bondFrom Y c) - chartBondScore (configSetting G σ₀) (bondFrom Y c)| +
        |chartBondScore (configSetting G σ') (bondFrom Y c) - chartBondScore (configSetting G σ₀) (bondFrom Y c)| := by
        rw [abs_sub_comm (chartBondScore (configSetting G σ') (bondFrom Y c))]
        exact abs_sub_le _ _ _
    _ ≤ _ := by linarith
end SiteMeans
private theorem tiltedGibbsLaw_one : tiltedGibbsLaw G (fun _ => (1 : ℝ)) = G.gibbsLaw ∅ := by apply _root_.YangMills.Construction.TiltedGasResponse.tiltedGibbsLaw_one <;> assumption
section OscillationParts
variable {A : ResponseSetup R} {Q : Finset (TorusSite n)} {B : Finset (TorusSite (n * R.params.side))} {e : ℝ}
  {Yt : G.Config → ℝ}
private def columnRate (R : StepSetup) : ℝ := R.params.rt / 2 ^ 6
private def nearFactor (R : StepSetup) : ℝ :=
  Real.exp (columnRate R * ((R.range : ℝ) / (4 * R.params.side) + 4))
private theorem coreWeightFrom_pos (Y : TorusSite n) (j : G.GasSpin) : 0 < G.coreWeightFrom Y j := by apply _root_.YangMills.Construction.GasComparison.coreWeightFrom_pos <;> assumption
private theorem oscillationBound_of_far (hrt : 0 < R.params.rt) {Y : TorusSite n} {H : G.Config → ℝ} {Mb Mf : ℝ}
    (hMb : 0 ≤ Mb) (hMf : 0 ≤ Mf)
    (hb : ∀ σ, |H σ| ≤ Mb)
    (hfar : ∀ (j : G.GasSpin) (σ σ' : G.Config), G.pairConstraint.IsAdmissible σ →
      G.pairConstraint.IsAdmissible σ' →
      (∀ k, k ≠ j → σ k = σ' k) → ∀ m : ℕ, (R.range : ℝ) / (4 * R.params.side) ≤ m →
        m + 2 ≤ setGap {Y} j.1.core →
      |H σ - H σ'| ≤ Mf * Real.exp (-(R.params.rt * m / 2 ^ 5))) :
    G.pairConstraint.OscillationBound H fun j => (2 * Mb + Mf) * nearFactor R * G.coreWeightFrom Y j := by
  have hrp : 0 < columnRate R := by unfold columnRate; positivity
  have hBs : 0 < nearFactor R := Real.exp_pos _
  refine ⟨fun j => mul_nonneg (by positivity) (coreWeightFrom_pos Y j).le, fun j σ σ' hσ hσ' hd => ?_⟩
  set g := setGap {Y} j.1.core with hg
  set L4 : ℝ := (R.range : ℝ) / (4 * R.params.side) with hL4
  have hL40 : 0 ≤ L4 := by positivity
  have hN : (1 : ℝ) ≤ (j.1.core.card : ℝ) := by exact_mod_cast (gasSupport_core_nonempty j).card_pos
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
        nearFactor R * Real.exp (-(columnRate R * (g : ℝ))) := by
      unfold nearFactor
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have e2 : R.params.rt = 2 ^ 6 * columnRate R := by unfold columnRate; ring
      rw [e1, e2]
      have : 0 ≤ columnRate R * L4 := by positivity
      have h3 : 0 ≤ columnRate R * ((g - 2 : ℕ) : ℝ) := by positivity
      push_cast
      nlinarith
    calc _ ≤ _ := h1
      _ ≤ Mf * (nearFactor R * G.coreWeightFrom Y j) := mul_le_mul_of_nonneg_left (h2.trans
          (mul_le_mul_of_nonneg_left hseen hBs.le)) hMf
      _ ≤ _ := by
          have : 0 ≤ nearFactor R * G.coreWeightFrom Y j := mul_nonneg hBs.le (coreWeightFrom_pos Y j).le
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
    have h4 : 1 ≤ nearFactor R * Real.exp (-(columnRate R * (g : ℝ))) := by
      unfold nearFactor
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    have h5 : 1 ≤ nearFactor R * G.coreWeightFrom Y j := h4.trans (mul_le_mul_of_nonneg_left hseen hBs.le)
    calc |H σ - H σ'| ≤ |H σ| + |H σ'| := abs_sub _ _
      _ ≤ 2 * Mb := by linarith [hb σ, hb σ']
      _ ≤ (2 * Mb + Mf) * 1 := by linarith
      _ ≤ (2 * Mb + Mf) * (nearFactor R * G.coreWeightFrom Y j) := mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = _ := by ring
private theorem nearFactor_le (hrt : 0 < R.params.rt) : nearFactor R ≤ nearBlockCost R := by
  unfold nearFactor nearBlockCost columnRate
  apply Real.exp_le_exp.mpr
  have hL : (1 : ℝ) ≤ (R.params.side : ℝ) := by
    have : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
    exact_mod_cast this
  have h1 : (R.range : ℝ) / (4 * R.params.side) ≤ 10 * (R.range : ℝ) / R.params.side := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith
private theorem oscillationBound_near (hrt : 0 < R.params.rt) {Y : TorusSite n} {H : G.Config → ℝ} {Mb Mf M : ℝ}
    (hMb : 0 ≤ Mb) (hMf : 0 ≤ Mf)
    (hM : 2 * Mb + Mf ≤ 4 * M) (hb : ∀ σ, |H σ| ≤ Mb)
    (hfar : ∀ (j : G.GasSpin) (σ σ' : G.Config), G.pairConstraint.IsAdmissible σ →
      G.pairConstraint.IsAdmissible σ' →
      (∀ k, k ≠ j → σ k = σ' k) → ∀ m : ℕ, (R.range : ℝ) / (4 * R.params.side) ≤ m →
        m + 2 ≤ setGap {Y} j.1.core →
      |H σ - H σ'| ≤ Mf * Real.exp (-(R.params.rt * m / 2 ^ 5))) :
    G.pairConstraint.OscillationBound H fun j => 4 * M * nearBlockCost R * decayFromSet G {Y} j := by
  have ho := oscillationBound_of_far hrt hMb hMf hb hfar
  have hBs : 0 < nearFactor R := Real.exp_pos _
  have hnc : 0 < nearBlockCost R := Real.exp_pos _
  have hM0 : 0 ≤ 4 * M := by linarith
  refine ⟨fun j => ?_, fun j σ σ' a b d => (ho.2 j σ σ' a b d).trans ?_⟩
  · show 0 ≤ 4 * M * nearBlockCost R * G.coreWeightFrom Y j
    exact mul_nonneg (mul_nonneg hM0 hnc.le) (coreWeightFrom_pos Y j).le
  · show (2 * Mb + Mf) * nearFactor R * G.coreWeightFrom Y j ≤ 4 * M * nearBlockCost R * G.coreWeightFrom Y j
    have h1 : (2 * Mb + Mf) * nearFactor R ≤ 4 * M * nearBlockCost R :=
      mul_le_mul hM (nearFactor_le hrt) hBs.le hM0
    exact mul_le_mul_of_nonneg_right h1 (coreWeightFrom_pos Y j).le
open Classical in
private def vacantPart (A : ResponseSetup R) (G : GasGround R n)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (y : TorusSite (n * R.params.side)) (σ : G.Config) : ℝ :=
  if G.pairConstraint.IsAdmissible σ ∧ ¬ ∃ i : G.GasSpin, y ∈ i.1.2 ∧ σ i ≠ G.pairConstraint.vacant i then
    siteResponseMean A G f y σ else 0
private def admissibleBondScore (G : GasGround R n) (c : TorusBond n) (σ : G.Config) : ℝ :=
  open Classical in if G.pairConstraint.IsAdmissible σ then bondScoreMean G c σ else 0
private theorem Standing.measurable_admissibleBondScore (h : Standing A G) (c : TorusBond n) :
    Measurable (admissibleBondScore G c) := by
  classical
  exact h.measurable_bondScoreMean c
private theorem abs_admissibleBondScore_le (h : Standing A G) (c : TorusBond n) (σ : G.Config) :
    |admissibleBondScore G c σ| ≤ 2 := by
  classical
  unfold admissibleBondScore
  split_ifs with hσ
  · exact h.abs_bondScoreMean_le hσ c
  · simp
private theorem Standing.recordedSiteScore_nonneg (h : Standing A G) (y : TorusSite (n * R.params.side)) :
    0 ≤ recordedSiteScore A G y :=
  siteScore_nonneg h.resp.price.nonneg _ _ _
private theorem Standing.one_le_C₀ (h : Standing A G) : 1 ≤ A.responseParams.C₀ := by
  have h3 := h.a_ge
  have h4 := h.c0
  linarith
private theorem Standing.siteResponseMean_eq_add (h : Standing A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (y : TorusSite (n * R.params.side)) :
    siteResponseMean A G f y σ = vacantPart A G f y σ + classResponsePart A G y f σ := by
  classical
  unfold vacantPart classResponsePart
  by_cases hc : ∃ i : G.GasSpin, y ∈ i.1.2 ∧ σ i ≠ G.pairConstraint.vacant i
  · rw [if_neg (fun hh => hh.2 hc), if_pos ⟨hσ, hc⟩, zero_add]
    exact h.siteResponseMean_eq hσ f y
  · rw [if_pos ⟨hσ, hc⟩, if_neg (fun hh => hc hh.2), add_zero]
private theorem siteLabelSum_eq_zero {y : TorusSite (n * R.params.side)} {σ : G.Config}
    (hc : ¬ ∃ i : G.GasSpin, y ∈ i.1.2 ∧ σ i ≠ G.pairConstraint.vacant i) : siteLabelSum A G y σ = 0 := by
  unfold siteLabelSum
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hy : y ∈ i.1.2
  · have e : σ i = G.pairConstraint.vacant i := by
      by_contra hn
      exact hc ⟨i, hy, hn⟩
    rw [e]
    exact spinLabelScore_vacant _ _ _
  · exact spinLabelScore_of_not_mem hy _
private theorem Standing.abs_vacantPart_le (h : Standing A G)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (y : TorusSite (n * R.params.side)) (σ : G.Config) :
    |vacantPart A G f y σ| ≤ A.responseParams.C₀ + recordedSiteScore A G y := by
  classical
  have h0 := h.one_le_C₀
  have h1 := h.recordedSiteScore_nonneg y
  unfold vacantPart
  split_ifs with hc
  · have a := h.abs_siteResponseMean_le hc.1 hsz y
    have b := h.configSiteScore_le y σ
    rw [siteLabelSum_eq_zero hc.2, add_zero] at b
    linarith
  · simp only [abs_zero]
    linarith
private theorem Standing.vacantPart_far (h : Standing A G)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (y : TorusSite (n * R.params.side)) (j : G.GasSpin) (σ σ' : G.Config) (hσ : G.pairConstraint.IsAdmissible σ)
    (hσ' : G.pairConstraint.IsAdmissible σ') (hd : ∀ l, l ≠ j → σ l = σ' l) (m : ℕ)
    (hm : (R.range : ℝ) / (4 * R.params.side) ≤ m)
    (hg : m + 2 ≤ setGap {parentBlock R.params.side y} j.1.core) :
    |vacantPart A G f y σ - vacantPart A G f y σ'| ≤
      (2 * (A.responseParams.C₀ + recordedSiteScore A G y)) * Real.exp (-(R.params.rt * m / 2 ^ 5)) := by
  classical
  have hyj : y ∉ j.1.2 := by
    intro hy
    have h1 : parentBlock R.params.side y ∈ j.1.core :=
      GasSupport.parentBlock_mem_core (Finset.mem_union_right _ hy)
    have h2 := setGap_le (Finset.mem_singleton_self (parentBlock R.params.side y)) h1
    rw [supDist_self] at h2
    omega
  have hiff : (∃ i : G.GasSpin, y ∈ i.1.2 ∧ σ i ≠ G.pairConstraint.vacant i) ↔
      ∃ i : G.GasSpin, y ∈ i.1.2 ∧ σ' i ≠ G.pairConstraint.vacant i := by
    constructor
    · rintro ⟨i, hi, hv⟩
      have hij : i ≠ j := fun e => hyj (e ▸ hi)
      exact ⟨i, hi, by rwa [← hd i hij]⟩
    · rintro ⟨i, hi, hv⟩
      have hij : i ≠ j := fun e => hyj (e ▸ hi)
      exact ⟨i, hi, by rwa [hd i hij]⟩
  have hE : 0 ≤ Real.exp (-(R.params.rt * m / 2 ^ 5)) := (Real.exp_pos _).le
  have h0 := h.one_le_C₀
  have h1 := h.recordedSiteScore_nonneg y
  unfold vacantPart
  by_cases hc : ∃ i : G.GasSpin, y ∈ i.1.2 ∧ σ i ≠ G.pairConstraint.vacant i
  · rw [if_neg (fun hh => hh.2 hc), if_neg (fun hh => hh.2 (hiff.mp hc))]
    simp only [sub_self, abs_zero]
    exact mul_nonneg (by linarith) hE
  · have hc' : ¬ ∃ i : G.GasSpin, y ∈ i.1.2 ∧ σ' i ≠ G.pairConstraint.vacant i := fun hh => hc (hiff.mpr hh)
    rw [if_pos ⟨hσ, hc⟩, if_pos ⟨hσ', hc'⟩]
    have p := h.siteResponseMean_far hσ hσ' hd hsz hm hg
    have s1 := h.configSiteScore_le y σ
    have s2 := h.configSiteScore_le y σ'
    rw [siteLabelSum_eq_zero hc, add_zero] at s1
    rw [siteLabelSum_eq_zero hc', add_zero] at s2
    refine p.trans (mul_le_mul_of_nonneg_right ?_ hE)
    linarith
private theorem Standing.measurable_vacantPart (h : Standing A G)
    (hw : MeasurableSet {σ : G.Config | G.pairConstraint.IsAdmissible σ})
    (ha : ∀ i, MeasurableSet {G.pairConstraint.vacant i})
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (y : TorusSite (n * R.params.side)) : Measurable (vacantPart A G f y) := by
  classical
  have hS : MeasurableSet {σ : G.Config | ∃ i : G.GasSpin, y ∈ i.1.2 ∧ σ i ≠ G.pairConstraint.vacant i} := by
    have e : {σ : G.Config | ∃ i : G.GasSpin, y ∈ i.1.2 ∧ σ i ≠ G.pairConstraint.vacant i} =
        ⋃ i : G.GasSpin, {σ : G.Config | y ∈ i.1.2 ∧ σ i ≠ G.pairConstraint.vacant i} := by
      ext σ
      simp
    rw [e]
    refine MeasurableSet.iUnion fun i => ?_
    by_cases hy : y ∈ i.1.2
    · have e2 : {σ : G.Config | y ∈ i.1.2 ∧ σ i ≠ G.pairConstraint.vacant i} =
          (fun σ : G.Config => σ i) ⁻¹' {G.pairConstraint.vacant i}ᶜ := by
        ext σ
        simp [hy]
      rw [e2]
      exact (measurable_pi_apply i) (ha i).compl
    · have e2 : {σ : G.Config | y ∈ i.1.2 ∧ σ i ≠ G.pairConstraint.vacant i} = ∅ := by
        ext σ
        simp [hy]
      rw [e2]
      exact MeasurableSet.empty
  have e : vacantPart A G f y = fun σ =>
      if ∃ i : G.GasSpin, y ∈ i.1.2 ∧ σ i ≠ G.pairConstraint.vacant i then 0 else
      (if G.pairConstraint.IsAdmissible σ then siteResponseMean A G f y σ else 0) := by
    funext σ
    unfold vacantPart
    by_cases h1 : G.pairConstraint.IsAdmissible σ <;>
      by_cases h2 : ∃ i : G.GasSpin, y ∈ i.1.2 ∧ σ i ≠ G.pairConstraint.vacant i <;>
        simp only [h1, h2, true_and, false_and, not_true_eq_false, not_false_eq_true, and_self, and_true,
          and_false, if_true, if_false]
  rw [e]
  exact Measurable.ite hS measurable_const (h.measurable_siteResponseMean f y)
end OscillationParts
section MeanExpansion
variable {A : ResponseSetup R}
private theorem integral_gasSupportMean_eq (h : Standing A G)
    (hset : MeasurableSet {σ : G.Config | G.pairConstraint.IsAdmissible σ})
    (ha : ∀ i, MeasurableSet {G.pairConstraint.vacant i})
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (ν : Measure G.Config)
    [IsProbabilityMeasure ν] (hadm : ∀ᵐ σ ∂ν, G.pairConstraint.IsAdmissible σ)
    (hRi : ∀ y ∈ lowerSites f, Integrable (classResponsePart A G y f) ν) :
    Integrable (gasSupportMean A G f) ν ∧ ∫ σ, gasSupportMean A G f σ ∂ν =
      ∑ y ∈ lowerSites f, (∫ σ, vacantPart A G f y σ ∂ν + ∫ σ, classResponsePart A G y f σ ∂ν) +
        R.params.coupling / 2 * A.coeff * ∑ Y ∈ upperSites f, blockMean R.params.side (R.depth + 1) n Y f *
          ∑ i : Fin 4, (∫ σ, admissibleBondScore G (Y, i) σ ∂ν +
            ∫ σ, admissibleBondScore G (Y - TorusFields.unitStep n i, i) σ ∂ν) -
        caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) := by
  classical
  have iC : ∀ y, Integrable (vacantPart A G f y) ν := fun y =>
    Integrable.of_bound (h.measurable_vacantPart hset ha f y).aestronglyMeasurable
      (A.responseParams.C₀ + recordedSiteScore A G y)
      (Filter.Eventually.of_forall fun σ => by
        rw [Real.norm_eq_abs]
        exact h.abs_vacantPart_le hsz y σ)
  have iG : ∀ c, Integrable (admissibleBondScore G c) ν := fun c =>
    Integrable.of_bound (h.measurable_admissibleBondScore c).aestronglyMeasurable 2
      (Filter.Eventually.of_forall fun σ => by
        rw [Real.norm_eq_abs]
        exact abs_admissibleBondScore_le h c σ)
  set F1 : G.Config → ℝ := fun σ => ∑ y ∈ lowerSites f, (vacantPart A G f y σ + classResponsePart A G y f σ)
    with hF1
  set F2 : G.Config → ℝ := fun σ => ∑ Y ∈ upperSites f, blockMean R.params.side (R.depth + 1) n Y f *
    ∑ i : Fin 4, (admissibleBondScore G (Y, i) σ + admissibleBondScore G (Y - TorusFields.unitStep n i, i) σ) with hF2
  have iB : ∀ Y, Integrable (fun σ => ∑ i : Fin 4,
      (admissibleBondScore G (Y, i) σ + admissibleBondScore G (Y - TorusFields.unitStep n i, i) σ)) ν :=
    fun Y => integrable_finset_sum _ fun i _ => (iG _).add (iG _)
  have i1 : Integrable F1 ν := integrable_finset_sum _ fun y hy => (iC y).add (hRi y hy)
  have i2 : Integrable F2 ν := integrable_finset_sum _ fun Y _ => (iB Y).const_mul _
  have i3 : Integrable (fun σ => F1 σ + R.params.coupling / 2 * A.coeff * F2 σ) ν := i1.add (i2.const_mul _)
  set vv := caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) with hvv
  have heq : gasSupportMean A G f =ᵐ[ν] fun σ => F1 σ + R.params.coupling / 2 * A.coeff * F2 σ - vv := by
    filter_upwards [hadm] with σ hσ
    rw [h.gasSupportMean_eq hσ hsz]
    simp only [hF1, hF2]
    rw [Finset.sum_congr rfl fun y _ => h.siteResponseMean_eq_add hσ f y]
    congr 3
    refine Finset.sum_congr rfl fun Y _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [admissibleBondScore, if_pos hσ]
  refine ⟨(i3.sub (integrable_const vv)).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_sub i3 (integrable_const vv), integral_add i1 (i2.const_mul _),
    integral_const_mul, integral_const, probReal_univ, one_smul]
  have e1 : ∫ σ, F1 σ ∂ν =
      ∑ y ∈ lowerSites f, (∫ σ, vacantPart A G f y σ ∂ν + ∫ σ, classResponsePart A G y f σ ∂ν) := by
    have ia : ∀ y ∈ lowerSites f, Integrable (fun σ => vacantPart A G f y σ + classResponsePart A G y f σ) ν :=
      fun y hy => (iC y).add (hRi y hy)
    have t := integral_finset_sum (μ := ν) (lowerSites f) ia
    refine t.trans (Finset.sum_congr rfl fun y hy => ?_)
    exact integral_add (iC y) (hRi y hy)
  have e2 : ∫ σ, F2 σ ∂ν = ∑ Y ∈ upperSites f, blockMean R.params.side (R.depth + 1) n Y f *
      ∑ i : Fin 4, (∫ σ, admissibleBondScore G (Y, i) σ ∂ν +
        ∫ σ, admissibleBondScore G (Y - TorusFields.unitStep n i, i) σ ∂ν) := by
    rw [hF2, integral_finset_sum _ fun Y _ => (iB Y).const_mul _]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [integral_const_mul]
    congr 1
    have ia : ∀ i ∈ (Finset.univ : Finset (Fin 4)), Integrable (fun σ => admissibleBondScore G (Y, i) σ +
        admissibleBondScore G (Y - TorusFields.unitStep n i, i) σ) ν := fun i _ => (iG _).add (iG _)
    have t := integral_finset_sum (μ := ν) (Finset.univ : Finset (Fin 4)) ia
    refine t.trans (Finset.sum_congr rfl fun i _ => ?_)
    exact integral_add (iG _) (iG _)
  rw [e1, e2]
private theorem abs_expansion_sub_le {κ₁ κ₂ : Type} (As : Finset κ₁) (Ap : Finset κ₂) (a b r r' t₁ : κ₁ → ℝ)
    (u v u' v' : κ₂ → Fin 4 → ℝ) (hh : κ₂ → ℝ) (cc vv t₂ : ℝ)
    (h1 : ∀ y ∈ As, |a y - b y| + |r y - r' y| ≤ t₁ y)
    (h2 : ∀ Y ∈ Ap, ∀ i, |u Y i - v Y i| ≤ t₂ ∧ |u' Y i - v' Y i| ≤ t₂) (hhat : ∀ Y ∈ Ap, |hh Y| ≤ 1)
    (ht₂ : 0 ≤ t₂) :
    |(∑ y ∈ As, (a y + r y) + cc * ∑ Y ∈ Ap, hh Y * ∑ i : Fin 4, (u Y i + u' Y i) - vv) -
        (∑ y ∈ As, (b y + r' y) + cc * ∑ Y ∈ Ap, hh Y * ∑ i : Fin 4, (v Y i + v' Y i) - vv)| ≤
      ∑ y ∈ As, t₁ y + |cc| * (Ap.card * (8 * t₂)) := by
  have e : (∑ y ∈ As, (a y + r y) + cc * ∑ Y ∈ Ap, hh Y * ∑ i : Fin 4, (u Y i + u' Y i) - vv) -
        (∑ y ∈ As, (b y + r' y) + cc * ∑ Y ∈ Ap, hh Y * ∑ i : Fin 4, (v Y i + v' Y i) - vv) =
      ∑ y ∈ As, ((a y - b y) + (r y - r' y)) +
        cc * ∑ Y ∈ Ap, hh Y * ∑ i : Fin 4, ((u Y i - v Y i) + (u' Y i - v' Y i)) := by
    have s1 : ∑ y ∈ As, ((a y - b y) + (r y - r' y)) = ∑ y ∈ As, (a y + r y) - ∑ y ∈ As, (b y + r' y) := by
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
    exact (abs_add_le _ _).trans (h1 y hy)
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
end MeanExpansion
section TiltedBound
variable {A : ResponseSetup R} {Q : Finset (TorusSite n)} {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ}
  {Yt : G.Config → ℝ}
private theorem parentBlock_mem_weightSupportSites {L t n : ℕ} [NeZero L] [NeZero n]
    (f : PlaquetteWeight (fineSide L (t + 1) n)) {y : TorusSite (n * L)}
    (hy : y ∈ weightSupportSites L t (n * L) f) : parentBlock L y ∈ weightSupportSites L (t + 1) n f := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.parentBlock_mem_weightSupportSites <;> assumption
private theorem image_parentBlock_weightSupportSites {L t n : ℕ} [NeZero L] [NeZero n]
    (f : PlaquetteWeight (fineSide L (t + 1) n)) :
    (open Classical in (weightSupportSites L t (n * L) f).image (parentBlock L)) =
      weightSupportSites L (t + 1) n f := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.image_parentBlock_weightSupportSites <;> assumption
private theorem coarseSiteScore_nonneg (h : Standing A G) (h₁ : 0 ≤ A.responseParams.s₁) (Y : TorusSite n) :
    0 ≤ coarseSiteScore A G.state Y :=
  siteScore_nonneg (fun w => by
    rcases w with u | st
    · exact h₁
    · show 0 ≤ coarseLabelScore A.responseParams.s₁ A.score (Sum.inr st)
      simp only [coarseLabelScore]
      refine add_nonneg h₁ (Finset.sum_nonneg fun o _ => ?_)
      rcases st.siteLabel o with u | a
      · simp
      · exact h.resp.price.nonneg a) _ _ _
private theorem sum_recordedSiteScore_le (h : Standing A G) (h₁ : 0 ≤ A.responseParams.s₁)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (hne : (upperSites f).Nonempty) :
    1 ≤ meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites f) G.state.1 G.state.2 ∧
    ∑ y ∈ lowerSites f, recordedSiteScore A G y ≤ ((lowerSites f).card : ℝ) *
      (meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites f) G.state.1 G.state.2 - 1) := by
  classical
  have h0 := sum_recordedSiteScore_le_parentBlocks (G := G) h.resp.price.nonneg h₁ (lowerSites f)
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
private theorem final_bound_arith {C₁ C₂ X Cz cA N Ss cc Ap : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hX : 0 ≤ X)
    (hCz : 1 ≤ Cz) (hcA : 0 ≤ cA)
    (hN : 1 ≤ N) (hSs : Ss ≤ cA * (N - 1)) (hcc : cc * Ap ≤ Cz * cA) :
    C₁ * X * (cA * Cz + Ss) + C₂ * X * cA + cc * (Ap * (8 * (C₁ * X * 2))) ≤
      (18 * C₁ + C₂) * X * (Cz * cA) * N := by
  have hCN : Cz + N - 1 ≤ 2 * (Cz * N) := by nlinarith
  have hK : 0 ≤ Cz * cA := by positivity
  have a1 : cA * Cz + Ss ≤ 2 * ((Cz * cA) * N) := by
    have : cA * (Cz + N - 1) ≤ cA * (2 * (Cz * N)) := mul_le_mul_of_nonneg_left hCN hcA
    nlinarith
  have a2 : cA ≤ (Cz * cA) * N := by
    have : 1 ≤ Cz * N := by nlinarith
    have h2 : cA * 1 ≤ cA * (Cz * N) := mul_le_mul_of_nonneg_left this hcA
    nlinarith
  have a3 : cc * Ap ≤ (Cz * cA) * N := by
    have : (Cz * cA) * 1 ≤ (Cz * cA) * N := mul_le_mul_of_nonneg_left hN hK
    linarith
  have hCX : 0 ≤ C₁ * X := by positivity
  have hDX : 0 ≤ C₂ * X := by positivity
  have b1 : C₁ * X * (cA * Cz + Ss) ≤ C₁ * X * (2 * ((Cz * cA) * N)) := mul_le_mul_of_nonneg_left a1 hCX
  have b2 : C₂ * X * cA ≤ C₂ * X * ((Cz * cA) * N) := mul_le_mul_of_nonneg_left a2 hDX
  have b3 : C₁ * X * (cc * Ap) ≤ C₁ * X * ((Cz * cA) * N) := mul_le_mul_of_nonneg_left a3 hCX
  have e1 : cc * (Ap * (8 * (C₁ * X * 2))) = 16 * (C₁ * X * (cc * Ap)) := by ring
  rw [e1]
  have e2 : (18 * C₁ + C₂) * X * (Cz * cA) * N =
      C₁ * X * (2 * ((Cz * cA) * N)) + C₂ * X * ((Cz * cA) * N) + 16 * (C₁ * X * ((Cz * cA) * N)) := by ring
  rw [e2]
  linarith
set_option maxHeartbeats 4000000 in
private theorem tilted_mean_bound (h : Standing A G) (hrt : 0 < R.params.rt) (he : 1 ≤ e)
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    (ht : IsGasTilt G A.score Q B e Yt) (hC : ActivityConditionalLawsStatement)
    {f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (hhat : ∀ Y, |blockMean R.params.side (R.depth + 1) n Y f| ≤ 1) (hne : (upperSites f).Nonempty)
    (hs₁ : 0 ≤ A.responseParams.s₁)
    {D : ℕ} (hD : ∀ Y ∈ upperSites f, ∀ Y' ∈ Q, D ≤ supDist Y Y') {C₁ C₂ X : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hX : 0 ≤ X)
    (loc : ∀ (Y : TorusSite n) (H : G.Config → ℝ) (M : ℝ), (∀ Y' ∈ Q, D ≤ supDist Y Y') → Measurable H → 0 ≤ M →
      (∀ σ, |H σ| ≤ 2 * M) →
      G.pairConstraint.OscillationBound H (fun i => 4 * M * nearBlockCost R * decayFromSet G {Y} i) →
      |∫ σ, H σ ∂(tiltedGibbsLaw G Yt) - G.expectation ∅ H| ≤ C₁ * X * M)
    (cls : ∀ y ∈ lowerSites f, Integrable (classResponsePart A G y f) (tiltedGibbsLaw G Yt) ∧
      Integrable (classResponsePart A G y f) (G.gibbsLaw ∅) ∧
      |∫ σ, classResponsePart A G y f σ ∂(tiltedGibbsLaw G Yt) - G.expectation ∅ (classResponsePart A G y f)| ≤
        C₂ * X) :
    Integrable (gasSupportMean A G f) (tiltedGibbsLaw G Yt) ∧ Integrable (gasSupportMean A G f) (G.gibbsLaw ∅) ∧
      |∫ σ, gasSupportMean A G f σ ∂(tiltedGibbsLaw G Yt) - G.expectation ∅ (gasSupportMean A G f)| ≤
        (18 * C₁ + C₂) * X * lowerSizeConst A f *
          meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites f) G.state.1 G.state.2 := by
  classical
  have hs := h.resp.price.nonneg
  have hset : MeasurableSet {σ : G.Config | G.pairConstraint.IsAdmissible σ} := hw.measurableSet_admissible
  have e0 : (0 : ℝ) ≤ e := by linarith
  have hw' := isActivityBounded_tilted hs hw paid ht
  have ht₁ : IsGasTilt G A.score Q ∅ e (fun _ => 1) := isGasTilt_one e0
  have hw₁ := isActivityBounded_tilted hs hw paid ht₁
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
  obtain ⟨Iν, Eν⟩ := integral_gasSupportMean_eq h hset hw.measurableSet_vacant hsz (tiltedGibbsLaw G Yt) adm₁
    fun y hy => (cls y hy).1
  obtain ⟨Iμ, Eμ⟩ := integral_gasSupportMean_eq h hset hw.measurableSet_vacant hsz (G.gibbsLaw ∅) adm₂
    fun y hy => (cls y hy).2.1
  refine ⟨Iν, Iμ, ?_⟩
  show |∫ σ, gasSupportMean A G f σ ∂(tiltedGibbsLaw G Yt) - ∫ σ, gasSupportMean A G f σ ∂(G.gibbsLaw ∅)| ≤ _
  rw [Eν, Eμ]
  have hguard : ∀ (Y : TorusSite n), (∀ Y' ∈ Q, D ≤ supDist Y Y') → ∀ (cb : (Fin 4 → ℤ) × Fin 4),
      IsBondAtOrigin cb →
      |∫ σ, admissibleBondScore G (bondFrom Y cb) σ ∂(tiltedGibbsLaw G Yt) -
        ∫ σ, admissibleBondScore G (bondFrom Y cb) σ ∂(G.gibbsLaw ∅)| ≤
        C₁ * X * 2 := by
    intro Y hDY cb hcb
    refine loc Y (admissibleBondScore G (bondFrom Y cb)) 2 hDY (h.measurable_admissibleBondScore _) zero_le_two
      (fun σ => (abs_admissibleBondScore_le h _ σ).trans (by norm_num)) ?_
    refine oscillationBound_near hrt (Mb := 2) (Mf := 2) zero_le_two zero_le_two (by norm_num)
      (abs_admissibleBondScore_le h _)
      fun j σ σ' a b d m hm hg => ?_
    simp only [admissibleBondScore, if_pos a, if_pos b]
    exact h.bondScoreMean_far a b d hm hg hcb
  have hstored := fun y => h.recordedSiteScore_nonneg y
  have hC1 := h.one_le_C₀
  have hM : ∀ y, 0 ≤ A.responseParams.C₀ + recordedSiteScore A G y := fun y => by linarith [hstored y]
  have diff := abs_expansion_sub_le (lowerSites f) (upperSites f)
    (fun y => ∫ σ, vacantPart A G f y σ ∂(tiltedGibbsLaw G Yt)) (fun y => ∫ σ, vacantPart A G f y σ ∂(G.gibbsLaw ∅))
    (fun y => ∫ σ, classResponsePart A G y f σ ∂(tiltedGibbsLaw G Yt))
    (fun y => ∫ σ, classResponsePart A G y f σ ∂(G.gibbsLaw ∅))
    (fun y => C₁ * X * (A.responseParams.C₀ + recordedSiteScore A G y) + C₂ * X)
    (fun Y i => ∫ σ, admissibleBondScore G (Y, i) σ ∂(tiltedGibbsLaw G Yt))
    (fun Y i => ∫ σ, admissibleBondScore G (Y, i) σ ∂(G.gibbsLaw ∅))
    (fun Y i => ∫ σ, admissibleBondScore G (Y - TorusFields.unitStep n i, i) σ ∂(tiltedGibbsLaw G Yt))
    (fun Y i => ∫ σ, admissibleBondScore G (Y - TorusFields.unitStep n i, i) σ ∂(G.gibbsLaw ∅))
    (fun Y => blockMean R.params.side (R.depth + 1) n Y f) (R.params.coupling / 2 * A.coeff)
    (caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f)) (C₁ * X * 2)
    (fun y hy => by
      have hb := parentBlock_mem_weightSupportSites f hy
      have a1 := loc (parentBlock R.params.side y) (vacantPart A G f y)
        (A.responseParams.C₀ + recordedSiteScore A G y) (hD _ hb)
        (h.measurable_vacantPart hset hw.measurableSet_vacant f y) (hM y)
        (fun σ => (h.abs_vacantPart_le hsz y σ).trans (by linarith [hM y]))
        (oscillationBound_near hrt (Mb := A.responseParams.C₀ + recordedSiteScore A G y)
          (Mf := 2 * (A.responseParams.C₀ + recordedSiteScore A G y)) (hM y)
          (by linarith [hM y]) (by linarith) (h.abs_vacantPart_le hsz y)
          fun j σ σ' a b d m hm hg => h.vacantPart_far hsz y j σ σ' a b d m hm hg)
      exact add_le_add a1 (cls y hy).2.2)
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
        have e1 : bondFrom Y ((-(Pi.single i 1) : Fin 4 → ℤ), i) = (Y - TorusFields.unitStep n i, i) := by
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
  have hsum : ∑ y ∈ lowerSites f, (C₁ * X * (A.responseParams.C₀ + recordedSiteScore A G y) + C₂ * X) =
      C₁ * X * (((lowerSites f).card : ℝ) * A.responseParams.C₀ + ∑ y ∈ lowerSites f, recordedSiteScore A G y) +
        C₂ * X * ((lowerSites f).card : ℝ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul]
    ring
  rw [hsum]
  have hcard : (upperSites f).card ≤ (lowerSites f).card := by
    have hpar : (open Classical in (lowerSites f).image (parentBlock R.params.side)) = upperSites f :=
      image_parentBlock_weightSupportSites f
    rw [← hpar]
    exact Finset.card_image_le
  have hcc : |R.params.coupling / 2 * A.coeff| * ((upperSites f).card : ℝ) ≤
      A.responseParams.C₀ * ((lowerSites f).card : ℝ) := by
    have ha := h.a_ge
    have h1 : |R.params.coupling / 2 * A.coeff| ≤ A.responseParams.C₀ := by
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ R.params.coupling / 2)]
      have h2 := h.resp.abs_coeff_le
      have h3 := h.c0
      have h4 := abs_nonneg A.coeff
      nlinarith only [h2, h3, h4, ha]
    have h2 : ((upperSites f).card : ℝ) ≤ ((lowerSites f).card : ℝ) := by exact_mod_cast hcard
    exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by linarith)
  exact final_bound_arith (Cz := A.responseParams.C₀) (cA := ((lowerSites f).card : ℝ)) hC₁ hC₂ hX hC1
    (Nat.cast_nonneg _) hN1 hst hcc
end TiltedBound
section Assembly
set_option maxHeartbeats 4000000 in
private theorem statement_holds (hcols : ClusterExpansionOfAStep.GasColumnsSmall) (hpaid : clusterScoreIntegralBound)
    (htwo : ChartResponseComparison) (hsc : BondScoreProperties)
    (hcfg : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hmass : SettingMassEqIntegral)
    (hpot : PotentialFactorization) (hagree : LocalSettingsAgree)
    (hborel : settingMeanMeasurableStatement) (hC : ActivityConditionalLawsStatement)
    (hwn : WeightsCloseToBlockMeans) (hloc : localFunctionFarTiltStatement)
    (hclass : classResponsePartFarTiltStatement) :
    separatedMeanUnderTiltStatement := by
  classical
  obtain ⟨r₁, p₁, H₁⟩ := hcols
  obtain ⟨r₂, p₂, H₂⟩ := hpaid
  obtain ⟨r₃, p₃, H₃⟩ := htwo
  obtain ⟨r₄, p₄, H₄⟩ := hmass
  obtain ⟨r₅, p₅, H₅⟩ := hborel
  obtain ⟨r₇, p₇, H₇⟩ := hloc
  obtain ⟨r₉, p₉, H₉⟩ := hclass
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (min (r₄ c) (min (r₅ c) (min (r₇ c) (r₉ c)))))),
    fun c => by
      simp only [lt_min_iff]
      exact ⟨p₁ c, p₂ c, p₃ c, p₄ c, p₅ c, p₇ c, p₉ c⟩, fun T hT' hrt K => ?_⟩
  simp only [le_min_iff] at hrt
  obtain ⟨t₁, t₂, t₃, t₄, t₅, t₇, t₉⟩ := hrt
  obtain ⟨y₁, H₁⟩ := H₁ T hT' t₁
  obtain ⟨y₂, H₂⟩ := H₂ T hT' t₂ K
  obtain ⟨y₃, H₃⟩ := H₃ T hT' t₃ K
  obtain ⟨y₄, H₄⟩ := H₄ T hT' t₄
  obtain ⟨y₅, H₅⟩ := H₅ T hT' t₅ K
  obtain ⟨y₆, H₆⟩ := hcfg T hT'
  obtain ⟨y₇, C₁, hC₁, H₇⟩ := H₇ T hT' t₇ K
  obtain ⟨y₉, C₂, hC₂, H₉⟩ := H₉ T hT' t₉ K
  have hrt0 := hT'.rt_pos
  have hch : 0 < T.gasRate := by
    have h1 := hT'.cE_pos
    have h2 := hT'.κ_pos
    have h3 := hT'.σ_pos
    unfold ParameterAssignment.gasRate ParameterAssignment.κ₁
    positivity
  refine ⟨max T.floorMin (max y₁ (max y₂ (max y₃ (max y₄ (max y₅ (max y₆ (max y₇ (max y₉ (200 * T.B))))))))),
    18 * C₁ + C₂,
    by positivity, fun y hy R A hK hAT n _ G hG f Q B e Yt D hsz hne hDr hD8 hQ hD hB he ht => ?_⟩
  simp only [max_le_iff] at hy
  obtain ⟨hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7, hy9, hy8⟩ := hy
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
  have st : Standing A G := {
    resp := hAT.admissible
    fit := hfit
    odd := hodd
    row := hstep.1.2
    side := hside
    n0 := hn
    flatD := hflat
    adm := hadm
    dens := fun σ hσ => by
      obtain ⟨a1, a2, -⟩ := H₄ y hy4 R hOT n (by rw [← hRn₀]; exact hn) (configSetting G σ) (hadm σ hσ)
      exact ⟨a1, a2⟩
    agree := hagree
    borel := fun F hF => H₅ y hy5 R A hK hAT n G hG F hF
    a_ge := ha1
    c0 := hc0'
    score_le := fun W V b c => (hsc R.params hfit R.coupling n b c).2.2.1 W V
    score_borel := fun b c => (hsc R.params hfit R.coupling n b c).2.2.2.2
    two := fun s s' Y m hs hs' hag hm => by
      obtain ⟨b1, b2⟩ := ((H₃ y hy3 R A hK hAT).2 n n s s' Y Y m hn hn hs hs').1 hag hm
      exact ⟨fun o ho h => b1 o ho h h fun _ _ _ _ _ => rfl, b2⟩ }
  obtain ⟨hw, cols⟩ := H₁ y hy1 R hOT hx' n G hG fun j => j.1.Touches ∅
  have paid := H₂ y hy2 R A hK hAT n G hG
  have hL1 : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hhat : ∀ Y, |blockMean R.params.side (R.depth + 1) n Y f| ≤ 1 := fun Y =>
    ((hwn R.params.side hodd (R.depth + 1) n Y).1 f).trans ((le_max_left _ _).trans hsz)
  have hs₁ : 0 ≤ A.responseParams.s₁ := by
    have h1 := hl.s₁_eq
    have h2 : 0 ≤ A.responseParams.C₀ + 2 := by linarith only [hc0', ha1]
    rw [h1]
    positivity
  have e0 : (0 : ℝ) ≤ e := by linarith only [he]
  have hq : (0 : ℝ) ≤ (Q.card : ℝ) := Nat.cast_nonneg _
  obtain ⟨Eb, hEb⟩ : ∃ Eb, Eb = Real.exp (-(6 * T.gasRate * R.coupling) - R.params.rt * D / 2 ^ 6) := ⟨_, rfl⟩
  have hEb0 : 0 ≤ Eb := by
    rw [hEb]
    exact (Real.exp_pos _).le
  have hX : 0 ≤ e * (Q.card : ℝ) * Eb := mul_nonneg (mul_nonneg e0 hq) hEb0
  have hlc := H₇ y hy7 R A hK hAT n G hG
  have hcl := H₉ y hy9 R A hK hAT n G hG
  have res := tilted_mean_bound st hrtR he hw paid ht hC hsz hhat hne hs₁ hD hC₁ hC₂ hX
    (fun Y H M hDY hm hM hb ho => by
      have := hlc Y Q B e Yt D H M hDr hQ hDY he ht hm hM hb ho
      rw [← hEb] at this
      exact this.trans (le_of_eq (by ring)))
    (fun y' hy' => by
      obtain ⟨a, b, c⟩ := hcl f y' Q B e Yt D hsz hDr hQ (hD _ (parentBlock_mem_weightSupportSites f hy'))
        (hB y' hy') he ht
      rw [← hEb] at c
      exact ⟨a, b, c.trans (le_of_eq (by ring))⟩)
  refine ⟨res.1, res.2.1, res.2.2.trans ?_⟩
  have hN1 := (sum_recordedSiteScore_le st hs₁ f hne).1
  have hK0 : 0 ≤ lowerSizeConst A f := by
    unfold lowerSizeConst
    have := st.one_le_C₀
    exact mul_nonneg (by linarith only [this]) (Nat.cast_nonneg _)
  have hCC : 0 ≤ 18 * C₁ + C₂ := by positivity
  have hEle : Eb ≤ Real.exp (-(R.params.rt * D / 2 ^ 6)) := by
    rw [hEb]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ 6 * T.gasRate * R.coupling := by positivity
    linarith only [this]
  have hP : 0 ≤ (18 * C₁ + C₂) * e * (Q.card : ℝ) * lowerSizeConst A f *
      meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites f) G.state.1 G.state.2 := by
    have : 0 ≤ meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites f) G.state.1 G.state.2 := by
      linarith only [hN1]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCC e0) hq) hK0) this
  calc _ = ((18 * C₁ + C₂) * e * (Q.card : ℝ) * lowerSizeConst A f *
        meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites f) G.state.1 G.state.2) * Eb := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hEle hP
end Assembly
end SeparatedMeanUnderTilt
theorem separatedMeanUnderTiltStatement_holds (hcols : ClusterExpansionOfAStep.GasColumnsSmall)
    (hpaid : clusterScoreIntegralBound)
    (htwo : ChartResponseComparison) (hsc : BondScoreProperties)
    (hcfg : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hmass : SettingMassEqIntegral)
    (hpot : PotentialFactorization) (hagree : LocalSettingsAgree)
    (hborel : FreeEnergies.settingMeanMeasurableStatement)
    (hC : Dobrushin.ActivityConditionalLawsStatement) (hwn : WeightsCloseToBlockMeans)
    (hloc : localFunctionFarTiltStatement) (hclass : classResponsePartFarTiltStatement) :
    separatedMeanUnderTiltStatement :=
  SeparatedMeanUnderTilt.statement_holds hcols hpaid htwo hsc hcfg hmass hpot hagree hborel hC hwn hloc hclass
end ResponseInTheExpansion
end YangMills.Construction
end
