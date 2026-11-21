import YangMills.Construction.LawByMomentsOfTheFlow.FarCopiesInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.NearCaseFunctionsSplitOverTheGas
import YangMills.Construction.LawByMomentsOfTheFlow.NearFunctionsSplitInASetting
import YangMills.Construction.LawByMomentsOfTheFlow.VariablesAreFarAtLiveStatesProof
import YangMills.Construction.LawInAState.CellsOfAPair
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open StepSettings TorusFields TorusLumps StepGas StepCosts WeightedResponses Dobrushin
namespace FarCovarianceDecay
section CoarseCases
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem caseIntegrable_of_abs_le (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n)
    {F : CaseFunction R n}
    (h1 : CaseIntegrable R C V q fun _ _ _ _ _ => 1)
    (hFm : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => F p.1 Yt p.2 bad b)
    {U : ℝ} (_hU : 0 ≤ U)
    (hle : ∀ W Yt ωt bad b, |F W Yt ωt bad b| ≤ U) : CaseIntegrable R C V q F := by apply _root_.YangMills.SharedProofs.p19766 <;> assumption
private theorem isHullState_of_weight_pos (hH : CoarseHullIsHullState) (hFo : R.IsWellPosed)
    (hbs : IsBlockTorusSide R.params n) {V : TorusField n}
    {q : CoarseState R n} (hpos : 0 < coarseStateWeight R (hotCoreSites R V) V q) :
    IsHullState R.params R.nextRange V q.1 := by apply _root_.YangMills.SharedProofs.p64097 <;> assumption
end CoarseCases
section GroundMeans
variable {R : StepSetup} {n : ℕ} [NeZero n]
private def GroundMeanIdentities (G : GasGround R n) : Prop :=
  (∀ᵐ σ ∂G.gibbsLaw ∅, G.pairConstraint.IsAdmissible σ ∧ 0 < ∫ η, chartDensity (configSetting G σ) η) ∧
    ∀ F : CaseFunction R n,
      (∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
        (b : BaseChoice R.params.side n),
        Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => F p.1 Yt p.2 bad b) →
      IsGaugeInvariantCase F → CaseIntegrable R G.cut G.coarse G.state F →
      Integrable (fun σ => weightedMean (chartDensity (configSetting G σ)) fun η =>
        F ((configSetting G σ).field η) (configSetting G σ).support (configSetting G σ).labelling
          (G.badBondsOf σ) (configSetting G σ).bases)
        (G.gibbsLaw ∅) ∧
      caseMean R G.cut G.coarse G.state F = gasExpectationOfCase G F
private abbrev settingMeanAt (G : GasGround R n) (F : CaseFunction R n) (σ : G.Config) : ℝ :=
  FreeEnergies.settingMean (configSetting G σ) (G.badBondsOf σ) F
private theorem abs_settingMeanAt_le (G : GasGround R n) {F : CaseFunction R n} {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ W Yt ωt bad b, |F W Yt ωt bad b| ≤ c) (σ : G.Config) : |settingMeanAt G F σ| ≤ c :=
  abs_weightedMean_le hc fun _ => hF _ _ _ _ _
private theorem covariance_le_at_ground (G : GasGround R n) (hCm : GroundMeanIdentities G)
    (hP : IsProbabilityMeasure (G.gibbsLaw ∅))
    {o o' : TorusSite (n * R.params.side)} {ρ : ℕ} {K : ℝ} (hK : 0 ≤ K) {F₁ F₂ : CaseFunction R n}
    (n₁ : IsNearlyLocalCaseFunction R o ρ K F₁) (n₂ : IsNearlyLocalCaseFunction R o' ρ K F₂)
    (h1 : CaseIntegrable R G.cut G.coarse G.state fun _ _ _ _ _ => 1) :
    |caseMean R G.cut G.coarse G.state (fun W Yt ωt bad b => F₁ W Yt ωt bad b * F₂ W Yt ωt bad b) -
        caseMean R G.cut G.coarse G.state F₁ * caseMean R G.cut G.coarse G.state F₂| ≤ 2 * K ^ 2 ∧
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ →
      (∀ σ, G.pairConstraint.IsAdmissible σ → 0 < ∫ η, chartDensity (configSetting G σ) η →
        |settingMeanAt G (fun W Yt ωt bad b => F₁ W Yt ωt bad b * F₂ W Yt ωt bad b) σ -
          settingMeanAt G F₁ σ * settingMeanAt G F₂ σ| ≤ E₁) →
      |G.expectation ∅ (fun σ => settingMeanAt G F₁ σ * settingMeanAt G F₂ σ) -
          G.expectation ∅ (settingMeanAt G F₁) * G.expectation ∅ (settingMeanAt G F₂)| ≤ E₂ →
      |caseMean R G.cut G.coarse G.state (fun W Yt ωt bad b => F₁ W Yt ωt bad b * F₂ W Yt ωt bad b) -
          caseMean R G.cut G.coarse G.state F₁ * caseMean R G.cut G.coarse G.state F₂| ≤ E₁ + E₂ := by
  classical
  have := hP
  obtain ⟨hae, hF⟩ := hCm
  let Fc : CaseFunction R n := fun W Yt ωt bad b => F₁ W Yt ωt bad b * F₂ W Yt ωt bad b
  have hFcm : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => Fc p.1 Yt p.2 bad b :=
    fun Yt bad b => (n₁.measurable Yt bad b).mul (n₂.measurable Yt bad b)
  have hFcg : IsGaugeInvariantCase Fc := fun W Yt ωt bad b u hl hb hc => by
    show F₁ _ _ _ _ _ * F₂ _ _ _ _ _ = F₁ _ _ _ _ _ * F₂ _ _ _ _ _
    rw [n₁.gaugeInvariant W Yt ωt bad b u hl hb hc, n₂.gaugeInvariant W Yt ωt bad b u hl hb hc]
  have hKK : 0 ≤ K * K := mul_nonneg hK hK
  have hFcb : ∀ W Yt ωt bad b, |Fc W Yt ωt bad b| ≤ K * K := fun W Yt ωt bad b => by
    show |F₁ _ _ _ _ _ * F₂ _ _ _ _ _| ≤ _
    rw [abs_mul]
    exact mul_le_mul (n₁.abs_le _ _ _ _ _) (n₂.abs_le _ _ _ _ _) (abs_nonneg _) hK
  obtain ⟨iF, eF⟩ := hF Fc hFcm hFcg (caseIntegrable_of_abs_le _ _ _ h1 hFcm hKK hFcb)
  obtain ⟨i₁, e₁⟩ := hF F₁ n₁.measurable n₁.gaugeInvariant
    (caseIntegrable_of_abs_le _ _ _ h1 n₁.measurable hK n₁.abs_le)
  obtain ⟨i₂, e₂⟩ := hF F₂ n₂.measurable n₂.gaugeInvariant
    (caseIntegrable_of_abs_le _ _ _ h1 n₂.measurable hK n₂.abs_le)
  have eF' : caseMean R G.cut G.coarse G.state Fc = ∫ σ, settingMeanAt G Fc σ ∂G.gibbsLaw ∅ := eF
  have e₁' : caseMean R G.cut G.coarse G.state F₁ = ∫ σ, settingMeanAt G F₁ σ ∂G.gibbsLaw ∅ := e₁
  have e₂' : caseMean R G.cut G.coarse G.state F₂ = ∫ σ, settingMeanAt G F₂ σ ∂G.gibbsLaw ∅ := e₂
  have b₁ : ∀ σ, |settingMeanAt G F₁ σ| ≤ K := abs_settingMeanAt_le G hK n₁.abs_le
  have b₂ : ∀ σ, |settingMeanAt G F₂ σ| ≤ K := abs_settingMeanAt_le G hK n₂.abs_le
  have bF : ∀ σ, |settingMeanAt G Fc σ| ≤ K * K := abs_settingMeanAt_le G hKK hFcb
  have abs_integral_le : ∀ {f : G.Config → ℝ} {c : ℝ}, (∀ σ, |f σ| ≤ c) → |∫ σ, f σ ∂G.gibbsLaw ∅| ≤ c :=
    fun {f c} h => by
      have := norm_integral_le_of_norm_le_const (μ := G.gibbsLaw ∅) (C := c) (f := f)
        (Filter.Eventually.of_forall fun σ => by simpa [Real.norm_eq_abs] using h σ)
      simpa [Real.norm_eq_abs] using this
  constructor
  · show |caseMean R G.cut G.coarse G.state Fc - _| ≤ _
    rw [eF', e₁', e₂']
    have c1 := abs_integral_le bF
    have c2 := abs_integral_le b₁
    have c3 := abs_integral_le b₂
    have c4 : |(∫ σ, settingMeanAt G F₁ σ ∂G.gibbsLaw ∅) * ∫ σ, settingMeanAt G F₂ σ ∂G.gibbsLaw ∅| ≤ K * K := by
      rw [abs_mul]
      exact mul_le_mul c2 c3 (abs_nonneg _) hK
    have c5 := abs_sub (∫ σ, settingMeanAt G Fc σ ∂G.gibbsLaw ∅)
      ((∫ σ, settingMeanAt G F₁ σ ∂G.gibbsLaw ∅) * ∫ σ, settingMeanAt G F₂ σ ∂G.gibbsLaw ∅)
    nlinarith
  · intro E₁ E₂ hE₁ hS hgas
    let h : G.Config → ℝ := fun σ => settingMeanAt G F₁ σ * settingMeanAt G F₂ σ
    have if' : Integrable (settingMeanAt G Fc) (G.gibbsLaw ∅) := iF
    have i₁' : Integrable (settingMeanAt G F₁) (G.gibbsLaw ∅) := i₁
    have i₂' : Integrable (settingMeanAt G F₂) (G.gibbsLaw ∅) := i₂
    have ih : Integrable h (G.gibbsLaw ∅) := by
      refine Integrable.of_bound (i₁'.aestronglyMeasurable.mul i₂'.aestronglyMeasurable) (K * K)
        (Filter.Eventually.of_forall fun σ => ?_)
      show ‖settingMeanAt G F₁ σ * settingMeanAt G F₂ σ‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (b₁ σ) (b₂ σ) (abs_nonneg _) hK
    have hdiff : ∀ᵐ σ ∂G.gibbsLaw ∅, |settingMeanAt G Fc σ - h σ| ≤ E₁ := by
      filter_upwards [hae] with σ hσ
      exact hS σ hσ.1 hσ.2
    have step : |∫ σ, settingMeanAt G Fc σ ∂G.gibbsLaw ∅ - ∫ σ, h σ ∂G.gibbsLaw ∅| ≤ E₁ := by
      rw [← integral_sub if' ih]
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ σ, |settingMeanAt G Fc σ - h σ| ∂G.gibbsLaw ∅ ≤ ∫ _σ, E₁ ∂G.gibbsLaw ∅ :=
            integral_mono_ae (if'.sub ih).abs (integrable_const E₁) hdiff
        _ = E₁ := by simp
    have hgas' : |∫ σ, h σ ∂G.gibbsLaw ∅ -
        (∫ σ, settingMeanAt G F₁ σ ∂G.gibbsLaw ∅) * ∫ σ, settingMeanAt G F₂ σ ∂G.gibbsLaw ∅| ≤ E₂ := hgas
    show |caseMean R G.cut G.coarse G.state Fc - _| ≤ _
    rw [eF', e₁', e₂']
    calc _ ≤ |∫ σ, settingMeanAt G Fc σ ∂G.gibbsLaw ∅ - ∫ σ, h σ ∂G.gibbsLaw ∅| +
          |∫ σ, h σ ∂G.gibbsLaw ∅ -
            (∫ σ, settingMeanAt G F₁ σ ∂G.gibbsLaw ∅) * ∫ σ, settingMeanAt G F₂ σ ∂G.gibbsLaw ∅| :=
          abs_sub_le _ _ _
      _ ≤ _ := add_le_add step hgas'
end GroundMeans
section SingleStep
set_option maxHeartbeats 4000000 in
private theorem covariance_bound_at_step (hS : nearlyLocalSettingFactorizationStatement)
    (hG : nearCaseFunctionsSplitStatement) (hC : caseMeanEqGasMeanStatement)
    (hM : ResponseInTheExpansion.productMeanScoreStepBound) (hcol : ClusterExpansionOfAStep.GasColumnsSmall)
    (hA : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hHu : HullStateIsHotCase)
    (hZ : ClusterExpansionOfAStep.CoarseWeightZeroOfFactorZero) (hH : CoarseHullIsHullState) :
    ∃ rt₀ : RenormalizationStepParameters.ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible →
      T.rt ≤ rt₀ T.toChainParameters →
      ∀ Kr : ResponseParameters, ∃ y₀ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y₀ ≤ y → ∀ (R : StepSetup) (A : ResponseSetup R),
        A.responseParams = Kr →
        OnStepParameters T y A → R.IsWellPosed → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
        ∀ (F₁ F₂ : CaseFunction R n) (o o' : TorusSite (n * R.params.side)) (K : ℝ) (ρ : ℕ),
          IsNearlyLocalCaseFunction R o ρ K F₁ → IsNearlyLocalCaseFunction R o' ρ K F₂ →
          ∀ (V : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel R.labels.Ω R.params.side),
            0 < coarseStateWeight R (hotCoreSites R V) V ⟨Y, ω⟩ →
            CaseIntegrable R (hotCoreSites R V) V ⟨Y, ω⟩ (fun _ _ _ _ _ => 1) ∧
            |caseMean R (hotCoreSites R V) V ⟨Y, ω⟩ (fun W Yt ωt bad b => F₁ W Yt ωt bad b * F₂ W Yt ωt bad b) -
                caseMean R (hotCoreSites R V) V ⟨Y, ω⟩ F₁ * caseMean R (hotCoreSites R V) V ⟨Y, ω⟩ F₂| ≤
              2 * K ^ 2 ∧
            ∀ D : ℕ, 2 ^ 10 * ((R.range : ℝ) + ρ) ≤ D →
            D ≤ TorusFields.supDist (parentBlock R.params.side o) (parentBlock R.params.side o') →
            |caseMean R (hotCoreSites R V) V ⟨Y, ω⟩ (fun W Yt ωt bad b => F₁ W Yt ωt bad b * F₂ W Yt ωt bad b) -
                caseMean R (hotCoreSites R V) V ⟨Y, ω⟩ F₁ * caseMean R (hotCoreSites R V) V ⟨Y, ω⟩ F₂| ≤
              C * K ^ 2 * Real.exp (-(R.params.rt * D / 2 ^ 7)) := by
  classical
  obtain ⟨r₁, p₁, g₁⟩ := hS
  obtain ⟨r₂, p₂, g₂⟩ := hG
  obtain ⟨r₃, p₃, g₃⟩ := hC
  obtain ⟨r₄, p₄, g₄⟩ := hM
  obtain ⟨r₅, p₅, g₅⟩ := hcol
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (min (r₄ c) (r₅ c)))),
    fun c => lt_min (p₁ c) (lt_min (p₂ c) (lt_min (p₃ c) (lt_min (p₄ c) (p₅ c)))), fun T hT hrt Kr => ?_⟩
  have b1 := hrt.trans (min_le_left _ _)
  have hr2 := hrt.trans (min_le_right _ _)
  have b2 := hr2.trans (min_le_left _ _)
  have hr3 := hr2.trans (min_le_right _ _)
  have b3 := hr3.trans (min_le_left _ _)
  have hr4 := hr3.trans (min_le_right _ _)
  have b4 := hr4.trans (min_le_left _ _)
  have b5 := hr4.trans (min_le_right _ _)
  obtain ⟨y₁, C₁, hC₁, S₁⟩ := g₁ T hT b1
  obtain ⟨y₂, C₂, hC₂, G₁⟩ := g₂ T hT b2 Kr
  obtain ⟨y₃, M₃⟩ := g₃ T hT b3
  obtain ⟨y₄, M₄⟩ := g₄ T hT b4 Kr
  obtain ⟨y₅, M₅⟩ := g₅ T hT b5
  obtain ⟨y₆, A₁⟩ := hA T hT
  obtain ⟨y₇, U₁⟩ := hHu T hT
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) (max (max y₅ y₆) (max y₇ (200 * T.B))), C₁ + C₂, add_nonneg hC₁ hC₂,
    fun y hy R A hAK hAt hFo n _ hbsn F₁ F₂ o o' K ρ hn₁ hn₂ V Y ω hpos => ?_⟩
  simp only [max_le_iff] at hy
  obtain ⟨⟨⟨hy1, hy2⟩, hy3, hy4⟩, ⟨hy5, hy6⟩, hy7, hyB⟩ := hy
  have hR := hAt.onFamily
  have hxy := hR.le_coupling
  have hB1 : (1 : ℝ) ≤ T.B := hT.B_ge
  have hxx : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAt.abs_sub_le).2
    linarith
  have hrtR : 0 ≤ R.params.rt := by
    rw [hR.params_eq]
    exact hT.rt_pos.le
  have hhull : IsHullState R.params R.nextRange V Y := isHullState_of_weight_pos (q := ⟨Y, ω⟩) hH hFo hbsn hpos
  have hΦ : ∀ X ∈ chainComponents R.nextRange Y, coarseFactor V (⟨Y, ω⟩ : CoarseState R n) X ≠ 0 := by
    intro X hX h0
    have := hZ R hFo n hbsn V ⟨Y, ω⟩ hhull ⟨X, hX, h0⟩
    linarith
  have hGr : (hotCaseGround R V ⟨Y, ω⟩).IsAdmissibleGround :=
    Or.inr (U₁ y hy7 R hR hFo n hbsn V ⟨Y, ω⟩ hhull hΦ)
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn₀ : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hLpos) hbsn.2
  obtain ⟨hw, hc⟩ := M₅ y hy5 R hR hxx n (hotCaseGround R V ⟨Y, ω⟩) hGr fun j => j.1.Touches ∅
  have hP : IsProbabilityMeasure ((hotCaseGround R V ⟨Y, ω⟩).gibbsLaw ∅) := hc.isProbabilityMeasure
  have h1 : CaseIntegrable R (hotCaseGround R V ⟨Y, ω⟩).cut (hotCaseGround R V ⟨Y, ω⟩).coarse
      (hotCaseGround R V ⟨Y, ω⟩).state fun _ _ _ _ _ => 1 := by
    simpa using (M₄ y hy4 R A hAK hAt n _ hGr Empty ∅ (fun e => e.elim)
      fun i hi => absurd hi (Finset.notMem_empty _)).1
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hn₁.abs_le (trivialField _) ∅ (StateLaws.emptyLabelling R.labels.Ω) ∅
    (hotCaseGround R V ⟨Y, ω⟩).groundBases)
  obtain ⟨hb, hsplit⟩ := covariance_le_at_ground (hotCaseGround R V ⟨Y, ω⟩) (M₃ y hy3 R hR hxx n _ hGr) hP hK0
    hn₁ hn₂ h1
  refine ⟨h1, hb, fun D hD hap => ?_⟩
  set e7 := Real.exp (-(R.params.rt * D / 2 ^ 7)) with he7
  set e4 := Real.exp (-(R.params.rt * D / 2 ^ 4)) with he4
  have he7p : 0 < e7 := Real.exp_pos _
  have he4p : 0 < e4 := Real.exp_pos _
  have he : e4 ≤ e7 := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ R.params.rt * (D : ℝ) := mul_nonneg hrtR (Nat.cast_nonneg _)
    linarith
  set Fs : Fin 2 → CaseFunction R n := ![F₁, F₂] with hFs
  set zs : Fin 2 → TorusSite (n * R.params.side) := ![o, o'] with hzs
  have hnear : ∀ i, IsNearlyLocalCaseFunction R (zs i) ρ K (Fs i) := by
    intro i
    fin_cases i
    · exact hn₁
    · exact hn₂
  have hfar : ∀ i j : Fin 2, i ≠ j →
      D ≤ TorusFields.supDist (parentBlock R.params.side (zs i)) (parentBlock R.params.side (zs j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hap
    · show D ≤ TorusFields.supDist (parentBlock R.params.side o') (parentBlock R.params.side o)
      rw [TorusFields.supDist_comm]
      exact hap
    · exact absurd rfl hij
  have hgas := G₁ y hy2 R A hAK hAt n _ hGr 2 Fs zs K ρ D (by norm_num) hnear hD hfar
  simp only [Fin.prod_univ_two] at hgas
  have hS₀ : ∀ σ, (hotCaseGround R V ⟨Y, ω⟩).pairConstraint.IsAdmissible σ →
      0 < ∫ η, chartDensity (configSetting (hotCaseGround R V ⟨Y, ω⟩) σ) η →
      |settingMeanAt (hotCaseGround R V ⟨Y, ω⟩) (fun W Yt ωt bad b => F₁ W Yt ωt bad b * F₂ W Yt ωt bad b) σ -
        settingMeanAt (hotCaseGround R V ⟨Y, ω⟩) F₁ σ * settingMeanAt (hotCaseGround R V ⟨Y, ω⟩) F₂ σ| ≤
        C₁ * K ^ 2 * e4 := by
    intro σ ha _
    have hs := A₁ y hy6 R hR hxx n _ hGr σ ha
    have h2 := S₁ y hy1 R hR n (configSetting (hotCaseGround R V ⟨Y, ω⟩) σ) hn₀ hs 2
      (fun i W A₂ ω₂ => Fs i W A₂ ω₂ ((hotCaseGround R V ⟨Y, ω⟩).badBondsOf σ)
        (configSetting (hotCaseGround R V ⟨Y, ω⟩) σ).bases)
      zs K ρ D (by norm_num) (by norm_num) (Nat.cast_nonneg _) (fun i => (hnear i).toStateFunction _ _) hD hfar
    simp only [Fin.prod_univ_two] at h2
    exact h2
  have key := hsplit (C₁ * K ^ 2 * e4) (C₂ * K ^ 2 * e7)
    (mul_nonneg (mul_nonneg hC₁ (by positivity)) he4p.le) hS₀ hgas
  refine key.trans ?_
  have h3 : C₁ * K ^ 2 * e4 ≤ C₁ * K ^ 2 * e7 := mul_le_mul_of_nonneg_left he (mul_nonneg hC₁ (by positivity))
  calc _ ≤ C₁ * K ^ 2 * e7 + C₂ * K ^ 2 * e7 := by linarith
    _ = _ := by ring
end SingleStep
end FarCovarianceDecay
open FarCovarianceDecay in
theorem farCovarianceDecay (hS : nearlyLocalSettingFactorizationStatement)
    (hG : nearCaseFunctionsSplitStatement) (hC : caseMeanEqGasMeanStatement)
    (hM : ResponseInTheExpansion.productMeanScoreStepBound) (hcol : ClusterExpansionOfAStep.GasColumnsSmall)
    (hA : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hHu : HullStateIsHotCase)
    (hZ : ClusterExpansionOfAStep.CoarseWeightZeroOfFactorZero) (hH : CoarseHullIsHullState)
    (hLv : ResponseInTheExpansion.StagesAreWellPosed) : farCovarianceDecayStatement := by
  classical
  obtain ⟨rt₀, hrt₀, H⟩ := covariance_bound_at_step hS hG hC hM hcol hA hHu hZ hH
  intro a _
  refine ⟨0, rt₀, 0, hrt₀, fun L _ _ Tb _ _ hTd _ _ hrt _ Kr _ => ?_⟩
  obtain ⟨y₁, C, hC0, H⟩ := H Tb hTd hrt Kr
  obtain ⟨y₂, V₁⟩ := hLv Tb hTd
  refine ⟨max y₁ y₂, fun y hy _ _ g _ _ k _ _ _ Rd d _ => ?_⟩
  intro K β Sz Rr
  have hrt0 : 0 < Tb.rt := hTd.rt_pos
  set Dm : ℝ := 2 ^ 10 * ((∑ u ∈ Finset.range K,
    (clusterRange (ResponseInTheExpansion.couplingsAlongFlow (Tb.stepParameters y) β u) : ℝ)) + Rr) with hDm
  refine ⟨C * Sz ^ 2 + 2 * Sz ^ 2 * Real.exp (Tb.rt * Dm / 2 ^ 8), ?_⟩
  intro S hK hβ u n _ hu hn V Y ω hpos o o' F G hF hG'
  subst hβ
  have hKu : u ≤ S.data.windowLevel := by omega
  have hst := S.onFlow u hKu
  have hFo := V₁ y ((le_max_right _ _).trans hy) Kr S.β S.labelFacts S.initial S.isInitial S.data.windowLevel
    S.onFlow u hKu
  have pack : ∀ z : ResponseInTheExpansion.StageWithResponse (Tb.stepParameters y),
      z = ResponseInTheExpansion.flowStages Tb y S.β S.labelFacts S.initial u →
      z.2.responseParams = Kr ∧ OnStepParameters Tb y z.2 ∧ z.1.toStepSetup.IsWellPosed ∧
        z.1.coupling = ResponseInTheExpansion.couplingsAlongFlow (Tb.stepParameters y) S.β u := by
    rintro _ rfl
    exact ⟨hst.params_eq, hst.onFamily, hFo, hst.coupling_eq⟩
  obtain ⟨hAK, hAt, hFS, hxe⟩ := pack ⟨S.tower.stage u, S.resp u⟩ (S.stage_eq u hKu)
  have hLpos : 0 < (Tb.stepParameters y).side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn₀ : 4096 ≤ (Tb.stepParameters y).n₀ := hTd.n₀_ge
  have hbs : IsBlockTorusSide (Tb.stepParameters y) n := by
    have hside : (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤
        S.data.period (Tb.stepParameters y).side := S.side_le
    have hm : S.data.sideExponent ≠ 0 := by
      intro h0
      unfold LevelTestFunctions.LevelData.period at hside
      rw [h0, pow_zero] at hside
      nlinarith
    rw [hn]
    refine ⟨?_, hside.trans (Nat.le_mul_of_pos_right _ (pow_pos hLpos _))⟩
    show (Tb.stepParameters y).side ∣
      S.data.period (Tb.stepParameters y).side * (Tb.stepParameters y).side ^ (S.data.windowLevel - (u + 1))
    unfold LevelTestFunctions.LevelData.period
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ hm) _) _
  have hb := H y ((le_max_left _ _).trans hy) (S.tower.stage u).toStepSetup (S.resp u) hAK hAt hFS n hbs
    F G o o' Sz Rr hF hG' V Y ω hpos
  obtain ⟨hI1, hsm, hbig⟩ := hb
  refine ⟨hI1, ?_⟩
  have hSz : 0 ≤ Sz ^ 2 := by positivity
  obtain ⟨Dd, hDd⟩ : ∃ Dd : ℕ,
      Dd = TorusFields.supDist (parentBlock (Tb.stepParameters y).side o) (parentBlock (Tb.stepParameters y).side o') :=
    ⟨_, rfl⟩
  have hrRr : (clusterRange (S.tower.stage u).toStepSetup.coupling : ℝ) ≤
      ∑ v ∈ Finset.range K, (clusterRange (ResponseInTheExpansion.couplingsAlongFlow (Tb.stepParameters y) S.β v) : ℝ) := by
    have e : (S.tower.stage u).toStepSetup.coupling =
        ResponseInTheExpansion.couplingsAlongFlow (Tb.stepParameters y) S.β u := hxe
    rw [e]
    exact Finset.single_le_sum
      (f := fun v => (clusterRange (ResponseInTheExpansion.couplingsAlongFlow (Tb.stepParameters y) S.β v) : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_range.mpr (hK ▸ hu))
  have he8 : 0 < Real.exp (-((Tb.stepParameters y).rt * (Dd : ℝ) / 2 ^ 8)) := Real.exp_pos _
  have hrtL : (Tb.stepParameters y).rt = Tb.rt := rfl
  by_cases hD : 2 ^ 10 * (((S.tower.stage u).toStepSetup.range : ℝ) + Rr) ≤ Dd
  · have h1 := hbig Dd hD hDd.le
    refine h1.trans ?_
    have h2 : Real.exp (-((S.tower.stage u).toStepSetup.params.rt * (Dd : ℝ) / 2 ^ 7)) ≤
        Real.exp (-((Tb.stepParameters y).rt * (Dd : ℝ) / 2 ^ 8)) := by
      apply Real.exp_le_exp.mpr
      have h3 : 0 ≤ (Tb.stepParameters y).rt * (Dd : ℝ) := by
        rw [hrtL]
        positivity
      have h4 : (S.tower.stage u).toStepSetup.params.rt = (Tb.stepParameters y).rt := rfl
      rw [h4]
      linarith
    rw [← hDd]
    have hCS : 0 ≤ C * Sz ^ 2 := mul_nonneg hC0 hSz
    have hx : 0 ≤ 2 * Sz ^ 2 * Real.exp (Tb.rt * Dm / 2 ^ 8) := by positivity
    calc _ ≤ C * Sz ^ 2 * Real.exp (-((Tb.stepParameters y).rt * (Dd : ℝ) / 2 ^ 8)) :=
          mul_le_mul_of_nonneg_left h2 hCS
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) he8.le
  · refine hsm.trans ?_
    rw [← hDd]
    have hDl : (Dd : ℝ) ≤ Dm := by
      have h1 : (Dd : ℝ) < 2 ^ 10 * (((S.tower.stage u).toStepSetup.range : ℝ) + Rr) := not_le.mp hD
      have h2 : ((S.tower.stage u).toStepSetup.range : ℝ) =
          (clusterRange (S.tower.stage u).toStepSetup.coupling : ℝ) := rfl
      rw [hDm]
      rw [h2] at h1
      nlinarith
    have h1 : 1 ≤ Real.exp (Tb.rt * Dm / 2 ^ 8) * Real.exp (-((Tb.stepParameters y).rt * (Dd : ℝ) / 2 ^ 8)) := by
      rw [← Real.exp_add, hrtL]
      apply Real.one_le_exp
      have := mul_le_mul_of_nonneg_left hDl hrt0.le
      have e : Tb.rt * Dm / 2 ^ 8 + -(Tb.rt * (Dd : ℝ) / 2 ^ 8) = (Tb.rt * Dm - Tb.rt * Dd) / 2 ^ 8 := by ring
      rw [e]
      apply div_nonneg _ (by positivity)
      linarith
    have hCS : 0 ≤ C * Sz ^ 2 := mul_nonneg hC0 hSz
    calc 2 * Sz ^ 2 = 2 * Sz ^ 2 * 1 := (mul_one _).symm
      _ ≤ 2 * Sz ^ 2 * (Real.exp (Tb.rt * Dm / 2 ^ 8) *
            Real.exp (-((Tb.stepParameters y).rt * (Dd : ℝ) / 2 ^ 8))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * Sz ^ 2 * Real.exp (Tb.rt * Dm / 2 ^ 8) *
            Real.exp (-((Tb.stepParameters y).rt * (Dd : ℝ) / 2 ^ 8)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) he8.le
end YangMills.Construction.MomentLaw
end
