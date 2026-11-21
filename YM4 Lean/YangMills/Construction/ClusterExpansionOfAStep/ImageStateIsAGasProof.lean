import YangMills.Construction.ClusterExpansionOfAStep.CalculusOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.ConfigurationsOfTheGasAreSettings
import YangMills.Construction.ClusterExpansionOfAStep.ConvexityOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.GasIsAWeight
import YangMills.Construction.ClusterExpansionOfAStep.GroundHasWeightAtItsFrames
import YangMills.Construction.ClusterExpansionOfAStep.ImageAtAGroundIsTheSumOverTheGas
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsAGas
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfPointsOfWeight
import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.StepSettings YangMills.Construction.StepGas YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters YangMills.Construction.Dobrushin YangMills.Construction.ClusterExpansionOfAStep
namespace CoarseGas
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖(toImaginary v : ℍ[ℝ])‖ = ‖v‖ := by apply _root_.YangMills.Construction.BlockTrees.norm_toImaginary <;> assumption
theorem cutoffFactor_le_one {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) {t : ℝ} (ht₀ : 0 ≤ t) :
    cutoffFactor ρ p t ≤ 1 := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_le_one <;> assumption
theorem cutoffFactor_nonneg (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
theorem measurable_cutoffFactor_coordNorm (ρ : ℝ) (p : ℝ → ℝ) (hp : IsCutoff ρ p) :
    Measurable fun v : EuclideanSpace ℝ (Fin 3) => cutoffFactor ρ p (coordNorm v) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.measurable_cutoffFactor_coordNorm <;> assumption
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem settingMass_pos_finite_integral (s : ChartSetting R n) (hρ : 0 < R.ballRadius)
    (hp : IsCutoff R.ballRadius R.barrierFn) {U : Set (FreeCoords s.free)}
    (hU : ∀ η, s.InBalls η → η ∈ U) (hcont : ContinuousOn s.potential U) :
    0 < settingMass s ∧ settingMass s ≠ ⊤ ∧
      (settingMass s).toReal = ∫ η, s.cutoffProduct η * Real.exp (-s.potential η) := by
  classical
  set K : Set (FreeCoords s.free) := Set.univ.pi fun _ => Metric.closedBall 0 R.ballRadius with hKdef
  have hmemK : ∀ η, η ∈ K ↔ s.InBalls η := by
    intro η
    simp only [hKdef, Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right,
      ChartSetting.InBalls, coordNorm, norm_toImaginary]
  have hKcpt : IsCompact K := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hKmeas : MeasurableSet K := MeasurableSet.univ_pi fun _ => measurableSet_closedBall
  have hcontK : ContinuousOn s.potential K := hcont.mono fun η hη => hU η ((hmemK η).mp hη)
  obtain ⟨A, hA⟩ := hKcpt.exists_bound_of_continuousOn hcontK
  set f : FreeCoords s.free → ℝ := fun η => s.cutoffProduct η * Real.exp (-s.potential η) with hfdef
  have hcut_nonneg : ∀ η, 0 ≤ s.cutoffProduct η :=
    fun η => Finset.prod_nonneg fun b _ => cutoffFactor_nonneg _ _ _
  have hcut_le : ∀ η, s.cutoffProduct η ≤ 1 := fun η => by
    unfold ChartSetting.cutoffProduct
    exact Finset.prod_le_one (fun b _ => cutoffFactor_nonneg _ _ _)
      fun b _ => cutoffFactor_le_one hρ hp (norm_nonneg _)
  have hf_nonneg : ∀ η, 0 ≤ f η := fun η => mul_nonneg (hcut_nonneg η) (Real.exp_pos _).le
  have hf_out : ∀ η, η ∉ K → f η = 0 := by
    intro η hη
    rw [hmemK] at hη
    unfold ChartSetting.InBalls at hη
    push Not at hη
    obtain ⟨b, hb⟩ := hη
    have hzero : s.cutoffProduct η = 0 := by
      unfold ChartSetting.cutoffProduct
      apply Finset.prod_eq_zero (Finset.mem_univ b)
      unfold cutoffFactor
      rw [if_neg (not_lt.mpr hb.le)]
    simp [hfdef, hzero]
  have hf_le : ∀ η ∈ K, f η ≤ Real.exp A := by
    intro η hη
    have hbound := hA η hη
    have hneg : -s.potential η ≤ A := by
      have := (abs_le.mp hbound).1
      linarith
    calc f η ≤ 1 * Real.exp (-s.potential η) :=
          mul_le_mul_of_nonneg_right (hcut_le η) (Real.exp_pos _).le
      _ ≤ Real.exp A := by rw [one_mul]; exact Real.exp_le_exp.mpr hneg
  have hcut_meas : Measurable fun η : FreeCoords s.free => s.cutoffProduct η := by
    unfold ChartSetting.cutoffProduct
    exact Finset.measurable_prod _ fun b _ =>
      (measurable_cutoffFactor_coordNorm _ _ hp).comp (measurable_pi_apply b)
  have hf_measK : AEStronglyMeasurable f (volume.restrict K) := by
    have hexp : AEStronglyMeasurable (fun η => Real.exp (-s.potential η)) (volume.restrict K) :=
      (Real.continuous_exp.comp_continuousOn hcontK.neg).aestronglyMeasurable hKmeas
    exact hcut_meas.aestronglyMeasurable.mul hexp
  have hf_meas : AEStronglyMeasurable f volume := by
    have hind : f = K.indicator f := by
      funext η
      by_cases hη : η ∈ K
      · rw [Set.indicator_of_mem hη]
      · rw [Set.indicator_of_notMem hη, hf_out η hη]
    rw [hind]
    exact (aestronglyMeasurable_indicator_iff hKmeas).mpr hf_measK
  have hlt_top : ∫⁻ η, ENNReal.ofReal (f η) < ⊤ := by
    have hle : ∀ η, ENNReal.ofReal (f η) ≤ K.indicator (fun _ => ENNReal.ofReal (Real.exp A)) η := by
      intro η
      by_cases hη : η ∈ K
      · rw [Set.indicator_of_mem hη]
        exact ENNReal.ofReal_le_ofReal (hf_le η hη)
      · rw [Set.indicator_of_notMem hη, hf_out η hη]
        simp
    refine lt_of_le_of_lt (lintegral_mono hle) ?_
    rw [lintegral_indicator_const hKmeas]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKcpt.measure_lt_top
  set B : Set (FreeCoords s.free) := Set.univ.pi fun _ => Metric.ball 0 (R.ballRadius / 2) with hBdef
  have hBmeas : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_ball
  have hBK : B ⊆ K := fun η hη b _ => Metric.ball_subset_closedBall
    (Metric.ball_subset_ball (by linarith) (hη b (Set.mem_univ b)))
  have hpos : 0 < ∫⁻ η, ENNReal.ofReal (f η) := by
    have hge : ∀ η, B.indicator (fun _ => ENNReal.ofReal (Real.exp (-A))) η ≤ ENNReal.ofReal (f η) := by
      intro η
      by_cases hη : η ∈ B
      · rw [Set.indicator_of_mem hη]
        apply ENNReal.ofReal_le_ofReal
        have hone : s.cutoffProduct η = 1 := by
          unfold ChartSetting.cutoffProduct
          apply Finset.prod_eq_one
          intro b _
          have hb : ‖η b‖ < R.ballRadius / 2 := by
            simpa [Metric.mem_ball, dist_zero_right] using hη b (Set.mem_univ b)
          unfold cutoffFactor coordNorm
          rw [norm_toImaginary, if_pos (by linarith), hp.vanish_small _ (norm_nonneg _) (by linarith)]
          simp
        have hbound := hA η (hBK hη)
        have hneg : -A ≤ -s.potential η := by
          have := (abs_le.mp hbound).2
          linarith
        simp only [hfdef, hone, one_mul]
        exact Real.exp_le_exp.mpr hneg
      · rw [Set.indicator_of_notMem hη]
        exact zero_le
    refine lt_of_lt_of_le ?_ (lintegral_mono hge)
    rw [lintegral_indicator_const hBmeas]
    have hvol : 0 < volume B := by
      rw [volume_pi, hBdef, Measure.pi_pi]
      exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun b _ =>
        (Metric.measure_ball_pos _ _ (by positivity)).ne')
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hvol.ne'
  have hmass : settingMass s = ∫⁻ η, ENNReal.ofReal (f η) := rfl
  refine ⟨by rw [hmass]; exact hpos, by rw [hmass]; exact hlt_top.ne, ?_⟩
  rw [hmass, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf_nonneg) hf_meas]
theorem coarseFactor_nonneg (hexp : R.HasExpansions) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn)
    (V : TorusField n) (q : CoarseState R n) (X : Finset (TorusSite n)) : 0 ≤ coarseFactor V q X := by
  classical
  have hmark : ∀ (W : TorusField (n * R.params.side)) (b : TorusBond (n * R.params.side)),
      0 ≤ bondMark R V W b ∧ bondMark R V W b ≤ 1 :=
    fun W b => ⟨cutoffFactor_nonneg _ _ _, cutoffFactor_le_one hρ hp (norm_nonneg _)⟩
  have hind : 0 ≤ admissibilityIndicator V q X := by
    unfold admissibilityIndicator
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  have hcluster : 0 ≤ clusterFactorProduct q X :=
    Finset.prod_nonneg fun _ _ => hexp.2.factor_nonneg _ hside _ _ _ _
  have hmarks : 0 ≤ markFactorProduct V q X := by
    refine Finset.prod_nonneg fun c _ => ?_
    split_ifs
    · linarith [(hmark (q.restrict X).storedField c).2]
    · exact (hmark _ c).1
  have hbase : 0 ≤ baseFactorProduct q X := by
    refine Finset.prod_nonneg fun y _ => ?_
    split
    · unfold blockBaseWeight
      split_ifs
      · positivity
      · exact le_rfl
    · exact zero_le_one
  unfold coarseFactor
  positivity
theorem coarseStateGasStatement_holds (hC : SettingsUniformlyConvex) (hS : SettingAdmissibleOfHasWeight)
    (hN : GroundWeightAtEmpty) (hP : CaseMassEqGasMass)
    (hA : GasConfigIsAdmissibleSetting) (hW : GasIsActivityBounded) : coarseStateGasStatement := by
  classical
  obtain ⟨rt₁, hrt₁, hconv⟩ := hC
  obtain ⟨rt₂, hrt₂, hweight⟩ := hW
  refine ⟨fun c => min (rt₁ c) (rt₂ c), fun c => lt_min (hrt₁ c) (hrt₂ c), fun T hT hT' => ?_⟩
  obtain ⟨Cc, yc, _, hc⟩ := hconv T hT (hT'.trans (min_le_left _ _))
  obtain ⟨yw, hwt⟩ := hweight T hT (hT'.trans (min_le_right _ _))
  obtain ⟨y₁, h1⟩ := hS T hT
  obtain ⟨y₂, h2⟩ := hN T hT
  obtain ⟨y₃, h3⟩ := hP T hT
  obtain ⟨y₄, h4⟩ := hA T hT
  refine ⟨max (max (max yc yw) y₁) (max y₂ (max y₃ y₄)), fun y hy R hOn hx n _ G hG => ?_⟩
  have hl := hOn.params_eq
  have hρA := hOn.anchorRadius_eq
  have hp := hOn.barrierFn_eq
  have hst := hOn.isStep
  have ey₀ : max (max yc yw) y₁ ≤ y := le_trans (le_max_left _ _) hy
  have ey₀' : max y₂ (max y₃ y₄) ≤ y := le_trans (le_max_right _ _) hy
  have eyc : yc ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ey₀
  have eyw : yw ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ey₀
  have ey₁ : y₁ ≤ y := le_trans (le_max_right _ _) ey₀
  have ey₂ : y₂ ≤ y := le_trans (le_max_left _ _) ey₀'
  have ey₃ : y₃ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ey₀'
  have ey₄ : y₄ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ey₀'
  have hset : G.groundSetting.IsAdmissible := by
    refine h1 y ey₁ R hOn hx n G hG GasFamily.empty ?_ 0 (h2 y ey₂ R hOn hx n G hG)
    exact ⟨fun θ h => by simp [GasFamily.Occupies, GasFamily.empty] at h, fun θ _ h => by
      simp [GasFamily.Occupies, GasFamily.empty] at h⟩
  have hgas : G.familyOf G.allVacant = GasFamily.empty := by
    funext θ
    unfold GasGround.familyOf GasGround.allVacant GasFamily.empty
    by_cases h : G.IsGasSupport θ
    · simp [h]
    · simp [h]
  have hcold : G.coldWeight = (settingMass G.groundSetting).toReal := by
    unfold GasGround.coldWeight GasGround.weight
    rw [hgas]
    exact if_pos (fun i j _ => Or.inl rfl)
  have en : R.params.n₀ = T.n₀ := by rw [hl]; rfl
  have eσ : R.params.threshold = T.threshold := by rw [hl]; rfl
  have hn₀ : T.n₀ ≤ n := by
    rcases hG with h | h
    · rw [← en]
      exact h.n₀_le
    · rw [← en]
      exact le_trans (Nat.le_mul_of_pos_left _ (NeZero.pos _)) h.isBlockSide.2
  have hρ : 0 < R.ballRadius := by
    unfold StepSetup.ballRadius
    rw [eσ]
    have := hT.σ_pos
    positivity
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    have h := hT.cut
    have e : R.ballRadius = T.ballRadius := by
      unfold StepSetup.ballRadius ParameterAssignment.ballRadius
      rw [eσ]
    rw [e, hp]
    exact h
  have hmass : ∀ s : ChartSetting R n, s.IsAdmissible →
      0 < settingMass s ∧ settingMass s ≠ ⊤ ∧
        (settingMass s).toReal = ∫ η, s.cutoffProduct η * Real.exp (-s.potential η) := by
    intro s hs
    obtain ⟨U, _, hUK, hUc⟩ := (hc y eyc R hOn n hn₀ s hs).1.contDiffOn_nhds
    exact settingMass_pos_finite_integral s hρ hcut hUK hUc.continuousOn
  obtain ⟨hm1, hm2, hm3⟩ := hmass G.groundSetting hset
  have hpos : 0 < G.coldWeight := by
    rw [hcold]
    exact ENNReal.toReal_pos hm1.ne' hm2
  set F : CaseFunctional R n := fun _ _ _ _ _ => 1 with hF
  have hFw : IsCaseFunctional F := ⟨fun _ _ _ => measurable_const, fun _ _ _ _ _ _ _ _ _ _ => rfl⟩
  have hint : G.gasIntegrand F = G.pairConstraint.weightDensity G.weight := by
    funext σ
    unfold GasGround.gasIntegrand PairConstraint.weightDensity
    by_cases ha : G.pairConstraint.IsAdmissible σ
    · rw [if_pos ha, if_pos ha]
      have hs := h4 y ey₄ R hOn hx n G hG σ ha
      obtain ⟨_, hf, _⟩ := hmass _ hs
      unfold GasGround.weight
      rw [if_pos ha, ENNReal.ofReal_toReal hf]
      unfold ChartSetting.settingIntegral settingMass
      simp [hF]
    · rw [if_neg ha, if_neg ha]
  have hmeas : Measurable (G.gasIntegrand F) := by
    rw [hint]
    exact (hwt y eyw R hOn hx n G hG fun j => j.1.Touches ∅).measurable_weightDensity
  have hsum0 := h3 y ey₃ R hOn hx n G hG ∅ F hFw hmeas
  have hgm : G.gasMass ∅ F = G.partitionFunction ∅ := by
    unfold GasGround.gasMass GasGround.partitionFunction
    rw [hint]
  have hcm : G.caseMass ∅ F = coarseStateMass R G.cut G.coarse G.state := by
    unfold GasGround.caseMass coarseStateMass
    refine Finset.sum_congr rfl fun bad _ => Finset.sum_congr rfl fun Yt _ => ?_
    have hoff : G.CaseAvoids ∅ bad Yt := ⟨fun _ _ _ => by simp, fun _ _ _ => by simp⟩
    rw [if_pos hoff]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold GasGround.caseIntegral GasGround.caseIntegrand
    simp [hF]
  have hsum : coarseStateMass R G.cut G.coarse G.state =
      ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
        ENNReal.ofReal (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) *
          G.partitionFunction ∅ := by
    rw [← hcm, hsum0, hgm]
  have hside : IsBlockTorusSide R.params (n * R.params.side) := by
    refine ⟨Dvd.intro_left n rfl, ?_⟩
    rw [en, Nat.mul_comm n]
    have : R.params.side * T.n₀ ≤ R.params.side * n := Nat.mul_le_mul_left _ hn₀
    exact this
  have hΦ : 0 ≤ ∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X :=
    Finset.prod_nonneg fun X _ => coarseFactor_nonneg hst.1 hside hρ hcut _ _ _
  have hD : 0 ≤ R.functional (n * R.params.side) (trivialField (n * R.params.side)) := by
    apply le_of_lt
    apply hst.1.1.positive _
      (le_trans (by rw [en]; exact hn₀) (Nat.le_mul_of_pos_right _ (NeZero.pos _)))
    intro x μ ν _
    have hσ : 0 < R.params.threshold := by rw [eσ]; exact hT.σ_pos
    simp [curvature, holonomy, trivialField, hσ]
  refine ⟨hset, hpos, hcold.trans hm3, hsum, ?_⟩
  unfold coarseStateWeight GasGround.xi
  rw [hsum, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hD,
    ENNReal.toReal_ofReal hΦ]
  field_simp
end CoarseGas
end YangMills.Construction
end
