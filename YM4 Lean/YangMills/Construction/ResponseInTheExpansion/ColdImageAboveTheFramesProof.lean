import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfFourDensitiesProofForm
import YangMills.Construction.ClusterExpansionOfAStep.ColdGroundIsTheColdSettingProof
import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingIsASettingProof
import YangMills.Construction.ResponseInTheExpansion.ColdImageAboveTheFrames
import YangMills.Construction.ResponseInTheExpansion.ImageAtAColdTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
namespace TorusTransfer
open TorusFields TorusLumps StepSettings StepGas BlockOffsets StepCosts
section Flat
variable {ℓ : TorusLumps.StepParameters}
theorem trivialField_isCold (hσ : 0 < ℓ.threshold) (n : ℕ) : IsCold ℓ.threshold (trivialField n) := by apply _root_.YangMills.Construction.TorusLumps.DensityExpansion.trivialField_isCold <;> assumption
end Flat
section Empty
variable {R : StepSetup} {n : ℕ}
variable [NeZero n]
theorem isHullState_empty (W : TorusField (n * R.params.side)) (hW : IsCold R.params.threshold W)
    (r : ℕ) : IsHullState R.params r W ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdChart.isHullState_empty <;> assumption
end Empty
section Ground
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem field_with_fine_field_zero (s : ChartSetting R n) (hodd : Odd R.params.side) (hn : 2 ≤ n)
    (hf : s.free ⊆ chartBonds R.params.side n) (η : FreeCoords s.free) :
    ({ s with fine := s.field 0 } : ChartSetting R n).field η = s.field η := by apply _root_.YangMills.Construction.ColdCaseGround.field_fine_field_zero <;> assumption
theorem settingWithFamily_coldCaseGround (V : TorusField n) :
    (coldCaseGround R V).settingWithFamily GasFamily.empty = coldChartSetting R V := by apply _root_.YangMills.Construction.ColdCaseGround.settingWithFamily_empty_coldCaseGround <;> assumption
omit [NeZero n] in
theorem with_fine_field_zero_congr {s s' : ChartSetting R n} (h : s = s') :
    ({ s with fine := s.field 0 } : ChartSetting R n) = ({ s' with fine := s'.field 0 } : ChartSetting R n) := by apply _root_.YangMills.Construction.ColdCaseGround.fine_field_zero_congr <;> assumption
end Ground
end TorusTransfer
namespace ResponseInTheExpansion
namespace ColdSettingMeans
open TorusFields TorusLumps StepSettings StepGas StepCosts WeightedResponses TorusTransfer
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem chartDensity_with_fine_of_field_eq (s : ChartSetting R n) (b : TorusField (n * R.params.side))
    (h : ∀ η, ({ s with fine := b } : ChartSetting R n).field η = s.field η) :
    chartDensity ({ s with fine := b } : ChartSetting R n) = chartDensity s := by
  funext η
  have hp : ({ s with fine := b } : ChartSetting R n).potential η = s.potential η := by
    unfold ChartSetting.potential
    rw [h]
    rfl
  unfold chartDensity
  rw [hp]
  rfl
theorem groundSetting_coldCaseGround (V : TorusField n) :
    (coldCaseGround R V).groundSetting =
      ({ coldChartSetting R V with fine := (coldChartSetting R V).field 0 } : ChartSetting R n) :=
  with_fine_field_zero_congr (s := (coldCaseGround R V).settingWithFamily GasFamily.empty)
    (s' := coldChartSetting R V) (settingWithFamily_coldCaseGround V)
omit [NeZero n] in
theorem cutoffProduct_eq_zero (s : ChartSetting R n) (η : FreeCoords s.free)
    (h : ¬ ∀ b, coordNorm (η b) < R.ballRadius) : s.cutoffProduct η = 0 := by
  push Not at h
  obtain ⟨b, hb⟩ := h
  unfold ChartSetting.cutoffProduct
  refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
  unfold ColdStepAtMirrorFrames.cutoffFactor
  rw [if_neg (not_lt.2 hb)]
theorem weightedMean_congr_on_balls (s : ChartSetting R n) {G G' : FreeCoords s.free → ℝ}
    (h : ∀ η, (∀ b, coordNorm (η b) < R.ballRadius) → G η = G' η) :
    weightedMean (chartDensity s) G = weightedMean (chartDensity s) G' := by
  unfold weightedMean
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  by_cases hη : ∀ b, coordNorm (η b) < R.ballRadius
  · show G η * _ = G' η * _
    rw [h η hη]
  · show G η * _ = G' η * _
    unfold chartDensity
    rw [cutoffProduct_eq_zero s η hη]
    simp
end ColdSettingMeans
open TorusFields TorusLumps StepSettings StepGas StepCosts WeightedResponses TorusTransfer
  ColdSettingMeans in
theorem coldStepAboveFrames_holds (himage : coldImageDecompositionStatement)
    (hmean : coldSettingMeanEqStepMean) (hcold : StepSettings.ColdChartSettingIsCold) :
    coldStepAboveFramesStatement := by
  classical
  obtain ⟨rt₀, hr, g⟩ := himage
  refine ⟨rt₀, hr, fun T hT hrt K => ?_⟩
  obtain ⟨y₀, g⟩ := g T hT hrt K
  by_cases hC : T.ColdStepHolds
  swap
  · exact ⟨0, fun y _ R A _ _ h => absurd h hC⟩
  obtain ⟨y₁, hm⟩ := hmean T hT hC
  obtain ⟨y₂, hc⟩ := hcold T hT
  refine ⟨max y₀ (max y₁ (max y₂ T.floorMin)), fun y hy R A hK hA _ n _ hn Y V hV h => ?_⟩
  have h0 : y₀ ≤ y := le_trans (le_max_left _ _) hy
  have h1 : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have h2 : y₂ ≤ y :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hy
  have h3 : T.floorMin ≤ y :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hy
  rw [g y h0 R A hK hA n hn Y V hV h]
  have hOn := hA.onFamily
  have hσ : R.params.threshold = T.threshold := by rw [hOn.params_eq]; rfl
  have hn' : T.n₀ ≤ n := by
    have : R.params.n₀ = T.n₀ := by rw [hOn.params_eq]; rfl
    omega
  have hσ0 : 0 < T.threshold := hT.σ_pos
  have hV' : IsCold (9 / 8 * T.threshold) V := fun x μ ν hμ => by
    have := hV x μ ν hμ
    rw [hσ] at this
    linarith
  have hodd : Odd R.params.side := by
    rw [hOn.params_eq]
    exact hT.L_odd
  have hn2 : 2 ≤ n := by
    have := hT.n₀_ge
    omega
  have hL : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hnL : n ≤ n * R.params.side := Nat.le_mul_of_pos_right n hL
  have hsame : ∀ η, ({ coldChartSetting R V with fine := (coldChartSetting R V).field 0 } :
      ChartSetting R n).field η = (coldChartSetting R V).field η := fun η =>
    field_with_fine_field_zero (coldChartSetting R V) hodd hn2 (Finset.Subset.refl _) η
  have hden := chartDensity_with_fine_of_field_eq (coldChartSetting R V)
    ((coldChartSetting R V).field 0) hsame
  have hflat : 0 < R.functional (n * R.params.side) (trivialField (n * R.params.side)) := by
    have hn0 : R.params.n₀ ≤ n * R.params.side := by omega
    exact hOn.isStep.1.1.positive _ hn0 _ (trivialField_isCold (by rw [hσ]; exact hσ0) _)
  have hlive : ∀ (W : TorusField (n * R.params.side)), IsCold R.params.threshold W →
      ∀ ω : (∅ : Finset (TorusSite (n * R.params.side))) → R.labels.Ω,
      IsLiveState R.params R.coupling R.labelWeight W ∅ ω := by
    intro W hW ω
    have hH : IsHullState R.params (clusterRange R.coupling) W ∅ := isHullState_empty W hW _
    refine ⟨hH, ?_⟩
    rw [hOn.isStep.1.2.form _ ⟨Dvd.intro_left n rfl, by rw [mul_comm n]; exact Nat.mul_le_mul_left _ hn⟩
      W ∅ ω hH]
    have : chainComponents (clusterRange R.coupling) (∅ : Finset (TorusSite (n * R.params.side))) = ∅ := by
      simp [chainComponents]
    rw [this, Finset.prod_empty, mul_one]
    exact mul_pos hflat (Real.exp_pos _)
  have e1 : ∀ y, chartResponse A (coldCaseGround R V).groundSetting y h =
      coldExpectationAbove R V (fun W => centeredResponse A.cold (n * R.params.side) y W h) := by
    intro y'
    have hmn := hm y h1 R hOn n hn' V hV' (fun W => centeredResponse A.cold (n * R.params.side) y' W h)
    unfold chartResponse
    rw [groundSetting_coldCaseGround, hden]
    refine Eq.trans ?_ hmn
    simp only [hsame]
    refine weightedMean_congr_on_balls (coldChartSetting R V) fun η hη => ?_
    have hc' : IsCold R.params.threshold ((coldChartSetting R V).field η) := by
      intro x μ ν hμ
      have := hc y h2 R hOn n hn' V hV' η (fun b => (hη b).le) x μ ν hμ
      rw [hσ]
      linarith
    unfold centeredHullResponse centeredResponse
    exact congrArg (fun z => z - A.cold (n * R.params.side) y' (trivialField (n * R.params.side)) h)
      (hA.admissible.bounds.empty _ ⟨Dvd.intro_left n rfl, by rw [mul_comm n]; exact Nat.mul_le_mul_left _ hn⟩
        y' _ (coldChartSetting R V).labelling (hlive _ hc' _) h)
  have e2 : ∀ c, chartBondScore (coldCaseGround R V).groundSetting c =
      coldExpectationAbove R V (fun W => bondScore R.params R.coupling W V (coldChartSetting R V).bases c) := by
    intro c
    have hmn := hm y h1 R hOn n hn' V hV'
      (fun W => bondScore R.params R.coupling W V (coldChartSetting R V).bases c)
    unfold chartBondScore
    rw [groundSetting_coldCaseGround, hden]
    refine Eq.trans ?_ hmn
    simp only [hsame]
    rfl
  unfold coldImagePart coldTermAbove
  simp only [e1, e2]
end ResponseInTheExpansion
end YangMills.Construction
end
