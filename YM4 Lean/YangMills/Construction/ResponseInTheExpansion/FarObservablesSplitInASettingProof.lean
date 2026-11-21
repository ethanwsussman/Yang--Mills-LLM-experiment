import YangMills.Construction.ResponseInTheExpansion.FarObservablesSplitInASetting
import YangMills.Construction.ResponseInTheExpansion.FarVariablesOfSizeBelowSplitInASetting
import YangMills.Construction.ResponseInTheExpansion.MeanOfASupportOfSizeBelowGivenTheFieldOne
import YangMills.Construction.TransfersOffTheWalk.OneStepOfSeveralResponsesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
section Balls
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
private theorem weightedMean_congr_inBalls (s : StepSettings.ChartSetting R n) {F F' : StepSettings.FreeCoords s.free → ℝ}
    (h : ∀ η, s.InBalls η → F η = F' η) :
    StepSettings.weightedMean (WeightedResponses.chartDensity s) F =
      StepSettings.weightedMean (WeightedResponses.chartDensity s) F' := by apply _root_.YangMills.SharedProofs.p21928 <;> assumption
end Balls
theorem separatedProductInChart (hFar : ResponseInTheExpansion.farWeightVariablesFactorize)
    (hMean : ResponseInTheExpansion.supportResponseMeanBound) (hVar : FreeEnergies.supportResponseLocalityStatement) :
    ResponseInTheExpansion.separatedProductInChartStatement := by
  classical
  obtain ⟨r₁, p₁, H₁⟩ := hFar
  obtain ⟨r₂, p₂, H₂⟩ := hMean
  obtain ⟨r₃, p₃, H₃⟩ := hVar
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (r₃ c)), fun c => lt_min (p₁ c) (lt_min (p₂ c) (p₃ c)), ?_⟩
  intro T hT hle K
  simp only [le_min_iff] at hle
  obtain ⟨l₁, l₂, l₃⟩ := hle
  obtain ⟨y₁, C, hC, h₁⟩ := H₁ T hT l₁ K
  obtain ⟨y₂, h₂⟩ := H₂ T hT l₂ K
  obtain ⟨y₃, h₃⟩ := H₃ T hT l₃ K
  refine ⟨max y₁ (max y₂ y₃), C, hC, fun y hy R A hK htab => ?_⟩
  simp only [max_le_iff] at hy
  obtain ⟨e₁, e₂, e₃⟩ := hy
  intro n _ s hn hset bad ι I f D hI hF
  set v : ι → ℝ := fun i => WeightedResponses.caseMean R ∅ (TorusFields.trivialField n) (StepGas.emptyCoarseState R)
    (ResponseInTheExpansion.supportResponseSum A (TorusFields.trivialField n) (f i)) with hvdef
  have hv : ∀ i ∈ I, |v i| ≤ (K.C₀ + 1 + 16 * R.params.coupling) *
      ((ResponseInTheExpansion.weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).card : ℝ) := by
    intro i hi
    have := h₂ y e₂ R A hK htab n hn (f i) (hF.weightNorm_le i hi) (hF.nonempty i hi)
    rw [hK] at this
    exact this
  have hsplit := h₁ y e₁ R n s hn hset bad ι I (fun _ => A) f v D (fun _ _ => hK) (fun _ _ => htab) hI hF.weightNorm_le
    hF.nonempty hF.range_le hF.eight_lt hF.separated hv
  have hball := (h₃ y e₃ R A hK htab n s hn hset).1
  have eX : ∀ (i : ι) (η : StepSettings.FreeCoords s.free), s.InBalls η →
      FreeEnergies.liveCaseFunction (ResponseInTheExpansion.centeredSupportResponse A s.coarse (f i)) (s.field η) s.support
          s.labelling bad s.bases =
        ResponseInTheExpansion.supportResponseSum A s.coarse (f i) (s.field η) s.support s.labelling bad s.bases - v i := by
    intro i η hη
    unfold FreeEnergies.liveCaseFunction
    rw [if_pos (hball η hη).1]
    rfl
  have eP : FreeEnergies.settingMean s bad (fun W Yt ωt bad b =>
        ∏ i ∈ I, FreeEnergies.liveCaseFunction (ResponseInTheExpansion.centeredSupportResponse A s.coarse (f i)) W Yt ωt bad b) =
      StepSettings.weightedMean (WeightedResponses.chartDensity s) (fun η =>
        ∏ i ∈ I, (ResponseInTheExpansion.supportResponseSum A s.coarse (f i) (s.field η) s.support s.labelling bad s.bases - v i)) :=
    weightedMean_congr_inBalls s fun η hη => Finset.prod_congr rfl fun i _ => eX i η hη
  have eM : ∀ i ∈ I, FreeEnergies.settingMean s bad
        (FreeEnergies.liveCaseFunction (ResponseInTheExpansion.centeredSupportResponse A s.coarse (f i))) =
      StepSettings.weightedMean (WeightedResponses.chartDensity s) (fun η =>
        ResponseInTheExpansion.supportResponseSum A s.coarse (f i) (s.field η) s.support s.labelling bad s.bases - v i) :=
    fun i _ => weightedMean_congr_inBalls s fun η hη => eX i η hη
  rw [eP, Finset.prod_congr rfl eM]
  refine hsplit.trans (le_of_eq ?_)
  have eB : ∀ i ∈ I, 4 * (K.C₀ * ((ResponseInTheExpansion.weightSupportSites R.params.side R.depth (n * R.params.side) (f i)).card : ℝ)) *
      ResponseInTheExpansion.meanSiteScore A.score
        (ResponseInTheExpansion.weightSupportSites R.params.side R.depth (n * R.params.side) (f i)) s.support s.labelling =
      ResponseInTheExpansion.lowerMajorant A (f i) s.support s.labelling := by
    intro i _
    unfold ResponseInTheExpansion.lowerMajorant FreeEnergies.lowerSizeConst
    rw [hK]
    rfl
  rw [Finset.prod_congr rfl eB]
  rfl
end YangMills.Construction.ResponseInTheExpansion
end
