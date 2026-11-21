import YangMills.Construction.ResponseInTheExpansion.LevelsOfAFlow
import YangMills.Construction.ResponseInTheExpansion.SupportsAlongTheLevels
import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenPointsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
open ClusterExpansionOfAStep RenormalizationStepParameters WeightedResponses ResponseInTheExpansion TestFunctions
def ForAllLargeFloors (P : ParameterAssignment → ResponseParameters → ℝ → Prop) : Prop :=
  ∃ rtMax : ChainParameters → ℝ, (∀ c, 0 < rtMax c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rtMax T.toChainParameters →
    ∀ R : ResponseParameters, ∃ yMin : ℝ, ∀ y : ℝ, yMin ≤ y → P T R y
def ForAllInitialStages (T : ParameterAssignment) (y : ℝ)
    (P : (β : ℝ) → (∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup) → StageWithResponse (T.stepParameters y) → Prop) : Prop :=
  ∀ (β : ℝ) (hLab : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup) (z₀ : StageWithResponse (T.stepParameters y)), IsInitialStage T y β z₀ → P β hLab z₀
def reflectedWeightsAtStage (T : ParameterAssignment) (y β : ℝ) (hLab : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup) (z₀ : StageWithResponse (T.stepParameters y)) (K κ s n : ℕ)
    (h : EuclideanFourSpace → ℝ) : (Fin 4 → Fin 2) → StageWeight hLab T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n :=
  fun k => reflectedWeight (levelSpacing (T.stepParameters y).side K 0) ((T.stepParameters y).side ^ κ) (fun μ => (k μ : ℕ)) h
def prodMeanSiteScores (T : ParameterAssignment) (y β : ℝ) (hLab : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup) (z₀ : StageWithResponse (T.stepParameters y)) (K κ s n : ℕ)
    [NeZero n] (h : EuclideanFourSpace → ℝ) : StateFunction (flowStages T y β hLab z₀ s).1.toStepSetup n :=
  fun _ Y ω => ∏ k : Fin 4 → Fin 2, meanSiteScore (flowStages T y β hLab z₀ s).2.score
    (weightSupportSites (T.stepParameters y).side (flowStages T y β hLab z₀ s).1.depth n (reflectedWeightsAtStage T y β hLab z₀ K κ s n h k)) Y ω
def radiusInStageUnits (L K : ℕ) (ρ : ℝ) (u : ℕ) : ℕ := ⌊ρ / levelSpacing L K (u + 1)⌋₊
end YangMills.Construction.SmallTorusCopies
end
