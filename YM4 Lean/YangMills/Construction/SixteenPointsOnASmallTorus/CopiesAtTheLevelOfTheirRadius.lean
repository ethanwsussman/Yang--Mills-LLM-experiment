import YangMills.Construction.SixteenPointsOnASmallTorus.LevelsOfACopyDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def ForAllResponseParameters
    (P : RenormalizationStepParameters.ParameterAssignment → WeightedResponses.ResponseParameters → ℝ → Prop) : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : RenormalizationStepParameters.ChainParameters → ℝ) (C₀ : ℝ), (∀ c, 0 < rt₀ c) ∧
    ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.coupling = a → T.side = L → T.Admissible → T.ColdStepHolds →
      T.HoldsFrom WeightedResponses.ColdRegimeEstimatesAt →
      T.rt ≤ rt₀ T.toChainParameters → C₀ ≤ T.derivBound →
      ∀ Kr : WeightedResponses.ResponseParameters, (∀ y, Kr.Admissible (T.stepParameters y)) →
        ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → StepReturn.ExpansionReturnsAt (T.stepParameters y) →
          (∀ β : ℝ, y ≤ β → TorusLumps.HasExpansion (T.stepParameters y) 0 β (TorusLumps.wilsonWeight β)) →
          P T Kr y
def reflectedMeanAtRadiusLevelStatement : Prop :=
  ForAllResponseParameters fun T Kr y => ∀ Ξ : ℝ, y + 2 * T.B ≤ Ξ → ∃ C : ℝ, 0 ≤ C ∧
    ForAllInitialStages T y fun β hL z₀ => ∀ (K κ s : ℕ) (ρ H : ℝ) (Λ : NNReal)
      (h : TestFunctions.EuclideanFourSpace → ℝ),
      IsAdmissibleFlow (T.stepParameters y) Ξ β K → 2 ≤ κ → 0 < ρ → ρ ≤ cellLength T.side K κ / 4 →
      IsLocalizedSource (cellLength T.side K κ) ρ H Λ h → radiusLevel (T.stepParameters y) β K ρ = some s →
      ResponseInTheExpansion.StagesOnFlowUpTo T Kr y β hL z₀ K → ∀ R : ℝ, 0 ≤ R →
      ResponseInTheExpansion.stateLIntegral (ResponseInTheExpansion.flowStages T y β hL z₀ s).1.toStepSetup
          (twoCellSide T.side κ s)
          (prodMeanSiteScores T y β hL z₀ K κ s (twoCellSide T.side κ s) h) ≤
        ENNReal.ofReal R * ResponseInTheExpansion.stateLIntegral
          (ResponseInTheExpansion.flowStages T y β hL z₀ s).1.toStepSetup (twoCellSide T.side κ s) (fun _ _ _ => 1) →
      ∀ z : TorusFields.TorusSite (2 * T.side ^ κ),
        reflectedProductMean β (levelSpacing T.side K 0) (T.side ^ κ) 2 z h
            (centring (T.stepParameters y) β (fun j => (ResponseInTheExpansion.flowStages T y β hL z₀ j).2.coeff) K κ ρ h) ≤
          (C * (1 + rangeAtLevel (T.stepParameters y) β s ^ 4 + ρ ^ 4) * sourceNorm ρ H Λ) ^ 16 * R
end YangMills.Construction.SmallTorusCopies
end
