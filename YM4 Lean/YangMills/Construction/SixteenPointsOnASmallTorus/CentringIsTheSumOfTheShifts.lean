import YangMills.Construction.SixteenPointsOnASmallTorus.LevelsOfACopyDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def centringEqSumShiftsStatement : Prop :=
  ForAllLargeFloors fun T Kr y => ForAllInitialStages T y fun β hL z₀ => ∀ s : ℕ,
    ResponseInTheExpansion.StagesOnFlowUpTo T Kr y β hL z₀ s →
    (∀ coeff : ℕ → ℝ, ResponseInTheExpansion.IsChainResponseCoeff (T.stepParameters y) Kr β s coeff → ∀ t ≤ s,
      coeff t = (ResponseInTheExpansion.flowStages T y β hL z₀ t).2.coeff) ∧
    ∀ (n : ℕ) [NeZero n] (w : (m : ℕ) → WeightedResponses.PlaquetteWeight m),
      TorusLumps.IsBlockTorusSide (T.stepParameters y) n →
      meanAtTrivial (T.stepParameters y) β (fun j => (ResponseInTheExpansion.flowStages T y β hL z₀ j).2.coeff) s n (w _) =
        ResponseInTheExpansion.accumulatedShift hL T.lam (ResponseInTheExpansion.couplingsAlongFlow (T.stepParameters y) β) z₀ s n (w _)
end YangMills.Construction.SmallTorusCopies
end
