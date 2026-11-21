import YangMills.Construction.ResponseInTheExpansion.CasesAtAColdTop
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages TorusFields StepSettings StepGas WeightedResponses
def GasShiftsAreColdExpectations : Prop :=
  HoldsAtEveryStep fun _ R A => R.IsSymmetricWeight → ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n →
    ∀ V : TorusField n, IsCold (9 / 8 * R.params.threshold) V →
    (∀ Yt b, Integrable (coldIntegrand R V (fun _ _ _ => 1) Yt b) (fieldLabelMeasure R n Yt)) ∧
    0 < coldWeightedIntegral R V (fun _ _ _ => 1) ∧
    (∀ (y : TorusSite (n * R.params.side)) (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))),
      (∀ Yt b, Integrable (coldIntegrand R V (fun Yt _ p => liveCenteredResponse A y h Yt p) Yt b)
        (fieldLabelMeasure R n Yt)) ∧
      coldWeightedIntegral R V (fun Yt _ p => |liveCenteredResponse A y h Yt p|) ≤
        (A.responseParams.C₀ + 1) * weightNorm R.params.side R.depth h *
          coldWeightedIntegral R V (fun _ _ _ => 1) ∧
      gasResponseShift A (coldCaseGround R V) y h =
        coldExpectation R V (fun Yt _ p => liveCenteredResponse A y h Yt p) -
          fullyMarkedExpectation R V (fun W => liveCenteredResponse A y h ∅ (W, emptyLabeling R))) ∧
    ∀ c : TorusBond n,
      (∀ Yt b, Integrable (coldIntegrand R V (fun _ b p => bondScore R.params R.coupling p.1 V b c) Yt b)
        (fieldLabelMeasure R n Yt)) ∧
      gasBondScoreShift (coldCaseGround R V) c =
        coldExpectation R V (fun _ b p => bondScore R.params R.coupling p.1 V b c) -
          fullyMarkedExpectation R V
            (fun W => bondScore R.params R.coupling W V (centreBases R.params.side n) c)
end YangMills.Construction.ResponseInTheExpansion
end
