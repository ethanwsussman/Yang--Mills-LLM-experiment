import YangMills.Construction.SummableBoundsOfTheFlow.NearPairingOfTheBox
import YangMills.Construction.SummableBoundsOfTheFlow.PartsOfALawOfTheFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace TorusComparison
def matchedCellPartsGradientBoundAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x s : ℝ) (l : StepLaw) (F F' : BlockFrame) (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (q : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F')))
    (h : Fin 4 → ℤ),
    T.coupling ≤ x → 0 ≤ s → s ≤ 1 →
    l.IsAdmissible T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio →
    IsCubicTopTorus T.L t T.n₀ F → IsCubicTopTorus T.L t T.n₀ F' →
    IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q → IsShortPairing Y Y' q j j' →
    T.blockIndex ≤ q → (∀ i, 8 * |h i| ≤ q) →
    ∀ ξ ∈ openPolyball ι T.ballRadius, ∀ k : ι,
      bondGradNorm (fun ζ =>
        TorusFreezing.stepLawCellPart l s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) V'
          (Y' + siteOfCoords F'.top h) (pushforwardField j' ζ) -
        TorusFreezing.stepLawCellPart l s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) V
          (Y + siteOfCoords F.top h) (pushforwardField j ζ)) k ξ ≤
      T.Cs * l.amplitude T.energyRatio * Real.exp (-(4 * T.κ * q)) *
        (x * Real.sqrt (weightedSqNormNear T.κ (fun k => TorusFreezing.bondCell (j k))
          TorusFreezing.realCellDist (Y + siteOfCoords F.top h) ξ) + 1) *
        Real.exp (-(2 * T.κ * TorusFreezing.realCellDist (TorusFreezing.bondCell (j k))
          (Y + siteOfCoords F.top h)))
def matchedCellPartsGradientBound : Prop := EventuallyInParameters matchedCellPartsGradientBoundAt
end TorusComparison
end YangMills.Construction
end
