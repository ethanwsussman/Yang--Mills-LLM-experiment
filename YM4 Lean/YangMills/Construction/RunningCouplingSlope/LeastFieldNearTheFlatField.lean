import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChain
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames TorusFields
def MinimizerNearTrivialField : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ (t n : ℕ) (ρ : ℝ), 2 * L ≤ n → 0 < ρ → ρ ≤ 1 →
    Tendsto (SlopeCoefficient.minimizerOnFinerTorus a ρ L t n) (𝓝 (trivialField n)) (𝓝 (trivialField (n * L))) ∧
    ∀ᶠ V in 𝓝 (trivialField n),
      (∃ w, IsMinimizingChart a (finiteCells (torusFrame L t n))
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ w) ∧
      (∀ W' : (torusFrame L t n).GaugeField (torusFrame L t n).depth,
        (∀ W'', blockEnergy a (finiteCells (torusFrame L t n)) (torusFrame L t n).depth W'
            (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ≤
          blockEnergy a (finiteCells (torusFrame L t n)) (torusFrame L t n).depth W''
            (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)) →
        ∃ γ : (torusFrame L t n).Site (torusFrame L t n).depth → UnitQuaternion,
          (∀ z : (torusFrame L t n).Cell, γ (cellCentre _ z) = 1) ∧
          W' = BlockAverages.gaugeTransform γ (fieldAboveFrame (F := torusFrame L t n) true a ρ 0
            (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) 0)) ∧
      (ReferenceDensity.chartedHessian (F := torusFrame L t n) a ρ
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) 0).PosDef ∧
      IsBondAnalyticAt (minimalAction a (finiteCells (torusFrame L t n)) (torusFrame L t n).top)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ∧
      ∀ b ∈ chordBonds (finiteCells (torusFrame L t n)),
        IsBondAnalyticAt (minimizingBondCoordinate a ρ (finiteCells (torusFrame L t n)) b)
          (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)
end RunningCouplingSlope
end YangMills.Construction
end
