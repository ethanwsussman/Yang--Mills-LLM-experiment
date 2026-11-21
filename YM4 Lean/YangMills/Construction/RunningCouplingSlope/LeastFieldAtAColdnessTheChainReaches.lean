import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import YangMills.Construction.RunningCouplingSlope.ColdnessTheChainReaches
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames ColdChain
def MinimizerAtReachableColdness : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∀ (F : BlockFrame) (s : ℝ) (V : F.GaugeField F.top), IsBlockTorus L F → IsReachableColdness c L s →
      IsSmallCurvature s V →
      IsMinimizingChart a (finiteCells F) V c.ρA (minimizingCoordinates a (finiteCells F) V c.ρA) ∧
      (∀ b ∈ chordBonds (finiteCells F), ‖stepFrame true a c.ρA 0 b V‖ ≤ c.N 0 * s) ∧
      IsSmallCurvature (s / 8) (torusMinimizingField a c.ρA V) ∧
      IsAdmissibleChartPoint L c.σA (fun x i => stepFrame true a c.ρA 0 (x, i) V) V ∧
      ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame true a c.ρA 0 b) V ∧
        ∀ (k : ℕ) (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X →
          ‖bondDeriv (stepFrame true a c.ρA 0 b) V e X‖ ≤
            c.N k * Real.exp (-(c.δ₁ * bondListDistance (enclosingCell b.1) e))
end YangMills.Construction.RunningCouplingSlope
end
