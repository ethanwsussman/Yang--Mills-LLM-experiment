import YangMills.Construction.ColdStepAtMirrorFrames.ChartPointsNearABox
import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
def ChartSlopeBoundNearBall : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ C : ℝ, 0 < C ∧
      ∀ (F F' : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
        (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
        (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) (θ : ℝ), 1 ≤ r →
        IsBlockTorus L F → IsBlockTorus L F' → F'.depth = F.depth → 0 ≤ θ →
        (∀ Δ : StepVariable (finiteCells F), (∀ b, ‖Δ b‖ ≤ θ) →
          IsAdmissibleChartPoint L c.s₀ (shiftCoordinates w Δ) V) →
        IsAdmissibleChartPoint L c.s₀ w' V' →
        AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r → CoordinatesCloseOnBall L Y Y' r θ w w' →
        ∀ (h o : Fin 4 → ℤ) (i : Fin 4) (e : imaginaryQuaternions), IsFineBondWithinRadius Y (r / 2) h o i →
          ‖e‖ = 1 →
          |chartedSlope a w V (fineBondAt Y h o i) e - chartedSlope a w' V' (fineBondAt Y' h o i) e| ≤
            C * (θ + Real.exp (-(c.δ₂ * ((L : ℝ) * ((r : ℝ) / 2) - 2 * L - 1))))
end YangMills.Construction.ColdStepAtMirrorFrames
end
