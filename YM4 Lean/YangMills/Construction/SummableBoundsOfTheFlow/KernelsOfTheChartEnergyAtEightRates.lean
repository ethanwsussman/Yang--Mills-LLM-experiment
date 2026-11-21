import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.Estimates
def ChartEnergyKernelDecay : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ Ck : ℕ → ℝ, (∀ k, 0 < Ck k) ∧
      ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
        IsBlockTorus L F →
        IsAdmissibleChartPoint L c.σA w V → ∀ (k : ℕ) (q : Fin k → ChartDirection F), 2 ≤ k →
          (∀ l, ‖directionVector (q l)‖ = 1) →
          |chartMixedDeriv a w V q| ≤ Ck k * Real.exp (-(8 * c.δ₁ * directionDiameter q))
end YangMills.Construction.Estimates
end
