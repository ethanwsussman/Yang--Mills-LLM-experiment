import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace SummableBoundsOfTheFlow
def ChartedSlopeKernelBound : Prop :=
  ∀ (a : ℝ) (L : ℕ) (p : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → p.Admissible a L →
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : BlockFrame) (w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
        IsBlockTorus L F →
        (∀ u : F.Site F.depth → Fin 4 → imaginaryQuaternions,
          (∀ z i, ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ u z i = w z i + θ • (w' z i - w z i)) →
          IsAdmissibleChartPoint L p.σA u V) →
        (∀ b, b ∉ chordBonds (finiteCells F) → w' b.1 b.2 = w b.1 b.2) →
        ∀ (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions), ‖e‖ = 1 →
          |chartedSlope a w' V b e - chartedSlope a w V b e| ≤
            ∑ b' ∈ chordBonds (finiteCells F),
              C * Real.exp (-(p.δ₁ * cellSupDist (enclosingCell b.1) (enclosingCell b'.1))) *
                ‖w' b'.1 b'.2 - w b'.1 b'.2‖
end SummableBoundsOfTheFlow
end YangMills.Construction
end
