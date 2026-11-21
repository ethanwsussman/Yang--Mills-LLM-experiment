import YangMills.Construction.ColdStepAtMirrorFrames.ChartPointsNearABox
import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheTermsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import YangMills.Construction.ColdStepAtMirrorFrames.PairedVariablesOfTwoTori
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def PairedEnergiesCompare : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ C : ℝ, 0 < C ∧
      ∀ (F F' : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
        (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
        (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (q r₂ : ℕ) (θ ρ₂ : ℝ) (ι : Type)
        [Fintype ι] [DecidableEq ι]
        (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F'))),
        IsBlockTorus L F → IsBlockTorus L F' → F'.depth = F.depth →
        0 ≤ θ → 0 < ρ₂ → 1 ≤ r₂ → r₂ ≤ q → (∀ i, 2 * q + 2 < F.extent i) → (∀ i, 2 * q + 2 < F'.extent i) →
        Function.Injective j → Function.Injective j' → AreOffsetPaired Y Y' q j j' →
        (∀ ξ ∈ openPolyball ι ρ₂, ∀ Δ : StepVariable (finiteCells F), (∀ b, ‖Δ b‖ ≤ θ) →
          IsAdmissibleChartPoint L c.s₀ (shiftCoordinates (shiftCoordinates w (pushforwardField j ξ)) Δ) V) →
        (∀ ξ ∈ openPolyball ι ρ₂, IsAdmissibleChartPoint L c.s₀ (shiftCoordinates w' (pushforwardField j' ξ)) V') →
        AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r₂ → CoordinatesCloseOnBall L Y Y' r₂ θ w w' →
        ContDiffOn ℝ 3 (fun ξ => chartedEnergyAt a w V (pushforwardField j ξ)) (openPolyball ι ρ₂) ∧
        ContDiffOn ℝ 3 (fun ξ => chartedEnergyAt a w' V' (pushforwardField j' ξ)) (openPolyball ι ρ₂) ∧
        (∀ ξ ∈ openPolyball ι ρ₂, ∀ (k : ι) (u : BondVector),
          chartedSlope a (shiftCoordinates w (pushforwardField j ξ)) V (j k).1 (toImaginary u) =
            bondPartialDeriv (fun ξ => chartedEnergyAt a w V (pushforwardField j ξ)) k ξ u ∧
          chartedSlope a (shiftCoordinates w' (pushforwardField j' ξ)) V' (j' k).1 (toImaginary u) =
            bondPartialDeriv (fun ξ => chartedEnergyAt a w' V' (pushforwardField j' ξ)) k ξ u) ∧
        ∀ (ρ₁ hh : ℝ), 0 < hh → 0 < ρ₁ → ρ₁ + hh ≤ ρ₂ → ∀ ξ ∈ openPolyball ι ρ₁,
          ∀ (k l : ι) (h o : Fin 4 → ℤ) (i : Fin 4) (u u' : BondVector),
            IsFineBondWithinRadius Y (r₂ / 2) h o i → (j k).1 = fineBondAt Y h o i →
            (j' k).1 = fineBondAt Y' h o i →
            |secondDerivAlong (fun ξ => chartedEnergyAt a w' V' (pushforwardField j' ξ)) ξ
                (bondVariation k u) (bondVariation l u') -
              secondDerivAlong (fun ξ => chartedEnergyAt a w V (pushforwardField j ξ)) ξ
                (bondVariation k u) (bondVariation l u')| ≤
              (2 * (C * (θ + Real.exp (-(c.δ₂ * ((L : ℝ) * ((r₂ : ℝ) / 2) - 2 * L - 1))))) / hh + 2 * C * hh) *
                ‖u‖ * ‖u'‖
end YangMills.Construction.ColdStepAtMirrorFrames
end
