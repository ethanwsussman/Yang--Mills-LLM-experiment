import YangMills.Construction.ColdStepAtMirrorFrames.ChartPointsNearABox
import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import YangMills.Construction.ColdStepAtMirrorFrames.OtherTermsOfTheExponentForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages ColdStepAtMirrorFrames
def EnergyAboveBasePointAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions),
    IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → IsChartBasePoint T w V →
    IsBlockTorus T.L F ∧
    (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsAdmissibleChartPoint T.L T.chainParams.σA (shiftCoordinates w η) V ∧
        ContDiffAt ℝ 3 (chartedEnergyAt T.a w V) η) ∧
    (∀ u : StepVariable (finiteCells F),
      T.chainParams.lam * ∑ b, ‖u b‖ ^ 2 ≤ secondDerivAlong (chartedEnergyAt T.a w V) 0 u u) ∧
    ∃ K : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ,
      (∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
        |secondDerivAlong (chartedEnergyAt T.a w V) 0 (bondVariation b e) (bondVariation b' e')| ≤
          K b b' * ‖e‖ * ‖e'‖) ∧
      ∀ b, ∑ b', K b b' * (Real.exp (2 * T.κ * chordBondDist F b b') - 1) ≤ T.chainParams.lam / 16
def EnergyAboveBasePoint : Prop := EventuallyInParameters EnergyAboveBasePointAt
end YangMills.Construction.ResponseInTheExpansion
end
