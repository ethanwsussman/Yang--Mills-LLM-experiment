import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.LocalTermsOfAMeasureForm
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.AdmittedObservables
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation TorusComparison
namespace TorusFreezing
variable {F : BlockFrame}
def stepLawCellPart (l : StepLaw) (s a ρA lam x : ℝ) (m : ℕ) (V : F.GaugeField F.top) (Y : F.Cell)
    (η : StepVariable (finiteCells F)) : ℝ :=
  match l with
  | .ofFamily φ => interpolatedBlockExponent s a ρA x m Y V η - interpolatedBlockExpansion s a ρA m φ Y η V
  | .ofWeight τ => τ * interpolatedBlockExponent s a ρA x m Y V η + (1 - τ) * cellQuadratic lam x Y η
def bondCell (b : ↥(chordBonds (finiteCells F))) : F.Cell := enclosingCell b.1.1
def realCellDist (y z : F.Cell) : ℝ := cellSupDist y z
def StepLawLocalDecomposition (P : StepParameters) : Prop :=
  ∀ (t : ℕ) (x s : ℝ) (l : StepLaw) (F : BlockFrame) [Fintype F.Cell] (V : F.GaugeField F.top),
    P.coupling ≤ x → 0 ≤ s → s ≤ 1 → l.IsAdmissible P.L t P.n₀ P.σ P.decayRate P.E P.energyRatio →
    IsCubicTopTorus P.L t P.n₀ F → IsSmallCurvature (5 / 4 * P.σ) V →
    ∃ Ψ : StepVariable (finiteCells F) → ℝ,
      (∀ η ∈ openPolyball _ P.ballRadius,
        Ψ η = l.exponent s P.a P.chainParams.ρA P.chainParams.lam x (frameRadius x) V η) ∧
      IsAdmissiblePotential P.ballRadius (x * P.chainParams.lam / 4) P.κ
        (fun b b' => realCellDist (bondCell b) (bondCell b')) Ψ ∧
      (∀ η ∈ openPolyball _ P.ballRadius,
        Ψ η = ∑ z, stepLawCellPart l s P.a P.chainParams.ρA P.chainParams.lam x (frameRadius x) V z η) ∧
      ∀ z, IsLocalTermAt P.ballRadius P.κ (P.Cs * l.amplitude P.energyRatio) x bondCell realCellDist z
        (stepLawCellPart l s P.a P.chainParams.ρA P.chainParams.lam x (frameRadius x) V z)
def stepLawLocalDecomposition : Prop := EventuallyInParameters StepLawLocalDecomposition
end TorusFreezing
end YangMills.Construction
end
