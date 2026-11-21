import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.ResponseInTheExpansion
variable {F : BlockFrame}
abbrev ChartCoordinate (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F)) × Fin 3
def linearFunctional (l : ChartCoordinate F → ℝ) (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ p, l p * η p.1 p.2
open Classical in
def twoCoordinateVariation (p q : ChartCoordinate F) (s s' : ℝ) : StepVariable (finiteCells F) := fun b =>
  WithLp.toLp 2 fun i => (if (b, i) = p then s else 0) + (if (b, i) = q then s' else 0)
def frameHessian (a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top) :
    Matrix (ChartCoordinate F) (ChartCoordinate F) ℝ :=
  fun p q => deriv (fun s => deriv (fun s' =>
    chartedEnergy a (coordsAboveFrame false a ρA m V (twoCoordinateVariation p q s s')) V) 0) 0
open Classical in
def wickPairingSum {q : ℕ} (G : Fin q → Fin q → ℝ) : ℝ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin q)),
    if ∀ B ∈ π.parts, B.card = 2 then
      ∏ B ∈ π.parts, (if h : B.Nonempty then G (B.min' h) (B.max' h) else 1)
    else 0
open Classical in
def GaussianMomentApproxAt (T : StepParameters) : Prop :=
  ∀ q : ℕ, ∃ C : ℝ, ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top),
    T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (9 / 8 * T.σ) V →
    ∀ l : Fin q → ChartCoordinate F → ℝ,
      |cutoffMean T.ballRadius T.p
          (stepExponent false T.a T.chainParams.ρA x (frameRadius x) f 1 V)
          (fun η => ∏ i, linearFunctional (l i) η) -
        x ^ (-(q : ℝ) / 2) * wickPairingSum fun i j =>
          l i ⬝ᵥ Matrix.mulVec (frameHessian T.a T.chainParams.ρA (frameRadius x) V)⁻¹ (l j)| ≤
      C * x ^ (-((q : ℝ) + 1) / 2) * ∏ i, ∑ p, |l i p|
def gaussianMomentApproxStatement : Prop := EventuallyInParameters GaussianMomentApproxAt
end YangMills.Construction.ResponseInTheExpansion
end
