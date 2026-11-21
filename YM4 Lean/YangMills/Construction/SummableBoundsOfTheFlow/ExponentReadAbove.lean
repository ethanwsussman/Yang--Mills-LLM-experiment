import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveAreAlongLists
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsAtTheFramesBetween
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.Interpolation
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.IteratedDerivative
variable {F : BlockFrame}
open Classical in
def cellChordBonds (Y : F.Cell) : Finset ↥(chordBonds (finiteCells F)) :=
  Finset.univ.filter fun b => enclosingCell b.1.1 = Y
open Classical in
def cellExponentRotatedEvalStatement : Prop :=
  (∀ (F : BlockFrame) (s a ρA x : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F))
    (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    (∀ v ∈ Set.Icc (0 : ℝ) 1,
      ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (rotatedEval (interpolatedEnergy s a ρA m) V c X) (v • η, 0)) →
    rotatedEval (fun ζ V' => interpolatedBlockExponent s a ρA x m Y V' ζ) V c X =ᶠ[𝓝 (η, 0)] fun p =>
      x * rayGradientSum (rotatedEval (interpolatedEnergy s a ρA m) V c X) (cellChordBonds Y) p -
      (∑ c₀ ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        (rotatedEval (contourHaarGap s a ρA x m c₀) V c X p - haarGap (a * x))) -
      ∑ b ∈ cellChordBonds Y, rotatedEval (interpolatedHaarLogRatio s a ρA m b) V c X p) ∧
  ∀ (F : BlockFrame) (s a ρA : ℝ) (m k : ℕ) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)),
    DifferentiableAt ℝ (rotatedEval (interpolatedEnergy s a ρA m) V c X) (0, τ) →
    interpolatedSlope s a ρA m b.1 (toImaginary e) (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) =
      fderiv ℝ (rotatedEval (interpolatedEnergy s a ρA m) V c X) (0, τ) (Pi.single b e, 0)
end YangMills.Construction.Interpolation
end
