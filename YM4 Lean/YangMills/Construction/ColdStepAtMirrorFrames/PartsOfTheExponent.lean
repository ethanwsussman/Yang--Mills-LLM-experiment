import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.CommonBondsOfTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F F' : BlockFrame}
open Classical in
def slopeComponent (star : Bool) (a ρA x : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : ℝ :=
  x * (∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
      ∫ v in (0 : ℝ)..1, chartedSlope a (coordsAboveFrame star a ρA m V (v • η)) V b.1
        (toImaginary (η b)) else 0)
open Classical in
def kernelGapComponent (star : Bool) (a ρA x : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
    haarGapExcess a x (fieldAboveFrame star a ρA m V η) c
open Classical in
def haarComponent (star : Bool) (a ρA : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
    haarLogRatio (coordsAboveFrame star a ρA m V η b.1.1 b.1.2) else 0
structure AgreeingTopPair (T : StepParameters) (t : ℕ) (x : ℝ) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
    (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) : Prop where
  coupling_le : T.coupling ≤ x
  top : IsCubicTopTorus T.L t T.n₀ F
  top' : IsCubicTopTorus T.L t T.n₀ F'
  small : IsSmallCurvature (5 / 4 * T.σ) V
  small' : IsSmallCurvature (5 / 4 * T.σ) V'
  agree : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r
  radius_le : T.blockIndex ≤ r
def NearCellsClose (ρ x κ ε : ℝ) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ)
    (G : F.Cell → StepVariable (finiteCells F) → ℝ) (G' : F'.Cell → StepVariable (finiteCells F') → ℝ) : Prop :=
  ∀ (c : ↥(centredCube (2 * (r / 8) + 1))), ∀ ζ ∈ openPolyball ↥(commonBondOffsets Y Y' (r / 2)) ρ,
    |G (offsetCell Y (r / 8) c) (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ) -
      G' (offsetCell Y' (r / 8) c) (zeroExtensionL (commonBondRight Y Y' (r / 2)) ζ)| ≤
    ε * (x * weightedSqNormAt κ (chordBondCell F) (cellDistReal F) (offsetCell Y (r / 8) c)
      (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ) + 1)
end YangMills.Construction.ColdStepAtMirrorFrames
end
