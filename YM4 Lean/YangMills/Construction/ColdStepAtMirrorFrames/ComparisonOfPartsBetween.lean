import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.DistancesOfBlocks
import YangMills.Construction.ColdStepAtMirrorFrames.LocalTermsOfAMeasureForm
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages FamilyNorms Interpolation
namespace ColdStepAtMirrorFrames
variable {F F' : BlockFrame}
def PairedPartsCompare {ι : Type} [Fintype ι] [DecidableEq ι] (ρ c ε x κ : ℝ)
    (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F'))) (z : F.Cell)
    (G : StepVariable (finiteCells F) → ℝ) (G' : StepVariable (finiteCells F') → ℝ) : Prop :=
  ∀ ξ ∈ openPolyball ι ρ,
    |G' (pushforwardField j' ξ) - G (pushforwardField j ξ)| ≤
      c * ε * (x * weightedSqNormNear κ (fun k => bondBlock F (j k)) (blockDist F) z ξ + 1) ∧
    ∀ k, bondGradNorm (fun ζ => G' (pushforwardField j' ζ) - G (pushforwardField j ζ)) k ξ ≤
      c * ε * (x * Real.sqrt (weightedSqNormNear κ (fun k => bondBlock F (j k)) (blockDist F) z ξ) + 1) *
        Real.exp (-(2 * κ * blockDist F (bondBlock F (j k)) z))
def PairedPartsCompareSmoothly {ι : Type} [Fintype ι] [DecidableEq ι] (ρ c ε x κ : ℝ)
    (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F'))) (z : F.Cell)
    (G : StepVariable (finiteCells F) → ℝ) (G' : StepVariable (finiteCells F') → ℝ) : Prop :=
  ContDiffOn ℝ 1 (fun ζ => G' (pushforwardField j' ζ) - G (pushforwardField j ζ)) (openPolyball ι ρ) ∧
    PairedPartsCompare ρ c ε x κ j j' z G G'
structure InterpolatedComparisonSetting (T : StepParameters) (t : ℕ) (x s : ℝ) (h : LocalFamily)
    {F F' : BlockFrame} (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell)
    (q : ℕ) {ι : Type} (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F')))
    (o : Fin 4 → ℤ) : Prop where
  coupling_le : T.coupling ≤ x
  interp_mem : 0 ≤ s ∧ s ≤ 1
  family : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio h
  top : IsCubicTopTorus T.L t T.n₀ F
  top' : IsCubicTopTorus T.L t T.n₀ F'
  small : IsSmallCurvature (5 / 4 * T.σ) V
  small' : IsSmallCurvature (5 / 4 * T.σ) V'
  agree : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q
  radius_le : T.blockIndex ≤ q
  injective : Function.Injective j
  injective' : Function.Injective j'
  paired : ∀ i, ∃ (g u : Fin 4 → ℤ) (k : Fin 4), u ∈ centredCube F.blockSide ∧ WithinRadius q g ∧
    (j i).1 = fineBondAt Y g u k ∧ (j' i).1 = fineBondAt Y' g u k
  offset_le : ∀ i, 8 * |o i| ≤ (q : ℤ)
open Classical in
def interpolatedSlopePart (s a ρA x : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : ℝ :=
  x * (∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
      ∫ v in (0 : ℝ)..1, chartedSlope a (interpolatedCoords s a ρA m V (v • η)) V b.1
        (toImaginary (η b)) else 0)
open Classical in
def interpolatedGapPart (s a ρA x : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
    haarGapExcess a x (interpolatedField s a ρA m V η) c
open Classical in
def interpolatedHaarPart (s a ρA : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
      haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) else 0
end ColdStepAtMirrorFrames
end YangMills.Construction
end
