import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ScaledVariables
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity TorusLumps
variable {F : BlockFrame}
def haarGapTail (u : ℝ) : ℝ :=
  -Real.log (2 / Real.pi * ∫ v in Set.Ioi (0 : ℝ), Real.exp (-v) * Real.sqrt v * Real.sqrt (2 - u * v))
def haarGapShift (a l r : ℝ) : ℝ := 3 / 2 * Real.log r + haarGapTail (l ^ 2 / (a * r)) - haarGapTail (l ^ 2 / a)
def rescaledCellTerm (a ρ l : ℝ) (Y : F.Cell) (V : F.GaugeField F.top) (ζ : StepVariable (finiteCells F)) : ℝ :=
  (∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
      ∫ v in (0 : ℝ)..1, (1 - v) * secondDerivAlong (chartedEnergyAtMinimizer a ρ V) ((v * l) • ζ)
        (bondVariation b (ζ b)) ζ else 0) -
    (∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
      haarGapShift a l ‖contourAverage (fieldAboveFrame true a ρ 0 V (l • ζ)) c‖) -
    ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
      haarLogRatio (coordsAboveFrame true a ρ 0 V (l • ζ) b.1.1 b.1.2) else 0
def rescaledExponent (a ρ : ℝ) (f : LocalFamily) (ν l : ℝ) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) : ℝ :=
  (∑ Y ∈ finiteCells F, rescaledCellTerm a ρ l Y V ζ) -
    ν * ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion true a ρ 0 f y (l • ζ) V
def rescaledEnergy (a ρ : ℝ) (p : ℝ → ℝ) (f : LocalFamily) (ν l : ℝ) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) : ℝ :=
  (∑ b : ↥(chordBonds (finiteCells F)), p (|l| * ‖ζ b‖)) + rescaledExponent a ρ f ν l V ζ
inductive StepLaw
  | tilted (ν : ℝ)
  | interpolated (τ : ℝ)
def stepLawExponent (a ρ lam x : ℝ) (f : LocalFamily) (V : F.GaugeField F.top) :
    StepLaw → StepVariable (finiteCells F) → ℝ
  | .tilted ν => stepExponent true a ρ x 0 f ν V
  | .interpolated τ => fun η => τ * stepExponent true a ρ x 0 f 0 V η + (1 - τ) * totalQuadratic lam x η
def rescaledLawExponent (a ρ lam : ℝ) (f : LocalFamily) (l : ℝ) (V : F.GaugeField F.top) :
    StepLaw → StepVariable (finiteCells F) → ℝ
  | .tilted ν => rescaledExponent a ρ f ν l V
  | .interpolated τ => fun ζ => τ * rescaledExponent a ρ f 0 l V ζ +
      (1 - τ) * (lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2)
def rescaledMean (a ρA ρ lam l : ℝ) (p : ℝ → ℝ) (f : LocalFamily) (law : StepLaw) (V : F.GaugeField F.top)
    (H : StepVariable (finiteCells F) → ℝ) : ℝ :=
  cutoffMean ρ p (stepLawExponent a ρA lam (l⁻¹ ^ 2) f V law) fun η => H (l⁻¹ • η)
def gaussianWeight (a ρ lam : ℝ) (f : LocalFamily) (V : F.GaugeField F.top) (law : StepLaw)
    (ζ : StepVariable (finiteCells F)) : ℝ :=
  Real.exp (-(rescaledLawExponent a ρ lam f 0 V law ζ - rescaledLawExponent a ρ lam f 0 V law 0))
def gaussianMean (a ρ lam : ℝ) (f : LocalFamily) (V : F.GaugeField F.top) (law : StepLaw)
    (H : StepVariable (finiteCells F) → ℝ) : ℝ :=
  (∫ ζ, H ζ * gaussianWeight a ρ lam f V law ζ) / ∫ ζ, gaussianWeight a ρ lam f V law ζ
def gaussianCovariance (a ρ lam : ℝ) (f : LocalFamily) (V : F.GaugeField F.top) (law : StepLaw)
    (H H' : StepVariable (finiteCells F) → ℝ) : ℝ :=
  gaussianMean a ρ lam f V law (fun ζ => H ζ * H' ζ) -
    gaussianMean a ρ lam f V law H * gaussianMean a ρ lam f V law H'
def taylorCoeffAtZero (i : ℕ) (g : ℝ → ℝ) : ℝ := iteratedDeriv i g 0 / (i.factorial : ℝ)
def secondOrderCoeff (a ρ lam : ℝ) (f : LocalFamily) (V : F.GaugeField F.top) (law : StepLaw)
    (Ob : ℝ → StepVariable (finiteCells F) → ℝ) : ℝ :=
  let O : ℕ → StepVariable (finiteCells F) → ℝ := fun i ζ => taylorCoeffAtZero i fun l => Ob l ζ
  let U : ℕ → StepVariable (finiteCells F) → ℝ := fun i ζ =>
    taylorCoeffAtZero i fun l => rescaledLawExponent a ρ lam f l V law ζ
  gaussianMean a ρ lam f V law (O 2) - gaussianCovariance a ρ lam f V law (O 1) (U 1) -
    gaussianCovariance a ρ lam f V law (O 0) (U 2) +
    1 / 2 * gaussianCovariance a ρ lam f V law (O 0) fun ζ => U 1 ζ ^ 2
def rescaledCellRemainder (a ρ lam l : ℝ) (Y : F.Cell) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) : ℝ :=
  rescaledCellTerm a ρ l Y V ζ - lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)),
    if enclosingCell b.1.1 = Y then ‖ζ b‖ ^ 2 else 0
def rescaledCellExpansion (a ρ : ℝ) (f : LocalFamily) (l : ℝ) (Y : F.Cell) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) : ℝ :=
  cellCentredExpansion true a ρ 0 f Y (l • ζ) V
def secondOrderDensityCoeff (a ρ lam : ℝ) (f : LocalFamily) (F : BlockFrame) (Y : F.Cell)
    (V : F.GaugeField F.top) : ℝ :=
  -(∫ τ in (0 : ℝ)..1, secondOrderCoeff a ρ lam f V (.interpolated τ) fun l => rescaledCellRemainder a ρ lam l Y V) +
    ∫ ν in (0 : ℝ)..1, secondOrderCoeff a ρ lam f V (.tilted ν) fun l => rescaledCellExpansion a ρ f l Y V
def secondStepCoefficient (a ρ lam : ℝ) (L t : ℕ) : ℝ :=
  curvatureCoefficient (densityOfTopFamily L t
    (secondOrderDensityCoeff a ρ lam (localFamilyOfDensity (referenceFamily a ρ lam L t))))
def minimizerDensities (a ρA ρ lam x : ℝ) (p : ℝ → ℝ) (L t : ℕ) (f : LocalFamily) : LocalDensity :=
  densityOfTopFamily L t fun _ Y V =>
    interactionDensity true a ρA ρ lam x 0 p f Y V + expansionDensity true a ρA ρ x 0 p f Y V
end ScaledVariables
end YangMills.Construction
end
