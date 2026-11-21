import YangMills.Construction.ClusterExpansionOfAStep.FormsOfAFamily
import YangMills.Construction.ClusterExpansionOfAStep.SharesAreACurvatureFamily
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusLumps ShareFamilies
namespace ReferenceDensity
variable {F : BlockFrame}
def chartedEnergyAtMinimizer (a ρ : ℝ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) : ℝ :=
  chartedEnergy a (coordsAboveFrame true a ρ 0 V η) V
abbrev ChartCoord (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F)) × Fin 3
def chartedHessian (a ρ : ℝ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    Matrix (ChartCoord F) (ChartCoord F) ℝ :=
  fun i j => secondDerivAlong (chartedEnergyAtMinimizer a ρ V) η (bondVariation i.1 (EuclideanSpace.single i.2 1))
    (bondVariation j.1 (EuclideanSpace.single j.2 1))
def hessianCellShare (a ρ lam : ℝ) (Y : F.Cell) (V : F.GaugeField F.top) (τ : ℝ) : ℝ :=
  ∑ i : ChartCoord F, if enclosingCell i.1.1.1 = Y then
    ((chartedHessian a ρ V 0 - lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)) *
      (τ • chartedHessian a ρ V 0 + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ))⁻¹) i i
    else 0
def stepDensity (a ρ lam : ℝ) (Y : F.Cell) (V : F.GaugeField F.top) : ℝ :=
  -(1 / 2) * (∫ τ in (0 : ℝ)..1, hessianCellShare a ρ lam Y V τ) +
    3 / 2 * (∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
      Real.log ‖contourAverage (fieldAboveFrame true a ρ 0 V 0) c‖) +
    ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
      haarLogRatio (coordsAboveFrame true a ρ 0 V 0 b.1.1 b.1.2) else 0
def stepDensityFamily (a ρ lam : ℝ) (L t : ℕ) : LocalDensity :=
  densityOfTopFamily L t fun _ Y V => stepDensity a ρ lam Y V
def oneLoopCoefficient (a ρ lam : ℝ) (L t : ℕ) : ℝ := curvatureCoefficient (stepDensityFamily a ρ lam L t)
def familyAtMinimizer (a ρ : ℝ) (L t : ℕ) (f : LocalDensity) : LocalDensity :=
  densityOfTopFamily L t fun _ Y V => cellCentredExpansion true a ρ 0 (localFamilyOfDensity f) Y 0 V
def referenceFamily (a ρ lam : ℝ) (L : ℕ) : ℕ → LocalDensity
  | 0 => 0
  | t + 1 => stepDensityFamily a ρ lam L t + familyAtMinimizer a ρ L t (referenceFamily a ρ lam L t) -
      oneLoopCoefficient a ρ lam L t • levelShareFamily a L (t + 1)
end ReferenceDensity
end YangMills.Construction
end
