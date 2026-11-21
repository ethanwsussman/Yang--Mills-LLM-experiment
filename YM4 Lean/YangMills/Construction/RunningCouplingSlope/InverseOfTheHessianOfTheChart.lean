import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames
variable {F : BlockFrame}
def chartHessian (g : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) :
    Matrix (ReferenceDensity.ChartCoord F) (ReferenceDensity.ChartCoord F) ℝ :=
  fun i j => ColdStepAtMirrorFrames.secondDerivAlong (fun η : StepVariable (finiteCells F) =>
      chartedEnergy g (fun x k => w x k + stepCoordinates η x k) V) 0
    (bondVariation i.1 (EuclideanSpace.single i.2 1)) (bondVariation j.1 (EuclideanSpace.single j.2 1))
structure IsBaseCoordinate (r s : ℝ) (V : F.GaugeField F.top) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) :
    Prop where
  vanish_off : ∀ e, e ∉ chordBonds (finiteCells F) → w e.1 e.2 = 0
  norm_le : ∀ e ∈ chordBonds (finiteCells F), ‖w e.1 e.2‖ ≤ r
  norm_le_inv_side : ∀ e ∈ chordBonds (finiteCells F), ‖w e.1 e.2‖ ≤ 1 / (64 * (F.blockSide : ℝ))
  cold : BlockAverages.IsCold (finiteCells F) F.depth s (chartedField w V)
def coordDist (i j : ReferenceDensity.ChartCoord F) : ℕ :=
  cellSupDist (enclosingCell i.1.1.1) (enclosingCell j.1.1.1)
def ChartHessianInverseDecay : Prop :=
  ∃ CS κ : RenormalizationStepParameters.ChainParameters → ℝ, (∀ p, 0 < CS p) ∧ (∀ p, 0 < κ p) ∧
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → κ T.toChainParameters ≤ T.δ₁ / 8 ∧
    ∀ F : BlockFrame, F.blockSide = T.side → IsLargeCubicTorus F →
      ∀ (s : ℝ) (V : F.GaugeField F.top) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions), 0 < s → s ≤ T.σA →
        BlockAverages.IsCold (finiteCells F) F.top s V → IsBaseCoordinate T.ρA T.σA V w →
        (∀ i j, |chartHessian T.coupling w V i j| ≤
          CS T.toChainParameters * Real.exp (-(T.δ₁ * coordDist i j))) ∧
        ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
          IsUnit (u • chartHessian T.coupling w V + (1 - u) • T.lam •
            (1 : Matrix (ReferenceDensity.ChartCoord F) (ReferenceDensity.ChartCoord F) ℝ)) ∧
          ∀ i j, |(u • chartHessian T.coupling w V + (1 - u) • T.lam •
              (1 : Matrix (ReferenceDensity.ChartCoord F) (ReferenceDensity.ChartCoord F) ℝ))⁻¹ i j| ≤
            2 / T.lam * Real.exp (-(2 * κ T.toChainParameters * coordDist i j))
end YangMills.Construction.RunningCouplingSlope
end
