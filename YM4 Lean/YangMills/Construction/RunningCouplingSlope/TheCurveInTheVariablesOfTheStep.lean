import YangMills.Construction.RunningCouplingSlope.ExponentOfAStepAlongACurve
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames StepSettings TorusFields TorusLumps
namespace RunningCouplingSlope
def imaginaryToEuclidean (v : imaginaryQuaternions) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(v : ℍ[ℝ]).imI, (v : ℍ[ℝ]).imJ, (v : ℍ[ℝ]).imK]
variable {k : ℕ} (S : StepSetup) (n : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
def minimizerCoordinatesAlong (τ : Fin k → ℝ) :
    StepVariable (finiteCells (torusFrame S.params.side S.depth n)) :=
  fun b => imaginaryToEuclidean
    (minimizingBondCoordinate S.params.coupling S.anchorRadius
      (finiteCells (torusFrame S.params.side S.depth n)) b.1 (perturbedTop S n c X τ))
def chartedEnergyAlong
    (p : StepVariable (finiteCells (torusFrame S.params.side S.depth n)) × (Fin k → ℝ)) : ℝ :=
  chartedEnergy S.params.coupling (stepCoordinates p.1) (perturbedTop S n c X p.2)
end RunningCouplingSlope
end YangMills.Construction
end
