import YangMills.Construction.RunningCouplingSlope.TotalOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps
namespace SlopeCoefficient
def minimizerOnFinerTorus (a ρ : ℝ) (L t n : ℕ) (V : TorusField n) : TorusField (n * L) :=
  fun z i => fieldAboveFrame (F := torusFrame L t n) true a ρ 0
    (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) 0
    (siteOfCoords (torusFrame L t n).depth fun k => ((z k).cast : ℤ)) i
def chainLogarithm (a ρ : ℝ) (L : ℕ) : ℕ → GaugeTotal
  | 0 => fun _ _ => 0
  | t + 1 => fun n V => stepGaugeTotal a ρ L t n V + chainLogarithm a ρ L t (n * L) (minimizerOnFinerTorus a ρ L t n V)
end SlopeCoefficient
end YangMills.Construction
end
