import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAStep
import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import YangMills.Construction.ResponseInTheExpansion.OneStepToSecondOrder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings StepCosts
open Classical
abbrev reflectedTorusFrame (L t m n : ℕ) : BlockFrame := reflectedFrame (torusFrame L t n) m
def reflectedBondPosition (L t m : ℕ) {n : ℕ} (o : TorusSite n) (b : TorusBond (n * L)) :
    (reflectedTorusFrame L t m n).Site (reflectedTorusFrame L t m n).depth × Fin 4 :=
  (siteOfCoords _ fun i => (b.1 i - (siteOfInt (n := n * L) fun l => (L : ℤ) * ((o l).cast : ℤ)) i).valMinAbs, b.2)
def reflectedTopField (L t m : ℕ) {n : ℕ} (o : TorusSite n) (V : TorusField n) :
    (reflectedTorusFrame L t m n).GaugeField (reflectedTorusFrame L t m n).top :=
  reflectedField m (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top o)
    (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)
def reflectedStepMean (R : StepSetup) (m : ℕ) {n : ℕ} (o : TorusSite n) (V : TorusField n)
    (H : StepVariable (finiteCells (reflectedTorusFrame R.params.side R.depth m n)) → ℝ) : ℝ :=
  cutoffMean R.ballRadius R.barrierFn
    (stepExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach (localFamilyOfDensity R.density) 1
      (reflectedTopField R.params.side R.depth m o V)) H
def reflectedCoordinateAt (L t m : ℕ) {n : ℕ} (o : TorusSite n)
    (η : StepVariable (finiteCells (reflectedTorusFrame L t m n))) (b : TorusBond (n * L)) : imaginaryQuaternions :=
  stepCoordinates η (reflectedBondPosition L t m o b).1 (reflectedBondPosition L t m o b).2
def imaginaryComponentsOn {n : ℕ} (Z : Finset (TorusBond n)) (e : TorusBond n → imaginaryQuaternions) :
    ↥Z × Fin 3 → ℝ := fun p => imaginaryComponent p.2 (e p.1.1)
def reflectedFunctional (L t m : ℕ) {n : ℕ} [NeZero n] [NeZero L] (o : TorusSite n) (l : TorusBond (n * L) → ℝ)
    (e : Fin 3) : ChartCoordinate (reflectedTorusFrame L t m n) → ℝ := fun p =>
  if p.2 = e then ∑ c : TorusBond (n * L), if reflectedBondPosition L t m o c = p.1.1 then l c else 0 else 0
end YangMills.Construction.ResponseInTheExpansion
end
