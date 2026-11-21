import YangMills.Construction.Lattice.PlaquetteFunctionsAndTwoNotionsOfSupport
import YangMills.Construction.TestFunctions.SeparatedBumpPairs
import YangMills.Construction.Torus.DistanceBallsIntegralAndVolumeInPhysicalUnits
import YangMills.Construction.Torus.QuadruplesOfTestFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.QuadrupleClasses
open TestFunctions TorusMetric
def pairsR4 (d ϑ : ℝ) : Set (((Fin 4 → ℝ) → ℝ) × ((Fin 4 → ℝ) → ℝ)) :=
  separatedPairs euclidDistR4 closedBallR4 setDistR4 TorusMeasure.integralR4 d ϑ
def pairsTorus (s : Conventions.StandingParameters) (d ϑ : ℝ) :
    Set ((s.Torus → ℝ) × (s.Torus → ℝ)) :=
  separatedPairs (Y := s.Torus) (euclidDistTorus (ℓ := PeriodicLattice.torusSide s.L s.m))
    (closedBallTorus (ℓ := PeriodicLattice.torusSide s.L s.m))
    (setEuclidDist (S := PeriodicLattice.torusSide s.L s.m))
    (TorusMeasure.torusIntegral (s := s)) d ϑ
def quadsR4 (d ϑ : ℝ) : Set (Fin 4 → (Fin 4 → ℝ) → ℝ) :=
  {f | IsScaleShape d ϑ ∧ f ∈ pairwiseQuadruples euclidDistR4 (pairsR4 d ϑ)}
def quadsTorus (s : Conventions.StandingParameters) (d ϑ : ℝ) : Set (Fin 4 → s.Torus → ℝ) :=
  {f | IsScaleShape d ϑ ∧ 40 * d ≤ PeriodicLattice.torusSide s.L s.m ∧
    f ∈ pairwiseQuadruples (euclidDistTorus (ℓ := PeriodicLattice.torusSide s.L s.m))
      (pairsTorus s d ϑ)}
theorem euclideanTSupport_eq_tsupport (f : (Fin 4 → ℝ) → ℝ) :
    PlaquetteSupports.euclideanTSupport f = tsupport f :=
  rfl
end YangMills.Construction.QuadrupleClasses
