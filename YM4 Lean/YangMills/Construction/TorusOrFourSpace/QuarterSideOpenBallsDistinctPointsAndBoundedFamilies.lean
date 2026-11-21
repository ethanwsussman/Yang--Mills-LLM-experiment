import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.TorusOrFourSpace.FunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (D : Params) (E : Kind)
def periodQuarter : Kind → ℝ≥0∞
  | euclidean => ⊤
  | torus => ENNReal.ofReal (D.side / 4)
def openBallAt (y : E.Pt D) (r : ℝ) : Set (E.Pt D) := {y' | quotDist D E y' y < r}
abbrev pairwiseDistinct (n : ℕ+) : Set (E.Tuple D n) :=
  TestFunctions.injectiveTuples (E.Pt D) (n : ℕ)
end YangMills.Construction.PeriodicSpace.Kind
