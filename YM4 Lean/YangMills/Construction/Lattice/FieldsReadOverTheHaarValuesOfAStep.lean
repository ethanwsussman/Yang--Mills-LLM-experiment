import YangMills.Construction.Lattice.OneStepAndLargeFieldOperationsAtAPoint
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
open ParameterChoice
namespace PeriodicLattice.CubesOfStep
variable {m K : ℕ} {c : ChoiceUpToRadii} {x : ℕ → ℝ} {E : ℕ → Type} {k : ℕ}
  {h : LabelHistory c.toChoiceUpToDegreeConstants m K x E k} {X : Set (FourTorus c.L m)}
def updateHaarAt (l : ℕ) (A : AllStepVariables c x h X) (W : AllLevelFields c.L m K) :
    AllLevelFields c.L m K :=
  Function.update W l (assignHaarValues A l (W l))
def liftFrom (l : ℕ) (A : AllStepVariables c x h X) (W : AllLevelFields c.L m K) :
    AllLevelFields c.L m K
  | 0 => W 0
  | n + 1 =>
    if l ≤ n then
      assignHaarValues A (n + 1) (assignAverages h X n (liftFrom l A W n) (W (n + 1)))
    else W (n + 1)
end PeriodicLattice.CubesOfStep
end YangMills.Construction
