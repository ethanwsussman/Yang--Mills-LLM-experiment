import YangMills.Construction.InfiniteLattice.GeneratingFunctionsAndConnectedFunctionsOfAMeasureAndOfATorus
import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open InfiniteLattice LevelTestFunctions
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
def rescaledTestFunction (i : Fin Λ.k) (x : InfiniteLattice.AmbientSpace) : ℝ :=
  S.data.fn i (WithLp.toLp 2 fun a => (Λ.stepParams.side : ℝ) ^ S.data.windowLevel / (Λ.stepParams.side : ℝ) ^ S.data.scaleLevel *
    (x a - S.data.center a))
def stateUrsell {K : ℕ} (ν : Measure (RefinedGaugeField Λ.stepParams.side K)) : ℂ :=
  ursellFunctionOfFamily ν fun i => S.rescaledTestFunction i
end MomentPoint
end YangMills.Construction.MomentLaw
end
