import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
namespace PeriodicTorusMeasures
abbrev pushforwardWilsonMeasure (L m K : ℕ) (β : ℝ) :
    Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ))) :=
  InfiniteLattice.liftedWilsonMeasure L m K β
section OfMeasure
variable {a : ℝ}
abbrev measureConnectedFunction {n : ℕ} (ν : Measure (InfiniteLattice.GaugeField a))
    (X : Fin n → InfiniteLattice.AmbientSpace → ℝ) : ℂ :=
  InfiniteLattice.smearedEnergyCumulant ν X
def measureCentredMoment (ν : Measure (InfiniteLattice.GaugeField a)) :
    List (InfiniteLattice.AmbientSpace → ℝ) → ℝ
  | [] => 1
  | f :: X => ∫ U, ((f :: X).map fun h =>
      InfiniteLattice.smearedEnergy h U - ∫ V, InfiniteLattice.smearedEnergy h V ∂ν).prod ∂ν
end OfMeasure
end PeriodicTorusMeasures
end InfiniteLattice
end YangMills.Construction
end
