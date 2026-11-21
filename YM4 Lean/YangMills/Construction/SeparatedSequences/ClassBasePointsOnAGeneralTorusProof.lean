import YangMills.Construction.SeparatedSequences.BasePointIsThatOfTheOperatorsAndTheFoot
import YangMills.Construction.SeparatedSequences.ClassBasePointsOnAGeneralTorus
import YangMills.Construction.SeparatedSequences.ClassGeometryOnAGeneralTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses.GaugeAnchorsOfClass
open SingleSequence SingleSequence.SequenceData
variable (s : SequenceData)
theorem toTorus_eq_readPoint (x : s.data.Point) :
    s.toTorus s.data.levelUnitTorus.toScaleData.torusSide x = s.data.levelUnitTorus.readPoint x := by
  have h : s.data.levelUnitTorus.toScaleData.torusSide ≠ 0 :=
    s.data.levelUnitTorus.torusSide_ne_zero
  rw [SequenceData.toTorus, dif_pos h]
  rfl
theorem toTorus_injective :
    Function.Injective (s.toTorus s.data.levelUnitTorus.toScaleData.torusSide) := by
  intro x y hxy
  rw [toTorus_eq_readPoint, toTorus_eq_readPoint] at hxy
  exact s.data.levelUnitTorus.levelEquiv.injective hxy
end SeparatedClasses.GaugeAnchorsOfClass
end YangMills.Construction
