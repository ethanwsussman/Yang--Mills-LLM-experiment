import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace TimeAxis
open TorusMetric PeriodicLattice
open InfiniteLattice (AmbientSpace)
def timeIdx : Fin 4 := 3
def timeComponent (x : AmbientSpace) : ℝ := x timeIdx
def timeLine : Set AmbientSpace := range fun r : ℝ => (Pi.single timeIdx r : AmbientSpace)
def timeReflection (x : AmbientSpace) : AmbientSpace := ![x 0, x 1, x 2, -x 3]
def upperHalfSpace : Set AmbientSpace := {x | timeComponent x > 0}
def IsPurelySpatial (v : AmbientSpace) : Prop := timeComponent v = 0
end TimeAxis
end YangMills.Construction
