import YangMills.Construction.Continuum.TuplesOfDisjointSupports
import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.CenteredRepresentatives
open InfiniteLattice DisjointTuples
def centeredRep (L K : ℕ) (ν : Measure (GaugeFieldAtScale L K)) (X : DisjointTuple)
    (U : GaugeFieldAtScale L K) : ℝ :=
  (X.1.map fun f => smearedEnergy f U - ∫ V, smearedEnergy f V ∂ν).prod
def centeredRepObs (L K : ℕ) (ν : Measure (GaugeFieldAtScale L K)) (X : DisjointTuple) :
    GaugeFieldAtScale L K → ℂ :=
  fun U => (centeredRep L K ν X U : ℂ)
theorem centeredRep_nil (L K : ℕ) (ν : Measure (GaugeFieldAtScale L K))
    (U : GaugeFieldAtScale L K) : centeredRep L K ν DisjointTuple.nil U = 1 :=
  rfl
end YangMills.Construction.CenteredRepresentatives
