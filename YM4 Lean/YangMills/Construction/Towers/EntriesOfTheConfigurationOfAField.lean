import YangMills.Construction.Towers.EntireCoordinatesOfAField
import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
open EntireDependence
open BackgroundJets (gaugeFieldOfForm)
def GaugeFieldOfFormEntries : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ,
    (∀ ζ, gaugeFieldOfForm L k ζ ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup) ∧
    ∀ (e : PeriodicOperators.PosEdge L k 0) (i j : Fin 2),
      IsEntireOn (remainderIndex L k) (edgeIndices L k e)
        (fun ζ => gaugeFieldOfForm L k ζ e.1 i j) ∧
      IsEntireOn (remainderIndex L k) (edgeIndices L k e)
        (fun ζ => (gaugeFieldOfForm L k ζ e.1)⁻¹ i j)
end YangMills.Construction.Tower.FullSpace
end
