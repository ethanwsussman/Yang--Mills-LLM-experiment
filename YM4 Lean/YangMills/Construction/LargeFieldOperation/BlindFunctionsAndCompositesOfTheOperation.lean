import YangMills.Construction.LargeField.StateSpaceMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
section Blind
variable {L m K k : ℕ}
abbrev IsBlindOnBonds {α : Type*} (F : BlockFields L m K k → α)
    (E : Set (BondAtLevel L m K k)) : Prop :=
  IndependentOfBonds F E
abbrev incidentBonds (L m K k : ℕ) (Y : Set (FourTorus L m)) : Set (BondAtLevel L m K k) :=
  bondsMeeting Y
def MeasuresAgreeOffBonds (E : Set (BondAtLevel L m K k))
    (μ μ' : ComplexMeasure (BlockFields L m K k)) : Prop :=
  ∀ F : BlockFields L m K k → ℂ, IsBoundedMeasurableBlockFunction F → IsBlindOnBonds F E →
    μ.integral F (ContinuousLinearMap.mul ℝ ℂ) = μ'.integral F (ContinuousLinearMap.mul ℝ ℂ)
abbrev MeasuresAgreeOffRegion (Y : Set (FourTorus L m))
    (μ μ' : ComplexMeasure (BlockFields L m K k)) : Prop :=
  MeasuresAgreeOffBonds (incidentBonds L m K k Y) μ μ'
end Blind
end YangMills.Construction.PeriodicLattice
