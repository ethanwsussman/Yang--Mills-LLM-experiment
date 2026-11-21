import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
instance : SecondCountableTopology Matrices.ComplexMatrix2 :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
namespace PeriodicLattice
variable {L m K k : ℕ}
abbrev BlockFields (L m K k : ℕ) : Type := ↥(gaugeFieldsAtLevel L m K k)
abbrev LevelStateSpace (L m K k : ℕ) (Y : Type*) : Type _ := BlockFields L m K k × Y
def blockFieldOf {Y : Type*} : LevelStateSpace L m K k Y → BlockFields L m K k := Prod.fst
abbrev ComplexStateMeasure (L m K k : ℕ) (Y : Type*) [MeasurableSpace Y] : Type _ :=
  ComplexMeasure (LevelStateSpace L m K k Y)
def pushToBlockFields {Y : Type*} [MeasurableSpace Y] (μ : ComplexStateMeasure L m K k Y) :
    ComplexMeasure (BlockFields L m K k) :=
  μ.map blockFieldOf
def IsBoundedMeasurableBlockFunction (F : BlockFields L m K k → ℂ) : Prop :=
  Measurable F ∧ ∃ C : ℝ, ∀ V, ‖F V‖ ≤ C
def IndependentOfBonds {E : Type*} (F : BlockFields L m K k → E)
    (B : Set (BondAtLevel L m K k)) : Prop :=
  ∀ V W : BlockFields L m K k, (∀ b, b ∉ B → V.1 b = W.1 b) → F V = F W
end PeriodicLattice
end YangMills.Construction
