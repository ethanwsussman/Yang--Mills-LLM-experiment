import YangMills.Construction.Conventions.StandingParameters
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def FiniteProductGroupStatement : Prop :=
  (∀ (S : Type) [Finite S],
    IsTopologicalGroup (S → specialUnitary) ∧ CompactSpace (S → specialUnitary) ∧
      TopologicalSpace.MetrizableSpace (S → specialUnitary)) ∧
  (∀ (S : Type) [Finite S],
    borel (S → specialUnitary) = MeasurableSpace.pi ∧
      (∃! μ : Measure (S → specialUnitary), IsProbabilityMeasure μ ∧ μ.IsMulLeftInvariant) ∧
      IsProbabilityMeasure (haarPi S) ∧ (haarPi S).IsMulLeftInvariant ∧
      (haarPi S).IsMulRightInvariant) ∧
  (∀ (s : YangMills.Construction.Conventions.StandingParameters)
    (A : Set (YangMills.Construction.PeriodicLattice.SiteAtLevel s.L s.m s.K 0)), A.Finite)
end YangMills.Construction.Matrices.ComplexMatrix2
