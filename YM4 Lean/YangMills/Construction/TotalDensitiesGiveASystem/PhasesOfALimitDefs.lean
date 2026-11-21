import YangMills.Construction.InfiniteLattice.RegularConditionalProbabilitiesByIntegrals
import YangMills.Construction.InfiniteLattice.RepresentativeOfASeparatedTupleCentredAtAState
import YangMills.Construction.SystemsWithFiveBounds.TheoremOverASystemWithFiveBounds
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
variable {L : ℕ} {IsPair : ℕ+ → ℝ → Prop}
abbrev FieldAt (Q : SystemsWithFiveBounds.PairSequence L IsPair) (j : ℕ+) : Type :=
  InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (((Q.cutoff j : ℕ)) : ℤ))
def IsConditionalKernel (Q : SystemsWithFiveBounds.PairSequence L IsPair)
    (κ : ∀ j, FieldAt Q j →
      InfiniteLattice.GaugeFieldProbability (PeriodicLattice.meshSize L (((Q.cutoff j : ℕ)) : ℤ))) : Prop :=
  ∀ j, InfiniteLattice.IsRegularConditionalByIntegrals (Q.state j) (κ j)
def centredMean (Q : SystemsWithFiveBounds.PairSequence L IsPair) (j : ℕ+) (ρ : Measure (FieldAt Q j))
    (X : DisjointTuples.DisjointTuple) : ℝ :=
  ∫ U, CenteredRepresentatives.centeredRep L (Q.cutoff j) (Q.state j) X U ∂ρ
def phaseMoment (Q : SystemsWithFiveBounds.PairSequence L IsPair)
    (κ : ∀ j, FieldAt Q j →
      InfiniteLattice.GaugeFieldProbability (PeriodicLattice.meshSize L (((Q.cutoff j : ℕ)) : ℤ)))
    (X : DisjointTuples.DisjointTuple) (Y : List DisjointTuples.DisjointTuple) (j : ℕ+) : ℝ :=
  ∫ U, centredMean Q j (κ j U).1 X * (Y.map fun Z => centredMean Q j (κ j U).1 Z).prod ∂Q.state j
end YangMills.Construction.TotalDensitiesGiveASystem
end
