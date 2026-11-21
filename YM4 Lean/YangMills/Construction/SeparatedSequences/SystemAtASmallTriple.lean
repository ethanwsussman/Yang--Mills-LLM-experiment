import YangMills.Construction.Lattice.DifferencesOfTheSystemAtASmallTriple
import YangMills.Construction.SeparatedSequences.SystemAtTheTrivialTriple
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SeparatedSequences.SmallTripleSystem
def tripleRadius (L : ℕ) : ℝ :=
  min (SequenceTriples.smallTripleRadius L)
    (4 * SequenceTriples.variationConstant L * SeparatedSequences.TrivialTripleSystem.constant L *
      Real.exp (Lattice.siteNearnessRadius L))⁻¹
def inverseConstant (L : ℕ) : ℝ := 16 * SeparatedSequences.TrivialTripleSystem.constant L
variable {L m : ℕ} (S : SeparatedSequences.ScaleData) (Ω : ℕ → Set (PeriodicLattice.FourTorus L m))
end YangMills.Construction.SeparatedSequences.SmallTripleSystem
end
