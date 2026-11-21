import YangMills.Construction.GrowingTori.DefinitionsForSequencesOfGrowingTori
import YangMills.Construction.InfiniteLattice.LimitsAlongTheCutoffs
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.FirstPassageSeqs
open InfiniteLattice
structure FirstPassageSequence (P : GrowingTori.GrowthParameters) (g : ℝ) where
  point : ℕ+ → GrowingTori.FirstPassagePoint P g
  cutoff_tendsto : CutoffLimits.CutoffsTendToTop fun n => (point n).K
namespace FirstPassageSequence
variable {P : GrowingTori.GrowthParameters} {g : ℝ} (S : FirstPassageSequence P g)
abbrev cutoff (n : ℕ+) : ℕ+ := (S.point n).K
abbrev coupling (n : ℕ+) : ℝ := (S.point n).β
abbrev mesh (n : ℕ+) : ℝ := PeriodicLattice.meshSize P.L ((S.cutoff n : ℕ) : ℤ)
abbrev Fields (n : ℕ+) : Type := GaugeField (S.mesh n)
abbrev gibbsStates (n : ℕ+) : Set (Measure (S.Fields n)) :=
  periodicGibbsSet P.L (S.cutoff n) (S.coupling n)
end FirstPassageSequence
end YangMills.Construction.FirstPassageSeqs
end
