import YangMills.Construction.Lattice.HistoriesCreationAndAges
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.ParameterChoice
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CubesOfStep
variable {c : ChoiceUpToDegreeConstants} {m K : ℕ} {x : ℕ → ℝ} {D : ℕ → Type}
def LabelHistory.creationCubesAt : ∀ {k : ℕ}, LabelHistory c m K x D k → ℕ → Set (FourTorus c.L m)
  | _, .initial, _ => ∅
  | k + 1, .extend h s _, t => if t = k + 1 then s.creationCubes h.finalLabel else h.creationCubesAt t
def LabelHistory.largeFieldRegionsAt : ∀ {k : ℕ}, LabelHistory c m K x D k → ℕ →
    Set (Set (FourTorus c.L m))
  | _, .initial, _ => ∅
  | k + 1, .extend h _ o, t =>
    if t = k + 1 then o.outcome.largeFieldSet else h.largeFieldRegionsAt t
end YangMills.Construction.PeriodicLattice.CubesOfStep
