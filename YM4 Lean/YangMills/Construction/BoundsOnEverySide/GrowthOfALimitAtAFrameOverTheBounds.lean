import YangMills.Construction.BoundsOnEverySide.SeparatedLimitsUnderABound
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
open AmbientPoints (TupleMapFamily separatedTuples)
namespace BoundsOnEverySide
def GibbsStateSequence.TendsToFamily {L : ℕ} {s : Conventions.StandingParameters}
    (Q : GibbsStateSequence L) (S : TupleMapFamily s .euclidean) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (f : separatedTuples s .euclidean n),
    Tendsto (fun k => InfiniteLattice.smearedEnergyCumulant (Q.gibbs k) f.1) atTop
      (𝓝 (S n hn f : ℂ))
end BoundsOnEverySide
end YangMills.Construction
end
