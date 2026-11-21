import YangMills.Construction.Towers.TheFunctionOfTheMassiveJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.ContinuousOnRealPolydisc
open FullSpace.BackgroundJets
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ m : ℝ, 0 < m →
    ∀ νPos νNeg : Fin 4,
    ContinuousOn
      (fun q : InfiniteLattice.AmbientSpace =>
        massiveLogFn L k (PeriodicOperators.toComplexVec q) νPos νNeg m)
      {q | PeriodicOperators.toComplexVec q ∈ momentumPolydisc (massWidth m)}
end YangMills.Construction.Tower.MassiveOpFunctions.ContinuousOnRealPolydisc
end
