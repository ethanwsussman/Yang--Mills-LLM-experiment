import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.Tempered
open PeriodicOperators (toComplexVec)
open PeriodicOperators.Tempered (IsTemperedFunctional hessianSymbol)
def MassiveFamilyTempered : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z →
    IsTemperedFunctional L (massiveFieldFamily L z) ∧
      ∀ (p : InfiniteLattice.AmbientSpace) (a : Fin 3) (μ ν : Fin 4),
        hessianSymbol L (massiveFieldFamily L z) μ ν (toComplexVec p) =
          logSymbol L z a μ ν (toComplexVec p)
end YangMills.Construction.Tower.MassiveOpFunctions.Tempered
end
