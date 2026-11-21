import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.ObjectsOfThePivotCorrection
import Mathlib
open Set
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Conventions
namespace PeriodicLattice
def PivotBondsLieApart : Prop :=
  ∀ L m K k : ℕ, IsAdmissibleBlockingFactor L → 0 < m → k < K →
    ∀ (c : ↥(coarsePositiveBonds L m K k)) (μ : Fin 4),
      (c : BondAtLevel L m K (k + 1)).target - (c : BondAtLevel L m K (k + 1)).source =
        unitStep L m (levelDepth K (k + 1)) μ → PivotPlacement c μ
end PeriodicLattice
end YangMills.Construction
end
