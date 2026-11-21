import YangMills.Construction.LawByMomentsOfTheFlow.PotentialOfAPlaquetteByAGreenFunction
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
def greenAsHeatTimeIntegralStatement : Prop :=
  (∀ z : Fin 4 → ℤ, IntegrableOn (fun T => YangMills.Construction.FreeKernel.UnitLattice.latticeHeatKernel T z) (Set.Ioi 0)) ∧
    (∀ z : Fin 4 → ℤ, YangMills.Construction.FreeKernel.UnitLattice.latticeLaplacian latticeGreen z = if z = 0 then 1 else 0) ∧
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (μ : Fin 4) (z : Fin 4 → ℤ),
      |latticeGreen (z + Pi.single μ 1) - latticeGreen z| ≤
        c * (YangMills.Construction.FreeKernel.UnitLattice.l1Length z + 1) ^ (-3 : ℝ)
end YangMills.Construction.MomentLaw
end
