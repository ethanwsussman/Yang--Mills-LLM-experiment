import YangMills.Construction.Towers.ChartAtTheTrivialConfigurationDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace IdentityExpChart
def AnalyticReadInExpChartStatement : Prop :=
  ∀ (σ τ : Type) [Fintype σ] [Nonempty σ] [Fintype τ] [Nonempty τ]
    (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless),
    RealAnalyticIffInExpChart σ τ β
end IdentityExpChart
end YangMills.Construction
