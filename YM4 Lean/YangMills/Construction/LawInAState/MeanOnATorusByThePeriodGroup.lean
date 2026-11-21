import YangMills.Construction.InequalityOnMirroredCopies.ArrayOnRectangularTori
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace LawInAState
open ChessboardTori ReflectedCopies
def TorusMeanViaPeriods.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.q = 0 → ∀ k : ℕ,
    0 < torusPartition g (cubicCounts D k) ∧
    ∀ F : D.GaugeField → ℂ, InfiniteLattice.IsBoundedObservable F →
      (∫ V, F V ∂InfiniteLattice.liftedWilsonMeasure D.L k D.K D.β) *
          (torusPartition g (cubicCounts D k) : ℂ) =
        ∫ V, F ((gridPeriods g (cubicCounts D k)).liftGaugeField V) *
            Complex.exp (-(D.β : ℂ) * ((gridPeriods g (cubicCounts D k)).wilsonAction V : ℂ))
          ∂(gridPeriods g (cubicCounts D k)).haarMeasure
end LawInAState
end YangMills.Construction
end
