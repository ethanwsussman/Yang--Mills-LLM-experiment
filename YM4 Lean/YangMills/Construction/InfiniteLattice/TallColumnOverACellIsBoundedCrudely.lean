import YangMills.Construction.InfiniteLattice.ColumnOverACell
import Mathlib
set_option autoImplicit false
open MeasureTheory
open YangMills.Construction.InfiniteLattice (upperAlgebra observableSupNorm)
noncomputable section
namespace YangMills.Construction.MultipleReflections
def TallStackOverTileBoundedCrudely : Prop :=
  ∀ (D : Setup) (μ : Measure D.GaugeField), μ ∈ D.gibbsStates →
    ∀ (G : D.Grid) (k : Fin 4 → ℤ), ∀ F ∈ G.tileAlgebra k,
      ∀ A ∈ upperAlgebra (G.wallTimeHalf k 0),
        ∀ s : ℕ+ → PeriodicLattice.torusSides D.L, G.IsStackSideSequence s →
          ∃ k₀ : ℕ, ∀ n' : ℕ, 1 ≤ n' →
            ‖G.stackCorrelation k μ F A (D.L ^ k₀ * n')‖ ≤
              observableSupNorm A ^ 2 * G.limsupStackNorm k s F ^ (2 * (D.L ^ k₀ * n'))
end YangMills.Construction.MultipleReflections
end
