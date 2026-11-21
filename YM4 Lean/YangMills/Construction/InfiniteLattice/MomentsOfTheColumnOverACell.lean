import YangMills.Construction.InfiniteLattice.ColumnOverACell
import Mathlib
set_option autoImplicit false
open MeasureTheory
open YangMills.Construction.InfiniteLattice (upperAlgebra reflectionPairingRoot)
noncomputable section
namespace YangMills.Construction.MultipleReflections
def StackCorrelationsLogConvex : Prop :=
  ∀ (D : Setup) (μ : Measure D.GaugeField), μ ∈ D.gibbsStates →
    ∀ (G : D.Grid) (k : Fin 4 → ℤ), ∀ F ∈ G.tileAlgebra k,
      (∀ A ∈ upperAlgebra (G.wallTimeHalf k 0),
        (∀ n : ℕ, (G.stackCorrelation k μ F A n).im = 0 ∧ 0 ≤ (G.stackCorrelation k μ F A n).re) ∧
        G.stackCorrelation k μ F A 0 =
          ((reflectionPairingRoot μ (G.wallTimeHalf k 0) A ^ 2 : ℝ) : ℂ) ∧
        ∀ n : ℕ, 1 ≤ n →
          (G.stackCorrelation k μ F A n).re ^ 2 ≤
            (G.stackCorrelation k μ F A (n - 1)).re * (G.stackCorrelation k μ F A (n + 1)).re) ∧
      ∀ A ∈ upperAlgebra (G.wallTimeHalf k 0), ∀ B ∈ upperAlgebra (G.wallTimeHalf k 0),
        ‖∫ U, G.stackReflect k 0 B U * F U * (G.stackShift 1).actOn A U ∂μ‖ ^ 2 ≤
          (G.stackCorrelation k μ F B 1).re * reflectionPairingRoot μ (G.wallTimeHalf k 0) A ^ 2
end YangMills.Construction.MultipleReflections
end
