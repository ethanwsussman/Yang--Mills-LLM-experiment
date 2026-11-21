import YangMills.Construction.InfiniteLattice.ColumnOverACell
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory
open InfiniteLattice (upperAlgebra observableSupNorm reflectionPairingRoot)
namespace MultipleReflections
def CellObservableBetweenHalfSpaces : Prop :=
  ∀ (D : Setup) (μ : Measure D.GaugeField), μ ∈ D.gibbsStates →
    ∀ (G : D.Grid) (k : Fin 4 → ℤ),
      (∀ A ∈ upperAlgebra (G.wallTimeHalf k 0),
        (∫ U, G.stackReflect k 0 A U * A U ∂μ).im = 0 ∧
          0 ≤ (∫ U, G.stackReflect k 0 A U * A U ∂μ).re) ∧
      (∀ F ∈ G.tileAlgebra k,
        ∀ A ∈ upperAlgebra (G.wallTimeHalf k 0), ∀ B ∈ upperAlgebra (G.wallTimeHalf k 0),
          ∀ ℓ : ℕ+ → PeriodicLattice.torusSides D.L, G.IsStackSideSequence ℓ →
            ‖∫ U, G.stackReflect k 0 B U * F U * (G.stackShift 1).actOn A U ∂μ‖ ≤
              G.limsupStackNorm k ℓ F * reflectionPairingRoot μ (G.wallTimeHalf k 0) B *
                reflectionPairingRoot μ (G.wallTimeHalf k 0) A) ∧
      (∀ A ∈ upperAlgebra (G.wallTimeHalf k 0), ∀ B ∈ upperAlgebra (G.wallTimeHalf k 0),
        ‖∫ U, G.stackReflect k 0 B U * (G.stackShift 1).actOn A U ∂μ‖ ≤
          reflectionPairingRoot μ (G.wallTimeHalf k 0) B *
            reflectionPairingRoot μ (G.wallTimeHalf k 0) A) ∧
      ∀ F ∈ G.tileAlgebra k, ∀ ℓ : ℕ+ → PeriodicLattice.torusSides D.L, G.IsStackSideSequence ℓ →
        G.limsupStackNorm k ℓ F ≤ observableSupNorm F
end MultipleReflections
end YangMills.Construction
