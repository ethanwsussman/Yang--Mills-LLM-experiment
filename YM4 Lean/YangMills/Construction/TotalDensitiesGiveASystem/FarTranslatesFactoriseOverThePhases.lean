import YangMills.Construction.TotalDensitiesGiveASystem.PhasesOfALimitDefs
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
open SystemsWithFiveBounds LimitTheorem SeparatedTuples
def latticePoint (z : Fin 4 → ℤ) : InfiniteLattice.AmbientSpace := fun μ => (z μ : ℝ)
def farTranslatesFactorStatement : Prop :=
  ∀ (L : ℕ), Conventions.IsAdmissibleBlockingFactor L → ∀ (IsPair : ℕ+ → ℝ → Prop) (Q : PairSequence L IsPair)
    (S : CumulantFamily), (∀ j, 0 < Q.coupling j) → Q.Defines S → ∀ κ, IsConditionalKernel Q κ →
    ∀ (X Y : SepTuple) (W : List SepTuple) (ε : ℝ), 0 < ε → ∃ R : ℕ, ∀ z : Fin 4 → ℤ, (∃ μ, (R : ℤ) ≤ |z μ|) → ∀ j,
      |∫ U, (centredMean Q j (κ j U).1 (SepTuple.juxt X (push (SeparatedTuples.translate (latticePoint z)) Y)) -
            centredMean Q j (κ j U).1 X * centredMean Q j (κ j U).1 Y) *
          (W.map fun Z => centredMean Q j (κ j U).1 Z).prod ∂Q.state j| ≤ ε
end YangMills.Construction.TotalDensitiesGiveASystem
end
