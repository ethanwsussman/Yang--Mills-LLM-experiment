import YangMills.Construction.LawInAState.DataOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
open InfiniteLattice (AmbientSpace)
def unitTorusObservablesIntegrableStatement : Prop :=
  ∀ (L K : ℕ) [NeZero L], Odd L → 3 ≤ L → 1 ≤ K → ∀ (β : ℝ) (p : ℕ) (φ : Fin p → AmbientSpace → ℝ),
    (∀ i, InfiniteLattice.IsBoundedBorelCompactlySupported (φ i)) →
      Integrable (fun U => ∏ i, smearedObservable L K (φ i) U) (unitTorusMeasure L K β)
end YangMills.Construction.StateLaws
end
