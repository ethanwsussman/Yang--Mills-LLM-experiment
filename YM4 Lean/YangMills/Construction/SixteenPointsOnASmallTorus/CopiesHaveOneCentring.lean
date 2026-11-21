import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenPointsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def reflectedCentringConstStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => ∀ (Ξ β : ℝ) (K κ : ℕ) (α : ℕ → ℝ) (ρ H : ℝ) (Λ : NNReal)
    (f : TestFunctions.EuclideanFourSpace → ℝ),
    IsAdmissibleFlow (Tb.stepParameters y) Ξ β K → 2 ≤ κ → 0 < ρ → ρ ≤ cellLength Tb.side K κ / 4 →
    IsLocalizedSource (cellLength Tb.side K κ) ρ H Λ f →
    ∀ k : Fin 4 → Fin 2, reflectedCentring (Tb.stepParameters y) β α K κ ρ (fun μ => (k μ : ℕ)) f =
      centring (Tb.stepParameters y) β α K κ ρ f
end YangMills.Construction.SmallTorusCopies
end
