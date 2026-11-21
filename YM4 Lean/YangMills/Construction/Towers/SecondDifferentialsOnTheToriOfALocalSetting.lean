import YangMills.Construction.PeriodicOperators.TracesOfKernelsAtUnitFields
import YangMills.Construction.Towers.TheSumOverThePointsOfTheSecondDerivativesOfTheLogarithmicDensity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
open OperatorCalculus UnitLatticeL2 AbelianFieldDensity OneLoopNotation
open PeriodicOperators PeriodicOperators.UnitFieldTraces PeriodicOperators.LogDetSecondDerivs
def PeriodicHessianLimit : Prop :=
  ∀ (F I : PeriodicData) (E : Type) (Φ : E → F.Carrier) (src : E → InfiniteLattice.AmbientSpace)
    (m m' : ℕ) (z C : ℝ) (T : (E → ℝ) → BddOp (IndexL2 I.Carrier))
    (S : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ),
    IsPeriodic F → IsPeriodic I → 0 < z → 0 < C →
    IsLocalOpFun F I I S →
    IsLocalExpansionSetting I.pos src m m' z C T →
    (∀ (e e' : E) (s t : ℝ) (i' i : I.Carrier),
      S ((s : ℂ) • siteIndicator F (Φ e) + (t : ℂ) • siteIndicator F (Φ e')) i' i =
        matrixEntry (addScalar (T (twoBondField e e' s t)) z) i' i) →
    ∀ (e e' : E) (ε : ℝ), 0 < ε → ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      ∀ (N : ℕ) (σ : Fin N ≃ F.QuotMod s),
        ‖logDetSecondDeriv F I S σ (quotIndicator F s (Φ e)) (quotIndicator F s (Φ e')) -
          variationTrace T z e e'‖ < ε
end YangMills.Construction.Tower.LocalFamilies
end
