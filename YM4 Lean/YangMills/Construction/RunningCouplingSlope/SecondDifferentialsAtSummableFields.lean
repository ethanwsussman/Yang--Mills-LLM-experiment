import YangMills.Construction.PeriodicOperators.SecondDifferentialsOfLogarithmsOfDeterminants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.SummableFields
open PeriodicOperators PeriodicOperators.LogDetSecondDerivs
def periodize (F : PeriodicData) (s : ℕ) (f : F.Carrier → ℂ) : F.QuotMod s → ℂ :=
  fun c => ∑' κ : {κ : F.Carrier // F.mkQuot s κ = c}, f κ
def SecondDerivConvergence : Prop :=
  ∀ F I : PeriodicData, IsPeriodic F → IsPeriodic I →
    ∀ T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I T →
      (∀ κ : InfiniteLattice.AmbientSpace,
        IsUnit (symbolHom I I (coeffZero F I I T) (toComplexVec κ) :
          Module.End ℂ (I.UnitQuot → ℂ))) →
      IsRealOnRealFields F I T →
      ∀ f g : F.Carrier → ℂ, Summable f → Summable g →
        ∃ l : ℂ, ∀ ε : ℝ, 0 < ε → ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
          ∀ (N : ℕ) (e : Fin N ≃ F.QuotMod s),
            ‖realLogAbsDetSecondDeriv F I T e (periodize F s f) (periodize F s g) - l‖ < ε
end YangMills.Construction.RunningCouplingSlope.SummableFields
end
