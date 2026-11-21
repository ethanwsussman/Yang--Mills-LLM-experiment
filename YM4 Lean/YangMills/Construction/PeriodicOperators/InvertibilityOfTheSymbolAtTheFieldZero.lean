import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.ZeroFieldInvertibility
open JetQuad (IsInvertibleJet)
def Claim : Prop :=
  ∀ F I : PeriodicData, IsPeriodic F → IsPeriodic I →
    ∀ T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I T →
      (∀ κ : InfiniteLattice.AmbientSpace,
        IsUnit (symbolHom I I (coeffZero F I I T) (toComplexVec κ) :
          Module.End ℂ (I.UnitQuot → ℂ))) →
      (∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ imStrip δ, ∀ εPlus εMinus : F.UnitQuot → ℂ,
        IsInvertibleJet δ p (jetAlong F I I T p εPlus εMinus)) ∧
      ∀ ρ R : ℝ, IsLocalWith F I I T ρ R → ∀ s : ℕ, 0 < s → 4 * R < s →
        IsUnit (linearMapOfEntries (descendMatrix I I s (periodicValue F I I T s 0)) :
          Module.End ℂ (I.QuotMod s → ℂ))
end YangMills.Construction.PeriodicOperators.ZeroFieldInvertibility
end
