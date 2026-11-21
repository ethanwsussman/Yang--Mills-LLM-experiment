import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
def SymbolCompClaim : Prop :=
  ∀ P Q R : PeriodicData, IsPeriodic P → IsPeriodic Q → IsPeriodic R →
    ∀ (K : Q.Carrier → P.Carrier → ℂ) (L : P.Carrier → R.Carrier → ℂ) (δ : ℝ),
      IsPeriodicKernel P Q K → IsDecayRate P Q K δ →
      IsPeriodicKernel R P L → IsDecayRate R P L δ →
        ∀ κ ∈ strictImStrip δ, SymbolSummableAt R Q (compKernel K L) κ ∧
          quotSymbol R Q (compKernel K L) κ =
            compKernel (quotSymbol P Q K κ) (quotSymbol R P L κ)
end PeriodicOperators
end YangMills.Construction
end
