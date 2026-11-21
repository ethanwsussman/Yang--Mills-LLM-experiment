import YangMills.Construction.Matrices.GaugeFixingConstantValues
import YangMills.Construction.Matrices.GaugeFixingNormaliser
import YangMills.Construction.Parameters.OrderOfChoice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ParameterChoice
structure CouplingCeilingTie (N : ExternalConstants) : Prop where
  isGaugeFixingCeiling : ∀ (A₀ : ℝ) (p : ℕ),
    Matrices.ComplexMatrix2.GaugeFixingParameters A₀ p →
      ∃ r ε b : ℝ, Matrices.ComplexMatrix2.IsGaugeFixingCeiling A₀ p r ε b (N.normaliserCeiling A₀ p)
end YangMills.Construction.ParameterChoice
end
