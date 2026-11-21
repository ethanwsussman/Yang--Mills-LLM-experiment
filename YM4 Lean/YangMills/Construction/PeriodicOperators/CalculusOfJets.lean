import YangMills.Construction.PeriodicOperators.RulesOfTheCalculusOfJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetCalculus
def Claim : Prop :=
  ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
    MulAssocNormLe δ p ∧ TransposeMulNorm δ p ∧ JetAlongHom δ p ∧
      TripleMulOfZeroPartZero δ p ∧ InvJetSpec δ p ∧ TraceNumberCommTranspose δ p ∧
      LogNumberMulAdd δ p ∧ BlockTriangularLogNumber δ p ∧ HasDerivLogNumber δ p
end YangMills.Construction.PeriodicOperators.JetCalculus
end
