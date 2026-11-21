import YangMills.Construction.PeriodicOperators.ExponentialSumsTorusWavesAndComponentSets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.StripJetNorms
open JetDomains
def Claim : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
      (imStrip δ ⊆ stripAddShift δ p ∧ imStrip δ ⊆ stripSubShift δ p) ∧
        ∀ T : JetQuad I I', JetQuad.IsJet δ p T → SupsFinite δ p T
end YangMills.Construction.PeriodicOperators.StripJetNorms
end
