import YangMills.Construction.PeriodicOperators.ExponentialSumsTorusWavesAndComponentSets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetAddSMul
open JetDomains
open JetQuad (IsJet EqAsJet)
def Claim : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
      (∀ T S : JetQuad I I', IsJet δ p T → IsJet δ p S →
        ∀ U U', AreNhds δ p U → AreNhds δ p U' →
          HolomorphicOnDomains U T → HolomorphicOnDomains U' S →
            ∃ V, AreNhds δ p V ∧ AddDefinedOn U U' V ∧
              HolomorphicOnDomains V (JetQuad.add T S)) ∧
      (∀ T S : JetQuad I I', IsJet δ p T → IsJet δ p S → IsJet δ p (JetQuad.add T S)) ∧
      (∀ (a : ℂ) (T : JetQuad I I'), IsJet δ p T →
        ∀ U, AreNhds δ p U → HolomorphicOnDomains U T →
          ∃ V, AreNhds δ p V ∧ SMulDefinedOn U V ∧
            HolomorphicOnDomains V (JetQuad.smul a T)) ∧
      ∀ (a : ℂ) (T : JetQuad I I'), IsJet δ p T → IsJet δ p (JetQuad.smul a T)
end YangMills.Construction.PeriodicOperators.JetAddSMul
end
