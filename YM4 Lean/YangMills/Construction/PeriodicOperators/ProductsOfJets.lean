import YangMills.Construction.PeriodicOperators.ExponentialSumsTorusWavesAndComponentSets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetProducts
open JetDomains
open JetQuad (IsJet EqAsJet)
def Claim : Prop :=
  ∀ I I' I'' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    IsPeriodic I'' → ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
      (∀ (T : JetQuad I I') (S : JetQuad I'' I), IsJet δ p T → IsJet δ p S →
        ∀ O O', AreNhds δ p O → AreNhds δ p O' →
          HolomorphicOnDomains O T → HolomorphicOnDomains O' S →
            ∃ N, AreNhds δ p N ∧ MulDefinedOn p O O' N ∧
              HolomorphicOnDomains N (JetQuad.mul p T S)) ∧
      ∀ (T : JetQuad I I') (S : JetQuad I'' I), IsJet δ p T → IsJet δ p S →
        IsJet δ p (JetQuad.mul p T S)
end YangMills.Construction.PeriodicOperators.JetProducts
end
