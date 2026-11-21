import YangMills.Construction.PeriodicOperators.ExponentialSumsTorusWavesAndComponentSets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetTransposition
open JetDomains
open JetQuad (IsJet EqAsJet)
def Holds : Prop :=
  ∀ P Q : PeriodicData, IsPeriodic P → IsPeriodic Q →
    ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
      (∀ T : JetQuad P Q, IsJet δ p T →
        ∀ U, AreNhds δ p U → HolomorphicOnDomains U T →
          ∃ V, AreNhds δ p V ∧ TransposeDefinedOn p U V ∧
            HolomorphicOnDomains V (JetQuad.transposeAt p T)) ∧
      ∀ T : JetQuad P Q, IsJet δ p T → IsJet δ p (JetQuad.transposeAt p T)
end YangMills.Construction.PeriodicOperators.JetTransposition
end
