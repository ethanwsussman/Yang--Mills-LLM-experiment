import YangMills.Construction.PeriodicOperators.ExponentialSumsTorusWavesAndComponentSets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.ZeroPartJets
open JetDomains
open JetQuad (IsJet EqAsJet)
def Claim : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
      (∀ T : I'.Carrier → I.Carrier → ℂ, IsPeriodicKernel I I' T →
        SymbolHolomorphicNear I I' (imStrip (2 * δ)) T → IsJet δ p (JetQuad.ofKernel I I' T)) ∧
      IsJet δ p (JetQuad.one I) ∧
      ∀ T : JetQuad I I, JetQuad.IsInvertibleJet δ p T →
        IsJet δ p (JetQuad.zeroPart T) ∧ IsJet δ p (JetQuad.zeroPartInv T) ∧
          EqAsJet δ p (JetQuad.mul p (JetQuad.zeroPartInv T) (JetQuad.zeroPart T))
            (JetQuad.one I) ∧
          EqAsJet δ p (JetQuad.mul p (JetQuad.zeroPart T) (JetQuad.zeroPartInv T))
            (JetQuad.one I)
end YangMills.Construction.PeriodicOperators.ZeroPartJets
end
