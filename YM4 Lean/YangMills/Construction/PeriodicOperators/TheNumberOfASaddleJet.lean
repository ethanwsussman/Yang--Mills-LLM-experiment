import YangMills.Construction.PeriodicOperators.BlockMatricesAndCopiesOfIndexSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
def pairData (I₁ I₂ : PeriodicData) : Fin 2 → PeriodicData
  | 0 => I₁
  | 1 => I₂
section Saddle
variable {I₁ I₂ : PeriodicData}
def saddleBlocks (z : Fin 4 → ℂ) (X : JetQuad I₁ I₁) (Q : JetQuad I₁ I₂) :
    ∀ i j : Fin 2, JetQuad (pairData I₁ I₂ j) (pairData I₁ I₂ i)
  | 0, 0 => X
  | 0, 1 => JetQuad.transposeAt z Q
  | 1, 0 => Q
  | 1, 1 => JetQuad.zeroJet I₂ I₂
def saddleJet (z : Fin 4 → ℂ) (X : JetQuad I₁ I₁) (Q : JetQuad I₁ I₂) :
    JetQuad (PeriodicData.sigma (pairData I₁ I₂)) (PeriodicData.sigma (pairData I₁ I₂)) :=
  blockJet (pairData I₁ I₂) (saddleBlocks z X Q)
def subGramJet (z : Fin 4 → ℂ) (Ξ : JetQuad I₁ I₁) (Q : JetQuad I₁ I₂) : JetQuad I₁ I₁ :=
  Ξ.add (JetQuad.smul (-1) (JetQuad.mul z (JetQuad.transposeAt z Q) Q))
def schurJet (z : Fin 4 → ℂ) (Ξ : JetQuad I₁ I₁) (Q : JetQuad I₁ I₂) :
    JetQuad I₂ I₂ :=
  JetQuad.mul z (JetQuad.mul z Q (JetQuad.invJet z Ξ)) (JetQuad.transposeAt z Q)
end Saddle
namespace SaddleJetNumber
open JetQuad (IsInvertibleJet IsJet logNumber)
def Claim : Prop :=
  ∀ I₁ I₂ : PeriodicData, IsPeriodic I₁ → IsPeriodic I₂ →
    ∀ (δ : ℝ) (z : Fin 4 → ℂ), 0 < δ → z ∈ imStrip δ →
      ∀ (Ξ : JetQuad I₁ I₁) (Q : JetQuad I₁ I₂),
        IsInvertibleJet δ z Ξ → IsJet δ z Q → IsInvertibleJet δ z (schurJet z Ξ Q) →
          IsInvertibleJet δ z (saddleJet z (subGramJet z Ξ Q) Q) ∧
            logNumber z (saddleJet z (subGramJet z Ξ Q) Q) =
              logNumber z Ξ + logNumber z (schurJet z Ξ Q)
end SaddleJetNumber
end YangMills.Construction.PeriodicOperators
end
