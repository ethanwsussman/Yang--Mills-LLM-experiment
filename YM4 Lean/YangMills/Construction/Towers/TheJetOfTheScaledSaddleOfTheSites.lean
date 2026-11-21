import YangMills.Construction.PeriodicOperators.JetsOnADisjointSumAndOnTheUnionOfAPair
import YangMills.Construction.Towers.TheJetsOfTheFormulaOfTheRemainder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad (EqAsJet)
open YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets
def rescaledVertexSaddle (L k : ℕ) : ((remainderIndex L k).Carrier → ℂ) →
    (ghostIndices L k).Carrier → (ghostIndices L k).Carrier → ℂ :=
  fun f => (rescaledOperators L k (gaugeFieldOfForm L k f)).saddleDelta
namespace VertexSaddleJet
def LocalWithBlockJet : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    IsLocalOpFun (remainderIndex L k)
        (PeriodicData.sigma (pairData (colourVertices L k 0) (colourVertices L k k)))
        (PeriodicData.sigma (pairData (colourVertices L k 0) (colourVertices L k k)))
        (readOnSigma (rescaledVertexSaddle L k)) ∧
      ∀ (δ : ℝ) (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4), 0 < δ → p ∈ imStrip δ →
        EqAsJet δ p (jetAlongResponse L k (readOnSigma (rescaledVertexSaddle L k)) p μPlus μMinus)
          (saddleJet p (subGramJet p (vertexMiddleJet L k p μPlus μMinus)
            (vertexSmoothingJet L k p μPlus μMinus)) (vertexSmoothingJet L k p μPlus μMinus))
end VertexSaddleJet
end YangMills.Construction.Tower.FullSpace.BackgroundJets
end
