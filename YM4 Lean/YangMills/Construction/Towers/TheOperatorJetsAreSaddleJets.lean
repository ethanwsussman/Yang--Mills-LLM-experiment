import YangMills.Construction.PeriodicOperators.TheNumberOfASaddleJet
import YangMills.Construction.Towers.TheJetsOfTheFormulaOfTheRemainder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad
variable (L k : ℕ) (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4)
def edgeSaddleJet :
    JetQuad (PeriodicData.sigma (pairData (colourEdges L k 0) (colourEdges L k k)))
      (PeriodicData.sigma (pairData (colourEdges L k 0) (colourEdges L k k))) :=
  saddleJet p (subGramJet p (edgeMiddleJet L k p μPlus μMinus) (edgeSmoothingJet L k p μPlus μMinus))
    (edgeSmoothingJet L k p μPlus μMinus)
def vertexSaddleJet :
    JetQuad (PeriodicData.sigma (pairData (colourVertices L k 0) (colourVertices L k k)))
      (PeriodicData.sigma (pairData (colourVertices L k 0) (colourVertices L k k))) :=
  saddleJet p
    (subGramJet p (vertexMiddleJet L k p μPlus μMinus) (vertexSmoothingJet L k p μPlus μMinus))
    (vertexSmoothingJet L k p μPlus μMinus)
def backgroundTriple (hL : 0 < L) (q : Fin 4 → ℂ) (μ : Fin 4) :
    (fieldPeriodicData L k hL).UnitQuot → ℂ :=
  tripleAmplitude L k hL (backgroundResponseSymbol L k q (axisPauliElement μ 2)) 0 0
namespace OperatorJetsSaddle
def Claim : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ p ∈ momentumPolydisc stripHalfWidth, ∀ μPlus μMinus : Fin 4,
      IsInvertibleJet stripHalfWidth p (edgeSaddleJet L k p μPlus μMinus) →
      IsInvertibleJet stripHalfWidth p (vertexSaddleJet L k p μPlus μMinus) →
        IsJointInvertibilityWidth L k hL stripHalfWidth ∧
          logNumber p
              (vectorJet L k hL p (backgroundTriple L k hL p μPlus)
                (backgroundTriple L k hL (-p) μMinus)) =
            logNumber p (edgeSaddleJet L k p μPlus μMinus) ∧
          logNumber p
              (ghostJet L k hL p (backgroundTriple L k hL p μPlus)
                (backgroundTriple L k hL (-p) μMinus)) =
            logNumber p (vertexSaddleJet L k p μPlus μMinus)
end OperatorJetsSaddle
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets
end
