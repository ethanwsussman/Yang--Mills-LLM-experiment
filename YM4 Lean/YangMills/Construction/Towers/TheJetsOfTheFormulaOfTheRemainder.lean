import YangMills.Construction.PeriodicOperators.NormsOfJetsAndAffineFamiliesOfInvertibleJets
import YangMills.Construction.Towers.TheFunctionOfTheMassiveJets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets
open PeriodicOperators
open PeriodicOperators.JetQuad
open PeriodicOperators.JetNormsAffine (affinePath)
section Interpolation
variable {I : PeriodicData}
def unitShiftedPath (A W : JetQuad I I) (t : ℝ) : JetQuad I I :=
  affinePath (addScalarJet A 1) W t
def unitShiftedInverse (p : Fin 4 → ℂ) (A : JetQuad I I) : JetQuad I I :=
  invJet p (addScalarJet A 1)
def perturbedInverse (p : Fin 4 → ℂ) (A W : JetQuad I I) (τ : ℝ) : JetQuad I I :=
  invJet p (addScalarJet (A.add W) τ)
def correctionIntegrand (p : Fin 4 → ℂ) (A W : JetQuad I I) (τ : ℝ) : ℂ :=
  ((1 - τ : ℝ) : ℂ) ^ 2 *
      traceNumber
        (mul p (mul p (unitShiftedInverse p A) (unitShiftedInverse p A)) (perturbedInverse p A W τ)) -
    traceNumber (mul p (mul p (unitShiftedInverse p A) W) (perturbedInverse p A W τ)) -
    ((1 - τ : ℝ) : ℂ) *
      traceNumber
        (mul p (mul p (mul p (unitShiftedInverse p A) (unitShiftedInverse p A)) W)
          (perturbedInverse p A W τ))
def pathRemainder (p : Fin 4 → ℂ) (A W : JetQuad I I) : ℂ :=
  (∫ t in (0 : ℝ)..1, traceNumber (mul p (invJet p (unitShiftedPath A W t)) W)) -
    ∫ τ in (0 : ℝ)..1, correctionIntegrand p A W τ
end Interpolation
def openPolydisc (δ : ℝ) : Set (Fin 4 → ℂ) := {p | ∀ μ, ‖p μ‖ < δ}
variable (L k : ℕ) (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4)
def edgeCorrectionJet : JetQuad (colourEdges L k 0) (colourEdges L k 0) :=
  (mul p (transposeAt p (edgeSmoothingJet L k p μPlus μMinus)) (edgeSmoothingJet L k p μPlus μMinus)).add
    (smul (-1)
      (mul p
        (mul p (covDerivJet L k p μPlus μMinus)
          (mul p (transposeAt p (vertexSmoothingJet L k p μPlus μMinus))
            (vertexSmoothingJet L k p μPlus μMinus)))
        (transposeAt p (covDerivJet L k p μPlus μMinus))))
def vertexCorrectionJet : JetQuad (colourVertices L k 0) (colourVertices L k 0) :=
  mul p (transposeAt p (vertexSmoothingJet L k p μPlus μMinus)) (vertexSmoothingJet L k p μPlus μMinus)
def edgeMiddleJet : JetQuad (colourEdges L k 0) (colourEdges L k 0) :=
  (edgeOperatorJet L k p μPlus μMinus).add (edgeCorrectionJet L k p μPlus μMinus)
def vertexMiddleJet : JetQuad (colourVertices L k 0) (colourVertices L k 0) :=
  (vertexOperatorJet L k p μPlus μMinus).add (vertexCorrectionJet L k p μPlus μMinus)
def edgeConstraintJet : JetQuad (colourEdges L k k) (colourEdges L k k) :=
  mul p (mul p (edgeSmoothingJet L k p μPlus μMinus) (invJet p (edgeMiddleJet L k p μPlus μMinus)))
    (transposeAt p (edgeSmoothingJet L k p μPlus μMinus))
def vertexConstraintJet : JetQuad (colourVertices L k k) (colourVertices L k k) :=
  mul p (mul p (vertexSmoothingJet L k p μPlus μMinus) (invJet p (vertexMiddleJet L k p μPlus μMinus)))
    (transposeAt p (vertexSmoothingJet L k p μPlus μMinus))
def edgeRemainder : ℂ :=
  pathRemainder p (edgeOperatorJet L k p μPlus μMinus)
    (edgeCorrectionJet L k p μPlus μMinus)
def vertexRemainder : ℂ :=
  pathRemainder p (vertexOperatorJet L k p μPlus μMinus)
    (vertexCorrectionJet L k p μPlus μMinus)
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets
end
