import YangMills.Construction.Towers.TheJetsOfTheFormulaOfTheRemainder
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.MiddleJetsInvertible
open PeriodicOperators
open PeriodicOperators.JetQuad
def InvertibleOnStrip {I : PeriodicData} (C : ℝ) (p : Fin 4 → ℂ) (T : JetQuad I I) : Prop :=
  IsInvertibleJet stripHalfWidth p T ∧
    ∀ κ ∈ imStrip (2 * stripHalfWidth),
      quotHomNorm (quotHomInverse (T.f00 κ)) ≤ ENNReal.ofReal C
def MiddleJetsInvertibleClaim : Prop :=
  ∃ C : ℝ, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ p ∈ momentumPolydisc stripHalfWidth, ∀ μPlus μMinus : Fin 4,
      (∀ t ∈ Icc (0 : ℝ) 1,
        InvertibleOnStrip C p
            (unitShiftedPath (edgeOperatorJet L k p μPlus μMinus)
              (edgeCorrectionJet L k p μPlus μMinus) t) ∧
          InvertibleOnStrip C p
            (unitShiftedPath (vertexOperatorJet L k p μPlus μMinus)
              (vertexCorrectionJet L k p μPlus μMinus) t) ∧
          InvertibleOnStrip C p (addScalarJet (edgeMiddleJet L k p μPlus μMinus) t) ∧
          InvertibleOnStrip C p (addScalarJet (vertexMiddleJet L k p μPlus μMinus) t)) ∧
        InvertibleOnStrip C p (edgeMiddleJet L k p μPlus μMinus) ∧
        InvertibleOnStrip C p (vertexMiddleJet L k p μPlus μMinus) ∧
        InvertibleOnStrip C p (edgeConstraintJet L k p μPlus μMinus) ∧
        InvertibleOnStrip C p (vertexConstraintJet L k p μPlus μMinus)
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.MiddleJetsInvertible
end
