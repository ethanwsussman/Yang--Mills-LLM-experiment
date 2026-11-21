import YangMills.Construction.PeriodicOperators.RulesOfTheCalculusOfJets
import YangMills.Construction.Towers.TheFunctionOfTheMassiveJets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.PeriodicOperators
def invJetSq {I : PeriodicData} (p : Fin 4 → ℂ) (T : JetQuad I I) : JetQuad I I :=
  JetQuad.mul p (JetQuad.invJet p T) (JetQuad.invJet p T)
namespace MassJets
def DenominatorReBound (L k : ℕ) (z : ℝ) : Prop :=
  ∀ κ ∈ imStrip (2 * massWidth z), ∀ m ∈ Tower.PlaneWaves.freqBox L k,
    1 / 3 * z ≤ (Tower.PlaneWaves.symbolSquare L k (Tower.PlaneWaves.shiftedFreq κ m) + (z : ℂ)).re
def ShiftInvertibleBounded {I : PeriodicData} (z : ℝ) (p : Fin 4 → ℂ) (T : JetQuad I I) : Prop :=
  JetQuad.IsInvertibleJet (massWidth z) p (addScalarJet T z) ∧
    ∀ κ ∈ imStrip (2 * massWidth z),
      quotHomNorm (quotHomInverse ((addScalarJet T z).f00 κ)) ≤ ENNReal.ofReal (3 / z)
def MassDerivatives {I : PeriodicData} (p : Fin 4 → ℂ) (T : JetQuad I I) : Prop :=
  ContDiffOn ℝ 2 (fun z : ℝ => JetQuad.logNumber p (addScalarJet T z))
      (Ioi (25 * stripHalfWidth ^ 2)) ∧
    ∀ z ∈ Ioi (25 * stripHalfWidth ^ 2),
      deriv (fun y : ℝ => JetQuad.logNumber p (addScalarJet T y)) z =
          JetQuad.traceNumber (JetQuad.invJet p (addScalarJet T z)) ∧
        deriv (deriv fun y : ℝ => JetQuad.logNumber p (addScalarJet T y)) z =
          -JetQuad.traceNumber (invJetSq p (addScalarJet T z))
def MassJetsClaim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ z : ℝ, 0 < z →
      DenominatorReBound L k z ∧
        ∀ p ∈ momentumPolydisc (massWidth z), ∀ μPlus μMinus : Fin 4,
          ShiftInvertibleBounded z p (vertexOperatorJet L k p μPlus μMinus) ∧
            ShiftInvertibleBounded z p (edgeOperatorJet L k p μPlus μMinus)) ∧
    (∀ z : ℝ, 0 < z → 25 * stripHalfWidth ^ 2 ≤ z → massWidth z = stripHalfWidth) ∧
    (∀ z : ℝ, 1 / 40 ≤ z → massWidth z = stripHalfWidth) ∧
    ∀ p ∈ momentumPolydisc stripHalfWidth, ∀ μPlus μMinus : Fin 4,
      MassDerivatives p (edgeOperatorJet L k p μPlus μMinus) ∧
        MassDerivatives p (vertexOperatorJet L k p μPlus μMinus)
end MassJets
end YangMills.Construction.Tower.FullSpace.BackgroundJets
end
