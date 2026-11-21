import YangMills.Construction.Towers.TheJetsOfTheFormulaOfTheRemainder
import YangMills.Construction.Towers.TheMassiveJets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.LogNumberInterpolation
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad
def UniformlyBoundedInverses {I : PeriodicData} (δ : ℝ) (T : ℝ → JetQuad I I) : Prop :=
  ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ s ∈ Icc (0 : ℝ) 1,
    (⨆ k ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse ((T s).f00 k))) ≤ C
def Claim : Prop :=
  ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ → ∀ I : PeriodicData, IsPeriodic I →
    ∀ A W : JetQuad I I, IsJet δ p A → IsJet δ p W →
      (∀ t ∈ Icc (0 : ℝ) 1, IsInvertibleJet δ p (unitShiftedPath A W t)) →
      (∀ τ ∈ Icc (0 : ℝ) 1, IsInvertibleJet δ p (addScalarJet (A.add W) τ)) →
      UniformlyBoundedInverses δ (unitShiftedPath A W) →
      UniformlyBoundedInverses δ (addScalarJet (A.add W)) →
        ContinuousOn (correctionIntegrand p A W) (Icc 0 1) ∧
          logNumber p (A.add W) =
            logNumber p (addScalarJet A 1) - traceNumber (unitShiftedInverse p A) -
                1 / 2 * traceNumber (invJetSq p (addScalarJet A 1)) +
              pathRemainder p A W
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.LogNumberInterpolation
end
