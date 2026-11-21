import YangMills.Construction.PeriodicOperators.RulesOfTheCalculusOfJets
import YangMills.Construction.PeriodicOperators.SymbolsOnStrips
import YangMills.Construction.Towers.OperatorFunctionsOfTheScaledPictureDefs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
open YangMills.Construction.PeriodicOperators
open ScaledOperatorFunctions
open StripSymbols (openStripInterior)
def InvertibleJetInverseHolomorphic : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ P : Set (Coordinates.ComplexCoordinates 4), IsOpen P →
    P ⊆ openStripInterior δ →
    ∀ I : PeriodicData, IsPeriodic I →
      ∀ T : Coordinates.ComplexCoordinates 4 → JetQuad I I, JetFamilyHolomorphic δ P T →
        (∀ p ∈ P, JetQuad.IsInvertibleJet δ p (T p)) →
          JetFamilyHolomorphic δ P fun p => JetQuad.invJet p (T p)
end YangMills.Construction.Tower.FullSpace
end
