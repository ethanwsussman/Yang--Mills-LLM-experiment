import YangMills.Construction.PeriodicOperators.SymbolsOnStrips
import YangMills.Construction.Towers.OperatorFunctionsOfTheScaledPictureDefs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.JetClosure
open PeriodicOperators
open ScaledOperatorFunctions
open StripSymbols (openStripInterior)
def JetOpsClosed : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ P : Set (Coordinates.ComplexCoordinates 4), IsOpen P →
    P ⊆ openStripInterior δ →
    ∀ I I' I'' : PeriodicData, IsPeriodic I → IsPeriodic I' → IsPeriodic I'' →
      (∀ T S : Coordinates.ComplexCoordinates 4 → JetQuad I I', JetFamilyHolomorphic δ P T →
        JetFamilyHolomorphic δ P S → JetFamilyHolomorphic δ P fun p => (T p).add (S p)) ∧
      (∀ (T : Coordinates.ComplexCoordinates 4 → JetQuad I I')
          (S : Coordinates.ComplexCoordinates 4 → JetQuad I'' I),
        JetFamilyHolomorphic δ P T → JetFamilyHolomorphic δ P S →
          JetFamilyHolomorphic δ P fun p => JetQuad.mul p (T p) (S p)) ∧
      (∀ T : Coordinates.ComplexCoordinates 4 → JetQuad I I', JetFamilyHolomorphic δ P T →
        JetFamilyHolomorphic δ P fun p => JetQuad.transposeAt p (T p))
end YangMills.Construction.Tower.FullSpace.JetClosure
end
