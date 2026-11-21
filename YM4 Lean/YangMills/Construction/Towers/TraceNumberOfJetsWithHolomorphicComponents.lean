import YangMills.Construction.PeriodicOperators.SymbolsOnStrips
import YangMills.Construction.Towers.OperatorFunctionsOfTheScaledPictureDefs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.JetTraceHolomorphy
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions
open YangMills.Construction.PeriodicOperators.StripSymbols (openStripInterior)
def Claim : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ P : Set (Coordinates.ComplexCoordinates 4), IsOpen P → P ⊆ openStripInterior δ →
    ∀ I : PeriodicData, IsPeriodic I →
      ∀ T : Coordinates.ComplexCoordinates 4 → JetQuad I I, JetFamilyHolomorphic δ P T →
        (⨆ p ∈ P, JetQuad.jetNorm δ p (T p)) < ⊤ →
          Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) P
            fun p _ => JetQuad.traceNumber (T p)
end YangMills.Construction.Tower.FullSpace.JetTraceHolomorphy
end
