import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.BackgroundCoeffsNearZero
open YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn)
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ O : Set (Fin 4 → ℂ), IsOpen O ∧ (0 : Fin 4 → ℂ) ∈ O ∧ O ⊆ momentumPolydisc stripHalfWidth ∧
      (∀ q ∈ O, ∀ μ ρ : Fin 4, ∀ m ∈ PlaneWaves.freqBox L k,
        PlaneWaves.edgeFourierCoeff L k (responseAmplitude L k q μ) ρ m =
          backgroundCoeff L k q μ ρ m • Matrices.ComplexMatrix2.pauliFamily 2) ∧
      (∀ μ ρ : Fin 4, ∀ m ∈ PlaneWaves.freqBox L k,
        IsHolomorphicScalarIn O fun q => backgroundCoeff L k q μ ρ m) ∧
      ∃ C : ℝ, ∀ q ∈ O, ∀ μ ρ : Fin 4,
        (∀ m ∈ PlaneWaves.freqBox L k, m ≠ 0 →
          ‖backgroundCoeff L k q μ ρ m‖ ≤ C * ResponseProperties.euclidNorm q ^ 2) ∧
        ‖backgroundCoeff L k q μ ρ 0 - (if ρ = μ then 1 else 0)‖ ≤
          C * ResponseProperties.euclidNorm q
end YangMills.Construction.Tower.MassiveOpFunctions.BackgroundCoeffsNearZero
end
