import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.BackgroundCoeffsOnRealPolydisc
open YangMills.Construction.PeriodicOperators (toComplexVec)
open YangMills.Construction.Tower.FullSpace.BackgroundJets
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ p : YangMills.Construction.InfiniteLattice.AmbientSpace,
      toComplexVec p ∈ momentumPolydisc stripHalfWidth →
      ∀ μ ρ : Fin 4, ∀ m ∈ PlaneWaves.freqBox L k,
        PlaneWaves.edgeFourierCoeff L k (responseAmplitude L k (toComplexVec p) μ) ρ m =
          backgroundCoeff L k (toComplexVec p) μ ρ m • Matrices.ComplexMatrix2.pauliFamily 2) ∧
    ∀ μ ρ : Fin 4, ∀ m ∈ PlaneWaves.freqBox L k,
      ContinuousOn
        (fun p : YangMills.Construction.InfiniteLattice.AmbientSpace =>
          backgroundCoeff L k (toComplexVec p) μ ρ m)
        {p | toComplexVec p ∈ momentumPolydisc stripHalfWidth}
end YangMills.Construction.Tower.MassiveOpFunctions.BackgroundCoeffsOnRealPolydisc
end
