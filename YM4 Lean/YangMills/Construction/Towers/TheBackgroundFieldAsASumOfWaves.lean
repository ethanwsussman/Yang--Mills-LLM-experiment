import YangMills.Construction.Towers.TheDilationOfTheMassiveFields
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.WaveExpansion
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.MassiveOpFunctions.Scaling
open YangMills.Construction.Tower.FullSpace.BackgroundJets
def BackgroundFieldWaveSum : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ p : InfiniteLattice.AmbientSpace, toComplexVec p ∈ momentumPolydisc stripHalfWidth →
      ∀ μ : Fin 4, ∀ ι : (colourEdges L k 0).Carrier,
        blochWave (colourEdges L k 0) (toComplexVec p) (scaledResponseField L k (toComplexVec p) μ) ι =
          ((Tower.finestMesh L k : ℝ) : ℂ) * ∑ m ∈ Tower.PlaneWaves.freqBox L k, ∑ ρ : Fin 4,
            backgroundCoeff L k (toComplexVec p) μ ρ m *
              thirdColourWave L k (shiftedMomentum p m) ρ ι
end YangMills.Construction.Tower.MassiveOpFunctions.WaveExpansion
end
