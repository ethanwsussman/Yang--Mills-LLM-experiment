import YangMills.Construction.Towers.TheFunctionOfTheMassiveJets
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.TorusMomenta
open PeriodicOperators (toComplexVec dualLattice)
open PeriodicOperators.Tempered (hessianSymbol)
open FullSpace.BackgroundJets
def MassiveLogFnAtTorusMomenta : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ z : ℝ, 0 < z → ∀ n : ℕ, 0 < n →
    ∀ p ∈ dualLattice (2 * L ^ n), toComplexVec p ∈ momentumPolydisc (massWidth z) →
      ∀ μPlus μMinus : Fin 4,
        massiveLogFn L k (toComplexVec p) μPlus μMinus z =
          (((finestMesh L k : ℝ) : ℂ) ^ 2)⁻¹ *
            ∑ m ∈ PlaneWaves.freqBox L k, ∑ ρ : Fin 4, ∑ σ : Fin 4,
              hessianSymbol L (massiveFieldFamily L (finestMesh L k ^ 2 * z)) ρ σ
                  (fun μ => ((finestMesh L k : ℝ) : ℂ) *
                    PlaneWaves.shiftedFreq (toComplexVec p) m μ) *
                backgroundCoeff L k (toComplexVec p) μPlus ρ m *
                backgroundCoeff L k (-toComplexVec p) μMinus σ (-m)
end YangMills.Construction.Tower.MassiveOpFunctions.TorusMomenta
end
