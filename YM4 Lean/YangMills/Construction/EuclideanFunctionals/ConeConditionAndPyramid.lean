import YangMills.Construction.EuclideanFunctionals.SymmetricEuclideanFunctional
import Mathlib
set_option autoImplicit false
open YangMills.Construction.EuclideanSpectral
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
theorem measurable_momCoord (j : Fin 3) : Measurable (momCoord j) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (j.succ : Fin 4)).continuous.measurable
def energyBelowMom (j : Fin 3) : BorelSubset 4 :=
  ⟨{p | energyCoord p < |momCoord j p|},
    measurableSet_lt measurable_energyCoord (measurable_momCoord j).abs⟩
def momentumPyramid : BorelSubset 4 :=
  ⟨{p | ∀ j : Fin 3, |momCoord j p| ≤ energyCoord p},
    by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j =>
        measurableSet_le (measurable_momCoord j).abs measurable_energyCoord⟩
namespace SymmEuclidFunctional
variable {c : SharpScale} {S : ConnFamily} (σ : SymmEuclidFunctional c S)
def EnergyBoundsMom (j : Fin 3) : Prop :=
  σ.osData.pvm (energyBelowMom j) = 0
def LightConeBound : Prop := σ.EnergyBoundsMom 0
end SymmEuclidFunctional
end YangMills.Construction.EuclideanFunctionals
