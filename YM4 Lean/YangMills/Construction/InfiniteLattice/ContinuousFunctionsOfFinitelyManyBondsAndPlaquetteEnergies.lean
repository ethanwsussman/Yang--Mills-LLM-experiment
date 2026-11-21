import YangMills.Construction.InfiniteLattice.ObservablesHypercubicLatticeMapsAndHyperplanes
import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def linkEndpoints {a : ℝ} (M : Set (Link a)) : Set AmbientSpace :=
  {x | ∃ b ∈ M, x = (b.initial : AmbientSpace) ∨ x = (b.terminal : AmbientSpace)}
def ContinuousLocalAndFaceEnergies.Statement : Prop :=
  (∀ M : Set (Link 1), IsLinkSet M → M.Finite →
    ∀ H : GaugeField 1 → ℂ, Continuous H → DependsOnlyOn M H →
      H ∈ continuousLocalFunctions 1 ∧ H ∈ regionObservables 1 (linkEndpoints M) ∧
        observableSupport H ⊆ M) ∧
  (∀ p : ElementaryPlaquette 1,
    (fun U : GaugeField 1 => (faceEnergy U p : ℂ)) ∈ continuousLocalFunctions 1 ∧
      DependsOnlyOn p.linkSet (fun U : GaugeField 1 => (faceEnergy U p : ℂ)) ∧
      ∀ U : GaugeField 1, 0 ≤ faceEnergy U p ∧ faceEnergy U p ≤ 2) ∧
  (∀ Λ : Set (Link 1), IsLinkSet Λ → Λ.Finite → (facesMeeting Λ).Finite)
end YangMills.Construction.InfiniteLattice
