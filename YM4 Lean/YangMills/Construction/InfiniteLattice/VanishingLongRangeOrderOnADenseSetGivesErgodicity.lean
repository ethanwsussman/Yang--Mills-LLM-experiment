import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import YangMills.Construction.InfiniteLattice.RepresentativesAndThePlateauForm
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.LatticePhases.ShiftErgodicityCriterion
def Statement : Prop :=
  ∀ (D : Setup) (ρ : ProbMeasure (GaugeField D.mesh)) (𝒮 : Set C(GaugeField D.mesh, ℂ)),
    IsShiftInvariant ρ.toMeasure →
    (∀ G : C(GaugeField D.mesh, ℂ), ∀ ε : ℝ, 0 < ε →
      ∃ A ∈ 𝒮, uniformSup (fun B => G B - A B) < ε) →
    (∀ A ∈ 𝒮, plateauVariance ρ.toMeasure (fun B => A B) = 0) →
    IsShiftErgodic ρ.toMeasure
end YangMills.Construction.LatticePhases.ShiftErgodicityCriterion
end
