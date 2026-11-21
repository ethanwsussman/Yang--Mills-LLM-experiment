import YangMills.Construction.Lattice.GaugeConfigSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ConfigSpaces
open BorelKernels FaddeevPopov
universe u v w
variable {L m K : ℕ} {𝔅 : Finset (GradedBond L m K)} {𝒴 : Type u} [MeasurableSpace 𝒴]
section Pushforwards
variable {𝕍 : Type v} [MeasurableSpace 𝕍]
structure IsPushforwardPresentation (τ : ComplexMeasure 𝕍)
    (ν : FiniteComplexMeasure (ConfigSpace 𝔅 𝒴)) (q : ConfigSpace 𝔅 𝒴 → 𝕍) : Prop where
  configSpace : IsConfigSpaceData 𝔅 𝒴
  measurable : IsBorelMeasurable q
  eq_map : τ = ν.map q
end Pushforwards
end YangMills.Construction.PeriodicLattice.ConfigSpaces
end
