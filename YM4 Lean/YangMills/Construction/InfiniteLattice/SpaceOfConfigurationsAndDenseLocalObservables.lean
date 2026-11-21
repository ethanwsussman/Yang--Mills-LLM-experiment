import YangMills.Construction.InfiniteLattice.StatesFunctionsAndTheWeakTopologyOfOneLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.GibbsAtFixedSpacing
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def GaugeFieldSpaceAndDenseLocal : Prop :=
  ∀ a : ℝ, 0 < a →
    CompactSpace (GaugeField a) ∧
    TopologicalSpace.MetrizableSpace (GaugeField a) ∧
    borel (GaugeField a) = linkSigma (Set.univ : Set (Link a)) ∧
    continuousLocalFunctions a ⊆ continuousFns a ∧
    (∀ F ∈ continuousLocalFunctions a, ∀ G ∈ continuousLocalFunctions a,
      F + G ∈ continuousLocalFunctions a ∧ F * G ∈ continuousLocalFunctions a) ∧
    (∀ (z : ℂ), ∀ F ∈ continuousLocalFunctions a, z • F ∈ continuousLocalFunctions a) ∧
    (∀ z : ℂ, (fun _ => z) ∈ continuousLocalFunctions a) ∧
    (∀ F ∈ continuousLocalFunctions a, (fun U => conj (F U)) ∈ continuousLocalFunctions a) ∧
    (∃ D : Set (GaugeField a → ℂ), D.Countable ∧ D ⊆ continuousLocalFunctions a ∧
      IsSupNormDenseIn D (continuousFns a)) ∧
    IsSupNormDenseIn (continuousLocalFunctions a) (continuousFns a) ∧
    IsSupNormDenseIn (continuousLocalFunctions a ∩ realContinuous a)
      (realContinuous a)
end YangMills.Construction.InfiniteLattice
end
