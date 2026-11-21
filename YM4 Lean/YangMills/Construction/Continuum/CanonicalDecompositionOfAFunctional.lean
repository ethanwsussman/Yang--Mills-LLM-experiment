import YangMills.Construction.Continuum.IteratedFarTranslationLimits
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
noncomputable section
namespace YangMills.Construction.SeparatedTuples
def measureSupport {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] (μ : Measure Y) : Set Y :=
  (⋃₀ {O | IsOpen O ∧ μ O = 0})ᶜ
structure DecompositionData where
  space : Type
  [topologicalSpace : TopologicalSpace space]
  [measurableSpace : MeasurableSpace space]
  [borelSpace : BorelSpace space]
  law : Measure space
  comp : space → TupleFunctional
attribute [instance] DecompositionData.topologicalSpace DecompositionData.measurableSpace
  DecompositionData.borelSpace
namespace DecompositionData
structure IsCanonical (A : DecompositionData) (σ : TupleFunctional) : Prop where
  compact : CompactSpace A.space
  metrizable : TopologicalSpace.MetrizableSpace A.space
  isProb : IsProbabilityMeasure A.law
  measureSupport_eq : measureSupport A.law = Set.univ
  comp_permInvariant : ∀ ξ, (A.comp ξ).IsPermInvariant
  comp_entrywiseLinear : ∀ ξ, (A.comp ξ).IsEntrywiseLinear
  continuous_comp : ∀ X : SepTuple, Continuous fun ξ => A.comp ξ X
  comp_injective : Function.Injective A.comp
  iterLimits_exist : ∀ (X : SepTuple) (Y : List SepTuple), IterLimitsExist σ X Y Set.univ
  integral_comp_prod : ∀ (X : SepTuple) (Y : List SepTuple),
    ∫ ξ, A.comp ξ X * (Y.map fun Z => A.comp ξ Z).prod ∂A.law =
      iteratedLimitAtInfinity σ X Y Set.univ
def Isomorphic (A B : DecompositionData) : Prop :=
  ∃ h : A.space ≃ₜ B.space, A.law.map h = B.law ∧
    ∀ ξ, B.comp (h ξ) = A.comp ξ
end DecompositionData
end YangMills.Construction.SeparatedTuples
