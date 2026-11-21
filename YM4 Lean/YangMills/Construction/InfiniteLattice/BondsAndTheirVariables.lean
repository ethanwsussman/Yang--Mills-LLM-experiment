import YangMills.Construction.InfiniteLattice.LatticeOfACutoffAndTheVariablesOfASetOfBonds
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.CutoffLinks
def LinksAndTheirVariables.Statement : Prop :=
  ∀ c : CutoffData,
    ((∀ ℓ : Link c.spacing, Xor (ℓ ∈ c.links) (∃ ℓ' ∈ c.links, ℓ = Link.opposite ℓ')) ∧
      (∀ (x y : LatticePoint c.spacing) (μ ν : Fin 4),
        Link.forwardFrom x μ = Link.forwardFrom y ν → x = y ∧ μ = ν) ∧
      c.links.Countable) ∧
    (IsHomeomorph (fun U : GaugeField c.spacing => restrictField U c.links) ∧
      CompactSpace (GaugeField c.spacing) ∧
      TopologicalSpace.MetrizableSpace (GaugeField c.spacing) ∧
      CompactSpace (LinkVariables c.links) ∧
      TopologicalSpace.MetrizableSpace (LinkVariables c.links)) ∧
    (∀ (S : Set (Link c.spacing)) (hS : S ⊆ c.links) (E : Type) [TopologicalSpace E]
        (F : GaugeField c.spacing → E), ReadsLinks S F →
      (∃! f : LinkVariables S → E, ∀ U, F U = f (restrictField U S)) ∧
      ∀ f : LinkVariables S → E, (∀ U, F U = f (restrictField U S)) →
        f = F ∘ c.extendByOne hS ∧ (Continuous F → Continuous f)) ∧
    (∀ S : Set (Link c.spacing), S ⊆ c.links → S.Finite →
      {F : GaugeField c.spacing → ℂ | IsContinuousLocal F ∧ ReadsLinks S F} =
        {F | ∃ f ∈ continuousVariableFunctions S, F = liftToFields f}) ∧
    ((∀ S : Set (Link c.spacing), S ⊆ c.links → S.Finite →
        (∃ m : MetricSpace (LinkVariables S),
          (∀ V V' : LinkVariables S, m.dist V V' = variablesDist V V') ∧
          m.toUniformSpace.toTopologicalSpace =
            (inferInstance : TopologicalSpace (LinkVariables S))) ∧
        CompactSpace (LinkVariables S)) ∧
      (∀ (S S' : Set (Link c.spacing)) [Finite S] [Finite S'], S ⊆ c.links → S' ⊆ c.links →
        ∀ h : Disjoint S S',
          (∀ (V V' : LinkVariables S) (Y Y' : LinkVariables S'),
            variablesDist ((variablesUnionHomeomorph h).symm (V, Y))
                ((variablesUnionHomeomorph h).symm (V', Y')) =
              max (variablesDist V V') (variablesDist Y Y')) ∧
          (LinkVariables.haarMeasure ↥(S ∪ S')).map (variablesUnionHomeomorph h) =
            (LinkVariables.haarMeasure S).prod (LinkVariables.haarMeasure S'))) ∧
    (∀ (S : Set (Link c.spacing)) (hS : S ⊆ c.links),
      Continuous (fun U : GaugeField c.spacing => restrictField U S) ∧
      Continuous (c.extendByOne hS) ∧
      (∀ V : LinkVariables S, restrictField (c.extendByOne hS V) S = V) ∧
      ∀ (W : Set (Link c.spacing)) (hW : W ⊆ c.links), W.Finite →
        Continuous (fun p : LinkVariables W × GaugeField c.spacing =>
          c.replaceOn hW p.1 p.2) ∧
        (∀ (V : LinkVariables W) (U : GaugeField c.spacing),
          restrictField (c.replaceOn hW V U) W = V) ∧
        (S ∩ W = ∅ → ∀ (V : LinkVariables W) (U : GaugeField c.spacing),
          restrictField (c.replaceOn hW V U) S = restrictField U S))
end YangMills.Construction.CutoffLinks
