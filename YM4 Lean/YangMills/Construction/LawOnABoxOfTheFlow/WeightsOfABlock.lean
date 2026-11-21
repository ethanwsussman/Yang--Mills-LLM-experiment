import YangMills.Construction.LawOnABoxOfTheFlow.EventsOfABox
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxEvents
def blockWeightBoundsStatement : Prop :=
  ∀ (L : ℕ) [NeZero L], 2 ≤ L → ∀ (s m : ℕ) [NeZero m] (P : TorusFields.TorusPlaquette m)
    (o : TorusFields.TorusSite (WeightedResponses.fineSide L s m)),
    (∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite (WeightedResponses.fineSide L s m))),
        blockWeight L s P p ^ 2 ≤ 1) ∧
    ∀ p : TorusFields.TorusPlaquette (WeightedResponses.fineSide L s m), blockWeight L s P p ≠ 0 →
      ∀ z ∈ TorusFields.plaquetteVertices p.1 p.2.1 p.2.2,
        TorusFields.supDist z o ≤ L ^ s * TorusFields.supDist P.1 (ResponseInTheExpansion.siteAbove L s m o) + 4 * L ^ s
end YangMills.Construction.BoxEvents
end
