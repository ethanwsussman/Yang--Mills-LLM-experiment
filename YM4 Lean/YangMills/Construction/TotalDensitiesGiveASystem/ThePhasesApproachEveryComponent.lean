import YangMills.Construction.TotalDensitiesGiveASystem.PhasesOfALimitDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
open SystemsWithFiveBounds LimitTheorem SeparatedTuples
open InfiniteLattice (IsRegularConditionalByIntegrals smearedEnergyCumulant)
open TestSpaces (SepTupleOfCard)
def phasesApproachComponentsStatement : Prop :=
  ∀ (L : ℕ), Conventions.IsAdmissibleBlockingFactor L → ∀ (IsPair : ℕ+ → ℝ → Prop) (Q : PairSequence L IsPair)
    (S : CumulantFamily), (∀ j, 0 < Q.coupling j) → Q.Defines S →
    ∀ A : DecompositionData, A.IsCanonical (centredOf S) →
    ∀ (ξ : A.space) (n : ℕ), 2 ≤ n → ∀ X : SepTupleOfCard n,
    ∀ E : ∀ j, Set (Measure (FieldAt Q j)),
      (∀ j κ, IsRegularConditionalByIntegrals (Q.state j) κ → ∀ᵐ U ∂Q.state j, (κ U).1 ∈ E j) →
      ∃ ρ : ∀ j, Measure (FieldAt Q j), (∀ j, ρ j ∈ E j) ∧ (∀ j, IsProbabilityMeasure (ρ j)) ∧
        Tendsto (fun j => smearedEnergyCumulant (ρ j) X.1) atTop (𝓝 ((connectedFn (A.comp ξ) X : ℝ) : ℂ))
end YangMills.Construction.TotalDensitiesGiveASystem
end
