import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import YangMills.Construction.TotalDensitiesGiveASystem.TopStatementDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
structure ContainsPairStates (ℓ : TorusLumps.StepParameters) (Bs g : ℝ)
    (Z : ∀ K : ℕ+, ℝ → Set (Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize ℓ.side (((K : ℕ)) : ℤ))))) : Prop where
  limitPoint_mem : ∀ K β, TotalDensitySystem.IsFirstPassagePair ℓ Bs g K β → ∀ ν,
    InfiniteLattice.IsInfiniteVolumeLimit ℓ.side K β ν → ν ∈ Z K β
  ergodicComponents_mem : ∀ K β, TotalDensitySystem.IsFirstPassagePair ℓ Bs g K β →
    ∀ (hL : Conventions.IsAdmissibleBlockingFactor ℓ.side) (hβ : 0 < β)
    (ν : InfiniteLattice.periodicGibbsSet ℓ.side K β), InfiniteLattice.IsInfiniteVolumeLimit ℓ.side K β ν.1 →
      SystemsWithFiveBounds.AEErgodicComponentsIn ⟨ℓ.side, hL, K, β, hβ⟩ ν (Z K β)
def ComponentsAreLimitsOfStates : Prop :=
  HoldsAtAdmissibleParameters fun T y => ForSmallCoupling fun g =>
    ∀ Z : ∀ K : ℕ+, ℝ → Set (Measure (InfiniteLattice.GaugeField
        (PeriodicLattice.meshSize (T.stepParameters y).side (((K : ℕ)) : ℤ)))),
      ContainsPairStates (T.stepParameters y) (2 * T.B) g Z →
      ∀ (Q : SystemsWithFiveBounds.PairSequence (T.stepParameters y).side
          (TotalDensitySystem.IsFirstPassagePair (T.stepParameters y) (2 * T.B) g))
        (S : LimitTheorem.CumulantFamily),
        Q.Defines S → ∀ A : SeparatedTuples.DecompositionData, A.IsCanonical (LimitTheorem.centredOf S) →
          ∀ (ξ : A.space) (n : ℕ), 2 ≤ n → ∀ X : TestSpaces.SepTupleOfCard n, ∃ (φ : ℕ → ℕ+)
            (ρ : ∀ l, Measure (InfiniteLattice.GaugeField
              (PeriodicLattice.meshSize (T.stepParameters y).side (((Q.cutoff (φ l) : ℕ)) : ℤ)))),
            Tendsto φ atTop atTop ∧ (∀ l, ρ l ∈ Z (Q.cutoff (φ l)) (Q.coupling (φ l))) ∧
            (∀ l, IsProbabilityMeasure (ρ l)) ∧
            Tendsto (fun l => InfiniteLattice.smearedEnergyCumulant (ρ l) X.1) atTop
              (𝓝 ((LimitTheorem.connectedFn (A.comp ξ) X : ℝ) : ℂ))
end YangMills.Construction.TotalDensities
end
