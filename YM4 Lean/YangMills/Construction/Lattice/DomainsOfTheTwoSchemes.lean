import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.GaugeFieldSpacesAndRealAnalyticMaps
import YangMills.Construction.Lattice.OneStepSchemes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K n : ℕ}
def HolomorphicOnAveragingDomain (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (Φ : (BondAtLevel L m K n → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2) : Prop :=
  (∃ _ : Fintype (PositiveBondOf (bondsInDoubleBlock c : Set (BondAtLevel L m K n))),
    Matrices.ComplexMatrix2.IsHolomorphicBetween
      (fun _ : PositiveBondOf (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) =>
        Matrices.ComplexMatrix2.FactorKind.group)
      (fun _ : Unit => Matrices.ComplexMatrix2.FactorKind.group)
      (restrictToPositive (bondsInDoubleBlock c) '' {W | IsSchemeAverageDefined s W c})
      fun v _ => Φ (extendFromPositive (bondsInDoubleBlock c) v)) ∧
    ∀ (N : ℕ) (ν : PositiveBondOf (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) ≃ Fin N)
      (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless),
      Coordinates.ComplexCoordinates.IsHolomorphicOnSL2Power β
        ((fun v => v ∘ ν.symm) ''
          (restrictToPositive (bondsInDoubleBlock c) '' {W | IsSchemeAverageDefined s W c}))
        fun X => Φ (extendFromPositive (bondsInDoubleBlock c) (X ∘ ν))
def AveragingDomainsOpenAndHolomorphic : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n < K →
    ∀ s : AveragingScheme,
    ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
      Matrices.ComplexMatrix2.IsRelativelyOpen
        (Matrices.ComplexMatrix2.complexifiedProduct fun _ :
          PositiveBondOf (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) =>
            Matrices.ComplexMatrix2.FactorKind.group)
        (restrictToPositive (bondsInDoubleBlock c) '' {W | IsSchemeAverageDefined s W c}) ∧
      (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
        ∀ x ∈ sitesInBlock (levelDepth K n) y,
          HolomorphicOnAveragingDomain s c fun W => contourHolonomy s W y x) ∧
      HolomorphicOnAveragingDomain s c fun W => schemeBlockAverage s W c
end PeriodicLattice
end YangMills.Construction
