import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
def GaugeCovarianceOfHolonomy : Prop :=
  ∀ L m : ℕ, Odd L → 13 ≤ L → 0 < m → ∀ j : ℤ, -(m : ℤ) ≤ j →
    ∀ (ℬ : Set (Bond L m j)) (U : Bond L m j → ComplexMatrix2) (u u' : Site L m j → ComplexMatrix2),
      IsReversalClosed ℬ → IsGaugeField complexGaugeGroup ℬ U →
      IsGaugeMap complexGaugeGroup u → IsGaugeMap complexGaugeGroup u' →
      (IsGaugeField complexGaugeGroup ℬ (gaugeTransform u U) ∧
        (IsGaugeField compactGaugeGroup ℬ U → IsGaugeMap compactGaugeGroup u →
          IsGaugeField compactGaugeGroup ℬ (gaugeTransform u U)) ∧
        ∀ b ∈ ℬ, gaugeTransform u' (gaugeTransform u U) b =
          gaugeTransform (fun x => u' x * u x) U b) ∧
      (∀ (Γ : List (Bond L m j)) (x x' : Site L m j), IsBondPathFromTo Γ x x' →
        (∀ b ∈ Γ, b ∈ ℬ) →
        pathHolonomy (gaugeTransform u U) Γ = u x * pathHolonomy U Γ * (u x')⁻¹) ∧
      ∀ p : Plaquette L m j, (∀ b ∈ p.boundaryBonds, b ∈ ℬ) →
        plaquetteHolonomy (gaugeTransform u U) p =
          u p.origin * plaquetteHolonomy U p * (u p.origin)⁻¹
end YangMills.Construction.PeriodicLattice
