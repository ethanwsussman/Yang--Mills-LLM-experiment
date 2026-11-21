import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.Lattice.TowersAndMinimalConfigurations
import YangMills.Construction.Lattice.WeightedWilsonActions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace IsometryCovariance
variable {L m : ℕ} {j : ℤ}
def CarriesHolonomies (σ : FourTorus L m ≃ FourTorus L m) (B : Set (Bond L m j))
    (U : Bond L m j → Matrices.ComplexMatrix2) : Prop :=
  IsReversalClosed (bondImage σ '' B) ∧
    IsGaugeField compactGaugeGroup (bondImage σ '' B) (transportGaugeField σ U) ∧
    ∀ γ : List (Bond L m j), IsBondPath γ → (∀ b ∈ γ, b ∈ B) →
      pathHolonomy (transportGaugeField σ U) (pathImage σ γ) = pathHolonomy U γ
def CarriesPlaquette (σ : FourTorus L m ≃ FourTorus L m) (s : ℤˣ)
    (U : Bond L m j → Matrices.ComplexMatrix2) (p : Plaquette L m j) : Prop :=
  (∃ γ : List (Bond L m j), γ <:+: p.boundaryBonds ∧
    plaquetteHolonomy (transportGaugeField σ U) (plaquetteImage σ p) =
      pathHolonomy U γ * plaquetteHolonomy U p ^ (s : ℤ) * (pathHolonomy U γ)⁻¹) ∧
  plaquetteCost (transportGaugeField σ U) (plaquetteImage σ p) = plaquetteCost U p ∧
  plaquetteEnergy (transportGaugeField σ U) (plaquetteImage σ p) =
    plaquetteEnergy U p ∧
  Matrices.ComplexMatrix2.operatorNorm
      (plaquetteHolonomy (transportGaugeField σ U) (plaquetteImage σ p) - 1) =
    Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1)
def CarriesWeightedEnergies (σ : FourTorus L m ≃ FourTorus L m)
    (U : Bond L m j → Matrices.ComplexMatrix2) : Prop :=
  (∀ w : Plaquette L m j → ℂ,
    plaquetteWeightedEnergy (transportPlaquetteFunction σ w) (transportGaugeField σ U) =
      plaquetteWeightedEnergy w U) ∧
  (∀ w : FourTorus L m → ℂ,
    barycenterWeightedEnergy (transportTorusFunction σ w) (transportGaugeField σ U) =
      barycenterWeightedEnergy w U) ∧
  ∀ (E : Type) [AddCommMonoid E] [Module ℝ E] (f : FourTorus L m → E),
    smearedObservable (transportTorusFunction σ f) (transportGaugeField σ U) =
      smearedObservable f U
def CarriesContourMean (σ : FourTorus L m ≃ FourTorus L m)
    (U : Bond L m (j + 1) → Matrices.ComplexMatrix2)
    (y : Site L m j) (x : Site L m (j + 1)) : Prop :=
  Matrices.ComplexMatrix2.familyDiameter (contourHolonomies (transportGaugeField σ U)
      (sitePreimage σ.symm y) (sitePreimage σ.symm x)) =
    Matrices.ComplexMatrix2.familyDiameter (contourHolonomies U y x) ∧
  (HasContourMean (transportGaugeField σ U)
      (sitePreimage σ.symm y) (sitePreimage σ.symm x) ↔ HasContourMean U y x) ∧
  (HasContourMean U y x →
    meanContourHolonomy (transportGaugeField σ U)
      (sitePreimage σ.symm y) (sitePreimage σ.symm x) = meanContourHolonomy U y x)
def Statement : Prop :=
  ∃ s : SignedFrame → Fin 4 → Fin 4 → ℤˣ,
    ∀ L m : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    ∀ i : ℤ, -(m : ℤ) ≤ i → ∀ σ ∈ latticeIsometries L m i,
      (∀ j : ℤ, i ≤ j →
        (∀ (B : Set (Bond L m j)) (U : Bond L m j → Matrices.ComplexMatrix2),
          IsReversalClosed B → IsGaugeField compactGaugeGroup B U →
            CarriesHolonomies σ B U ∧
            ∀ p : Plaquette L m j, (∀ b ∈ p.boundaryBonds, b ∈ B) →
              CarriesPlaquette σ (s (linearComponent σ) p.firstAxis p.secondAxis) U p) ∧
        (∀ (i' : ℤ) (Ω : Set (FourTorus L m)) (U : Bond L m j → Matrices.ComplexMatrix2),
          i ≤ i' → IsPartitionRegion i' Ω →
          IsGaugeField compactGaugeGroup (bondsInside Ω) U →
            interiorEnergy (σ '' Ω) (transportGaugeField σ U) = interiorEnergy Ω U) ∧
        (∀ U ∈ compactGaugeFields L m j, CarriesWeightedEnergies σ U) ∧
        ∀ (y : Site L m j) (x : Site L m (j + 1)) (B : Set (Bond L m (j + 1)))
          (U : Bond L m (j + 1) → Matrices.ComplexMatrix2),
          x ∈ sitesInBlock (j + 1) y → IsReversalClosed B → IsGaugeField compactGaugeGroup B U →
          (∀ γ ∈ contourSet y x, ∀ b ∈ γ, b ∈ B) → CarriesContourMean σ U y x) ∧
      ∀ (K : ℕ) (i' : ℤ) (Ω : Set (FourTorus L m)) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2),
        i ≤ levelDepth K 0 → i ≤ i' → IsPartitionRegion i' Ω →
        IsGaugeField compactGaugeGroup (bondsInside Ω) U →
          actionInside K (σ '' Ω) (transportGaugeField σ U) = actionInside K Ω U
end IsometryCovariance
end PeriodicLattice
end YangMills.Construction
