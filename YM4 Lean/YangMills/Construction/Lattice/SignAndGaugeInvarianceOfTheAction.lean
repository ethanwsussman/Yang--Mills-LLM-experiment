import YangMills.Construction.Lattice.RegionSequenceExtension
import YangMills.Construction.Lattice.TowersAndMinimalConfigurations
import YangMills.Construction.Lattice.WeightedWilsonActions
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
def ActionNonnegAndGaugeInvariant : Prop :=
  ∀ L m K : ℕ, Odd L → 13 ≤ L → 0 < m → 0 < K →
    (∀ (Ω₀ : Set (FourTorus L m)) (U : BondAtLevel L m K 0 → ComplexMatrix2)
        (u : SiteAtLevel L m K 0 → ComplexMatrix2),
      YangMills.Construction.RegionSequences.IsTorusRegion Ω₀ →
      IsGaugeField compactGaugeGroup (bondsInside Ω₀) U →
      (∀ x ∈ (sitesIn Ω₀ : Set (SiteAtLevel L m K 0)), u x ∈ compactGaugeGroup) →
      (∀ p ∈ (plaquettesInside Ω₀ : Set (PlaquetteAtLevel L m K 0)),
        0 ≤ plaquetteCost U p ∧ plaquetteCost (gaugeTransform u U) p = plaquetteCost U p ∧
          0 ≤ plaquetteEnergy U p ∧
          plaquetteEnergy (gaugeTransform u U) p = plaquetteEnergy U p) ∧
      0 ≤ actionInside K Ω₀ U ∧ actionInside K Ω₀ (gaugeTransform u U) = actionInside K Ω₀ U ∧
      0 ≤ interiorEnergy Ω₀ U ∧ interiorEnergy Ω₀ (gaugeTransform u U) = interiorEnergy Ω₀ U) ∧
    ∀ (U : BondAtLevel L m K 0 → ComplexMatrix2) (u : SiteAtLevel L m K 0 → ComplexMatrix2),
      U ∈ gaugeFieldsAtLevel L m K 0 → IsGaugeMap compactGaugeGroup u →
      0 ≤ wilsonAction U ∧ wilsonAction (gaugeTransform u U) = wilsonAction U
end YangMills.Construction.PeriodicLattice
