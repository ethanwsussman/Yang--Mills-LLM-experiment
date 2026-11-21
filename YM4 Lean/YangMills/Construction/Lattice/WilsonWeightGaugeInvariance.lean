import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def WilsonWeightGaugeInvariance.statement : Prop :=
  ∀ (L m K : ℕ) (β : ℝ), 1 < L → 0 < m → 0 < K →
    (∀ U ∈ compactGaugeFields L m (K : ℤ), ∀ p,
      plaquetteCost U p ∈ Icc (0 : ℝ) 2 ∧
      (∀ k : ℕ, (Matrices.ComplexMatrix2.fullTrace
          (pathHolonomy U (p.boundaryBonds.rotate k))).re =
        (Matrices.ComplexMatrix2.fullTrace (plaquetteHolonomy U p)).re) ∧
      pathHolonomy U (reversePath p.boundaryBonds) = (plaquetteHolonomy U p)⁻¹ ∧
      (plaquetteHolonomy U p)⁻¹ = (plaquetteHolonomy U p).conjTranspose ∧
      (Matrices.ComplexMatrix2.fullTrace (pathHolonomy U (reversePath p.boundaryBonds))).re =
        (Matrices.ComplexMatrix2.fullTrace (plaquetteHolonomy U p)).re) ∧
    ContinuousOn (boltzmannWeight β) (compactGaugeFields L m (K : ℤ)) ∧
    (∀ U ∈ compactGaugeFields L m (K : ℤ), 0 < boltzmannWeight β U) ∧
    Integrable (boltzmannWeight β) (productHaarMeasure L m (K : ℤ)) ∧
    0 < partitionFunction L m K β ∧
    IsProbabilityMeasure (productHaarMeasure L m (K : ℤ)) ∧
    productHaarMeasure L m (K : ℤ) (compactGaugeFields L m (K : ℤ))ᶜ = 0 ∧
    IsProbabilityMeasure (wilsonGibbsMeasure L m K β) ∧
    wilsonGibbsMeasure L m K β (compactGaugeFields L m (K : ℤ))ᶜ = 0 ∧
    ∀ g : Site L m (K : ℤ) → Matrices.ComplexMatrix2, IsGaugeMap compactGaugeGroup g →
      (∀ U ∈ compactGaugeFields L m (K : ℤ),
        gaugeTransform g U ∈ compactGaugeFields L m (K : ℤ) ∧
        (∀ p, plaquetteHolonomy (gaugeTransform g U) p =
            g p.origin * plaquetteHolonomy U p * (g p.origin)⁻¹ ∧
          plaquetteCost (gaugeTransform g U) p = plaquetteCost U p) ∧
        wilsonAction (gaugeTransform g U) = wilsonAction U ∧
        boltzmannWeight β (gaugeTransform g U) = boltzmannWeight β U) ∧
      (wilsonGibbsMeasure L m K β).map (gaugeTransform g) = wilsonGibbsMeasure L m K β
end PeriodicLattice
end YangMills.Construction
