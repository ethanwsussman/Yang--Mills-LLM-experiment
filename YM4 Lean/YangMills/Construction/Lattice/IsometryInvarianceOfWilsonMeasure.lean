import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def WilsonMeasureIsometryInvariant : Prop :=
  ∀ (L m K : ℕ) (β : ℝ), 1 < L → 0 < m → 0 < K →
    (∀ v : Site L m (K : ℤ), IsSublatticeIsometry (K : ℤ) (translateBy v)) ∧
    (∀ σ ∈ hyperoctahedralGroup L m, IsSublatticeIsometry (K : ℤ) σ) ∧
    ∀ σ : FourTorus L m ≃ FourTorus L m, IsSublatticeIsometry (K : ℤ) σ →
      (∀ b : Bond L m (K : ℤ),
        ((bondPreimage σ b).source : FourTorus L m) = σ.symm b.source ∧
        ((bondPreimage σ b).target : FourTorus L m) = σ.symm b.target) ∧
      (∀ U ∈ compactGaugeFields L m (K : ℤ),
        transportGaugeField σ U ∈ compactGaugeFields L m (K : ℤ)) ∧
      (wilsonGibbsMeasure L m K β).map (transportGaugeField σ) = wilsonGibbsMeasure L m K β
end PeriodicLattice
end YangMills.Construction
