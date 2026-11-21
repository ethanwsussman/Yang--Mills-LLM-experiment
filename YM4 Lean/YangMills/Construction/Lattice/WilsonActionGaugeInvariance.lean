import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def WilsonActionGaugeInvariant : Prop :=
  ∀ L m K : ℕ, Odd L → 13 ≤ L → 0 < m → 0 < K →
    ∀ U ∈ gaugeFieldsAtLevel L m K 0, ∀ u : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2,
      IsGaugeMap compactGaugeGroup u → wilsonAction (gaugeTransform u U) = wilsonAction U
end YangMills.Construction.PeriodicLattice
