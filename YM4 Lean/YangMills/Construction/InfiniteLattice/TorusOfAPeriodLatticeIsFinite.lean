import YangMills.Construction.InfiniteLattice.PeriodLatticesToriAndTheirWilsonMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def PeriodQuotientFinite : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ Γ : PeriodSublattice a,
    Finite (LatticePoint a ⧸ Γ.periods) ∧ Finite Γ.QuotientLink ∧ Finite Γ.QuotientPlaquette
end YangMills.Construction.InfiniteLattice
