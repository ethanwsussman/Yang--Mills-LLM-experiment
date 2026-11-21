import YangMills.Construction.InfiniteLattice.PeriodLatticesToriAndTheirWilsonMeasures
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def PeriodSublattice.minNonzeroNorm (Γ : PeriodSublattice a) : ℝ :=
  sInf {s | ∃ γ ∈ Γ.periods, γ ≠ 0 ∧ s = ‖(γ : AmbientSpace)‖}
def MinNonzeroNormTendsToInfinity (Γ : ℕ → PeriodSublattice a) : Prop :=
  Tendsto (fun i => (Γ i).minNonzeroNorm) atTop atTop
end YangMills.Construction.InfiniteLattice
end
