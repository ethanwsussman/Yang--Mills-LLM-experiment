import YangMills.Construction.InfiniteLattice.PeriodLatticesToriAndTheirWilsonMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
namespace PeriodSublattice
variable (Γ : PeriodSublattice 1)
theorem lift_apply_positive (U : Γ.QuotientField) (l : PositiveLink 1) :
    Γ.lift U l.1 = U (Γ.linkClass l) :=
  dif_pos l.2
def linkClassImage (S : Set (Link 1)) : Set Γ.QuotientLink :=
  {c | ∃ l : PositiveLink 1, l.1 ∈ S ∧ c = Γ.linkClass l}
variable {Γ}
def integralOf (μ : Measure Γ.QuotientField) (f : Γ.QuotientField → ℂ) : ℂ :=
  ∫ U, f U ∂μ
def IsHomeomorphInvariant (μ : Measure Γ.QuotientField)
    (h : Γ.QuotientField ≃ₜ Γ.QuotientField) : Prop :=
  ∀ f : C(Γ.QuotientField, ℂ), integralOf μ (f ∘ h) = integralOf μ f
end PeriodSublattice
end InfiniteLattice
end YangMills.Construction
