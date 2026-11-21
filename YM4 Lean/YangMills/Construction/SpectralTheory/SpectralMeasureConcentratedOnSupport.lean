import YangMills.Construction.SpectralTheory.SpectralMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.SpectralTheory.ProjectionMeasure
variable {n : ℕ} [NeZero n] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
theorem isClosed_support (E : ProjectionMeasure n H) : IsClosed E.support :=
  (isOpen_sUnion fun _ hU => hU.1).isClosed_compl
structure SupportLaws (E : ProjectionMeasure n H) : Prop where
  isFiniteMeasure : ∀ v : H, IsFiniteMeasure (E.spectralValueMeasure v)
  spectralValueMeasure_univ : ∀ v : H, E.spectralValueMeasure v univ = ENNReal.ofReal (‖v‖ ^ 2)
  eq_zero_iff : ∀ A : BorelSets n, E A = 0 ↔ ∀ v : H, E.spectralValue v A = 0
  vanishesOn_of_subset : ∀ A B : BorelSets n, B.1 ⊆ A.1 → E.VanishesOn A → E.VanishesOn B
  vanishesOn_iUnion : ∀ (ι : Type) [Countable ι] (A : ι → BorelSets n),
    (∀ k, E.VanishesOn (A k)) →
      E.VanishesOn ⟨⋃ k, (A k).1, MeasurableSet.iUnion fun k => (A k).2⟩
  isConcentratedOn_support : E.IsConcentratedOn ⟨E.support, E.isClosed_support.measurableSet⟩
  isGreatest_compl_support :
    IsGreatest {U | ∃ hU : IsOpen U, E.VanishesOn ⟨U, hU.measurableSet⟩} E.supportᶜ
  support_subset_iff : ∀ (C : Set (Fin n → ℝ)) (hC : IsClosed C),
    E.support ⊆ C ↔ E ⟨Cᶜ, hC.isOpen_compl.measurableSet⟩ = 0
end YangMills.Construction.SpectralTheory.ProjectionMeasure
namespace YangMills.Construction.SpectralSupport
open YangMills.Construction.SpectralTheory
def ConcentratedOnSupportTheorem : Prop :=
  ∀ (n : ℕ) [NeZero n] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (E : ProjectionMeasure n H), E.SupportLaws
end YangMills.Construction.SpectralSupport
