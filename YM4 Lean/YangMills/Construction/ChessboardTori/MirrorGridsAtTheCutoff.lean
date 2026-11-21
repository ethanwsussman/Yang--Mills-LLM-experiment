import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ChessboardSetup
variable (D : ChessboardSetup)
def linkAlgebra (O : Set AmbientSpace) : Set (D.GaugeField → ℂ) :=
  {F | ∃ Φ : (D.positiveLinksOn O → Conventions.StandingParameters.gaugeGroup) → ℂ,
    Measurable Φ ∧ (∃ C : ℝ, ∀ u, ‖Φ u‖ ≤ C) ∧ ∀ U, F U = Φ fun b => U.1 b.1}
theorem isBoundedObservable_of_mem_linkAlgebra {O : Set AmbientSpace} {F : D.GaugeField → ℂ}
    (hF : F ∈ D.linkAlgebra O) : InfiniteLattice.IsBoundedObservable F := by
  obtain ⟨Φ, hΦ, ⟨C, hC⟩, e⟩ := hF
  have hm : Measurable fun U : D.GaugeField => fun b : D.positiveLinksOn O => U.1 b.1 :=
    measurable_pi_iff.mpr fun b =>
      (show Continuous fun U : D.GaugeField => U.1 b.1 from
        (continuous_apply b.1).comp continuous_subtype_val).measurable
  have hFe : F = Φ ∘ fun U : D.GaugeField => fun b : D.positiveLinksOn O => U.1 b.1 := funext e
  rw [hFe]
  exact ⟨hΦ.comp hm, C, fun U => hC _⟩
def openCellAlgebra (S : Set AmbientSpace) : Set (D.GaugeField → ℂ) :=
  D.linkAlgebra (interior S)
end ChessboardSetup
end ChessboardTori
end YangMills.Construction
end
