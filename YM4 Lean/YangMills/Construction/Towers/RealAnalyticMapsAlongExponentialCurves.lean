import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.Tower
def AnalyticAlongExpCurves.Statement : Prop :=
  ∀ L n k j j' : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k → j' ≤ k →
    ∀ (U B : Edge L n k j → Matrices.ComplexMatrix2) (𝒩 : Set (Edge L n k j → Matrices.ComplexMatrix2))
      (F : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2),
      U ∈ fieldSpace L n k j → U ∈ 𝒩 → B ∈ edgeFormSpace L n k j → IsAnalyticFieldMap 𝒩 F →
      ∃ I : Set ℝ, IsOpenIntervalAroundZero I ∧
        (∀ t ∈ I, PeriodicLattice.expTwist ((t : ℂ) • B) U ∈ 𝒩) ∧
        ∀ (b : Edge L n k j') (r s : Fin 2),
          ContDiffOn ℝ ∞ (fun t : ℝ => F (PeriodicLattice.expTwist ((t : ℂ) • B) U) b r s) I
end YangMills.Construction.Tower
end
