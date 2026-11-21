import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower
variable {L n k j : ℕ}
def IsDiffAtZeroPath (δ : ℝ → Edge L n k j → Matrices.ComplexMatrix2) : Prop :=
  (∀ᶠ t in 𝓝 (0 : ℝ), δ t ∈ fieldSpace L n k j) ∧
    ∀ e : Edge L n k j, e.IsPositivelyOriented → DifferentiableAt ℝ (fun t => δ t e) 0
def diffAtZeroPathsStatement : Prop :=
  ∀ L n k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k →
    (∀ δ : ℝ → Edge L n k j → Matrices.ComplexMatrix2, IsDiffAtZeroPath δ →
      curveTangent δ ∈ edgeFormSpace L n k j ∧
        Tendsto δ (𝓝 0) (𝓝[fieldSpace L n k j] δ 0)) ∧
    (∀ O : Set (Edge L n k j → Matrices.ComplexMatrix2),
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup O → ∀ U ∈ O,
        O ∈ 𝓝[fieldSpace L n k j] U) ∧
    ∀ U ∈ fieldSpace L n k j, ∀ B ∈ edgeFormSpace L n k j,
      IsDiffAtZeroPath (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B) U) ∧
        PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B) U = U ∧
        curveTangent (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B) U) = B
end YangMills.Construction.Tower
end
