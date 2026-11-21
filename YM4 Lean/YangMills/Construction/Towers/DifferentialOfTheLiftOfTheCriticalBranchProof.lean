import YangMills.Construction.Towers.DifferentialOfTheLiftOfTheCriticalBranch
import YangMills.Construction.Towers.FunctionalAlongTheCriticalBranchIsRealAnalyticProof
import YangMills.Construction.Towers.NormaliserLogarithmIsInvariantUnderIsometriesProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
namespace ProlongDerivative
variable {L m k : ℕ}
private theorem prolongComp_trivial {b : CriticalBranchData L m k} (hb : b.IsCritical) :
    ∀ j ≤ k, b.prolongComp j (trivialField L m k j) = trivialField L m k 0 := by apply _root_.YangMills.Construction.Tower.AlongBranchAnalyticity.prolongComp_trivial <;> assumption
private theorem prolongComp_analytic (hM : AnalyticNearField.CompositionAndExpTwist)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {b : CriticalBranchData L m k}
    (hb : b.IsCritical) (j : ℕ) (hj : 1 ≤ j) :
    j ≤ k → ∃ U : Set (Edge L m k j → Matrices.ComplexMatrix2), IsOpenNhdOfOne U ∧
      IsAnalyticFieldMap U (b.prolongComp j) := by apply _root_.YangMills.Construction.Tower.AlongBranchAnalyticity.prolongComp_analytic <;> assumption
private theorem curveTangent_congr {j : ℕ} {γ γ' : ℝ → Edge L m k j → Matrices.ComplexMatrix2}
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), γ t = γ' t) : curveTangent γ = curveTangent γ' := by apply _root_.YangMills.Construction.Tower.SymmetryInvariance.curveTangent_congr <;> assumption
end ProlongDerivative
open ProlongDerivative in
theorem chosenProlongDerivAtIdentity_holds (hB : CriticalBranchExists)
    (hM : AnalyticNearField.CompositionAndExpTwist)
    (hR : AnalyticMapsAlongCurves) (hP : diffAtZeroPathsStatement)
    (hF : SmoothingFibres) : ChosenProlongDerivAtIdentity := by
  intro L hL i m hm B hBf
  cases i with
  | zero => rfl
  | succ i =>
    have hb : (chosenCriticalBranch L m (i + 1 + 1)).IsCritical :=
      Classical.epsilon_spec (hB L m (i + 1 + 1) hL hm)
    obtain ⟨Up, hUp, hAp⟩ := hb.analytic_prolong (i + 1) (by omega)
    obtain ⟨Uc, hUc, hAc⟩ := prolongComp_analytic hM hL hm hb (i + 1 + 1) (by omega) le_rfl
    have hOne : trivialField L m (i + 1 + 1) (i + 1 + 1) ∈
        fieldSpace L m (i + 1 + 1) (i + 1 + 1) := hUp.1.1 hUp.2
    obtain ⟨hδ, hδ0, hδB⟩ := (hP L m (i + 1 + 1) (i + 1 + 1) hL hm le_rfl).2.2 _ hOne B hBf
    have hδt := ((hP L m (i + 1 + 1) (i + 1 + 1) hL hm le_rfl).1 _ hδ).2
    rw [hδ0] at hδt
    have hp := ((hR L m (i + 1 + 1) (i + 1 + 1) (i + 1) hL hm le_rfl (by omega)).1 Up _ hAp).2 _
      hUp.2
    have hc := ((hR L m (i + 1 + 1) (i + 1 + 1) 0 hL hm le_rfl (by omega)).1 Uc _ hAc).2 _ hUc.2
    obtain ⟨hγ, hγB⟩ := hc.2 _ hδ hδ0
    have hc1 := prolongComp_trivial hb (i + 1 + 1) le_rfl
    have hγ0 : (chosenCriticalBranch L m (i + 1 + 1)).prolongComp (i + 1 + 1)
        (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B)
          (trivialField L m (i + 1 + 1) (i + 1 + 1))) =
        trivialField L m (i + 1 + 1) 0 := by
      rw [hδ0, hc1]
    have hAf := ((hP L m (i + 1 + 1) 0 hL hm (by omega)).1 _ hγ).1
    obtain ⟨hFd, -, -, -, ⟨Um, hUm, -, hAm, -⟩, -⟩ := hF L m (i + 1 + 1) i hL hm (by omega)
    have hmap := ((hR L m (i + 1 + 1) 0 (i + 1) hL hm (by omega) (by omega)).1 Um _ hAm).2 _ hUm.2
    have hmγ := (hmap.2 _ hγ hγ0).2
    rw [hγB, hδB] at hmγ
    rw [hγB, hδB] at hAf
    have hpδ := (hp.2 _ hδ hδ0).2
    rw [hδB] at hpδ
    have hev := hδt.eventually (hb.prolongComp_lift (i + 1) (by omega))
    have htan := curveTangent_congr hev
    change leftDifferential ((chosenCriticalBranch L m (i + 1 + 1)).prolong (i + 1)) _ B =
      linearSmoothingIter L m (i + 1 + 1) (i + 1)
        (leftDifferential ((chosenCriticalBranch L m (i + 1 + 1)).prolongComp (i + 1 + 1)) _ B)
    rw [← hpδ, ← htan, hmγ, hFd _ hAf]
end YangMills.Construction.Tower
end
