import YangMills.Construction.Towers.FunctionalAlongTheCriticalBranchIsRealAnalyticProof
import YangMills.Construction.Towers.GradientsAreFormedAlongTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.CriticalBranchGradients
open YangMills.Construction.Tower.CriticalBranchResponse
variable {L n k j : ℕ}
theorem gradientExistsAt_of_analytic (hD : AnalyticDifferentials.AnalyticMapsDifferentiable)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {𝒰 : Set (Edge L n k j → Matrices.ComplexMatrix2)}
    {S : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ}
    (hS : IsAnalyticFieldFunction 𝒰 S) {W : Edge L n k j → Matrices.ComplexMatrix2} (hW : W ∈ 𝒰) :
    GradientExistsAt S W := by
  have hC : IsAnalyticComplexFieldFunction 𝒰 (fun V => (S V : ℂ)) := hS
  obtain ⟨-, hdiff, -, hform⟩ := (hD L n k j j hL hn hj hj 𝒰 hS.1).1 _ hC
  obtain ⟨⟨-, hg, -⟩, -⟩ := hform W hW
  refine ⟨?_, ?_⟩
  · obtain ⟨ho, inst, hd, hc⟩ := hdiff
    refine ⟨𝒰, hW, ho, inst, hd, fun c => ?_⟩
    have h := Complex.reCLM.differentiable.comp_differentiableOn (hc c)
    exact h
  · have hIs : IsLeftGradient (fieldSpace L n k j) (fun V => (S V : ℂ)) W
        (leftGradient 𝒰 (fun V => (S V : ℂ)) W) :=
      ⟨hg.1, fun _ => hg.2.1 fun V _ => Complex.ofReal_im _, hg.2.2⟩
    exact Classical.epsilon_spec (⟨_, hIs⟩ : ∃ X, IsLeftGradient (fieldSpace L n k j)
      (fun V => (S V : ℂ)) W X)
theorem prolongComp_analytic (hM : AnalyticNearField.CompositionAndExpTwist)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {b : CriticalBranchData L n k}
    (hb : b.IsCritical) (j : ℕ) (hj : 1 ≤ j) :
    j ≤ k → ∃ 𝒰 : Set (Edge L n k j → Matrices.ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
      IsAnalyticFieldMap 𝒰 (b.prolongComp j) := by apply _root_.YangMills.Construction.Tower.AlongBranchAnalyticity.prolongComp_analytic <;> assumption
theorem gradientsExistAlongBranch_holds (hF : ChosenBranchIsCritical)
    (hM : AnalyticNearField.CompositionAndExpTwist)
    (hD : AnalyticDifferentials.AnalyticMapsDifferentiable)
    (hA : WilsonActionAnalytic)
    (hP : diffAtZeroPathsStatement) : GradientsExistAlongBranch := by
  intro L hL k hk n hn B
  have hb : (chosenCriticalBranch L n k).IsCritical := (hF L n k hL hn).1
  obtain ⟨𝒰, h𝒰, hS⟩ := hb.analytic_energy k le_rfl
  obtain ⟨𝒱, h𝒱, hc⟩ := prolongComp_analytic hM hL hn hb k hk le_rfl
  have hone : trivialField L n k k ∈ fieldSpace L n k k := h𝒰.1.1 h𝒰.2
  obtain ⟨hpath, h0, -⟩ := (hP L n k k hL hn le_rfl).2.2 _ hone B B.2
  have hlim := ((hP L n k k hL hn le_rfl).1 _ hpath).2
  rw [h0] at hlim
  have near : ∀ 𝒪 : Set (Edge L n k k → Matrices.ComplexMatrix2), IsOpenNhdOfOne 𝒪 →
      ∀ᶠ t in 𝓝 (0 : ℝ), expLineField L n k B t ∈ 𝒪 := fun 𝒪 h =>
    hlim ((hP L n k k hL hn le_rfl).2.1 𝒪 h.1 _ h.2)
  refine ⟨?_, ?_⟩
  · filter_upwards [near 𝒰 h𝒰] with t ht
    exact gradientExistsAt_of_analytic hD hL hn le_rfl hS ht
  · filter_upwards [near 𝒱 h𝒱] with t ht
    exact gradientExistsAt_of_analytic hD hL hn (Nat.zero_le k) (hA L n k hL hn) (hc.2.1 ht)
end YangMills.Construction.Tower.CriticalBranchGradients
end
