import YangMills.Construction.RunningCouplingSlope.HessiansOfTheStepsArePositive
import YangMills.Construction.RunningCouplingSlope.LeastFieldNearTheFlatField
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
private theorem le_torusSideBelow {L : ℕ} (hL : 1 ≤ L) : ∀ s N : ℕ, N ≤ torusSideBelow L s N
  | 0, _ => le_rfl
  | s + 1, N => (Nat.le_mul_of_pos_right N hL).trans (le_torusSideBelow hL s (N * L))
private theorem tendsto_minimizerBelow (hM : MinimizerNearTrivialField) {a ρ : ℝ} (ha : 0 < a)
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hρ₀ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    ∀ (s k N : ℕ), 2 * L ≤ N →
    Tendsto (minimizerBelow a ρ L k s N) (𝓝 (TorusFields.trivialField N))
      (𝓝 (TorusFields.trivialField (torusSideBelow L s N)))
  | 0, _, _, _ => tendsto_id
  | s + 1, k, N, hN => by
    have h := (hM a ha L hL (k - 1) N ρ hN hρ₀ hρ₁).1
    have hL1 : 1 ≤ L := by have := hL.2; omega
    exact (tendsto_minimizerBelow hM ha hL hρ₀ hρ₁ s (k - 1) (N * L)
      (hN.trans (Nat.le_mul_of_pos_right N hL1))).comp h
theorem stepChartHessiansPosDef_of_minimizerNearTrivialField (hM : MinimizerNearTrivialField) :
    StepChartHessiansPosDef := by
  intro a ha L hL k n hn ρ hρ₀ hρ₁
  have hL1 : 1 ≤ L := by have := hL.2; omega
  have hbase : 2 * L ≤ 2 * L ^ n := by
    have h : L ^ 1 ≤ L ^ n := Nat.pow_le_pow_right hL1 hn
    rw [pow_one] at h
    omega
  have hstep : ∀ j, j ∈ Finset.range k →
      ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)), (chartHessianAtStep a ρ L n k j V).PosDef := by
    intro j _
    have hs : 2 * L ≤ torusSideBelow L (k - (j + 1)) (2 * L ^ n) :=
      hbase.trans (le_torusSideBelow hL1 _ _)
    exact (tendsto_minimizerBelow hM ha hL hρ₀ hρ₁ (k - (j + 1)) k (2 * L ^ n) hbase).eventually
      ((hM a ha L hL j _ ρ hs hρ₀ hρ₁).2.mono fun V h => h.2.2.1)
  exact ((Filter.eventually_all_finset (Finset.range k)).2 hstep).mono
    fun V h j hj => h j (Finset.mem_range.2 hj)
end YangMills.Construction.RunningCouplingSlope
end
