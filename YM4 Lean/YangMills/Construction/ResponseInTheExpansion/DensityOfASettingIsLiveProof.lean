import YangMills.Construction.ClusterExpansionOfAStep.WeightOfTheGasIsBorelProof
import YangMills.Construction.ResponseInTheExpansion.DensityOfASettingIsLive
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepSettings StepCosts RenormalizationStepParameters LumpContours
namespace ChartDensity
variable {n : ℕ} {R : StepSetup} [NeZero n]
theorem sum_sum_sitesInBlocks_singleton (L : ℕ) [NeZero L] (f : TorusSite (n * L) → ℝ) :
    ∑ Y : TorusSite n, ∑ y ∈ sitesInBlocks L {Y}, f y = ∑ y, f y := by apply _root_.YangMills.Construction.FreeBonds.sum_sitesInBlocks_singleton <;> assumption
theorem sum_levelShare_eq_actionAtLevel (hS : SharesSumToAction) (a : ℝ) (L t m : ℕ) [NeZero m]
    (S : Finset (TorusSite m)) (W : TorusField m) (ha : 0 ≤ a) (hL : 0 < L) (hm : 2 ≤ m) :
    ∑ y, levelShare a L t S y W = actionAtLevel a L t S W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.sum_levelShare <;> assumption
def totalBondFit (ℓ : TorusLumps.StepParameters) (W : TorusField (n * ℓ.side)) (V : TorusField n)
    (b : BaseChoice ℓ.side n) : ℝ :=
  ∑ Y : TorusSite n, ℓ.coupling / 2 *
    ∑ i : Fin 4, (bondFit ℓ W V b (Y, i) + bondFit ℓ W V b (Y - unitStep n i, i))
theorem exp_neg_potential_eq
    (hr : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
      R.clusterFactor R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0) (hS : SharesSumToAction)
    (ha : 0 ≤ R.params.coupling) (hL : 0 < R.params.side) (hm : 2 ≤ n * R.params.side)
    (s : ChartSetting R n) (η : FreeCoords s.free)
    (hh : IsHullState R.params R.range (s.field η) s.support)
    (hΦ : ∀ X ∈ chainComponents R.range s.support,
      R.clusterFactor (n * R.params.side) (s.field η) s.support s.labelling X ≠ 0) :
    Real.exp (-s.potential η) =
      R.labelWeight (n * R.params.side) (s.field η) s.support s.labelling /
          (R.functional (n * R.params.side) (trivialField _) *
            ∏ X ∈ chainComponents R.range s.support,
              R.clusterFactor (n * R.params.side) (s.field η) s.support s.labelling X) *
        Real.exp (-(R.coupling * totalBondFit R.params (s.field η) s.coarse s.bases) +
          ∑ Y : TorusSite n, s.logJacobian (s.field η) η Y) :=
  _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.exp_neg_potential
    hr hside hflat hS ha hL hm s η hh hΦ
end ChartDensity
open ChartDensity in
theorem chartDensitySupportedOnLiveStates_of_sharesSumToAction (hS : SharesSumToAction) :
    ChartDensitySupportedOnLiveStates := by
  intro T hT
  refine ⟨T.floorMin, fun y hy R hR n _ s hn hs η hd => ?_⟩
  have hrow := hR.isStep.1
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hn4 : 4096 ≤ R.params.n₀ := by
    rw [hR.params_eq]
    exact hT.n₀_ge
  have hnL : R.params.n₀ ≤ n * R.params.side := le_trans hn (Nat.le_mul_of_pos_right _ hLpos)
  have hm : 2 ≤ n * R.params.side := by omega
  have ha : 0 ≤ R.params.coupling := by
    rw [hR.params_eq]
    exact le_trans zero_le_one hT.a_ge
  have hσ : 0 < R.params.threshold := by
    rw [hR.params_eq]
    exact hT.σ_pos
  have hcold : IsCold R.params.threshold (trivialField (n * R.params.side)) := by
    intro x μ ν _
    simpa [curvature, holonomy, trivialField] using hσ
  have hflat : R.functional (n * R.params.side) (trivialField _) ≠ 0 :=
    (hrow.1.positive (n * R.params.side) hnL _ hcold).ne'
  have hη : s.InBalls η := by
    by_contra hη
    apply hd
    simp only [ChartSetting.InBalls, not_forall, not_le] at hη
    obtain ⟨e, he⟩ := hη
    unfold chartDensity ChartSetting.cutoffProduct
    rw [Finset.prod_eq_zero (Finset.mem_univ e) (by
      unfold ColdStepAtMirrorFrames.cutoffFactor
      exact if_neg (not_lt.mpr he.le)), zero_mul]
  have hh := hs.isHull η hη
  have hΦ := hs.factor_ne_zero η hη
  have e := exp_neg_potential_eq hrow.2 hside hflat hS ha hLpos hm s η hh hΦ
  refine ⟨hh, lt_of_le_of_ne (hrow.2.nonneg (n * R.params.side) hside _ _ _ hh) fun h0 => ?_⟩
  rw [← h0] at e
  simp only [zero_div, zero_mul] at e
  exact (Real.exp_pos _).ne' e
end YangMills.Construction.WeightedResponses
end
