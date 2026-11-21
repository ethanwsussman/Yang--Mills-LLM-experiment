import YangMills.Construction.CellOfTheFlow.TheLowerMajorantIsBelowTheMajorant
import YangMills.Construction.CellOfTheFlow.TheLowerWindowLiesInTheHull
import YangMills.Construction.ClusterExpansionOfAStep.PlacesOfABlock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps StepSettings StepCosts WeightedResponses BlockPlaces
variable {ℓ : TorusLumps.StepParameters}
private theorem coarseLabelScore_nonneg {Ω : Type} {L : ℕ} {s₁ : ℝ} {sc : Ω → ℝ} (h₁ : 0 ≤ s₁)
    (hs : ∀ w, 0 ≤ sc w) : ∀ w : CoarseLabel Ω L, 0 ≤ coarseLabelScore (L := L) s₁ sc w
  | Sum.inl _ => h₁
  | Sum.inr st => add_nonneg h₁ (Finset.sum_nonneg fun o _ => by
      cases st.siteLabel o with
      | inl _ => exact le_rfl
      | inr a => exact hs a)
private theorem labelMajorant_nonneg (T : StageTower ℓ) {s₀ s₁ : ℝ} (h₀ : 0 ≤ s₀) (h₁ : 0 ≤ s₁) (t : ℕ) :
    ∀ w, 0 ≤ labelMajorant T s₀ s₁ t w := by
  induction t with
  | zero => exact fun _ => h₀
  | succ t ih => exact coarseLabelScore_nonneg (L := ℓ.side) h₁ ih
private theorem siteScore_nonneg {Ω : Type} {n : ℕ} {sc : Ω → ℝ} (hs : ∀ w, 0 ≤ sc w)
    (Y : Finset (TorusSite n)) (ω : Y → Ω) (y : TorusSite n) : 0 ≤ siteScore sc Y ω y := by
  unfold siteScore
  split_ifs
  · exact hs _
  · exact le_rfl
private theorem siteMajorant_nonneg (T : StageTower ℓ) {s₀ s₁ : ℝ} (h₀ : 0 ≤ s₀) (h₁ : 0 ≤ s₁) (t n : ℕ)
    [NeZero n] (u : MarkedSample ℓ t n) (y : TorusSite n) : 0 ≤ siteMajorant T s₀ s₁ t n u y :=
  siteScore_nonneg (labelMajorant_nonneg T h₀ h₁ t) _ _ _
open Classical in
private theorem siteScore_coarseStateOf (R : StepSetup) {n : ℕ} [NeZero n] (s₁ : ℝ) (sc : R.labels.Ω → ℝ)
    (C : Finset (TorusSite n)) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) (y : TorusSite n)
    (hy : y ∈ (coarseStateOf R C W Yt ωt bad b).1) :
    siteScore (coarseLabelScore (L := R.params.side) s₁ sc) (coarseStateOf R C W Yt ωt bad b).1
        (coarseStateOf R C W Yt ωt bad b).2 y =
      s₁ + (if y ∈ storedBlocks R.params.side R.range bad Yt C then
        ∑ o : BlockOffset R.params.side, siteScore sc Yt ωt (blockSite y o) else 0) := by
  unfold siteScore
  rw [dif_pos hy]
  by_cases hz : y ∈ storedBlocks R.params.side R.range bad Yt C
  · have e : (coarseStateOf R C W Yt ωt bad b).2 ⟨y, hy⟩ =
        Sum.inr (blockConfigAt R C (storedBlocks R.params.side R.range bad Yt C) W Yt ωt bad b y) := by
      simp only [coarseStateOf]
      exact if_pos hz
    rw [e, if_pos hz]
    show s₁ + _ = _
    congr 1
    refine Finset.sum_congr rfl fun o _ => ?_
    by_cases ho : blockSite y o ∈ Yt
    · simp only [blockConfigAt, dif_pos ho, Sum.elim_inr]
    · simp only [blockConfigAt, dif_neg ho, Sum.elim_inl]
  · have e : (coarseStateOf R C W Yt ωt bad b).2 ⟨y, hy⟩ = Sum.inl () := by
      simp only [coarseStateOf]
      exact if_neg hz
    rw [e, if_neg hz, add_zero]
    rfl
private theorem sum_sitesInBlocks_le {n L : ℕ} [NeZero n] [NeZero L] (y : TorusSite n)
    {f g : TorusSite (n * L) → ℝ} (hfg : ∀ z, f z ≤ g z) :
    ∑ z ∈ sitesInBlocks L {y}, f z ≤ ∑ o : BlockOffset L, g (blockSite y o) := by
  have e : ∑ z ∈ sitesInBlocks L {y}, g z = ∑ o : BlockOffset L, g (blockSite y o) := by
    refine Finset.sum_nbij' siteOffset (blockSite y) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
    · intro o _
      simp [sitesInBlocks, parentBlock_blockSite]
    · intro z hz
      have hb : parentBlock L z = y := by simpa [sitesInBlocks] using hz
      rw [← hb]
      exact blockSite_parentBlock_siteOffset z
    · intro o _
      exact siteOffset_blockSite y o
    · intro z hz
      have hb : parentBlock L z = y := by simpa [sitesInBlocks] using hz
      rw [← hb, blockSite_parentBlock_siteOffset z]
  rw [← e]
  exact Finset.sum_le_sum fun z _ => hfg z
private theorem lowerScore_nonneg_and_le (hW : lowerHullSubsetStageHullStatement) (T : StageTower ℓ) (k : ℕ)
    {s₀ s₁ : ℝ} (h₀ : 0 ≤ s₀) (h₁ : 0 ≤ s₁) (s : ℕ) :
    ∀ (n : ℕ) [NeZero n] (u : MarkedSample ℓ s n) (c : Finset (TorusSite n)) (z : TorusSite n),
      0 ≤ lowerScore T k s₀ s₁ s n u c z ∧ lowerScore T k s₀ s₁ s n u c z ≤ siteMajorant T s₀ s₁ s n u z := by
  induction s with
  | zero =>
    intro n _ W c z
    rw [lowerScore]
    by_cases hz : z ∈ lowerHull T k 0 n W c
    · rw [if_pos hz]
      refine ⟨h₀, ?_⟩
      have hy : z ∈ (stageState T 0 n W).2.1 := (hW ℓ T k).1 0 n W c hz
      unfold siteMajorant siteScore
      rw [dif_pos hy]
      exact le_rfl
    · rw [if_neg hz]
      exact ⟨le_rfl, siteMajorant_nonneg T h₀ h₁ 0 n W z⟩
  | succ s ih =>
    intro n _ u c y
    rw [lowerScore]
    by_cases hy : y ∈ lowerHull T k (s + 1) n u c
    · rw [if_pos hy]
      have hY : y ∈ (coarseStateOf (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1)
          (stageState T s (n * ℓ.side) u.1).1 (stageState T s (n * ℓ.side) u.1).2.1
          (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1).1 := (hW ℓ T k).1 (s + 1) n u c hy
      have hm : siteMajorant T s₀ s₁ (s + 1) n u y = s₁ +
          (if y ∈ storedBlocks ℓ.side (T.stage s).toStepSetup.range u.2.2.2
              (stageState T s (n * ℓ.side) u.1).2.1 (hotCoreSites (T.stage s).toStepSetup u.2.2.1) then
            ∑ o : BlockOffset ℓ.side, siteMajorant T s₀ s₁ s (n * ℓ.side) u.1 (blockSite y o) else 0) :=
        siteScore_coarseStateOf (T.stage s).toStepSetup s₁ (labelMajorant T s₀ s₁ s) _ _ _ _ _ _ y hY
      have hsum : ∀ z : BlockOffset ℓ.side, 0 ≤ siteMajorant T s₀ s₁ s (n * ℓ.side) u.1 (blockSite y z) :=
        fun z => siteMajorant_nonneg T h₀ h₁ s (n * ℓ.side) u.1 _
      rw [hm]
      by_cases hz : y ∈ lowerZone T k s (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.2
          (lowerHull T k s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c)) c
      · have hz' := (hW ℓ T k).2 s n u c hz
        rw [if_pos hz, if_pos hz']
        refine ⟨add_nonneg h₁ (Finset.sum_nonneg fun z _ =>
          (ih (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c) z).1), ?_⟩
        linarith [sum_sitesInBlocks_le y fun z => (ih (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c) z).2]
      · rw [if_neg hz, add_zero]
        refine ⟨h₁, ?_⟩
        split_ifs
        · exact le_add_of_nonneg_right (Finset.sum_nonneg fun z _ => hsum z)
        · rw [add_zero]
    · rw [if_neg hy]
      exact ⟨le_rfl, siteMajorant_nonneg T h₀ h₁ (s + 1) n u y⟩
theorem lowerScore_le_majorant (hW : lowerHullSubsetStageHullStatement) :
    lowerScoreLeMajorantStatement := by
  intro ℓ T k s₀ s₁ h₀ h₁ s m _ u c
  refine ⟨lowerScore_nonneg_and_le hW T k h₀ h₁ s m u c, ?_⟩
  unfold lowerScoreSum hullMajorantSum
  calc ∑ y ∈ lowerHull T k s m u c, lowerScore T k s₀ s₁ s m u c y
      ≤ ∑ y ∈ lowerHull T k s m u c, siteMajorant T s₀ s₁ s m u y :=
        Finset.sum_le_sum fun y _ => (lowerScore_nonneg_and_le hW T k h₀ h₁ s m u c y).2
    _ ≤ ∑ y ∈ stageHull T s m u, siteMajorant T s₀ s₁ s m u y :=
        Finset.sum_le_sum_of_subset_of_nonneg (((hW ℓ T k).1 s m u c))
          fun y _ _ => siteMajorant_nonneg T h₀ h₁ s m u y
end YangMills.Construction.CellWindows
end
