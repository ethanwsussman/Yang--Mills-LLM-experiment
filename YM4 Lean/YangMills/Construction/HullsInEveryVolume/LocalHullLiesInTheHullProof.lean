import YangMills.Construction.CellOfTheFlow.TheLowerWindowLiesInTheHullProof
import YangMills.Construction.ClusterExpansionOfAStep.ClassesBesideAFarSet
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import YangMills.Construction.HullsInEveryVolume.LocalHullLiesInTheHull
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresInALimitFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
open TorusLumps TorusFields StepSettings StepGas StepReturn BlockPlaces TorusBalls ClusterExpansionOfAStep WeightedResponses
section Sets
variable {n L : ℕ} [NeZero n] [NeZero L]
private theorem attachedSites_mono (r : ℕ) {bad bad' : Finset (TorusBond (n * L))} {Yt Yt' : Finset (TorusSite (n * L))}
    {C C' : Finset (TorusSite n)} (hb : bad' ⊆ bad) (hY : Yt' ⊆ Yt) (hC : C' ⊆ C) :
    attachedSites L r bad' Yt' C' ⊆ attachedSites L r bad Yt C := by
  classical
  have hA : clusterSites bad' Yt' C' ⊆ clusterSites bad Yt C := by
    intro z hz
    simp only [clusterSites, Finset.mem_union, Finset.mem_image, mem_sitesInBlocks] at hz ⊢
    rcases hz with (⟨b, hb', rfl⟩ | hz) | hz
    · exact Or.inl (Or.inl ⟨b, hb hb', rfl⟩)
    · exact Or.inl (Or.inr (hY hz))
    · exact Or.inr (hC hz)
  intro z hz
  obtain ⟨X, hX, hzX, c, hc⟩ := (mem_attachedSites_iff r bad' Yt' C').mp hz
  obtain ⟨hcX, hcC⟩ := Finset.mem_inter.mp hc
  have hcC' : c ∈ sitesInBlocks L C := mem_sitesInBlocks.mpr (hC (mem_sitesInBlocks.mp hcC))
  have hcA := sitesInBlocks_subset_attachedSites r bad Yt C hcC'
  obtain ⟨X2, hX2, hc2, hne⟩ := (mem_attachedSites_iff r bad Yt C).mp hcA
  exact (mem_attachedSites_iff r bad Yt C).mpr ⟨X2, hX2,
    mem_of_chainConnected_of_mem_chainComponents hX2 hc2 (hA (subset_of_mem_chainComponents hX hzX))
      (chainConnected_mono hA (chainConnected_of_mem_chainComponents hX hcX hzX)), hne⟩
private theorem coreBlocks_mono (r : ℕ) {θ θ' : Finset (TorusSite (n * L))} (h : θ ⊆ θ') :
    coreBlocks L r θ ⊆ coreBlocks L r θ' := by apply _root_.YangMills.SharedProofs.p23923 <;> assumption
private theorem thickening_mono {m : ℕ} {A B : Finset (TorusSite n)} (h : A ⊆ B) :
    thickening m A ⊆ thickening m B := by
  intro z hz
  obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp hz
  exact (mem_thickening _ _ _).mpr ⟨x, h hx, hd⟩
private theorem component_subset_attachedSites_local (r : ℕ) {bad bad' : Finset (TorusBond (n * L))}
    {Yt lo : Finset (TorusSite (n * L))}
    {C CQ Q : Finset (TorusSite n)} (hbad : ∀ b, b ∈ bad' ↔ b ∈ bad ∧ b.1 ∈ sitesInBlocks L Q)
    (hCQ : ∀ y, y ∈ CQ ↔ y ∈ C ∧ y ∈ Q) {X : Finset (TorusSite (n * L))}
    (hX : X ∈ chainComponents (10 * r) (clusterSites bad Yt C)) (hne : (X ∩ sitesInBlocks L C).Nonempty)
    (hQ : X ⊆ sitesInBlocks L Q) (hlo : ∀ t ∈ X, t ∈ Yt → t ∈ lo) :
    X ⊆ attachedSites L r bad' lo CQ := by
  classical
  have hXA : X ⊆ clusterSites bad' lo CQ := by
    intro t ht
    have htA := subset_of_mem_chainComponents hX ht
    have htQ := hQ ht
    simp only [clusterSites, Finset.mem_union, Finset.mem_image] at htA ⊢
    rcases htA with (⟨b, hb, rfl⟩ | hty) | htC
    · exact Or.inl (Or.inl ⟨b, (hbad b).mpr ⟨hb, htQ⟩, rfl⟩)
    · exact Or.inl (Or.inr (hlo t ht hty))
    · exact Or.inr (mem_sitesInBlocks.mpr ((hCQ _).mpr ⟨mem_sitesInBlocks.mp htC, mem_sitesInBlocks.mp htQ⟩))
  obtain ⟨c, hc⟩ := hne
  obtain ⟨hcX, hcC⟩ := Finset.mem_inter.mp hc
  have hcQ : c ∈ sitesInBlocks L CQ :=
    mem_sitesInBlocks.mpr ((hCQ _).mpr ⟨mem_sitesInBlocks.mp hcC, mem_sitesInBlocks.mp (hQ hcX)⟩)
  have hcA := sitesInBlocks_subset_attachedSites r bad' lo CQ hcQ
  obtain ⟨X2, hX2, hc2, hne2⟩ := (mem_attachedSites_iff r bad' lo CQ).mp hcA
  have key : ∀ u, ChainConnected (10 * r) (clusterSites bad Yt C) c u →
      ChainConnected (10 * r) (clusterSites bad' lo CQ) c u := by
    intro u hu
    induction hu with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b hab hs ih =>
      have haX : a ∈ X := mem_of_chainConnected_of_mem_chainComponents hX hcX hs.1 hab
      have hbX : b ∈ X := mem_of_chainConnected_of_mem_chainComponents hX hcX hs.2.1 (hab.tail hs)
      exact ih.tail ⟨hXA haX, hXA hbX, hs.2.2⟩
  intro z hz
  exact (mem_attachedSites_iff r bad' lo CQ).mpr ⟨X2, hX2,
    mem_of_chainConnected_of_mem_chainComponents hX2 hc2 (hXA hz)
      (key z (chainConnected_of_mem_chainComponents hX hcX hz)), hne2⟩
omit [NeZero n] in
private theorem mem_hullClass_of_supDist_le {r : ℕ} {Y : Finset (TorusSite n)} {z a b : TorusSite n}
    (ha : a ∈ hullClass r Y z) (hb : b ∈ Y) (hd : supDist a b ≤ r) : b ∈ hullClass r Y z := by
  classical
  exact Finset.mem_filter.mpr ⟨hb, (Finset.mem_filter.mp ha).2.tail ⟨(Finset.mem_filter.mp ha).1, hb, hd⟩⟩
private theorem storedBlocks_subset_coarseHull (r r' : ℕ) (bad : Finset (TorusBond (n * L)))
    (Yt : Finset (TorusSite (n * L))) (C : Finset (TorusSite n)) :
    storedBlocks L r bad Yt C ⊆ coarseHull L r r' bad Yt C :=
  subset_thickening_self _ _
private theorem parentBlock_mem_hullClass_of_component {r r' : ℕ} {bad : Finset (TorusBond (n * L))}
    {Yt : Finset (TorusSite (n * L))}
    {C : Finset (TorusSite n)} {z₀ : TorusSite n} (hr : 10 * r / L + 1 ≤ r') {θ : Finset (TorusSite (n * L))}
    (hθ : θ ∈ chainComponents (10 * r) (clusterSites bad Yt C)) (hne : (θ ∩ sitesInBlocks L C).Nonempty)
    {w : TorusSite (n * L)} (hw : w ∈ θ) (hb : parentBlock L w ∈ hullClass r' (coarseHull L r r' bad Yt C) z₀) :
    ∀ t ∈ θ, parentBlock L t ∈ hullClass r' (coarseHull L r r' bad Yt C) z₀ := by
  classical
  have key : ∀ u, ChainConnected (10 * r) (clusterSites bad Yt C) w u →
      parentBlock L u ∈ hullClass r' (coarseHull L r r' bad Yt C) z₀ := by
    intro u hu
    induction hu with
    | refl => exact hb
    | @tail a b hab hs ih =>
      have hbθ : b ∈ θ := mem_of_chainConnected_of_mem_chainComponents hθ hw hs.2.1 (hab.tail hs)
      have hbA : b ∈ attachedSites L r bad Yt C := (mem_attachedSites_iff r bad Yt C).mpr ⟨θ, hθ, hbθ, hne⟩
      have hst := parentBlock_mem_storedBlocks r bad Yt C hbA
      have hd := supDist_parentBlock_le_div_add_one L a b
      have hdist : supDist a b / L ≤ 10 * r / L := Nat.div_le_div_right hs.2.2
      exact mem_hullClass_of_supDist_le ih (storedBlocks_subset_coarseHull r r' bad Yt C hst) (by omega)
  exact fun t ht => key t (chainConnected_of_mem_chainComponents hθ hw ht)
private theorem hullClass_subset_component {r : ℕ} {bad : Finset (TorusBond (n * L))}
    {Yt : Finset (TorusSite (n * L))}
    {C : Finset (TorusSite n)} {θ : Finset (TorusSite (n * L))}
    (hθ : θ ∈ chainComponents (10 * r) (clusterSites bad Yt C))
    {t : TorusSite (n * L)} (ht : t ∈ θ) : hullClass r Yt t ⊆ θ := by
  classical
  have hY : Yt ⊆ clusterSites bad Yt C := by
    intro z hz
    simp only [clusterSites, Finset.mem_union]
    exact Or.inl (Or.inr hz)
  have key : ∀ u, ChainConnected r Yt t u → ChainConnected (10 * r) (clusterSites bad Yt C) t u := by
    intro u hj
    induction hj with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.tail ⟨hY hs.1, hY hs.2.1, hs.2.2.trans (by omega)⟩
  intro u hu
  obtain ⟨huY, hj⟩ := Finset.mem_filter.mp hu
  exact mem_of_chainConnected_of_mem_chainComponents hθ ht (hY huY) (key u hj)
private theorem hullClass_subset_of_storedBlock {r r' : ℕ} {bad : Finset (TorusBond (n * L))}
    {Yt : Finset (TorusSite (n * L))}
    {C Q : Finset (TorusSite n)} {z₀ c : TorusSite n} (hL : L ≤ 6 * r) (hr : 10 * r / L + 1 ≤ r')
    (hXQ : hullClass r' (coarseHull L r r' bad Yt C) z₀ ⊆ Q) (hc : c ∈ storedBlocks L r bad Yt C)
    (hcX : c ∈ hullClass r' (coarseHull L r r' bad Yt C) z₀) {t : TorusSite (n * L)} (ht : t ∈ Yt)
    (hb : parentBlock L t = c) : hullClass r Yt t ⊆ sitesInBlocks L Q := by
  classical
  have htA : t ∈ clusterSites bad Yt C := by
    simp only [clusterSites, Finset.mem_union]
    exact Or.inl (Or.inr ht)
  have hatt := mem_attachedSites_of_parentBlock_mem r bad Yt C hL htA (hb ▸ hc)
  obtain ⟨θ, hθ, htθ, hne⟩ := (mem_attachedSites_iff r bad Yt C).mp hatt
  intro u hu
  exact mem_sitesInBlocks.mpr (hXQ (parentBlock_mem_hullClass_of_component hr hθ hne htθ (hb ▸ hcX) u
    (hullClass_subset_component hθ htθ hu)))
private theorem storedBlock_mem_local {r r' : ℕ} {bad bad' : Finset (TorusBond (n * L))}
    {Yt lo : Finset (TorusSite (n * L))}
    {C CQ Q : Finset (TorusSite n)} {z₀ c : TorusSite n} (hr : 10 * r / L + 1 ≤ r')
    (hbad : ∀ b, b ∈ bad' ↔ b ∈ bad ∧ b.1 ∈ sitesInBlocks L Q) (hCQ : ∀ y, y ∈ CQ ↔ y ∈ C ∧ y ∈ Q)
    (hIH : ∀ t ∈ Yt, hullClass r Yt t ⊆ sitesInBlocks L Q → t ∈ lo)
    (hXQ : hullClass r' (coarseHull L r r' bad Yt C) z₀ ⊆ Q) (hc : c ∈ storedBlocks L r bad Yt C)
    (hcX : c ∈ hullClass r' (coarseHull L r r' bad Yt C) z₀) :
    c ∈ CQ ∨ c ∈ coreBlocks L r (attachedSites L r bad' lo CQ) ∧ c ∈ Q := by
  classical
  have hcQ := hXQ hcX
  rcases Finset.mem_union.mp hc with hC | hcore
  · exact Or.inl ((hCQ c).mpr ⟨hC, hcQ⟩)
  · refine Or.inr ⟨?_, hcQ⟩
    obtain ⟨v, hv⟩ := (Finset.mem_filter.mp hcore).2
    obtain ⟨hv1, hv2⟩ := Finset.mem_inter.mp hv
    have hvb : parentBlock L v = c := Finset.mem_singleton.mp (mem_sitesInBlocks.mp hv1)
    obtain ⟨w, hw, hvw⟩ := (mem_thickening _ _ _).mp hv2
    obtain ⟨θ, hθ, hwθ, hne⟩ := (mem_attachedSites_iff r bad Yt C).mp hw
    have hwst := parentBlock_mem_storedBlocks r bad Yt C hw
    have hd := supDist_parentBlock_le_div_add_one L v w
    have hdist : supDist v w / L ≤ 10 * r / L := Nat.div_le_div_right (by omega)
    have hwX : parentBlock L w ∈ hullClass r' (coarseHull L r r' bad Yt C) z₀ :=
      mem_hullClass_of_supDist_le hcX (storedBlocks_subset_coarseHull r r' bad Yt C hwst) (by rw [← hvb]; omega)
    have hblocks := parentBlock_mem_hullClass_of_component hr hθ hne hwθ hwX
    have hover : θ ⊆ sitesInBlocks L Q := fun t ht => mem_sitesInBlocks.mpr (hXQ (hblocks t ht))
    have hloc := component_subset_attachedSites_local r hbad hCQ hθ hne hover fun t ht hty =>
      hIH t hty fun u hu => hover (hullClass_subset_component hθ ht hu)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, v,
      Finset.mem_inter.mpr ⟨hv1, (mem_thickening _ _ _).mpr ⟨w, hloc hwθ, hvw⟩⟩⟩
private theorem sum_blockOffset_eq_sum_sitesInBlocks (y : TorusSite n) (f : TorusSite (n * L) → ℝ) :
    ∑ o : BlockOffset L, f (blockSite y o) = ∑ z ∈ sitesInBlocks L {y}, f z := by
  classical
  refine Finset.sum_nbij' (fun o => blockSite y o) siteOffset ?_ ?_ ?_ ?_ ?_
  · intro o _
    exact mem_sitesInBlocks.mpr (Finset.mem_singleton.mpr (parentBlock_blockSite y o))
  · intro z _
    exact Finset.mem_univ _
  · intro o _
    exact siteOffset_blockSite y o
  · intro z hz
    have hb : parentBlock L z = y := Finset.mem_singleton.mp (mem_sitesInBlocks.mp hz)
    have := blockSite_parentBlock_siteOffset z
    rw [hb] at this
    exact this
  · intro o _
    rfl
end Sets
section Draws
variable {ℓ : StepParameters} (T : StageTower ℓ) {s₁ : ℝ}
private theorem siteSize_nonneg (h₁ : 0 ≤ s₁) (u n : ℕ) [NeZero n] (w : MarkedSample ℓ u n) (y : TorusSite n) :
    0 ≤ siteSize T s₁ u n w y := by apply _root_.YangMills.SharedProofs.p9879 <;> assumption
private theorem siteSize_of_not_mem (u n : ℕ) [NeZero n] (w : MarkedSample ℓ u n) {y : TorusSite n}
    (hy : y ∉ hullSet T u n w) : siteSize T s₁ u n w y = 0 := by
  unfold siteSize siteScore
  exact dif_neg hy
private theorem siteSize_succ (j n : ℕ) [NeZero n] (w : MarkedSample ℓ (j + 1) n) {y : TorusSite n}
    (hy : y ∈ hullSet T (j + 1) n w) :
    siteSize T s₁ (j + 1) n w y = open Classical in if y ∈ coreZone T j n w then
      s₁ + ∑ z ∈ sitesInBlocks ℓ.side {y}, siteSize T s₁ j (n * ℓ.side) w.1 z else s₁ := by
  classical
  have h0 : siteSize T s₁ (j + 1) n w y =
      coarseLabelScore s₁ (labelSize T s₁ j) ((stageState T (j + 1) n w).2.2 ⟨y, hy⟩) := by
    unfold siteSize siteScore
    exact dif_pos hy
  rw [h0]
  by_cases hz : y ∈ coreZone T j n w
  · rw [if_pos hz]
    have h1 : (stageState T (j + 1) n w).2.2 ⟨y, hy⟩ = Sum.inr (blockConfigAt (T.stage j).toStepSetup
        (hotCoreSites (T.stage j).toStepSetup w.2.2.1) (coreZone T j n w) (stageState T j (n * ℓ.side) w.1).1
        (stageState T j (n * ℓ.side) w.1).2.1 (stageState T j (n * ℓ.side) w.1).2.2 w.2.2.2 w.2.1 y) := if_pos hz
    rw [h1]
    simp only [coarseLabelScore]
    rw [← sum_blockOffset_eq_sum_sitesInBlocks y (siteSize T s₁ j (n * ℓ.side) w.1)]
    congr 1
    refine Finset.sum_congr rfl fun o _ => ?_
    simp only [blockConfigAt, siteSize, siteScore]
    split_ifs <;> rfl
  · rw [if_neg hz]
    have h1 : (stageState T (j + 1) n w).2.2 ⟨y, hy⟩ = Sum.inl () := if_neg hz
    rw [h1]
    rfl
open Classical in
private theorem localHullData_fst_succ (s₁ : ℝ) (j n : ℕ) [NeZero n] (w : MarkedSample ℓ (j + 1) n)
    (Q : Finset (TorusSite n)) :
    (localHullData T s₁ (j + 1) n w Q).1 =
      thickening ((T.stage j).toStepSetup.nextRange / 2) (localCoreZone T s₁ j n w Q) ∩ Q := rfl
open Classical in
private theorem localHullData_snd_succ (s₁ : ℝ) (j n : ℕ) [NeZero n] (w : MarkedSample ℓ (j + 1) n)
    (Q : Finset (TorusSite n)) (y : TorusSite n) :
    (localHullData T s₁ (j + 1) n w Q).2 y = if y ∈ localCoreZone T s₁ j n w Q then
      s₁ + ∑ z ∈ sitesInBlocks ℓ.side {y} ∩ (localHullData T s₁ j (n * ℓ.side) w.1 (sitesInBlocks ℓ.side Q)).1,
        (localHullData T s₁ j (n * ℓ.side) w.1 (sitesInBlocks ℓ.side Q)).2 z
    else if y ∈ (localHullData T s₁ (j + 1) n w Q).1 then s₁ else 0 := rfl
private theorem localCoreZone_subset_coreZone (j n : ℕ) [NeZero n] (w : MarkedSample ℓ (j + 1) n)
    (Q : Finset (TorusSite n))
    (hlo : (localHullData T s₁ j (n * ℓ.side) w.1 (sitesInBlocks ℓ.side Q)).1 ⊆ hullSet T j (n * ℓ.side) w.1) :
    localCoreZone T s₁ j n w Q ⊆ coreZone T j n w := by
  classical
  intro y hy
  rcases Finset.mem_union.mp hy with hC | hcore
  · exact Finset.mem_union_left _ (Finset.mem_inter.mp hC).1
  · exact Finset.mem_union_right _ (coreBlocks_mono _ (attachedSites_mono _ (Finset.filter_subset _ _) hlo
      Finset.inter_subset_left) (Finset.mem_inter.mp hcore).1)
private theorem localHullData_le (h₁ : 0 ≤ s₁) :
    ∀ (j n : ℕ) [NeZero n] (w : MarkedSample ℓ j n) (Q : Finset (TorusSite n)),
    (localHullData T s₁ j n w Q).1 ⊆ hullSet T j n w ∧
      ∀ z ∈ (localHullData T s₁ j n w Q).1, (localHullData T s₁ j n w Q).2 z ≤ siteSize T s₁ j n w z := by
  classical
  intro j
  induction j with
  | zero =>
    intro n _ w Q
    exact ⟨Finset.inter_subset_left, fun z _ => siteSize_nonneg T h₁ 0 n w z⟩
  | succ j ih =>
    intro n _ w Q
    obtain ⟨hlo, hsz⟩ := ih (n * ℓ.side) w.1 (sitesInBlocks ℓ.side Q)
    have hzone := localCoreZone_subset_coreZone T j n w Q hlo
    have hfst : (localHullData T s₁ (j + 1) n w Q).1 ⊆ hullSet T (j + 1) n w := by
      rw [localHullData_fst_succ]
      exact Finset.inter_subset_left.trans (thickening_mono hzone)
    refine ⟨hfst, fun z hz => ?_⟩
    rw [localHullData_snd_succ, siteSize_succ T j n w (hfst hz)]
    by_cases hzz : z ∈ localCoreZone T s₁ j n w Q
    · rw [if_pos hzz, if_pos (hzone hzz)]
      have hsum : ∑ t ∈ sitesInBlocks ℓ.side {z} ∩ (localHullData T s₁ j (n * ℓ.side) w.1 (sitesInBlocks ℓ.side Q)).1,
          (localHullData T s₁ j (n * ℓ.side) w.1 (sitesInBlocks ℓ.side Q)).2 t ≤
          ∑ t ∈ sitesInBlocks ℓ.side {z}, siteSize T s₁ j (n * ℓ.side) w.1 t :=
        (Finset.sum_le_sum fun t ht => hsz t (Finset.mem_inter.mp ht).2).trans
          (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
            fun t _ _ => siteSize_nonneg T h₁ j _ _ t)
      linarith
    · rw [if_neg hzz, if_pos hz]
      split_ifs
      · have : 0 ≤ ∑ t ∈ sitesInBlocks ℓ.side {z}, siteSize T s₁ j (n * ℓ.side) w.1 t :=
          Finset.sum_nonneg fun t _ => siteSize_nonneg T h₁ j _ _ t
        linarith
      · exact le_refl _
private theorem localHullData_eq_on_hullClass (h₁ : 0 ≤ s₁) : ∀ (j : ℕ),
    (∀ i < j, ℓ.side ≤ 6 * (T.stage i).toStepSetup.range ∧
      10 * (T.stage i).toStepSetup.range / ℓ.side + 1 ≤ (T.stage i).toStepSetup.nextRange) →
    ∀ (n : ℕ) [NeZero n] (w : MarkedSample ℓ j n) (z : TorusSite n) (Q : Finset (TorusSite n)), z ∈ hullSet T j n w →
      hullClass (stageRange T j) (hullSet T j n w) z ⊆ Q →
      z ∈ (localHullData T s₁ j n w Q).1 ∧ (localHullData T s₁ j n w Q).2 z = siteSize T s₁ j n w z := by
  classical
  intro j
  induction j with
  | zero =>
    intro _ n _ w z Q hz hQ
    have hzX : z ∈ hullClass (stageRange T 0) (hullSet T 0 n w) z :=
      Finset.mem_filter.mpr ⟨hz, Relation.ReflTransGen.refl⟩
    refine ⟨Finset.mem_inter.mpr ⟨hz, hQ hzX⟩, ?_⟩
    have h0 : siteSize T s₁ 0 n w z = labelSize T s₁ 0 _ := dif_pos hz
    rw [h0]
    rfl
  | succ j ih =>
    intro hsp n _ w z Q hz hQ
    obtain ⟨hL, hr⟩ := hsp j (Nat.lt_succ_self j)
    have hIH := ih (fun i hi => hsp i (Nat.lt_succ_of_lt hi)) (n * ℓ.side) w.1
    obtain ⟨hlo, -⟩ := localHullData_le T h₁ j (n * ℓ.side) w.1 (sitesInBlocks ℓ.side Q)
    have hzone := localCoreZone_subset_coreZone T j n w Q hlo
    have hzX : z ∈ hullClass (stageRange T (j + 1)) (hullSet T (j + 1) n w) z :=
      Finset.mem_filter.mpr ⟨hz, Relation.ReflTransGen.refl⟩
    have hloc : ∀ c ∈ coreZone T j n w, c ∈ hullClass (stageRange T (j + 1)) (hullSet T (j + 1) n w) z →
        c ∈ localCoreZone T s₁ j n w Q := by
      intro c hc hcX
      have := storedBlock_mem_local (L := ℓ.side) (r := (T.stage j).toStepSetup.range)
        (r' := (T.stage j).toStepSetup.nextRange)
        (bad' := (show Finset (TorusBond (n * ℓ.side)) from w.2.2.2).filter
        fun b => b.1 ∈ sitesInBlocks ℓ.side Q)
        (lo := (localHullData T s₁ j (n * ℓ.side) w.1 (sitesInBlocks ℓ.side Q)).1)
        (CQ := hotCoreSites (T.stage j).toStepSetup w.2.2.1 ∩ Q) hr (fun b => Finset.mem_filter)
        (fun y => Finset.mem_inter) (fun t ht h => (hIH t _ ht h).1) hQ hc hcX
      rcases this with h | ⟨h, h'⟩
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨h, h'⟩)
    have hzmem : z ∈ (localHullData T s₁ (j + 1) n w Q).1 := by
      rw [localHullData_fst_succ]
      obtain ⟨c, hc, hd⟩ := (mem_thickening _ _ _).mp hz
      have hcX : c ∈ hullClass (stageRange T (j + 1)) (hullSet T (j + 1) n w) z :=
        mem_hullClass_of_supDist_le hzX (storedBlocks_subset_coarseHull _ _ _ _ _ hc)
          (hd.trans (Nat.div_le_self _ _))
      exact Finset.mem_inter.mpr ⟨(mem_thickening _ _ _).mpr ⟨c, hloc c hc hcX, hd⟩, hQ hzX⟩
    refine ⟨hzmem, ?_⟩
    rw [localHullData_snd_succ, siteSize_succ T j n w hz]
    by_cases hzz : z ∈ localCoreZone T s₁ j n w Q
    · have hzs := hzone hzz
      rw [if_pos hzz, if_pos hzs]
      congr 1
      have hsub : sitesInBlocks ℓ.side {z} ∩
          (localHullData T s₁ j (n * ℓ.side) w.1 (sitesInBlocks ℓ.side Q)).1 ⊆ sitesInBlocks ℓ.side {z} :=
        Finset.inter_subset_left
      rw [← Finset.sum_subset hsub ?_]
      · refine Finset.sum_congr rfl fun t ht => ?_
        obtain ⟨ht1, ht2⟩ := Finset.mem_inter.mp ht
        have hty := hlo ht2
        have hb : parentBlock ℓ.side t = z := Finset.mem_singleton.mp (mem_sitesInBlocks.mp ht1)
        exact (hIH t _ hty (hullClass_subset_of_storedBlock hL hr hQ hzs hzX hty hb)).2
      · intro t ht1 ht2
        refine siteSize_of_not_mem T j _ _ fun hty => ht2 (Finset.mem_inter.mpr ⟨ht1, ?_⟩)
        have hb : parentBlock ℓ.side t = z := Finset.mem_singleton.mp (mem_sitesInBlocks.mp ht1)
        exact (hIH t _ hty (hullClass_subset_of_storedBlock hL hr hQ hzs hzX hty hb)).1
    · have hzs : z ∉ coreZone T j n w := fun h => hzz (hloc z h hzX)
      rw [if_neg hzz, if_pos hzmem, if_neg hzs]
end Draws
section ScaleFlow
private theorem couplingFlow_succ (ℓ : StepParameters) (β : ℝ) (hret : ExpansionReturnsAt ℓ) {t : ℕ}
    (hy : ℓ.y₁ ≤ (couplingFlow ℓ β t).1)
    (hrow : HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2) :
    HasExpansion ℓ (t + 1) (couplingFlow ℓ β (t + 1)).1 (couplingFlow ℓ β (t + 1)).2 ∧
      |(couplingFlow ℓ β (t + 1)).1 - (couplingFlow ℓ β t).1| ≤ 2 * ℓ.B := by
  classical
  obtain ⟨x', ⟨hx', hd⟩, huniq⟩ := hret t _ _ hy hrow
  have hex : ∃ x' : ℝ, HasExpansion ℓ (t + 1) x'
      (kernelImage ℓ (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2) := ⟨x', hx'⟩
  have hch : (couplingFlow ℓ β (t + 1)).1 = hex.choose := dif_pos hex
  obtain ⟨f, hf, -⟩ := hex.choose_spec.2
  have heq : (couplingFlow ℓ β (t + 1)).1 = x' := hch.trans (huniq _ f hf)
  rw [heq]
  exact ⟨hx', hd⟩
private theorem hasExpansion_couplingFlow (ℓ : StepParameters) (β : ℝ) (hret : ExpansionReturnsAt ℓ)
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) :
    ∀ t, (∀ j < t, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) →
      HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2
  | 0, _ => h0
  | t + 1, h => (couplingFlow_succ ℓ β hret (h t (Nat.lt_succ_self t))
      (hasExpansion_couplingFlow ℓ β hret h0 t fun j hj => h j (Nat.lt_succ_of_lt hj))).1
private theorem le_clusterRange {L : ℕ} {x : ℝ} (hx : (L : ℝ) ^ 100 ≤ x) : L ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
private theorem clusterRange_le_two_mul {x x' : ℝ} (h0 : 0 ≤ x') (hx : 0 ≤ x) (h : x ≤ 2 * x') :
    clusterRange x ≤ 2 * clusterRange x' := by
  have h2 : (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h3 : x ^ ((1 : ℝ) / 100) ≤ (2 * x') ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow hx h (by norm_num)
  have h4 : (2 * x') ^ ((1 : ℝ) / 100) = (2 : ℝ) ^ ((1 : ℝ) / 100) * x' ^ ((1 : ℝ) / 100) :=
    Real.mul_rpow (by norm_num) h0
  have h5 : x' ^ ((1 : ℝ) / 100) ≤ (clusterRange x' : ℝ) := Nat.le_ceil _
  have h6 : 0 ≤ x' ^ ((1 : ℝ) / 100) := Real.rpow_nonneg h0 _
  have h7 : x ^ ((1 : ℝ) / 100) ≤ ((2 * clusterRange x' : ℕ) : ℝ) := by
    push_cast
    nlinarith
  exact Nat.ceil_le.mpr h7
private theorem spacing_of_ranges {L r r' : ℕ} (hL : 100 ≤ L) (h1 : L ≤ r) (h2 : L ≤ r') (h3 : r ≤ 2 * r') :
    L ≤ 6 * r ∧ 10 * r / L + 1 ≤ r' := by
  refine ⟨by omega, ?_⟩
  have h4 : 10 * r ≤ L * (r' - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, r' = k + 1 := ⟨r' - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : 100 * k ≤ L * k := Nat.mul_le_mul_right k hL
    omega
  have h5 := Nat.div_le_of_le_mul h4
  omega
end ScaleFlow
theorem localHullSubset : localHullSubsetStatement := by
  classical
  unfold localHullSubsetStatement EventuallyInParameters
  intro a ha
  refine ⟨100, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L hodd hL Tb hTa hTL hdrawn hcold hhalf hrt hder
  refine ⟨0, ?_⟩
  intro Kr hKc hη hN hfits hresp
  refine ⟨max ((L : ℝ) ^ 100) (2 * Tb.B), ?_⟩
  intro y hy hret hrow
  have hyL : (L : ℝ) ^ 100 ≤ y := (le_max_left _ _).trans hy
  have hyB : 2 * Tb.B ≤ y := (le_max_right _ _).trans hy
  have hy0 : 0 ≤ y := le_trans (by positivity) hyL
  have h₁ : 0 ≤ Kr.s₁ := by
    have hf := hfits y
    have hC : 0 ≤ Kr.C₀ + 2 := by
      have h1 := hf.Kc_ge
      have h2 := hf.N₀_nonneg
      have h3 : (Tb.stepParameters y).coupling = a := hTa
      rw [hf.C₀_eq, h3]
      linarith
    have h3 : (Tb.stepParameters y).coupling = a := hTa
    rw [hf.s₁_eq, h3]
    have : 0 ≤ 2 * (((Tb.stepParameters y).side : ℕ) : ℝ) ^ 4 * (Kr.C₀ + 2) := by positivity
    linarith
  intro g β K m T
  have spaced : ∀ (u n : ℕ) [NeZero n], HullChainAtLevel Tb y g β K m T u n → ∀ i < u,
      (Tb.stepParameters y).side ≤ 6 * (T.stage i).toStepSetup.range ∧
        10 * (T.stage i).toStepSetup.range / (Tb.stepParameters y).side + 1 ≤
          (T.stage i).toStepSetup.nextRange := by
    intro u n _ hat i hi
    have hrun := hat.chain
    have hiK : i < K := lt_of_lt_of_le hi hat.le
    have hpass := hrun.isFirst
    have hfl : y ≤ (g ^ 2)⁻¹ := hrun.le_inv_sq
    have hab := hrun.upper_le
    have hBpos : 1 ≤ Tb.B := hdrawn.B_ge
    have hwin : windowUpper (Tb.stepParameters y) g = (g ^ 2)⁻¹ + 2 * Tb.B := rfl
    have hlow : ∀ j < K, y + 2 * Tb.B < (couplingFlow (Tb.stepParameters y) β j).1 := fun j hj => by
      have := hpass.2 j hj
      rw [hwin] at this
      linarith
    have hβ : y ≤ β := by
      rw [hwin] at hab
      linarith
    have hy₁ : (Tb.stepParameters y).y₁ = y := rfl
    have hrowi := hasExpansion_couplingFlow (Tb.stepParameters y) β hret (hrow β hβ) i fun j hj => by
      rw [hy₁]
      linarith [hlow j (hj.trans hiK)]
    have hxi := hlow i hiK
    have hstep := (couplingFlow_succ (Tb.stepParameters y) β hret (by rw [hy₁]; linarith) hrowi).2
    have hBB : (Tb.stepParameters y).B = Tb.B := rfl
    rw [hBB] at hstep
    have hd := abs_le.mp hstep
    have e1 : (T.stage i).toStepSetup.range = clusterRange (couplingFlow (Tb.stepParameters y) β i).1 := by
      show clusterRange (T.stage i).coupling = _
      rw [hrun.follows i (by omega)]
    have e2 : (T.stage i).toStepSetup.nextRange =
        clusterRange (couplingFlow (Tb.stepParameters y) β (i + 1)).1 := by
      show clusterRange (T.stage (i + 1)).coupling = _
      rw [hrun.follows (i + 1) (by omega)]
    have hLL : (Tb.stepParameters y).side = L := hTL
    rw [e1, e2, hLL]
    have hx' : y ≤ (couplingFlow (Tb.stepParameters y) β (i + 1)).1 := by linarith [hd.1]
    exact spacing_of_ranges hL (le_clusterRange (by linarith)) (le_clusterRange (by linarith))
      (clusterRange_le_two_mul (by linarith) (by linarith) (by linarith [hd.2]))
  refine ⟨?_, ?_⟩
  · intro u n _ hat w
    refine ⟨fun Q => localHullData_le T h₁ u n w Q, ?_⟩
    intro z D hD hz hdiam
    refine localHullData_eq_on_hullClass T h₁ u (spaced u n hat) n w z _ hz ?_
    intro v hv
    have hzX : z ∈ hullClass (stageRange T u) (hullSet T u n w) z :=
      Finset.mem_filter.mpr ⟨hz, Relation.ReflTransGen.refl⟩
    have h1 : supDist v z ≤ supDiam (hullClass (stageRange T u) (hullSet T u n w) z) :=
      (Finset.le_sup (f := fun b => supDist v b) hzX).trans
        (Finset.le_sup (f := fun a => (hullClass (stageRange T u) (hullSet T u n w) z).sup fun b => supDist a b) hv)
    have h2 : supDiam (hullClass (stageRange T u) (hullSet T u n w) z) ≤ ⌊2 * D⌋₊ :=
      Nat.le_floor (by linarith)
    exact (mem_thickening _ _ _).mpr ⟨z, Finset.mem_singleton_self z, by omega⟩
  · intro j n _ hat w Q
    exact localCoreZone_subset_coreZone T j n w Q (localHullData_le T h₁ j _ w.1 _).1
end YangMills.Construction.HullTrees
end
