import YangMills.Construction.CellOfTheFlow.AFalseSiteHoldsALongClass
import YangMills.Construction.ClusterExpansionOfAStep.BallsAndBlocksOfATorusForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CellWindows
open TorusLumps TorusFields TorusBalls StepSettings WeightedResponses BlockAverages
variable {ℓ : TorusLumps.StepParameters}
section Helpers
variable {n : ℕ} [NeZero n] {r : ℕ}
open Classical in
private theorem chainConnected_filter {Y : Finset (TorusSite n)} {a z : TorusSite n}
    (h : ChainConnected r Y a z) :
    ChainConnected r (Y.filter (ChainConnected r Y a)) a z := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    exact ih.tail ⟨Finset.mem_filter.mpr ⟨hbc.1, hab⟩,
      Finset.mem_filter.mpr ⟨hbc.2.1, hab.tail hbc⟩, hbc.2.2⟩
abbrev _root_.YangMills.DeltaSharedProofs.p501436 := @chainConnected_filter
open Classical in
private theorem chainConnected_within_component {X K : Finset (TorusSite n)}
    (hK : K ∈ chainComponents r X) {y z : TorusSite n}
    (hy : y ∈ K) (hz : z ∈ K) : ChainConnected r K y z := by
  have h := chainConnected_filter (chainConnected_of_mem_chainComponents hK hy hz)
  rwa [← eq_filter_of_mem_chainComponents hK hy] at h
omit [NeZero n] in
private theorem chainConnected_mono {A B : Finset (TorusSite n)} (hAB : A ⊆ B) {a b : TorusSite n}
    (h : ChainConnected r A a b) : ChainConnected r B a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail ⟨hAB hs.1, hAB hs.2.1, hs.2.2⟩
omit [NeZero n] in
private theorem supDist_le_siteDiameter {S : Finset (TorusSite n)} {y z : TorusSite n}
    (hy : y ∈ S) (hz : z ∈ S) :
    supDist y z ≤ siteDiameter S :=
  le_trans (Finset.le_sup (f := fun z => supDist y z) hz)
    (Finset.le_sup (f := fun y => S.sup fun z => supDist y z) hy)
private theorem le_mul_ceilDiv (a L : ℕ) (hL : 0 < L) : a ≤ L * ceilDiv a L := by
  have h1 := Nat.div_add_mod (a + L - 1) L
  have h2 := Nat.mod_lt (a + L - 1) hL
  unfold ceilDiv
  omega
abbrev _root_.YangMills.SharedProofs.p15502 := @le_mul_ceilDiv
private theorem mul_sub_le_supDist_of_deep (L : ℕ) [NeZero L] {ρ D : ℕ} (hρ : 0 < ρ)
    {c : Finset (TorusSite n)} {z : TorusSite n}
    (hdeep : ∀ w, w ∉ c → D ≤ supDist z w) {x w : TorusSite (n * L)} (hx : parentBlock L x = z)
    (hw : w ∉ sitesInBlocks L (interiorAtDepth ρ c)) : L * (D - ρ) ≤ supDist x w := by
  classical
  have hb : parentBlock L w ∉ interiorAtDepth ρ c :=
    fun h => hw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hex : ∃ w', w' ∉ c ∧ supDist (parentBlock L w) w' < ρ := by
    by_cases hc : parentBlock L w ∈ c
    · by_contra hno
      refine hb (Finset.mem_filter.mpr ⟨hc, fun w' hw' => ?_⟩)
      by_contra hlt
      exact hno ⟨w', hw', not_le.mp hlt⟩
    · exact ⟨_, hc, by rw [supDist_self]; exact hρ⟩
  obtain ⟨w', hw', hd⟩ := hex
  have h1 := hdeep w' hw'
  have h2 := supDist_triangle z (parentBlock L w) w'
  have h3 := supDist_parentBlock_le_div_add_one L x w
  rw [hx] at h3
  obtain ⟨q, hq⟩ : ∃ q, q = supDist x w / L := ⟨_, rfl⟩
  rw [← hq] at h3
  have h4 : D - ρ ≤ q := by omega
  rw [hq] at h4
  exact le_trans (Nat.mul_le_mul_left L h4) (Nat.mul_div_le _ _)
end Helpers
section Step
variable {n : ℕ} [NeZero n] {L : ℕ} [NeZero L]
private theorem extraSite_descent_step {r g : ℕ} {bad : Finset (TorusBond (n * L))}
    {Yp Y Rw : Finset (TorusSite (n * L))}
    {C : Finset (TorusSite n)} {z : TorusSite n}
    (hz : z ∈ C ∪ coreBlocks L r
      (upperAttached L r (windowSeeds L bad Yp C Rw) (sitesInBlocks L C) Rw))
    (hz' : z ∉ storedBlocks L r bad Y C)
    (hfar : ∀ x w : TorusSite (n * L), parentBlock L x = z → w ∉ Rw → g ≤ supDist x w)
    (hg : 28 * r ≤ g) :
    (∃ y ∈ Yp, y ∉ Y) ∨ ∃ X ∈ clusterComponents L r bad Y C, ¬ (X ∩ sitesInBlocks L C).Nonempty ∧
      IsLongWithin L r g (supportOfComponent L bad Y X) Rw := by
  classical
  have hzC : z ∉ C := fun h => hz' (Finset.mem_union_left _ h)
  have hzcore : z ∉ coreBlocks L r (attachedSites L r bad Y C) :=
    fun h => hz' (Finset.mem_union_right _ h)
  have hz1 := (Finset.mem_union.mp hz).resolve_left hzC
  obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hz1).2
  obtain ⟨hxb, hxw⟩ := Finset.mem_inter.mp hx
  have hxz : parentBlock L x = z := by
    have := (Finset.mem_filter.mp hxb).2
    simpa using this
  obtain ⟨t, ht, htx⟩ := (mem_thickening _ _ _).mp hxw
  obtain ⟨κ, hκ, htκ⟩ := Finset.mem_biUnion.mp ht
  obtain ⟨hκc, hκt⟩ := Finset.mem_filter.mp hκ
  have htκ' : t ∈ κ := htκ
  by_cases hextra : ∃ y ∈ κ, y ∈ Yp ∧ y ∉ Y
  · obtain ⟨y, _, hy, hy'⟩ := hextra
    exact Or.inl ⟨y, hy, hy'⟩
  right
  have hextra : ∀ y ∈ κ, y ∈ Yp → y ∈ Y := fun y hy hy' => by
    by_contra hno
    exact hextra ⟨y, hy, hy', hno⟩
  have hκX : ∀ p ∈ κ, p ∈ (bad.image Prod.fst ∪ Yp ∪ sitesInBlocks L C) ∩ Rw :=
    fun p hp => subset_of_mem_chainComponents hκc hp
  have hκS : κ ⊆ bad.image Prod.fst ∪ Y ∪ sitesInBlocks L C := by
    intro p hp
    have h1 := (Finset.mem_inter.mp (hκX p hp)).1
    rcases Finset.mem_union.mp h1 with h2 | h2
    · rcases Finset.mem_union.mp h2 with h3 | h3
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h3)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hextra p hp h3))
    · exact Finset.mem_union_right _ h2
  obtain ⟨X, hX, htX⟩ : ∃ X ∈ clusterComponents L r bad Y C, t ∈ X :=
    exists_mem_chainComponents (hκS htκ')
  have hX' : X ∈ chainComponents (10 * r) (bad.image Prod.fst ∪ Y ∪ sitesInBlocks L C) := hX
  have hκinX : κ ⊆ X := fun p hp =>
    mem_of_chainConnected_of_mem_chainComponents hX' htX (hκS hp)
      (chainConnected_mono hκS (chainConnected_within_component hκc htκ' hp))
  have hfree : ¬ (X ∩ sitesInBlocks L C).Nonempty := by
    intro hne
    apply hzcore
    have hatt : t ∈ attachedSites L r bad Y C :=
      Finset.mem_biUnion.mpr ⟨X, Finset.mem_filter.mpr ⟨hX, hne⟩, htX⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨x, Finset.mem_inter.mpr ⟨hxb, (mem_thickening _ _ _).mpr ⟨t, hatt, htx⟩⟩⟩⟩
  refine ⟨X, hX, hfree, ?_⟩
  have hnoLC : ¬ (κ ∩ sitesInBlocks L C).Nonempty := by
    rintro ⟨p, hp⟩
    obtain ⟨hp1, hp2⟩ := Finset.mem_inter.mp hp
    exact hfree ⟨p, Finset.mem_inter.mpr ⟨hκinX hp1, hp2⟩⟩
  obtain ⟨u', hu', w, hw, huw⟩ := hκt.resolve_left hnoLC
  refine ⟨κ, ?_, ⟨t, htκ'⟩, fun y hy z' hz'' => chainConnected_within_component hκc hy hz'', ?_⟩
  · intro p hp
    refine Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp (hκX p hp)).2⟩
    have hpX := hκinX hp
    rcases Finset.mem_union.mp (hκS hp) with h2 | h2
    · rcases Finset.mem_union.mp h2 with h3 | h3
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h3
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨b, Finset.mem_filter.mpr ⟨hb, hpX⟩, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨h3, hpX⟩)
    · exact absurd ⟨p, Finset.mem_inter.mpr ⟨hpX, h2⟩⟩ hfree
  · have h1 := hfar x w hxz hw
    have h2 := supDist_triangle x t w
    have h3 := supDist_triangle t u' w
    have h4 := supDist_le_siteDiameter htκ' hu'
    omega
end Step
private theorem extraSite_descent (T : StageTower ℓ) (k : ℕ) : ∀ (s : ℕ), s ≤ k → ∀ (n : ℕ) [NeZero n]
    (u : MarkedSample ℓ s n) (c : Finset (TorusSite n)) (v : TorusSite n),
    v ∈ upperHull T k s n u c → v ∉ stageHull T s n u → ∃ j < s, HasLongSupport T k j s n u c := by
  intro s
  induction s with
  | zero =>
    intro _ n _ u c v hv hv'
    have hv2 : v ∈ (stageState T 0 n u).2.1 ∩ interiorAtDepth (windowDepth T k 0) c := hv
    exact absurd (Finset.mem_inter.mp hv2).1 hv'
  | succ s ih =>
    intro hs n _ u c v hv hv'
    have hv2 : v ∈ interiorAtDepth (windowDepth T k (s + 1)) c ∩ thickening (stageRange T (s + 1) / 2)
        (upperZone T k s (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.2
          (upperHull T k s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c)) c) := hv
    obtain ⟨hvdeep, hvw⟩ := Finset.mem_inter.mp hv2
    obtain ⟨z, hzZ, hvz⟩ := (mem_thickening _ _ _).mp hvw
    have hvd : ∀ w, w ∉ c → windowDepth T k (s + 1) ≤ supDist v w := by
      classical
      exact (Finset.mem_filter.mp hvdeep).2
    have hz' : z ∉ storedBlocks ℓ.side (stageRange T s) u.2.2.2 (stageHull T s (n * ℓ.side) u.1)
        (hotCoreSites (T.stage s).toStepSetup u.2.2.1) := by
      intro h
      apply hv'
      have : v ∈ thickening (stageRange T (s + 1) / 2)
          (storedBlocks ℓ.side (stageRange T s) u.2.2.2 (stageHull T s (n * ℓ.side) u.1)
            (hotCoreSites (T.stage s).toStepSetup u.2.2.1)) := (mem_thickening _ _ _).mpr ⟨z, h, hvz⟩
      exact this
    have hdepth : windowDepth T k (s + 1) =
        blockDepth T k s + ceilDiv (windowLength T k s) ℓ.side + stageRange T (s + 1) := rfl
    have hρ : 0 < blockDepth T k s := lt_of_lt_of_le (Nat.succ_pos _) (le_max_right _ _)
    have hLpos : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne _)
    have hzdeep : ∀ w, w ∉ c →
        blockDepth T k s + ceilDiv (windowLength T k s) ℓ.side ≤ supDist z w := by
      intro w hw
      have h1 := hvd w hw
      have h2 := supDist_triangle v z w
      omega
    have hfar : ∀ x w : TorusSite (n * ℓ.side), parentBlock ℓ.side x = z →
        w ∉ sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) c) →
          windowLength T k s ≤ supDist x w := by
      intro x w hx hw
      have h1 := mul_sub_le_supDist_of_deep ℓ.side hρ hzdeep hx hw
      have h2 : blockDepth T k s + ceilDiv (windowLength T k s) ℓ.side - blockDepth T k s =
          ceilDiv (windowLength T k s) ℓ.side := by omega
      rw [h2] at h1
      exact le_trans (le_mul_ceilDiv _ _ hLpos) h1
    have hg : 28 * stageRange T s ≤ windowLength T k s := by
      have h1 : 1 ≤ k - s := by omega
      have h2 : 2 ^ 12 * stageRange T s * 1 ≤ 2 ^ 12 * stageRange T s * (k - s) :=
        Nat.mul_le_mul_left _ h1
      unfold windowLength
      omega
    rcases extraSite_descent_step (Finset.mem_inter.mp hzZ).1 hz' hfar hg with h | h
    · obtain ⟨y, hy, hy'⟩ := h
      obtain ⟨j, hj, hl⟩ := ih (by omega) (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c) y hy hy'
      exact ⟨j, by omega, Or.inr hl⟩
    · obtain ⟨X, hX, hfree, hlong⟩ := h
      refine ⟨s, Nat.lt_succ_self s, Or.inl ⟨rfl, _, ?_, hlong⟩⟩
      exact Finset.mem_image.mpr ⟨X, Finset.mem_filter.mpr ⟨hX, hfree⟩, rfl⟩
theorem extraHullSiteHasLongSupport : extraHullSiteHasLongSupportStatement := by
  intro a _
  refine ⟨0, fun _ => 1, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ _ _
  refine ⟨0, ?_⟩
  intro y _ _ _ T β k _ s hs m _ u G κ _ v hv hv'
  exact extraSite_descent T k s hs m u _ v hv hv'
end YangMills.Construction.CellWindows
end
