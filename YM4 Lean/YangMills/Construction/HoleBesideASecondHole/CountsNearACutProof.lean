import YangMills.Construction.HoleBesideASecondHole.ComponentsOfLumps
import YangMills.Construction.HoleBesideASecondHole.CountsNearACut
import YangMills.Construction.HoleBesideASecondHole.DistancesBlocksAndLumps
import YangMills.Construction.HoleBesideASecondHole.PathsAndHolonomies
import YangMills.Construction.HoleBesideASecondHole.SitesOfBlocksAndCells
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HoleSavings
open BlockAverages LumpContours Holes PathHolonomy BlockSites
namespace CutCounting
variable {F : BlockFrame}
theorem cutBelow_mono {X Y : Finset F.Cell} (h : X ⊆ Y) : cutBelow F.depth X ⊆ cutBelow F.depth Y := by
  unfold cutBelow
  exact Finset.biUnion_subset_biUnion_of_subset_left _ h
theorem exists_cell_of_mem_cutBelow {X : Finset F.Cell} {x : F.Site F.depth}
    (hx : x ∈ cutBelow F.depth X) : ∃ u ∈ X, x ∈ sitesBelow F.depth u := by
  unfold cutBelow at hx
  exact Finset.mem_biUnion.1 hx
theorem exists_cell_of_subset_cutBelow {l : Finset (F.Site F.depth)} {B : Finset F.Cell}
    (h : l ⊆ cutBelow F.depth B) : ∀ u ∈ l, ∃ v ∈ B, u ∈ sitesBelow F.depth v :=
  fun _ hu => exists_cell_of_mem_cutBelow (h hu)
theorem card_cellBall_le (z : F.Cell) (r : ℕ) : (_root_.YangMills.Construction.LumpContours.cellBall z r).card ≤ (2 * r + 1) ^ 4 := by
  refine Finset.card_image_le.trans ?_
  rw [card_centredCube (⟨r, rfl⟩ : Odd (2 * r + 1))]
end CutCounting
attribute [local irreducible] _root_.YangMills.Construction.LumpContours.cellBall
open CutCounting in
open Classical in
set_option maxHeartbeats 1000000 in
theorem countsNearCut_holds (hcomp : LinkComponentProperties) (hd : TorusDistanceBlockLumpFacts) :
    countsNearCutStatement := by
  intro F g a s θ C J₀ D idx o hL hT hS
  have hext : ∀ k, 0 < F.extent k := fun k => by
    have h1 := hT.1 k
    have h2 := hT.2
    omega
  have hLpos := hL.pos
  obtain ⟨dcomm, dtri, denl, dbelow, dcell, ctri, ccomm, cball, dlump⟩ := hd F hLpos hext
  obtain ⟨c1, c2, -, -, -⟩ := hcomp F D.hotFineLumps
  set r := holeScale J₀ (topScaleIndex J₀ F.blockSide) with hr
  have hlumpOf : ∀ l ∈ D.hotFineLumps, ∃ x, l = lumpOf g x := by
    intro l hl
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 hl
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨x, rfl⟩
  have hblock : ∀ l ∈ D.hotFineLumps, ∃ z : F.Cell, l ⊆ sitesBelow F.depth z ∧ ∀ u ∈ l, enclosingCell u = z := by
    intro l hl
    obtain ⟨x, rfl⟩ := hlumpOf l hl
    obtain ⟨-, h2, -⟩ := dlump hL g x
    exact ⟨enclosingCell x, h2, fun u hu => (dbelow hL u _).1 (h2 hu)⟩
  have hhole : ∀ k ∈ D.componentsAtCore C, ∀ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o,
      H ∈ D.holesAt C idx o ∧ ∃ l ∈ H.lumps, l ∈ D.hotFineLumps ∧ l ∈ k ∧
        linkComponent r D.hotFineLumps l = k := by
    intro k hk H hH
    have hHh : H ∈ D.holesAt C idx o := Finset.mem_biUnion.2 ⟨k, hk, hH⟩
    refine ⟨hHh, ?_⟩
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hH
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk'
    obtain ⟨l₁, hl₁, rfl⟩ := Finset.mem_image.1 hk1
    have hin : l₁ ∈ linkComponent (holeScale J₀ (idx k)) D.hotFineLumps l₁ := c1 _ _ hl₁
    have hlk : l₁ ∈ k := hk2 hin
    refine ⟨l₁, hin, hl₁, hlk, ?_⟩
    obtain ⟨hk3, -⟩ := Finset.mem_filter.1 hk
    obtain ⟨l₀, _, hl₀⟩ := Finset.mem_image.1 hk3
    rw [← hl₀] at hlk ⊢
    exact c2 _ _ _ hlk
  refine ⟨fun X => ?_, fun y hy X hX => ?_, fun X => ?_⟩
  · refine Finset.card_le_card_of_surjOn (fun l => linkComponent r D.hotFineLumps l) ?_
    intro k hk
    obtain ⟨hk1, H, hH, x, hx⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hk)
    obtain ⟨hHh, l, hlH, hl, hlk, hcl⟩ := hhole k hk1 H hH
    obtain ⟨hxo, hxX⟩ := Finset.mem_inter.1 hx
    obtain ⟨r1, r2⟩ := hS.radius_bounds H hHh
    obtain ⟨u, hu, hdist⟩ := (denl _ _ _ _).1 (hS.outer_subset H hHh l hlH hxo)
    obtain ⟨z, hz, hzu⟩ := hblock l hl
    obtain ⟨v, hv, hxv⟩ := exists_cell_of_mem_cutBelow hxX
    have h3 : supDist u x ≤ 1 * F.blockSide := by
      have : 3 * H.radius ≤ 1 * F.blockSide := by nlinarith
      omega
    have h4 := dcell hL 1 u x h3
    rw [hzu u hu, (dbelow hL x v).1 hxv] at h4
    refine ⟨l, ?_, hcl⟩
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hl, v, hv, z, ?_, hz⟩)
    rw [ccomm]
    omega
  · have hfew := hS.few_near_uncrowded y hy
    generalize _root_.YangMills.Construction.LumpContours.cellBall y 1 = B at hfew hX
    refine le_trans ?_ hfew.le
    obtain ⟨f, hf⟩ : ∃ f : Hole F → Finset (Finset (F.Site F.depth)), ∀ H, f H =
        if h : H.lumps.Nonempty then linkComponent r D.hotFineLumps h.choose else ∅ := ⟨_, fun _ => rfl⟩
    refine Finset.card_le_card_of_surjOn f ?_
    intro k hk
    obtain ⟨hk1, H, hH, x, hx⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hk)
    obtain ⟨hHh, l, hlH, hl, hlk, hcl⟩ := hhole k hk1 H hH
    obtain ⟨hxo, hxX⟩ := Finset.mem_inter.1 hx
    have hxb : x ∈ cutBelow F.depth B := cutBelow_mono hX hxX
    refine ⟨H, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hHh, x, Finset.mem_inter.2 ⟨hxo, hxb⟩⟩), ?_⟩
    have hne : H.lumps.Nonempty := ⟨l, hlH⟩
    rw [hf, dif_pos hne]
    obtain ⟨k', hk', hHe⟩ := Finset.mem_image.1 hH
    obtain ⟨_, hk2⟩ := Finset.mem_filter.1 hk'
    have hsub : H.lumps ⊆ k := by
      rw [← hHe]
      exact hk2
    have hch : hne.choose ∈ k := hsub hne.choose_spec
    rw [← hcl] at hch ⊢
    exact c2 _ _ _ hch
  · obtain ⟨z, hzd⟩ : ∃ z : Finset (F.Site F.depth) → F.Cell, ∀ l,
        z l = if h : l.Nonempty then enclosingCell h.choose else 0 :=
      ⟨_, fun _ => rfl⟩
    have hnear : ((cutBonds X).filter fun c =>
        ¬ (nearbyLumps D.hotFineLumps c.1 = ∅ ∧
          nearbyLumps D.hotFineLumps (c.1 + unitStep F.top c.2) = ∅)) ⊆
        (D.nearbyFineLumps X).biUnion fun l => (_root_.YangMills.Construction.LumpContours.cellBall (z l) 3) ×ˢ (Finset.univ : Finset (Fin 4)) := by
      intro c hc
      obtain ⟨hc1, hc2⟩ := Finset.mem_filter.1 hc
      obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hc1
      have hcX : c.1 ∈ X := (Finset.mem_product.1 hb1).1
      have hend : c.1 + unitStep F.top c.2 ∈ _root_.YangMills.Construction.LumpContours.cellBall c.1 1 := mem_cellBall_iff.2 ⟨Pi.single c.2 1, fun k => by
        by_cases h : k = c.2
        · subst h
          simp
        · simp [h], rfl⟩
      have hd1 : cellSupDist c.1 (c.1 + unitStep F.top c.2) ≤ 1 := (cball _ 1 _).1 hend
      have hfind : ∀ e : F.Cell, cellSupDist c.1 e ≤ 1 → nearbyLumps D.hotFineLumps e ≠ ∅ →
          c ∈ (D.nearbyFineLumps X).biUnion fun l => (_root_.YangMills.Construction.LumpContours.cellBall (z l) 3) ×ˢ (Finset.univ : Finset (Fin 4)) := by
        intro e he hne
        obtain ⟨l, hl⟩ := Finset.nonempty_iff_ne_empty.2 hne
        obtain ⟨hl1, hl2⟩ := Finset.mem_filter.1 hl
        obtain ⟨w, hw, hwz⟩ := hblock l hl1
        have hln : l.Nonempty := by
          obtain ⟨x, rfl⟩ := hlumpOf l hl1
          exact ⟨x, (dlump hL g x).1⟩
        obtain ⟨u, hu⟩ := hln
        obtain ⟨v, hv, huv⟩ := exists_cell_of_subset_cutBelow hl2 u hu
        have e1 : v = w := by
          rw [← (dbelow hL u v).1 huv]
          exact hwz u hu
        have hew : cellSupDist e w ≤ 2 := (cball e 2 w).1 (e1 ▸ hv)
        have hcw : cellSupDist c.1 w ≤ 3 := by
          have := ctri c.1 e w
          omega
        have hzl : z l = w := by
          have hne' : l.Nonempty := ⟨u, hu⟩
          rw [hzd, dif_pos hne']
          exact hwz _ hne'.choose_spec
        refine Finset.mem_biUnion.2 ⟨l, Finset.mem_filter.2 ⟨hl1, c.1, hcX, w, hcw, hw⟩, ?_⟩
        rw [hzl]
        refine Finset.mem_product.2 ⟨(cball w 3 c.1).2 ?_, Finset.mem_univ _⟩
        rw [ccomm]
        exact hcw
      by_cases h1 : nearbyLumps D.hotFineLumps c.1 = ∅
      · exact hfind _ hd1 fun h2 => hc2 ⟨h1, h2⟩
      · exact hfind _ (by have : cellSupDist c.1 c.1 = 0 := by simp [cellSupDist]
                          omega) h1
    refine (Finset.card_le_card hnear).trans (Finset.card_biUnion_le.trans ?_)
    have hone : ∀ l ∈ D.nearbyFineLumps X,
        ((_root_.YangMills.Construction.LumpContours.cellBall (z l) 3) ×ˢ (Finset.univ : Finset (Fin 4))).card ≤ 9604 := by
      intro l _
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      have h7 := card_cellBall_le (z l) 3
      omega
    calc ∑ l ∈ D.nearbyFineLumps X, ((_root_.YangMills.Construction.LumpContours.cellBall (z l) 3) ×ˢ (Finset.univ : Finset (Fin 4))).card
        ≤ ∑ _l ∈ D.nearbyFineLumps X, 9604 := Finset.sum_le_sum hone
      _ = 9604 * (D.nearbyFineLumps X).card := by
        simp [mul_comm]
end YangMills.Construction.HoleSavings
end
