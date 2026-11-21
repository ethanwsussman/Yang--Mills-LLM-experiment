import YangMills.Construction.HoleBesideASecondHole.BoxesAtACellClose
import YangMills.Construction.HoleBesideASecondHole.ContoursOfABondAreMostlyGood
import YangMills.Construction.HoleBesideASecondHole.DistancesBlocksAndLumps
import YangMills.Construction.HoleBesideASecondHole.MeanOfAProductOfGroupVariablesProof
import YangMills.Construction.HoleBesideASecondHole.MeansAtABondProof
import YangMills.Construction.HoleBesideASecondHole.MeansAtACoreBond
import YangMills.Construction.HoleBesideASecondHole.SitesOfBlocksAndCells
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages PathHolonomy LumpContours BondMeans Holes HoleSavings BlockSites GroupMeans ChainGauges
  BondContours BlockTrees
namespace CoreBondMeans
variable {F : BlockFrame}
theorem cellCentre_depth_eq_refineSite (y : F.Cell) : cellCentre F.depth y = refineSite y := by apply _root_.YangMills.Construction.BondMeans.cellCentre_eq_refineSite <;> assumption
theorem mem_cutBelow_of_mem {X : Finset F.Cell} {u : F.Cell} {x : F.Site F.depth} (hu : u ∈ X)
    (hx : x ∈ sitesBelow F.depth u) : x ∈ cutBelow F.depth X := by
  unfold cutBelow
  exact Finset.mem_biUnion.2 ⟨u, hu, hx⟩
theorem sitesBelow_union_subset_cutBelow {X : Finset F.Cell} {u v : F.Cell} (hu : u ∈ X) (hv : v ∈ X) :
    sitesBelow F.depth u ∪ sitesBelow F.depth v ⊆ cutBelow F.depth X :=
  Finset.union_subset (fun _ h => mem_cutBelow_of_mem hu h) (fun _ h => mem_cutBelow_of_mem hv h)
theorem cellSupDist_self_eq_zero (y : F.Cell) : cellSupDist y y = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem offsetInBlock_zero (hL : Odd F.blockSide) : OffsetInBlock F.blockSide 0 := by
  intro m
  obtain ⟨k, hk⟩ := hL
  simp only [Pi.zero_apply, abs_zero]
  rw [hk]
  push_cast
  omega
open Classical in
theorem base_mem_sitesBelow (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth)
    (hL : Odd F.blockSide) (hB : IsBaseChoice J₀ h b) (u : F.Cell) : b u ∈ sitesBelow F.depth u := by
  by_cases he : nearbyLumps h u = ∅ ∨ IsCrowded J₀ h u
  · rw [(hB u).1 he, cellCentre_depth_eq_refineSite]
    have := refineSite_add_mem_sitesBelow F.depth u (offsetInBlock_zero hL)
    simpa [_root_.YangMills.Construction.PathHolonomy.siteOfCoords_zero] using this
  · exact ((hB u).2 he).1
theorem cutPlaquettes_mono {j : ℕ} {A B : Finset (F.Site j)} (h : A ⊆ B) {p : F.Site j × Fin 4 × Fin 4}
    (hp : p ∈ cutPlaquettes A) : p ∈ cutPlaquettes B := by
  obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hp |>.2 |> fun x => (⟨(Finset.mem_filter.1 hp).1, x.1, x.2⟩ :
    p ∈ A ×ˢ (Finset.univ ×ˢ Finset.univ) ∧ p.2.1 < p.2.2 ∧ plaquetteCorners p ⊆ A)
  refine Finset.mem_filter.2 ⟨?_, h2, h3.trans h⟩
  obtain ⟨a, b⟩ := Finset.mem_product.1 h1
  exact Finset.mem_product.2 ⟨h a, b⟩
theorem cutBonds_mono {j : ℕ} {A B : Finset (F.Site j)} (h : A ⊆ B) {b : F.Site j × Fin 4}
    (hb : b ∈ cutBonds A) : b ∈ cutBonds B := by
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hb
  obtain ⟨a, c⟩ := Finset.mem_product.1 h1
  exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h a, c⟩, h h2⟩
theorem card_image_outerBox_le (H : Hole F) (k : Fin 4) :
    (H.outerBox.image fun z => z k).card ≤ 4 * H.radius + 1 := by
  have hsub : (H.outerBox.image fun z => z k) ⊆
      (Finset.Icc (-(2 * H.radius : ℤ)) (2 * H.radius)).image
        fun c : ℤ => H.centre k + (c : ZMod (F.period F.depth k)) := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
    simp only [Hole.outerBox, thicken, Finset.singleton_biUnion] at hz
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hz
    have hb := Fintype.mem_piFinset.1 hh k
    have e : (((2 * (2 * H.radius) + 1 : ℕ) : ℤ) - 1) / 2 = 2 * H.radius := by
      push_cast
      omega
    rw [e] at hb
    refine Finset.mem_image.2 ⟨h k, ?_, ?_⟩
    · simpa using hb
    · simp [siteOfCoords]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp only [Int.card_Icc]
  omega
theorem norm_quatAverage_le_one {E : Type} (I : Finset E) (hI : I.Nonempty) (f : E → UnitQuaternion) :
    ‖quatAverage I fun e => (f e : ℍ[ℝ])‖ ≤ 1 := by apply _root_.YangMills.Construction.GroupMeans.norm_quatAverage_unit_le_one <;> assumption
open Classical in
set_option maxHeartbeats 2000000 in
theorem coreBondMeanEstimate (hmb : BondMeanEstimate) (hg : MostContoursGoodStatement)
    (hc : ExcludedBoxesAtUncrowdedCell) (hd : TorusDistanceBlockLumpFacts) : CoreBondMeanEstimate := by
  intro F g a s θ C C₀ CJ J₀ D idx o U2 Wt γ c hL hT hJ hs hC hC₀ hCJ hbox hbox3 hS hFi hB hy hy' hη
  obtain ⟨y, i⟩ := c
  simp only at hy hy' ⊢
  set y' := y + unitStep F.top i with hy'd
  have hside : ∀ k, 64 ≤ F.extent k := fun k => by
    have h1 := hT.1 k
    have h2 := hT.2
    omega
  have hs0 : ∀ k, 0 < F.extent k := fun k => by
    have := hside k
    omega
  have hLpos := hL.pos
  obtain ⟨dcomm, dtri, denl, dunder, dcell, ctri, ccomm, cball, dlump⟩ := hd F hLpos hs0
  have hnc : ∀ {u : F.Cell} {k : ℕ}, u ∈ D.coreCells C k → 1 ≤ k → ¬ IsCrowded J₀ D.hotFineLumps u := by
    intro u k hu hk hcr
    obtain ⟨huS, hall⟩ := Finset.mem_filter.1 hu
    have hsp : u ∈ D.badCells C := Finset.mem_union_right _ (Finset.mem_filter.2 ⟨huS, hcr⟩)
    have := hall u hsp
    rw [cellSupDist_self_eq_zero] at this
    omega
  have hmono : ∀ {u : F.Cell} {k k' : ℕ}, k' ≤ k → u ∈ D.coreCells C k → u ∈ D.coreCells C k' := by
    intro u k k' hk hu
    obtain ⟨huS, hall⟩ := Finset.mem_filter.1 hu
    exact Finset.mem_filter.2 ⟨huS, fun z hz => hk.trans (hall z hz)⟩
  have hyball : y' ∈ cellBall y 1 := mem_cellBall_iff.2 ⟨Pi.single i 1, fun k => by
    by_cases h : k = i
    · subst h
      simp
    · simp [h], rfl⟩
  have hyy : y ∈ cellBall y 1 := (cball y 1 y).2 (by rw [cellSupDist_self_eq_zero]; omega)
  have hyy' : cellSupDist y y' ≤ 1 := (cball y 1 y').1 hyball
  have hyy's : cellSupDist y' y ≤ 1 := by
    rw [ccomm]
    exact hyy'
  have hfew0 := hS.few_near_uncrowded y (hnc hy (by norm_num))
  have hcur0 := hFi.curvature_le y hy
  generalize cellBall y 1 = B1 at hyball hyy hfew0 hcur0
  have hlump : ∀ l ∈ D.hotFineLumps, IsLump g l := by
    intro l hl
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 hl
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨x, rfl⟩
  have hclose : ∀ {u : F.Cell}, ¬ IsCrowded J₀ D.hotFineLumps u → _ := fun {u} hu =>
    hc F g J₀ D.hotFineLumps u hL (fun k => by have := hside k; omega) hbox hlump hu
  obtain ⟨-, hsum, -, -⟩ := hclose (hnc hy (by norm_num))
  obtain ⟨-, hsum', -, -⟩ := hclose (hnc hy' (by norm_num))
  obtain ⟨hpath, hgood⟩ := hg F J₀ (excludedBoxSide J₀) D.hotFineLumps D.base (y, i) hL hside D.isBaseChoice
  have hbad := hgood (hnc hy (by norm_num)) (hnc hy' (by norm_num))
    (fun Z hZ hm => hB.mem_excludedBoxes_of_adj y' hy' y hy hyy's Z hZ (Or.inr hm))
    (fun Z hZ hm => hB.mem_excludedBoxes_of_adj y hy y' hy' hyy' Z hZ (Or.inr hm)) hsum hsum'
  set Gd := (allContours F).filter fun e => IsGoodContour J₀ D.hotFineLumps D.base (y, i) e.1 e.2 with hGd
  have hcardI : (allContours F).card = F.blockSide ^ 4 * 24 := by
    simp [allContours, card_centredCube hL, Finset.card_product, Finset.card_univ, Fintype.card_perm,
      Nat.factorial]
  have hsplit : Gd.card + ((allContours F).filter
      fun e => ¬ IsGoodContour J₀ D.hotFineLumps D.base (y, i) e.1 e.2).card =
      (allContours F).card := Finset.card_filter_add_card_filter_not _
  have hbadlt : 24 * (8 * (F.blockSide * (2 * excludedBoxSide J₀) ^ 3)) < F.blockSide ^ 4 * 24 := by
    have : F.blockSide * (8 * (2 * excludedBoxSide J₀) ^ 3) < F.blockSide * F.blockSide ^ 3 :=
      Nat.mul_lt_mul_of_pos_left hbox3 hLpos
    nlinarith
  have hGne : Gd.Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hused : usedContours J₀ D.hotFineLumps D.base (y, i) = Gd := by
    unfold usedContours
    rw [if_neg]
    rintro (h1 | h1 | h1)
    · exact hnc hy (by norm_num) h1
    · exact hnc hy' (by norm_num) h1
    · rw [← hGd] at h1
      rw [h1] at hGne
      simp at hGne
  set Wp := gaugeChain γ U2 F.depth with hWp
  set κ := coreCurvatureBound C C₀ CJ s with hκd
  set K := CJ * Real.sqrt F.blockSide * s with hKd
  set N := J₀ * Nat.sqrt F.blockSide with hNd
  set τ : ℝ := 8 * (2 * excludedBoxSide J₀ : ℝ) ^ 3 / (F.blockSide : ℝ) ^ 3 with hτd
  have hκ0 : 0 ≤ κ := mul_nonneg (Real.sqrt_nonneg _) hs.le
  have hK0 : 0 ≤ K := by positivity
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hLpos
  have hQball : sitesBelow F.depth y ∪ sitesBelow F.depth y' ⊆ cutBelow F.depth B1 :=
    sitesBelow_union_subset_cutBelow hyy hyball
  have hQcore : sitesBelow F.depth y ∪ sitesBelow F.depth y' ⊆ cutBelow F.depth (D.coreCells C 5) :=
    sitesBelow_union_subset_cutBelow hy hy'
  obtain ⟨Hs, hHs⟩ : ∃ Hs : Finset (Hole F), Hs =
      (D.holesAt C idx o).filter fun H => (H.outerBox ∩ cutBelow F.depth B1).Nonempty := ⟨_, rfl⟩
  obtain ⟨Ds, hDs⟩ : ∃ Ds : Finset (F.Site F.depth), Ds = Hs.biUnion Hole.outerBox := ⟨_, rfl⟩
  have hoff : ∀ x ∈ sitesBelow F.depth y ∪ sitesBelow F.depth y', x ∉ Ds →
      x ∉ holeSupport (D.holesAt C idx o) := by
    intro x hx hn hh
    obtain ⟨H, hH, hxH⟩ := Finset.mem_biUnion.1 hh
    rw [hDs] at hn
    refine hn (Finset.mem_biUnion.2 ⟨H, ?_, hxH⟩)
    rw [hHs]
    exact Finset.mem_filter.2 ⟨hH, ⟨x, Finset.mem_inter.2 ⟨hxH, hQball hx⟩⟩⟩
  have hnear : LinksClose Wp Wt Ds (sitesBelow F.depth y ∪ sitesBelow F.depth y') K := by
    refine linksClose_of_cutBonds Wp Wt Ds _ K (fun b hb => hB.norm_sub_le y hy y' hy' hyy' b hb)
      (fun b hb h1 h2 => ?_)
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
    have hbq : b.1 ∈ sitesBelow F.depth y ∪ sitesBelow F.depth y' := (Finset.mem_product.1 hb1).1
    have g1 := hoff _ hbq h1
    have g2 := hoff _ hb2 h2
    obtain ⟨a1, a2⟩ := hB.eq_off_holes b (cutBonds_mono hQcore hb) g1 g2
    have t1 : Wp = gaugeTransform γ (U2 F.depth) := hB.gaugeChain_top
    rw [t1, a1]
    simp only [gaugeTransform]
    rw [hB.gauge_eq_one _ g1, hB.gauge_eq_one _ g2, a2]
    simp
  have hcount : ∀ k, (Ds.image fun z => z k).card ≤ N := by
    intro k
    have e : (Ds.image fun z => z k) = Hs.biUnion fun H => H.outerBox.image fun z => z k := by
      ext v
      rw [hDs]
      simp only [Finset.mem_image, Finset.mem_biUnion]
      constructor
      · rintro ⟨z, ⟨H, hH, hz⟩, rfl⟩
        exact ⟨H, hH, z, hz, rfl⟩
      · rintro ⟨H, hH, z, hz, rfl⟩
        exact ⟨z, ⟨H, hH, hz⟩, rfl⟩
    rw [e]
    refine Finset.card_biUnion_le.trans ?_
    have hone : ∀ H ∈ Hs, (H.outerBox.image fun z => z k).card ≤ Nat.sqrt F.blockSide := by
      intro H hH
      rw [hHs] at hH
      obtain ⟨r1, r2⟩ := hS.radius_bounds H (Finset.mem_filter.1 hH).1
      refine (card_image_outerBox_le H k).trans ?_
      rw [Nat.le_sqrt']
      nlinarith
    have hfew : Hs.card < J₀ := by
      rw [hHs]
      exact hfew0
    calc ∑ H ∈ Hs, (H.outerBox.image fun z => z k).card ≤ ∑ _H ∈ Hs, Nat.sqrt F.blockSide :=
          Finset.sum_le_sum hone
      _ = Hs.card * Nat.sqrt F.blockSide := by simp
      _ ≤ N := Nat.mul_le_mul_right _ hfew.le
  have hcross : ∀ u ∈ D.coreCells C 5, blockCurvatureNorm Wt u ≤ κ := by
    intro u hu
    have h1 := hB.curvature_le u hu u hu (by rw [cellSupDist_self_eq_zero]; omega)
    rw [Finset.union_self] at h1
    unfold blockCurvatureNorm
    refine Real.sqrt_le_iff.2 ⟨hκ0, h1.trans ?_⟩
    rw [hκd]
    unfold coreCurvatureBound
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg s, mul_pos hC₀ hC, sq_pos_of_pos hs]
  have htop : ∑ p ∈ blockPairPlaquettes (y, i), plaquetteDefect Wp p ^ 2 ≤ κ ^ 2 := by
    have e1 : ∑ p ∈ blockPairPlaquettes (y, i), plaquetteDefect Wp p ^ 2 =
        ∑ p ∈ blockPairPlaquettes (y, i), plaquetteDefect (U2 F.depth) p ^ 2 :=
      Finset.sum_congr rfl fun p _ => by rw [hWp, hB.plaquetteDefect_top_eq p]
    rw [e1]
    have hsub : blockPairPlaquettes (y, i) ⊆ cutPlaquettes (cutBelow F.depth (B1 ∩ D.coreCells C 4)) := by
      intro p hp
      exact cutPlaquettes_mono (sitesBelow_union_subset_cutBelow
        (Finset.mem_inter.2 ⟨hyy, hmono (by norm_num) hy⟩)
        (Finset.mem_inter.2 ⟨hyball, hmono (by norm_num) hy'⟩)) hp
    have h2 := hcur0
    have h3 : ∑ p ∈ blockPairPlaquettes (y, i), plaquetteDefect (U2 F.depth) p ^ 2 ≤
        ∑ p ∈ cutPlaquettes (cutBelow F.depth (B1 ∩ D.coreCells C 4)), plaquetteDefect (U2 F.depth) p ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => sq_nonneg _
    refine h3.trans (h2.trans ?_)
    rw [hκd]
    unfold coreCurvatureBound
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [sq_pos_of_pos hs, mul_pos hCJ (sq_pos_of_pos hs)]
  have hgoodW : ∀ e ∈ usedContours J₀ D.hotFineLumps D.base (y, i),
      baseContourHolonomy Wt D.base (y, i) e = baseContourHolonomy D.fineField D.base (y, i) e := by
    intro e he
    rw [hused] at he
    obtain ⟨heI, hgd⟩ := Finset.mem_filter.1 he
    obtain ⟨P, hP⟩ : ∃ P, P = contourPath D.base (y, i) e.1 e.2 := ⟨_, rfl⟩
    obtain ⟨Qp, hQp⟩ : ∃ Qp : Finset (F.Site F.depth), Qp = (pathSites (D.base y) P).toFinset := ⟨_, rfl⟩
    have hoffbox : ∀ x ∈ Qp, ∀ Z ∈ D.coreBoxes C, x ∉ Z := by
      intro x hx Z hZ hxZ
      rw [hQp] at hx
      have hxp : x ∈ pathSites (D.base y) P := List.mem_toFinset.1 hx
      rw [hP] at hxp
      have hxb := hpath e heI x hxp
      obtain ⟨y2, hy2, hZ2⟩ := Finset.mem_biUnion.1 hZ
      obtain ⟨hZ3, x2, hx2⟩ := Finset.mem_filter.1 hZ2
      obtain ⟨hxZ2, hxu2⟩ := Finset.mem_inter.1 hx2
      obtain ⟨-, -, hcorn, -⟩ := hclose (hnc hy2 (by norm_num))
      obtain ⟨lo, hi, hZeq, hsz⟩ := hcorn Z hZ3
      have hdist : supDist x2 x ≤ 1 * F.blockSide := by
        have : ∀ k, NeZero (F.period F.depth k) := fun k => ⟨by
          rw [_root_.YangMills.Construction.BlockSites.period_depth]
          exact Nat.mul_ne_zero (hs0 k).ne' hLpos.ne'⟩
        rw [hZeq] at hxZ hxZ2
        obtain ⟨a1, ha1, rfl⟩ := Finset.mem_image.1 hxZ
        obtain ⟨a2, ha2, rfl⟩ := Finset.mem_image.1 hxZ2
        have e1 : (siteOfCoords F.depth a1 : F.Site F.depth) =
            siteOfCoords F.depth a2 + siteOfCoords F.depth (a1 - a2) := by
          rw [← BlockSites.siteOfCoords_add]
          simp
        rw [e1]
        have hb : ∀ k, |(a1 - a2) k| ≤ (excludedBoxSide J₀ : ℕ) := by
          intro k
          have b1 := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 ha1 k)
          have b2 := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 ha2 k)
          have b3 := (hsz k).2
          simp only [Pi.sub_apply]
          rw [abs_le]
          have b4 : ((11 * 2 ^ 12 * J₀ : ℕ) : ℤ) = (excludedBoxSide J₀ : ℕ) := rfl
          push_cast at b3 b4 ⊢
          constructor <;> omega
        have hp : ∀ k, 2 * ((excludedBoxSide J₀ : ℕ) : ℤ) < F.period F.depth k := by
          intro k
          rw [_root_.YangMills.Construction.BlockSites.period_depth]
          have h1 : 64 * F.blockSide ≤ F.extent k * F.blockSide := Nat.mul_le_mul_right _ (hside k)
          have h2 : (64 * F.blockSide : ℤ) ≤ ((F.extent k * F.blockSide : ℕ) : ℤ) := by exact_mod_cast h1
          have h3 : ((excludedBoxSide J₀ : ℕ) : ℤ) < F.blockSide := by exact_mod_cast hbox
          omega
        have := supDist_add_le (x := siteOfCoords F.depth a2) hb hp
        omega
      have hcd := dcell hL 1 x2 x hdist
      have near' : ∀ u ∈ D.coreCells C 5, x ∈ sitesBelow F.depth u →
          Z ∈ excludedBoxes J₀ D.hotFineLumps u := by
        intro u hu hxu
        have e2 : enclosingCell x2 = y2 := (dunder hL x2 y2).1 hxu2
        have e3 : enclosingCell x = u := (dunder hL x u).1 hxu
        rw [e2, e3] at hcd
        exact hB.mem_excludedBoxes_of_adj y2 hy2 u hu hcd Z hZ3 (Or.inl ⟨x2, Finset.mem_inter.2 ⟨hxZ2, hxu2⟩⟩)
      rcases Finset.mem_union.1 hxb with hxu | hxu
      · exact hgd x hxp Z (Finset.mem_union_left _ (near' y hy hxu)) hxZ
      · exact hgd x hxp Z (Finset.mem_union_right _ (near' y' hy' hxu)) hxZ
    have hWb : ∀ b ∈ cutBonds Qp, Wt b.1 b.2 = D.fineField b.1 b.2 := by
      intro b hb
      obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
      have hbq : b.1 ∈ Qp := (Finset.mem_product.1 hb1).1
      refine hB.eq_of_not_touches b fun Z hZ hm => ?_
      rcases hm with hm | hm
      · exact hoffbox _ hbq Z hZ hm
      · exact hoffbox _ hb2 Z hZ hm
    have hsn : LinksClose Wt D.fineField ∅ Qp 0 := by
      refine linksClose_of_cutBonds Wt D.fineField ∅ Qp 0 (fun b hb => ?_) (fun b hb _ _ => hWb b hb)
      rw [hWb b hb]
      simp
    have h0 := norm_pathHolonomy_sub_le Wt D.fineField ∅ Qp 0 le_rfl hsn P (D.base y) (fun z hz => by
      rw [hQp]
      exact List.mem_toFinset.2 hz)
    rw [zero_mul] at h0
    have h1 : ‖((pathHolonomy Wt (D.base y) P : UnitQuaternion) : ℍ[ℝ]) -
        (pathHolonomy D.fineField (D.base y) P : UnitQuaternion)‖ = 0 :=
      le_antisymm h0 (norm_nonneg _)
    have h2 := Subtype.ext (sub_eq_zero.1 (norm_eq_zero.1 h1))
    rw [hP] at h2
    exact h2
  have hsubG : usedContours J₀ D.hotFineLumps D.base (y, i) ⊆ allContours F := by
    rw [hused]
    exact Finset.filter_subset _ _
  have hGne' : (usedContours J₀ D.hotFineLumps D.base (y, i)).Nonempty := by
    rw [hused]
    exact hGne
  have hshare : ((allContours F \ usedContours J₀ D.hotFineLumps D.base (y, i)).card : ℝ) ≤
      τ * (allContours F).card := by
    have e : allContours F \ usedContours J₀ D.hotFineLumps D.base (y, i) =
        (allContours F).filter fun e => ¬ IsGoodContour J₀ D.hotFineLumps D.base (y, i) e.1 e.2 := by
      rw [hused, hGd]
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_filter]
      tauto
    rw [e, hcardI]
    have h1 : (((allContours F).filter
        fun e => ¬ IsGoodContour J₀ D.hotFineLumps D.base (y, i) e.1 e.2).card : ℝ) ≤
        24 * (8 * ((F.blockSide : ℝ) * (2 * (excludedBoxSide J₀ : ℝ)) ^ 3)) := by
      exact_mod_cast hbad
    refine h1.trans (le_of_eq ?_)
    rw [hτd]
    push_cast
    field_simp
  have dd : BondBesideHoles Wt Wp D.fineField D.base (y, i) (usedContours J₀ D.hotFineLumps D.base (y, i))
      Ds κ K τ N :=
    { base_mem := base_mem_sitesBelow J₀ D.hotFineLumps D.base hL D.isBaseChoice y
      base_mem' := base_mem_sitesBelow J₀ D.hotFineLumps D.base hL D.isBaseChoice y'
      contours_subset := hsubG
      contours_nonempty := hGne'
      defect_le := hcross y hy
      defect_le' := hcross y' hy'
      pairDefect_le := htop
      links_close := hnear
      coords_card_le := hcount
      holonomy_eq := hgoodW
      missing_le := by convert hshare }
  obtain ⟨m1, m2⟩ := hmb F Wt Wp D.fineField D.base (y, i) _ Ds κ K τ N hL hside hκ0 hK0 dd hη
  refine ⟨m1, m2, ?_⟩
  exact norm_quatAverage_le_one _ hGne' _
end CoreBondMeans
end YangMills.Construction
end
