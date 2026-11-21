import YangMills.Construction.HoleBesideASecondHole.BadCellsPay
import YangMills.Construction.HoleBesideASecondHole.CellsKeptOffTheSpots
import YangMills.Construction.HoleBesideASecondHole.CoordinatesInOneOrderAgainstTheOther
import YangMills.Construction.HoleBesideASecondHole.CostOnWholeCellsIsTheLeastAction
import YangMills.Construction.HoleBesideASecondHole.CrowdedCellsAreFew
import YangMills.Construction.HoleBesideASecondHole.CurvatureBelowTheElementsAtItsCorners
import YangMills.Construction.HoleBesideASecondHole.EnergyInTheChart
import YangMills.Construction.HoleBesideASecondHole.FieldAboveTheLeastFieldPaysItsDistance
import YangMills.Construction.HoleBesideASecondHole.LeastFieldsOfTwoCutsAgreeFarFromTheirDifference
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.HoleSavings.BadCellCount
open BlockAverages hiding cellBall siteOfCoords_zero siteOfCoords_add
open GaugeFixing LumpContours HoleBounds
variable {F : BlockFrame}
theorem cutChainEnergy_depth_le_top (hL : Odd F.blockSide) (a : ℝ) (ha : 0 ≤ a) (X : Finset F.Cell)
    (Q : Finset (F.Site F.depth)) (hQ : Q ⊆ cutBelow F.depth X) (U : F.FieldChain) :
    cutChainEnergy a F.depth Q U ≤ cutChainEnergy a F.top X U := by
  have hi : ∀ i, i ≤ F.depth → cutBelow i Q ⊆ cutBelow i X := by
    intro i hi z hz
    obtain ⟨w, hw, hzw⟩ := Finset.mem_biUnion.1 hz
    obtain ⟨x, hx, hwx⟩ := Finset.mem_biUnion.1 (hQ hw)
    exact Finset.mem_biUnion.2 ⟨x, hx, BlockLevels.sitesBelow_trans hi (Nat.le_succ _) le_rfl hL x hwx hzw⟩
  unfold cutChainEnergy
  have h1 : ∑ p ∈ cutPlaquettes (cutBelow 0 Q), plaquetteEnergy (U 0) p ≤
      ∑ p ∈ cutPlaquettes (cutBelow 0 X), plaquetteEnergy (U 0) p :=
    Finset.sum_le_sum_of_subset_of_nonneg (BlockLevels.cutPlaquettes_mono (hi 0 (Nat.zero_le _)))
      fun p _ _ => BlockLevels.plaquetteEnergy_nonneg _ _
  have h2 : ∑ i ∈ Finset.range F.depth, ∑ c ∈ cutBonds (cutBelow (i + 1) Q), blockFit (U i) (U (i + 1)) c ≤
      ∑ i ∈ Finset.range F.top, ∑ c ∈ cutBonds (cutBelow (i + 1) X), blockFit (U i) (U (i + 1)) c := by
    refine le_trans (Finset.sum_le_sum fun i hi' => ?_) (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.le_succ _)) fun i _ _ => Finset.sum_nonneg fun c _ => BlockLevels.blockFit_nonneg _ _ _)
    exact Finset.sum_le_sum_of_subset_of_nonneg (BlockLevels.cutBonds_mono (hi _ (Finset.mem_range.1 hi')))
      fun c _ _ => BlockLevels.blockFit_nonneg _ _ _
  have := mul_le_mul_of_nonneg_left h2 ha
  linarith
theorem cutBelow_top (X : Finset F.Cell) : cutBelow F.top X = X := by
  rw [BlockLevels.cutBelow_eq_sitesOfCells]
  ext y
  exact mem_sitesOfCells_top
theorem blockFit_le_cutChainEnergy_top (a : ℝ) (ha : 0 ≤ a) (X : Finset F.Cell) (U : F.FieldChain)
    (c : F.Cell × Fin 4) (hc : c ∈ cutBonds X) :
    a * blockFit (U F.depth) (U F.top) c ≤ cutChainEnergy a F.top X U := by
  unfold cutChainEnergy
  have h1 : 0 ≤ ∑ p ∈ cutPlaquettes (cutBelow 0 X), plaquetteEnergy (U 0) p :=
    Finset.sum_nonneg fun p _ => BlockLevels.plaquetteEnergy_nonneg _ _
  have h2 : blockFit (U F.depth) (U F.top) c ≤
      ∑ c ∈ cutBonds (cutBelow (F.depth + 1) X), blockFit (U F.depth) (U (F.depth + 1)) c := by
    have hc' : c ∈ cutBonds (cutBelow (F.depth + 1) X) := by
      have := cutBelow_top X
      simp only [BlockFrame.top] at this
      rw [this]
      exact hc
    exact Finset.single_le_sum (f := fun c => blockFit (U F.depth) (U (F.depth + 1)) c)
      (fun c _ => BlockLevels.blockFit_nonneg _ _ _) hc'
  have h3 : ∑ c ∈ cutBonds (cutBelow (F.depth + 1) X), blockFit (U F.depth) (U (F.depth + 1)) c ≤
      ∑ i ∈ Finset.range F.top, ∑ c ∈ cutBonds (cutBelow (i + 1) X), blockFit (U i) (U (i + 1)) c :=
    Finset.single_le_sum (f := fun i => ∑ c ∈ cutBonds (cutBelow (i + 1) X), blockFit (U i) (U (i + 1)) c)
      (fun i _ => Finset.sum_nonneg fun c _ => BlockLevels.blockFit_nonneg _ _ _)
      (Finset.mem_range.2 (Nat.lt_succ_self _))
  have := mul_le_mul_of_nonneg_left (h2.trans h3) ha
  linarith
theorem mem_coreCells_of_far {L : ℕ} {g : LumpGrid L} {a s θ : ℝ} {J₀ : ℕ} {F : BlockFrame}
    (D : HoleData F g a s θ J₀) (C : ℝ) {S₁ : Finset F.Cell} (hsub : S₁ ⊆ D.keptCells)
    (hsp : ∀ y ∈ S₁, ∀ z ∈ D.badCells C, 10 < cellSupDist y z) (k : ℕ) (hk : k ≤ 11) {y : F.Cell}
    (hy : y ∈ S₁) : y ∈ D.coreCells C k := by
  classical
  have hyS : y ∈ D.cells := (Finset.mem_sdiff.1 (hsub hy)).1
  simp only [HoleData.coreCells, Finset.mem_filter]
  refine ⟨hyS, fun z hz => ?_⟩
  have := hsp y hy z hz
  omega
theorem liesNearTop_of_filling {L : ℕ} {g : LumpGrid L} {a s θ : ℝ} {J₀ : ℕ} {F : BlockFrame}
    (D : HoleData F g a s θ J₀) (C ε CJ cK : ℝ) (U2 : F.FieldChain) (S₁ : Finset F.Cell) (r : ℝ) (ha : 1 ≤ a)
    (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (hcK : 0 < cK)
    (hcurv : ∀ (p : F.Site F.depth × Fin 4 × Fin 4) (U : F.FieldChain), p.2.1 < p.2.2 →
      cutChainEnergy a F.depth (plaquetteCorners p) U < cK * (F.blockSide : ℝ) ^ (-4 : ℤ) →
      plaquetteDefect (U F.depth) p ^ 2 ≤ cutChainEnergy a F.depth (plaquetteCorners p) U / cK)
    (hsmall : CJ * s ^ 2 < cK * (F.blockSide : ℝ) ^ (-4 : ℤ)) (hfill : D.IsFillingChain C ε CJ U2)
    (hsub : S₁ ⊆ D.keptCells) (hsp : ∀ y ∈ S₁, ∀ z ∈ D.badCells C, 10 < cellSupDist y z) (hr0 : 0 ≤ r)
    (hr1 : CJ * s ^ 2 / cK ≤ r ^ 2) (hr2 : CJ * s ^ 2 ≤ r ^ 2) :
    LiesNearTop r S₁ D.topField (U2 F.depth) := by
  classical
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨htop, -, hplaces, -⟩ := hfill
  refine ⟨fun p hp => ?_, fun c hc => ?_⟩
  · have hcor : p.2.1 < p.2.2 ∧ plaquetteCorners p ⊆ cutBelow F.depth S₁ := by
      simp only [cutPlaquettes, Finset.mem_filter] at hp
      exact hp.2
    have hp1 : p.1 ∈ cutBelow F.depth S₁ := by
      simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product] at hp
      exact hp.1.1
    set y := enclosingCell p.1 with hy
    have hyS : y ∈ S₁ := (mem_cutBelow_depth hs' hodd S₁ _).1 hp1
    set X := (plaquetteCorners p).image (enclosingCell (F := F)) with hX
    have hXsub : X ⊆ cellBall y 1 ∩ D.coreCells C 5 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
      refine Finset.mem_inter.2
        ⟨BlockLevels.enclosingCell_corner_mem_cellBall (Nat.le_succ _) hodd.pos p hcor.1 hx, ?_⟩
      exact mem_coreCells_of_far D C hsub hsp 5 (by norm_num) ((mem_cutBelow_depth hs' hodd S₁ _).1 (hcor.2 hx))
    have hQ : plaquetteCorners p ⊆ cutBelow F.depth X := by
      intro x hx
      exact (mem_cutBelow_depth hs' hodd X x).2 (Finset.mem_image.2 ⟨x, hx, rfl⟩)
    have h1 := hplaces y (mem_coreCells_of_far D C hsub hsp 6 (by norm_num) hyS) X hXsub
    have h2 := cutChainEnergy_depth_le_top hodd a ha0 X (plaquetteCorners p) hQ U2
    have h3 : cutChainEnergy a F.depth (plaquetteCorners p) U2 ≤ CJ * s ^ 2 := h2.trans h1
    have h4 := hcurv p U2 hcor.1 (h3.trans_lt hsmall)
    have h5 : plaquetteDefect (U2 F.depth) p ^ 2 ≤ r ^ 2 :=
      h4.trans ((div_le_div_of_nonneg_right h3 hcK.le).trans hr1)
    exact (abs_le_of_sq_le_sq' h5 hr0).2
  · have hc' : c.1 ∈ S₁ ∧ c.1 + unitStep F.top c.2 ∈ S₁ := by
      simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hc
      exact hc
    set X : Finset F.Cell := {c.1, c.1 + unitStep F.top c.2} with hX
    have hXsub : X ⊆ cellBall c.1 1 ∩ D.coreCells C 5 := by
      intro z hz
      simp only [hX, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · refine Finset.mem_inter.2 ⟨?_, mem_coreCells_of_far D C hsub hsp 5 (by norm_num) hc'.1⟩
        have := BlockLevels.add_mem_cellBall_one (F := F) c.1 0 (by simp)
        simpa [siteOfCoords_zero] using this
      · refine Finset.mem_inter.2 ⟨?_, mem_coreCells_of_far D C hsub hsp 5 (by norm_num) hc'.2⟩
        exact BlockLevels.add_mem_cellBall_one (F := F) c.1 (Pi.single c.2 1) (BlockLevels.abs_single_le_one _)
    have h1 := hplaces c.1 (mem_coreCells_of_far D C hsub hsp 6 (by norm_num) hc'.1) X hXsub
    have hcX : c ∈ cutBonds X :=
      Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨by simp [hX], Finset.mem_univ _⟩, by simp [hX]⟩
    have h2 := blockFit_le_cutChainEnergy_top a ha0 X U2 c hcX
    rw [htop] at h2
    have h3 : 0 ≤ blockFit (U2 F.depth) D.topField c := BlockLevels.blockFit_nonneg _ _ _
    have h4 : blockFit (U2 F.depth) D.topField c ≤ a * blockFit (U2 F.depth) D.topField c := by nlinarith
    linarith
theorem card_centredCube_of_odd {M : ℕ} (hM : Odd M) : (centredCube M).card = M ^ 4 := by
  obtain ⟨k, rfl⟩ := hM
  have h1 : (Finset.Icc (-halfSide (2 * k + 1)) (halfSide (2 * k + 1))).card = 2 * k + 1 := by
    rw [Int.card_Icc]
    simp only [halfSide]
    push_cast
    omega
  simp only [centredCube, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
theorem card_cellBall_le (y : F.Cell) (r : ℕ) : (cellBall y r).card ≤ (2 * r + 1) ^ 4 := by
  rw [← card_centredCube_of_odd (odd_two_mul_add_one r)]
  exact Finset.card_image_le
theorem halfSide_two_mul_add_one (r : ℕ) : halfSide (2 * r + 1) = r := by
  simp only [halfSide]
  push_cast
  omega
theorem mem_cellBall_symm {y z : F.Cell} {r : ℕ} (h : z ∈ cellBall y r) : y ∈ cellBall z r := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
  refine Finset.mem_image.2 ⟨-a, ?_, ?_⟩
  · rw [mem_centredCube_iff_abs_le] at ha ⊢
    intro i
    simpa using ha i
  · rw [siteOfCoords_neg]
    abel
theorem mem_cellBall_trans {y z w : F.Cell} {r r' : ℕ} (h : z ∈ cellBall y r) (h' : w ∈ cellBall z r') :
    w ∈ cellBall y (r + r') := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 h'
  refine Finset.mem_image.2 ⟨a + b, ?_, ?_⟩
  · rw [mem_centredCube_iff_abs_le] at ha hb ⊢
    intro i
    have h1 := ha i
    have h2 := hb i
    rw [halfSide_two_mul_add_one] at h1 h2
    have h3 := abs_add_le (a i) (b i)
    rw [show 2 * (r + r') + 1 = 2 * (r + r') + 1 from rfl, halfSide_two_mul_add_one]
    push_cast
    simp only [Pi.add_apply]
    omega
  · rw [siteOfCoords_add, add_assoc]
theorem self_mem_cellBall (y : F.Cell) (r : ℕ) : y ∈ cellBall y r := by
  refine Finset.mem_image.2 ⟨0, ?_, ?_⟩
  · rw [mem_centredCube_iff_abs_le]
    intro i
    rw [halfSide_two_mul_add_one]
    simp
  · rw [siteOfCoords_zero, add_zero]
theorem cellSupDist_le_one_of_mem_cellBall (hA : IsAdmissibleAmbient F) {y z : F.Cell} (h : z ∈ cellBall y 1) :
    cellSupDist y z ≤ 1 := by
  obtain ⟨a, ha, e⟩ := Finset.mem_image.1 (mem_cellBall_symm h)
  rw [← e]
  refine cellSupDist_add_le hA z (by norm_num) fun i => ?_
  have := mem_centredCube_iff_abs_le.1 ha i
  rw [halfSide_two_mul_add_one] at this
  exact_mod_cast this
attribute [local irreducible] cellBall
theorem abs_offsetFromCentre_le {L : ℕ} (hL : Odd L) (c : ℤ) : |offsetFromCentre L c| ≤ ((L : ℤ) - 1) / 2 := by
  obtain ⟨k, rfl⟩ := hL
  have hpos : (0 : ℤ) < ((2 * k + 1 : ℕ) : ℤ) := by positivity
  have e : (((2 * k + 1 : ℕ) : ℤ) - 1) / 2 = k := by push_cast; omega
  unfold offsetFromCentre
  rw [e]
  have h1 := Int.emod_nonneg (c + k) hpos.ne'
  have h2 := Int.emod_lt_of_pos (c + k) hpos
  rw [abs_le]
  push_cast at h1 h2 ⊢
  omega
theorem mem_lumpOf_self {L : ℕ} (g : LumpGrid L) (hL : Odd L) {j : ℕ} (x : F.Site j) : x ∈ lumpOf g x := by
  unfold lumpOf boxSites
  refine Finset.mem_image.2 ⟨siteCoords x, ?_, siteOfCoords_siteCoords x⟩
  simp only [Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hb := g.mem_interval _ (abs_offsetFromCentre_le hL (siteCoords x i))
  omega
theorem nonempty_of_mem_hotLumps {L : ℕ} (g : LumpGrid L) (hL : Odd L) {s : ℝ} {j : ℕ} {X : Finset (F.Site j)}
    {W : F.GaugeField j} {l : Finset (F.Site j)} (hl : l ∈ hotLumps g s X W) : l.Nonempty := by
  classical
  unfold hotLumps at hl
  obtain ⟨p, -, hl⟩ := Finset.mem_biUnion.1 hl
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hl
  exact ⟨x, mem_lumpOf_self g hL x⟩
theorem mem_nearbyLumps (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide)
    {h : Finset (Finset (F.Site F.depth))} {y : F.Cell} {l : Finset (F.Site F.depth)}
    (hl : l ∈ nearbyLumps h y) : l ∈ h ∧ ∀ x ∈ l, enclosingCell x ∈ cellBall y 2 := by
  classical
  unfold nearbyLumps at hl
  rw [Finset.mem_filter] at hl
  refine ⟨hl.1, fun x hx => ?_⟩
  have h1 : x ∈ cutBelow F.depth (cellBall y 2) := hl.2 hx
  exact (mem_cutBelow_depth hs hL _ _).1 h1
open Classical in
theorem card_near_hotLumps_le {L : ℕ} {g : LumpGrid L} {a s θ : ℝ} {J₀ : ℕ} {F : BlockFrame}
    (D : HoleData F g a s θ J₀) (hL : Odd L) (hs : ∀ i, 0 < F.extent i) (hFL : F.blockSide = L) :
    (D.keptCells.filter fun y => ∃ z ∈ cellBall y 1, nearbyLumps D.hotFineLumps z ≠ ∅).card ≤
      D.hotFineLumps.card * 2401 := by
  have hL' : Odd F.blockSide := hFL ▸ hL
  obtain ⟨pt, hpt⟩ : ∃ pt : Finset (F.Site F.depth) → F.Site F.depth,
      ∀ l : Finset (F.Site F.depth), l.Nonempty → pt l ∈ l :=
    ⟨fun l => if h : l.Nonempty then h.choose else 0, fun l h => by
      simp only [dif_pos h]
      exact h.choose_spec⟩
  have hsub : (D.keptCells.filter fun y => ∃ z ∈ cellBall y 1, nearbyLumps D.hotFineLumps z ≠ ∅) ⊆
      D.hotFineLumps.biUnion fun l => cellBall (enclosingCell (pt l)) 3 := by
    intro y hy
    obtain ⟨-, z, hz, hne⟩ := Finset.mem_filter.1 hy
    obtain ⟨l, hl⟩ := Finset.nonempty_iff_ne_empty.2 hne
    obtain ⟨hlh, hls⟩ := mem_nearbyLumps hs hL' hl
    have hnon : l.Nonempty := nonempty_of_mem_hotLumps g hL hlh
    have hp : pt l ∈ l := hpt l hnon
    have h2 : enclosingCell (pt l) ∈ cellBall z 2 := hls _ hp
    exact Finset.mem_biUnion.2 ⟨l, hlh, mem_cellBall_symm (mem_cellBall_trans hz h2)⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine Finset.card_biUnion_le_card_mul _ _ _ fun l _ => ?_
  have := card_cellBall_le (enclosingCell (pt l)) 3
  norm_num at this
  exact this
theorem cellSupDist_le_half (hc : IsCubicTorus F 64) (y z : F.Cell) : cellSupDist y z ≤ F.extent 0 / 2 := by
  refine Finset.sup_le fun i _ => ?_
  have hp : F.period F.top i = F.extent 0 := by rw [period_top, hc.1 i]
  haveI : NeZero (F.period F.top i) := ⟨by rw [hp]; have := hc.2; omega⟩
  refine (ZMod.natAbs_valMinAbs_le _).trans (le_of_eq ?_)
  rw [hp]
theorem cellSupDist_add_siteOfCoords_le (hc : IsCubicTorus F 64) (y : F.Cell) (h : Fin 4 → ℤ) (r : ℕ)
    (hb : WithinRadius r h) (h2 : 2 * r < F.extent 0) : cellSupDist y (y + siteOfCoords F.top h) ≤ r := by
  refine Finset.sup_le fun i _ => ?_
  have h1 : (y i - (y + siteOfCoords F.top h : F.Cell) i) = ((-h i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  have hbi := hb i
  have hp : 2 * |(-h i)| < ((F.period F.top i : ℕ) : ℤ) := by
    rw [period_top, hc.1 i, abs_neg]
    have : (2 * (r : ℤ)) < (F.extent 0 : ℤ) := by exact_mod_cast h2
    omega
  show ((y i - (y + siteOfCoords F.top h : F.Cell) i).valMinAbs).natAbs ≤ r
  rw [h1, valMinAbs_intCast_of_small (Or.inr hp)]
  have : |(-h i)| ≤ (r : ℤ) := by rwa [abs_neg]
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this
theorem bondCoordinate_congr (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide) (V : F.GaugeField F.top)
    (W W2 : F.GaugeField F.depth) (c : F.Site F.depth × Fin 4)
    (h : ∀ b ∈ cutBonds (sitesBelow F.depth (enclosingCell c.1) ∪
        sitesBelow F.depth (enclosingCell (c.1 + unitStep F.depth c.2))),
      W b.1 b.2 = W2 b.1 b.2) : bondCoordinate 1 V W c = bondCoordinate 1 V W2 c := by
  have tg : ∀ x, (sitesBelow F.depth (enclosingCell x) ⊆ sitesBelow F.depth (enclosingCell c.1) ∪
      sitesBelow F.depth (enclosingCell (c.1 + unitStep F.depth c.2))) →
      axialGauge 1 W x = axialGauge 1 W2 x := by
    intro x hx
    refine pathHolonomy_congr (Q := sitesBelow F.depth (enclosingCell x))
      (fun b hb => h b (BlockLevels.cutBonds_mono hx hb)) _ _ ?_
    exact pathWithin_axisPath _ (fun o ho => cellCentre_add_mem_sitesBelow hL _ o ho) _
      (cellOffset_mem_and_eq hs hL x).1 1
  have h1 := tg c.1 Finset.subset_union_left
  have h2 := tg (c.1 + unitStep F.depth c.2) Finset.subset_union_right
  have hc : c ∈ cutBonds (sitesBelow F.depth (enclosingCell c.1) ∪
      sitesBelow F.depth (enclosingCell (c.1 + unitStep F.depth c.2))) := by
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩, ?_⟩
    · exact Finset.mem_union_left _ ((mem_sitesBelow_depth hs hL _ _).2 rfl)
    · exact Finset.mem_union_right _ ((mem_sitesBelow_depth hs hL _ _).2 rfl)
  have h3 := h c hc
  have h4 : gaugeTransform (axialGauge 1 W) W c.1 c.2 = gaugeTransform (axialGauge 1 W2) W2 c.1 c.2 := by
    simp only [gaugeTransform]
    rw [h1, h2, h3]
  unfold bondCoordinate
  rw [h4]
theorem mem_thickening {S Δ : Finset F.Cell} {m : ℕ} {y : F.Cell} :
    y ∈ thickening S Δ m ↔ y ∈ S ∧ ∃ d ∈ Δ, cellSupDist y d ≤ m := by
  classical
  simp [thickening]
theorem lexBondCoordinate_minimizers_close (hc : IsCubicTorus F 64) (V : F.GaugeField F.top)
    (Wl Wl1 : F.GaugeField F.depth) (kept S₁ : Finset F.Cell) (hsub : S₁ ⊆ kept) (R : ℕ) (hR : 1 ≤ R) (e : ℝ)
    (he : 0 ≤ e) (hΔ : kept \ S₁ = ∅ → Wl1 = Wl)
    (hlf : ∀ (y : F.Cell) (r : ℕ), r = R → 2 * r + 2 < F.extent 0 →
      (∀ h, WithinRadius r h → (y + siteOfCoords F.top h ∈ kept ↔ y + siteOfCoords F.top h ∈ S₁)) →
      ∀ b ∈ innerBonds kept F.depth, b ∈ innerBonds S₁ F.depth → cellSupDist y (enclosingCell b.1) ≤ 1 →
        cellSupDist y (enclosingCell (b.1 + unitStep F.depth b.2)) ≤ 1 →
        ‖(lexBondCoordinate V Wl b : ℍ[ℝ]) - lexBondCoordinate V Wl1 b‖ ≤ e)
    (y : F.Cell) (hy : y ∈ kept) (hyB : y ∉ thickening kept (kept \ S₁) (R + 1)) (c : F.Site F.depth × Fin 4)
    (hc1 : c ∈ innerBonds kept F.depth) (hc2 : c ∈ innerBonds S₁ F.depth)
    (hd1 : cellSupDist y (enclosingCell c.1) ≤ 1)
    (hd2 : cellSupDist y (enclosingCell (c.1 + unitStep F.depth c.2)) ≤ 1) :
    ‖(lexBondCoordinate V Wl c : ℍ[ℝ]) - lexBondCoordinate V Wl1 c‖ ≤ e := by
  classical
  by_cases hemp : kept \ S₁ = ∅
  · rw [hΔ hemp]
    simpa using he
  have hside : 2 * R + 2 < F.extent 0 := by
    by_contra hcon
    obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.2 hemp
    apply hyB
    rw [mem_thickening]
    refine ⟨hy, z, hz, (cellSupDist_le_half hc y z).trans ?_⟩
    omega
  refine hlf y R rfl hside (fun h hb => ⟨fun hk => ?_, fun h1 => hsub h1⟩) c hc1 hc2 hd1 hd2
  by_contra hn
  apply hyB
  rw [mem_thickening]
  refine ⟨hy, _, Finset.mem_sdiff.2 ⟨hk, hn⟩, ?_⟩
  have := cellSupDist_add_siteOfCoords_le hc y h R hb (by omega)
  omega
theorem lexBondCoordinate_of_isAxialTreeBond (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (V : F.GaugeField F.top) (W : F.GaugeField F.depth) (b : F.Site F.depth × Fin 4) (hb : IsAxialTreeBond b) :
    lexBondCoordinate V W b = 0 := by
  have h0 : minimalLog (1 : UnitQuaternion) = 0 := by
    have := minimalLog_expUnit (0 : imaginaryQuaternions) (by simpa using Real.pi_pos)
    rwa [expUnit_zero] at this
  unfold lexBondCoordinate bondCoordinate
  rw [if_neg hb.1, gaugeTransform_axialGauge_of_isAxialTreeBond hs hL W b.1 b.2 hb, h0]
theorem exists_far_chordBond_of_bad {L : ℕ} {g : LumpGrid L} {a s θ : ℝ} {J₀ : ℕ} {F : BlockFrame}
    (D : HoleData F g a s θ J₀) (C K d : ℝ) (U2 : F.FieldChain) (S₁ : Finset F.Cell)
    (Wl Wl1 : F.GaugeField F.depth) (R : ℕ) (hc : IsCubicTorus F 64) (hL : Odd F.blockSide)
    (hsub : S₁ ⊆ D.keptCells) (hsp : ∀ y ∈ S₁, ∀ z ∈ D.badCells C, 10 < cellSupDist y z)
    (hsame : ∀ b ∈ cutBonds (cutBelow F.depth (D.coreCells C 5)),
      nearbyLumps D.hotFineLumps (enclosingCell b.1) = ∅ →
      nearbyLumps D.hotFineLumps (enclosingCell (b.1 + unitStep F.depth b.2)) = ∅ →
      U2 F.depth b.1 b.2 = D.fineField b.1 b.2)
    (hn1 : ∀ c ∈ innerBonds S₁ F.depth, ‖(lexBondCoordinate D.topField (U2 F.depth) c : ℍ[ℝ])‖ ≤ 1 / K)
    (hn2 : ∀ c ∈ innerBonds D.keptCells F.depth, ‖(lexBondCoordinate D.topField Wl c : ℍ[ℝ])‖ ≤ 1 / K)
    (horder : ∀ (b : F.Site F.depth × Fin 4) (d' : ℝ),
      (∀ c ∈ bondsOfEndBlocks b, ‖(lexBondCoordinate D.topField D.fineField c : ℍ[ℝ])‖ ≤ 1 / K) →
      (∀ c ∈ bondsOfEndBlocks b, ‖(lexBondCoordinate D.topField Wl c : ℍ[ℝ])‖ ≤ 1 / K) →
      (∀ c ∈ bondsOfEndBlocks b,
        ‖(lexBondCoordinate D.topField D.fineField c : ℍ[ℝ]) - lexBondCoordinate D.topField Wl c‖ ≤ d') →
      ∀ π : Equiv.Perm (Fin 4),
        ‖(bondCoordinate π D.topField D.fineField b : ℍ[ℝ]) - bondCoordinate π D.topField Wl b‖ ≤ K * d')
    (hclose : ∀ y ∈ D.keptCells, y ∉ thickening D.keptCells (D.keptCells \ S₁) (R + 1) →
      ∀ c ∈ innerBonds D.keptCells F.depth, c ∈ innerBonds S₁ F.depth →
      cellSupDist y (enclosingCell c.1) ≤ 1 → cellSupDist y (enclosingCell (c.1 + unitStep F.depth c.2)) ≤ 1 →
      ‖(lexBondCoordinate D.topField Wl c : ℍ[ℝ]) - lexBondCoordinate D.topField Wl1 c‖ ≤ d / 2)
    (hd : K * d < s / 128) (hd0 : 0 < d) (y : F.Cell)
    (hbad : y ∈ HoleBounds.badCells (s / 128) D.keptCells D.topField D.fineField Wl)
    (hnoA : ∀ z ∈ cellBall y 1, nearbyLumps D.hotFineLumps z = ∅)
    (hyB : y ∉ thickening D.keptCells (D.keptCells \ S₁) (R + 1)) :
    ∃ c ∈ chordBonds S₁, enclosingCell c.1 ∈ cellBall y 1 ∧
      d / 2 ≤ ‖(lexBondCoordinate D.topField (U2 F.depth) c : ℍ[ℝ]) - lexBondCoordinate D.topField Wl1 c‖ := by
  classical
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hc.1 i]; have := hc.2; omega
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hA : IsAdmissibleAmbient F := Or.inr fun i => by rw [hc.1 i]; exact hc.2
  simp only [HoleBounds.badCells, Finset.mem_filter] at hbad
  obtain ⟨hyk, π, b, hb, hend, hbig⟩ := hbad
  have hb' : b.1 ∈ cutBelow F.depth D.keptCells ∧ b.1 + unitStep F.depth b.2 ∈ cutBelow F.depth D.keptCells := by
    simpa only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] using hb
  set y₁ := enclosingCell b.1 with hy₁
  set y₂ := enclosingCell (b.1 + unitStep F.depth b.2) with hy₂
  have k1 : y₁ ∈ D.keptCells := (mem_cutBelow_depth hs' hL _ _).1 hb'.1
  have k2 : y₂ ∈ D.keptCells := (mem_cutBelow_depth hs' hL _ _).1 hb'.2
  have b12 : y₂ ∈ cellBall y₁ 1 :=
    BlockLevels.enclosingCell_add_unitStep_mem_cellBall (Nat.le_succ _) hL.pos b.1 b.2
  have ball12 : y₁ ∈ cellBall y 1 ∧ y₂ ∈ cellBall y 1 := by
    rcases hend with h | h
    · rw [← h]
      exact ⟨self_mem_cellBall _ _, b12⟩
    · rw [← h]
      exact ⟨mem_cellBall_symm b12, self_mem_cellBall _ _⟩
  have tocells : ∀ z ∈ cellBall y 1, z ∈ D.keptCells → z ∈ S₁ := by
    intro z hz hk
    by_contra hn
    apply hyB
    rw [mem_thickening]
    refine ⟨hyk, z, Finset.mem_sdiff.2 ⟨hk, hn⟩, ?_⟩
    have := cellSupDist_le_one_of_mem_cellBall hA hz
    omega
  have s1 : y₁ ∈ S₁ := tocells _ ball12.1 k1
  have s2 : y₂ ∈ S₁ := tocells _ ball12.2 k2
  have cells : ∀ c ∈ bondsOfEndBlocks b, (enclosingCell c.1 = y₁ ∨ enclosingCell c.1 = y₂) ∧
      (enclosingCell (c.1 + unitStep F.depth c.2) = y₁ ∨ enclosingCell (c.1 + unitStep F.depth c.2) = y₂) := by
    intro c hc'
    have h1 : c.1 ∈ sitesBelow F.depth y₁ ∪ sitesBelow F.depth y₂ ∧
        c.1 + unitStep F.depth c.2 ∈ sitesBelow F.depth y₁ ∪ sitesBelow F.depth y₂ := by
      simpa only [bondsOfEndBlocks, cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
        using hc'
    rw [Finset.mem_union, Finset.mem_union, mem_sitesBelow_depth hs' hL, mem_sitesBelow_depth hs' hL,
      mem_sitesBelow_depth hs' hL, mem_sitesBelow_depth hs' hL] at h1
    exact h1
  have inS : ∀ z, (z = y₁ ∨ z = y₂) → z ∈ S₁ ∧ z ∈ D.keptCells ∧ z ∈ cellBall y 1 := by
    rintro z (rfl | rfl)
    · exact ⟨s1, k1, ball12.1⟩
    · exact ⟨s2, k2, ball12.2⟩
  have hbS : ∀ c ∈ bondsOfEndBlocks b, c ∈ innerBonds S₁ F.depth ∧ c ∈ innerBonds D.keptCells F.depth := by
    intro c hc'
    obtain ⟨e1, e2⟩ := cells c hc'
    obtain ⟨a1, a2, -⟩ := inS _ e1
    obtain ⟨a3, a4, -⟩ := inS _ e2
    refine ⟨?_, ?_⟩
    · simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      exact ⟨(mem_sitesOfCells_depth hs' hL _ _).2 a1, (mem_sitesOfCells_depth hs' hL _ _).2 a3⟩
    · simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      exact ⟨(mem_sitesOfCells_depth hs' hL _ _).2 a2, (mem_sitesOfCells_depth hs' hL _ _).2 a4⟩
  have hagree : ∀ c ∈ bondsOfEndBlocks b, D.fineField c.1 c.2 = U2 F.depth c.1 c.2 := by
    intro c hc'
    obtain ⟨e1, e2⟩ := cells c hc'
    obtain ⟨a1, -, a2⟩ := inS _ e1
    obtain ⟨a3, -, a4⟩ := inS _ e2
    refine (hsame c ?_ (hnoA _ a2) (hnoA _ a4)).symm
    simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨(mem_cutBelow_depth hs' hL _ _).2 (mem_coreCells_of_far D C hsub hsp 5 (by norm_num) a1),
      (mem_cutBelow_depth hs' hL _ _).2 (mem_coreCells_of_far D C hsub hsp 5 (by norm_num) a3)⟩
  have hlex : ∀ c ∈ bondsOfEndBlocks b,
      lexBondCoordinate D.topField D.fineField c = lexBondCoordinate D.topField (U2 F.depth) c := by
    intro c hc'
    obtain ⟨e1, e2⟩ := cells c hc'
    refine bondCoordinate_congr hs' hL D.topField D.fineField (U2 F.depth) c fun b' hb'' => hagree b' ?_
    have hsubQ : sitesBelow F.depth (enclosingCell c.1) ∪
        sitesBelow F.depth (enclosingCell (c.1 + unitStep F.depth c.2)) ⊆
        sitesBelow F.depth y₁ ∪ sitesBelow F.depth y₂ := by
      refine Finset.union_subset ?_ ?_
      · rcases e1 with h | h <;> rw [h]
        · exact Finset.subset_union_left
        · exact Finset.subset_union_right
      · rcases e2 with h | h <;> rw [h]
        · exact Finset.subset_union_left
        · exact Finset.subset_union_right
    exact BlockLevels.cutBonds_mono hsubQ hb''
  have hexists : ∃ c ∈ bondsOfEndBlocks b,
      d < ‖(lexBondCoordinate D.topField D.fineField c : ℍ[ℝ]) - lexBondCoordinate D.topField Wl c‖ := by
    by_contra hcon
    have hall : ∀ c ∈ bondsOfEndBlocks b,
        ‖(lexBondCoordinate D.topField D.fineField c : ℍ[ℝ]) - lexBondCoordinate D.topField Wl c‖ ≤ d := by
      intro c hc'
      by_contra hlt
      exact hcon ⟨c, hc', not_le.1 hlt⟩
    have := horder b d (fun c hc' => by
      rw [hlex c hc']
      exact hn1 c (hbS c hc').1) (fun c hc' => hn2 c (hbS c hc').2) hall π
    linarith
  obtain ⟨c, hc', hbigc⟩ := hexists
  obtain ⟨e1, e2⟩ := cells c hc'
  obtain ⟨-, -, a2⟩ := inS _ e1
  obtain ⟨-, -, a4⟩ := inS _ e2
  have hcl := hclose y hyk hyB c (hbS c hc').2 (hbS c hc').1 (cellSupDist_le_one_of_mem_cellBall hA a2)
    (cellSupDist_le_one_of_mem_cellBall hA a4)
  rw [hlex c hc'] at hbigc
  have hfar : d / 2 ≤
      ‖(lexBondCoordinate D.topField (U2 F.depth) c : ℍ[ℝ]) - lexBondCoordinate D.topField Wl1 c‖ := by
    have h3 := norm_sub_le_norm_sub_add_norm_sub (lexBondCoordinate D.topField (U2 F.depth) c : ℍ[ℝ])
      (lexBondCoordinate D.topField Wl1 c) (lexBondCoordinate D.topField Wl c)
    rw [norm_sub_rev (lexBondCoordinate D.topField Wl1 c : ℍ[ℝ])] at h3
    linarith
  refine ⟨c, ?_, a2, hfar⟩
  simp only [chordBonds, Finset.mem_filter]
  refine ⟨(hbS c hc').1, fun ht => ?_⟩
  rw [lexBondCoordinate_of_isAxialTreeBond hs hL _ _ c ht, lexBondCoordinate_of_isAxialTreeBond hs hL _ _ c ht]
    at hfar
  simp only [sub_self, norm_zero] at hfar
  linarith
theorem le_sq_of_one_add_le (x c : ℝ) (hx : 0 ≤ x) (h : 1 + x ≤ c) : x ≤ c ^ 2 := by nlinarith
theorem bad_count_arith (nb nA nB nC nh ne nc nT CD κ s lamh d bracket sum cE : ℝ) (hnb : nb ≤ nA + nB + nC)
    (hA : nA ≤ nh * 2401) (hB : nB ≤ CD * (ne + nc)) (hC : nC ≤ 81 * nT) (hc : nc ≤ nh) (hCD : 1 ≤ CD)
    (hne : 0 ≤ ne) (hnc : 0 ≤ nc) (hnh : 0 ≤ nh) (hcE : 0 < cE)
    (h1 : cE ≤ (κ / 4) * s ^ 2 / (2401 + CD)) (h2 : cE ≤ s ^ 2 / CD) (h3 : cE ≤ lamh * (d / 2) ^ 2 / 81)
    (hsum : (d / 2) ^ 2 * nT ≤ sum) (hlam : 0 < lamh) (hbr : lamh * sum ≤ bracket) (hnT : 0 ≤ nT) :
    cE * nb ≤ (κ / 4) * s ^ 2 * nh + s ^ 2 * ne + bracket := by
  have p1 : cE * (2401 + CD) ≤ (κ / 4) * s ^ 2 := by
    rwa [le_div_iff₀ (by linarith)] at h1
  have p2 : cE * CD ≤ s ^ 2 := by
    rwa [le_div_iff₀ (by linarith)] at h2
  have p3 : cE * 81 ≤ lamh * (d / 2) ^ 2 := by
    rwa [le_div_iff₀ (by norm_num)] at h3
  have q1 : cE * nb ≤ cE * (nh * 2401 + CD * (ne + nc) + 81 * nT) :=
    mul_le_mul_of_nonneg_left (by linarith) hcE.le
  have q2 : cE * (2401 + CD) * nh ≤ (κ / 4) * s ^ 2 * nh := mul_le_mul_of_nonneg_right p1 hnh
  have q3 : cE * CD * ne ≤ s ^ 2 * ne := mul_le_mul_of_nonneg_right p2 hne
  have q4 : cE * 81 * nT ≤ lamh * (d / 2) ^ 2 * nT := mul_le_mul_of_nonneg_right p3 hnT
  have q5 : lamh * ((d / 2) ^ 2 * nT) ≤ lamh * sum := mul_le_mul_of_nonneg_left hsum hlam.le
  have q6 : cE * CD * nc ≤ cE * CD * nh :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  nlinarith
set_option maxHeartbeats 4000000 in
theorem badCellsBound (hF : minimizerQuadraticGapStatement)
    (hLF : minimizingFieldsLocalStatement)
    (hC : NearTopCoordinateBound) (hO : BondCoordinatesLexComparison)
    (hK : CornerDefectBound) (hKept : KeptCellsAwayFromBad)
    (hCr : CrowdedCellsBound) (hLV : minimalChainExistenceStatement)
    (hCost : WholeCellCostEqualsMinimalAction) : BadCellsBound := by
  intro a κ ε Θ C CJ J₀ ha hκ hε hΘ hC0 hCJ hJ
  have ha0 : 0 < a := by linarith
  have hΘ0 : 0 < Θ := by linarith
  obtain ⟨L1, h1⟩ := hF a ha
  obtain ⟨δ, hδ, L2, h2⟩ := hLF a ha
  obtain ⟨K₁, hK₁, hco⟩ := hC
  obtain ⟨K₂, hK₂, hor⟩ := hO
  obtain ⟨cK, hcK, -, L3, hk⟩ := hK
  refine ⟨max L1 (max L2 L3), fun L hodd hL g => ?_⟩
  have l1 : L1 ≤ L := (le_max_left _ _).trans hL
  have l2 : L2 ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have l3 : L3 ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  obtain ⟨lam, r₀, hlam, hr₀, hfa⟩ := h1 L hodd l1
  obtain ⟨σ, N, hσ, hN, hlf⟩ := h2 L hodd l2
  set Cn := 1 + Θ + CJ / cK + CJ with hCn
  have hx0 : 0 < CJ / cK := div_pos hCJ hcK
  have hCn1 : 1 ≤ Cn := by rw [hCn]; linarith
  have hCnΘ : Θ ≤ Cn := by rw [hCn]; linarith
  have hCn0 : 0 < Cn := by linarith
  set K1 := K₁ L with hK1d
  set K2 := K₂ L with hK2d
  have hK1p : 0 < K1 := by have := hK₁ L; linarith
  have hK2p : 0 < K2 := by have := hK₂ L; linarith
  set M := N * Θ * 258 * K2 with hM
  have hMp : 0 < M := by positivity
  obtain ⟨R₀, hR₀⟩ := exists_nat_ge (M / δ)
  set R := R₀ + 1 with hRd
  have hexp : M * Real.exp (-δ * ((R : ℝ) - 1)) ≤ 1 := by
    have e1 : (R : ℝ) - 1 = R₀ := by rw [hRd]; push_cast; ring
    have e2 : M ≤ δ * R₀ := by
      rw [div_le_iff₀ hδ] at hR₀
      linarith
    have e3 := Real.add_one_le_exp (δ * R₀)
    have e4 : Real.exp (-δ * (R₀ : ℝ)) * Real.exp (δ * R₀) = 1 := by
      rw [← Real.exp_add]; simp
    rw [e1]
    have e5 := Real.exp_pos (-δ * (R₀ : ℝ))
    nlinarith
  have hLp : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hodd.pos
  set q := cK * (L : ℝ) ^ (-4 : ℤ) / (2 * (CJ + 1)) with hq
  have hq0 : 0 < q := by positivity
  refine ⟨min (min (r₀ / Cn) (1 / (K1 * Cn))) (min (min (σ / Θ) (1 / (K2 * K1 * Cn)))
    (min (1 / (K2 * N * Θ)) (min 1 q))), ?_, fun s hs0 hss => ?_⟩
  · refine lt_min (lt_min (by positivity) (by positivity)) (lt_min (lt_min (by positivity) (by positivity))
      (lt_min (by positivity) (lt_min one_pos hq0)))
  have x1 : s ≤ r₀ / Cn := hss.trans ((min_le_left _ _).trans (min_le_left _ _))
  have x2 : s ≤ 1 / (K1 * Cn) := hss.trans ((min_le_left _ _).trans (min_le_right _ _))
  have x3 : s ≤ σ / Θ := hss.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have x4 : s ≤ 1 / (K2 * K1 * Cn) :=
    hss.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have x5 : s ≤ 1 / (K2 * N * Θ) :=
    hss.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have x6 : s ≤ 1 := hss.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have x7 : s ≤ q := hss.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  set d := s / (129 * K2) with hd
  have hd0 : 0 < d := by positivity
  obtain ⟨CDn, hCDn⟩ : ∃ n : ℕ, n = max ((2 ^ 17 + 2 * (R + 1)) ^ 4) (2 ^ 72) := ⟨_, rfl⟩
  obtain ⟨CD, hCD⟩ : ∃ x : ℝ, x = (CDn : ℝ) := ⟨_, rfl⟩
  have hCD1 : 1 ≤ CD := by
    have h1 : 1 ≤ CDn := by
      rw [hCDn]
      exact le_max_of_le_right Nat.one_le_two_pow
    rw [hCD]
    exact_mod_cast h1
  refine ⟨min (min ((κ / 4) * s ^ 2 / (2401 + CD)) (s ^ 2 / CD)) ((lam / 2) * (d / 2) ^ 2 / 81), ?_, ?_⟩
  · refine lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  intro F D U2 S₁ Wl hFL hcub hth hfill hsub hreg hsp hcnt hleast
  subst hFL
  classical
  have hcnt' := hcnt (R + 1)
  rw [← hCDn] at hcnt'
  clear hcnt hCDn
  have hc64 : IsCubicTorus F 64 := ⟨hcub.1, by have := hcub.2; omega⟩
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hcub.1 i]; have := hcub.2; omega
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hA : IsAdmissibleAmbient F := Or.inr fun i => by rw [hcub.1 i]; have := hcub.2; omega
  obtain ⟨hregK, hcoldK, -⟩ := hKept F F.blockSide g a s (Θ * s) C J₀ D rfl hodd hcub hth
  have hcr := hCr F F.blockSide g a s (Θ * s) J₀ D rfl hodd hcub
  have hcr' : (D.crowdedCells).card ≤ D.hotFineLumps.card := by
    have h625 : 625 * (D.crowdedCells).card ≤ J₀ * (D.crowdedCells).card := Nat.mul_le_mul_right _ hJ
    omega
  set r := Cn * s with hr
  have hr0 : 0 < r := by positivity
  have hrr : r ≤ r₀ := by
    rw [hr]
    rw [le_div_iff₀ hCn0] at x1
    linarith
  have hK1r : K1 * r ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at x2
    rw [hr]
    linarith
  have hK1r2 : K1 * r ≤ 1 / K2 := by
    rw [le_div_iff₀ (by positivity)] at x4
    rw [le_div_iff₀ hK2p, hr]
    linarith
  have hΘσ : Θ * s ≤ σ := by
    rw [le_div_iff₀ hΘ0] at x3
    linarith
  have hNΘ : N * (Θ * s) ≤ 1 / K2 := by
    rw [le_div_iff₀ (by positivity)] at x5
    rw [le_div_iff₀ hK2p]
    linarith
  have hΘr : Θ * s ≤ r := by
    rw [hr]
    exact mul_le_mul_of_nonneg_right hCnΘ hs0.le
  have hsmall : CJ * s ^ 2 < cK * (F.blockSide : ℝ) ^ (-4 : ℤ) := by
    have hpos : 0 < cK * (F.blockSide : ℝ) ^ (-4 : ℤ) := by positivity
    have e1 : s ^ 2 ≤ s := pow_le_of_le_one hs0.le x6 two_ne_zero
    have e2 : (2 * (CJ + 1)) * q = cK * (F.blockSide : ℝ) ^ (-4 : ℤ) := by
      rw [hq]
      field_simp
    have a1 : CJ * s ^ 2 ≤ CJ * s := mul_le_mul_of_nonneg_left e1 hCJ.le
    have a2 : CJ * s ≤ CJ * q := mul_le_mul_of_nonneg_left x7 hCJ.le
    have a3 : 2 * (CJ + 1) * q = CJ * q + (CJ + 2) * q := by ring
    have a4 : 0 < (CJ + 2) * q := by positivity
    rw [← e2, a3]
    linarith
  have hnear : LiesNearTop r S₁ D.topField (U2 F.depth) := by
    refine liesNearTop_of_filling D C ε CJ cK U2 S₁ r ha hodd hs hcK
      (fun p U e1 e2 => (hk a F.blockSide ha hodd l3 F rfl hA F.depth (Nat.le_succ _)).1 p U e1 e2) hsmall hfill
      hsub hsp hr0.le ?_ ?_
    · have e1 : CJ * s ^ 2 / cK = (CJ / cK) * s ^ 2 := by ring
      rw [e1, hr, mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact le_sq_of_one_add_le _ _ hx0.le (by rw [hCn]; linarith)
    · rw [hr, mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact le_sq_of_one_add_le _ _ hCJ.le (by rw [hCn]; linarith)
  have hcoldθ : IsCold S₁ F.top (Θ * s) D.topField := by
    intro p hp
    refine hcoldK p ?_
    simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp ⊢
    refine ⟨mem_sitesOfCells_top.2 (hsub (mem_sitesOfCells_top.1 hp.1)), hp.2.1, fun x hx => ?_⟩
    exact mem_sitesOfCells_top.2 (hsub (mem_sitesOfCells_top.1 (hp.2.2 hx)))
  have hcoldr : IsCold S₁ F.top r D.topField := fun p hp => (hcoldθ p hp).trans_le hΘr
  have hplain : ∀ (T : Finset F.Cell) (W : F.GaugeField F.depth),
      plainBlockEnergy a T W D.topField = blockEnergy a T F.depth W D.topField :=
    fun T W => (hCost F a T hodd ha0.le).2.2 W D.topField
  obtain ⟨Wl1, hWl1, hΔ⟩ : ∃ Wl1 : F.GaugeField F.depth, IsMinimizingField a S₁ D.topField Wl1 ∧
      (D.keptCells \ S₁ = ∅ → Wl1 = Wl) := by
    by_cases hemp : D.keptCells \ S₁ = ∅
    · have e : S₁ = D.keptCells := Finset.Subset.antisymm hsub (Finset.sdiff_eq_empty_iff_subset.1 hemp)
      exact ⟨Wl, by rw [e]; exact hleast, fun _ => rfl⟩
    · obtain ⟨W₀, -, hmin⟩ := (hLV F a S₁ ha0.le).2.2.1 F.depth D.topField
      exact ⟨W₀, fun W' => by rw [hplain, hplain]; exact hmin W', fun h => absurd h hemp⟩
  have hfield := hfa F 1024 S₁ rfl hc64 le_rfl hreg r D.topField (U2 F.depth) Wl1 hr0 hrr hcoldr hnear hWl1
  have hlf' := hlf F 1024 D.keptCells S₁ rfl hc64 le_rfl hregK hreg (Θ * s) D.topField Wl Wl1 (by positivity) hΘσ
    hcoldK hcoldθ hleast hWl1
  have hn1 : ∀ c ∈ innerBonds S₁ F.depth, ‖(lexBondCoordinate D.topField (U2 F.depth) c : ℍ[ℝ])‖ ≤ 1 / K2 :=
    fun c hc => (hco F hodd hc64 S₁ D.topField (U2 F.depth) r hr0.le hK1r hnear c hc).trans hK1r2
  have hn2 : ∀ c ∈ innerBonds D.keptCells F.depth, ‖(lexBondCoordinate D.topField Wl c : ℍ[ℝ])‖ ≤ 1 / K2 :=
    fun c hc => (hlf'.1 c hc).trans hNΘ
  have hbound : N * (Θ * s) * Real.exp (-δ * ((R : ℝ) - 1)) ≤ d / 2 := by
    have e1 : d / 2 = s / (258 * K2) := by rw [hd]; field_simp; ring
    rw [e1, le_div_iff₀ (by positivity)]
    have e2 : N * (Θ * s) * Real.exp (-δ * ((R : ℝ) - 1)) * (258 * K2) =
        s * (M * Real.exp (-δ * ((R : ℝ) - 1))) := by rw [hM]; ring
    rw [e2]
    exact mul_le_of_le_one_right hs0.le hexp
  have hclose : ∀ y ∈ D.keptCells, y ∉ thickening D.keptCells (D.keptCells \ S₁) (R + 1) →
      ∀ c ∈ innerBonds D.keptCells F.depth, c ∈ innerBonds S₁ F.depth →
      cellSupDist y (enclosingCell c.1) ≤ 1 → cellSupDist y (enclosingCell (c.1 + unitStep F.depth c.2)) ≤ 1 →
      ‖(lexBondCoordinate D.topField Wl c : ℍ[ℝ]) - lexBondCoordinate D.topField Wl1 c‖ ≤ d / 2 := by
    intro y hy hyB c c1 c2 d1 d2
    refine lexBondCoordinate_minimizers_close hc64 D.topField Wl Wl1 D.keptCells S₁ hsub R (by omega) (d / 2)
      (by positivity) hΔ ?_ y hy hyB c c1 c2 d1 d2
    intro y' r' hr' e1 e2 b b1 b2 b3 b4
    subst hr'
    exact (hlf'.2 y' R (by omega) e1 e2 b b1 b2 b3 b4).trans hbound
  have hKd : K2 * d < s / 128 := by
    have e1 : K2 * d = s / 129 := by rw [hd]; field_simp
    rw [e1]
    exact div_lt_div_of_pos_left hs0 (by norm_num) (by norm_num)
  set A := D.keptCells.filter fun y => ∃ z ∈ cellBall y 1, nearbyLumps D.hotFineLumps z ≠ ∅ with hAd
  set B := thickening D.keptCells (D.keptCells \ S₁) (R + 1) with hBd
  set bad := HoleBounds.badCells (s / 128) D.keptCells D.topField D.fineField Wl with hbadd
  set Cc := (bad \ A) \ B with hCc
  have hbadk : ∀ y ∈ bad, y ∈ D.keptCells := fun y hy => by
    simp only [hbadd, HoleBounds.badCells, Finset.mem_filter] at hy
    exact hy.1
  have hsubset : bad ⊆ A ∪ B ∪ Cc := by
    intro y hy
    by_cases h1 : y ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
    · by_cases h2 : y ∈ B
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h2)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨hy, h1⟩, h2⟩)
  have hkey : ∀ y ∈ Cc, ∃ c ∈ chordBonds S₁, enclosingCell c.1 ∈ cellBall y 1 ∧
      d / 2 ≤ ‖(lexBondCoordinate D.topField (U2 F.depth) c : ℍ[ℝ]) - lexBondCoordinate D.topField Wl1 c‖ := by
    intro y hy
    obtain ⟨hy1, hyB⟩ := Finset.mem_sdiff.1 hy
    obtain ⟨hyb, hyA⟩ := Finset.mem_sdiff.1 hy1
    refine exists_far_chordBond_of_bad D C K2 d U2 S₁ Wl Wl1 R hc64 hodd hsub hsp hfill.2.2.2 hn1 hn2
      (fun b d' e1 e2 e3 π => hor F hodd hc64 D.topField D.fineField Wl b d' e1 e2 e3 π) hclose hKd hd0 y hyb ?_
      hyB
    intro z hz
    by_contra hne
    exact hyA (Finset.mem_filter.2 ⟨hbadk y hyb, z, hz, hne⟩)
  choose! cf hcf1 hcf2 hcf3 using hkey
  have hfib : Cc.card ≤ 81 * (Cc.image cf).card := by
    refine Finset.card_le_mul_card_image Cc 81 fun c hc => ?_
    have hsub2 : (Cc.filter fun y => cf y = c) ⊆ cellBall (enclosingCell c.1) 1 := by
      intro y hy
      obtain ⟨hy1, rfl⟩ := Finset.mem_filter.1 hy
      exact mem_cellBall_symm (hcf2 y hy1)
    have := (Finset.card_le_card hsub2).trans (card_cellBall_le _ 1)
    norm_num at this
    exact this
  have hTsub : Cc.image cf ⊆ chordBonds S₁ := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    exact hcf1 y hy
  set sum := ∑ b ∈ chordBonds S₁,
    ‖(lexBondCoordinate D.topField (U2 F.depth) b : ℍ[ℝ]) - lexBondCoordinate D.topField Wl1 b‖ ^ 2 with hsumd
  have hsum : (d / 2) ^ 2 * ((Cc.image cf).card : ℝ) ≤ sum := by
    have e1 : ∀ c ∈ Cc.image cf, (d / 2) ^ 2 ≤
        ‖(lexBondCoordinate D.topField (U2 F.depth) c : ℍ[ℝ]) - lexBondCoordinate D.topField Wl1 c‖ ^ 2 := by
      intro c hc
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
      exact pow_le_pow_left₀ (by positivity) (hcf3 y hy) 2
    have e2 := Finset.card_nsmul_le_sum _ _ _ e1
    rw [nsmul_eq_mul] at e2
    have e3 : ∑ c ∈ Cc.image cf,
        ‖(lexBondCoordinate D.topField (U2 F.depth) c : ℍ[ℝ]) - lexBondCoordinate D.topField Wl1 c‖ ^ 2 ≤ sum :=
      Finset.sum_le_sum_of_subset_of_nonneg hTsub fun _ _ _ => by positivity
    linarith
  have hnb : (bad.card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) + (Cc.card : ℝ) := by
    have e1 := Finset.card_le_card hsubset
    have e2 := Finset.card_union_le (A ∪ B) Cc
    have e3 := Finset.card_union_le A B
    have : bad.card ≤ A.card + B.card + Cc.card := by omega
    exact_mod_cast this
  have hnA : (A.card : ℝ) ≤ (D.hotFineLumps.card : ℝ) * 2401 := by
    have := card_near_hotLumps_le D hodd hs' rfl
    exact_mod_cast this
  have hnB : (B.card : ℝ) ≤ CD * (((D.excitedCells C).card : ℝ) + ((D.crowdedCells).card : ℝ)) := by
    rw [hCD]
    exact_mod_cast hcnt'
  have hnC : (Cc.card : ℝ) ≤ 81 * ((Cc.image cf).card : ℝ) := by exact_mod_cast hfib
  have hcr2 : ((D.crowdedCells).card : ℝ) ≤ (D.hotFineLumps.card : ℝ) := by exact_mod_cast hcr'
  exact bad_count_arith _ _ _ _ _ _ _ _ CD κ s (lam / 2) d _ sum _ hnb hnA hnB hnC hcr2 hCD1 (by positivity)
    (by positivity) (by positivity) (lt_min (lt_min (by positivity) (by positivity)) (by positivity))
    ((min_le_left _ _).trans (min_le_left _ _)) ((min_le_left _ _).trans (min_le_right _ _)) (min_le_right _ _)
    hsum (by positivity) hfield (by positivity)
end YangMills.Construction.HoleSavings.BadCellCount
end
