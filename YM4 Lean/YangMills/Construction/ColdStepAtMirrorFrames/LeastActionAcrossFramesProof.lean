import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfCellsAndSites
import YangMills.Construction.ColdChainAtEveryLevel.LinesOfTheBlocksOfABond
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOverContoursOfAFormForm
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import YangMills.Construction.ColdStepAtMirrorFrames.ComponentsOfAFieldAlongAnElement
import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionAcrossFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
private abbrev IntPoint : Type := Fin 4 → ℤ
variable {F G : BlockFrame}
private theorem siteOfCoords_siteCoords {k : ℕ} (y : F.Site k) : siteOfCoords k (siteCoords y) = y := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
private theorem transferSite_siteOfCoords {k : ℕ} (hp : ∀ i, F.period k i = G.period k i) (z : IntPoint) :
    transferSite G (siteOfCoords k z : F.Site k) = (siteOfCoords k z : G.Site k) := by apply _root_.YangMills.Construction.FrameTorusAction.transferSite_siteOfCoords <;> assumption
private theorem transferSite_transferSite {k : ℕ} (hp : ∀ i, F.period k i = G.period k i) (x : F.Site k) :
    transferSite F (transferSite G x) = x := by apply _root_.YangMills.Construction.FrameTorusAction.transferSite_transferSite <;> assumption
private theorem transferField_siteOfCoords {k : ℕ} (hp : ∀ i, F.period k i = G.period k i)
    (W : F.GaugeField k) (z : IntPoint) (i : Fin 4) :
    transferField G W (siteOfCoords k z) i = W (siteOfCoords k z) i := by
  unfold transferField
  rw [transferSite_siteOfCoords (fun i => (hp i).symm)]
private def stepOffset (st : PathStep) : IntPoint :=
  if st.2 then Pi.single st.1 1 else - Pi.single st.1 1
private theorem siteOfCoords_add {H : BlockFrame} (j : ℕ) (a b : IntPoint) :
    (siteOfCoords j (a + b) : H.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_add <;> assumption
private theorem siteOfCoords_neg {H : BlockFrame} (j : ℕ) (a : IntPoint) :
    (siteOfCoords j (-a) : H.Site j) = - siteOfCoords j a := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_neg <;> assumption
private theorem siteOfCoords_add_stepDisplacement {H : BlockFrame} (j : ℕ) (z : IntPoint) (st : PathStep) :
    (siteOfCoords j z : H.Site j) + stepDisplacement j st = siteOfCoords j (z + stepOffset st) := by
  unfold stepDisplacement stepOffset unitStep
  by_cases h : st.2 = true
  · simp only [h, if_true, siteOfCoords_add]
  · simp only [h, Bool.false_eq_true, if_false, siteOfCoords_add, siteOfCoords_neg]
abbrev _root_.YangMills.DeltaSharedProofs.p4150 := @siteOfCoords_add_stepDisplacement
private theorem siteOfCoords_sub_unitStep {H : BlockFrame} (j : ℕ) (z : IntPoint) (i : Fin 4) :
    (siteOfCoords j z : H.Site j) - unitStep j i = siteOfCoords j (z - Pi.single i 1) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, siteOfCoords_add, siteOfCoords_neg]; rfl
private theorem pathHolonomy_transferField {k : ℕ} (hp : ∀ i, F.period k i = G.period k i)
    (W : F.GaugeField k) :
    ∀ (p : List PathStep) (z : IntPoint),
      pathHolonomy (transferField G W) (siteOfCoords k z) p = pathHolonomy W (siteOfCoords k z) p
  | [], _ => rfl
  | st :: r, z => by
    rw [pathHolonomy, pathHolonomy, siteOfCoords_add_stepDisplacement, siteOfCoords_add_stepDisplacement,
      pathHolonomy_transferField hp W r]
    congr 1
    unfold linkValue
    by_cases hb : st.2 = true
    · simp only [hb, if_true, transferField_siteOfCoords hp]
    · simp only [hb, Bool.false_eq_true, if_false, siteOfCoords_sub_unitStep, transferField_siteOfCoords hp]
private theorem period_eq_period_succ_mul {H : BlockFrame} {j : ℕ} (hj : j < H.top) (i : Fin 4) :
    H.period j i = H.period (j + 1) i * H.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.period_eq_mul_blockSide <;> assumption
private theorem refineSite_siteOfCoords {H : BlockFrame} {j : ℕ} (hj : j < H.top) (z : IntPoint) :
    (refineSite (siteOfCoords (j + 1) z : H.Site (j + 1)) : H.Site j) =
      siteOfCoords j (fun i => (H.blockSide : ℤ) * z i) := by apply _root_.YangMills.Construction.BlockLines.refineSite_siteOfCoords <;> assumption
private theorem contourAverage_transferField {k : ℕ} (hL : F.blockSide = G.blockSide) (hF : k < F.top)
    (hG : k < G.top) (hp : ∀ i, F.period k i = G.period k i) (W : F.GaugeField k) (z : IntPoint) (i : Fin 4) :
    _root_.YangMills.Construction.BlockAverages.contourAverage (transferField G W) (siteOfCoords (k + 1) z, i) =
      _root_.YangMills.Construction.BlockAverages.contourAverage W (siteOfCoords (k + 1) z, i) := by
  unfold _root_.YangMills.Construction.BlockAverages.contourAverage
  dsimp only
  rw [refineSite_siteOfCoords hG, refineSite_siteOfCoords hF, hL]
  congr 1
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun π _ => ?_
  rw [pathHolonomy_transferField hp]
private theorem blockFit_transferField {k : ℕ} (hL : F.blockSide = G.blockSide) (hF : k < F.top)
    (hG : k < G.top) (hp : ∀ i, F.period k i = G.period k i)
    (hp' : ∀ i, F.period (k + 1) i = G.period (k + 1) i)
    (W : F.GaugeField k) (V : F.GaugeField (k + 1)) (z : IntPoint) (i : Fin 4) :
    blockFit (transferField G W) (transferField G V) (siteOfCoords (k + 1) z, i) =
      blockFit W V (siteOfCoords (k + 1) z, i) := by
  unfold blockFit
  dsimp only
  rw [contourAverage_transferField hL hF hG hp, transferField_siteOfCoords hp']
private theorem mem_innerBonds_finiteCells {H : BlockFrame} (hodd : Odd H.blockSide)
    (hs : ∀ i, 0 < H.extent i) {k : ℕ} (hk : k ≤ H.top)
    (b : H.Site k × Fin 4) : b ∈ innerBonds (finiteCells H) k := by
  unfold innerBonds
  rw [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨_root_.YangMills.Construction.ColdStepAtMirrorFrames.mem_sitesOfCells_finiteCells hodd hs hk _, Finset.mem_univ _⟩,
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.mem_sitesOfCells_finiteCells hodd hs hk _⟩
private theorem mem_innerPlaquettes_finiteCells_iff {H : BlockFrame} (hodd : Odd H.blockSide)
    (hs : ∀ i, 0 < H.extent i) {k : ℕ} (hk : k ≤ H.top)
    (p : H.Site k × Fin 4 × Fin 4) : p ∈ innerPlaquettes (finiteCells H) k ↔ p.2.1 < p.2.2 := by
  unfold innerPlaquettes
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
  constructor
  · exact fun h => h.2.1
  · intro h
    exact ⟨⟨_root_.YangMills.Construction.ColdStepAtMirrorFrames.mem_sitesOfCells_finiteCells hodd hs hk _, Finset.mem_univ _, Finset.mem_univ _⟩, h,
      fun x _ => _root_.YangMills.Construction.ColdStepAtMirrorFrames.mem_sitesOfCells_finiteCells hodd hs hk x⟩
private theorem wilsonAction_transferField (hodd : Odd F.blockSide) (hG : Odd G.blockSide)
    (hsF : ∀ i, 0 < F.extent i) (hsG : ∀ i, 0 < G.extent i)
    (hp : ∀ i, F.period 0 i = G.period 0 i) (U : F.GaugeField 0) :
    wilsonAction (finiteCells F) U = wilsonAction (finiteCells G) (transferField G U) := by
  unfold wilsonAction
  refine Finset.sum_bij' (fun p _ => (transferSite G p.1, p.2)) (fun p _ => (transferSite F p.1, p.2))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp'
    rw [mem_innerPlaquettes_finiteCells_iff hG hsG (Nat.zero_le _)]
    exact (mem_innerPlaquettes_finiteCells_iff hodd hsF (Nat.zero_le _) p).1 hp'
  · intro p hp'
    rw [mem_innerPlaquettes_finiteCells_iff hodd hsF (Nat.zero_le _)]
    exact (mem_innerPlaquettes_finiteCells_iff hG hsG (Nat.zero_le _) p).1 hp'
  · intro p _
    exact Prod.ext (transferSite_transferSite hp _) rfl
  · intro p _
    exact Prod.ext (transferSite_transferSite (fun i => (hp i).symm) _) rfl
  · intro p _
    unfold plaquetteHolonomy
    dsimp only
    obtain ⟨x, μ, ν⟩ := p
    dsimp only
    conv_lhs => rw [← siteOfCoords_siteCoords x]
    unfold transferSite
    rw [pathHolonomy_transferField hp]
private theorem sum_blockFit_transferField {k : ℕ} (h : SharePeriods F G (k + 1)) (a : ℝ)
    (W : F.GaugeField k) (V : F.GaugeField (k + 1)) :
    ∑ c ∈ innerBonds (finiteCells F) (k + 1), blockFit W V c =
      ∑ c ∈ innerBonds (finiteCells G) (k + 1), blockFit (transferField G W) (transferField G V) c := by
  have hG : Odd G.blockSide := h.blockSide_eq ▸ h.blockSide_odd
  have hp' := h.period_eq (k + 1) le_rfl
  have hp := h.period_eq k (Nat.le_succ k)
  have hkF : k + 1 ≤ F.top := h.le_top_left
  have hkG : k + 1 ≤ G.top := h.le_top_right
  refine Finset.sum_bij' (fun c _ => (transferSite G c.1, c.2)) (fun c _ => (transferSite F c.1, c.2))
    ?_ ?_ ?_ ?_ ?_
  · intro c _; exact mem_innerBonds_finiteCells hG h.extent_pos_right hkG _
  · intro c _; exact mem_innerBonds_finiteCells h.blockSide_odd h.extent_pos_left hkF _
  · intro c _; exact Prod.ext (transferSite_transferSite hp' _) rfl
  · intro c _; exact Prod.ext (transferSite_transferSite (fun i => (hp' i).symm) _) rfl
  · rintro ⟨x, i⟩ _
    dsimp only
    conv_lhs => rw [← siteOfCoords_siteCoords x]
    unfold transferSite
    exact (blockFit_transferField h.blockSide_eq (by omega) (by omega) hp hp' W V (siteCoords x) i).symm
private theorem transferField_surjective {k : ℕ} (hp : ∀ i, F.period k i = G.period k i) :
    Function.Surjective (transferField (F := F) G (k := k)) := by
  intro W'
  refine ⟨transferField F W', ?_⟩
  funext x i
  unfold transferField
  rw [transferSite_transferSite (fun i => (hp i).symm)]
private theorem minimalAction_transferField (a : ℝ) :
    ∀ (k : ℕ), SharePeriods F G k → ∀ W : F.GaugeField k,
      minimalAction a (finiteCells F) k W = minimalAction a (finiteCells G) k (transferField G W)
  | 0, h, W => by
    have hG : Odd G.blockSide := h.blockSide_eq ▸ h.blockSide_odd
    exact wilsonAction_transferField h.blockSide_odd hG h.extent_pos_left h.extent_pos_right
      (h.period_eq 0 le_rfl) W
  | k + 1, h, V => by
    have hk : SharePeriods F G k := ⟨h.blockSide_eq, h.blockSide_odd, h.extent_pos_left, h.extent_pos_right,
      by have := h.le_top_left; omega, by have := h.le_top_right; omega, fun j hj => h.period_eq j (by omega)⟩
    show (⨅ W : F.GaugeField k, (minimalAction a (finiteCells F) k W +
        a * ∑ c ∈ innerBonds (finiteCells F) (k + 1), blockFit W V c)) =
      ⨅ W : G.GaugeField k, (minimalAction a (finiteCells G) k W +
        a * ∑ c ∈ innerBonds (finiteCells G) (k + 1), blockFit W (transferField G V) c)
    rw [← (transferField_surjective (F := F) (G := G) (k := k) (hk.period_eq k le_rfl)).iInf_comp]
    refine iInf_congr fun W => ?_
    rw [minimalAction_transferField a k hk W, sum_blockFit_transferField h a W V]
theorem minimalActionTransfer : MinimalActionTransfer := by
  intro F G K a h
  have hsub : ∀ k, k ≤ K → SharePeriods F G k := fun k hk =>
    ⟨h.blockSide_eq, h.blockSide_odd, h.extent_pos_left, h.extent_pos_right, hk.trans h.le_top_left,
      hk.trans h.le_top_right, fun j hj => h.period_eq j (hj.trans hk)⟩
  refine ⟨fun k W hk => minimalAction_transferField a k (hsub k hk) W, fun k W V hk => ?_,
    fun k W z i hk => ?_,
    fun k W z i hk => transferField_siteOfCoords (h.period_eq k hk) W z i,
    fun k W p z hk => pathHolonomy_transferField (h.period_eq k hk) W p z,
    fun k x hk => transferSite_transferSite (h.period_eq k hk) x,
    fun k y hk => transferSite_transferSite (fun i => (h.period_eq k hk i).symm) y, fun k x hk => ?_⟩
  rotate_left 2
  · funext i
    have h1 : siteCoords (siteOfCoords k (siteCoords x) : F.Site k) i = siteCoords x i := by
      rw [siteOfCoords_siteCoords]
    have h2 : siteCoords (siteOfCoords k (siteCoords x) : F.Site k) i =
        siteCoords x i % (F.period k i : ℤ) := ZMod.coe_intCast _
    have h3 : siteCoords (transferSite G x) i = siteCoords x i % (G.period k i : ℤ) := ZMod.coe_intCast _
    rw [h3, ← h.period_eq k hk i, ← h2, h1]
  · unfold blockEnergy
    rw [minimalAction_transferField a k (hsub k hk.le) W, sum_blockFit_transferField (hsub (k + 1) hk) a W V]
  · have hF := h.le_top_left
    have hG := h.le_top_right
    exact contourAverage_transferField h.blockSide_eq (by omega) (by omega) (h.period_eq k hk.le) W z i
end YangMills.Construction.ColdStepAtMirrorFrames
end
