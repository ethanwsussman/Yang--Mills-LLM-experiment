import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import YangMills.Construction.ColdStepAtMirrorFrames.ColdChainAboveLevelZero
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfADecayOverTheCells
import YangMills.Construction.ColdStepAtMirrorFrames.SumsAgainstFlatResponsesProof
import YangMills.Construction.RunningCouplingSlope.HessianOfAStepIsPositiveProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.deprecated false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F G : BlockFrame}
private theorem transferSite_siteOfCoords {k : ℕ} (hp : ∀ i, F.period k i = G.period k i) (z : Fin 4 → ℤ) :
    transferSite G (siteOfCoords k z : F.Site k) = (siteOfCoords k z : G.Site k) := by apply _root_.YangMills.SharedProofs.p84300 <;> assumption
private theorem transferSite_transferSite {k : ℕ} (hp : ∀ i, F.period k i = G.period k i) (x : F.Site k) :
    transferSite F (transferSite G x) = x := by apply _root_.YangMills.Construction.FrameTorusAction.transferSite_transferSite <;> assumption
private theorem transferSite_add {k : ℕ} (hp : ∀ i, F.period k i = G.period k i) (x y : F.Site k) :
    transferSite G (x + y) = transferSite G x + transferSite G y := by apply _root_.YangMills.Construction.FrameTorusAction.transferSite_add <;> assumption
private theorem valMinAbs_cast_sub_congr {n m : ℕ} (h : n = m) (u v : ℤ) :
    (((u : ZMod m) - (v : ZMod m))).valMinAbs = (((u : ZMod n) - (v : ZMod n))).valMinAbs := by
  subst h
  rfl
private theorem siteSupDist_transferSite {k : ℕ} (hp : ∀ i, F.period k i = G.period k i) (x y : F.Site k) :
    siteSupDist (transferSite G x) (transferSite G y) = siteSupDist x y := by
  unfold siteSupDist
  refine Finset.sup_congr rfl fun i _ => ?_
  have h := valMinAbs_cast_sub_congr (hp i) (siteCoords x i) (siteCoords y i)
  have hx : ((siteCoords x i : ℤ) : ZMod (F.period k i)) = x i := congrFun (siteOfCoords_siteCoords x) i
  have hy : ((siteCoords y i : ℤ) : ZMod (F.period k i)) = y i := congrFun (siteOfCoords_siteCoords y) i
  rw [hx, hy] at h
  show ((((siteCoords x i : ℤ) : ZMod (G.period k i)) - ((siteCoords y i : ℤ) : ZMod (G.period k i))).valMinAbs).natAbs = _
  rw [h]
private theorem siteCoords_transferSite {k : ℕ} (hp : ∀ i, F.period k i = G.period k i) (x : F.Site k) :
    siteCoords (transferSite G x) = siteCoords x := by apply _root_.YangMills.Construction.FrameTorusAction.siteCoords_transferSite <;> assumption
private theorem transferField_leftTranslate {k n : ℕ} (hp : ∀ i, F.period k i = G.period k i)
    (c : Fin n → F.Site k × Fin 4) (X : Fin n → imaginaryQuaternions) (τ : Fin n → ℝ) (W : F.GaugeField k) :
    transferField G (leftTranslate (bondSpread c X τ) W) =
      leftTranslate (bondSpread (fun l => (transferSite G (c l).1, (c l).2)) X τ) (transferField G W) := by apply _root_.YangMills.SharedProofs.p8763 <;> assumption
private def truncatedAction (a : ℝ) (A : BlockFrame) (K : ℕ) (X : A.FieldChain) : ℝ :=
  wilsonAction (finiteCells A) (X 0) +
    a * ∑ j ∈ Finset.range K, ∑ c ∈ innerBonds (finiteCells A) (j + 1), blockFit (X j) (X (j + 1)) c
private def transferChain (B : BlockFrame) {A : BlockFrame} (X : A.FieldChain) : B.FieldChain :=
  fun k => transferField B (X k)
private theorem truncatedAction_transferChain (hA : MinimalActionTransfer) {A B : BlockFrame} {K : ℕ} {a : ℝ}
    (ha : a ≠ 0) (h : SharePeriods A B K) (X : A.FieldChain) :
    truncatedAction a A K X = truncatedAction a B K (transferChain B X) := by
  obtain ⟨h1, h2, -⟩ := hA A B K a h
  unfold truncatedAction
  have e0 : wilsonAction (finiteCells A) (X 0) = wilsonAction (finiteCells B) (transferChain B X 0) :=
    h1 0 (X 0) (Nat.zero_le _)
  rw [e0]
  congr 2
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < K := Finset.mem_range.1 hj
  have e1 := h2 j (X j) (X (j + 1)) hj'
  have e2 := h1 j (X j) hj'.le
  unfold blockEnergy at e1
  rw [e2] at e1
  exact mul_left_cancel₀ ha (add_left_cancel e1)
private def IsTruncatedMinimizer (a : ℝ) (A : BlockFrame) (K : ℕ) (W : A.GaugeField K) (X : A.FieldChain) : Prop :=
  X K = W ∧ ∀ X' : A.FieldChain, X' K = W → truncatedAction a A K X ≤ truncatedAction a A K X'
private theorem SharePeriods.symm {A B : BlockFrame} {K : ℕ} (h : SharePeriods A B K) : SharePeriods B A K :=
  ⟨h.blockSide_eq.symm, h.blockSide_eq ▸ h.blockSide_odd, h.extent_pos_right, h.extent_pos_left,
    h.le_top_right, h.le_top_left, fun k hk i => (h.period_eq k hk i).symm⟩
private theorem transferField_transferField {A B : BlockFrame} {K : ℕ} (h : SharePeriods A B K)
    (W : A.GaugeField K) : transferField A (transferField B W) = W := by
  funext x i
  simp only [transferField]
  rw [transferSite_transferSite (fun i => h.period_eq K le_rfl i)]
private theorem isTruncatedMinimizer_transfer (hA : MinimalActionTransfer) {A B : BlockFrame} {K : ℕ} {a : ℝ}
    (ha : a ≠ 0) (h : SharePeriods A B K) {W : A.GaugeField K} {X : A.FieldChain}
    (hX : IsTruncatedMinimizer a A K W X) :
    IsTruncatedMinimizer a B K (transferField B W) (transferChain B X) := by
  refine ⟨by show transferField B (X K) = _; rw [hX.1], fun X' hX' => ?_⟩
  rw [← truncatedAction_transferChain hA ha h X, truncatedAction_transferChain hA ha h.symm X']
  refine hX.2 _ ?_
  show transferField A (X' K) = W
  rw [hX', transferField_transferField h]
private theorem continuous_expUnit : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
private theorem continuous_leftTranslate_apply {k n : ℕ} (c : Fin n → F.Site k × Fin 4)
    (X : Fin n → imaginaryQuaternions) (W : F.GaugeField k) (x : F.Site k) (i : Fin 4) :
    Continuous fun τ : Fin n → ℝ => leftTranslate (bondSpread c X τ) W x i := by
  unfold leftTranslate bondSpread
  refine Continuous.mul (continuous_expUnit.comp ?_) continuous_const
  refine continuous_finsetSum _ fun l _ => ?_
  by_cases h : c l = (x, i)
  · simp only [if_pos h]
    exact (continuous_apply l).smul continuous_const
  · simp only [if_neg h]
    exact continuous_const
abbrev _root_.YangMills.SharedProofs.p21885 := @continuous_leftTranslate_apply
private theorem continuous_pathHolonomy_leftTranslate {k n : ℕ} (c : Fin n → F.Site k × Fin 4)
    (X : Fin n → imaginaryQuaternions) (W : F.GaugeField k) :
    ∀ (p : List PathStep) (x : F.Site k),
      Continuous fun τ : Fin n → ℝ => pathHolonomy (leftTranslate (bondSpread c X τ) W) x p
  | [], _ => continuous_const
  | st :: r, x => by
    simp only [pathHolonomy]
    refine Continuous.mul ?_ (continuous_pathHolonomy_leftTranslate c X W r _)
    unfold linkValue
    by_cases h : st.2 = true
    · simp only [h, if_true]
      exact continuous_leftTranslate_apply c X W _ _
    · simp only [h, Bool.false_eq_true, if_false]
      exact (continuous_leftTranslate_apply c X W _ _).inv
private theorem leftTranslate_bondSpread_zero {k n : ℕ} (c : Fin n → F.Site k × Fin 4)
    (X : Fin n → imaginaryQuaternions) (W : F.GaugeField k) :
    leftTranslate (bondSpread c X 0) W = W := by
  funext x i
  have h0 : bondSpread c X (0 : Fin n → ℝ) x i = 0 := by
    unfold bondSpread
    refine Finset.sum_eq_zero fun l _ => ?_
    simp
  have he : expUnit 0 = 1 := by
    apply Subtype.ext
    simp [expUnit]
  simp only [leftTranslate, h0, he, one_mul]
abbrev _root_.YangMills.SharedProofs.p1939 := @leftTranslate_bondSpread_zero
private theorem eventually_isSmallCurvature {k n : ℕ} [Finite (F.Site k)] {s : ℝ} {W : F.GaugeField k}
    (hW : IsSmallCurvature s W) (c : Fin n → F.Site k × Fin 4) (X : Fin n → imaginaryQuaternions) :
    ∀ᶠ τ in nhds (0 : Fin n → ℝ), IsSmallCurvature s (leftTranslate (bondSpread c X τ) W) := by
  unfold IsSmallCurvature
  rw [Filter.eventually_all]
  intro p
  by_cases hp : p.2.1 < p.2.2
  · have hc : Continuous fun τ : Fin n → ℝ => plaquetteDefect (leftTranslate (bondSpread c X τ) W) p := by
      unfold plaquetteDefect plaquetteHolonomy
      exact ((continuous_subtype_val.comp (continuous_pathHolonomy_leftTranslate c X W _ _)).sub
        continuous_const).norm
    have h0 : plaquetteDefect (leftTranslate (bondSpread c X 0) W) p < s := by
      rw [leftTranslate_bondSpread_zero]
      exact hW p hp
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds h0)] with τ hτ _
    exact hτ
  · exact Filter.Eventually.of_forall fun τ h => absurd h hp
private theorem bondDeriv_transfer {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k n : ℕ}
    (hp : ∀ i, F.period k i = G.period k i) {Φ : F.GaugeField k → E} {Ψ : G.GaugeField k → E}
    {W : F.GaugeField k} (c : Fin n → F.Site k × Fin 4) (X : Fin n → imaginaryQuaternions)
    (h : ∀ᶠ τ in nhds (0 : Fin n → ℝ),
      Φ (leftTranslate (bondSpread c X τ) W) = Ψ (transferField G (leftTranslate (bondSpread c X τ) W))) :
    bondDeriv Φ W c X = bondDeriv Ψ (transferField G W) (fun l => (transferSite G (c l).1, (c l).2)) X := by
  unfold bondDeriv
  have e : (fun τ : Fin n → ℝ => Φ (leftTranslate (bondSpread c X τ) W)) =ᶠ[nhds 0]
      fun τ => Ψ (leftTranslate (bondSpread (fun l => (transferSite G (c l).1, (c l).2)) X τ)
        (transferField G W)) := by
    filter_upwards [h] with τ hτ
    rw [hτ, transferField_leftTranslate hp]
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ e n).self_of_nhds]
private theorem analyticAt_of_transfer {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k n : ℕ}
    (hp : ∀ i, F.period k i = G.period k i) {Φ : F.GaugeField k → E} {Ψ : G.GaugeField k → E}
    {W : F.GaugeField k} (c : Fin n → F.Site k × Fin 4) (X : Fin n → imaginaryQuaternions)
    (h : ∀ᶠ τ in nhds (0 : Fin n → ℝ),
      Φ (leftTranslate (bondSpread c X τ) W) = Ψ (transferField G (leftTranslate (bondSpread c X τ) W)))
    (ha : AnalyticAt ℝ (fun τ : Fin n → ℝ =>
      Ψ (leftTranslate (bondSpread (fun l => (transferSite G (c l).1, (c l).2)) X τ) (transferField G W))) 0) :
    AnalyticAt ℝ (fun τ : Fin n → ℝ => Φ (leftTranslate (bondSpread c X τ) W)) 0 := by
  refine ha.congr ?_
  filter_upwards [h] with τ hτ
  rw [hτ, transferField_leftTranslate hp]
private theorem transferSite_unitStep {k : ℕ} (hp : ∀ i, F.period k i = G.period k i) (i : Fin 4) :
    transferSite G (unitStep k i : F.Site k) = (unitStep k i : G.Site k) := by apply _root_.YangMills.Construction.FrameTorusAction.transferSite_unitStep <;> assumption
private theorem transferSite_injective {k : ℕ} (hp : ∀ i, F.period k i = G.period k i) :
    Function.Injective (transferSite (F := F) G (k := k)) := fun x y e => by
  rw [← transferSite_transferSite hp x, e, transferSite_transferSite hp]
private theorem plaquetteCorners_transfer {k : ℕ} (hp : ∀ i, F.period k i = G.period k i)
    (p : F.Site k × Fin 4 × Fin 4) :
    plaquetteCorners ((transferSite G p.1, p.2) : G.Site k × Fin 4 × Fin 4) =
      (plaquetteCorners p).image (transferSite G) := by
  unfold plaquetteCorners
  simp only [Finset.image_insert, Finset.image_singleton, transferSite_add hp, transferSite_unitStep hp]
private theorem mem_innerBonds_finiteCells {H : BlockFrame} (hodd : Odd H.blockSide) (hs : ∀ i, 0 < H.extent i)
    {k : ℕ} (hk : k ≤ H.top) (b : H.Site k × Fin 4) : b ∈ innerBonds (finiteCells H) k := by
  unfold innerBonds
  rw [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨mem_allSites hodd hs hk _, Finset.mem_univ _⟩, mem_allSites hodd hs hk _⟩
private theorem mem_innerPlaquettes_finiteCells {H : BlockFrame} (hodd : Odd H.blockSide)
    (hs : ∀ i, 0 < H.extent i) {k : ℕ} (hk : k ≤ H.top) (p : H.Site k × Fin 4 × Fin 4) :
    p ∈ innerPlaquettes (finiteCells H) k ↔ p.2.1 < p.2.2 := by
  unfold innerPlaquettes
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
  constructor
  · exact fun h => h.2.1
  · intro h
    exact ⟨⟨mem_allSites hodd hs hk _, Finset.mem_univ _, Finset.mem_univ _⟩, h,
      fun x _ => mem_allSites hodd hs hk x⟩
private theorem sum_innerPlaquettes_transfer {A B : BlockFrame} {K k : ℕ} (h : SharePeriods A B K) (hk : k ≤ K)
    (g : B.Site k × Fin 4 × Fin 4 → ℝ) :
    ∑ p ∈ innerPlaquettes (finiteCells B) k, g p =
      ∑ p ∈ innerPlaquettes (finiteCells A) k, g (transferSite B p.1, p.2) := by
  have hB : Odd B.blockSide := h.blockSide_eq ▸ h.blockSide_odd
  have hp := h.period_eq k hk
  symm
  refine Finset.sum_bij' (fun p _ => (transferSite B p.1, p.2)) (fun p _ => (transferSite A p.1, p.2))
    ?_ ?_ ?_ ?_ ?_
  · intro p hq
    rw [mem_innerPlaquettes_finiteCells hB h.extent_pos_right (hk.trans h.le_top_right)]
    exact (mem_innerPlaquettes_finiteCells h.blockSide_odd h.extent_pos_left (hk.trans h.le_top_left) p).1 hq
  · intro p hq
    rw [mem_innerPlaquettes_finiteCells h.blockSide_odd h.extent_pos_left (hk.trans h.le_top_left)]
    exact (mem_innerPlaquettes_finiteCells hB h.extent_pos_right (hk.trans h.le_top_right) p).1 hq
  · intro p _
    exact Prod.ext (transferSite_transferSite hp _) rfl
  · intro p _
    exact Prod.ext (transferSite_transferSite (fun i => (hp i).symm) _) rfl
  · intro p _
    rfl
private theorem sum_innerBonds_transfer {A B : BlockFrame} {K k : ℕ} (h : SharePeriods A B K) (hk : k ≤ K)
    (g : B.Site k × Fin 4 → ℝ) :
    ∑ b ∈ innerBonds (finiteCells B) k, g b =
      ∑ b ∈ innerBonds (finiteCells A) k, g (transferSite B b.1, b.2) := by
  have hB : Odd B.blockSide := h.blockSide_eq ▸ h.blockSide_odd
  have hp := h.period_eq k hk
  symm
  refine Finset.sum_bij' (fun p _ => (transferSite B p.1, p.2)) (fun p _ => (transferSite A p.1, p.2))
    ?_ ?_ ?_ ?_ ?_
  · intro p _
    exact mem_innerBonds_finiteCells hB h.extent_pos_right (hk.trans h.le_top_right) _
  · intro p _
    exact mem_innerBonds_finiteCells h.blockSide_odd h.extent_pos_left (hk.trans h.le_top_left) _
  · intro p _
    exact Prod.ext (transferSite_transferSite hp _) rfl
  · intro p _
    exact Prod.ext (transferSite_transferSite (fun i => (hp i).symm) _) rfl
  · intro p _
    rfl
private abbrev coarseFrame (L j : ℕ) (side : Fin 4 → ℕ) : BlockFrame := ⟨L, j + 1, side⟩
private abbrev refinedFrame (L j : ℕ) (side : Fin 4 → ℕ) : BlockFrame := ⟨L, j, fun i => side i * L⟩
variable {L j : ℕ} {side : Fin 4 → ℕ}
private theorem period_coarse_eq_refined :
    ∀ k, k ≤ j + 1 → ∀ i, (coarseFrame L j side).period k i = (refinedFrame L j side).period k i := by apply _root_.YangMills.DeltaSharedProofs.p501881 <;> assumption
private theorem sharePeriods_coarse_refined (hL : Odd L) (hs : ∀ i, 0 < side i) :
    SharePeriods (coarseFrame L j side) (refinedFrame L j side) (j + 1) :=
  ⟨rfl, hL, hs, fun i => Nat.mul_pos (hs i) hL.pos, Nat.le_succ _, le_rfl, period_coarse_eq_refined⟩
private theorem enclosingCell_transferSite {l : ℕ} (hl : l ≤ j + 1) (x : (coarseFrame L j side).Site l) :
    enclosingCell (transferSite (refinedFrame L j side) x) =
      transferSite (refinedFrame L j side) (ancestorSite (F := coarseFrame L j side) (j + 1) x) := by
  unfold enclosingCell ancestorSite
  rw [transferSite_siteOfCoords (period_coarse_eq_refined _ le_rfl),
    siteCoords_transferSite (period_coarse_eq_refined l hl)]
private theorem enclosingCell_transferSite_eq_iff {l : ℕ} (hl : l ≤ j + 1) (x : (coarseFrame L j side).Site l)
    (y : (coarseFrame L j side).Site (j + 1)) :
    enclosingCell (transferSite (refinedFrame L j side) x) = transferSite (refinedFrame L j side) y ↔
      ancestorSite (F := coarseFrame L j side) (j + 1) x = y := by
  rw [enclosingCell_transferSite hl]
  exact (transferSite_injective (period_coarse_eq_refined _ le_rfl)).eq_iff
private theorem plaquetteHolonomy_transfer (hA : MinimalActionTransfer) {A B : BlockFrame} {K k : ℕ} (a : ℝ)
    (h : SharePeriods A B K) (hk : k ≤ K) (U : A.GaugeField k) (p : A.Site k × Fin 4 × Fin 4) :
    plaquetteHolonomy (transferField B U) (transferSite B p.1, p.2) = plaquetteHolonomy U p := by apply _root_.YangMills.SharedProofs.p90208 <;> assumption
private theorem blockFit_transfer (hA : MinimalActionTransfer) {A B : BlockFrame} {K k : ℕ} (a : ℝ)
    (h : SharePeriods A B K) (hk : k < K) (U : A.GaugeField k) (V : A.GaugeField (k + 1))
    (b : A.Site (k + 1) × Fin 4) :
    blockFit (transferField B U) (transferField B V) (transferSite B b.1, b.2) = blockFit U V b := by
  obtain ⟨x, i⟩ := b
  have e := (hA A B K a h).2.2.1 k U (siteCoords x) i hk
  rw [siteOfCoords_siteCoords] at e
  unfold blockFit
  dsimp only
  have e' : _root_.YangMills.Construction.BlockAverages.contourAverage (transferField B U) (transferSite B x, i) = _root_.YangMills.Construction.BlockAverages.contourAverage U (x, i) := e
  rw [e']
  have e2 : transferField B V (transferSite B x) i = V x i := by
    simp only [transferField]
    rw [transferSite_transferSite (h.period_eq (k + 1) hk)]
  rw [e2]
private theorem cellShare_transferChain (hA : MinimalActionTransfer) (a : ℝ)
    (h : SharePeriods (coarseFrame L j side) (refinedFrame L j side) (j + 1))
    (y : (coarseFrame L j side).Site (j + 1)) (X : (coarseFrame L j side).FieldChain) :
    cellShare a (finiteCells (refinedFrame L j side)) (transferSite (refinedFrame L j side) y)
        (transferChain (refinedFrame L j side) X) =
      chainSiteShare a (finiteCells (coarseFrame L j side)) y X := by
  unfold cellShare chainSiteShare
  congr 1
  · rw [sum_innerPlaquettes_transfer h (Nat.zero_le _)]
    refine Finset.sum_congr rfl fun p _ => ?_
    dsimp only
    rw [plaquetteCorners_transfer (h.period_eq 0 (Nat.zero_le _)),
      Finset.sum_image fun u _ v _ e => transferSite_injective (h.period_eq 0 (Nat.zero_le _)) e]
    have e1 : plaquetteHolonomy (transferChain (refinedFrame L j side) X 0)
        (transferSite (refinedFrame L j side) p.1, p.2) = plaquetteHolonomy (X 0) p :=
      plaquetteHolonomy_transfer hA a h (Nat.zero_le _) (X 0) p
    rw [e1]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : ancestorSite (F := coarseFrame L j side) (j + 1) x = y
    · rw [if_pos hx, if_pos ((enclosingCell_transferSite_eq_iff (Nat.zero_le _) x y).2 hx)]
    · rw [if_neg hx, if_neg fun e => hx ((enclosingCell_transferSite_eq_iff (Nat.zero_le _) x y).1 e)]
  · congr 1
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l < j + 1 := Finset.mem_range.1 hl
    rw [sum_innerBonds_transfer h hl']
    refine Finset.sum_congr rfl fun b _ => ?_
    dsimp only
    have e1 : blockFit (transferChain (refinedFrame L j side) X l) (transferChain (refinedFrame L j side) X (l + 1))
        (transferSite (refinedFrame L j side) b.1, b.2) = blockFit (X l) (X (l + 1)) b :=
      blockFit_transfer hA a h hl' (X l) (X (l + 1)) b
    rw [e1]
    congr 1
    have hp := h.period_eq (l + 1) hl'
    congr 1
    · by_cases hx : ancestorSite (F := coarseFrame L j side) (j + 1) b.1 = y
      · rw [if_pos hx, if_pos ((enclosingCell_transferSite_eq_iff hl' b.1 y).2 hx)]
      · rw [if_neg hx, if_neg fun e => hx ((enclosingCell_transferSite_eq_iff hl' b.1 y).1 e)]
    · have e2 : transferSite (refinedFrame L j side) b.1 + unitStep (l + 1) b.2 =
          transferSite (refinedFrame L j side) (b.1 + unitStep (l + 1) b.2) := by
        rw [transferSite_add hp, transferSite_unitStep hp]
      rw [e2]
      by_cases hx : ancestorSite (F := coarseFrame L j side) (j + 1) (b.1 + unitStep (l + 1) b.2) = y
      · rw [if_pos hx, if_pos ((enclosingCell_transferSite_eq_iff hl' _ y).2 hx)]
      · rw [if_neg hx, if_neg fun e => hx ((enclosingCell_transferSite_eq_iff hl' _ y).1 e)]
private theorem minimalSiteShare_eq_transfer (hA : MinimalActionTransfer) {a : ℝ} (ha : a ≠ 0)
    (h : SharePeriods (coarseFrame L j side) (refinedFrame L j side) (j + 1))
    (W : (coarseFrame L j side).GaugeField (j + 1))
    (hsh : ∀ X, IsMinimalChain a (finiteCells (refinedFrame L j side)) (transferField (refinedFrame L j side) W) X →
      ∀ Y, cellShare a (finiteCells (refinedFrame L j side)) Y X =
        minimalCellShare a (finiteCells (refinedFrame L j side)) Y (transferField (refinedFrame L j side) W))
    (y : (coarseFrame L j side).Site (j + 1)) :
    minimalSiteShare a y W =
      minimalCellShare a (finiteCells (refinedFrame L j side)) (transferSite (refinedFrame L j side) y)
        (transferField (refinedFrame L j side) W) := by
  by_cases hex : ∃ X, IsMinimizingChainBelow a (finiteCells (coarseFrame L j side)) W X
  · have hm : IsTruncatedMinimizer a (coarseFrame L j side) (j + 1) W hex.choose :=
      ⟨hex.choose_spec.1, fun X' e => hex.choose_spec.2 X' e⟩
    have hm' := isTruncatedMinimizer_transfer hA ha h hm
    have e := hsh (transferChain (refinedFrame L j side) hex.choose) ⟨hm'.1, fun X' e => hm'.2 X' e⟩
      (transferSite (refinedFrame L j side) y)
    rw [← e, cellShare_transferChain hA a h]
    unfold minimalSiteShare
    rw [dif_pos hex]
  · have hn : ¬ ∃ X, IsMinimalChain a (finiteCells (refinedFrame L j side))
        (transferField (refinedFrame L j side) W) X := by
      rintro ⟨X, hX⟩
      have hm : IsTruncatedMinimizer a (refinedFrame L j side) (j + 1) (transferField (refinedFrame L j side) W) X :=
        ⟨hX.1, fun X' e => hX.2 X' e⟩
      have hm' := isTruncatedMinimizer_transfer hA ha h.symm hm
      rw [transferField_transferField h] at hm'
      exact hex ⟨_, hm'.1, fun X' e => hm'.2 X' e⟩
    unfold minimalSiteShare minimalCellShare
    rw [dif_neg hex, dif_neg hn]
private theorem finite_site_coarse (hL : Odd L) (hs : ∀ i, 0 < side i) {k : ℕ} :
    Finite ((coarseFrame L j side).Site k) := by
  have : ∀ i, Finite (ZMod ((coarseFrame L j side).period k i)) := fun i => by
    have : NeZero ((coarseFrame L j side).period k i) := ⟨(period_pos hL.pos hs k i).ne'⟩
    exact inferInstance
  exact Pi.finite
private theorem isSmallCurvature_transfer (hA : MinimalActionTransfer) {A B : BlockFrame} {K : ℕ} (a : ℝ)
    (h : SharePeriods A B K) {s : ℝ} {W : A.GaugeField K} (hW : IsSmallCurvature s W) :
    IsSmallCurvature s (transferField B W) := by apply _root_.YangMills.SharedProofs.p56584 <;> assumption
private theorem isBlockTorus_refined {L' : ℕ} (hT : IsBlockTorus L' (coarseFrame L j side)) (hL : 0 < L) :
    IsBlockTorus L' (refinedFrame L j side) := by
  obtain ⟨hb, n, hn, hside⟩ := hT
  refine ⟨hb, n * L, ?_, fun i => ?_⟩
  · nlinarith
  · show side i * L = n * L
    rw [show side i = n from hside i]
private theorem extent_pos_of_isBlockTorus {L' : ℕ} (hT : IsBlockTorus L' (coarseFrame L j side)) :
    ∀ i, 0 < side i := by
  obtain ⟨_, n, hn, hside⟩ := hT
  intro i
  have : side i = n := hside i
  omega
private theorem transfer_bondsAt {k n : ℕ} (hp : ∀ i, F.period k i = G.period k i) (y : F.Site k)
    (h : Fin n → (Fin 4 → ℤ) × Fin 4) :
    (fun l => (transferSite G ((bondsAt y h) l).1, ((bondsAt y h) l).2)) = bondsAt (transferSite G y) h := by
  funext l
  simp only [bondsAt]
  rw [transferSite_add hp, transferSite_siteOfCoords hp]
private theorem bondListDiameter_transfer {k n : ℕ} (hp : ∀ i, F.period k i = G.period k i)
    (c : Fin n → F.Site k × Fin 4) :
    ColdStepAtMirrorFrames.bondListDiameter
        (fun l => ((transferSite G (c l).1, (c l).2) : G.Site k × Fin 4)) =
      ColdStepAtMirrorFrames.bondListDiameter c := by
  unfold ColdStepAtMirrorFrames.bondListDiameter
  simp only [siteSupDist_transferSite hp]
private theorem bondListDist_transfer {k n : ℕ} (hp : ∀ i, F.period k i = G.period k i) (y : F.Site k)
    (c : Fin n → F.Site k × Fin 4) :
    bondListDist (transferSite G y) (fun l => ((transferSite G (c l).1, (c l).2) : G.Site k × Fin 4)) =
      bondListDist y c := by
  unfold bondListDist
  simp only [siteSupDist_transferSite hp]
private theorem siteSupDist_comm {k : ℕ} (x y : F.Site k) : siteSupDist x y = siteSupDist y x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.siteSupDist_comm <;> assumption
private theorem plaquetteHolonomy_eq_product {k : ℕ} (U : F.GaugeField k) (x : F.Site k) (μ ν : Fin 4) :
    plaquetteHolonomy U (x, μ, ν) =
      U x μ * (U (x + unitStep k μ) ν * ((U (x + unitStep k ν) μ)⁻¹ * ((U x ν)⁻¹ * 1))) := by
  have e1 : x + unitStep k μ + unitStep k ν - unitStep k μ = x + unitStep k ν := by abel
  have e2 : x + unitStep k μ + unitStep k ν + -unitStep k μ - unitStep k ν = x := by abel
  simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
    if_false, e1, e2]
abbrev _root_.YangMills.SharedProofs.p41793 := @plaquetteHolonomy_eq_product
private theorem plaquetteDefect_gaugeTransform {k : ℕ} (γ : F.Site k → UnitQuaternion) (U : F.GaugeField k)
    (p : F.Site k × Fin 4 × Fin 4) : plaquetteDefect (gaugeTransform γ U) p = plaquetteDefect U p := by apply _root_.YangMills.Construction.GaugeFixing.plaquetteDefect_gaugeTransform <;> assumption
private theorem plaquetteDefect_translateField {k : ℕ} (h : F.Site k) (U : F.GaugeField k)
    (p : F.Site k × Fin 4 × Fin 4) : plaquetteDefect (translateField h U) p = plaquetteDefect U (p.1 - h, p.2) := by
  obtain ⟨x, μ, ν⟩ := p
  unfold plaquetteDefect
  rw [show (x - h, (μ, ν)) = ((x - h, μ, ν) : F.Site k × Fin 4 × Fin 4) from rfl,
    plaquetteHolonomy_eq_product, plaquetteHolonomy_eq_product]
  simp only [translateField, add_sub_right_comm]
private theorem transferField_gaugeTransform {k : ℕ} (hp : ∀ i, F.period k i = G.period k i)
    (γ : F.Site k → UnitQuaternion) (U : F.GaugeField k) :
    transferField G (gaugeTransform γ U) =
      gaugeTransform (fun x => γ (transferSite F x)) (transferField G U) := by
  funext x i
  simp only [transferField, gaugeTransform]
  rw [transferSite_add (fun i => (hp i).symm), transferSite_unitStep (fun i => (hp i).symm)]
private theorem bondDeriv_one_sum {A : BlockFrame} {k : ℕ} {ι : Type} (S : Finset ι) (f : ι → A.GaugeField k → ℝ)
    (W : A.GaugeField k) (c : Fin 1 → A.Site k × Fin 4) (X : Fin 1 → imaginaryQuaternions)
    (h : ∀ i ∈ S, AnalyticAt ℝ (fun τ : Fin 1 → ℝ => f i (leftTranslate (bondSpread c X τ) W)) 0) :
    bondDeriv (fun V => ∑ i ∈ S, f i V) W c X = ∑ i ∈ S, bondDeriv (f i) W c X := by
  unfold bondDeriv
  simp only [iteratedFDeriv_one_apply]
  rw [fderiv_fun_sum fun i hi => (h i hi).differentiableAt]
  simp
private theorem coldEstimatesBelow_coarse (hA : MinimalActionTransfer) (hS : sumCellSharesEqAction) {a : ℝ}
    {L' : ℕ} {c : ColdChainParameters} (ha : 1 ≤ a) (hL : Odd L') (hc : c.Admissible a L') {B : ℝ}
    (hB : ∀ (F : BlockFrame) (j : ℕ) (y : F.Site j) (A : Finset (F.Site j)),
      ∑ z ∈ A, Real.exp (-(c.δ₁ * siteSupDist y z)) ≤ B) {N : ℕ → ℝ}
    (hN : ∀ k, c.N k ≤ N k) (hN1 : c.N 1 * B ≤ N 1) (hN2 : c.N 1 * B * c.σA ≤ N 1) {s : ℝ}
    {W : (coarseFrame L j side).GaugeField (j + 1)} (hT : IsBlockTorus L' (coarseFrame L j side)) (hs : 0 < s)
    (hsσ : s ≤ c.σA) (hW : IsSmallCurvature s W) : ColdEstimatesBelow a c.δ₁ s N W := by
  have hLL : L = L' := hT.1
  subst hLL
  have ha0 : a ≠ 0 := by linarith
  have ha' : 0 ≤ a := by linarith
  have hside := extent_pos_of_isBlockTorus hT
  have h := sharePeriods_coarse_refined (j := j) hL hside
  have hF := finite_site_coarse (j := j) hL hside (k := j + 1)
  have hTG := isBlockTorus_refined hT hL.pos
  have hp := period_coarse_eq_refined (L := L) (j := j) (side := side) (j + 1) le_rfl
  have hact := fun (V : (coarseFrame L j side).GaugeField (j + 1)) => (hA _ _ (j + 1) a h).1 (j + 1) V le_rfl
  have hcl : ∀ (V : (coarseFrame L j side).GaugeField (j + 1)), IsSmallCurvature s V →
      c.EstimatesAt a s (transferField (refinedFrame L j side) V) := fun V hV =>
    hc.estimates (refinedFrame L j side) s _ hTG hs hsσ (isSmallCurvature_transfer hA a h hV)
  have hshare : ∀ (V : (coarseFrame L j side).GaugeField (j + 1)), IsSmallCurvature s V →
      ∀ y, minimalSiteShare a y V = minimalCellShare a (finiteCells (refinedFrame L j side))
        (transferSite (refinedFrame L j side) y) (transferField (refinedFrame L j side) V) := fun V hV y =>
    minimalSiteShare_eq_transfer hA ha0 h V (hcl V hV).cellShares.2.2.1 y
  have hev : ∀ {n : ℕ} (c' : Fin n → (coarseFrame L j side).Site (j + 1) × Fin 4) (X : Fin n → imaginaryQuaternions)
      (y : (coarseFrame L j side).Site (j + 1)), ∀ᶠ τ in nhds (0 : Fin n → ℝ),
      minimalSiteShare a y (leftTranslate (bondSpread c' X τ) W) =
        minimalCellShare a (finiteCells (refinedFrame L j side)) (transferSite (refinedFrame L j side) y)
          (transferField (refinedFrame L j side) (leftTranslate (bondSpread c' X τ) W)) := fun c' X y => by
    filter_upwards [eventually_isSmallCurvature hW c' X] with τ hτ
    exact hshare _ hτ y
  have hevA : ∀ {n : ℕ} (c' : Fin n → (coarseFrame L j side).Site (j + 1) × Fin 4) (X : Fin n → imaginaryQuaternions),
      ∀ᶠ τ in nhds (0 : Fin n → ℝ),
      minimalAction a (finiteCells (coarseFrame L j side)) (j + 1) (leftTranslate (bondSpread c' X τ) W) =
        minimalAction a (finiteCells (refinedFrame L j side)) (j + 1)
          (transferField (refinedFrame L j side) (leftTranslate (bondSpread c' X τ) W)) := fun c' X =>
    Filter.Eventually.of_forall fun τ => hact _
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := (hcl W hW).cellShares
  have hexp : ∀ x : ℝ, 0 ≤ Real.exp x := fun x => (Real.exp_pos x).le
  have hslope : ∀ (c' : Fin 1 → (coarseFrame L j side).Site (j + 1) × Fin 4) (X : Fin 1 → imaginaryQuaternions),
      AreUnitVectors X →
      |bondDeriv (minimalAction a (finiteCells (coarseFrame L j side)) (j + 1)) W c' X| ≤ c.N 1 * B * s := by
    intro c' X hX
    have e0 := bondDeriv_transfer (G := refinedFrame L j side) hp c' X (hevA c' X)
    rw [e0]
    set c'' : Fin 1 → (refinedFrame L j side).Site (j + 1) × Fin 4 :=
      fun l => (transferSite (refinedFrame L j side) (c' l).1, (c' l).2) with hc''
    have hsum : (minimalAction a (finiteCells (refinedFrame L j side)) (j + 1)) =
        fun V => ∑ Y ∈ finiteCells (refinedFrame L j side), minimalCellShare a (finiteCells (refinedFrame L j side)) Y V := by
      funext V
      have hside2 : ∀ i, 2 ≤ (refinedFrame L j side).extent i := by
        obtain ⟨_, n, hn, hsd⟩ := hTG
        intro i
        rw [hsd i]
        omega
      exact ((hS (refinedFrame L j side) a (fun _ _ => 0) V ha' hL hside2).1).symm
    rw [hsum, bondDeriv_one_sum _ _ _ _ _ fun Y _ => h2 Y 1 c'' X]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ Y ∈ finiteCells (refinedFrame L j side),
        |bondDeriv (minimalCellShare a (finiteCells (refinedFrame L j side)) Y)
            (transferField (refinedFrame L j side) W) c'' X| ≤
          c.N 1 * s * Real.exp (-(c.δ₁ * siteSupDist (c'' 0).1 Y)) := by
      intro Y _
      have e9 := h9 Y c'' X hX
      have e : BlockAverages.bondListDistance Y c'' = siteSupDist (c'' 0).1 Y := by
        unfold BlockAverages.bondListDistance
        rw [siteSupDist_comm]
        simp
        rfl
      rw [e, neg_mul] at e9
      exact e9
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum]
    have hBs := hB (refinedFrame L j side) (j + 1) (c'' 0).1 (finiteCells (refinedFrame L j side))
    have hN0 : 0 ≤ c.N 1 * s := mul_nonneg (hc.positivity.2.2.2.2.2.1 1).le hs.le
    calc c.N 1 * s * _ ≤ c.N 1 * s * B := mul_le_mul_of_nonneg_left hBs hN0
      _ = c.N 1 * B * s := by ring
  have hB0 : 0 ≤ B := by simpa using hB (refinedFrame L j side) 0 0 ∅
  have hNB : 0 ≤ c.N 1 * B := mul_nonneg (hc.positivity.2.2.2.2.2.1 1).le hB0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k c' X
    exact analyticAt_of_transfer hp c' X (hevA c' X)
      (h1 k (fun l => (transferSite (refinedFrame L j side) (c' l).1, (c' l).2)) X)
  · intro y k c' X
    exact analyticAt_of_transfer hp c' X (hev c' X y)
      (h2 _ k (fun l => (transferSite (refinedFrame L j side) (c' l).1, (c' l).2)) X)
  · intro X hX y
    have hm : IsTruncatedMinimizer a (coarseFrame L j side) (j + 1) W X := ⟨hX.1, fun X' e => hX.2 X' e⟩
    have hm' := isTruncatedMinimizer_transfer hA ha0 h hm
    have e := h3 (transferChain (refinedFrame L j side) X) ⟨hm'.1, fun X' e => hm'.2 X' e⟩
      (transferSite (refinedFrame L j side) y)
    rw [hshare W hW, ← e, cellShare_transferChain hA a h]
  · intro k c' X hk hX
    rw [bondDeriv_transfer hp c' X (hevA c' X)]
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1 : k = 1 := by omega
      subst hk1
      have e1 := hslope c' X hX
      rw [bondDeriv_transfer hp c' X (hevA c' X)] at e1
      have hdiam : ColdStepAtMirrorFrames.bondListDiameter c' = 0 := by
        unfold ColdStepAtMirrorFrames.bondListDiameter siteSupDist
        simp
      rw [hdiam]
      simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
      exact e1.trans ((mul_le_mul_of_nonneg_left hsσ hNB).trans hN2)
    · have e6 := h6 k (fun l => (transferSite (refinedFrame L j side) (c' l).1, (c' l).2)) X hk2 hX
      have ed : BlockAverages.bondListDiameter (fun l => ((transferSite (refinedFrame L j side) (c' l).1, (c' l).2) :
          (refinedFrame L j side).Site (j + 1) × Fin 4)) = ColdStepAtMirrorFrames.bondListDiameter c' :=
        bondListDiameter_transfer hp c'
      rw [ed] at e6
      exact e6.trans (mul_le_mul_of_nonneg_right (hN k) (hexp _))
  · intro c' X hX
    exact (hslope c' X hX).trans (mul_le_mul_of_nonneg_right hN1 hs.le)
  · intro y k c' X hk hX
    rw [bondDeriv_transfer hp c' X (hev c' X y)]
    have e7 := h7 (transferSite (refinedFrame L j side) y) k
      (fun l => (transferSite (refinedFrame L j side) (c' l).1, (c' l).2)) X hk hX
    have ed : BlockAverages.bondListDistance (transferSite (refinedFrame L j side) y)
        (fun l => ((transferSite (refinedFrame L j side) (c' l).1, (c' l).2) :
          (refinedFrame L j side).Site (j + 1) × Fin 4)) = bondListDist y c' := bondListDist_transfer hp y c'
    rw [ed] at e7
    exact e7.trans (mul_le_mul_of_nonneg_right (hN k) (hexp _))
  · intro y
    rw [hshare W hW]
    obtain ⟨e0, e1⟩ := h8 (transferSite (refinedFrame L j side) y)
    exact ⟨e0, e1.trans (mul_le_mul_of_nonneg_right (hN 0) (sq_nonneg s))⟩
  · intro y c' X hX
    rw [bondDeriv_transfer hp c' X (hev c' X y)]
    have e9 := h9 (transferSite (refinedFrame L j side) y)
      (fun l => (transferSite (refinedFrame L j side) (c' l).1, (c' l).2)) X hX
    have ed : BlockAverages.bondListDistance (transferSite (refinedFrame L j side) y)
        (fun l => ((transferSite (refinedFrame L j side) (c' l).1, (c' l).2) :
          (refinedFrame L j side).Site (j + 1) × Fin 4)) = bondListDist y c' := bondListDist_transfer hp y c'
    rw [ed] at e9
    refine e9.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hN 1) hs.le) (hexp _))
  · intro y γ
    have hg : IsSmallCurvature s (gaugeTransform γ W) := fun p hq => by
      rw [plaquetteDefect_gaugeTransform]
      exact hW p hq
    rw [hshare _ hg, hshare W hW, transferField_gaugeTransform hp, h4]
  · intro y u
    have hg : IsSmallCurvature s (translateField u W) := fun p hq => by
      rw [plaquetteDefect_translateField]
      exact hW _ hq
    rw [hshare _ hg, hshare W hW]
    set g : CubicSymmetry := ⟨1, fun _ => 1, siteCoords (transferSite (refinedFrame L j side) u)⟩ with hgdef
    have hon : ∀ x : (refinedFrame L j side).Site (j + 1), g.actSite (F := refinedFrame L j side) (j + 1) x =
        x + transferSite (refinedFrame L j side) u := by
      intro x
      unfold CubicSymmetry.actSite
      have e : (fun i => g.sign i * siteCoords x (g.perm i) +
          ((refinedFrame L j side).blockSide : ℤ) ^ ((refinedFrame L j side).top - (j + 1)) * g.shift i) =
          siteCoords x + siteCoords (transferSite (refinedFrame L j side) u) := by
        funext i
        simp [hgdef]
      rw [e, siteOfCoords_add, siteOfCoords_siteCoords, siteOfCoords_siteCoords]
    have hcar : g.TransportsField (F := refinedFrame L j side) (transferField (refinedFrame L j side) W)
        (transferField (refinedFrame L j side) (translateField u W)) := by
      intro x k
      have e1 : g.actStep k = (k, true) := rfl
      rw [e1]
      show linkValue _ (g.actSite (F := refinedFrame L j side) (j + 1) x) (k, true) = _
      rw [hon]
      simp only [linkValue, if_true, transferField, translateField]
      rw [transferSite_add (fun i => (hp i).symm), transferSite_transferSite (fun i => hp i), add_sub_cancel_right]
    have hiso : g.IsSymmetry (refinedFrame L j side) := by
      obtain ⟨_, n, _, hsd⟩ := hTG
      exact ⟨fun _ => Or.inl rfl, fun i i' => by rw [hsd i, hsd i']⟩
    have hmem : ∀ z : (refinedFrame L j side).Cell, z ∈ finiteCells (refinedFrame L j side) := fun z =>
      mem_finiteCells hL.pos (fun i => Nat.mul_pos (hside i) hL.pos) z
    have e := h5 g (finiteCells (refinedFrame L j side)) _ hiso (fun z => ⟨fun _ => hmem _, fun _ => hmem _⟩) hcar
      (transferSite (refinedFrame L j side) y)
    rw [hon] at e
    rw [transferSite_add hp]
    exact e
private theorem coldComparisonBelow_coarse (hA : MinimalActionTransfer) {a : ℝ} {L' : ℕ} {c : ColdChainParameters}
    (ha : 1 ≤ a) (hL : Odd L') (hc : c.Admissible a L') {N : ℕ → ℝ} (hN : ∀ k, c.N k ≤ N k) (hNK : c.K ≤ N 0)
    {s : ℝ} {side' : Fin 4 → ℕ} {W : (coarseFrame L j side).GaugeField (j + 1)}
    {W' : (coarseFrame L j side').GaugeField (j + 1)} {y : (coarseFrame L j side).Site (j + 1)}
    {y' : (coarseFrame L j side').Site (j + 1)} {r : ℕ}
    (hT : IsBlockTorus L' (coarseFrame L j side)) (hT' : IsBlockTorus L' (coarseFrame L j side')) (hs : 0 < s)
    (hsσ : s ≤ c.σA) (hW : IsSmallCurvature s W) (hW' : IsSmallCurvature s W') (hag : AgreeOnBox W W' y y' r) :
    ColdComparisonBelow a c.δ₁ c.δ₂ s c.s₀ N W W' y y' r := by
  have hLL : L = L' := hT.1
  subst hLL
  have ha0 : a ≠ 0 := by linarith
  have hside := extent_pos_of_isBlockTorus hT
  have hside' := extent_pos_of_isBlockTorus hT'
  have h := sharePeriods_coarse_refined (j := j) hL hside
  have h' := sharePeriods_coarse_refined (j := j) hL hside'
  have hTG := isBlockTorus_refined hT hL.pos
  have hTG' := isBlockTorus_refined hT' hL.pos
  have hp := period_coarse_eq_refined (L := L) (j := j) (side := side) (j + 1) le_rfl
  have hcW := isSmallCurvature_transfer hA a h hW
  have hcW' := isSmallCurvature_transfer hA a h' hW'
  have hper : ∀ (u : Fin 4 → ℕ) (i : Fin 4), (coarseFrame L j u).period (j + 1) i = u i * L := by
    intro u i
    show u i * L ^ (j + 1 + 1 - (j + 1)) = u i * L
    simp
  have hread : ∀ {u : Fin 4 → ℕ} (V : (coarseFrame L j u).GaugeField (j + 1)) (x : (coarseFrame L j u).Site (j + 1))
      (z : Fin 4 → ℤ) (i : Fin 4),
      transferField (refinedFrame L j u) V (transferSite (refinedFrame L j u) x + siteOfCoords (j + 1) z) i =
        V (x + siteOfCoords (j + 1) z) i := by
    intro u V x z i
    have hq := period_coarse_eq_refined (L := L) (j := j) (side := u) (j + 1) le_rfl
    have e : transferSite (refinedFrame L j u) x + siteOfCoords (j + 1) z =
        transferSite (refinedFrame L j u) (x + siteOfCoords (j + 1) z) := by
      rw [transferSite_add hq, transferSite_siteOfCoords hq]
    rw [e]
    simp only [transferField]
    rw [transferSite_transferSite hq]
  have hagree : AgreeOnBall (finiteCells (refinedFrame L j side)) (transferField (refinedFrame L j side) W)
      (finiteCells (refinedFrame L j side')) (transferField (refinedFrame L j side') W')
      (transferSite (refinedFrame L j side) y) (transferSite (refinedFrame L j side') y') r := by
    refine ⟨fun i => Or.inr ?_, fun i => Or.inr ?_, fun q _ => ?_, fun b hb => ?_⟩
    · have e := hag.1 i
      rw [show (coarseFrame L j side).period (coarseFrame L j side).depth i = side i * L from hper side i] at e
      exact e
    · have e := hag.2.1 i
      rw [show (coarseFrame L j side').period (coarseFrame L j side').depth i = side' i * L from hper side' i] at e
      exact e
    · have m1 := mem_finiteCells (F := refinedFrame L j side) hL.pos (fun i => Nat.mul_pos (hside i) hL.pos)
        (transferSite (refinedFrame L j side) y + siteOfCoords (refinedFrame L j side).top q)
      have m2 := mem_finiteCells (F := refinedFrame L j side') hL.pos (fun i => Nat.mul_pos (hside' i) hL.pos)
        (transferSite (refinedFrame L j side') y' + siteOfCoords (refinedFrame L j side').top q)
      exact ⟨fun _ => m2, fun _ => m1⟩
    · have e1 := hread W y b.1 b.2
      have e2 := hread W' y' b.1 b.2
      exact e1.trans ((hag.2.2 b hb).trans e2.symm)
  have hshare : ∀ {u : Fin 4 → ℕ} (V : (coarseFrame L j u).GaugeField (j + 1)), IsBlockTorus L (coarseFrame L j u) →
      IsSmallCurvature s V → ∀ (y₀ : (coarseFrame L j u).Site (j + 1)) (k : ℕ)
      (q : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
      bondDeriv (minimalSiteShare a y₀) V (bondsAt y₀ q) X =
        bondDeriv (minimalCellShare a (finiteCells (refinedFrame L j u)) (transferSite (refinedFrame L j u) y₀))
          (transferField (refinedFrame L j u) V) (bondsAt (transferSite (refinedFrame L j u) y₀) q) X := by
    intro u V hTu hV y₀ k q X
    have hsu := extent_pos_of_isBlockTorus hTu
    have hu := sharePeriods_coarse_refined (j := j) hL hsu
    have hFu := finite_site_coarse (j := j) hL hsu (k := j + 1)
    have hq := period_coarse_eq_refined (L := L) (j := j) (side := u) (j + 1) le_rfl
    have hTGu := isBlockTorus_refined hTu hL.pos
    rw [← transfer_bondsAt hq]
    refine bondDeriv_transfer hq _ X ?_
    filter_upwards [eventually_isSmallCurvature hV (bondsAt y₀ q) X] with τ hτ
    exact minimalSiteShare_eq_transfer hA ha0 hu _
      (hc.estimates (refinedFrame L j u) s _ hTGu hs hsσ (isSmallCurvature_transfer hA a hu hτ)).cellShares.2.2.1 y₀
  have hact : ∀ {u : Fin 4 → ℕ} (V : (coarseFrame L j u).GaugeField (j + 1)), IsBlockTorus L (coarseFrame L j u) →
      ∀ (y₀ : (coarseFrame L j u).Site (j + 1)) (b : (Fin 4 → ℤ) × Fin 4) (X : Fin 1 → imaginaryQuaternions),
      bondDeriv (minimalAction a (finiteCells (coarseFrame L j u)) (j + 1)) V (bondsAt y₀ fun _ => b) X =
        bondDeriv (minimalAction a (finiteCells (refinedFrame L j u)) (j + 1))
          (transferField (refinedFrame L j u) V) (bondsAt (transferSite (refinedFrame L j u) y₀) fun _ => b) X := by
    intro u V hTu y₀ b X
    have hsu := extent_pos_of_isBlockTorus hTu
    have hu := sharePeriods_coarse_refined (j := j) hL hsu
    have hq := period_coarse_eq_refined (L := L) (j := j) (side := u) (j + 1) le_rfl
    rw [← transfer_bondsAt hq]
    refine bondDeriv_transfer hq _ X (Filter.Eventually.of_forall fun τ => ?_)
    exact (hA _ _ (j + 1) a hu).1 (j + 1) _ le_rfl
  have hexp : ∀ x : ℝ, 0 ≤ Real.exp x := fun x => (Real.exp_pos x).le
  refine ⟨fun k q X hq hX => ?_, fun hs0 b X hb hX => ?_⟩
  · rw [hshare W hT hW, hshare W' hT' hW']
    have e := ((hc.estimates (refinedFrame L j side) s _ hTG hs hsσ hcW).locality (refinedFrame L j side') _
      (transferSite (refinedFrame L j side) y) (transferSite (refinedFrame L j side') y') r rfl rfl hTG'.2 hcW'
      hagree).1 k q X hq hX
    refine e.trans ?_
    have hf : 0 ≤ derivativeScale s k := by
      unfold derivativeScale
      split_ifs <;> positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hN k) hf) (hexp _)
  · rw [hact W hT, hact W' hT']
    have e := ((hc.classical.2 (refinedFrame L j side) s _ hTG hs hs0 hcW).2.2.2 (refinedFrame L j side') _
      (transferSite (refinedFrame L j side) y) (transferSite (refinedFrame L j side') y') r hTG' rfl hcW'
      hagree).firstDerivative b X hb hX
    have ed : cellSupDist (transferSite (refinedFrame L j side) y)
        (transferSite (refinedFrame L j side) y + siteOfCoords (refinedFrame L j side).top b.1) =
          siteSupDist y (y + siteOfCoords (j + 1) b.1) := by
      have e1 : transferSite (refinedFrame L j side) y + siteOfCoords (refinedFrame L j side).top b.1 =
          transferSite (refinedFrame L j side) (y + siteOfCoords (j + 1) b.1) := by
        rw [transferSite_add hp, transferSite_siteOfCoords hp]
      rw [e1]
      exact siteSupDist_transferSite hp _ _
    rw [ed] at e
    refine e.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNK hs.le) (hexp _)
theorem coldEstimatesAtPositiveDepth_holds (hA : MinimalActionTransfer) (hS : sumCellSharesEqAction)
    (hD : ExpDecaySumBounded) : ColdEstimatesAtPositiveDepth := by
  intro a L c ha hL _ hc
  obtain ⟨B, hB0, hB⟩ := hD c.δ₁ hc.positivity.1
  have hK : 0 < c.K := hc.classical.1.2.2.2.2.2.1
  have hNk : ∀ k, 0 < c.N k := hc.positivity.2.2.2.2.2.1
  have hσ : 0 < c.σA := hc.positivity.2.2.2.1
  have hm : 0 ≤ c.N 1 * B * (1 + c.σA) := by
    have := hNk 1
    positivity
  have hm2 : 0 ≤ c.N 1 * B * c.σA := by
    have := hNk 1
    positivity
  have hm3 : 0 ≤ c.N 1 * B := by
    have := hNk 1
    positivity
  have hN : ∀ k, c.N k ≤ c.N k + c.K + c.N 1 * B * (1 + c.σA) := fun k => by linarith
  have hN1 : c.N 1 * B ≤ c.N 1 + c.K + c.N 1 * B * (1 + c.σA) := by
    have e : c.N 1 * B * (1 + c.σA) = c.N 1 * B + c.N 1 * B * c.σA := by ring
    have := hNk 1
    linarith
  have hN2 : c.N 1 * B * c.σA ≤ c.N 1 + c.K + c.N 1 * B * (1 + c.σA) := by
    have e : c.N 1 * B * (1 + c.σA) = c.N 1 * B + c.N 1 * B * c.σA := by ring
    have := hNk 1
    linarith
  have hNK : c.K ≤ c.N 0 + c.K + c.N 1 * B * (1 + c.σA) := by
    have := hNk 0
    linarith
  refine ⟨fun k => c.N k + c.K + c.N 1 * B * (1 + c.σA), fun k => ?_, ?_, ?_⟩
  · have := hNk k
    positivity
  · intro F s W hT ht hs hsσ hW
    obtain ⟨L', t, side⟩ := F
    cases t with
    | zero => exact absurd ht (by norm_num)
    | succ j => exact coldEstimatesBelow_coarse hA hS ha hL hc hB hN hN1 hN2 hT hs hsσ hW
  · intro F F' s W W' y y' r hT hT' ht htt hs hsσ hW hW' hag
    obtain ⟨L₁, t, side⟩ := F
    obtain ⟨L₂, t', side'⟩ := F'
    have e1 : L₁ = L := hT.1
    have e2 : L₂ = L := hT'.1
    subst e1
    subst e2
    have e3 : t' = t := htt
    subst e3
    cases t' with
    | zero => exact absurd ht (by norm_num)
    | succ j => exact coldComparisonBelow_coarse hA ha hL hc hN hNK hT hT' hs hsσ hW hW' hag
end ColdStepAtMirrorFrames
end YangMills.Construction
end
