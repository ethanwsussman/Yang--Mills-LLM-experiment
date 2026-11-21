import YangMills.Construction.ClusterExpansionOfAStep.AdmissionEqualInBoxes
import YangMills.Construction.ClusterExpansionOfAStep.BlocksReadTheirBoxes
import YangMills.Construction.ClusterExpansionOfAStep.FactorOfAClassIsOneRule
import YangMills.Construction.ClusterExpansionOfAStep.FrameReadsItsBox
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace CoarseFactorLocality
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings StepCosts
  CongruentBoxes CongruentAdmission CongruentStates BlockPlaces
section Cutoff
variable {ρ : ℝ} {p : ℝ → ℝ}
theorem cutoff_nonneg_of_lt (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 ≤ u) (hu : u < ρ) : 0 ≤ p u := by
  by_cases hs : u ≤ 5 * ρ / 8
  · rw [hp.vanish_small u h0 hs]
  · have hs' : 5 * ρ / 8 < u := not_le.mp hs
    have hupos : 0 < u := by linarith
    have ha : (0 : ℝ) ≤ 1 - (5 * ρ / 8) / u := by rw [sub_nonneg, div_le_one hupos]; exact hs'.le
    have hb : (0 : ℝ) ≤ (5 * ρ / 8) / u := by positivity
    have h1 := hp.convex.2 (show (0 : ℝ) ∈ Set.Ico 0 ρ from ⟨le_rfl, hρ⟩) (show u ∈ Set.Ico 0 ρ from ⟨h0, hu⟩) ha hb
      (by ring)
    have e : (1 - (5 * ρ / 8) / u) • (0 : ℝ) + ((5 * ρ / 8) / u) • u = 5 * ρ / 8 := by
      simp only [smul_eq_mul, mul_zero, zero_add]
      field_simp
    rw [e, hp.vanish_small _ (by positivity) le_rfl, hp.vanish_small 0 le_rfl (by positivity)] at h1
    simp only [smul_eq_mul, mul_zero, zero_add] at h1
    have hc : 0 < (5 * ρ / 8) / u := by positivity
    by_contra hneg
    have : (5 * ρ / 8) / u * p u < 0 := mul_neg_of_pos_of_neg hc (not_le.mp hneg)
    linarith
theorem cutoffFactor_le_one (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 ≤ u) : cutoffFactor ρ p u ≤ 1 := by
  unfold cutoffFactor
  split_ifs with h
  · exact Real.exp_le_one_iff.mpr (by have := cutoff_nonneg_of_lt hρ hp h0 h; linarith)
  · exact zero_le_one
theorem cutoffFactor_nonneg (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by
  unfold cutoffFactor
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl
end Cutoff
section Sites
variable {n n' : ℕ} [NeZero n] [NeZero n'] {L : ℕ} [NeZero L]
theorem stepBlockFrame_period_zero (L n : ℕ) (i : Fin 4) : (stepBlockFrame L n).period 0 i = n * L := by apply _root_.YangMills.Construction.BlockOffsets.period_zero <;> assumption
theorem stepBlockFrame_period_one (L n : ℕ) (i : Fin 4) : (stepBlockFrame L n).period 1 i = n := by apply _root_.YangMills.Construction.BlockOffsets.period_one <;> assumption
theorem siteAtOffset_eq_add {F : BlockFrame} (c : F.Cell) (a b : Fin 4 → ℤ) :
    (siteAtOffset c a : F.Site F.depth) = siteAtOffset c b + siteOfCoords F.depth (a - b) := by
  unfold siteAtOffset
  rw [add_assoc, ← siteOfCoords_add]
  simp
theorem torusSiteInFrame_blockSite_eq (w : TorusSite n) (o : BlockOffset L) :
    torusSiteInFrame (stepBlockFrame L n) 0 (blockSite w o : TorusSite (n * L)) =
      siteAtOffset (torusSiteInFrame (stepBlockFrame L n) 1 w) (refinedOffset L 0 o) :=
  torusSiteInFrame_blockSite (n := n) (L := L) 0 w o
theorem toTorusSite_siteAtOffset (w : TorusSite n) (o : BlockOffset L) (u : Fin 4 → ℤ) :
    toTorusSite (n * L) (siteAtOffset (torusSiteInFrame (stepBlockFrame L n) 1 w) u : (stepBlockFrame L n).Site 0) =
      blockSite w o + siteOfInt (u - refinedOffset L 0 o) := by
  have hp := stepBlockFrame_period_zero L n
  have a1 : toTorusSite (n * L) (siteAtOffset (torusSiteInFrame (stepBlockFrame L n) 1 w) (refinedOffset L 0 o) :
      (stepBlockFrame L n).Site 0) = blockSite w o :=
    (congrArg (toTorusSite (n * L)) (torusSiteInFrame_blockSite_eq w o)).symm.trans
      (TopLevelSites.toTorusSite_torusSiteInFrame hp (blockSite w o))
  have a2 := TopLevelSites.toTorusSite_siteOfCoords (F := stepBlockFrame L n) (j := 0) hp (u - refinedOffset L 0 o)
  have a3 := TopLevelSites.toTorusSite_add (F := stepBlockFrame L n) (j := 0) hp
    (siteAtOffset (torusSiteInFrame (stepBlockFrame L n) 1 w) (refinedOffset L 0 o))
    (siteOfCoords 0 (u - refinedOffset L 0 o))
  exact (congrArg (toTorusSite (n * L)) (siteAtOffset_eq_add (F := stepBlockFrame L n) _ u (refinedOffset L 0 o))).trans
    (a3.trans (congrArg₂ (· + ·) a1 a2))
theorem mem_image_torusSiteInFrame {S : Finset (TorusSite (n * L))} {s : (stepBlockFrame L n).Site 0}
    [DecidableEq ((stepBlockFrame L n).Site 0)] :
    s ∈ S.image (torusSiteInFrame (stepBlockFrame L n) 0) ↔ toTorusSite (n * L) s ∈ S := by
  have hp := stepBlockFrame_period_zero L n
  constructor
  · intro h
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
    rw [TopLevelSites.toTorusSite_torusSiteInFrame hp]
    exact hz
  · intro h
    exact Finset.mem_image.mpr ⟨_, h, TopLevelSites.torusSiteInFrame_toTorusSite hp s⟩
theorem cellOffset_blockSite (hL : Odd L) (h2 : 2 ≤ n) (t : ℕ) (w : TorusSite n) (o : BlockOffset L) :
    cellOffset (F := torusFrame L t n)
        (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth (blockSite w o : TorusSite (n * L))) =
      refinedOffset L 0 o :=
  (congrArg (cellOffset (F := torusFrame L t n)) (torusSiteInFrame_blockSite (n := n) (L := L) t w o)).trans
    (TopLevelSites.cellOffset_centre_add (F := torusFrame L t n) hL (fun _ => h2) _ _
      (refinedOffset_mem_centredCube hL o))
theorem abs_refinedOffset_le (hL : Odd L) (o : BlockOffset L) (i : Fin 4) : |refinedOffset L 0 o i| ≤ (L : ℤ) := by
  have := (TopLevelSites.mem_centredCube_iff _).mp (refinedOffset_mem_centredCube hL o) i
  have hh : TopLevelSites.halfWidth L = ((L : ℤ) - 1) / 2 := rfl
  rw [hh] at this
  have h0 : (0 : ℤ) < L := side_pos_int
  rw [abs_le]
  constructor <;> omega
theorem abs_sub_refinedOffset_le (hL : Odd L) {u : Fin 4 → ℤ} (hu : OffsetInBox (3 * L) u) (o : BlockOffset L)
    (i : Fin 4) : |(u - refinedOffset L 0 o) i| ≤ 4 * (L : ℤ) := by
  have h1 := abs_le.mp (hu i)
  have h2 := abs_le.mp (abs_refinedOffset_le hL o i)
  push_cast at h1
  simp only [Pi.sub_apply]
  rw [abs_le]
  constructor <;> omega
theorem chartCoord_eq_of_agree (hblocks : BlockDataIsLocal) {ℓ : StepParameters} (hfit : ℓ.Admissible)
    (h16 : 16 ≤ n) (h16' : 16 ≤ n') {W : TorusField (n * ℓ.side)} {W' : TorusField (n' * ℓ.side)}
    {V : TorusField n} {V' : TorusField n'} (w : TorusSite n) (w' : TorusSite n') (o : BlockOffset ℓ.side)
    (i : Fin 4)
    (hW : ∀ (e : Fin 4 → ℤ) (k : Fin 4), (∀ j, |e j| ≤ 4 * (ℓ.side : ℤ)) →
      W (blockSite w o + siteOfInt e) k = W' (blockSite w' o + siteOfInt e) k)
    (hV : V w i = V' w' i) :
    chartCoord ℓ V W (blockSite w o, i) = chartCoord ℓ V' W' (blockSite w' o, i) := by
  have hag : ∀ (u : Fin 4 → ℤ) (k : Fin 4), OffsetInBox (3 * ℓ.side) u →
      OffsetInBox (3 * ℓ.side) (u + Pi.single k 1) →
      readAtLevel (stepBlockFrame ℓ.side n) 0 W (siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 w) u) k =
        readAtLevel (stepBlockFrame ℓ.side n') 0 W'
          (siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n') 1 w') u) k := by
    intro u k hu hu'
    have e := hW _ k (abs_sub_refinedOffset_le hfit.L_odd hu o)
    rw [← toTorusSite_siteAtOffset w o u, ← toTorusSite_siteAtOffset w' o u] at e
    exact e
  have hVr : readAtLevel (stepBlockFrame ℓ.side n) 1 V (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 w) i =
      readAtLevel (stepBlockFrame ℓ.side n') 1 V' (torusSiteInFrame (stepBlockFrame ℓ.side n') 1 w') i := by
    rw [TopLevelSites.readAtLevel_torusSiteInFrame (stepBlockFrame_period_one ℓ.side n),
      TopLevelSites.readAtLevel_torusSiteInFrame (stepBlockFrame_period_one ℓ.side n')]
    exact hV
  have key := (hblocks ℓ hfit n n' h16 h16' _ _ _ _ hag).2 _ _ _ i (refinedOffset_mem_centredCube hfit.L_odd o) hVr
  have c₁ := torusSiteInFrame_blockSite_eq (L := ℓ.side) w o
  have c₂ := torusSiteInFrame_blockSite_eq (L := ℓ.side) w' o
  exact (congrArg (fun s => bondCoordinate 1 (readAtLevel (stepBlockFrame ℓ.side n) 1 V)
      (readAtLevel (stepBlockFrame ℓ.side n) 0 W) (s, i)) c₁).trans
    (key.trans (congrArg (fun s => bondCoordinate 1 (readAtLevel (stepBlockFrame ℓ.side n') 1 V')
      (readAtLevel (stepBlockFrame ℓ.side n') 0 W') (s, i)) c₂).symm)
theorem blockBaseWeight_eq_of_agree (hblocks : BlockDataIsLocal) {ℓ : StepParameters} (hfit : ℓ.Admissible)
    (h16 : 16 ≤ n) (h16' : 16 ≤ n') {W : TorusField (n * ℓ.side)} {W' : TorusField (n' * ℓ.side)}
    {S : Finset (TorusSite (n * ℓ.side))} {S' : Finset (TorusSite (n' * ℓ.side))} (w : TorusSite n)
    (w' : TorusSite n') (o : BlockOffset ℓ.side)
    (hW : ∀ (e : Fin 4 → ℤ) (k : Fin 4), (∀ j, |e j| ≤ 4 * (ℓ.side : ℤ)) →
      W (blockSite w o + siteOfInt e) k = W' (blockSite w' o + siteOfInt e) k)
    (hS : ∀ e : Fin 4 → ℤ, (∀ j, |e j| ≤ 4 * (ℓ.side : ℤ)) →
      (blockSite w o + siteOfInt e ∈ S ↔ blockSite w' o + siteOfInt e ∈ S')) :
    blockBaseWeight ℓ (frameHotLumps ℓ S W) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 w)
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 (blockSite w o)) =
      blockBaseWeight ℓ (frameHotLumps ℓ S' W') (torusSiteInFrame (stepBlockFrame ℓ.side n') 1 w')
        (torusSiteInFrame (stepBlockFrame ℓ.side n') 0 (blockSite w' o)) := by
  classical
  have hag : ∀ (u : Fin 4 → ℤ) (k : Fin 4), OffsetInBox (3 * ℓ.side) u →
      OffsetInBox (3 * ℓ.side) (u + Pi.single k 1) →
      readAtLevel (stepBlockFrame ℓ.side n) 0 W (siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 w) u) k =
        readAtLevel (stepBlockFrame ℓ.side n') 0 W'
          (siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n') 1 w') u) k := by
    intro u k hu hu'
    have e := hW _ k (abs_sub_refinedOffset_le hfit.L_odd hu o)
    rw [← toTorusSite_siteAtOffset w o u, ← toTorusSite_siteAtOffset w' o u] at e
    exact e
  obtain ⟨hc, hm⟩ := (hblocks ℓ hfit n n' h16 h16' _ _ _ _ hag).1
    (S.image (torusSiteInFrame (stepBlockFrame ℓ.side n) 0))
    (S'.image (torusSiteInFrame (stepBlockFrame ℓ.side n') 0)) (fun u hu => by
      refine mem_image_torusSiteInFrame.trans (Iff.trans ?_ mem_image_torusSiteInFrame.symm)
      have e := hS _ (abs_sub_refinedOffset_le hfit.L_odd hu o)
      rw [← toTorusSite_siteAtOffset w o u, ← toTorusSite_siteAtOffset w' o u] at e
      exact e)
  have hz₀ := hm _ (refinedOffset_mem_centredCube hfit.L_odd o)
  have e₁ := torusSiteInFrame_blockSite_eq (L := ℓ.side) w o
  have e₂ := torusSiteInFrame_blockSite_eq (L := ℓ.side) w' o
  have hz : torusSiteInFrame (stepBlockFrame ℓ.side n) 0 (blockSite w o : TorusSite (n * ℓ.side)) ∈
        baseSitesAt ℓ.baseDepth (hotLumps ℓ.grid ℓ.threshold (S.image (torusSiteInFrame (stepBlockFrame ℓ.side n) 0))
          (readAtLevel (stepBlockFrame ℓ.side n) 0 W)) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 w) ↔
      torusSiteInFrame (stepBlockFrame ℓ.side n') 0 (blockSite w' o : TorusSite (n' * ℓ.side)) ∈
        baseSitesAt ℓ.baseDepth (hotLumps ℓ.grid ℓ.threshold
          (S'.image (torusSiteInFrame (stepBlockFrame ℓ.side n') 0))
          (readAtLevel (stepBlockFrame ℓ.side n') 0 W')) (torusSiteInFrame (stepBlockFrame ℓ.side n') 1 w') :=
    (iff_of_eq (congrArg (· ∈ baseSitesAt ℓ.baseDepth _ _) e₁)).trans
      (hz₀.trans (iff_of_eq (congrArg (· ∈ baseSitesAt ℓ.baseDepth _ _) e₂)).symm)
  unfold blockBaseWeight frameHotLumps
  exact if_congr hz (congrArg (fun c : ℕ => 1 / (c : ℝ)) hc) rfl
end Sites
section Matched
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n'] {V : TorusField n} {V' : TorusField n'}
  {X : Finset (TorusSite n)} {X' : Finset (TorusSite n')} {y : TorusSite n} {y' : TorusSite n'} {m : ℕ}
theorem le_of_ballInBox {ρ : ℕ} {a : Fin 4 → ℤ} (h : BallInBox m ρ a) : ρ ≤ m := by
  have h1 := h (fun _ => (ρ : ℤ)) (fun i => by simp)
  have h2 := h (fun _ => -(ρ : ℤ)) (fun i => by simp)
  have a1 := abs_le.mp (h1 0)
  have a2 := abs_le.mp (h2 0)
  simp only [Pi.add_apply] at a1 a2
  omega
theorem sixteen_le_of_isBlockTorusSide {ℓ : StepParameters} (hfit : ℓ.Admissible) (hb : IsBlockTorusSide ℓ n) :
    16 ≤ n := by
  have := lt_of_isBlockTorusSide hfit hb
  omega
section Pair
variable {p : CoarseState R n} {p' : CoarseState R n'}
  (K : MatchedRecords R V V' X X' p p' y y' m) (A : p.IsAdmissibleCoarseState (hotNeighbourhoodOn R X V) X)
include K A
theorem field_eq_near_zone {a : Fin 4 → ℤ} (ha : OffsetInBox m a) (hz : y + siteOfInt a ∈ p.markedZone)
    (g : Fin 4 → ℤ) (i : Fin 4) (hg : BondOffsetInBox (R.nextRange / 2) (g, i)) :
    V (y + siteOfInt a + siteOfInt g) i = V' (y' + siteOfInt a + siteOfInt g) i := by
  have hd := K.ballsInBox_controlRegion A a ha hz
  have hin : ∀ e : Fin 4 → ℤ, (∀ k, |e k| ≤ ((R.nextRange / 2 : ℕ) : ℤ)) → y + siteOfInt (a + e) ∈ X := by
    intro e he
    rw [add_siteOfInt_add, A.eq_thickening]
    exact add_siteOfInt_mem_thickening hz he
  have hg1 : ∀ k, |g k| ≤ ((R.nextRange / 2 : ℕ) : ℤ) := hg.1
  have hg2 : ∀ k, |(g + Pi.single i 1 : Fin 4 → ℤ) k| ≤ ((R.nextRange / 2 : ℕ) : ℤ) := hg.2
  have e2 : a + g + Pi.single i 1 = a + (g + Pi.single i 1) := add_assoc _ _ _
  have e1 := K.agree (a + g, i) ⟨hd g hg1, by
    show OffsetInBox m (a + g + Pi.single i 1)
    rw [e2]
    exact hd _ hg2⟩ (hin g hg1) (by
      rw [bondFrom_fst_add_unitStep]
      show y + siteOfInt (a + g + Pi.single i 1) ∈ X
      rw [e2]
      exact hin _ hg2)
  rw [← add_siteOfInt_add, ← add_siteOfInt_add]
  exact e1
theorem refinedCentre_add_eq_blockSite {h : Fin 4 → ℤ} :
    refinedCentre R y + siteOfInt h =
      blockSite (y + siteOfInt (coarseOffset R.params.side h)) (offsetInBlock R.params.side h) := by
  have := blockSite_parentBlock_siteOffset (L := R.params.side)
    (refinedCentre R y + siteOfInt h : TorusSite (n * R.params.side))
  rw [parentBlock_blockCentre_add, siteOffset_blockCentre_add] at this
  exact this.symm
theorem refinedCentre_add_eq_blockSite' {h : Fin 4 → ℤ} :
    refinedCentre R y' + siteOfInt h =
      blockSite (y' + siteOfInt (coarseOffset R.params.side h)) (offsetInBlock R.params.side h) := by
  have := blockSite_parentBlock_siteOffset (L := R.params.side)
    (refinedCentre R y' + siteOfInt h : TorusSite (n' * R.params.side))
  rw [parentBlock_blockCentre_add, siteOffset_blockCentre_add] at this
  exact this.symm
theorem four_mul_side_le_interactionRadius : 4 * R.params.side ≤ localityRadius R := by
  have h1 := K.wellPosed.range_ge_side
  unfold localityRadius
  omega
theorem bondMark_eq_of_matched (hframe : FrameLocality.FrameCoordLocal) (hblocks : BlockDataIsLocal)
    {h : Fin 4 → ℤ} (hh : OffsetInBox (refinedBox R m) h)
    (hin : refinedCentre R y + siteOfInt h ∈ sitesInBlocks R.params.side p.markedZone) (i : Fin 4) :
    bondMark R V p.storedField (refinedCentre R y + siteOfInt h, i) =
      bondMark R V' p'.storedField (refinedCentre R y' + siteOfInt h, i) := by
  have hR := K.wellPosed
  have hfit := hR.admissible
  have ha : OffsetInBox m (coarseOffset R.params.side h) := (offsetInBox_refinedRadius_iff K.side_odd).mp hh
  have hz : y + siteOfInt (coarseOffset R.params.side h) ∈ p.markedZone := by
    have := ClusterExpansionOfAStep.mem_sitesInBlocks.mp hin
    rwa [parentBlock_blockCentre_add] at this
  have hball := K.ballsInBox_controlRegion A _ ha hz
  have e₁ := refinedCentre_add_eq_blockSite K A (h := h)
  have e₂ := refinedCentre_add_eq_blockSite' K A (h := h)
  have hd := K.ballsInBox_sitesInBlocks' A h hh hin
  have h4 := four_mul_side_le_interactionRadius K A
  have hfour : ∀ e : Fin 4 → ℤ, (∀ j, |e j| ≤ 4 * (R.params.side : ℤ)) → OffsetInBox (refinedBox R m) (h + e) :=
    fun e he => hd e fun j => (he j).trans (by exact_mod_cast h4)
  have hr1 := hR.range_le
  have hr2 := hR.range_ge_side
  have hr3 := hfit.L_ge
  have hr4 := hR.nextRange_ge
  have hbond : ∀ i : Fin 4, BondOffsetInBox (R.nextRange / 2) ((0 : Fin 4 → ℤ), i) := fun i => by
    have hone : (1 : ℤ) ≤ ((R.nextRange / 2 : ℕ) : ℤ) := by
      have : 1 ≤ R.nextRange / 2 := by omega
      exact_mod_cast this
    refine ⟨fun k => ?_, fun k => ?_⟩
    · simp only [Pi.zero_apply, abs_zero]
      omega
    · have : |(Pi.single i 1 : Fin 4 → ℤ) k| ≤ 1 := by
        by_cases hk : k = i
        · subst hk
          simp
        · simp [hk]
      simp only [zero_add]
      linarith
  have hc : chartCoord R.params V p.storedField (refinedCentre R y + siteOfInt h, i) =
      chartCoord R.params V' p'.storedField (refinedCentre R y' + siteOfInt h, i) := by
    rw [e₁, e₂]
    refine chartCoord_eq_of_agree hblocks hfit (sixteen_le_of_isBlockTorusSide hfit K.isBlockTorusSide)
      (sixteen_le_of_isBlockTorusSide hfit K.isBlockTorusSide') _ _ _ i (fun e k he => ?_) ?_
    · rw [← e₁, ← e₂, ← add_siteOfInt_add, ← add_siteOfInt_add]
      exact K.recordsAgree.storedField_eq K.side_odd (hfour e he) k
    · have := field_eq_near_zone K A ha hz 0 i (hbond i)
      simpa [siteOfInt_zero_offset] using this
  have hside := le_of_ballInBox hball
  have hs := K.box_lt
  have hs' := K.box_lt'
  have hm₀ : R.frameReach = R.range / 2 ^ 11 := rfl
  have hf : frameCoord R.params R.anchorRadius R.depth R.frameReach V (refinedCentre R y + siteOfInt h, i) =
      frameCoord R.params R.anchorRadius R.depth R.frameReach V' (refinedCentre R y' + siteOfInt h, i) := by
    refine hframe R.params R.anchorRadius R.depth R.frameReach n n' V V' _ _ hfit (by omega) (by omega) (by omega)
      rfl ?_ ?_
    · show cellOffset (F := torusFrame R.params.side R.depth n)
          (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).depth
            (refinedCentre R y + siteOfInt h)) =
        cellOffset (F := torusFrame R.params.side R.depth n')
          (torusSiteInFrame (torusFrame R.params.side R.depth n') (torusFrame R.params.side R.depth n').depth
            (refinedCentre R y' + siteOfInt h))
      rw [e₁, e₂, cellOffset_blockSite K.side_odd K.two_le, cellOffset_blockSite K.side_odd K.two_le']
    · show FieldsAgreeNear V V' (parentBlock R.params.side (refinedCentre R y + siteOfInt h))
        (parentBlock R.params.side (refinedCentre R y' + siteOfInt h)) R.frameReach
      rw [parentBlock_blockCentre_add, parentBlock_blockCentre_add]
      intro b hb
      have hle : ((R.frameReach : ℕ) : ℤ) ≤ ((R.nextRange / 2 : ℕ) : ℤ) := by
        have : R.frameReach ≤ R.nextRange / 2 := by omega
        exact_mod_cast this
      exact field_eq_near_zone K A ha hz b.1 b.2 ⟨fun k => (hb.1 k).trans hle, fun k => (hb.2 k).trans hle⟩
  unfold bondMark
  rw [hc, hf]
end Pair
section Parts
variable {q : CoarseState R n} {q' : CoarseState R n'}
  (K : MatchedRecords R V V' X X' (q.restrict X) (q'.restrict X') y y' m)
  (A : (q.restrict X).IsAdmissibleCoarseState (hotNeighbourhoodOn R X V) X)
include K A
theorem markFactor_eq_of_matched (hframe : FrameLocality.FrameCoordLocal) (hblocks : BlockDataIsLocal) :
    ∏ b ∈ markedBonds R (hotNeighbourhoodOn R X V) ∩ bondsOverBlocks R.params.side (q.restrict X).markedZone,
      (open Classical in if b ∈ (q.restrict X).storedBadBonds then 1 - bondMark R V (q.restrict X).storedField b
        else bondMark R V (q.restrict X).storedField b) =
    ∏ b ∈ markedBonds R (hotNeighbourhoodOn R X' V') ∩ bondsOverBlocks R.params.side (q'.restrict X').markedZone,
      (open Classical in if b ∈ (q'.restrict X').storedBadBonds then 1 - bondMark R V' (q'.restrict X').storedField b
        else bondMark R V' (q'.restrict X').storedField b) := by
  classical
  have hS := K.congruent_sitesInBlocks A
  refine prod_eq_prod_of_rel (fun (b : TorusBond (n * R.params.side)) (b' : TorusBond (n' * R.params.side)) =>
    ∃ h i, OffsetInBox (refinedBox R m) h ∧
      b = (refinedCentre R y + siteOfInt h, i) ∧ b' = (refinedCentre R y' + siteOfInt h, i)) _ _ ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, i⟩ hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_inter.mp hb
    have hx : x ∈ sitesInBlocks R.params.side (q.restrict X).markedZone :=
      ClusterExpansionOfAStep.mem_sitesInBlocks.mpr (Finset.mem_filter.mp hb2).2.1
    obtain ⟨h, hh, rfl⟩ := hS.1 x hx
    exact ⟨(_, i), Finset.mem_inter.mpr ⟨(K.mem_markedBonds_iff A hh i).mp hb1,
      (K.mem_bondsOverBlocks_iff A hh hx i).mp hb2⟩, h, i, hh, rfl, rfl⟩
  · rintro ⟨x, i⟩ hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_inter.mp hb
    have hx : x ∈ sitesInBlocks R.params.side (q'.restrict X').markedZone :=
      ClusterExpansionOfAStep.mem_sitesInBlocks.mpr (Finset.mem_filter.mp hb2).2.1
    obtain ⟨h, hh, rfl⟩ := hS.2.1 x hx
    have hin := (hS.2.2 h hh).mpr hx
    exact ⟨(_, i), Finset.mem_inter.mpr ⟨(K.mem_markedBonds_iff A hh i).mpr hb1,
      (K.mem_bondsOverBlocks_iff A hh hin i).mpr hb2⟩, h, i, hh, rfl, rfl⟩
  · rintro a - b - b' - ⟨h, i, hh, rfl, rfl⟩ ⟨h₂, i₂, hh₂, he, rfl⟩
    obtain ⟨e1, e2⟩ := Prod.mk.inj he
    rw [eq_of_add_siteOfInt_eq K.refinedBox_lt hh hh₂ e1, e2]
  · rintro a - a' - b - ⟨h, i, hh, rfl, rfl⟩ ⟨h₂, i₂, hh₂, rfl, he⟩
    obtain ⟨e1, e2⟩ := Prod.mk.inj he
    rw [eq_of_add_siteOfInt_eq K.refinedBox_lt' hh hh₂ e1, e2]
  · rintro a ha b hb ⟨h, i, hh, rfl, rfl⟩
    obtain ⟨-, hb2⟩ := Finset.mem_inter.mp ha
    have hx : refinedCentre R y + siteOfInt h ∈ sitesInBlocks R.params.side (q.restrict X).markedZone :=
      ClusterExpansionOfAStep.mem_sitesInBlocks.mpr (Finset.mem_filter.mp hb2).2.1
    have hbad := K.recordsAgree.mem_storedBadBonds_iff K.side_odd hh i
    have hmk := bondMark_eq_of_matched K A hframe hblocks hh hx i
    by_cases hbd : ((refinedCentre R y + siteOfInt h, i) : TorusBond _) ∈ (q.restrict X).storedBadBonds
    · rw [if_pos hbd, if_pos (hbad.mp hbd), hmk]
    · rw [if_neg hbd, if_neg (fun h' => hbd (hbad.mpr h')), hmk]
theorem baseFactorProduct_eq_of_matched (hblocks : BlockDataIsLocal) :
    baseFactorProduct q X = baseFactorProduct q' X' := by
  classical
  have hZ := K.recordsAgree.markedZone_congruent
  have hfit := K.wellPosed.admissible
  unfold baseFactorProduct
  refine prod_eq_prod_of_rel (fun (w : TorusSite n) (w' : TorusSite n') =>
    ∃ a, OffsetInBox m a ∧ w = y + siteOfInt a ∧ w' = y' + siteOfInt a) _ _ ?_ ?_ ?_ ?_ ?_
  · intro w hw
    obtain ⟨a, ha, rfl⟩ := hZ.1 w hw
    exact ⟨_, (hZ.2.2 a ha).mp hw, a, ha, rfl, rfl⟩
  · intro w hw
    obtain ⟨a, ha, rfl⟩ := hZ.2.1 w hw
    exact ⟨_, (hZ.2.2 a ha).mpr hw, a, ha, rfl, rfl⟩
  · rintro a - b - b' - ⟨c, hc, rfl, rfl⟩ ⟨c₂, hc₂, he, rfl⟩
    rw [eq_of_add_siteOfInt_eq K.box_lt hc hc₂ he]
  · rintro a - a' - b - ⟨c, hc, rfl, rfl⟩ ⟨c₂, hc₂, rfl, he⟩
    rw [eq_of_add_siteOfInt_eq K.box_lt' hc hc₂ he]
  · rintro w hw w' - ⟨a, ha, rfl, rfl⟩
    have hst := K.recordsAgree.markAt_eq a ha
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (ClusterExpansionOfAStep.mem_controlRegion.mp hw)
    have hs' : (q'.restrict X').markAt (y' + siteOfInt a) = some s := hst ▸ hs
    simp only [hs, hs']
    have hb₁ : OffsetInBox (refinedBox R m) (refinedOffset R.params.side a s.basePoint) :=
      offsetInBox_refinedOffset K.side_odd ha _
    have hin : refinedCentre R y + siteOfInt (refinedOffset R.params.side a s.basePoint) ∈
        sitesInBlocks R.params.side (q.restrict X).markedZone := by
      rw [ClusterExpansionOfAStep.mem_sitesInBlocks, parentBlock_blockCentre_add, coarseOffset_refinedOffset]
      exact hw
    have hd := K.ballsInBox_sitesInBlocks' A _ hb₁ hin
    have h4 := four_mul_side_le_interactionRadius K A
    have hfour : ∀ e : Fin 4 → ℤ, (∀ j, |e j| ≤ 4 * (R.params.side : ℤ)) →
        OffsetInBox (refinedBox R m) (refinedOffset R.params.side a s.basePoint + e) := fun e he =>
      hd e fun j => (he j).trans (by exact_mod_cast h4)
    refine blockBaseWeight_eq_of_agree hblocks hfit (sixteen_le_of_isBlockTorusSide hfit K.isBlockTorusSide)
      (sixteen_le_of_isBlockTorusSide hfit K.isBlockTorusSide') _ _ s.basePoint (fun e k he => ?_) (fun e he => ?_)
    · rw [blockSite_add_eq, blockSite_add_eq, ← add_siteOfInt_add, ← add_siteOfInt_add]
      exact K.recordsAgree.storedField_eq K.side_odd (hfour e he) k
    · rw [blockSite_add_eq, blockSite_add_eq, ← add_siteOfInt_add, ← add_siteOfInt_add]
      exact (K.congruent_sitesInBlocks A).2.2 _ (hfour e he)
theorem coarseFactor_eq_of_admissible (hframe : FrameLocality.FrameCoordLocal) (hblocks : BlockDataIsLocal) :
    coarseFactor V q X = coarseFactor V' q' X' := by
  classical
  have A' := K.isAdmissibleOn' A
  have e1 : clusterFactorProduct q X = clusterFactorProduct q' X' := K.prod_clusterFactor_eq A
  have e2 : markFactorProduct V q X = markFactorProduct V' q' X' := markFactor_eq_of_matched K A hframe hblocks
  unfold coarseFactor admissibilityIndicator
  rw [if_pos A, if_pos A', e1, e2, baseFactorProduct_eq_of_matched K A hblocks]
end Parts
theorem coarseFactor_eq_of_matched {q : CoarseState R n} {q' : CoarseState R n'}
    (hframe : FrameLocality.FrameCoordLocal) (hblocks : BlockDataIsLocal)
    (K : MatchedRecords R V V' X X' (q.restrict X) (q'.restrict X') y y' m) :
    coarseFactor V q X = coarseFactor V' q' X' := by
  classical
  by_cases A : (q.restrict X).IsAdmissibleCoarseState (hotNeighbourhoodOn R X V) X
  · exact coarseFactor_eq_of_admissible K A hframe hblocks
  · have hn : ¬ (q'.restrict X').IsAdmissibleCoarseState (hotNeighbourhoodOn R X' V') X' :=
      fun h => A (K.symm.isAdmissibleOn' h)
    unfold coarseFactor admissibilityIndicator
    rw [if_neg A, if_neg hn]
    simp
theorem markAt_eq_of_label_eq {Y : Finset (TorusSite n)} {Y' : Finset (TorusSite n')}
    {ω : Y → CoarseLabel R.labels.Ω R.params.side} {ω' : Y' → CoarseLabel R.labels.Ω R.params.side}
    {z : TorusSite n} {z' : TorusSite n'} (m1 : z ∈ Y) (m2 : z' ∈ Y') (e : ω ⟨z, m1⟩ = ω' ⟨z', m2⟩) :
    CoarseState.markAt (⟨Y, ω⟩ : CoarseState R n) z = CoarseState.markAt (⟨Y', ω'⟩ : CoarseState R n') z' := by
  rcases hω : ω ⟨z, m1⟩ with u | s
  · rw [ClusterExpansionOfAStep.markAt_of_inl (q := ⟨Y, ω⟩) m1 hω,
      ClusterExpansionOfAStep.markAt_of_inl (q := ⟨Y', ω'⟩) m2 (e.symm.trans hω)]
  · rw [ClusterExpansionOfAStep.markAt_of_inr (q := ⟨Y, ω⟩) m1 hω,
      ClusterExpansionOfAStep.markAt_of_inr (q := ⟨Y', ω'⟩) m2 (e.symm.trans hω)]
theorem recordsAgree_of_labelsAgree {Y : Finset (TorusSite n)} {Y' : Finset (TorusSite n')}
    {ω : Y → CoarseLabel R.labels.Ω R.params.side} {ω' : Y' → CoarseLabel R.labels.Ω R.params.side}
    (hX : X ⊆ Y) (hX' : X' ⊆ Y') (hbox : CongruentInBoxes X X' y y' m)
    (hl : LabelsAgreeNear Y Y' ω ω' y y' m X) :
    RecordsAgree (CoarseState.restrict (⟨Y, ω⟩ : CoarseState R n) X)
      (CoarseState.restrict (⟨Y', ω'⟩ : CoarseState R n') X') y y' m := by
  classical
  refine ⟨fun a ha => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · rw [ClusterExpansionOfAStep.markAt_restrict, ClusterExpansionOfAStep.markAt_restrict]
    by_cases h : y + siteOfInt a ∈ X
    · have h' := (hbox.2.2 a ha).mp h
      rw [if_pos h, if_pos h']
      exact markAt_eq_of_label_eq (hX h) (hX' h') (hl a ha (hX h) (hX' h') h)
    · rw [if_neg h, if_neg fun h' => h ((hbox.2.2 a ha).mpr h')]
  · refine hbox.1 z ?_
    by_contra h
    rw [ClusterExpansionOfAStep.markAt_restrict, if_neg h] at hz
    simp at hz
  · refine hbox.2.1 z ?_
    by_contra h
    rw [ClusterExpansionOfAStep.markAt_restrict, if_neg h] at hz
    simp at hz
end Matched
section Top
variable {R : StepSetup}
theorem coarseFactorExpansion_eq (R : StepSetup) (n : ℕ) [NeZero n] (V : TorusField n) (Y X : Finset (TorusSite n))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) :
    coarseFactorExpansion R n V Y ω X = coarseFactor V (⟨Y, ω⟩ : CoarseState R n) X := dif_neg (NeZero.ne n)
theorem isBlockTorusSide_mul {n : ℕ} (hb : IsBlockTorusSide R.params n) :
    IsBlockTorusSide R.params (n * R.params.side) := by
  have h0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have h1 := hb.2
  refine ⟨Dvd.intro_left _ rfl, ?_⟩
  have h2 : R.params.n₀ ≤ n := by
    have : 1 * R.params.n₀ ≤ R.params.side * R.params.n₀ := Nat.mul_le_mul_right _ h0
    omega
  calc R.params.side * R.params.n₀ = R.params.n₀ * R.params.side := Nat.mul_comm _ _
    _ ≤ n * R.params.side := Nat.mul_le_mul_right _ h2
theorem coarseFactor_nonneg (hR : R.IsWellPosed) {n : ℕ} [NeZero n] (hb : IsBlockTorusSide R.params n)
    (V : TorusField n) (q : CoarseState R n) (X : Finset (TorusSite n)) : 0 ≤ coarseFactor V q X := by
  classical
  have hρ : 0 < R.ballRadius := by
    have := hR.admissible.σ_pos
    unfold StepSetup.ballRadius
    positivity
  have hbf := isBlockTorusSide_mul hb
  unfold coarseFactor
  refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
  · unfold admissibilityIndicator
    split_ifs <;> norm_num
  · exact Finset.prod_nonneg fun _ _ => hR.hasExpansions.2.factor_nonneg _ hbf _ _ _ _
  · refine Finset.prod_nonneg fun b _ => ?_
    split_ifs
    · have : bondMark R V (q.restrict X).storedField b ≤ 1 := cutoffFactor_le_one hρ hR.isCutoff (norm_nonneg _)
      linarith
    · exact cutoffFactor_nonneg _
  · refine Finset.prod_nonneg fun w _ => ?_
    split
    · unfold blockBaseWeight
      split_ifs
      · positivity
      · exact le_rfl
    · exact zero_le_one
section Read
variable {n : ℕ} [NeZero n] {V V' : TorusField n} {X : Finset (TorusSite n)}
theorem curvature_eq_of_agree
    (hV : ∀ b : TorusBond n, b.1 ∈ X → b.1 + TorusFields.unitStep n b.2 ∈ X → V b.1 b.2 = V' b.1 b.2) {x : TorusSite n}
    {μ ν : Fin 4} (hc : ∀ z ∈ plaquetteVertices x μ ν, z ∈ X) : curvature V x μ ν = curvature V' x μ ν := by
  have c0 : x ∈ X := hc _ (by simp [plaquetteVertices])
  have c1 : x + TorusFields.unitStep n μ ∈ X := hc _ (by simp [plaquetteVertices])
  have c2 : x + TorusFields.unitStep n ν ∈ X := hc _ (by simp [plaquetteVertices])
  have c3 : x + TorusFields.unitStep n μ + TorusFields.unitStep n ν ∈ X := hc _ (by simp [plaquetteVertices])
  have c3' : x + TorusFields.unitStep n ν + TorusFields.unitStep n μ ∈ X := by
    rw [add_right_comm]
    exact c3
  have e1 : V x μ = V' x μ := hV (x, μ) c0 c1
  have e2 : V (x + TorusFields.unitStep n μ) ν = V' (x + TorusFields.unitStep n μ) ν :=
    hV (x + TorusFields.unitStep n μ, ν) c1 c3
  have e3 : V (x + TorusFields.unitStep n ν) μ = V' (x + TorusFields.unitStep n ν) μ :=
    hV (x + TorusFields.unitStep n ν, μ) c2 c3'
  have e4 : V x ν = V' x ν := hV (x, ν) c0 c2
  unfold curvature holonomy
  rw [e1, e2, e3, e4]
theorem hotNeighbourhoodOn_congr (hfit : R.params.Admissible) (hL : R.params.side ∣ n)
    (hV : ∀ b : TorusBond n, b.1 ∈ X → b.1 + TorusFields.unitStep n b.2 ∈ X → V b.1 b.2 = V' b.1 b.2) :
    hotNeighbourhoodOn R X V = hotNeighbourhoodOn R X V' := by
  have : hotLumpsOn R.params X V = hotLumpsOn R.params X V' := by
    ext l
    rw [mem_hotLumpsOn_iff R.params hfit hL, mem_hotLumpsOn_iff R.params hfit hL]
    constructor
    · rintro ⟨x, μ, ν, h1, h2, h3, z, hz, rfl⟩
      exact ⟨x, μ, ν, h1, by rwa [← curvature_eq_of_agree hV h3], h3, z, hz, rfl⟩
    · rintro ⟨x, μ, ν, h1, h2, h3, z, hz, rfl⟩
      exact ⟨x, μ, ν, h1, by rwa [curvature_eq_of_agree hV h3], h3, z, hz, rfl⟩
  unfold hotNeighbourhoodOn
  rw [this]
theorem bondMark_eq_of_fieldsAgree (hframe : FrameLocality.FrameCoordLocal) (hblocks : BlockDataIsLocal)
    (hR : R.IsWellPosed) (hb : IsBlockTorusSide R.params n) {Z : Finset (TorusSite n)}
    (hX : X = thickening (R.nextRange / 2) Z)
    (hV : ∀ b : TorusBond n, b.1 ∈ X → b.1 + TorusFields.unitStep n b.2 ∈ X → V b.1 b.2 = V' b.1 b.2)
    {b : TorusBond (n * R.params.side)} (hbz : b ∈ bondsOverBlocks R.params.side Z)
    (W : TorusField (n * R.params.side)) : bondMark R V W b = bondMark R V' W b := by
  classical
  obtain ⟨x, i⟩ := b
  have hfit := hR.admissible
  have hz : parentBlock R.params.side x ∈ Z := (Finset.mem_filter.mp hbz).2.1
  have e : x = blockSite (parentBlock R.params.side x) (siteOffset x) := (blockSite_parentBlock_siteOffset x).symm
  have hball : ∀ e : Fin 4 → ℤ, (∀ k, |e k| ≤ ((R.nextRange / 2 : ℕ) : ℤ)) →
      parentBlock R.params.side x + siteOfInt e ∈ X := by
    intro e he
    rw [hX]
    exact add_siteOfInt_mem_thickening hz he
  have hbd : ∀ (g : Fin 4 → ℤ) (k : Fin 4), BondOffsetInBox (R.nextRange / 2) (g, k) →
      V (parentBlock R.params.side x + siteOfInt g) k = V' (parentBlock R.params.side x + siteOfInt g) k := by
    intro g k hg
    refine hV (parentBlock R.params.side x + siteOfInt g, k) (hball g hg.1) ?_
    show parentBlock R.params.side x + siteOfInt g + TorusFields.unitStep n k ∈ X
    rw [unitStep_eq_siteOfInt, ← add_siteOfInt_add]
    exact hball _ hg.2
  have hr1 := hR.range_le
  have hr2 := hR.range_ge_side
  have hr3 := hfit.L_ge
  have hone : (1 : ℤ) ≤ ((R.nextRange / 2 : ℕ) : ℤ) := by
    have : 1 ≤ R.nextRange / 2 := by omega
    exact_mod_cast this
  have h0 : V (parentBlock R.params.side x) i = V' (parentBlock R.params.side x) i := by
    have := hbd 0 i ⟨fun k => by
      simp only [Pi.zero_apply, abs_zero]
      omega, fun k => by
      have : |(Pi.single i 1 : Fin 4 → ℤ) k| ≤ 1 := by
        by_cases hk : k = i
        · subst hk
          simp
        · simp [hk]
      simp only [zero_add]
      linarith⟩
    simpa [siteOfInt_zero_offset] using this
  have hc : chartCoord R.params V W (x, i) = chartCoord R.params V' W (x, i) := by
    have h16 := sixteen_le_of_isBlockTorusSide hfit hb
    have := chartCoord_eq_of_agree hblocks hfit h16 h16 (W := W) (W' := W) (V := V) (V' := V')
      (parentBlock R.params.side x) (parentBlock R.params.side x) (siteOffset x) i (fun _ _ _ => rfl) h0
    rwa [← e] at this
  have hm₀ : R.frameReach = R.range / 2 ^ 11 := rfl
  have hf : frameCoord R.params R.anchorRadius R.depth R.frameReach V (x, i) =
      frameCoord R.params R.anchorRadius R.depth R.frameReach V' (x, i) := by
    by_cases hbig : 4 * R.frameReach + 5 < n
    · refine hframe R.params R.anchorRadius R.depth R.frameReach n n V V' _ _ hfit (by omega) hbig hbig rfl rfl
        fun c hc => ?_
      have hle : ((R.frameReach : ℕ) : ℤ) ≤ ((R.nextRange / 2 : ℕ) : ℤ) := by
        have : R.frameReach ≤ R.nextRange / 2 := by omega
        exact_mod_cast this
      exact hbd c.1 c.2 ⟨fun k => (hc.1 k).trans hle, fun k => (hc.2 k).trans hle⟩
    · have hXu : ∀ z, z ∈ X := by
        intro z
        rw [hX]
        refine (mem_thickening _ _ _).mpr ⟨_, hz, ?_⟩
        have h1 : supDist z (parentBlock R.params.side x) ≤ n / 2 :=
          (supDist_le_iff _ _ _).mpr fun i => ZMod.natAbs_valMinAbs_le _
        omega
      have : V = V' := funext fun z => funext fun k => hV (z, k) (hXu _) (hXu _)
      rw [this]
  unfold bondMark
  rw [hc, hf]
theorem coarseFactor_eq_of_fieldsAgree (hframe : FrameLocality.FrameCoordLocal) (hblocks : BlockDataIsLocal)
    (hR : R.IsWellPosed) (hb : IsBlockTorusSide R.params n) {q q' : CoarseState R n}
    (hp : q.restrict X = q'.restrict X)
    (hV : ∀ b : TorusBond n, b.1 ∈ X → b.1 + TorusFields.unitStep n b.2 ∈ X → V b.1 b.2 = V' b.1 b.2) :
    coarseFactor V q X = coarseFactor V' q' X := by
  classical
  have hC := hotNeighbourhoodOn_congr hR.admissible hb.1 hV
  unfold coarseFactor admissibilityIndicator clusterFactorProduct markFactorProduct baseFactorProduct
  rw [← hp, ← hC]
  by_cases A : (q.restrict X).IsAdmissibleCoarseState (hotNeighbourhoodOn R X V) X
  · rw [if_pos A]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun b hb' => ?_)) rfl
    rw [bondMark_eq_of_fieldsAgree hframe hblocks hR hb A.eq_thickening hV (Finset.mem_inter.mp hb').2]
  · rw [if_neg A]
    simp
end Read
end Top
end CoarseFactorLocality
namespace ClusterExpansionOfAStep
open BlockAverages LumpContours TorusFields TorusLumps StepSettings CongruentAdmission CoarseFactorLocality
theorem coarseFactorIsLocal (h₁ : FrameLocality.FrameCoordLocal) (h₂ : BlockDataIsLocal) :
    CoarseFactorIsLocalStatement := by
  intro R hR
  refine ⟨?_, ?_, ?_⟩
  · intro n _ hb V Y X ω
    rw [coarseFactorExpansion_eq]
    exact coarseFactor_nonneg hR hb V _ X
  · intro n _ hb V V' Y Y' X ω ω' hX hX' hV hl
    classical
    rw [coarseFactorExpansion_eq, coarseFactorExpansion_eq]
    refine coarseFactor_eq_of_fieldsAgree h₁ h₂ hR hb (coarseState_ext _ _ ?_ fun z => ?_) hV
    · show Y ∩ X = Y' ∩ X
      rw [Finset.inter_eq_right.mpr hX, Finset.inter_eq_right.mpr hX']
    · rw [markAt_restrict, markAt_restrict]
      by_cases h : z ∈ X
      · rw [if_pos h, if_pos h]
        exact markAt_eq_of_label_eq (hX h) (hX' h) (hl z (hX h) (hX' h) h)
      · rw [if_neg h, if_neg h]
  · intro n n' _ _ hb hb' V V' Y Y' ω ω' X X' y y' m hn hn' hXY hXY' hblk hbox hf hl
    rw [coarseFactorExpansion_eq, coarseFactorExpansion_eq]
    exact coarseFactor_eq_of_matched h₁ h₂ ⟨hR, hb, hb', hn, hn', hblk, hbox, hf, recordsAgree_of_labelsAgree hXY hXY' hbox hl⟩
end ClusterExpansionOfAStep
end YangMills.Construction
end
