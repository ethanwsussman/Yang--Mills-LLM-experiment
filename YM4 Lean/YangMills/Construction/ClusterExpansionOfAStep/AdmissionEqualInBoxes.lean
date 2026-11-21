import YangMills.Construction.ClusterExpansionOfAStep.StatesEqualInBoxes
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.CongruentAdmission
open BlockAverages LumpContours TorusLumps TorusFields StepSettings CongruentBoxes CongruentStates TopLevelSites
  StepCosts BlockPlaces ClusterExpansionOfAStep FiniteDifferences
section Frames
variable {n : ℕ} [NeZero n] {L : ℕ} [NeZero L]
theorem torusFrame_period_depth (L t n : ℕ) (i : Fin 4) : (torusFrame L t n).period t i = n * L := by
  simp [BlockFrame.period, torusFrame, BlockFrame.top]
theorem torusFrame_period_succ (L t n : ℕ) (i : Fin 4) : (torusFrame L t n).period (t + 1) i = n := by
  simp [BlockFrame.period, torusFrame, BlockFrame.top]
theorem torusSiteInFrame_blockSite (t : ℕ) (w : TorusSite n) (o : BlockOffset L) :
    torusSiteInFrame (torusFrame L t n) t (blockSite w o : TorusSite (n * L)) =
      cellCentre t (torusSiteInFrame (torusFrame L t n) (t + 1) w) + siteOfCoords t (refinedOffset L 0 o) := by
  have hp0 := torusFrame_period_depth L t n
  have hp1 := torusFrame_period_succ L t n
  have e : (blockSite w o : TorusSite (n * L)) =
      siteOfInt (fun i => (L : ℤ) * ((w i).cast : ℤ) + refinedOffset L 0 o i) := by
    rw [blockSite_eq_blockCentre_add, blockCentre_add_siteOfInt]
  rw [e, torusSiteInFrame_siteOfInt hp0]
  unfold cellCentre
  rw [← siteOfCoords_add]
  congr 1
  funext i
  have hs : (torusFrame L t n).top - t = 1 := by simp [BlockFrame.top, torusFrame]
  simp only [Pi.add_apply, hs, pow_one]
  have hc := siteCoords_torusSiteInFrame (F := torusFrame L t n) (j := t + 1) hp1 w i
  exact congrArg (fun c : ℤ => (L : ℤ) * c + refinedOffset L 0 o i) hc.symm
theorem refinedOffset_mem_centredCube (hL : Odd L) (o : BlockOffset L) : refinedOffset L 0 o ∈ centredCube L := by
  rw [mem_centredCube_iff]
  intro i
  obtain ⟨s, hs⟩ := hL
  have h1 := (o i).2
  have hz : ((L : ℤ) - 1) / 2 = s := by omega
  have hh : halfWidth L = s := hz
  simp only [refinedOffset, hh, hz]
  constructor <;> simp
  omega
theorem mem_chartBonds_iff (hL : Odd L) (h2 : 2 ≤ n) (x : TorusSite (n * L)) (i : Fin 4) :
    (x, i) ∈ chartBonds L n ↔ ¬ IsTreeOffset L (refinedOffset L 0 (siteOffset x), i) := by
  classical
  have hs : ∀ i, 2 ≤ (stepBlockFrame L n).extent i := fun _ => h2
  have e : torusSiteInFrame (stepBlockFrame L n) 0 x =
      cellCentre 0 (torusSiteInFrame (stepBlockFrame L n) 1 (parentBlock L x)) +
        siteOfCoords 0 (refinedOffset L 0 (siteOffset x)) := by
    have := torusSiteInFrame_blockSite (n := n) (L := L) 0 (parentBlock L x) (siteOffset x)
    rw [blockSite_parentBlock_siteOffset] at this
    exact this
  simp only [chartBonds, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [e]
  exact not_congr (isAxialTreeBond_iff (F := stepBlockFrame L n) hL hs _ _ (refinedOffset_mem_centredCube hL _) i)
end Frames
section Numbers
variable {n : ℕ}
theorem lt_of_isBlockTorusSide {ℓ : StepParameters} (hfit : ℓ.Admissible) (hb : IsBlockTorusSide ℓ n) :
    2 ^ 17 < n := by
  have h1 := hb.2
  have h2 := hfit.L_ge
  have h3 := hfit.n₀_ge
  have : 2 ^ 16 * 4096 ≤ ℓ.side * ℓ.n₀ := Nat.mul_le_mul h2 h3
  omega
def localityRadius (R : StepSetup) : ℕ := 10 * R.range + 2 ^ 17
theorem localityRadius_add_side_le {R : StepSetup} (hR : R.IsWellPosed) :
    localityRadius R + R.params.side ≤ R.params.side * (R.nextRange / 2) := by
  have h1 := hR.range_le
  have h2 := hR.range_ge_side
  have h3 := hR.admissible.L_ge
  obtain ⟨u, hu⟩ : ∃ u, R.nextRange / 2 = u + 1 := ⟨R.nextRange / 2 - 1, by have := hR.nextRange_ge; omega⟩
  rw [hu, Nat.mul_add, Nat.mul_one]
  have h4 : 2 ^ 16 * u ≤ R.params.side * u := Nat.mul_le_mul_right _ h3
  unfold localityRadius
  omega
end Numbers
section Small
variable {n : ℕ} [NeZero n] {y : TorusSite n} {m : ℕ}
theorem ballInBox_mono {ρ ρ₁ : ℕ} {a : Fin 4 → ℤ} (h : BallInBox m ρ a) (hρ : ρ₁ ≤ ρ) : BallInBox m ρ₁ a :=
  fun e he => h e fun i => (he i).trans (by exact_mod_cast hρ)
theorem add_siteOfInt_mem_thickening {S : Finset (TorusSite n)} {z : TorusSite n} (hz : z ∈ S) {ρ : ℕ}
    {e : Fin 4 → ℤ} (he : ∀ i, |e i| ≤ (ρ : ℤ)) : z + siteOfInt e ∈ thickening ρ S :=
  (mem_thickening _ _ _).mpr ⟨z, hz, by
    rw [supDist_comm]
    exact supDist_add_siteOfInt_le _ _ _ fun i => natAbs_le_of_abs_le_natCast (he i)⟩
theorem mem_coreBlocks_iff {L r : ℕ} [NeZero L] {θ : Finset (TorusSite (n * L))} {w : TorusSite n} :
    w ∈ coreBlocks L r θ ↔ ∃ x ∈ thickening (4 * r) θ, parentBlock L x = w := by
  classical
  simp only [coreBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hx
    exact ⟨x, h2, Finset.mem_singleton.mp (CongruentBoxes.mem_sitesInBlocks.mp h1)⟩
  · rintro ⟨x, h2, rfl⟩
    exact ⟨x, Finset.mem_inter.mpr ⟨CongruentBoxes.mem_sitesInBlocks.mpr (Finset.mem_singleton.mpr rfl), h2⟩⟩
theorem dvd_cast_intCast_mul {L : ℕ} [NeZero L] (c : ℤ) :
    (L : ℤ) ∣ ((((L : ℤ) * c : ℤ) : ZMod (n * L)).cast : ℤ) := by
  have hc : (((((L : ℤ) * c : ℤ) : ZMod (n * L))).cast : ℤ) = ((L : ℤ) * c) % ((n * L : ℕ) : ℤ) :=
    ZMod.coe_intCast _
  rw [hc, Int.emod_def]
  refine dvd_sub (Dvd.intro _ rfl) ?_
  push_cast
  exact Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _
end Small
theorem frameHotLumpSites_eq_hotLumpsOn {n : ℕ} [NeZero n] (ℓ : StepParameters) (S : Finset (TorusSite (n * ℓ.side)))
    (W : TorusField (n * ℓ.side)) : frameHotLumpSites ℓ S W = hotLumpsOn ℓ S W := by
  classical
  have hk : n * ℓ.side / ℓ.side = n := Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (NeZero.ne _))
  let Ψ : ℕ → Finset (Finset (TorusSite (n * ℓ.side))) := fun k =>
    (hotLumps ℓ.grid ℓ.threshold (S.image (torusSiteInFrame (stepBlockFrame ℓ.side k) 0))
      (readAtLevel (stepBlockFrame ℓ.side k) 0 W)).image fun l => l.image (toTorusSite (n * ℓ.side))
  exact (congrArg Ψ hk).symm
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n'] {V : TorusField n} {V' : TorusField n'}
  {X : Finset (TorusSite n)} {X' : Finset (TorusSite n')} {p : CoarseState R n} {p' : CoarseState R n'}
  {y : TorusSite n} {y' : TorusSite n'} {m : ℕ}
theorem sameBlockPosition_blockCentre {ℓ : StepParameters} (y : TorusSite n) (y' : TorusSite n') :
    SameBlockPosition ℓ (blockCentre ℓ.side y) (blockCentre ℓ.side y') := fun i =>
  Int.emod_eq_zero_of_dvd (dvd_sub (dvd_cast_intCast_mul _) (dvd_cast_intCast_mul _))
structure MatchedRecords (R : StepSetup) (V : TorusField n) (V' : TorusField n') (X : Finset (TorusSite n))
    (X' : Finset (TorusSite n')) (p : CoarseState R n) (p' : CoarseState R n') (y : TorusSite n) (y' : TorusSite n')
    (m : ℕ) : Prop where
  wellPosed : R.IsWellPosed
  isBlockTorusSide : IsBlockTorusSide R.params n
  isBlockTorusSide' : IsBlockTorusSide R.params n'
  box_lt : 2 * m + 2 < n
  box_lt' : 2 * m + 2 < n'
  sameBlock : SameBlockPosition R.params y y'
  congruent : CongruentInBoxes X X' y y' m
  agree : FieldsAgreeOnSet V V' y y' m X
  recordsAgree : RecordsAgree p p' y y' m
namespace MatchedRecords
variable (K : MatchedRecords R V V' X X' p p' y y' m)
include K
theorem symm : MatchedRecords R V' V X' X p' p y' y m :=
  ⟨K.wellPosed, K.isBlockTorusSide', K.isBlockTorusSide, K.box_lt', K.box_lt, sameBlockPosition_symm K.sameBlock,
    congruentInBoxes_symm K.congruent, fieldsAgreeOnSet_symm K.congruent K.agree, K.recordsAgree.symm⟩
theorem side_odd : Odd R.params.side := K.wellPosed.admissible.L_odd
theorem refinedBox_lt : 2 * refinedBox R m + 2 < n * R.params.side := refinedRadius_lt_side K.side_odd K.box_lt
theorem refinedBox_lt' : 2 * refinedBox R m + 2 < n' * R.params.side := refinedRadius_lt_side K.side_odd K.box_lt'
theorem two_le : 2 ≤ n := by have := K.box_lt; omega
theorem two_le' : 2 ≤ n' := by have := K.box_lt'; omega
theorem lt_refinedSide : 2 ^ 17 < n * R.params.side :=
  (lt_of_isBlockTorusSide K.wellPosed.admissible K.isBlockTorusSide).trans_le
    (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne _)))
theorem lt_refinedSide' : 2 ^ 17 < n' * R.params.side :=
  (lt_of_isBlockTorusSide K.wellPosed.admissible K.isBlockTorusSide').trans_le
    (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne _)))
variable (A : p.IsAdmissibleCoarseState (hotNeighbourhoodOn R X V) X)
include A
theorem markedZone_subset : p.markedZone ⊆ X := fun z hz => by
  rw [A.eq_thickening]
  exact subset_thickening_self _ _ hz
theorem ballsInBox_controlRegion : BallsInBox y m p.markedZone (R.nextRange / 2) := fun a ha hz =>
  offsetInBox_add_of_ball_subset K.box_lt K.congruent.1 ha rfl fun e he => by
    rw [A.eq_thickening]
    exact add_siteOfInt_mem_thickening hz he
theorem ballInBox_of_mem_hotLump {l : Finset (TorusSite n)} (hl : l ∈ hotLumpsOn R.params X V) {a : Fin 4 → ℤ}
    (ha : OffsetInBox m a) (hx : y + siteOfInt a ∈ l) : BallInBox m (2 * R.nextRange) a := by
  have hH : y + siteOfInt a ∈ (hotLumpsOn R.params X V).biUnion id := Finset.mem_biUnion.mpr ⟨l, hl, hx⟩
  exact offsetInBox_add_of_ball_subset K.box_lt K.congruent.1 ha rfl fun e he =>
    K.markedZone_subset A (A.subset_dataZone
      (show _ ∈ hotNeighbourhoodOn R X V from add_siteOfInt_mem_thickening hH he))
theorem congruent_hotNeighbourhood :
    CongruentInBoxes (hotNeighbourhoodOn R X V) (hotNeighbourhoodOn R X' V') y y' m := by
  have hfit := K.wellPosed.admissible
  have hr := K.wellPosed.nextRange_ge
  refine congruentInBoxes_thickening K.box_lt K.box_lt' (congruentInBoxes_hotLumps hfit K.isBlockTorusSide.1
    K.isBlockTorusSide'.1 (lt_of_isBlockTorusSide hfit K.isBlockTorusSide)
    (lt_of_isBlockTorusSide hfit K.isBlockTorusSide') K.box_lt K.box_lt' K.sameBlock K.congruent K.agree ?_) ?_
  · intro l hl a ha hx
    exact ballInBox_mono (K.ballInBox_of_mem_hotLump A hl ha hx) (by omega)
  · intro a ha hx
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hx
    exact K.ballInBox_of_mem_hotLump A hl ha hxl
theorem eq_thickening' : X' = thickening (R.nextRange / 2) p'.markedZone := by
  have h := K.congruent
  rw [A.eq_thickening] at h
  exact eq_of_congruentInBoxes_of_congruentInBoxes h
    (congruentInBoxes_thickening K.box_lt K.box_lt' K.recordsAgree.markedZone_congruent (K.ballsInBox_controlRegion A))
theorem congruent_sitesInBlocks :
    CongruentInBoxes (sitesInBlocks R.params.side p.markedZone) (sitesInBlocks R.params.side p'.markedZone)
      (refinedCentre R y) (refinedCentre R y') (refinedBox R m) :=
  congruentInBoxes_sitesInBlocks K.side_odd K.recordsAgree.markedZone_congruent
theorem ballsInBox_sitesInBlocks' :
    BallsInBox (refinedCentre R y) (refinedBox R m) (sitesInBlocks R.params.side p.markedZone) (localityRadius R) :=
  ballsInBox_sitesInBlocks K.side_odd (localityRadius_add_side_le K.wellPosed) (K.ballsInBox_controlRegion A)
theorem labelSet_subset : p.labelSet ⊆ sitesInBlocks R.params.side p.markedZone := fun z hz => by
  simp only [CoarseState.labelSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  exact CongruentBoxes.mem_sitesInBlocks.mpr (mem_controlRegion.mpr (isSome_of_labelAt_ne K.side_odd hz))
theorem badSites_subset : p.storedBadBonds.image Prod.fst ⊆ sitesInBlocks R.params.side p.markedZone := fun z hz => by
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
  exact CongruentBoxes.mem_sitesInBlocks.mpr (mem_controlRegion.mpr (isSome_of_mem_storedBadBonds K.side_odd hc))
theorem hotBlocks_subset :
    sitesInBlocks R.params.side (hotNeighbourhoodOn R X V) ⊆ sitesInBlocks R.params.side p.markedZone := fun z hz =>
  CongruentBoxes.mem_sitesInBlocks.mpr (A.subset_dataZone (CongruentBoxes.mem_sitesInBlocks.mp hz))
theorem congruent_clusterSites : CongruentInBoxes (clusterSites p.storedBadBonds p.labelSet (hotNeighbourhoodOn R X V))
    (clusterSites p'.storedBadBonds p'.labelSet (hotNeighbourhoodOn R X' V')) (refinedCentre R y) (refinedCentre R y')
      (refinedBox R m) :=
  congruentInBoxes_union (congruentInBoxes_union (K.recordsAgree.badSites_congruent K.side_odd)
    (K.recordsAgree.labelSet_congruent K.side_odd)) (congruentInBoxes_sitesInBlocks K.side_odd (K.congruent_hotNeighbourhood A))
theorem clusterSites_subset :
    clusterSites p.storedBadBonds p.labelSet (hotNeighbourhoodOn R X V) ⊆ sitesInBlocks R.params.side p.markedZone := by
  intro z hz
  rcases Finset.mem_union.mp hz with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact K.badSites_subset A h
    · exact K.labelSet_subset A h
  · exact K.hotBlocks_subset A h
theorem ballsInBox_clusterSites (ρ : ℕ) (hρ : ρ ≤ localityRadius R) :
    BallsInBox (refinedCentre R y) (refinedBox R m) (clusterSites p.storedBadBonds p.labelSet (hotNeighbourhoodOn R X V)) ρ :=
  (K.ballsInBox_sitesInBlocks' A).mono (K.clusterSites_subset A) hρ
theorem congruent_attachedSites :
    CongruentInBoxes (attachedSites R.params.side R.range p.storedBadBonds p.labelSet (hotNeighbourhoodOn R X V))
      (attachedSites R.params.side R.range p'.storedBadBonds p'.labelSet (hotNeighbourhoodOn R X' V'))
      (refinedCentre R y) (refinedCentre R y') (refinedBox R m) := by
  classical
  have hU := K.congruent_clusterSites A
  have hd := K.ballsInBox_clusterSites A (10 * R.range) (by unfold localityRadius; omega)
  have hB := congruentInBoxes_sitesInBlocks K.side_odd (K.congruent_hotNeighbourhood A)
  refine ⟨fun z hz => hU.1 z (attachedSites_subset _ _ _ _ hz), fun z hz => hU.2.1 z (attachedSites_subset _ _ _ _ hz),
    fun h hh => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · obtain ⟨K₀, hK, hzK, w, hw⟩ := (mem_attachedSites_iff _ _ _ _).mp hz
    obtain ⟨K', hK', hs⟩ := exists_congruent_component K.refinedBox_lt K.refinedBox_lt' hU hd hK
    obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
    obtain ⟨b, hb, rfl⟩ := hB.1 w hw2
    exact (mem_attachedSites_iff _ _ _ _).mpr ⟨K', hK', (hs.2.2 h hh).mp hzK, _,
      Finset.mem_inter.mpr ⟨(hs.2.2 b hb).mp hw1, (hB.2.2 b hb).mp hw2⟩⟩
  · obtain ⟨K', hK', hzK, w, hw⟩ := (mem_attachedSites_iff _ _ _ _).mp hz
    obtain ⟨K₀, hK, hs⟩ := exists_congruent_component_symm K.refinedBox_lt K.refinedBox_lt' hU hd hK'
    obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
    obtain ⟨b, hb, rfl⟩ := hB.2.1 w hw2
    exact (mem_attachedSites_iff _ _ _ _).mpr ⟨K₀, hK, (hs.2.2 h hh).mpr hzK, _,
      Finset.mem_inter.mpr ⟨(hs.2.2 b hb).mpr hw1, (hB.2.2 b hb).mpr hw2⟩⟩
theorem congruent_coreBlocks : CongruentInBoxes
    (coreBlocks R.params.side R.range (attachedSites R.params.side R.range p.storedBadBonds p.labelSet
      (hotNeighbourhoodOn R X V)))
    (coreBlocks R.params.side R.range (attachedSites R.params.side R.range p'.storedBadBonds p'.labelSet
      (hotNeighbourhoodOn R X' V'))) y y' m := by
  classical
  have hθ := K.congruent_attachedSites A
  have hd : BallsInBox (refinedCentre R y) (refinedBox R m)
      (attachedSites R.params.side R.range p.storedBadBonds p.labelSet (hotNeighbourhoodOn R X V)) (4 * R.range) :=
    (K.ballsInBox_clusterSites A (4 * R.range) (by unfold localityRadius; omega)).mono
      (attachedSites_subset _ _ _ _) le_rfl
  have hw := congruentInBoxes_thickening K.refinedBox_lt K.refinedBox_lt' hθ hd
  have hodd := K.side_odd
  refine ⟨fun w hw' => ?_, fun w hw' => ?_, fun a ha => ⟨fun hw' => ?_, fun hw' => ?_⟩⟩
  · obtain ⟨x, hx, rfl⟩ := mem_coreBlocks_iff.mp hw'
    obtain ⟨h, hh, rfl⟩ := hw.1 x hx
    exact ⟨_, (offsetInBox_refinedRadius_iff hodd).mp hh, parentBlock_blockCentre_add _ _⟩
  · obtain ⟨x, hx, rfl⟩ := mem_coreBlocks_iff.mp hw'
    obtain ⟨h, hh, rfl⟩ := hw.2.1 x hx
    exact ⟨_, (offsetInBox_refinedRadius_iff hodd).mp hh, parentBlock_blockCentre_add _ _⟩
  · obtain ⟨x, hx, he⟩ := mem_coreBlocks_iff.mp hw'
    obtain ⟨h, hh, rfl⟩ := hw.1 x hx
    rw [parentBlock_blockCentre_add] at he
    have := eq_of_add_siteOfInt_eq K.box_lt ((offsetInBox_refinedRadius_iff hodd).mp hh) ha he
    subst this
    exact mem_coreBlocks_iff.mpr ⟨_, (hw.2.2 h hh).mp hx, parentBlock_blockCentre_add _ _⟩
  · obtain ⟨x, hx, he⟩ := mem_coreBlocks_iff.mp hw'
    obtain ⟨h, hh, rfl⟩ := hw.2.1 x hx
    rw [parentBlock_blockCentre_add] at he
    have := eq_of_add_siteOfInt_eq K.box_lt' ((offsetInBox_refinedRadius_iff hodd).mp hh) ha he
    subst this
    exact mem_coreBlocks_iff.mpr ⟨_, (hw.2.2 h hh).mpr hx, parentBlock_blockCentre_add _ _⟩
theorem mem_bondsOverBlocks_iff {h : Fin 4 → ℤ} (hh : OffsetInBox (refinedBox R m) h)
    (hin : refinedCentre R y + siteOfInt h ∈ sitesInBlocks R.params.side p.markedZone) (i : Fin 4) :
    ((refinedCentre R y + siteOfInt h, i) : TorusBond _) ∈ bondsOverBlocks R.params.side p.markedZone ↔
      ((refinedCentre R y' + siteOfInt h, i) : TorusBond _) ∈ bondsOverBlocks R.params.side p'.markedZone := by
  classical
  have hS := K.congruent_sitesInBlocks A
  have hd := K.ballsInBox_sitesInBlocks' A h hh hin (Pi.single i 1) (fun k => by
    have : |(Pi.single i 1 : Fin 4 → ℤ) k| ≤ 1 := by
      by_cases hk : k = i
      · subst hk
        simp
      · simp [hk]
    have h2 : 1 ≤ localityRadius R := by
      unfold localityRadius
      omega
    have h3 : (1 : ℤ) ≤ (localityRadius R : ℤ) := by exact_mod_cast h2
    linarith)
  have e₁ := hS.2.2 h hh
  have e₂ := hS.2.2 _ hd
  rw [CongruentBoxes.mem_sitesInBlocks, CongruentBoxes.mem_sitesInBlocks] at e₁ e₂
  simp only [bondsOverBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [unitStep_eq_siteOfInt, unitStep_eq_siteOfInt, ← add_siteOfInt_add, ← add_siteOfInt_add, e₁, e₂]
theorem mem_markedBonds_iff {h : Fin 4 → ℤ} (hh : OffsetInBox (refinedBox R m) h) (i : Fin 4) :
    ((refinedCentre R y + siteOfInt h, i) : TorusBond _) ∈ markedBonds R (hotNeighbourhoodOn R X V) ↔
      ((refinedCentre R y' + siteOfInt h, i) : TorusBond _) ∈ markedBonds R (hotNeighbourhoodOn R X' V') := by
  classical
  have hC := K.congruent_hotNeighbourhood A
  simp only [markedBonds, Finset.mem_filter, mem_chartBonds_iff K.side_odd K.two_le,
    mem_chartBonds_iff K.side_odd K.two_le', siteOffset_blockCentre_add, parentBlock_blockCentre_add]
  rw [hC.2.2 _ ((offsetInBox_refinedRadius_iff K.side_odd).mp hh)]
theorem storedFieldBonds_eq' : p'.storedFieldBonds = bondsOverBlocks R.params.side p'.markedZone := by
  classical
  have hS := K.congruent_sitesInBlocks A
  have hodd := K.side_odd
  ext ⟨x, i⟩
  constructor
  · intro hc
    obtain ⟨h, hh, rfl⟩ := K.recordsAgree.symm.exists_offset_of_isSome hodd (isSome_of_mem_storedFieldBonds hodd hc)
    have h1 := (K.recordsAgree.mem_storedFieldBonds_iff hodd hh i).mpr hc
    rw [A.fieldBonds_eq] at h1
    have hin : refinedCentre R y + siteOfInt h ∈ sitesInBlocks R.params.side p.markedZone :=
      CongruentBoxes.mem_sitesInBlocks.mpr (Finset.mem_filter.mp h1).2.1
    exact (K.mem_bondsOverBlocks_iff A hh hin i).mp h1
  · intro hc
    have hx : x ∈ sitesInBlocks R.params.side p'.markedZone := CongruentBoxes.mem_sitesInBlocks.mpr (Finset.mem_filter.mp hc).2.1
    obtain ⟨h, hh, rfl⟩ := hS.2.1 x hx
    have hin := (hS.2.2 h hh).mpr hx
    have h1 := (K.mem_bondsOverBlocks_iff A hh hin i).mpr hc
    rw [← A.fieldBonds_eq] at h1
    exact (K.recordsAgree.mem_storedFieldBonds_iff hodd hh i).mp h1
theorem storedBadBonds_subset' : p'.storedBadBonds ⊆ markedBonds R (hotNeighbourhoodOn R X' V') := by
  rintro ⟨x, i⟩ hc
  have hodd := K.side_odd
  obtain ⟨h, hh, rfl⟩ := K.recordsAgree.symm.exists_offset_of_isSome hodd (isSome_of_mem_storedBadBonds hodd hc)
  exact (K.mem_markedBonds_iff A hh i).mp
    (A.badBonds_subset ((K.recordsAgree.mem_storedBadBonds_iff hodd hh i).mpr hc))
theorem isCore_eq' : ∀ z s, p'.markAt z = some s →
    s.isCore = (open Classical in decide (z ∈ hotNeighbourhoodOn R X' V')) := by
  classical
  intro z s hs
  obtain ⟨a, ha, rfl⟩ := K.recordsAgree.support_right z (by simp [hs])
  have h1 := K.recordsAgree.markAt_eq a ha
  rw [hs] at h1
  rw [A.isCore_eq _ _ h1]
  exact decide_eq_decide.mpr ((K.congruent_hotNeighbourhood A).2.2 a ha)
theorem agree_storedField (S : Finset (TorusSite (n * R.params.side))) :
    FieldsAgreeOnSet p.storedField p'.storedField (refinedCentre R y) (refinedCentre R y') (refinedBox R m) S :=
  fun b hb _ _ => K.recordsAgree.storedField_eq K.side_odd hb.1 b.2
omit A in
theorem side_dvd_refined : R.params.side ∣ n * R.params.side := Dvd.intro_left _ rfl
omit A in
theorem side_dvd_refined' : R.params.side ∣ n' * R.params.side := Dvd.intro_left _ rfl
theorem ballInBox_of_mem_storedLump {l : Finset (TorusSite (n * R.params.side))}
    (hl : l ∈ hotLumpsOn R.params (sitesInBlocks R.params.side p.markedZone) p.storedField) {a : Fin 4 → ℤ}
    (ha : OffsetInBox (refinedBox R m) a) (hx : refinedCentre R y + siteOfInt a ∈ l) :
    BallInBox (refinedBox R m) (10 * R.range + 2 ^ 16) a := by
  have hfit := K.wellPosed.admissible
  obtain ⟨c, hc, hcS, rfl, -⟩ := exists_hot_lump_transfer hfit K.side_dvd_refined K.side_dvd_refined'
    K.refinedBox_lt K.refinedBox_lt' (K.congruent_sitesInBlocks A) (K.agree_storedField A _) hl
  obtain ⟨e, he, hze⟩ := exists_offset_of_mem_torusLumpOf hfit K.side_dvd_refined hx
  have hd := K.ballsInBox_sitesInBlocks' A c hc hcS
  have hin := hd e fun i => (he i).trans (by
    have : 2 ^ 15 ≤ localityRadius R := by
      unfold localityRadius
      omega
    exact_mod_cast this)
  have hac : a = c + e := eq_of_add_siteOfInt_eq K.refinedBox_lt ha hin (by rw [hze, add_siteOfInt_add])
  subst hac
  intro e' he'
  have := hd (e + e') fun i => by
    have h1 := abs_le.mp (he i)
    have h2 := abs_le.mp (he' i)
    simp only [Pi.add_apply]
    unfold localityRadius
    rw [abs_le]
    push_cast at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  rwa [← add_assoc] at this
theorem congruent_frameHotLumps :
    CongruentInBoxes ((frameHotLumpSites R.params (sitesInBlocks R.params.side p.markedZone) p.storedField).biUnion id)
      ((frameHotLumpSites R.params (sitesInBlocks R.params.side p'.markedZone) p'.storedField).biUnion id)
      (refinedCentre R y) (refinedCentre R y') (refinedBox R m) := by
  rw [frameHotLumpSites_eq_hotLumpsOn, frameHotLumpSites_eq_hotLumpsOn]
  exact congruentInBoxes_hotLumps K.wellPosed.admissible K.side_dvd_refined K.side_dvd_refined' K.lt_refinedSide
    K.lt_refinedSide' K.refinedBox_lt K.refinedBox_lt' (sameBlockPosition_blockCentre y y')
    (K.congruent_sitesInBlocks A) (K.agree_storedField A _)
    fun l hl a ha hx => ballInBox_mono (K.ballInBox_of_mem_storedLump A hl ha hx) (by omega)
theorem ballsInBox_frameHotLumps : BallsInBox (refinedCentre R y) (refinedBox R m)
    ((frameHotLumpSites R.params (sitesInBlocks R.params.side p.markedZone) p.storedField).biUnion id)
      (2 * R.range) := by
  intro a ha hx
  rw [frameHotLumpSites_eq_hotLumpsOn] at hx
  obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hx
  exact ballInBox_mono (K.ballInBox_of_mem_storedLump A hl ha hxl) (by omega)
theorem ballsInBox_labelSet (ρ : ℕ) (hρ : ρ ≤ localityRadius R) :
    BallsInBox (refinedCentre R y) (refinedBox R m) p.labelSet ρ :=
  (K.ballsInBox_sitesInBlocks' A).mono (K.labelSet_subset A) hρ
theorem thickening_subset_labelSet' : thickening (2 * R.range)
    ((frameHotLumpSites R.params (sitesInBlocks R.params.side p'.markedZone) p'.storedField).biUnion id) ⊆
      p'.labelSet :=
  subset_of_congruentInBoxes
    (congruentInBoxes_thickening K.refinedBox_lt K.refinedBox_lt' (K.congruent_frameHotLumps A)
      (K.ballsInBox_frameHotLumps A))
    (K.recordsAgree.labelSet_congruent K.side_odd) A.hotHull_subset
theorem component_meets' : ∀ Xc ∈ chainComponents R.range p'.labelSet,
    ∃ l ∈ frameHotLumpSites R.params (sitesInBlocks R.params.side p'.markedZone) p'.storedField,
      (open Classical in (l ∩ Xc).Nonempty) := by
  classical
  intro Xc' hX'
  obtain ⟨Xc, hXc, hs⟩ := exists_congruent_component_symm K.refinedBox_lt K.refinedBox_lt'
    (K.recordsAgree.labelSet_congruent K.side_odd)
    (K.ballsInBox_labelSet A R.range (by unfold localityRadius; omega)) hX'
  obtain ⟨l, hl, u, hu⟩ := A.component_meets Xc hXc
  obtain ⟨hul, huX⟩ := Finset.mem_inter.mp hu
  obtain ⟨h, hh, rfl⟩ := hs.1 u huX
  have h1 := ((K.congruent_frameHotLumps A).2.2 h hh).mp (Finset.mem_biUnion.mpr ⟨l, hl, hul⟩)
  obtain ⟨l', hl', hul'⟩ := Finset.mem_biUnion.mp h1
  exact ⟨l', hl', _, Finset.mem_inter.mpr ⟨hul', (hs.2.2 h hh).mp huX⟩⟩
theorem congruent_storedBlocks :
    CongruentInBoxes (storedBlocks R.params.side R.range p.storedBadBonds p.labelSet (hotNeighbourhoodOn R X V))
      (storedBlocks R.params.side R.range p'.storedBadBonds p'.labelSet (hotNeighbourhoodOn R X' V')) y y' m :=
  congruentInBoxes_union (K.congruent_hotNeighbourhood A) (K.congruent_coreBlocks A)
theorem isAdmissibleOn' : p'.IsAdmissibleCoarseState (hotNeighbourhoodOn R X' V') X' where
  eq_thickening := K.eq_thickening' A
  isCore_eq := K.isCore_eq' A
  subset_dataZone := subset_of_congruentInBoxes (K.congruent_hotNeighbourhood A)
    K.recordsAgree.markedZone_congruent A.subset_dataZone
  badBonds_subset := K.storedBadBonds_subset' A
  fieldBonds_eq := K.storedFieldBonds_eq' A
  attached_eq := eq_of_congruentInBoxes_of_eq (K.congruent_attachedSites A) (K.congruent_clusterSites A) A.attached_eq
  storedBlocks_eq := eq_of_congruentInBoxes_of_eq (K.congruent_storedBlocks A) K.recordsAgree.markedZone_congruent
    A.storedBlocks_eq
  hotHull_subset := K.thickening_subset_labelSet' A
  component_meets := K.component_meets' A
omit A in
theorem isBlockTorusSide_refined : IsBlockTorusSide R.params (n * R.params.side) := by
  have h0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have h1 := K.isBlockTorusSide.2
  refine ⟨K.side_dvd_refined, ?_⟩
  have h2 : R.params.n₀ ≤ n := by
    have : 1 * R.params.n₀ ≤ R.params.side * R.params.n₀ := Nat.mul_le_mul_right _ h0
    omega
  calc R.params.side * R.params.n₀ = R.params.n₀ * R.params.side := Nat.mul_comm _ _
    _ ≤ n * R.params.side := Nat.mul_le_mul_right _ h2
omit A in
theorem isBlockTorusSide_refined' : IsBlockTorusSide R.params (n' * R.params.side) := by
  have h0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have h1 := K.isBlockTorusSide'.2
  refine ⟨K.side_dvd_refined', ?_⟩
  have h2 : R.params.n₀ ≤ n' := by
    have : 1 * R.params.n₀ ≤ R.params.side * R.params.n₀ := Nat.mul_le_mul_right _ h0
    omega
  calc R.params.side * R.params.n₀ = R.params.n₀ * R.params.side := Nat.mul_comm _ _
    _ ≤ n' * R.params.side := Nat.mul_le_mul_right _ h2
theorem prod_clusterFactor_eq :
    ∏ Xc ∈ chainComponents R.range p.labelSet,
        R.clusterFactor (n * R.params.side) p.storedField p.labelSet p.labeling Xc =
      ∏ Xc ∈ chainComponents R.range p'.labelSet,
        R.clusterFactor (n' * R.params.side) p'.storedField p'.labelSet p'.labeling Xc := by
  have hrow := K.wellPosed.hasExpansions.2
  have hl := K.recordsAgree.labelSet_congruent K.side_odd
  have hd := K.ballsInBox_labelSet A R.range (by unfold localityRadius; omega)
  refine prod_eq_prod_of_rel
    (fun K₁ K₂ => CongruentInBoxes K₁ K₂ (refinedCentre R y) (refinedCentre R y') (refinedBox R m)) _ _
    (fun a ha => exists_congruent_component K.refinedBox_lt K.refinedBox_lt' hl hd ha)
    (fun b hb => exists_congruent_component_symm K.refinedBox_lt K.refinedBox_lt' hl hd hb)
    (fun a _ b _ b' _ h1 h2 => eq_of_congruentInBoxes_of_congruentInBoxes h1 h2)
    (fun a _ a' _ b _ h1 h2 =>
      eq_of_congruentInBoxes_of_congruentInBoxes (congruentInBoxes_symm h1) (congruentInBoxes_symm h2))
    (fun a ha b hb hr => ?_)
  exact hrow.one_rule _ _ K.isBlockTorusSide_refined K.isBlockTorusSide_refined' _ _ _ _ _ _ a b
    (refinedCentre R y) (refinedCentre R y') (refinedBox R m) K.refinedBox_lt K.refinedBox_lt'
    (subset_of_mem_chainComponents ha) (subset_of_mem_chainComponents hb) (sameBlockPosition_blockCentre y y') hr
    (K.agree_storedField A a) (fun h hh hz hz' _ => K.recordsAgree.labeling_eq K.side_odd hh hz hz')
end MatchedRecords
end YangMills.Construction.CongruentAdmission
end
