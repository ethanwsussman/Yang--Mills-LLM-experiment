import YangMills.Construction.LawByMomentsOfTheFlow.ABoundAtClearStatesInALimitFieldProof
import YangMills.Construction.ClusterExpansionOfAStep.AZeroFactorKillsTheState
import YangMills.Construction.ClusterExpansionOfAStep.ClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslationsProof
import YangMills.Construction.FreeEnergiesOfTheFlow.FunctionsOfTheLabelsAreIntegrable
import YangMills.Construction.FreeEnergiesOfTheFlow.SupportVariablesHaveTheirSizesProof
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.VariablesAreFarAtLiveStates
import YangMills.Construction.LawByMomentsOfTheFlow.WeightsAndSitesBelowTheScale
import YangMills.Construction.LawOnABoxOfTheFlow.ToolsOfAChart
import YangMills.Construction.SixteenPointsOnASmallTorus.MeanOfTheScoresOfTheCopiesProof
import YangMills.Construction.TransfersOffTheWalk.OneStepOfSeveralResponsesProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps StepSettings StepCosts StepGas RenormalizationStepParameters WeightedResponses ResponseInTheExpansion FreeEnergies LevelTestFunctions HullTrees
section BlockCentres
variable {L n : ℕ} [NeZero L] [NeZero n]
private def centreOffset (L : ℕ) [NeZero L] : BlockOffset L := fun _ => ⟨(L - 1) / 2, by
  have := NeZero.pos L
  omega⟩
private theorem period_stepFrame_top (i : Fin 4) :
    (stepBlockFrame L n).period (stepBlockFrame L n).top i = n := by
  simp [BlockAverages.BlockFrame.period, stepBlockFrame]
private theorem period_stepFrame_zero (i : Fin 4) : (stepBlockFrame L n).period 0 i = n * L := by apply _root_.YangMills.Construction.TorusContours.stepBlockFrame_period_zero <;> assumption
private abbrev cellOfSite (L : ℕ) {n : ℕ} (Z : TorusSite n) : (stepBlockFrame L n).Cell :=
  torusSiteInFrame (stepBlockFrame L n) 1 Z
private theorem cellCentreOnTorus_cellOfSite (Z : TorusSite n) :
    cellCentreOnTorus L (cellOfSite L Z) = blockSite Z (centreOffset L) := by
  have hcell : ∀ i, ((BlockAverages.siteCoords (cellOfSite L Z) i : ℤ) : ZMod n) = Z i := fun i =>
    congrFun (TorusChain.toTorusSite_torusSiteInFrame (F := stepBlockFrame L n) period_stepFrame_top Z) i
  have e : (BlockAverages.cellCentre 0 (cellOfSite L Z) : (stepBlockFrame L n).Site 0) =
      BlockAverages.siteOfCoords 0 fun i => (L : ℤ) * BlockAverages.siteCoords (cellOfSite L Z) i :=
    TorusContours.cellCentre_eq (F := stepBlockFrame L n) (cellOfSite L Z)
  unfold cellCentreOnTorus
  rw [e, TorusContours.toTorusSite_siteOfCoords (F := stepBlockFrame L n) (j := 0) period_stepFrame_zero]
  funext i
  simp only [siteOfInt, blockSite]
  have h1 : ((BlockAverages.siteCoords (cellOfSite L Z) i : ℤ) : ZMod n) = (((Z i).cast : ℤ) : ZMod n) := by
    rw [ZMod.intCast_zmod_cast]
    exact hcell i
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
  have hm : (((centreOffset L i : Fin L) : ℕ) : ℤ) - ((L : ℤ) - 1) / 2 = 0 := by
    have := NeZero.pos L
    simp only [centreOffset]
    omega
  rw [hm, add_zero]
  have e2 : (L : ℤ) * ((Z i).cast : ℤ) =
      (L : ℤ) * BlockAverages.siteCoords (cellOfSite L Z) i + ((n * L : ℕ) : ℤ) * k := by
    have : ((Z i).cast : ℤ) = BlockAverages.siteCoords (cellOfSite L Z) i + (n : ℤ) * k := by linarith
    rw [this]
    push_cast
    ring
  rw [e2, Int.cast_add, Int.cast_mul ((n * L : ℕ) : ℤ), Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]
private theorem zmod_cast_add_intCast {m : ℕ} [NeZero m] (x : ZMod m) (z : ℤ) :
    ∃ k : ℤ, (((x + (z : ZMod m) : ZMod m)).cast : ℤ) = (x.cast : ℤ) + z + (m : ℤ) * k := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.exists_cast_add_intCast <;> assumption
private theorem blockSite_add_siteOfInt (y : TorusSite n) (o : BlockOffset L) (v : Fin 4 → ℤ) :
    (blockSite (y + siteOfInt v) o : TorusSite (n * L)) = blockSite y o + siteOfInt fun i => (L : ℤ) * v i := by
  funext i
  obtain ⟨k, hk⟩ := zmod_cast_add_intCast (y i) (v i)
  simp only [blockSite, siteOfInt, Pi.add_apply]
  rw [hk]
  have e : (L : ℤ) * (((y i).cast : ℤ) + v i + (n : ℤ) * k) + (((o i : ℕ) : ℤ) - ((L : ℤ) - 1) / 2) =
      ((L : ℤ) * ((y i).cast : ℤ) + (((o i : ℕ) : ℤ) - ((L : ℤ) - 1) / 2)) + (L : ℤ) * v i +
        ((n * L : ℕ) : ℤ) * k := by
    push_cast
    ring
  rw [e, Int.cast_add, Int.cast_mul ((n * L : ℕ) : ℤ), Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero,
    Int.cast_add]
private theorem supDist_blockSite_centre_le (y : TorusSite (n * L)) (Z : TorusSite n)
    (h : TorusFields.supDist (parentBlock L y) Z ≤ 2) :
    TorusFields.supDist (blockSite Z (centreOffset L) : TorusSite (n * L)) y ≤ 3 * L := by
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist (parentBlock L y) Z
  have h1 : TorusFields.supDist (blockSite (parentBlock L y) (centreOffset L) : TorusSite (n * L)) y ≤ L :=
    ClusterExpansionOfAStep.supDist_le_of_parentBlock_eq (u := blockSite (parentBlock L y) (centreOffset L)) (v := y)
      (BlockPlaces.parentBlock_blockSite _ _)
  have h2 : TorusFields.supDist (blockSite Z (centreOffset L) : TorusSite (n * L))
      (blockSite (parentBlock L y) (centreOffset L)) ≤ 2 * L := by
    rw [he, blockSite_add_siteOfInt, supDist_comm]
    refine supDist_add_siteOfInt_le (blockSite (parentBlock L y) (centreOffset L) : TorusSite (n * L)) _ _ fun i => ?_
    have := hb i
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    rw [mul_comm]
    exact Nat.mul_le_mul_right _ (this.trans h)
  have := supDist_triangle (blockSite Z (centreOffset L) : TorusSite (n * L))
    (blockSite (parentBlock L y) (centreOffset L)) y
  omega
end BlockCentres
section BondScores
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
private theorem bondScore_eq_of_agree (hLoc : BondKernelLocality) (hSc : BondScoreProperties) (hfit : ℓ.Admissible)
    (hn : 16 ≤ n) (x : ℝ) {W W' : TorusField (n * ℓ.side)} (V : TorusField n) {b b' : BaseChoice ℓ.side n}
    (c : TorusBond n)
    (e₁ : b (cellOfSite ℓ.side c.1) = b' (cellOfSite ℓ.side c.1))
    (e₂ : b (cellOfSite ℓ.side (c.1 + unitStep n c.2)) = b' (cellOfSite ℓ.side (c.1 + unitStep n c.2)))
    (u₁ : b (cellOfSite ℓ.side c.1) ∈ LumpContours.sitesBelow 0 (cellOfSite ℓ.side c.1))
    (u₂ : b (cellOfSite ℓ.side (c.1 + unitStep n c.2)) ∈
      LumpContours.sitesBelow 0 (cellOfSite ℓ.side (c.1 + unitStep n c.2)))
    (h₁ : FieldsAgreeNear W W' (blockSite c.1 (centreOffset ℓ.side)) (blockSite c.1 (centreOffset ℓ.side)) (3 * ℓ.side))
    (h₂ : FieldsAgreeNear W W' (blockSite (c.1 + unitStep n c.2) (centreOffset ℓ.side))
      (blockSite (c.1 + unitStep n c.2) (centreOffset ℓ.side)) (3 * ℓ.side)) :
    bondScore ℓ x W V b c = bondScore ℓ x W' V b' c := by
  have hnext : cellOfSite ℓ.side c.1 + BlockAverages.unitStep (F := stepBlockFrame ℓ.side n)
      (stepBlockFrame ℓ.side n).top c.2 = cellOfSite ℓ.side (c.1 + unitStep n c.2) := by
    have h1 := TorusChain.torusSiteInFrame_add (F := stepBlockFrame ℓ.side n) (n := n) period_stepFrame_top c.1
      (unitStep n c.2)
    have h2 := TorusChain.torusSiteInFrame_unitStep (F := stepBlockFrame ℓ.side n) (n := n) period_stepFrame_top c.2
    show _ = torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).top _
    rw [h1, h2]
    rfl
  rw [← cellCentreOnTorus_cellOfSite] at h₁ h₂
  set y := cellOfSite ℓ.side c.1 with hy
  rw [← hnext] at e₂ u₂ h₂
  obtain ⟨z₀, hz₀, hb₀⟩ := (TorusContours.mem_sitesBelow_iff (F := stepBlockFrame ℓ.side n) y _).mp u₁
  obtain ⟨z₁, hz₁, hb₁⟩ := (TorusContours.mem_sitesBelow_iff (F := stepBlockFrame ℓ.side n)
    (y + BlockAverages.unitStep (F := stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).top c.2) _).mp u₂
  have L₁ := hLoc ℓ hfit hfit.depth_lt n n hn hn W W' y y
  have L₂ := hLoc ℓ hfit hfit.depth_lt n n hn hn W W'
    (y + BlockAverages.unitStep (F := stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).top c.2)
    (y + BlockAverages.unitStep (F := stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).top c.2)
  have h2L : FieldsAgreeNear W W' (cellCentreOnTorus ℓ.side y) (cellCentreOnTorus ℓ.side y) (2 * ℓ.side) := by
    intro e he
    refine h₁ e ⟨fun i => (he.1 i).trans ?_, fun i => (he.2 i).trans ?_⟩ <;>
    · have : (0 : ℤ) ≤ ℓ.side := by positivity
      push_cast
      linarith
  have hm := (L₁.2.2.2 c.2 x (readAtLevel _ 1 V) (readAtLevel _ 1 V) b b' z₀ z₁ hz₀ hz₁ hb₀ (e₁ ▸ hb₀) hb₁
    (e₂ ▸ hb₁) h2L (L₁.2.1 h₁) (L₂.2.1 h₂)).1
  have hmean : bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W) b c =
      bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W') b' c := hm
  have hsize : meanNorm ℓ W b c = meanNorm ℓ W' b' c := congrArg norm hm
  rw [(hSc ℓ hfit x n b c).2.1 W V, (hSc ℓ hfit x n b' c).2.1 W' V, hmean, hsize]
end BondScores
section NearbyResponses
variable {R : StepSetup} {n : ℕ} [NeZero n] (A : ResponseSetup R)
private theorem siteScore_nonneg_of {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) {N : ℕ} (Yt : Finset (TorusSite N))
    (ωt : Yt → Ω) (y : TorusSite N) : 0 ≤ siteScore s Yt ωt y := by apply _root_.YangMills.SharedProofs.p22275 <;> assumption
private theorem add_siteOfInt_mem_supBall {N : ℕ} [NeZero N] {P o : TorusSite N} {a k : ℕ} {ρ : ℝ}
    (hP : TorusFields.supDist P o ≤ a) (hρ : ((a + k : ℕ) : ℝ) ≤ ρ) {e : Fin 4 → ℤ} (he : OffsetInBox k e) :
    P + siteOfInt e ∈ supBall o ρ := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have h1 : TorusFields.supDist (P + siteOfInt e) P ≤ k := by
    rw [supDist_comm]
    refine supDist_add_siteOfInt_le P e k fun i => ?_
    have := he i
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  have h2 := supDist_triangle (P + siteOfInt e) P o
  have h3 : TorusFields.supDist (P + siteOfInt e) o ≤ a + k := by omega
  exact (by exact_mod_cast h3 : ((TorusFields.supDist (P + siteOfInt e) o : ℕ) : ℝ) ≤ ((a + k : ℕ) : ℝ)).trans hρ
private theorem bondOffset_mem_supBall {N : ℕ} [NeZero N] {P o : TorusSite N} {a k : ℕ} {ρ : ℝ}
    (hP : TorusFields.supDist P o ≤ a) (hρ : ((a + k : ℕ) : ℝ) ≤ ρ) {e : Fin 4 → ℤ} {i : Fin 4} (he : BondOffsetInBox k (e, i)) :
    P + siteOfInt e ∈ supBall o ρ ∧ P + siteOfInt e + unitStep N i ∈ supBall o ρ := by
  refine ⟨add_siteOfInt_mem_supBall hP hρ he.1, ?_⟩
  have h := add_siteOfInt_mem_supBall hP hρ he.2
  rwa [siteOfInt_add, ← BlockOffsets.unitStep_eq_siteOfInt, ← add_assoc] at h
private theorem centeredHullResponse_sub_le (hres : A.IsAdmissible) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (hs : weightNorm R.params.side R.depth f ≤ 1)
    {o y : TorusSite (n * R.params.side)} {Rr m : ℕ} (hRr : 1 ≤ Rr) (hy : TorusFields.supDist y o ≤ Rr)
    (hm : (clusterRange R.coupling : ℝ) / 64 ≤ m) {W W' : TorusField (n * R.params.side)}
    {Yt Yt' : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω} {ωt' : Yt' → R.labels.Ω}
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt)
    (hl' : IsLiveState R.params R.coupling R.labelWeight W' Yt' ωt')
    (hW : ∀ c : TorusBond (n * R.params.side), c.1 ∈ supBall o ((Rr : ℝ) + m) →
      c.1 + unitStep (n * R.params.side) c.2 ∈ supBall o ((Rr : ℝ) + m) → W c.1 c.2 = W' c.1 c.2)
    (hY : ∀ y ∈ supBall o ((Rr : ℝ) + m), (y ∈ Yt ↔ y ∈ Yt') ∧
      ∀ (hy : y ∈ Yt) (hy' : y ∈ Yt'), ωt ⟨y, hy⟩ = ωt' ⟨y, hy'⟩) :
    |centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f -
        centeredHullResponse A.cold A.hull (n * R.params.side) y W' Yt' ωt' f| ≤
      (1 + siteScore A.score Yt ωt y) * Real.exp (-(R.params.decayRate * (m : ℝ))) := by
  have hs0 : 0 ≤ 1 + siteScore A.score Yt ωt y := by
    have := siteScore_nonneg_of hres.price.nonneg Yt ωt y
    linarith
  have hE : 0 ≤ (1 + siteScore A.score Yt ωt y) * Real.exp (-(R.params.decayRate * (m : ℝ))) :=
    mul_nonneg hs0 (Real.exp_pos _).le
  by_cases hbig : 2 * m + 2 < n * R.params.side
  · have hρ : ((Rr + m : ℕ) : ℝ) ≤ (Rr : ℝ) + m := by
      push_cast
      exact le_rfl
    have hst : StatesAgreeNear R.params W W' Yt Yt' ωt ωt' y y m := by
      refine ⟨hbig, hbig, ?_, ?_, ?_, fun _ i => by simp⟩
      · rintro ⟨e, i⟩ he
        have h := bondOffset_mem_supBall hy hρ he
        exact hW (y + siteOfInt e, i) h.1 h.2
      · intro e he
        exact (hY _ (add_siteOfInt_mem_supBall hy hρ he)).1
      · intro e he h1 h2 _
        exact (hY _ (add_siteOfInt_mem_supBall hy hρ he)).2 h1 h2
    have h := hres.bounds.forget (n * R.params.side) (n * R.params.side) hb hb W W' Yt Yt' ωt ωt' y y m f f hl hl'
      hm hst (fun _ _ _ _ _ => rfl)
    refine h.trans ?_
    rw [neg_mul]
    exact mul_le_of_le_one_right hE hs
  · have all : ∀ z : TorusSite (n * R.params.side), z ∈ supBall o ((Rr : ℝ) + m) := by
      intro z
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h1 := SettingShifts.two_mul_supDist_le z o
      have h2 : TorusFields.supDist z o ≤ Rr + m := by omega
      exact_mod_cast h2
    have eW : W = W' := funext fun z => funext fun i => hW (z, i) (all _) (all _)
    have eY : Yt = Yt' := Finset.ext fun z => (hY z (all z)).1
    subst eW eY
    have eω : ωt = ωt' := funext fun z => (hY z.1 (all _)).2 z.2 z.2
    subst eω
    rw [sub_self, abs_zero]
    exact hE
variable {A}
private theorem clampBasesToBlocks_mem {L n : ℕ} (hL : 1 ≤ L) (b : BaseChoice L n) (c : (stepBlockFrame L n).Cell) :
    clampBasesToBlocks b c ∈ LumpContours.sitesBelow 0 c := by
  classical
  unfold clampBasesToBlocks
  split_ifs with h
  · exact h
  · refine (TorusContours.mem_sitesBelow_iff (F := stepBlockFrame L n) c _).mpr
      ⟨0, TorusContours.zero_mem_centredCube hL, ?_⟩
    rw [siteAtOffset, BlockAverages.siteOfCoords_zero, add_zero]
    rfl
private theorem clampBasesToBlocks_congr {L n : ℕ} {b b' : BaseChoice L n} {c : (stepBlockFrame L n).Cell}
    (h : b c = b' c) : clampBasesToBlocks b c = clampBasesToBlocks b' c := by
  unfold clampBasesToBlocks
  rw [h]
private theorem bondScore_clamp_eq (hLoc : BondKernelLocality) (hSc : BondScoreProperties) (hfit : R.params.Admissible)
    (hn : 16 ≤ n) {o y : TorusSite (n * R.params.side)} {ρ m : ℕ} (hy : TorusFields.supDist y o ≤ ρ)
    {W W' : TorusField (n * R.params.side)} (V : TorusField n) {b b' : BaseChoice R.params.side n}
    (hW : ∀ c : TorusBond (n * R.params.side), c.1 ∈ supBall o (((ρ + 8 * R.params.side : ℕ) : ℝ) + m) →
      c.1 + unitStep (n * R.params.side) c.2 ∈ supBall o (((ρ + 8 * R.params.side : ℕ) : ℝ) + m) →
        W c.1 c.2 = W' c.1 c.2)
    (hB : ∀ c, (TorusFields.supDist (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c)
      (parentBlock R.params.side o) : ℝ) ≤ ((ρ + 8 * R.params.side : ℕ) : ℝ) → b c = b' c)
    (c : TorusBond n) (h₁ : TorusFields.supDist (parentBlock R.params.side y) c.1 ≤ 2)
    (h₂ : TorusFields.supDist (parentBlock R.params.side y) (c.1 + unitStep n c.2) ≤ 2) :
    bondScore R.params R.coupling W V (clampBasesToBlocks b) c =
      bondScore R.params R.coupling W' V (clampBasesToBlocks b') c := by
  have hL : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hbase : ∀ Z : TorusSite n, TorusFields.supDist (parentBlock R.params.side y) Z ≤ 2 →
      clampBasesToBlocks b (cellOfSite R.params.side Z) = clampBasesToBlocks b' (cellOfSite R.params.side Z) := by
    intro Z hZ
    refine clampBasesToBlocks_congr (hB _ ?_)
    rw [show toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n (cellOfSite R.params.side Z) = Z from
      TorusChain.toTorusSite_torusSiteInFrame (F := stepBlockFrame R.params.side n) period_stepFrame_top Z]
    have h1 := TorusBalls.supDist_parentBlock_le_div_add_one (n := n) R.params.side y o
    have h2 := supDist_triangle Z (parentBlock R.params.side y) (parentBlock R.params.side o)
    have h5 := supDist_comm Z (parentBlock R.params.side y)
    have h3 : TorusFields.supDist y o / R.params.side ≤ ρ := (Nat.div_le_self _ _).trans hy
    have h4 : TorusFields.supDist Z (parentBlock R.params.side o) ≤ ρ + 8 * R.params.side := by omega
    exact_mod_cast h4
  have hfield : ∀ Z : TorusSite n, TorusFields.supDist (parentBlock R.params.side y) Z ≤ 2 →
      FieldsAgreeNear W W' (blockSite Z (centreOffset R.params.side)) (blockSite Z (centreOffset R.params.side))
        (3 * R.params.side) := by
    intro Z hZ
    rintro ⟨e, i⟩ he
    have h1 := supDist_blockSite_centre_le y Z hZ
    have h2 := supDist_triangle (blockSite Z (centreOffset R.params.side) : TorusSite (n * R.params.side)) y o
    have h3 : TorusFields.supDist (blockSite Z (centreOffset R.params.side) : TorusSite (n * R.params.side)) o ≤
        ρ + 3 * R.params.side := by omega
    have hρ : (((ρ + 3 * R.params.side) + 3 * R.params.side : ℕ) : ℝ) ≤
        ((ρ + 8 * R.params.side : ℕ) : ℝ) + m := by
      have : (ρ + 3 * R.params.side) + 3 * R.params.side ≤ ρ + 8 * R.params.side + m := by omega
      exact_mod_cast this
    have h := bondOffset_mem_supBall h3 hρ he
    exact hW (_ + siteOfInt e, i) h.1 h.2
  exact bondScore_eq_of_agree hLoc hSc hfit hn R.coupling V c (hbase _ h₁) (hbase _ h₂)
    (clampBasesToBlocks_mem hL _ _) (clampBasesToBlocks_mem hL _ _) (hfield _ h₁) (hfield _ h₂)
end NearbyResponses
section Products
variable {R : StepSetup} {n : ℕ} [NeZero n] {A : ResponseSetup R}
private theorem abs_prod_sub_prod_le {ι : Type} (J : Finset ι) (a b : ι → ℝ) {M e : ℝ} (hM : 0 ≤ M) (he : 0 ≤ e)
    (ha : ∀ i ∈ J, |a i| ≤ M) (hb : ∀ i ∈ J, |b i| ≤ M) (hd : ∀ i ∈ J, |a i - b i| ≤ M * e) :
    |∏ i ∈ J, a i - ∏ i ∈ J, b i| ≤ J.card * M ^ J.card * e := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert i J hi ih =>
    have ih' := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)) (fun j hj => hb j (Finset.mem_insert_of_mem hj))
      (fun j hj => hd j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have hQ : |∏ j ∈ J, b j| ≤ M ^ J.card := by
      rw [Finset.abs_prod]
      calc _ ≤ ∏ _j ∈ J, M :=
            Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j hj => hb j (Finset.mem_insert_of_mem hj))
        _ = _ := by simp
    have e1 : a i * ∏ j ∈ J, a j - b i * ∏ j ∈ J, b j =
        a i * (∏ j ∈ J, a j - ∏ j ∈ J, b j) + (a i - b i) * ∏ j ∈ J, b j := by ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 := mul_le_mul (ha i (Finset.mem_insert_self _ _)) ih' (abs_nonneg _) hM
    have h2 := mul_le_mul (hd i (Finset.mem_insert_self _ _)) hQ (abs_nonneg _) (mul_nonneg hM he)
    calc _ ≤ M * (J.card * M ^ J.card * e) + M * e * M ^ J.card := add_le_add h1 h2
      _ = _ := by
        push_cast
        ring
private theorem blockBondScores_clamp_eq (hLoc : BondKernelLocality) (hSc : BondScoreProperties)
    (hfit : R.params.Admissible) (hn : 16 ≤ n) {o y : TorusSite (n * R.params.side)} {ρ m : ℕ} (hy : TorusFields.supDist y o ≤ ρ)
    {W W' : TorusField (n * R.params.side)} (V : TorusField n) {b b' : BaseChoice R.params.side n}
    (hW : ∀ c : TorusBond (n * R.params.side), c.1 ∈ supBall o (((ρ + 8 * R.params.side : ℕ) : ℝ) + m) →
      c.1 + unitStep (n * R.params.side) c.2 ∈ supBall o (((ρ + 8 * R.params.side : ℕ) : ℝ) + m) →
        W c.1 c.2 = W' c.1 c.2)
    (hB : ∀ c, (TorusFields.supDist (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c)
      (parentBlock R.params.side o) : ℝ) ≤ ((ρ + 8 * R.params.side : ℕ) : ℝ) → b c = b' c) :
    blockBondScores (R := R) W V (clampBasesToBlocks b) (parentBlock R.params.side y) =
      blockBondScores (R := R) W' V (clampBasesToBlocks b') (parentBlock R.params.side y) := by
  unfold blockBondScores
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨Y, hY⟩ : ∃ Y, Y = parentBlock R.params.side y := ⟨_, rfl⟩
  have e₀ : TorusFields.supDist (parentBlock R.params.side y) (parentBlock R.params.side y) ≤ 2 := by
    rw [supDist_self]
    omega
  have e₁ : TorusFields.supDist (parentBlock R.params.side y) (parentBlock R.params.side y + unitStep n i) ≤ 2 :=
    (supDist_add_unitStep_le _ i).trans (by omega)
  have e₂ : TorusFields.supDist (parentBlock R.params.side y) (parentBlock R.params.side y - unitStep n i) ≤ 2 := by
    have h := supDist_add_unitStep_le (parentBlock R.params.side y - unitStep n i) i
    rw [sub_add_cancel, supDist_comm] at h
    omega
  have e₃ : TorusFields.supDist (parentBlock R.params.side y) (parentBlock R.params.side y - unitStep n i + unitStep n i) ≤ 2 := by
    rw [sub_add_cancel]
    exact e₀
  rw [bondScore_clamp_eq hLoc hSc hfit hn hy V hW hB (parentBlock R.params.side y, i) e₀ e₁,
    bondScore_clamp_eq hLoc hSc hfit hn hy V hW hB (parentBlock R.params.side y - unitStep n i, i) e₂ e₃]
private theorem centeredSupportResponse_sub_le (hLoc : BondKernelLocality) (hSc : BondScoreProperties)
    (hfit : R.params.Admissible) (hres : A.IsAdmissible) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (hn : 16 ≤ n) (V : TorusField n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (hs : weightNorm R.params.side R.depth f ≤ 1) {o : TorusSite (n * R.params.side)} {ρ m : ℕ}
    (hsite : ∀ y ∈ lowerSites f, TorusFields.supDist y o ≤ ρ) (hm : (clusterRange R.coupling : ℝ) / 64 ≤ m)
    {W W' : TorusField (n * R.params.side)} {Yt Yt' : Finset (TorusSite (n * R.params.side))}
    {ωt : Yt → R.labels.Ω} {ωt' : Yt' → R.labels.Ω} (bad bad' : Finset (TorusBond (n * R.params.side)))
    {b b' : BaseChoice R.params.side n}
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt)
    (hl' : IsLiveState R.params R.coupling R.labelWeight W' Yt' ωt')
    (hW : ∀ c : TorusBond (n * R.params.side), c.1 ∈ supBall o (((ρ + 8 * R.params.side : ℕ) : ℝ) + m) →
      c.1 + unitStep (n * R.params.side) c.2 ∈ supBall o (((ρ + 8 * R.params.side : ℕ) : ℝ) + m) →
        W c.1 c.2 = W' c.1 c.2)
    (hY : ∀ y ∈ supBall o (((ρ + 8 * R.params.side : ℕ) : ℝ) + m), (y ∈ Yt ↔ y ∈ Yt') ∧
      ∀ (hy : y ∈ Yt) (hy' : y ∈ Yt'), ωt ⟨y, hy⟩ = ωt' ⟨y, hy'⟩)
    (hB : ∀ c, (TorusFields.supDist (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c)
      (parentBlock R.params.side o) : ℝ) ≤ ((ρ + 8 * R.params.side : ℕ) : ℝ) → b c = b' c) :
    |centeredSupportResponse A V f W Yt ωt bad (clampBasesToBlocks b) -
        centeredSupportResponse A V f W' Yt' ωt' bad' (clampBasesToBlocks b')| ≤
      ∑ y ∈ lowerSites f, (1 + siteScore A.score Yt ωt y) * Real.exp (-(R.params.decayRate * (m : ℝ))) := by
  classical
  have hL : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hsame : ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
        blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (R := R) W V (clampBasesToBlocks b) Y =
      ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
        blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (R := R) W' V (clampBasesToBlocks b') Y := by
    refine Finset.sum_congr rfl fun Y hY' => ?_
    have hpar : Y ∈ parentBlocks (R := R) (lowerSites f) := by
      rw [parentBlocks_lowerSites]
      exact hY'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hpar
    rw [blockBondScores_clamp_eq hLoc hSc hfit hn (hsite y hy) V hW hB]
  obtain ⟨v, hv⟩ : ∃ v, v = caseMean R ∅ (trivialField n) (emptyCoarseState R)
      (supportResponseSum A (trivialField n) f) := ⟨_, rfl⟩
  have e₁ : centeredSupportResponse A V f W Yt ωt bad (clampBasesToBlocks b) =
      ∑ y ∈ lowerSites f, centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f +
        R.params.coupling / 2 * A.coeff * ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
          blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (R := R) W V (clampBasesToBlocks b) Y - v := by
    rw [hv]
    rfl
  have e₂ : centeredSupportResponse A V f W' Yt' ωt' bad' (clampBasesToBlocks b') =
      ∑ y ∈ lowerSites f, centeredHullResponse A.cold A.hull (n * R.params.side) y W' Yt' ωt' f +
        R.params.coupling / 2 * A.coeff * ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
          blockMean R.params.side (R.depth + 1) n Y f * blockBondScores (R := R) W' V (clampBasesToBlocks b') Y - v := by
    rw [hv]
    rfl
  rw [e₁, e₂, hsame]
  have e₃ : ∀ p q c : ℝ, p + c - v - (q + c - v) = p - q := fun p q c => by ring
  rw [e₃, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y hy => ?_)
  exact centeredHullResponse_sub_le A hres hb f hs (by omega) ((hsite y hy).trans (by omega)) hm hl hl' hW hY
private theorem meanSiteScore_le_one_add_sum {N : ℕ} {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w)
    {B C : Finset (TorusSite N)} (hBC : B ⊆ C) (Y : Finset (TorusSite N)) (ω : Y → Ω) :
    meanSiteScore s B Y ω ≤ 1 + ∑ y ∈ C, siteScore s Y ω y := by
  have h0 : 0 ≤ ∑ y ∈ B, siteScore s Y ω y := Finset.sum_nonneg fun y _ => siteScore_nonneg_of hs Y ω y
  have h1 : ∑ y ∈ B, siteScore s Y ω y ≤ ∑ y ∈ C, siteScore s Y ω y :=
    Finset.sum_le_sum_of_subset_of_nonneg hBC fun y _ _ => siteScore_nonneg_of hs Y ω y
  have h2 : ((B.card : ℝ))⁻¹ * ∑ y ∈ B, siteScore s Y ω y ≤ ∑ y ∈ B, siteScore s Y ω y := by
    rcases B.eq_empty_or_nonempty with rfl | hB
    · simp
    · have hc : (1 : ℝ) ≤ B.card := by exact_mod_cast hB.card_pos
      exact mul_le_of_le_one_left h0 (inv_le_one_of_one_le₀ hc)
  unfold meanSiteScore
  linarith
private theorem one_le_meanSiteScore {N : ℕ} {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) (B : Finset (TorusSite N))
    (Y : Finset (TorusSite N)) (ω : Y → Ω) : 1 ≤ meanSiteScore s B Y ω := by apply _root_.YangMills.SharedProofs.p106812 <;> assumption
private theorem gauge_clampBasesToBlocks_eq_one {L n : ℕ} [NeZero L] [NeZero n]
    {u : TorusSite (n * L) → BlockAverages.UnitQuaternion} {b : BaseChoice L n}
    (hu : ∀ c, u (toTorusSite (n * L) (b c)) = 1) (hc : ∀ y : TorusSite n, u (blockSite y (centreOffset L)) = 1)
    (c : (stepBlockFrame L n).Cell) : u (toTorusSite (n * L) (clampBasesToBlocks b c)) = 1 := by
  classical
  unfold clampBasesToBlocks
  split_ifs with h
  · exact hu c
  · have h1 := hc (toTorusSite n c)
    rw [← cellCentreOnTorus_cellOfSite] at h1
    have h2 : cellOfSite L (toTorusSite n c) = c :=
      TorusChain.torusSiteInFrame_toTorusSite (F := stepBlockFrame L n) period_stepFrame_top c
    rw [h2] at h1
    exact h1
private theorem prod_isQuasiLocalCaseFunction (hLoc : BondKernelLocality) (hSc : BondScoreProperties)
    (hfit : R.params.Admissible) (hres : A.IsAdmissible) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (hn : 16 ≤ n) (V : TorusField n) {k : ℕ} (J : Finset (Fin k))
    (f : Fin k → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) {o : TorusSite (n * R.params.side)}
    {ρ : ℕ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hs : ∀ i ∈ J, weightNorm R.params.side R.depth (f i) ≤ 1)
    (hsite : ∀ i ∈ J, ∀ y ∈ lowerSites (f i), TorusFields.supDist y o ≤ ρ)
    (hcard : ∀ i ∈ J, ((lowerSites (f i)).card : ℝ) ≤ κ)
    (hborel : ∀ i ∈ J, ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        liveCaseFunction (centeredSupportResponse A V (f i)) p.1 Yt p.2 bad b)
    (hgauge : ∀ i ∈ J, IsGaugeInvariantCase (liveCaseFunction (centeredSupportResponse A V (f i))))
    (hsize : ∀ i ∈ J, ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
      (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
      IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
      |centeredSupportResponse A V (f i) W Yt ωt bad b| ≤
        4 * lowerSizeConst A (f i) * meanSiteScore A.score (lowerSites (f i)) Yt ωt) :
    IsQuasiLocalCaseFunction R o (ρ + 8 * R.params.side) J.card
      ((J.card + 1) * (4 * A.responseParams.C₀ * κ + κ + 1) ^ J.card)
      (J.biUnion fun i => lowerSites (f i)) A.score
      (fun W Yt ωt bad b => ∏ i ∈ J, liveCaseFunction (centeredSupportResponse A V (f i)) W Yt ωt bad
        (clampBasesToBlocks b)) := by
  classical
  have hs₀ := hres.price.nonneg
  have hC : 0 ≤ A.responseParams.C₀ := by
    have h := hres.params_admissible
    have h1 := h.C₀_eq
    have h2 := h.N₀_nonneg
    have h3 := h.Kc_ge
    have h4 := hfit.a_ge
    linarith
  obtain ⟨cc, hcc⟩ : ∃ cc, cc = 4 * A.responseParams.C₀ * κ + κ + 1 := ⟨_, rfl⟩
  have hcc0 : 0 ≤ cc := by
    rw [hcc]
    positivity
  rw [← hcc]
  obtain ⟨As, hAs⟩ : ∃ As, As = J.biUnion fun i => lowerSites (f i) := ⟨_, rfl⟩
  rw [← hAs]
  have hsub : ∀ i ∈ J, lowerSites (f i) ⊆ As := fun i hi => by
    rw [hAs]
    exact Finset.subset_biUnion_of_mem (fun i => lowerSites (f i)) hi
  have hN1 : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω),
      1 ≤ 1 + ∑ y ∈ As, siteScore A.score Yt ωt y := fun Yt ωt => by
    have : 0 ≤ ∑ y ∈ As, siteScore A.score Yt ωt y := Finset.sum_nonneg fun y _ => siteScore_nonneg_of hs₀ Yt ωt y
    linarith
  have size : ∀ i ∈ J, ∀ W Yt ωt bad b, IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
      |centeredSupportResponse A V (f i) W Yt ωt bad b| ≤ cc * (1 + ∑ y ∈ As, siteScore A.score Yt ωt y) := by
    intro i hi W Yt ωt bad b hl
    refine (hsize i hi W Yt ωt bad b hl).trans ?_
    have h1 := meanSiteScore_le_one_add_sum hs₀ (hsub i hi) Yt ωt
    have h2 := one_le_meanSiteScore hs₀ (lowerSites (f i)) Yt ωt
    have h3 : 4 * lowerSizeConst A (f i) ≤ cc := by
      unfold lowerSizeConst
      have := mul_le_mul_of_nonneg_left (hcard i hi) hC
      rw [hcc]
      linarith
    exact mul_le_mul h3 h1 (by linarith) hcc0
  have hpow : ∀ N : ℝ, 0 ≤ N → cc ^ J.card * N ^ J.card ≤ ((J.card : ℝ) + 1) * cc ^ J.card * N ^ J.card := by
    intro N hN
    have h1 : 0 ≤ cc ^ J.card * N ^ J.card := by positivity
    have h2 : (0 : ℝ) ≤ J.card := by positivity
    nlinarith
  refine
    { mem_ball := ?_
      weight_measurable := hres.price.borel
      weight_nonneg := hs₀
      weight_gauge := fun Y g ω y => hres.price.gauge _ Y g ω y
      abs_le := ?_
      measurable := fun Yt bad b => Finset.measurable_prod _ fun i hi => hborel i hi Yt bad _
      gaugeInvariant := ?_
      sub_le_of_agree := ?_ }
  · intro y hy
    rw [hAs] at hy
    obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.mp hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h1 := hsite i hi y hyi
    have h2 : TorusFields.supDist y o ≤ ρ + 8 * R.params.side := by omega
    exact_mod_cast h2
  · intro W Yt ωt bad b
    by_cases hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt
    · have h1 : |∏ i ∈ J, liveCaseFunction (centeredSupportResponse A V (f i)) W Yt ωt bad (clampBasesToBlocks b)| ≤
          ∏ _i ∈ J, (cc * (1 + ∑ y ∈ As, siteScore A.score Yt ωt y)) := by
        rw [Finset.abs_prod]
        refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i hi => ?_
        unfold liveCaseFunction
        rw [if_pos hl]
        exact size i hi _ _ _ _ _ hl
      refine h1.trans ?_
      rw [Finset.prod_const, mul_pow]
      exact hpow _ (zero_le_one.trans (hN1 Yt ωt))
    · rcases J.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
      · simp
      · rw [Finset.prod_eq_zero hi (by unfold liveCaseFunction; rw [if_neg hl]), abs_zero]
        have := zero_le_one.trans (hN1 Yt ωt)
        positivity
  · intro W Yt ωt bad b u hl hu hc
    refine Finset.prod_congr rfl fun i hi => ?_
    exact hgauge i hi W Yt ωt bad _ u hl (gauge_clampBasesToBlocks_eq_one hu hc) hc
  · intro m hm W W' Yt Yt' ωt ωt' bad bad' b b' hl hl' hW hY hB
    have hW' : ∀ c : TorusBond (n * R.params.side), c.1 ∈ supBall o (((ρ + 8 * R.params.side : ℕ) : ℝ) + m) →
        c.1 + unitStep (n * R.params.side) c.2 ∈ supBall o (((ρ + 8 * R.params.side : ℕ) : ℝ) + m) →
          W c.1 c.2 = W' c.1 c.2 :=
      fun c h1 h2 => (hW c h1 h2).1
    have hNN : ∑ y ∈ As, siteScore A.score Yt' ωt' y = ∑ y ∈ As, siteScore A.score Yt ωt y := by
      refine Finset.sum_congr rfl fun y hy => ?_
      have hin : y ∈ supBall o (((ρ + 8 * R.params.side : ℕ) : ℝ) + m) := by
        rw [hAs] at hy
        obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.mp hy
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have h1 := hsite i hi y hyi
        have h2 : TorusFields.supDist y o ≤ ρ + 8 * R.params.side + m := by omega
        exact_mod_cast h2
      obtain ⟨h1, h2⟩ := hY y hin
      unfold siteScore
      by_cases h : y ∈ Yt
      · rw [dif_pos h, dif_pos (h1.mp h), h2 h (h1.mp h)]
      · rw [dif_neg h, dif_neg (fun h' => h (h1.mpr h'))]
    obtain ⟨N, hN⟩ : ∃ N, N = 1 + ∑ y ∈ As, siteScore A.score Yt ωt y := ⟨_, rfl⟩
    have hN1' : 1 ≤ N := by
      rw [hN]
      exact hN1 Yt ωt
    have he : 0 ≤ Real.exp (-(R.params.decayRate * (m : ℝ))) := (Real.exp_pos _).le
    have e₁ : ∏ i ∈ J, liveCaseFunction (centeredSupportResponse A V (f i)) W Yt ωt bad (clampBasesToBlocks b) =
        ∏ i ∈ J, centeredSupportResponse A V (f i) W Yt ωt bad (clampBasesToBlocks b) :=
      Finset.prod_congr rfl fun i _ => by
        unfold liveCaseFunction
        rw [if_pos hl]
    have e₂ : ∏ i ∈ J, liveCaseFunction (centeredSupportResponse A V (f i)) W' Yt' ωt' bad' (clampBasesToBlocks b') =
        ∏ i ∈ J, centeredSupportResponse A V (f i) W' Yt' ωt' bad' (clampBasesToBlocks b') :=
      Finset.prod_congr rfl fun i _ => by
        unfold liveCaseFunction
        rw [if_pos hl']
    show |∏ i ∈ J, liveCaseFunction (centeredSupportResponse A V (f i)) W Yt ωt bad (clampBasesToBlocks b) -
      ∏ i ∈ J, liveCaseFunction (centeredSupportResponse A V (f i)) W' Yt' ωt' bad' (clampBasesToBlocks b')| ≤ _
    rw [e₁, e₂]
    have hmain := abs_prod_sub_prod_le J (fun i => centeredSupportResponse A V (f i) W Yt ωt bad (clampBasesToBlocks b))
      (fun i => centeredSupportResponse A V (f i) W' Yt' ωt' bad' (clampBasesToBlocks b')) (M := cc * N)
      (e := Real.exp (-(R.params.decayRate * (m : ℝ)))) (by positivity) he
      (fun i hi => by
        rw [hN]
        exact size i hi _ _ _ _ _ hl)
      (fun i hi => by
        rw [hN, ← hNN]
        exact size i hi _ _ _ _ _ hl')
      (fun i hi => by
        refine (centeredSupportResponse_sub_le hLoc hSc hfit hres hb hn V (f i) (hs i hi) (hsite i hi) hm bad bad'
          hl hl' hW' (fun y hy => hY y hy) (fun c hc => hB c hc)).trans ?_
        rw [← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right ?_ he
        have h1 : ∑ y ∈ lowerSites (f i), (1 + siteScore A.score Yt ωt y) ≤ ∑ _y ∈ lowerSites (f i), N := by
          refine Finset.sum_le_sum fun y hy => ?_
          rw [hN]
          have := Finset.single_le_sum (f := fun y => siteScore A.score Yt ωt y)
            (fun y _ => siteScore_nonneg_of hs₀ Yt ωt y) (hsub i hi hy)
          linarith
        refine h1.trans ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        have h2 : ((lowerSites (f i)).card : ℝ) ≤ cc := by
          have := hcard i hi
          have h3 : 0 ≤ 4 * A.responseParams.C₀ * κ := by positivity
          rw [hcc]
          linarith
        exact mul_le_mul_of_nonneg_right h2 (by linarith))
    refine hmain.trans ?_
    rw [mul_pow, ← hN]
    have h0 : 0 ≤ N := by linarith
    have h3 : 0 ≤ cc ^ J.card * N ^ J.card := by positivity
    have h4 : (J.card : ℝ) * (cc ^ J.card * N ^ J.card) ≤ ((J.card : ℝ) + 1) * cc ^ J.card * N ^ J.card := by
      nlinarith
    exact mul_le_mul_of_nonneg_right (by linarith) he
end Products
section SupportSites
variable {k : ℕ}
private theorem exists_mem_offsetCube_of_mem_supportSites (hP : supportSitesLocationStatement) {L : ℕ} [NeZero L]
    (hL : Odd L) (P : LevelData k) {R d : ℝ} (hF : P.SupAdmissible L R d) {u : ℕ} (hu : u ≤ P.scaleLevel) (i : Fin k)
    {y : TorusSite (P.sideAt L u)} (hy : y ∈ P.supportSites L u i) :
    ∃ z ∈ offsetCube (⌈R * (L : ℝ) ^ (P.scaleLevel - u)⌉₊ + 2), ∀ a, y a =
      ((round (P.center a * (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ u) : ℤ) : ZMod (P.sideAt L u)) +
        ((z a : ℤ) : ZMod (P.sideAt L u)) := by apply _root_.YangMills.SharedProofs.p54227 <;> assumption
private theorem weightNorm_testWeight_congr (P : LevelData k) (L : ℕ) (i : Fin k) {t u N N' : ℕ} (ht : t = u)
    (hN : N = N') :
    weightNorm L t (P.testWeight L i (fineSide L t N)) = weightNorm L u (P.testWeight L i (fineSide L u N')) := by
  subst ht hN
  rfl
private theorem card_weightSupportSites_congr (P : LevelData k) (L : ℕ) [NeZero L] (i : Fin k) {t u N N' : ℕ}
    [NeZero N] [NeZero N'] (ht : t = u) (hN : N = N') :
    (weightSupportSites L t N (P.testWeight L i (fineSide L t N))).card =
      (weightSupportSites L u N' (P.testWeight L i (fineSide L u N'))).card := by
  subst ht hN
  rfl
end SupportSites
section Stages
private theorem hullDecayRate_nonneg {Tb : ParameterAssignment} (h : Tb.Admissible) : 0 ≤ hullDecayRate Tb := by apply _root_.YangMills.SharedProofs.p10157 <;> assumption
end Stages
section Points
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem stageOnFlow_of_le {j : ℕ} (hj : j ≤ S.data.windowLevel) :
    StageOnFlow Λ.table Λ.response Λ.floor S.β j ⟨S.tower.stage j, S.resp j⟩ := by apply _root_.YangMills.SharedProofs.p6811 <;> assumption
private theorem stage_succ_densities {j : ℕ} (hj : j + 1 ≤ S.data.windowLevel) :
    S.tower.densities j = (S.tower.stage j).toStepSetup.renormalizedDensity Λ.table.lam ∧
      S.tower.siteDensities (S.tower.stage j).toStepSetup = (S.tower.stage j).toStepSetup.stateDensity Λ.table.lam ∧
      ∀ ω, (S.resp (j + 1)).score ω = coarseLabelScore (S.resp j).responseParams.s₁ (S.resp j).score ω := by apply _root_.YangMills.SharedProofs.p36968 <;> assumption
private theorem resp_score_eq_labelSize (u : ℕ) (hu : u ≤ S.data.windowLevel) :
    (S.resp u).score = labelSize S.tower Λ.response.s₁ u := by apply _root_.YangMills.SharedProofs.p9388 <;> assumption
private theorem towerFollowsFlow_windowLevel : TowerFollowsFlow S.tower S.β S.data.windowLevel := by apply _root_.YangMills.SharedProofs.p11317 <;> assumption
private theorem hullChainAtLevel_of_le (hg : 0 < Λ.g) (hfl : Λ.floor ≤ (Λ.g ^ 2)⁻¹) {u N : ℕ}
    (hu : u ≤ S.data.windowLevel) (hN : N = S.data.sideAt Λ.stepParams.side u) :
    HullChainAtLevel Λ.table Λ.floor Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower u N where
  chain :=
    { g_pos := hg
      le_inv_sq := hfl
      upper_le := S.window_le
      isFirst := S.passage
      volume_le := S.side_le
      follows := towerFollowsFlow_windowLevel S
      depth_bottom := S.startsAtWilson.depth_eq
      functional_bottom := S.startsAtWilson.functional_eq
      anchor_bottom := (stageOnFlow_of_le S (Nat.zero_le _)).onFamily.onFamily.anchorRadius_eq
      cutoff_bottom := S.isCutoff
      marks := S.marksMeasurable
      expansions := fun j hj => (stageOnFlow_of_le S hj).onFamily.onFamily.isStep.1
      reads_flow :=
        { startsAtWilson := S.startsAtWilson
          coupling_eq := towerFollowsFlow_windowLevel S
          onFamily := fun j hj => (stageOnFlow_of_le S hj).onFamily.onFamily
          siteDensities_eq := fun j hj => (stage_succ_densities S hj).2.1
          densities_eq := fun j hj => (stage_succ_densities S hj).1 } }
  le := hu
  side_eq := by
    rw [hN]
    show S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - u) = fineSide _ _ _
    rw [fineSide_eq]
    rfl
private theorem sideAtLevel_succ_mul {u : ℕ} (hu : u + 1 ≤ S.data.windowLevel) :
    S.sideAtLevel (u + 1) * Λ.stepParams.side = S.data.sideAt Λ.stepParams.side u := by
  show fineSide _ _ _ * _ = _
  rw [fineSide_eq]
  unfold LevelData.sideAt
  have : S.data.windowLevel - u = (S.data.windowLevel - (u + 1)) + 1 := by omega
  rw [this, pow_succ, mul_assoc]
abbrev _root_.YangMills.DeltaSharedProofs.p502146 := @sideAtLevel_succ_mul
private theorem sideAtLevel_eq (u : ℕ) : S.sideAtLevel u = S.data.sideAt Λ.stepParams.side u := by apply _root_.YangMills.DeltaSharedProofs.p7007 <;> assumption
private theorem isBlockTorusSide_sideAtLevel (hfit : Λ.stepParams.Admissible) (u : ℕ) :
    IsBlockTorusSide Λ.stepParams (S.sideAtLevel u) := by apply _root_.YangMills.SharedProofs.p591 <;> assumption
private theorem supDist_originSite_le (hP : supportSitesLocationStatement) (hL : Odd Λ.stepParams.side) {u : ℕ}
    (hu : u ≤ S.data.scaleLevel) (i : Fin Λ.k) {t N : ℕ} [NeZero N] (ht : t = u)
    (hN : N = S.data.sideAt Λ.stepParams.side u) {y : TorusSite N}
    (hy : y ∈ weightSupportSites Λ.stepParams.side t N (S.weight i (fineSide Λ.stepParams.side t N))) :
    TorusFields.supDist y (S.originSite u N) ≤ S.supportRadius u := by
  subst ht hN
  obtain ⟨z, hz, hyz⟩ := exists_mem_offsetCube_of_mem_supportSites hP hL S.data S.supAdmissible hu i hy
  have e : y = S.originSite t _ + siteOfInt z := by
    funext a
    exact hyz a
  rw [e, supDist_comm]
  refine supDist_add_siteOfInt_le _ _ _ fun a => ?_
  unfold offsetCube at hz
  have h1 := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hz a)
  unfold MomentPoint.supportRadius
  omega
end Points
section Samples
variable {R : StepSetup} {n : ℕ} [NeZero n] {A : ResponseSetup R}
private theorem measurableSet_isLiveState (hrow : R.HasExpansions) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) :
    MeasurableSet {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) |
      IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} := by apply _root_.YangMills.SharedProofs.p6018 <;> assumption
private theorem measurable_bondScore_joint (hS : BondScoreProperties) (hfit : R.params.Admissible)
    (Yt : Finset (TorusSite (n * R.params.side))) (c : TorusBond n) :
    Measurable fun p : (TorusField (n * R.params.side) × (Yt → R.labels.Ω)) × StepOutcome R.params n =>
      bondScore R.params R.coupling p.1.1 p.2.2.1 (clampBasesToBlocks p.2.1) c := by
  classical
  have hsum : (fun p : (TorusField (n * R.params.side) × (Yt → R.labels.Ω)) × StepOutcome R.params n =>
      bondScore R.params R.coupling p.1.1 p.2.2.1 (clampBasesToBlocks p.2.1) c) = fun p =>
      ∑ b : BaseChoice R.params.side n,
        if p.2.1 = b then bondScore R.params R.coupling p.1.1 p.2.2.1 (clampBasesToBlocks b) c else 0 := by
    funext p
    simp
  rw [hsum]
  refine Finset.measurable_sum _ fun b _ => ?_
  have hset : MeasurableSet {p : (TorusField (n * R.params.side) × (Yt → R.labels.Ω)) × StepOutcome R.params n |
      p.2.1 = b} :=
    (measurable_fst.comp measurable_snd) (show MeasurableSet ({b} : Set (BaseChoice R.params.side n)) from trivial)
  have h1 : Measurable fun p : (TorusField (n * R.params.side) × (Yt → R.labels.Ω)) × StepOutcome R.params n =>
      (p.1.1, p.2.2.1) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have h2 := ((hS R.params hfit R.coupling n (clampBasesToBlocks b) c).2.2.2.2).comp h1
  exact Measurable.ite hset h2 measurable_const
private theorem measurable_liveCase_joint (hS : BondScoreProperties) (hfit : R.params.Admissible)
    (hrow : R.HasExpansions) (hres : A.IsAdmissible) (hb : IsBlockTorusSide R.params (n * R.params.side))
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable fun p : (TorusField (n * R.params.side) × (Yt → R.labels.Ω)) × StepOutcome R.params n =>
      liveCaseFunction (centeredSupportResponse A p.2.2.1 f) p.1.1 Yt p.1.2 p.2.2.2 (clampBasesToBlocks p.2.1) := by
  classical
  have hl := measurableSet_isLiveState hrow hb Yt
  have hl' : MeasurableSet {p : (TorusField (n * R.params.side) × (Yt → R.labels.Ω)) × StepOutcome R.params n |
      IsLiveState R.params R.coupling R.labelWeight p.1.1 Yt p.1.2} :=
    measurable_fst hl
  obtain ⟨v, hv⟩ : ∃ v, v = caseMean R ∅ (trivialField n) (emptyCoarseState R)
      (supportResponseSum A (trivialField n) f) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = ∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
      A.cold (n * R.params.side) y (trivialField (n * R.params.side)) f := ⟨_, rfl⟩
  have e : (fun p : (TorusField (n * R.params.side) × (Yt → R.labels.Ω)) × StepOutcome R.params n =>
      liveCaseFunction (centeredSupportResponse A p.2.2.1 f) p.1.1 Yt p.1.2 p.2.2.2 (clampBasesToBlocks p.2.1)) =
      fun p =>
      ∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
          (if IsLiveState R.params R.coupling R.labelWeight p.1.1 Yt p.1.2 then
            A.hull (n * R.params.side) y p.1.1 Yt p.1.2 f else 0) +
        (if IsLiveState R.params R.coupling R.labelWeight p.1.1 Yt p.1.2 then
          R.params.coupling / 2 * A.coeff * ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
            blockMean R.params.side (R.depth + 1) n Y f *
              blockBondScores (R := R) p.1.1 p.2.2.1 (clampBasesToBlocks p.2.1) Y - d - v else 0) := by
    funext p
    have hX : centeredSupportResponse A p.2.2.1 f p.1.1 Yt p.1.2 p.2.2.2 (clampBasesToBlocks p.2.1) =
        supportResponseSum A p.2.2.1 f p.1.1 Yt p.1.2 p.2.2.2 (clampBasesToBlocks p.2.1) - v := by
      rw [hv]
      rfl
    unfold liveCaseFunction
    rw [hX]
    unfold supportResponseSum centeredHullResponse
    by_cases hp : IsLiveState R.params R.coupling R.labelWeight p.1.1 Yt p.1.2
    · simp only [if_pos hp, Finset.sum_sub_distrib, ← hd]
      ring
    · simp [hp]
  rw [e]
  have hsc : ∀ Y : TorusSite n, Measurable fun p : (TorusField (n * R.params.side) × (Yt → R.labels.Ω)) ×
      StepOutcome R.params n => blockBondScores (R := R) p.1.1 p.2.2.1 (clampBasesToBlocks p.2.1) Y := fun Y => by
    unfold blockBondScores
    exact Finset.measurable_sum _ fun i _ =>
      (measurable_bondScore_joint hS hfit Yt _).add (measurable_bondScore_joint hS hfit Yt _)
  refine (Finset.measurable_sum _ fun y _ => (hres.bounds.hull_borel _ hb y Yt f).comp measurable_fst).add
    (Measurable.ite hl' (((Measurable.const_mul (Finset.measurable_sum _ fun Y _ => (hsc Y).const_mul _) _).sub_const
      _).sub_const _) measurable_const)
private theorem stageState_fst {ℓ : StepParameters} (T : StageTower ℓ) :
    ∀ (s n : ℕ) [NeZero n] (w : MarkedSample ℓ s n), (stageState T s n w).1 = topField ℓ s n w
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem measurable_caseLift {ℓ : StepParameters} (T : StageTower ℓ) (u n : ℕ) [NeZero n]
    (hSt : Measurable (stageState T u (n * ℓ.side))) (Φ : TorusField n → CaseFunction (T.stage u).toStepSetup n)
    (hΦ : ∀ Y : Finset (TorusSite (n * ℓ.side)),
      Measurable fun p : (TorusField (n * ℓ.side) × (Y → (T.stage u).labels.Ω)) × StepOutcome ℓ n =>
        Φ p.2.2.1 p.1.1 Y p.1.2 p.2.2.2 p.2.1) : Measurable (caseLift T u n Φ) := by
  have hG : Measurable fun r : StageState T u (n * ℓ.side) × StepOutcome ℓ n =>
      Φ r.2.2.1 r.1.1 r.1.2.1 r.1.2.2 r.2.2.2 r.2.1 :=
    BoxGaussian.measurable_prod_sigma_of_forall
      (Z := fun Y : Finset (TorusSite (n * ℓ.side)) => Y → (T.stage u).labels.Ω) hΦ
  have hm : Measurable fun x : MarkedSample ℓ (u + 1) n =>
      ((stageState T u (n * ℓ.side) x.1, x.2) : StageState T u (n * ℓ.side) × StepOutcome ℓ n) := by
    let _ := markedSampleMeasurableSpace ℓ u (n * ℓ.side)
    exact (hSt.comp measurable_fst).prodMk measurable_snd
  have e : caseLift T u n Φ = fun x : MarkedSample ℓ (u + 1) n =>
      Φ x.2.2.1 (stageState T u (n * ℓ.side) x.1).1 (stageState T u (n * ℓ.side) x.1).2.1
        (stageState T u (n * ℓ.side) x.1).2.2 x.2.2.2 x.2.1 := by
    funext x
    unfold caseLift
    rw [stageState_fst]
  rw [e]
  exact hG.comp hm
private theorem measurable_fieldWithStoredLinks (q : CoarseState R n) : Measurable q.fieldWithStoredLinks := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fieldWithStoredLinks <;> assumption
private theorem measurable_fillLabels (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable (q.fillLabels Yt) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fillLabels <;> assumption
private theorem caseIntegrable_of_abs_le {C : Finset (TorusSite n)} {V : TorusField n} {q : CoarseState R n}
    {F H : CaseFunction R n} {c : ℝ}
    (hF : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => F p.1 Yt p.2 bad b)
    (h1 : CaseIntegrable R C V q fun _ _ _ _ _ => 1) (hH : CaseIntegrable R C V q H)
    (hle : ∀ W Yt ωt bad b, |F W Yt ωt bad b| ≤ c * H W Yt ωt bad b) : CaseIntegrable R C V q F := by
  classical
  intro bad hbad Yt b
  have i1 := h1 bad hbad Yt b
  have iH := (hH bad hbad Yt b).const_mul c
  have e : (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      caseTerm R C V q F bad Yt b p.1 p.2) = fun p =>
      F (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b *
        caseTerm R C V q (fun _ _ _ _ _ => 1) bad Yt b p.1 p.2 := by
    funext p
    unfold caseTerm
    split_ifs
    · ring
    · simp
  refine iH.mono ?_ (Filter.Eventually.of_forall fun p => ?_)
  · rw [e]
    have hm : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
        F (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b :=
      (hF Yt bad b).comp (((measurable_fieldWithStoredLinks q).comp measurable_fst).prodMk
        ((measurable_fillLabels q Yt).comp measurable_snd))
    exact hm.aestronglyMeasurable.mul i1.aestronglyMeasurable
  · simp only [Real.norm_eq_abs]
    unfold caseTerm
    split_ifs
    · rw [abs_mul, ← mul_assoc, abs_mul, abs_mul]
      have h2 := hle (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b
      have h3 : c * H (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b ≤
          |c| * |H (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b| := by
        rw [← abs_mul]
        exact le_abs_self _
      exact mul_le_mul_of_nonneg_right (h2.trans h3) (abs_nonneg _)
    · simp
private theorem measurable_siteScore {Ω : Type} [MeasurableSpace Ω] {s : Ω → ℝ} (hs : Measurable s) {N : ℕ}
    (Y : Finset (TorusSite N)) (y : TorusSite N) : Measurable fun ω : Y → Ω => siteScore s Y ω y := by apply _root_.YangMills.SharedProofs.p56706 <;> assumption
private theorem one_add_pow_le_exp {x : ℝ} (hx : 0 ≤ x) (a : ℕ) :
    (1 + x) ^ a ≤ (a.factorial : ℝ) * Real.exp 1 * Real.exp x := by
  have h := Real.pow_div_factorial_le_exp (x := 1 + x) (by linarith) a
  have hf : (0 : ℝ) < a.factorial := by exact_mod_cast a.factorial_pos
  rw [div_le_iff₀ hf, Real.exp_add] at h
  linarith
private theorem isHullState_of_coarseStateWeight_pos (hH : CoarseHullIsHullState) (hFo : R.IsWellPosed)
    (hbs : IsBlockTorusSide R.params n) {V : TorusField n} {q : CoarseState R n}
    (hpos : 0 < coarseStateWeight R (hotCoreSites R V) V q) : IsHullState R.params R.nextRange V q.1 := by
  classical
  by_contra hno
  have hz : coarseStateMass R (hotCoreSites R V) V q = 0 := by
    unfold coarseStateMass
    refine Finset.sum_eq_zero fun bad _ => Finset.sum_eq_zero fun Yt _ => Finset.sum_eq_zero fun b _ => ?_
    have h0 : ∀ (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω),
        ¬ (IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
          coarseStateOf R (hotCoreSites R V) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) := by
      rintro W ν ⟨-, e⟩
      apply hno
      have e1 := congrArg Sigma.fst e
      rw [← e1]
      exact hH R.params hFo.admissible R.range R.nextRange hFo.range_le hFo.nextRange_ge n hbs.1 V bad Yt
    simp [h0]
  simp [coarseStateWeight, hz] at hpos
abbrev _root_.YangMills.SharedProofs.p64097 := @isHullState_of_coarseStateWeight_pos
end Samples
section Assembly
private abbrev StepVariableBounds (R : StepSetup) (A : ResponseSetup R) : Prop :=
  ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (V : TorusField n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)),
    weightNorm R.params.side (R.depth + 1) f ≤ 1 → weightNorm R.params.side R.depth f ≤ 1 → (upperSites f).Nonempty →
    (∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        liveCaseFunction (centeredSupportResponse A V f) p.1 Yt p.2 bad b) ∧
    IsGaugeInvariantCase (liveCaseFunction (centeredSupportResponse A V f)) ∧
    ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
      (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
      IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
      |centeredSupportResponse A V f W Yt ωt bad b| ≤ 4 * lowerSizeConst A f * meanSiteScore A.score (lowerSites f) Yt ωt
private abbrev StepLabelIntegrability (R : StepSetup) (A : ResponseSetup R) : Prop :=
  ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround → ∀ (S : Finset (TorusSite (n * R.params.side)))
    (h : (Yt : Finset (TorusSite (n * R.params.side))) → (Yt → R.labels.Ω) → ℝ), (∀ Yt, Measurable (h Yt)) →
    (∀ Yt ωt, |h Yt ωt| ≤ Real.exp (scoreSumOn A S Yt ωt)) →
    CaseIntegrable R G.cut G.coarse G.state fun _ Yt ωt _ _ => h Yt ωt
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem quasiLocal_at_point (hDr : Λ.table.Admissible) (hfit : Λ.stepParams.Admissible) (hg : 0 < Λ.g)
    (hfl : Λ.floor ≤ (Λ.g ^ 2)⁻¹) (hLoc : BondKernelLocality) (hSc : BondScoreProperties)
    (hP : supportSitesLocationStatement) (hD : forgetLastStepStatement) (hSt : StageStatesMeasurableStatement)
    (hH : CoarseHullIsHullState) {C₂ : ℕ → ℝ}
    (hSz : ∀ u ≤ S.data.scaleLevel, ∀ i : Fin Λ.k,
      weightNorm Λ.stepParams.side u (S.weight i (fineSide Λ.stepParams.side u (S.levelSide u))) ≤ 1 ∧
      ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) ≤
        C₂ 0 * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u)))
    (hVar : ∀ (R : StepSetup) (A : ResponseSetup R), A.responseParams = Λ.response →
      OnStepParameters Λ.table Λ.floor A → StepVariableBounds R A)
    (hLab : ∀ (R : StepSetup) (A : ResponseSetup R), A.responseParams = Λ.response →
      OnStepParameters Λ.table Λ.floor A → StepLabelIntegrability R A)
    (hLive : ∀ u ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide Λ.stepParams n → ∀ᵐ w ∂(S.law u n),
      IsLiveState Λ.stepParams (S.tower.stage u).coupling (S.tower.stage u).labelWeight (S.state u n w).1
        (S.state u n w).2.1 (S.state u n w).2.2)
    (hZ : ClusterExpansionOfAStep.CoarseWeightZeroOfFactorZero)
    (hGr : ∀ R : StepSetup, R.OnParameters Λ.table Λ.floor → R.IsWellPosed → ∀ (n : ℕ) [NeZero n],
      IsBlockTorusSide R.params n → ∀ (V : TorusField n) (q : CoarseState R n), IsHullState R.params R.nextRange V q.1 →
      (∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) → (hotCaseGround R V q).IsHotCase)
    (hFo : ∀ u ≤ S.data.windowLevel, (S.tower.stage u).toStepSetup.IsWellPosed)
    {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    (hC : ∀ (β : ℝ) (K m : ℕ) (T : StageTower Λ.stepParams) (u n : ℕ) [NeZero n],
      HullChainAtLevel Λ.table Λ.floor Λ.g β K m T u n → ∀ (z : TorusSite n) (k : ℕ), 1 ≤ k →
      Integrable (fun w => siteSize T Λ.response.s₁ u n w z ^ k) (markedSampleLaw T β u n) ∧
      ∫ w, siteSize T Λ.response.s₁ u n w z ^ k ∂(markedSampleLaw T β u n) ≤
        C₀ ^ k * (k.factorial : ℝ) ^ 6 * Real.exp (-(hullDecayRate Λ.table * stageCoupling T u / 4)))
    {u : ℕ} (hu : u < S.data.scaleLevel) (J : Finset (Fin Λ.k)) :
    ∃ A' : Finset (TorusSite (S.sideAtLevel (u + 1) * Λ.stepParams.side)),
      (∀ V, IsQuasiLocalCaseFunction (S.tower.stage u).toStepSetup (S.originSite u _)
        (S.supportRadius u + 8 * Λ.stepParams.side) J.card
        ((J.card + 1) * (4 * Λ.response.C₀ * (|C₂ 0| * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u))) +
          |C₂ 0| * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u)) + 1) ^ J.card)
        A' (S.resp u).score (S.variableCaseProduct u J V)) ∧
      Measurable (caseLift S.tower u _ (S.variableCaseProduct u J)) ∧
      (∀ᵐ x ∂(markedSampleLaw S.tower S.β (u + 1) (S.sideAtLevel (u + 1))),
        CaseIntegrableAtSample S.tower u _ (S.variableCaseProduct u J) x) ∧
      ∫⁻ x, ENNReal.ofReal (supportWeightOfSample S.tower u _ A' (S.resp u).score x)
          ∂(markedSampleLaw S.tower S.β (u + 1) (S.sideAtLevel (u + 1))) ≤
        ENNReal.ofReal (1 + J.card * (|C₂ 0| * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u))) * C₀) := by
  classical
  have hsK : S.data.scaleLevel ≤ S.data.windowLevel := S.supAdmissible.scaleLevel_le
  have hKu : u ≤ S.data.windowLevel := by omega
  have hK1 : u + 1 ≤ S.data.windowLevel := by omega
  have hst := stageOnFlow_of_le S hKu
  have hAK : (S.resp u).responseParams = Λ.response := hst.params_eq
  have hAt : OnStepParameters Λ.table Λ.floor (S.resp u) := hst.onFamily
  have hlev : (S.tower.stage u).toStepSetup.depth = u := hst.depth_eq
  have hres : (S.resp u).IsAdmissible := hAt.admissible
  have hrow : (S.tower.stage u).toStepSetup.HasExpansions := hAt.onFamily.isStep.1
  have hLpos : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hbsn : IsBlockTorusSide Λ.stepParams (S.sideAtLevel (u + 1)) := isBlockTorusSide_sideAtLevel S hfit (u + 1)
  have hn₀ : Λ.stepParams.n₀ ≤ S.sideAtLevel (u + 1) := le_trans (Nat.le_mul_of_pos_left _ hLpos) hbsn.2
  have hn16 : 16 ≤ S.sideAtLevel (u + 1) := by
    have := hfit.n₀_ge
    omega
  have hb : IsBlockTorusSide Λ.stepParams (S.sideAtLevel (u + 1) * Λ.stepParams.side) :=
    ⟨Dvd.intro_left _ rfl, hbsn.2.trans (Nat.le_mul_of_pos_right _ hLpos)⟩
  have hside : S.sideAtLevel (u + 1) * Λ.stepParams.side = S.data.sideAt Λ.stepParams.side u :=
    sideAtLevel_succ_mul S hK1
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = |C₂ 0| * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u)) := ⟨_, rfl⟩
  rw [← hκ]
  have hκ0 : 0 ≤ κ := by
    rw [hκ]
    positivity
  obtain ⟨f, hf⟩ : ∃ f : Fin Λ.k → PlaquetteWeight (fineSide Λ.stepParams.side
      ((S.tower.stage u).toStepSetup.depth + 1) (S.sideAtLevel (u + 1))),
      f = fun i => S.weight i _ := ⟨_, rfl⟩
  have hs0 : ∀ i, weightNorm Λ.stepParams.side (S.tower.stage u).toStepSetup.depth (f i) ≤ 1 := fun i => by
    rw [hf]
    exact (weightNorm_testWeight_congr S.data Λ.stepParams.side i hlev hside).le.trans (hSz u hu.le i).1
  have hs1 : ∀ i, weightNorm Λ.stepParams.side ((S.tower.stage u).toStepSetup.depth + 1) (f i) ≤ 1 := fun i => by
    rw [hf]
    exact (weightNorm_testWeight_congr S.data Λ.stepParams.side i (by rw [hlev]) (sideAtLevel_eq S (u + 1))).le.trans
      (hSz (u + 1) hu i).1
  have hcard : ∀ i, ((lowerSites (R := (S.tower.stage u).toStepSetup) (f i)).card : ℝ) ≤ κ := fun i => by
    rw [hf]
    have e : (lowerSites (R := (S.tower.stage u).toStepSetup) (S.weight i (fineSide Λ.stepParams.side
        ((S.tower.stage u).toStepSetup.depth + 1) (S.sideAtLevel (u + 1))))).card =
        (S.data.supportSites Λ.stepParams.side u i).card :=
      card_weightSupportSites_congr S.data Λ.stepParams.side i hlev hside
    rw [e, hκ]
    refine (hSz u hu.le i).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hne : ∀ i, (upperSites (R := (S.tower.stage u).toStepSetup) (f i)).Nonempty := fun i => by
    rw [hf]
    have e : (upperSites (R := (S.tower.stage u).toStepSetup) (S.weight i (fineSide Λ.stepParams.side
        ((S.tower.stage u).toStepSetup.depth + 1) (S.sideAtLevel (u + 1))))).card =
        (S.data.supportSites Λ.stepParams.side (u + 1) i).card :=
      card_weightSupportSites_congr S.data Λ.stepParams.side i (by rw [hlev]) (sideAtLevel_eq S (u + 1))
    have h1 := (hP Λ.stepParams.side hfit.L_odd Λ.k S.data (u + 1) hK1 i).2 (S.supAdmissible.exists_ne_zero i)
    exact Finset.card_pos.mp (by rw [e]; exact Finset.card_pos.mpr h1)
  have hsite : ∀ i, ∀ y ∈ lowerSites (R := (S.tower.stage u).toStepSetup) (f i),
      TorusFields.supDist y (S.originSite u (S.sideAtLevel (u + 1) * Λ.stepParams.side)) ≤ S.supportRadius u := by
    intro i y hy
    rw [hf] at hy
    exact supDist_originSite_le S hP hfit.L_odd hu.le i hlev hside hy
  have hvar := fun V i => hVar _ (S.resp u) hAK hAt (S.sideAtLevel (u + 1)) hn₀ V (f i) (hs1 i) (hs0 i) (hne i)
  have hfar : ∀ V, IsQuasiLocalCaseFunction (S.tower.stage u).toStepSetup
      (S.originSite u (S.sideAtLevel (u + 1) * Λ.stepParams.side)) (S.supportRadius u + 8 * Λ.stepParams.side) J.card
      ((J.card + 1) * (4 * Λ.response.C₀ * κ + κ + 1) ^ J.card)
      (J.biUnion fun i => lowerSites (R := (S.tower.stage u).toStepSetup) (f i)) (S.resp u).score
      (S.variableCaseProduct u J V) := by
    intro V
    have h := prod_isQuasiLocalCaseFunction hLoc hSc hfit hres hb hn16 V J f hκ0 (fun i _ => hs0 i)
      (fun i _ => hsite i) (fun i _ => hcard i) (fun i _ Yt bad b => (hvar V i).1 Yt bad b)
      (fun i _ => (hvar V i).2.1) (fun i _ W Yt ωt bad b hl => (hvar V i).2.2 W Yt ωt bad b hl)
    rw [hAK] at h
    have e : S.variableCaseProduct u J V = fun W Yt ωt bad b =>
        ∏ i ∈ J, liveCaseFunction (centeredSupportResponse (S.resp u) V (f i)) W Yt ωt bad (clampBasesToBlocks b) := by
      rw [hf]
      rfl
    rw [e]
    exact h
  refine ⟨J.biUnion fun i => lowerSites (R := (S.tower.stage u).toStepSetup) (f i), hfar, ?_, ?_, ?_⟩
  · refine measurable_caseLift S.tower u (S.sideAtLevel (u + 1)) (hSt Λ.stepParams hfit S.tower u _) _ fun Y => ?_
    have h : ∀ i ∈ J, Measurable fun p : (TorusField (S.sideAtLevel (u + 1) * Λ.stepParams.side) ×
        (Y → (S.tower.stage u).labels.Ω)) × StepOutcome Λ.stepParams (S.sideAtLevel (u + 1)) =>
        liveCaseFunction (centeredSupportResponse (S.resp u) p.2.2.1 (f i)) p.1.1 Y p.1.2 p.2.2.2
          (clampBasesToBlocks p.2.1) := fun i _ =>
      measurable_liveCase_joint hSc hfit hrow hres hb (f i) Y
    have h2 := Finset.measurable_prod J h
    rw [hf] at h2
    exact h2
  · have hC0 : 0 ≤ Λ.response.C₀ := by
      have h := hres.params_admissible
      have h1 := h.C₀_eq
      have h2 := h.N₀_nonneg
      have h3 := h.Kc_ge
      have h4 := hfit.a_ge
      rw [← hAK]
      linarith
    have hlive := hLive (u + 1) hK1 (S.sideAtLevel (u + 1)) hbsn
    refine hlive.mono fun x hx => ?_
    obtain ⟨V, hV⟩ : ∃ V, V = x.2.2.1 := ⟨_, rfl⟩
    have hpos : 0 < coarseStateWeight (S.tower.stage u).toStepSetup
        (hotCoreSites (S.tower.stage u).toStepSetup x.2.2.1) x.2.2.1
        (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2 := by
      have h2 : 0 < coarseWeightExpansion (S.tower.stage u).toStepSetup (S.sideAtLevel (u + 1)) x.2.2.1
          (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2.1
          (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2.2 := hx.2
      unfold coarseWeightExpansion at h2
      rw [dif_neg (NeZero.ne _)] at h2
      exact h2
    have hFoU := hFo u hKu
    have hhull := isHullState_of_coarseStateWeight_pos hH hFoU hbsn hpos
    have hΦ : ∀ X ∈ chainComponents (S.tower.stage u).toStepSetup.nextRange
        (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2.1,
        coarseFactor x.2.2.1 (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2 X ≠ 0 := by
      intro X hX h0
      have := hZ _ hFoU _ hbsn x.2.2.1 _ hhull ⟨X, hX, h0⟩
      linarith
    have hG : (hotCaseGround (S.tower.stage u).toStepSetup x.2.2.1
        (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2).IsAdmissibleGround :=
      Or.inr (hGr _ hAt.onFamily hFoU _ hbsn _ _ hhull hΦ)
    have hlab := hLab _ (S.resp u) hAK hAt (S.sideAtLevel (u + 1)) _ hG
    have h1 := hlab ∅ (fun _ _ => 1) (fun _ => measurable_const) (fun Yt ωt => by simp [scoreSumOn])
    have hE := hlab (J.biUnion fun i => lowerSites (R := (S.tower.stage u).toStepSetup) (f i))
      (fun Yt ωt => Real.exp (scoreSumOn (S.resp u)
        (J.biUnion fun i => lowerSites (R := (S.tower.stage u).toStepSetup) (f i)) Yt ωt))
      (fun Yt => Real.measurable_exp.comp (Finset.measurable_sum _ fun y _ =>
        measurable_siteScore hres.price.borel Yt y))
      (fun Yt ωt => by rw [abs_of_pos (Real.exp_pos _)])
    have hSz0 : 0 ≤ ((J.card : ℝ) + 1) * (4 * Λ.response.C₀ * κ + κ + 1) ^ J.card := by positivity
    refine caseIntegrable_of_abs_le
      (c := ((J.card : ℝ) + 1) * (4 * Λ.response.C₀ * κ + κ + 1) ^ J.card * ((J.card.factorial : ℝ) * Real.exp 1))
      (hfar x.2.2.1).measurable h1 hE fun W Yt ωt bad b => ?_
    have hb₁ := (hfar x.2.2.1).abs_le W Yt ωt bad b
    have hx0 : 0 ≤ ∑ y ∈ J.biUnion fun i => lowerSites (R := (S.tower.stage u).toStepSetup) (f i),
        siteScore (S.resp u).score Yt ωt y :=
      Finset.sum_nonneg fun y _ => siteScore_nonneg_of hres.price.nonneg Yt ωt y
    have hb₂ := one_add_pow_le_exp hx0 J.card
    refine hb₁.trans ((mul_le_mul_of_nonneg_left hb₂ hSz0).trans (le_of_eq ?_))
    unfold scoreSumOn
    ring
  · have hAtL := hullChainAtLevel_of_le S hg hfl hKu hside
    have hpres := (hD Λ.stepParams hfit hfit.depth_lt S.tower S.isCutoff S.marksMeasurable S.β u
      (S.sideAtLevel (u + 1))).2
    have hprob : IsProbabilityMeasure (markedSampleLaw S.tower S.β u (S.sideAtLevel (u + 1) * Λ.stepParams.side)) :=
      (hD Λ.stepParams hfit hfit.depth_lt S.tower S.isCutoff S.marksMeasurable S.β u
        (S.sideAtLevel (u + 1) * Λ.stepParams.side)).1
    have hsc := resp_score_eq_labelSize S u hKu
    have hval : ∀ (w : MarkedSample Λ.stepParams u (S.sideAtLevel (u + 1) * Λ.stepParams.side))
        (y : TorusSite (S.sideAtLevel (u + 1) * Λ.stepParams.side)),
        siteSize S.tower Λ.response.s₁ u _ w y ^ 1 =
          siteScore (S.resp u).score (stageState S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side) w).2.1
            (stageState S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side) w).2.2 y := by
      intro w y
      rw [pow_one, hsc]
      rfl
    have hint : ∀ y : TorusSite (S.sideAtLevel (u + 1) * Λ.stepParams.side), Integrable (fun w =>
        siteScore (S.resp u).score (stageState S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side) w).2.1
          (stageState S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side) w).2.2 y)
        (markedSampleLaw S.tower S.β u (S.sideAtLevel (u + 1) * Λ.stepParams.side)) := fun y => by
      have h := (hC S.β S.data.windowLevel S.data.sideExponent S.tower u _ hAtL y 1 le_rfl).1
      simpa only [hval] using h
    have hbd : ∀ y : TorusSite (S.sideAtLevel (u + 1) * Λ.stepParams.side), ∫ w, siteScore (S.resp u).score
        (stageState S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side) w).2.1
        (stageState S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side) w).2.2 y
        ∂(markedSampleLaw S.tower S.β u (S.sideAtLevel (u + 1) * Λ.stepParams.side)) ≤ C₀ := fun y => by
      have h := (hC S.β S.data.windowLevel S.data.sideExponent S.tower u _ hAtL y 1 le_rfl).2
      simp only [hval] at h
      refine h.trans ?_
      have hexp : Real.exp (-(hullDecayRate Λ.table * stageCoupling S.tower u / 4)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have hx : Λ.floor ≤ stageCoupling S.tower u := hAt.onFamily.le_coupling
        have hy0 : (0 : ℝ) ≤ Λ.floor := zero_le_one.trans hfit.y₁_ge
        have := mul_nonneg (hullDecayRate_nonneg hDr) (hy0.trans hx)
        linarith
      simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_pow, mul_one]
      exact mul_le_of_le_one_right (by linarith) hexp
    generalize hAs : (J.biUnion fun i => lowerSites (R := (S.tower.stage u).toStepSetup) (f i)) = As
    have hgi : Integrable (fun w => 1 + ∑ y ∈ As, siteScore (S.resp u).score
        (stageState S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side) w).2.1
        (stageState S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side) w).2.2 y)
        (markedSampleLaw S.tower S.β u (S.sideAtLevel (u + 1) * Λ.stepParams.side)) :=
      (integrable_const 1).add (integrable_finsetSum _ fun y _ => hint y)
    have hlint : ∫⁻ x, ENNReal.ofReal (supportWeightOfSample S.tower u _ As (S.resp u).score x)
          ∂(markedSampleLaw S.tower S.β (u + 1) (S.sideAtLevel (u + 1))) =
        ∫⁻ w, ENNReal.ofReal (1 + ∑ y ∈ As, siteScore (S.resp u).score
          (stageState S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side) w).2.1
          (stageState S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side) w).2.2 y)
          ∂(markedSampleLaw S.tower S.β u (S.sideAtLevel (u + 1) * Λ.stepParams.side)) := by
      have hae : AEMeasurable (fun w => ENNReal.ofReal (1 + ∑ y ∈ As, siteScore (S.resp u).score
          (stageState S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side) w).2.1
          (stageState S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side) w).2.2 y))
          (Measure.map (fun x : MarkedSample Λ.stepParams (u + 1) (S.sideAtLevel (u + 1)) => x.1)
            (markedSampleLaw S.tower S.β (u + 1) (S.sideAtLevel (u + 1)))) := by
        rw [hpres.map_eq]
        exact hgi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      have h := lintegral_map' hae hpres.measurable.aemeasurable
      rw [hpres.map_eq] at h
      exact h.symm
    rw [hlint, ← ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall fun w => ?_)]
    · refine ENNReal.ofReal_le_ofReal ?_
      rw [integral_add (integrable_const 1) (integrable_finsetSum _ fun y _ => hint y), integral_const,
        integral_finsetSum _ fun y _ => hint y]
      simp only [probReal_univ, smul_eq_mul, mul_one]
      have h1 : ∑ y ∈ As, ∫ w, siteScore (S.resp u).score
          (stageState S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side) w).2.1
          (stageState S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side) w).2.2 y
          ∂(markedSampleLaw S.tower S.β u (S.sideAtLevel (u + 1) * Λ.stepParams.side)) ≤ (As.card : ℝ) * C₀ := by
        refine (Finset.sum_le_sum fun y _ => hbd y).trans (le_of_eq ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
      have h2 : (As.card : ℝ) ≤ J.card * κ := by
        have h3 : As.card ≤ ∑ i ∈ J, (lowerSites (R := (S.tower.stage u).toStepSetup) (f i)).card := by
          rw [← hAs]
          exact Finset.card_biUnion_le
        have h4 : ((∑ i ∈ J, (lowerSites (R := (S.tower.stage u).toStepSetup) (f i)).card : ℕ) : ℝ) ≤ J.card * κ := by
          push_cast
          refine (Finset.sum_le_sum fun i _ => hcard i).trans (le_of_eq ?_)
          rw [Finset.sum_const, nsmul_eq_mul]
        exact (by exact_mod_cast h3 : (As.card : ℝ) ≤
          ((∑ i ∈ J, (lowerSites (R := (S.tower.stage u).toStepSetup) (f i)).card : ℕ) : ℝ)).trans h4
      have h5 := mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ C₀)
      linarith
    · have : 0 ≤ ∑ y ∈ As, siteScore (S.resp u).score
          (stageState S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side) w).2.1
          (stageState S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side) w).2.2 y :=
        Finset.sum_nonneg fun y _ => siteScore_nonneg_of hres.price.nonneg _ _ y
      show (0 : ℝ) ≤ _
      linarith
end Assembly
section Parameters
private theorem forAllHull_of_forAll {Q : MomentParameters → Prop} (h : ForAllParameters Q) :
    ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem forAllHull_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁)
    (h₂ : ForAllHullParameters Q₂) : ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem forAllHull_of_holdsAtEveryStep {P : ParameterAssignment → ∀ R : StepSetup, ResponseSetup R → Prop}
    (h : HoldsAtEveryStep P) :
    ForAllHullParameters fun Λ => ∀ (R : StepSetup) (A : ResponseSetup R), A.responseParams = Λ.response →
      OnStepParameters Λ.table Λ.floor A → P Λ.table R A := by
  intro a _
  obtain ⟨rt₀, hrt, H⟩ := h
  refine ⟨0, rt₀, 0, hrt, ?_⟩
  intro L _ _ Tb _ _ d₁ _ _ d₄ _
  refine ⟨0, ?_⟩
  intro Kr _ _ _ _ _
  obtain ⟨y₀, H⟩ := H Tb d₁ d₄ Kr
  refine ⟨y₀, ?_⟩
  intro y hy _ _ g _ _ k _ _ _ R d _
  exact H y hy
private theorem forAllHull_of_eventually_admissible {P : ParameterAssignment → ℝ → Prop}
    (h : ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → P T y) :
    ForAllHullParameters fun Λ => P Λ.table Λ.floor := by apply _root_.YangMills.SharedProofs.p14065 <;> assumption
private theorem forAllHull_of_eventually {P : ParameterAssignment → ResponseParameters → ℝ → ℝ → Prop}
    (h : EventuallyInParameters fun Tb Kr y => ∀ g : ℝ, P Tb Kr y g) :
    ForAllHullParameters fun Λ => P Λ.table Λ.response Λ.floor Λ.g := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, H⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, hrt, ?_⟩
  intro L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  obtain ⟨M, G⟩ := H L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  refine ⟨M, ?_⟩
  intro Kr k₁ k₂ k₃ k₄ k₅
  obtain ⟨y₀, Y⟩ := G Kr k₁ k₂ k₃ k₄ k₅
  refine ⟨y₀, ?_⟩
  intro y hy hrow hw g _ _ k _ _ _ R d _
  exact Y y hy hrow hw g
private theorem forAllHull_mono {Q₁ Q₂ : MomentParameters → Prop} (h : ForAllHullParameters Q₁)
    (f : ∀ Λ : MomentParameters, Λ.table.Admissible → Λ.stepParams.Admissible → 0 < Λ.g →
      Λ.floor ≤ (Λ.g ^ 2)⁻¹ → Q₁ Λ → Q₂ Λ) : ForAllHullParameters Q₂ := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, H⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, hrt, ?_⟩
  intro L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  obtain ⟨M, G⟩ := H L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  refine ⟨M, ?_⟩
  intro Kr k₁ k₂ k₃ k₄ k₅
  obtain ⟨y₀, Y⟩ := G Kr k₁ k₂ k₃ k₄ k₅
  refine ⟨max y₀ Tb.floorMin, ?_⟩
  intro y hy hrow hw g hg hgy k _ hk2 hk8 R d hd
  have hfit : (Tb.stepParameters y).Admissible := d₁.fits y ((le_max_right _ _).trans hy)
  exact f ⟨Tb, Kr, y, g, k, R, d⟩ d₁ hfit hg hgy (Y y ((le_max_left _ _).trans hy) hrow hw g hg hgy k hk2 hk8 R d hd)
end Parameters
theorem stepVariablesQuasiLocal (hW : weightsSitesBelowScaleStatement) (hV : supportResponseBoundStatement)
    (hFL : labelFunctionsIntegrableStatement) (hP : supportSitesLocationStatement) (hL : liveStatesStatement)
    (hM : siteSizeMomentStatement) (hLoc : BondKernelLocality) (hSc : BondScoreProperties)
    (hD : forgetLastStepStatement) (hSt : StageStatesMeasurableStatement) (hLv : StagesAreWellPosed)
    (hG : HullStateIsHotCase) (hZ : ClusterExpansionOfAStep.CoarseWeightZeroOfFactorZero) (hH : CoarseHullIsHullState) :
    stepVariablesQuasiLocalStatement := by
  unfold weightsSitesBelowScaleStatement ForAllPoints at hW
  unfold liveStatesStatement ForAllPoints at hL
  unfold supportResponseBoundStatement at hV
  unfold labelFunctionsIntegrableStatement at hFL
  unfold siteSizeMomentStatement at hM
  have h := forAllHull_and (forAllHull_of_forAll hW) (forAllHull_and (forAllHull_of_forAll hL)
    (forAllHull_and (forAllHull_of_holdsAtEveryStep hV) (forAllHull_and (forAllHull_of_holdsAtEveryStep hFL)
      (forAllHull_and (forAllHull_of_eventually_admissible hLv) (forAllHull_and (forAllHull_of_eventually_admissible hG)
        (forAllHull_of_eventually hM))))))
  refine forAllHull_mono h fun Λ hDr hfit hg hy hh => ?_
  obtain ⟨⟨C₂, _, _, _, _, Q₂⟩, ⟨_, _, _, _, _, Q₃⟩, Q₄, Q₅, Q₆, Q₇, C₀, hC₀, Q₈⟩ := hh
  intro S u hu J
  refine ⟨S.supportRadius u + 8 * Λ.stepParams.side,
    (J.card + 1) * (4 * Λ.response.C₀ * (|C₂ 0| * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u))) +
      |C₂ 0| * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u)) + 1) ^ J.card,
    1 + J.card * (|C₂ 0| * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u))) * C₀, ?_⟩
  rintro S' ⟨m, hp, hs, rfl⟩
  have fo : ∀ v ≤ (S.withSideExponent m hp hs).data.windowLevel,
      ((S.withSideExponent m hp hs).tower.stage v).toStepSetup.IsWellPosed := by
    intro v hv
    have h0 := Q₆ Λ.response S.β S.labelFacts S.initial S.isInitial S.data.windowLevel S.onFlow v hv
    have pack : ∀ z : StageWithResponse Λ.stepParams,
        z = flowStages Λ.table Λ.floor S.β S.labelFacts S.initial v → z.1.toStepSetup.IsWellPosed := by
      rintro _ rfl
      exact h0
    exact pack ⟨S.tower.stage v, S.resp v⟩ (S.stage_eq v hv)
  exact quasiLocal_at_point (S.withSideExponent m hp hs) hDr hfit hg hy hLoc hSc hP hD hSt hH (Q₂ _) Q₄ Q₅ (Q₃ _) hZ
    Q₇ fo hC₀ Q₈ hu J
end YangMills.Construction.MomentLaw
end
