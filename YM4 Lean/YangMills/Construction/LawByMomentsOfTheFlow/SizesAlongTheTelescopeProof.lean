import YangMills.Construction.LawByMomentsOfTheFlow.VariablesAreFarAtLiveStatesProof
import YangMills.Construction.LawByMomentsOfTheFlow.SizesAlongTheTelescope
import YangMills.Construction.LawByMomentsOfTheFlow.VariablesOfAPointSplitProof
import YangMills.Construction.ResponseInTheExpansion.MeanOfASupportOfSizeBelowGivenTheFieldOne
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open WeightedResponses ResponseInTheExpansion TorusLumps TorusFields StepSettings StepGas RenormalizationStepParameters FreeEnergies LevelTestFunctions
section WeightBounds
private theorem supportSites_card_congr {L : ℕ} [NeZero L] (w : ∀ m : ℕ, PlaquetteWeight m) {t t' n n' : ℕ} [NeZero n] [NeZero n']
    (ht : t = t') (hn : n = n') :
    (weightSupportSites L t n (w (fineSide L t n))).card = (weightSupportSites L t' n' (w (fineSide L t' n'))).card := by
  subst ht
  subst hn
  rfl
private theorem supportSites_depth_congr {L : ℕ} [NeZero L] (w : ∀ m : ℕ, PlaquetteWeight m) {t s : ℕ} (n : ℕ) [NeZero n] (h : t = s) :
    weightSupportSites L t n (w (fineSide L t n)) = weightSupportSites L s n (w (fineSide L s n)) := by apply _root_.YangMills.SharedProofs.p57791 <;> assumption
private theorem weightNorm_congr {L : ℕ} (w : ∀ m : ℕ, PlaquetteWeight m) {t t' m m' : ℕ} (ht : t = t') (hm : m = m') :
    weightNorm L t (w m) = weightNorm L t' (w m') := by
  subst ht
  subst hm
  rfl
private theorem fineSide_succ_congr {L t t' n n' : ℕ} (ht : t = t') (hn : n * L = n') :
    fineSide L (t + 1) n = fineSide L t' n' := by
  subst ht
  subst hn
  rfl
private theorem blockMean_eq_zero_of_not_mem (hMW : BlockMeanIsLinearAndLocal) {L : ℕ} [NeZero L] (hL : Odd L) {t n : ℕ} [NeZero n]
    {h : PlaquetteWeight (fineSide L t n)} {Y : TorusSite n} (hY : Y ∉ weightSupportSites L t n h) : blockMean L t n Y h = 0 := by
  classical
  obtain ⟨-, hlin, hread⟩ := hMW L hL t n Y
  have hz : ∀ p, IsPlaquetteAt L t Y p → h p = (fun _ => (0 : ℝ)) p := fun p hp => by
    by_contra hne
    exact hY (Finset.mem_filter.2 ⟨Finset.mem_univ _, p, hp, hne⟩)
  have e₁ := hread h (fun _ => 0) hz
  have e₂ := hlin 0 0 h h
  simp only [zero_mul, add_zero] at e₂
  rw [e₁]
  exact e₂
private theorem abs_stepSourceTerm_le (hS : BondScoreProperties) (hW : WeightsCloseToBlockMeans) (hM : BlockMeanIsLinearAndLocal)
    {ℓ : StepParameters} (hf : ℓ.Admissible) (x c : ℝ) (hc : |c| ≤ 2) (s : ℕ) {n : ℕ} [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n))
    (hz : weightNorm ℓ.side (s + 1) h ≤ 1) (W : TorusField (n * ℓ.side)) (d : StepOutcome ℓ n) :
    |stepSourceTerm ℓ x c s h W d| ≤ 16 * ℓ.coupling * ((weightSupportSites ℓ.side (s + 1) n h).card : ℝ) := by
  classical
  have ha : 0 < ℓ.coupling := by linarith [hf.a_ge]
  have hsc : ∀ b : TorusBond n, |bondScore ℓ x W d.2.1 d.1 b| ≤ 2 := fun b => (hS ℓ hf x n d.1 b).2.2.1 W d.2.1
  have hblock : ∀ Y : TorusSite n,
      |∑ i : Fin 4, (bondScore ℓ x W d.2.1 d.1 (Y, i) + bondScore ℓ x W d.2.1 d.1 (Y - unitStep n i, i))| ≤ 16 := fun Y => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h4 : ∀ i : Fin 4, |bondScore ℓ x W d.2.1 d.1 (Y, i) + bondScore ℓ x W d.2.1 d.1 (Y - unitStep n i, i)| ≤ 4 := fun i =>
      (abs_add_le _ _).trans (by linarith [hsc (Y, i), hsc (Y - unitStep n i, i)])
    calc _ ≤ ∑ _i : Fin 4, (4 : ℝ) := Finset.sum_le_sum fun i _ => h4 i
      _ = 16 := by norm_num
  have hterm : ∀ Y : TorusSite n, |blockMean ℓ.side (s + 1) n Y h *
      ∑ i : Fin 4, (bondScore ℓ x W d.2.1 d.1 (Y, i) + bondScore ℓ x W d.2.1 d.1 (Y - unitStep n i, i))| ≤ 16 := fun Y => by
    rw [abs_mul]
    have h1 : |blockMean ℓ.side (s + 1) n Y h| ≤ 1 :=
      ((hW ℓ.side hf.L_odd (s + 1) n Y).1 h).trans ((le_max_left _ _).trans hz)
    calc _ ≤ 1 * 16 := mul_le_mul h1 (hblock Y) (abs_nonneg _) zero_le_one
      _ = 16 := by norm_num
  have hsum : |∑ Y : TorusSite n, blockMean ℓ.side (s + 1) n Y h *
      ∑ i : Fin 4, (bondScore ℓ x W d.2.1 d.1 (Y, i) + bondScore ℓ x W d.2.1 d.1 (Y - unitStep n i, i))| ≤
      16 * ((weightSupportSites ℓ.side (s + 1) n h).card : ℝ) := by
    rw [← Finset.sum_subset (Finset.subset_univ (weightSupportSites ℓ.side (s + 1) n h)) fun Y _ hY => by
      rw [blockMean_eq_zero_of_not_mem hM hf.L_odd hY, zero_mul]]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _Y ∈ weightSupportSites ℓ.side (s + 1) n h, (16 : ℝ) := Finset.sum_le_sum fun Y _ => hterm Y
      _ = _ := by simp [mul_comm]
  unfold stepSourceTerm
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < ℓ.coupling / 2)]
  calc ℓ.coupling / 2 * |c| * _ ≤ ℓ.coupling / 2 * 2 * (16 * ((weightSupportSites ℓ.side (s + 1) n h).card : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hc (by positivity)) hsum (abs_nonneg _) (by positivity)
    _ = _ := by ring
private theorem stepMeanShift_eq_zero_of_empty {R : StepSetup} (A : ResponseSetup R) {n : ℕ} [NeZero n]
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (he : upperSites f = ∅) : stepMeanShift A f = 0 := by
  classical
  have hb : lowerSites f = ∅ := by
    have h := parentBlocks_lowerSites f
    rw [he] at h
    exact Finset.image_eq_empty.mp h
  have e : supportResponseSum A (trivialField n) f = fun _ _ _ _ _ => 0 := by
    funext W Yt ωt bad b
    unfold supportResponseSum
    have h1 : weightSupportSites R.params.side R.depth (n * R.params.side) f = ∅ := hb
    have h2 : weightSupportSites R.params.side (R.depth + 1) n f = ∅ := he
    rw [h1, h2]
    simp
  unfold stepMeanShift
  rw [e]
  simp [caseMean, caseIntegral, caseTerm]
private theorem abs_stepMeanShift_le {R : StepSetup} (A : ResponseSetup R) {n : ℕ} [NeZero n]
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (c : ℝ)
    (hc : 0 ≤ c) (hcard : ((lowerSites f).card : ℝ) = c) (hb : 0 ≤ A.responseParams.C₀ + 1 + 16 * R.params.coupling)
    (H : (upperSites f).Nonempty → |caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f)| ≤
      (A.responseParams.C₀ + 1 + 16 * R.params.coupling) * ((lowerSites f).card : ℝ)) :
    |stepMeanShift A f| ≤ (A.responseParams.C₀ + 1 + 16 * R.params.coupling) * c := by
  rcases (upperSites f).eq_empty_or_nonempty with he | hne
  · rw [stepMeanShift_eq_zero_of_empty A f he, abs_zero]
    exact mul_nonneg hb hc
  · have h := H hne
    rw [hcard] at h
    exact h
end WeightBounds
section Parameters
private theorem forAllParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁) (h₂ : ForAllParameters Q₂) :
    ForAllParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_mono {Q₁ Q₂ : MomentParameters → Prop} (h : ∀ Λ, Q₁ Λ → Q₂ Λ) (h₁ : ForAllParameters Q₁) :
    ForAllParameters Q₂ := by apply _root_.YangMills.SharedProofs.p432 <;> assumption
private theorem forAllParameters_admissible : ForAllParameters fun Λ => Λ.table.Admissible ∧ Λ.table.floorMin ≤ Λ.floor := by apply _root_.YangMills.SharedProofs.p9852 <;> assumption
private theorem forAllParameters_of_forAllSteps {P : ParameterAssignment → ∀ R : StepSetup, ResponseSetup R → Prop}
    (h : HoldsAtEveryStep P) :
    ForAllParameters fun Λ => ∀ (R : StepSetup) (A : ResponseSetup R), A.responseParams = Λ.response →
      OnStepParameters Λ.table Λ.floor A → P Λ.table R A := by
  obtain ⟨rt₀, hr, H⟩ := h
  intro a _
  refine ⟨0, rt₀, 0, hr, ?_⟩
  intro L _ _ Tb _ _ e3 _ _ e6 _ Kr _
  obtain ⟨y₁, Y₁⟩ := H Tb e3 e6 Kr
  exact ⟨y₁, fun y hy _ _ g _ _ k _ _ _ R d _ => Y₁ y hy⟩
end Parameters
section Points
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem stageOnFlow_at {u : ℕ} (hu : u ≤ S.data.windowLevel) :
    StageOnFlow Λ.table Λ.response Λ.floor S.β u (⟨S.tower.stage u, S.resp u⟩ : StageWithResponse Λ.stepParams) := by apply _root_.YangMills.SharedProofs.p21183 <;> assumption
private theorem sideAtLevel_eq (u : ℕ) : S.sideAtLevel u = S.levelSide u := by apply _root_.YangMills.SharedProofs.p7138 <;> assumption
private theorem sideAtLevel_succ_mul {u : ℕ} (h : u + 1 ≤ S.data.windowLevel) :
    S.sideAtLevel (u + 1) * Λ.stepParams.side = S.levelSide u := by apply _root_.YangMills.DeltaSharedProofs.p502146 <;> assumption
private theorem markedSampleLaw_cast {ℓ : StepParameters} (T : StageTower ℓ) (β : ℝ) (n : ℕ) [NeZero n] {K K' : ℕ} (e : K = K') :
    Measurable (fun w : MarkedSample ℓ K n => e ▸ w) ∧
      (markedSampleLaw T β K n).map (fun w : MarkedSample ℓ K n => e ▸ w) = markedSampleLaw T β K' n := by
  subst e
  exact ⟨measurable_id, Measure.map_id⟩
private theorem map_sampleAtLevel (hB : sampleBelowLawStatement) (hFit : Λ.stepParams.Admissible) (u : ℕ)
    (hu : u ≤ S.data.windowLevel) :
    Measurable (S.sampleAtLevel u hu) ∧
      (S.law S.data.windowLevel (S.data.period Λ.stepParams.side)).map (S.sampleAtLevel u hu) = S.law u (S.sideAtLevel u) := by
  obtain ⟨hc1, hc2⟩ := markedSampleLaw_cast S.tower S.β (S.data.period Λ.stepParams.side) (Nat.add_sub_of_le hu).symm
  obtain ⟨hd1, hd2⟩ := (hB Λ.stepParams hFit hFit.depth_lt S.tower S.isCutoff S.marksMeasurable S.β S.coeff).1 u
    (S.data.windowLevel - u) (S.data.period Λ.stepParams.side)
  refine ⟨hd1.comp hc1, ?_⟩
  have e : S.sampleAtLevel u hu = sampleBelow Λ.stepParams u (S.data.windowLevel - u) (S.data.period Λ.stepParams.side) ∘
      (fun w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side) =>
        (Nat.add_sub_of_le hu).symm ▸ w) := rfl
  rw [e, ← Measure.map_map hd1 hc1]
  show ((markedSampleLaw S.tower S.β S.data.windowLevel (S.data.period Λ.stepParams.side)).map _).map _ = _
  rw [hc2]
  exact hd2
abbrev _root_.YangMills.SharedProofs.p20473 := @map_sampleAtLevel
private theorem isBlockTorusSide_sideAtLevel (hn : 3 ≤ Λ.stepParams.n₀) (t : ℕ) :
    IsBlockTorusSide Λ.stepParams (S.sideAtLevel t) := by
  rw [sideAtLevel_eq S t]
  have hL : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hs := S.side_le
  have hm : S.data.sideExponent ≠ 0 := by
    intro h0
    unfold LevelData.period at hs
    rw [h0] at hs
    have : 1 * 3 ≤ Λ.stepParams.side * Λ.stepParams.n₀ := Nat.mul_le_mul hL hn
    simp at hs
    omega
  obtain ⟨m, hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm
  refine ⟨?_, ?_⟩
  · show Λ.stepParams.side ∣ S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - t)
    unfold LevelData.period
    rw [hm', pow_succ]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Dvd.intro_left _ rfl) _) _
  · show _ ≤ S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - t)
    exact hs.trans (Nat.le_mul_of_pos_right _ (pow_pos hL _))
abbrev _root_.YangMills.SharedProofs.p22950 := @isBlockTorusSide_sideAtLevel
private theorem C₀_lower_bound {R : StepSetup} {A : ResponseSetup R} (hI : A.IsAdmissible) :
    14 + 40 * R.params.coupling ≤ A.responseParams.C₀ := by
  have hk := hI.params_admissible
  rw [hk.C₀_eq]
  linarith [hk.N₀_nonneg, hk.Kc_ge]
private theorem abs_supportTotal_le_of_live (ha : 1 ≤ Λ.stepParams.coupling) {u : ℕ} (hu : u ≤ S.data.windowLevel) (i : Fin Λ.k)
    {n : ℕ} [NeZero n] (hb : IsBlockTorusSide Λ.stepParams n)
    (hsize : weightNorm Λ.stepParams.side u (S.weight i (fineSide Λ.stepParams.side u n)) ≤ 1) (q : StageState S.tower u n)
    (hlive : IsLiveState Λ.stepParams (S.tower.stage u).coupling (S.tower.stage u).labelWeight q.1 q.2.1 q.2.2) :
    |S.supportTotal u n i q| ≤ Λ.response.C₀ * ((S.supportAt u n i).card : ℝ) * S.meanScore u n i q := by
  classical
  have hst := stageOnFlow_at S hu
  have hτ : (S.tower.stage u).depth = u := hst.depth_eq
  have hK : (S.resp u).responseParams = Λ.response := hst.params_eq
  have hres : (S.resp u).IsAdmissible := hst.onFamily.admissible
  have hC₀ : 1 ≤ Λ.response.C₀ := by
    have h := C₀_lower_bound hres
    rw [hK] at h
    linarith
  have hsites : weightSupportSites Λ.stepParams.side (S.tower.stage u).depth n
      (S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth n)) = S.supportAt u n i :=
    supportSites_depth_congr (fun m => S.weight i m) _ hτ
  have hsz : weightNorm Λ.stepParams.side (S.tower.stage u).depth
      (S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth n)) ≤ 1 := by
    rw [weightNorm_congr (fun m => S.weight i m) hτ (congrArg (fun t => fineSide Λ.stepParams.side t n) hτ)]
    exact hsize
  have hs0 : ∀ y, 0 ≤ siteScore (S.resp u).score q.2.1 q.2.2 y := fun y => by
    unfold siteScore
    split_ifs
    · exact hres.price.nonneg _
    · exact le_rfl
  have hterm : ∀ y, |centeredHullResponse (S.resp u).cold (S.resp u).hull n y q.1 q.2.1 q.2.2
      (S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth n))| ≤
      Λ.response.C₀ + siteScore (S.resp u).score q.2.1 q.2.2 y := fun y => by
    have h := hres.bounds.size_hull n hb y q.1 q.2.1 q.2.2 hlive
      (S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth n))
    rw [hK] at h
    refine h.trans ?_
    have hc : 0 ≤ Λ.response.C₀ + siteScore (S.resp u).score q.2.1 q.2.2 y := by linarith [hs0 y]
    exact mul_le_of_le_one_right hc hsz
  have hF : S.supportTotal u n i q = ∑ y ∈ S.supportAt u n i,
      centeredHullResponse (S.resp u).cold (S.resp u).hull n y q.1 q.2.1 q.2.2
        (S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth n)) := by
    rw [← hsites]
    rfl
  have hN : S.meanScore u n i q = 1 + ((S.supportAt u n i).card : ℝ)⁻¹ *
      ∑ y ∈ S.supportAt u n i, siteScore (S.resp u).score q.2.1 q.2.2 y := rfl
  rw [hF, hN]
  have hsum : |∑ y ∈ S.supportAt u n i, centeredHullResponse (S.resp u).cold (S.resp u).hull n y q.1 q.2.1 q.2.2
      (S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth n))| ≤
      Λ.response.C₀ * ((S.supportAt u n i).card : ℝ) +
        ∑ y ∈ S.supportAt u n i, siteScore (S.resp u).score q.2.1 q.2.2 y := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun y _ => hterm y).trans (le_of_eq ?_))
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine hsum.trans ?_
  set c : ℝ := ((S.supportAt u n i).card : ℝ) with hc
  set sc : ℝ := ∑ y ∈ S.supportAt u n i, siteScore (S.resp u).score q.2.1 q.2.2 y with hsc
  have hsc0 : 0 ≤ sc := Finset.sum_nonneg fun y _ => hs0 y
  by_cases hc0 : c = 0
  · have hempty : S.supportAt u n i = ∅ := by
      have h0 : ((S.supportAt u n i).card : ℝ) = 0 := hc0
      rw [← Finset.card_eq_zero]
      exact_mod_cast h0
    have : sc = 0 := by rw [hsc, hempty, Finset.sum_empty]
    rw [hc0, this]
    simp
  · have e : Λ.response.C₀ * c * (1 + c⁻¹ * sc) = Λ.response.C₀ * c + Λ.response.C₀ * sc := by
      field_simp
    rw [e]
    nlinarith
private theorem abs_centredStepScore_le (hS : BondScoreProperties) (hW : WeightsCloseToBlockMeans) (hM : BlockMeanIsLinearAndLocal)
    (hFit : Λ.stepParams.Admissible) (hn : 3 ≤ Λ.stepParams.n₀)
    (HM : ∀ (R : StepSetup) (A : ResponseSetup R), A.responseParams = Λ.response → OnStepParameters Λ.table Λ.floor A →
      ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n →
      ∀ f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n), weightNorm R.params.side R.depth f ≤ 1 →
      (upperSites f).Nonempty →
      |caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f)| ≤
        (A.responseParams.C₀ + 1 + 16 * R.params.coupling) * ((lowerSites f).card : ℝ))
    {u : ℕ} (h1 : u + 1 ≤ S.data.windowLevel) (i : Fin Λ.k)
    (hz : weightNorm Λ.stepParams.side u (S.weight i (fineSide Λ.stepParams.side u (S.levelSide u))) ≤ 1)
    (hz1 : weightNorm Λ.stepParams.side (u + 1)
      (S.weight i (fineSide Λ.stepParams.side (u + 1) (S.levelSide (u + 1)))) ≤ 1)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    |centredStepScore u i S w| ≤ 2 * (Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ)) := by
  classical
  have h0 : u ≤ S.data.windowLevel := by omega
  have hst := stageOnFlow_at S h0
  have hτ : (S.tower.stage u).depth = u := hst.depth_eq
  have hK : (S.resp u).responseParams = Λ.response := hst.params_eq
  have hres : (S.resp u).IsAdmissible := hst.onFamily.admissible
  have hC : 14 + 40 * Λ.stepParams.coupling ≤ Λ.response.C₀ := by
    have h := C₀_lower_bound hres
    rw [hK] at h
    exact h
  have ha : 1 ≤ Λ.stepParams.coupling := hFit.a_ge
  have hbs := isBlockTorusSide_sideAtLevel S hn (u + 1)
  have hLpos : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hfloor : Λ.stepParams.n₀ ≤ S.sideAtLevel (u + 1) := (Nat.le_mul_of_pos_left _ hLpos).trans hbs.2
  have e : centredStepScore u i S w =
      sourceTerm S.tower S.coeff u (S.sideAtLevel (u + 1)) (S.weight i _) (S.sampleAtLevel (u + 1) h1 w) -
        stepMeanShift (n := S.sideAtLevel (u + 1)) (S.resp u) (S.weight i _) := dif_pos h1
  let f : PlaquetteWeight (fineSide (S.tower.stage u).toStepSetup.params.side ((S.tower.stage u).toStepSetup.depth + 1)
    (S.sideAtLevel (u + 1))) := S.weight i _
  have hmid : fineSide Λ.stepParams.side ((S.tower.stage u).depth + 1) (S.sideAtLevel (u + 1)) =
      fineSide Λ.stepParams.side u (S.levelSide u) :=
    fineSide_succ_congr hτ (sideAtLevel_succ_mul S h1)
  have hfz : weightNorm Λ.stepParams.side (S.tower.stage u).depth f ≤ 1 := by
    show weightNorm Λ.stepParams.side (S.tower.stage u).depth
      (S.weight i (fineSide Λ.stepParams.side ((S.tower.stage u).depth + 1) (S.sideAtLevel (u + 1)))) ≤ 1
    rw [weightNorm_congr (fun m => S.weight i m) hτ hmid]
    exact hz
  have hsrc : |sourceTerm S.tower S.coeff u (S.sideAtLevel (u + 1))
      (S.weight i (fineSide Λ.stepParams.side (u + 1) (S.sideAtLevel (u + 1)))) (S.sampleAtLevel (u + 1) h1 w)| ≤
      16 * Λ.stepParams.coupling * ((weightSupportSites Λ.stepParams.side (u + 1) (S.sideAtLevel (u + 1))
        (S.weight i (fineSide Λ.stepParams.side (u + 1) (S.sideAtLevel (u + 1))))).card : ℝ) := by
    refine abs_stepSourceTerm_le hS hW hM hFit _ _ hres.abs_coeff_le u _ ?_ _ _
    rw [weightNorm_congr (fun m => S.weight i m) rfl
      (congrArg (fineSide Λ.stepParams.side (u + 1)) (sideAtLevel_eq S (u + 1)))]
    exact hz1
  have hA : (weightSupportSites Λ.stepParams.side (u + 1) (S.sideAtLevel (u + 1))
      (S.weight i (fineSide Λ.stepParams.side (u + 1) (S.sideAtLevel (u + 1))))).card =
      (upperSites (R := (S.tower.stage u).toStepSetup) f).card :=
    supportSites_card_congr (fun m => S.weight i m) (congrArg (· + 1) hτ.symm) rfl
  have hAB : (upperSites (R := (S.tower.stage u).toStepSetup) f).card ≤
      (lowerSites (R := (S.tower.stage u).toStepSetup) f).card := by
    have hp := parentBlocks_lowerSites (R := (S.tower.stage u).toStepSetup) (n := S.sideAtLevel (u + 1)) f
    rw [← hp]
    exact Finset.card_image_le
  have hB : (lowerSites (R := (S.tower.stage u).toStepSetup) f).card = (S.data.supportSites Λ.stepParams.side u i).card :=
    supportSites_card_congr (fun m => S.weight i m) hτ (sideAtLevel_succ_mul S h1)
  have hC' : (S.resp u).responseParams.C₀ = Λ.response.C₀ := congrArg ResponseParameters.C₀ hK
  have hk0 : (0 : ℝ) ≤ ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) := Nat.cast_nonneg _
  have hb0 : 0 ≤ (S.resp u).responseParams.C₀ + 1 + 16 * (S.tower.stage u).toStepSetup.params.coupling := by
    have h3 : (S.tower.stage u).toStepSetup.params.coupling = Λ.stepParams.coupling := rfl
    rw [hC', h3]
    linarith
  have hshift := abs_stepMeanShift_le (S.resp u) f _ hk0 (congrArg (Nat.cast : ℕ → ℝ) hB) hb0
    (fun hne => HM _ (S.resp u) hK hst.onFamily _ hfloor f hfz hne)
  rw [hC'] at hshift
  have hsrc' : |sourceTerm S.tower S.coeff u (S.sideAtLevel (u + 1))
      (S.weight i (fineSide Λ.stepParams.side (u + 1) (S.sideAtLevel (u + 1)))) (S.sampleAtLevel (u + 1) h1 w)| ≤
      16 * Λ.stepParams.coupling * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) := by
    refine hsrc.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [hA, ← hB]
    exact_mod_cast hAB
  rw [e]
  refine (abs_sub _ _).trans ?_
  have hk : (0 : ℝ) ≤ ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) := Nat.cast_nonneg _
  have hfin : 0 ≤ (Λ.response.C₀ - 1 - 32 * Λ.stepParams.coupling) *
      ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) :=
    mul_nonneg (by linarith) hk
  have h2 : |stepMeanShift (n := S.sideAtLevel (u + 1)) (S.resp u)
      (S.weight i (fineSide Λ.stepParams.side ((S.tower.stage u).depth + 1) (S.sideAtLevel (u + 1))))| ≤
      (Λ.response.C₀ + 1 + 16 * Λ.stepParams.coupling) * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) := hshift
  clear_value f
  nlinarith [hsrc', h2, hfin]
end Points
theorem telescopeTermBounds_holds (h₁ : weightsSitesBelowScaleStatement) (h₂ : liveStatesStatement)
    (h₃ : sampleBelowLawStatement) (h₄ : supportResponseMeanBound)
    (h₅ : BondScoreProperties) (h₆ : WeightsCloseToBlockMeans) (h₇ : BlockMeanIsLinearAndLocal) :
    telescopeTermBoundsStatement := by
  unfold weightsSitesBelowScaleStatement at h₁
  unfold liveStatesStatement at h₂
  unfold supportResponseMeanBound at h₄
  unfold telescopeTermBoundsStatement
  unfold ForAllPoints at h₁ h₂ ⊢
  refine forAllParameters_mono ?_ (forAllParameters_and h₁ (forAllParameters_and h₂
    (forAllParameters_and (forAllParameters_of_forAllSteps h₄) forAllParameters_admissible)))
  rintro Λ ⟨⟨C, _, _, _, _, HW⟩, ⟨_, _, _, _, _, HL⟩, HM, hD, hy⟩
  refine ⟨fun _ => 0, 1, Λ.floor, one_pos, le_rfl, fun S => ⟨?_, ?_⟩⟩
  · intro u hu i w
    have hFit : Λ.stepParams.Admissible := hD.fits Λ.floor hy
    have hn : 3 ≤ Λ.stepParams.n₀ := le_trans (by norm_num) hD.n₀_ge
    have hs := S.supAdmissible.scaleLevel_le
    exact abs_centredStepScore_le S h₅ h₆ h₇ hFit hn (fun R A e t => HM R A e t) (by omega) i
      (HW S u hu.le i).1 (HW S (u + 1) hu i).1 w
  · intro u hu i
    have hFit : Λ.stepParams.Admissible := hD.fits Λ.floor hy
    have hn : 3 ≤ Λ.stepParams.n₀ := le_trans (by norm_num) hD.n₀_ge
    have hK : u ≤ S.data.windowLevel := hu.trans S.supAdmissible.scaleLevel_le
    have hb := isBlockTorusSide_sideAtLevel S hn u
    obtain ⟨m1, e1⟩ := map_sampleAtLevel S h₃ hFit u hK
    have hlive := HL S u hK (S.sideAtLevel u) hb
    rw [← e1] at hlive
    have hae := ae_of_ae_map m1.aemeasurable hlive
    filter_upwards [hae] with w hw
    have e2 : responseAtLevel u i S w = S.supportTotal u (S.sideAtLevel u) i (S.stateAtLevel u hK w) := dif_pos hK
    have e3 : meanScoreAtLevel u i S w = S.meanScore u (S.sideAtLevel u) i (S.stateAtLevel u hK w) := dif_pos hK
    rw [e2, e3]
    have hsz : weightNorm Λ.stepParams.side u (S.weight i (fineSide Λ.stepParams.side u (S.sideAtLevel u))) ≤ 1 := by
      rw [weightNorm_congr (fun m => S.weight i m) rfl (congrArg (fineSide Λ.stepParams.side u) (sideAtLevel_eq S u))]
      exact (HW S u hu i).1
    have h := abs_supportTotal_le_of_live S hFit.a_ge hK i hb hsz (S.stateAtLevel u hK w) hw
    have hc : (S.supportAt u (S.sideAtLevel u) i).card = (S.data.supportSites Λ.stepParams.side u i).card :=
      supportSites_card_congr (fun m => S.weight i m) rfl (sideAtLevel_eq S u)
    rw [hc] at h
    exact h
end YangMills.Construction.MomentLaw
end
