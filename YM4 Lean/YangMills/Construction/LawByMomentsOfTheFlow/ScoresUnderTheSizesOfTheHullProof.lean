import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.ScoresUnderTheSizesOfTheHull
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses ResponseInTheExpansion ClusterExpansionOfAStep HullTrees LevelTestFunctions
section Numbers
private theorem one_add_pow_le_two_pow_mul {s : ℝ} (hs : 0 ≤ s) (p : ℕ) : (1 + s) ^ p ≤ 2 ^ p * (1 + s ^ p) := by apply _root_.YangMills.SharedProofs.p7069 <;> assumption
private theorem prod_one_add_mean_le {ι σ τ : Type} (J : Finset ι) (hJ : J.Nonempty) (B : ι → Finset σ) (f : σ → ℝ)
    (hf : ∀ y, 0 ≤ f y) (box : Finset τ) (site : τ → σ) (hbox : ∀ i ∈ J, ∀ y ∈ B i, ∃ z ∈ box, y = site z) :
    ∏ i ∈ J, (1 + ((B i).card : ℝ)⁻¹ * ∑ y ∈ B i, f y) ≤
      1 + 2 ^ J.card * (1 + ∑ z ∈ box, f (site z) ^ J.card) := by
  have hT : 0 ≤ ∑ z ∈ box, f (site z) ^ J.card := Finset.sum_nonneg fun z _ => pow_nonneg (hf _) _
  have hmean0 : ∀ i, 0 ≤ ((B i).card : ℝ)⁻¹ * ∑ y ∈ B i, f y := fun i =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => hf y)
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image J (fun i => 1 + ((B i).card : ℝ)⁻¹ * ∑ y ∈ B i, f y) hJ
  have hprod : ∏ i ∈ J, (1 + ((B i).card : ℝ)⁻¹ * ∑ y ∈ B i, f y) ≤
      (1 + ((B m).card : ℝ)⁻¹ * ∑ y ∈ B m, f y) ^ J.card := by
    calc ∏ i ∈ J, (1 + ((B i).card : ℝ)⁻¹ * ∑ y ∈ B i, f y)
        ≤ ∏ _i ∈ J, (1 + ((B m).card : ℝ)⁻¹ * ∑ y ∈ B m, f y) :=
          Finset.prod_le_prod (fun i _ => by have := hmean0 i; linarith) hmax
      _ = _ := by rw [Finset.prod_const]
  have h2 : (0 : ℝ) ≤ 2 ^ J.card := by positivity
  have hfm : (1 + ((B m).card : ℝ)⁻¹ * ∑ y ∈ B m, f y) ^ J.card ≤
      2 ^ J.card * (1 + ∑ z ∈ box, f (site z) ^ J.card) := by
    rcases (B m).eq_empty_or_nonempty with hB | hB
    · have h1 : (1 : ℝ) ≤ 2 ^ J.card := one_le_pow₀ (by norm_num)
      rw [hB]
      simp only [Finset.sum_empty, mul_zero, add_zero, one_pow]
      exact h1.trans (le_mul_of_one_le_right h2 (by linarith))
    · obtain ⟨y, hy, hymax⟩ := Finset.exists_max_image (B m) f hB
      have hc : (0 : ℝ) < ((B m).card : ℝ) := by exact_mod_cast hB.card_pos
      have hmean : ((B m).card : ℝ)⁻¹ * ∑ x ∈ B m, f x ≤ f y := by
        have h1 : ∑ x ∈ B m, f x ≤ ((B m).card : ℝ) * f y := by
          simpa using Finset.sum_le_card_nsmul (B m) f (f y) hymax
        rw [inv_mul_le_iff₀ hc]
        exact h1
      obtain ⟨z, hz, rfl⟩ := hbox m hm y hy
      have hpow : f (site z) ^ J.card ≤ ∑ z ∈ box, f (site z) ^ J.card :=
        Finset.single_le_sum (f := fun z => f (site z) ^ J.card) (fun z _ => pow_nonneg (hf _) _) hz
      calc (1 + ((B m).card : ℝ)⁻¹ * ∑ y ∈ B m, f y) ^ J.card ≤ (1 + f (site z)) ^ J.card :=
            pow_le_pow_left₀ (by have := hmean0 m; linarith) (by linarith) _
        _ ≤ 2 ^ J.card * (1 + f (site z) ^ J.card) := one_add_pow_le_two_pow_mul (hf _) _
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) h2
  linarith
end Numbers
section Sites
variable {k : ℕ}
private theorem exists_mem_offsetCube_of_mem_supportSites (hP : supportSitesLocationStatement) {L : ℕ} [NeZero L] (hL : Odd L)
    (P : LevelData k) {R d : ℝ} (hF : P.SupAdmissible L R d) {u : ℕ} (hu : u ≤ P.scaleLevel) (i : Fin k)
    {y : TorusSite (P.sideAt L u)} (hy : y ∈ P.supportSites L u i) :
    ∃ z ∈ offsetCube (⌈R * (L : ℝ) ^ (P.scaleLevel - u)⌉₊ + 2), ∀ a, y a =
      ((round (P.center a * (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ u) : ℤ) : ZMod (P.sideAt L u)) +
        ((z a : ℤ) : ZMod (P.sideAt L u)) := by apply _root_.YangMills.SharedProofs.p54227 <;> assumption
end Sites
section Scores
variable {ℓ : StepParameters}
private theorem coarseLabelScore_nonneg_aux {Ω : Type} {L : ℕ} {s₁ : ℝ} {s : Ω → ℝ} (h₁ : 0 ≤ s₁) (hs : ∀ w, 0 ≤ s w)
    (ω : CoarseLabel Ω L) : 0 ≤ coarseLabelScore s₁ s ω := by apply _root_.YangMills.Construction.ResponseInTheExpansion.CoarseScore.coarseLabelScore_nonneg <;> assumption
private theorem labelSize_nonneg_aux (T : StageTower ℓ) {s₁ : ℝ} (h₁ : 0 ≤ s₁) :
    ∀ (t : ℕ) (w : (T.stage t).labels.Ω), 0 ≤ labelSize T s₁ t w
  | 0, _ => le_rfl
  | t + 1, w => coarseLabelScore_nonneg_aux h₁ (labelSize_nonneg_aux T h₁ t) w
end Scores
section Point
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem score_eq_labelSize (u : ℕ) (hu : u ≤ S.data.windowLevel) : (S.resp u).score = labelSize S.tower Λ.response.s₁ u := by apply _root_.YangMills.SharedProofs.p9388 <;> assumption
private theorem exists_offset_of_mem_supportAt (hP : supportSitesLocationStatement) (hL : Odd Λ.stepParams.side) {u : ℕ}
    (hu : u ≤ S.data.scaleLevel) (i : Fin Λ.k) (n : ℕ) [NeZero n] (hn : n = S.levelSide u) (y : TorusSite n)
    (hy : y ∈ S.supportAt u n i) :
    ∃ z ∈ offsetCube (S.supportRadius u), y = S.originSite u n + siteOfInt z := by
  subst hn
  obtain ⟨z, hz, hy'⟩ := exists_mem_offsetCube_of_mem_supportSites hP hL S.data S.supAdmissible hu i (y := y) hy
  exact ⟨z, hz, funext hy'⟩
private theorem meanScore_bounds_at (hP : supportSitesLocationStatement) (hL : Odd Λ.stepParams.side) (hs₁ : 0 ≤ Λ.response.s₁)
    {u : ℕ} (hu : u ≤ S.data.scaleLevel) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    (∀ i : Fin Λ.k, 1 ≤ meanScoreAtLevel u i S w) ∧ ∀ J : Finset (Fin Λ.k), J.Nonempty →
      ∏ i ∈ J, meanScoreAtLevel u i S w ≤
        1 + 2 ^ J.card * (1 + ∑ z ∈ offsetCube (S.supportRadius u), hullSizePower u z J.card S w) := by
  have hK : u ≤ S.data.windowLevel := hu.trans S.supAdmissible.scaleLevel_le
  have hn : S.sideAtLevel u = S.levelSide u := WeightedResponses.fineSide_eq _ _ _
  let f : TorusSite (S.sideAtLevel u) → ℝ := fun y =>
    siteScore (labelSize S.tower Λ.response.s₁ u) (S.stateAtLevel u hK w).2.1 (S.stateAtLevel u hK w).2.2 y
  have hf0 : ∀ y, 0 ≤ f y := fun y => by
    show 0 ≤ siteScore _ _ _ _
    unfold siteScore
    split_ifs
    · exact labelSize_nonneg_aux S.tower hs₁ u _
    · exact le_rfl
  have hN : ∀ i, meanScoreAtLevel u i S w =
      1 + ((S.supportAt u (S.sideAtLevel u) i).card : ℝ)⁻¹ * ∑ y ∈ S.supportAt u (S.sideAtLevel u) i, f y := fun i => by
    unfold meanScoreAtLevel
    rw [dif_pos hK]
    show meanSiteScore (S.resp u).score _ _ _ = _
    rw [score_eq_labelSize S u hK]
    rfl
  have hZ : ∀ (z : Fin 4 → ℤ) (p : ℕ), hullSizePower u z p S w = f (S.siteAt u z) ^ p := fun z p => by
    unfold hullSizePower
    rw [dif_pos hK]
    rfl
  refine ⟨fun i => ?_, fun J hJ => ?_⟩
  · rw [hN i]
    have : 0 ≤ ((S.supportAt u (S.sideAtLevel u) i).card : ℝ)⁻¹ * ∑ y ∈ S.supportAt u (S.sideAtLevel u) i, f y :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => hf0 y)
    linarith
  · rw [Finset.prod_congr rfl fun i _ => hN i, Finset.sum_congr rfl fun z _ => hZ z J.card]
    exact prod_one_add_mean_le J hJ (fun i => S.supportAt u (S.sideAtLevel u) i) f hf0 _ (S.siteAt u)
      fun i _ y hy => exists_offset_of_mem_supportAt S hP hL hu i _ hn y hy
end Point
theorem meanScoreProductBound (hP : supportSitesLocationStatement) : meanScoreProductBoundStatement := by
  unfold meanScoreProductBoundStatement ForAllPoints ForAllParameters
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L hodd _ Tb _ hTL hDr _ _ _ _ Kr hfit => ?_⟩
  refine ⟨Tb.floorMin, fun y hy _ _ g _ _ k _ _ _ R d _ => ?_⟩
  have hfits : (Tb.stepParameters y).Admissible := hDr.fits y hy
  have hs₁ : 0 ≤ Kr.s₁ := by
    have hk := hfit y
    have ha1 : 1 ≤ (Tb.stepParameters y).coupling := hfits.a_ge
    have hC0 : 0 ≤ Kr.C₀ + 2 := by
      have := hk.Kc_ge
      have := hk.N₀_nonneg
      rw [hk.C₀_eq]
      linarith
    rw [hk.s₁_eq]
    exact add_nonneg (mul_nonneg (by positivity) hC0) (by linarith)
  have hodd' : Odd (MomentParameters.stepParams ⟨Tb, Kr, y, g, k, R, d⟩).side := by
    show Odd Tb.side
    rw [hTL]
    exact hodd
  exact ⟨fun _ => 0, 1, y, one_pos, le_rfl, fun S u hu w => meanScore_bounds_at S hP hodd' hs₁ hu w⟩
end YangMills.Construction.MomentLaw
end
