import YangMills.Construction.LawByMomentsOfTheFlow.ClassicalFormsNearTheResponsesProof
import YangMills.Construction.LawByMomentsOfTheFlow.RestOfTheImageAtTheFrameFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.TheFramesCarryFormsAtOne
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps RenormalizationStepParameters StepSettings StepCosts ShareFamilies WeightedResponses ResponseInTheExpansion BlockAverages
namespace RemainderStep
private theorem forAllParameters_and {Q Q' : MomentParameters → Prop} (h : ForAllParameters Q) (h' : ForAllParameters Q') :
    ForAllParameters fun Λ => Q Λ ∧ Q' Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_of_holdsOnAllParameters {P : ParameterAssignment → ℝ → Prop} (h : HoldsOnParameterFamilies P) :
    ForAllParameters fun Λ => P Λ.table Λ.floor := by apply _root_.YangMills.SharedProofs.p27928 <;> assumption
private theorem weightLipschitz_nonneg (L t : ℕ) {N : ℕ} (h : PlaquetteWeight N) : 0 ≤ weightLipschitz L t h := by apply _root_.YangMills.Construction.ResponseInTheExpansion.weightLipschitz_nonneg <;> assumption
private theorem weightLipschitz_succ {L t m : ℕ} (hL : 0 < L) (h : PlaquetteWeight m) :
    weightLipschitz L (t + 1) h = (L : ℝ) * weightLipschitz L t h := by apply _root_.YangMills.SharedProofs.p7308 <;> assumption
private theorem unitGenerator_pair_units : AreUnitVectors ![unitGenerator, unitGenerator] := by
  intro l
  fin_cases l <;> exact SingleColourFields.norm_unitGenerator
variable {n : ℕ} [NeZero n]
private theorem hasQuadraticFormAtIdentity_add_smul {G₁ G₂ : TorusField n → ℝ} (κ : ℝ)
    (h₁ : ContDiffThreeAt G₁ (trivialField n)) (h₂ : ContDiffThreeAt G₂ (trivialField n))
    (f₁ : HasQuadraticFormAtIdentity G₁) (f₂ : HasQuadraticFormAtIdentity G₂) :
    HasQuadraticFormAtIdentity (fun W => G₁ W + κ * G₂ W) := by apply _root_.YangMills.SharedProofs.p19488 <;> assumption
private theorem abs_sub_le_of_two_steps {a b c u l G Cu Cv E : ℝ} (h₁ : |a - b| ≤ Cu * u * l / G)
    (h₂ : |b - c| ≤ Cv * u * (E * l) / G) (hu : 0 ≤ u) (hl : 0 ≤ l) (hG : 0 < G) (hE : 0 ≤ E) :
    |a - c| ≤ (|Cu| + |Cv| * E) * u * l / G := by
  have t₁ : Cu * u * l / G ≤ |Cu| * u * l / G :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hu) hl) hG.le
  have t₂ : Cv * u * (E * l) / G ≤ |Cv| * u * (E * l) / G :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hu) (by positivity)) hG.le
  have e : (|Cu| + |Cv| * E) * u * l / G = |Cu| * u * l / G + |Cv| * u * (E * l) / G := by
    field_simp
  rw [e]
  exact (abs_sub_le _ _ _).trans (add_le_add (h₁.trans t₁) (h₂.trans t₂))
end RemainderStep
open RemainderStep in
theorem remainderOneStepStatement_holds (hU : remainderHessianAtFrameFieldStatement) (hV : framesPullbackFormsStatement)
    (hF : responsesHaveFormsStatement) (hSh : levelSharesUniformStatement) (hW : WeightsCloseToBlockMeans) :
    remainderOneStepStatement := by
  unfold remainderHessianAtFrameFieldStatement ForAllPoints at hU
  unfold framesPullbackFormsStatement ForAllPoints at hV
  unfold responsesHaveFormsStatement ForAllPoints at hF
  unfold levelSharesUniformStatement at hSh
  have all := forAllParameters_and hU (forAllParameters_and hV (forAllParameters_and hF (forAllParameters_of_holdsOnAllParameters hSh)))
  unfold remainderOneStepStatement ForAllPoints ForAllParameters
  intro a ha
  obtain ⟨L₀, r₀, C₀, p₀, g⟩ := all a ha
  refine ⟨L₀, r₀, C₀, p₀, fun L hodd hL T hTa hTL hD hCS hOn hrt hCd Kr hFit => ?_⟩
  obtain ⟨y₀, f⟩ := g L hodd hL T hTa hTL hD hCS hOn hrt hCd Kr hFit
  refine ⟨max y₀ T.floorMin, fun y hy hRt hWy gg hg hgy k _ hk2 hk8 R d hd => ?_⟩
  have hy₄ : 1 ≤ y := hD.yC_ge.trans ((le_max_left _ _).trans ((le_max_right _ _).trans hy))
  obtain ⟨⟨Cu, _, _, _, _, bU⟩, ⟨Cv, _, _, _, _, bV⟩, ⟨_, _, _, _, _, bF⟩, bSh⟩ :=
    f y ((le_max_left _ _).trans hy) hRt hWy gg hg hgy k hk2 hk8 R d hd
  obtain ⟨Csh, hCsh, bFam⟩ := bSh
  have hσ : 0 < (T.stepParameters y).threshold := hD.σ_pos
  have hLpos : 0 < (T.stepParameters y).side := lt_of_lt_of_le (by norm_num) (show 2 ^ 40 ≤ T.side from hD.L_ge)
  have hodd' : Odd (T.stepParameters y).side := by rw [show (T.stepParameters y).side = L from hTL]; exact hodd
  have hL1 : (1 : ℝ) ≤ (T.stepParameters y).side := by exact_mod_cast hLpos
  have hKc : 0 ≤ Kr.Kc := by linarith [(hFit y).Kc_ge]
  refine ⟨fun _ => |Cu 0| + |Cv 0| * (Kr.Kc + 3 * Csh), 1, y, one_pos, le_rfl, fun S t ht n _ hn Y h c c' => ?_⟩
  have ht' : t ≤ S.data.windowLevel := by omega
  have st : StageOnFlow T Kr y S.β t ⟨S.tower.stage t, S.resp t⟩ := by
    have h₁ := S.onFlow t ht'
    rw [← S.stage_eq t ht'] at h₁
    exact h₁
  have row := st.onFamily.admissible.bounds
  have hK : (S.resp t).responseParams = Kr := st.params_eq
  have hnL : (T.stepParameters y).n₀ ≤ n * (T.stepParameters y).side := hn.trans (Nat.le_mul_of_pos_right _ hLpos)
  have cold : IsCold (T.stepParameters y).threshold (trivialField (n * (T.stepParameters y).side)) :=
    TermCalculus.isCold_trivialField hσ _
  obtain ⟨hw₀, hw₁⟩ : (0 : ℝ) ≤ weightLipschitz (T.stepParameters y).side (S.tower.stage t).depth
      (show PlaquetteWeight (fineSide (T.stepParameters y).side (S.tower.stage t).depth (n * (T.stepParameters y).side)) from h) ∧
      weightLipschitz (T.stepParameters y).side ((S.tower.stage t).depth + 1) h =
        ((T.stepParameters y).side : ℝ) * weightLipschitz (T.stepParameters y).side (S.tower.stage t).depth
      (show PlaquetteWeight (fineSide (T.stepParameters y).side (S.tower.stage t).depth (n * (T.stepParameters y).side)) from h) :=
    ⟨_root_.YangMills.Construction.MomentLaw.RemainderStep.weightLipschitz_nonneg _ _ _, weightLipschitz_succ hLpos _⟩
  set lip := weightLipschitz (T.stepParameters y).side ((S.tower.stage t).depth + 1) h with hlip
  set lt₀ := weightLipschitz (T.stepParameters y).side (S.tower.stage t).depth
      (show PlaquetteWeight (fineSide (T.stepParameters y).side (S.tower.stage t).depth (n * (T.stepParameters y).side)) from h)
    with hlt₀
  have hlip0 : 0 ≤ lip := by rw [hw₁]; positivity
  have hlt : lt₀ ≤ lip := by rw [hw₁]; nlinarith
  set D : TorusSite (n * (T.stepParameters y).side) → ℝ := fun z =>
    blockMean (T.stepParameters y).side (S.tower.stage t).depth (n * (T.stepParameters y).side) z h -
      blockMean (T.stepParameters y).side ((S.tower.stage t).depth + 1) n Y h with hDdef
  set gf : TorusSite (n * (T.stepParameters y).side) → TorusField (n * (T.stepParameters y).side) → ℝ := fun z W =>
    responseRemainder (S.resp t).cold (n * (T.stepParameters y).side) z h W +
      D z * levelShare (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth Finset.univ z W with hgf
  have eS : ∀ z : TorusSite (n * (T.stepParameters y).side),
      levelShareFamily (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth
        (n * (T.stepParameters y).side) z =
      levelShare (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth Finset.univ z := by
    intro z
    funext W
    unfold levelShareFamily
    rw [dif_neg (NeZero.ne _)]
  have hFam := (bFam (S.tower.stage t).depth).1
  have sm₁ : ∀ z, ContDiffThreeAt (responseRemainder (S.resp t).cold (n * (T.stepParameters y).side) z h) (trivialField _) :=
    fun z => row.remainder_smooth _ hnL z _ cold h
  have sm₂ : ∀ z, ContDiffThreeAt (levelShare (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth
      Finset.univ z) (trivialField (n * (T.stepParameters y).side)) := by
    intro z
    rw [← eS]
    exact hFam.smooth _ hnL z _ cold
  have hess : ∀ z, hessianAtIdentity (gf z) = fun b b' =>
      D z * shareHessian (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth z b b' +
        remainderHessian (S.resp t) (n * (T.stepParameters y).side) z h b b' := by
    intro z
    funext b b'
    show mixedDeriv (fun W => responseRemainder (S.resp t).cold (n * (T.stepParameters y).side) z h W +
      D z * levelShare (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth Finset.univ z W)
      (trivialField _) ![b, b'] ![unitGenerator, unitGenerator] = _
    rw [TermCalculus.mixedDeriv_add _ (fun W => D z * levelShare (T.stepParameters y).coupling (T.stepParameters y).side
        (S.tower.stage t).depth Finset.univ z W) _ _ _
        (by norm_num) (sm₁ z 2 _ _) (contDiffAt_const.mul (sm₂ z 2 _ _)),
      TermCalculus.mixedDeriv_const_mul _ _ _ _ _ (by norm_num) (sm₂ z 2 _ _)]
    show _ + _ = D z * mixedDeriv _ _ _ _ + mixedDeriv _ _ _ _
    ring
  have hyp : ∀ z ∈ sitesInBlocks (T.stepParameters y).side {Y},
      ContDiffThreeAt (gf z) (trivialField (n * (T.stepParameters y).side)) ∧ HasQuadraticFormAtIdentity (gf z) ∧
      IsDecayingAbout (T.stepParameters y) ((Kr.Kc + 3 * Csh) * lip) z (hessianAtIdentity (gf z)) := by
    intro z hz
    have hD₃ : |D z| ≤ 3 * lip := (hW (T.stepParameters y).side hodd' (S.tower.stage t).depth n Y).2.2 h z hz
    obtain ⟨f₁, f₂, -⟩ := id (show _ ∧ _ ∧ _ from
      ⟨(bF S t ht' (n * (T.stepParameters y).side) hnL z h).1, (bF S t ht' (n * (T.stepParameters y).side) hnL z h).2.1, trivial⟩)
    refine ⟨fun m c₁ X₁ => (sm₁ z m c₁ X₁).add (contDiffAt_const.mul (sm₂ z m c₁ X₁)),
      hasQuadraticFormAtIdentity_add_smul (D z) (sm₁ z) (sm₂ z) f₂ f₁, fun b b' => ?_⟩
    rw [hess z]
    have hG := TermCalculus.weight_pos (T.stepParameters y) (tripleDiam z b b')
    have hr := row.remainder_decay _ hnL z _ cold h 2 ![b, b'] ![unitGenerator, unitGenerator] (by norm_num) (by norm_num)
      unitGenerator_pair_units
    simp only [show ¬ (2 = 3) by norm_num, if_false, hK] at hr
    have hr' : |remainderHessian (S.resp t) (n * (T.stepParameters y).side) z h b b'| ≤
        Kr.Kc * lt₀ / (T.stepParameters y).weight (tripleDiam z b b') := hr
    have ha := hFam.decay _ hnL z _ cold 2 ![b, b'] ![unitGenerator, unitGenerator] (by norm_num) (by norm_num)
      unitGenerator_pair_units
    rw [eS] at ha
    have ha' : |shareHessian (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth z b b'| ≤
        Csh / (T.stepParameters y).weight (tripleDiam z b b') := ha
    have t₁ : |D z * shareHessian (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth z b b'| ≤
        3 * lip * (Csh / (T.stepParameters y).weight (tripleDiam z b b')) := by
      rw [abs_mul]
      exact mul_le_mul hD₃ ha' (abs_nonneg _) (by positivity)
    have t₂ : Kr.Kc * lt₀ / (T.stepParameters y).weight (tripleDiam z b b') ≤
        Kr.Kc * lip / (T.stepParameters y).weight (tripleDiam z b b') :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlt hKc) hG.le
    have e : (Kr.Kc + 3 * Csh) * lip / (T.stepParameters y).weight (tripleDiam z b b') =
        3 * lip * (Csh / (T.stepParameters y).weight (tripleDiam z b b')) +
          Kr.Kc * lip / (T.stepParameters y).weight (tripleDiam z b b') := by
      field_simp
      ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add t₁ (hr'.trans t₂))
  have key₁ := bU S t ht n hn Y h c c'
  have key₂ := bV S t ht n hn Y ((Kr.Kc + 3 * Csh) * lip) (by positivity) gf hyp c c'
  have e₃ : ∑ z ∈ sitesInBlocks (T.stepParameters y).side {Y},
      pullbackForm (T.stepParameters y).coupling (S.tower.stage t).anchorRadius (T.stepParameters y).side
        (S.tower.stage t).depth (n := n) (hessianAtIdentity (gf z)) c c' =
      ∑ z ∈ sitesInBlocks (T.stepParameters y).side {Y},
        pullbackForm (T.stepParameters y).coupling (S.tower.stage t).anchorRadius (T.stepParameters y).side
        (S.tower.stage t).depth (n := n) (fun b b' =>
          D z * shareHessian (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth z b b' +
          remainderHessian (S.resp t) (n * (T.stepParameters y).side) z h b b') c c' :=
    Finset.sum_congr rfl fun z _ => by rw [hess z]
  rw [e₃] at key₂
  have hG := TermCalculus.weight_pos (T.stepParameters y) (tripleDiam Y c c')
  have hxt : 0 ≤ S.coupling t ^ (-(1 / 2) : ℝ) := by
    have h₁ : y ≤ (S.tower.stage t).coupling := st.onFamily.onFamily.le_coupling
    have h₂ : (S.tower.stage t).coupling = S.coupling t := st.coupling_eq
    exact Real.rpow_nonneg (by linarith) _
  have hE : 0 ≤ Kr.Kc + 3 * Csh := by positivity
  exact abs_sub_le_of_two_steps key₁ key₂ hxt hlip0 hG hE
end YangMills.Construction.MomentLaw
end
