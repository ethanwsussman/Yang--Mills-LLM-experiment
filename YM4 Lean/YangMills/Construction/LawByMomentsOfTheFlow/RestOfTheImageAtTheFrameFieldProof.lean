import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheResponsesAtOne
import YangMills.Construction.LawByMomentsOfTheFlow.NumberOfTheFlowNearOne
import YangMills.Construction.LawByMomentsOfTheFlow.ResponseOfTheFrameFieldAtOne
import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import YangMills.Construction.ResponseInTheExpansion.MeanInTheColdSetting
import Mathlib
import YangMills.Construction.LawByMomentsOfTheFlow.VariablesOfAPointSplitProof
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheParts
import YangMills.Construction.ResponseInTheExpansion.RestOfAStepAtTheFrameField
import YangMills.Construction.ResponseInTheExpansion.SharesAtEveryLevel
set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion StepCosts
def remainderHessianAtFrameFieldStatement : Prop :=
  ForAllPoints fun Λ C _ _ S => ∀ t, t + 1 ≤ S.data.windowLevel → ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n →
    ∀ (Y : TorusSite n) (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage (t + 1)).depth n))
      (c c' : TorusBond n),
    |remainderHessian (S.resp (t + 1)) n Y h c c' -
        ∑ y ∈ sitesInBlocks Λ.stepParams.side {Y}, hessianAtIdentity (fun V : TorusField n =>
          responseRemainder (S.resp t).cold (n * Λ.stepParams.side) y h
              (coldFieldAboveFrames (S.tower.stage t).toStepSetup V 0) +
            (blockMean Λ.stepParams.side (S.tower.stage t).depth (n * Λ.stepParams.side) y h -
                blockMean Λ.stepParams.side ((S.tower.stage t).depth + 1) n Y h) *
              levelShare Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth Finset.univ y
                (coldFieldAboveFrames (S.tower.stage t).toStepSetup V 0)) c c'| ≤
      C 0 * S.coupling t ^ (-(1 / 2) : ℝ) * weightLipschitz Λ.stepParams.side (S.tower.stage (t + 1)).depth h /
        Λ.stepParams.weight (tripleDiam Y c c')
end YangMills.Construction.MomentLaw
end

set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields
namespace RemainderHessianAux
private theorem forAllParameters_and {Q Q' : MomentParameters → Prop} (h : ForAllParameters Q)
    (h' : ForAllParameters Q') : ForAllParameters fun p => Q p ∧ Q' p := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_of_holdsOnAllParameters {P : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop}
    (h : ResponseInTheExpansion.HoldsOnParameterFamilies P) : ForAllParameters fun p => P p.table p.floor := by apply _root_.YangMills.SharedProofs.p27928 <;> assumption
private theorem cold_heq_of_eq {ℓ : TorusLumps.StepParameters} {z z' : ResponseInTheExpansion.StageWithResponse ℓ}
    (h : z = z') : HEq z.2.cold z'.2.cold := by
  subst h
  rfl
variable {n : ℕ} [NeZero n]
private theorem mixedDeriv_const_zero {k : ℕ} (hk : k ≠ 0) (c : Fin k → TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions) :
    mixedDeriv (fun _ : TorusField n => (0 : ℝ)) (trivialField n) c X = 0 := by
  unfold mixedDeriv
  rw [iteratedFDeriv_const_of_ne hk]
  rfl
private theorem hasQuadraticForm_add_smul {G₁ G₂ : TorusField n → ℝ} (κ : ℝ)
    (h₁ : ContDiffThreeAt G₁ (trivialField n)) (h₂ : ContDiffThreeAt G₂ (trivialField n))
    (f₁ : HasQuadraticFormAtIdentity G₁) (f₂ : HasQuadraticFormAtIdentity G₂) :
    HasQuadraticFormAtIdentity (fun W => G₁ W + κ * G₂ W) := by
  obtain ⟨z₁, q₁, s₁, k₁, e₁⟩ := f₁
  obtain ⟨z₂, q₂, s₂, k₂, e₂⟩ := f₂
  have dd : ∀ {m : ℕ} (c : Fin m → TorusBond n) (X : Fin m → BlockAverages.imaginaryQuaternions), m ≤ 3 →
      mixedDeriv (fun W => G₁ W + κ * G₂ W) (trivialField n) c X =
        mixedDeriv G₁ (trivialField n) c X + κ * mixedDeriv G₂ (trivialField n) c X := by
    intro m c X hm
    rw [ResponseInTheExpansion.TermCalculus.mixedDeriv_add G₁ (fun W => κ * G₂ W) (trivialField n) c X hm (h₁ m c X)
        (contDiffAt_const.mul (h₂ m c X)),
      ResponseInTheExpansion.TermCalculus.mixedDeriv_const_mul κ G₂ (trivialField n) c X hm (h₂ m c X)]
  refine ⟨fun b X => ?_, fun b b' => q₁ b b' + κ * q₂ b b', fun b b' => by
    show q₁ b b' + κ * q₂ b b' = q₁ b' b + κ * q₂ b' b
    rw [s₁ b b', s₂ b b'], fun φ A => ⟨?_, ?_⟩, fun b b' X X' => ?_⟩
  · rw [dd _ _ (by norm_num), z₁, z₂]
    simp
  · have a₁ := (k₁ φ A).1
    have a₂ := (k₂ φ A).1
    unfold bilinearEval at a₁ a₂ ⊢
    have e : ∑ b, ∑ b', latticeGradient φ b * (q₁ b b' + κ * q₂ b b') * A b' =
        (∑ b, ∑ b', latticeGradient φ b * q₁ b b' * A b') +
          κ * ∑ b, ∑ b', latticeGradient φ b * q₂ b b' * A b' := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b' _ => ?_
      ring
    rw [e, a₁, a₂]
    simp
  · have a₁ := (k₁ φ A).2
    have a₂ := (k₂ φ A).2
    unfold bilinearEval at a₁ a₂ ⊢
    have e : ∑ b, ∑ b', A b * (q₁ b b' + κ * q₂ b b') * latticeGradient φ b' =
        (∑ b, ∑ b', A b * q₁ b b' * latticeGradient φ b') +
          κ * ∑ b, ∑ b', A b * q₂ b b' * latticeGradient φ b' := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b' _ => ?_
      ring
    rw [e, a₁, a₂]
    simp
  · rw [dd _ _ (by norm_num), e₁, e₂]
    ring
abbrev _root_.YangMills.SharedProofs.p19488 := @hasQuadraticForm_add_smul
private theorem hessianAtIdentity_add_smul {G₁ G₂ : TorusField n → ℝ} (κ : ℝ)
    (h₁ : ContDiffThreeAt G₁ (trivialField n)) (h₂ : ContDiffThreeAt G₂ (trivialField n)) (b b' : TorusBond n) :
    hessianAtIdentity (fun W => G₁ W + κ * G₂ W) b b' = hessianAtIdentity G₁ b b' + κ * hessianAtIdentity G₂ b b' := by
  unfold hessianAtIdentity
  rw [ResponseInTheExpansion.TermCalculus.mixedDeriv_add G₁ (fun W => κ * G₂ W) (trivialField n) _ _ (by norm_num)
      (h₁ 2 _ _) (contDiffAt_const.mul (h₂ 2 _ _)),
    ResponseInTheExpansion.TermCalculus.mixedDeriv_const_mul κ G₂ (trivialField n) _ _ (by norm_num) (h₂ 2 _ _)]
private theorem finsetSum_hasQuadraticForm {ι : Type} (s : Finset ι) (f : ι → TorusField n → ℝ)
    (hs : ∀ y ∈ s, ContDiffThreeAt (f y) (trivialField n)) (hf : ∀ y ∈ s, HasQuadraticFormAtIdentity (f y)) :
    ContDiffThreeAt (fun W => ∑ y ∈ s, f y W) (trivialField n) ∧
      HasQuadraticFormAtIdentity (fun W => ∑ y ∈ s, f y W) ∧
      ∀ b b', hessianAtIdentity (fun W => ∑ y ∈ s, f y W) b b' = ∑ y ∈ s, hessianAtIdentity (f y) b b' := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨fun k c X => contDiffAt_const,
      ⟨fun b X => mixedDeriv_const_zero (by norm_num) _ _, fun _ _ => 0, fun _ _ => rfl,
      fun φ A => ⟨by simp [bilinearEval], by simp [bilinearEval]⟩, fun b b' X X' => ?_⟩,
      fun b b' => mixedDeriv_const_zero (by norm_num) _ _⟩
    rw [mixedDeriv_const_zero (by norm_num)]
    simp
  | insert y s hy ih =>
    obtain ⟨i₁, i₂, i₃⟩ := ih (fun z hz => hs z (Finset.mem_insert_of_mem hz))
      (fun z hz => hf z (Finset.mem_insert_of_mem hz))
    have hy₁ := hs y (Finset.mem_insert_self _ _)
    have hy₂ := hf y (Finset.mem_insert_self _ _)
    have e : (fun W => ∑ z ∈ insert y s, f z W) = fun W => (∑ z ∈ s, f z W) + 1 * f y W := by
      funext W
      rw [Finset.sum_insert hy]
      ring
    rw [e]
    refine ⟨fun k c X => (i₁ k c X).add (contDiffAt_const.mul (hy₁ k c X)),
      hasQuadraticForm_add_smul 1 i₁ hy₁ i₂ hy₂, fun b b' => ?_⟩
    rw [hessianAtIdentity_add_smul 1 i₁ hy₁, i₃, Finset.sum_insert hy]
    ring
variable {N : ℕ} [NeZero N]
private def pullbackForm (Z : TorusBond N → TorusBond n → ℝ) (c c' : TorusBond n)
    (q : TorusBond N → TorusBond N → ℝ) : ℝ :=
  ∑ b, ∑ b', Z b c * q b b' * Z b' c'
private theorem pullbackForm_add (Z : TorusBond N → TorusBond n → ℝ) (c c' : TorusBond n)
    (q q' : TorusBond N → TorusBond N → ℝ) :
    pullbackForm Z c c' (fun b b' => q b b' + q' b b') = pullbackForm Z c c' q + pullbackForm Z c c' q' := by
  unfold pullbackForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring
private theorem pullbackForm_sum {ι : Type} (s : Finset ι) (Z : TorusBond N → TorusBond n → ℝ)
    (c c' : TorusBond n) (q : ι → TorusBond N → TorusBond N → ℝ) :
    pullbackForm Z c c' (fun b b' => ∑ y ∈ s, q y b b') = ∑ y ∈ s, pullbackForm Z c c' (q y) := by
  unfold pullbackForm
  have e : ∀ b b', Z b c * (∑ y ∈ s, q y b b') * Z b' c' = ∑ y ∈ s, Z b c * q y b b' * Z b' c' :=
    fun b b' => by
      rw [Finset.mul_sum, Finset.sum_mul]
  simp only [e]
  rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm]
  exact Finset.sum_comm
private theorem abs_sub_le_of_three {a b c d al u l G C₁ C₂ CN : ℝ} (h₁ : |a - b - al * c| ≤ C₂ * u * l / G)
    (h₂ : |c| ≤ C₁ * l / G) (h₃ : |al - 1| ≤ CN * u) (hd : d = b + c) (hu : 0 ≤ u) (hl : 0 ≤ l) (hG : 0 < G) :
    |a - d| ≤ (|C₂| + |CN| * |C₁|) * u * l / G := by
  have t₁ : C₂ * u * l / G ≤ |C₂| * u * l / G :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hu) hl) hG.le
  have t₂ : |al - 1| * |c| ≤ (|CN| * u) * (|C₁| * l / G) := by
    refine mul_le_mul (h₃.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hu)) (h₂.trans ?_) (abs_nonneg _)
      (by positivity)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hl) hG.le
  have e₁ : a - d = (a - b - al * c) + (al - 1) * c := by
    rw [hd]
    ring
  have e₂ : (|C₂| + |CN| * |C₁|) * u * l / G = |C₂| * u * l / G + (|CN| * u) * (|C₁| * l / G) := by
    field_simp
  rw [e₁, e₂]
  refine (abs_add_le _ _).trans (add_le_add (h₁.trans t₁) ?_)
  rw [abs_mul]
  exact t₂
end RemainderHessianAux
open RemainderHessianAux in
theorem remainderHessianAtFrameField_holds (hP : WeightedResponses.stepRemainderAtFrameFieldStatement)
    (hZ : frameFieldResponseAtIdentityStatement) (hN : responseCoeffNearOneStatement)
    (hF : responsesHaveFormsStatement) (hSh : ResponseInTheExpansion.levelSharesUniformStatement) :
    remainderHessianAtFrameFieldStatement := by
  classical
  have hOn' : ∀ T : RenormalizationStepParameters.ParameterAssignment, T.HoldsFrom WeightedResponses.ColdRegimeEstimatesAt →
      T.HoldsFrom fun U => WeightedResponses.ColdRegimeEstimatesAt U ∧
        WeightedResponses.blockSumExpectationNearValueAt U :=
    fun _ ⟨c, nss, ht, h⟩ => ⟨c, nss, ht, fun y hy => ⟨h y hy, (h y hy).nearValue⟩⟩
  unfold frameFieldResponseAtIdentityStatement ForAllPoints at hZ
  unfold responseCoeffNearOneStatement ForAllPoints at hN
  unfold responsesHaveFormsStatement ForAllPoints at hF
  unfold ResponseInTheExpansion.levelSharesUniformStatement at hSh
  have all := forAllParameters_and hZ (forAllParameters_and hN
    (forAllParameters_and hF (forAllParameters_of_holdsOnAllParameters hSh)))
  unfold remainderHessianAtFrameFieldStatement ForAllPoints ForAllParameters
  intro a ha
  obtain ⟨L₁, r₁, p₁, g₁⟩ := hP a ha
  obtain ⟨L₂, r₂, C₂', p₂, g₂⟩ := all a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), C₂', fun c => lt_min (p₁ c) (p₂ c), ?_⟩
  intro L hodd hL T hTa hTL hD hCS hOn hrt hCd Kr hFit
  have hL₁ : L₁ ≤ T.side := by
    rw [hTL]
    exact (le_max_left _ _).trans hL
  obtain ⟨C₁, f₁⟩ := g₁ T hTa hL₁ hD hCS (hOn' T hOn) (hrt.trans (min_le_left _ _))
  obtain ⟨C₂, y₁, f₂⟩ := f₁ Kr
  obtain ⟨y₂, f₃⟩ := g₂ L hodd ((le_max_right _ _).trans hL) T hTa hTL hD hCS hOn
    (hrt.trans (min_le_right _ _)) hCd Kr hFit
  refine ⟨max (max y₁ y₂) T.floorMin, fun y hy hRt hWy gg hg hgy k _ hk2 hk8 R d hd => ?_⟩
  have hyy₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hyy₂ : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy₁ : 1 ≤ y := hD.yC_ge.trans ((le_max_left _ _).trans ((le_max_right _ _).trans hy))
  obtain ⟨⟨CZ, _, _, _, _, bZ⟩, ⟨CN, _, _, _, _, bN⟩, ⟨_, _, _, _, _, bF⟩, Csh, hCsh, bFam⟩ :=
    f₃ y hyy₂ hRt hWy gg hg hgy k hk2 hk8 R d hd
  refine ⟨fun _ => |C₂| + |CN 0| * |C₁|, 1, y, one_pos, le_rfl, fun S t ht n _ hn Y h c c' => ?_⟩
  have ht' : t ≤ S.data.windowLevel := by omega
  have st : ResponseInTheExpansion.StageOnFlow T Kr y S.β t ⟨S.tower.stage t, S.resp t⟩ := by
    have h₁ := S.onFlow t ht'
    rw [← S.stage_eq t ht'] at h₁
    exact h₁
  have hK : (S.resp t).responseParams = Kr := st.params_eq
  have hxc : (S.tower.stage t).coupling = S.coupling t := st.coupling_eq
  have hLpos : 0 < (T.stepParameters y).side :=
    lt_of_lt_of_le (by norm_num) (show 2 ^ 40 ≤ T.side from hD.L_ge)
  have hnL : (T.stepParameters y).n₀ ≤ n * (T.stepParameters y).side :=
    hn.trans (Nat.le_mul_of_pos_right _ hLpos)
  have hσ : 0 < (T.stepParameters y).threshold := hD.σ_pos
  have cold : IsCold (T.stepParameters y).threshold (trivialField (n * (T.stepParameters y).side)) :=
    ResponseInTheExpansion.TermCalculus.isCold_trivialField hσ _
  have hP' : (S.resp (t + 1)).cold = (S.resp t).coldStep := by
    have a₁ := S.stage_eq (t + 1) ht
    have a₂ := S.stage_eq t ht'
    have a₃ : (⟨S.tower.stage (t + 1), S.resp (t + 1)⟩ : ResponseInTheExpansion.StageWithResponse (T.stepParameters y)) =
        ResponseInTheExpansion.nextStageWithResponse S.labelFacts T.lam
          (ResponseInTheExpansion.couplingsAlongFlow (T.stepParameters y) S.β (t + 2)) ⟨S.tower.stage t, S.resp t⟩ := by
      rw [a₁, a₂]
      rfl
    exact eq_of_heq (cold_heq_of_eq a₃)
  have hrest : remainderHessian (S.resp (t + 1)) n Y h c c' =
      hessianAtIdentity (WeightedResponses.responseRemainder (S.resp t).coldStep n Y h) c c' := by
    have e₀ : remainderHessian (S.resp (t + 1)) n Y h =
        hessianAtIdentity (WeightedResponses.responseRemainder (S.resp (t + 1)).cold n Y h) := rfl
    rw [e₀, hP']
    rfl
  have row := st.onFamily.admissible.bounds
  have hFam := (bFam (S.tower.stage t).depth).1
  have eS : ∀ z : TorusSite (n * (T.stepParameters y).side),
      ShareFamilies.levelShareFamily (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth
        (n * (T.stepParameters y).side) z =
      StepCosts.levelShare (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth
        Finset.univ z := by
    intro z
    funext W
    unfold ShareFamilies.levelShareFamily
    rw [dif_neg (NeZero.ne _)]
  have sm₁ : ∀ z, ContDiffThreeAt (WeightedResponses.responseRemainder (S.resp t).cold
      (n * (T.stepParameters y).side) z h) (trivialField _) := fun z =>
    row.remainder_smooth _ hnL z _ cold h
  have sm₂ : ∀ z, ContDiffThreeAt (StepCosts.levelShare (T.stepParameters y).coupling (T.stepParameters y).side
      (S.tower.stage t).depth Finset.univ z) (trivialField (n * (T.stepParameters y).side)) := by
    intro z
    rw [← eS]
    exact hFam.smooth _ hnL z _ cold
  set D : TorusSite (n * (T.stepParameters y).side) → ℝ := fun z =>
    WeightedResponses.blockMean (T.stepParameters y).side (S.tower.stage t).depth (n * (T.stepParameters y).side) z h -
      WeightedResponses.blockMean (T.stepParameters y).side ((S.tower.stage t).depth + 1) n Y h with hDdef
  have fr₁ : ∀ z, HasQuadraticFormAtIdentity (WeightedResponses.responseRemainder (S.resp t).cold
      (n * (T.stepParameters y).side) z h) := fun z =>
    (bF S t ht' (n * (T.stepParameters y).side) hnL z h).2.1
  have fr₂ : ∀ z, HasQuadraticFormAtIdentity (StepCosts.levelShare (T.stepParameters y).coupling
      (T.stepParameters y).side (S.tower.stage t).depth Finset.univ z) := fun z =>
    (bF S t ht' (n * (T.stepParameters y).side) hnL z h).1
  have zero₀ := finsetSum_hasQuadraticForm (n := n * (T.stepParameters y).side)
    (∅ : Finset (TorusSite (n * (T.stepParameters y).side))) (fun _ _ => 0) (by simp) (by simp)
  simp only [Finset.sum_empty] at zero₀
  have sm₃ : ∀ z, ContDiffThreeAt (fun W => D z * StepCosts.levelShare (T.stepParameters y).coupling
      (T.stepParameters y).side (S.tower.stage t).depth Finset.univ z W) (trivialField (n * (T.stepParameters y).side)) :=
    fun z k c₀ X₀ => contDiffAt_const.mul (sm₂ z k c₀ X₀)
  have fr₃ : ∀ z, HasQuadraticFormAtIdentity (fun W => D z * StepCosts.levelShare (T.stepParameters y).coupling
      (T.stepParameters y).side (S.tower.stage t).depth Finset.univ z W) := by
    intro z
    have h₀ := hasQuadraticForm_add_smul (D z) zero₀.1 (sm₂ z) zero₀.2.1 (fr₂ z)
    have e : (fun W => (0 : ℝ) + D z * StepCosts.levelShare (T.stepParameters y).coupling
        (T.stepParameters y).side (S.tower.stage t).depth Finset.univ z W) =
        fun W => D z * StepCosts.levelShare (T.stepParameters y).coupling
          (T.stepParameters y).side (S.tower.stage t).depth Finset.univ z W := by
      funext W
      ring
    rwa [e] at h₀
  obtain ⟨a₁, a₂, a₃⟩ := finsetSum_hasQuadraticForm (TorusLumps.sitesInBlocks (T.stepParameters y).side {Y})
    (fun z => WeightedResponses.responseRemainder (S.resp t).cold (n * (T.stepParameters y).side) z h)
    (fun z _ => sm₁ z) (fun z _ => fr₁ z)
  obtain ⟨b₁, b₂, b₃⟩ := finsetSum_hasQuadraticForm (TorusLumps.sitesInBlocks (T.stepParameters y).side {Y})
    (fun z W => D z * StepCosts.levelShare (T.stepParameters y).coupling (T.stepParameters y).side
      (S.tower.stage t).depth Finset.univ z W) (fun z _ => sm₃ z) (fun z _ => fr₃ z)
  obtain ⟨Z, z₁, z₂, z₃⟩ := bZ S t ht n hn
  have hsplit : ∑ z ∈ TorusLumps.sitesInBlocks (T.stepParameters y).side {Y}, hessianAtIdentity (fun V : TorusField n =>
        WeightedResponses.responseRemainder (S.resp t).cold (n * (T.stepParameters y).side) z h
          (ResponseInTheExpansion.coldFieldAboveFrames (S.tower.stage t).toStepSetup V 0) +
        D z * StepCosts.levelShare (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth
          Finset.univ z (ResponseInTheExpansion.coldFieldAboveFrames (S.tower.stage t).toStepSetup V 0)) c c' =
      hessianAtIdentity (fun V : TorusField n => ∑ z ∈ TorusLumps.sitesInBlocks (T.stepParameters y).side {Y},
        WeightedResponses.responseRemainder (S.resp t).cold (n * (T.stepParameters y).side) z h
          (ResponseInTheExpansion.coldFieldAboveFrames (S.tower.stage t).toStepSetup V 0)) c c' +
      hessianAtIdentity (fun V : TorusField n => ∑ z ∈ TorusLumps.sitesInBlocks (T.stepParameters y).side {Y},
        D z * StepCosts.levelShare (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth
          Finset.univ z (ResponseInTheExpansion.coldFieldAboveFrames (S.tower.stage t).toStepSetup V 0)) c c' := by
    have l₁ := z₁ _ a₁ a₂ c c'
    have l₂ := z₁ _ b₁ b₂ c c'
    have l₃ : ∀ z, hessianAtIdentity (fun V : TorusField n =>
        WeightedResponses.responseRemainder (S.resp t).cold (n * (T.stepParameters y).side) z h
          (ResponseInTheExpansion.coldFieldAboveFrames (S.tower.stage t).toStepSetup V 0) +
        D z * StepCosts.levelShare (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth
          Finset.univ z (ResponseInTheExpansion.coldFieldAboveFrames (S.tower.stage t).toStepSetup V 0)) c c' =
        RemainderHessianAux.pullbackForm Z c c' (hessianAtIdentity
          (WeightedResponses.responseRemainder (S.resp t).cold (n * (T.stepParameters y).side) z h)) +
        RemainderHessianAux.pullbackForm Z c c' (hessianAtIdentity (fun W => D z * StepCosts.levelShare (T.stepParameters y).coupling
          (T.stepParameters y).side (S.tower.stage t).depth Finset.univ z W)) := by
      intro z
      have h₀ := z₁ (fun W => WeightedResponses.responseRemainder (S.resp t).cold (n * (T.stepParameters y).side) z h W +
        D z * StepCosts.levelShare (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth
          Finset.univ z W)
        (fun k c₀ X₀ => (sm₁ z k c₀ X₀).add (sm₃ z k c₀ X₀))
        (hasQuadraticForm_add_smul (D z) (sm₁ z) (sm₂ z) (fr₁ z) (fr₂ z)) c c'
      refine h₀.trans ?_
      rw [← pullbackForm_add]
      unfold RemainderHessianAux.pullbackForm
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      have e₃ : hessianAtIdentity (fun W => D z * StepCosts.levelShare (T.stepParameters y).coupling
            (T.stepParameters y).side (S.tower.stage t).depth Finset.univ z W) b b' =
          D z * hessianAtIdentity (StepCosts.levelShare (T.stepParameters y).coupling
            (T.stepParameters y).side (S.tower.stage t).depth Finset.univ z) b b' :=
        ResponseInTheExpansion.TermCalculus.mixedDeriv_const_mul _ _ _ _ _ (by norm_num) (sm₂ z 2 _ _)
      show Z b c * _ * Z b' c' = Z b c * (hessianAtIdentity
          (WeightedResponses.responseRemainder (S.resp t).cold (n * (T.stepParameters y).side) z h) b b' +
        hessianAtIdentity (fun W => D z * StepCosts.levelShare (T.stepParameters y).coupling
          (T.stepParameters y).side (S.tower.stage t).depth Finset.univ z W) b b') * Z b' c'
      rw [e₃]
      exact congrArg (fun q => Z b c * q * Z b' c') (hessianAtIdentity_add_smul (D z) (sm₁ z) (sm₂ z) b b')
    rw [Finset.sum_congr rfl fun z _ => l₃ z, Finset.sum_add_distrib, l₁, l₂]
    have m₁ : ∑ b, ∑ b', Z b c * hessianAtIdentity (fun W => ∑ z ∈ TorusLumps.sitesInBlocks (T.stepParameters y).side {Y},
        WeightedResponses.responseRemainder (S.resp t).cold (n * (T.stepParameters y).side) z h W) b b' * Z b' c' =
        RemainderHessianAux.pullbackForm Z c c' (fun b b' => ∑ z ∈ TorusLumps.sitesInBlocks (T.stepParameters y).side {Y},
          hessianAtIdentity (WeightedResponses.responseRemainder (S.resp t).cold
            (n * (T.stepParameters y).side) z h) b b') := by
      unfold RemainderHessianAux.pullbackForm
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      rw [a₃]
    have m₂ : ∑ b, ∑ b', Z b c * hessianAtIdentity (fun W => ∑ z ∈ TorusLumps.sitesInBlocks (T.stepParameters y).side {Y},
        D z * StepCosts.levelShare (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth
          Finset.univ z W) b b' * Z b' c' =
        RemainderHessianAux.pullbackForm Z c c' (fun b b' => ∑ z ∈ TorusLumps.sitesInBlocks (T.stepParameters y).side {Y},
          hessianAtIdentity (fun W => D z * StepCosts.levelShare (T.stepParameters y).coupling
            (T.stepParameters y).side (S.tower.stage t).depth Finset.univ z W) b b') := by
      unfold RemainderHessianAux.pullbackForm
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      rw [b₃]
    rw [m₁, m₂, pullbackForm_sum, pullbackForm_sum]
  obtain ⟨t₁, t₂⟩ := f₂ y hyy₁ (S.tower.stage t).toStepSetup (S.resp t) hK st.onFamily st.isSymmetricWeight n hn Y h c c'
  have hnum := bN S t ht'
  have hG := ResponseInTheExpansion.TermCalculus.weight_pos (T.stepParameters y) (tripleDiam Y c c')
  have hxt : 0 ≤ S.coupling t ^ (-(1 / 2) : ℝ) := by
    have h₁ : y ≤ (S.tower.stage t).coupling := st.onFamily.onFamily.le_coupling
    exact Real.rpow_nonneg (by linarith) _
  have hlip0 : 0 ≤ WeightedResponses.weightLipschitz (T.stepParameters y).side ((S.tower.stage t).depth + 1) h :=
    Real.iSup_nonneg fun _ => div_nonneg (abs_nonneg _) (by unfold WeightedResponses.barycentreDist; positivity)
  rw [hrest]
  have hxc' : (S.tower.stage t).toStepSetup.coupling = S.coupling t := hxc
  rw [hxc'] at t₂
  exact abs_sub_le_of_three t₂ t₁ hnum hsplit hxt hlip0 hG
end YangMills.Construction.MomentLaw
end
