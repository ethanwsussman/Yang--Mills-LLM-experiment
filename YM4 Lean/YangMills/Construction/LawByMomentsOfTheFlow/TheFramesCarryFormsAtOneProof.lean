import YangMills.Construction.LawByMomentsOfTheFlow.FormAgainstTwoDecayingForms
import YangMills.Construction.LawByMomentsOfTheFlow.ResponseOfTheFrameFieldAtOne
import YangMills.Construction.LawByMomentsOfTheFlow.TheFramesCarryFormsAtOne
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheParts
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
namespace PullbackForms
variable {m : ℕ} [NeZero m]
private theorem bilinear_sub_bilinear (q : BondBilinear m) (A A' B B' : TorusFields.TorusBond m → ℝ) :
    (∑ b, ∑ b', A b * q b b' * A' b') - ∑ b, ∑ b', B b * q b b' * B' b' =
      bilinearEval q (fun b => A b - B b) A' + bilinearEval q B (fun b => A' b - B' b) := by
  unfold bilinearEval
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring
end PullbackForms
open PullbackForms in
theorem framesPullbackForms (hZ : frameFieldResponseAtIdentityStatement) (hS : twoDecayingFormsSumStatement) :
    framesPullbackFormsStatement := by
  unfold frameFieldResponseAtIdentityStatement ForAllPoints ForAllParameters at hZ
  unfold framesPullbackFormsStatement ForAllPoints ForAllParameters
  intro a ha
  obtain ⟨L₀, r₀, C₀, p₀, g⟩ := hZ a ha
  refine ⟨L₀, r₀, C₀, p₀, fun L hodd hL T hTa hTL hD hCS hOn hrt hCd Kr hFit => ?_⟩
  obtain ⟨y₀, f⟩ := g L hodd hL T hTa hTL hD hCS hOn hrt hCd Kr hFit
  refine ⟨max y₀ T.floorMin, fun y hy hRt hWy gg hg hgy k _ hk2 hk8 R d hd => ?_⟩
  obtain ⟨C, _, _, _, _, bZ⟩ := f y ((le_max_left _ _).trans hy) hRt hWy gg hg hgy k hk2 hk8 R d hd
  have hfits := hD.fits y ((le_max_right _ _).trans hy)
  have hy₁ : 1 ≤ y := hD.yC_ge.trans ((le_max_left _ _).trans ((le_max_right _ _).trans hy))
  have hrt₀ : 0 < (T.stepParameters y).rt := hD.rt_pos
  have hn₁ : 0 < (T.stepParameters y).n₁ := by
    show 0 < (T.side : ℝ) ^ (1 / 640 : ℝ)
    have hL : 0 < T.side := lt_of_lt_of_le (by positivity) hD.L_ge
    exact Real.rpow_pos_of_pos (by exact_mod_cast hL) _
  obtain ⟨CS, hCS0, bS⟩ := hS (T.stepParameters y) hrt₀ hn₁ hD.L_odd (by
    show 2 ^ 21 ≤ T.side
    exact (Nat.pow_le_pow_right (by norm_num) (by norm_num)).trans hD.L_ge)
  refine ⟨fun _ => CS * |C 0| * (|C 0| + |C 1|) + CS * |C 1| * |C 0|, 1, y, one_pos, le_rfl,
    fun S t ht n _ hn Y e he gy hyp c c' => ?_⟩
  obtain ⟨Z, hZ₁, hZ₂, hZ₃⟩ := bZ S t ht n hn
  have hx : 1 ≤ S.coupling t := by
    have st : ResponseInTheExpansion.StageOnFlow T Kr y S.β t ⟨S.tower.stage t, S.resp t⟩ := by
      have h₁ := S.onFlow t (by omega)
      rw [← S.stage_eq t (by omega)] at h₁
      exact h₁
    have h₁ : y ≤ (S.tower.stage t).coupling := st.onFamily.onFamily.le_coupling
    have h₂ : (S.tower.stage t).coupling = S.coupling t := st.coupling_eq
    linarith
  set u := S.coupling t ^ (-(1 / 2) : ℝ) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg (by linarith) _
  have hu1 : u ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  set M : TorusFields.TorusBond (n * (T.stepParameters y).side) → TorusFields.TorusBond n → ℝ :=
    fun b c => WeightedResponses.responseKernel (T.stepParameters y).coupling (S.tower.stage t).anchorRadius
      (T.stepParameters y).side (S.tower.stage t).depth b c with hM
  have hex : ∀ (b : TorusFields.TorusBond (n * (T.stepParameters y).side)) (z : TorusFields.TorusBond n),
      0 ≤ Real.exp (-(2 * (T.stepParameters y).weightRate *
        TwoLevelMixtures.bondSiteDist (T.stepParameters y).side b z.1)) :=
    fun _ _ => (Real.exp_pos _).le
  have hR₁ : ∀ (z : TorusFields.TorusBond n) (b), |Z b z - M b z| ≤ (|C 0| * u) *
      Real.exp (-(2 * (T.stepParameters y).weightRate *
        TwoLevelMixtures.bondSiteDist (T.stepParameters y).side b z.1)) := fun z b =>
    (hZ₂ b z).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hu0) (hex b z))
  have hR₂ : ∀ (z : TorusFields.TorusBond n) (b), |M b z| ≤ |C 1| *
      Real.exp (-(2 * (T.stepParameters y).weightRate *
        TwoLevelMixtures.bondSiteDist (T.stepParameters y).side b z.1)) := fun z b =>
    (hZ₃ b z).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (hex b z))
  have hR₃ : ∀ (z : TorusFields.TorusBond n) (b), |Z b z| ≤ (|C 0| + |C 1|) *
      Real.exp (-(2 * (T.stepParameters y).weightRate *
        TwoLevelMixtures.bondSiteDist (T.stepParameters y).side b z.1)) := by
    intro z b
    have h₁ : |Z b z| ≤ |Z b z - M b z| + |M b z| := by
      have := abs_add_le (Z b z - M b z) (M b z)
      simpa using this
    have h₂ : |C 0| * u * Real.exp (-(2 * (T.stepParameters y).weightRate *
          TwoLevelMixtures.bondSiteDist (T.stepParameters y).side b z.1)) ≤
        |C 0| * Real.exp (-(2 * (T.stepParameters y).weightRate *
          TwoLevelMixtures.bondSiteDist (T.stepParameters y).side b z.1)) :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) hu1) (hex b z)
    have := hR₁ z b
    have := hR₂ z b
    rw [add_mul]
    linarith
  have hq : ∀ z ∈ TorusLumps.sitesInBlocks (T.stepParameters y).side {Y},
      IsDecayingAbout (T.stepParameters y) e z (hessianAtIdentity (gy z)) := fun z hz => (hyp z hz).2.2
  have s₁ := bS n Y c c' e (|C 0| * u) (|C 0| + |C 1|) (fun z => hessianAtIdentity (gy z))
    (fun b => Z b c - M b c) (fun b => Z b c') he
    (by positivity) (by positivity) hq (hR₁ c) (hR₃ c')
  have s₂ := bS n Y c c' e (|C 1|) (|C 0| * u) (fun z => hessianAtIdentity (gy z))
    (fun b => M b c) (fun b => Z b c' - M b c') he
    (by positivity) (by positivity) hq (hR₂ c) (hR₁ c')
  have e₁ : ∑ z ∈ TorusLumps.sitesInBlocks (T.stepParameters y).side {Y},
        hessianAtIdentity (fun V : TorusFields.TorusField n =>
          gy z (ResponseInTheExpansion.coldFieldAboveFrames (S.tower.stage t).toStepSetup V 0)) c c' -
      ∑ z ∈ TorusLumps.sitesInBlocks (T.stepParameters y).side {Y},
        pullbackForm (T.stepParameters y).coupling (S.tower.stage t).anchorRadius (T.stepParameters y).side
          (S.tower.stage t).depth (n := n) (hessianAtIdentity (gy z)) c c' =
      ∑ z ∈ TorusLumps.sitesInBlocks (T.stepParameters y).side {Y},
        (bilinearEval (hessianAtIdentity (gy z)) (fun b => Z b c - M b c) (fun b => Z b c') +
        bilinearEval (hessianAtIdentity (gy z)) (fun b => M b c) (fun b => Z b c' - M b c')) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [hZ₁ (gy z) (hyp z hz).1 (hyp z hz).2.1 c c']
    exact bilinear_sub_bilinear _ _ _ _ _
  have hG := ResponseInTheExpansion.TermCalculus.weight_pos (T.stepParameters y) (tripleDiam Y c c')
  show |_| ≤ _ * u * e / _
  rw [e₁]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have t₁ : ∑ z ∈ TorusLumps.sitesInBlocks (T.stepParameters y).side {Y},
      |bilinearEval (hessianAtIdentity (gy z)) (fun b => Z b c - M b c) (fun b => Z b c') +
        bilinearEval (hessianAtIdentity (gy z)) (fun b => M b c) (fun b => Z b c' - M b c')| ≤
      ∑ z ∈ TorusLumps.sitesInBlocks (T.stepParameters y).side {Y},
        |bilinearEval (hessianAtIdentity (gy z)) (fun b => Z b c - M b c) (fun b => Z b c')| +
      ∑ z ∈ TorusLumps.sitesInBlocks (T.stepParameters y).side {Y},
        |bilinearEval (hessianAtIdentity (gy z)) (fun b => M b c) (fun b => Z b c' - M b c')| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun z _ => abs_add_le _ _
  refine t₁.trans ((add_le_add s₁ s₂).trans (le_of_eq ?_))
  field_simp
end YangMills.Construction.MomentLaw
end
