import YangMills.Construction.ClusterExpansionOfAStep.BondsOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.FunctionsNearTheBallsExtend
import YangMills.Construction.ClusterExpansionOfAStep.TwoSettingsOnABoxProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages ColdStepAtMirrorFrames StepSettings TorusFields TorusLumps
namespace ChartPotential
theorem coordNorm_toImaginary (z : EuclideanSpace ℝ (Fin 3)) : coordNorm z = ‖z‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coordNorm_eq_norm <;> assumption
section Calculus
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι] in
theorem continuous_add_smul (x w : BondField ι) : Continuous fun t : ℝ => x + t • w :=
  continuous_const.add (continuous_id.smul continuous_const)
omit [Fintype ι] [DecidableEq ι] in
theorem tendsto_add_smul_zero (x w : BondField ι) :
    Filter.Tendsto (fun t : ℝ => x + t • w) (nhds 0) (nhds x) := by
  simpa using (continuous_add_smul x w).tendsto 0
omit [DecidableEq ι] in
theorem hasDerivAt_comp_add_smul {f : BondField ι → ℝ} (hf : Differentiable ℝ f) (x w : BondField ι)
    (s : ℝ) : HasDerivAt (fun t : ℝ => f (x + t • w)) (fderiv ℝ f (x + s • w) w) s := by
  have hline : HasDerivAt (fun t : ℝ => x + t • w) w s := by
    simpa using ((hasDerivAt_id s).smul_const w).const_add x
  exact (hf _).hasFDerivAt.comp_hasDerivAt s hline
omit [Fintype ι] [DecidableEq ι] in
theorem eventuallyEq_comp_add_smul {f g : BondField ι → ℝ} {x w : BondField ι} {s : ℝ}
    (h : f =ᶠ[nhds (x + s • w)] g) :
    (fun t : ℝ => g (x + t • w)) =ᶠ[nhds s] fun t => f (x + t • w) :=
  (((continuous_add_smul x w).tendsto s).eventually h).mono fun _ ht => ht.symm
omit [DecidableEq ι] in
theorem deriv_comp_add_smul_of_eventuallyEq {f g : BondField ι → ℝ} (hf : Differentiable ℝ f)
    {x w : BondField ι} (h : f =ᶠ[nhds x] g) :
    deriv (fun t : ℝ => g (x + t • w)) 0 = fderiv ℝ f x w := by
  have h' : f =ᶠ[nhds (x + (0 : ℝ) • w)] g := by simpa using h
  rw [(eventuallyEq_comp_add_smul h').deriv_eq]
  simpa using (hasDerivAt_comp_add_smul hf x w 0).deriv
omit [DecidableEq ι] in
theorem differentiable_fderiv_apply {f : BondField ι → ℝ} (hf : ContDiff ℝ 3 f) (v : BondField ι) :
    Differentiable ℝ fun x => fderiv ℝ f x v := by
  have h2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
  exact fun x => ((h2 x).hasFDerivAt.clm_apply (hasFDerivAt_const v x)).differentiableAt
omit [DecidableEq ι] in
theorem deriv_deriv_comp_of_eventuallyEq {f g : BondField ι → ℝ} {x : BondField ι}
    (hf : ContDiff ℝ 3 f) (h : f =ᶠ[nhds x] g) (w w' : BondField ι) :
    deriv (fun t : ℝ => deriv (fun t' : ℝ => g (x + t • w + t' • w')) 0) 0 =
      secondDerivAlong f x w' w := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hall := (tendsto_add_smul_zero x w).eventually h.eventuallyEq_nhds
  have e : (fun t : ℝ => deriv (fun t' : ℝ => g (x + t • w + t' • w')) 0) =ᶠ[nhds 0]
      fun t => fderiv ℝ f (x + t • w) w' :=
    hall.mono fun t ht => deriv_comp_add_smul_of_eventuallyEq hd ht
  rw [e.deriv_eq]
  simpa [secondDerivAlong] using
    (hasDerivAt_comp_add_smul (differentiable_fderiv_apply hf w') x w 0).deriv
omit [DecidableEq ι] in
theorem deriv_deriv_line_of_eventuallyEq {f g : BondField ι → ℝ} {x : BondField ι}
    (hf : ContDiff ℝ 3 f) (h : f =ᶠ[nhds x] g) (v : BondField ι) :
    deriv (deriv fun t : ℝ => g (x + t • v)) 0 = secondDerivAlong f x v v := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hall := (tendsto_add_smul_zero x v).eventually h.eventuallyEq_nhds
  have e : (deriv fun t : ℝ => g (x + t • v)) =ᶠ[nhds 0] fun t => fderiv ℝ f (x + t • v) v :=
    hall.mono fun t ht =>
      (eventuallyEq_comp_add_smul ht).deriv_eq.trans (hasDerivAt_comp_add_smul hd x v t).deriv
  rw [e.deriv_eq]
  simpa [secondDerivAlong] using
    (hasDerivAt_comp_add_smul (differentiable_fderiv_apply hf v) x v 0).deriv
omit [Fintype ι] in
theorem update_add_smul_eq (x : BondField ι) (b : ι) (X : BondVector) (t : ℝ) :
    Function.update x b (x b + t • X) = x + t • bondVariation b X := by
  funext c
  by_cases h : c = b
  · subst h
    simp [bondVariation]
  · simp [bondVariation, Function.update_of_ne h, Pi.single_eq_of_ne h]
omit [DecidableEq ι] in
theorem secondDerivAlong_eq_fderiv_fderiv {f : BondField ι → ℝ} (hf : ContDiff ℝ 3 f)
    (x u v : BondField ι) : secondDerivAlong f x u v = fderiv ℝ (fderiv ℝ f) x v u := by
  have h2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
  have h : fderiv ℝ (fun y => fderiv ℝ f y u) x = _ :=
    ((h2 x).hasFDerivAt.clm_apply (hasFDerivAt_const u x)).fderiv
  unfold secondDerivAlong
  rw [h]
  simp
omit [DecidableEq ι] in
theorem secondDerivAlong_comm {f : BondField ι → ℝ} (hf : ContDiff ℝ 3 f) (x u v : BondField ι) :
    secondDerivAlong f x u v = secondDerivAlong f x v u := by
  rw [secondDerivAlong_eq_fderiv_fderiv hf, secondDerivAlong_eq_fderiv_fderiv hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp; norm_num)) v u
omit [Fintype ι] in
theorem bondVariation_smul (b : ι) (c : ℝ) (X : BondVector) :
    bondVariation b (c • X) = c • bondVariation b X := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LocalMeans.bondVariation_smul <;> assumption
theorem abs_secondDerivAlong_le_mul_norm {f : BondField ι → ℝ} {x : BondField ι} {b b' : ι} {k : ℝ}
    (hf : ContDiff ℝ 3 f)
    (h : ∀ X X' : BondVector, ‖X‖ = 1 → ‖X'‖ = 1 →
      |secondDerivAlong f x (bondVariation b X) (bondVariation b' X')| ≤ k)
    (e e' : BondVector) :
    |secondDerivAlong f x (bondVariation b e) (bondVariation b' e')| ≤ k * ‖e‖ * ‖e'‖ := by
  by_cases he : e = 0
  · subst he
    have : bondVariation b (0 : BondVector) = 0 := by simp [bondVariation]
    rw [this, secondDerivAlong_eq_fderiv_fderiv hf]
    simp
  by_cases he' : e' = 0
  · subst he'
    have : bondVariation b' (0 : BondVector) = 0 := by simp [bondVariation]
    rw [this, secondDerivAlong_eq_fderiv_fderiv hf]
    simp
  have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr he
  have hn' : ‖e'‖ ≠ 0 := norm_ne_zero_iff.mpr he'
  set X := ‖e‖⁻¹ • e with hX
  set X' := ‖e'‖⁻¹ • e' with hX'
  have u1 : ‖X‖ = 1 := by
    rw [hX, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have u2 : ‖X'‖ = 1 := by
    rw [hX', norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn']
  have e1 : e = ‖e‖ • X := by
    rw [hX, smul_smul, mul_inv_cancel₀ hn, one_smul]
  have e2 : e' = ‖e'‖ • X' := by
    rw [hX', smul_smul, mul_inv_cancel₀ hn', one_smul]
  have key : secondDerivAlong f x (bondVariation b e) (bondVariation b' e') =
      ‖e‖ * ‖e'‖ * secondDerivAlong f x (bondVariation b X) (bondVariation b' X') := by
    have hL : bondVariation b e = ‖e‖ • bondVariation b X := by rw [← bondVariation_smul, ← e1]
    have hL' : bondVariation b' e' = ‖e'‖ • bondVariation b' X' := by
      rw [← bondVariation_smul, ← e2]
    rw [secondDerivAlong_eq_fderiv_fderiv hf, secondDerivAlong_eq_fderiv_fderiv hf, hL, hL']
    simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [key, abs_mul, abs_of_nonneg (by positivity)]
  calc ‖e‖ * ‖e'‖ * _ ≤ ‖e‖ * ‖e'‖ * k := mul_le_mul_of_nonneg_left (h X X' u1 u2) (by positivity)
    _ = _ := by ring
end Calculus
theorem exp_le_inv_mul_exp_sub_one {κ d : ℝ} (hκ : 0 < κ) (hd : 1 ≤ d) :
    Real.exp (κ * d) ≤ (2 * κ)⁻¹ * (Real.exp (2 * κ * d) - 1) := by
  set t := κ * d with ht
  have ht0 : 0 ≤ t := by positivity
  have hκt : κ ≤ t := by nlinarith
  have hs := Real.self_le_sinh_iff.mpr ht0
  have e1 : Real.exp (2 * κ * d) - 1 = Real.exp t * (2 * Real.sinh t) := by
    have e2 : Real.exp (2 * κ * d) = Real.exp t * Real.exp t := by
      rw [← Real.exp_add]
      congr 1
      rw [ht]
      ring
    have e3 : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [e2, Real.sinh_eq]
    linear_combination e3
  rw [e1, ← mul_assoc, mul_comm _ (Real.exp t), mul_assoc]
  have hE := Real.exp_pos t
  have h2 : 1 ≤ (2 * κ)⁻¹ * (2 * Real.sinh t) := by
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    linarith
  calc Real.exp t = Real.exp t * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hE.le
end ChartPotential
open ChartPotential in
theorem chartPotentialConvex_of_extension (hE : BallExtensions.ContDiffExtensionNearBalls)
    (hBk : BondsPerBlockBound) : ChartPotentialConvex := by
  intro R lam C hσ hrt hx hlam n _ s u hs
  have hρ : 0 < R.ballRadius := by
    unfold StepSetup.ballRadius
    positivity
  have hin : ∀ η : BondField s.free, (∀ b, ‖η b‖ ≤ R.ballRadius) → s.InBalls η := fun η h b => by
    rw [coordNorm_toImaginary]
    exact h b
  have hin' : ∀ η : BondField s.free, s.InBalls η → ∀ b, ‖η b‖ ≤ R.ballRadius := fun η h b => by
    have := h b
    rwa [coordNorm_toImaginary] at this
  obtain ⟨U, hUo, hUb, hUc⟩ := hs.contDiffOn_nhds
  obtain ⟨Ψ, hΨ, hΨe⟩ :=
    hE s.free R.ballRadius 3 u U hρ hUo (fun η h => hUb η (hin η h)) (by exact_mod_cast hUc)
  have hΨ3 : ContDiff ℝ 3 Ψ := by exact_mod_cast hΨ
  obtain ⟨M, hM, hMr⟩ := hs.toHasDecay.decay
  set K : s.free → s.free → ℝ := fun b b' => min (min (M b b') (M b' b)) (C * R.coupling) with hK
  have hgerm : ∀ η : BondField s.free, s.InBalls η → Ψ =ᶠ[nhds η] u := fun η h =>
    hΨe η (hin' η h)
  have hrow : ∀ η : BondField s.free, s.InBalls η → ∀ (b b' : s.free) (X X' : BondVector),
      mixedSecondDeriv u η b b' X X' = secondDerivAlong Ψ η (bondVariation b' X') (bondVariation b X) := by
    intro η hη b b' X X'
    unfold mixedSecondDeriv
    simp only [update_add_smul_eq]
    exact deriv_deriv_comp_of_eventuallyEq hΨ3 (hgerm η hη) _ _
  have hunit : ∀ η : BondField s.free, s.InBalls η → ∀ (b b' : s.free) (X X' : BondVector),
      ‖X‖ = 1 → ‖X'‖ = 1 →
      |secondDerivAlong Ψ η (bondVariation b X) (bondVariation b' X')| ≤ K b b' := by
    intro η hη b b' X X' hX hX'
    refine le_min (le_min ?_ ?_) ?_
    · rw [secondDerivAlong_comm hΨ3, ← hrow η hη]
      exact hM η hη b b' X X' hX hX'
    · rw [← hrow η hη]
      exact hM η hη b' b X' X hX' hX
    · rw [secondDerivAlong_comm hΨ3, ← hrow η hη]
      exact hs.mixedSecondDeriv_le η hη b b' X X' hX hX'
  have h0 : s.InBalls (0 : BondField s.free) := hin 0 fun b => by simpa using hρ.le
  have hK0 : ∀ b b', 0 ≤ K b b' := by
    intro b b'
    have e1 : ‖(EuclideanSpace.single 0 1 : BondVector)‖ = 1 := by simp
    exact (abs_nonneg _).trans (hunit 0 h0 b b' _ _ e1 e1)
  have hfac : ∀ b b' : s.free, 0 ≤ Real.exp (2 * R.params.rt * s.bondDist b b') - 1 := by
    intro b b'
    have : 0 ≤ 2 * R.params.rt * s.bondDist b b' :=
      mul_nonneg (by positivity) (Nat.cast_nonneg _)
    linarith [Real.add_one_le_exp (2 * R.params.rt * s.bondDist b b')]
  have hKrow : ∀ b, ∑ b', K b b' * (Real.exp (2 * R.params.rt * s.bondDist b b') - 1) ≤
      R.coupling * lam / 8 := by
    intro b
    refine le_trans (Finset.sum_le_sum fun b' _ => ?_) (hMr b)
    exact mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) (hfac b b')
  refine ⟨Ψ, K, hgerm, ?_, fun b b' => min_le_right _ _, ?_⟩
  · refine ⟨hΨ3, ?_, ?_, ?_, hKrow⟩
    · intro η hη v
      have hη' : s.InBalls η := hin η fun b => (hη b).le
      have h1 := hs.toHasDecay.hessian_ge η hη' v
      rw [deriv_deriv_line_of_eventuallyEq hΨ3 (hgerm η hη')] at h1
      calc _ = R.coupling * lam / 4 * ∑ b, ‖v b‖ ^ 2 := by ring
        _ ≤ _ := h1
    · intro η hη b b' e e'
      exact abs_secondDerivAlong_le_mul_norm hΨ3 (hunit η (hin η fun b => (hη b).le) b b') e e'
    · intro b b'
      simp only [hK]
      rw [min_comm (M b b') (M b' b)]
  · intro b
    set κ := R.params.rt with hκ
    set m := R.coupling * lam / 8 with hm
    set bk : s.free → TorusSite n := fun c => bondBlock (R := R) c.1 with hbk
    have hCx : 0 ≤ C * R.coupling := (hK0 b b).trans (min_le_right _ _)
    have hterm : ∀ b' : s.free, K b b' * Real.exp (κ * s.bondDist b b') ≤
        (if bk b' = bk b then C * R.coupling else 0) +
          (2 * κ)⁻¹ * (K b b' * (Real.exp (2 * κ * s.bondDist b b') - 1)) := by
      intro b'
      have hnn : 0 ≤ (2 * κ)⁻¹ * (K b b' * (Real.exp (2 * κ * s.bondDist b b') - 1)) :=
        mul_nonneg (by positivity) (mul_nonneg (hK0 _ _) (hfac b b'))
      by_cases hb : bk b' = bk b
      · have hd0 : s.bondDist b b' = 0 := by
          simp only [ChartSetting.bondDist, bondBlockDist]
          have : bondBlock (R := R) b.1 = bondBlock (R := R) b'.1 := hb.symm
          rw [this, supDist_self]
          simp
        rw [if_pos hb, hd0]
        simp only [mul_zero, Real.exp_zero, mul_one, sub_self, add_zero]
        exact min_le_right _ _
      · rw [if_neg hb, zero_add]
        have hd1 : 1 ≤ s.bondDist b b' := by
          have : supDist (bondBlock (R := R) b.1) (bondBlock (R := R) b'.1) ≠ 0 := by
            intro h
            apply hb
            funext i
            have h1 := (supDist_le_iff _ _ 0).mp (le_of_eq h) i
            have h2 : (bondBlock (R := R) b.1 i - bondBlock (R := R) b'.1 i).valMinAbs = 0 := by
              omega
            have h3 := (ZMod.valMinAbs_eq_zero _).mp h2
            exact (sub_eq_zero.mp h3).symm
          simp only [ChartSetting.bondDist, bondBlockDist]
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
        have := exp_le_inv_mul_exp_sub_one hrt hd1
        calc _ ≤ K b b' * ((2 * κ)⁻¹ * (Real.exp (2 * κ * s.bondDist b b') - 1)) :=
              mul_le_mul_of_nonneg_left this (hK0 _ _)
          _ = _ := by ring
    have hcard : ((Finset.univ.filter fun b' : s.free => bk b' = bk b).card : ℝ) ≤
        R.params.blockBondBound := by
      refine le_trans ?_ (hBk R.params.side n (bk b))
      have : (Finset.univ.filter fun b' : s.free => bk b' = bk b).card ≤
          (Finset.univ.filter fun c : TorusBond (n * R.params.side) =>
            parentBlock R.params.side c.1 = bk b).card := by
        apply Finset.card_le_card_of_injOn Subtype.val
        · intro c hc
          simpa [hbk, bondBlock] using hc
        · exact fun x _ y _ h => Subtype.ext h
      exact_mod_cast this
    have hsum : ∑ b' ∈ Finset.univ.erase b,
        ((if bk b' = bk b then C * R.coupling else 0) +
          (2 * κ)⁻¹ * (K b b' * (Real.exp (2 * κ * s.bondDist b b') - 1))) ≤
        ∑ b', ((if bk b' = bk b then C * R.coupling else 0) +
          (2 * κ)⁻¹ * (K b b' * (Real.exp (2 * κ * s.bondDist b b') - 1))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro b' _ _
      apply add_nonneg
      · split_ifs
        · exact hCx
        · exact le_rfl
      · exact mul_nonneg (by positivity) (mul_nonneg (hK0 _ _) (hfac b b'))
    refine (Finset.sum_le_sum fun b' _ => hterm b').trans (hsum.trans ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    have h1 : ((Finset.univ.filter fun b' : s.free => bk b' = bk b).card : ℝ) * (C * R.coupling) ≤
        R.params.blockBondBound * (C * R.coupling) := mul_le_mul_of_nonneg_right hcard hCx
    have h2 : (2 * κ)⁻¹ * ∑ b', K b b' * (Real.exp (2 * κ * s.bondDist b b') - 1) ≤
        (2 * κ)⁻¹ * m := mul_le_mul_of_nonneg_left (hKrow b) (by positivity)
    have e : R.params.offDiagonalBound lam C * m =
        R.params.blockBondBound * (C * R.coupling) + (2 * κ)⁻¹ * m := by
      have hk : R.params.rt = κ := rfl
      have hk0 : κ ≠ 0 := hrt.ne'
      unfold StepParameters.offDiagonalBound
      rw [hk, hm]
      field_simp
    rw [e]
    exact add_le_add h1 h2
end YangMills.Construction.ClusterExpansionOfAStep
end
