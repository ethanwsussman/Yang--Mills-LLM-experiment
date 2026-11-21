import YangMills.Construction.ClusterExpansionOfAStep.LawsOnProductsOfBalls
import YangMills.Construction.ColdStepAtMirrorFrames.CalculusOfLocalTerms
import YangMills.Construction.ColdStepAtMirrorFrames.ExponentsStayGood
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace PotentialStability
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
theorem differentiable_fderiv_apply {V : BondField ι → ℝ} (hV : ContDiff ℝ 3 V) (w : BondField ι) :
    Differentiable ℝ (fun x => fderiv ℝ V x w) :=
  ((hV.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)
theorem differentiable_of_contDiff_three {V : BondField ι → ℝ} (hV : ContDiff ℝ 3 V) :
    Differentiable ℝ V :=
  hV.differentiable (by norm_num)
theorem fderiv_comp_clm_apply {V : BondField ι → ℝ} (hV : ContDiff ℝ 3 V)
    (T : BondField κ →L[ℝ] BondField ι) (x w : BondField κ) :
    fderiv ℝ (fun y => V (T y)) x w = fderiv ℝ V (T x) (T w) := by
  have h := ((differentiable_of_contDiff_three hV (T x)).hasFDerivAt).comp x T.hasFDerivAt
  have e : (fun y => V (T y)) = V ∘ T := rfl
  rw [e, h.fderiv]
  rfl
theorem secondDerivAlong_comp_clm {V : BondField ι → ℝ} (hV : ContDiff ℝ 3 V)
    (T : BondField κ →L[ℝ] BondField ι) (y w z : BondField κ) :
    secondDerivAlong (fun y => V (T y)) y w z = secondDerivAlong V (T y) (T w) (T z) := by
  unfold secondDerivAlong
  have e : (fun x => fderiv ℝ (fun y => V (T y)) x w) = (fun p => fderiv ℝ V p (T w)) ∘ T := by
    funext x
    exact fderiv_comp_clm_apply hV T x w
  rw [e]
  have h := ((differentiable_fderiv_apply hV (T w) (T y)).hasFDerivAt).comp y T.hasFDerivAt
  rw [h.fderiv]
  rfl
theorem secondDerivAlong_zero_left (V : BondField ι → ℝ) (y z : BondField ι) :
    secondDerivAlong V y 0 z = 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BallLaws.secondDerivAlong_zero_left <;> assumption
theorem secondDerivAlong_zero_right (V : BondField ι → ℝ) (y w : BondField ι) :
    secondDerivAlong V y w 0 = 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BallLaws.secondDerivAlong_zero_right <;> assumption
theorem fderiv_linear_combination {F G : BondField ι → ℝ} (hF : ContDiff ℝ 3 F) (hG : ContDiff ℝ 3 G)
    (s t : ℝ) (x w : BondField ι) :
    fderiv ℝ (fun y => s * F y + t * G y) x w = s * fderiv ℝ F x w + t * fderiv ℝ G x w := by
  have h := (((differentiable_of_contDiff_three hF x).hasFDerivAt).const_mul s).add
    (((differentiable_of_contDiff_three hG x).hasFDerivAt).const_mul t)
  have e : HasFDerivAt (fun y => s * F y + t * G y) (s • fderiv ℝ F x + t • fderiv ℝ G x) x := h
  rw [e.fderiv]
  simp
theorem secondDerivAlong_linear_combination {F G : BondField ι → ℝ} (hF : ContDiff ℝ 3 F)
    (hG : ContDiff ℝ 3 G) (s t : ℝ) (y w z : BondField ι) :
    secondDerivAlong (fun y => s * F y + t * G y) y w z =
      s * secondDerivAlong F y w z + t * secondDerivAlong G y w z := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BallLaws.secondDerivAlong_linComb <;> assumption
theorem kernel_nonneg {ρ m r : ℝ} {d : ι → ι → ℝ} {V : BondField ι → ℝ} {K : ι → ι → ℝ}
    (hρ : 0 < ρ) (h : IsUniformlyConvexDecaying ρ m r d V K) (p q : ι) : 0 ≤ K p q := by apply _root_.YangMills.Construction.ConvexMeasures.LocalCovariance.kernel_nonneg <;> assumption
theorem pseudoMetric_nonneg {d : ι → ι → ℝ} (hd : IsPseudoMetricOnBonds d) (p q : ι) :
    0 ≤ d p q := by apply _root_.YangMills.Construction.ConvexMeasures.LocalCovariance.pseudoMetric_nonneg <;> assumption
theorem expWeight_sub_one_nonneg {r : ℝ} {d : ι → ι → ℝ} (hr : 0 ≤ r) (hd : IsPseudoMetricOnBonds d)
    (p q : ι) : 0 ≤ Real.exp (2 * r * d p q) - 1 := by
  have : 0 ≤ 2 * r * d p q := by
    have := pseudoMetric_nonneg hd p q
    positivity
  have := Real.add_one_le_exp (2 * r * d p q)
  linarith
theorem contDiff_halfSqNormOn (μ : ℝ) (Λ : Finset ι) :
    ContDiff ℝ 3 (halfSqNormOn μ Λ : BondField ι → ℝ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.contDiff_halfSqNormOn <;> assumption
theorem fderiv_halfSqNormOn_apply (μ : ℝ) (Λ : Finset ι) (x w : BondField ι) :
    fderiv ℝ (halfSqNormOn μ Λ) x w = ∑ p ∈ Λ, μ * ⟪x p, w p⟫_ℝ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.fderiv_halfSqNormOn_apply <;> assumption
theorem secondDerivAlong_halfSqNormOn (μ : ℝ) (Λ : Finset ι) (y w z : BondField ι) :
    secondDerivAlong (halfSqNormOn μ Λ) y w z = ∑ p ∈ Λ, μ * ⟪z p, w p⟫_ℝ := by
  unfold secondDerivAlong
  have e : (fun x => fderiv ℝ (halfSqNormOn μ Λ) x w) = fun x => ∑ p ∈ Λ, μ * ⟪x p, w p⟫_ℝ := by
    funext x
    exact fderiv_halfSqNormOn_apply μ Λ x w
  rw [e]
  have hp : ∀ p ∈ Λ, HasFDerivAt (fun x : BondField ι => μ * ⟪x p, w p⟫_ℝ)
      (μ • (((innerSL ℝ (w p)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) p)))) y := by
    intro p _
    have h1 : (fun x : BondField ι => ⟪x p, w p⟫_ℝ) =
        fun x => ((innerSL ℝ (w p)).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) p)) x := by
      funext x
      simp [real_inner_comm]
    have h2 := (((innerSL ℝ (w p)).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) p)).hasFDerivAt (x := y))
    have h3 : HasFDerivAt (fun x : BondField ι => ⟪x p, w p⟫_ℝ) ((innerSL ℝ (w p)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) p)) y := by
      rw [h1]
      exact h2
    exact h3.const_mul μ
  have h := HasFDerivAt.fun_sum hp
  rw [h.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.proj_apply]
  apply Finset.sum_congr rfl
  intro p _
  simp [real_inner_comm]
def restrictCLM (Λ : Finset ι) : BondField ι →L[ℝ] BondField ι :=
  ContinuousLinearMap.pi fun p => if p ∈ Λ then
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) p else 0
theorem restrictCLM_apply (Λ : Finset ι) (y : BondField ι) :
    restrictCLM Λ y = restrictToBonds Λ y := by
  funext p
  by_cases h : p ∈ Λ <;> simp [restrictCLM, restrictToBonds, h]
def pushforwardCLM (j : κ → ι) : BondField κ →L[ℝ] BondField ι :=
  ContinuousLinearMap.pi fun p => ∑ k, if j k = p then
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => BondVector) k else 0
theorem pushforwardCLM_apply (j : κ → ι) (ξ : BondField κ) :
    pushforwardCLM j ξ = pushforwardField j ξ := by
  funext p
  simp only [pushforwardCLM, pushforwardField, ContinuousLinearMap.coe_pi',
    ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : j k = p <;> simp [h]
theorem pushforwardField_apply_image (j : κ → ι) (hj : Function.Injective j) (ξ : BondField κ)
    (k : κ) : pushforwardField j ξ (j k) = ξ k := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.pushforwardField_apply_image <;> assumption
theorem pushforwardField_apply_of_not_mem_range (j : κ → ι) (ξ : BondField κ) (p : ι)
    (h : ∀ k, j k ≠ p) : pushforwardField j ξ p = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.pushforwardField_apply_of_not_mem_range <;> assumption
theorem pushforwardField_bondVariation (j : κ → ι) (hj : Function.Injective j) (k : κ)
    (v : BondVector) : pushforwardField j (bondVariation k v) = bondVariation (j k) v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.pushforwardField_bondVariation <;> assumption
theorem norm_pushforwardField_lt {ρ : ℝ} (hρ : 0 < ρ) (j : κ → ι) (hj : Function.Injective j)
    (ξ : BondField κ) (h : ∀ k, ‖ξ k‖ < ρ) (p : ι) : ‖pushforwardField j ξ p‖ < ρ := by
  by_cases hp : ∃ k, j k = p
  · obtain ⟨k, rfl⟩ := hp
    rw [pushforwardField_apply_image j hj]
    exact h k
  · push Not at hp
    rw [pushforwardField_apply_of_not_mem_range j _ p hp]
    simpa using hρ
theorem sum_norm_sq_pushforwardField (j : κ → ι) (hj : Function.Injective j) (ξ : BondField κ) :
    ∑ p, ‖pushforwardField j ξ p‖ ^ 2 = ∑ k, ‖ξ k‖ ^ 2 := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image j))]
  · rw [Finset.sum_image (fun a _ b _ h => hj h)]
    exact Finset.sum_congr rfl fun k _ => by rw [pushforwardField_apply_image j hj]
  · intro p _ hp
    have : ∀ k, j k ≠ p := fun k e => hp (by simp [← e])
    simp [pushforwardField_apply_of_not_mem_range j _ p this]
theorem restrictToBonds_bondVariation_of_mem (Λ : Finset ι) {p : ι} (hp : p ∈ Λ) (v : BondVector) :
    restrictToBonds Λ (bondVariation p v) = bondVariation p v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.restrictToBonds_bondVariation_of_mem <;> assumption
theorem restrictToBonds_bondVariation_of_not_mem (Λ : Finset ι) {p : ι} (hp : p ∉ Λ)
    (v : BondVector) : restrictToBonds Λ (bondVariation p v) = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.restrictToBonds_bondVariation_of_not_mem <;> assumption
end PotentialStability
open PotentialStability in
theorem admissiblePotentialStability_holds : AdmissiblePotentialStability := by
  intro ι _ _ ρ m r μ d hρ hm hr hd hμ
  have hμ0 : 0 < μ := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro F G t ⟨KF, hF, sF⟩ ⟨KG, hG, sG⟩ ht0 ht1
    have ht1' : 0 ≤ 1 - t := by linarith
    have eseg : segmentInterpolant F G t = fun y => (1 - t) * F y + t * G y := by
      funext y
      simp only [segmentInterpolant]
      ring
    rw [eseg]
    refine ⟨fun p q => (1 - t) * KF p q + t * KG p q, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact (contDiff_const.mul hF.smooth).add (contDiff_const.mul hG.smooth)
    · intro y hy w
      rw [secondDerivAlong_linear_combination hF.smooth hG.smooth]
      have h1 := hF.floor y hy w
      have h2 := hG.floor y hy w
      nlinarith [mul_le_mul_of_nonneg_left h1 ht1', mul_le_mul_of_nonneg_left h2 ht0]
    · intro y hy p q e e'
      rw [secondDerivAlong_linear_combination hF.smooth hG.smooth]
      have h1 := hF.kernel y hy p q e e'
      have h2 := hG.kernel y hy p q e e'
      calc |(1 - t) * secondDerivAlong F y (bondVariation p e) (bondVariation q e') +
              t * secondDerivAlong G y (bondVariation p e) (bondVariation q e')|
          ≤ (1 - t) * |secondDerivAlong F y (bondVariation p e) (bondVariation q e')| +
              t * |secondDerivAlong G y (bondVariation p e) (bondVariation q e')| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg ht1', abs_of_nonneg ht0]
        _ ≤ (1 - t) * (KF p q * ‖e‖ * ‖e'‖) + t * (KG p q * ‖e‖ * ‖e'‖) := by
            gcongr
        _ = _ := by ring
    · intro p q
      simp only [hF.symm p q, hG.symm p q]
    · intro p
      have h1 := hF.standingConstraints p
      have h2 := hG.standingConstraints p
      calc ∑ q, ((1 - t) * KF p q + t * KG p q) * (Real.exp (2 * r * d p q) - 1)
          = (1 - t) * ∑ q, KF p q * (Real.exp (2 * r * d p q) - 1) +
              t * ∑ q, KG p q * (Real.exp (2 * r * d p q) - 1) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun _ _ => by ring
        _ ≤ (1 - t) * m + t * m := by gcongr
        _ = m := by ring
    · intro p e
      have h1 := sF p e
      have h2 := sG p e
      unfold bondPartialDeriv at *
      rw [fderiv_linear_combination hF.smooth hG.smooth]
      calc |(1 - t) * fderiv ℝ F 0 (bondVariation p e) + t * fderiv ℝ G 0 (bondVariation p e)|
          ≤ (1 - t) * |fderiv ℝ F 0 (bondVariation p e)| +
              t * |fderiv ℝ G 0 (bondVariation p e)| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg ht1', abs_of_nonneg ht0]
        _ ≤ (1 - t) * (Real.sqrt m * ‖e‖) + t * (Real.sqrt m * ‖e‖) := by gcongr
        _ = _ := by ring
  · refine ⟨fun p q => if p = q then μ else 0, ⟨contDiff_halfSqNormOn μ _, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro y _ w
      rw [secondDerivAlong_halfSqNormOn]
      simp only [Finset.mem_univ, real_inner_self_eq_norm_sq]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p _
      have := sq_nonneg ‖w p‖
      nlinarith
    · intro y _ p q e e'
      rw [secondDerivAlong_halfSqNormOn]
      by_cases hpq : p = q
      · subst hpq
        rw [Finset.sum_eq_single p]
        · simp only [bondVariation, Pi.single_eq_same, if_true]
          rw [abs_mul, abs_of_pos hμ0]
          have := abs_real_inner_le_norm e' e
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hμ0.le
          linarith [mul_comm ‖e'‖ ‖e‖]
        · intro c _ hc
          simp [bondVariation, hc]
        · simp
      · rw [Finset.sum_eq_zero]
        · simp [hpq]
        · intro c _
          by_cases h1 : c = p
          · subst h1
            have : c ≠ q := hpq
            simp [bondVariation, this]
          · simp [bondVariation, h1]
    · intro p q
      by_cases h : p = q
      · simp [h]
      · simp [h, Ne.symm h]
    · intro p
      have : ∑ q, (if p = q then μ else 0) * (Real.exp (2 * r * d p q) - 1) = 0 := by
        rw [Finset.sum_eq_single p]
        · simp [hd.self]
        · intro c _ hc
          simp [Ne.symm hc]
        · simp
      rw [this]
      exact hm.le
    · intro p e
      unfold bondPartialDeriv
      rw [fderiv_halfSqNormOn_apply]
      simp only [Pi.zero_apply, inner_zero_left, mul_zero, Finset.sum_const_zero, abs_zero]
      positivity
  · rintro V Λ ⟨K, hK, sK⟩
    have hV := hK.smooth
    set T := restrictCLM Λ with hT
    have eT : ∀ y, T y = restrictToBonds Λ y := restrictCLM_apply Λ
    have hcomp : ContDiff ℝ 3 (fun y => V (T y)) := hV.comp T.contDiff
    have efr : frozenPotential Λ μ V = fun y => 1 * V (T y) + 1 * halfSqNormOn μ Λᶜ y := by
      funext y
      simp only [frozenPotential, eT, one_mul]
    have hsec : ∀ y w z, secondDerivAlong (frozenPotential Λ μ V) y w z =
        secondDerivAlong V (restrictToBonds Λ y) (restrictToBonds Λ w) (restrictToBonds Λ z) +
          ∑ p ∈ Λᶜ, μ * ⟪z p, w p⟫_ℝ := by
      intro y w z
      rw [efr, secondDerivAlong_linear_combination hcomp (contDiff_halfSqNormOn μ _),
        secondDerivAlong_halfSqNormOn, secondDerivAlong_comp_clm hV]
      simp only [eT, one_mul]
    have hball : ∀ y : BondField ι, (∀ p, ‖y p‖ < ρ) → ∀ p, ‖restrictToBonds Λ y p‖ < ρ := by
      intro y hy p
      by_cases h : p ∈ Λ
      · simpa [restrictToBonds, h] using hy p
      · simpa [restrictToBonds, h] using hρ
    refine ⟨fun p q => if p ∈ Λ ∧ q ∈ Λ then K p q else if p = q then μ else 0,
      ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [efr]
      exact (contDiff_const.mul hcomp).add (contDiff_const.mul (contDiff_halfSqNormOn μ _))
    · intro y hy w
      rw [hsec]
      have h1 := hK.floor _ (hball y hy) (restrictToBonds Λ w)
      have e1 : ∑ p ∈ Λᶜ, μ * ⟪w p, w p⟫_ℝ = ∑ p ∈ Λᶜ, μ * ‖w p‖ ^ 2 :=
        Finset.sum_congr rfl fun p _ => by rw [real_inner_self_eq_norm_sq]
      have e2 : ∑ p, ‖restrictToBonds Λ w p‖ ^ 2 = ∑ p ∈ Λ, ‖w p‖ ^ 2 := by
        rw [← Finset.sum_subset (Finset.subset_univ Λ)]
        · exact Finset.sum_congr rfl fun p hp => by simp [restrictToBonds, hp]
        · intro p _ hp
          simp [restrictToBonds, hp]
      have e3 : ∑ p, ‖w p‖ ^ 2 = ∑ p ∈ Λ, ‖w p‖ ^ 2 + ∑ p ∈ Λᶜ, ‖w p‖ ^ 2 :=
        (Finset.sum_add_sum_compl Λ _).symm
      rw [e1, e3, mul_add, ← Finset.mul_sum]
      rw [e2] at h1
      have h3 : 0 ≤ ∑ p ∈ Λᶜ, ‖w p‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
      nlinarith
    · intro y hy p q e e'
      rw [hsec]
      by_cases hp : p ∈ Λ
      · by_cases hq : q ∈ Λ
        · rw [restrictToBonds_bondVariation_of_mem Λ hp, restrictToBonds_bondVariation_of_mem Λ hq,
            Finset.sum_eq_zero]
          · simpa [hp, hq] using hK.kernel _ (hball y hy) p q e e'
          · intro c hc
            have hc' : c ∉ Λ := by simpa using hc
            have h1 : c ≠ p := fun h => hc' (h ▸ hp)
            simp [bondVariation, h1]
        · rw [restrictToBonds_bondVariation_of_not_mem Λ hq, secondDerivAlong_zero_right,
            Finset.sum_eq_zero]
          · have h1 : p ≠ q := fun h => hq (h ▸ hp)
            simp [hq, h1]
          · intro c hc
            have hc' : c ∉ Λ := by simpa using hc
            have h1 : c ≠ p := fun h => hc' (h ▸ hp)
            simp [bondVariation, h1]
      · rw [restrictToBonds_bondVariation_of_not_mem Λ hp, secondDerivAlong_zero_left, zero_add]
        by_cases hpq : p = q
        · subst hpq
          rw [Finset.sum_eq_single p]
          · simp only [bondVariation, Pi.single_eq_same]
            simp only [hp, false_and, if_false, if_true]
            rw [abs_mul, abs_of_pos hμ0, mul_assoc]
            refine mul_le_mul_of_nonneg_left ?_ hμ0.le
            have := abs_real_inner_le_norm e' e
            linarith [mul_comm ‖e'‖ ‖e‖]
          · intro c _ hc
            simp [bondVariation, hc]
          · intro h
            exact absurd (by simpa using hp) h
        · rw [Finset.sum_eq_zero]
          · simp [hp, hpq]
          · intro c _
            by_cases h1 : c = p
            · subst h1
              have : c ≠ q := hpq
              simp [bondVariation, this]
            · simp [bondVariation, h1]
    · intro p q
      by_cases h : p ∈ Λ ∧ q ∈ Λ
      · have h' : q ∈ Λ ∧ p ∈ Λ := ⟨h.2, h.1⟩
        simp only [h, h', and_self, if_true]
        exact hK.symm p q
      · have h' : ¬ (q ∈ Λ ∧ p ∈ Λ) := fun x => h ⟨x.2, x.1⟩
        simp only [h, h', if_false]
        by_cases e : p = q
        · simp [e]
        · simp [e, Ne.symm e]
    · intro p
      by_cases hp : p ∈ Λ
      · refine le_trans (Finset.sum_le_sum fun q _ => ?_) (hK.standingConstraints p)
        by_cases hq : q ∈ Λ
        · simp [hp, hq]
        · have h1 : p ≠ q := fun h => hq (h ▸ hp)
          simp only [hp, hq, and_false, if_false, h1, zero_mul]
          exact mul_nonneg (kernel_nonneg hρ hK p q) (expWeight_sub_one_nonneg hr hd p q)
      · have : ∑ q, (if p ∈ Λ ∧ q ∈ Λ then K p q else if p = q then μ else 0) *
            (Real.exp (2 * r * d p q) - 1) = 0 := by
          rw [Finset.sum_eq_single p]
          · simp [hd.self]
          · intro c _ hc
            simp [hp, Ne.symm hc]
          · simp
        rw [this]
        exact hm.le
    · intro p e
      unfold bondPartialDeriv
      have e0 : fderiv ℝ (frozenPotential Λ μ V) 0 (bondVariation p e) =
          fderiv ℝ V 0 (restrictToBonds Λ (bondVariation p e)) := by
        rw [efr]
        have := fderiv_linear_combination hcomp (contDiff_halfSqNormOn μ Λᶜ) 1 1 0 (bondVariation p e)
        rw [this, fderiv_comp_clm_apply hV, fderiv_halfSqNormOn_apply, map_zero T,
          eT (bondVariation p e)]
        simp
      rw [e0]
      by_cases hp : p ∈ Λ
      · rw [restrictToBonds_bondVariation_of_mem Λ hp]
        exact sK p e
      · rw [restrictToBonds_bondVariation_of_not_mem Λ hp]
        simp only [map_zero, abs_zero]
        positivity
  · intro κ _ _ j V hj ⟨K, hK, sK⟩
    have hV := hK.smooth
    set T := pushforwardCLM (ι := ι) j with hT
    have eT : ∀ ξ, T ξ = pushforwardField j ξ := pushforwardCLM_apply j
    have efr : (fun ξ => V (pushforwardField j ξ)) = fun ξ => V (T ξ) := by
      funext ξ
      rw [eT]
    rw [efr]
    have hcomp : ContDiff ℝ 3 (fun ξ => V (T ξ)) := hV.comp T.contDiff
    refine ⟨fun k k' => K (j k) (j k'), ⟨hcomp, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro y hy w
      rw [secondDerivAlong_comp_clm hV]
      simp only [eT]
      have h1 := hK.floor _ (norm_pushforwardField_lt hρ j hj y hy) (pushforwardField j w)
      rwa [sum_norm_sq_pushforwardField j hj] at h1
    · intro y hy p q e e'
      rw [secondDerivAlong_comp_clm hV]
      simp only [eT]
      rw [pushforwardField_bondVariation j hj, pushforwardField_bondVariation j hj]
      exact hK.kernel _ (norm_pushforwardField_lt hρ j hj y hy) _ _ e e'
    · intro k k'
      exact hK.symm _ _
    · intro k
      classical
      refine le_trans ?_ (hK.standingConstraints (j k))
      rw [← Finset.sum_image (s := Finset.univ) (g := j)
        (f := fun q => K (j k) q * (Real.exp (2 * r * d (j k) q) - 1)) (fun a _ b _ h => hj h)]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro q _ _
      exact mul_nonneg (kernel_nonneg hρ hK _ _) (expWeight_sub_one_nonneg hr hd _ _)
    · intro k e
      unfold bondPartialDeriv
      rw [fderiv_comp_clm_apply hV]
      simp only [eT]
      rw [pushforwardField_bondVariation j hj]
      have e0 : pushforwardField j (0 : BondField κ) = 0 := by
        funext p
        simp [pushforwardField]
      rw [e0]
      exact sK (j k) e
end YangMills.Construction.ColdStepAtMirrorFrames
end
