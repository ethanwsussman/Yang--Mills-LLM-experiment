import YangMills.Construction.ClusterExpansionOfAStep.LawsOnProductsOfBalls
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMembersAreClosed
import Mathlib
set_option autoImplicit false
noncomputable section
open Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.ConvexClass
set_option linter.unusedSectionVars false
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem secondDerivAlong_eq_fderiv_fderiv {f : BondField ι → ℝ} {η : BondField ι} (hf : ContDiff ℝ 3 f)
    (u v : BondField ι) : secondDerivAlong f η u v = fderiv ℝ (fderiv ℝ f) η v u := by
  have h2 : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) η := (h2.differentiable (by norm_num)) η
  unfold secondDerivAlong
  rw [(hd.hasFDerivAt.clm_apply (hasFDerivAt_const u η)).fderiv]
  simp
theorem differentiableAt_fderiv_apply {f : BondField ι → ℝ} (hf : ContDiff ℝ 3 f) (u : BondField ι)
    (η : BondField ι) : DifferentiableAt ℝ (fun ζ => fderiv ℝ f ζ u) η := by
  have h2 : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  exact ((h2.differentiable (by norm_num)) η).clm_apply (differentiableAt_const u)
theorem secondDerivAlong_linearComb {f g : BondField ι → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (s t : ℝ) (η u v : BondField ι) :
    secondDerivAlong (fun ζ => s * f ζ + t * g ζ) η u v =
      s * secondDerivAlong f η u v + t * secondDerivAlong g η u v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BallLaws.secondDerivAlong_linComb <;> assumption
def weightedSqNormOn (T : Finset ι) (m : ℝ) (η : BondField ι) : ℝ := ∑ b ∈ T, 2 * m * ‖η b‖ ^ 2
abbrev bondProj (b : ι) : BondField ι →L[ℝ] BondVector :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b
theorem contDiff_weightedSqNormOn (T : Finset ι) (m : ℝ) : ContDiff ℝ 3 (weightedSqNormOn T m) := by
  unfold weightedSqNormOn
  exact ContDiff.sum fun b _ => contDiff_const.mul
    ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ BondVector b))
theorem hasFDerivAt_weightedSqNormOn (T : Finset ι) (m : ℝ) (ζ : BondField ι) :
    HasFDerivAt (weightedSqNormOn T m) (∑ b ∈ T, (4 * m) • (innerSL ℝ (ζ b)).comp (bondProj b)) ζ := by
  have h : ∀ b ∈ T, HasFDerivAt (fun η : BondField ι => 2 * m * ‖η b‖ ^ 2)
      ((4 * m) • (innerSL ℝ (ζ b)).comp (bondProj b)) ζ := by
    intro b _
    have h1 : HasFDerivAt (fun η : BondField ι => η b) (bondProj b) ζ := (bondProj b).hasFDerivAt
    have h2 := (h1.norm_sq).const_mul (2 * m)
    refine h2.congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
      two_nsmul, ContinuousLinearMap.add_apply]
    ring
  exact HasFDerivAt.fun_sum h
theorem fderiv_weightedSqNormOn (T : Finset ι) (m : ℝ) (ζ u : BondField ι) :
    fderiv ℝ (weightedSqNormOn T m) ζ u = ∑ b ∈ T, 4 * m * inner ℝ (u b) (ζ b) := by
  rw [(hasFDerivAt_weightedSqNormOn T m ζ).fderiv, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    innerSL_apply_apply, ContinuousLinearMap.proj_apply]
  rw [real_inner_comm]
theorem secondDerivAlong_weightedSqNormOn (T : Finset ι) (m : ℝ) (η u v : BondField ι) :
    secondDerivAlong (weightedSqNormOn T m) η u v = ∑ b ∈ T, 4 * m * inner ℝ (u b) (v b) := by
  have h1 : (fun ζ => fderiv ℝ (weightedSqNormOn T m) ζ u) =
      (∑ b ∈ T, (4 * m) • (innerSL ℝ (u b)).comp (bondProj b) : BondField ι →L[ℝ] ℝ) := by
    funext ζ
    rw [fderiv_weightedSqNormOn, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
      innerSL_apply_apply, ContinuousLinearMap.proj_apply]
  unfold secondDerivAlong
  rw [h1, ContinuousLinearMap.fderiv, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    innerSL_apply_apply, ContinuousLinearMap.proj_apply]
theorem sum_inner_bondVariation (T : Finset ι) (b b' : ι) (e e' : BondVector) :
    ∑ c ∈ T, (inner ℝ (bondVariation b e c) (bondVariation b' e' c) : ℝ) =
      if b = b' ∧ b ∈ T then inner ℝ e e' else 0 := by
  by_cases hb : b ∈ T
  · rw [Finset.sum_eq_single b]
    · by_cases hbb : b = b'
      · subst hbb
        simp [bondVariation, hb]
      · have : (Pi.single b' e' : BondField ι) b = 0 := Pi.single_eq_of_ne hbb _
        simp [bondVariation, hbb, this]
    · intro c _ hc
      simp [bondVariation, Pi.single_eq_of_ne hc]
    · intro h
      exact absurd hb h
  · rw [Finset.sum_eq_zero]
    · simp [hb]
    · intro c hc
      have : c ≠ b := fun h => hb (h ▸ hc)
      simp [bondVariation, Pi.single_eq_of_ne this]
theorem isConvexClassMember_sqNorm {ρ m κ : ℝ} {d : ι → ι → ℝ} (hm : 0 < m)
    (hd : IsPseudoMetricOnBonds d) :
    IsConvexClassMember ρ m κ d (fun η => ∑ b, 2 * m * ‖η b‖ ^ 2) := by
  refine ⟨weightedSqNormOn Finset.univ m, fun b b' => if b = b' then 4 * m else 0, fun η _ => rfl,
    ⟨contDiff_weightedSqNormOn _ _, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro η _ u
    rw [secondDerivAlong_weightedSqNormOn, Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖u b‖]
  · intro η _ b b' e e'
    rw [secondDerivAlong_weightedSqNormOn, ← Finset.mul_sum, sum_inner_bondVariation]
    by_cases hbb : b = b'
    · simp only [hbb, Finset.mem_univ, and_self, if_true]
      rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * m)]
      have := abs_real_inner_le_norm e e'
      nlinarith
    · simp [hbb]
  · intro b b'
    by_cases hbb : b = b'
    · simp [hbb]
    · simp [hbb, Ne.symm hbb]
  · intro b
    have : ∀ b' ∈ (Finset.univ : Finset ι), (if b = b' then 4 * m else 0) *
        (Real.exp (2 * κ * d b b') - 1) = 0 := by
      intro b' _
      by_cases hbb : b = b'
      · subst hbb
        simp [hd.self]
      · simp [hbb]
    rw [Finset.sum_eq_zero this]
    exact hm.le
  · intro b e
    have : bondPartialDeriv (weightedSqNormOn Finset.univ m) b 0 e = 0 := by
      unfold bondPartialDeriv
      rw [fderiv_weightedSqNormOn]
      simp
    rw [this]
    simp only [abs_zero]
    positivity
theorem isConvexClassMember_convexComb {ρ m κ : ℝ} {d : ι → ι → ℝ} (hm : 0 < m)
    {P Q : BondField ι → ℝ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hP : IsConvexClassMember ρ m κ d P)
    (hQ : IsConvexClassMember ρ m κ d Q) :
    IsConvexClassMember ρ m κ d fun η => t * P η + (1 - t) * Q η := by
  obtain ⟨Ψ₁, K₁, e₁, c₁, s₁⟩ := hP
  obtain ⟨Ψ₂, K₂, e₂, c₂, s₂⟩ := hQ
  have ht' : 0 ≤ 1 - t := by linarith
  refine ⟨fun η => t * Ψ₁ η + (1 - t) * Ψ₂ η, fun b b' => t * K₁ b b' + (1 - t) * K₂ b b', ?_,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro η hη
    simp only [e₁ η hη, e₂ η hη]
  · exact (contDiff_const.mul c₁.smooth).add (contDiff_const.mul c₂.smooth)
  · intro η hη u
    rw [secondDerivAlong_linearComb c₁.smooth c₂.smooth]
    have h1 := mul_le_mul_of_nonneg_left (c₁.floor η hη u) ht0
    have h2 := mul_le_mul_of_nonneg_left (c₂.floor η hη u) ht'
    nlinarith
  · intro η hη b b' e e'
    rw [secondDerivAlong_linearComb c₁.smooth c₂.smooth]
    have h1 := mul_le_mul_of_nonneg_left (c₁.kernel η hη b b' e e') ht0
    have h2 := mul_le_mul_of_nonneg_left (c₂.kernel η hη b b' e e') ht'
    calc _ ≤ |t * secondDerivAlong Ψ₁ η (bondVariation b e) (bondVariation b' e')| +
          |(1 - t) * secondDerivAlong Ψ₂ η (bondVariation b e) (bondVariation b' e')| := abs_add_le _ _
      _ = t * |secondDerivAlong Ψ₁ η (bondVariation b e) (bondVariation b' e')| +
          (1 - t) * |secondDerivAlong Ψ₂ η (bondVariation b e) (bondVariation b' e')| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg ht']
      _ ≤ _ := by nlinarith
  · intro b b'
    simp only [c₁.symm b b', c₂.symm b b']
  · intro b
    have h1 := mul_le_mul_of_nonneg_left (c₁.standingConstraints b) ht0
    have h2 := mul_le_mul_of_nonneg_left (c₂.standingConstraints b) ht'
    have h3 : ∑ b', (t * K₁ b b' + (1 - t) * K₂ b b') * (Real.exp (2 * κ * d b b') - 1) =
        t * ∑ b', K₁ b b' * (Real.exp (2 * κ * d b b') - 1) +
          (1 - t) * ∑ b', K₂ b b' * (Real.exp (2 * κ * d b b') - 1) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b' _ => ?_
      ring
    rw [h3]
    nlinarith
  · intro b e
    have hd1 : DifferentiableAt ℝ Ψ₁ 0 := (c₁.smooth.differentiable (by norm_num)) 0
    have hd2 : DifferentiableAt ℝ Ψ₂ 0 := (c₂.smooth.differentiable (by norm_num)) 0
    have h1 : HasFDerivAt (fun η => t * Ψ₁ η + (1 - t) * Ψ₂ η)
        (t • fderiv ℝ Ψ₁ 0 + (1 - t) • fderiv ℝ Ψ₂ 0) 0 :=
      (hd1.hasFDerivAt.const_mul t).add (hd2.hasFDerivAt.const_mul (1 - t))
    have h2 : bondPartialDeriv (fun η => t * Ψ₁ η + (1 - t) * Ψ₂ η) b 0 e =
        t * bondPartialDeriv Ψ₁ b 0 e + (1 - t) * bondPartialDeriv Ψ₂ b 0 e := by
      unfold bondPartialDeriv
      rw [h1.fderiv]
      simp
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_left (s₁ b e) ht0
    have h4 := mul_le_mul_of_nonneg_left (s₂ b e) ht'
    calc _ ≤ |t * bondPartialDeriv Ψ₁ b 0 e| + |(1 - t) * bondPartialDeriv Ψ₂ b 0 e| := abs_add_le _ _
      _ = t * |bondPartialDeriv Ψ₁ b 0 e| + (1 - t) * |bondPartialDeriv Ψ₂ b 0 e| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg ht']
      _ ≤ _ := by nlinarith
def restrictCLM (Λ : Finset ι) : BondField ι →L[ℝ] BondField ι :=
  ContinuousLinearMap.pi fun b => if b ∈ Λ then bondProj b else 0
theorem restrictCLM_apply (Λ : Finset ι) (η : BondField ι) :
    restrictCLM Λ η = restrictToSupport Λ η := by
  funext b
  by_cases h : b ∈ Λ <;> simp [restrictCLM, restrictToSupport, h]
theorem restrictCLM_bondVariation (Λ : Finset ι) (b : ι) (e : BondVector) :
    restrictCLM Λ (bondVariation b e) = if b ∈ Λ then bondVariation b e else 0 := by
  rw [restrictCLM_apply]
  funext c
  by_cases hc : c = b
  · subst hc
    by_cases h : c ∈ Λ <;> simp [restrictToSupport, h, bondVariation]
  · have : (Pi.single b e : BondField ι) c = 0 := Pi.single_eq_of_ne hc _
    by_cases h : c ∈ Λ <;> by_cases h' : b ∈ Λ <;> simp [restrictToSupport, h, h', bondVariation, this]
theorem secondDerivAlong_comp_restrictCLM {Ψ : BondField ι → ℝ} (hΨ : ContDiff ℝ 3 Ψ) (Λ : Finset ι)
    (η u v : BondField ι) :
    secondDerivAlong (Ψ ∘ restrictCLM Λ) η u v =
      secondDerivAlong Ψ (restrictCLM Λ η) (restrictCLM Λ u) (restrictCLM Λ v) := by
  have hd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have h1 : (fun ζ => fderiv ℝ (Ψ ∘ restrictCLM Λ) ζ u) =
      (fun ξ => fderiv ℝ Ψ ξ (restrictCLM Λ u)) ∘ restrictCLM Λ := by
    funext ζ
    rw [fderiv_comp ζ (hd _) (restrictCLM Λ).differentiableAt, (restrictCLM Λ).fderiv]
    rfl
  unfold secondDerivAlong
  rw [h1, fderiv_comp η (differentiableAt_fderiv_apply hΨ _ _) (restrictCLM Λ).differentiableAt,
    (restrictCLM Λ).fderiv]
  rfl
theorem isConvexClassMember_block {ρ m κ : ℝ} {d : ι → ι → ℝ} (hρ : 0 < ρ) (hm : 0 < m) (hκ : 0 ≤ κ)
    (hd : IsPseudoMetricOnBonds d) (hd0 : ∀ b b', 0 ≤ d b b') {P : BondField ι → ℝ} (Λ : Finset ι)
    (hP : IsConvexClassMember ρ m κ d P) :
    IsConvexClassMember ρ m κ d fun η =>
      P (restrictToSupport Λ η) + ∑ b ∈ Finset.univ \ Λ, 2 * m * ‖η b‖ ^ 2 := by
  obtain ⟨Ψ, K, e₁, c₁, s₁⟩ := hP
  set T : Finset ι := Finset.univ \ Λ with hT
  have hsm : ContDiff ℝ 3 (Ψ ∘ restrictCLM Λ) := c₁.smooth.comp (restrictCLM Λ).contDiff
  have hballs : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, ‖restrictCLM Λ η b‖ < ρ := by
    intro η hη b
    rw [restrictCLM_apply]
    by_cases h : b ∈ Λ
    · simpa [restrictToSupport, h] using hη b
    · simpa [restrictToSupport, h] using hρ
  have hsec : ∀ η u v : BondField ι,
      secondDerivAlong (fun ζ => (Ψ ∘ restrictCLM Λ) ζ + weightedSqNormOn T m ζ) η u v =
        secondDerivAlong Ψ (restrictCLM Λ η) (restrictCLM Λ u) (restrictCLM Λ v) +
          ∑ b ∈ T, 4 * m * inner ℝ (u b) (v b) := by
    intro η u v
    have h := secondDerivAlong_linearComb hsm (contDiff_weightedSqNormOn T m) 1 1 η u v
    simp only [one_mul] at h
    rw [h, secondDerivAlong_comp_restrictCLM c₁.smooth, secondDerivAlong_weightedSqNormOn]
  have hzero : ∀ (ξ w : BondField ι), secondDerivAlong Ψ ξ 0 w = 0 ∧ secondDerivAlong Ψ ξ w 0 = 0 := by
    intro ξ w
    rw [secondDerivAlong_eq_fderiv_fderiv c₁.smooth, secondDerivAlong_eq_fderiv_fderiv c₁.smooth]
    simp
  have hK0 : ∀ b b', 0 ≤ K b b' := by
    intro b b'
    set e₀ : BondVector := EuclideanSpace.single 0 1 with he₀
    have hn : ‖e₀‖ = 1 := by simp [he₀]
    have h := c₁.kernel 0 (fun b => by simpa using hρ) b b' e₀ e₀
    rw [hn] at h
    have := abs_nonneg (secondDerivAlong Ψ 0 (bondVariation b e₀) (bondVariation b' e₀))
    linarith
  have hw : ∀ b b', 0 ≤ Real.exp (2 * κ * d b b') - 1 := by
    intro b b'
    have : 1 ≤ Real.exp (2 * κ * d b b') := Real.one_le_exp (by have := hd0 b b'; positivity)
    linarith
  have hmemT : ∀ b, b ∈ T ↔ b ∉ Λ := by
    intro b
    simp [hT]
  refine ⟨fun ζ => (Ψ ∘ restrictCLM Λ) ζ + weightedSqNormOn T m ζ,
    fun b b' => if b ∈ Λ ∧ b' ∈ Λ then K b b' else if b = b' then 4 * m else 0, ?_,
    ⟨hsm.add (contDiff_weightedSqNormOn T m), ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro η hη
    have h1 := e₁ (restrictCLM Λ η) (hballs η hη)
    rw [restrictCLM_apply] at h1
    simp only [Function.comp, restrictCLM_apply, weightedSqNormOn, h1]
  · intro η hη u
    rw [hsec]
    have h1 := c₁.floor (restrictCLM Λ η) (hballs η hη) (restrictCLM Λ u)
    have h2 : ∑ b, ‖restrictCLM Λ u b‖ ^ 2 = ∑ b ∈ Λ, ‖u b‖ ^ 2 := by
      have : ∀ b, ‖restrictCLM Λ u b‖ ^ 2 = if b ∈ Λ then ‖u b‖ ^ 2 else 0 := by
        intro b
        rw [restrictCLM_apply]
        by_cases h : b ∈ Λ <;> simp [restrictToSupport, h]
      simp only [this]
      rw [Finset.sum_ite_mem]
      simp
    have h3 : ∑ b, ‖u b‖ ^ 2 = ∑ b ∈ T, ‖u b‖ ^ 2 + ∑ b ∈ Λ, ‖u b‖ ^ 2 :=
      (Finset.sum_sdiff (Finset.subset_univ Λ)).symm
    have h4 : ∑ b ∈ T, 4 * m * inner ℝ (u b) (u b) = 4 * m * ∑ b ∈ T, ‖u b‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [real_inner_self_eq_norm_sq]
    rw [h4, h3]
    rw [h2] at h1
    have h5 : 0 ≤ ∑ b ∈ T, ‖u b‖ ^ 2 := Finset.sum_nonneg fun b _ => sq_nonneg _
    nlinarith
  · intro η hη b b' e e'
    rw [hsec, ← Finset.mul_sum, sum_inner_bondVariation, restrictCLM_bondVariation,
      restrictCLM_bondVariation]
    have hin : |(inner ℝ e e' : ℝ)| ≤ ‖e‖ * ‖e'‖ := abs_real_inner_le_norm e e'
    by_cases hb : b ∈ Λ
    · by_cases hb' : b' ∈ Λ
      · have hnot : ¬ (b = b' ∧ b ∈ T) := fun h => (hmemT b).1 h.2 hb
        simp only [hb, hb', if_true, and_self, if_neg hnot, mul_zero, add_zero]
        exact c₁.kernel _ (hballs η hη) b b' e e'
      · have hnot : ¬ (b = b' ∧ b ∈ T) := fun h => (hmemT b).1 h.2 hb
        have hne : b ≠ b' := fun h => hb' (h ▸ hb)
        simp only [hb, hb', if_true, if_false, and_false, if_neg hnot, mul_zero, add_zero, hne]
        rw [(hzero _ _).2]
        simp
    · rw [if_neg hb, (hzero _ _).1, zero_add]
      have hnotand : ¬ (b ∈ Λ ∧ b' ∈ Λ) := fun h => hb h.1
      by_cases hbb : b = b'
      · subst hbb
        simp only [hnotand, if_false, if_true, (hmemT b).2 hb, and_self]
        rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * m)]
        nlinarith
      · simp [hbb, hnotand]
  · intro b b'
    by_cases h1 : b ∈ Λ ∧ b' ∈ Λ
    · have h2 : b' ∈ Λ ∧ b ∈ Λ := ⟨h1.2, h1.1⟩
      simp only [h1, h2, and_self, if_true, c₁.symm b b']
    · have h2 : ¬ (b' ∈ Λ ∧ b ∈ Λ) := fun h => h1 ⟨h.2, h.1⟩
      simp only [h1, h2, if_false, eq_comm]
  · intro b
    by_cases hb : b ∈ Λ
    · refine le_trans (Finset.sum_le_sum fun b' _ => ?_) (c₁.standingConstraints b)
      by_cases hb' : b' ∈ Λ
      · simp [hb, hb']
      · have hne : b ≠ b' := fun h => hb' (h ▸ hb)
        simp only [hb, hb', and_false, if_false, hne, zero_mul]
        exact mul_nonneg (hK0 b b') (hw b b')
    · have : ∀ b' ∈ (Finset.univ : Finset ι),
          (if b ∈ Λ ∧ b' ∈ Λ then K b b' else if b = b' then 4 * m else 0) *
            (Real.exp (2 * κ * d b b') - 1) = 0 := by
        intro b' _
        by_cases hbb : b = b'
        · subst hbb
          simp [hd.self]
        · simp [hb, hbb]
      rw [Finset.sum_eq_zero this]
      exact hm.le
  · intro b e
    have hd1 : DifferentiableAt ℝ (Ψ ∘ restrictCLM Λ) 0 := (hsm.differentiable (by norm_num)) 0
    have h1 : bondPartialDeriv (fun ζ => (Ψ ∘ restrictCLM Λ) ζ + weightedSqNormOn T m ζ) b 0 e =
        fderiv ℝ Ψ 0 (restrictCLM Λ (bondVariation b e)) := by
      have h2 := hd1.hasFDerivAt.add (hasFDerivAt_weightedSqNormOn T m 0)
      have h3 : HasFDerivAt (fun ζ => (Ψ ∘ restrictCLM Λ) ζ + weightedSqNormOn T m ζ) _ 0 := h2
      unfold bondPartialDeriv
      rw [h3.fderiv, ContinuousLinearMap.add_apply, ← (hasFDerivAt_weightedSqNormOn T m 0).fderiv,
        fderiv_weightedSqNormOn]
      have hc : fderiv ℝ (Ψ ∘ restrictCLM Λ) 0 (bondVariation b e) =
          fderiv ℝ Ψ 0 (restrictCLM Λ (bondVariation b e)) := by
        have hdΨ : DifferentiableAt ℝ Ψ (restrictCLM Λ 0) := (c₁.smooth.differentiable (by norm_num)) _
        rw [fderiv_comp 0 hdΨ (restrictCLM Λ).differentiableAt, (restrictCLM Λ).fderiv]
        simp
      rw [hc]
      simp
    rw [h1, restrictCLM_bondVariation]
    by_cases hb : b ∈ Λ
    · simp only [hb, if_true]
      exact s₁ b e
    · simp only [hb, if_false, map_zero, abs_zero]
      positivity
theorem convexClassClosure_holds : ConvexClassClosure := by
  intro ι _ _ ρ m κ d hρ hm hκ hd hd0
  exact ⟨isConvexClassMember_sqNorm hm hd,
    fun P Q t h0 h1 hP hQ => isConvexClassMember_convexComb hm h0 h1 hP hQ,
    fun P Λ hP => isConvexClassMember_block hρ hm hκ hd hd0 Λ hP⟩
end YangMills.Construction.ColdStepAtMirrorFrames.ConvexClass
end
