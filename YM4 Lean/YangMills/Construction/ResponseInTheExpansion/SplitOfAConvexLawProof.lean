import YangMills.Construction.ClusterExpansionOfAStep.CutOfAConvexLawProof
import YangMills.Construction.ResponseInTheExpansion.FarVariablesSplitOverTheGasProof
import YangMills.Construction.ResponseInTheExpansion.SplitOfAConvexLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open ClusterExpansionOfAStep ColdStepAtMirrorFrames ClusterExpansionOfAStep.BallLaws
namespace ConvexDecoupling
set_option linter.unusedSectionVars false
variable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α] {ρ m κ : ℝ}
def splitPotential (c : ℝ) (I : Finset α) (Lam : α → Finset ι) (Ψ : BondField ι → ℝ) (η : BondField ι) : ℝ :=
  ∑ i ∈ I, Ψ (restrictCLM (Lam i) η) + gaussianOn c (Finset.univ \ I.biUnion Lam) η
def splitPotentialKernel (c : ℝ) (I : Finset α) (Lam : α → Finset ι) (K : ι → ι → ℝ) (b b' : ι) : ℝ :=
  ∑ i ∈ I, (if b ∈ Lam i ∧ b' ∈ Lam i then K b b' else 0) + if b = b' then c else 0
theorem sum_ite_mem_le_of_pairwiseDisjoint {I : Finset α} {Lam : α → Finset ι}
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (Lam i) (Lam j)) {b b' : ι} {k : ℝ} (hk : 0 ≤ k) :
    ∑ i ∈ I, (if b ∈ Lam i ∧ b' ∈ Lam i then k else 0) ≤ k := by
  by_cases h : ∃ i ∈ I, b ∈ Lam i ∧ b' ∈ Lam i
  · obtain ⟨i, hi, hb⟩ := h
    rw [Finset.sum_eq_single i]
    · simp [hb]
    · intro j hj hji
      rw [if_neg]
      rintro ⟨h1, _⟩
      exact Finset.disjoint_left.mp (hdis j hj i hi hji) h1 hb.1
    · exact fun hn => absurd hi hn
  · rw [Finset.sum_eq_zero]
    · exact hk
    · intro i hi
      rw [if_neg]
      exact fun hh => h ⟨i, hi, hh⟩
theorem contDiff_splitPotential {Ψ : BondField ι → ℝ} (h : ContDiff ℝ 3 Ψ) (c : ℝ) (I : Finset α) (Lam : α → Finset ι) :
    ContDiff ℝ 3 (splitPotential c I Lam Ψ) := by
  unfold splitPotential
  exact (ContDiff.sum fun i _ => h.comp (restrictCLM (Lam i)).contDiff).add (gaussianOn_contDiff c _)
theorem secondDerivAlong_sum_restrict {Ψ : BondField ι → ℝ} (h : ContDiff ℝ 3 Ψ) (I : Finset α) (Lam : α → Finset ι)
    (η u w : BondField ι) :
    secondDerivAlong (fun ζ => ∑ i ∈ I, Ψ (restrictCLM (Lam i) ζ)) η u w =
      ∑ i ∈ I, secondDerivAlong Ψ (restrictCLM (Lam i) η) (restrictCLM (Lam i) u) (restrictCLM (Lam i) w) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp [secondDerivAlong]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [secondDerivAlong_add (f := fun ζ => Ψ (restrictCLM (Lam a) ζ)) (g := fun ζ => ∑ i ∈ s, Ψ (restrictCLM (Lam i) ζ))
      (h.comp (restrictCLM (Lam a)).contDiff) (ContDiff.sum fun i _ => h.comp (restrictCLM (Lam i)).contDiff),
      secondDerivAlong_comp_clm h, ih]
theorem secondDerivAlong_splitPotential {Ψ : BondField ι → ℝ} (h : ContDiff ℝ 3 Ψ) (c : ℝ) (I : Finset α)
    (Lam : α → Finset ι) (η u w : BondField ι) :
    secondDerivAlong (splitPotential c I Lam Ψ) η u w =
      ∑ i ∈ I, secondDerivAlong Ψ (restrictCLM (Lam i) η) (restrictCLM (Lam i) u) (restrictCLM (Lam i) w) +
        c * ∑ x ∈ Finset.univ \ I.biUnion Lam, inner ℝ (w x) (u x) := by
  have e : splitPotential c I Lam Ψ =
      fun ζ => (∑ i ∈ I, Ψ (restrictCLM (Lam i) ζ)) + gaussianOn c (Finset.univ \ I.biUnion Lam) ζ := rfl
  rw [e, secondDerivAlong_add (f := fun ζ => ∑ i ∈ I, Ψ (restrictCLM (Lam i) ζ))
    (ContDiff.sum fun i _ => h.comp (restrictCLM (Lam i)).contDiff) (gaussianOn_contDiff c _),
    secondDerivAlong_sum_restrict h, gaussianOn_secondDerivAlong]
theorem sum_norm_sq_restrict (X : Finset ι) (u : BondField ι) :
    ∑ b, ‖restrictCLM X u b‖ ^ 2 = ∑ b ∈ X, ‖u b‖ ^ 2 := by
  rw [← Finset.sum_sdiff (Finset.subset_univ X)]
  have z : ∑ b ∈ Finset.univ \ X, ‖restrictCLM X u b‖ ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    have hb' : b ∉ X := (Finset.mem_sdiff.mp hb).2
    simp [restrictCLM_apply, restrictToSet, hb']
  rw [z, zero_add]
  refine Finset.sum_congr rfl fun b hb => ?_
  simp [restrictCLM_apply, restrictToSet, hb]
theorem isUniformlyConvexDecaying_splitPotential {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} {c : ℝ}
    (hρ : 0 < ρ) (hκ : 0 ≤ κ) (hd : IsPseudoMetricOnBonds d) (H : IsUniformlyConvexDecaying ρ m κ d Ψ K)
    (hc : 2 * m ≤ c) (hm : 0 < m)
    {I : Finset α} {Lam : α → Finset ι} (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (Lam i) (Lam j)) :
    IsUniformlyConvexDecaying ρ m κ d (splitPotential c I Lam Ψ) (splitPotentialKernel c I Lam K) := by
  have hc0 : 0 ≤ c := by linarith
  refine ⟨contDiff_splitPotential H.smooth c I Lam, ?_, ?_, ?_, ?_⟩
  · intro η hη u
    rw [secondDerivAlong_splitPotential H.smooth]
    have a : ∑ i ∈ I, 2 * m * ∑ b ∈ Lam i, ‖u b‖ ^ 2 ≤
        ∑ i ∈ I, secondDerivAlong Ψ (restrictCLM (Lam i) η) (restrictCLM (Lam i) u) (restrictCLM (Lam i) u) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have := H.floor (restrictCLM (Lam i) η) (restrictCLM_mem hρ hη) (restrictCLM (Lam i) u)
      rwa [sum_norm_sq_restrict] at this
    have e1 : ∑ i ∈ I, 2 * m * ∑ b ∈ Lam i, ‖u b‖ ^ 2 = 2 * m * ∑ b ∈ I.biUnion Lam, ‖u b‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_biUnion]
      exact fun i hi j hj hij => hdis i hi j hj hij
    have e2 : ∑ x ∈ Finset.univ \ I.biUnion Lam, inner ℝ (u x) (u x) =
        ∑ x ∈ Finset.univ \ I.biUnion Lam, ‖u x‖ ^ 2 :=
      Finset.sum_congr rfl fun x _ => real_inner_self_eq_norm_sq _
    have e3 : ∑ b, ‖u b‖ ^ 2 = ∑ x ∈ Finset.univ \ I.biUnion Lam, ‖u x‖ ^ 2 + ∑ b ∈ I.biUnion Lam, ‖u b‖ ^ 2 :=
      (Finset.sum_sdiff (Finset.subset_univ _)).symm
    rw [e2, e3]
    have hS : 0 ≤ ∑ x ∈ Finset.univ \ I.biUnion Lam, ‖u x‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    nlinarith
  · intro η hη b b' e e'
    rw [secondDerivAlong_splitPotential H.smooth]
    have hK := kernel_nonneg hρ H b b'
    have a1 : ∀ i ∈ I, |secondDerivAlong Ψ (restrictCLM (Lam i) η) (restrictCLM (Lam i) (bondVariation b e))
        (restrictCLM (Lam i) (bondVariation b' e'))| ≤
        (if b ∈ Lam i ∧ b' ∈ Lam i then K b b' else 0) * ‖e‖ * ‖e'‖ := by
      intro i _
      rw [restrictCLM_bondVariation, restrictCLM_bondVariation]
      by_cases h1 : b ∈ Lam i
      · by_cases h2 : b' ∈ Lam i
        · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
          exact H.kernel (restrictCLM (Lam i) η) (restrictCLM_mem hρ hη) b b' e e'
        · rw [if_neg h2, secondDerivAlong_zero_right, abs_zero, if_neg (fun hh => h2 hh.2)]
          simp
      · rw [if_neg h1, secondDerivAlong_zero_left, abs_zero, if_neg (fun hh => h1 hh.1)]
        simp
    have a2 := abs_sum_inner_bondVariation_le (Finset.univ \ I.biUnion Lam) b b' e e'
    have a3 : |∑ i ∈ I, secondDerivAlong Ψ (restrictCLM (Lam i) η) (restrictCLM (Lam i) (bondVariation b e))
        (restrictCLM (Lam i) (bondVariation b' e'))| ≤
        (∑ i ∈ I, if b ∈ Lam i ∧ b' ∈ Lam i then K b b' else 0) * ‖e‖ * ‖e'‖ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_le_sum a1
    unfold splitPotentialKernel
    calc _ ≤ |∑ i ∈ I, secondDerivAlong Ψ (restrictCLM (Lam i) η) (restrictCLM (Lam i) (bondVariation b e))
            (restrictCLM (Lam i) (bondVariation b' e'))| +
          |c * ∑ x ∈ Finset.univ \ I.biUnion Lam,
            inner ℝ ((bondVariation b' e' : BondField ι) x) ((bondVariation b e : BondField ι) x)| :=
          abs_add_le _ _
      _ ≤ (∑ i ∈ I, if b ∈ Lam i ∧ b' ∈ Lam i then K b b' else 0) * ‖e‖ * ‖e'‖ +
            c * ((if b = b' then 1 else 0) * ‖e‖ * ‖e'‖) := by
          rw [abs_mul, abs_of_nonneg hc0]
          gcongr
      _ = _ := by
          by_cases h : b = b' <;> simp [h] <;> ring
  · intro b b'
    unfold splitPotentialKernel
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [H.symm b b', and_comm]
    · simp only [eq_comm]
  · intro b
    refine le_trans ?_ (H.standingConstraints b)
    refine Finset.sum_le_sum fun b' _ => ?_
    by_cases h : b = b'
    · subst h
      simp [hd.self]
    · have hw : 0 ≤ Real.exp (2 * κ * d b b') - 1 := by
        have : 0 ≤ 2 * κ * d b b' := by
          have := pseudoMetric_nonneg hd b b'
          positivity
        linarith [Real.add_one_le_exp (2 * κ * d b b')]
      have hK := kernel_nonneg hρ H b b'
      unfold splitPotentialKernel
      rw [if_neg h, add_zero]
      exact mul_le_mul_of_nonneg_right (sum_ite_mem_le_of_pairwiseDisjoint hdis hK) hw
theorem sum_splitPotentialKernel_mul_exp_le {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} {c Bd : ℝ}
    (hρ : 0 < ρ) (H : IsUniformlyConvexDecaying ρ m κ d Ψ K) {I : Finset α} {Lam : α → Finset ι}
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (Lam i) (Lam j))
    (hA : ∀ b, ∑ b' ∈ Finset.univ.erase b, K b b' * Real.exp (κ * d b b') ≤ Bd) (b : ι) :
    ∑ b' ∈ Finset.univ.erase b, splitPotentialKernel c I Lam K b b' * Real.exp (κ * d b b') ≤ Bd := by
  refine le_trans (Finset.sum_le_sum fun b' hb' => ?_) (hA b)
  have h : b ≠ b' := fun e => (Finset.mem_erase.mp hb').1 e.symm
  unfold splitPotentialKernel
  rw [if_neg h, add_zero]
  exact mul_le_mul_of_nonneg_right (sum_ite_mem_le_of_pairwiseDisjoint hdis (kernel_nonneg hρ H b b'))
    (Real.exp_pos _).le
theorem sum_inner_bondVariation (S : Finset ι) (b : ι) (η : BondField ι) (e : BondVector) :
    ∑ x ∈ S, inner ℝ (η x) ((bondVariation b e : BondField ι) x) = if b ∈ S then inner ℝ (η b) e else 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.RestrictedLaw.sum_inner_bondVariation <;> assumption
theorem fderiv_sum_restrict {Ψ : BondField ι → ℝ} (h : ContDiff ℝ 3 Ψ) (I : Finset α) (Lam : α → Finset ι)
    (η a : BondField ι) :
    fderiv ℝ (fun ζ => ∑ i ∈ I, Ψ (restrictCLM (Lam i) ζ)) η a =
      ∑ i ∈ I, fderiv ℝ Ψ (restrictCLM (Lam i) η) (restrictCLM (Lam i) a) := by
  classical
  have d1 : ∀ i, DifferentiableAt ℝ (fun ζ => Ψ (restrictCLM (Lam i) ζ)) η := fun i =>
    (h.comp (restrictCLM (Lam i)).contDiff).differentiable (by norm_num) η
  have := (HasFDerivAt.fun_sum (u := I) (A := fun i ζ => Ψ (restrictCLM (Lam i) ζ)) (x := η)
    (fun i _ => (d1 i).hasFDerivAt)).fderiv
  erw [this]
  rw [ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => fderiv_comp_clm h _ _ _
theorem fderiv_sub_splitPotential {Ψ : BondField ι → ℝ} (h : ContDiff ℝ 3 Ψ) (c : ℝ) (I : Finset α)
    (Lam : α → Finset ι) (η a : BondField ι) :
    fderiv ℝ (fun ζ => Ψ ζ - splitPotential c I Lam Ψ ζ) η a =
      fderiv ℝ Ψ η a - ∑ i ∈ I, fderiv ℝ Ψ (restrictCLM (Lam i) η) (restrictCLM (Lam i) a) -
        c * ∑ x ∈ Finset.univ \ I.biUnion Lam, inner ℝ (η x) (a x) := by
  have d₀ : Differentiable ℝ Ψ := h.differentiable (by norm_num)
  have d₁ : DifferentiableAt ℝ (fun ζ => ∑ i ∈ I, Ψ (restrictCLM (Lam i) ζ)) η :=
    (ContDiff.sum fun i _ => h.comp (restrictCLM (Lam i)).contDiff).differentiable (by norm_num) η
  have d₂ : DifferentiableAt ℝ (gaussianOn c (Finset.univ \ I.biUnion Lam)) η :=
    (gaussianOn_contDiff c _).differentiable (by norm_num) η
  have e : (fun ζ => Ψ ζ - splitPotential c I Lam Ψ ζ) =
      fun ζ => Ψ ζ - ((∑ i ∈ I, Ψ (restrictCLM (Lam i) ζ)) + gaussianOn c (Finset.univ \ I.biUnion Lam) ζ) := rfl
  rw [e]
  have := ((d₀ η).hasFDerivAt.sub (d₁.hasFDerivAt.add d₂.hasFDerivAt)).fderiv
  erw [this]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
  rw [fderiv_sum_restrict h, gaussianOn_fderiv]
  ring
theorem abs_fderiv_sub_fderiv_restrict_le {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} (hρ : 0 < ρ)
    (H : IsUniformlyConvexDecaying ρ m κ d Ψ K) (X : Finset ι) {η : BondField ι} (hη : ∀ b, ‖η b‖ < ρ) (b : ι)
    (e : BondVector) :
    |fderiv ℝ Ψ η (bondVariation b e) - fderiv ℝ Ψ (restrictCLM X η) (bondVariation b e)| ≤
      ρ * (∑ b' ∈ Finset.univ \ X, K b b') * ‖e‖ := by
  set a : BondField ι := bondVariation b e with ha
  set ξ : BondField ι := η - restrictCLM X η with hξ
  have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => fderiv ℝ Ψ (restrictCLM X η + t • ξ) a)
      (secondDerivAlong Ψ (restrictCLM X η + t • ξ) a ξ) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => restrictCLM X η + t • ξ) ξ t := by
      simpa using ((hasDerivAt_id t).smul_const ξ).const_add (restrictCLM X η)
    exact (differentiable_fderiv_apply H.smooth a (restrictCLM X η + t • ξ)).hasFDerivAt.comp_hasDerivAt t h1
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖(restrictCLM X η + t • ξ) x‖ < ρ := by
    intro t ht x
    rw [hξ, restrictCLM_apply]
    by_cases hx : x ∈ X
    · simp [restrictToSet, hx, hη x]
    · simp only [restrictToSet, hx, if_false, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
        zero_add, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖η x‖ ≤ 1 * ‖η x‖ := by gcongr; exact ht.2
        _ < ρ := by simpa using hη x
  have hξsum : ξ = ∑ x ∈ Finset.univ \ X, bondVariation x (η x) := by
    funext y
    rw [Finset.sum_apply]
    rw [hξ, restrictCLM_apply]
    by_cases hy : y ∈ X
    · simp only [Pi.sub_apply, restrictToSet, hy, if_true, sub_self]
      symm
      refine Finset.sum_eq_zero fun x hx => ?_
      have : y ≠ x := fun hh => (Finset.mem_sdiff.mp hx).2 (hh ▸ hy)
      simp [bondVariation, Pi.single_eq_of_ne this]
    · simp only [Pi.sub_apply, restrictToSet, hy, if_false, sub_zero]
      rw [Finset.sum_eq_single y]
      · simp [bondVariation]
      · intro x _ hx
        simp [bondVariation, Pi.single_eq_of_ne hx.symm]
      · intro hn
        exact absurd (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩) hn
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖secondDerivAlong Ψ (restrictCLM X η + t • ξ) a ξ‖ ≤
      ρ * (∑ b' ∈ Finset.univ \ X, K b b') * ‖e‖ := by
    intro t ht
    rw [Real.norm_eq_abs]
    have e1 : secondDerivAlong Ψ (restrictCLM X η + t • ξ) a ξ =
        ∑ x ∈ Finset.univ \ X, secondDerivAlong Ψ (restrictCLM X η + t • ξ) a (bondVariation x (η x)) := by
      unfold secondDerivAlong
      rw [hξsum, map_sum]
    rw [e1]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun x _ => ?_
    have := H.kernel _ (hmem t ht) b x e (η x)
    have hK := kernel_nonneg hρ H b x
    calc _ ≤ K b x * ‖e‖ * ‖η x‖ := this
      _ ≤ K b x * ‖e‖ * ρ := by
          gcongr
          exact (hη x).le
      _ = ρ * K b x * ‖e‖ := by ring
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => fderiv ℝ Ψ (restrictCLM X η + t • ξ) a)
    (f' := fun t => secondDerivAlong Ψ (restrictCLM X η + t • ξ) a ξ)
    (s := Set.Icc (0 : ℝ) 1) (C := ρ * (∑ b' ∈ Finset.univ \ X, K b b') * ‖e‖) (x := 0) (y := 1)
    (fun t _ => (hder t).hasDerivWithinAt) hbound (convex_Icc 0 1) (by simp) (by simp)
  have e0 : restrictCLM X η + (0 : ℝ) • ξ = restrictCLM X η := by simp
  have e1 : restrictCLM X η + (1 : ℝ) • ξ = η := by simp [hξ]
  simp only [e0, e1] at hmv
  simpa [Real.norm_eq_abs] using hmv
theorem bondGradNorm_sub_splitPotential_le {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} {c C₁ : ℝ}
    (hρ : 0 < ρ) (H : IsUniformlyConvexDecaying ρ m κ d Ψ K) (hc : 0 ≤ c)
    (hf : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm Ψ b η ≤ C₁) {I : Finset α}
    {Lam : α → Finset ι} (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (Lam i) (Lam j)) {B : ι → ℝ}
    (hB1 : ∀ i ∈ I, ∀ b ∈ Lam i, ρ * ∑ b' ∈ Finset.univ \ Lam i, K b b' ≤ B b)
    (hB2 : ∀ b, (∀ i ∈ I, b ∉ Lam i) → C₁ + c * ρ ≤ B b)
    {η : BondField ι} (hη : ∀ b, ‖η b‖ < ρ) (b : ι) :
    bondGradNorm (fun ζ => Ψ ζ - splitPotential c I Lam Ψ ζ) b η ≤ B b := by
  have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans (hf η hη b)
  by_cases hb : ∃ i ∈ I, b ∈ Lam i
  · obtain ⟨i, hi, hbi⟩ := hb
    have hS : 0 ≤ ∑ b' ∈ Finset.univ \ Lam i, K b b' := Finset.sum_nonneg fun b' _ => kernel_nonneg hρ H b b'
    have hB0 : 0 ≤ ρ * ∑ b' ∈ Finset.univ \ Lam i, K b b' := mul_nonneg hρ.le hS
    refine le_trans (bondGradNorm_le_of_forall hB0 fun e => ?_) (hB1 i hi b hbi)
    rw [fderiv_sub_splitPotential H.smooth, sum_inner_bondVariation]
    have hoff : b ∉ Finset.univ \ I.biUnion Lam := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
      exact Finset.mem_biUnion.mpr ⟨i, hi, hbi⟩
    rw [if_neg hoff, mul_zero, sub_zero]
    have hone : ∑ j ∈ I, fderiv ℝ Ψ (restrictCLM (Lam j) η) (restrictCLM (Lam j) (bondVariation b e)) =
        fderiv ℝ Ψ (restrictCLM (Lam i) η) (bondVariation b e) := by
      rw [Finset.sum_eq_single i]
      · rw [restrictCLM_bondVariation, if_pos hbi]
      · intro j hj hji
        have : b ∉ Lam j := fun h => Finset.disjoint_left.mp (hdis j hj i hi hji) h hbi
        rw [restrictCLM_bondVariation, if_neg this, map_zero]
      · exact fun hn => absurd hi hn
    rw [hone]
    exact abs_fderiv_sub_fderiv_restrict_le hρ H (Lam i) hη b e
  · have hb' : ∀ i ∈ I, b ∉ Lam i := fun i hi h => hb ⟨i, hi, h⟩
    have hbS : b ∈ Finset.univ \ I.biUnion Lam := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion, not_exists, not_and]
      exact hb'
    refine le_trans (bondGradNorm_le_of_forall (by positivity) fun e => ?_) (hB2 b hb')
    rw [fderiv_sub_splitPotential H.smooth, sum_inner_bondVariation, if_pos hbS]
    have hz : ∑ j ∈ I, fderiv ℝ Ψ (restrictCLM (Lam j) η) (restrictCLM (Lam j) (bondVariation b e)) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [restrictCLM_bondVariation, if_neg (hb' j hj), map_zero]
    rw [hz, sub_zero]
    have h1 := abs_fderiv_bondVariation_le Ψ η b e
    have h2 : |inner ℝ (η b) e| ≤ ρ * ‖e‖ := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      gcongr
      exact (hη b).le
    calc |fderiv ℝ Ψ η (bondVariation b e) - c * inner ℝ (η b) e|
        ≤ |fderiv ℝ Ψ η (bondVariation b e)| + |c * inner ℝ (η b) e| := abs_sub _ _
      _ ≤ C₁ * ‖e‖ + c * (ρ * ‖e‖) := by
          rw [abs_mul, abs_of_nonneg hc]
          gcongr
          exact h1.trans (by gcongr; exact hf η hη b)
      _ = (C₁ + c * ρ) * ‖e‖ := by ring
def InFinset (S : Finset ι) (b : ι) : Prop := b ∈ S
instance (S : Finset ι) : DecidablePred (InFinset S) := fun b => inferInstanceAs (Decidable (b ∈ S))
theorem exists_integral_mul_eq_of_separate (S : Finset ι) :
    ∃ (uf : (BondField ι → ℝ) → ℝ) (ug : (BondField ι → ℝ) → ℝ),
      (∀ f' g' : BondField ι → ℝ, (∀ η η' : BondField ι, (∀ b ∈ S, η b = η' b) → f' η = f' η') →
        (∀ η η' : BondField ι, (∀ b, b ∉ S → η b = η' b) → g' η = g' η') →
        ∫ η, f' η * g' η = uf f' * ug g') := by
  let Φ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => BondVector) (InFinset S)
  have hΦ : MeasurePreserving Φ volume volume := volume_preserving_piEquivPiSubtypeProd _ _
  have hsym : ∀ (z : BondField {b // InFinset S b} × BondField {b // ¬ InFinset S b}) (b : ι),
      Φ.symm z b = if h : InFinset S b then z.1 ⟨b, h⟩ else z.2 ⟨b, h⟩ := fun _ _ => rfl
  refine ⟨fun f' => ∫ ξ : BondField {b // InFinset S b}, f' (Φ.symm (ξ, 0)),
    fun g' => ∫ ζ : BondField {b // ¬ InFinset S b}, g' (Φ.symm (0, ζ)), ?_⟩
  intro f' g' hf' hg'
  have h1 := hΦ.symm.integral_comp' (fun η => f' η * g' η)
  rw [← h1]
  have point : ∀ z : BondField {b // InFinset S b} × BondField {b // ¬ InFinset S b},
      f' (Φ.symm z) * g' (Φ.symm z) = f' (Φ.symm (z.1, 0)) * g' (Φ.symm (0, z.2)) := by
    intro z
    congr 1
    · refine hf' _ _ fun b hb => ?_
      rw [hsym, hsym, dif_pos (show InFinset S b from hb), dif_pos (show InFinset S b from hb)]
    · refine hg' _ _ fun b hb => ?_
      rw [hsym, hsym, dif_neg (show ¬ InFinset S b from hb), dif_neg (show ¬ InFinset S b from hb)]
  simp only [point]
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul (fun ξ : BondField {b // InFinset S b} => f' (Φ.symm (ξ, 0)))
    (fun ζ : BondField {b // ¬ InFinset S b} => g' (Φ.symm (0, ζ)))
theorem ratio_integral_mul_eq_of_product_density (S : Finset ι) (a b' f g : BondField ι → ℝ) (D : BondField ι → ℝ)
    (hD : ∀ η, D η = a η * b' η)
    (ha : ∀ η η' : BondField ι, (∀ b ∈ S, η b = η' b) → a η = a η')
    (hb : ∀ η η' : BondField ι, (∀ b, b ∉ S → η b = η' b) → b' η = b' η')
    (hf : ∀ η η' : BondField ι, (∀ b ∈ S, η b = η' b) → f η = f η')
    (hg : ∀ η η' : BondField ι, (∀ b, b ∉ S → η b = η' b) → g η = g η') :
    (∫ η, f η * g η * D η) / ∫ η, D η = ((∫ η, f η * D η) / ∫ η, D η) * ((∫ η, g η * D η) / ∫ η, D η) := by
  obtain ⟨uf, ug, h⟩ := exists_integral_mul_eq_of_separate S
  have e1 : ∫ η, f η * g η * D η = uf (fun η => f η * a η) * ug (fun η => g η * b' η) := by
    rw [← h _ _ (fun η η' e => by beta_reduce; rw [hf η η' e, ha η η' e])
      (fun η η' e => by beta_reduce; rw [hg η η' e, hb η η' e])]
    exact integral_congr_ae (Filter.Eventually.of_forall fun η => by simp only [hD]; ring)
  have e2 : ∫ η, f η * D η = uf (fun η => f η * a η) * ug b' := by
    rw [← h _ _ (fun η η' e => by beta_reduce; rw [hf η η' e, ha η η' e]) hb]
    exact integral_congr_ae (Filter.Eventually.of_forall fun η => by simp only [hD]; ring)
  have e3 : ∫ η, g η * D η = uf a * ug (fun η => g η * b' η) := by
    rw [← h _ _ ha (fun η η' e => by beta_reduce; rw [hg η η' e, hb η η' e])]
    exact integral_congr_ae (Filter.Eventually.of_forall fun η => by simp only [hD]; ring)
  have e4 : ∫ η, D η = uf a * ug b' := by
    rw [← h _ _ ha hb]
    exact integral_congr_ae (Filter.Eventually.of_forall fun η => by simp only [hD])
  rw [e1, e2, e3, e4]
  by_cases h0 : uf a * ug b' = 0
  · simp [h0]
  · field_simp
theorem integral_ballDensity_pos {Ψ : BondField ι → ℝ} (hΨ : Continuous Ψ) {p : ℝ → ℝ} (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) :
    0 < ∫ η, ballDensity (cutoffFactor ρ p) Ψ η := by
  have := isFiniteMeasure_radialLaw (ι := ι) hρ hp
  have := radialLaw_neZero (ι := ι) hρ hp
  obtain ⟨M, hM⟩ := exists_abs_le_on_ballProduct (ι := ι) hρ hΨ
  have hi : Integrable (fun η : BondField ι => Real.exp (-Ψ η)) (radialLaw _ ρ p) := by
    refine Integrable.of_bound (hΨ.neg.rexp.aestronglyMeasurable) (Real.exp M) ?_
    filter_upwards [ae_mem_ballProduct] with η hη
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := hM η hη
    have h2 := neg_abs_le (Ψ η)
    linarith
  have h := integral_exp_pos hi
  rw [integral_radialLaw hp] at h
  refine h.trans_eq (integral_congr_ae (Filter.Eventually.of_forall fun η => ?_))
  simp only [ballDensity]
  ring
theorem ballDensity_eq_zero {Ψ : BondField ι → ℝ} {p : ℝ → ℝ} {η : BondField ι} (hη : η ∉ ballProduct ι ρ) :
    ballDensity (cutoffFactor ρ p) Ψ η = 0 := by
  unfold ballDensity
  rw [radialWeightProd_eq_zero hη, zero_mul]
theorem ballDensity_nonneg {Ψ : BondField ι → ℝ} {p : ℝ → ℝ} (η : BondField ι) :
    0 ≤ ballDensity (cutoffFactor ρ p) Ψ η :=
  mul_nonneg (radialWeightProd_nonneg η) (Real.exp_pos _).le
theorem abs_ballExpectation_le {Ψ : BondField ι → ℝ} {p : ℝ → ℝ} {F : BondField ι → ℝ} {Q : ℝ} (hQ : 0 ≤ Q)
    (hF : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |F η| ≤ Q) :
    |ballExpectation (cutoffFactor ρ p) Ψ F| ≤ Q := by
  unfold ballExpectation
  set D := ballDensity (cutoffFactor ρ p) Ψ with hD
  have hD0 : 0 ≤ ∫ η, D η := integral_nonneg fun η => ballDensity_nonneg η
  by_cases hI : Integrable D
  · rcases hD0.eq_or_lt with h0 | h0
    · rw [← h0]
      simpa using hQ
    · rw [abs_div, abs_of_pos h0, div_le_iff₀ h0]
      have : ‖∫ η, F η * D η‖ ≤ ∫ η, Q * D η := by
        refine norm_integral_le_of_norm_le (hI.const_mul Q) (Filter.Eventually.of_forall fun η => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ballDensity_nonneg η)]
        by_cases hη : η ∈ ballProduct ι ρ
        · exact mul_le_mul_of_nonneg_right (hF η hη) (ballDensity_nonneg η)
        · rw [hD, ballDensity_eq_zero hη]
          simp
      rw [integral_const_mul] at this
      simpa [Real.norm_eq_abs] using this
  · rw [integral_undef hI]
    simpa using hQ
theorem abs_prod_sub_prod_le {a b P : α → ℝ} {e : ℝ} (he : 0 ≤ e) (J : Finset α) (hP : ∀ i ∈ J, 0 ≤ P i)
    (ha : ∀ i ∈ J, |a i| ≤ P i) (hb : ∀ i ∈ J, |b i| ≤ P i) (hab : ∀ i ∈ J, |a i - b i| ≤ e * P i) :
    |∏ i ∈ J, a i - ∏ i ∈ J, b i| ≤ J.card * e * ∏ i ∈ J, P i := by apply _root_.YangMills.Construction.ResponseInTheExpansion.Decorrelation.abs_prod_sub_prod_le <;> assumption
theorem radialWeightProd_eq_mul (S : Finset ι) (r : ℝ → ℝ) (η : BondField ι) :
    radialWeightProd r η = (∏ b ∈ S, r ‖η b‖) * ∏ b ∈ Finset.univ \ S, r ‖η b‖ := by
  unfold radialWeightProd
  rw [mul_comm, Finset.prod_sdiff (Finset.subset_univ S)]
theorem restrictCLM_congr (S : Finset ι) {η η' : BondField ι} (h : ∀ b ∈ S, η b = η' b) :
    restrictCLM S η = restrictCLM S η' := by
  funext b
  rw [restrictCLM_apply, restrictCLM_apply]
  unfold restrictToSet
  split_ifs with hb
  · exact h b hb
  · rfl
theorem ballExpectation_prod_splitPotential {Ψ : BondField ι → ℝ} (hΨ : Continuous Ψ) {p : ℝ → ℝ} {c : ℝ}
    (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    {I : Finset α} {Lam X : α → Finset ι} {F : α → BondField ι → ℝ}
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (Lam i) (Lam j)) (hX : ∀ i ∈ I, X i ⊆ Lam i)
    (hread : ∀ i ∈ I, ∀ η η' : BondField ι, (∀ b ∈ X i, η b = η' b) → F i η = F i η')
    (hcont : Continuous (splitPotential c I Lam Ψ)) (J : Finset α) (hJ : J ⊆ I) :
    ballExpectation (cutoffFactor ρ p) (splitPotential c I Lam Ψ) (fun η => ∏ i ∈ J, F i η) =
      ∏ i ∈ J, ballExpectation (cutoffFactor ρ p) (splitPotential c I Lam Ψ) (F i) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    have h := integral_ballDensity_pos (ι := ι) hcont hρ hp
    simp only [Finset.prod_empty]
    unfold ballExpectation
    simp only [one_mul]
    exact div_self h.ne'
  | insert i s hi ih =>
    have hiI : i ∈ I := hJ (Finset.mem_insert_self i s)
    have hsI : s ⊆ I := fun j hj => hJ (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, ← ih hsI]
    set S := Lam i with hS
    set rest : BondField ι → ℝ := fun η =>
      ∑ j ∈ I.erase i, Ψ (restrictCLM (Lam j) η) + gaussianOn c (Finset.univ \ I.biUnion Lam) η with hrest
    set a : BondField ι → ℝ :=
      fun η => (∏ b ∈ S, cutoffFactor ρ p ‖η b‖) * Real.exp (-Ψ (restrictCLM S η)) with ha
    set b' : BondField ι → ℝ :=
      fun η => (∏ b ∈ Finset.univ \ S, cutoffFactor ρ p ‖η b‖) * Real.exp (-rest η) with hb'
    have hD : ∀ η, ballDensity (cutoffFactor ρ p) (splitPotential c I Lam Ψ) η = a η * b' η := by
      intro η
      have e : splitPotential c I Lam Ψ η = Ψ (restrictCLM S η) + rest η := by
        unfold splitPotential
        rw [hrest, ← Finset.add_sum_erase I _ hiI]
        ring
      unfold ballDensity
      rw [radialWeightProd_eq_mul S, e, neg_add, Real.exp_add]
      simp only [ha, hb']
      ring
    have hoff : ∀ j ∈ I.erase i, ∀ b ∈ Lam j, b ∉ S := by
      intro j hj b hb hbS
      obtain ⟨hne, hjI⟩ := Finset.mem_erase.mp hj
      exact Finset.disjoint_left.mp (hdis j hjI i hiI hne) hb hbS
    have ra : ∀ η η' : BondField ι, (∀ b ∈ S, η b = η' b) → a η = a η' := by
      intro η η' e
      simp only [ha]
      rw [restrictCLM_congr S e]
      congr 1
      exact Finset.prod_congr rfl fun b hb => by rw [e b hb]
    have rb : ∀ η η' : BondField ι, (∀ b, b ∉ S → η b = η' b) → b' η = b' η' := by
      intro η η' e
      have e1 : rest η = rest η' := by
        simp only [hrest]
        congr 1
        · refine Finset.sum_congr rfl fun j hj => ?_
          rw [restrictCLM_congr (Lam j) fun b hb => e b (hoff j hj b hb)]
        · unfold gaussianOn
          congr 1
          refine Finset.sum_congr rfl fun b hb => ?_
          have : b ∉ S := fun hbS => (Finset.mem_sdiff.mp hb).2 (Finset.mem_biUnion.mpr ⟨i, hiI, hbS⟩)
          rw [e b this]
      simp only [hb']
      rw [e1]
      congr 1
      exact Finset.prod_congr rfl fun b hb => by rw [e b (Finset.mem_sdiff.mp hb).2]
    have rf : ∀ η η' : BondField ι, (∀ b ∈ S, η b = η' b) → F i η = F i η' :=
      fun η η' e => hread i hiI η η' fun b hb => e b (hX i hiI hb)
    have rg : ∀ η η' : BondField ι, (∀ b, b ∉ S → η b = η' b) → (∏ j ∈ s, F j η) = ∏ j ∈ s, F j η' := by
      intro η η' e
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjI := hsI hj
      have hne : j ≠ i := fun h => hi (h ▸ hj)
      exact hread j hjI η η' fun b hb => e b (hoff j (Finset.mem_erase.mpr ⟨hne, hjI⟩) b (hX j hjI hb))
    have := ratio_integral_mul_eq_of_product_density S a b' (F i) (fun η => ∏ j ∈ s, F j η)
      (ballDensity (cutoffFactor ρ p) (splitPotential c I Lam Ψ)) hD ra rb rf rg
    unfold ballExpectation
    simp only [Finset.prod_insert hi]
    exact this
theorem productMeanNearMeanProduct_of_segment (hseg : ConvexLawSegmentBound) : ProductMeanNearMeanProduct := by
  intro ι α _ _ _ ρ m κ A c C₁ d Ψ K p hρ hm hκ hp hd H hA hc hf I Lam X F P B hdis hX hF hread hP hB1 hB2
  have hc0 : 0 ≤ c := by linarith
  have hΦ := isUniformlyConvexDecaying_splitPotential hρ hκ hd H hc hm hdis
  have hA₀ := sum_splitPotentialKernel_mul_exp_le (c := c) hρ H hdis hA
  have hcontΨ : Continuous Ψ := H.smooth.continuous
  have hcontΦ : Continuous (splitPotential c I Lam Ψ) := hΦ.smooth.continuous
  have hmem0 : ∀ b, ‖(0 : BondField ι) b‖ < ρ := fun b => by simpa using hρ
  have hP0 : ∀ i ∈ I, 0 ≤ P i := fun i hi => (abs_nonneg _).trans (hP i hi 0 hmem0)
  have hB0 : ∀ b, 0 ≤ B b := fun b =>
    (norm_nonneg _).trans (bondGradNorm_sub_splitPotential_le hρ H hc0 hf hdis hB1 hB2 hmem0 b)
  set Z := I.biUnion X with hZ
  set Sm := ∑ b ∈ Z, ∑ b', B b' * Real.exp (-(κ * d b b')) with hSm
  have hS0 : 0 ≤ Sm := Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun b' _ =>
    mul_nonneg (hB0 b') (Real.exp_pos _).le
  set e := 4 * ρ * (1 + A) * 2 * Sm with he
  have he0 : 0 ≤ e := by
    rcases isEmpty_or_nonempty ι with h | ⟨⟨b₀⟩⟩
    · have : Sm = 0 := by
        rw [hSm]
        exact Finset.sum_eq_zero fun b _ => (h.false b).elim
      simp [he, this]
    · have h1 : 0 ≤ A * m := le_trans (Finset.sum_nonneg fun b' _ =>
        mul_nonneg (kernel_nonneg hρ H b₀ b') (Real.exp_pos _).le) (hA b₀)
      have hA0 : 0 ≤ A := nonneg_of_mul_nonneg_left h1 hm
      positivity
  have seg : ∀ (F₀ : BondField ι → ℝ) (O : ℝ), Measurable F₀ →
      (∀ η η' : BondField ι, (∀ b ∈ Z, η b = η' b) → F₀ η = F₀ η') →
      (∀ η η' : BondField ι, (∀ b, ‖η b‖ < ρ) → (∀ b, ‖η' b‖ < ρ) → |F₀ η - F₀ η'| ≤ O) →
      |ballExpectation (cutoffFactor ρ p) Ψ F₀ - ballExpectation (cutoffFactor ρ p) (splitPotential c I Lam Ψ) F₀| ≤
        4 * ρ * (1 + A) * O * Sm :=
    fun F₀ O h1 h2 h3 => hseg ι ρ m κ A O d (splitPotential c I Lam Ψ) Ψ _ K p hρ hm hκ hp hd hΦ H hA₀ hA Z F₀ B
      h1 h2 h3 (fun η hη b => bondGradNorm_sub_splitPotential_le hρ H hc0 hf hdis hB1 hB2 hη b)
  have hprod : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |∏ i ∈ I, F i η| ≤ ∏ i ∈ I, P i := by
    intro η hη
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i hi => hP i hi η hη
  have T1 := seg (fun η => ∏ i ∈ I, F i η) (2 * ∏ i ∈ I, P i) (Finset.measurable_fun_prod _ hF)
    (fun η η' e => Finset.prod_congr rfl fun i hi => hread i hi η η' fun b hb =>
      e b (Finset.mem_biUnion.mpr ⟨i, hi, hb⟩))
    (fun η η' h1 h2 => by
      have a := hprod η h1
      have b := hprod η' h2
      calc _ ≤ |∏ i ∈ I, F i η| + |∏ i ∈ I, F i η'| := abs_sub _ _
        _ ≤ _ := by linarith)
  have hone : ∀ i ∈ I, |ballExpectation (cutoffFactor ρ p) (splitPotential c I Lam Ψ) (F i) -
      ballExpectation (cutoffFactor ρ p) Ψ (F i)| ≤ e * P i := by
    intro i hi
    rw [abs_sub_comm]
    have := seg (F i) (2 * P i) (hF i hi)
      (fun η η' e => hread i hi η η' fun b hb => e b (Finset.mem_biUnion.mpr ⟨i, hi, hb⟩))
      (fun η η' h1 h2 => by
        have a := hP i hi η h1
        have b := hP i hi η' h2
        calc _ ≤ |F i η| + |F i η'| := abs_sub _ _
          _ ≤ _ := by linarith)
    calc _ ≤ _ := this
      _ = e * P i := by rw [he]; ring
  have T2 := abs_prod_sub_prod_le (a := fun i => ballExpectation (cutoffFactor ρ p) (splitPotential c I Lam Ψ) (F i))
    (b := fun i => ballExpectation (cutoffFactor ρ p) Ψ (F i)) he0 I hP0
    (fun i hi => abs_ballExpectation_le (hP0 i hi) (hP i hi))
    (fun i hi => abs_ballExpectation_le (hP0 i hi) (hP i hi)) hone
  have hpm := ballExpectation_prod_splitPotential (c := c) hcontΨ hρ hp hdis hX hread hcontΦ I (Finset.Subset.refl I)
  rw [← hpm] at T2
  calc _ ≤ |ballExpectation (cutoffFactor ρ p) Ψ (fun η => ∏ i ∈ I, F i η) -
          ballExpectation (cutoffFactor ρ p) (splitPotential c I Lam Ψ) (fun η => ∏ i ∈ I, F i η)| +
        |ballExpectation (cutoffFactor ρ p) (splitPotential c I Lam Ψ) (fun η => ∏ i ∈ I, F i η) -
          ∏ i ∈ I, ballExpectation (cutoffFactor ρ p) Ψ (F i)| := abs_sub_le _ _ _
    _ ≤ 4 * ρ * (1 + A) * (2 * ∏ i ∈ I, P i) * Sm + I.card * e * ∏ i ∈ I, P i := add_le_add T1 T2
    _ = _ := by rw [he]; ring
theorem productMeanNearMeanProduct (hseg : ConvexLawSegmentBound) : ProductMeanNearMeanProduct := by apply _root_.YangMills.Construction.ConvexDecoupling.productMeanNearMeanProduct_of_segment <;> assumption
end ConvexDecoupling
end YangMills.Construction
end
