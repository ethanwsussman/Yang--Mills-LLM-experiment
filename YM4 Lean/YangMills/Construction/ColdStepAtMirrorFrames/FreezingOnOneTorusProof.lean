import YangMills.Construction.ColdStepAtMirrorFrames.CalculusOfLocalTerms
import YangMills.Construction.ColdStepAtMirrorFrames.ExponentsStayGood
import YangMills.Construction.ColdStepAtMirrorFrames.FreezingOnOneTorus
import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACut
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace FreezingBound
open LocalCalculus
variable {ι P : Type} [Fintype ι] [DecidableEq ι] [Fintype P] {ρ r c x : ℝ} {pos : ι → P}
  {D : P → P → ℝ} {z : P} {θ : BondField ι → ℝ}
def restrictedFn (Λ : Finset ι) (θ : BondField ι → ℝ) (η : BondField ι) : ℝ := θ (restrictToBonds Λ η)
theorem restrictedFn_eq_comp (Λ : Finset ι) (θ : BondField ι → ℝ) :
    restrictedFn Λ θ = fun ζ => θ (restrictToBondsCLM Λ ζ) := by
  funext ζ
  simp [restrictedFn, restrictToBondsCLM_apply]
theorem contDiffOn_restrictedFn (hρ : 0 < ρ) (Λ : Finset ι) {n : WithTop ℕ∞}
    (hθ : ContDiffOn ℝ n θ (openPolyball ι ρ)) :
    ContDiffOn ℝ n (restrictedFn Λ θ) (openPolyball ι ρ) := by
  rw [restrictedFn_eq_comp]
  exact hθ.comp (restrictToBondsCLM Λ).contDiff.contDiffOn (fun η hη => by
    rw [restrictToBondsCLM_apply]
    exact restrictToBonds_mem_openPolyball hρ Λ hη)
theorem norm_restrictToBonds_le (Λ : Finset ι) (η : BondField ι) (b : ι) :
    ‖restrictToBonds Λ η b‖ ≤ ‖η b‖ := by
  by_cases h : b ∈ Λ <;> simp [restrictToBonds, h]
theorem bondGradNorm_restrictedFn_le (hρ : 0 < ρ) (Λ : Finset ι) (hθ : ContDiffOn ℝ 1 θ (openPolyball ι ρ))
    {η : BondField ι} (hη : η ∈ openPolyball ι ρ) (b : ι) :
    bondGradNorm (restrictedFn Λ θ) b η ≤ if b ∈ Λ then bondGradNorm θ b (restrictToBonds Λ η) else 0 := by
  have hm : restrictToBondsCLM Λ η ∈ openPolyball ι ρ := by
    rw [restrictToBondsCLM_apply]
    exact restrictToBonds_mem_openPolyball hρ Λ hη
  rw [restrictedFn_eq_comp]
  by_cases hb : b ∈ Λ
  · simp only [hb, if_true]
    have := bondGradNorm_comp_clm_le hρ hθ (restrictToBondsCLM Λ) hm (k := b) (b := b) (fun e => by
      rw [restrictToBondsCLM_apply, restrictToBonds_bondVariation_of_mem Λ hb])
    rwa [restrictToBondsCLM_apply] at this
  · simp only [hb, if_false]
    exact (bondGradNorm_comp_clm_eq_zero hρ hθ (restrictToBondsCLM Λ) hm (k := b) (fun e => by
      rw [restrictToBondsCLM_apply, restrictToBonds_bondVariation_of_not_mem Λ hb])).le
theorem majorant_mono {c x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) {w : ℝ} (hw : 0 ≤ w) (z : P)
    {ζ η : BondField ι} (h : ∀ b, ‖ζ b‖ ≤ ‖η b‖) :
    c * (x * Real.sqrt (weightedSqNormNear r pos D z ζ) + 1) * w ≤
      c * (x * Real.sqrt (weightedSqNormNear r pos D z η) + 1) * w := by
  apply mul_le_mul_of_nonneg_right _ hw
  apply mul_le_mul_of_nonneg_left _ hc
  have := Real.sqrt_le_sqrt (weightedSqNormNear_mono (r := r) (pos := pos) (D := D) z h)
  have := mul_le_mul_of_nonneg_left this hx
  linarith
theorem bondGradNorm_restrictedFn_le_of_localTerm (hρ : 0 < ρ) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hT : IsLocalTermAt ρ r c x pos D z θ) (Λ : Finset ι)
    {η : BondField ι} (hη : η ∈ openPolyball ι ρ) (b : ι) :
    bondGradNorm (restrictedFn Λ θ) b η ≤
      c * (x * Real.sqrt (weightedSqNormNear r pos D z η) + 1) * Real.exp (-(2 ^ 5 * r * D (pos b) z)) := by
  refine (bondGradNorm_restrictedFn_le hρ Λ (contDiffOn_one_of_two hT.smooth) hη b).trans ?_
  split_ifs with hb
  · refine (hT.slope _ (restrictToBonds_mem_openPolyball hρ Λ hη) b).trans ?_
    exact majorant_mono hc hx (Real.exp_pos _).le z (norm_restrictToBonds_le Λ η)
  · have : 0 ≤ Real.sqrt (weightedSqNormNear r pos D z η) := Real.sqrt_nonneg _
    positivity
def restrictionDefect (Λ : Finset ι) (θ : BondField ι → ℝ) (η : BondField ι) : ℝ :=
  θ η - restrictedFn Λ θ η
theorem contDiffOn_restrictionDefect (hρ : 0 < ρ) (Λ : Finset ι) {n : WithTop ℕ∞}
    (hθ : ContDiffOn ℝ n θ (openPolyball ι ρ)) :
    ContDiffOn ℝ n (restrictionDefect Λ θ) (openPolyball ι ρ) :=
  hθ.sub (contDiffOn_restrictedFn hρ Λ hθ)
theorem restrictionDefect_eq (Λ : Finset ι) (θ : BondField ι → ℝ) :
    restrictionDefect Λ θ = fun ζ => 1 * θ ζ + (-1) * restrictedFn Λ θ ζ := by
  funext ζ
  simp only [restrictionDefect]
  ring
theorem bondGradNorm_restrictionDefect_le (hρ : 0 < ρ) (hθ : ContDiffOn ℝ 1 θ (openPolyball ι ρ))
    (Λ : Finset ι) {η : BondField ι} (hη : η ∈ openPolyball ι ρ) (b : ι) :
    bondGradNorm (restrictionDefect Λ θ) b η ≤ bondGradNorm θ b η + bondGradNorm (restrictedFn Λ θ) b η := by
  rw [restrictionDefect_eq]
  have := bondGradNorm_linear_combination_le hρ hθ (contDiffOn_restrictedFn hρ Λ hθ) 1 (-1) hη b
  simpa using this
theorem bondGradNorm_restrictionDefect_le_of_not_mem (hρ : 0 < ρ) (hθ : ContDiffOn ℝ 1 θ (openPolyball ι ρ))
    (Λ : Finset ι) {η : BondField ι} (hη : η ∈ openPolyball ι ρ) {b : ι} (hb : b ∉ Λ) :
    bondGradNorm (restrictionDefect Λ θ) b η ≤ bondGradNorm θ b η := by
  have h1 := bondGradNorm_restrictionDefect_le hρ hθ Λ hη b
  have h2 := bondGradNorm_restrictedFn_le hρ Λ hθ hη b
  simp only [hb, if_false] at h2
  linarith
theorem bondGradNorm_restrictionDefect_le_of_mem (hρ : 0 < ρ) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hT : IsLocalTermAt ρ r c x pos D z θ)
    (Λ : Finset ι) {η : BondField ι} (hη : η ∈ openPolyball ι ρ) {b : ι} (hb : b ∈ Λ) :
    bondGradNorm (restrictionDefect Λ θ) b η ≤ ∑ b', (if b' ∈ Λ then 0 else
      c * x * Real.exp (-(2 ^ 5 * r * max (D (pos b) z) (D (pos b') z)))) * ‖η b'‖ := by
  have hθ1 := contDiffOn_one_of_two hT.smooth
  have hcm := restrictToBonds_mem_openPolyball hρ Λ hη
  have hnn : 0 ≤ ∑ b', (if b' ∈ Λ then 0 else
      c * x * Real.exp (-(2 ^ 5 * r * max (D (pos b) z) (D (pos b') z)))) * ‖η b'‖ := by
    refine Finset.sum_nonneg fun b' _ => mul_nonneg ?_ (norm_nonneg _)
    split_ifs
    · exact le_rfl
    · positivity
  apply bondGradNorm_le_of_forall hnn
  intro e
  have hO := isOpen_openPolyball (ι := ι) hρ
  have d1 : HasFDerivAt θ (fderiv ℝ θ η) η :=
    ((hθ1.contDiffAt (hO.mem_nhds hη)).differentiableAt (by norm_num)).hasFDerivAt
  have d2 : HasFDerivAt (restrictedFn Λ θ) (fderiv ℝ (restrictedFn Λ θ) η) η :=
    (((contDiffOn_restrictedFn hρ Λ hθ1).contDiffAt (hO.mem_nhds hη)).differentiableAt
      (by norm_num)).hasFDerivAt
  have d3 : HasFDerivAt (restrictionDefect Λ θ) (fderiv ℝ θ η - fderiv ℝ (restrictedFn Λ θ) η) η :=
    d1.sub d2
  have e2 : fderiv ℝ (restrictedFn Λ θ) η (bondVariation b e) =
      fderiv ℝ θ (restrictToBonds Λ η) (bondVariation b e) := by
    rw [restrictedFn_eq_comp, fderiv_comp_clm_apply hρ hθ1 (restrictToBondsCLM Λ)
      (by rw [restrictToBondsCLM_apply]; exact hcm), restrictToBondsCLM_apply, restrictToBondsCLM_apply,
      restrictToBonds_bondVariation_of_mem Λ hb]
  rw [d3.fderiv]
  simp only [ContinuousLinearMap.sub_apply]
  rw [e2]
  set G : BondField ι → ℝ := fun ξ => fderiv ℝ θ ξ (bondVariation b e) with hG
  have hG1 : ContDiffOn ℝ 1 G (openPolyball ι ρ) := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ θ) (openPolyball ι ρ) :=
      hT.smooth.fderiv_of_isOpen hO (by norm_num)
    exact h1.clm_apply contDiffOn_const
  have key := abs_sub_le_sum_bondGradNorm hρ hG1 hη hcm
    (fun b' => c * x * Real.exp (-(2 ^ 5 * r * max (D (pos b) z) (D (pos b') z))) * ‖e‖)
    (fun s hs b' => by
      have hmem : restrictToBonds Λ η + s • (η - restrictToBonds Λ η) ∈ openPolyball ι ρ :=
        (convex_openPolyball (ι := ι) hρ).add_smul_sub_mem hcm hη hs
      apply bondGradNorm_le_of_forall (by positivity)
      intro e'
      have := hT.second _ hmem b b' e e'
      exact this)
  refine key.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun b' _ => ?_
  by_cases hb' : b' ∈ Λ
  · simp [restrictToBonds, hb']
  · simp only [hb', if_false, restrictToBonds, sub_zero]
    exact le_of_eq (by ring)
theorem exp_neg_le_mul_exp_neg {r R s d : ℝ} (h : r * R / 16 ≤ (s - r / 4) * d) :
    Real.exp (-(s * d)) ≤ Real.exp (-(r / 4 * d)) * Real.exp (-(r * R / 16)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith
section Measure
variable {m S lam R : ℝ} {p : ℝ → ℝ} {T : BondField ι → ℝ} {H : BondField ι → ℝ} {Y : P}
  {Λ : Finset ι}
theorem abs_ballExpectation_restrictionDefect_le (hρ : 0 < ρ) (hr : 0 < r) (hx : 1 ≤ x) (hc : 0 ≤ c)
    (hm : 0 < m) (hR : 0 ≤ R)
    (hD : IsPseudoMetricOnBonds D) (hSn : 0 ≤ S)
    (hS : ∀ z, ∑ b, Real.exp (-(r / 4 * D (pos b) z)) ≤ S)
    (F : IsPositiveUnitalForm ρ p T) (Sz : AdmissibleMomentBounds ρ m r S p pos D T)
    (hH : IsLocalTermAt ρ r c x pos D Y H) (hoff : ∀ b, b ∉ Λ → R / 2 ≤ D (pos b) Y)
    (hn : IsBoundedContinuousOn ι ρ (fun η => H η - restrictedFn Λ H η)) :
    |ballExpectation (cutoffFactor ρ p) T (fun η => H η - restrictedFn Λ H η)| ≤
      c * (x / 2 * (8 * S ^ 2 / m) + x * (8 * S / m) + 1 / 2) *
        (S * Real.exp (-(r * R / 16))) := by
  have hx0 : 0 ≤ x := by linarith
  set ob : ι → ℝ := fun b => if b ∈ Λ then 0 else Real.exp (-(2 ^ 5 * r * D (pos b) Y)) with hob
  have hob0 : ∀ b, 0 ≤ ob b := fun b => by
    simp only [hob]
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  set g : BondField ι → ℝ := fun η => ∑ b, c * ob b *
    (x / 2 * weightedSqNormNear r pos D Y η + x * ‖η b‖ ^ 2 + 1 / 2) with hg
  have hq := isBoundedContinuousOn_weightedSqNormNear (r := r) (pos := pos) (D := D) (ι := ι) hρ Y
  have hin : ∀ b, IsBoundedContinuousOn ι ρ
      (fun η => x / 2 * weightedSqNormNear r pos D Y η + x * ‖η b‖ ^ 2 + 1 / 2) :=
    fun b => (((IsBoundedContinuousOn.const _).mul hq).add
      ((IsBoundedContinuousOn.const _).mul (IsBoundedContinuousOn.norm_sq_apply hρ b))).add
      (IsBoundedContinuousOn.const _)
  have hgn : IsBoundedContinuousOn ι ρ g :=
    IsBoundedContinuousOn.sum _ _ fun b _ => (IsBoundedContinuousOn.const _).mul (hin b)
  have hpt : ∀ η ∈ openPolyball ι ρ, |H η - restrictedFn Λ H η| ≤ g η := by
    intro η hη
    have hcm := restrictToBonds_mem_openPolyball hρ Λ hη
    have key := abs_sub_le_sum_bondGradNorm hρ (contDiffOn_one_of_two hH.smooth) hη hcm
      (fun b => c * (x * Real.sqrt (weightedSqNormNear r pos D Y η) + 1) *
        Real.exp (-(2 ^ 5 * r * D (pos b) Y)))
      (fun s hs b => by
        have hmem : restrictToBonds Λ η + s • (η - restrictToBonds Λ η) ∈ openPolyball ι ρ :=
          (convex_openPolyball (ι := ι) hρ).add_smul_sub_mem hcm hη hs
        refine (hH.slope _ hmem b).trans ?_
        apply majorant_mono hc hx0 (Real.exp_pos _).le Y
        intro b'
        by_cases hb' : b' ∈ Λ
        · simp [restrictToBonds, hb']
        · simp only [restrictToBonds, hb', if_false, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, sub_zero,
            zero_add, norm_smul, Real.norm_eq_abs]
          rw [abs_of_nonneg hs.1]
          have := norm_nonneg (η b')
          nlinarith [hs.2])
    refine key.trans (Finset.sum_le_sum fun b _ => ?_)
    by_cases hb : b ∈ Λ
    · simp [hob, restrictToBonds, hb]
    · simp only [hob, hb, if_false, restrictToBonds, sub_zero]
      set u := Real.sqrt (weightedSqNormNear r pos D Y η) with hu
      have hu2 : u ^ 2 = weightedSqNormNear r pos D Y η := Real.sq_sqrt (weightedSqNormNear_nonneg Y η)
      set t := ‖η b‖ with ht
      rw [← hu2]
      have hmain : (x * u + 1) * t ≤ x / 2 * u ^ 2 + x * t ^ 2 + 1 / 2 := by
        nlinarith [sq_nonneg (u - t), sq_nonneg (t - 1), mul_nonneg hx0 (sq_nonneg (u - t)),
          mul_nonneg (by linarith : 0 ≤ x - 1) (sq_nonneg t)]
      calc c * (x * u + 1) * Real.exp (-(2 ^ 5 * r * D (pos b) Y)) * t
          = c * Real.exp (-(2 ^ 5 * r * D (pos b) Y)) * ((x * u + 1) * t) := by ring
        _ ≤ c * Real.exp (-(2 ^ 5 * r * D (pos b) Y)) * (x / 2 * u ^ 2 + x * t ^ 2 + 1 / 2) :=
            mul_le_mul_of_nonneg_left hmain (by positivity)
  refine (abs_ballExpectation_le F hn hgn hpt).trans ?_
  simp only [hg]
  rw [F.map_sum Finset.univ _ (fun b _ => (IsBoundedContinuousOn.const _).mul (hin b))]
  simp only [F.map_smul]
  have hmean : ∀ b, ballExpectation (cutoffFactor ρ p) T
      (fun η => x / 2 * weightedSqNormNear r pos D Y η + x * ‖η b‖ ^ 2 + 1 / 2) ≤
      x / 2 * (8 * S ^ 2 / m) + x * (8 * S / m) + 1 / 2 := by
    intro b
    have e1 : ballExpectation (cutoffFactor ρ p) T (fun _ => (1 / 2 : ℝ)) = 1 / 2 := by
      have := F.map_smul (1 / 2) (fun _ => 1)
      rw [F.map_one] at this
      simpa using this
    rw [F.map_add _ _ (((IsBoundedContinuousOn.const _).mul hq).add
        ((IsBoundedContinuousOn.const _).mul (IsBoundedContinuousOn.norm_sq_apply hρ b)))
      (IsBoundedContinuousOn.const _), F.map_add _ _ ((IsBoundedContinuousOn.const _).mul hq)
      ((IsBoundedContinuousOn.const _).mul (IsBoundedContinuousOn.norm_sq_apply hρ b)), F.map_smul,
      F.map_smul, e1]
    have h1 := mul_le_mul_of_nonneg_left (Sz.near_moment_le Y) (by positivity : 0 ≤ x / 2)
    have h2 := mul_le_mul_of_nonneg_left (Sz.second_moment_le b) hx0
    linarith
  have hsum : ∑ b, ob b ≤ S * Real.exp (-(r * R / 16)) := by
    have h1 : ∀ b, ob b ≤ Real.exp (-(r / 4 * D (pos b) Y)) * Real.exp (-(r * R / 16)) := by
      intro b
      by_cases hb : b ∈ Λ
      · simp only [hob, hb, if_true]
        positivity
      · simp only [hob, hb, if_false]
        apply exp_neg_le_mul_exp_neg
        have h2 := hoff b hb
        have h3 : 0 ≤ r * R := by positivity
        have h4 : (R / 2) * r ≤ D (pos b) Y * r := mul_le_mul_of_nonneg_right h2 hr.le
        nlinarith
    refine (Finset.sum_le_sum fun b _ => h1 b).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hS Y) (Real.exp_pos _).le
  set Nv := x / 2 * (8 * S ^ 2 / m) + x * (8 * S / m) + 1 / 2 with hNv
  calc ∑ b, c * ob b * ballExpectation (cutoffFactor ρ p) T
        (fun η => x / 2 * weightedSqNormNear r pos D Y η + x * ‖η b‖ ^ 2 + 1 / 2)
      ≤ ∑ b, c * ob b * Nv :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hmean b)
          (mul_nonneg hc (hob0 b))
    _ = c * Nv * ∑ b, ob b := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ c * Nv * (S * Real.exp (-(r * R / 16))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
theorem ballL2Norm_bondGradNorm_le_of_majorant (hρ : 0 < ρ) (hr : 0 < r) (hx : 0 ≤ x)
    (hD : IsPseudoMetricOnBonds D)
    (F : IsPositiveUnitalForm ρ p T) (Sz : AdmissibleMomentBounds ρ m r S p pos D T)
    {G : BondField ι → ℝ} (hG : ContDiffOn ℝ 1 G (openPolyball ι ρ)) {M a : ℝ} (ha : 0 ≤ a)
    (hM : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm G b η ≤ M) (z : P) {b : ι} {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ η ∈ openPolyball ι ρ, bondGradNorm G b η ≤
      a * (x * Real.sqrt (weightedSqNormNear r pos D z η) + 1) * w) :
    ballL2Norm (cutoffFactor ρ p) T (bondGradNorm G b) ≤
      a * w * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) := by
  apply ballL2Norm_le_of_near_majorant hρ F Sz (isBoundedContinuousOn_bondGradNorm hρ hG hM b)
    (by positivity) hx z
  intro η hη
  rw [abs_of_nonneg (bondGradNorm_nonneg G b η)]
  refine (h η hη).trans (le_of_eq ?_)
  ring
theorem exists_bondGradNorm_restrictionDefect_bound (hρ : 0 < ρ) (hr : 0 < r) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hD : IsPseudoMetricOnBonds D)
    (hT : IsLocalTermAt ρ r c x pos D z θ) (Λ : Finset ι) :
    ∃ M, 0 ≤ M ∧ ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm (restrictionDefect Λ θ) b η ≤ M := by
  obtain ⟨M, hM0, hM⟩ := exists_bondGradNorm_bound_of_localTerm hρ hr.le hc hx hD hT
  have h1 := contDiffOn_one_of_two hT.smooth
  refine ⟨2 * M, by positivity, fun η hη b => ?_⟩
  have h2 := bondGradNorm_restrictionDefect_le hρ h1 Λ hη b
  have h3 := bondGradNorm_restrictedFn_le hρ Λ h1 hη b
  have h4 : bondGradNorm (restrictedFn Λ θ) b η ≤ M := by
    refine h3.trans ?_
    split_ifs
    · exact hM _ (restrictToBonds_mem_openPolyball hρ Λ hη) b
    · exact hM0
  have := hM η hη b
  linarith
theorem ballL2Norm_restrictionDefect_le (hρ : 0 < ρ) (hr : 0 < r) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hD : IsPseudoMetricOnBonds D)
    (F : IsPositiveUnitalForm ρ p T) (Sz : AdmissibleMomentBounds ρ m r S p pos D T)
    (hT : IsLocalTermAt ρ r c x pos D z θ) (Λ : Finset ι) (b : ι) :
    ballL2Norm (cutoffFactor ρ p) T (bondGradNorm (restrictionDefect Λ θ) b) ≤
      2 * c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) * Real.exp (-(2 * r * D (pos b) z)) := by
  obtain ⟨M, _, hM⟩ := exists_bondGradNorm_restrictionDefect_bound hρ hr hc hx hD hT Λ
  have h1 := contDiffOn_one_of_two hT.smooth
  have key := ballL2Norm_bondGradNorm_le_of_majorant (a := 2 * c)
    (w := Real.exp (-(2 ^ 5 * r * D (pos b) z))) hρ hr hx hD F Sz
    (contDiffOn_restrictionDefect hρ Λ h1) (by positivity) hM z (Real.exp_pos _).le (fun η hη => by
      have h2 := bondGradNorm_restrictionDefect_le hρ h1 Λ hη b
      have h3 := bondGradNorm_restrictedFn_le_of_localTerm hρ hc hx hT Λ hη b
      have h4 := hT.slope η hη b
      linarith)
  refine key.trans ?_
  have hw : Real.exp (-(2 ^ 5 * r * D (pos b) z)) ≤ Real.exp (-(2 * r * D (pos b) z)) := by
    apply Real.exp_le_exp.mpr
    have := pseudoMetric_nonneg hD (pos b) z
    nlinarith
  calc 2 * c * Real.exp (-(2 ^ 5 * r * D (pos b) z)) * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2)
      = 2 * c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) * Real.exp (-(2 ^ 5 * r * D (pos b) z)) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
theorem ballL2Norm_restrictionDefect_le_of_far (hρ : 0 < ρ) (hr : 0 < r) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hm : 0 < m) (hR : 0 ≤ R)
    (hSn : 0 ≤ S) (hD : IsPseudoMetricOnBonds D) (hS : ∀ z, ∑ b, Real.exp (-(r / 4 * D (pos b) z)) ≤ S)
    (F : IsPositiveUnitalForm ρ p T) (Sz : AdmissibleMomentBounds ρ m r S p pos D T)
    (hT : IsLocalTermAt ρ r c x pos D z θ) (Λ : Finset ι) (hoff : ∀ b, b ∉ Λ → R / 4 ≤ D (pos b) z)
    (b : ι) :
    ballL2Norm (cutoffFactor ρ p) T (bondGradNorm (restrictionDefect Λ θ) b) ≤
      c * (Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) + S * (x * Real.sqrt (8 * S / m))) *
        Real.exp (-(r * R / 16)) * Real.exp (-(2 * r * D (pos b) z)) := by
  obtain ⟨M, _, hM⟩ := exists_bondGradNorm_restrictionDefect_bound hρ hr hc hx hD hT Λ
  have h1 := contDiffOn_one_of_two hT.smooth
  have hG := Real.sqrt_nonneg (2 * x ^ 2 * (8 * S ^ 2 / m) + 2)
  have hq := Real.sqrt_nonneg (8 * S / m)
  set G := Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2)
  set q := Real.sqrt (8 * S / m)
  have he := Real.exp_pos (-(r * R / 16))
  have hu := pseudoMetric_nonneg hD (pos b) z
  by_cases hb : b ∈ Λ
  · set a' : ι → ℝ := fun b' => (if b' ∈ Λ then 0 else
      c * x * Real.exp (-(2 ^ 5 * r * max (D (pos b) z) (D (pos b') z)))) with ha'
    have ha0 : ∀ b', 0 ≤ a' b' := fun b' => by
      simp only [ha']
      split_ifs
      · exact le_rfl
      · positivity
    have key := ballL2Norm_le_of_linear_majorant hρ F Sz hSn hm
      (isBoundedContinuousOn_bondGradNorm hρ (contDiffOn_restrictionDefect hρ Λ h1) hM b) a' ha0
      (fun η hη => by
        rw [abs_of_nonneg (bondGradNorm_nonneg _ b η)]
        exact bondGradNorm_restrictionDefect_le_of_mem hρ hc hx hT Λ hη hb)
    refine key.trans ?_
    have hsum : ∑ b', a' b' ≤ c * x * Real.exp (-(2 ^ 4 * r * D (pos b) z)) *
        (S * Real.exp (-(r * R / 16))) := by
      have h2 : ∀ b', a' b' ≤ c * x * Real.exp (-(2 ^ 4 * r * D (pos b) z)) *
          (Real.exp (-(r / 4 * D (pos b') z)) * Real.exp (-(r * R / 16))) := by
        intro b'
        by_cases hb' : b' ∈ Λ
        · simp only [ha', hb', if_true]
          positivity
        · simp only [ha', hb', if_false]
          have hv := hoff b' hb'
          have hspl := exp_neg_le_mul_exp_neg (r := r) (R := R) (s := 2 ^ 4 * r) (d := D (pos b') z) (by
            have h3 : (R / 4) * r ≤ D (pos b') z * r := mul_le_mul_of_nonneg_right hv hr.le
            have h4 : 0 ≤ r * R := by positivity
            nlinarith)
          have hmax : Real.exp (-(2 ^ 5 * r * max (D (pos b) z) (D (pos b') z))) ≤
              Real.exp (-(2 ^ 4 * r * D (pos b) z)) * Real.exp (-(2 ^ 4 * r * D (pos b') z)) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have m1 := le_max_left (D (pos b) z) (D (pos b') z)
            have m2 := le_max_right (D (pos b) z) (D (pos b') z)
            nlinarith
          calc c * x * Real.exp (-(2 ^ 5 * r * max (D (pos b) z) (D (pos b') z)))
              ≤ c * x * (Real.exp (-(2 ^ 4 * r * D (pos b) z)) *
                  Real.exp (-(2 ^ 4 * r * D (pos b') z))) :=
                mul_le_mul_of_nonneg_left hmax (by positivity)
            _ ≤ c * x * (Real.exp (-(2 ^ 4 * r * D (pos b) z)) *
                  (Real.exp (-(r / 4 * D (pos b') z)) * Real.exp (-(r * R / 16)))) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul_of_nonneg_left hspl (Real.exp_pos _).le
            _ = _ := by ring
      refine (Finset.sum_le_sum fun b' _ => h2 b').trans ?_
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right (hS z) he.le
    have hw : Real.exp (-(2 ^ 4 * r * D (pos b) z)) ≤ Real.exp (-(2 * r * D (pos b) z)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc (∑ b', a' b') * q
        ≤ (c * x * Real.exp (-(2 ^ 4 * r * D (pos b) z)) * (S * Real.exp (-(r * R / 16)))) * q :=
          mul_le_mul_of_nonneg_right hsum hq
      _ = c * (S * (x * q)) * Real.exp (-(r * R / 16)) * Real.exp (-(2 ^ 4 * r * D (pos b) z)) := by ring
      _ ≤ c * (G + S * (x * q)) * Real.exp (-(r * R / 16)) * Real.exp (-(2 * r * D (pos b) z)) := by
          apply mul_le_mul _ hw (Real.exp_pos _).le (by positivity)
          apply mul_le_mul_of_nonneg_right _ he.le
          apply mul_le_mul_of_nonneg_left _ hc
          linarith
  · have key := ballL2Norm_bondGradNorm_le_of_majorant (a := c) (w := Real.exp (-(2 ^ 5 * r * D (pos b) z)))
      hρ hr hx hD F Sz
      (contDiffOn_restrictionDefect hρ Λ h1) hc hM z (Real.exp_pos _).le (fun η hη =>
        (bondGradNorm_restrictionDefect_le_of_not_mem hρ h1 Λ hη hb).trans (hT.slope η hη b))
    refine key.trans ?_
    have hw : Real.exp (-(2 ^ 5 * r * D (pos b) z)) ≤
        Real.exp (-(r * R / 16)) * Real.exp (-(2 * r * D (pos b) z)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hv := hoff b hb
      have h3 : (R / 4) * r ≤ D (pos b) z * r := mul_le_mul_of_nonneg_right hv hr.le
      have h4 : 0 ≤ r * R := by positivity
      nlinarith
    calc c * Real.exp (-(2 ^ 5 * r * D (pos b) z)) * G
        = c * G * Real.exp (-(2 ^ 5 * r * D (pos b) z)) := by ring
      _ ≤ c * G * (Real.exp (-(r * R / 16)) * Real.exp (-(2 * r * D (pos b) z))) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
      _ ≤ c * (G + S * (x * q)) * (Real.exp (-(r * R / 16)) * Real.exp (-(2 * r * D (pos b) z))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ hc
          have : 0 ≤ S * (x * q) := by positivity
          linarith
      _ = _ := by ring
theorem abs_ballCovariance_potentialDifference_le {Q : P → BondField ι → ℝ} {Ψ A Hv : BondField ι → ℝ} {μ : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hc : 0 ≤ c) (hx : 0 ≤ x) (hm : 0 < m) (hR : 0 ≤ R) (hμ : 0 ≤ μ)
    (hSn : 0 ≤ S) (hD : IsPseudoMetricOnBonds D)
    (hS : ∀ z, ∑ b, Real.exp (-(r / 4 * D (pos b) z)) ≤ S)
    (hSp : ∀ z, ∑ z', Real.exp (-(r / 4 * D z' z)) ≤ S)
    (F : IsPositiveUnitalForm ρ p T) (Sz : AdmissibleMomentBounds ρ m r S p pos D T)
    (hQ : ∀ z, IsLocalTermAt ρ r c x pos D z (Q z))
    (hsplit : ∀ η ∈ openPolyball ι ρ, Ψ η - A η = (∑ z, restrictionDefect Λ (Q z) η) - halfSqNormOn μ Λᶜ η)
    (hoff : ∀ b, b ∉ Λ → R / 2 ≤ D (pos b) Y)
    (hHv : ContDiffOn ℝ 1 Hv (openPolyball ι ρ)) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hMv : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm Hv b η ≤ Mv)
    (hHn : ∀ b, ballL2Norm (cutoffFactor ρ p) T (bondGradNorm Hv b) ≤
      c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) * Real.exp (-(2 * r * D (pos b) Y))) :
    |ballCovariance (cutoffFactor ρ p) T Hv (fun η => Ψ η - A η)| ≤
      m⁻¹ * (c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2)) * S *
          (2 * c * (Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) + S * (x * Real.sqrt (8 * S / m))) * S *
            (S * Real.exp (-(r * R / 16)))) +
        m⁻¹ * (c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2)) * S *
          (μ * Real.sqrt (8 * S / m) * (S * Real.exp (-(r * R / 16)))) := by
  set G := Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) with hGd
  set q := Real.sqrt (8 * S / m) with hqd
  set e := Real.exp (-(r * R / 16)) with hed
  have he : 0 < e := Real.exp_pos _
  have hnn := fun y w => pseudoMetric_nonneg hD y w
  have hvn := isBoundedContinuousOn_of_bondGradNorm_le hρ hHv hMv0 hMv
  have hgs : ∀ z, ContDiffOn ℝ 1 (restrictionDefect Λ (Q z)) (openPolyball ι ρ) := fun z =>
    contDiffOn_restrictionDefect hρ Λ (contDiffOn_one_of_two (hQ z).smooth)
  have hgb := fun z => exists_bondGradNorm_restrictionDefect_bound hρ hr hc hx hD (hQ z) Λ
  have hgn : ∀ z, IsBoundedContinuousOn ι ρ (restrictionDefect Λ (Q z)) := fun z => by
    obtain ⟨M, hM0, hM⟩ := hgb z
    exact isBoundedContinuousOn_of_bondGradNorm_le hρ (hgs z) hM0 hM
  have hqs : ContDiffOn ℝ 1 (halfSqNormOn μ Λᶜ) (openPolyball ι ρ) :=
    ((contDiff_halfSqNormOn μ Λᶜ).of_le (by norm_num)).contDiffOn
  have hqb : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm (halfSqNormOn μ Λᶜ) b η ≤ μ * ρ := by
    intro η hη b
    refine (bondGradNorm_halfSqNormOn_le hμ Λᶜ η b).trans ?_
    split_ifs
    · exact mul_le_mul_of_nonneg_left (hη b).le hμ
    · positivity
  have hqn : IsBoundedContinuousOn ι ρ (halfSqNormOn μ Λᶜ) :=
    isBoundedContinuousOn_of_bondGradNorm_le hρ hqs (by positivity) hqb
  have e1 : ballCovariance (cutoffFactor ρ p) T Hv (fun η => Ψ η - A η) =
      (∑ z, ballCovariance (cutoffFactor ρ p) T Hv (restrictionDefect Λ (Q z))) -
        ballCovariance (cutoffFactor ρ p) T Hv (halfSqNormOn μ Λᶜ) := by
    rw [ballCovariance_congr F (fun _ _ => rfl) hsplit, ballCovariance_sub_right F hvn
      (IsBoundedContinuousOn.sum _ _ fun z _ => hgn z) hqn,
      ballCovariance_sum_right F hvn _ _ fun z _ => hgn z]
  rw [e1]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    set Bx := 2 * c * (G + S * (x * q)) with hBx
    have hBx0 : 0 ≤ Bx := by positivity
    have hz : ∀ z, |ballCovariance (cutoffFactor ρ p) T Hv (restrictionDefect Λ (Q z))| ≤
        m⁻¹ * (c * G) * S * (Bx * S * (e * Real.exp (-(r / 4 * D z Y)))) := by
      intro z
      obtain ⟨M, hM0, hM⟩ := hgb z
      obtain ⟨Mc, hMc⟩ := exists_common_bound hρ hHv (hgs z) hMv0 hM0 hMv hM
      by_cases hnear : D z Y < R / 4
      · have h1 := abs_ballCovariance_le_of_decay (B := Bx * e) (z := Y) (z' := z) hρ hr hD Sz hm hS hHv
          (hgs z) hMc (by positivity) (by positivity) hHn (fun b => by
            have hoffz : ∀ b', b' ∉ Λ → R / 4 ≤ D (pos b') z := fun b' hb' => by
              have t := hD.triangle (pos b') z Y
              have := hoff b' hb'
              linarith
            refine (ballL2Norm_restrictionDefect_le_of_far hρ hr hc hx hm hR hSn hD hS F Sz (hQ z) Λ
              hoffz b).trans ?_
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            apply mul_le_mul_of_nonneg_right _ he.le
            simp only [hBx]
            have : 0 ≤ c * (G + S * (x * q)) := by positivity
            linarith)
        refine h1.trans ?_
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h2 : Real.exp (-(r / 2 * D z Y)) ≤ Real.exp (-(r / 4 * D z Y)) := by
          apply Real.exp_le_exp.mpr
          have := hnn z Y
          nlinarith
        calc Bx * e * S * Real.exp (-(r / 2 * D z Y))
            ≤ Bx * e * S * Real.exp (-(r / 4 * D z Y)) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = _ := by ring
      · push Not at hnear
        have h1 := abs_ballCovariance_le_of_decay (B := Bx) (z := Y) (z' := z) hρ hr hD Sz hm hS hHv
          (hgs z) hMc (by positivity) hBx0 hHn (fun b => by
            refine (ballL2Norm_restrictionDefect_le hρ hr hc hx hD F Sz (hQ z) Λ b).trans ?_
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            simp only [hBx]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have : 0 ≤ S * (x * q) := by positivity
            linarith)
        refine h1.trans ?_
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h2 := exp_neg_le_mul_exp_neg (r := r) (R := R) (s := r / 2) (d := D z Y) (by
          have h3 : (R / 4) * r ≤ D z Y * r := mul_le_mul_of_nonneg_right hnear hr.le
          nlinarith)
        calc Bx * S * Real.exp (-(r / 2 * D z Y))
            ≤ Bx * S * (Real.exp (-(r / 4 * D z Y)) * e) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = _ := by ring
    refine (Finset.sum_le_sum fun z _ => hz z).trans ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [mul_comm S e]
    exact mul_le_mul_of_nonneg_left (hSp Y) he.le
  · obtain ⟨Mc, hMc⟩ := exists_common_bound hρ hHv hqs hMv0 (by positivity) hMv hqb
    set Gq : ι → ℝ := fun b => if b ∈ Λ then 0 else μ * q with hGq
    have hGq0 : ∀ b, 0 ≤ Gq b := fun b => by
      simp only [hGq]
      split_ifs
      · exact le_rfl
      · positivity
    have h1 := Sz.covariance_le Hv (halfSqNormOn μ Λᶜ) Mc (c * G) Y Gq hHv hqs hMc (by positivity) hGq0 hHn
      (fun b => by
        set a' : ι → ℝ := fun b' => if b' = b ∧ b ∉ Λ then μ else 0 with ha'
        have ha0 : ∀ b', 0 ≤ a' b' := fun b' => by
          simp only [ha']
          split_ifs
          · exact hμ
          · exact le_rfl
        have key := ballL2Norm_le_of_linear_majorant hρ F Sz hSn hm
          (isBoundedContinuousOn_bondGradNorm hρ hqs hqb b) a' ha0
          (fun η hη => by
            rw [abs_of_nonneg (bondGradNorm_nonneg _ b η)]
            refine (bondGradNorm_halfSqNormOn_le hμ Λᶜ η b).trans ?_
            by_cases hb : b ∈ Λ
            · simp only [Finset.mem_compl, hb, not_true_eq_false, if_false]
              exact Finset.sum_nonneg fun b' _ => mul_nonneg (ha0 b') (norm_nonneg _)
            · simp only [Finset.mem_compl, hb, not_false_eq_true, if_true]
              rw [Finset.sum_eq_single b]
              · simp [ha', hb]
              · intro b' _ hne
                simp [ha', hne]
              · simp)
        refine key.trans (le_of_eq ?_)
        by_cases hb : b ∈ Λ
        · simp [ha', hGq, hb]
        · simp only [ha', hGq, hb, not_false_eq_true, and_true, if_false]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
          rfl)
    refine h1.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h2 : ∀ b, Gq b * Real.exp (-(r / 2 * D (pos b) Y)) ≤
        μ * q * (Real.exp (-(r / 4 * D (pos b) Y)) * e) := by
      intro b
      by_cases hb : b ∈ Λ
      · simp only [hGq, hb, if_true, zero_mul]
        positivity
      · simp only [hGq, hb, if_false]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply exp_neg_le_mul_exp_neg
        have h3 : (R / 2) * r ≤ D (pos b) Y * r := mul_le_mul_of_nonneg_right (hoff b hb) hr.le
        have h4 : 0 ≤ r * R := by positivity
        nlinarith
    refine (Finset.sum_le_sum fun b _ => h2 b).trans ?_
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right (hS Y) he.le
end Measure
theorem three_terms_le_freezingConstant {lam S x c e : ℝ} (hlam : 0 < lam) (hSn : 0 ≤ S) (hx : 1 ≤ x)
    (hc : 1 ≤ c) (he : 0 < e) :
    c * (x / 2 * (8 * S ^ 2 / (x * lam / 4)) + x * (8 * S / (x * lam / 4)) + 1 / 2) * (S * e) +
      ((x * lam / 4)⁻¹ * (c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2)) * S *
          (2 * c * (Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) +
            S * (x * Real.sqrt (8 * S / (x * lam / 4)))) * S * (S * e)) +
        (x * lam / 4)⁻¹ * (c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2)) * S *
          (x * lam * Real.sqrt (8 * S / (x * lam / 4)) * (S * e))) ≤
      c ^ 2 * freezingConstant lam S * e := by
  have hx0 : 0 < x := by linarith
  set m := x * lam / 4 with hm
  have hG2 : 0 ≤ 2 * x ^ 2 * (8 * S ^ 2 / m) + 2 := by positivity
  have hq2 : 0 ≤ 8 * S / m := by positivity
  set G := Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) with hG
  set q := Real.sqrt (8 * S / m) with hq
  have hGs : G ^ 2 = 2 * x ^ 2 * (8 * S ^ 2 / m) + 2 := Real.sq_sqrt hG2
  have hqs : q ^ 2 = 8 * S / m := Real.sq_sqrt hq2
  set N₃ := (4 / lam) * (64 * S ^ 2 / lam + 2) with hN₃
  set N₄ := 128 * S / lam ^ 2 with hN₄
  have hN₃0 : 0 ≤ N₃ := by positivity
  have hN₄0 : 0 ≤ N₄ := by positivity
  have a1 : m⁻¹ * G ^ 2 ≤ N₃ := by
    rw [hGs, hm, hN₃]
    have e1 : (x * lam / 4)⁻¹ * (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) =
        (4 / lam) * (64 * S ^ 2 / lam + 2 / x) := by
      field_simp
      ring
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : 2 / x ≤ 2 := by
      rw [div_le_iff₀ hx0]
      linarith
    linarith
  have a2 : m⁻¹ * (x * q) ^ 2 = N₄ := by
    rw [mul_pow, hqs, hm, hN₄]
    field_simp
    ring
  have a3 : m⁻¹ * G * (x * q) ≤ N₃ + N₄ := by
    have h1 : 0 ≤ m⁻¹ * (G - x * q) ^ 2 := by positivity
    nlinarith
  have first : x / 2 * (8 * S ^ 2 / m) + x * (8 * S / m) + 1 / 2 ≤
      16 * S ^ 2 / lam + 32 * S / lam + 1 := by
    have e1 : x / 2 * (8 * S ^ 2 / m) = 16 * S ^ 2 / lam := by
      rw [hm]
      field_simp
      ring
    have e2 : x * (8 * S / m) = 32 * S / lam := by
      rw [hm]
      field_simp
      ring
    rw [e1, e2]
    linarith
  have t2 : m⁻¹ * (c * G) * S * (2 * c * (G + S * (x * q)) * S * (S * e)) =
      2 * c ^ 2 * S ^ 3 * (m⁻¹ * G ^ 2 + S * (m⁻¹ * G * (x * q))) * e := by ring
  have t3 : m⁻¹ * (c * G) * S * (x * lam * q * (S * e)) =
      c * lam * S ^ 2 * (m⁻¹ * G * (x * q)) * e := by ring
  rw [t2, t3]
  unfold freezingConstant
  rw [← hN₃, ← hN₄]
  have hcc : c ≤ c ^ 2 := by nlinarith
  have b1 : c * (x / 2 * (8 * S ^ 2 / m) + x * (8 * S / m) + 1 / 2) * (S * e) ≤
      c ^ 2 * ((16 * S ^ 2 / lam + 32 * S / lam + 1) * S) * e := by
    have h0 : 0 ≤ 16 * S ^ 2 / lam + 32 * S / lam + 1 := by positivity
    calc c * (x / 2 * (8 * S ^ 2 / m) + x * (8 * S / m) + 1 / 2) * (S * e)
        ≤ c * (16 * S ^ 2 / lam + 32 * S / lam + 1) * (S * e) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left first (by linarith)
      _ ≤ c ^ 2 * (16 * S ^ 2 / lam + 32 * S / lam + 1) * (S * e) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hcc h0
      _ = _ := by ring
  have b2 : 2 * c ^ 2 * S ^ 3 * (m⁻¹ * G ^ 2 + S * (m⁻¹ * G * (x * q))) * e ≤
      c ^ 2 * (2 * S ^ 3 * (N₃ + S * (N₃ + N₄))) * e := by
    have h0 : m⁻¹ * G ^ 2 + S * (m⁻¹ * G * (x * q)) ≤ N₃ + S * (N₃ + N₄) :=
      add_le_add a1 (mul_le_mul_of_nonneg_left a3 hSn)
    calc 2 * c ^ 2 * S ^ 3 * (m⁻¹ * G ^ 2 + S * (m⁻¹ * G * (x * q))) * e
        ≤ 2 * c ^ 2 * S ^ 3 * (N₃ + S * (N₃ + N₄)) * e := by
          apply mul_le_mul_of_nonneg_right _ he.le
          exact mul_le_mul_of_nonneg_left h0 (by positivity)
      _ = _ := by ring
  have b3 : c * lam * S ^ 2 * (m⁻¹ * G * (x * q)) * e ≤ c ^ 2 * (lam * S ^ 2 * (N₃ + N₄)) * e := by
    calc c * lam * S ^ 2 * (m⁻¹ * G * (x * q)) * e
        ≤ c * lam * S ^ 2 * (N₃ + N₄) * e := by
          apply mul_le_mul_of_nonneg_right _ he.le
          exact mul_le_mul_of_nonneg_left a3 (by positivity)
      _ ≤ c ^ 2 * lam * S ^ 2 * (N₃ + N₄) * e := by
          apply mul_le_mul_of_nonneg_right _ he.le
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hcc hlam.le
      _ = _ := by ring
  nlinarith
end FreezingBound
open FreezingBound LocalCalculus in
theorem freezingBoundOnTorus_holds (hseg : MeanDifferenceBoundAlongSegment)
    (hgood : AdmissiblePotentialStability) (hsz : AdmissibleMomentBoundsHold)
    (hmc : CutoffExpectationIsPositiveForm) (hrim : CutoffFactorIsRadialCutoff) :
    FreezingBoundOnTorus := by
  intro ι P _ _ _ ρ r S lam x c R p pos D Ψ H θ Y Λ hρ hr hlam hx hc hR hp hD hΨ hS hSp hθ hsum hH hΛ
  have hx0 : 0 < x := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hm0 : 0 < x * lam / 4 := by positivity
  have h2m : 2 * (x * lam / 4) ≤ x * lam := by nlinarith [mul_pos hx0 hlam]
  have hd : IsPseudoMetricOnBonds (fun b b' => D (pos b) (pos b')) :=
    ⟨fun b => hD.self _, fun b b' => hD.symm _ _, fun b b' b'' => hD.triangle _ _ _⟩
  have hSn : 0 ≤ S := (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le).trans (hS Y)
  obtain ⟨hsg, -, hfrz, -⟩ := hgood ι ρ (x * lam / 4) r (x * lam) _ hρ hm0 hr.le hd h2m
  have gA := hfrz Ψ Λ hΨ
  have cΨ : Continuous Ψ := by
    obtain ⟨K, hK, _⟩ := hΨ
    exact hK.smooth.continuous
  have cA : Continuous (frozenPotential Λ (x * lam) Ψ) := by
    obtain ⟨K, hK, _⟩ := gA
    exact hK.smooth.continuous
  set A := frozenPotential Λ (x * lam) Ψ with hA
  have hH1 := contDiffOn_one_of_two hH.smooth
  have hHc := contDiffOn_restrictedFn hρ Λ hH1
  obtain ⟨MH, hMH0, hMH⟩ := exists_bondGradNorm_bound_of_localTerm hρ hr.le hc0 hx0.le hD hH
  have hHcb : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm (restrictedFn Λ H) b η ≤ MH := by
    intro η hη b
    refine (bondGradNorm_restrictedFn_le hρ Λ hH1 hη b).trans ?_
    split_ifs
    · exact hMH _ (restrictToBonds_mem_openPolyball hρ Λ hη) b
    · exact hMH0
  have nH := isBoundedContinuousOn_of_bondGradNorm_le hρ hH1 hMH0 hMH
  have nHc := isBoundedContinuousOn_of_bondGradNorm_le hρ hHc hMH0 hHcb
  obtain ⟨_, M₁, hM₁⟩ := nH
  obtain ⟨_, M₂, hM₂⟩ := nHc
  have hbdd : ∀ f : BondField ι → ℝ, Continuous f → ∃ M, ∀ η ∈ openPolyball ι ρ, |f η| ≤ M := by
    intro f hf
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : BondField ι) ρ).exists_bound_of_continuousOn
      hf.continuousOn
    refine ⟨M, fun η hη => ?_⟩
    have : η ∈ Metric.closedBall (0 : BondField ι) ρ := by
      rw [openPolyball_eq_ball hρ] at hη
      exact Metric.ball_subset_closedBall hη
    simpa using hM η this
  obtain ⟨M₃, hM₃⟩ := hbdd A cA
  obtain ⟨M₄, hM₄⟩ := hbdd Ψ cΨ
  have hr' := hrim ρ p hρ hp
  have hfin := hseg ι ρ _ A Ψ (restrictedFn Λ H) H (|M₁| + |M₂| + |M₃| + |M₄|)
    (c ^ 2 * freezingConstant lam S * Real.exp (-(r * R / 16))) hρ hr' cA.continuousOn cΨ.continuousOn
    hHc.continuousOn hH1.continuousOn
    (fun η hη => by
      have h1 := hM₁ η hη
      have h2 := hM₂ η hη
      have h3 := hM₃ η hη
      have h4 := hM₄ η hη
      have a1 := le_abs_self M₁
      have a2 := le_abs_self M₂
      have a3 := le_abs_self M₃
      have a4 := le_abs_self M₄
      have b1 := abs_nonneg M₁
      have b2 := abs_nonneg M₂
      have b3 := abs_nonneg M₃
      have b4 := abs_nonneg M₄
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
  have conv : ∀ (Φ f : BondField ι → ℝ),
      ballExpectation (fun u => cutoffFactor ρ p (max u 0)) Φ f = ballExpectation (cutoffFactor ρ p) Φ f := by
    intro Φ f
    unfold ballExpectation ballDensity radialWeightProd
    simp only [max_eq_left (norm_nonneg _)]
  have convc : ∀ (Φ f g : BondField ι → ℝ),
      ballCovariance (fun u => cutoffFactor ρ p (max u 0)) Φ f g = ballCovariance (cutoffFactor ρ p) Φ f g := by
    intro Φ f g
    unfold ballCovariance
    simp only [conv]
  simp only [conv, convc] at hfin
  refine hfin ?_
  intro v hv0 hv1
  have hv1' : 0 ≤ 1 - v := by linarith
  set T := segmentInterpolant A Ψ v with hT
  have gT := hsg A Ψ v gA hΨ hv0 hv1
  have cT : Continuous T := by
    obtain ⟨K, hK, _⟩ := gT
    exact hK.smooth.continuous
  have F := hmc ι ρ p T hρ hp cT
  have Sz := hsz ι P ρ (x * lam / 4) r S p pos D T hρ hm0 hr hp hD gT hS
  have hoff : ∀ b, b ∉ Λ → R / 2 ≤ D (pos b) Y := fun b hb => by
    have : ¬ D (pos b) Y ≤ R / 2 := fun h => hb ((hΛ b).mpr h)
    linarith
  have nD : IsBoundedContinuousOn ι ρ (fun η => H η - restrictedFn Λ H η) :=
    (isBoundedContinuousOn_of_bondGradNorm_le hρ hH1 hMH0 hMH).sub
      (isBoundedContinuousOn_of_bondGradNorm_le hρ hHc hMH0 hHcb)
  have t1 := abs_ballExpectation_restrictionDefect_le hρ hr hx hc0 hm0 hR hD hSn hS F Sz hH hoff nD
  set Hv := segmentInterpolant (restrictedFn Λ H) H v with hHvd
  have hHv : ContDiffOn ℝ 1 Hv (openPolyball ι ρ) :=
    (contDiffOn_const.mul hH1).add (contDiffOn_const.mul hHc)
  have hlin : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm Hv b η ≤ v * bondGradNorm H b η +
      (1 - v) * bondGradNorm (restrictedFn Λ H) b η := by
    intro η hη b
    have := bondGradNorm_linear_combination_le hρ hH1 hHc v (1 - v) hη b
    rwa [abs_of_nonneg hv0, abs_of_nonneg hv1'] at this
  have hMv : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm Hv b η ≤ MH := by
    intro η hη b
    refine (hlin η hη b).trans ?_
    have h1 := mul_le_mul_of_nonneg_left (hMH η hη b) hv0
    have h2 := mul_le_mul_of_nonneg_left (hHcb η hη b) hv1'
    nlinarith
  have hHn : ∀ b, ballL2Norm (cutoffFactor ρ p) T (bondGradNorm Hv b) ≤
      c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) * Real.exp (-(2 * r * D (pos b) Y)) := by
    intro b
    have key := ballL2Norm_bondGradNorm_le_of_majorant (a := c) (w := Real.exp (-(2 ^ 5 * r * D (pos b) Y)))
      hρ hr hx0.le hD F Sz
      hHv hc0 hMv Y (Real.exp_pos _).le (fun η hη => by
        refine (hlin η hη b).trans ?_
        have h1 := mul_le_mul_of_nonneg_left (hH.slope η hη b) hv0
        have h2 := mul_le_mul_of_nonneg_left
          (bondGradNorm_restrictedFn_le_of_localTerm hρ hc0 hx0.le hH Λ hη b) hv1'
        nlinarith)
    refine key.trans ?_
    have hw : Real.exp (-(2 ^ 5 * r * D (pos b) Y)) ≤ Real.exp (-(2 * r * D (pos b) Y)) := by
      apply Real.exp_le_exp.mpr
      have := pseudoMetric_nonneg hD (pos b) Y
      nlinarith
    have hG := Real.sqrt_nonneg (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2)
    calc c * Real.exp (-(2 ^ 5 * r * D (pos b) Y)) * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2)
        = c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) *
            Real.exp (-(2 ^ 5 * r * D (pos b) Y)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
  have hsplit : ∀ η ∈ openPolyball ι ρ,
      Ψ η - A η = (∑ z, restrictionDefect Λ (θ z) η) - halfSqNormOn (x * lam) Λᶜ η := by
    intro η hη
    have h1 := hsum η hη
    have h2 := hsum _ (restrictToBonds_mem_openPolyball hρ Λ hη)
    simp only [hA, frozenPotential, restrictionDefect, restrictedFn, Finset.sum_sub_distrib]
    rw [h1, h2]
    ring
  have t2 := abs_ballCovariance_potentialDifference_le (T := T) hρ hr hc0 hx0.le hm0 hR (by positivity) hSn hD
    hS hSp F Sz hθ hsplit hoff hHv hMH0 hMv hHn
  have tt : |ballExpectation (cutoffFactor ρ p) T (fun η => H η - restrictedFn Λ H η) -
      ballCovariance (cutoffFactor ρ p) T Hv (fun η => Ψ η - A η)| ≤ _ :=
    (abs_sub _ _).trans (add_le_add t1 t2)
  exact tt.trans (three_terms_le_freezingConstant hlam hSn hx hc (Real.exp_pos _))
end YangMills.Construction.ColdStepAtMirrorFrames
end
