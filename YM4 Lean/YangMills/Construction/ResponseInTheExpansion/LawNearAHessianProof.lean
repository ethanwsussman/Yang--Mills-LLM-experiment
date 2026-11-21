import YangMills.Construction.ColdStepAtMirrorFrames.MomentsOfAConvexMeasure
import YangMills.Construction.ResponseInTheExpansion.ByPartsOfACutLaw
import YangMills.Construction.ResponseInTheExpansion.LawNearAHessian
import YangMills.Construction.ResponseInTheExpansion.MomentsOfWeightedSums
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionHasTheConditionsOfThirdOrderProof
import YangMills.Construction.SummableBoundsOfTheFlow.RimMomentsOfALaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearResponse
open MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.ConvexObservables YangMills.Construction.WeightedResponses YangMills.Construction.Moments YangMills.Construction.Estimates YangMills.Construction.Wick
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def configOfCoords (x : ι × Fin 3 → ℝ) : BondField ι :=
  fun b => WithLp.toLp 2 fun i => x (b, i)
theorem configOfCoords_eq_sum (x : ι × Fin 3 → ℝ) :
    configOfCoords x = ∑ r, x r • bondCoordinateVector r := by
  funext b
  have hb : (∑ r, x r • bondCoordinateVector r) b =
      ∑ j, x (b, j) • (EuclideanSpace.single j (1 : ℝ) : BondVector) := by
    rw [Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single b]
    · simp [bondCoordinateVector, bondVariation]
    · intro b' _ hb'
      simp [bondCoordinateVector, bondVariation, Pi.single_eq_of_ne hb'.symm]
    · intro h
      exact absurd (Finset.mem_univ b) h
  rw [hb]
  ext i
  simp [configOfCoords, Finset.sum_apply, Pi.single_apply]
theorem norm_configOfCoords_le (x : ι × Fin 3 → ℝ) (b : ι) :
    ‖configOfCoords x b‖ ≤ ∑ j, |x (b, j)| := by
  have e : configOfCoords x b = ∑ j, x (b, j) • (EuclideanSpace.single j (1 : ℝ) : BondVector) := by
    ext i
    simp [configOfCoords, Finset.sum_apply, Pi.single_apply]
  rw [e]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [norm_smul]
theorem sum_norm_configOfCoords_le (x : ι × Fin 3 → ℝ) : ∑ b, ‖configOfCoords x b‖ ≤ ∑ r, |x r| := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun b _ => norm_configOfCoords_le x b
theorem abs_cutoffRadialDeriv_le (p : ℝ → ℝ) (e v : BondVector) :
    |cutoffRadialDeriv p e v| ≤ ‖v‖ * |deriv p ‖e‖| := by
  unfold cutoffRadialDeriv
  rw [abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  by_cases h : e = 0
  · subst h
    simp
  · have hn : 0 < ‖e‖ := norm_pos_iff.2 h
    rw [abs_div, abs_of_pos hn, div_le_iff₀ hn, mul_comm]
    exact abs_real_inner_le_norm e v
theorem abs_coord_le_norm (η : BondField ι) (r : ι × Fin 3) : |η r.1 r.2| ≤ ‖η r.1‖ := by
  have := PiLp.norm_apply_le (η r.1) r.2
  simpa using this
def coordLinearMap (l : ι × Fin 3 → ℝ) : BondField ι →L[ℝ] ℝ :=
  ∑ r, l r • (EuclideanSpace.proj r.2 : BondVector →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) r.1)
theorem coordLinearMap_apply (l : ι × Fin 3 → ℝ) (η : BondField ι) :
    coordLinearMap l η = ∑ r, l r * η r.1 r.2 := by
  simp [coordLinearMap]
theorem coordLinearMap_configOfCoords (l v : ι × Fin 3 → ℝ) :
    coordLinearMap l (configOfCoords v) = l ⬝ᵥ v := by
  rw [coordLinearMap_apply]
  simp [dotProduct, configOfCoords]
def gaussianMomentConst (W lam : ℝ) (r : ℕ) : ℝ :=
  (∏ k ∈ Finset.range r, (4 * (k : ℝ) + 8 * W)) / (lam / 4) ^ r
theorem gaussianMomentConst_nonneg {W lam : ℝ} (hW : 0 ≤ W) (hlam : 0 < lam) (r : ℕ) :
    0 ≤ gaussianMomentConst W lam r := by
  unfold gaussianMomentConst
  have : 0 ≤ ∏ k ∈ Finset.range r, (4 * (k : ℝ) + 8 * W) :=
    Finset.prod_nonneg fun k _ => by positivity
  positivity
structure BallLawMoments {ι : Type} [Fintype ι] (ρ x : ℝ) (p : ℝ → ℝ) (μ : Measure (BondField ι))
    (Mq Cr : ℕ → ℝ) : Prop where
  ae_in_balls : ∀ᵐ η ∂μ, ∀ b, ‖η b‖ < ρ
  integrable_of_continuous : ∀ f : BondField ι → ℝ, Continuous f → Integrable f μ
  norm_moment_le : ∀ (r : ℕ) (b : ι), ∫ η, ‖η b‖ ^ (2 * r) ∂μ ≤ Mq r * (x ^ r)⁻¹
  integrable_deriv_pow : ∀ (r : ℕ) (b : ι), 1 ≤ r → Integrable (fun η => |deriv p ‖η b‖| ^ (2 * r)) μ
  deriv_moment_le : ∀ (r : ℕ) (b : ι), 1 ≤ r → ∫ η, |deriv p ‖η b‖| ^ (2 * r) ∂μ ≤ Cr r
section Moments
variable {ρ x y : ℝ} {p : ℝ → ℝ} {μ : Measure (BondField ι)} [IsProbabilityMeasure μ]
  {Mq Cr : ℕ → ℝ}
theorem continuous_norm_pow (b : ι) (n : ℕ) :
    Continuous fun η : BondField ι => ‖η b‖ ^ n :=
  ((continuous_apply b).norm).pow n
theorem moment_le_of_abs_le_weighted_sum (hMS : EvenMomentOfWeightedSumBound) (hF : BallLawMoments ρ x p μ Mq Cr)
    (hMq : ∀ r, 0 ≤ Mq r) (hx : 0 < x) (c : ι → ℝ) (hc : ∀ b, 0 ≤ c b) (f : BondField ι → ℝ)
    (hf : Continuous f) (hb : ∀ η, |f η| ≤ ∑ b, c b * ‖η b‖) (r : ℕ) (hr : 1 ≤ r) :
    ∫ η, f η ^ (2 * r) ∂μ ≤ (∑ b, c b) ^ (2 * r) * (Mq r * (x ^ r)⁻¹) := by
  refine (hMS _ μ ι c (fun b η => ‖η b‖) f r (Mq r * (x ^ r)⁻¹) hr hc
    (mul_nonneg (hMq r) (by positivity)) hf.aestronglyMeasurable
    (fun b => hF.integrable_of_continuous _ (continuous_norm_pow b _)) (fun b => hF.norm_moment_le r b)
    (Filter.Eventually.of_forall fun η => ?_)).2
  simpa using hb η
end Moments
section DerivGap
variable {ρ lam x κ Dc W K₀ Ci S : ℝ} {p : ℝ → ℝ} {d kk : ι → ι → ℝ} {P Ψ : BondField ι → ℝ}
  {H : Matrix (ι × Fin 3) (ι × Fin 3) ℝ} {μ : Measure (BondField ι)} [IsProbabilityMeasure μ]
  {Mq Cr : ℕ → ℝ}
def hessianDerivGap (Ψ : BondField ι → ℝ) (H : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) (x : ℝ) (r : ι × Fin 3)
    (η : BondField ι) : ℝ :=
  fderiv ℝ Ψ η (bondCoordinateVector r) - x * H.mulVec (fun c => η c.1 c.2) r
theorem continuous_coords : Continuous fun (η : BondField ι) (c : ι × Fin 3) => η c.1 c.2 := by
  refine continuous_pi fun c => ?_
  exact (EuclideanSpace.proj c.2 : BondVector →L[ℝ] ℝ).continuous.comp (continuous_apply c.1)
theorem continuous_hessianDerivGap (hΨ : ContDiff ℝ 3 Ψ) (r : ι × Fin 3) :
    Continuous (hessianDerivGap Ψ H x r) := by
  unfold hessianDerivGap
  refine ((hΨ.continuous_fderiv (by norm_num)).clm_apply continuous_const).sub
    (continuous_const.mul ?_)
  have : Continuous fun v : ι × Fin 3 → ℝ => H.mulVec v r :=
    ((continuous_apply r)).comp (Continuous.matrix_mulVec continuous_const continuous_id)
  exact this.comp continuous_coords
end DerivGap
theorem isOpen_balls (ρ : ℝ) : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by apply _root_.YangMills.SharedProofs.p5886 <;> assumption
theorem fderiv_eq_of_eqOn_balls {ρ : ℝ} {P Ψ : BondField ι → ℝ} (h : ∀ η, (∀ b, ‖η b‖ < ρ) → Ψ η = P η)
    {η : BondField ι} (hη : ∀ b, ‖η b‖ < ρ) : fderiv ℝ Ψ η = fderiv ℝ P η := by
  have : Ψ =ᶠ[nhds η] P := by
    filter_upwards [(isOpen_balls ρ).mem_nhds hη] with ζ hζ using h ζ hζ
  exact this.fderiv_eq
section Remainder
variable {ρ lam x κ Dc W K₀ Ci S : ℝ} {p : ℝ → ℝ} {d kk : ι → ι → ℝ} {P Ψ : BondField ι → ℝ}
  {H : Matrix (ι × Fin 3) (ι × Fin 3) ℝ} {μ : Measure (BondField ι)} [IsProbabilityMeasure μ]
  {Mq Cr : ℕ → ℝ}
def derivGapConst (K₀ S : ℝ) (Mq : ℕ → ℝ) (r : ℕ) : ℝ := (2 * K₀) ^ (2 * r) * (1 + S ^ (4 * r) * Mq (2 * r))
theorem hessianDerivGap_moment_le (hMS : EvenMomentOfWeightedSumBound) (hF : BallLawMoments ρ x p μ Mq Cr)
    (hMq : ∀ r, 0 ≤ Mq r) (hx : 0 < x) (hK₀ : 0 ≤ K₀) (hS : 0 ≤ S) (hΨ : ContDiff ℝ 3 Ψ)
    (hΨe : ∀ η, (∀ b, ‖η b‖ < ρ) → Ψ η = P η) (hN : IsNearHessian ρ lam x κ Dc W K₀ Ci S d kk P H)
    (c : ι × Fin 3) (r : ℕ) (hr : 1 ≤ r) :
    ∫ η, hessianDerivGap Ψ H x c η ^ (2 * r) ∂μ ≤ derivGapConst K₀ S Mq r := by
  set Tn : BondField ι → ℝ := fun η => ∑ b', kk c.1 b' * ‖η b'‖ with hTn
  have hTc : Continuous Tn :=
    continuous_finsetSum _ fun b' _ => continuous_const.mul (continuous_apply b').norm
  have hT0 : ∀ η, 0 ≤ Tn η := fun η =>
    Finset.sum_nonneg fun b' _ => mul_nonneg (hN.kernel_nonneg _ _) (norm_nonneg _)
  have hT := moment_le_of_abs_le_weighted_sum hMS hF hMq hx (kk c.1) (hN.kernel_nonneg c.1) Tn hTc
    (fun η => by rw [abs_of_nonneg (hT0 η)]) (2 * r) (by omega)
  have hsum0 : 0 ≤ ∑ b', kk c.1 b' := Finset.sum_nonneg fun b' _ => hN.kernel_nonneg _ _
  have hpw : (∑ b', kk c.1 b') ^ (2 * (2 * r)) ≤ S ^ (4 * r) := by
    have : 2 * (2 * r) = 4 * r := by ring
    rw [this]
    exact pow_le_pow_left₀ hsum0 (hN.kernel_sum c.1) _
  set g2 : BondField ι → ℝ := fun η => x * Tn η ^ 2 with hg2
  have hg2c : Continuous g2 := continuous_const.mul (hTc.pow 2)
  have hpow : ∀ η, g2 η ^ (2 * r) = x ^ (2 * r) * Tn η ^ (2 * (2 * r)) := by
    intro η
    simp only [hg2]
    rw [mul_pow, ← pow_mul]
  have hg2m : ∫ η, g2 η ^ (2 * r) ∂μ ≤ S ^ (4 * r) * Mq (2 * r) := by
    simp only [hpow]
    rw [integral_const_mul]
    have hxr : 0 < x ^ (2 * r) := by positivity
    calc x ^ (2 * r) * ∫ η, Tn η ^ (2 * (2 * r)) ∂μ
        ≤ x ^ (2 * r) * ((∑ b', kk c.1 b') ^ (2 * (2 * r)) * (Mq (2 * r) * (x ^ (2 * r))⁻¹)) :=
          mul_le_mul_of_nonneg_left hT hxr.le
      _ = (∑ b', kk c.1 b') ^ (2 * (2 * r)) * Mq (2 * r) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hpw (hMq _)
  have hD0 : 0 ≤ 1 + S ^ (4 * r) * Mq (2 * r) := by
    have := hMq (2 * r)
    positivity
  have hm := (hMS _ μ Bool (fun _ => K₀) (fun i η => if i then 1 else g2 η) (hessianDerivGap Ψ H x c) r
    (1 + S ^ (4 * r) * Mq (2 * r)) hr (fun _ => hK₀) hD0
    (continuous_hessianDerivGap hΨ c).aestronglyMeasurable
    (fun i => by
      cases i
      · have := hF.integrable_of_continuous (fun η => g2 η ^ (2 * r)) (hg2c.pow _)
        simpa using this
      · simp)
    (fun i => by
      cases i
      · simp only [Bool.false_eq_true, if_false]
        have : 0 ≤ S ^ (4 * r) * Mq (2 * r) := mul_nonneg (by positivity) (hMq _)
        linarith
      · simp only [if_true, one_pow, integral_const, probReal_univ, smul_eq_mul, mul_one]
        have : 0 ≤ S ^ (4 * r) * Mq (2 * r) := mul_nonneg (by positivity) (hMq _)
        linarith)
    (by
      filter_upwards [hF.ae_in_balls] with η hη
      have h1 := hN.deriv_near_linear η hη c
      rw [← fderiv_eq_of_eqOn_balls hΨe hη] at h1
      simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, abs_one, mul_one]
      have h2 : |g2 η| = g2 η := abs_of_nonneg (mul_nonneg hx.le (sq_nonneg _))
      rw [h2]
      calc |hessianDerivGap Ψ H x c η| ≤ K₀ * (1 + x * Tn η ^ 2) := h1
        _ = _ := by
            simp only [hg2]
            ring)).2
  refine hm.trans (le_of_eq ?_)
  unfold derivGapConst
  simp only [Fintype.sum_bool]
  ring_nf
def byPartsRemainder (Ψ : BondField ι → ℝ) (H : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) (x : ℝ) (p : ℝ → ℝ)
    (v : ι × Fin 3 → ℝ) (η : BondField ι) : ℝ :=
  ∑ r, v r * hessianDerivGap Ψ H x r η + ∑ b, cutoffRadialDeriv p (η b) (configOfCoords v b)
theorem measurable_cutoffRadialDeriv (p : ℝ → ℝ) (b : ι) (w : BondVector) :
    Measurable fun η : BondField ι => cutoffRadialDeriv p (η b) w := by
  unfold cutoffRadialDeriv
  have hn : Measurable fun η : BondField ι => ‖η b‖ := ((continuous_apply b).norm).measurable
  have hi : Continuous fun η : BondField ι => inner ℝ (η b) w :=
    (continuous_apply b).inner continuous_const
  exact ((measurable_deriv p).comp hn).mul (hi.measurable.div hn)
theorem measurable_byPartsRemainder (hΨ : ContDiff ℝ 3 Ψ) (v : ι × Fin 3 → ℝ) :
    Measurable (byPartsRemainder Ψ H x p v) := by
  unfold byPartsRemainder
  refine Measurable.add ?_ ?_
  · exact Finset.measurable_sum _ fun r _ => (continuous_hessianDerivGap hΨ r).measurable.const_mul _
  · exact Finset.measurable_sum _ fun b _ => measurable_cutoffRadialDeriv p b _
theorem byPartsRemainder_moment (hMS : EvenMomentOfWeightedSumBound) (hF : BallLawMoments ρ x p μ Mq Cr)
    (hMq : ∀ r, 0 ≤ Mq r) (hCr : ∀ r, 0 ≤ Cr r) (hx : 0 < x) (hK₀ : 0 ≤ K₀) (hS : 0 ≤ S)
    (hΨ : ContDiff ℝ 3 Ψ) (hΨe : ∀ η, (∀ b, ‖η b‖ < ρ) → Ψ η = P η)
    (hN : IsNearHessian ρ lam x κ Dc W K₀ Ci S d kk P H) (v : ι × Fin 3 → ℝ) (r : ℕ) (hr : 1 ≤ r) :
    Integrable (fun η => byPartsRemainder Ψ H x p v η ^ (2 * r)) μ ∧
    ∫ η, byPartsRemainder Ψ H x p v η ^ (2 * r) ∂μ ≤
      (2 * ∑ c, |v c|) ^ (2 * r) * (derivGapConst K₀ S Mq r + Cr r) := by
  have hG0 : 0 ≤ derivGapConst K₀ S Mq r := by
    unfold derivGapConst
    have := hMq (2 * r)
    positivity
  have hm := hMS _ μ ((ι × Fin 3) ⊕ ι)
    (Sum.elim (fun c => |v c|) (fun b => ‖configOfCoords v b‖))
    (Sum.elim (fun c η => hessianDerivGap Ψ H x c η) (fun b η => |deriv p ‖η b‖|))
    (byPartsRemainder Ψ H x p v) r (derivGapConst K₀ S Mq r + Cr r) hr
    (by
      rintro (c | b)
      · exact abs_nonneg _
      · exact norm_nonneg _)
    (add_nonneg hG0 (hCr r)) (measurable_byPartsRemainder hΨ v).aestronglyMeasurable
    (by
      rintro (c | b)
      · exact hF.integrable_of_continuous _ ((continuous_hessianDerivGap hΨ c).pow _)
      · exact hF.integrable_deriv_pow r b hr)
    (by
      rintro (c | b)
      · have := hessianDerivGap_moment_le hMS hF hMq hx hK₀ hS hΨ hΨe hN c r hr
        have h2 := hCr r
        simp only [Sum.elim_inl]
        linarith
      · have := hF.deriv_moment_le r b hr
        simp only [Sum.elim_inr]
        linarith)
    (Filter.Eventually.of_forall fun η => by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, abs_abs]
      unfold byPartsRemainder
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [abs_mul]
      · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact Finset.sum_le_sum fun b _ => abs_cutoffRadialDeriv_le p _ _)
  refine ⟨hm.1, hm.2.trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (add_nonneg hG0 (hCr r))
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have h0 : 0 ≤ (∑ c, |v c|) + ∑ b, ‖configOfCoords v b‖ :=
    add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  refine pow_le_pow_left₀ h0 ?_ _
  have := sum_norm_configOfCoords_le v
  linarith
end Remainder
section ByParts
variable {ρ x : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ}
  {H : Matrix (ι × Fin 3) (ι × Fin 3) ℝ} {μ : Measure (BondField ι)}
theorem coordLinearMap_eq_dotProduct (l : ι × Fin 3 → ℝ) (η : BondField ι) :
    coordLinearMap l η = l ⬝ᵥ fun c => η c.1 c.2 := by
  rw [coordLinearMap_apply]
  rfl
theorem deriv_along_inverse_hessian (hsym : H.IsSymm) (hdet : IsUnit H.det) (l : ι × Fin 3 → ℝ)
    (η : BondField ι) :
    fderiv ℝ Ψ η (configOfCoords (H⁻¹.mulVec l)) +
        ∑ b, cutoffRadialDeriv p (η b) (configOfCoords (H⁻¹.mulVec l) b) =
      x * coordLinearMap l η + byPartsRemainder Ψ H x p (H⁻¹.mulVec l) η := by
  set v := H⁻¹.mulVec l with hv
  set c : ι × Fin 3 → ℝ := fun c => η c.1 c.2 with hc
  have h1 : fderiv ℝ Ψ η (configOfCoords v) = ∑ r, v r * fderiv ℝ Ψ η (bondCoordinateVector r) := by
    rw [configOfCoords_eq_sum, map_sum]
    simp
  have hHv : H.mulVec v = l := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H hdet, Matrix.one_mulVec]
  have h2 : ∑ r, v r * H.mulVec c r = coordLinearMap l η := by
    have e1 : ∑ r, v r * H.mulVec c r = v ⬝ᵥ H.mulVec c := rfl
    have e2 : Matrix.vecMul v H = H.mulVec v := by
      have := Matrix.vecMul_transpose H v
      rwa [hsym.eq] at this
    rw [e1, Matrix.dotProduct_mulVec, e2, hHv, coordLinearMap_eq_dotProduct]
  unfold byPartsRemainder hessianDerivGap
  rw [h1]
  have h3 : ∑ r, v r * (fderiv ℝ Ψ η (bondCoordinateVector r) - x * H.mulVec c r) =
      ∑ r, v r * fderiv ℝ Ψ η (bondCoordinateVector r) - x * ∑ r, v r * H.mulVec c r := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [h3, h2]
  ring
theorem integration_by_parts_linear [IsProbabilityMeasure μ] (hBP : cutoffIntegrationByPartsStatement)
    (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (hΨ : ContDiff ℝ 3 Ψ) (hmean : ∀ f : BondField ι → ℝ, ∫ η, f η ∂μ = ballExpectation (cutoffFactor ρ p) Ψ f)
    (hc : ∀ f : BondField ι → ℝ, Continuous f → Integrable f μ) (hsym : H.IsSymm) (hdet : IsUnit H.det)
    {q : ℕ} (l : Fin q → ι × Fin 3 → ℝ) {y : ℝ} (hx : 0 < x) (hy : y ^ 2 = x⁻¹)
    (hRint : ∀ a, Integrable (fun η => byPartsRemainder Ψ H x p (H⁻¹.mulVec (l a)) η ^ 2) μ)
    (hRm : ∀ a, AEStronglyMeasurable (byPartsRemainder Ψ H x p (H⁻¹.mulVec (l a))) μ)
    (s : Finset (Fin q)) (a : Fin q) :
    ∫ ω, (∏ i ∈ s, coordLinearMap (l i) ω) * coordLinearMap (l a) ω ∂μ =
      y ^ 2 * (∑ i ∈ s, (l i ⬝ᵥ H⁻¹.mulVec (l a)) * ∫ ω, ∏ j ∈ s.erase i, coordLinearMap (l j) ω ∂μ) -
        y ^ 2 * ∫ ω, (∏ i ∈ s, coordLinearMap (l i) ω) * byPartsRemainder Ψ H x p (H⁻¹.mulVec (l a)) ω ∂μ := by
  set v := H⁻¹.mulVec (l a) with hv
  set u := configOfCoords v with hu
  set g : BondField ι → ℝ := fun η => ∏ i ∈ s, coordLinearMap (l i) η with hg
  have hgc : ContDiff ℝ 1 g := contDiff_prod fun i _ => (coordLinearMap (l i)).contDiff
  have hgd : ∀ η, fderiv ℝ g η u =
      ∑ i ∈ s, (l i ⬝ᵥ v) * ∏ j ∈ s.erase i, coordLinearMap (l j) η := by
    intro η
    have h := HasFDerivAt.finsetProd (u := s) (g := fun i ζ => coordLinearMap (l i) ζ)
      (g' := fun i => coordLinearMap (l i)) (x := η) fun i _ => (coordLinearMap (l i)).hasFDerivAt
    have e : fderiv ℝ g η = _ := h.fderiv
    rw [e]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu, coordLinearMap_configOfCoords]
    ring
  have hbp := hBP ι ρ p Ψ g u hρ hp (hΨ.of_le (by norm_num)) hgc
  have hm : ∫ η, fderiv ℝ g η u ∂μ =
      ∫ η, g η * (fderiv ℝ Ψ η u + ∑ b, cutoffRadialDeriv p (η b) (u b)) ∂μ := by
    rw [hmean, hmean]
    unfold ballExpectation
    rw [hbp]
  have hid : ∀ η, g η * (fderiv ℝ Ψ η u + ∑ b, cutoffRadialDeriv p (η b) (u b)) =
      x * (g η * coordLinearMap (l a) η) + g η * byPartsRemainder Ψ H x p v η := by
    intro η
    rw [hu, hv, deriv_along_inverse_hessian (x := x) (p := p) (Ψ := Ψ) hsym hdet]
    ring
  have hgcont : Continuous g := hgc.continuous
  have hi1 : Integrable (fun η => g η * coordLinearMap (l a) η) μ :=
    hc _ (hgcont.mul (coordLinearMap (l a)).continuous)
  have hi2 : Integrable (fun η => g η * byPartsRemainder Ψ H x p v η) μ := by
    have hdom : Integrable (fun η => g η ^ 2 + byPartsRemainder Ψ H x p v η ^ 2) μ :=
      (hc _ (hgcont.pow 2)).add (hRint a)
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun η => ?_)
    · exact (hgcont.aestronglyMeasurable).mul (hRm a)
    · rw [Real.norm_eq_abs, abs_mul]
      nlinarith [sq_abs (g η), sq_abs (byPartsRemainder Ψ H x p v η),
        sq_nonneg (|g η| - |byPartsRemainder Ψ H x p v η|),
        abs_nonneg (g η), abs_nonneg (byPartsRemainder Ψ H x p v η)]
  have hL : ∫ η, fderiv ℝ g η u ∂μ =
      ∑ i ∈ s, (l i ⬝ᵥ v) * ∫ ω, ∏ j ∈ s.erase i, coordLinearMap (l j) ω ∂μ := by
    simp only [hgd]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul]
    · intro i _
      refine (hc _ ?_).const_mul _
      exact continuous_finsetProd _ fun j _ => (coordLinearMap (l j)).continuous
  have hR : ∫ η, g η * (fderiv ℝ Ψ η u + ∑ b, cutoffRadialDeriv p (η b) (u b)) ∂μ =
      x * (∫ η, g η * coordLinearMap (l a) η ∂μ) + ∫ η, g η * byPartsRemainder Ψ H x p v η ∂μ := by
    simp only [hid]
    rw [integral_add (hi1.const_mul x) hi2, integral_const_mul]
  rw [hL, hR] at hm
  have hx0 : x ≠ 0 := hx.ne'
  rw [hy, hm]
  field_simp
  ring
end ByParts
set_option maxHeartbeats 1000000 in
theorem gaussianMomentsNearHessian_proof (hMom : GaussianMomentBound) (hRM : cutoffDerivMomentsStatement)
    (hLaw : normalizedBallLawIsProbabilityStatement) (hRim : CutoffFactorIsRadialCutoff)
    (hMC : CutoffExpectationIsPositiveForm) (hBP : cutoffIntegrationByPartsStatement)
    (hMS : EvenMomentOfWeightedSumBound) (hWick : WickOfIntegrationByParts) :
    GaussianMomentsNearHessian := by
  intro ρ p lam Dc W K₀ Ci S hρ hp hlam hDc hW hK₀ hCi hS q
  have hMq : ∀ r, 0 ≤ gaussianMomentConst W lam r := gaussianMomentConst_nonneg hW hlam
  set Mq := gaussianMomentConst W lam with hMqd
  have hRr := fun r : ℕ => hRM ρ p lam Dc W hρ hp hlam hDc hW 1 (2 * max r 1) 0 le_rfl
    (by have := le_max_right r 1; omega)
  choose Cr hCr0 hCr using hRr
  set A : ℕ → ℝ := fun r => 1 + Mq r + (2 * Ci) ^ (2 * r) * (derivGapConst K₀ S Mq r + Cr r) with hA
  have hG0 : ∀ r, 0 ≤ derivGapConst K₀ S Mq r := by
    intro r
    unfold derivGapConst
    have := hMq (2 * r)
    positivity
  have hR0 : ∀ r, 0 ≤ (2 * Ci) ^ (2 * r) * (derivGapConst K₀ S Mq r + Cr r) := fun r =>
    mul_nonneg (by positivity) (add_nonneg (hG0 r) (hCr0 r))
  have hA1 : ∀ r, 1 ≤ A r := fun r => by
    have := hMq r
    have := hR0 r
    simp only [hA]
    linarith
  have hAM : ∀ r, Mq r ≤ A r := fun r => by
    have := hR0 r
    simp only [hA]
    linarith
  have hAR : ∀ r, (2 * Ci) ^ (2 * r) * (derivGapConst K₀ S Mq r + Cr r) ≤ A r := fun r => by
    have := hMq r
    simp only [hA]
    linarith
  obtain ⟨Cw, hCw0, hWk⟩ := hWick A Ci
  refine ⟨Cw q, hCw0 q, ?_⟩
  intro ι _ _ x κ d kk P H hx hκ hN l
  obtain ⟨Ψ, K, hΨe, hΨc, hΨ0⟩ := hN.convexMember
  have hΨ3 : ContDiff ℝ 3 Ψ := hΨc.smooth
  have hx0 : 0 < x := by linarith
  have hcontΨ : Continuous Ψ := hΨ3.continuous
  obtain ⟨hprob, hint, _, hae, _⟩ := hLaw ι ρ p Ψ hρ hp hcontΨ
  obtain ⟨_, _, hiff, _⟩ := hLaw ι ρ p Ψ hρ hp hcontΨ
  set μ := YangMills.Construction.ConvexObservables.normalizedBallLaw (cutoffFactor ρ p) Ψ with hμ
  haveI := hprob
  have hm0 : 0 < x * lam / 4 := by positivity
  have hrim := hRim ρ p hρ hp
  have hdens : ballDensity (fun u => cutoffFactor ρ p (max u 0)) Ψ = ballDensity (cutoffFactor ρ p) Ψ := by
    funext η
    unfold ballDensity radialWeightProd
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    change cutoffFactor ρ p (max ‖η b‖ 0) = _
    rw [max_eq_left (norm_nonneg (η b))]
  have hslopeΨ : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ (b : ι) (e : BondVector),
      |bondPartialDeriv Ψ b η e| ≤ Dc * x * ‖e‖ := by
    intro η hη b e
    have := hN.deriv_bound η hη b e
    unfold bondPartialDeriv at this ⊢
    rwa [fderiv_eq_of_eqOn_balls hΨe hη]
  have hF : BallLawMoments ρ x p μ Mq Cr := by
    refine ⟨hae, ?_, ?_, ?_, ?_⟩
    · intro f hf
      obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : BondField ι) ρ).exists_bound_of_continuousOn
        hf.continuousOn
      refine Integrable.of_bound hf.aestronglyMeasurable C ?_
      filter_upwards [hae] with η hη
      apply hC
      rw [mem_closedBall_zero_iff]
      exact (pi_norm_le_iff_of_nonneg hρ.le).mpr fun b => (hη b).le
    · intro r b
      have h1 := hMom ι ρ (x * lam / 4) κ W d Ψ K (fun u => cutoffFactor ρ p (max u 0)) hρ hm0 hκ hrim
        hN.isPseudoMetric hΨc hN.weight_sum hΨ0 r b
      rw [hint]
      have e1 : ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ (2 * r)) =
          ballExpectation (fun u => cutoffFactor ρ p (max u 0)) Ψ (fun η => ‖η b‖ ^ (2 * r)) := by
        unfold ballExpectation
        rw [hdens]
      rw [e1]
      refine h1.trans (le_of_eq ?_)
      simp only [hMqd, gaussianMomentConst]
      have e2 : x * lam / 4 = x * (lam / 4) := by ring
      rw [e2, mul_pow]
      field_simp
    · intro r b hr
      have h1 := (hCr r ι x κ d Ψ K hx hκ hN.isPseudoMetric hΨc hN.weight_sum hΨ0 hslopeΨ b).1
      rw [max_eq_left hr, iteratedDeriv_one] at h1
      exact (hiff _).2 h1
    · intro r b hr
      have h1 := (hCr r ι x κ d Ψ K hx hκ hN.isPseudoMetric hΨc hN.weight_sum hΨ0 hslopeΨ b).2
      rw [max_eq_left hr, iteratedDeriv_one] at h1
      rw [hint]
      simpa using h1
  set y : ℝ := x ^ (-(1 / 2 : ℝ)) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hx0 _
  have hyn : ∀ n : ℕ, y ^ n = x ^ (-(n : ℝ) / 2) := by
    intro n
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  have hy2 : y ^ 2 = x⁻¹ := by
    rw [hyn 2]
    have : -((2 : ℕ) : ℝ) / 2 = -1 := by norm_num
    rw [this, Real.rpow_neg_one]
  have hy2r : ∀ r : ℕ, y ^ (2 * r) = (x ^ r)⁻¹ := by
    intro r
    rw [pow_mul, hy2, inv_pow]
  have hRmom := fun (v : ι × Fin 3 → ℝ) (r : ℕ) (hr : 1 ≤ r) =>
    byPartsRemainder_moment hMS hF hMq hCr0 hx0 hK₀ hS hΨ3 hΨe hN v r hr
  have hkey : ∀ Λ : Fin q → ℝ, (∀ i, 0 < Λ i) → (∀ i, ∑ r, |l i r| ≤ Λ i) →
      |(∫ ω, ∏ i, coordLinearMap (l i) ω ∂μ) -
          y ^ q * pairingSum (fun i j => l i ⬝ᵥ H⁻¹.mulVec (l j)) Finset.univ| ≤
        Cw q * y ^ (q + 1) * ∏ i, Λ i := by
    intro Λ hΛ0 hΛ
    have hvl : ∀ a, ∑ r, |H⁻¹.mulVec (l a) r| ≤ Ci * Λ a := fun a =>
      (hN.inverse_bound (l a)).trans (mul_le_mul_of_nonneg_left (hΛ a) hCi)
    have hRd : GaussianByParts μ (fun i => coordLinearMap (l i))
        (fun a => byPartsRemainder Ψ H x p (H⁻¹.mulVec (l a)))
        (fun i j => l i ⬝ᵥ H⁻¹.mulVec (l j)) y Λ A Ci := by
      refine ⟨fun i r => hF.integrable_of_continuous _ ((coordLinearMap (l i)).continuous.pow _), ?_, ?_, ?_, ?_, ?_⟩
      · intro a r
        rcases Nat.eq_zero_or_pos r with rfl | hr
        · simp
        · exact (hRmom _ r hr).1
      · intro i r
        rcases Nat.eq_zero_or_pos r with rfl | hr
        · simpa using hA1 0
        · have hb := moment_le_of_abs_le_weighted_sum hMS hF hMq hx0 (fun b => ∑ j, |l i (b, j)|)
            (fun b => Finset.sum_nonneg fun _ _ => abs_nonneg _) (coordLinearMap (l i))
            (coordLinearMap (l i)).continuous (fun η => by
              rw [coordLinearMap_apply]
              refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
              rw [Fintype.sum_prod_type]
              refine Finset.sum_le_sum fun b _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_le_sum fun j _ => ?_
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (abs_coord_le_norm η (b, j)) (abs_nonneg _)) r hr
          refine hb.trans ?_
          have hs : ∑ b, ∑ j, |l i (b, j)| = ∑ c, |l i c| :=
            (Fintype.sum_prod_type (fun c => |l i c|)).symm
          rw [hs, ← hy2r r, mul_pow]
          have h0 : 0 ≤ ∑ c, |l i c| := Finset.sum_nonneg fun _ _ => abs_nonneg _
          have hp1 : (∑ c, |l i c|) ^ (2 * r) ≤ Λ i ^ (2 * r) := pow_le_pow_left₀ h0 (hΛ i) _
          have hy' : 0 ≤ y ^ (2 * r) := by positivity
          calc (∑ c, |l i c|) ^ (2 * r) * (Mq r * y ^ (2 * r))
              ≤ Λ i ^ (2 * r) * (A r * y ^ (2 * r)) :=
                mul_le_mul hp1 (mul_le_mul_of_nonneg_right (hAM r) hy')
                  (mul_nonneg (hMq r) hy') (by have := hΛ0 i; positivity)
            _ = _ := by ring
      · intro a r
        rcases Nat.eq_zero_or_pos r with rfl | hr
        · simpa using hA1 0
        · refine (hRmom _ r hr).2.trans ?_
          have h0 : 0 ≤ ∑ c, |H⁻¹.mulVec (l a) c| := Finset.sum_nonneg fun _ _ => abs_nonneg _
          have hp1 : (2 * ∑ c, |H⁻¹.mulVec (l a) c|) ^ (2 * r) ≤ (2 * (Ci * Λ a)) ^ (2 * r) :=
            pow_le_pow_left₀ (by positivity) (by have := hvl a; linarith) _
          have hp2 : 0 ≤ Λ a ^ (2 * r) := by
            have := hΛ0 a
            positivity
          calc (2 * ∑ c, |H⁻¹.mulVec (l a) c|) ^ (2 * r) * (derivGapConst K₀ S Mq r + Cr r)
              ≤ (2 * (Ci * Λ a)) ^ (2 * r) * (derivGapConst K₀ S Mq r + Cr r) :=
                mul_le_mul_of_nonneg_right hp1 (add_nonneg (hG0 r) (hCr0 r))
            _ = ((2 * Ci) ^ (2 * r) * (derivGapConst K₀ S Mq r + Cr r)) * Λ a ^ (2 * r) := by
                rw [← mul_assoc, mul_pow]
                ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (hAR r) hp2
      · intro i j
        have h1 : |l i ⬝ᵥ H⁻¹.mulVec (l j)| ≤ ∑ r, |l i r| * |H⁻¹.mulVec (l j) r| := by
          simp only [dotProduct]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [abs_mul]
        have h2 : ∑ r, |l i r| * |H⁻¹.mulVec (l j) r| ≤
            (∑ r, |l i r|) * ∑ r, |H⁻¹.mulVec (l j) r| := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact Finset.single_le_sum (f := fun r => |H⁻¹.mulVec (l j) r|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ r)
        have h3 : (∑ r, |l i r|) * ∑ r, |H⁻¹.mulVec (l j) r| ≤ Λ i * (Ci * Λ j) :=
          mul_le_mul (hΛ i) (hvl j) (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hΛ0 i).le
        calc _ ≤ Λ i * (Ci * Λ j) := h1.trans (h2.trans h3)
          _ = Ci * Λ i * Λ j := by ring
      · intro s a _ _
        refine integration_by_parts_linear hBP hρ hp hΨ3 hint hF.integrable_of_continuous hN.isSymm
          hN.isUnit_det l hx0 hy2 ?_ ?_ s a
        · intro a
          have := (hRmom (H⁻¹.mulVec (l a)) 1 le_rfl).1
          simpa using this
        · intro a
          exact (measurable_byPartsRemainder hΨ3 _).aestronglyMeasurable
    have hf := hWk _ μ q _ _ _ y Λ hy0 hΛ0 hRd Finset.univ
    simpa [Finset.card_univ, Fintype.card_fin] using hf
  have hmeanP : ballExpectation (cutoffFactor ρ p) P (fun η => ∏ i, ∑ r, l i r * η r.1 r.2) =
      ∫ ω, ∏ i, coordLinearMap (l i) ω ∂μ := by
    rw [hint, (hMC ι ρ p Ψ hρ hp hcontΨ).congr_potential P _ fun η hη => hΨe η hη]
    congr 1
    funext η
    exact Finset.prod_congr rfl fun i _ => (coordLinearMap_apply _ _).symm
  rw [hmeanP, ← hyn q]
  have e1 : x ^ (-((q : ℝ) + 1) / 2) = y ^ (q + 1) := by
    rw [hyn (q + 1)]
    push_cast
    rfl
  rw [e1]
  set Ls : Fin q → ℝ := fun i => ∑ r, |l i r| with hLs
  have hLs0 : ∀ i, 0 ≤ Ls i := fun i => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcont : Continuous fun ε : ℝ => Cw q * y ^ (q + 1) * ∏ i, (Ls i + ε) :=
    continuous_const.mul (continuous_finsetProd _ fun i _ => continuous_const.add continuous_id)
  have hlim : Filter.Tendsto (fun ε : ℝ => Cw q * y ^ (q + 1) * ∏ i, (Ls i + ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Cw q * y ^ (q + 1) * ∏ i, (Ls i + 0))) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hfin := ge_of_tendsto hlim (Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε =>
    hkey (fun i => Ls i + ε) (fun i => add_pos_of_nonneg_of_pos (hLs0 i) hε)
      (fun i => le_add_of_nonneg_right (le_of_lt hε)))
  simpa using hfin
end YangMills.Construction.LinearResponse
end
