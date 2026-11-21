import YangMills.Construction.Matrices.OrthogonalityRelationsAndPeterWeylOnGProof
import YangMills.Construction.Matrices.ProjectionsOntoCoefficientSpacesOfG
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices YangMills.Construction.Matrices.ComplexMatrix2
open scoped Matrix.Norms.L2Operator ENNReal
noncomputable section
namespace YangMills.Construction.SpinHarmonics
namespace CoeffProjections
variable {l : HalfNatural}
theorem homogeneousInner_monomialBasis_left (l : HalfNatural) (i : Fin (l.doubled + 1))
    (Q : homogeneousSpace l) : homogeneousInner l (monomialBasis l i) Q = monomialCoord l i Q := by
  simp [homogeneousInner, monomialCoord_monomialBasis, apply_ite star]
theorem spinCoeff_mul (hRep : SpinRepFacts l l) (i k : Fin (l.doubled + 1))
    (x y : ComplexMatrix2.specialUnitary) :
    spinCoeff l i k (x * y) =
      ∑ j, spinCoeff l i j x * spinCoeff l j k y := by
  have hexpand := sum_monomialCoord_smul_monomialBasis l (spinRep l y (monomialBasis l k))
  simp only [spinCoeff, homogeneousInner_monomialBasis_left]
  rw [hRep.spinRep_mul, LinearMap.comp_apply]
  conv_lhs => rw [← hexpand]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul, smul_eq_mul, mul_comm]
theorem spinCharacter_eq_sum_spinCoeff (l : HalfNatural) (x : ComplexMatrix2.specialUnitary) :
    spinCharacter l x = ∑ i, spinCoeff l i i x := by
  simp [spinCharacter, spinCoeffMap]
theorem spinCharacter_mul_inv (hRep : SpinRepFacts l l) (x x' : ComplexMatrix2.specialUnitary) :
    spinCharacter l (x * x'⁻¹) =
      ∑ q : Fin (l.doubled + 1) × Fin (l.doubled + 1),
        spinCoeff l q.1 q.2 x * star (spinCoeff l q.1 q.2 x') := by
  rw [spinCharacter_eq_sum_spinCoeff, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [spinCoeff_mul hRep]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hRep.spinCoeff_inv]
theorem integrable_continuousMap_mul (f : C(ComplexMatrix2.specialUnitary, ℂ))
    {φ : ComplexMatrix2.specialUnitary → ℂ} (hφ : Integrable φ haarProb) :
    Integrable (fun x => f x * φ x) haarProb :=
  hφ.bdd_mul (c := ‖f‖) f.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x)
theorem integrable_of_memL2 (φ : Lp ℂ 2 haarProb) : Integrable φ haarProb :=
  (Lp.memLp φ).integrable one_le_two
theorem integrable_continuousMap (f : C(ComplexMatrix2.specialUnitary, ℂ)) :
    Integrable f haarProb :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
def coeffIntegral (l : HalfNatural) (φ : ComplexMatrix2.specialUnitary → ℂ)
    (q : Fin (l.doubled + 1) × Fin (l.doubled + 1)) : ℂ :=
  ∫ x, star (spinCoeff l q.1 q.2 x) * φ x ∂haarProb
theorem integrable_star_spinCoeff_mul (i k : Fin (l.doubled + 1))
    {φ : ComplexMatrix2.specialUnitary → ℂ} (hφ : Integrable φ haarProb) :
    Integrable (fun x => star (spinCoeff l i k x) * φ x) haarProb :=
  integrable_continuousMap_mul (star (spinCoeffMap l i k)) hφ
theorem inner_scaledCoeffL2 (l : HalfNatural)
    (q : Fin (l.doubled + 1) × Fin (l.doubled + 1)) (φ : Lp ℂ 2 haarProb) :
    inner ℂ (scaledCoeffL2 l q) φ =
      ((Real.sqrt (2 * l.toReal + 1) : ℝ) : ℂ) * coeffIntegral l φ q := by
  rw [scaledCoeffL2, inner_smul_left, L2.inner_def, Complex.conj_ofReal]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := haarProb) (𝕜 := ℂ)
    (spinCoeffMap l q.1 q.2)] with x hx
  rw [hx, RCLike.inner_apply']
  rfl
theorem coeffProjection_eq_sum (hPW : PeterWeylFacts l l) (φ : Lp ℂ 2 haarProb) :
    coeffProjection l φ =
      ∑ q, inner ℂ (scaledCoeffL2 l q) φ • scaledCoeffL2 l q := by
  have hortho := hPW.orthonormal_scaledCoeffL2
  have hin : ∀ q, scaledCoeffL2 l q ∈ coeffSpanL2 l := fun q => by
    rw [← hPW.span_scaledCoeffL2]
    exact Submodule.subset_span ⟨q, rfl⟩
  unfold coeffProjection
  refine Submodule.eq_starProjection_of_mem_orthogonal
    (Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (hin q)) ?_
  rw [Submodule.mem_orthogonal]
  intro v hv
  rw [← hPW.span_scaledCoeffL2] at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨r, rfl⟩ := hw
    rw [inner_sub_right, hortho.inner_right_fintype, sub_self]
  | zero => simp
  | add w w' _ _ hw hw' => rw [inner_add_left, hw, hw', add_zero]
  | smul z w _ hw => rw [inner_smul_left, hw, mul_zero]
def projectedFun (l : HalfNatural) (φ : ComplexMatrix2.specialUnitary → ℂ) :
    C(ComplexMatrix2.specialUnitary, ℂ) :=
  ((2 * l.toReal + 1 : ℝ) : ℂ) • ∑ q, coeffIntegral l φ q • spinCoeffMap l q.1 q.2
theorem projectedFun_apply (l : HalfNatural) (φ : ComplexMatrix2.specialUnitary → ℂ)
    (x : ComplexMatrix2.specialUnitary) :
    projectedFun l φ x =
      ((2 * l.toReal + 1 : ℝ) : ℂ) *
        ∑ q, coeffIntegral l φ q * spinCoeff l q.1 q.2 x := by
  simp [projectedFun, spinCoeffMap]
theorem two_mul_toReal_add_one_pos (l : HalfNatural) : 0 < 2 * l.toReal + 1 := by apply _root_.YangMills.Construction.SpinHarmonics.PeterWeylOrthogonality.two_mul_toReal_add_one_pos <;> assumption
theorem coeffProjection_eq_toLp (hPW : PeterWeylFacts l l) (φ : Lp ℂ 2 haarProb) :
    coeffProjection l φ = ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ (projectedFun l φ) := by
  have hsq : ((Real.sqrt (2 * l.toReal + 1) : ℝ) : ℂ) * ((Real.sqrt (2 * l.toReal + 1) : ℝ) : ℂ) =
      ((2 * l.toReal + 1 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (two_mul_toReal_add_one_pos l).le]
  rw [coeffProjection_eq_sum hPW, projectedFun, map_smul, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [inner_scaledCoeffL2, map_smul, scaledCoeffL2, smul_smul, smul_smul]
  congr 1
  linear_combination coeffIntegral l φ q * hsq
theorem integral_kernel_eq_projectedFun (hRep : SpinRepFacts l l)
    {φ : ComplexMatrix2.specialUnitary → ℂ} (hφ : Integrable φ haarProb)
    (x : ComplexMatrix2.specialUnitary) :
    ∫ y, ((2 * l.toReal + 1 : ℝ) : ℂ) * spinCharacter l (x * y⁻¹) * φ y ∂haarProb =
      projectedFun l φ x := by
  have hpt : ∀ y : ComplexMatrix2.specialUnitary,
      ((2 * l.toReal + 1 : ℝ) : ℂ) * spinCharacter l (x * y⁻¹) * φ y =
      ∑ q : Fin (l.doubled + 1) × Fin (l.doubled + 1),
        (((2 * l.toReal + 1 : ℝ) : ℂ) * spinCoeff l q.1 q.2 x) *
          (star (spinCoeff l q.1 q.2 y) * φ y) := by
    intro y
    rw [spinCharacter_mul_inv hRep, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun q _ => (integrable_star_spinCoeff_mul q.1 q.2 hφ).const_mul _]
  simp_rw [integral_const_mul]
  rw [projectedFun_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [coeffIntegral]
  ring
theorem measurePreserving_mul_mul
    (hInv : ∀ A B : ComplexMatrix2.specialUnitary,
      Measure.map (fun V : ComplexMatrix2.specialUnitary => A * V * B) haarProb = haarProb)
    (u u' : ComplexMatrix2.specialUnitary) :
    MeasurePreserving (fun x : ComplexMatrix2.specialUnitary => u * x * u') haarProb haarProb :=
  ⟨(continuous_const.mul continuous_id |>.mul continuous_const).measurable, hInv u u'⟩
theorem measurableEmbedding_mul_mul (u u' : ComplexMatrix2.specialUnitary) :
    MeasurableEmbedding (fun x : ComplexMatrix2.specialUnitary => u * x * u') :=
  ((Homeomorph.mulLeft u).trans (Homeomorph.mulRight u')).measurableEmbedding
theorem projectedFun_translate (hRep : SpinRepFacts l l) (hChi : SpinCharacterFacts l)
    (hInv : ∀ A B : ComplexMatrix2.specialUnitary,
      Measure.map (fun V : ComplexMatrix2.specialUnitary => A * V * B) haarProb = haarProb)
    (u u' : ComplexMatrix2.specialUnitary)
    {G G' : ComplexMatrix2.specialUnitary → ℂ} (hGi : Integrable G haarProb)
    (hG'i : Integrable G' haarProb)
    (hG : G' =ᵐ[haarProb] fun x => G (u * x * u')) (x : ComplexMatrix2.specialUnitary) :
    projectedFun l G' x = projectedFun l G (u * x * u') := by
  have hcomp := (measurePreserving_mul_mul hInv u u').integral_comp
    (measurableEmbedding_mul_mul u u') (fun z =>
      ((2 * l.toReal + 1 : ℝ) : ℂ) * spinCharacter l (u * x * u' * z⁻¹) * G z)
  rw [← integral_kernel_eq_projectedFun hRep hG'i, ← integral_kernel_eq_projectedFun hRep hGi,
    ← hcomp]
  refine integral_congr_ae ?_
  filter_upwards [hG] with y hy
  have hy' : G' y = G (u * y * u') := hy
  have hgrp : u * x * u' * (u * y * u')⁻¹ = u * (x * y⁻¹) * u⁻¹ := by group
  rw [hy', hgrp, hChi.isConjInvariant]
theorem coeffIntegral_conj (hRep : SpinRepFacts l l)
    (hInv : ∀ A B : ComplexMatrix2.specialUnitary,
      Measure.map (fun V : ComplexMatrix2.specialUnitary => A * V * B) haarProb = haarProb)
    {G : ComplexMatrix2.specialUnitary → ℂ} (hG : IsConjInvariant G) (hGi : Integrable G haarProb)
    (i k : Fin (l.doubled + 1)) (u : ComplexMatrix2.specialUnitary) :
    coeffIntegral l G (i, k) =
      ∑ n, ∑ j, (star (spinCoeff l i j u) * spinCoeff l k n u) *
        coeffIntegral l G (j, n) := by
  have hpt : ∀ x : ComplexMatrix2.specialUnitary,
      star (spinCoeff l i k (u * x * u⁻¹)) * G (u * x * u⁻¹) =
      ∑ n, ∑ j, (star (spinCoeff l i j u) * spinCoeff l k n u) *
        (star (spinCoeff l j n x) * G x) := by
    intro x
    rw [hG x u, spinCoeff_mul hRep, star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [spinCoeff_mul hRep, hRep.spinCoeff_inv, star_mul', star_star, star_sum,
      Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul']
    ring
  have hcomp := (measurePreserving_mul_mul hInv u u⁻¹).integral_comp
    (measurableEmbedding_mul_mul u u⁻¹) (fun x => star (spinCoeff l i k x) * G x)
  have hdef : coeffIntegral l G (i, k) = ∫ x, star (spinCoeff l i k x) * G x ∂haarProb :=
    rfl
  rw [hdef, ← hcomp]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun j _ =>
    (integrable_star_spinCoeff_mul j n hGi).const_mul _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_finsetSum _ fun j _ => (integrable_star_spinCoeff_mul j n hGi).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  rfl
theorem coeffIntegral_of_isConjInvariant (hRep : SpinRepFacts l l)
    (hPW : PeterWeylFacts l l)
    (hInv : ∀ A B : ComplexMatrix2.specialUnitary,
      Measure.map (fun V : ComplexMatrix2.specialUnitary => A * V * B) haarProb = haarProb)
    {G : ComplexMatrix2.specialUnitary → ℂ} (hG : IsConjInvariant G) (hGi : Integrable G haarProb)
    (i k : Fin (l.doubled + 1)) :
    coeffIntegral l G (i, k) =
      if i = k then (∑ j, coeffIntegral l G (j, j)) / ((2 * l.toReal + 1 : ℝ) : ℂ) else 0 := by
  have hint : ∀ j n : Fin (l.doubled + 1), Integrable
      (fun u => star (spinCoeff l i j u) * spinCoeff l k n u) haarProb := fun j n =>
    integrable_star_spinCoeff_mul i j (integrable_continuousMap (spinCoeffMap l k n))
  have havg : coeffIntegral l G (i, k) =
      ∫ u, ∑ n, ∑ j, (star (spinCoeff l i j u) * spinCoeff l k n u) *
        coeffIntegral l G (j, n) ∂haarProb := by
    simp_rw [← coeffIntegral_conj hRep hInv hG hGi i k]
    simp
  rw [havg, integral_finsetSum _ fun n _ => integrable_finsetSum _ fun j _ =>
    (hint j n).mul_const _]
  have hin : ∀ n : Fin (l.doubled + 1),
      ∫ u, ∑ j : Fin (l.doubled + 1),
        (star (spinCoeff l i j u) * spinCoeff l k n u) *
          coeffIntegral l G (j, n) ∂haarProb =
      ∑ j : Fin (l.doubled + 1), (if l = l ∧ (i : ℕ) = k ∧ (j : ℕ) = n then 1 else 0) /
        ((2 * l.toReal + 1 : ℝ) : ℂ) * coeffIntegral l G (j, n) := by
    intro n
    rw [integral_finsetSum _ fun j _ => (hint j n).mul_const _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const, hPW.integral_star_spinCoeff_mul]
  simp_rw [hin]
  by_cases hik : i = k
  · subst hik
    simp only [true_and, if_true, Fin.val_inj]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_eq_single n]
    · simp
      ring
    · intro j _ hj
      simp [hj]
    · simp
  · have hik' : ¬ (i : ℕ) = k := fun e => hik (Fin.ext e)
    simp [hik, hik']
theorem projectedFun_of_isConjInvariant (hRep : SpinRepFacts l l)
    (hPW : PeterWeylFacts l l)
    (hInv : ∀ A B : ComplexMatrix2.specialUnitary,
      Measure.map (fun V : ComplexMatrix2.specialUnitary => A * V * B) haarProb = haarProb)
    {G : ComplexMatrix2.specialUnitary → ℂ} (hG : IsConjInvariant G) (hGi : Integrable G haarProb) :
    projectedFun l G = (∫ x, star (spinCharacter l x) * G x ∂haarProb) • spinCharacter l := by
  have hne : ((2 * l.toReal + 1 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (two_mul_toReal_add_one_pos l).ne'
  have htr : ∫ x, star (spinCharacter l x) * G x ∂haarProb = ∑ j, coeffIntegral l G (j, j) := by
    have hpt : ∀ x, star (spinCharacter l x) * G x =
        ∑ j, star (spinCoeff l j j x) * G x := by
      intro x
      rw [spinCharacter_eq_sum_spinCoeff, star_sum, Finset.sum_mul]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun j _ => integrable_star_spinCoeff_mul j j hGi]
    rfl
  have hrow : ∀ i, ∑ k, coeffIntegral l G (i, k) • spinCoeffMap l i k =
      ((∑ j, coeffIntegral l G (j, j)) / ((2 * l.toReal + 1 : ℝ) : ℂ)) •
        spinCoeffMap l i i := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [coeffIntegral_of_isConjInvariant hRep hPW hInv hG hGi i i, if_pos rfl]
    · intro k _ hk
      rw [coeffIntegral_of_isConjInvariant hRep hPW hInv hG hGi i k, if_neg (Ne.symm hk),
        zero_smul]
    · simp
  rw [projectedFun, Fintype.sum_prod_type]
  simp only [hrow]
  rw [htr, ← Finset.smul_sum, smul_smul, mul_div_cancel₀ _ hne]
  rfl
theorem integral_spinCharacter_mul_eq {l' : HalfNatural} (hRep : SpinRepFacts l l)
    (hRep' : SpinRepFacts l' l') (hPW : PeterWeylFacts l l') (x x' : ComplexMatrix2.specialUnitary) :
    ∫ u, spinCharacter l (x * u⁻¹) * spinCharacter l' (u * x'⁻¹) ∂haarProb =
      (if l = l' then 1 else 0) * ((2 * l.toReal + 1 : ℝ) : ℂ)⁻¹ * spinCharacter l (x * x'⁻¹) := by
  have hpt : ∀ u : ComplexMatrix2.specialUnitary,
      spinCharacter l (x * u⁻¹) * spinCharacter l' (u * x'⁻¹) =
      ∑ q : Fin (l.doubled + 1) × Fin (l.doubled + 1),
        ∑ r : Fin (l'.doubled + 1) × Fin (l'.doubled + 1),
        (spinCoeff l q.1 q.2 x * star (spinCoeff l' r.1 r.2 x')) *
          (star (spinCoeff l q.1 q.2 u) * spinCoeff l' r.1 r.2 u) := by
    intro u
    rw [spinCharacter_mul_inv hRep, spinCharacter_mul_inv hRep', Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
    ring
  have hint : ∀ (q : Fin (l.doubled + 1) × Fin (l.doubled + 1))
      (r : Fin (l'.doubled + 1) × Fin (l'.doubled + 1)), Integrable
      (fun u => star (spinCoeff l q.1 q.2 u) * spinCoeff l' r.1 r.2 u) haarProb :=
    fun q r => integrable_star_spinCoeff_mul q.1 q.2
      (integrable_continuousMap (spinCoeffMap l' r.1 r.2))
  simp_rw [hpt]
  rw [integral_finsetSum _ fun q _ => integrable_finsetSum _ fun r _ =>
    (hint q r).const_mul _]
  have hin : ∀ q : Fin (l.doubled + 1) × Fin (l.doubled + 1),
      ∫ u, ∑ r : Fin (l'.doubled + 1) × Fin (l'.doubled + 1),
        (spinCoeff l q.1 q.2 x * star (spinCoeff l' r.1 r.2 x')) *
          (star (spinCoeff l q.1 q.2 u) * spinCoeff l' r.1 r.2 u) ∂haarProb =
      ∑ r : Fin (l'.doubled + 1) × Fin (l'.doubled + 1),
        (spinCoeff l q.1 q.2 x * star (spinCoeff l' r.1 r.2 x')) *
          ((if l = l' ∧ (q.1 : ℕ) = r.1 ∧ (q.2 : ℕ) = r.2 then 1 else 0) /
            ((2 * l.toReal + 1 : ℝ) : ℂ)) := by
    intro q
    rw [integral_finsetSum _ fun r _ => (hint q r).const_mul _]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [integral_const_mul, hPW.integral_star_spinCoeff_mul]
  simp_rw [hin]
  by_cases hll : l = l'
  · subst hll
    rw [spinCharacter_mul_inv hRep, if_pos rfl, one_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_eq_single q]
    · simp
      ring
    · intro r _ hr
      have : ¬ ((q.1 : ℕ) = r.1 ∧ (q.2 : ℕ) = r.2) := fun e =>
        hr (Prod.ext (Fin.ext e.1.symm) (Fin.ext e.2.symm))
      simp [this]
    · simp
  · simp [hll]
end CoeffProjections
theorem CoeffProjections.proof
    (hReps : SpinRepsUnitaryIrreducible.Statement)
    (hOrth : PeterWeylOrthogonality.Statement)
    (hChars : AllCharacterFacts)
    (hHaar : ComplexMatrix2.HaarExpChartProperties) :
    CoeffProjections.Statement := by
  intro l l'
  have hRep := hReps l l
  have hPW := hOrth l l
  have hChi := hChars l
  have hInv := hHaar.2.2.1
  refine
    { hasKernel := ?_
      kernel_eq_sum := ?_
      translate := ?_
      apply_of_isConjInvariant := ?_
      integral_spinCharacter_mul := ?_ }
  · intro φ
    rw [CoeffProjections.coeffProjection_eq_toLp hPW]
    filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := haarProb) (𝕜 := ℂ)
      (CoeffProjections.projectedFun l φ)] with x hx
    rw [hx]
    exact (CoeffProjections.integral_kernel_eq_projectedFun hRep
      (CoeffProjections.integrable_of_memL2 φ) x).symm
  · intro x x'
    rw [CoeffProjections.spinCharacter_mul_inv hRep, Fintype.sum_prod_type]
  · intro u u' G G' hG
    have hcoe : ∀ φ : Lp ℂ 2 haarProb, (coeffProjection l φ : ComplexMatrix2.specialUnitary → ℂ)
        =ᵐ[haarProb] CoeffProjections.projectedFun l φ := fun φ => by
      rw [CoeffProjections.coeffProjection_eq_toLp hPW]
      exact ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := haarProb) (𝕜 := ℂ) _
    have hcomp := (CoeffProjections.measurePreserving_mul_mul hInv u
      u').quasiMeasurePreserving.ae_eq_comp (hcoe G)
    refine (hcoe G').trans (Filter.EventuallyEq.trans ?_ hcomp.symm)
    exact Filter.Eventually.of_forall fun x =>
      CoeffProjections.projectedFun_translate hRep hChi hInv u u'
        (CoeffProjections.integrable_of_memL2 G)
        (CoeffProjections.integrable_of_memL2 G') hG x
  · intro G _ hconj hG
    have hGi : Integrable G haarProb := hG.integrable one_le_two
    have hae : (hG.toLp G : ComplexMatrix2.specialUnitary → ℂ) =ᵐ[haarProb] G := hG.coeFn_toLp
    have hsame : CoeffProjections.projectedFun l (hG.toLp G) =
        CoeffProjections.projectedFun l G := by
      have hc : ∀ q, CoeffProjections.coeffIntegral l (hG.toLp G) q =
          CoeffProjections.coeffIntegral l G q := fun q => by
        refine integral_congr_ae ?_
        filter_upwards [hae] with x hx
        rw [hx]
      simp only [CoeffProjections.projectedFun, hc]
    rw [CoeffProjections.coeffProjection_eq_toLp hPW, hsame,
      CoeffProjections.projectedFun_of_isConjInvariant hRep hPW hInv hconj hGi,
      map_smul]
  · intro x x'
    exact CoeffProjections.integral_spinCharacter_mul_eq hRep (hReps l' l') (hOrth l l') x x'
end YangMills.Construction.SpinHarmonics
