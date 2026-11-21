import YangMills.Construction.Matrices.CharactersOfG
import YangMills.Construction.Matrices.ClassFunctionsAsKernelsOnG
import YangMills.Construction.Matrices.HaarExpChartDensity
import YangMills.Construction.Matrices.RepresentationsOfGAreUnitaryAndIrreducible
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open Matrices.ComplexMatrix2
namespace SpinHarmonics.ConjInvariantKernels
theorem integrable_haarProb_of_continuous {f : specialUnitary → ℂ} (hf : Continuous f) :
    Integrable f haarProb :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
theorem integral_comp_of_map_eq {φ : specialUnitary → specialUnitary} (hφ : Continuous φ)
    (hmap : Measure.map φ haarProb = haarProb)
    {f : specialUnitary → ℂ} (hf : Continuous f) :
    ∫ x, f (φ x) ∂haarProb = ∫ x, f x ∂haarProb := by
  have key := integral_map (μ := haarProb) hφ.measurable.aemeasurable (f := f)
    (by rw [hmap]; exact hf.aestronglyMeasurable)
  rw [hmap] at key
  exact key.symm
theorem spinCoeff_eq_monomialCoord (j : HalfNatural) (i k : Fin (j.doubled + 1))
    (u : specialUnitary) :
    spinCoeff j i k u = monomialCoord j i (spinRep j u (monomialBasis j k)) := by
  simp [spinCoeff, homogeneousInner, monomialCoord_monomialBasis]
theorem monomialCoord_spinRep (j : HalfNatural) (u : specialUnitary) (v : homogeneousSpace j)
    (i : Fin (j.doubled + 1)) :
    monomialCoord j i (spinRep j u v) =
      ∑ m, spinCoeff j i m u * monomialCoord j m v := by
  conv_lhs => rw [← sum_monomialCoord_smul_monomialBasis j v]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [spinCoeff_eq_monomialCoord, mul_comm]
theorem spinCoeff_mul (j : HalfNatural) (hRep : SpinRepFacts j j) (u v : specialUnitary)
    (i k : Fin (j.doubled + 1)) :
    spinCoeff j i k (u * v) =
      ∑ m, spinCoeff j i m u * spinCoeff j m k v := by
  rw [spinCoeff_eq_monomialCoord, hRep.spinRep_mul, LinearMap.comp_apply,
    monomialCoord_spinRep]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [spinCoeff_eq_monomialCoord j m k v]
def avgEntry (j : HalfNatural) (F : C(specialUnitary, ℂ)) (i m : Fin (j.doubled + 1)) : ℂ :=
  ∫ x, F x * spinCoeff j i m x⁻¹ ∂haarProb
theorem continuous_spinCoeff_inv (j : HalfNatural) (i m : Fin (j.doubled + 1)) :
    Continuous fun x : specialUnitary => spinCoeff j i m x⁻¹ :=
  (continuous_spinCoeff j i m).comp continuous_inv
theorem sum_avgEntry_mul (j : HalfNatural) (hRep : SpinRepFacts j j)
    (F : C(specialUnitary, ℂ)) (u : specialUnitary) (i k : Fin (j.doubled + 1)) :
    ∑ m, avgEntry j F i m * spinCoeff j m k u =
      ∫ x, F x * spinCoeff j i k (x⁻¹ * u) ∂haarProb := by
  have hx : ∀ x : specialUnitary, F x * spinCoeff j i k (x⁻¹ * u) =
      ∑ m, F x * spinCoeff j i m x⁻¹ * spinCoeff j m k u := by
    intro x
    rw [spinCoeff_mul j hRep, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => (mul_assoc _ _ _).symm
  simp only [hx]
  have hint : ∀ m ∈ Finset.univ, Integrable
      (fun x : specialUnitary => F x * spinCoeff j i m x⁻¹ * spinCoeff j m k u) haarProb :=
    fun m _ => integrable_haarProb_of_continuous
      ((F.continuous.mul (continuous_spinCoeff_inv j i m)).mul continuous_const)
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [avgEntry, integral_mul_const]
theorem sum_mul_avgEntry (j : HalfNatural) (hRep : SpinRepFacts j j)
    (F : C(specialUnitary, ℂ)) (u : specialUnitary) (i k : Fin (j.doubled + 1)) :
    ∑ m, spinCoeff j i m u * avgEntry j F m k =
      ∫ x, F x * spinCoeff j i k (u * x⁻¹) ∂haarProb := by
  have hx : ∀ x : specialUnitary, F x * spinCoeff j i k (u * x⁻¹) =
      ∑ m, spinCoeff j i m u * (F x * spinCoeff j m k x⁻¹) := by
    intro x
    rw [spinCoeff_mul j hRep, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  simp only [hx]
  have hint : ∀ m ∈ Finset.univ, Integrable
      (fun x : specialUnitary => spinCoeff j i m u * (F x * spinCoeff j m k x⁻¹)) haarProb :=
    fun m _ => integrable_haarProb_of_continuous
      (continuous_const.mul (F.continuous.mul (continuous_spinCoeff_inv j m k)))
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [avgEntry, integral_const_mul]
theorem avgEntry_commute (j : HalfNatural) (hRep : SpinRepFacts j j)
    (hHaar : ∀ s t : specialUnitary,
      Measure.map (fun w : specialUnitary => s * w * t) haarProb = haarProb)
    {F : C(specialUnitary, ℂ)} (hF : IsConjInvariant F) (u : specialUnitary)
    (i k : Fin (j.doubled + 1)) :
    ∑ m, avgEntry j F i m * spinCoeff j m k u =
      ∑ m, spinCoeff j i m u * avgEntry j F m k := by
  rw [sum_avgEntry_mul j hRep, sum_mul_avgEntry j hRep]
  have hcont : Continuous fun x : specialUnitary => F x * spinCoeff j i k (x⁻¹ * u) :=
    F.continuous.mul ((continuous_spinCoeff j i k).comp
      (continuous_inv.mul continuous_const))
  have hφ : Continuous fun w : specialUnitary => u * w * u⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  rw [← integral_comp_of_map_eq hφ (hHaar u u⁻¹) hcont]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hconj : (u * x * u⁻¹)⁻¹ * u = u * x⁻¹ := by group
  simp only [hF x u, hconj]
def avgMap (j : HalfNatural) (F : C(specialUnitary, ℂ)) :
    homogeneousSpace j →ₗ[ℂ] homogeneousSpace j :=
  ∑ i, (∑ m, avgEntry j F i m • monomialCoord j m).smulRight (monomialBasis j i)
theorem monomialCoord_avgMap (j : HalfNatural) (F : C(specialUnitary, ℂ))
    (v : homogeneousSpace j) (i : Fin (j.doubled + 1)) :
    monomialCoord j i (avgMap j F v) = ∑ m, avgEntry j F i m * monomialCoord j m v := by
  simp [avgMap, LinearMap.sum_apply, monomialCoord_monomialBasis]
theorem eq_of_monomialCoord_eq (j : HalfNatural) {v w : homogeneousSpace j}
    (h : ∀ i, monomialCoord j i v = monomialCoord j i w) : v = w := by
  rw [← sum_monomialCoord_smul_monomialBasis j v, ← sum_monomialCoord_smul_monomialBasis j w]
  simp only [h]
theorem exists_avgEntry_eq_diag (j : HalfNatural) (hRep : SpinRepFacts j j)
    (hHaar : ∀ s t : specialUnitary,
      Measure.map (fun w : specialUnitary => s * w * t) haarProb = haarProb)
    {F : C(specialUnitary, ℂ)} (hF : IsConjInvariant F) :
    ∃ μ : ℂ, ∀ i k, avgEntry j F i k = if i = k then μ else 0 := by
  have hcomm : ∀ u, avgMap j F ∘ₗ spinRep j u = spinRep j u ∘ₗ avgMap j F := by
    intro u
    refine LinearMap.ext fun v => eq_of_monomialCoord_eq j fun i => ?_
    simp only [LinearMap.comp_apply, monomialCoord_avgMap, monomialCoord_spinRep,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := congrArg (· * monomialCoord j k v) (avgEntry_commute j hRep hHaar hF u i k)
    simp only [Finset.sum_mul] at hk
    calc _ = _ := Finset.sum_congr rfl fun m _ => (mul_assoc _ _ _).symm
      _ = _ := hk
      _ = _ := Finset.sum_congr rfl fun m _ => mul_assoc _ _ _
  obtain ⟨μ, hμ⟩ := hRep.eq_smul_id_of_commute _ hcomm
  refine ⟨μ, fun i k => ?_⟩
  have hk := monomialCoord_avgMap j F (monomialBasis j k) i
  rw [hμ] at hk
  simp only [monomialCoord_monomialBasis, LinearMap.smul_apply, LinearMap.id_apply, map_smul,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at hk
  exact hk.symm
theorem sum_avgEntry_diag (j : HalfNatural) (hChar : SpinCharacterFacts j)
    (F : C(specialUnitary, ℂ)) :
    ∑ i, avgEntry j F i i = ∫ x, star (spinCharacter j x) * F x ∂haarProb := by
  simp only [avgEntry]
  have hint : ∀ i ∈ Finset.univ, Integrable
      (fun x : specialUnitary => F x * spinCoeff j i i x⁻¹) haarProb :=
    fun i _ => integrable_haarProb_of_continuous
      (F.continuous.mul (continuous_spinCoeff_inv j i i))
  rw [← integral_finsetSum _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hχ : ∀ w : specialUnitary, spinCharacter j w = ∑ i, spinCoeff j i i w := by
    intro w
    simp [spinCharacter, spinCoeffMap, ContinuousMap.coe_sum, Finset.sum_apply]
  have hstar : star (spinCharacter j x) = spinCharacter j x⁻¹ := by
    rw [hChar.apply_inv x]
    exact Complex.conj_eq_iff_im.mpr (hChar.im_eq_zero x)
  show ∑ i, F x * spinCoeff j i i x⁻¹ = star (spinCharacter j x) * F x
  rw [hstar, hχ x⁻¹, ← Finset.mul_sum, mul_comm]
theorem integral_mul_spinCoeff (j : HalfNatural) (hRep : SpinRepFacts j j)
    (hHaar : ∀ s t : specialUnitary,
      Measure.map (fun w : specialUnitary => s * w * t) haarProb = haarProb)
    (hInv : Measure.map (fun w : specialUnitary => w⁻¹) haarProb = haarProb)
    (F : C(specialUnitary, ℂ)) {μ : ℂ}
    (hμ : ∀ i k, avgEntry j F i k = if i = k then μ else 0)
    (u : specialUnitary) (i k : Fin (j.doubled + 1)) :
    ∫ y, F (u * y⁻¹) * spinCoeff j i k y ∂haarProb = μ * spinCoeff j i k u := by
  have hcont : Continuous fun x : specialUnitary => F x * spinCoeff j i k (x⁻¹ * u) :=
    F.continuous.mul ((continuous_spinCoeff j i k).comp
      (continuous_inv.mul continuous_const))
  have hφ : Continuous fun w : specialUnitary => u * w * 1 :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hsubst : ∫ x, F x * spinCoeff j i k (x⁻¹ * u) ∂haarProb =
      ∫ y, F (u * y⁻¹) * spinCoeff j i k y ∂haarProb := by
    have hleft := integral_comp_of_map_eq hφ (hHaar u 1) hcont
    have hflip := integral_comp_of_map_eq continuous_inv hInv
      (f := fun x : specialUnitary => F (u * x * 1) * spinCoeff j i k ((u * x * 1)⁻¹ * u))
      (hcont.comp hφ)
    refine hleft.symm.trans (hflip.symm.trans
      (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)))
    have hy : (u * y⁻¹)⁻¹ * u = y := by group
    show F (u * y⁻¹ * 1) * spinCoeff j i k ((u * y⁻¹ * 1)⁻¹ * u) =
      F (u * y⁻¹) * spinCoeff j i k y
    rw [mul_one, hy]
  rw [← hsubst, ← sum_avgEntry_mul j hRep]
  simp [hμ]
theorem conjInvariantKernelFormula (j : HalfNatural) (hRep : SpinRepFacts j j)
    (hChar : SpinCharacterFacts j)
    (hHaar : ∀ s t : specialUnitary,
      Measure.map (fun w : specialUnitary => s * w * t) haarProb = haarProb)
    (hInv : Measure.map (fun w : specialUnitary => w⁻¹) haarProb = haarProb) :
    ConjInvariantKernelFormula j := by
  intro F hF ψ hψ u
  obtain ⟨μ, hμ⟩ := exists_avgEntry_eq_diag j hRep hHaar hF
  have hne : ((2 * j.toReal + 1 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * j.toReal + 1 := by
      have : (0 : ℝ) ≤ j.toReal := div_nonneg (Nat.cast_nonneg _) zero_le_two
      linarith
    exact Complex.ofReal_ne_zero.mpr this.ne'
  have htrace : ((2 * j.toReal + 1 : ℝ) : ℂ) * μ =
      ∫ x, star (spinCharacter j x) * F x ∂haarProb := by
    rw [← sum_avgEntry_diag j hChar F]
    simp only [hμ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    simp only [HalfNatural.toReal]
    push_cast
    ring
  have hconst : ((2 * j.toReal + 1 : ℝ) : ℂ)⁻¹ *
      (∫ x, star (spinCharacter j x) * F x ∂haarProb) = μ := by
    rw [← htrace, inv_mul_cancel_left₀ hne]
  rw [hconst]
  have hcontF : Continuous fun y : specialUnitary => F (u * y⁻¹) :=
    F.continuous.comp (continuous_const.mul continuous_inv)
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact integral_mul_spinCoeff j hRep hHaar hInv F hμ u p.1 p.2
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [ContinuousMap.add_apply, mul_add]
    have ix : Integrable (fun w : specialUnitary => F (u * w⁻¹) * x w) haarProb :=
      integrable_haarProb_of_continuous (hcontF.mul x.continuous)
    have iy : Integrable (fun w : specialUnitary => F (u * w⁻¹) * y w) haarProb :=
      integrable_haarProb_of_continuous (hcontF.mul y.continuous)
    rw [integral_add ix iy, hx, hy]
  | smul c x _ hx =>
    have hk : ∀ w : specialUnitary, F (u * w⁻¹) * (c • x) w = c * (F (u * w⁻¹) * x w) := by
      intro w
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      ring
    simp only [hk]
    rw [integral_const_mul, hx]
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    ring
theorem allConjInvariantKernels (hRep : SpinRepsUnitaryIrreducible.Statement)
    (hChar : AllCharacterFacts) (hHaar : HaarExpChartProperties) :
    AllConjInvariantKernels := fun j =>
  conjInvariantKernelFormula j (hRep j j) (hChar j) hHaar.2.2.1 hHaar.2.2.2
end SpinHarmonics.ConjInvariantKernels
end YangMills.Construction
