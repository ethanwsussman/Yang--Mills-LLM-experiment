import YangMills.Construction.Matrices.ClassFunctionsAsKernelsOnGProof
import YangMills.Construction.Matrices.ClebschGordanRuleOnG
import YangMills.Construction.Matrices.MultiplicationByAPolynomialOnPowersOfGProof
import YangMills.Construction.Matrices.OrthogonalityRelationsAndPeterWeylOnG
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2 MvPolynomial
open scoped Matrix.Norms.L2Operator ENNReal
noncomputable section
namespace YangMills.Construction.SpinHarmonics
namespace PeterWeylOrthogonality
instance haarProb_isMulLeftInvariant : (haarProb : Measure specialUnitary).IsMulLeftInvariant := by
  unfold haarProb
  infer_instance
theorem integrable_haarProb_of_continuous {f : specialUnitary → ℂ} (hf : Continuous f) :
    Integrable f haarProb :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
theorem homogeneousInner_monomialBasis_left (l : HalfNatural) (a : Fin (l.doubled + 1))
    (P : homogeneousSpace l) :
    homogeneousInner l (monomialBasis l a) P = monomialCoord l a P := by
  simp only [homogeneousInner, monomialCoord_monomialBasis]
  simp
theorem ext_monomialCoord (l : HalfNatural) {P Q : homogeneousSpace l}
    (h : ∀ a, monomialCoord l a P = monomialCoord l a Q) : P = Q := by apply _root_.YangMills.Construction.SpinHarmonics.ConjInvariantKernels.eq_of_monomialCoord_eq <;> assumption
theorem monomialCoord_spinRep (l : HalfNatural) (a : Fin (l.doubled + 1)) (g : specialUnitary)
    (P : homogeneousSpace l) :
    monomialCoord l a (spinRep l g P) =
      ∑ b, spinCoeff l a b g * monomialCoord l b P := by
  conv_lhs => rw [← sum_monomialCoord_smul_monomialBasis l P]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [spinCoeff, homogeneousInner_monomialBasis_left, mul_comm]
theorem spinCoeff_mul (hR : SpinRepsUnitaryIrreducible.Statement)
    (l : HalfNatural) (a c : Fin (l.doubled + 1)) (g h : specialUnitary) :
    spinCoeff l a c (g * h) =
      ∑ b, spinCoeff l a b g * spinCoeff l b c h := by
  rw [spinCoeff, homogeneousInner_monomialBasis_left, (hR l l).spinRep_mul, LinearMap.comp_apply,
    monomialCoord_spinRep]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [spinCoeff.eq_1 l b c h, homogeneousInner_monomialBasis_left]
theorem spinCoeff_one (hR : SpinRepsUnitaryIrreducible.Statement)
    (l : HalfNatural) (a c : Fin (l.doubled + 1)) :
    spinCoeff l a c 1 = if a = c then 1 else 0 := by
  rw [spinCoeff, (hR l l).spinRep_one, LinearMap.id_apply,
    homogeneousInner_monomialBasis]
theorem star_spinCoeff (hR : SpinRepsUnitaryIrreducible.Statement)
    (l : HalfNatural) (a c : Fin (l.doubled + 1)) (g : specialUnitary) :
    star (spinCoeff l a c g) = spinCoeff l c a g⁻¹ :=
  ((hR l l).spinCoeff_inv g c a).symm
def haarCrossEntry (l l' : HalfNatural) (c : Fin (l.doubled + 1)) (c' : Fin (l'.doubled + 1))
    (x : Fin (l'.doubled + 1)) (a : Fin (l.doubled + 1)) : ℂ :=
  ∫ g, spinCoeff l' x c' g * star (spinCoeff l a c g) ∂haarProb
theorem continuous_spinCoeff_mul_star (l l' : HalfNatural) (c a : Fin (l.doubled + 1))
    (c' x : Fin (l'.doubled + 1)) :
    Continuous fun g => spinCoeff l' x c' g * star (spinCoeff l a c g) :=
  (continuous_spinCoeff l' x c').mul (continuous_star.comp (continuous_spinCoeff l a c))
theorem haarCrossEntry_intertwines (hR : SpinRepsUnitaryIrreducible.Statement)
    (l l' : HalfNatural) (c : Fin (l.doubled + 1)) (c' : Fin (l'.doubled + 1)) (h : specialUnitary)
    (x : Fin (l'.doubled + 1)) (b : Fin (l.doubled + 1)) :
    ∑ y, spinCoeff l' x y h * haarCrossEntry l l' c c' y b =
      ∑ a, haarCrossEntry l l' c c' x a * spinCoeff l a b h := by
  have h₁ : ∑ y, spinCoeff l' x y h * haarCrossEntry l l' c c' y b =
      ∫ g, spinCoeff l' x c' (h * g) * star (spinCoeff l b c g) ∂haarProb := by
    simp only [haarCrossEntry, ← integral_const_mul]
    rw [← integral_finsetSum]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only [spinCoeff_mul hR, Finset.sum_mul, mul_assoc]
    · exact fun y _ => integrable_haarProb_of_continuous
        (continuous_const.mul (continuous_spinCoeff_mul_star l l' c b c' y))
  have h₂ : ∫ g, spinCoeff l' x c' (h * g) * star (spinCoeff l b c g) ∂haarProb =
      ∫ g, spinCoeff l' x c' g * star (spinCoeff l b c (h⁻¹ * g)) ∂haarProb := by
    rw [← integral_mul_left_eq_self
      (fun g => spinCoeff l' x c' g * star (spinCoeff l b c (h⁻¹ * g))) h]
    simp
  have h₃ : ∑ a, haarCrossEntry l l' c c' x a * spinCoeff l a b h =
      ∫ g, spinCoeff l' x c' g * star (spinCoeff l b c (h⁻¹ * g)) ∂haarProb := by
    simp only [haarCrossEntry, ← integral_mul_const]
    rw [← integral_finsetSum]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only [spinCoeff_mul hR, star_sum, star_mul', Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [star_spinCoeff hR l b a h⁻¹, inv_inv]
      ring
    · exact fun a _ => integrable_haarProb_of_continuous
        ((continuous_spinCoeff_mul_star l l' c a c' x).mul continuous_const)
  rw [h₁, h₂, h₃]
def haarCrossMap (l l' : HalfNatural) (c : Fin (l.doubled + 1)) (c' : Fin (l'.doubled + 1)) :
    homogeneousSpace l →ₗ[ℂ] homogeneousSpace l' :=
  ∑ x, ∑ a, haarCrossEntry l l' c c' x a • (monomialCoord l a).smulRight (monomialBasis l' x)
theorem monomialCoord_haarCrossMap (l l' : HalfNatural) (c : Fin (l.doubled + 1))
    (c' x : Fin (l'.doubled + 1)) (P : homogeneousSpace l) :
    monomialCoord l' x (haarCrossMap l l' c c' P) =
      ∑ a, haarCrossEntry l l' c c' x a * monomialCoord l a P := by
  simp only [haarCrossMap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    map_sum, map_smul, monomialCoord_monomialBasis, smul_eq_mul]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp
theorem haarCrossMap_intertwines (hR : SpinRepsUnitaryIrreducible.Statement)
    (l l' : HalfNatural) (c : Fin (l.doubled + 1)) (c' : Fin (l'.doubled + 1)) (g : specialUnitary) :
    haarCrossMap l l' c c' ∘ₗ spinRep l g = spinRep l' g ∘ₗ haarCrossMap l l' c c' := by
  ext1 P
  apply ext_monomialCoord
  intro x
  simp only [LinearMap.comp_apply, monomialCoord_haarCrossMap, monomialCoord_spinRep]
  calc ∑ a, haarCrossEntry l l' c c' x a * ∑ b, spinCoeff l a b g * monomialCoord l b P
      = ∑ b, (∑ a, haarCrossEntry l l' c c' x a * spinCoeff l a b g) * monomialCoord l b P := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        simp only [mul_assoc]
    _ = ∑ b, (∑ y, spinCoeff l' x y g * haarCrossEntry l l' c c' y b) * monomialCoord l b P := by
        simp only [haarCrossEntry_intertwines hR]
    _ = ∑ y, spinCoeff l' x y g * ∑ a, haarCrossEntry l l' c c' y a * monomialCoord l a P := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        simp only [mul_assoc]
theorem monomialCoord_haarCrossMap_monomialBasis (l l' : HalfNatural) (c : Fin (l.doubled + 1))
    (c' x : Fin (l'.doubled + 1)) (a : Fin (l.doubled + 1)) :
    monomialCoord l' x (haarCrossMap l l' c c' (monomialBasis l a)) = haarCrossEntry l l' c c' x a := by
  simp [monomialCoord_haarCrossMap, monomialCoord_monomialBasis]
theorem haarCrossEntry_of_ne (hR : SpinRepsUnitaryIrreducible.Statement)
    {l l' : HalfNatural} (h : l ≠ l') (c : Fin (l.doubled + 1)) (c' x : Fin (l'.doubled + 1))
    (a : Fin (l.doubled + 1)) : haarCrossEntry l l' c c' x a = 0 := by
  rw [← monomialCoord_haarCrossMap_monomialBasis,
    (hR l l').eq_zero_of_intertwines h _ (haarCrossMap_intertwines hR l l' c c')]
  simp
theorem ofReal_two_mul_toReal_add_one (l : HalfNatural) :
    ((2 * l.toReal + 1 : ℝ) : ℂ) = ((l.doubled + 1 : ℕ) : ℂ) := by
  simp only [HalfNatural.toReal]
  push_cast
  ring
theorem sum_haarCrossEntry_diag (hR : SpinRepsUnitaryIrreducible.Statement)
    (l : HalfNatural) (c c' : Fin (l.doubled + 1)) :
    ∑ a, haarCrossEntry l l c c' a a = if c = c' then 1 else 0 := by
  simp only [haarCrossEntry]
  rw [← integral_finsetSum _ fun a _ =>
    integrable_haarProb_of_continuous (continuous_spinCoeff_mul_star l l c a c' a)]
  have h : ∀ g, ∑ a, spinCoeff l a c' g * star (spinCoeff l a c g) =
      if c = c' then 1 else 0 := by
    intro g
    have h₁ := spinCoeff_mul hR l c c' g⁻¹ g
    rw [inv_mul_cancel, spinCoeff_one hR] at h₁
    rw [h₁]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [star_spinCoeff hR, mul_comm]
  simp only [h]
  simp
theorem haarCrossEntry_same (hR : SpinRepsUnitaryIrreducible.Statement)
    (l : HalfNatural) (c c' x a : Fin (l.doubled + 1)) :
    haarCrossEntry l l c c' x a =
      (if x = a ∧ c = c' then 1 else 0) / ((l.doubled + 1 : ℕ) : ℂ) := by
  obtain ⟨μ, hμ⟩ := (hR l l).eq_smul_id_of_commute _ (haarCrossMap_intertwines hR l l c c')
  have hT : ∀ x a, haarCrossEntry l l c c' x a = μ * if x = a then 1 else 0 := by
    intro x a
    rw [← monomialCoord_haarCrossMap_monomialBasis, hμ]
    simp [monomialCoord_monomialBasis]
  have hn : ((l.doubled + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  have htr := sum_haarCrossEntry_diag hR l c c'
  simp only [hT, if_true, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at htr
  rw [hT, eq_div_iff hn]
  by_cases hx : x = a
  · simp only [hx, if_true, true_and, mul_one]
    rw [mul_comm, htr]
  · simp [hx]
theorem integral_star_spinCoeff_mul_spinCoeff (hR : SpinRepsUnitaryIrreducible.Statement)
    (l l' : HalfNatural) (a c : Fin (l.doubled + 1)) (a' c' : Fin (l'.doubled + 1)) :
    ∫ g, star (spinCoeff l a c g) * spinCoeff l' a' c' g ∂haarProb =
      (if l = l' ∧ (a : ℕ) = a' ∧ (c : ℕ) = c' then 1 else 0) / ((2 * l.toReal + 1 : ℝ) : ℂ) := by
  have h : ∫ g, star (spinCoeff l a c g) * spinCoeff l' a' c' g ∂haarProb =
      haarCrossEntry l l' c c' a' a := by
    simp only [haarCrossEntry, mul_comm]
  rw [h]
  by_cases hl : l = l'
  · subst hl
    rw [haarCrossEntry_same hR, ofReal_two_mul_toReal_add_one]
    congr 1
    refine if_congr ⟨?_, ?_⟩ rfl rfl
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨-, h₁, h₂⟩
      exact ⟨(Fin.ext h₁).symm, Fin.ext h₂⟩
  · rw [haarCrossEntry_of_ne hR hl, if_neg fun h => hl h.1]
    simp
theorem inner_scaledCoeffL2 (l l' : HalfNatural) (p : Fin (l.doubled + 1) × Fin (l.doubled + 1))
    (q : Fin (l'.doubled + 1) × Fin (l'.doubled + 1)) :
    inner ℂ (scaledCoeffL2 l p) (scaledCoeffL2 l' q) =
      ((Real.sqrt (2 * l.toReal + 1) * Real.sqrt (2 * l'.toReal + 1) : ℝ) : ℂ) *
        ∫ g, star (spinCoeff l p.1 p.2 g) * spinCoeff l' q.1 q.2 g ∂haarProb := by
  rw [scaledCoeffL2, scaledCoeffL2, inner_smul_left, inner_smul_right,
    ContinuousMap.inner_toLp]
  simp [spinCoeffMap, mul_comm, mul_assoc]
theorem two_mul_toReal_add_one_pos (l : HalfNatural) : 0 < 2 * l.toReal + 1 := by
  have : 0 ≤ l.toReal := by
    simp only [HalfNatural.toReal]
    positivity
  linarith
theorem ofReal_sqrt_dim_ne_zero (l : HalfNatural) : ((Real.sqrt (2 * l.toReal + 1) : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (two_mul_toReal_add_one_pos l)).ne'
theorem orthonormal_scaledCoeffL2_family (hR : SpinRepsUnitaryIrreducible.Statement)
    (l : HalfNatural) : Orthonormal ℂ (scaledCoeffL2 l) := by
  rw [orthonormal_iff_ite]
  intro p q
  have hpos := two_mul_toReal_add_one_pos l
  have hne : ((2 * l.toReal + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  rw [inner_scaledCoeffL2, integral_star_spinCoeff_mul_spinCoeff hR, Real.mul_self_sqrt hpos.le]
  by_cases hpq : p = q
  · subst hpq
    simp only [true_and, if_true]
    field_simp
  · have h : ¬(l = l ∧ (p.1 : ℕ) = q.1 ∧ (p.2 : ℕ) = q.2) := fun h =>
      hpq (Prod.ext (Fin.ext h.2.1) (Fin.ext h.2.2))
    rw [if_neg h, if_neg hpq]
    simp
theorem inner_scaledCoeffL2_of_ne (hR : SpinRepsUnitaryIrreducible.Statement)
    {l l' : HalfNatural} (h : l ≠ l') (p : Fin (l.doubled + 1) × Fin (l.doubled + 1))
    (q : Fin (l'.doubled + 1) × Fin (l'.doubled + 1)) :
    inner ℂ (scaledCoeffL2 l p) (scaledCoeffL2 l' q) = 0 := by
  rw [inner_scaledCoeffL2, integral_star_spinCoeff_mul_spinCoeff hR, if_neg fun e => h e.1]
  simp
theorem toLp_spinCoeffMap (l : HalfNatural) (p : Fin (l.doubled + 1) × Fin (l.doubled + 1)) :
    ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ (spinCoeffMap l p.1 p.2) =
      ((Real.sqrt (2 * l.toReal + 1) : ℝ) : ℂ)⁻¹ • scaledCoeffL2 l p := by
  rw [scaledCoeffL2, smul_smul, inv_mul_cancel₀ (ofReal_sqrt_dim_ne_zero l), one_smul]
theorem span_range_scaledCoeffL2 (l : HalfNatural) :
    Submodule.span ℂ (Set.range (scaledCoeffL2 l)) = coeffSpanL2 l := by
  rw [coeffSpanL2, coeffSpan, Submodule.map_span, ← Set.range_comp]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, rfl⟩
    have := toLp_spinCoeffMap l p
    simp only [Function.comp_apply, SetLike.mem_coe]
    erw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
theorem linearIndependent_spinCoeffMap
    (hR : SpinRepsUnitaryIrreducible.Statement) (l : HalfNatural) :
    LinearIndependent ℂ (fun p : Fin (l.doubled + 1) × Fin (l.doubled + 1) =>
      spinCoeffMap l p.1 p.2) := by
  have h := (orthonormal_scaledCoeffL2_family hR l).linearIndependent.units_smul
    (fun _ : Fin (l.doubled + 1) × Fin (l.doubled + 1) =>
      Units.mk0 _ (inv_ne_zero (ofReal_sqrt_dim_ne_zero l)))
  refine LinearIndependent.of_comp (ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ).toLinearMap ?_
  have e : (⇑(ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ).toLinearMap ∘
      fun p : Fin (l.doubled + 1) × Fin (l.doubled + 1) => spinCoeffMap l p.1 p.2) =
      (fun _ : Fin (l.doubled + 1) × Fin (l.doubled + 1) =>
        Units.mk0 _ (inv_ne_zero (ofReal_sqrt_dim_ne_zero l))) • scaledCoeffL2 l :=
    _root_.funext fun p => toLp_spinCoeffMap l p
  rw [e]
  exact h
theorem finrank_coeffSpan_eq (hR : SpinRepsUnitaryIrreducible.Statement)
    (l : HalfNatural) : Module.finrank ℂ (coeffSpan l) = (l.doubled + 1) ^ 2 := by
  rw [coeffSpan, finrank_span_eq_card (linearIndependent_spinCoeffMap hR l)]
  simp [sq]
theorem coeffSpanL2_isOrtho_of_ne (hR : SpinRepsUnitaryIrreducible.Statement)
    {t t' : HalfNatural} (h : t ≠ t') :
    (coeffSpanL2 t).IsOrtho (coeffSpanL2 t') := by
  rw [← span_range_scaledCoeffL2, ← span_range_scaledCoeffL2, Submodule.isOrtho_span]
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
  exact inner_scaledCoeffL2_of_ne hR h p q
theorem isInCoeffSpan_spinCoeff (l : HalfNatural) (a c : Fin (l.doubled + 1)) :
    IsInCoeffSpan l (spinCoeff l a c) :=
  ⟨spinCoeffMap l a c, Submodule.subset_span ⟨(a, c), rfl⟩, fun _ => rfl⟩
theorem isInCoeffSpan_add {l : HalfNatural} {F H : specialUnitary → ℂ} (hF : IsInCoeffSpan l F)
    (hH : IsInCoeffSpan l H) : IsInCoeffSpan l (F + H) := by
  obtain ⟨ψ, hψ, h₁⟩ := hF
  obtain ⟨φ, hφ, h₂⟩ := hH
  exact ⟨ψ + φ, Submodule.add_mem _ hψ hφ, fun g => by simp [h₁, h₂]⟩
theorem isInCoeffSpan_smul {l : HalfNatural} {F : specialUnitary → ℂ} (c : ℂ)
    (hF : IsInCoeffSpan l F) : IsInCoeffSpan l (c • F) := by
  obtain ⟨ψ, hψ, h₁⟩ := hF
  exact ⟨c • ψ, Submodule.smul_mem _ c hψ, fun g => by simp [h₁]⟩
theorem isInCoeffSpan_zero (l : HalfNatural) : IsInCoeffSpan l 0 :=
  ⟨0, Submodule.zero_mem _, fun _ => rfl⟩
theorem isInCoeffSpan_sum {l : HalfNatural} {ι : Type*} (s : Finset ι)
    (F : ι → specialUnitary → ℂ) (hF : ∀ i ∈ s, IsInCoeffSpan l (F i)) :
    IsInCoeffSpan l fun g => ∑ i ∈ s, F i g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isInCoeffSpan_zero l
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact isInCoeffSpan_add (hF i (Finset.mem_insert_self i s))
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))
theorem isInCoeffSpan_map_of_mem {l : HalfNatural} (T : C(specialUnitary, ℂ) → specialUnitary → ℂ)
    (hgen : ∀ a c, IsInCoeffSpan l (T (spinCoeffMap l a c)))
    (hzero : T 0 = 0) (hadd : ∀ f f', T (f + f') = T f + T f')
    (hsmul : ∀ (c : ℂ) f, ∃ c' : ℂ, T (c • f) = c' • T f) :
    ∀ ψ ∈ coeffSpan l, IsInCoeffSpan l (T ψ) := by
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact hgen p.1 p.2
  | zero => rw [hzero]; exact isInCoeffSpan_zero l
  | add x y _ _ hx hy => rw [hadd]; exact isInCoeffSpan_add hx hy
  | smul c x _ hx =>
    obtain ⟨c', hc⟩ := hsmul c x
    rw [hc]
    exact isInCoeffSpan_smul c' hx
theorem isInCoeffSpan_leftTranslate (hR : SpinRepsUnitaryIrreducible.Statement) (l : HalfNatural)
    (h : specialUnitary) : ∀ ψ ∈ coeffSpan l, IsInCoeffSpan l fun g => ψ (h * g) := by
  refine isInCoeffSpan_map_of_mem (fun ψ g => ψ (h * g)) ?_ rfl (fun _ _ => rfl)
    (fun c f => ⟨c, rfl⟩)
  intro a c
  have e : (fun g => spinCoeffMap l a c (h * g)) =
      fun g => ∑ b, (spinCoeff l a b h • spinCoeff l b c) g := by
    funext g
    exact spinCoeff_mul hR l a c h g
  rw [e]
  exact isInCoeffSpan_sum _ _ fun b _ =>
    isInCoeffSpan_smul _ (isInCoeffSpan_spinCoeff l b c)
theorem isInCoeffSpan_rightTranslate (hR : SpinRepsUnitaryIrreducible.Statement) (l : HalfNatural)
    (h : specialUnitary) : ∀ ψ ∈ coeffSpan l, IsInCoeffSpan l fun g => ψ (g * h) := by
  refine isInCoeffSpan_map_of_mem (fun ψ g => ψ (g * h)) ?_ rfl (fun _ _ => rfl)
    (fun c f => ⟨c, rfl⟩)
  intro a c
  have e : (fun g => spinCoeffMap l a c (g * h)) =
      fun g => ∑ b, (spinCoeff l b c h • spinCoeff l a b) g := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, mul_comm (spinCoeff l _ c h)]
    exact spinCoeff_mul hR l a c g h
  rw [e]
  exact isInCoeffSpan_sum _ _ fun b _ =>
    isInCoeffSpan_smul _ (isInCoeffSpan_spinCoeff l a b)
theorem star_aeval_of_real {σ : Type*} (p : MvPolynomial σ ℝ) (f : σ → ℂ) :
    star (aeval f p) = aeval (fun i => star (f i)) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]
theorem exists_conj_eq_conjEntries (hW : InfiniteLattice.TraceAndSingleBondWeight) :
    ∃ E : specialUnitary, ∀ g : specialUnitary, ∀ i j,
      ((E * g * E⁻¹ : specialUnitary) : Matrices.ComplexMatrix2) i j =
        star ((g : Matrices.ComplexMatrix2) i j) := by
  have hE : symplecticUnit ∈ specialUnitary := hW.1.1
  refine ⟨⟨_, hE⟩, fun g i j => ?_⟩
  have h₁ : (((⟨_, hE⟩ : specialUnitary)⁻¹ : specialUnitary) : Matrices.ComplexMatrix2) =
      symplecticUnit⁻¹ := by
    refine (Matrix.inv_eq_left_inv ?_).symm
    exact congrArg Subtype.val (inv_mul_cancel (⟨_, hE⟩ : specialUnitary))
  have h₂ := (hW.1.2 g).2.2.2.2.1
  have h₃ : ((⟨_, hE⟩ * g * (⟨_, hE⟩ : specialUnitary)⁻¹ : specialUnitary) :
      Matrices.ComplexMatrix2) = conjEntries (g : Matrices.ComplexMatrix2) := by
    rw [h₂, Submonoid.coe_mul, Submonoid.coe_mul, h₁]
  rw [h₃]
  simp [conjEntries]
theorem isInCoeffSpan_star_spinCoeff (hR : SpinRepsUnitaryIrreducible.Statement)
    (hW : InfiniteLattice.TraceAndSingleBondWeight) (l : HalfNatural)
    (a c : Fin (l.doubled + 1)) :
    IsInCoeffSpan l fun g => star (spinCoeff l a c g) := by
  obtain ⟨E, hE⟩ := exists_conj_eq_conjEntries hW
  obtain ⟨p, -, hp⟩ := (hR l l).spinCoeff_isHomogeneous a c
  have e : (fun g => star (spinCoeff l a c g)) =
      fun g => spinCoeffMap l a c (E * g * E⁻¹) := by
    funext g
    change _ = spinCoeff l a c (E * g * E⁻¹)
    rw [hp, hp, star_aeval_of_real]
    congr 2
    funext q
    exact (hE g q.1 q.2).symm
  rw [e]
  obtain ⟨ψ, hψ, h₁⟩ := isInCoeffSpan_rightTranslate hR l E⁻¹ _
    (Submodule.subset_span ⟨(a, c), rfl⟩ : spinCoeffMap l a c ∈ coeffSpan l)
  obtain ⟨φ, hφ, h₂⟩ := isInCoeffSpan_leftTranslate hR l E ψ hψ
  exact ⟨φ, hφ, fun g => (h₂ g).trans (h₁ _)⟩
theorem isInCoeffSpan_star (hR : SpinRepsUnitaryIrreducible.Statement)
    (hW : InfiniteLattice.TraceAndSingleBondWeight) (l : HalfNatural) :
    ∀ ψ ∈ coeffSpan l, IsInCoeffSpan l fun g => star (ψ g) := by
  refine isInCoeffSpan_map_of_mem (fun ψ g => star (ψ g)) ?_ ?_ ?_ ?_
  · exact fun a c => isInCoeffSpan_star_spinCoeff hR hW l a c
  · funext g
    simp
  · intro f f'
    funext g
    simp
  · intro c f
    refine ⟨star c, ?_⟩
    funext g
    simp
theorem isInCoeffSpan_comp_inv (hR : SpinRepsUnitaryIrreducible.Statement)
    (hW : InfiniteLattice.TraceAndSingleBondWeight) (l : HalfNatural) :
    ∀ ψ ∈ coeffSpan l, IsInCoeffSpan l fun g => ψ g⁻¹ := by
  refine isInCoeffSpan_map_of_mem (fun ψ g => ψ g⁻¹) ?_ rfl (fun _ _ => rfl)
    (fun c f => ⟨c, rfl⟩)
  intro a c
  have e : (fun g => spinCoeffMap l a c g⁻¹) =
      fun g => star (spinCoeff l c a g) := by
    funext g
    exact (hR l l).spinCoeff_inv g a c
  rw [e]
  exact isInCoeffSpan_star_spinCoeff hR hW l c a
theorem isPolyInEntries_add {F H : specialUnitary → ℂ} (hF : IsPolyInEntries F)
    (hH : IsPolyInEntries H) : IsPolyInEntries (F + H) := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hH
  exact ⟨p + q, fun g => by simp [hp, hq]⟩
theorem isPolyInEntries_mul {F H : specialUnitary → ℂ} (hF : IsPolyInEntries F)
    (hH : IsPolyInEntries H) : IsPolyInEntries (F * H) := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hH
  exact ⟨p * q, fun g => by simp [hp, hq]⟩
theorem isPolyInEntries_const (c : ℂ) : IsPolyInEntries fun _ => c :=
  ⟨C c, fun g => by simp⟩
theorem isPolyInEntries_of_mem_coeffSpan (hR : SpinRepsUnitaryIrreducible.Statement)
    (l : HalfNatural) : ∀ ψ ∈ coeffSpan l, IsPolyInEntries ψ := by
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨r, -, hr⟩ := (hR l l).spinCoeff_isHomogeneous p.1 p.2
    refine ⟨map (algebraMap ℝ ℂ) r, fun g => ?_⟩
    change spinCoeff l p.1 p.2 g = _
    rw [hr, aeval_def, eval_map]
  | zero => exact ⟨0, fun g => by simp⟩
  | add x y _ _ hx hy => exact isPolyInEntries_add hx hy
  | smul c x _ hx =>
    exact isPolyInEntries_mul (isPolyInEntries_const c) hx
theorem isPolyInEntries_of_mem_iSup (hR : SpinRepsUnitaryIrreducible.Statement) :
    ∀ ψ ∈ ⨆ t, coeffSpan t, IsPolyInEntries ψ := by
  intro ψ hψ
  induction hψ using Submodule.iSup_induction' with
  | mem t x hx => exact isPolyInEntries_of_mem_coeffSpan hR t x hx
  | zero => exact ⟨0, fun g => by simp⟩
  | add x y _ _ hx hy => exact isPolyInEntries_add hx hy
theorem one_mem_coeffSpan_zero :
    (1 : C(specialUnitary, ℂ)) ∈ coeffSpan ⟨0⟩ := by apply _root_.YangMills.Construction.SpinHarmonics.PolyMulShift.one_mem_coeffSpan_zero <;> assumption
theorem coeffSpanPred_le_iSup (l : HalfNatural) :
    coeffSpanPred l ≤ ⨆ t, coeffSpan t := by
  rcases l with ⟨n⟩
  cases n with
  | zero => exact bot_le
  | succ n => exact le_iSup coeffSpan ⟨n⟩
theorem entryMap_mul_mem_iSup (hC : AllClebschGordan) (ι κ : Fin 2) :
    ∀ ψ ∈ ⨆ t, coeffSpan t, entryMap ι κ * ψ ∈ ⨆ t, coeffSpan t := by
  intro ψ hψ
  induction hψ using Submodule.iSup_induction' with
  | mem t x hx =>
    exact (sup_le (coeffSpanPred_le_iSup t) (le_iSup coeffSpan t.addHalf))
      ((hC t).entryMap_mul_mem ι κ x hx)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
theorem exists_mem_iSup_eval_eq (hC : AllClebschGordan) (p : MvPolynomial (Fin 2 × Fin 2) ℂ) :
    ∃ ψ ∈ ⨆ t, coeffSpan t, ∀ g, ψ g = eval (entryValues g) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    exact ⟨a • 1, Submodule.smul_mem _ a
      (le_iSup coeffSpan ⟨0⟩ one_mem_coeffSpan_zero), fun g => by simp⟩
  | add p q hp hq =>
    obtain ⟨ψ, hψ, h₁⟩ := hp
    obtain ⟨φ, hφ, h₂⟩ := hq
    exact ⟨ψ + φ, Submodule.add_mem _ hψ hφ, fun g => by simp [h₁, h₂]⟩
  | mul_X p i hp =>
    obtain ⟨ψ, hψ, h₁⟩ := hp
    refine ⟨entryMap i.1 i.2 * ψ, entryMap_mul_mem_iSup hC i.1 i.2 ψ hψ, fun g => ?_⟩
    simp [h₁, entryMap, entryValues, mul_comm]
theorem isPolyInEntries_iff_mem_iSup (hR : SpinRepsUnitaryIrreducible.Statement)
    (hC : AllClebschGordan) (F : specialUnitary → ℂ) :
    IsPolyInEntries F ↔ ∃ ψ ∈ ⨆ t, coeffSpan t, ∀ g, ψ g = F g := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨ψ, hψ, h⟩ := exists_mem_iSup_eval_eq hC p
    exact ⟨ψ, hψ, fun g => by rw [h, hp]⟩
  · rintro ⟨ψ, hψ, h⟩
    obtain ⟨p, hp⟩ := isPolyInEntries_of_mem_iSup hR ψ hψ
    exact ⟨p, fun g => by rw [← h, hp]⟩
theorem star_mem_iSup_coeffSpan (hR : SpinRepsUnitaryIrreducible.Statement)
    (hW : InfiniteLattice.TraceAndSingleBondWeight) :
    ∀ ψ ∈ ⨆ t, coeffSpan t, star ψ ∈ ⨆ t, coeffSpan t := by
  intro ψ hψ
  induction hψ using Submodule.iSup_induction' with
  | mem t x hx =>
    obtain ⟨φ, hφ, h⟩ := isInCoeffSpan_star hR hW t x hx
    have e : φ = star x := ContinuousMap.ext h
    rw [← e]
    exact le_iSup coeffSpan t hφ
  | zero => simp
  | add x y _ _ hx hy =>
    rw [star_add]
    exact Submodule.add_mem _ hx hy
def entryPolyAlgebra (hR : SpinRepsUnitaryIrreducible.Statement)
    (hC : AllClebschGordan)
    (hW : InfiniteLattice.TraceAndSingleBondWeight) :
    StarSubalgebra ℂ C(specialUnitary, ℂ) where
  carrier := {ψ | IsPolyInEntries ψ}
  mul_mem' := fun ha hb => isPolyInEntries_mul ha hb
  one_mem' := isPolyInEntries_const 1
  add_mem' := fun ha hb => isPolyInEntries_add ha hb
  zero_mem' := isPolyInEntries_const 0
  algebraMap_mem' := fun c => isPolyInEntries_const c
  star_mem' := by
    intro ψ hψ
    obtain ⟨φ, hφ, h⟩ := (isPolyInEntries_iff_mem_iSup hR hC ψ).mp hψ
    have e : φ = ψ := ContinuousMap.ext h
    rw [← e]
    exact isPolyInEntries_of_mem_iSup hR _ (star_mem_iSup_coeffSpan hR hW φ hφ)
theorem dense_entryPolyAlgebra (hR : SpinRepsUnitaryIrreducible.Statement)
    (hC : AllClebschGordan)
    (hW : InfiniteLattice.TraceAndSingleBondWeight) :
    Dense (entryPolyAlgebra hR hC hW : Set C(specialUnitary, ℂ)) := by
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (entryPolyAlgebra hR hC hW) (by
      intro x y hxy
      obtain ⟨i, j, hij⟩ : ∃ i j,
          (x : Matrices.ComplexMatrix2) i j ≠ (y : Matrices.ComplexMatrix2) i j := by
        by_contra hne
        push Not at hne
        exact hxy (Subtype.ext (Matrix.ext hne))
      exact ⟨_, ⟨entryMap i j,
        ⟨X (i, j), fun g => by simp [entryMap, entryValues]⟩, rfl⟩, hij⟩)
  rw [dense_iff_closure_eq, ← StarSubalgebra.topologicalClosure_coe, h]
  rfl
instance haarProb_regular : (haarProb : Measure specialUnitary).Regular := by
  unfold haarProb
  infer_instance
theorem top_le_closure_iSup_coeffSpanL2 (hR : SpinRepsUnitaryIrreducible.Statement)
    (hC : AllClebschGordan)
    (hW : InfiniteLattice.TraceAndSingleBondWeight) :
    ⊤ ≤ (⨆ t, coeffSpanL2 t).topologicalClosure := by
  have hd : DenseRange (ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ) :=
    ContinuousMap.toLp_denseRange ℂ haarProb ℂ (by simp)
  have hdense := hd.dense_image (ContinuousLinearMap.continuous _)
    (dense_entryPolyAlgebra hR hC hW)
  rw [top_le_iff, ← SetLike.coe_set_eq, Submodule.topologicalClosure_coe, Submodule.top_coe,
    ← dense_iff_closure_eq]
  refine hdense.mono ?_
  rintro _ ⟨ψ, hψ, rfl⟩
  obtain ⟨φ, hφ, h⟩ := (isPolyInEntries_iff_mem_iSup hR hC ψ).mp hψ
  have e : φ = ψ := ContinuousMap.ext h
  rw [← e]
  simp only [coeffSpanL2]
  rw [← Submodule.map_iSup]
  exact Submodule.mem_map_of_mem hφ
theorem hasSum_coeffProjection_self (hR : SpinRepsUnitaryIrreducible.Statement)
    (hC : AllClebschGordan)
    (hW : InfiniteLattice.TraceAndSingleBondWeight) (F : Lp ℂ 2 haarProb) :
    HasSum (fun t => coeffProjection t F) F := by
  have : ∀ t, CompleteSpace (coeffSpanL2 t) := fun t => FiniteDimensional.complete ℂ _
  have hortho : OrthogonalFamily ℂ (fun t => coeffSpanL2 t)
      fun t => (coeffSpanL2 t).subtypeₗᵢ := by
    intro t t' h v w
    exact (coeffSpanL2_isOrtho_of_ne hR h).inner_eq v.2 w.2
  have hV := IsHilbertSum.mkInternal _ hortho (top_le_closure_iSup_coeffSpanL2 hR hC hW)
  have hsum := hV.hasSum_linearIsometryEquiv_symm (hV.linearIsometryEquiv F)
  rw [LinearIsometryEquiv.symm_apply_apply] at hsum
  have hx : ∀ s, coeffProjection s F =
      (coeffSpanL2 s).subtypeₗᵢ (hV.linearIsometryEquiv F s) := by
    intro s
    have h₁ := hsum.mapL (coeffProjection s)
    have h₂ : ∀ t, t ≠ s → coeffProjection s
        ((coeffSpanL2 t).subtypeₗᵢ (hV.linearIsometryEquiv F t)) = 0 := by
      intro t ht
      rw [coeffProjection, Submodule.starProjection_apply_eq_zero_iff]
      exact (coeffSpanL2_isOrtho_of_ne hR ht).le (hV.linearIsometryEquiv F t).2
    have h₃ := h₁.unique (hasSum_single s h₂)
    rw [h₃, coeffProjection]
    exact Submodule.starProjection_eq_self_iff.mpr (hV.linearIsometryEquiv F s).2
  simp only [hx]
  exact hsum
end PeterWeylOrthogonality
open PeterWeylOrthogonality in
theorem PeterWeylOrthogonality.holds
    (hR : SpinRepsUnitaryIrreducible.Statement)
    (hC : AllClebschGordan)
    (hW : InfiniteLattice.TraceAndSingleBondWeight) :
    PeterWeylOrthogonality.Statement := fun l l' =>
  { integral_star_spinCoeff_mul := integral_star_spinCoeff_mul_spinCoeff hR l l'
    finrank_coeffSpan := finrank_coeffSpan_eq hR l
    orthonormal_scaledCoeffL2 := orthonormal_scaledCoeffL2_family hR l
    span_scaledCoeffL2 := span_range_scaledCoeffL2 l
    isPolyInEntries_of_mem := isPolyInEntries_of_mem_coeffSpan hR l
    isPolyInEntries_iff := isPolyInEntries_iff_mem_iSup hR hC
    leftTranslate_mem := fun ψ hψ h => isInCoeffSpan_leftTranslate hR l h ψ hψ
    rightTranslate_mem := fun ψ hψ h => isInCoeffSpan_rightTranslate hR l h ψ hψ
    star_mem := isInCoeffSpan_star hR hW l
    comp_inv_mem := isInCoeffSpan_comp_inv hR hW l
    coeffSpanL2_isOrtho := fun _ _ h => coeffSpanL2_isOrtho_of_ne hR h
    hasSum_coeffProjection := hasSum_coeffProjection_self hR hC hW }
end YangMills.Construction.SpinHarmonics
