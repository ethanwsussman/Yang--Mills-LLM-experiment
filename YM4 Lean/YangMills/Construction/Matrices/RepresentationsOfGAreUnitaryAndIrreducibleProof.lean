import YangMills.Construction.Matrices.CharactersOfGProof
import YangMills.Construction.Matrices.ClassFunctionsAsKernelsOnGProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Matrices MvPolynomial
namespace SpinHarmonics.SpinRepsUnitaryIrreducible
variable (l : HalfNatural)
theorem monomialCoord_apply (a : Fin (l.doubled + 1)) (P : homogeneousSpace l) :
    monomialCoord l a P =
      ((monomialNorm l a : ℝ) : ℂ) * coeff (monomialExponent l a) (P : MvPolynomial (Fin 2) ℂ) := by
  simp [monomialCoord]
theorem monomialNorm_ofReal_ne_zero (a : Fin (l.doubled + 1)) : ((monomialNorm l a : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (monomialNorm_pos l a).ne'
theorem ext_monomialCoord {P Q : homogeneousSpace l} (h : ∀ a, monomialCoord l a P = monomialCoord l a Q) :
    P = Q := by apply _root_.YangMills.Construction.SpinHarmonics.ConjInvariantKernels.eq_of_monomialCoord_eq <;> assumption
theorem monomialCoord_sum_smul (c : Fin (l.doubled + 1) → ℂ) (a : Fin (l.doubled + 1)) :
    monomialCoord l a (∑ b, c b • monomialBasis l b) = c a := by
  simp [map_sum, monomialCoord_monomialBasis]
def coordEquiv : homogeneousSpace l ≃ₗ[ℂ] (Fin (l.doubled + 1) → ℂ) where
  toFun P a := monomialCoord l a P
  map_add' P Q := by ext a; simp
  map_smul' c P := by ext a; simp
  invFun c := ∑ b, c b • monomialBasis l b
  left_inv P := sum_monomialCoord_smul_monomialBasis l P
  right_inv c := by ext a; exact monomialCoord_sum_smul l c a
theorem finrank_eq : Module.finrank ℂ (homogeneousSpace l) = l.doubled + 1 := by
  rw [(coordEquiv l).finrank_eq, Module.finrank_fin_fun]
theorem rowMul_mul (z : Fin 2 → ℂ) (A B : ComplexMatrix2) :
    rowMul z (A * B) = rowMul (rowMul z A) B := by
  funext j
  simp only [rowMul, Matrix.mul_apply, Fin.sum_univ_two]
  ring
theorem rowMul_one (z : Fin 2 → ℂ) : rowMul z (1 : ComplexMatrix2) = z := by
  funext j
  fin_cases j <;> simp [rowMul, Matrix.one_apply]
theorem spinRep_mul_eq (g h : ComplexMatrix2.specialUnitary) :
    spinRep l (g * h) = spinRep l g ∘ₗ spinRep l h := by
  refine LinearMap.ext fun P => Subtype.ext (MvPolynomial.funext fun z => ?_)
  rw [LinearMap.comp_apply, eval_spinRep, eval_spinRep, eval_spinRep,
    Submonoid.coe_mul, rowMul_mul]
theorem spinRep_one_eq : spinRep l 1 = LinearMap.id := by
  refine LinearMap.ext fun P => Subtype.ext (MvPolynomial.funext fun z => ?_)
  rw [eval_spinRep, LinearMap.id_apply, OneMemClass.coe_one, rowMul_one]
theorem coeff_linearForm_pow (a : Fin (l.doubled + 1)) (α β : ℂ) :
    coeff (monomialExponent l a) ((C α * X 0 + C β * X 1 : MvPolynomial (Fin 2) ℂ) ^ l.doubled) =
      ((l.doubled.choose a : ℕ) : ℂ) * α ^ (a : ℕ) * β ^ (l.doubled - (a : ℕ)) := by
  have hterm : ∀ m ∈ Finset.range (l.doubled + 1),
      (C α * X 0 : MvPolynomial (Fin 2) ℂ) ^ m * (C β * X 1) ^ (l.doubled - m) *
          ((l.doubled.choose m : ℕ) : MvPolynomial (Fin 2) ℂ) =
        monomial (Finsupp.single 0 m + Finsupp.single 1 (l.doubled - m))
          (α ^ m * β ^ (l.doubled - m) * ((l.doubled.choose m : ℕ) : ℂ)) := by
    intro m _
    rw [← map_natCast (C : ℂ →+* MvPolynomial (Fin 2) ℂ), mul_pow, mul_pow, ← C_pow, ← C_pow,
      X_pow_eq_monomial, X_pow_eq_monomial, C_mul_monomial, C_mul_monomial, monomial_mul,
      mul_comm _ (C _), C_mul_monomial]
    simp only [mul_one]
    congr 1
    ring
  rw [add_pow, Finset.sum_congr rfl hterm, coeff_sum, Finset.sum_eq_single (a : ℕ)]
  · have he : Finsupp.single 0 (a : ℕ) + Finsupp.single 1 (l.doubled - (a : ℕ)) =
        monomialExponent l a := rfl
    rw [coeff_monomial, if_pos he]
    ring
  · intro m hm hma
    rw [coeff_monomial, if_neg]
    intro h
    have h0 := DFunLike.congr_fun h 0
    simp [monomialExponent] at h0
    exact hma h0
  · intro h
    exact absurd (Finset.mem_range.mpr a.2) h
def conjLinearForm (w : Fin 2 → ℂ) : MvPolynomial (Fin 2) ℂ :=
  C (star (w 0)) * X 0 + C (star (w 1)) * X 1
theorem isHomogeneous_conjLinearForm (w : Fin 2 → ℂ) : (conjLinearForm w).IsHomogeneous 1 := by
  have hl : ∀ (j : Fin 2) (c : ℂ), (C c * X j : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 := by
    intro j c
    simpa using (isHomogeneous_C (Fin 2) c).mul (isHomogeneous_X ℂ j)
  exact (hl 0 _).add (hl 1 _)
def kernelVector (w : Fin 2 → ℂ) : homogeneousSpace l :=
  ⟨C (((l.doubled.factorial : ℕ) : ℂ)⁻¹) * conjLinearForm w ^ l.doubled, by
    rw [mem_homogeneousSubmodule]
    have h := ((isHomogeneous_conjLinearForm w).pow l.doubled).C_mul
      (((l.doubled.factorial : ℕ) : ℂ)⁻¹)
    simpa using h⟩
theorem eval_normalizedMonomial (w : Fin 2 → ℂ) (a : Fin (l.doubled + 1)) :
    eval w (normalizedMonomial l a) =
      ((monomialNorm l a : ℝ) : ℂ)⁻¹ * w 0 ^ (a : ℕ) * w 1 ^ (l.doubled - (a : ℕ)) := by
  simp [normalizedMonomial]
theorem monomialNorm_mul_choose (a : Fin (l.doubled + 1)) :
    ((monomialNorm l a : ℝ) : ℂ) *
        (((l.doubled.factorial : ℕ) : ℂ)⁻¹ * ((l.doubled.choose a : ℕ) : ℂ)) =
      ((monomialNorm l a : ℝ) : ℂ)⁻¹ := by
  have ha : (a : ℕ) ≤ l.doubled := Nat.lt_succ_iff.mp a.2
  have hsq : ((monomialNorm l a : ℝ) : ℂ) * ((monomialNorm l a : ℝ) : ℂ) =
      (((a : ℕ).factorial : ℕ) : ℂ) * (((l.doubled - (a : ℕ)).factorial : ℕ) : ℂ) := by
    rw [← Complex.ofReal_mul, monomialNorm, Real.mul_self_sqrt (by positivity)]
    simp
  have hf : ((l.doubled.choose a : ℕ) : ℂ) * (((a : ℕ).factorial : ℕ) : ℂ) *
      (((l.doubled - (a : ℕ)).factorial : ℕ) : ℂ) = ((l.doubled.factorial : ℕ) : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial ha
  have hn : ((l.doubled.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  have hb := monomialNorm_ofReal_ne_zero l a
  field_simp
  rw [← hf, pow_two, hsq]
  ring
theorem monomialCoord_kernelVector (w : Fin 2 → ℂ) (a : Fin (l.doubled + 1)) :
    monomialCoord l a (kernelVector l w) = star (eval w (normalizedMonomial l a)) := by
  have hb : star (((monomialNorm l a : ℝ) : ℂ)⁻¹) = ((monomialNorm l a : ℝ) : ℂ)⁻¹ := by
    simp
  rw [monomialCoord_apply, eval_normalizedMonomial, star_mul', star_mul', hb, star_pow, star_pow]
  simp only [kernelVector, conjLinearForm, coeff_C_mul, coeff_linearForm_pow]
  rw [← monomialNorm_mul_choose l a]
  ring
theorem eval_eq_sum_monomialCoord (P : homogeneousSpace l) (w : Fin 2 → ℂ) :
    eval w (P : MvPolynomial (Fin 2) ℂ) =
      ∑ a, monomialCoord l a P * eval w (normalizedMonomial l a) := by
  conv_lhs => rw [← sum_monomialCoord_smul_monomialBasis l P]
  rw [AddSubmonoidClass.coe_finsetSum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [monomialBasis]
theorem homogeneousInner_kernelVector (w : Fin 2 → ℂ) (P : homogeneousSpace l) :
    homogeneousInner l (kernelVector l w) P = eval w (P : MvPolynomial (Fin 2) ℂ) := by
  rw [eval_eq_sum_monomialCoord, homogeneousInner]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [monomialCoord_kernelVector, star_star, mul_comm]
theorem eval_kernelVector (w z : Fin 2 → ℂ) :
    eval z (kernelVector l w : MvPolynomial (Fin 2) ℂ) =
      ((l.doubled.factorial : ℕ) : ℂ)⁻¹ * (star (w 0) * z 0 + star (w 1) * z 1) ^ l.doubled := by
  simp [kernelVector, conjLinearForm]
theorem spinRep_kernelVector (g : ComplexMatrix2) (hg : g ∈ ComplexMatrix2.specialUnitary)
    (w : Fin 2 → ℂ) :
    spinRep l ⟨g, hg⟩ (kernelVector l w) = kernelVector l (rowMul w (star g)) := by
  refine Subtype.ext (MvPolynomial.funext fun z => ?_)
  rw [eval_spinRep, eval_kernelVector, eval_kernelVector]
  congr 2
  simp only [rowMul, Matrix.star_apply, star_add, star_mul', star_star]
  ring
theorem homogeneousInner_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (u : ι → homogeneousSpace l) (Q : homogeneousSpace l) :
    homogeneousInner l (∑ i ∈ s, c i • u i) Q =
      ∑ i ∈ s, star (c i) * homogeneousInner l (u i) Q := by
  simp only [homogeneousInner, map_sum, map_smul, smul_eq_mul, star_sum, star_mul', Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring
theorem homogeneousInner_map (L : homogeneousSpace l →ₗ[ℂ] homogeneousSpace l)
    (P Q : homogeneousSpace l) :
    homogeneousInner l (L P) Q =
      ∑ a, star (monomialCoord l a P) * homogeneousInner l (L (monomialBasis l a)) Q := by
  conv_lhs => rw [← sum_monomialCoord_smul_monomialBasis l P]
  simp only [map_sum, map_smul]
  exact homogeneousInner_sum_smul l _ _ _ Q
theorem star_mul_self_specialUnitary {g : ComplexMatrix2.specialUnitary} :
    star (g : ComplexMatrix2) * (g : ComplexMatrix2) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
theorem spinRep_inner (g : ComplexMatrix2.specialUnitary) (P Q : homogeneousSpace l) :
    homogeneousInner l (spinRep l g P) (spinRep l g Q) = homogeneousInner l P Q := by
  have hz : ∀ w, homogeneousInner l (spinRep l g (kernelVector l w)) (spinRep l g Q) =
      homogeneousInner l (kernelVector l w) Q := by
    intro w
    have h := spinRep_kernelVector l (g : ComplexMatrix2) g.2 w
    rw [show (⟨(g : ComplexMatrix2), g.2⟩ : ComplexMatrix2.specialUnitary) = g from rfl] at h
    rw [h, homogeneousInner_kernelVector, homogeneousInner_kernelVector, eval_spinRep, ← rowMul_mul,
      star_mul_self_specialUnitary, rowMul_one]
  have hbasis : ∀ a, homogeneousInner l (spinRep l g (monomialBasis l a)) (spinRep l g Q) =
      homogeneousInner l (monomialBasis l a) Q := by
    intro a
    have hR : ∑ b, (homogeneousInner l (spinRep l g (monomialBasis l b)) (spinRep l g Q) -
        homogeneousInner l (monomialBasis l b) Q) • monomialBasis l b = 0 := by
      refine Subtype.ext (MvPolynomial.funext fun w => ?_)
      rw [eval_eq_sum_monomialCoord]
      simp only [monomialCoord_sum_smul]
      have h1 := hz w
      rw [homogeneousInner_map l (spinRep l g) (kernelVector l w) (spinRep l g Q),
        ← LinearMap.id_apply (R := ℂ) (kernelVector l w),
        homogeneousInner_map l LinearMap.id (kernelVector l w) Q] at h1
      simp only [monomialCoord_kernelVector, star_star, LinearMap.id_apply] at h1
      simp only [sub_mul, Finset.sum_sub_distrib, ZeroMemClass.coe_zero, map_zero]
      rw [sub_eq_zero]
      simpa [mul_comm] using h1
    have h2 := congrArg (monomialCoord l a) hR
    rw [monomialCoord_sum_smul, map_zero] at h2
    exact sub_eq_zero.mp h2
  rw [homogeneousInner_map l (spinRep l g) P, ← LinearMap.id_apply (R := ℂ) P,
    homogeneousInner_map l LinearMap.id P Q]
  simp only [hbasis, LinearMap.id_apply]
theorem homogeneousInner_monomialBasis (a : Fin (l.doubled + 1)) (P : homogeneousSpace l) :
    homogeneousInner l (monomialBasis l a) P = monomialCoord l a P := by
  simp [homogeneousInner, monomialCoord_monomialBasis]
theorem spinCoeff_eq_monomialCoord (a c : Fin (l.doubled + 1)) (g : ComplexMatrix2.specialUnitary) :
    spinCoeff l a c g = monomialCoord l a (spinRep l g (monomialBasis l c)) :=
  homogeneousInner_monomialBasis l a _
theorem spinRep_inv_cancel (g : ComplexMatrix2.specialUnitary) (P : homogeneousSpace l) :
    spinRep l g (spinRep l g⁻¹ P) = P := by
  rw [← LinearMap.comp_apply, ← spinRep_mul_eq, mul_inv_cancel, spinRep_one_eq,
    LinearMap.id_apply]
theorem spinCoeff_inv_eq (g : ComplexMatrix2.specialUnitary) (a c : Fin (l.doubled + 1)) :
    spinCoeff l a c g⁻¹ = star (spinCoeff l c a g) := by
  unfold spinCoeff
  rw [← spinRep_inner l g (monomialBasis l a) (spinRep l g⁻¹ (monomialBasis l c)),
    spinRep_inv_cancel, star_homogeneousInner]
def genericColumnForm (j : Fin 2) : MvPolynomial (Fin 2) (MvPolynomial (Fin 2 × Fin 2) ℝ) :=
  C (X (0, j)) * X 0 + C (X (1, j)) * X 1
def CoeffsHomogeneous (d : ℕ)
    (A : MvPolynomial (Fin 2) (MvPolynomial (Fin 2 × Fin 2) ℝ)) : Prop :=
  ∀ m, (coeff m A).IsHomogeneous d
theorem CoeffsHomogeneous.mul {d e : ℕ}
    {A B : MvPolynomial (Fin 2) (MvPolynomial (Fin 2 × Fin 2) ℝ)}
    (hA : CoeffsHomogeneous d A) (hB : CoeffsHomogeneous e B) :
    CoeffsHomogeneous (d + e) (A * B) := fun m => by
  rw [coeff_mul]
  exact IsHomogeneous.sum _ _ _ fun x _ => (hA x.1).mul (hB x.2)
theorem coeffsHomogeneous_genericColumnForm (j : Fin 2) :
    CoeffsHomogeneous 1 (genericColumnForm j) := fun m => by
  simp only [genericColumnForm, coeff_add, coeff_C_mul, coeff_X]
  refine IsHomogeneous.add ?_ ?_ <;> split_ifs
  · rw [mul_one]; exact isHomogeneous_X _ _
  · rw [mul_zero]; exact isHomogeneous_zero _ _ _
  · rw [mul_one]; exact isHomogeneous_X _ _
  · rw [mul_zero]; exact isHomogeneous_zero _ _ _
theorem coeffsHomogeneous_genericColumnForm_pow (j : Fin 2) (k : ℕ) :
    CoeffsHomogeneous k (genericColumnForm j ^ k) := by
  induction k with
  | zero =>
    intro m
    rw [pow_zero, coeff_one]
    split_ifs
    · exact isHomogeneous_one _ _
    · exact isHomogeneous_zero _ _ _
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul (coeffsHomogeneous_genericColumnForm j)
def entryRingHom (g : ComplexMatrix2.specialUnitary) : MvPolynomial (Fin 2 × Fin 2) ℝ →+* ℂ :=
  (aeval (entryValues g) : MvPolynomial (Fin 2 × Fin 2) ℝ →ₐ[ℝ] ℂ).toRingHom
theorem map_genericColumnForm (g : ComplexMatrix2.specialUnitary) (j : Fin 2) :
    map (entryRingHom g) (genericColumnForm j) = columnForms (g : ComplexMatrix2) j := by
  simp [genericColumnForm, columnForms, entryRingHom, entryValues]
theorem coe_spinRep_monomialBasis (g : ComplexMatrix2.specialUnitary) (c : Fin (l.doubled + 1)) :
    (spinRep l g (monomialBasis l c) : MvPolynomial (Fin 2) ℂ) =
      C (((monomialNorm l c : ℝ) : ℂ)⁻¹) *
        (columnForms (g : ComplexMatrix2) 0 ^ (c : ℕ) *
          columnForms (g : ComplexMatrix2) 1 ^ (l.doubled - (c : ℕ))) := by
  show aeval (columnForms (g : ComplexMatrix2)) (normalizedMonomial l c) = _
  simp [normalizedMonomial, algebraMap_eq, mul_assoc]
theorem spinCoeff_polynomial (a c : Fin (l.doubled + 1)) :
    ∃ p : MvPolynomial (Fin 2 × Fin 2) ℝ, p.IsHomogeneous l.doubled ∧
      ∀ g, spinCoeff l a c g = aeval (entryValues g) p := by
  have hc : (c : ℕ) ≤ l.doubled := Nat.lt_succ_iff.mp c.2
  have hU := (coeffsHomogeneous_genericColumnForm_pow 0 (c : ℕ)).mul
    (coeffsHomogeneous_genericColumnForm_pow 1 (l.doubled - (c : ℕ)))
  rw [Nat.add_sub_cancel' hc] at hU
  refine ⟨C (monomialNorm l a / monomialNorm l c) *
    coeff (monomialExponent l a)
      (genericColumnForm 0 ^ (c : ℕ) * genericColumnForm 1 ^ (l.doubled - (c : ℕ))),
    (hU _).C_mul _, fun g => ?_⟩
  have hmap : columnForms (g : ComplexMatrix2) 0 ^ (c : ℕ) *
      columnForms (g : ComplexMatrix2) 1 ^ (l.doubled - (c : ℕ)) =
      map (entryRingHom g)
        (genericColumnForm 0 ^ (c : ℕ) * genericColumnForm 1 ^ (l.doubled - (c : ℕ))) := by
    rw [map_mul, map_pow, map_pow, map_genericColumnForm, map_genericColumnForm]
  rw [spinCoeff_eq_monomialCoord, monomialCoord_apply, coe_spinRep_monomialBasis, hmap,
    coeff_C_mul, coeff_map, map_mul, aeval_C]
  have he : ∀ q, entryRingHom g q = aeval (entryValues g) q := fun _ => rfl
  rw [he]
  simp only [Complex.coe_algebraMap, Complex.ofReal_div]
  ring
theorem spinRep_oneHalf_linearMonomial (g : ComplexMatrix2.specialUnitary) (κ : Fin 2) :
    spinRep HalfNatural.oneHalf g (linearMonomial κ) =
      ∑ ι, (g : ComplexMatrix2) ι κ • linearMonomial ι := by
  refine Subtype.ext (MvPolynomial.funext fun z => ?_)
  rw [eval_spinRep]
  simp [linearMonomial, rowMul, Fin.sum_univ_two, mul_comm]
theorem monomialBasis_oneHalf_zero (h : 0 < HalfNatural.oneHalf.doubled + 1) :
    monomialBasis HalfNatural.oneHalf ⟨0, h⟩ = linearMonomial 1 := by
  refine Subtype.ext ?_
  show normalizedMonomial HalfNatural.oneHalf ⟨0, h⟩ = X 1
  simp [normalizedMonomial, monomialNorm, HalfNatural.oneHalf]
theorem monomialBasis_oneHalf_one (h : 1 < HalfNatural.oneHalf.doubled + 1) :
    monomialBasis HalfNatural.oneHalf ⟨1, h⟩ = linearMonomial 0 := by
  refine Subtype.ext ?_
  show normalizedMonomial HalfNatural.oneHalf ⟨1, h⟩ = X 0
  simp [normalizedMonomial, monomialNorm, HalfNatural.oneHalf]
def oneHalfIndex (a : Fin (HalfNatural.oneHalf.doubled + 1)) : Fin 2 :=
  ⟨1 - (a : ℕ), by omega⟩
theorem spinCoeff_oneHalf (a c : Fin (HalfNatural.oneHalf.doubled + 1))
    (g : ComplexMatrix2.specialUnitary) :
    spinCoeff HalfNatural.oneHalf a c g = (g : ComplexMatrix2) (oneHalfIndex a) (oneHalfIndex c) := by
  have h0 : 0 < HalfNatural.oneHalf.doubled + 1 := Nat.succ_pos _
  have h1 : 1 < HalfNatural.oneHalf.doubled + 1 := Nat.lt_succ_self 1
  have hc : ∀ c : Fin (HalfNatural.oneHalf.doubled + 1),
      monomialBasis HalfNatural.oneHalf c = linearMonomial (oneHalfIndex c) := by
    rintro ⟨c, hc⟩
    have hc' : c < 2 := hc
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
    · exact monomialBasis_oneHalf_zero hc
    · exact monomialBasis_oneHalf_one hc
  rw [spinCoeff_eq_monomialCoord, hc, spinRep_oneHalf_linearMonomial, Fin.sum_univ_two,
    ← monomialBasis_oneHalf_one h1, ← monomialBasis_oneHalf_zero h0, map_add, map_smul, map_smul,
    monomialCoord_monomialBasis, monomialCoord_monomialBasis]
  obtain ⟨a, ha⟩ := a
  have ha' : a < 2 := ha
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
  · simp [oneHalfIndex]
  · simp [oneHalfIndex]
theorem range_spinCoeffMap_oneHalf_eq :
    Set.range (fun p : Fin (HalfNatural.oneHalf.doubled + 1) × Fin (HalfNatural.oneHalf.doubled + 1) =>
      spinCoeffMap HalfNatural.oneHalf p.1 p.2) =
    Set.range (fun p : Fin 2 × Fin 2 => entryMap p.1 p.2) := by
  have h : ∀ a c : Fin (HalfNatural.oneHalf.doubled + 1), spinCoeffMap HalfNatural.oneHalf a c =
      entryMap (oneHalfIndex a) (oneHalfIndex c) := fun a c =>
    ContinuousMap.ext fun g => spinCoeff_oneHalf a c g
  have hs : ∀ ι : Fin 2, ∃ a, oneHalfIndex a = ι := by
    intro ι
    have hι : 1 - (ι : ℕ) < HalfNatural.oneHalf.doubled + 1 :=
      lt_of_le_of_lt (Nat.sub_le 1 _) (Nat.lt_succ_self 1)
    refine ⟨⟨1 - (ι : ℕ), hι⟩, Fin.ext ?_⟩
    have := ι.2
    simp only [oneHalfIndex]
    omega
  ext F
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(oneHalfIndex p.1, oneHalfIndex p.2), (h p.1 p.2).symm⟩
  · rintro ⟨p, rfl⟩
    obtain ⟨a, ha⟩ := hs p.1
    obtain ⟨c, hc⟩ := hs p.2
    refine ⟨(a, c), ?_⟩
    show spinCoeffMap HalfNatural.oneHalf a c = entryMap p.1 p.2
    rw [h, ha, hc]
def phaseWeight (φ : ℝ) (a : Fin (l.doubled + 1)) : ℂ :=
  Complex.exp (Complex.I * φ) ^ (a : ℕ) * Complex.exp (-(Complex.I * φ)) ^ (l.doubled - (a : ℕ))
theorem spinRep_diagPhase (φ : ℝ) (a : Fin (l.doubled + 1)) :
    spinRep l (diagPhase φ) (monomialBasis l a) = phaseWeight l φ a • monomialBasis l a := by apply _root_.YangMills.Construction.SpinHarmonics.SpinCharacters.spinRep_diagPhase_monomialBasis <;> assumption
theorem monomialCoord_spinRep_diagPhase (φ : ℝ) (b : Fin (l.doubled + 1)) (P : homogeneousSpace l) :
    monomialCoord l b (spinRep l (diagPhase φ) P) =
      phaseWeight l φ b * monomialCoord l b P := by
  have h : spinRep l (diagPhase φ) P =
      ∑ c, (monomialCoord l c P * phaseWeight l φ c) • monomialBasis l c := by
    conv_lhs => rw [← sum_monomialCoord_smul_monomialBasis l P]
    simp only [map_sum, map_smul, spinRep_diagPhase, smul_smul]
  rw [h, monomialCoord_sum_smul, mul_comm]
theorem phaseWeight_injective :
    Function.Injective (phaseWeight l (Real.pi / ((l.doubled : ℝ) + 1))) := by
  intro a b hab
  set φ : ℝ := Real.pi / ((l.doubled : ℝ) + 1) with hφdef
  have hn : ((l.doubled : ℝ) + 1) ≠ 0 := by positivity
  have hφ : φ ≠ 0 := div_ne_zero Real.pi_ne_zero hn
  have hπ : (Real.pi : ℂ) = (φ : ℂ) * ((l.doubled : ℂ) + 1) := by
    have : Real.pi = φ * ((l.doubled : ℝ) + 1) := by
      rw [hφdef]
      field_simp
    rw [this]
    push_cast
    ring
  have ha : (a : ℕ) ≤ l.doubled := Nat.lt_succ_iff.mp a.2
  have hb : (b : ℕ) ≤ l.doubled := Nat.lt_succ_iff.mp b.2
  have hw : ∀ c : Fin (l.doubled + 1), phaseWeight l φ c = Complex.exp
      (((c : ℕ) : ℂ) * (Complex.I * φ) +
        ((l.doubled - (c : ℕ) : ℕ) : ℂ) * (-(Complex.I * φ))) := by
    intro c
    rw [phaseWeight, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_nat_mul]
  rw [hw, hw, Complex.exp_eq_exp_iff_exists_int] at hab
  obtain ⟨k, hk⟩ := hab
  rw [Nat.cast_sub ha, Nat.cast_sub hb] at hk
  have hne : (2 * Complex.I * (φ : ℂ)) ≠ 0 := by
    simp [hφ]
  have hz : ((a : ℕ) : ℂ) - ((b : ℕ) : ℂ) = (k : ℂ) * ((l.doubled : ℂ) + 1) := by
    refine mul_left_cancel₀ hne ?_
    linear_combination hk + (k : ℂ) * 2 * Complex.I * hπ
  have hzi : ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) = k * ((l.doubled : ℤ) + 1) := by
    exact_mod_cast hz
  have hk0 : k = 0 := by
    by_contra hk0
    rcases lt_or_gt_of_ne hk0 with h | h
    · have : k ≤ -1 := by omega
      nlinarith
    · have : 1 ≤ k := by omega
      nlinarith
  rw [hk0] at hzi
  exact Fin.ext (by omega)
def invSqrtTwo : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
theorem invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = 1 / 2 := by
  rw [invSqrtTwo, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  simp
theorem star_invSqrtTwo : star invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo]
theorem invSqrtTwo_ne_zero : invSqrtTwo ≠ 0 := by
  intro h
  have := invSqrtTwo_mul_self
  rw [h] at this
  norm_num at this
def quarterRotation : ComplexMatrix2 := !![invSqrtTwo, -invSqrtTwo; invSqrtTwo, invSqrtTwo]
theorem quarterRotation_mem_specialUnitary : quarterRotation ∈ ComplexMatrix2.specialUnitary := by
  have hs := invSqrtTwo_mul_self
  have hc : (starRingEnd ℂ) invSqrtTwo = invSqrtTwo := star_invSqrtTwo
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quarterRotation, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, hc, hs]
    all_goals norm_num
  · simp only [quarterRotation, Matrix.det_fin_two_of]
    linear_combination 2 * hs
def quarterRotationElem : ComplexMatrix2.specialUnitary :=
  ⟨quarterRotation, quarterRotation_mem_specialUnitary⟩
def topIndex : Fin (l.doubled + 1) := Fin.last l.doubled
theorem monomialCoord_spinRep_quarterRotation_ne_zero (b : Fin (l.doubled + 1)) :
    monomialCoord l b (spinRep l quarterRotationElem (monomialBasis l (topIndex l))) ≠ 0 := by
  have hb : (b : ℕ) ≤ l.doubled := Nat.lt_succ_iff.mp b.2
  have hr : columnForms ((quarterRotationElem : ComplexMatrix2.specialUnitary) : ComplexMatrix2) 0 =
      C invSqrtTwo * X 0 + C invSqrtTwo * X 1 := by
    simp [columnForms, quarterRotationElem, quarterRotation]
  rw [monomialCoord_apply, coe_spinRep_monomialBasis]
  simp only [topIndex, Fin.val_last, Nat.sub_self, pow_zero, mul_one, hr]
  rw [coeff_C_mul, coeff_linearForm_pow]
  have hc : ((l.doubled.choose (b : ℕ) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hb).ne'
  exact mul_ne_zero (monomialNorm_ofReal_ne_zero l b)
    (mul_ne_zero (inv_ne_zero (monomialNorm_ofReal_ne_zero l _))
      (mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ invSqrtTwo_ne_zero))
        (pow_ne_zero _ invSqrtTwo_ne_zero)))
theorem eq_smul_id_of_commute_spinRep (B : homogeneousSpace l →ₗ[ℂ] homogeneousSpace l)
    (h : ∀ g, B ∘ₗ spinRep l g = spinRep l g ∘ₗ B) :
    ∃ c : ℂ, B = c • LinearMap.id := by
  have hB : ∀ g P, B (spinRep l g P) = spinRep l g (B P) :=
    fun g P => LinearMap.congr_fun (h g) P
  have hoff : ∀ a b, a ≠ b → monomialCoord l b (B (monomialBasis l a)) = 0 := by
    intro a b hab
    have h1 := congrArg (monomialCoord l b)
      (hB (diagPhase (Real.pi / ((l.doubled : ℝ) + 1))) (monomialBasis l a))
    rw [spinRep_diagPhase, map_smul, map_smul, monomialCoord_spinRep_diagPhase, smul_eq_mul] at h1
    have h2 : (phaseWeight l (Real.pi / ((l.doubled : ℝ) + 1)) a -
        phaseWeight l (Real.pi / ((l.doubled : ℝ) + 1)) b) *
        monomialCoord l b (B (monomialBasis l a)) = 0 := by
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (phaseWeight_injective l (sub_eq_zero.mp h3)) hab
    · exact h3
  have hcoord : ∀ P b, monomialCoord l b (B P) =
      monomialCoord l b (B (monomialBasis l b)) * monomialCoord l b P := by
    intro P b
    conv_lhs => rw [← sum_monomialCoord_smul_monomialBasis l P]
    rw [map_sum, map_sum, Finset.sum_eq_single b]
    · rw [map_smul, map_smul, smul_eq_mul, mul_comm]
    · intro a _ hab
      rw [map_smul, map_smul, hoff a b hab, smul_zero]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  have hv := hB quarterRotationElem (monomialBasis l (topIndex l))
  have hd : B (monomialBasis l (topIndex l)) =
      monomialCoord l (topIndex l) (B (monomialBasis l (topIndex l))) •
        monomialBasis l (topIndex l) := by
    refine ext_monomialCoord l fun b => ?_
    rw [hcoord, map_smul, monomialCoord_monomialBasis, smul_eq_mul]
    by_cases hb : b = topIndex l
    · subst hb
      simp
    · simp [hb]
  have hall : ∀ b, monomialCoord l b (B (monomialBasis l b)) =
      monomialCoord l (topIndex l) (B (monomialBasis l (topIndex l))) := by
    intro b
    have h1 := congrArg (monomialCoord l b) hv
    rw [hcoord] at h1
    conv_rhs at h1 => rw [hd, map_smul, map_smul, smul_eq_mul]
    exact mul_right_cancel₀ (monomialCoord_spinRep_quarterRotation_ne_zero l b) h1
  refine ⟨monomialCoord l (topIndex l) (B (monomialBasis l (topIndex l))),
    LinearMap.ext fun P => ext_monomialCoord l fun b => ?_⟩
  rw [hcoord, hall, LinearMap.smul_apply, LinearMap.id_apply, map_smul, smul_eq_mul]
def toEuclidean : homogeneousSpace l ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (l.doubled + 1)) :=
  (coordEquiv l).trans (WithLp.linearEquiv 2 ℂ (Fin (l.doubled + 1) → ℂ)).symm
theorem inner_toEuclidean (P Q : homogeneousSpace l) :
    inner ℂ (toEuclidean l P) (toEuclidean l Q) = homogeneousInner l P Q := by
  have hc : ∀ (R : homogeneousSpace l) a, toEuclidean l R a = monomialCoord l a R :=
    fun _ _ => rfl
  simp only [PiLp.inner_apply, hc, homogeneousInner, RCLike.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]
  rfl
theorem eq_bot_or_top_of_spinRep_invariant (S : Submodule ℂ (homogeneousSpace l))
    (hS : ∀ g, ∀ P ∈ S, spinRep l g P ∈ S) : S = ⊥ ∨ S = ⊤ := by
  set T := toEuclidean l with hT
  set K : Submodule ℂ (EuclideanSpace ℂ (Fin (l.doubled + 1))) := S.map T.toLinearMap with hK
  have hmem : ∀ P, T P ∈ K ↔ P ∈ S := by
    intro P
    constructor
    · rintro ⟨Q, hQ, hQP⟩
      have : Q = P := T.injective hQP
      exact this ▸ hQ
    · exact fun hP => ⟨P, hP, rfl⟩
  have hsymm : ∀ x, T (T.symm x) = x := T.apply_symm_apply
  let U : ComplexMatrix2.specialUnitary → EuclideanSpace ℂ (Fin (l.doubled + 1)) →
      EuclideanSpace ℂ (Fin (l.doubled + 1)) :=
    fun g x => T (spinRep l g (T.symm x))
  have hUinner : ∀ g x y, inner ℂ (U g x) (U g y) = inner ℂ x y := by
    intro g x y
    have := spinRep_inner l g (T.symm x) (T.symm y)
    rw [← inner_toEuclidean, ← inner_toEuclidean, hsymm, hsymm] at this
    exact this
  have hUinv : ∀ g x, U g (U g⁻¹ x) = x := by
    intro g x
    simp only [U, T.symm_apply_apply, spinRep_inv_cancel, hsymm]
  have hUK : ∀ g, ∀ x ∈ K, U g x ∈ K := by
    intro g x hx
    rw [← hsymm x, hmem] at hx
    exact (hmem _).mpr (hS g _ hx)
  have hUKo : ∀ g, ∀ x ∈ Kᗮ, U g x ∈ Kᗮ := by
    intro g x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro y hy
    rw [← hUinv g y, hUinner]
    exact hx _ (hUK _ _ hy)
  have hUsub : ∀ g x y, U g (x - y) = U g x - U g y := by
    intro g x y
    simp only [U, map_sub]
  have hproj : ∀ g x, K.starProjection (U g x) = U g (K.starProjection x) := by
    intro g x
    refine Submodule.eq_starProjection_of_mem_orthogonal
      (hUK g _ (Submodule.starProjection_apply_mem _ _)) ?_
    rw [← hUsub]
    exact hUKo g _ (Submodule.sub_starProjection_mem_orthogonal x)
  let B : homogeneousSpace l →ₗ[ℂ] homogeneousSpace l :=
    T.symm.toLinearMap ∘ₗ K.starProjection.toLinearMap ∘ₗ T.toLinearMap
  have hBT : ∀ P, T (B P) = K.starProjection (T P) := fun P => hsymm _
  have hBcomm : ∀ g, B ∘ₗ spinRep l g = spinRep l g ∘ₗ B := by
    intro g
    refine LinearMap.ext fun P => T.injective ?_
    have h1 := hproj g (T P)
    simp only [U, T.symm_apply_apply] at h1
    show T (B (spinRep l g P)) = T (spinRep l g (B P))
    rw [hBT]
    exact h1
  obtain ⟨c, hc⟩ := eq_smul_id_of_commute_spinRep l B hBcomm
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨P, hP, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hfix : B P = P := by
    apply T.injective
    rw [hBT]
    exact Submodule.starProjection_eq_self_iff.mpr ((hmem P).mpr hP)
  have hc1 : c = 1 := by
    rw [hc, LinearMap.smul_apply, LinearMap.id_apply] at hfix
    have h0 : (c - 1) • P = c • P - (1 : ℂ) • P := sub_smul c 1 P
    have : (c - 1) • P = 0 := by rw [h0, hfix, one_smul, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hP0
  rw [eq_top_iff]
  intro Q _
  rw [← hmem]
  have : T (B Q) = T Q := by
    rw [hc, hc1]
    simp
  rw [← this, hBT]
  exact Submodule.starProjection_apply_mem _ _
theorem eq_zero_of_spinRep_intertwines (l' : HalfNatural) (hl : l ≠ l')
    (B : homogeneousSpace l →ₗ[ℂ] homogeneousSpace l')
    (h : ∀ g, B ∘ₗ spinRep l g = spinRep l' g ∘ₗ B) : B = 0 := by
  by_contra hB
  have hBg : ∀ g P, B (spinRep l g P) = spinRep l' g (B P) :=
    fun g P => LinearMap.congr_fun (h g) P
  have hker : LinearMap.ker B = ⊥ := by
    refine (eq_bot_or_top_of_spinRep_invariant l _ fun g P hP => ?_).resolve_right
      fun ht => hB ?_
    · rw [LinearMap.mem_ker] at hP ⊢
      rw [hBg, hP, map_zero]
    · exact LinearMap.ker_eq_top.mp ht
  have hrange : LinearMap.range B = ⊤ := by
    refine (eq_bot_or_top_of_spinRep_invariant l' _ fun g P hP => ?_).resolve_left
      fun hb => hB ?_
    · obtain ⟨Q, rfl⟩ := hP
      exact ⟨spinRep l g Q, hBg g Q⟩
    · exact LinearMap.range_eq_bot.mp hb
  have hfin := (LinearEquiv.ofBijective B
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hrange⟩).finrank_eq
  rw [finrank_eq, finrank_eq] at hfin
  have ht : l.doubled = l'.doubled := by omega
  apply hl
  cases l
  cases l'
  simpa using ht
theorem spinRepsUnitaryIrreducible : SpinRepsUnitaryIrreducible.Statement := fun l l' =>
  { finrank_homogeneousSpace := finrank_eq l
    spinRep_mul := spinRep_mul_eq l
    spinRep_one := spinRep_one_eq l
    spinRep_isometry := spinRep_inner l
    spinCoeff_inv := spinCoeff_inv_eq l
    spinCoeff_isHomogeneous := spinCoeff_polynomial l
    spinRep_oneHalf := spinRep_oneHalf_linearMonomial
    range_spinCoeffMap_oneHalf := range_spinCoeffMap_oneHalf_eq
    eq_smul_id_of_commute := eq_smul_id_of_commute_spinRep l
    eq_bot_or_top_of_invariant := eq_bot_or_top_of_spinRep_invariant l
    eq_zero_of_intertwines := fun hl B h => eq_zero_of_spinRep_intertwines l l' hl B h }
end SpinHarmonics.SpinRepsUnitaryIrreducible
end YangMills.Construction
