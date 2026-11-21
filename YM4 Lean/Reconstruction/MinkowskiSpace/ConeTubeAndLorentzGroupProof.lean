import YangMills.Construction.Continuum.ChosenSmoothFunctionsPartitionsOfUnityRotationsAndIntegrability
import Reconstruction.MinkowskiSpace.ConeTubeAndLorentzGroup
import Reconstruction.MinkowskiSpace.WightmanTheoriesOfOneHermitianScalarField
import Mathlib
set_option autoImplicit false
open Complex Matrix
noncomputable section
namespace YangMills.Construction.MinkowskiSpace.ConeTubeLorentz
theorem spaceNorm_nonneg (v : Fin 3 → ℝ) : 0 ≤ spaceNorm v := Real.sqrt_nonneg _
theorem spaceNorm_sq (v : Fin 3 → ℝ) : spaceNorm v ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [spaceNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Fin.sum_univ_three]
theorem spaceNorm_eq_euclidean_norm (v : Fin 3 → ℝ) :
    spaceNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [spaceNorm]
theorem spaceNorm_add_le (v w : Fin 3 → ℝ) :
    spaceNorm (v + w) ≤ spaceNorm v + spaceNorm w := by
  simp only [spaceNorm_eq_euclidean_norm, WithLp.toLp_add]
  exact norm_add_le _ _
theorem spaceNorm_smul (t : ℝ) (v : Fin 3 → ℝ) : spaceNorm (t • v) = |t| * spaceNorm v := by
  simp only [spaceNorm_eq_euclidean_norm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
theorem spaceNorm_neg (v : Fin 3 → ℝ) : spaceNorm (-v) = spaceNorm v := by
  have h := spaceNorm_smul (-1) v
  simpa using h
theorem spaceNorm_zero : spaceNorm 0 = 0 := by
  simp [spaceNorm]
theorem abs_dotProduct_le_spaceNorm_mul (v w : Fin 3 → ℝ) :
    |v ⬝ᵥ w| ≤ spaceNorm v * spaceNorm w := by
  apply abs_le_of_sq_le_sq _ (mul_nonneg (spaceNorm_nonneg v) (spaceNorm_nonneg w))
  rw [mul_pow, spaceNorm_sq, spaceNorm_sq]
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [sq_nonneg (v 0 * w 1 - v 1 * w 0), sq_nonneg (v 0 * w 2 - v 2 * w 0),
    sq_nonneg (v 1 * w 2 - v 2 * w 1)]
theorem unitSphere3_sum_sq (v : unitSphere3) :
    (v : Fin 3 → ℝ) 0 ^ 2 + (v : Fin 3 → ℝ) 1 ^ 2 + (v : Fin 3 → ℝ) 2 ^ 2 = 1 := by
  have h : spaceNorm (v : Fin 3 → ℝ) = 1 := v.2
  rw [← spaceNorm_sq, h, one_pow]
theorem spacePart_add (y y' : RealVec4) : spacePart (y + y') = spacePart y + spacePart y' := rfl
theorem spacePart_smul (t : ℝ) (y : RealVec4) : spacePart (t • y) = t • spacePart y := rfl
theorem coneGap_smul {t : ℝ} (ht : 0 ≤ t) (y : RealVec4) :
    coneGap (t • y) = t * coneGap y := by
  simp only [coneGap, spacePart_smul, spaceNorm_smul, abs_of_nonneg ht, Pi.smul_apply,
    smul_eq_mul]
  ring
theorem coneGap_superadditive (y y' : RealVec4) :
    coneGap (y + y') ≥ coneGap y + coneGap y' := by
  have := spaceNorm_add_le (spacePart y) (spacePart y')
  simp only [coneGap, spacePart_add, Pi.add_apply]
  linarith
theorem coneGap_add_ge_sub (y y' : RealVec4) :
    coneGap (y + y') ≥ coneGap y - |y' 0| - spaceNorm (spacePart y') := by
  have := spaceNorm_add_le (spacePart y) (spacePart y')
  have h0 := neg_abs_le (y' 0)
  simp only [coneGap, spacePart_add, Pi.add_apply]
  linarith
theorem coneGapBounds_holds : ConeGapBounds :=
  ⟨fun _ y ht => coneGap_smul ht y, coneGap_superadditive, coneGap_add_ge_sub⟩
theorem convex_futureCone : Convex ℝ futureCone := by
  intro x hx y hy a b ha hb hab
  have hx' : coneGap x > 0 := hx
  have hy' : coneGap y > 0 := hy
  have h := coneGap_superadditive (a • x) (b • y)
  rw [coneGap_smul ha, coneGap_smul hb] at h
  show coneGap (a • x + b • y) > 0
  rcases ha.eq_or_lt with h0 | h0
  · have hb1 : b = 1 := by linarith
    subst hb1
    have := mul_pos one_pos hy'
    nlinarith
  · have := mul_pos h0 hx'
    have := mul_nonneg hb hy'.le
    linarith
theorem convex_closedFutureCone : Convex ℝ closedFutureCone := by
  intro x hx y hy a b ha hb hab
  have hx' : coneGap x ≥ 0 := hx
  have hy' : coneGap y ≥ 0 := hy
  have h := coneGap_superadditive (a • x) (b • y)
  rw [coneGap_smul ha, coneGap_smul hb] at h
  show coneGap (a • x + b • y) ≥ 0
  have := mul_nonneg ha hx'
  have := mul_nonneg hb hy'
  linarith
theorem imPart_real_combination (a b : ℝ) (x y : ComplexVec4) :
    imPart (a • x + b • y) = a • imPart x + b • imPart y := by
  funext μ
  simp [imPart]
theorem convex_futureTube : Convex ℝ futureTube := by
  intro x hx y hy a b ha hb hab
  show imPart (a • x + b • y) ∈ futureCone
  rw [imPart_real_combination]
  exact convex_futureCone hx hy ha hb hab
theorem conesTubeConvex_holds : ConesTubeConvex := by
  refine ⟨convex_futureCone, ?_, convex_closedFutureCone, ?_, ?_, convex_futureTube, ?_⟩
  · intro t ht y hy
    have hy' : coneGap y > 0 := hy
    show coneGap (t • y) > 0
    rw [coneGap_smul ht.le]
    exact mul_pos ht hy'
  · intro t ht y hy
    have hy' : coneGap y ≥ 0 := hy
    show coneGap (t • y) ≥ 0
    rw [coneGap_smul ht.le]
    exact mul_nonneg ht.le hy'
  · intro y hy y' hy'
    have h1 : coneGap y ≥ 0 := hy
    have h2 : coneGap y' > 0 := hy'
    have := coneGap_superadditive y y'
    show coneGap (y + y') > 0
    linarith
  · intro b
    exact convex_pi fun _ _ => convex_futureTube
def realMinkowskiForm (y p : RealVec4) : ℝ := y 0 * p 0 - spacePart y ⬝ᵥ spacePart p
theorem minkowskiForm_toComplex (y p : RealVec4) :
    minkowskiForm (toComplex y) (toComplex p) = (realMinkowskiForm y p : ℂ) := by
  simp [minkowskiForm, realMinkowskiForm, spaceBilin, spacePart, toComplex, dotProduct,
    Fin.sum_univ_three]
theorem realMinkowskiForm_self (y : RealVec4) :
    realMinkowskiForm y y = y 0 ^ 2 - spaceNorm (spacePart y) ^ 2 := by
  rw [spaceNorm_sq]
  simp only [realMinkowskiForm, dotProduct, Fin.sum_univ_three]
  ring
theorem spaceNorm_le_time_of_mem_closed {p : RealVec4} (hp : p ∈ closedFutureCone) :
    spaceNorm (spacePart p) ≤ p 0 := by
  have h : coneGap p ≥ 0 := hp
  simp only [coneGap] at h
  linarith
theorem formOnClosedCone_holds : FormOnClosedCone := by
  intro y hy p hp
  have hp0 := spaceNorm_le_time_of_mem_closed hp
  have hnp := spaceNorm_nonneg (spacePart p)
  have hny := spaceNorm_nonneg (spacePart y)
  have hd : coneGap y ≥ 0 := hy
  refine ⟨?_, mul_nonneg hd (hnp.trans hp0), ?_⟩
  · rw [minkowskiForm_toComplex, Complex.ofReal_re]
    have hc := (abs_le.mp (abs_dotProduct_le_spaceNorm_mul (spacePart y) (spacePart p))).2
    simp only [realMinkowskiForm, coneGap]
    nlinarith [mul_le_mul_of_nonneg_left hp0 hny]
  · have hpp : 0 ≤ p 0 := hnp.trans hp0
    have hsq : spaceNorm (spacePart p) ^ 2 ≤ p 0 ^ 2 := by nlinarith
    rw [spaceNorm_sq] at hsq
    have hs : ∑ μ, p μ ^ 2 ≤ 2 * p 0 ^ 2 := by
      simp only [Fin.sum_univ_four]
      simp only [spacePart] at hsq
      have e1 : (Fin.succ (0 : Fin 3) : Fin 4) = 1 := rfl
      have e2 : (Fin.succ (1 : Fin 3) : Fin 4) = 2 := rfl
      have e3 : (Fin.succ (2 : Fin 3) : Fin 4) = 3 := rfl
      rw [e1, e2, e3] at hsq
      linarith
    calc YangMills.Construction.TorusMetric.euclidNormVec p ≤ Real.sqrt (2 * p 0 ^ 2) :=
          Real.sqrt_le_sqrt hs
      _ = Real.sqrt 2 * p 0 := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hpp]
theorem ext_of_mulVec_eq {M N : ComplexMat4} (h : ∀ ζ, M *ᵥ ζ = N *ᵥ ζ) : M = N :=
  Matrix.mulVec_injective (funext h)
theorem minkowskiForm_wickMap (x x' : ComplexVec4) :
    minkowskiForm (wickMap x) (wickMap x') = -∑ μ, x μ * x' μ := by
  simp only [minkowskiForm, spaceBilin, spacePart_wickMap, wickMap_apply_zero,
    Fin.sum_univ_three, Fin.sum_univ_four]
  simp only [Matrix.cons_val]
  linear_combination (x 3 * x' 3) * Complex.I_sq
theorem minkowskiForm_wickMap_eq_neg_dotProduct (x x' : ComplexVec4) :
    minkowskiForm (wickMap x) (wickMap x') = -(x ⬝ᵥ x') :=
  minkowskiForm_wickMap x x'
theorem conjByWick_mulVec (M : ComplexMat4) (ζ : ComplexVec4) :
    conjByWick M *ᵥ ζ = wickMap (M *ᵥ wickMap.symm ζ) := by
  simp [conjByWick, LinearMap.toMatrix'_mulVec]
theorem conjByWickInv_mulVec (M : ComplexMat4) (x : ComplexVec4) :
    conjByWickInv M *ᵥ x = wickMap.symm (M *ᵥ wickMap x) := by
  simp [conjByWickInv, LinearMap.toMatrix'_mulVec]
theorem conjByWick_conjByWickInv (Z : ComplexMat4) : conjByWick (conjByWickInv Z) = Z := by
  apply ext_of_mulVec_eq
  intro ζ
  simp [conjByWick_mulVec, conjByWickInv_mulVec]
theorem conjByWickInv_conjByWick (A : ComplexMat4) : conjByWickInv (conjByWick A) = A := by
  apply ext_of_mulVec_eq
  intro ζ
  simp [conjByWick_mulVec, conjByWickInv_mulVec]
theorem conjByWick_add (A B : ComplexMat4) :
    conjByWick (A + B) = conjByWick A + conjByWick B := by
  apply ext_of_mulVec_eq
  intro ζ
  simp [conjByWick_mulVec, Matrix.add_mulVec]
theorem conjByWick_smul (t : ℂ) (A : ComplexMat4) : conjByWick (t • A) = t • conjByWick A := by
  apply ext_of_mulVec_eq
  intro ζ
  simp [conjByWick_mulVec, Matrix.smul_mulVec]
theorem toComplexMatrix_transpose (A : RealMat4) :
    (toComplexMatrix A)ᵀ = toComplexMatrix Aᵀ := by
  ext i j
  simp [toComplexMatrix]
theorem toComplexMatrix_mul (A B : RealMat4) :
    toComplexMatrix (A * B) = toComplexMatrix A * toComplexMatrix B := by
  ext i j
  simp [toComplexMatrix, Matrix.mul_apply]
theorem toComplexMatrix_one : toComplexMatrix 1 = 1 := by
  ext i j
  simp [toComplexMatrix, Matrix.one_apply]
  split_ifs <;> simp
theorem toComplexMatrix_injective : Function.Injective toComplexMatrix := by
  intro A B h
  ext i j
  have := congrFun (congrFun h i) j
  simpa [toComplexMatrix] using this
theorem toComplexMatrix_mulVec (A : RealMat4) (y : RealVec4) :
    toComplexMatrix A *ᵥ toComplex y = toComplex (A *ᵥ y) := by
  funext μ
  simp [toComplexMatrix, toComplex, Matrix.mulVec, dotProduct]
theorem mulVec_dotProduct_eq_dotProduct_transpose_mulVec (W : ComplexMat4) (a b : ComplexVec4) :
    (W *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (Wᵀ *ᵥ b) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
theorem mem_lorentzAlgebraC_iff (Z : ComplexMat4) : Z ∈ lorentzAlgebraC ↔
    (conjByWickInv Z)ᵀ = -conjByWickInv Z := by
  set W := conjByWickInv Z with hW
  have hZ : ∀ a, Z *ᵥ wickMap a = wickMap (W *ᵥ a) := by
    intro a
    simp [hW, conjByWickInv_mulVec]
  have key : ∀ a b : ComplexVec4,
      minkowskiForm (Z *ᵥ wickMap a) (wickMap b) + minkowskiForm (wickMap a) (Z *ᵥ wickMap b) =
      -((W *ᵥ a) ⬝ᵥ b + a ⬝ᵥ (W *ᵥ b)) := by
    intro a b
    rw [hZ, hZ, minkowskiForm_wickMap_eq_neg_dotProduct, minkowskiForm_wickMap_eq_neg_dotProduct]
    ring
  constructor
  · intro hmem
    ext i j
    have h := hmem (wickMap (Pi.single j 1)) (wickMap (Pi.single i 1))
    rw [key] at h
    simp only [Matrix.mulVec_single_one, dotProduct_single_one, single_one_dotProduct,
      neg_eq_zero] at h
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.col_apply] at h ⊢
    linear_combination h
  · intro hT ζ ζ'
    have h := key (wickMap.symm ζ) (wickMap.symm ζ')
    simp only [LinearEquiv.apply_symm_apply] at h
    rw [h, mulVec_dotProduct_eq_dotProduct_transpose_mulVec, hT]
    simp [Matrix.neg_mulVec, dotProduct_neg]
theorem conjByWick_orthogonal_mem (R : Matrix.orthogonalGroup (Fin 4) ℝ) :
    conjByWick (toComplexMatrix (R : RealMat4)) ∈ lorentzGroupC := by
  intro ζ ζ'
  rw [conjByWick_mulVec, conjByWick_mulVec, minkowskiForm_wickMap_eq_neg_dotProduct,
    mulVec_dotProduct_eq_dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    toComplexMatrix_transpose, ← toComplexMatrix_mul]
  have h : (R : RealMat4)ᵀ * (R : RealMat4) = 1 := by
    have := (Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).mp R.2
    simpa [Matrix.star_eq_conjTranspose] using this
  rw [h, toComplexMatrix_one, Matrix.one_mulVec, ← minkowskiForm_wickMap_eq_neg_dotProduct]
  simp
theorem map_re_transpose_of_antisymm {W : ComplexMat4} (h : Wᵀ = -W) :
    (W.map Complex.re)ᵀ = -W.map Complex.re := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
  simp [this]
theorem map_im_transpose_of_antisymm {W : ComplexMat4} (h : Wᵀ = -W) :
    (W.map Complex.im)ᵀ = -W.map Complex.im := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
  simp [this]
theorem eq_re_add_I_smul_im (W : ComplexMat4) :
    W = toComplexMatrix (W.map Complex.re) + I • toComplexMatrix (W.map Complex.im) := by
  ext i j
  simp [toComplexMatrix, mul_comm I]
theorem lorentzAlgebraC_eq_span : lorentzAlgebraC = Submodule.span ℂ
      {Z | ∃ A : RealMat4, Aᵀ = -A ∧ Z = conjByWick (toComplexMatrix A)} := by
  have hgen : ∀ A : RealMat4, Aᵀ = -A → conjByWick (toComplexMatrix A) ∈ lorentzAlgebraC := by
    intro A hA
    rw [mem_lorentzAlgebraC_iff, conjByWickInv_conjByWick, toComplexMatrix_transpose, hA]
    ext i j
    simp [toComplexMatrix]
  apply le_antisymm
  · intro Z hZ
    have hW := (mem_lorentzAlgebraC_iff Z).mp hZ
    set W := conjByWickInv Z with hWdef
    have hZW : Z = conjByWick W := (conjByWick_conjByWickInv Z).symm
    rw [hZW, eq_re_add_I_smul_im W, conjByWick_add, conjByWick_smul]
    refine Submodule.add_mem _
      (Submodule.subset_span ⟨_, map_re_transpose_of_antisymm hW, rfl⟩) ?_
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, map_im_transpose_of_antisymm hW, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro Z ⟨A, hA, rfl⟩
    exact hgen A hA
theorem imPart_wickMap (x : ComplexVec4) :
    imPart (wickMap x) = mkTimeSpace (x 3).re ![(x 0).im, (x 1).im, (x 2).im] := by
  funext μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp [imPart, wickMap_apply_zero, mkTimeSpace]
  · have h := congrFun (spacePart_wickMap x) i
    simp only [spacePart] at h
    simp only [imPart, mkTimeSpace, Fin.cons_succ, h]
    fin_cases i <;> simp
theorem wickMap_toComplex_mem_futureTube_iff (x : RealVec4) :
    wickMap (toComplex x) ∈ futureTube ↔ x 3 > 0 := by
  have h := imPart_wickMap (toComplex x)
  have hz : (![((toComplex x) 0).im, ((toComplex x) 1).im, ((toComplex x) 2).im] :
      Fin 3 → ℝ) = 0 := by
    funext i
    fin_cases i <;> simp [toComplex]
  show coneGap (imPart _) > 0 ↔ _
  rw [h, hz]
  have hs : spacePart (mkTimeSpace ((toComplex x) 3).re (0 : Fin 3 → ℝ)) = 0 := by
    funext i
    simp [spacePart, mkTimeSpace]
  have hm : coneGap (mkTimeSpace ((toComplex x) 3).re (0 : Fin 3 → ℝ)) = x 3 := by
    rw [coneGap, hs, spaceNorm_zero]
    simp [mkTimeSpace, toComplex]
  rw [hm]
theorem conjPoint_wickMap_toComplex (x : RealVec4) : conjPoint (wickMap (toComplex x)) =
      wickMap (toComplex (YangMills.Construction.TestSpaces.timeReflect x)) := by
  funext μ
  fin_cases μ <;>
    simp [conjPoint, rePart, imPart, wickMap, toComplex,
      YangMills.Construction.TestSpaces.timeReflect]
theorem rotationSumOne_eq_of_entries (R : Matrix.orthogonalGroup (Fin 3) ℝ) :
    rotationSumOne R = !![(R : Matrix (Fin 3) (Fin 3) ℝ) 0 0, (R : Matrix (Fin 3) (Fin 3) ℝ) 0 1,
        (R : Matrix (Fin 3) (Fin 3) ℝ) 0 2, 0;
      (R : Matrix (Fin 3) (Fin 3) ℝ) 1 0, (R : Matrix (Fin 3) (Fin 3) ℝ) 1 1,
        (R : Matrix (Fin 3) (Fin 3) ℝ) 1 2, 0;
      (R : Matrix (Fin 3) (Fin 3) ℝ) 2 0, (R : Matrix (Fin 3) (Fin 3) ℝ) 2 1,
        (R : Matrix (Fin 3) (Fin 3) ℝ) 2 2, 0;
      0, 0, 0, 1] := by
  have h0 : finSumFinEquiv.symm (0 : Fin (3 + 1)) = Sum.inl (0 : Fin 3) := rfl
  have h1 : finSumFinEquiv.symm (1 : Fin (3 + 1)) = Sum.inl (1 : Fin 3) := rfl
  have h2 : finSumFinEquiv.symm (2 : Fin (3 + 1)) = Sum.inl (2 : Fin 3) := rfl
  have h3 : finSumFinEquiv.symm (3 : Fin (3 + 1)) = Sum.inr (0 : Fin 1) := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationSumOne, Matrix.reindex_apply, h0, h1, h2, h3]
theorem rotationLinearMap_apply_zero (R : Matrix.orthogonalGroup (Fin 3) ℝ) (ζ : ComplexVec4) :
    rotationLinearMap R ζ 0 = ζ 0 := rfl
theorem rotationLinearMap_apply_succ (R : Matrix.orthogonalGroup (Fin 3) ℝ) (ζ : ComplexVec4)
    (i : Fin 3) :
    rotationLinearMap R ζ i.succ = ∑ j, ((R : Matrix (Fin 3) (Fin 3) ℝ) i j : ℂ) * ζ j.succ := by
  simp [rotationLinearMap, mkTimeSpace, Matrix.mulVec, dotProduct, spacePart]
theorem conjByWick_rotationSumOne (R : Matrix.orthogonalGroup (Fin 3) ℝ) :
    conjByWick (toComplexMatrix (rotationSumOne R)) = rotationMatrix R := by
  apply ext_of_mulVec_eq
  intro ζ
  rw [conjByWick_mulVec, rotationMatrix_mulVec, rotationSumOne_eq_of_entries]
  funext μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · rw [rotationLinearMap_apply_zero]
    simp [toComplexMatrix, wickMap, Matrix.mulVec, dotProduct, Fin.sum_univ_four, ← mul_assoc]
  · rw [rotationLinearMap_apply_succ]
    fin_cases i <;>
      simp [toComplexMatrix, wickMap, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        Fin.sum_univ_three]
theorem wickMapFormulas_holds : WickMapFormulas :=
  ⟨minkowskiForm_wickMap, conjByWick_orthogonal_mem, mem_lorentzAlgebraC_iff,
    lorentzAlgebraC_eq_span, imPart_wickMap, wickMap_toComplex_mem_futureTube_iff,
    conjPoint_wickMap_toComplex, conjByWick_rotationSumOne⟩
def boostEntries {R : Type*} [CommRing R] (c s : R) (n : Fin 3 → R) : Matrix (Fin 4) (Fin 4) R :=
  !![c, s * n 0, s * n 1, s * n 2;
     s * n 0, 1 + (c - 1) * n 0 * n 0, (c - 1) * n 0 * n 1, (c - 1) * n 0 * n 2;
     s * n 1, (c - 1) * n 1 * n 0, 1 + (c - 1) * n 1 * n 1, (c - 1) * n 1 * n 2;
     s * n 2, (c - 1) * n 2 * n 0, (c - 1) * n 2 * n 1, 1 + (c - 1) * n 2 * n 2]
theorem boostMatrix_mulVec_zero (v : unitSphere3) (β : ℂ) (ζ : ComplexVec4) :
    (boostMatrix v β *ᵥ ζ) 0 = Complex.cosh β * ζ 0 + Complex.sinh β * axisDot v ζ := by
  rw [boostMatrix_mulVec]
  simp [boostLinearMap, timeUnit, ofSpaceVector, mkTimeSpace, toComplex]
  ring
theorem boostMatrix_mulVec_succ (v : unitSphere3) (β : ℂ) (ζ : ComplexVec4) (i : Fin 3) :
    (boostMatrix v β *ᵥ ζ) i.succ = ζ i.succ +
      ((Complex.cosh β - 1) * axisDot v ζ + Complex.sinh β * ζ 0) *
        ((v : Fin 3 → ℝ) i : ℂ) := by
  rw [boostMatrix_mulVec]
  simp [boostLinearMap, timeUnit, ofSpaceVector, mkTimeSpace, toComplex]
  ring
theorem unitSphere3_sum_sq_complex (v : unitSphere3) :
    (((v : Fin 3 → ℝ) 0 : ℂ)) ^ 2 + (((v : Fin 3 → ℝ) 1 : ℂ)) ^ 2 +
      (((v : Fin 3 → ℝ) 2 : ℂ)) ^ 2 = 1 := by
  exact_mod_cast unitSphere3_sum_sq v
theorem axisDot_eq (v : unitSphere3) (ζ : ComplexVec4) :
    axisDot v ζ = ((v : Fin 3 → ℝ) 0 : ℂ) * ζ 1 + ((v : Fin 3 → ℝ) 1 : ℂ) * ζ 2 +
      ((v : Fin 3 → ℝ) 2 : ℂ) * ζ 3 := by
  simp only [axisDot, spaceBilin, spacePart, Fin.sum_univ_three]
  rfl
theorem boostMatrix_mulVec_one (v : unitSphere3) (β : ℂ) (ζ : ComplexVec4) :
    (boostMatrix v β *ᵥ ζ) 1 = ζ 1 +
      ((Complex.cosh β - 1) * axisDot v ζ + Complex.sinh β * ζ 0) *
        ((v : Fin 3 → ℝ) 0 : ℂ) := boostMatrix_mulVec_succ v β ζ 0
theorem boostMatrix_mulVec_two (v : unitSphere3) (β : ℂ) (ζ : ComplexVec4) :
    (boostMatrix v β *ᵥ ζ) 2 = ζ 2 +
      ((Complex.cosh β - 1) * axisDot v ζ + Complex.sinh β * ζ 0) *
        ((v : Fin 3 → ℝ) 1 : ℂ) := boostMatrix_mulVec_succ v β ζ 1
theorem boostMatrix_mulVec_three (v : unitSphere3) (β : ℂ) (ζ : ComplexVec4) :
    (boostMatrix v β *ᵥ ζ) 3 = ζ 3 +
      ((Complex.cosh β - 1) * axisDot v ζ + Complex.sinh β * ζ 0) *
        ((v : Fin 3 → ℝ) 2 : ℂ) := boostMatrix_mulVec_succ v β ζ 2
theorem axisDot_boostMatrix_mulVec (v : unitSphere3) (β : ℂ) (ζ : ComplexVec4) :
    axisDot v (boostMatrix v β *ᵥ ζ) = Complex.cosh β * axisDot v ζ + Complex.sinh β * ζ 0 := by
  have hv := unitSphere3_sum_sq_complex v
  have hd := axisDot_eq v ζ
  rw [axisDot_eq v (boostMatrix v β *ᵥ ζ), boostMatrix_mulVec_one, boostMatrix_mulVec_two,
    boostMatrix_mulVec_three]
  linear_combination ((Complex.cosh β - 1) * axisDot v ζ + Complex.sinh β * ζ 0) * hv - hd
theorem minkowskiForm_eq (a b : ComplexVec4) :
    minkowskiForm a b = a 0 * b 0 - (a 1 * b 1 + a 2 * b 2 + a 3 * b 3) := by
  simp only [minkowskiForm, spaceBilin, spacePart, Fin.sum_univ_three]
  rfl
theorem boostMatrix_mem_lorentzGroupC (v : unitSphere3) (β : ℂ) :
    boostMatrix v β ∈ lorentzGroupC := by
  intro ζ ζ'
  have hv := unitSphere3_sum_sq_complex v
  have hcs := Complex.cosh_sq_sub_sinh_sq β
  have hd := axisDot_eq v ζ
  have hd' := axisDot_eq v ζ'
  rw [minkowskiForm_eq, minkowskiForm_eq, boostMatrix_mulVec_zero, boostMatrix_mulVec_zero,
    boostMatrix_mulVec_one, boostMatrix_mulVec_one, boostMatrix_mulVec_two,
    boostMatrix_mulVec_two, boostMatrix_mulVec_three, boostMatrix_mulVec_three]
  rw [hd, hd']
  generalize ((v : Fin 3 → ℝ) 0 : ℂ) = n0 at *
  generalize ((v : Fin 3 → ℝ) 1 : ℂ) = n1 at *
  generalize ((v : Fin 3 → ℝ) 2 : ℂ) = n2 at *
  generalize Complex.cosh β = c at *
  generalize Complex.sinh β = s at *
  linear_combination
    (ζ 0 * ζ' 0 - (n0 * ζ 1 + n1 * ζ 2 + n2 * ζ 3) * (n0 * ζ' 1 + n1 * ζ' 2 + n2 * ζ' 3)) * hcs -
      (((c - 1) * (n0 * ζ 1 + n1 * ζ 2 + n2 * ζ 3) + s * ζ 0) *
        ((c - 1) * (n0 * ζ' 1 + n1 * ζ' 2 + n2 * ζ' 3) + s * ζ' 0)) * hv
theorem boostMatrix_mul (v : unitSphere3) (β β' : ℂ) :
    boostMatrix v β * boostMatrix v β' = boostMatrix v (β + β') := by
  apply ext_of_mulVec_eq
  intro ζ
  rw [← Matrix.mulVec_mulVec]
  funext μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · rw [boostMatrix_mulVec_zero, boostMatrix_mulVec_zero, boostMatrix_mulVec_zero,
      axisDot_boostMatrix_mulVec, Complex.cosh_add, Complex.sinh_add]
    ring
  · rw [boostMatrix_mulVec_succ, boostMatrix_mulVec_succ, boostMatrix_mulVec_succ,
      axisDot_boostMatrix_mulVec, boostMatrix_mulVec_zero, Complex.cosh_add, Complex.sinh_add]
    ring
theorem boostMatrix_eq_boostEntries (v : unitSphere3) (β : ℂ) : boostMatrix v β =
    boostEntries (Complex.cosh β) (Complex.sinh β) fun i => ((v : Fin 3 → ℝ) i : ℂ) := by
  apply ext_of_mulVec_eq
  intro ζ
  funext μ
  have hd := axisDot_eq v ζ
  fin_cases μ
  · show (boostMatrix v β *ᵥ ζ) 0 = _
    rw [boostMatrix_mulVec_zero, hd]
    simp [boostEntries, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
  · show (boostMatrix v β *ᵥ ζ) 1 = _
    rw [boostMatrix_mulVec_one, hd]
    simp [boostEntries, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
  · show (boostMatrix v β *ᵥ ζ) 2 = _
    rw [boostMatrix_mulVec_two, hd]
    simp [boostEntries, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
  · show (boostMatrix v β *ᵥ ζ) 3 = _
    rw [boostMatrix_mulVec_three, hd]
    simp [boostEntries, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
theorem boostMatrix_polynomial_entries : ∃ P : Fin 4 → Fin 4 → MvPolynomial (Fin 5) ℂ,
      ∀ (v : unitSphere3) (β : ℂ) (μ ν : Fin 4), boostMatrix v β μ ν =
        MvPolynomial.aeval
          ![Complex.cosh β, Complex.sinh β, ((v : Fin 3 → ℝ) 0 : ℂ), ((v : Fin 3 → ℝ) 1 : ℂ),
            ((v : Fin 3 → ℝ) 2 : ℂ)] (P μ ν) := by
  refine ⟨fun μ ν => boostEntries (MvPolynomial.X 0) (MvPolynomial.X 1)
    ![MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4] μ ν, ?_⟩
  intro v β μ ν
  rw [boostMatrix_eq_boostEntries]
  fin_cases μ <;> fin_cases ν <;> simp [boostEntries]
def planeRotEntries {R : Type*} [CommRing R] (c s : R) (n : Fin 3 → R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![1 + (c - 1) * n 0 * n 0, (c - 1) * n 0 * n 1, (c - 1) * n 0 * n 2, -(s * n 0);
     (c - 1) * n 1 * n 0, 1 + (c - 1) * n 1 * n 1, (c - 1) * n 1 * n 2, -(s * n 1);
     (c - 1) * n 2 * n 0, (c - 1) * n 2 * n 1, 1 + (c - 1) * n 2 * n 2, -(s * n 2);
     s * n 0, s * n 1, s * n 2, c]
theorem imagBoostRotation_eq_planeRotEntries (v : unitSphere3) (a : ℝ) : imagBoostRotation v a =
    planeRotEntries (Real.cos a) (Real.sin a) (v : Fin 3 → ℝ) := by
  apply Matrix.mulVec_injective
  funext x
  rw [imagBoostRotation_mulVec]
  funext μ
  fin_cases μ <;>
    simp [imagBoostRotationMap, planeRotEntries, spaceDot, euclidTimeUnit, ofSpaceEuclid,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] <;>
    ring
theorem boostMatrix_I_mul_wickMap (v : unitSphere3) (a : ℝ) (x : ComplexVec4) :
    boostMatrix v (I * a) *ᵥ wickMap x = wickMap (toComplexMatrix (imagBoostRotation v a) *ᵥ x) := by
  have hc : Complex.cosh (I * a) = Complex.cos a := by
    rw [mul_comm, Complex.cosh_mul_I]
  have hs : Complex.sinh (I * a) = Complex.sin a * I := by
    rw [mul_comm, Complex.sinh_mul_I]
  have hd : axisDot v (wickMap x) = ((v : Fin 3 → ℝ) 0 : ℂ) * x 0 +
      ((v : Fin 3 → ℝ) 1 : ℂ) * x 1 + ((v : Fin 3 → ℝ) 2 : ℂ) * x 2 := by
    rw [axisDot_eq]
    rfl
  have hR : ∀ μ : Fin 4, (toComplexMatrix (imagBoostRotation v a) *ᵥ x) μ =
      (planeRotEntries (Real.cos a : ℂ) (Real.sin a : ℂ)
        (fun i => ((v : Fin 3 → ℝ) i : ℂ)) *ᵥ x) μ := by
    intro μ
    rw [imagBoostRotation_eq_planeRotEntries]
    fin_cases μ <;>
      simp [toComplexMatrix, planeRotEntries, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  funext μ
  have h0 : (wickMap x) 0 = I * x 3 := rfl
  have h1 : (wickMap x) 1 = x 0 := rfl
  have h2 : (wickMap x) 2 = x 1 := rfl
  have h3 : (wickMap x) 3 = x 2 := rfl
  have hI := Complex.I_sq
  fin_cases μ
  · show (boostMatrix v (I * a) *ᵥ wickMap x) 0 =
      I * (toComplexMatrix (imagBoostRotation v a) *ᵥ x) 3
    rw [boostMatrix_mulVec_zero, hR, hc, hs, hd, h0]
    simp [planeRotEntries, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
  · show (boostMatrix v (I * a) *ᵥ wickMap x) 1 =
      (toComplexMatrix (imagBoostRotation v a) *ᵥ x) 0
    rw [boostMatrix_mulVec_one, hR, hc, hs, hd, h0, h1]
    simp [planeRotEntries, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    linear_combination (Complex.sin a * x 3 * ((v : Fin 3 → ℝ) 0 : ℂ)) * hI
  · show (boostMatrix v (I * a) *ᵥ wickMap x) 2 =
      (toComplexMatrix (imagBoostRotation v a) *ᵥ x) 1
    rw [boostMatrix_mulVec_two, hR, hc, hs, hd, h0, h2]
    simp [planeRotEntries, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    linear_combination (Complex.sin a * x 3 * ((v : Fin 3 → ℝ) 1 : ℂ)) * hI
  · show (boostMatrix v (I * a) *ᵥ wickMap x) 3 =
      (toComplexMatrix (imagBoostRotation v a) *ᵥ x) 2
    rw [boostMatrix_mulVec_three, hR, hc, hs, hd, h0, h3]
    simp [planeRotEntries, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    linear_combination (Complex.sin a * x 3 * ((v : Fin 3 → ℝ) 2 : ℂ)) * hI
open YangMills.Construction.WightmanReconstruction.SmoothToolkit in
theorem imagBoostRotation_mem_SO (hrot : PlaneRotationsAndTransitivity) (v : unitSphere3)
    (a : ℝ) : imagBoostRotation v a ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ := by
  have hv := unitSphere3_sum_sq v
  have he : IsUnitVec (ofSpaceEuclid v) := by
    have : ofSpaceEuclid v ⬝ᵥ ofSpaceEuclid v = 1 := by
      simp only [ofSpaceEuclid, dotProduct, Fin.sum_univ_four]
      simp
      linarith
    simp [IsUnitVec, vecLength, this]
  have hw : IsUnitVec euclidTimeUnit := by
    have : euclidTimeUnit ⬝ᵥ euclidTimeUnit = 1 := by
      simp [euclidTimeUnit, dotProduct, Fin.sum_univ_four]
    simp [IsUnitVec, vecLength, this]
  have hew : ofSpaceEuclid v ⬝ᵥ euclidTimeUnit = 0 := by
    simp [ofSpaceEuclid, euclidTimeUnit, dotProduct, Fin.sum_univ_four]
  have hmap : imagBoostRotationMap v a = planeRotation (ofSpaceEuclid v) euclidTimeUnit a := by
    apply LinearMap.ext
    intro x
    funext μ
    fin_cases μ <;>
      simp [imagBoostRotationMap, planeRotation, spaceDot, euclidTimeUnit, ofSpaceEuclid,
        dotProduct, Fin.sum_univ_four]
  have := ((hrot 4 (Or.inr rfl)).1 _ _ a he hw hew).1
  rwa [← hmap] at this
theorem boostsAndRotations_holds
    (hrot : YangMills.Construction.WightmanReconstruction.SmoothToolkit.PlaneRotationsAndTransitivity) :
    BoostsAndRotations :=
  ⟨boostMatrix_mem_lorentzGroupC, boostMatrix_mul, boostMatrix_polynomial_entries,
    fun v a => ⟨imagBoostRotation_mem_SO hrot v a, boostMatrix_I_mul_wickMap v a⟩⟩
theorem axisDot_re (v : unitSphere3) (ζ : ComplexVec4) :
    (axisDot v ζ).re = (v : Fin 3 → ℝ) ⬝ᵥ spacePart (rePart ζ) := by
  simp [axisDot, spaceBilin, spacePart, rePart, dotProduct, Fin.sum_univ_three]
theorem axisDot_im (v : unitSphere3) (ζ : ComplexVec4) :
    (axisDot v ζ).im = (v : Fin 3 → ℝ) ⬝ᵥ spacePart (imPart ζ) := by
  simp [axisDot, spaceBilin, spacePart, imPart, dotProduct, Fin.sum_univ_three]
def imagBoostShift (v : unitSphere3) (a : ℝ) (ζ : ComplexVec4) : RealVec4 :=
  mkTimeSpace
    ((Real.cos a - 1) * imPart ζ 0 + Real.sin a * ((v : Fin 3 → ℝ) ⬝ᵥ spacePart (rePart ζ)))
    (((Real.cos a - 1) * ((v : Fin 3 → ℝ) ⬝ᵥ spacePart (imPart ζ)) +
      Real.sin a * rePart ζ 0) • (v : Fin 3 → ℝ))
theorem imPart_boostMatrix_I_mul (v : unitSphere3) (a : ℝ) (ζ : ComplexVec4) :
    imPart (boostMatrix v (I * a) *ᵥ ζ) = imPart ζ + imagBoostShift v a ζ := by
  have hc : Complex.cosh (I * a) = (Real.cos a : ℂ) := by
    rw [mul_comm, Complex.cosh_mul_I, Complex.ofReal_cos]
  have hs : Complex.sinh (I * a) = (Real.sin a : ℂ) * I := by
    rw [mul_comm, Complex.sinh_mul_I, Complex.ofReal_sin]
  funext μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp only [imPart, Pi.add_apply]
    rw [boostMatrix_mulVec_zero, hc, hs]
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, imagBoostShift, mkTimeSpace, Fin.cons_zero]
    have h1 := axisDot_re v ζ
    simp only [imPart] at h1 ⊢
    rw [h1]
    ring
  · simp only [imPart, Pi.add_apply]
    rw [boostMatrix_mulVec_succ, hc, hs]
    have h1 := axisDot_im v ζ
    simp only [Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.mul_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      imagBoostShift, mkTimeSpace, Fin.cons_succ, Pi.smul_apply, smul_eq_mul, Complex.one_re,
      Complex.one_im]
    simp only [rePart] at h1 ⊢
    rw [h1]
    ring
theorem spaceNorm_unitSphere3 (v : unitSphere3) : spaceNorm (v : Fin 3 → ℝ) = 1 := v.2
theorem abs_unit_dotProduct_le (v : unitSphere3) (w : Fin 3 → ℝ) :
    |(v : Fin 3 → ℝ) ⬝ᵥ w| ≤ spaceNorm w := by
  have := abs_dotProduct_le_spaceNorm_mul (v : Fin 3 → ℝ) w
  rwa [spaceNorm_unitSphere3, one_mul] at this
theorem spacePart_mkTimeSpace {α : Type*} (t : α) (w : Fin 3 → α) :
    spacePart (mkTimeSpace t w) = w := by
  funext i
  simp [spacePart, mkTimeSpace]
theorem mkTimeSpace_zero {α : Type*} (t : α) (w : Fin 3 → α) : mkTimeSpace t w 0 = t := by
  simp [mkTimeSpace]
theorem tubeGap_boost_ge (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (v : unitSphere3) (ζ : ComplexVec4) :
    tubeGap (boostMatrix v (I * a) *ᵥ ζ) ≥ tubeGap ζ - a * l1Norm ζ := by
  have hsin0 : 0 ≤ Real.sin a :=
    Real.sin_nonneg_of_nonneg_of_le_pi ha (ha1.trans (by linarith [Real.pi_gt_three]))
  have hsin : Real.sin a ≤ a := Real.sin_le ha
  have hcos0 : 0 ≤ 1 - Real.cos a := by linarith [Real.cos_le_one a]
  have hcos : 1 - Real.cos a ≤ a := by
    have := Real.one_sub_sq_div_two_le_cos (x := a)
    nlinarith
  rw [tubeGap, imPart_boostMatrix_I_mul]
  have hm := coneGap_add_ge_sub (imPart ζ) (imagBoostShift v a ζ)
  set u := rePart ζ with hu
  set w := imPart ζ with hw
  have hdu := abs_unit_dotProduct_le v (spacePart u)
  have hdw := abs_unit_dotProduct_le v (spacePart w)
  have ht : |imagBoostShift v a ζ 0| ≤
      (1 - Real.cos a) * |w 0| + Real.sin a * spaceNorm (spacePart u) := by
    rw [imagBoostShift, mkTimeSpace_zero]
    calc _ ≤ |(Real.cos a - 1) * imPart ζ 0| +
          |Real.sin a * ((v : Fin 3 → ℝ) ⬝ᵥ spacePart (rePart ζ))| := abs_add_le _ _
      _ = (1 - Real.cos a) * |w 0| + Real.sin a * |(v : Fin 3 → ℝ) ⬝ᵥ spacePart u| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hsin0, abs_of_nonpos (by linarith)]
        simp only [neg_sub, hu, hw]
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hdu hsin0
        linarith
  have hsp : spaceNorm (spacePart (imagBoostShift v a ζ)) ≤
      (1 - Real.cos a) * spaceNorm (spacePart w) + Real.sin a * |u 0| := by
    rw [imagBoostShift, spacePart_mkTimeSpace, spaceNorm_smul, spaceNorm_unitSphere3, mul_one]
    calc _ ≤ |(Real.cos a - 1) * ((v : Fin 3 → ℝ) ⬝ᵥ spacePart (imPart ζ))| +
          |Real.sin a * rePart ζ 0| := abs_add_le _ _
      _ = (1 - Real.cos a) * |(v : Fin 3 → ℝ) ⬝ᵥ spacePart w| + Real.sin a * |u 0| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hsin0, abs_of_nonpos (by linarith)]
        simp only [neg_sub, hu, hw]
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hdw hcos0
        linarith
  have hn1 := abs_nonneg (w 0)
  have hn2 := spaceNorm_nonneg (spacePart w)
  have hn3 := abs_nonneg (u 0)
  have hn4 := spaceNorm_nonneg (spacePart u)
  have hon : l1Norm ζ = |u 0| + spaceNorm (spacePart u) + |w 0| + spaceNorm (spacePart w) := rfl
  have b1 := mul_le_mul_of_nonneg_right hcos (add_nonneg hn1 hn2)
  have b2 := mul_le_mul_of_nonneg_right hsin (add_nonneg hn3 hn4)
  rw [hon, show tubeGap ζ = coneGap w from rfl]
  nlinarith
theorem rePart_toComplex_add_I_smul (x : RealVec4) (ε : ℝ) :
    rePart (toComplex x + I • toComplex (ε • timeUnit)) = x := by
  funext μ
  simp [rePart, toComplex]
theorem imPart_toComplex_add_I_smul (x : RealVec4) (ε : ℝ) :
    imPart (toComplex x + I • toComplex (ε • timeUnit)) = ε • timeUnit := by
  funext μ
  simp [imPart, toComplex]
theorem spacePart_timeUnit : spacePart timeUnit = 0 := by
  rw [timeUnit, spacePart_mkTimeSpace]
theorem timeUnit_zero : timeUnit 0 = 1 := by
  rw [timeUnit, mkTimeSpace_zero]
theorem boostMatrix_I_mul_point_formulas (x : RealVec4) (ε a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (v : unitSphere3) :
    imPart (boostMatrix v (I * a) *ᵥ (toComplex x + I • toComplex (ε • timeUnit))) =
          (ε * Real.cos a) • timeUnit +
            Real.sin a • (((v : Fin 3 → ℝ) ⬝ᵥ spacePart x) • timeUnit + x 0 • ofSpaceVector v) ∧
        tubeGap (boostMatrix v (I * a) *ᵥ (toComplex x + I • toComplex (ε • timeUnit))) =
          ε * Real.cos a + Real.sin a * ((v : Fin 3 → ℝ) ⬝ᵥ spacePart x - |x 0|) := by
  have hsin0 : 0 ≤ Real.sin a :=
    Real.sin_nonneg_of_nonneg_of_le_pi ha (ha1.trans (by linarith [Real.pi_gt_three]))
  have him : imPart (boostMatrix v (I * a) *ᵥ (toComplex x + I • toComplex (ε • timeUnit))) =
      mkTimeSpace (ε * Real.cos a + Real.sin a * ((v : Fin 3 → ℝ) ⬝ᵥ spacePart x))
        ((Real.sin a * x 0) • (v : Fin 3 → ℝ)) := by
    rw [imPart_boostMatrix_I_mul, imagBoostShift, rePart_toComplex_add_I_smul,
      imPart_toComplex_add_I_smul, spacePart_smul, spacePart_timeUnit]
    funext μ
    refine Fin.cases ?_ (fun i => ?_) μ
    · simp [mkTimeSpace, timeUnit]
      ring
    · simp [mkTimeSpace, timeUnit]
  constructor
  · rw [him]
    funext μ
    refine Fin.cases ?_ (fun i => ?_) μ
    · simp [mkTimeSpace, timeUnit, ofSpaceVector]
    · simp [mkTimeSpace, timeUnit, ofSpaceVector]
      ring
  · rw [tubeGap, him, coneGap, spacePart_mkTimeSpace, mkTimeSpace_zero, spaceNorm_smul,
      spaceNorm_unitSphere3, mul_one, abs_mul, abs_of_nonneg hsin0]
    ring
theorem tubeGapUnderImagBoosts_holds : TubeGapUnderImagBoosts :=
  ⟨tubeGap_boost_ge, fun x ε a _ ha ha1 v => boostMatrix_I_mul_point_formulas x ε a ha ha1 v⟩
theorem continuous_spaceNorm : Continuous spaceNorm := by
  unfold spaceNorm
  fun_prop
theorem continuous_spacePart : Continuous (spacePart : RealVec4 → Fin 3 → ℝ) := by
  unfold spacePart
  fun_prop
theorem spacelikeSet_eq : spacelikeSet = {x | |x 0| < spaceNorm (spacePart x)} := by
  ext x
  exact isSpacelikeVec_iff x
theorem isOpen_spacelikeSet : IsOpen spacelikeSet := by
  rw [spacelikeSet_eq]
  apply isOpen_lt
  · fun_prop
  · exact continuous_spaceNorm.comp continuous_spacePart
theorem continuous_mkTimeSpace {X : Type*} [TopologicalSpace X] {t : X → ℝ}
    {w : X → Fin 3 → ℝ} (ht : Continuous t) (hw : Continuous w) :
    Continuous fun p => (mkTimeSpace (t p) (w p) : RealVec4) := by
  apply continuous_pi
  intro μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · simpa [mkTimeSpace] using ht
  · have h := (continuous_apply i).comp hw
    simp only [mkTimeSpace, Fin.cons_succ]
    exact h
theorem spaceNorm_pos {v : Fin 3 → ℝ} (hv : v ≠ 0) : 0 < spaceNorm v := by
  rw [spaceNorm_eq_euclidean_norm, norm_pos_iff]
  intro h
  apply hv
  simpa using h
theorem isConnected_spacelikeSet : IsConnected spacelikeSet := by
  have hrank : 1 < Module.rank ℝ (Fin 3 → ℝ) := by
    rw [rank_fin_fun]
    norm_num
  have hS : IsConnected ({0}ᶜ : Set (Fin 3 → ℝ)) :=
    isConnected_compl_singleton_of_one_lt_rank hrank 0
  have hT : IsConnected (Set.Ioo (-1 : ℝ) 1) := by
    exact ⟨⟨0, by norm_num⟩, isPreconnected_Ioo⟩
  have hP := hS.prod hT
  let f : (Fin 3 → ℝ) × ℝ → RealVec4 := fun p => mkTimeSpace (p.2 * spaceNorm p.1) p.1
  have hf : Continuous f :=
    continuous_mkTimeSpace
      (continuous_snd.mul (continuous_spaceNorm.comp continuous_fst)) continuous_fst
  have himg : f '' (({0}ᶜ : Set (Fin 3 → ℝ)) ×ˢ Set.Ioo (-1 : ℝ) 1) = spacelikeSet := by
    rw [spacelikeSet_eq]
    ext x
    constructor
    · rintro ⟨⟨v, t⟩, ⟨hv, ht⟩, rfl⟩
      have hpos := spaceNorm_pos (v := v) hv
      show |(mkTimeSpace (t * spaceNorm v) v : RealVec4) 0| <
        spaceNorm (spacePart (mkTimeSpace (t * spaceNorm v) v : RealVec4))
      rw [mkTimeSpace_zero, spacePart_mkTimeSpace, abs_mul, abs_of_pos hpos]
      have : |t| < 1 := abs_lt.mpr ht
      nlinarith
    · intro hx
      have hx' : |x 0| < spaceNorm (spacePart x) := hx
      have hpos : 0 < spaceNorm (spacePart x) := (abs_nonneg _).trans_lt hx'
      refine ⟨(spacePart x, x 0 / spaceNorm (spacePart x)), ⟨?_, ?_⟩, ?_⟩
      · intro h0
        have h0' : spacePart x = 0 := h0
        rw [h0', spaceNorm_zero] at hpos
        exact lt_irrefl _ hpos
      · have : |x 0 / spaceNorm (spacePart x)| < 1 := by
          rw [abs_div, abs_of_pos hpos, div_lt_one hpos]
          exact hx'
        exact abs_lt.mp this
      · funext μ
        refine Fin.cases ?_ (fun i => ?_) μ
        · show (mkTimeSpace _ _ : RealVec4) 0 = _
          rw [mkTimeSpace_zero]
          field_simp
        · simp [f, mkTimeSpace, spacePart]
  rw [← himg]
  exact hP.image f hf.continuousOn
theorem spacelikeSetOpenConnected_holds : SpacelikeSetOpenConnected :=
  ⟨isOpen_spacelikeSet, isConnected_spacelikeSet⟩
def metricMatrix : ComplexMat4 := Matrix.diagonal ![1, -1, -1, -1]
theorem minkowskiForm_eq_dotProduct_metric (a b : ComplexVec4) :
    minkowskiForm a b = a ⬝ᵥ (metricMatrix *ᵥ b) := by
  rw [minkowskiForm_eq]
  simp [metricMatrix, dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_four]
  ring
theorem transpose_mul_metric_mul {Λ : ComplexMat4} (h : Λ ∈ lorentzGroupC) :
    Λᵀ * metricMatrix * Λ = metricMatrix := by
  have key : ∀ a b : ComplexVec4,
      a ⬝ᵥ ((Λᵀ * metricMatrix * Λ) *ᵥ b) = a ⬝ᵥ (metricMatrix *ᵥ b) := by
    intro a b
    rw [← minkowskiForm_eq_dotProduct_metric, ← h a b, minkowskiForm_eq_dotProduct_metric,
      mulVec_dotProduct_eq_dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  ext i j
  have := key (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single_one, single_one_dotProduct] using this
theorem det_metricMatrix : metricMatrix.det = -1 := by
  simp [metricMatrix, Matrix.det_diagonal, Fin.prod_univ_four]
theorem det_sq_of_mem_lorentzGroupC {Λ : ComplexMat4} (h : Λ ∈ lorentzGroupC) :
    Λ.det ^ 2 = 1 := by
  have := congrArg Matrix.det (transpose_mul_metric_mul h)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_metricMatrix] at this
  linear_combination -this
theorem isUnit_det_of_mem_lorentzGroupC {Λ : ComplexMat4} (h : Λ ∈ lorentzGroupC) :
    IsUnit Λ.det := by
  have h2 := det_sq_of_mem_lorentzGroupC h
  exact IsUnit.of_mul_eq_one Λ.det (by rw [← sq]; exact h2)
theorem one_mem_lorentzGroupC : (1 : ComplexMat4) ∈ lorentzGroupC := by
  intro ζ ζ'
  simp
theorem mul_mem_lorentzGroupC {A B : ComplexMat4} (hA : A ∈ lorentzGroupC)
    (hB : B ∈ lorentzGroupC) : A * B ∈ lorentzGroupC := by
  intro ζ ζ'
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hB]
theorem inv_mem_lorentzGroupC {A : ComplexMat4} (hA : A ∈ lorentzGroupC) :
    A⁻¹ ∈ lorentzGroupC := by
  intro ζ ζ'
  have h := hA (A⁻¹ *ᵥ ζ) (A⁻¹ *ᵥ ζ')
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_lorentzGroupC hA), Matrix.one_mulVec,
    Matrix.one_mulVec] at h
  exact h.symm
theorem lorentzGroupCIsGroup_holds : LorentzGroupCIsGroup :=
  ⟨fun _ h => (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_of_mem_lorentzGroupC h),
    one_mem_lorentzGroupC, fun _ hA _ hB => mul_mem_lorentzGroupC hA hB,
    fun _ hA => ⟨isUnit_det_of_mem_lorentzGroupC hA, inv_mem_lorentzGroupC hA⟩⟩
def realBoostMatrix (v : unitSphere3) (β : ℝ) : RealMat4 :=
  boostEntries (Real.cosh β) (Real.sinh β) (v : Fin 3 → ℝ)
theorem toComplexMatrix_realBoostMatrix (v : unitSphere3) (β : ℝ) :
    toComplexMatrix (realBoostMatrix v β) = boostMatrix v β := by
  rw [boostMatrix_eq_boostEntries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toComplexMatrix, realBoostMatrix, boostEntries]
def realRotationMatrix (R : Matrix.orthogonalGroup (Fin 3) ℝ) : RealMat4 :=
  !![1, 0, 0, 0;
     0, (R : Matrix (Fin 3) (Fin 3) ℝ) 0 0, (R : Matrix (Fin 3) (Fin 3) ℝ) 0 1,
       (R : Matrix (Fin 3) (Fin 3) ℝ) 0 2;
     0, (R : Matrix (Fin 3) (Fin 3) ℝ) 1 0, (R : Matrix (Fin 3) (Fin 3) ℝ) 1 1,
       (R : Matrix (Fin 3) (Fin 3) ℝ) 1 2;
     0, (R : Matrix (Fin 3) (Fin 3) ℝ) 2 0, (R : Matrix (Fin 3) (Fin 3) ℝ) 2 1,
       (R : Matrix (Fin 3) (Fin 3) ℝ) 2 2]
theorem realRotationMatrix_zero_zero (R : Matrix.orthogonalGroup (Fin 3) ℝ) :
    realRotationMatrix R 0 0 = 1 := by
  simp [realRotationMatrix]
theorem realRotationMatrix_zero_succ (R : Matrix.orthogonalGroup (Fin 3) ℝ) (j : Fin 3) :
    realRotationMatrix R 0 j.succ = 0 := by
  fin_cases j <;> simp [realRotationMatrix]
theorem realRotationMatrix_succ_zero (R : Matrix.orthogonalGroup (Fin 3) ℝ) (i : Fin 3) :
    realRotationMatrix R i.succ 0 = 0 := by
  fin_cases i <;> simp [realRotationMatrix]
theorem realRotationMatrix_succ_succ (R : Matrix.orthogonalGroup (Fin 3) ℝ) (i j : Fin 3) :
    realRotationMatrix R i.succ j.succ = (R : Matrix (Fin 3) (Fin 3) ℝ) i j := by
  fin_cases i <;> fin_cases j <;> simp [realRotationMatrix]
theorem realRotationMatrix_mulVec_zero (R : Matrix.orthogonalGroup (Fin 3) ℝ) (y : RealVec4) :
    (realRotationMatrix R *ᵥ y) 0 = y 0 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, realRotationMatrix_zero_zero,
    realRotationMatrix_zero_succ]
theorem realRotationMatrix_mulVec_succ (R : Matrix.orthogonalGroup (Fin 3) ℝ) (y : RealVec4)
    (i : Fin 3) :
    (realRotationMatrix R *ᵥ y) i.succ = ((R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ spacePart y) i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ (n := 3), realRotationMatrix_succ_zero,
    realRotationMatrix_succ_succ, spacePart]
  simp
theorem toComplexMatrix_realRotationMatrix (R : Matrix.orthogonalGroup (Fin 3) ℝ) :
    toComplexMatrix (realRotationMatrix R) = rotationMatrix R := by
  apply ext_of_mulVec_eq
  intro ζ
  rw [rotationMatrix_mulVec]
  funext μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · rw [rotationLinearMap_apply_zero]
    simp [toComplexMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ (n := 3),
      realRotationMatrix_zero_zero, realRotationMatrix_zero_succ]
  · rw [rotationLinearMap_apply_succ]
    simp [toComplexMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ (n := 3),
      realRotationMatrix_succ_zero, realRotationMatrix_succ_succ]
theorem orthogonal3_transpose_mul_self (R : Matrix.orthogonalGroup (Fin 3) ℝ) :
    (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (R : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  have := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp R.2
  simpa [Matrix.star_eq_conjTranspose] using this
theorem rotationMatrix_mem_lorentzGroupC (R : Matrix.orthogonalGroup (Fin 3) ℝ) :
    rotationMatrix R ∈ lorentzGroupC := by
  intro ζ ζ'
  rw [rotationMatrix_mulVec, rotationMatrix_mulVec]
  set C : Matrix (Fin 3) (Fin 3) ℂ := (R : Matrix (Fin 3) (Fin 3) ℝ).map fun r => (r : ℂ) with hC
  have hCC : Cᵀ * C = 1 := by
    ext i j
    have := congrFun (congrFun (orthogonal3_transpose_mul_self R) i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at this
    simp only [hC, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) this
    simp only [Complex.ofReal_sum, Complex.ofReal_mul] at h2
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hs : ∀ z : ComplexVec4, spacePart (rotationLinearMap R z) = C *ᵥ spacePart z := fun z => by
    show spacePart (mkTimeSpace _ _) = _
    exact spacePart_mkTimeSpace _ _
  have hd : spaceBilin (C *ᵥ spacePart ζ) (C *ᵥ spacePart ζ') =
      spaceBilin (spacePart ζ) (spacePart ζ') := by
    show (C *ᵥ spacePart ζ) ⬝ᵥ (C *ᵥ spacePart ζ') = spacePart ζ ⬝ᵥ spacePart ζ'
    have hdot : ∀ a b : Fin 3 → ℂ, (C *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (Cᵀ *ᵥ b) := by
      intro a b
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [hdot, Matrix.mulVec_mulVec, hCC, Matrix.one_mulVec]
  simp only [minkowskiForm, hs, rotationLinearMap_apply_zero, hd]
theorem det_toComplexMatrix (A : RealMat4) : (toComplexMatrix A).det = (A.det : ℂ) :=
  (Complex.ofRealHom.map_det A).symm
theorem det_sq_of_toComplexMatrix_mem {A : RealMat4} (h : toComplexMatrix A ∈ lorentzGroupC) :
    A.det ^ 2 = 1 := by
  have := det_sq_of_mem_lorentzGroupC h
  rw [det_toComplexMatrix] at this
  exact_mod_cast this
theorem eq_one_of_sq_eq_one_of_nonneg {x : ℝ} (h : x ^ 2 = 1) (h0 : 0 ≤ x) : x = 1 := by
  have : (x - 1) * (x + 1) = 0 := by
    ring_nf
    linarith
  rcases mul_eq_zero.mp this with h1 | h1 <;> linarith
theorem toComplexMatrix_realBoostMatrix_mem (v : unitSphere3) (β : ℝ) :
    toComplexMatrix (realBoostMatrix v β) ∈ lorentzGroupC := by
  rw [toComplexMatrix_realBoostMatrix]
  exact boostMatrix_mem_lorentzGroupC v _
theorem realBoostMatrix_mul (v : unitSphere3) (β β' : ℝ) :
    realBoostMatrix v β * realBoostMatrix v β' = realBoostMatrix v (β + β') := by
  apply toComplexMatrix_injective
  rw [toComplexMatrix_mul, toComplexMatrix_realBoostMatrix, toComplexMatrix_realBoostMatrix,
    toComplexMatrix_realBoostMatrix, boostMatrix_mul]
  push_cast
  rfl
theorem realBoostMatrix_zero (v : unitSphere3) : realBoostMatrix v 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realBoostMatrix, boostEntries]
theorem det_realBoostMatrix (v : unitSphere3) (β : ℝ) : (realBoostMatrix v β).det = 1 := by
  have h : realBoostMatrix v β = realBoostMatrix v (β / 2) * realBoostMatrix v (β / 2) := by
    rw [realBoostMatrix_mul]
    congr 1
    ring
  apply eq_one_of_sq_eq_one_of_nonneg
    (det_sq_of_toComplexMatrix_mem (toComplexMatrix_realBoostMatrix_mem v β))
  rw [h, Matrix.det_mul]
  exact mul_self_nonneg _
theorem det_realRotationMatrix (R : Matrix.orthogonalGroup (Fin 3) ℝ) :
    (realRotationMatrix R).det = (R : Matrix (Fin 3) (Fin 3) ℝ).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [realRotationMatrix_zero_succ, realRotationMatrix_zero_zero]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  simp only [Fin.val_zero, pow_zero, one_mul]
  congr 1
  ext i j
  have e : (Fin.succAbove (0 : Fin 4) j) = j.succ := rfl
  simp only [Matrix.submatrix_apply, e, realRotationMatrix_succ_succ]
theorem realRotationMatrix_mul (R R' : Matrix.orthogonalGroup (Fin 3) ℝ) :
    realRotationMatrix R * realRotationMatrix R' = realRotationMatrix (R * R') := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp [Matrix.mul_apply, Fin.sum_univ_succ (n := 3), realRotationMatrix_zero_zero,
      realRotationMatrix_zero_succ, realRotationMatrix_succ_zero]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ (n := 3), realRotationMatrix_zero_zero,
      realRotationMatrix_zero_succ]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ (n := 3), realRotationMatrix_zero_zero,
      realRotationMatrix_succ_zero]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ (n := 3), realRotationMatrix_zero_succ,
      realRotationMatrix_succ_zero, realRotationMatrix_succ_succ]
theorem realRotationMatrix_one : realRotationMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realRotationMatrix]
theorem realRotationMatrix_mul_inv (R : Matrix.orthogonalGroup (Fin 3) ℝ) :
    realRotationMatrix R * realRotationMatrix R⁻¹ = 1 := by
  rw [realRotationMatrix_mul, mul_inv_cancel, realRotationMatrix_one]
theorem realRotationMatrix_inv_mul (R : Matrix.orthogonalGroup (Fin 3) ℝ) :
    realRotationMatrix R⁻¹ * realRotationMatrix R = 1 := by
  rw [realRotationMatrix_mul, inv_mul_cancel, realRotationMatrix_one]
theorem toComplexMatrix_realRotationMatrix_mem (R : Matrix.orthogonalGroup (Fin 3) ℝ) :
    toComplexMatrix (realRotationMatrix R) ∈ lorentzGroupC := by
  rw [toComplexMatrix_realRotationMatrix]
  exact rotationMatrix_mem_lorentzGroupC R
theorem realMinkowskiForm_mulVec {A : RealMat4} (h : toComplexMatrix A ∈ lorentzGroupC)
    (a b : RealVec4) : realMinkowskiForm (A *ᵥ a) (A *ᵥ b) = realMinkowskiForm a b := by
  have := h (toComplex a) (toComplex b)
  rw [toComplexMatrix_mulVec, toComplexMatrix_mulVec, minkowskiForm_toComplex,
    minkowskiForm_toComplex] at this
  exact_mod_cast this
theorem mem_futureCone_iff (y : RealVec4) :
    y ∈ futureCone ↔ 0 < y 0 ∧ 0 < realMinkowskiForm y y := by
  have hn := spaceNorm_nonneg (spacePart y)
  rw [realMinkowskiForm_self]
  show coneGap y > 0 ↔ _
  simp only [coneGap]
  constructor
  · intro h
    exact ⟨by linarith, by nlinarith⟩
  · rintro ⟨h0, h1⟩
    by_contra hc
    have : y 0 ≤ spaceNorm (spacePart y) := by linarith
    nlinarith
def MapsFutureCone (A : RealMat4) : Prop := ∀ y ∈ futureCone, A *ᵥ y ∈ futureCone
theorem MapsFutureCone.mul {A B : RealMat4} (hA : MapsFutureCone A) (hB : MapsFutureCone B) :
    MapsFutureCone (A * B) := by
  intro y hy
  rw [← Matrix.mulVec_mulVec]
  exact hA _ (hB _ hy)
theorem realBoostMatrix_mulVec_zero (v : unitSphere3) (β : ℝ) (y : RealVec4) :
    (realBoostMatrix v β *ᵥ y) 0 =
      Real.cosh β * y 0 + Real.sinh β * ((v : Fin 3 → ℝ) ⬝ᵥ spacePart y) := by
  simp [realBoostMatrix, boostEntries, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    Fin.sum_univ_three, spacePart]
  ring
theorem mapsFutureCone_realBoostMatrix (v : unitSphere3) (β : ℝ) :
    MapsFutureCone (realBoostMatrix v β) := by
  intro y hy
  have hy' := (mem_futureCone_iff y).mp hy
  have hm : coneGap y > 0 := hy
  rw [mem_futureCone_iff, realMinkowskiForm_mulVec (toComplexMatrix_realBoostMatrix_mem v β),
    realBoostMatrix_mulVec_zero]
  refine ⟨?_, hy'.2⟩
  have hd := abs_unit_dotProduct_le v (spacePart y)
  have hc := Real.cosh_pos β
  have hs : |Real.sinh β| ≤ Real.cosh β := by
    rw [abs_le]
    have h1 := Real.sinh_lt_cosh β
    have h2 := Real.sinh_lt_cosh (-β)
    rw [Real.sinh_neg, Real.cosh_neg] at h2
    constructor <;> linarith
  have hb : |Real.sinh β * ((v : Fin 3 → ℝ) ⬝ᵥ spacePart y)| ≤
      Real.cosh β * spaceNorm (spacePart y) := by
    rw [abs_mul]
    exact mul_le_mul hs hd (abs_nonneg _) hc.le
  have := (abs_le.mp hb).1
  simp only [coneGap] at hm
  nlinarith [mul_pos hc hm]
theorem mapsFutureCone_realRotationMatrix (R : Matrix.orthogonalGroup (Fin 3) ℝ) :
    MapsFutureCone (realRotationMatrix R) := by
  intro y hy
  have hy' := (mem_futureCone_iff y).mp hy
  rw [mem_futureCone_iff, realMinkowskiForm_mulVec (toComplexMatrix_realRotationMatrix_mem R),
    realRotationMatrix_mulVec_zero]
  exact hy'
theorem timeUnit_mem_futureCone : timeUnit ∈ futureCone := by
  show coneGap timeUnit > 0
  rw [coneGap, spacePart_timeUnit, spaceNorm_zero, timeUnit_zero]
  norm_num
theorem realMinkowskiForm_timeUnit (a : RealVec4) : realMinkowskiForm timeUnit a = a 0 := by
  simp [realMinkowskiForm, spacePart_timeUnit, timeUnit_zero]
theorem mem_restrictedLorentz_of_mapsFutureCone {A : RealMat4}
    (hL : toComplexMatrix A ∈ lorentzGroupC) (hdet : A.det = 1) (hF : MapsFutureCone A) :
    A ∈ restrictedLorentz := by
  refine ⟨hL, hdet, ?_⟩
  rw [toComplexMatrix_mulVec, minkowskiForm_toComplex, Complex.ofReal_re,
    realMinkowskiForm_timeUnit]
  have h := (mem_futureCone_iff _).mp (hF _ timeUnit_mem_futureCone)
  have hq := realMinkowskiForm_mulVec hL timeUnit timeUnit
  rw [realMinkowskiForm_timeUnit, timeUnit_zero, realMinkowskiForm_self] at hq
  nlinarith [sq_nonneg (spaceNorm (spacePart (A *ᵥ timeUnit))), h.1]
theorem image_mulVec_eq_of_mul_eq_one {A B : RealMat4} {S : Set RealVec4}
    (hA : ∀ y ∈ S, A *ᵥ y ∈ S) (hB : ∀ y ∈ S, B *ᵥ y ∈ S) (hAB : A * B = 1) :
    (fun y => A *ᵥ y) '' S = S := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact hA y hy
  · intro y hy
    refine ⟨B *ᵥ y, hB y hy, ?_⟩
    show A *ᵥ (B *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
theorem realBoostsRotationsRestricted_holds : RealBoostsRotationsRestricted := by
  constructor
  · intro v β
    refine ⟨realBoostMatrix v β,
      mem_restrictedLorentz_of_mapsFutureCone (toComplexMatrix_realBoostMatrix_mem v β)
        (det_realBoostMatrix v β) (mapsFutureCone_realBoostMatrix v β),
      toComplexMatrix_realBoostMatrix v β, ?_⟩
    refine image_mulVec_eq_of_mul_eq_one (mapsFutureCone_realBoostMatrix v β)
      (mapsFutureCone_realBoostMatrix v (-β)) ?_
    rw [realBoostMatrix_mul, add_neg_cancel, realBoostMatrix_zero]
  · intro R hR
    refine ⟨realRotationMatrix R,
      mem_restrictedLorentz_of_mapsFutureCone (toComplexMatrix_realRotationMatrix_mem R)
        (by rw [det_realRotationMatrix, hR]) (mapsFutureCone_realRotationMatrix R),
      toComplexMatrix_realRotationMatrix R, ?_⟩
    exact image_mulVec_eq_of_mul_eq_one (mapsFutureCone_realRotationMatrix R)
      (mapsFutureCone_realRotationMatrix R⁻¹) (realRotationMatrix_mul_inv R)
theorem isUnitVec_of_unitSphere3 (v : unitSphere3) :
    YangMills.Construction.WightmanReconstruction.SmoothToolkit.IsUnitVec (v : Fin 3 → ℝ) := by
  have hv := unitSphere3_sum_sq v
  have h : (v : Fin 3 → ℝ) ⬝ᵥ (v : Fin 3 → ℝ) = 1 := by
    simp only [dotProduct, Fin.sum_univ_three]
    linarith
  simp [YangMills.Construction.WightmanReconstruction.SmoothToolkit.IsUnitVec,
    YangMills.Construction.WightmanReconstruction.SmoothToolkit.vecLength, h]
theorem exists_unit_direction (w : Fin 3 → ℝ) :
    ∃ n : unitSphere3, w = spaceNorm w • (n : Fin 3 → ℝ) := by
  by_cases hw : w = 0
  · exact ⟨spaceAxisOne, by simp [hw, spaceNorm_zero]⟩
  · have hpos := spaceNorm_pos hw
    refine ⟨⟨(spaceNorm w)⁻¹ • w, ?_⟩, ?_⟩
    · show spaceNorm _ = 1
      rw [spaceNorm_smul, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
    · simp [smul_smul, mul_inv_cancel₀ hpos.ne']
theorem timeUnit_eq_single : timeUnit = Pi.single 0 1 := by
  funext μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp [timeUnit, mkTimeSpace]
  · simp [timeUnit, mkTimeSpace]
theorem realBoostMatrix_mulVec_timeUnit (v : unitSphere3) (β : ℝ) :
    realBoostMatrix v β *ᵥ timeUnit =
      mkTimeSpace (Real.cosh β) (Real.sinh β • (v : Fin 3 → ℝ)) := by
  rw [timeUnit_eq_single, Matrix.mulVec_single_one]
  funext μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp [realBoostMatrix, boostEntries, mkTimeSpace]
  · show _ = (Real.sinh β • (v : Fin 3 → ℝ)) i
    fin_cases i <;> simp [realBoostMatrix, boostEntries]
theorem spacePart_single_succ (i : Fin 3) :
    spacePart (Pi.single i.succ 1 : RealVec4) = Pi.single i 1 := by
  funext k
  simp [spacePart, Pi.single_apply, Fin.succ_inj]
theorem restrictedLorentz_decomposition_real
    (hrot : YangMills.Construction.WightmanReconstruction.SmoothToolkit.PlaneRotationsAndTransitivity)
    {Λ : RealMat4} (hΛ : Λ ∈ restrictedLorentz) :
    ∃ R₁ R₂ : Matrix.orthogonalGroup (Fin 3) ℝ, ∃ β : ℝ,
      (R₁ : Matrix (Fin 3) (Fin 3) ℝ).det = 1 ∧ (R₂ : Matrix (Fin 3) (Fin 3) ℝ).det = 1 ∧ 0 ≤ β ∧
        Λ = realRotationMatrix R₁ * realBoostMatrix spaceAxisOne β * realRotationMatrix R₂ := by
  obtain ⟨hL, hdet, hge⟩ := hΛ
  rw [toComplexMatrix_mulVec, minkowskiForm_toComplex, Complex.ofReal_re,
    realMinkowskiForm_timeUnit] at hge
  set y := Λ *ᵥ timeUnit with hy
  have hq : realMinkowskiForm y y = 1 := by
    rw [hy, realMinkowskiForm_mulVec hL, realMinkowskiForm_timeUnit, timeUnit_zero]
  rw [realMinkowskiForm_self] at hq
  obtain ⟨n, hn⟩ := exists_unit_direction (spacePart y)
  set r := spaceNorm (spacePart y) with hr
  have hr0 : 0 ≤ r := spaceNorm_nonneg _
  set β := Real.arsinh r with hβ
  have hβ0 : 0 ≤ β := Real.arsinh_nonneg_iff.mpr hr0
  have hsinh : Real.sinh β = r := Real.sinh_arsinh r
  have hcosh : Real.cosh β = y 0 := by
    rw [hβ, Real.cosh_arsinh, show 1 + r ^ 2 = y 0 ^ 2 by linarith, Real.sqrt_sq (by linarith)]
  obtain ⟨R, hRmem, hRe⟩ := (hrot 3 (Or.inl rfl)).2 _ _ (isUnitVec_of_unitSphere3 spaceAxisOne)
    (isUnitVec_of_unitSphere3 n)
  obtain ⟨hRo, hRd⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp hRmem
  let R₁ : Matrix.orthogonalGroup (Fin 3) ℝ := ⟨R, hRo⟩
  have hR₁ : (R₁ : Matrix (Fin 3) (Fin 3) ℝ) = R := rfl
  set G := realRotationMatrix R₁ * realBoostMatrix spaceAxisOne β with hG
  set G' := realBoostMatrix spaceAxisOne (-β) * realRotationMatrix R₁⁻¹ with hG'
  have hG'G : G' * G = 1 := by
    rw [hG, hG', Matrix.mul_assoc, ← Matrix.mul_assoc (realRotationMatrix R₁⁻¹),
      realRotationMatrix_inv_mul, Matrix.one_mul, realBoostMatrix_mul, neg_add_cancel,
      realBoostMatrix_zero]
  have hGG' : G * G' = 1 := by
    rw [hG, hG', Matrix.mul_assoc, ← Matrix.mul_assoc (realBoostMatrix spaceAxisOne β),
      realBoostMatrix_mul, add_neg_cancel, realBoostMatrix_zero, Matrix.one_mul,
      realRotationMatrix_mul_inv]
  have hGe : G *ᵥ timeUnit = y := by
    rw [hG, ← Matrix.mulVec_mulVec, realBoostMatrix_mulVec_timeUnit]
    funext μ
    refine Fin.cases ?_ (fun i => ?_) μ
    · rw [realRotationMatrix_mulVec_zero, mkTimeSpace_zero, hcosh]
    · rw [realRotationMatrix_mulVec_succ, spacePart_mkTimeSpace, Matrix.mulVec_smul, hR₁, hRe,
        hsinh]
      exact (congrFun hn i).symm
  set M := G' * Λ with hM
  have hMe : M *ᵥ timeUnit = timeUnit := by
    rw [hM, ← Matrix.mulVec_mulVec, ← hy, ← hGe, Matrix.mulVec_mulVec, hG'G, Matrix.one_mulVec]
  have hML : toComplexMatrix M ∈ lorentzGroupC := by
    rw [hM, hG', toComplexMatrix_mul, toComplexMatrix_mul]
    exact mul_mem_lorentzGroupC
      (mul_mem_lorentzGroupC (toComplexMatrix_realBoostMatrix_mem _ _)
        (toComplexMatrix_realRotationMatrix_mem _)) hL
  have hdetG : G.det = 1 := by
    rw [hG, Matrix.det_mul, det_realBoostMatrix, det_realRotationMatrix, hR₁, hRd, one_mul]
  have hdetM : M.det = 1 := by
    have h1 : G'.det * G.det = 1 := by rw [← Matrix.det_mul, hG'G, Matrix.det_one]
    rw [hdetG, mul_one] at h1
    rw [hM, Matrix.det_mul, hdet, mul_one, h1]
  have htime : ∀ a, (M *ᵥ a) 0 = a 0 := by
    intro a
    have h := realMinkowskiForm_mulVec hML timeUnit a
    rwa [hMe, realMinkowskiForm_timeUnit, realMinkowskiForm_timeUnit] at h
  have hrow : ∀ j : Fin 3, M 0 j.succ = 0 := by
    intro j
    have h := htime (Pi.single j.succ 1)
    simpa [Matrix.mulVec_single_one] using h
  have hcolumn : ∀ μ, M μ 0 = timeUnit μ := by
    intro μ
    have h := congrFun hMe μ
    rw [timeUnit_eq_single, Matrix.mulVec_single_one] at h
    rw [timeUnit_eq_single]
    exact h
  have hcol : ∀ i : Fin 3, M i.succ 0 = 0 := by
    intro i
    rw [hcolumn, timeUnit_eq_single]
    simp
  have h00 : M 0 0 = 1 := by
    rw [hcolumn, timeUnit_zero]
  let P : Matrix (Fin 3) (Fin 3) ℝ := fun i j => M i.succ j.succ
  have hP : Pᵀ * P = 1 := by
    ext i j
    have h := realMinkowskiForm_mulVec hML (Pi.single i.succ 1) (Pi.single j.succ 1)
    rw [realMinkowskiForm, realMinkowskiForm, htime, htime, spacePart_single_succ,
      spacePart_single_succ, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    have hc : ∀ k : Fin 3, spacePart (M.col k.succ) = fun l => P l k := fun k => rfl
    rw [hc, hc] at h
    simp only [Pi.single_apply, single_one_dotProduct] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    simp only [dotProduct] at h
    exact sub_right_injective h
  have hmem : P ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mpr
      (by simpa [Matrix.star_eq_conjTranspose] using hP)
  let R₂ : Matrix.orthogonalGroup (Fin 3) ℝ := ⟨P, hmem⟩
  have hMR : M = realRotationMatrix R₂ := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rw [realRotationMatrix_zero_zero]
      exact h00
    · rw [realRotationMatrix_zero_succ]
      exact hrow j
    · rw [realRotationMatrix_succ_zero]
      exact hcol i
    · rw [realRotationMatrix_succ_succ]
  refine ⟨R₁, R₂, β, hRd, ?_, hβ0, ?_⟩
  · rw [← det_realRotationMatrix, ← hMR]
    exact hdetM
  · rw [← hMR, hM, ← Matrix.mul_assoc, hGG', Matrix.one_mul]
theorem restrictedLorentzDecomposition_holds
    (hrot : YangMills.Construction.WightmanReconstruction.SmoothToolkit.PlaneRotationsAndTransitivity) :
    RestrictedLorentzDecomposition := by
  intro Λ hΛ
  obtain ⟨R₁, R₂, β, h1, h2, h0, h⟩ := restrictedLorentz_decomposition_real hrot hΛ
  refine ⟨R₁, R₂, β, h1, h2, h0, ?_⟩
  rw [h, toComplexMatrix_mul, toComplexMatrix_mul, toComplexMatrix_realRotationMatrix,
    toComplexMatrix_realRotationMatrix, toComplexMatrix_realBoostMatrix]
theorem mapsFutureCone_of_mem_restrictedLorentz
    (hrot : YangMills.Construction.WightmanReconstruction.SmoothToolkit.PlaneRotationsAndTransitivity)
    {Λ : RealMat4} (hΛ : Λ ∈ restrictedLorentz) : MapsFutureCone Λ ∧ MapsFutureCone Λ⁻¹ := by
  obtain ⟨R₁, R₂, β, -, -, -, h⟩ := restrictedLorentz_decomposition_real hrot hΛ
  have hW : Λ * (realRotationMatrix R₂⁻¹ * realBoostMatrix spaceAxisOne (-β) *
      realRotationMatrix R₁⁻¹) = 1 := by
    rw [h]
    calc realRotationMatrix R₁ * realBoostMatrix spaceAxisOne β * realRotationMatrix R₂ *
          (realRotationMatrix R₂⁻¹ * realBoostMatrix spaceAxisOne (-β) * realRotationMatrix R₁⁻¹)
        = realRotationMatrix R₁ * (realBoostMatrix spaceAxisOne β *
            (realRotationMatrix R₂ * realRotationMatrix R₂⁻¹) *
            realBoostMatrix spaceAxisOne (-β)) * realRotationMatrix R₁⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [realRotationMatrix_mul_inv, Matrix.mul_one, realBoostMatrix_mul, add_neg_cancel,
            realBoostMatrix_zero, Matrix.mul_one, realRotationMatrix_mul_inv]
  rw [Matrix.inv_eq_right_inv hW, h]
  exact ⟨((mapsFutureCone_realRotationMatrix R₁).mul (mapsFutureCone_realBoostMatrix _ β)).mul
      (mapsFutureCone_realRotationMatrix R₂),
    ((mapsFutureCone_realRotationMatrix R₂⁻¹).mul (mapsFutureCone_realBoostMatrix _ (-β))).mul
      (mapsFutureCone_realRotationMatrix R₁⁻¹)⟩
theorem mul_inv_of_mem_restrictedLorentz {Λ : RealMat4} (hΛ : Λ ∈ restrictedLorentz) :
    Λ * Λ⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (by rw [hΛ.2.1]; exact isUnit_one)
theorem inv_mul_of_mem_restrictedLorentz {Λ : RealMat4} (hΛ : Λ ∈ restrictedLorentz) :
    Λ⁻¹ * Λ = 1 :=
  Matrix.nonsing_inv_mul _ (by rw [hΛ.2.1]; exact isUnit_one)
theorem one_mem_restrictedLorentz : (1 : RealMat4) ∈ restrictedLorentz := by apply _root_.YangMills.Construction.WightmanTheory.one_mem_restrictedLorentz <;> assumption
theorem mul_mem_restrictedLorentz
    (hrot : YangMills.Construction.WightmanReconstruction.SmoothToolkit.PlaneRotationsAndTransitivity)
    {A B : RealMat4} (hA : A ∈ restrictedLorentz) (hB : B ∈ restrictedLorentz) :
    A * B ∈ restrictedLorentz := by
  refine mem_restrictedLorentz_of_mapsFutureCone
    (by rw [toComplexMatrix_mul]; exact mul_mem_lorentzGroupC hA.1 hB.1) ?_
    ((mapsFutureCone_of_mem_restrictedLorentz hrot hA).1.mul
      (mapsFutureCone_of_mem_restrictedLorentz hrot hB).1)
  rw [Matrix.det_mul, hA.2.1, hB.2.1, one_mul]
theorem inv_mem_restrictedLorentz
    (hrot : YangMills.Construction.WightmanReconstruction.SmoothToolkit.PlaneRotationsAndTransitivity)
    {A : RealMat4} (hA : A ∈ restrictedLorentz) : A⁻¹ ∈ restrictedLorentz := by
  have hc : toComplexMatrix A⁻¹ = (toComplexMatrix A)⁻¹ := by
    apply (Matrix.inv_eq_right_inv _).symm
    rw [← toComplexMatrix_mul, mul_inv_of_mem_restrictedLorentz hA, toComplexMatrix_one]
  refine mem_restrictedLorentz_of_mapsFutureCone (by rw [hc]; exact inv_mem_lorentzGroupC hA.1) ?_
    (mapsFutureCone_of_mem_restrictedLorentz hrot hA).2
  have h := congrArg Matrix.det (mul_inv_of_mem_restrictedLorentz hA)
  rwa [Matrix.det_mul, hA.2.1, one_mul, Matrix.det_one] at h
theorem mapsClosedFutureCone_of_mapsFutureCone {A : RealMat4} (hF : MapsFutureCone A) :
    ∀ y ∈ closedFutureCone, A *ᵥ y ∈ closedFutureCone := by
  intro y hy
  have hy' : coneGap y ≥ 0 := hy
  set w := A *ᵥ timeUnit with hw
  set K := |w 0| + spaceNorm (spacePart w) with hK
  have hK0 : 0 ≤ K := add_nonneg (abs_nonneg _) (spaceNorm_nonneg _)
  have key : ∀ t : ℝ, 0 < t → coneGap (A *ᵥ y) ≥ -(t * K) := by
    intro t ht
    have hmem : y + t • timeUnit ∈ futureCone := by
      show coneGap (y + t • timeUnit) > 0
      have h1 := coneGap_superadditive y (t • timeUnit)
      rw [coneGap_smul ht.le] at h1
      have h2 : coneGap timeUnit = 1 := by
        rw [coneGap, spacePart_timeUnit, spaceNorm_zero, timeUnit_zero, sub_zero]
      rw [h2] at h1
      linarith
    have h1 : coneGap (A *ᵥ y + t • w) > 0 := by
      have h := hF _ hmem
      rw [Matrix.mulVec_add, Matrix.mulVec_smul] at h
      exact h
    have h2 := coneGap_add_ge_sub (A *ᵥ y + t • w) (-(t • w))
    rw [add_neg_cancel_right] at h2
    have h3 : |(-(t • w)) 0| = t * |w 0| := by
      simp [abs_mul, abs_of_pos ht]
    have h4 : spaceNorm (spacePart (-(t • w))) = t * spaceNorm (spacePart w) := by
      have : spacePart (-(t • w)) = -(t • spacePart w) := rfl
      rw [this, spaceNorm_neg, spaceNorm_smul, abs_of_pos ht]
    rw [h3, h4] at h2
    rw [hK]
    nlinarith
  show coneGap (A *ᵥ y) ≥ 0
  by_contra hc
  set d := -coneGap (A *ᵥ y) with hd
  have hd0 : 0 < d := by linarith
  have ht : 0 < d / (K + 1) := div_pos hd0 (by linarith)
  have h := key _ ht
  have e : d / (K + 1) * K < d := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  linarith
theorem imPart_toComplexMatrix_mulVec (A : RealMat4) (ζ : ComplexVec4) :
    imPart (toComplexMatrix A *ᵥ ζ) = A *ᵥ imPart ζ := by
  funext μ
  simp [imPart, toComplexMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
theorem restrictedLorentzGroupPreserves_holds
    (hrot : YangMills.Construction.WightmanReconstruction.SmoothToolkit.PlaneRotationsAndTransitivity) :
    RestrictedLorentzGroupPreserves := by
  refine ⟨⟨one_mem_restrictedLorentz, fun _ hA _ hB => mul_mem_restrictedLorentz hrot hA hB,
    fun A hA => ⟨?_, inv_mem_restrictedLorentz hrot hA⟩⟩, ?_⟩
  · rw [hA.2.1]
    exact isUnit_one
  · intro Λ hΛ
    obtain ⟨hF, hF'⟩ := mapsFutureCone_of_mem_restrictedLorentz hrot hΛ
    refine ⟨image_mulVec_eq_of_mul_eq_one hF hF' (mul_inv_of_mem_restrictedLorentz hΛ),
      image_mulVec_eq_of_mul_eq_one (mapsClosedFutureCone_of_mapsFutureCone hF)
        (mapsClosedFutureCone_of_mapsFutureCone hF') (mul_inv_of_mem_restrictedLorentz hΛ),
      ?_, ?_⟩
    · apply Set.Subset.antisymm
      · rintro _ ⟨ζ, hζ, rfl⟩
        show imPart _ ∈ futureCone
        rw [imPart_toComplexMatrix_mulVec]
        exact hF _ hζ
      · intro ζ hζ
        refine ⟨toComplexMatrix Λ⁻¹ *ᵥ ζ, ?_, ?_⟩
        · show imPart _ ∈ futureCone
          rw [imPart_toComplexMatrix_mulVec]
          exact hF' _ hζ
        · show toComplexMatrix Λ *ᵥ (toComplexMatrix Λ⁻¹ *ᵥ ζ) = ζ
          rw [Matrix.mulVec_mulVec, ← toComplexMatrix_mul, mul_inv_of_mem_restrictedLorentz hΛ,
            toComplexMatrix_one, Matrix.one_mulVec]
    · rw [hΛ.2.1, abs_one]
theorem poincareGroupAction_holds
    (hrot : YangMills.Construction.WightmanReconstruction.SmoothToolkit.PlaneRotationsAndTransitivity) :
    PoincareGroupAction := by
  refine ⟨⟨trivial, one_mem_restrictedLorentz⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg g' hg'
    exact ⟨trivial, mul_mem_restrictedLorentz hrot hg.2 hg'.2⟩
  · intro g _ g' _ g'' _
    simp only [poincareMul]
    refine Prod.ext ?_ (Matrix.mul_assoc _ _ _)
    simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]
  · intro g _
    constructor
    · simp [poincareMul]
    · simp [poincareMul]
  · intro g hg
    have h1 := mul_inv_of_mem_restrictedLorentz hg.2
    have h2 := inv_mul_of_mem_restrictedLorentz hg.2
    refine ⟨⟨trivial, inv_mem_restrictedLorentz hrot hg.2⟩, ?_, ?_⟩
    · simp only [poincareMul, poincareInv]
      rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, add_neg_cancel]
    · simp only [poincareMul, poincareInv]
      rw [h2, neg_add_cancel]
  · intro g _ g' _ x
    simp only [poincareMul, poincareSMul, Matrix.mulVec_add, Matrix.mulVec_mulVec]
    abel
theorem statement_of_toolkit (h : YangMills.Construction.WightmanReconstruction.SmoothToolkit.Toolkit) :
    Statement := by
  obtain ⟨-, -, -, -, -, hrot, -, -⟩ := h
  exact ⟨coneGapBounds_holds, conesTubeConvex_holds, formOnClosedCone_holds,
    wickMapFormulas_holds, boostsAndRotations_holds hrot, tubeGapUnderImagBoosts_holds,
    realBoostsRotationsRestricted_holds, restrictedLorentzDecomposition_holds hrot,
    restrictedLorentzGroupPreserves_holds hrot, lorentzGroupCIsGroup_holds,
    poincareGroupAction_holds hrot, spacelikeSetOpenConnected_holds⟩
end YangMills.Construction.MinkowskiSpace.ConeTubeLorentz
end
