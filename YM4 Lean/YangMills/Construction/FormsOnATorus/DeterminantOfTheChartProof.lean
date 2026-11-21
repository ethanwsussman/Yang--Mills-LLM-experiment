import YangMills.Construction.FormsOnATorus.DeterminantNearOne
import YangMills.Construction.FormsOnATorus.DeterminantOfTheChart
import YangMills.Construction.FormsOnATorus.FactsOfTheHalfChart
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Matrix
open scoped Quaternion
namespace YangMills.Construction.GaugeCharts
open YangMills.Construction.BlockAverages YangMills.Construction.MatrixDeterminants
namespace ChartDeterminant
def imaginaryCoords : imaginaryQuaternions ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun w := ![(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK]
  map_add' a b := by
    funext i
    fin_cases i <;> simp
  map_smul' c a := by
    funext i
    fin_cases i <;> simp
  invFun x := ⟨⟨0, x 0, x 1, x 2⟩, rfl⟩
  left_inv w := by
    apply Subtype.ext
    ext <;> simp [re_coe_imaginary]
  right_inv x := by
    funext i
    fin_cases i <;> rfl
theorem imaginaryCoords_dotProduct (X Y : imaginaryQuaternions) :
    imaginaryCoords X ⬝ᵥ imaginaryCoords Y = inner ℝ X Y := by
  rw [Submodule.coe_inner, Quaternion.inner_def]
  simp [imaginaryCoords, dotProduct, Fin.sum_univ_three, re_coe_imaginary]
def formCoords (T : Type) [Fintype T] : (T → imaginaryQuaternions) ≃ₗ[ℝ] (T × Fin 3 → ℝ) where
  toFun χ p := imaginaryCoords (χ p.1) p.2
  map_add' a b := by
    funext p
    simp
  map_smul' c a := by
    funext p
    simp
  invFun x t := imaginaryCoords.symm fun d => x (t, d)
  left_inv χ := by
    funext t
    simp
  right_inv x := by
    funext p
    simp
theorem formCoords_dotProduct {T : Type} [Fintype T] (χ ψ : T → imaginaryQuaternions) :
    formCoords T χ ⬝ᵥ formCoords T ψ = ∑ t, inner ℝ (χ t) (ψ t) := by
  simp only [dotProduct, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← imaginaryCoords_dotProduct]
  rfl
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
def formMatrix (A : (ι → imaginaryQuaternions) →ₗ[ℝ] (κ → imaginaryQuaternions)) :
    Matrix (κ × Fin 3) (ι × Fin 3) ℝ :=
  LinearMap.toMatrix' ((formCoords κ).toLinearMap ∘ₗ A ∘ₗ (formCoords ι).symm.toLinearMap)
theorem formMatrix_mulVec (A : (ι → imaginaryQuaternions) →ₗ[ℝ] (κ → imaginaryQuaternions))
    (χ : ι → imaginaryQuaternions) : formMatrix A *ᵥ formCoords ι χ = formCoords κ (A χ) := by
  rw [formMatrix, LinearMap.toMatrix'_mulVec]
  simp
theorem sum_sq_mul_pseudoInverse {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] (Dm Em : Matrix β α ℝ)
    (hN : IsUnit (Dmᵀ * Dm).det) :
    ∑ i, ∑ j, (Em * ((Dmᵀ * Dm)⁻¹ * Dmᵀ)) i j ^ 2 = ∑ i, Em i ⬝ᵥ ((Dmᵀ * Dm)⁻¹ *ᵥ Em i) := by
  set N := Dmᵀ * Dm with hNdef
  set Ni := N⁻¹ with hNi
  have hNs : Nᵀ = N := by simp [hNdef, Matrix.transpose_mul]
  have hNis : Niᵀ = Ni := by rw [hNi, Matrix.transpose_nonsing_inv, hNs]
  have hmul : Ni * N = 1 := Matrix.nonsing_inv_mul _ hN
  have hM : (Em * (Ni * Dmᵀ)) * (Em * (Ni * Dmᵀ))ᵀ = Em * Ni * Emᵀ := by
    calc (Em * (Ni * Dmᵀ)) * (Em * (Ni * Dmᵀ))ᵀ = Em * (Ni * (Dmᵀ * Dm) * Ni) * Emᵀ := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hNis, Matrix.mul_assoc]
      _ = Em * Ni * Emᵀ := by
          rw [← hNdef, hmul, Matrix.one_mul, Matrix.mul_assoc]
  have h1 : ∑ i, ∑ j, (Em * (Ni * Dmᵀ)) i j ^ 2 = ((Em * (Ni * Dmᵀ)) * (Em * (Ni * Dmᵀ))ᵀ).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply (M := Em * (Ni * Dmᵀ)), Matrix.transpose_apply, sq]
  rw [h1, hM, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring
def pointSource (o : Option ι) (p : imaginaryQuaternions) : ι → imaginaryQuaternions :=
  fun z => if o = some z then p else 0
theorem sum_inner_pointSource (o : Option ι) (p : imaginaryQuaternions) (ψ : ι → imaginaryQuaternions) :
    ∑ z, inner ℝ (pointSource o p z) (ψ z) = inner ℝ p (formAtEnd ψ o) := by
  cases o with
  | none => simp [pointSource, formAtEnd]
  | some z₀ =>
    rw [Finset.sum_eq_single z₀]
    · simp [pointSource, formAtEnd]
    · intro z _ hz
      have : (some z₀ : Option ι) ≠ some z := fun h => hz (Option.some.inj h).symm
      simp [pointSource, this]
    · simp
theorem exists_inner_eq_of_abs_le (A : imaginaryQuaternions →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ X, |A X| ≤ C * ‖X‖) :
    ∃ p : imaginaryQuaternions, ‖p‖ ≤ C ∧ ∀ X, inner ℝ p X = A X := by
  haveI : CompleteSpace imaginaryQuaternions := FiniteDimensional.complete ℝ imaginaryQuaternions
  let ℓ : StrongDual ℝ imaginaryQuaternions := A.toContinuousLinearMap
  refine ⟨(InnerProductSpace.toDual ℝ imaginaryQuaternions).symm ℓ, ?_, fun X => ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    exact ContinuousLinearMap.opNorm_le_bound _ hC fun X => by
      simpa [ℓ] using h X
  · rw [InnerProductSpace.toDual_symm_apply]
    rfl
theorem abs_imaginaryCoords_le (w : imaginaryQuaternions) (d : Fin 3) : |imaginaryCoords w d| ≤ ‖w‖ := by
  have h := norm_sq_imaginary w
  have hs : (imaginaryCoords w d) ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [h]
    fin_cases d <;> simp [imaginaryCoords] <;> nlinarith [sq_nonneg (w : ℍ[ℝ]).imI, sq_nonneg (w : ℍ[ℝ]).imJ, sq_nonneg (w : ℍ[ℝ]).imK]
  exact abs_le_of_sq_le_sq hs (norm_nonneg _)
theorem norm_imaginaryPart_le (q : ℍ[ℝ]) : ‖imaginaryPart q‖ ≤ ‖q‖ := by
  have h := norm_sq_eq_re_sq_add_imaginaryPart q
  have h2 : ‖imaginaryPart q‖ ^ 2 ≤ ‖q‖ ^ 2 := by nlinarith [sq_nonneg q.re]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
theorem norm_hemispherePoint_sub_one_sq_le {y : imaginaryQuaternions} (hy : ‖y‖ ≤ 1) :
    ‖hemispherePoint y - 1‖ ^ 2 ≤ 2 * ‖y‖ ^ 2 := by
  have h := norm_sq_eq_re_sq_add_imaginaryPart (hemispherePoint y - 1)
  have h1 : imaginaryPart (hemispherePoint y - 1) = y := by
    have : imaginaryPart (1 : ℍ[ℝ]) = 0 := by
      simpa using imaginaryPart_coe_real 1
    rw [map_sub, imaginaryPart_hemispherePoint, this, sub_zero]
  have h2 : (hemispherePoint y - 1).re = Real.sqrt (1 - ‖y‖ ^ 2) - 1 := by
    simp [re_hemispherePoint]
  have h0 := norm_nonneg y
  have h3 : 1 - ‖y‖ ≤ Real.sqrt (1 - ‖y‖ ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have h4 : Real.sqrt (1 - ‖y‖ ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  rw [h, h1, h2]
  nlinarith
theorem gaugeLinearization_sub_zero (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (y : κ → imaginaryQuaternions) (χ : ι → imaginaryQuaternions) (b : κ) :
    gaugeLinearization tl hd V y χ b - gaugeLinearization tl hd V 0 χ b =
      imaginaryPart ((formAtEnd χ (tl b) : ℍ[ℝ]) * (hemispherePoint (y b) - 1)) -
        imaginaryPart ((hemispherePoint (y b) - 1) * ((V b : ℍ[ℝ]) * (formAtEnd χ (hd b) : ℍ[ℝ]) * star (V b : ℍ[ℝ]))) := by
  simp only [gaugeLinearization, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, hemispherePoint_zero, mul_one, one_mul,
    mul_sub, sub_mul, map_sub]
  abel
theorem row_greenForm_le (tl hd : κ → Option ι) (V : κ → UnitQuaternion) (y : κ → imaginaryQuaternions)
    (hy : ∀ b, ‖y b‖ ≤ 1)
    (Ni : Matrix (ι × Fin 3) (ι × Fin 3) ℝ)
    (hG : ∀ (o : Option ι) (p : imaginaryQuaternions) (z : ι),
      ‖(formCoords ι).symm (Ni *ᵥ formCoords ι (pointSource o p)) z‖ ≤ ‖p‖)
    (b : κ) (c : Fin 3) (w : ι × Fin 3 → ℝ)
    (hw : ∀ χ, w ⬝ᵥ formCoords ι χ =
      imaginaryCoords (gaugeLinearization tl hd V y χ b - gaugeLinearization tl hd V 0 χ b) c) :
    w ⬝ᵥ (Ni *ᵥ w) ≤ 8 * ‖y b‖ ^ 2 := by
  set M : ℍ[ℝ] := hemispherePoint (y b) - 1 with hM
  set v : ℍ[ℝ] := (V b : ℍ[ℝ]) with hv
  have hC : 0 ≤ ‖M‖ := norm_nonneg _
  let ℓ₁ : imaginaryQuaternions →ₗ[ℝ] ℝ := (LinearMap.proj c) ∘ₗ imaginaryCoords.toLinearMap ∘ₗ imaginaryPart ∘ₗ
    (LinearMap.mulRight ℝ M) ∘ₗ imaginaryQuaternions.subtype
  let ℓ₂ : imaginaryQuaternions →ₗ[ℝ] ℝ := -((LinearMap.proj c) ∘ₗ imaginaryCoords.toLinearMap ∘ₗ imaginaryPart ∘ₗ
    (LinearMap.mulLeft ℝ M) ∘ₗ (LinearMap.mulRight ℝ (star v)) ∘ₗ (LinearMap.mulLeft ℝ v) ∘ₗ imaginaryQuaternions.subtype)
  have hℓ₁ : ∀ X : imaginaryQuaternions, ℓ₁ X = imaginaryCoords (imaginaryPart ((X : ℍ[ℝ]) * M)) c := fun X => rfl
  have hℓ₂ : ∀ X : imaginaryQuaternions, ℓ₂ X = -imaginaryCoords (imaginaryPart (M * (v * (X : ℍ[ℝ]) * star v))) c :=
    fun X => rfl
  obtain ⟨p, hp, hpX⟩ := exists_inner_eq_of_abs_le ℓ₁ hC fun X => by
    rw [hℓ₁]
    calc _ ≤ ‖imaginaryPart ((X : ℍ[ℝ]) * M)‖ := abs_imaginaryCoords_le _ _
      _ ≤ ‖(X : ℍ[ℝ]) * M‖ := norm_imaginaryPart_le _
      _ = ‖M‖ * ‖X‖ := by
          rw [norm_mul, mul_comm]
          rfl
  obtain ⟨q, hq, hqX⟩ := exists_inner_eq_of_abs_le ℓ₂ hC fun X => by
    rw [hℓ₂, abs_neg]
    calc _ ≤ ‖imaginaryPart (M * (v * (X : ℍ[ℝ]) * star v))‖ := abs_imaginaryCoords_le _ _
      _ ≤ ‖M * (v * (X : ℍ[ℝ]) * star v)‖ := norm_imaginaryPart_le _
      _ = ‖M‖ * ‖X‖ := by
          rw [norm_mul, norm_mul, norm_mul, norm_star, hv, norm_unitQuaternion, one_mul, mul_one]
          rfl
  have hw' : ∀ χ, w ⬝ᵥ formCoords ι χ = inner ℝ p (formAtEnd χ (tl b)) + inner ℝ q (formAtEnd χ (hd b)) := by
    intro χ
    rw [hw, gaugeLinearization_sub_zero, hpX, hqX, hℓ₁, hℓ₂, map_sub]
    simp only [Pi.sub_apply]
    ring
  have hweq : w = formCoords ι (pointSource (tl b) p) + formCoords ι (pointSource (hd b) q) := by
    refine dotProduct_eq _ _ fun x => ?_
    obtain ⟨χ, rfl⟩ := (formCoords ι).surjective x
    rw [hw', add_dotProduct, formCoords_dotProduct, formCoords_dotProduct, sum_inner_pointSource, sum_inner_pointSource]
  set χ₁ : ι → imaginaryQuaternions := (formCoords ι).symm (Ni *ᵥ formCoords ι (pointSource (tl b) p)) with hχ₁
  set χ₂ : ι → imaginaryQuaternions := (formCoords ι).symm (Ni *ᵥ formCoords ι (pointSource (hd b) q)) with hχ₂
  have hNw : Ni *ᵥ w = formCoords ι (χ₁ + χ₂) := by
    rw [map_add, hχ₁, hχ₂, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, ← Matrix.mulVec_add, ← hweq]
  have hb : ∀ o : Option ι, ‖formAtEnd (χ₁ + χ₂) o‖ ≤ ‖p‖ + ‖q‖ := by
    intro o
    cases o with
    | none =>
      simp only [formAtEnd, norm_zero]
      positivity
    | some z =>
      exact (norm_add_le _ _).trans (add_le_add (hG _ _ z) (hG _ _ z))
  rw [hNw, hw']
  have h1 : inner ℝ p (formAtEnd (χ₁ + χ₂) (tl b)) ≤ ‖p‖ * (‖p‖ + ‖q‖) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _))
  have h2 : inner ℝ q (formAtEnd (χ₁ + χ₂) (hd b)) ≤ ‖q‖ * (‖p‖ + ‖q‖) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _))
  have hM2 := norm_hemispherePoint_sub_one_sq_le (hy b)
  have hpq : (‖p‖ + ‖q‖) ^ 2 ≤ (2 * ‖M‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  nlinarith
end ChartDeterminant
open ChartDeterminant in
theorem chartLinearizationDetBound_of_logDetOneAddBound (hDet : LogDetOneAddBound) :
    ChartLinearizationDetBound := by
  intro ι κ S _ _ _ _ _ _ tl hd V e he hrange hinj hgreen
  set D : (ι → imaginaryQuaternions) →ₗ[ℝ] (κ → imaginaryQuaternions) := gaugeLinearization tl hd V 0 with hD
  set Dm : Matrix (κ × Fin 3) (ι × Fin 3) ℝ := formMatrix D with hDm
  set N : Matrix (ι × Fin 3) (ι × Fin 3) ℝ := Dmᵀ * Dm with hN
  have hcvD : ∀ χ, Dm *ᵥ formCoords ι χ = formCoords κ (D χ) := formMatrix_mulVec D
  have hdotN : ∀ u x, (N *ᵥ u) ⬝ᵥ x = (Dm *ᵥ u) ⬝ᵥ (Dm *ᵥ x) := by
    intro u x
    rw [hN, ← Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  have hNu : IsUnit N.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have h1 : (Dm *ᵥ v) ⬝ᵥ (Dm *ᵥ v) = 0 := by
      rw [← hdotN, hv, zero_dotProduct]
    have h2 : Dm *ᵥ v = 0 := dotProduct_self_eq_zero.mp h1
    obtain ⟨χ, rfl⟩ := (formCoords ι).surjective v
    rw [hcvD] at h2
    have h3 : D χ = 0 := by
      apply (formCoords κ).injective
      rw [h2, map_zero]
    apply hv0
    rw [hinj χ h3, map_zero]
  set Ni := N⁻¹ with hNi
  have hNN : N * Ni = 1 := Matrix.mul_nonsing_inv _ hNu
  have hNN' : Ni * N = 1 := Matrix.nonsing_inv_mul _ hNu
  set Dp : Matrix (ι × Fin 3) (κ × Fin 3) ℝ := Ni * Dmᵀ with hDp
  let Dplus : (κ → imaginaryQuaternions) →ₗ[ℝ] (ι → imaginaryQuaternions) :=
    (formCoords ι).symm.toLinearMap ∘ₗ Matrix.toLin' Dp ∘ₗ (formCoords κ).toLinearMap
  have hcvP : ∀ v, formCoords ι (Dplus v) = Dp *ᵥ formCoords κ v := fun v => by
    simp [Dplus, Matrix.toLin'_apply]
  have hPD : ∀ χ, Dplus (D χ) = χ := by
    intro χ
    apply (formCoords ι).injective
    rw [hcvP, ← hcvD, hDp, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      show Ni * (Dmᵀ * Dm) = 1 from hNN', Matrix.one_mulVec]
  have horth : ∀ v χ, ∑ b, inner ℝ ((v - D (Dplus v)) b) (D χ b) = 0 := by
    intro v χ
    have hz : Dmᵀ *ᵥ (formCoords κ (v - D (Dplus v))) = 0 := by
      rw [map_sub, ← hcvD, hcvP, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      have h1 : Dmᵀ * Dm * Dp = Dmᵀ := by
        rw [← hN, hDp, ← Matrix.mul_assoc, hNN, Matrix.one_mul]
      rw [h1, sub_self]
    rw [← formCoords_dotProduct, ← hcvD, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hz, zero_dotProduct]
  have hmem : ∀ v, ((LinearMap.id - D ∘ₗ Dplus :
      (κ → imaginaryQuaternions) →ₗ[ℝ] (κ → imaginaryQuaternions))) v ∈ LinearMap.range e :=
    fun v => (hrange _).mpr (horth v)
  let eq₁ : S ≃ₗ[ℝ] LinearMap.range e := LinearEquiv.ofInjective e he
  have he₁ : ∀ x : LinearMap.range e, e (eq₁.symm x) = x := fun x => by
    have := congrArg Subtype.val (eq₁.apply_symm_apply x)
    exact this
  let P : (κ → imaginaryQuaternions) →ₗ[ℝ] LinearMap.range e := LinearMap.codRestrict _
    (LinearMap.id - D ∘ₗ Dplus : (κ → imaginaryQuaternions) →ₗ[ℝ] (κ → imaginaryQuaternions)) hmem
  let Q : (κ → imaginaryQuaternions) →ₗ[ℝ] ((ι → imaginaryQuaternions) × S) :=
    LinearMap.prod Dplus (eq₁.symm.toLinearMap ∘ₗ P)
  have hcl : ∀ (y : κ → imaginaryQuaternions) (χ : ι → imaginaryQuaternions) (η : S),
      chartLinearization tl hd V e y (χ, η) = gaugeLinearization tl hd V y χ + e η := fun y χ η => by
    simp [chartLinearization]
  have hPv : ∀ v, e (eq₁.symm (P v)) = v - D (Dplus v) := fun v => he₁ (P v)
  have hQv : ∀ v, Q v = (Dplus v, eq₁.symm (P v)) := fun v => rfl
  have hPe : ∀ η, Dplus (e η) = 0 := by
    intro η
    have hz : Dmᵀ *ᵥ (formCoords κ (e η)) = 0 := by
      refine dotProduct_eq _ _ fun x => ?_
      obtain ⟨χ, rfl⟩ := (formCoords ι).surjective x
      have h1 : (formCoords κ (e η)) ⬝ᵥ (Dm *ᵥ formCoords ι χ) = 0 := by
        rw [hcvD, formCoords_dotProduct]
        exact (hrange _).mp ⟨η, rfl⟩ χ
      rw [zero_dotProduct, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
      exact h1
    apply (formCoords ι).injective
    rw [hcvP, hDp, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, map_zero]
  refine ⟨Q, ?_, ?_, ?_⟩
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, hQv, hcl, hPv]
    simp [hD]
  · refine LinearMap.ext fun p => ?_
    obtain ⟨χ, η⟩ := p
    rw [LinearMap.comp_apply, hcl, hQv]
    have h1 : Dplus (gaugeLinearization tl hd V 0 χ + e η) = χ := by
      rw [map_add, ← hD, hPD, hPe, add_zero]
    refine Prod.ext h1 (he ?_)
    rw [LinearMap.id_apply]
    show e (eq₁.symm (P (gaugeLinearization tl hd V 0 χ + e η))) = e η
    rw [hPv, h1, ← hD]
    abel
  intro y s hy hs hs8 hsum
  set Ey : (ι → imaginaryQuaternions) →ₗ[ℝ] (κ → imaginaryQuaternions) := gaugeLinearization tl hd V y - D with hEy
  set Em : Matrix (κ × Fin 3) (ι × Fin 3) ℝ := formMatrix Ey with hEm
  set M : Matrix (κ × Fin 3) (κ × Fin 3) ℝ := Em * Dp with hM
  have hA : ∀ v, chartLinearization tl hd V e y (Q v) = v + Ey (Dplus v) := by
    intro v
    rw [hQv, hcl, hPv, hEy, LinearMap.sub_apply]
    abel
  have hdet : LinearMap.det (chartLinearization tl hd V e y ∘ₗ Q) = (1 + M).det := by
    have hc : (formCoords κ).toLinearMap ∘ₗ (chartLinearization tl hd V e y ∘ₗ Q) ∘ₗ
        (formCoords κ).symm.toLinearMap = Matrix.toLin' (1 + M) := by
      refine LinearMap.ext fun x => ?_
      obtain ⟨v, rfl⟩ := (formCoords κ).surjective x
      show (formCoords κ) (chartLinearization tl hd V e y (Q ((formCoords κ).symm (formCoords κ v)))) =
        Matrix.toLin' (1 + M) (formCoords κ v)
      rw [LinearEquiv.symm_apply_apply, hA, map_add, Matrix.toLin'_apply, Matrix.add_mulVec, Matrix.one_mulVec,
        ← formMatrix_mulVec Ey, hcvP, hM, Matrix.mulVec_mulVec]
    rw [← LinearMap.det_conj _ (formCoords κ), hc, LinearMap.det_toLin']
  have hG : ∀ (o : Option ι) (p : imaginaryQuaternions) (z : ι),
      ‖(formCoords ι).symm (Ni *ᵥ formCoords ι (pointSource o p)) z‖ ≤ ‖p‖ := by
    intro o p z
    cases o with
    | none =>
      have h0 : pointSource (ι := ι) none p = 0 := by
        funext z'
        simp [pointSource]
      rw [h0, map_zero, Matrix.mulVec_zero, map_zero]
      simp
    | some z₀ =>
      refine hgreen _ z₀ p (fun ψ => ?_) z
      have hχ : formCoords ι ((formCoords ι).symm (Ni *ᵥ formCoords ι (pointSource (some z₀) p))) =
          Ni *ᵥ formCoords ι (pointSource (some z₀) p) :=
        LinearEquiv.apply_symm_apply _ _
      rw [← formCoords_dotProduct, ← hcvD, ← hcvD, ← hdotN, hχ, Matrix.mulVec_mulVec, hNN, Matrix.one_mulVec,
        formCoords_dotProduct, sum_inner_pointSource]
      rfl
  have hrow : ∀ b c, Em (b, c) ⬝ᵥ (Ni *ᵥ Em (b, c)) ≤ 8 * ‖y b‖ ^ 2 := by
    intro b c
    refine row_greenForm_le tl hd V y hy Ni hG b c _ fun χ => ?_
    have := congrFun (formMatrix_mulVec Ey χ) (b, c)
    exact this
  have hHS : (∑ i, ∑ j, M i j ^ 2) ≤ s ^ 2 := by
    rw [hM, hDp, hNi, hN, sum_sq_mul_pseudoInverse Dm Em hNu, ← hN, ← hNi, Fintype.sum_prod_type]
    calc ∑ b, ∑ c, Em (b, c) ⬝ᵥ (Ni *ᵥ Em (b, c)) ≤ ∑ b, ∑ c : Fin 3, 8 * ‖y b‖ ^ 2 :=
          Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ => hrow b c
      _ = 24 * ∑ b, ‖y b‖ ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          simp
          ring
      _ ≤ s ^ 2 := hsum
  obtain ⟨h1, h2⟩ := hDet (κ × Fin 3) M s hs hs8 hHS
  rw [hdet]
  exact ⟨h1, h2⟩
end YangMills.Construction.GaugeCharts
end
