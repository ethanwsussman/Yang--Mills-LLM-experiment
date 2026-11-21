import YangMills.Construction.EuclideanFunctionals.SupportsIsometriesAndConcatenationProof
import YangMills.Construction.RotationInvariance.MotionsOfPlatesAndQuarterRotations
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ProductMotions
open YangMills.Construction.RealPlane
theorem contDiff_coord (i : Fin 2) :
    ContDiff ℝ 1 (fun y : RealPlane => y i) :=
  (EuclideanSpace.proj i : RealPlane →L[ℝ] ℝ).contDiff
theorem contDiff_rotate (t : ℝ) : ContDiff ℝ 1 (rotate t) := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [RealPlane.rotate] using ((contDiff_coord 0).mul contDiff_const).sub
      ((contDiff_coord 1).mul contDiff_const)
  · simpa [RealPlane.rotate] using ((contDiff_coord 0).mul contDiff_const).add
      ((contDiff_coord 1).mul contDiff_const)
theorem contDiff_reflectFirst : ContDiff ℝ 1 reflectFirst := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [reflectFirst] using (contDiff_coord 0).neg
  · simpa [reflectFirst] using contDiff_coord 1
theorem rotate_rotate (s t : ℝ) (y : RealPlane) :
    rotate s (rotate t y) = rotate (s + t) y := by
  ext i
  fin_cases i
  · simp [RealPlane.rotate, Real.cos_add, Real.sin_add]
    ring
  · simp [RealPlane.rotate, Real.cos_add, Real.sin_add]
    ring
theorem rotate_zero (y : RealPlane) : rotate 0 y = y := by
  ext i
  fin_cases i <;> simp [RealPlane.rotate]
theorem reflectFirst_reflectFirst (y : RealPlane) : reflectFirst (reflectFirst y) = y := by
  ext i
  fin_cases i <;> simp [reflectFirst]
def rotateHomeomorph (t : ℝ) : RealPlane ≃ₜ RealPlane where
  toFun := rotate t
  invFun := rotate (-t)
  left_inv y := by rw [rotate_rotate, neg_add_cancel, rotate_zero]
  right_inv y := by rw [rotate_rotate, add_neg_cancel, rotate_zero]
  continuous_toFun := (contDiff_rotate t).continuous
  continuous_invFun := (contDiff_rotate (-t)).continuous
def reflectFirstHomeomorph : RealPlane ≃ₜ RealPlane where
  toFun := reflectFirst
  invFun := reflectFirst
  left_inv := reflectFirst_reflectFirst
  right_inv := reflectFirst_reflectFirst
  continuous_toFun := contDiff_reflectFirst.continuous
  continuous_invFun := contDiff_reflectFirst.continuous
theorem comp_mem_complexProfiles {α : RealPlane → ℂ} (hα : α ∈ complexProfiles)
    (κ : RealPlane ≃ₜ RealPlane) (hκ : ContDiff ℝ 1 κ) : α ∘ κ ∈ complexProfiles :=
  ⟨hα.1.comp hκ, hα.2.comp_homeomorph κ⟩
theorem conj_mem_complexProfiles {α : RealPlane → ℂ} (hα : α ∈ complexProfiles) :
    (fun y => conj (α y)) ∈ complexProfiles :=
  ⟨Complex.conjCLE.contDiff.comp hα.1, hα.2.comp_left (g := fun z : ℂ => conj z) (map_zero _)⟩
theorem rotateFour_rotateFour (s t : ℝ) (x : R4) :
    rotateFour s (rotateFour t x) = rotateFour (s + t) x := by
  simp only [rotateFour, planeComponent_ofComponents, orthogonalComponent_ofComponents,
    rotate_rotate]
theorem rotateMotion_add (s t : ℝ) :
    rotateMotion (s + t) = rotateMotion s * rotateMotion t :=
  EuclidMotion.ext_of_apply fun x => by
    rw [EuclidMotion.mul_apply, rotateMotion_apply, rotateMotion_apply, rotateMotion_apply,
      rotateFour_rotateFour]
theorem rotateMotion_zero : rotateMotion 0 = 1 :=
  EuclidMotion.ext_of_apply fun x => by
    rw [rotateMotion_apply, EuclidMotion.one_apply, rotateFour, rotate_zero,
      ofComponents_planeComponent_orthogonalComponent]
theorem rotateMotion_inv (t : ℝ) : (rotateMotion t)⁻¹ = rotateMotion (-t) :=
  inv_eq_of_mul_eq_one_left (by
    rw [← rotateMotion_add, neg_add_cancel, rotateMotion_zero])
theorem toMatrix'_rotateLin (t : ℝ) :
    LinearMap.toMatrix' (rotateLin t) =
      !![Real.cos t, 0, 0, Real.sin t;
         0, 1, 0, 0;
         0, 0, 1, 0;
         -Real.sin t, 0, 0, Real.cos t] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix'_apply, rotateLin, rotateFour, ofComponents,
      RealPlane.rotate, planeComponent, orthogonalComponent]
theorem det_rotationMatrix (t : ℝ) :
    Matrix.det (!![Real.cos t, 0, 0, Real.sin t;
         0, 1, 0, 0;
         0, 0, 1, 0;
         -Real.sin t, 0, 0, Real.cos t] : Matrix (Fin 4) (Fin 4) ℝ) = 1 := by
  have h := Real.sin_sq_add_cos_sq t
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  linear_combination h
theorem det_rotateLin (t : ℝ) : LinearMap.det (rotateLin t) = 1 := by
  rw [← LinearMap.det_toMatrix', toMatrix'_rotateLin, det_rotationMatrix]
theorem toMatrix'_rotateLin_mem_specialOrthogonalGroup (t : ℝ) :
    LinearMap.toMatrix' (rotateLin t) ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, by rw [toMatrix'_rotateLin, det_rotationMatrix]⟩
  have h := Real.sin_sq_add_cos_sq t
  rw [toMatrix'_rotateLin, Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first
      | ring1
      | linear_combination h
theorem rotationsSpecialOrthogonal : RotationsSpecialOrthogonal :=
  fun t => ⟨fun _ => add_zero _, (rotateMotion t).lin_norm, det_rotateLin t,
    toMatrix'_rotateLin_mem_specialOrthogonalGroup t, rotateMotion_inv t⟩
theorem rotateMotion_pi_div_two_mem : rotateMotion (Real.pi / 2) ∈ hyperoctahedral := by
  refine ⟨(Equiv.swap 0 3, ![1, 1, 1, -1]), EuclidMotion.ext_of_apply fun x => ?_⟩
  rw [ofSignedFrame_apply, rotateMotion_apply]
  funext μ
  fin_cases μ <;>
    simp [PeriodicLattice.SignedFrame.actOnVector, rotateFour, ofComponents,
      RealPlane.rotate, planeComponent, orthogonalComponent, Equiv.swap_apply_def]
theorem rightAngleRotationsHyperoctahedral : RightAngleRotationsHyperoctahedral := by
  intro k
  induction k using Int.induction_on with
  | zero =>
    simp [rotateMotion_zero]
  | succ n ih =>
    have h : (((n : ℤ) + 1 : ℤ) : ℝ) * (Real.pi / 2) =
        ((n : ℤ) : ℝ) * (Real.pi / 2) + Real.pi / 2 := by
      push_cast
      ring
    rw [h, rotateMotion_add]
    exact hyperoctahedral.mul_mem ih rotateMotion_pi_div_two_mem
  | pred n ih =>
    have h : ((-(n : ℤ) - 1 : ℤ) : ℝ) * (Real.pi / 2) =
        ((-(n : ℤ) : ℤ) : ℝ) * (Real.pi / 2) + -(Real.pi / 2) := by
      push_cast
      ring
    rw [h, rotateMotion_add, ← rotateMotion_inv]
    exact hyperoctahedral.mul_mem ih (hyperoctahedral.inv_mem rotateMotion_pi_div_two_mem)
theorem contDiff_planeComponent : ContDiff ℝ 1 planeComponent := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [planeComponent] using contDiff_apply ℝ ℝ (3 : Fin 4)
  · simpa [planeComponent] using contDiff_apply ℝ ℝ (0 : Fin 4)
theorem contDiff_orthogonalComponent : ContDiff ℝ 1 orthogonalComponent := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [orthogonalComponent] using contDiff_apply ℝ ℝ (1 : Fin 4)
  · simpa [orthogonalComponent] using contDiff_apply ℝ ℝ (2 : Fin 4)
theorem continuous_ofComponents :
    Continuous fun p : RealPlane × RealPlane => ofComponents p.1 p.2 := by
  refine continuous_pi fun i => ?_
  have h₁ : ∀ j : Fin 2, Continuous fun p : RealPlane × RealPlane => p.1 j :=
    fun j => (contDiff_coord j).continuous.comp continuous_fst
  have h₂ : ∀ j : Fin 2, Continuous fun p : RealPlane × RealPlane => p.2 j :=
    fun j => (contDiff_coord j).continuous.comp continuous_snd
  fin_cases i
  · simpa [ofComponents] using h₁ 1
  · simpa [ofComponents] using h₂ 0
  · simpa [ofComponents] using h₂ 1
  · simpa [ofComponents] using h₁ 0
def supportBox (α : RealPlane → ℂ) (φ : RealPlane → ℝ) : Set R4 :=
  {x | planeComponent x ∈ tsupport α ∧ orthogonalComponent x ∈ tsupport φ}
theorem isClosed_supportBox (α : RealPlane → ℂ) (φ : RealPlane → ℝ) :
    IsClosed (supportBox α φ) :=
  ((isClosed_tsupport α).preimage contDiff_planeComponent.continuous).inter
    ((isClosed_tsupport φ).preimage contDiff_orthogonalComponent.continuous)
theorem isCompact_supportBox {α : RealPlane → ℂ} {φ : RealPlane → ℝ}
    (hα : HasCompactSupport α) (hφ : HasCompactSupport φ) :
    IsCompact (supportBox α φ) := by
  have h := (IsCompact.prod hα hφ).image continuous_ofComponents
  refine h.of_isClosed_subset (isClosed_supportBox α φ) fun x hx => ?_
  exact ⟨(planeComponent x, orthogonalComponent x), ⟨hx.1, hx.2⟩,
    ofComponents_planeComponent_orthogonalComponent x⟩
theorem ne_zero_subset_supportBox (α : RealPlane → ℂ) (φ : RealPlane → ℝ) :
    {x | productFunction α φ x ≠ 0} ⊆ supportBox α φ := by
  intro x hx
  have hx' : α (planeComponent x) * (φ (orthogonalComponent x) : ℂ) ≠ 0 := hx
  refine ⟨subset_tsupport _ (left_ne_zero_of_mul hx'), subset_tsupport _ ?_⟩
  intro h0
  exact hx' (by simp [show φ (orthogonalComponent x) = 0 from h0])
theorem supp_eq_closure (f : R4 → ℂ) : supp f = closure {x | f x ≠ 0} :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
theorem productFunctionsCompactC1 : ProductFunctionsCompactC1 := by
  intro α hα φ hφ
  have hsub : supp (productFunction α φ) ⊆ supportBox α φ := by
    rw [supp_eq_closure]
    exact closure_minimal (ne_zero_subset_supportBox α φ) (isClosed_supportBox α φ)
  have hclosed : IsClosed (supp (productFunction α φ)) := by
    rw [supp_eq_closure]
    exact isClosed_closure
  refine ⟨⟨?_, ?_⟩, hsub⟩
  · exact (hα.1.comp contDiff_planeComponent).mul
      ((Complex.ofRealCLM.contDiff.comp hφ.1).comp contDiff_orthogonalComponent)
  · exact (SeparatedTuplesR4.isCompactWrt_euclid_iff (fun _ _ => rfl) _).2
      ((isCompact_supportBox hα.2 hφ.2).of_isClosed_subset hclosed hsub)
theorem planeComponent_sub_embedFour (u : RealPlane) (x : R4) :
    planeComponent (x - embedFour u) = planeComponent x - u := by
  ext i
  fin_cases i <;>
    simp [planeComponent, embedFour, PeriodicLattice.coordVec]
theorem orthogonalComponent_sub_embedFour (u : RealPlane) (x : R4) :
    orthogonalComponent (x - embedFour u) = orthogonalComponent x := by
  ext i
  fin_cases i <;>
    simp [orthogonalComponent, embedFour, PeriodicLattice.coordVec]
theorem timeFlip_inv : timeFlip⁻¹ = timeFlip := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionProofs.timeFlip_inv <;> assumption
theorem motionsActOnPlaneFactor : MotionsActOnPlaneFactor := by
  intro α _ φ _ u t
  refine ⟨?_, ?_, ?_⟩
  · funext x
    rw [planeShift, EuclidMotion.actFn_transl]
    simp only [productFunction, translateProfile, planeComponent_sub_embedFour,
      orthogonalComponent_sub_embedFour]
  · funext x
    simp only [EuclidMotion.actFn, rotateMotion_inv, rotateMotion_apply, productFunction,
      rotateFour, planeComponent_ofComponents, orthogonalComponent_ofComponents, Function.comp]
  · funext x
    simp only [EuclidMotion.actFn, timeFlip_inv, ← liftFour_reflectFirst, productFunction,
      liftFour, planeComponent_ofComponents, orthogonalComponent_ofComponents, Function.comp,
      map_mul, Complex.conj_ofReal]
theorem motionImagesAreProducts : MotionImagesAreProducts := by
  intro α hα φ hφ u t
  have h₁ : translateProfile u α ∈ complexProfiles :=
    comp_mem_complexProfiles hα (Homeomorph.subRight u) (contDiff_id.sub contDiff_const)
  have h₂ : α ∘ rotate (-t) ∈ complexProfiles :=
    comp_mem_complexProfiles hα (rotateHomeomorph (-t)) (contDiff_rotate (-t))
  have h₃ : (fun y => conj (α y)) ∘ reflectFirst ∈ complexProfiles :=
    comp_mem_complexProfiles (conj_mem_complexProfiles hα) reflectFirstHomeomorph
      contDiff_reflectFirst
  exact ⟨h₁, h₂, h₃, ⟨_, h₁, φ, hφ, rfl⟩, ⟨_, h₂, φ, hφ, rfl⟩, ⟨_, h₃, φ, hφ, rfl⟩⟩
theorem motionFacts_holds : MotionFacts :=
  ⟨rotationsSpecialOrthogonal, rightAngleRotationsHyperoctahedral,
    productFunctionsCompactC1, motionsActOnPlaneFactor, motionImagesAreProducts⟩
end YangMills.Construction.EuclideanFunctionals.ProductMotions
end
