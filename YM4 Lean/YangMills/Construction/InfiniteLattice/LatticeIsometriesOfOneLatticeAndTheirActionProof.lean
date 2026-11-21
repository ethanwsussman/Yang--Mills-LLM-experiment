import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfASpacingAsMotionsAndTheirActionProof
import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfOneLatticeAndTheirAction
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotions
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.InfiniteLattice
open scoped Matrix
noncomputable section
namespace YangMills.Construction.LatticePhases.LatticeSymmetryAction
variable {a : ℝ}
theorem pullbackField_comp (r r' : LatticeSymmetry a) :
    (r.comp r').pullbackField = r'.pullbackField ∘ r.pullbackField := by apply _root_.YangMills.Construction.InfiniteLattice.SymmetriesAsMotions.pullbackField_comp <;> assumption
theorem pullbackField_leftInverse {t r : LatticeSymmetry a}
    (h : Function.LeftInverse r.toFun t.toFun) (U : GaugeField a) :
    t.pullbackField (r.pullbackField U) = U := by apply _root_.YangMills.Construction.InfiniteLattice.SymmetriesAsMotions.pullbackField_pullbackField <;> assumption
theorem basisVector_ne {i j : Fin 4} (hij : i ≠ j) : basisVector i ≠ basisVector j := by
  intro e
  have := congrFun e i
  simp [basisVector, Pi.single_eq_of_ne hij] at this
theorem basisVector_ne_neg {i j : Fin 4} (hij : i ≠ j) : basisVector i ≠ -basisVector j := by
  intro e
  have := congrFun e i
  simp [basisVector, Pi.single_eq_of_ne hij] at this
theorem mulVec_basisVector_eq (ha : 0 < a) (r : LatticeSymmetry a)
    {R : Matrix (Fin 4) (Fin 4) ℝ} {v : AmbientSpace}
    (hf : ∀ x, r.toFun x = R *ᵥ x + v) (hv : v ∈ latticeSubgroup a) (i : Fin 4) :
    ∃ j, R *ᵥ basisVector i = basisVector j ∨ R *ᵥ basisVector i = -basisVector j := by
  have h0 : r.toFun 0 = v := by simpa using hf 0
  have hstep : ((axisStep a i : LatticePoint a) : AmbientSpace) = a • basisVector i := by
    funext μ
    by_cases h : μ = i
    · subst h
      simp [axisStep, basisVector]
    · simp [axisStep, basisVector, Pi.single_eq_of_ne h]
  obtain ⟨m, hm⟩ : r.toFun (axisStep a i : LatticePoint a) - v ∈ latticeSubgroup a :=
    sub_mem (r.pointMap (axisStep a i)).2 hv
  have hRe : ∀ μ, (R *ᵥ basisVector i) μ = m μ := by
    intro μ
    have h := hm μ
    rw [hf, hstep, Matrix.mulVec_smul] at h
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_right] at h
    exact mul_left_cancel₀ ha.ne' (by rw [h]; ring)
  have hlen := r.preservesDist (axisStep a i : LatticePoint a) 0
  rw [h0, sub_zero] at hlen
  have hlen' : TorusMetric.euclidNormVec ((axisStep a i : LatticePoint a) : AmbientSpace) = |a| :=
    euclidNormVec_single i a
  rw [hlen', TorusMetric.euclidNormVec] at hlen
  have hsq : ∑ μ, ((m μ : ℝ) * a) ^ 2 = a ^ 2 := by
    have h2 : Real.sqrt (∑ μ, (r.toFun ((axisStep a i : LatticePoint a) : AmbientSpace) - v) μ ^ 2) ^ 2
        = |a| ^ 2 := by
      rw [hlen]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), sq_abs] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun μ _ => by rw [hm μ]
  have hreal : ∑ μ, (m μ : ℝ) ^ 2 = 1 := by
    have h3 : a ^ 2 * ∑ μ, (m μ : ℝ) ^ 2 = a ^ 2 * 1 := by
      rw [mul_one, Finset.mul_sum]
      refine Eq.trans (Finset.sum_congr rfl fun μ _ => ?_) hsq
      ring
    exact mul_left_cancel₀ (pow_ne_zero 2 ha.ne') h3
  have hint : ∑ μ, m μ ^ 2 = 1 := by exact_mod_cast hreal
  obtain ⟨j, hj | hj⟩ := int_vec_unit_of_sum_sq_eq_one m hint
  · refine ⟨j, Or.inl (funext fun μ => ?_)⟩
    rw [hRe, hj]
    by_cases h : μ = j
    · subst h
      simp [basisVector]
    · simp [basisVector, Pi.single_eq_of_ne h]
  · refine ⟨j, Or.inr (funext fun μ => ?_)⟩
    rw [hRe, hj]
    by_cases h : μ = j
    · subst h
      simp [basisVector]
    · simp [basisVector, Pi.single_eq_of_ne h]
theorem toFun_mem_latticeMotions (ha : 0 < a)
    (hiso : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine)
    (r : LatticeSymmetry a) : r.toFun ∈ latticeMotions a := by
  obtain ⟨R, hR, v, hf⟩ := hiso r.toFun r.preservesDist
  have h0 : r.toFun 0 = v := by simpa using hf 0
  have hv : v ∈ latticeSubgroup a := by
    have h : r.toFun 0 ∈ r.toFun '' (latticeSubgroup a : Set AmbientSpace) := ⟨0, zero_mem _, rfl⟩
    rw [r.image_eq, h0] at h
    exact h
  have hback : ∀ x : AmbientSpace, star R *ᵥ (R *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff'.mp hR, Matrix.one_mulVec]
  have hRinj : ∀ x y : AmbientSpace, R *ᵥ x = R *ᵥ y → x = y := fun x y h => by
    rw [← hback x, h, hback]
  choose σ hσ using mulVec_basisVector_eq ha r hf hv
  have hinj : Function.Injective σ := by
    intro i i' h
    by_contra hne
    rcases hσ i with h1 | h1 <;> rcases hσ i' with h2 | h2
    · exact basisVector_ne hne (hRinj _ _ (by rw [h1, h2, h]))
    · refine basisVector_ne_neg hne (hRinj _ _ ?_)
      rw [Matrix.mulVec_neg, h1, h2, h, neg_neg]
    · refine basisVector_ne_neg hne (hRinj _ _ ?_)
      rw [Matrix.mulVec_neg, h1, h2, h]
    · exact basisVector_ne hne (hRinj _ _ (by rw [h1, h2, h]))
  refine ⟨Matrix.mulVecLin R,
    ⟨Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj), fun i => ?_⟩, v, hv, fun x => ?_⟩
  · simpa using hσ i
  · rw [hf]
    rfl
theorem symmetriesAreMotions (D : Setup)
    (hiso : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine) :
    SymmetriesAreMotions D := by
  unfold SymmetriesAreMotions
  ext r
  constructor
  · rintro ⟨s, rfl⟩
    exact toFun_mem_latticeMotions D.mesh_pos hiso s
  · intro hr
    exact ⟨latticeMotionSymmetry ⟨r, hr⟩, rfl⟩
theorem motionsFormGroup (D : Setup)
    (hiso : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine)
    (hinv : LatticeSymmetryInverses D.mesh) : MotionsFormGroup D := by
  refine ⟨⟨LinearMap.id, ⟨1, fun i => Or.inl rfl⟩, 0, zero_mem _, fun x => by simp⟩, ?_, ?_⟩
  · intro r hr r' hr'
    exact toFun_mem_latticeMotions D.mesh_pos hiso
      ((latticeMotionSymmetry ⟨r, hr⟩).comp (latticeMotionSymmetry ⟨r', hr'⟩))
  · intro r hr
    obtain ⟨t, ht⟩ := (hinv (latticeMotionSymmetry ⟨r, hr⟩)).2.1
    exact ⟨t.toFun, toFun_mem_latticeMotions D.mesh_pos hiso t, funext fun x => ht.2 x,
      funext fun x => ht.1 x⟩
def singleNegation (μ : Fin 4) : Fin 4 → ℤˣ := Function.update 1 μ (-1)
theorem signFlip_singleNegation (μ : Fin 4) :
    ⇑(signFlip (singleNegation μ)) = (axialReflection a μ).toFun := by
  rw [axialReflection_toFun_eq_axisReflection, axisReflection_eq_coordinateSignFlip]
  funext x ν
  by_cases h : ν = μ
  · subst h
    simp [signFlip, coordinateSignFlip, singleNegation]
  · simp [signFlip, coordinateSignFlip, singleNegation, h]
theorem signFlip_mul (ε ε' : Fin 4 → ℤˣ) :
    signFlip (ε * ε') = signFlip ε * signFlip ε' := by
  refine LinearEquiv.ext fun x => ?_
  funext μ
  change ((((ε * ε') μ : ℤˣ) : ℤ) : ℝ) * x μ = ((ε μ : ℤ) : ℝ) * (((ε' μ : ℤ) : ℝ) * x μ)
  simp [mul_assoc]
theorem signFlip_one : signFlip 1 = 1 := by
  refine LinearEquiv.ext fun x => ?_
  funext μ
  change (((1 : Fin 4 → ℤˣ) μ : ℤ) : ℝ) * x μ = x μ
  simp
theorem axisSignChangesSubgroup (D : Setup) : AxisSignChangesSubgroup D := by
  refine ⟨by rw [axisSignChanges_eq_signFlipSet]; exact ncard_signFlipSet,
    signFlipGroup, ?_, ?_, ?_⟩
  · rintro γ ⟨ε, rfl⟩
    exact signFlipSet_subset_hypercubicGroup ⟨ε, rfl⟩
  · rw [axisSignChanges_eq_signFlipSet]
    ext γ
    constructor
    · rintro ⟨g, ⟨ε, rfl⟩, rfl⟩
      exact ⟨ε, rfl⟩
    · rintro ⟨ε, rfl⟩
      exact ⟨signFlip ε, ⟨ε, rfl⟩, rfl⟩
  · refine le_antisymm ?_ ((Subgroup.closure_le _).mpr ?_)
    · rintro _ ⟨ε, rfl⟩
      have hsingle : ∀ (μ : Fin 4) (u : ℤˣ), signFlip (Function.update 1 μ u) ∈
          Subgroup.closure {γ : AmbientSpace ≃ₗ[ℝ] AmbientSpace |
            ∃ μ : Fin 4, ⇑γ = (axialReflection D.mesh μ).toFun} := by
        intro μ u
        rcases Int.units_eq_one_or u with rfl | rfl
        · have h1 : Function.update (1 : Fin 4 → ℤˣ) μ 1 = 1 := Function.update_eq_self μ 1
          rw [h1, signFlip_one]
          exact one_mem _
        · exact Subgroup.subset_closure ⟨μ, signFlip_singleNegation μ⟩
      have hε : ε = Function.update (1 : Fin 4 → ℤˣ) 0 (ε 0) *
          Function.update (1 : Fin 4 → ℤˣ) 1 (ε 1) * Function.update (1 : Fin 4 → ℤˣ) 2 (ε 2) *
          Function.update (1 : Fin 4 → ℤˣ) 3 (ε 3) := by
        funext ν
        fin_cases ν <;> simp [Function.update]
      have hfac : signFlip ε =
          signFlip (Function.update (1 : Fin 4 → ℤˣ) 0 (ε 0)) *
            signFlip (Function.update (1 : Fin 4 → ℤˣ) 1 (ε 1)) *
            signFlip (Function.update (1 : Fin 4 → ℤˣ) 2 (ε 2)) *
            signFlip (Function.update (1 : Fin 4 → ℤˣ) 3 (ε 3)) := by
        rw [← signFlip_mul, ← signFlip_mul, ← signFlip_mul]
        exact congrArg _ hε
      have hmem := mul_mem (mul_mem (mul_mem (hsingle 0 (ε 0)) (hsingle 1 (ε 1)))
        (hsingle 2 (ε 2))) (hsingle 3 (ε 3))
      rw [← hfac] at hmem
      exact hmem
    · rintro γ ⟨μ, hγ⟩
      exact ⟨singleNegation μ, LinearEquiv.ext fun x =>
        congrFun ((signFlip_singleNegation μ).trans hγ.symm) x⟩
theorem symmetryActionFacts_holds (hcls : Tower.OrthogonalMotions.Classification)
    (hact : InfiniteLattice.SymmetryActionOnObservables) : SymmetryActionFacts := by
  intro D
  have hm := hcls.2.1
  have hall := hact ⟨D.mesh, D.mesh_pos⟩
  have hhom : PullbackFieldIsHomeomorph D.mesh := hall.2.1
  have hobs : ActOnPreservesAlgebraAndRegions D.mesh := hall.2.2.1
  have hnorm : ActOnLinearIsometric D.mesh := hall.2.2.2.2.2.1
  have hlocal : ActOnLocalRegions D.mesh := hall.2.2.2.2.2.2.2.2.1
  have hinv : LatticeSymmetryInverses D.mesh := hall.2.2.2.2.2.2.2.2.2.1
  have hset : ∀ (r : LatticeSymmetry D.mesh) (S : Set AmbientSpace),
      (fun F : GaugeField D.mesh → ℂ => r.actOn F) '' regionObservables D.mesh S =
        regionObservables D.mesh (r.setImage S) := fun r S => (hobs r).2 S
  refine ⟨⟨symmetriesAreMotions D hm, motionsFormGroup D hm hinv⟩, ⟨?_, ?_⟩,
    fun P => toFun_mem_latticeMotions D.mesh_pos hm P.symmetry, axisSignChangesSubgroup D, ?_⟩
  · intro r r' _ _
    exact ⟨(hhom r).2, pullbackField_comp r r', fun t ht =>
      ⟨fun U => pullbackField_leftInverse ht.2 U, fun U => pullbackField_leftInverse ht.1 U⟩⟩
  · intro r r' _ _
    refine ⟨fun _ _ => rfl, fun _ => rfl, hset r, fun F => ?_⟩
    funext U
    change F ((r.comp r').pullbackField U) = F (r'.pullbackField (r.pullbackField U))
    rw [pullbackField_comp]
    rfl
  · intro r _ F hF
    refine ⟨((hnorm r).2 F hF).2.2.2, fun hc => hc.comp (hhom r).2.continuous, fun S hS => ?_⟩
    have hFS := hS.2
    obtain ⟨hFobs, ⟨S₀, hS₀, hm₀⟩, hcont⟩ :
        IsBoundedObservable F ∧ IsLocalObservable F ∧ Continuous F := hS.1
    have hrS : r.actOn F ∈ regionObservables D.mesh (r.setImage S) := by
      rw [← hset r S]
      exact ⟨F, hFS, rfl⟩
    have hl : F ∈ localRegionObservables D.mesh univ := by
      refine mem_iUnion₂.mpr ⟨S₀, hS₀, hFobs, ?_⟩
      rw [univ_inter]
      exact hm₀
    have hrl : r.actOn F ∈ localRegionObservables D.mesh (r.setImage univ) := by
      rw [← hlocal.1 r univ]
      exact ⟨F, hl, rfl⟩
    obtain ⟨Q, hQ, hrQ⟩ := mem_iUnion₂.mp hrl
    exact ⟨⟨hrS.1, ⟨_, Bornology.IsBounded.subset hQ inter_subset_right, hrQ.2⟩,
      hcont.comp (hhom r).2.continuous⟩, hrS⟩
end YangMills.Construction.LatticePhases.LatticeSymmetryAction
end
