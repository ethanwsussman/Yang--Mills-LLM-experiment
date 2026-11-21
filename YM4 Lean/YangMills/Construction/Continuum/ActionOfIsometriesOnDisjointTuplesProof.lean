import YangMills.Construction.Continuum.OperationsOnFunctionsOfSeveralPoints
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotionsProof
import YangMills.Construction.Continuum.ActionOfIsometriesOnDisjointTuples
import Mathlib
set_option autoImplicit false
open Matrix MeasureTheory Set
namespace YangMills.Construction.DisjointTuples.IsometryAction
open InfiniteLattice (IsSpaceIsometry)
open SchwingerFunctions (IsC1c)
open TestFunctions (sharpNormR4 lipConstR4 uniformNorm bestLipschitzConstant)
theorem invMap_comp {a b : (Fin 4 → ℝ) → Fin 4 → ℝ} (ha : Function.Bijective a)
    (hb : Function.Bijective b) : invMap (a ∘ b) = invMap b ∘ invMap a := by
  funext x
  obtain ⟨y, rfl⟩ := ha.2 x
  obtain ⟨z, rfl⟩ := hb.2 y
  have e₁ : invMap (a ∘ b) ((a ∘ b) z) = z := Function.leftInverse_invFun (ha.1.comp hb.1) z
  have e₂ : invMap a (a (b z)) = b z := Function.leftInverse_invFun ha.1 _
  have e₃ : invMap b (b z) = z := Function.leftInverse_invFun hb.1 _
  simp only [Function.comp_apply] at e₁ ⊢
  rw [e₁, e₂, e₃]
theorem pushFun_comp {E : Type*} {a b : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (ha : Function.Bijective a) (hb : Function.Bijective b) (φ : (Fin 4 → ℝ) → E) :
    pushFun (a ∘ b) φ = pushFun a (pushFun b φ) := by
  simp only [pushFun, invMap_comp ha hb, Function.comp_assoc]
theorem isometry_toEuclidean {r : (Fin 4 → ℝ) → Fin 4 → ℝ} (hr : IsSpaceIsometry r) :
    Isometry (fun x : EuclideanSpace ℝ (Fin 4) => (WithLp.toLp 2 (r (WithLp.ofLp x)) :
      EuclideanSpace ℝ (Fin 4))) := by
  refine Isometry.of_dist_eq fun x y => ?_
  have hxy := hr (WithLp.ofLp x) (WithLp.ofLp y)
  simp only [InfiniteLattice.euclidDist, TorusMetric.euclidNormVec, Pi.sub_apply] at hxy
  simp only [EuclideanSpace.dist_eq, Real.dist_eq, sq_abs]
  exact hxy
theorem bijective_of_isSpaceIsometry {r : (Fin 4 → ℝ) → Fin 4 → ℝ} (hr : IsSpaceIsometry r) :
    Function.Bijective r := by
  have hI := isometry_toEuclidean hr
  have hsurj : Function.Surjective (hI.affineIsometryOfStrictConvexSpace) := by
    have hlin : Function.Surjective
        (hI.affineIsometryOfStrictConvexSpace).linearIsometry.toLinearMap :=
      LinearMap.injective_iff_surjective.1
        (hI.affineIsometryOfStrictConvexSpace).linearIsometry.injective
    exact (AffineMap.linear_surjective_iff
      (hI.affineIsometryOfStrictConvexSpace).toAffineMap).1 hlin
  constructor
  · intro x y hxy
    have he : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 4)) = WithLp.toLp 2 y := by
      apply hI.injective
      simp [hxy]
    simpa using congrArg WithLp.ofLp he
  · intro y
    obtain ⟨z, hz⟩ := hsurj (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 4))
    refine ⟨WithLp.ofLp z, ?_⟩
    have hz' : (WithLp.toLp 2 (r (WithLp.ofLp z)) : EuclideanSpace ℝ (Fin 4)) =
        WithLp.toLp 2 y := hz
    simpa using congrArg WithLp.ofLp hz'
section Affine
variable {Q : Matrix (Fin 4) (Fin 4) ℝ}
theorem mul_transpose_eq_one (hQ : Q ∈ O4) : Q * Qᵀ = 1 := by apply _root_.YangMills.Construction.Tower.OrthogonalMotions.orth_mul_transpose_self <;> assumption
theorem inv_eq_transpose (hQ : Q ∈ O4) : Q⁻¹ = Qᵀ :=
  Matrix.inv_eq_right_inv (mul_transpose_eq_one hQ)
theorem transpose_mul_eq_one (hQ : Q ∈ O4) : Qᵀ * Q = 1 := by apply _root_.YangMills.Construction.ConfigSpace.orth_transpose_mul_self <;> assumption
theorem contDiff_mulVec (A : Matrix (Fin 4) (Fin 4) ℝ) :
    ContDiff ℝ 1 (fun x : Fin 4 → ℝ => A *ᵥ x) :=
  (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).contDiff
noncomputable def affineEuclidHomeomorph (hQ : Q ∈ O4) (c : Fin 4 → ℝ) :
    (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toFun := affineEuclid Q c
  invFun := fun x => Q⁻¹ *ᵥ (x - c)
  left_inv := fun x => by
    simp [affineEuclid, inv_eq_transpose hQ, Matrix.mulVec_mulVec, transpose_mul_eq_one hQ]
  right_inv := fun x => by
    simp [affineEuclid, inv_eq_transpose hQ, Matrix.mulVec_mulVec, mul_transpose_eq_one hQ]
  continuous_toFun := ((contDiff_mulVec Q).add contDiff_const).continuous
  continuous_invFun := ((contDiff_mulVec Q⁻¹).comp (contDiff_id.sub contDiff_const)).continuous
theorem pushFun_affineEuclid {E : Type*} (hQ : Q ∈ O4) (c : Fin 4 → ℝ)
    (φ : (Fin 4 → ℝ) → E) :
    pushFun (affineEuclid Q c) φ = φ ∘ (affineEuclidHomeomorph hQ c).symm := by
  funext x
  simp only [pushFun, Function.comp_apply, invMap_affineEuclid hQ]
  rfl
theorem tsupport_pushFun_affineEuclid (hQ : Q ∈ O4) (c : Fin 4 → ℝ) (φ : RealFun) :
    tsupport (pushFun (affineEuclid Q c) φ) = affineEuclid Q c '' tsupport φ := by
  rw [pushFun_affineEuclid hQ, tsupport_comp_eq_preimage φ (affineEuclidHomeomorph hQ c).symm]
  exact ((affineEuclidHomeomorph hQ c).toEquiv.image_eq_preimage_symm _).symm
theorem mapsC1cAndSupport_affineEuclid (hQ : Q ∈ O4) (c : Fin 4 → ℝ) :
    MapsC1cAndSupport (affineEuclid Q c) := by
  intro φ hφ
  have hs := tsupport_pushFun_affineEuclid hQ c φ
  refine ⟨⟨?_, ?_⟩, hs⟩
  · rw [pushFun_affineEuclid hQ]
    exact hφ.1.comp ((contDiff_mulVec Q⁻¹).comp (contDiff_id.sub contDiff_const))
  · change IsCompact (tsupport _)
    rw [hs]
    exact IsCompact.image hφ.2 (affineEuclidHomeomorph hQ c).continuous
theorem affineEuclid_injective (hQ : Q ∈ O4) (c : Fin 4 → ℝ) :
    Function.Injective (affineEuclid Q c) :=
  (affineEuclidHomeomorph hQ c).injective
theorem affineEuclid_bijective (hQ : Q ∈ O4) (c : Fin 4 → ℝ) :
    Function.Bijective (affineEuclid Q c) :=
  (affineEuclidHomeomorph hQ c).bijective
theorem isDisjointTuple_pushList (hQ : Q ∈ O4) (c : Fin 4 → ℝ) (X : DisjointTuple) :
    IsDisjointTuple (pushList (affineEuclid Q c) X.1) := by
  refine ⟨fun ψ hψ => ?_, ?_⟩
  · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hψ
    exact (mapsC1cAndSupport_affineEuclid hQ c φ (X.2.1 φ hφ)).1
  · refine List.pairwise_map.2 (X.2.2.imp fun {φ ψ} hφψ => ?_)
    rw [tsupport_pushFun_affineEuclid hQ, tsupport_pushFun_affineEuclid hQ]
    exact (Set.disjoint_image_iff (affineEuclid_injective hQ c)).2 hφψ
theorem pushTuple_affineEuclid_val (hQ : Q ∈ O4) (c : Fin 4 → ℝ) (X : DisjointTuple) :
    (pushTuple (affineEuclid Q c) X).1 = pushList (affineEuclid Q c) X.1 :=
  pushTuple_val _ X (isDisjointTuple_pushList hQ c X)
theorem preservesAppend_affineEuclid (hQ : Q ∈ O4) (c : Fin 4 → ℝ) :
    PreservesAppend (affineEuclid Q c) := by
  intro X Y hXY
  refine ⟨isDisjointTuple_pushList hQ c X, isDisjointTuple_pushList hQ c Y, ?_, ?_⟩
  · intro φ hφ ψ hψ
    rw [pushTuple_affineEuclid_val hQ] at hφ hψ
    obtain ⟨φ', hφ', rfl⟩ := List.mem_map.1 hφ
    obtain ⟨ψ', hψ', rfl⟩ := List.mem_map.1 hψ
    rw [tsupport_pushFun_affineEuclid hQ, tsupport_pushFun_affineEuclid hQ]
    exact (Set.disjoint_image_iff (affineEuclid_injective hQ c)).2 (hXY φ' hφ' ψ' hψ')
  · apply Subtype.ext
    rw [pushTuple_affineEuclid_val hQ]
    simp [DisjointTuple.append, pushTuple_affineEuclid_val hQ, pushList]
theorem translate_eq_affineEuclid (v : Fin 4 → ℝ) : translate v = affineEuclid 1 v := by
  funext x
  simp [translate, affineEuclid]
theorem one_mem_O4 : (1 : Matrix (Fin 4) (Fin 4) ℝ) ∈ O4 :=
  one_mem _
theorem translate_bijective (v : Fin 4 → ℝ) : Function.Bijective (translate v) := by
  rw [translate_eq_affineEuclid]
  exact affineEuclid_bijective one_mem_O4 v
theorem pushTuple_translate_val (v : Fin 4 → ℝ) (X : DisjointTuple) :
    (pushTuple (translate v) X).1 = pushList (translate v) X.1 := by
  rw [translate_eq_affineEuclid]
  exact pushTuple_affineEuclid_val one_mem_O4 v X
theorem intertwinesTranslations_affineEuclid (hQ : Q ∈ O4) (c : Fin 4 → ℝ) :
    IntertwinesTranslations Q (affineEuclid Q c) := by
  intro v
  have hmap : affineEuclid Q c ∘ translate v = translate (Q *ᵥ v) ∘ affineEuclid Q c := by
    funext x
    simp only [Function.comp_apply, affineEuclid, translate, Matrix.mulVec_add]
    abel
  have hb := affineEuclid_bijective hQ c
  have hfun : ∀ (E : Type) (φ : (Fin 4 → ℝ) → E),
      pushFun (affineEuclid Q c) (pushFun (translate v) φ) =
        pushFun (translate (Q *ᵥ v)) (pushFun (affineEuclid Q c) φ) := by
    intro E φ
    rw [← pushFun_comp hb (translate_bijective v), hmap,
      pushFun_comp (translate_bijective _) hb]
  have htup : ∀ X : DisjointTuple,
      pushTuple (affineEuclid Q c) (pushTuple (translate v) X) =
        pushTuple (translate (Q *ᵥ v)) (pushTuple (affineEuclid Q c) X) := by
    intro X
    apply Subtype.ext
    rw [pushTuple_affineEuclid_val hQ, pushTuple_translate_val, pushTuple_translate_val,
      pushTuple_affineEuclid_val hQ]
    simp only [pushList, List.map_map]
    exact List.map_congr_left fun φ _ => hfun ℝ φ
  refine ⟨hmap, hfun, htup, fun F => ?_⟩
  have hcomp : pushTuple (affineEuclid Q c) ∘ pushTuple (translate v) =
      pushTuple (translate (Q *ᵥ v)) ∘ pushTuple (affineEuclid Q c) := funext htup
  simp only [liftMap, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp, hcomp]
theorem lipConstR4_comp {g : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : Function.Surjective g)
    (hd : ∀ x y, TestFunctions.euclidDistR4 (g x) (g y) = TestFunctions.euclidDistR4 x y)
    (φ : RealFun) : lipConstR4 (φ ∘ g) = lipConstR4 φ := by
  unfold lipConstR4 bestLipschitzConstant
  congr 1
  ext C
  constructor
  · rintro ⟨hC, hle⟩
    refine ⟨hC, fun x y => ?_⟩
    obtain ⟨x', rfl⟩ := hs x
    obtain ⟨y', rfl⟩ := hs y
    rw [hd]
    exact hle x' y'
  · rintro ⟨hC, hle⟩
    refine ⟨hC, fun x y => ?_⟩
    have hxy := hle (g x) (g y)
    rwa [hd] at hxy
theorem sharpNormInvariant_affineEuclid (hQ : Q ∈ O4) (c : Fin 4 → ℝ)
    (hr : IsSpaceIsometry (affineEuclid Q c)) : SharpNormInvariant (affineEuclid Q c) := by
  intro M _ φ _
  have hs : Function.Surjective (affineEuclidHomeomorph hQ c).symm :=
    (affineEuclidHomeomorph hQ c).symm.surjective
  have hd : ∀ x y, TestFunctions.euclidDistR4 ((affineEuclidHomeomorph hQ c).symm x)
      ((affineEuclidHomeomorph hQ c).symm y) = TestFunctions.euclidDistR4 x y := by
    intro x y
    have hxy := hr ((affineEuclidHomeomorph hQ c).symm x) ((affineEuclidHomeomorph hQ c).symm y)
    have hx : affineEuclid Q c ((affineEuclidHomeomorph hQ c).symm x) = x :=
      (affineEuclidHomeomorph hQ c).apply_symm_apply x
    have hy : affineEuclid Q c ((affineEuclidHomeomorph hQ c).symm y) = y :=
      (affineEuclidHomeomorph hQ c).apply_symm_apply y
    rw [hx, hy] at hxy
    exact hxy.symm
  have hsup : uniformNorm (φ ∘ (affineEuclidHomeomorph hQ c).symm) = uniformNorm φ :=
    hs.iSup_comp fun x => ‖φ x‖
  rw [pushFun_affineEuclid hQ]
  simp only [sharpNormR4, hsup, lipConstR4_comp hs hd φ]
theorem abs_det_inv_eq_one (hQ : Q ∈ O4) : |(Q⁻¹).det| = 1 := by
  have hd : Q.det * Q.det = 1 := by
    have hm := congrArg Matrix.det (mul_transpose_eq_one hQ)
    simpa [Matrix.det_mul, Matrix.det_transpose] using hm
  rw [inv_eq_transpose hQ, Matrix.det_transpose]
  have habs : |Q.det| * |Q.det| = 1 := by rw [← abs_mul, hd, abs_one]
  nlinarith [abs_nonneg Q.det, sq_nonneg (|Q.det| - 1), sq_nonneg (|Q.det| + 1)]
theorem integralInvariant_affineEuclid (hQ : Q ∈ O4) (c : Fin 4 → ℝ) :
    IntegralInvariant (affineEuclid Q c) := by
  intro φ hφ
  have hdet : (Q⁻¹).det ≠ 0 := by
    intro h0
    have h1 := abs_det_inv_eq_one hQ
    rw [h0, abs_zero] at h1
    exact zero_ne_one h1
  have hmap : Measure.map (Matrix.toLin' Q⁻¹) (volume : Measure (Fin 4 → ℝ)) = volume := by
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, abs_inv, abs_det_inv_eq_one hQ]
    simp
  have hcont : Continuous φ := hφ.1.continuous
  have hlin : Continuous (Matrix.toLin' Q⁻¹) := (contDiff_mulVec Q⁻¹).continuous
  have e₁ : ∫ x, pushFun (affineEuclid Q c) φ x = ∫ x, φ (Q⁻¹ *ᵥ (x - c)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [pushFun, invMap_affineEuclid hQ]
  have e₂ : ∫ x, φ (Q⁻¹ *ᵥ (x - c)) = ∫ x, φ (Q⁻¹ *ᵥ x) :=
    integral_sub_right_eq_self (fun x => φ (Q⁻¹ *ᵥ x)) c
  have e₃ : ∫ x, φ (Q⁻¹ *ᵥ x) = ∫ x, φ (Matrix.toLin' Q⁻¹ x) := by
    simp [Matrix.toLin'_apply]
  rw [e₁, e₂, e₃, ← integral_map hlin.aemeasurable hcont.aestronglyMeasurable, hmap]
end Affine
theorem pushFunComp : PushFunComp := by
  intro r r' hr hr' E φ
  exact pushFun_comp (bijective_of_isSpaceIsometry hr)
    (bijective_of_isSpaceIsometry hr') φ
def singleton (φ : RealFun) (hφ : IsC1c φ) : DisjointTuple :=
  ⟨[φ], by simpa [IsDisjointTuple] using hφ⟩
theorem existsLinearNotMultilinear : ExistsLinearNotMultilinear := by
  classical
  let b : ContDiffBump (0 : Fin 4 → ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let φ : RealFun := b
  have hφ : IsC1c φ := ⟨b.contDiff, b.hasCompactSupport⟩
  have hφ0 : φ 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  have hφφ : IsC1c (φ + φ) := ⟨ContDiff.add hφ.1 hφ.1, hφ.2.add hφ.2⟩
  let X : DisjointTuple := singleton φ hφ
  let Z : DisjointTuple := singleton (φ + φ) hφφ
  have hne : Z ≠ X := by
    intro hZ
    have e₁ : ([φ + φ] : List RealFun) = [φ] := congrArg Subtype.val hZ
    have e₂ : φ + φ = φ := by simpa using e₁
    have e₃ := congrFun e₂ 0
    simp only [Pi.add_apply, hφ0] at e₃
    norm_num at e₃
  refine ⟨liftFun fun Y => if Y = X then 1 else 0, φ, φ, X, X, Z, hφ, hφ, rfl, rfl, rfl, ?_⟩
  rw [liftFun_ofTuple, liftFun_ofTuple]
  simp [hne]
  norm_num
theorem isometryActionFacts_holds : IsometryActionFacts := by
  refine ⟨?_, pushFunComp, existsLinearNotMultilinear⟩
  rintro r c Q hr hQ rfl
  exact ⟨mapsC1cAndSupport_affineEuclid hQ c, preservesAppend_affineEuclid hQ c,
    intertwinesTranslations_affineEuclid hQ c, sharpNormInvariant_affineEuclid hQ c hr,
    integralInvariant_affineEuclid hQ c⟩
end YangMills.Construction.DisjointTuples.IsometryAction
