import YangMills.Construction.Continuum.CubicGroupAndHypercubicMapsKeepingTheTimeAxisProof
import YangMills.Construction.Continuum.OrthogonalBlockEmbedding
import YangMills.Construction.Continuum.SharpNormOfATestFunctionAndNeighbourhoodsOfDisjointCompactSetsProof
import YangMills.Construction.ReflectionPositivity.ContractionOfTheLimitOfALatticeApproximationProof
import YangMills.Construction.BoundsOnEverySide.MovingTuplesOfALimitAlongStatesProof
import YangMills.Construction.Continuum.RulesOfTheOrthogonalAction
import YangMills.Construction.InfiniteLattice.ReflectionsAndLatticeMirrorsProof
import YangMills.Construction.ReflectionPositivity.CovarianceAlgebraAndLocalisationOfTheRepresentativesProof
import YangMills.Construction.ReflectionPositivity.FactsOnSeparatedTuplesOfFourSpaceProof
import Mathlib
set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
namespace YangMills.Construction
open Orthogonal SeparatedTuples
namespace OrthogonalAction
open InfiniteLattice (AmbientSpace)
open TimeAxis (upperHalfSpace timeComponent timeIdx)
open TorusLifts (hyperoctahedralGroupEuclidean signedCoordinateEquiv)
namespace Laws
theorem coe_inv_eq_transpose (Q : orthogonalGroupFour) : (Q⁻¹ : orthogonalGroupFour).1 = Q.1ᵀ := by
  show star Q.1 = Q.1ᵀ
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
theorem matMap_mul (Q Q' : orthogonalGroupFour) (x : AmbientSpace) :
    matMap (Q * Q') x = matMap Q (matMap Q' x) := by
  show (Q.1 * Q'.1) *ᵥ x = Q.1 *ᵥ (Q'.1 *ᵥ x)
  rw [Matrix.mulVec_mulVec]
theorem matMap_one (x : AmbientSpace) : matMap 1 x = x := by
  show (1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ x = x
  rw [Matrix.one_mulVec]
theorem matMap_inv_matMap (Q : orthogonalGroupFour) (x : AmbientSpace) :
    matMap Q⁻¹ (matMap Q x) = x := by
  rw [← matMap_mul, inv_mul_cancel, matMap_one]
theorem matMap_matMap_inv (Q : orthogonalGroupFour) (x : AmbientSpace) :
    matMap Q (matMap Q⁻¹ x) = x := by
  rw [← matMap_mul, mul_inv_cancel, matMap_one]
theorem matMap_sub (Q : orthogonalGroupFour) (x y : AmbientSpace) :
    matMap Q (x - y) = matMap Q x - matMap Q y :=
  Matrix.mulVec_sub _ _ _
theorem matMap_smul (Q : orthogonalGroupFour) (t : ℝ) (x : AmbientSpace) :
    matMap Q (t • x) = t • matMap Q x :=
  Matrix.mulVec_smul _ _ _
theorem contDiff_matMap (Q : orthogonalGroupFour) : ContDiff ℝ 1 (matMap Q) :=
  (LinearMap.toContinuousLinearMap (Matrix.mulVecLin Q.1)).contDiff
def matHomeomorph (Q : orthogonalGroupFour) : AmbientSpace ≃ₜ AmbientSpace where
  toFun := matMap Q
  invFun := matMap Q⁻¹
  left_inv := matMap_inv_matMap Q
  right_inv := matMap_matMap_inv Q
  continuous_toFun := (contDiff_matMap Q).continuous
  continuous_invFun := (contDiff_matMap Q⁻¹).continuous
theorem dotProduct_self_mulVec (Q : orthogonalGroupFour) (x : AmbientSpace) :
    (Q.1 *ᵥ x) ⬝ᵥ (Q.1 *ᵥ x) = x ⬝ᵥ x := by
  have h : Q.1ᵀ *ᵥ (Q.1 *ᵥ x) = x := by
    rw [← coe_inv_eq_transpose]
    exact matMap_inv_matMap Q x
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h, dotProduct_comm]
theorem euclidNormVec_matMap (Q : orthogonalGroupFour) (x : AmbientSpace) :
    TorusMetric.euclidNormVec (matMap Q x) = TorusMetric.euclidNormVec x := by
  have h : ∀ y : AmbientSpace, ∑ μ, y μ ^ 2 = y ⬝ᵥ y := fun y => by
    simp [dotProduct, sq]
  unfold TorusMetric.euclidNormVec
  rw [h, h]
  exact congrArg Real.sqrt (dotProduct_self_mulVec Q x)
theorem euclidDistR4_matMap (Q : orthogonalGroupFour) (x y : AmbientSpace) :
    TestFunctions.euclidDistR4 (matMap Q x) (matMap Q y) = TestFunctions.euclidDistR4 x y := by
  unfold TestFunctions.euclidDistR4
  rw [← matMap_sub, euclidNormVec_matMap]
theorem invMap_eq_symm (e : AmbientSpace ≃ₜ AmbientSpace) : invMap e = e.symm := by apply _root_.YangMills.Construction.BoundsOnEverySide.TranslatedTuples.invMap_homeo_eq <;> assumption
theorem tsupport_comp_homeomorph_symm (e : AmbientSpace ≃ₜ AmbientSpace) (f : RealValued) :
    tsupport (f ∘ e.symm) = e '' tsupport f := by
  unfold tsupport
  rw [e.image_closure]
  congr 1
  ext x
  constructor
  · intro h
    exact ⟨e.symm x, h, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [Function.mem_support] using hy
theorem isC1c_comp_symm (e : AmbientSpace ≃ₜ AmbientSpace) (he : ContDiff ℝ 1 e.symm)
    {f : RealValued} (hf : IsC1c f) : IsC1c (f ∘ e.symm) := by
  refine ⟨ContDiff.comp (show ContDiff ℝ 1 f from hf.1) he, ?_⟩
  unfold HasCompactSupport
  rw [tsupport_comp_homeomorph_symm]
  exact IsCompact.image hf.2 e.continuous
theorem isDisjointlySupported_map_comp (e : AmbientSpace ≃ₜ AmbientSpace)
    (he : ContDiff ℝ 1 e.symm) {X : List RealValued}
    (hX : IsDisjointlySupported X) : IsDisjointlySupported (X.map fun f => f ∘ e.symm) := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.isDisjointlySupported_map_comp <;> assumption
theorem push_coe (e : AmbientSpace ≃ₜ AmbientSpace) (he : ContDiff ℝ 1 e.symm) (X : SepTuple) :
    (push e X).1 = X.1.map fun f => f ∘ e.symm := by
  have h : pushList e X.1 = X.1.map fun f => f ∘ e.symm := by
    rw [pushList, invMap_eq_symm]
  have hs : IsDisjointlySupported (pushList e X.1) := by
    rw [h]
    exact isDisjointlySupported_map_comp e he X.2
  unfold push
  rw [dif_pos hs]
  exact h
theorem push_mem_supportedIn (e : AmbientSpace ≃ₜ AmbientSpace) (he : ContDiff ℝ 1 e.symm)
    {O O' : Set AmbientSpace} (h : e '' O ⊆ O') {X : SepTuple} (hX : X ∈ supportedIn O) :
    push e X ∈ supportedIn O' := by
  intro g hg
  rw [push_coe e he] at hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  rw [tsupport_comp_homeomorph_symm]
  exact (Set.image_mono (hX f hf)).trans h
theorem composable_push (e : AmbientSpace ≃ₜ AmbientSpace) (he : ContDiff ℝ 1 e.symm)
    {X Y : SepTuple} (h : SepTuple.Composable X Y) :
    SepTuple.Composable (push e X) (push e Y) := by
  intro g hg k hk
  rw [push_coe e he] at hg hk
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hk
  rw [tsupport_comp_homeomorph_symm, tsupport_comp_homeomorph_symm]
  exact (Set.disjoint_image_iff e.injective).2 (h f hf l hl)
theorem push_juxt (e : AmbientSpace ≃ₜ AmbientSpace) (he : ContDiff ℝ 1 e.symm) {X Y : SepTuple}
    (h : SepTuple.Composable X Y) :
    push e (SepTuple.juxt X Y) = SepTuple.juxt (push e X) (push e Y) := by
  apply Subtype.ext
  rw [push_coe e he, SepTuple.juxt_val h, SepTuple.juxt_val (composable_push e he h),
    push_coe e he, push_coe e he, List.map_append]
theorem push_push_comm (e e' e'' : AmbientSpace ≃ₜ AmbientSpace) (he : ContDiff ℝ 1 e.symm)
    (he' : ContDiff ℝ 1 e'.symm) (he'' : ContDiff ℝ 1 e''.symm)
    (h : ∀ x, e'.symm (e.symm x) = e.symm (e''.symm x)) (X : SepTuple) :
    push e (push e' X) = push e'' (push e X) := by
  apply Subtype.ext
  rw [push_coe e he, push_coe e' he', push_coe e'' he'', push_coe e he, List.map_map,
    List.map_map]
  refine List.map_congr_left fun f _ => ?_
  funext x
  simp [h]
theorem contDiff_timeReflection : ContDiff ℝ 1 TimeAxis.timeReflection := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_apply ℝ ℝ (0 : Fin 4)
  · exact contDiff_apply ℝ ℝ (1 : Fin 4)
  · exact contDiff_apply ℝ ℝ (2 : Fin 4)
  · exact (contDiff_apply ℝ ℝ (3 : Fin 4)).neg
theorem timeReflection_involutive (x : AmbientSpace) :
    TimeAxis.timeReflection (TimeAxis.timeReflection x) = x := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.timeReflection_involutive_apply <;> assumption
def timeReflectionHomeomorph : AmbientSpace ≃ₜ AmbientSpace where
  toFun := TimeAxis.timeReflection
  invFun := TimeAxis.timeReflection
  left_inv := timeReflection_involutive
  right_inv := timeReflection_involutive
  continuous_toFun := contDiff_timeReflection.continuous
  continuous_invFun := contDiff_timeReflection.continuous
def translateHomeomorph (a : AmbientSpace) : AmbientSpace ≃ₜ AmbientSpace where
  toFun := translate a
  invFun := fun x => x - a
  left_inv x := by simp [SeparatedTuples.translate]
  right_inv x := by simp [SeparatedTuples.translate]
  continuous_toFun := by
    unfold SeparatedTuples.translate
    fun_prop
  continuous_invFun := by fun_prop
theorem contDiff_translateHomeomorph_symm (a : AmbientSpace) :
    ContDiff ℝ 1 (translateHomeomorph a).symm :=
  contDiff_id.sub contDiff_const
theorem orthogonalAct_orthogonalAct (Q Q' : orthogonalGroupFour) (f : RealValued) :
    orthogonalAct Q (orthogonalAct Q' f) = orthogonalAct (Q * Q') f := by
  funext x
  show f (matMap Q'⁻¹ (matMap Q⁻¹ x)) = f (matMap (Q * Q')⁻¹ x)
  rw [_root_.mul_inv_rev, matMap_mul]
theorem orthogonalAct_one (f : RealValued) : orthogonalAct 1 f = f := by
  funext x
  show f (matMap 1⁻¹ x) = f x
  rw [inv_one, matMap_one]
theorem orthogonalAct_apply_matMap (Q : orthogonalGroupFour) (f : RealValued) (x : AmbientSpace) :
    orthogonalAct Q f (matMap Q x) = f x :=
  congrArg f (matMap_inv_matMap Q x)
theorem uniformNorm_orthogonalAct (Q : orthogonalGroupFour) (f : RealValued) :
    TestFunctions.uniformNorm (orthogonalAct Q f) = TestFunctions.uniformNorm f :=
  (matHomeomorph Q).symm.surjective.iSup_comp fun y => ‖f y‖
theorem lipConstR4_orthogonalAct (Q : orthogonalGroupFour) (f : RealValued) :
    TestFunctions.lipConstR4 (orthogonalAct Q f) = TestFunctions.lipConstR4 f := by
  unfold TestFunctions.lipConstR4 TestFunctions.bestLipschitzConstant
  congr 1
  ext C
  refine and_congr_right fun _ => ⟨fun h x y => ?_, fun h x y => ?_⟩
  · have := h (matMap Q x) (matMap Q y)
    rw [euclidDistR4_matMap, orthogonalAct_apply_matMap, orthogonalAct_apply_matMap] at this
    exact this
  · have := h (matMap Q⁻¹ x) (matMap Q⁻¹ y)
    rw [euclidDistR4_matMap] at this
    exact this
theorem sharpNormR4_orthogonalAct (M : ℝ) (Q : orthogonalGroupFour) (f : RealValued) :
    TestFunctions.sharpNormR4 M (orthogonalAct Q f) = TestFunctions.sharpNormR4 M f := by
  unfold TestFunctions.sharpNormR4
  rw [uniformNorm_orthogonalAct, lipConstR4_orthogonalAct]
theorem det_mul_self_eq_one (Q : orthogonalGroupFour) : Q.1.det * Q.1.det = 1 := by
  have h : Q.1ᵀ * Q.1 = 1 := by
    rw [← coe_inv_eq_transpose]
    exact congrArg Subtype.val (inv_mul_cancel Q)
  have := congrArg Matrix.det h
  rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
theorem measurePreserving_matMap (Q : orthogonalGroupFour) :
    MeasurePreserving (matMap Q) volume volume := by
  refine ⟨(contDiff_matMap Q).continuous.measurable, ?_⟩
  have hsq := det_mul_self_eq_one Q
  have hd : Q.1.det ≠ 0 := fun h => by simp [h] at hsq
  have habs : |(Q.1.det)⁻¹| = 1 := by
    rw [abs_inv]
    have : |Q.1.det| * |Q.1.det| = 1 := by rw [← abs_mul, hsq, abs_one]
    have h0 : 0 ≤ |Q.1.det| := abs_nonneg _
    have : |Q.1.det| = 1 := by nlinarith
    rw [this, inv_one]
  have := Real.map_matrix_volume_pi_eq_smul_volume_pi hd
  rw [habs, ENNReal.ofReal_one, one_smul] at this
  exact this
theorem integral_orthogonalAct (Q : orthogonalGroupFour) (f : RealValued) :
    ∫ x, orthogonalAct Q f x = ∫ x, f x :=
  (measurePreserving_matMap Q⁻¹).integral_comp (matHomeomorph Q⁻¹).measurableEmbedding f
theorem partialDerivR4_eq_fderiv {f : RealValued} (hf : Differentiable ℝ f) (μ : Fin 4)
    (x : AmbientSpace) :
    TestFunctions.partialDerivR4 μ f x = fderiv ℝ f x (Pi.single μ (1 : ℝ)) := by apply _root_.YangMills.Construction.Continuum.SeparatedFourTuples.SharpNormAndThickenings.partialDerivR4_eq_fderiv <;> assumption
theorem gradR4_orthogonalAct (Q : orthogonalGroupFour) {f : RealValued}
    (hf : IsC1c f) (x : AmbientSpace) :
    gradR4 (orthogonalAct Q f) x = Q.1 *ᵥ gradR4 f ((Q⁻¹ : orthogonalGroupFour).1 *ᵥ x) := by
  have hd : Differentiable ℝ f :=
    ContDiff.differentiable (show ContDiff ℝ 1 f from hf.1) (by norm_num)
  let L : AmbientSpace →L[ℝ] AmbientSpace :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin (Q⁻¹ : orthogonalGroupFour).1)
  have hL : ∀ y, L y = (Q⁻¹ : orthogonalGroupFour).1 *ᵥ y := fun _ => rfl
  have hc : orthogonalAct Q f = f ∘ L := rfl
  have hd' : Differentiable ℝ (orthogonalAct Q f) := by
    rw [hc]
    exact hd.comp L.differentiable
  have hder : fderiv ℝ (orthogonalAct Q f) x = (fderiv ℝ f (L x)).comp L := by
    rw [hc]
    exact ((hd (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  funext μ
  show TestFunctions.partialDerivR4 μ (orthogonalAct Q f) x = _
  rw [partialDerivR4_eq_fderiv hd', hder, ContinuousLinearMap.comp_apply, ← hL x]
  have hv : ∀ v : AmbientSpace, v = ∑ ν, v ν • (Pi.single ν (1 : ℝ) : AmbientSpace) := fun v => by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hcoef : ∀ ν, L (Pi.single μ (1 : ℝ)) ν = Q.1 μ ν := fun ν => by
    rw [hL, coe_inv_eq_transpose]
    simp
  rw [hv (L (Pi.single μ (1 : ℝ))), map_sum]
  simp only [map_smul, smul_eq_mul, hcoef]
  show _ = ∑ ν, Q.1 μ ν * TestFunctions.partialDerivR4 ν f (L x)
  exact Finset.sum_congr rfl fun ν _ => by rw [partialDerivR4_eq_fderiv hd]
theorem push_matMap_coe (Q : orthogonalGroupFour) (X : SepTuple) :
    (push (matMap Q) X).1 = X.1.map (orthogonalAct Q) :=
  push_coe (matHomeomorph Q) (contDiff_matMap Q⁻¹) X
theorem push_matMap_push_matMap (Q Q' : orthogonalGroupFour) (X : SepTuple) :
    push (matMap Q) (push (matMap Q') X) = push (matMap (Q * Q')) X := by
  apply Subtype.ext
  rw [push_matMap_coe, push_matMap_coe, push_matMap_coe, List.map_map]
  exact List.map_congr_left fun f _ => orthogonalAct_orthogonalAct Q Q' f
theorem push_matMap_one (X : SepTuple) : push (matMap 1) X = X := by
  apply Subtype.ext
  rw [push_matMap_coe]
  have : (orthogonalAct 1 : RealValued → RealValued) = id := funext orthogonalAct_one
  rw [this, List.map_id]
theorem sublistOn_map (g : RealValued → RealValued) (X : List RealValued) (I : Finset ℕ) :
    SepTuple.sublistOn (X.map g) I = (SepTuple.sublistOn X I).map g := by
  unfold SepTuple.sublistOn
  rw [List.zipIdx_map, List.filter_map, List.map_map, List.map_map]
  rfl
theorem actionLaws_holds (Q Q' : orthogonalGroupFour) : ActionLaws Q Q' := by
  refine ⟨fun f hf => ⟨?_, orthogonalAct_orthogonalAct Q Q' f, ?_,
      fun M _ => sharpNormR4_orthogonalAct M Q f, integral_orthogonalAct Q f,
      gradR4_orthogonalAct Q hf⟩, ?_, ?_, push_matMap_push_matMap Q Q', ?_, ?_⟩
  · exact isC1c_comp_symm (matHomeomorph Q) (contDiff_matMap Q⁻¹) hf
  · exact tsupport_comp_homeomorph_symm (matHomeomorph Q) f
  · refine Function.bijective_iff_has_inverse.2 ⟨push (matMap Q⁻¹), fun X => ?_, fun X => ?_⟩
    · rw [push_matMap_push_matMap, inv_mul_cancel, push_matMap_one]
    · rw [push_matMap_push_matMap, mul_inv_cancel, push_matMap_one]
  · intro X
    show (push (matMap Q) X).1.length = X.1.length
    rw [push_matMap_coe, List.length_map]
  · intro X I _
    apply Subtype.ext
    show SepTuple.sublistOn (push (matMap Q) X).1 I = (push (matMap Q) (X.subtuple I)).1
    rw [push_matMap_coe, push_matMap_coe, sublistOn_map]
    rfl
  · intro X Y h
    exact ⟨composable_push (matHomeomorph Q) (contDiff_matMap Q⁻¹) h,
      push_juxt (matHomeomorph Q) (contDiff_matMap Q⁻¹) h⟩
theorem timeComponent_spacetimePoint (u : Fin 3 → ℝ) (t : ℝ) :
    timeComponent (spacetimePoint u t) = t := spacetimePoint_last u t
theorem spacetimePoint_timeComponent (x : AmbientSpace) :
    spacetimePoint (spatialProjection x) (timeComponent x) = x :=
  spacetimePoint_spatialProjection x
theorem matMap_embedOrthogonal (R : orthogonalGroupThree) (u : Fin 3 → ℝ) (t : ℝ) :
    matMap (embedOrthogonal R) (spacetimePoint u t) = spacetimePoint (R.1 *ᵥ u) t := by apply _root_.YangMills.Construction.Orthogonal.embedOrthogonal_mulVec <;> assumption
theorem ext_castSucc_last {x y : AmbientSpace} (h₁ : ∀ i : Fin 3, x i.castSucc = y i.castSucc)
    (h₂ : x (Fin.last 3) = y (Fin.last 3)) : x = y := by
  funext μ
  exact Fin.lastCases h₂ h₁ μ
theorem timeReflection_spacetimePoint (u : Fin 3 → ℝ) (t : ℝ) :
    TimeAxis.timeReflection (spacetimePoint u t) = spacetimePoint u (-t) := by apply _root_.YangMills.Construction.Continuum.AxisPreservingSymmetries.timeReflection_mkPoint <;> assumption
theorem unitTime_eq_spacetimePoint : unitTime = spacetimePoint 0 1 := by apply _root_.YangMills.Construction.Continuum.AxisPreservingSymmetries.timeBasisVector_eq_mkPoint <;> assumption
theorem blockDiagOne_mul (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    blockDiagOne (A * B) = blockDiagOne A * blockDiagOne B := by
  unfold blockDiagOne
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp
theorem blockDiagOne_one : blockDiagOne 1 = 1 := by
  unfold blockDiagOne
  rw [Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
theorem blockDiagOne_transpose (A : Matrix (Fin 3) (Fin 3) ℝ) :
    blockDiagOne Aᵀ = (blockDiagOne A)ᵀ := by
  unfold blockDiagOne
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.transpose_submatrix,
    Matrix.fromBlocks_transpose]
  simp
theorem blockDiagOne_injective : Function.Injective blockDiagOne := fun A B h => by
  ext i j
  rw [← blockDiagOne_castSucc_castSucc A, h, blockDiagOne_castSucc_castSucc]
theorem embedOrthogonal_mul (R R' : orthogonalGroupThree) :
    embedOrthogonal (R * R') = embedOrthogonal R * embedOrthogonal R' :=
  Subtype.ext (blockDiagOne_mul R.1 R'.1)
theorem embedOrthogonal_one : embedOrthogonal 1 = 1 := Subtype.ext blockDiagOne_one
theorem embedOrthogonal_inv (R : orthogonalGroupThree) :
    (embedOrthogonal R)⁻¹ = embedOrthogonal R⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, ← embedOrthogonal_mul, mul_inv_cancel, embedOrthogonal_one]
theorem timeComponent_matMap_embed (R : orthogonalGroupThree) (x : AmbientSpace) :
    timeComponent (matMap (embedOrthogonal R) x) = timeComponent x := by
  rw [← spacetimePoint_timeComponent x, matMap_embedOrthogonal, timeComponent_spacetimePoint,
    timeComponent_spacetimePoint]
theorem matMap_embed_timeReflection (R : orthogonalGroupThree) (x : AmbientSpace) :
    matMap (embedOrthogonal R) (TimeAxis.timeReflection x) =
      TimeAxis.timeReflection (matMap (embedOrthogonal R) x) := by
  rw [← spacetimePoint_timeComponent x, matMap_embedOrthogonal, timeReflection_spacetimePoint,
    timeReflection_spacetimePoint, matMap_embedOrthogonal]
theorem matMap_embed_unitTime (R : orthogonalGroupThree) :
    matMap (embedOrthogonal R) unitTime = unitTime := by
  rw [unitTime_eq_spacetimePoint, matMap_embedOrthogonal, Matrix.mulVec_zero]
theorem image_matMap_embed_timeSet (R : orthogonalGroupThree) (p : ℝ → Prop) :
    matMap (embedOrthogonal R) '' {x | p (timeComponent x)} = {x | p (timeComponent x)} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show p (timeComponent (matMap (embedOrthogonal R) x))
    rw [timeComponent_matMap_embed]
    exact hx
  · intro hy
    refine ⟨matMap (embedOrthogonal R)⁻¹ y, ?_, matMap_matMap_inv _ y⟩
    show p (timeComponent (matMap (embedOrthogonal R)⁻¹ y))
    rw [embedOrthogonal_inv, timeComponent_matMap_embed]
    exact hy
theorem norm_sq_spacetimePoint (u : Fin 3 → ℝ) (t : ℝ) :
    ‖WithLp.toLp 2 (spacetimePoint u t)‖ ^ 2 = ‖WithLp.toLp 2 u‖ ^ 2 + t ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  have h : spacetimePoint u t 3 = t := spacetimePoint_last u t
  simp [spacetimePoint_castSucc, h]
theorem norm_spacetimePoint_zero (u : Fin 3 → ℝ) :
    ‖WithLp.toLp 2 (spacetimePoint u 0)‖ = ‖WithLp.toLp 2 u‖ := by
  have h := norm_sq_spacetimePoint u 0
  have h' : ‖WithLp.toLp 2 (spacetimePoint u 0)‖ ^ 2 = ‖WithLp.toLp 2 u‖ ^ 2 := by simpa using h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h'
theorem norm_le_norm_spacetimePoint (u : Fin 3 → ℝ) (t : ℝ) :
    ‖WithLp.toLp 2 u‖ ≤ ‖WithLp.toLp 2 (spacetimePoint u t)‖ := by
  have h := norm_sq_spacetimePoint u t
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by nlinarith [sq_nonneg t])
theorem embed_sub_one_mulVec (R : orthogonalGroupThree) (u : Fin 3 → ℝ) (t : ℝ) :
    ((embedOrthogonal R).1 - 1) *ᵥ spacetimePoint u t = spacetimePoint ((R.1 - 1) *ᵥ u) 0 := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, embedOrthogonal_mulVec, Matrix.one_mulVec,
    Matrix.one_mulVec]
  refine ext_castSucc_last (fun i => ?_) ?_
  · simp [spacetimePoint_castSucc]
  · show spacetimePoint (R.1 *ᵥ u) t (Fin.last 3) - spacetimePoint u t (Fin.last 3) =
      spacetimePoint (R.1 *ᵥ u - u) 0 (Fin.last 3)
    rw [spacetimePoint_last, spacetimePoint_last, spacetimePoint_last, sub_self]
theorem matrixOperatorNorm_embed_sub_one (R : orthogonalGroupThree) :
    matrixOperatorNorm ((embedOrthogonal R).1 - 1) = matrixOperatorNorm (R.1 - 1) := by
  unfold matrixOperatorNorm
  set D := Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) ((embedOrthogonal R).1 - 1) with hD
  set A := Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (R.1 - 1) with hA
  have hDA : ∀ (u : Fin 3 → ℝ) (t : ℝ),
      D (WithLp.toLp 2 (spacetimePoint u t)) =
        WithLp.toLp 2 (spacetimePoint ((R.1 - 1) *ᵥ u) 0) := fun u t => by
    rw [hD, Matrix.toEuclideanCLM_toLp, embed_sub_one_mulVec]
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    obtain ⟨y, rfl⟩ : ∃ y : AmbientSpace, WithLp.toLp 2 y = x := ⟨x.ofLp, rfl⟩
    rw [← spacetimePoint_spatialProjection y, hDA, norm_spacetimePoint_zero]
    calc ‖WithLp.toLp 2 ((R.1 - 1) *ᵥ spatialProjection y)‖
        = ‖A (WithLp.toLp 2 (spatialProjection y))‖ := by rw [hA, Matrix.toEuclideanCLM_toLp]
      _ ≤ ‖A‖ * ‖WithLp.toLp 2 (spatialProjection y)‖ := A.le_opNorm _
      _ ≤ ‖A‖ * ‖WithLp.toLp 2 (spacetimePoint (spatialProjection y) (y (Fin.last 3)))‖ :=
        mul_le_mul_of_nonneg_left (norm_le_norm_spacetimePoint _ _) (norm_nonneg _)
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    obtain ⟨u, rfl⟩ : ∃ u : Fin 3 → ℝ, WithLp.toLp 2 u = x := ⟨x.ofLp, rfl⟩
    calc ‖A (WithLp.toLp 2 u)‖ = ‖WithLp.toLp 2 ((R.1 - 1) *ᵥ u)‖ := by
          rw [hA, Matrix.toEuclideanCLM_toLp]
      _ = ‖D (WithLp.toLp 2 (spacetimePoint u 0))‖ := by rw [hDA, norm_spacetimePoint_zero]
      _ ≤ ‖D‖ * ‖WithLp.toLp 2 (spacetimePoint u 0)‖ := D.le_opNorm _
      _ = ‖D‖ * ‖WithLp.toLp 2 u‖ := by rw [norm_spacetimePoint_zero]
theorem embeddingLaws_holds (R R' : orthogonalGroupThree) : EmbeddingLaws R R' :=
  ⟨timeComponent_matMap_embed R, matMap_embed_timeReflection R, matMap_embed_unitTime R,
    fun v => matMap_embedOrthogonal R v 0, embedOrthogonal_mul R R', embedOrthogonal_one,
    matrixOperatorNorm_embed_sub_one R,
    image_matMap_embed_timeSet R fun t => t > 0, image_matMap_embed_timeSet R fun t => t < 0⟩
theorem push_timeReflection_mem {X : SepTuple} (hX : X ∈ supportedIn upperHalfSpace) :
    push TimeAxis.timeReflection X ∈ supportedIn {x | timeComponent x < 0} := by
  refine push_mem_supportedIn timeReflectionHomeomorph contDiff_timeReflection ?_ hX
  rintro _ ⟨x, hx, rfl⟩
  have hx' : timeComponent x > 0 := hx
  have h : timeComponent (TimeAxis.timeReflection x) = -timeComponent x := rfl
  show timeComponent (TimeAxis.timeReflection x) < 0
  linarith
theorem composable_timeReflection {X Y : SepTuple} (hX : X ∈ supportedIn upperHalfSpace)
    (hY : Y ∈ supportedIn upperHalfSpace) :
    SepTuple.Composable (push TimeAxis.timeReflection X) Y := by
  refine composable_of_mem_supportedIn ?_ (push_timeReflection_mem hX) hY
  refine Set.disjoint_left.2 fun x h₁ h₂ => ?_
  have h₁' : timeComponent x < 0 := h₁
  have h₂' : timeComponent x > 0 := h₂
  linarith
theorem push_translate_mem {a : AmbientSpace} (ha : 0 ≤ timeComponent a) {X : SepTuple}
    (hX : X ∈ supportedIn upperHalfSpace) : push (translate a) X ∈ supportedIn upperHalfSpace := by
  refine push_mem_supportedIn (translateHomeomorph a) (contDiff_translateHomeomorph_symm a) ?_ hX
  rintro _ ⟨x, hx, rfl⟩
  have hx' : timeComponent x > 0 := hx
  have h : timeComponent (translate a x) = timeComponent x + timeComponent a := rfl
  show timeComponent (translate a x) > 0
  linarith
theorem timeComponent_smul_unitTime (t : ℝ) : timeComponent (t • unitTime) = t := by apply _root_.YangMills.Construction.ReflectionPositivity.LimitContraction.timeComponent_smul_basisVector <;> assumption
theorem pushSpan_basisVec (r : AmbientSpace → AmbientSpace) (X : SepTuple) :
    pushSpan r (basisVec X) = basisVec (push r X) :=
  linearExtend_basisVec _ X
theorem formalSpan_linearMap_ext {φ ψ : FormalSpan →ₗ[ℂ] FormalSpan}
    (h : ∀ X, φ (basisVec X) = ψ (basisVec X)) : φ = ψ := by apply _root_.YangMills.Construction.SeparatedTuples.BasicFacts.formalSpan_linearMap_ext <;> assumption
theorem pushSpan_mem_spanIn {r : AmbientSpace → AmbientSpace} {O O' : Set AmbientSpace}
    (h : ∀ X ∈ supportedIn O, push r X ∈ supportedIn O') {F : FormalSpan}
    (hF : F ∈ spanIn O) : pushSpan r F ∈ spanIn O' := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨X, rfl⟩ := hx
    show pushSpan r (basisVec X.1) ∈ _
    rw [pushSpan_basisVec]
    exact Submodule.subset_span ⟨⟨_, h _ X.2⟩, rfl⟩
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | add _ _ _ _ h₁ h₂ =>
    rw [map_add]
    exact add_mem h₁ h₂
  | smul c _ _ h₁ =>
    rw [map_smul]
    exact Submodule.smul_mem _ c h₁
theorem push_embed_mem (R : orthogonalGroupThree) {X : SepTuple}
    (hX : X ∈ supportedIn upperHalfSpace) :
    push (matMap (embedOrthogonal R)) X ∈ supportedIn upperHalfSpace :=
  push_mem_supportedIn (matHomeomorph (embedOrthogonal R)) (contDiff_matMap _)
    (image_matMap_embed_timeSet R fun t => t > 0).subset hX
theorem pushSpan_embed_inv_pushSpan_embed (R : orthogonalGroupThree) (F : FormalSpan) :
    pushSpan (matMap (embedOrthogonal R⁻¹)) (pushSpan (matMap (embedOrthogonal R)) F) = F := by
  have h : (pushSpan (matMap (embedOrthogonal R⁻¹))).comp
      (pushSpan (matMap (embedOrthogonal R))) = LinearMap.id :=
    formalSpan_linearMap_ext fun X => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply, pushSpan_basisVec]
      rw [push_matMap_push_matMap, ← embedOrthogonal_mul, inv_mul_cancel, embedOrthogonal_one,
        push_matMap_one]
  exact LinearMap.congr_fun h F
theorem push_timeReflection_push_embed (R : orthogonalGroupThree) (X : SepTuple) :
    push TimeAxis.timeReflection (push (matMap (embedOrthogonal R)) X) =
      push (matMap (embedOrthogonal R)) (push TimeAxis.timeReflection X) := by
  refine push_push_comm timeReflectionHomeomorph (matHomeomorph (embedOrthogonal R))
    (matHomeomorph (embedOrthogonal R)) contDiff_timeReflection
    (contDiff_matMap _) (contDiff_matMap _) (fun x => ?_) X
  show matMap (embedOrthogonal R)⁻¹ (TimeAxis.timeReflection x) =
    TimeAxis.timeReflection (matMap (embedOrthogonal R)⁻¹ x)
  rw [embedOrthogonal_inv, matMap_embed_timeReflection]
theorem push_embed_push_translate (R : orthogonalGroupThree) (a : AmbientSpace) (X : SepTuple) :
    push (matMap (embedOrthogonal R)) (push (translate a) X) =
      push (translate (matMap (embedOrthogonal R) a)) (push (matMap (embedOrthogonal R)) X) := by
  refine push_push_comm (matHomeomorph (embedOrthogonal R)) (translateHomeomorph a)
    (translateHomeomorph (matMap (embedOrthogonal R) a))
    (contDiff_matMap _) (contDiff_translateHomeomorph_symm a)
    (contDiff_translateHomeomorph_symm _) (fun x => ?_) X
  show matMap (embedOrthogonal R)⁻¹ x - a =
    matMap (embedOrthogonal R)⁻¹ (x - matMap (embedOrthogonal R) a)
  rw [matMap_sub, matMap_inv_matMap]
theorem pushSpan_embed_pushSpan_translate (R : orthogonalGroupThree) (a : AmbientSpace)
    (F : FormalSpan) :
    pushSpan (matMap (embedOrthogonal R)) (pushSpan (translate a) F) =
      pushSpan (translate (matMap (embedOrthogonal R) a))
        (pushSpan (matMap (embedOrthogonal R)) F) := by
  have h : (pushSpan (matMap (embedOrthogonal R))).comp (pushSpan (translate a)) =
      (pushSpan (translate (matMap (embedOrthogonal R) a))).comp
        (pushSpan (matMap (embedOrthogonal R))) := formalSpan_linearMap_ext fun X => by
    simp only [LinearMap.comp_apply, pushSpan_basisVec]
    rw [push_embed_push_translate]
  exact LinearMap.congr_fun h F
theorem juxt_push_embed (R : orthogonalGroupThree) {X Y : SepTuple}
    (hX : X ∈ supportedIn upperHalfSpace) (hY : Y ∈ supportedIn upperHalfSpace) :
    SepTuple.juxt (push TimeAxis.timeReflection (push (matMap (embedOrthogonal R)) X))
        (push (matMap (embedOrthogonal R)) Y) =
      push (matMap (embedOrthogonal R)) (SepTuple.juxt (push TimeAxis.timeReflection X) Y) := by
  rw [push_timeReflection_push_embed]
  exact (push_juxt (matHomeomorph (embedOrthogonal R)) (contDiff_matMap _)
    (composable_timeReflection hX hY)).symm
theorem formalMul_pushSpan_embed_basisVec (R : orthogonalGroupThree) {X : SepTuple}
    (hX : X ∈ supportedIn upperHalfSpace) {F' : FormalSpan} (hF' : F' ∈ spanIn upperHalfSpace) :
    formalMul
        (pushSpan TimeAxis.timeReflection
          (conjugation (pushSpan (matMap (embedOrthogonal R)) (basisVec X))))
        (pushSpan (matMap (embedOrthogonal R)) F') =
      pushSpan (matMap (embedOrthogonal R))
        (formalMul (pushSpan TimeAxis.timeReflection (conjugation (basisVec X))) F') := by
  induction hF' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Y, rfl⟩ := hx
    show formalMul _ (pushSpan _ (basisVec Y.1)) = pushSpan _ (formalMul _ (basisVec Y.1))
    simp only [pushSpan_basisVec, conjugation_basisVec, formalMul_basisVec]
    rw [juxt_push_embed R hX Y.2]
  | zero => simp only [map_zero]
  | add _ _ _ _ h₁ h₂ => simp only [map_add, h₁, h₂]
  | smul c _ _ h₁ => simp only [map_smul, h₁]
theorem formalMul_pushSpan_embed (R : orthogonalGroupThree) {F F' : FormalSpan}
    (hF : F ∈ spanIn upperHalfSpace) (hF' : F' ∈ spanIn upperHalfSpace) :
    formalMul
        (pushSpan TimeAxis.timeReflection (conjugation (pushSpan (matMap (embedOrthogonal R)) F)))
        (pushSpan (matMap (embedOrthogonal R)) F') =
      pushSpan (matMap (embedOrthogonal R))
        (formalMul (pushSpan TimeAxis.timeReflection (conjugation F)) F') := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨X, rfl⟩ := hx
    exact formalMul_pushSpan_embed_basisVec R X.2 hF'
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add _ _ _ _ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | smul c _ _ h₁ => simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, h₁]
theorem upperHalfSpaceLaws_holds (R : orthogonalGroupThree) : UpperHalfSpaceLaws R := by
  have hmaps : ∀ R' : orthogonalGroupThree, Set.MapsTo (pushSpan (matMap (embedOrthogonal R')))
      (spanIn upperHalfSpace : Set FormalSpan) (spanIn upperHalfSpace : Set FormalSpan) :=
    fun R' _ hF => pushSpan_mem_spanIn (fun _ hX => push_embed_mem R' hX) hF
  have hinv : Set.InvOn (pushSpan (matMap (embedOrthogonal R⁻¹)))
      (pushSpan (matMap (embedOrthogonal R)))
      (spanIn upperHalfSpace : Set FormalSpan) (spanIn upperHalfSpace : Set FormalSpan) := by
    refine ⟨fun F _ => pushSpan_embed_inv_pushSpan_embed R F, fun F _ => ?_⟩
    have h := pushSpan_embed_inv_pushSpan_embed R⁻¹ F
    rwa [inv_inv] at h
  refine ⟨fun X hX Y hY => composable_timeReflection hX hY,
    fun X hX => ⟨fun t ht => ?_, fun v => ?_⟩,
    hinv.bijOn (hmaps R) (hmaps R⁻¹), hinv, ?_, fun F hF F' hF' =>
      ⟨formalMul_pushSpan_embed R hF hF', fun t _ => ?_, fun v => ?_⟩⟩
  · refine push_translate_mem ?_ hX
    rw [timeComponent_smul_unitTime]
    exact ht
  · refine push_translate_mem ?_ hX
    rw [timeComponent_spacetimePoint]
  · rw [pushSpan_basisVec, push_nil]
  · rw [pushSpan_embed_pushSpan_translate, matMap_smul, matMap_embed_unitTime]
  · rw [pushSpan_embed_pushSpan_translate, matMap_embedOrthogonal]
def signedPermMatrix (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => if π i = j then ((s i : ℤ) : ℝ) else 0
theorem signedPermMatrix_mulVec (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) (x : AmbientSpace) :
    signedPermMatrix π s *ᵥ x = signedCoordinateEquiv π s x := by
  funext i
  show ∑ j, (if π i = j then ((s i : ℤ) : ℝ) else 0) * x j = ((s i : ℤ) : ℝ) * x (π i)
  simp [ite_mul]
theorem unitSign_mul_self (ε : ℤˣ) : ((ε : ℤ) : ℝ) * ((ε : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or ε with h | h <;> simp [h]
theorem unitSign_ne_zero (ε : ℤˣ) : ((ε : ℤ) : ℝ) ≠ 0 := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReflections.unitCast_ne_zero <;> assumption
theorem signedPermMatrix_mul_transpose (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) :
    signedPermMatrix π s * (signedPermMatrix π s)ᵀ = 1 := by
  ext i j
  show ∑ k, (if π i = k then ((s i : ℤ) : ℝ) else 0) * (if π j = k then ((s j : ℤ) : ℝ) else 0) =
    (1 : Matrix (Fin 4) (Fin 4) ℝ) i j
  by_cases h : i = j
  · subst h
    simp [ite_mul, unitSign_mul_self]
  · simp [ite_mul, h]
theorem unitTime_last : unitTime (Fin.last 3) = 1 := by
  rw [unitTime_eq_spacetimePoint, spacetimePoint_last]
theorem unitTime_castSucc (i : Fin 3) : unitTime i.castSucc = 0 := by
  rw [unitTime_eq_spacetimePoint, spacetimePoint_castSucc]
  rfl
theorem unitTime_of_ne_last {μ : Fin 4} (h : μ ≠ Fin.last 3) : unitTime μ = 0 := by
  obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 h
  exact unitTime_castSucc i
theorem perm_last_of_fixes_unitTime {π : Equiv.Perm (Fin 4)} {s : Fin 4 → ℤˣ}
    (h : signedCoordinateEquiv π s unitTime = unitTime) :
    π (Fin.last 3) = Fin.last 3 ∧ ((s (Fin.last 3) : ℤ) : ℝ) = 1 := by
  have hval : ∀ μ, ((s μ : ℤ) : ℝ) * unitTime (π μ) = unitTime μ := fun μ => congrFun h μ
  have h₁ : π.symm (Fin.last 3) = Fin.last 3 := by
    by_contra hne
    have hv := hval (π.symm (Fin.last 3))
    rw [Equiv.apply_symm_apply, unitTime_last, mul_one, unitTime_of_ne_last hne] at hv
    exact unitSign_ne_zero _ hv
  have h₂ : π (Fin.last 3) = Fin.last 3 := by
    conv_lhs => rw [← h₁]
    exact Equiv.apply_symm_apply π _
  refine ⟨h₂, ?_⟩
  have hv := hval (Fin.last 3)
  rwa [h₂, unitTime_last, mul_one] at hv
theorem exists_embedding_of_mem_timeStabilizer {w : Equiv.Perm AmbientSpace}
    (hw : w ∈ timeStabilizer) :
    ∃ R : orthogonalGroupThree, IsEmbeddingOf w R ∧ (∀ i, ∃! j, R.1 i j ≠ 0) ∧
      (∀ j, ∃! i, R.1 i j ≠ 0) ∧ ∀ i j, R.1 i j ≠ 0 → R.1 i j = 1 ∨ R.1 i j = -1 := by
  obtain ⟨⟨π, s, rfl⟩, hfix⟩ := hw
  obtain ⟨hπ, hs⟩ := perm_last_of_fixes_unitTime hfix
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    (signedPermMatrix π s).submatrix Fin.castSucc Fin.castSucc
  have hent : ∀ i j, A i j = if π i.castSucc = j.castSucc then ((s i.castSucc : ℤ) : ℝ) else 0 :=
    fun _ _ => rfl
  have hne : ∀ i : Fin 3, π i.castSucc ≠ Fin.last 3 := fun i h =>
    (Fin.castSucc_lt_last i).ne (π.injective (h.trans hπ.symm))
  have hne' : ∀ j : Fin 3, π.symm j.castSucc ≠ Fin.last 3 := fun j h => by
    have h' : j.castSucc = π (Fin.last 3) := by rw [← h, Equiv.apply_symm_apply]
    exact (Fin.castSucc_lt_last j).ne (h'.trans hπ)
  have hAB : blockDiagOne A = signedPermMatrix π s := by
    ext i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [blockDiagOne_last_last]
      show (1 : ℝ) = if π (Fin.last 3) = Fin.last 3 then ((s (Fin.last 3) : ℤ) : ℝ) else 0
      rw [if_pos hπ, hs]
    · rw [blockDiagOne_last_castSucc]
      show (0 : ℝ) = if π (Fin.last 3) = j.castSucc then ((s (Fin.last 3) : ℤ) : ℝ) else 0
      rw [if_neg]
      rw [hπ]
      exact (Fin.castSucc_lt_last j).ne'
    · rw [blockDiagOne_castSucc_last]
      show (0 : ℝ) = if π i.castSucc = Fin.last 3 then ((s i.castSucc : ℤ) : ℝ) else 0
      rw [if_neg (hne i)]
    · rw [blockDiagOne_castSucc_castSucc]
      rfl
  have hA : A ∈ orthogonalGroupThree := by
    rw [Matrix.mem_orthogonalGroup_iff]
    apply blockDiagOne_injective
    rw [blockDiagOne_mul, blockDiagOne_transpose, hAB, blockDiagOne_one]
    exact signedPermMatrix_mul_transpose π s
  have hnz : ∀ i j, A i j ≠ 0 → π i.castSucc = j.castSucc := fun i j h => by
    by_contra hc
    exact h (by rw [hent, if_neg hc])
  refine ⟨⟨A, hA⟩, ?_, fun i => ?_, fun j => ?_, fun i j h => ?_⟩
  · funext x
    show signedCoordinateEquiv π s x = blockDiagOne A *ᵥ x
    rw [hAB, signedPermMatrix_mulVec]
  · obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.2 (hne i)
    refine ⟨j, ?_, fun j' hj' => ?_⟩
    · show A i j ≠ 0
      rw [hent, if_pos hj.symm]
      exact unitSign_ne_zero _
    · exact Fin.castSucc_injective _ ((hnz i j' hj').symm.trans hj.symm)
  · obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 (hne' j)
    have hi' : π i.castSucc = j.castSucc := by rw [hi, Equiv.apply_symm_apply]
    refine ⟨i, ?_, fun i' hi'' => ?_⟩
    · show A i j ≠ 0
      rw [hent, if_pos hi']
      exact unitSign_ne_zero _
    · exact Fin.castSucc_injective _ (π.injective ((hnz i' j hi'').trans hi'.symm))
  · show A i j = 1 ∨ A i j = -1
    rw [hent, if_pos (hnz i j h)]
    rcases Int.units_eq_one_or (s i.castSucc) with e | e <;> simp [e]
theorem isEmbeddingOf_unique {w : Equiv.Perm AmbientSpace} {R R' : orthogonalGroupThree}
    (h : IsEmbeddingOf w R) (h' : IsEmbeddingOf w R') : R = R' := by
  have hm : ∀ u : Fin 3 → ℝ, R.1 *ᵥ u = R'.1 *ᵥ u := fun u => by
    have e : matMap (embedOrthogonal R) = matMap (embedOrthogonal R') := Eq.trans (Eq.symm h) h'
    have e' := congrFun e (spacetimePoint u 0)
    rw [matMap_embedOrthogonal, matMap_embedOrthogonal] at e'
    funext i
    have e'' := congrFun e' i.castSucc
    rwa [spacetimePoint_castSucc, spacetimePoint_castSucc] at e''
  exact Subtype.ext (Matrix.toLin'.injective (LinearMap.ext fun v => by simpa using hm v))
theorem spatialPart_eq {w : Equiv.Perm AmbientSpace} {R : orthogonalGroupThree}
    (h : IsEmbeddingOf w R) : spatialPart w = R :=
  isEmbeddingOf_unique (Classical.epsilon_spec ⟨R, h⟩) h
theorem stabilizerLaws_holds : StabilizerLaws := by
  refine ⟨fun w hw => ?_, fun w hw w' hw' => ?_, fun w hw w' hw' h => ?_⟩
  · obtain ⟨R, hR, h₁, h₂, h₃⟩ := exists_embedding_of_mem_timeStabilizer hw
    rw [spatialPart_eq hR]
    exact ⟨hR, fun R' hR' => isEmbeddingOf_unique hR' hR, h₁, h₂, h₃⟩
  · obtain ⟨R, hR, -⟩ := exists_embedding_of_mem_timeStabilizer hw
    obtain ⟨R', hR', -⟩ := exists_embedding_of_mem_timeStabilizer hw'
    rw [spatialPart_eq hR, spatialPart_eq hR']
    refine spatialPart_eq ?_
    funext x
    have e₁ : w (w' x) = matMap (embedOrthogonal R) (w' x) := congrFun hR _
    have e₂ : w' x = matMap (embedOrthogonal R') x := congrFun hR' _
    show w (w' x) = matMap (embedOrthogonal (R * R')) x
    rw [e₁, e₂, embedOrthogonal_mul, matMap_mul]
  · obtain ⟨R, hR, -⟩ := exists_embedding_of_mem_timeStabilizer hw
    obtain ⟨R', hR', -⟩ := exists_embedding_of_mem_timeStabilizer hw'
    rw [spatialPart_eq hR, spatialPart_eq hR'] at h
    subst h
    exact Equiv.coe_fn_injective (Eq.trans hR (Eq.symm hR'))
theorem statement_holds : Statement :=
  ⟨actionLaws_holds, embeddingLaws_holds, upperHalfSpaceLaws_holds, stabilizerLaws_holds⟩
end Laws
end OrthogonalAction
end YangMills.Construction
