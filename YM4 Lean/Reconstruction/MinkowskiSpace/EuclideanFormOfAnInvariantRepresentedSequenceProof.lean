import YangMills.Construction.Continuum.CompactSupportAndTensorsOfSeparatedTuples
import YangMills.Construction.Continuum.ChosenSmoothFunctionsPartitionsOfUnityRotationsAndIntegrability
import Reconstruction.Continuum.InvarianceOfSequenceOnTestFunctionSpaces
import Reconstruction.MinkowskiSpace.EuclideanFormOfAnInvariantRepresentedSequence
import Reconstruction.MinkowskiSpace.ProductsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.MinkowskiSpace.InvariantEuclideanProof
open TestSpaces Motions MinkowskiSpace FieldForms WightmanTheory HilbertToolkit
  ProjectionMeasures PVMCalculus OneLoopNotation
section RotatePermuteMap
variable {n : ℕ}
theorem orthogonal_inv_mul (R : Matrix.orthogonalGroup (Fin 4) ℝ) :
    (R : Matrix (Fin 4) (Fin 4) ℝ)⁻¹ * (R : Matrix (Fin 4) (Fin 4) ℝ) = 1 :=
  RigidMotion.inv_mul_mat ⟨R.1, R.2, 0⟩
theorem orthogonal_mul_inv (R : Matrix.orthogonalGroup (Fin 4) ℝ) :
    (R : Matrix (Fin 4) (Fin 4) ℝ) * (R : Matrix (Fin 4) (Fin 4) ℝ)⁻¹ = 1 :=
  RigidMotion.mat_mul_inv ⟨R.1, R.2, 0⟩
def unrotate (R : Matrix.orthogonalGroup (Fin 4) ℝ) (σ : Equiv.Perm (Fin n)) (y : PointTuple n) :
    PointTuple n :=
  fun j => (R : Matrix (Fin 4) (Fin 4) ℝ)⁻¹.mulVec (y (σ.symm j))
def rotatePermuteHomeomorph (R : Matrix.orthogonalGroup (Fin 4) ℝ) (σ : Equiv.Perm (Fin n)) :
    PointTuple n ≃ₜ PointTuple n where
  toFun := rotatePermute R σ
  invFun := unrotate R σ
  left_inv x := by
    funext j
    simp [unrotate, rotatePermute, Matrix.mulVec_mulVec, orthogonal_inv_mul]
  right_inv y := by
    funext i
    simp [unrotate, rotatePermute, Matrix.mulVec_mulVec, orthogonal_mul_inv]
  continuous_toFun := continuous_pi fun i =>
    Continuous.matrix_mulVec continuous_const (continuous_apply _)
  continuous_invFun := continuous_pi fun j =>
    Continuous.matrix_mulVec continuous_const (continuous_apply _)
theorem measurePreserving_orthogonal_mulVec (R : Matrix.orthogonalGroup (Fin 4) ℝ) :
    MeasurePreserving (fun u : Fin 4 → ℝ => (R : Matrix (Fin 4) (Fin 4) ℝ).mulVec u) volume volume := by
  have hdet : ((R : Matrix (Fin 4) (Fin 4) ℝ).det) * ((R : Matrix (Fin 4) (Fin 4) ℝ).det) = 1 := by
    have hTR : (R : Matrix (Fin 4) (Fin 4) ℝ).transpose * (R : Matrix (Fin 4) (Fin 4) ℝ) = 1 :=
      (Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).1 R.2
    have := congrArg Matrix.det hTR
    simpa [Matrix.det_mul, Matrix.det_transpose] using this
  have hne : (R : Matrix (Fin 4) (Fin 4) ℝ).det ≠ 0 := fun h => by simp [h] at hdet
  have habs : |((R : Matrix (Fin 4) (Fin 4) ℝ).det)⁻¹| = 1 := by
    rw [abs_inv]
    have : |(R : Matrix (Fin 4) (Fin 4) ℝ).det| = 1 := by
      have hsq : |(R : Matrix (Fin 4) (Fin 4) ℝ).det| * |(R : Matrix (Fin 4) (Fin 4) ℝ).det| = 1 := by
        rw [← abs_mul, hdet, abs_one]
      nlinarith [abs_nonneg (R : Matrix (Fin 4) (Fin 4) ℝ).det]
    simp [this]
  refine ⟨Continuous.measurable (Continuous.matrix_mulVec continuous_const continuous_id), ?_⟩
  have hvol := Real.map_matrix_volume_pi_eq_smul_volume_pi hne
  rw [habs] at hvol
  have hfun : (fun u : Fin 4 → ℝ => (R : Matrix (Fin 4) (Fin 4) ℝ).mulVec u) =
      ⇑(Matrix.toLin' (R : Matrix (Fin 4) (Fin 4) ℝ)) := by
    funext u
    simp
  rw [hfun, hvol]
  simp
theorem contDiff_rotatePermute (R : Matrix.orthogonalGroup (Fin 4) ℝ)
    (σ : Equiv.Perm (Fin n)) : ContDiff ℝ ∞ (rotatePermute R σ : PointTuple n → PointTuple n) :=
  contDiff_pi.2 fun i =>
    (LinearMap.toContinuousLinearMap (Matrix.toLin' (R : Matrix (Fin 4) (Fin 4) ℝ))).contDiff.comp
      (contDiff_apply ℝ (Fin 4 → ℝ) (σ i))
theorem contDiff_unrotate (R : Matrix.orthogonalGroup (Fin 4) ℝ) (σ : Equiv.Perm (Fin n)) :
    ContDiff ℝ ∞ (unrotate R σ : PointTuple n → PointTuple n) :=
  contDiff_pi.2 fun j =>
    (LinearMap.toContinuousLinearMap
      (Matrix.toLin' (R : Matrix (Fin 4) (Fin 4) ℝ)⁻¹)).contDiff.comp
      (contDiff_apply ℝ (Fin 4 → ℝ) (σ.symm j))
theorem measurePreserving_rotatePermute (R : Matrix.orthogonalGroup (Fin 4) ℝ)
    (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (rotatePermute R σ : PointTuple n → PointTuple n) volume volume := by
  have hperm : MeasurePreserving (fun x : PointTuple n => fun i => x (σ i)) volume volume := by
    have hpc := volume_measurePreserving_piCongrLeft (fun _ : Fin n => Fin 4 → ℝ) σ.symm
    convert hpc using 1
    funext x i
    have := Equiv.piCongrLeft_apply_apply (fun _ : Fin n => Fin 4 → ℝ) σ.symm x (σ i)
    rw [MeasurableEquiv.coe_piCongrLeft]
    simpa using this.symm
  have hrot : MeasurePreserving
      (fun x : PointTuple n => fun i => (R : Matrix (Fin 4) (Fin 4) ℝ).mulVec (x i)) volume volume :=
    volume_preserving_pi fun _ => measurePreserving_orthogonal_mulVec R
  exact hrot.comp hperm
end RotatePermuteMap
section OrderedContinuity
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
theorem continuous_wickMap_toComplex : Continuous fun u : Fin 4 → ℝ =>
    wickMap (toComplex u) :=
  (wickMap.toLinearMap.continuous_of_finiteDimensional).comp
    (continuous_pi fun μ => Complex.continuous_ofReal.comp (continuous_apply μ))
theorem continuous_wickDiffs {n : ℕ} :
    Continuous (FieldForms.wickDiffs (n := n)) := by
  refine continuous_pi fun i => ?_
  change Continuous fun x : PointTuple (n + 1) =>
    wickMap (toComplex (x i.succ)) - wickMap (toComplex (x i.castSucc))
  exact (continuous_wickMap_toComplex.comp (continuous_apply _)).sub
    (continuous_wickMap_toComplex.comp (continuous_apply _))
theorem imagTimeShift_one_mem_futureTube : imagTimeShift 1 ∈ futureTube := by
  have him : MinkowskiSpace.imPart (imagTimeShift 1) = mkTimeSpace 1 0 := by
    funext μ
    fin_cases μ <;>
      simp [MinkowskiSpace.imPart, imagTimeShift, toComplex, timeUnit, mkTimeSpace, Fin.cons]
  change coneGap (MinkowskiSpace.imPart (imagTimeShift 1)) > 0
  rw [him]
  simp [coneGap, spacePart, mkTimeSpace, spaceNorm]
theorem continuousOn_orderedSchwinger {E : FourBorelSet → BddOp K} {Ω : K}
    {A : ℝ → BddOp K} (hd : FieldProductHolomorphic E A) (m : ℕ) :
    ContinuousOn (orderedSchwinger E Ω A m) (increasingTimes (m + 1)) := by
  have hmap : Continuous fun x : PointTuple (m + 1) =>
      consPoint (imagTimeShift 1)
        (snocPoint (FieldForms.wickDiffs x) (imagTimeShift 1)) := by
    refine continuous_pi fun k => ?_
    refine Fin.cases ?_ (fun k' => ?_) k
    · simpa [consPoint] using continuous_const
    · refine Fin.lastCases ?_ (fun i => ?_) k'
      · simpa [consPoint, snocPoint] using continuous_const
      · have hi : Continuous fun x : PointTuple (m + 1) => FieldForms.wickDiffs x i :=
          (continuous_apply i).comp continuous_wickDiffs
        simpa [consPoint, snocPoint] using hi
  have hin : Set.MapsTo (fun x : PointTuple (m + 1) => consPoint (imagTimeShift 1)
      (snocPoint (FieldForms.wickDiffs x) (imagTimeShift 1))) (increasingTimes (m + 1))
      (tubeTuples (m + 1 + 1)) := by
    intro x hx k _
    refine Fin.cases ?_ (fun k' => ?_) k
    · simpa [consPoint] using imagTimeShift_one_mem_futureTube
    · refine Fin.lastCases ?_ (fun i => ?_) k'
      · simpa [consPoint, snocPoint] using imagTimeShift_one_mem_futureTube
      · simpa [consPoint, snocPoint] using wickDiffs_mem_futureTube hx i
  have hcomp := (hd (m + 1)).1.comp hmap.continuousOn hin
  have hev : Continuous fun T : BddOp K => inner ℂ Ω (T Ω) :=
    continuous_const.inner (continuous_eval_const Ω)
  exact hev.comp_continuousOn hcomp
end OrderedContinuity
section TestFunctions
variable {n : ℕ}
theorem mem_schwartzFlatOffDiagonal_of_smooth (hC : ConfigSpace.CompactSupportTensorFacts)
    (hn : 1 ≤ n) {f : PointTuple n → ℂ}
    (hf : f ∈ (TestSpaces.smoothCompactSupp (distinctLocus n) : Set (PointTuple n → ℂ))) :
    f ∈ ConfigSpace.schwartzFlatOffDiagonal n :=
  (hC n hn).2.1 ⟨ConfigSpace.isOpen_distinctArgs, hf.1, hf.2.1, hf.2.2⟩
theorem comp_homeomorph_mem_smoothCompactSupp {f : PointTuple n → ℂ} {W W' : Set (PointTuple n)}
    (g : PointTuple n ≃ₜ PointTuple n) (hg : ContDiff ℝ ∞ g)
    (hf : f ∈ (TestSpaces.smoothCompactSupp W : Set (PointTuple n → ℂ)))
    (hW : g ⁻¹' W ⊆ W') :
    f ∘ g ∈ (TestSpaces.smoothCompactSupp W' : Set (PointTuple n → ℂ)) := by
  refine ⟨hf.1.comp hg, hf.2.1.comp_homeomorph g, ?_⟩
  rw [tsupport_comp_eq_preimage]
  exact (Set.preimage_mono hf.2.2).trans hW
theorem ofReal_mem_smoothCompactSupp {h : PointTuple n → ℝ} {U : Set (PointTuple n)}
    (hh : h ∈ (TestSpaces.smoothCompactSupp U : Set (PointTuple n → ℝ))) :
    (fun z => (h z : ℂ)) ∈ (TestSpaces.smoothCompactSupp U : Set (PointTuple n → ℂ)) := by
  have hsub : tsupport (fun z => (h z : ℂ)) ⊆ tsupport h := closure_mono fun z hz h0 =>
    hz (by simpa using (show h z = 0 from h0))
  exact ⟨Complex.ofRealCLM.contDiff.comp hh.1,
    IsCompact.of_isClosed_subset hh.2.1 (isClosed_tsupport _) hsub, hsub.trans hh.2.2⟩
theorem integrable_ofReal_mul {U : Set (PointTuple n)} (hU : IsOpen U) {h : PointTuple n → ℝ}
    (hh : h ∈ (TestSpaces.smoothCompactSupp U : Set (PointTuple n → ℝ))) {v : PointTuple n → ℂ}
    (hv : ContinuousOn v U) : Integrable fun z => (h z : ℂ) * v z := by
  have hsub : tsupport (fun z => (h z : ℂ) * v z) ⊆ tsupport h := closure_mono fun z hz h0 =>
    hz (by simp [show h z = 0 from h0])
  have hc : Continuous fun z => (h z : ℂ) * v z := continuous_of_tsupport fun x hx =>
    ((Complex.continuous_ofReal.comp hh.1.continuous).continuousAt).mul
      (hv.continuousAt (hU.mem_nhds (hh.2.2 (hsub hx))))
  exact hc.integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset hh.2.1 (isClosed_tsupport _) hsub)
theorem indicator_ofReal_mul_eq {V U : Set (PointTuple n)} (hUV : U ⊆ V) {h : PointTuple n → ℝ}
    (hh : h ∈ (TestSpaces.smoothCompactSupp U : Set (PointTuple n → ℝ))) (s : PointTuple n → ℂ) :
    (fun z => V.indicator (fun y => (h y : ℂ) * s y) z) = fun z => (h z : ℂ) * s z := by
  funext z
  by_cases hz : z ∈ V
  · simp [Set.indicator_of_mem hz]
  · have h0 : h z = 0 := image_eq_zero_of_notMem_tsupport fun hz' => hz (hUV (hh.2.2 hz'))
    simp [Set.indicator_of_notMem hz, h0]
theorem integral_indicator_comp_symm {V : Set (PointTuple n)} (R : Matrix.orthogonalGroup (Fin 4) ℝ)
    (σ : Equiv.Perm (Fin n)) {h : PointTuple n → ℝ}
    (hh : h ∈ (TestSpaces.smoothCompactSupp (V ∩ rotatePermuteHomeomorph R σ ⁻¹' V) :
      Set (PointTuple n → ℝ))) (s : PointTuple n → ℂ) :
    ∫ y, V.indicator (fun y => (h ((rotatePermuteHomeomorph R σ).symm y) : ℂ) * s y) y =
      ∫ z, (h z : ℂ) * s (rotatePermuteHomeomorph R σ z) := by
  have hm := (measurePreserving_rotatePermute (n := n) R σ).integral_comp
    (rotatePermuteHomeomorph R σ).measurableEmbedding
    (fun y => V.indicator (fun y => (h ((rotatePermuteHomeomorph R σ).symm y) : ℂ) * s y) y)
  refine hm.symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
  change V.indicator (fun y => (h ((rotatePermuteHomeomorph R σ).symm y) : ℂ) * s y)
    (rotatePermuteHomeomorph R σ z) = _
  by_cases hz : rotatePermuteHomeomorph R σ z ∈ V
  · simp [Set.indicator_of_mem hz]
  · have h0 : h z = 0 := image_eq_zero_of_notMem_tsupport fun hz' => hz (hh.2.2 hz').2
    simp [Set.indicator_of_notMem hz, h0]
end TestFunctions
theorem euclideanOfInvariantRepresented_proof (hI : ConfigSpace.MotionInvarianceStatement)
    (hC : ConfigSpace.CompactSupportTensorFacts)
    (hT : WightmanReconstruction.SmoothToolkit.Toolkit)
    (hP : FieldProductProperties) : EuclideanOfInvariantRepresented := by
  intro S hE hS K _ _ _ E Ω A ℘ C hB hR m x hx R σ hy
  have hn : 1 ≤ m + 1 := Nat.succ_pos m
  have hs : ContinuousOn (orderedSchwinger E Ω A m) (increasingTimes (m + 1)) :=
    continuousOn_orderedSchwinger (hP K E Ω A ℘ C hB).2.2.2.2.2.2.1 m
  have hU : IsOpen (increasingTimes (m + 1) ∩ rotatePermuteHomeomorph R σ ⁻¹' increasingTimes (m + 1)) :=
    (isOpen_increasingTimes _).inter
      ((isOpen_increasingTimes _).preimage (rotatePermuteHomeomorph R σ).continuous)
  have hs₁ : ContinuousOn (orderedSchwinger E Ω A m)
      (increasingTimes (m + 1) ∩ rotatePermuteHomeomorph R σ ⁻¹' increasingTimes (m + 1)) :=
    hs.mono Set.inter_subset_left
  have hs₂ : ContinuousOn (fun z => orderedSchwinger E Ω A m (rotatePermuteHomeomorph R σ z))
      (increasingTimes (m + 1) ∩ rotatePermuteHomeomorph R σ ⁻¹' increasingTimes (m + 1)) :=
    hs.comp (rotatePermuteHomeomorph R σ).continuous.continuousOn fun z hz => hz.2
  have key := hT.2.2.2.2.1 (m + 1) hn _
    (fun z => orderedSchwinger E Ω A m (rotatePermuteHomeomorph R σ z) -
      orderedSchwinger E Ω A m z) hU (hs₂.sub hs₁) (fun h hh => by
    have hφU := ofReal_mem_smoothCompactSupp hh
    have hφV : (fun z => (h z : ℂ)) ∈ (TestSpaces.smoothCompactSupp (increasingTimes (m + 1)) :
        Set (PointTuple (m + 1) → ℂ)) := ⟨hφU.1, hφU.2.1, hφU.2.2.trans Set.inter_subset_left⟩
    have hψV : (fun z => (h z : ℂ)) ∘ (rotatePermuteHomeomorph R σ).symm ∈
        (TestSpaces.smoothCompactSupp (increasingTimes (m + 1)) :
          Set (PointTuple (m + 1) → ℂ)) :=
      comp_homeomorph_mem_smoothCompactSupp (rotatePermuteHomeomorph R σ).symm
        (contDiff_unrotate R σ) hφU fun y hy' => by
        simpa using hy'.2
    have hsubV : increasingTimes (m + 1) ⊆ distinctLocus (m + 1) :=
      increasingTimes_subset_distinctLocus _
    have hφD : (fun z => (h z : ℂ)) ∈ (TestSpaces.smoothCompactSupp
        (distinctLocus (m + 1)) : Set (PointTuple (m + 1) → ℂ)) :=
      ⟨hφV.1, hφV.2.1, hφV.2.2.trans hsubV⟩
    have hψD : (fun z => (h z : ℂ)) ∘ (rotatePermuteHomeomorph R σ).symm ∈
        (TestSpaces.smoothCompactSupp (distinctLocus (m + 1)) :
          Set (PointTuple (m + 1) → ℂ)) :=
      ⟨hψV.1, hψV.2.1, hψV.2.2.trans hsubV⟩
    have hφF := mem_schwartzFlatOffDiagonal_of_smooth hC hn hφD
    have hψF := mem_schwartzFlatOffDiagonal_of_smooth hC hn hψD
    have hgF : permuteArgs σ⁻¹ (fun z => (h z : ℂ)) ∈
        ConfigSpace.schwartzFlatOffDiagonal (m + 1) := by
      refine mem_schwartzFlatOffDiagonal_of_smooth hC hn ?_
      have hg := comp_homeomorph_mem_smoothCompactSupp (W' := distinctLocus (m + 1))
        (rotatePermuteHomeomorph 1 σ⁻¹) (contDiff_rotatePermute 1 σ⁻¹) hφD ?_
      · convert hg using 1
        funext z
        simp only [permuteArgs, Function.comp_apply, rotatePermuteHomeomorph,
          Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk]
        congr 2
        funext i
        simp [rotatePermute]
      · intro w hw i j hij
        have hσ := @hw (σ i) (σ j) (by simp [rotatePermuteHomeomorph, rotatePermute, hij])
        exact σ.injective hσ
    have hmot : actOnFun ⟨R.1, R.2, 0⟩ (permuteArgs σ⁻¹ fun z => (h z : ℂ)) =
        (fun z => (h z : ℂ)) ∘ (rotatePermuteHomeomorph R σ).symm := by
      funext y
      simp [actOnFun, permuteArgs, RigidMotion.invFun, rotatePermuteHomeomorph,
        Equiv.Perm.inv_def]
      rfl
    have hmF : actOnFun ⟨R.1, R.2, 0⟩ (permuteArgs σ⁻¹ fun z => (h z : ℂ)) ∈
        ConfigSpace.schwartzFlatOffDiagonal (m + 1) := hmot ▸ hψF
    have hinv := hI S hE hS
    have e₁ := hinv.perm m ⟨_, hφF⟩ σ⁻¹ hgF
    have e₂ := hinv.orthogonal m ⟨_, hgF⟩ R hmF
    have e₃ : S.atSucc m ⟨_, hψF⟩ = S.atSucc m ⟨_, hmF⟩ :=
      congrArg _ (Subtype.ext hmot.symm)
    have r₁ := hR.2 m _ hφV hφF
    have r₂ := hR.2 m _ hψV hψF
    have i₁ : orderedIntegral E Ω A m (fun z => (h z : ℂ)) =
        ∫ z, (h z : ℂ) * orderedSchwinger E Ω A m z := by
      unfold orderedIntegral
      rw [indicator_ofReal_mul_eq Set.inter_subset_left hh]
    have i₂ : orderedIntegral E Ω A m
        ((fun z => (h z : ℂ)) ∘ (rotatePermuteHomeomorph R σ).symm) =
        ∫ z, (h z : ℂ) * orderedSchwinger E Ω A m (rotatePermuteHomeomorph R σ z) :=
      integral_indicator_comp_symm R σ hh _
    have hsum : ∫ z, (h z : ℂ) * orderedSchwinger E Ω A m (rotatePermuteHomeomorph R σ z) =
        ∫ z, (h z : ℂ) * orderedSchwinger E Ω A m z := by
      rw [← i₁, ← i₂, ← r₁, ← r₂, e₃, e₂, e₁]
    simp only [mul_sub]
    rw [integral_sub (integrable_ofReal_mul hU hh hs₂) (integrable_ofReal_mul hU hh hs₁), hsum,
      sub_self])
  exact sub_eq_zero.1 (key x ⟨hx, hy⟩)
end YangMills.Construction.MinkowskiSpace.InvariantEuclideanProof
end
