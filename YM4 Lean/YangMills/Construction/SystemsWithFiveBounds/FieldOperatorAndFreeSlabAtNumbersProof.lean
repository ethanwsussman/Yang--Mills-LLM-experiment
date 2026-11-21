import YangMills.Construction.BoundsOnEverySide.MovingTuplesOfALimitAlongStatesProof
import YangMills.Construction.LawInAState.PairOfTheLawIsNearAPointProof
import YangMills.Construction.ReflectionsAndOneInsertion.PartitionOfUnityOfMeshProof
import YangMills.Construction.LawInAState.FromSixteenCopiesToOneBoxProof
import YangMills.Construction.ReflectionsAndOneInsertion.PartitionOfUnityOfMesh
import YangMills.Construction.SystemsWithFiveBounds.FieldOperatorAndFreeSlabAtNumbers
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction
open SeparatedTuples
open ReflectionPositivity.TupleForm (PositiveSpan reflectConj)
open R4TupleForms (FinTuple singleTuple realSpanLift toTupleFunctional
  FormalMulDefined formalMulDefined_of_mem formalMul_mem finTupleEquiv)
open SlabInsertion (timeVec timeAbove insertionForm shiftDownNorm)
open InfiniteLattice (AmbientSpace)
open ReflectionsAndOneInsertion (spanClassNorm gradNorm)
open Insertion (ballRadiusRatio)
open AmbientPoints (IsTupleFunctional)
open BoundsOnEverySide (timeZeroPoint)
open TorusMetric (euclidNormVec)
open TimeAxis (timeComponent timeReflection timeIdx upperHalfSpace)
open TestFunctions (uniformNorm lipConstR4 sharpNormR4 euclidDistR4 closedBallR4 IsLipschitzFor
  HasDiameterLE)
open Continuum.SeparatedFourTuples (IsMultilin SepTupleLen ofFixedLength sepTuple_ext EuclidFour
  dist_toLp_eq_euclidNormVec)
namespace SystemsWithFiveBounds
namespace SingleCellToFieldAndSlab
variable {s : Conventions.StandingParameters}
private theorem getD_append_cons (A B : List RealValued) (h : RealValued) :
    (A ++ h :: B).getD A.length 0 = h := by
  simp
private theorem getD_append_cons_congr (A B : List RealValued) (h h' : RealValued) {j : ℕ}
    (hj : j ≠ A.length) :
    (A ++ h :: B).getD j 0 = (A ++ h' :: B).getD j 0 := by
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt]
  · rw [List.getD_append_right _ _ _ _ hgt.le, List.getD_append_right _ _ _ _ hgt.le]
    obtain ⟨m, hm⟩ : ∃ m, j - A.length = m + 1 := ⟨j - A.length - 1, by omega⟩
    rw [hm]
    simp
private def listSepTuple (T : SepTuple) {n : ℕ} (hT : T.1.length = n) : SepTupleLen s n :=
  ⟨fun k => T.1.get (Fin.cast hT.symm k), (R4TupleForms.mem_separatedTuples_iff_ofFn _).2 (by
    have h : List.ofFn (fun k : Fin n => T.1.get (Fin.cast hT.symm k)) = T.1 :=
      (List.ofFn_congr hT T.1.get).symm.trans (List.ofFn_get _)
    rw [h]
    exact T.2)⟩
private theorem ofFixedLength_listSepTuple (T : SepTuple) {n : ℕ} (hT : T.1.length = n) :
    ofFixedLength (listSepTuple (s := s) T hT) = (finTupleEquiv s).symm T :=
  sepTuple_ext hT.symm fun _ => rfl
private theorem listSepTuple_apply (T : SepTuple) {n : ℕ} (hT : T.1.length = n) (k : Fin n) :
    (listSepTuple (s := s) T hT).1 k = T.1.getD k 0 := by
  have hk : (k : ℕ) < T.1.length := by
    rw [hT]
    exact k.2
  change T.1.get (Fin.cast hT.symm k) = _
  rw [List.getD_eq_getElem _ _ hk]
  rfl
private theorem functional_linear_at {σ : FinTuple s → ℝ} (hm : IsMultilin σ)
    (A B : List RealValued) (f f' : RealValued) (t t' : ℝ) (X X' Z : SepTuple)
    (hX : X.1 = A ++ f :: B) (hX' : X'.1 = A ++ f' :: B)
    (hZ : Z.1 = A ++ (t • f + t' • f') :: B) :
    σ ((finTupleEquiv s).symm Z) =
      t * σ ((finTupleEquiv s).symm X) + t' * σ ((finTupleEquiv s).symm X') := by
  have len : ∀ h : RealValued, (A ++ h :: B).length = A.length + B.length + 1 := fun h => by
    simp
    omega
  have lX : X.1.length = A.length + B.length + 1 := by rw [hX, len]
  have lX' : X'.1.length = A.length + B.length + 1 := by rw [hX', len]
  have lZ : Z.1.length = A.length + B.length + 1 := by rw [hZ, len]
  have h := hm (A.length + B.length + 1) (by omega) ⟨A.length, by omega⟩ t t'
    (listSepTuple (s := s) X lX) (listSepTuple (s := s) X' lX') (listSepTuple (s := s) Z lZ)
    (fun j hj => by
      have hj' : (j : ℕ) ≠ A.length := fun e => hj (Fin.ext e)
      rw [listSepTuple_apply, listSepTuple_apply, hX, hX']
      exact getD_append_cons_congr A B f f' hj')
    (by
      rw [listSepTuple_apply, listSepTuple_apply, listSepTuple_apply, hX, hX', hZ]
      simp only [getD_append_cons]
      rfl)
    (fun j hj => by
      have hj' : (j : ℕ) ≠ A.length := fun e => hj (Fin.ext e)
      rw [listSepTuple_apply, listSepTuple_apply, hZ, hX]
      exact getD_append_cons_congr A B _ f hj')
  simpa only [ofFixedLength_listSepTuple] using h
private theorem singleTuple_mem {O : Set AmbientSpace} {g : RealValued} (hg : IsC1c g)
    (hs : tsupport g ⊆ O) : singleTuple g hg ∈ supportedIn O := fun f hf => by
  obtain rfl : f = g := List.mem_singleton.1 hf
  exact hs
private theorem juxt_mem {O O' : Set AmbientSpace} (hO : Disjoint O O') {X Y : SepTuple}
    (hX : X ∈ supportedIn O) (hY : Y ∈ supportedIn O') : SepTuple.juxt X Y ∈ supportedIn (O ∪ O') := by
  intro f hf
  rw [SepTuple.juxt_val (composable_of_mem_supportedIn hO hX hY)] at hf
  rcases List.mem_append.1 hf with hf | hf
  · exact (hX f hf).trans Set.subset_union_left
  · exact (hY f hf).trans Set.subset_union_right
private theorem juxt_juxt {O₁ O₂ O₃ : Set AmbientSpace} (h12 : Disjoint O₁ O₂) (h13 : Disjoint O₁ O₃)
    (h23 : Disjoint O₂ O₃) {X Y Z : SepTuple} (hX : X ∈ supportedIn O₁) (hY : Y ∈ supportedIn O₂)
    (hZ : Z ∈ supportedIn O₃) :
    SepTuple.juxt (SepTuple.juxt X Y) Z = SepTuple.juxt X (SepTuple.juxt Y Z) := by
  have hXY := juxt_mem h12 hX hY
  have hYZ := juxt_mem h23 hY hZ
  have d1 : Disjoint (O₁ ∪ O₂) O₃ := Set.disjoint_union_left.2 ⟨h13, h23⟩
  have d2 : Disjoint O₁ (O₂ ∪ O₃) := Set.disjoint_union_right.2 ⟨h12, h13⟩
  apply Subtype.ext
  rw [SepTuple.juxt_val (composable_of_mem_supportedIn d1 hXY hZ),
    SepTuple.juxt_val (composable_of_mem_supportedIn h12 hX hY),
    SepTuple.juxt_val (composable_of_mem_supportedIn d2 hX hYZ),
    SepTuple.juxt_val (composable_of_mem_supportedIn h23 hY hZ), List.append_assoc]
private theorem formalMul_formalMul {O₁ O₂ O₃ : Set AmbientSpace} (h12 : Disjoint O₁ O₂)
    (h13 : Disjoint O₁ O₃) (h23 : Disjoint O₂ O₃) {A E B : FormalSpan} (hA : A ∈ spanIn O₁)
    (hE : E ∈ spanIn O₂) (hB : B ∈ spanIn O₃) :
    formalMul (formalMul A E) B = formalMul A (formalMul E B) := by
  induction hA using Submodule.span_induction with
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | smul c a _ ha => simp only [map_smul, LinearMap.smul_apply, ha]
  | mem G hG =>
    obtain ⟨X, rfl⟩ := hG
    induction hE using Submodule.span_induction with
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | smul c a _ ha => simp only [map_smul, LinearMap.smul_apply, ha]
    | mem G hG =>
      obtain ⟨Y, rfl⟩ := hG
      induction hB using Submodule.span_induction with
      | zero => simp
      | add a b _ _ ha hb => simp only [map_add, ha, hb]
      | smul c a _ ha => simp only [map_smul, ha]
      | mem G hG =>
        obtain ⟨Z, rfl⟩ := hG
        simp only [formalMul_basisVec]
        rw [juxt_juxt h12 h13 h23 X.2 Y.2 Z.2]
private def middle (σ : FinTuple s → ℝ) (A B : FormalSpan) (g : RealValued) : ℂ :=
  open Classical in
  if hg : IsC1c g then
    realSpanLift σ (formalMul (formalMul A (basisVec (singleTuple g hg))) B)
  else 0
private theorem middle_eq (σ : FinTuple s → ℝ) (A B : FormalSpan) {g : RealValued}
    (hg : IsC1c g) :
    middle σ A B g =
      realSpanLift σ (formalMul (formalMul A (basisVec (singleTuple g hg))) B) :=
  dif_pos hg
private def IsTestOn (O : Set AmbientSpace) (g : RealValued) : Prop :=
  IsC1c g ∧ tsupport g ⊆ O
private theorem IsTestOn.lincomb {O : Set AmbientSpace} {g g' : RealValued} (hg : IsTestOn O g)
    (hg' : IsTestOn O g') (t t' : ℝ) : IsTestOn O (t • g + t' • g') := by
  refine ⟨⟨(hg.1.1.const_smul t).add (hg'.1.1.const_smul t'), ?_⟩, ?_⟩
  · exact (hg.1.2.smul_left (f := fun _ => t)).add (hg'.1.2.smul_left (f := fun _ => t'))
  · have hsm : ∀ (c : ℝ) (u : RealValued), tsupport (c • u) ⊆ tsupport u := fun c u =>
      closure_mono fun x hx h => hx (by simp [h])
    exact (tsupport_add _ _).trans (Set.union_subset ((hsm t g).trans hg.2) ((hsm t' g').trans hg'.2))
private theorem middle_lincomb {σ : FinTuple s → ℝ} (hm : IsMultilin σ)
    {O₁ O₂ O₃ : Set AmbientSpace} (h12 : Disjoint O₁ O₂) (h13 : Disjoint O₁ O₃) (h23 : Disjoint O₂ O₃)
    {A B : FormalSpan} (hA : A ∈ spanIn O₁) (hB : B ∈ spanIn O₃)
    {g g' : RealValued} (hg : IsTestOn O₂ g) (hg' : IsTestOn O₂ g') (t t' : ℝ) :
    middle σ A B (t • g + t' • g') = t * middle σ A B g + t' * middle σ A B g' := by
  have hc := hg.lincomb hg' t t'
  rw [middle_eq σ A B hc.1, middle_eq σ A B hg.1, middle_eq σ A B hg'.1]
  induction hA using Submodule.span_induction with
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb]
    ring
  | smul c a _ ha =>
    simp only [map_smul, LinearMap.smul_apply, ha, smul_eq_mul]
    ring
  | mem G hG =>
    obtain ⟨X, rfl⟩ := hG
    induction hB using Submodule.span_induction with
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [map_add, ha, hb]
      ring
    | smul c a _ ha =>
      simp only [map_smul, ha, smul_eq_mul]
      ring
    | mem G hG =>
      obtain ⟨Z, rfl⟩ := hG
      simp only [formalMul_basisVec]
      have hval : ∀ W : SepTuple, realSpanLift σ (basisVec W) =
          ((σ ((finTupleEquiv s).symm W) : ℝ) : ℂ) := fun W => linearExtend_basisVec _ _
      have hlist : ∀ {u : RealValued} (hu : IsTestOn O₂ u),
          (SepTuple.juxt (SepTuple.juxt X.1 (singleTuple u hu.1)) Z.1).1 = X.1.1 ++ u :: Z.1.1 := by
        intro u hu
        have hu' := singleTuple_mem hu.1 hu.2
        have d1 : Disjoint (O₁ ∪ O₂) O₃ := Set.disjoint_union_left.2 ⟨h13, h23⟩
        rw [SepTuple.juxt_val (composable_of_mem_supportedIn d1
            (juxt_mem h12 X.2 hu') Z.2),
          SepTuple.juxt_val (composable_of_mem_supportedIn h12 X.2 hu')]
        simp [singleTuple]
      rw [hval, hval, hval, functional_linear_at hm X.1.1 Z.1.1 g g' t t' _ _ _ (hlist hg)
        (hlist hg') (hlist hc)]
      push_cast
      ring
section Gradient
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem gradNorm_continuous {f : AmbientSpace → E} (hf : ContDiff ℝ 1 f) :
    Continuous (gradNorm f) := by
  unfold gradNorm
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun μ _ =>
    (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).norm.pow 2))
private theorem gradNorm_bddAbove {f : AmbientSpace → E} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : BddAbove (Set.range (gradNorm f)) := by
  have hs : HasCompactSupport (gradNorm f) := by
    refine (hc.fderiv (𝕜 := ℝ)).mono fun x hx hz => hx ?_
    have hz' : fderiv ℝ f x = 0 := hz
    simp [gradNorm, hz']
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous (gradNorm_continuous hf)
  exact ⟨C, by
    rintro _ ⟨x, rfl⟩
    exact (le_abs_self _).trans (hC x)⟩
private theorem gradNorm_nonneg_at (f : AmbientSpace → E) (x : AmbientSpace) : 0 ≤ gradNorm f x :=
  Real.sqrt_nonneg _
end Gradient
private def supGrad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : AmbientSpace → E) : ℝ :=
  ⨆ x, gradNorm f x
private theorem supGrad_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AmbientSpace → E) : 0 ≤ supGrad f := Real.iSup_nonneg fun x => gradNorm_nonneg_at f x
private theorem eq_sum_single (w : AmbientSpace) : w = ∑ μ, w μ • (Pi.single μ 1 : AmbientSpace) := by
  funext i
  simp [Finset.sum_apply, Pi.single_apply]
private theorem abs_fderiv_le_gradNorm (f : AmbientSpace → ℝ) (x w : AmbientSpace) :
    |fderiv ℝ f x w| ≤ gradNorm f x * euclidNormVec w := by
  have h1 : fderiv ℝ f x w = ∑ μ, w μ * fderiv ℝ f x (Pi.single μ 1) := by
    conv_lhs => rw [eq_sum_single w]
    simp [map_sum]
  rw [h1, gradNorm, euclidNormVec, ← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  refine Real.abs_le_sqrt ?_
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun μ => w μ)
    (fun μ => fderiv ℝ f x (Pi.single μ 1))
  simp only [Real.norm_eq_abs, sq_abs]
  linarith [h2, mul_comm (∑ μ, w μ ^ 2) (∑ μ, fderiv ℝ f x (Pi.single μ 1) ^ 2)]
private theorem abs_sub_le_supGrad {f : RealValued} (hf : IsC1c f) (x y : AmbientSpace) :
    |f x - f y| ≤ supGrad f * euclidNormVec (x - y) := by
  set w := x - y with hw
  have hb := gradNorm_bddAbove hf.1 hf.2
  have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (y + t • w)) (fderiv ℝ f (y + t • w) w) t := by
    intro t
    have hline : HasDerivAt (fun t : ℝ => y + t • w) w t := by
      simpa using ((hasDerivAt_id t).smul_const w).const_add y
    have hd : DifferentiableAt ℝ f (y + t • w) := (hf.1.differentiable one_ne_zero) _
    exact hd.hasFDerivAt.comp_hasDerivAt t hline
  have hbound : ∀ t ∈ (Set.univ : Set ℝ), ‖fderiv ℝ f (y + t • w) w‖ ≤
      supGrad f * euclidNormVec w := fun t _ => by
    rw [Real.norm_eq_abs]
    exact (abs_fderiv_le_gradNorm f _ w).trans (mul_le_mul_of_nonneg_right (le_ciSup hb _)
      (Real.sqrt_nonneg _))
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hder t).hasDerivWithinAt) hbound convex_univ (Set.mem_univ (0 : ℝ)) (Set.mem_univ 1)
  simp only [zero_smul, add_zero, one_smul, sub_zero, norm_one, mul_one] at h
  have h2 : y + w = x := by
    rw [hw]
    abel
  rw [h2, Real.norm_eq_abs] at h
  exact h
private theorem isLipschitzFor_of_isC1c {f : RealValued} (hf : IsC1c f) :
    IsLipschitzFor euclidDistR4 f :=
  ⟨supGrad f, supGrad_nonneg f, fun x y => abs_sub_le_supGrad hf x y⟩
abbrev _root_.YangMills.DeltaSharedProofs.p501087 := @isLipschitzFor_of_isC1c
abbrev _root_.YangMills.SharedProofs.p37577 := @isLipschitzFor_of_isC1c
private theorem lipConstR4_le_supGrad {f : RealValued} (hf : IsC1c f) :
    lipConstR4 f ≤ supGrad f :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨supGrad_nonneg f, fun x y => abs_sub_le_supGrad hf x y⟩
private theorem lipConstR4_nonneg_of {f : RealValued} (hf : IsLipschitzFor euclidDistR4 f) :
    0 ≤ lipConstR4 f := by apply _root_.YangMills.Construction.MeshPartition.lipConstR4_nonneg <;> assumption
private theorem norm_sub_le_lipConstR4_mul_dist {f : RealValued}
    (hf : IsLipschitzFor euclidDistR4 f) (x y : AmbientSpace) :
    ‖f x - f y‖ ≤ lipConstR4 f * euclidDistR4 x y := by apply _root_.YangMills.DeltaSharedProofs.p501590 <;> assumption
private theorem supGrad_le_lipConstR4 {k : RealValued} (hk : IsC1c k) :
    supGrad k ≤ lipConstR4 k := by
  have hl := isLipschitzFor_of_isC1c hk
  refine ciSup_le fun x => ?_
  set D := fderiv ℝ k x with hD
  set w : AmbientSpace := fun μ => D (Pi.single μ 1) with hw
  have hG : gradNorm k x = euclidNormVec w := by
    simp only [gradNorm, euclidNormVec, Real.norm_eq_abs, sq_abs]
    rfl
  have hDw : D w = euclidNormVec w ^ 2 := by
    have h1 : D w = ∑ μ, w μ * D (Pi.single μ 1) := by
      conv_lhs => rw [eq_sum_single w]
      simp [map_sum]
    rw [h1, euclidNormVec, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun μ _ => by
      simp only [hw]
      ring
  have hder : HasDerivAt (fun t : ℝ => k (x + t • w)) (D w) 0 := by
    have hline : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
    have hd : HasFDerivAt k D (x + (0 : ℝ) • w) := by
      simpa [hD] using ((hk.1.differentiable one_ne_zero) x).hasFDerivAt
    exact hd.comp_hasDerivAt (0 : ℝ) hline
  have hnn : 0 ≤ lipConstR4 k * euclidNormVec w :=
    mul_nonneg (lipConstR4_nonneg_of hl) (Real.sqrt_nonneg _)
  have hlip : LipschitzWith (Real.toNNReal (lipConstR4 k * euclidNormVec w))
      (fun t : ℝ => k (x + t • w)) := by
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    have h1 := norm_sub_le_lipConstR4_mul_dist hl (x + s • w) (x + t • w)
    have h2 : euclidDistR4 (x + s • w) (x + t • w) =
        |s - t| * euclidNormVec w := by
      have h3 : x + s • w - (x + t • w) = (s - t) • w := by
        rw [sub_smul]
        abel
      simp only [euclidDistR4, h3, euclidNormVec, Pi.smul_apply, smul_eq_mul, mul_pow]
      rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    rw [Real.dist_eq, Real.coe_toNNReal _ hnn]
    rw [h2, Real.norm_eq_abs] at h1
    rw [Real.dist_eq]
    calc |k (x + s • w) - k (x + t • w)| ≤ _ := h1
      _ = _ := by ring
  have hn := hder.le_of_lipschitz hlip
  rw [Real.coe_toNNReal _ hnn, hDw, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hn
  rw [hG]
  have hve : 0 ≤ euclidNormVec w := Real.sqrt_nonneg _
  rcases hve.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact lipConstR4_nonneg_of hl
  · have : euclidNormVec w * euclidNormVec w ≤ lipConstR4 k * euclidNormVec w := by
      rw [← sq]
      exact hn
    exact le_of_mul_le_mul_right this hpos
private theorem euclidNormVec_timeVec_eq (c : ℝ) : euclidNormVec (timeVec c) = |c| := by
  simp only [euclidNormVec, Fin.sum_univ_four, timeVec, timeIdx]
  simp [Pi.single_apply, Real.sqrt_sq_eq_abs]
private theorem norm_le_uniformNorm_of {E : Type*} [NormedAddCommGroup E] {f : AmbientSpace → E}
    (hc : Continuous f) (hs : HasCompactSupport f) (x : AmbientSpace) : ‖f x‖ ≤ uniformNorm f := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
  exact le_ciSup (f := fun x => ‖f x‖) ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩ x
private theorem uniformNorm_nonneg_of {E : Type*} [NormedAddCommGroup E] (f : AmbientSpace → E) :
    0 ≤ uniformNorm f := Real.iSup_nonneg fun _ => norm_nonneg _
private theorem uniformNorm_le_of_slab {f : RealValued} (hf : IsC1c f) {η : ℝ} (hη : 0 < η)
    (hs : tsupport f ⊆ {x | η ≤ timeComponent x ∧ timeComponent x ≤ 3 * η}) :
    uniformNorm f ≤ η * supGrad f := by
  have hG := supGrad_nonneg f
  refine ciSup_le fun x => ?_
  rw [Real.norm_eq_abs]
  by_cases hx : f x = 0
  · rw [hx, abs_zero]
    positivity
  have hxs := hs (subset_tsupport _ hx)
  have hx1 : η ≤ x 3 := hxs.1
  have hx2 : x 3 ≤ 3 * η := hxs.2
  have hzero : ∀ y : AmbientSpace, (y 3 < η ∨ 3 * η < y 3) → f y = 0 := by
    intro y hy
    by_contra hne
    have hys := hs (subset_tsupport _ hne)
    have h1 : η ≤ y 3 := hys.1
    have h2 : y 3 ≤ 3 * η := hys.2
    rcases hy with hy | hy <;> linarith
  have key : ∀ t : ℝ, 0 < t → |f x| ≤ supGrad f * (η + t) := by
    intro t ht
    rcases le_total (x 3) (2 * η) with hc | hc
    · have hy := hzero (x - timeVec (x 3 - η + t)) (Or.inl (by
        have : (x - timeVec (x 3 - η + t)) 3 = x 3 - (x 3 - η + t) := by
          simp [timeVec, timeIdx]
        rw [this]
        linarith))
      have h1 := abs_sub_le_supGrad hf x (x - timeVec (x 3 - η + t))
      have hp : 0 < x 3 - η + t := by linarith
      rw [hy, sub_zero, sub_sub_cancel, euclidNormVec_timeVec_eq, abs_of_pos hp] at h1
      have hq : x 3 - η + t ≤ η + t := by linarith
      exact h1.trans (mul_le_mul_of_nonneg_left hq hG)
    · have hy := hzero (x + timeVec (3 * η - x 3 + t)) (Or.inr (by
        have : (x + timeVec (3 * η - x 3 + t)) 3 = x 3 + (3 * η - x 3 + t) := by
          simp [timeVec, timeIdx]
        rw [this]
        linarith))
      have h1 := abs_sub_le_supGrad hf x (x + timeVec (3 * η - x 3 + t))
      have h2 : x - (x + timeVec (3 * η - x 3 + t)) = -timeVec (3 * η - x 3 + t) := by abel
      have h3 : euclidNormVec (-timeVec (3 * η - x 3 + t)) =
          euclidNormVec (timeVec (3 * η - x 3 + t)) := by
        simp [euclidNormVec]
      have hp : 0 < 3 * η - x 3 + t := by linarith
      rw [hy, sub_zero, h2, h3, euclidNormVec_timeVec_eq, abs_of_pos hp] at h1
      have hq : 3 * η - x 3 + t ≤ η + t := by linarith
      exact h1.trans (mul_le_mul_of_nonneg_left hq hG)
  have hlim : Tendsto (fun t : ℝ => supGrad f * (η + t)) (𝓝[>] 0)
      (𝓝 (supGrad f * (η + 0))) :=
    ((continuous_const.mul (continuous_const.add continuous_id)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have := ge_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin] with t ht using key t ht)
  calc |f x| ≤ supGrad f * (η + 0) := this
    _ = η * supGrad f := by ring
private def addPermR (v : AmbientSpace) : Equiv.Perm AmbientSpace := Equiv.addRight v
private theorem coe_addPermR (v : AmbientSpace) : ⇑(addPermR v) = SeparatedTuples.translate v := rfl
private def reflPerm : Equiv.Perm AmbientSpace where
  toFun := timeReflection
  invFun := timeReflection
  left_inv := SlabInsertion.timeReflection_timeReflection
  right_inv := SlabInsertion.timeReflection_timeReflection
private theorem isEuclidIsometry_reflPerm : IsEuclidIsometry ⇑reflPerm := by
  intro x y
  simp only [euclidNormVec, Fin.sum_univ_four]
  congr 1
  simp [reflPerm, timeReflection]
  ring
abbrev _root_.YangMills.DeltaSharedProofs.p502081 := @isEuclidIsometry_reflPerm
private theorem isC1c_shift {f : RealValued} (hf : IsC1c f) (v : AmbientSpace) :
    IsC1c fun x => f (x - v) := by apply _root_.YangMills.Construction.BoundsOnEverySide.TranslatedTuples.isC1c_shift <;> assumption
private theorem push_translate_single (v : AmbientSpace) {f : RealValued} (hf : IsC1c f) :
    push (translate v) (singleTuple f hf) = singleTuple (fun x => f (x - v)) (isC1c_shift hf v) := by
  have hl : pushList (translate v) (singleTuple f hf).1 = [fun x => f (x - v)] := by
    rw [pushList_translate]
    rfl
  have hsep : IsDisjointlySupported (pushList (translate v) (singleTuple f hf).1) := by
    rw [hl]
    exact (singleTuple _ (isC1c_shift hf v)).2
  unfold push
  rw [dif_pos hsep]
  exact Subtype.ext hl
private theorem pushSpan_perm_mul (rules : ReflectionsAndOneInsertion.FunctionAndSpanActionLaws)
    {r r' : Equiv.Perm AmbientSpace} (hr : IsEuclidIsometry r) (hr' : IsEuclidIsometry r')
    (Ξ : FormalSpan) :
    pushSpan (⇑(r * r')) Ξ = pushSpan r (pushSpan r' Ξ) :=
  ((rules r r' hr hr').2 Ξ 0 (by intro X hX; simp at *)).1
private theorem conjugation_pushSpan_perm
    (rules : ReflectionsAndOneInsertion.FunctionAndSpanActionLaws)
    {r : Equiv.Perm AmbientSpace} (hr : IsEuclidIsometry r) (Ξ : FormalSpan) :
    conjugation (pushSpan r Ξ) = pushSpan r (conjugation Ξ) :=
  ((rules r r hr hr).2 Ξ 0 (by intro X hX; simp at *)).2.2.2
private theorem reflectConj_mem_timeBelow (Q : PositiveSpan) :
    reflectConj Q ∈ spanIn (SlabInsertion.timeBelow 0) := by
  refine SlabInsertion.pushSpan_mem_spanIn SlabInsertion.invMap_timeReflection
    SlabInsertion.continuous_timeReflection (fun x hx => ?_) (SlabInsertion.conjugation_mem_spanIn Q.2)
  have h : timeComponent (timeReflection x) > 0 := hx
  rw [SlabInsertion.timeComponent_timeReflection] at h
  change timeComponent x < 0
  linarith
abbrev _root_.YangMills.DeltaSharedProofs.p500614 := @reflectConj_mem_timeBelow
abbrev _root_.YangMills.SharedProofs.p8728 := @reflectConj_mem_timeBelow
private theorem pushSpan_mem_timeAbove (l : ℝ) (P : PositiveSpan) :
    pushSpan (translate (timeVec l)) P.1 ∈ spanIn (timeAbove l) := by
  have hc : Continuous fun x : AmbientSpace => x - timeVec l := continuous_id.sub continuous_const
  have hO : ∀ x, x - timeVec l ∈ upperHalfSpace → x ∈ timeAbove l := by
    intro x hx
    have h : timeComponent (x - timeVec l) > 0 := hx
    rw [SlabInsertion.timeComponent_sub_timeVec] at h
    change l < timeComponent x
    linarith
  exact SlabInsertion.pushSpan_mem_spanIn (SlabInsertion.invMap_translate _) hc hO P.2
abbrev _root_.YangMills.SharedProofs.p50971 := @pushSpan_mem_timeAbove
private abbrev slabOf (T : ℝ) : Set AmbientSpace := {x | 0 < timeComponent x ∧ timeComponent x < T}
private theorem disjoint_timeBelow_slabOf {T : ℝ} : Disjoint (SlabInsertion.timeBelow 0) (slabOf T) :=
  Set.disjoint_left.2 fun x h h' => by
    have h₁ : timeComponent x < 0 := h
    linarith [h'.1]
abbrev _root_.YangMills.DeltaSharedProofs.p502575 := @disjoint_timeBelow_slabOf
private theorem disjoint_timeBelow_timeAbove_of {T : ℝ} (hT : 0 < T) :
    Disjoint (SlabInsertion.timeBelow 0) (timeAbove T) :=
  Set.disjoint_left.2 fun x h h' => by
    have h₁ : timeComponent x < 0 := h
    have h₂ : T < timeComponent x := h'
    linarith
private theorem disjoint_slabOf_timeAbove {T : ℝ} : Disjoint (slabOf T) (timeAbove T) :=
  Set.disjoint_left.2 fun x h h' => by
    have h₂ : T < timeComponent x := h'
    linarith [h.2]
private theorem smul_timeUnitVec_eq (u : ℝ) :
    u • ReflectionsAndOneInsertion.timeUnitVec = timeVec u := by
  funext μ
  by_cases hμ : μ = InfiniteLattice.timeAxis
  · subst hμ
    simp [ReflectionsAndOneInsertion.timeUnitVec, ChessboardTori.coordVec, timeVec,
      timeIdx, InfiniteLattice.timeAxis]
  · have hμ' : μ ≠ timeIdx := hμ
    simp [ReflectionsAndOneInsertion.timeUnitVec, ChessboardTori.coordVec, timeVec,
      Pi.single_eq_of_ne hμ, Pi.single_eq_of_ne hμ']
private theorem timeVec_add_eq (u w : ℝ) : timeVec (u + w) = timeVec u + timeVec w := by
  funext μ
  by_cases hμ : μ = timeIdx
  · subst hμ
    simp [timeVec]
  · simp [timeVec, Pi.single_eq_of_ne hμ]
private theorem isTestOn_zero (O : Set AmbientSpace) : IsTestOn O (0 : RealValued) :=
  ⟨⟨contDiff_const, HasCompactSupport.zero⟩, by simp [tsupport]⟩
private theorem middle_zero {σ : FinTuple s → ℝ} (hm : IsMultilin σ)
    {O₁ O₂ O₃ : Set AmbientSpace} (h12 : Disjoint O₁ O₂) (h13 : Disjoint O₁ O₃) (h23 : Disjoint O₂ O₃)
    {A B : FormalSpan} (hA : A ∈ spanIn O₁) (hB : B ∈ spanIn O₃) :
    middle σ A B 0 = 0 := by
  have h := middle_lincomb hm h12 h13 h23 hA hB (isTestOn_zero O₂) (isTestOn_zero O₂) 0 0
  simpa using h
private theorem middle_finsum {σ : FinTuple s → ℝ} (hm : IsMultilin σ)
    {O₁ O₂ O₃ : Set AmbientSpace} (h12 : Disjoint O₁ O₂) (h13 : Disjoint O₁ O₃) (h23 : Disjoint O₂ O₃)
    {A B : FormalSpan} (hA : A ∈ spanIn O₁) (hB : B ∈ spanIn O₃)
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (g : ι → RealValued)
    (hg : ∀ i ∈ S, IsTestOn O₂ (g i)) :
    IsTestOn O₂ (∑ i ∈ S, g i) ∧ middle σ A B (∑ i ∈ S, g i) = ∑ i ∈ S, middle σ A B (g i) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨by simpa using isTestOn_zero O₂, by simpa using middle_zero hm h12 h13 h23 hA hB⟩
  | insert a S ha ih =>
    obtain ⟨h₁, h₂⟩ := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hga := hg a (Finset.mem_insert_self a S)
    have hc := hga.lincomb h₁ 1 1
    have hl := middle_lincomb hm h12 h13 h23 hA hB hga h₁ 1 1
    simp only [one_smul, Complex.ofReal_one, one_mul] at hc hl
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨hc, by rw [hl, h₂]⟩
private theorem abs_coord_le_euclidNormVec (v : AmbientSpace) (μ : Fin 4) :
    |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.SharedProofs.p10398 <;> assumption
private theorem exists_boxFrom_cover {f : RealValued} (hf : IsC1c f) {η R : ℝ}
    (hs : tsupport f ⊆ {x | η ≤ timeComponent x ∧ timeComponent x ≤ 3 * η})
    (hd : HasDiameterLE (tsupport f) R) :
    ∃ b : Fin 4 → ℝ, tsupport f ⊆ MeshPartition.boxFrom b ![R, R, R, 2 * η] := by
  rcases (tsupport f).eq_empty_or_nonempty with he | hne
  · exact ⟨0, by rw [he]; exact Set.empty_subset _⟩
  have hK : IsCompact (tsupport f) := hf.2
  have hmin : ∀ μ : Fin 4, ∃ m ∈ tsupport f, ∀ x ∈ tsupport f, m μ ≤ x μ := fun μ => by
    obtain ⟨m, hm, h⟩ := hK.exists_isMinOn hne (continuous_apply μ).continuousOn
    exact ⟨m, hm, fun x hx => h hx⟩
  choose m hm hmle using hmin
  refine ⟨![m 0 0, m 1 1, m 2 2, η], fun x hx μ => ?_⟩
  have hcoord : ∀ ν : Fin 4, x ν - m ν ν ≤ R := fun ν =>
    (le_abs_self _).trans ((abs_coord_le_euclidNormVec (x - m ν) ν).trans (hd x hx _ (hm ν)))
  have hx' := hs hx
  have h3a : η ≤ x 3 := hx'.1
  have h3b : x 3 ≤ 3 * η := hx'.2
  fin_cases μ
  · exact ⟨hmle 0 x hx, by simpa using by linarith [hcoord 0]⟩
  · exact ⟨hmle 1 x hx, by simpa using by linarith [hcoord 1]⟩
  · exact ⟨hmle 2 x hx, by simpa using by linarith [hcoord 2]⟩
  · exact ⟨by simpa using h3a, by simpa using by linarith⟩
private theorem spanIn_mono_of {O O' : Set AmbientSpace} (h : O ⊆ O') {W : FormalSpan}
    (hW : W ∈ spanIn O) : W ∈ spanIn O' :=
  (R4TupleForms.mem_spanIn_iff _ W).2 fun X hX f hf =>
    ((R4TupleForms.mem_spanIn_iff _ W).1 hW X hX f hf).trans h
open scoped ComplexOrder in
private theorem spanClassNorm_sq_le_norm {ς : TupleFunctional}
    (hpsd : HilbertSpaceBasics.IsPosSemidef (ReflectionPositivity.TupleForm.reflectionForm ς))
    (G : PositiveSpan) :
    spanClassNorm ς G ^ 2 ≤ ‖ReflectionPositivity.TupleForm.reflectionForm ς G G‖ := by
  have h0 : 0 ≤ (ReflectionPositivity.TupleForm.reflectionForm ς G G).re :=
    (Complex.le_def.1 (hpsd.nonneg G)).1
  unfold spanClassNorm
  rw [Real.sq_sqrt h0]
  exact Complex.re_le_norm _
private theorem contDiff_of_isC1cComplex_of {f : ComplexTestFunctions.ComplexValued}
    (hf : ComplexTestFunctions.IsC1cComplex f) : ContDiff ℝ 1 f := by
  have h : f = fun x => Complex.ofRealCLM (ComplexTestFunctions.rePart f x) +
      Complex.ofRealCLM (ComplexTestFunctions.imPart f x) * Complex.I := by
    funext x
    simp [ComplexTestFunctions.rePart, ComplexTestFunctions.imPart, Complex.re_add_im]
  rw [h]
  exact (Complex.ofRealCLM.contDiff.comp hf.1.1).add
    ((Complex.ofRealCLM.contDiff.comp hf.1.2).mul contDiff_const)
private theorem gradNorm_comp_clm_le {f : ComplexTestFunctions.ComplexValued} (hc : ContDiff ℝ 1 f)
    (Φ : ℂ →L[ℝ] ℝ) (hΦ : ∀ z, |Φ z| ≤ ‖z‖) (x : AmbientSpace) :
    gradNorm (fun y => Φ (f y)) x ≤ gradNorm f x := by
  have hd : DifferentiableAt ℝ f x := hc.differentiable one_ne_zero x
  have h1 : fderiv ℝ (fun y => Φ (f y)) x = Φ.comp (fderiv ℝ f x) :=
    (Φ.hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  unfold gradNorm
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun μ _ => ?_)
  rw [h1, ContinuousLinearMap.comp_apply, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hΦ _) 2
private theorem supGrad_comp_clm_le {f : ComplexTestFunctions.ComplexValued}
    (hf : ComplexTestFunctions.IsC1cComplex f) (Φ : ℂ →L[ℝ] ℝ) (hΦ : ∀ z, |Φ z| ≤ ‖z‖)
    {g : RealValued} (hg : ∀ y, g y = Φ (f y)) :
    supGrad g ≤ ⨆ x, gradNorm f x := by
  have hc := contDiff_of_isC1cComplex_of hf
  obtain rfl : g = fun y => Φ (f y) := funext hg
  refine ciSup_le fun x => (gradNorm_comp_clm_le hc Φ hΦ x).trans ?_
  exact le_ciSup (gradNorm_bddAbove hc hf.2) x
private theorem uniformNorm_comp_clm_le {f : ComplexTestFunctions.ComplexValued}
    (hf : ComplexTestFunctions.IsC1cComplex f) (Φ : ℂ →L[ℝ] ℝ) (hΦ : ∀ z, |Φ z| ≤ ‖z‖)
    {g : RealValued} (hg : ∀ y, g y = Φ (f y)) :
    uniformNorm g ≤ uniformNorm f := by
  have hc := (contDiff_of_isC1cComplex_of hf).continuous
  obtain rfl : g = fun y => Φ (f y) := funext hg
  refine ciSup_le fun x => ?_
  rw [Real.norm_eq_abs]
  exact (hΦ _).trans (norm_le_uniformNorm_of hc hf.2 x)
private theorem spanClassNorm_I_smul_eq (ς : TupleFunctional) (G : PositiveSpan) :
    spanClassNorm ς (Complex.I • G) = spanClassNorm ς G := by
  have hform := ReflectionPositivity.TupleForm.isSesquilinear_reflectionForm ς
  unfold spanClassNorm
  rw [hform.smul_left, hform.smul_right]
  congr 2
  rw [← mul_assoc]
  simp
private theorem add_le_of_half_bounds {C v W W₁ W₂ c a b : ℝ} (hC : 0 ≤ C) (hv : 0 ≤ v) (hc : 0 ≤ c)
    (h₁ : W₁ ≤ W) (h₂ : W₂ ≤ W) (h0 : 0 ≤ W₁) (ha : a ≤ 1 / 2 * C * v * W₁ * c)
    (hb : b ≤ 1 / 2 * C * v * W₂ * c) :
    a + b ≤ C * v * W * c ∧ a ≤ C * v * W * c := by
  have hk : 0 ≤ 1 / 2 * C * v := by positivity
  have hup : ∀ W' : ℝ, W' ≤ W → 1 / 2 * C * v * W' * c ≤ 1 / 2 * (C * v * W * c) := by
    intro W' hW'
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW' hk) hc
    calc 1 / 2 * C * v * W' * c ≤ 1 / 2 * C * v * W * c := this
      _ = _ := by ring
  have hW0 : 0 ≤ W := h0.trans h₁
  have hX : 0 ≤ C * v * W * c := by positivity
  have ha' := ha.trans (hup _ h₁)
  have hb' := hb.trans (hup _ h₂)
  exact ⟨by linarith, by linarith⟩
private theorem pushSpan_translate_reflect_conjugation
    (rules : ReflectionsAndOneInsertion.FunctionAndSpanActionLaws) (u : ℝ) (W : FormalSpan) :
    pushSpan (translate (timeVec (-u))) (pushSpan timeReflection (conjugation W)) =
      pushSpan timeReflection (conjugation (pushSpan (translate (timeVec u)) W)) := by
  have hrI : IsEuclidIsometry ⇑(addPermR (timeVec (-u))) := isEuclidIsometry_translate _
  have huI : IsEuclidIsometry ⇑(addPermR (timeVec u)) := isEuclidIsometry_translate _
  have hperm : addPermR (timeVec (-u)) * reflPerm = reflPerm * addPermR (timeVec u) := by
    ext x i
    change (timeReflection x + timeVec (-u)) i = timeReflection (x + timeVec u) i
    fin_cases i <;> simp [timeReflection, timeVec, timeIdx]
    ring
  have e1 := pushSpan_perm_mul rules hrI isEuclidIsometry_reflPerm (conjugation W)
  have e2 := pushSpan_perm_mul rules isEuclidIsometry_reflPerm huI (conjugation W)
  have e3 := conjugation_pushSpan_perm rules huI W
  rw [hperm] at e1
  have e4 : pushSpan timeReflection (conjugation (pushSpan (translate (timeVec u)) W)) =
      pushSpan timeReflection (pushSpan (translate (timeVec u)) (conjugation W)) := congrArg _ e3
  rw [e4]
  exact e1.symm.trans e2
private theorem pushSpan_translate_add (rules : ReflectionsAndOneInsertion.FunctionAndSpanActionLaws)
    (a b : ℝ) (W : FormalSpan) :
    pushSpan (translate (timeVec a)) (pushSpan (translate (timeVec b)) W) =
      pushSpan (translate (timeVec (a + b))) W := by
  have haI : IsEuclidIsometry ⇑(addPermR (timeVec a)) := isEuclidIsometry_translate _
  have hbI : IsEuclidIsometry ⇑(addPermR (timeVec b)) := isEuclidIsometry_translate _
  have e1 := pushSpan_perm_mul rules haI hbI W
  have h : addPermR (timeVec a) * addPermR (timeVec b) = addPermR (timeVec (a + b)) := by
    ext x i
    change (x + timeVec b + timeVec a) i = (x + timeVec (a + b)) i
    rw [add_assoc, ← timeVec_add_eq, add_comm b a]
  rw [h] at e1
  exact e1.symm
private theorem euclidNormVec_sub_le_two_mul_of {x z c : AmbientSpace} {r : ℝ}
    (hx : euclidNormVec (x - c) ≤ r) (hz : euclidNormVec (z - c) ≤ r) :
    euclidNormVec (x - z) ≤ 2 * r := by
  have h1 := dist_triangle_right (WithLp.toLp 2 x : EuclidFour) (WithLp.toLp 2 z)
    (WithLp.toLp 2 c)
  rw [dist_toLp_eq_euclidNormVec, dist_toLp_eq_euclidNormVec, dist_toLp_eq_euclidNormVec] at h1
  linarith
private theorem fieldOperatorConst_nonneg {L M : ℝ} {N : BoundConstants} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hN : N.Admissible) (R : ℝ) : 0 ≤ fieldOperatorConst L M N R := by
  have h0 : 0 < N.insertionRadiusRatio := hN.insertionRadiusRatio_mem.1
  have h1 : 0 ≤ N.insertionConst := hN.insertionConst_nonneg
  have h4 : 0 ≤ pieceCount N.insertionRadiusRatio := by
    unfold pieceCount
    positivity
  unfold fieldOperatorConst
  positivity
private theorem norm_middle_translate_le (rules : ReflectionsAndOneInsertion.FunctionAndSpanActionLaws)
    {σ : FinTuple s → ℝ} (hσ : IsTupleFunctional σ)
    (hinvar : ∀ (y : Fin 4 → ℝ) (Ξ : FormalSpan),
      realSpanLift σ (pushSpan (translate y) Ξ) = realSpanLift σ Ξ)
    (hcontr : ∀ (u : ℝ), 0 ≤ u → ∀ F : PositiveSpan, ∃ G : PositiveSpan,
      G.1 = pushSpan (translate (u • ReflectionsAndOneInsertion.timeUnitVec)) F.1 ∧
        spanClassNorm (toTupleFunctional σ hσ) G ≤ spanClassNorm (toTupleFunctional σ hσ) F)
    {L : ℕ} {M : ℝ} {N : BoundConstants} (hM : 1 ≤ M) (hN : N.Admissible)
    (hone : SingleCellBound L M N (toTupleFunctional σ hσ))
    {e : ℤ} {l : ℝ} (hl : l = (L : ℝ) ^ e) (hlpos : 0 < l) (hl1 : l ≤ 1) {α : AmbientSpace}
    {g : RealValued} (hg : IsC1c g) (hs : tsupport g ⊆ closedBallR4 α (N.insertionRadiusRatio * l))
    {T : ℝ} (hT : 0 < T) (hu : 0 ≤ α 3 - l / 2) (hu' : 0 ≤ T - α 3 - l / 2)
    (hslab : tsupport g ⊆ slabOf T) (P' P : PositiveSpan) :
    ‖realSpanLift σ (formalMul (formalMul (reflectConj P')
        (basisVec (singleTuple g hg))) (pushSpan (translate (timeVec T)) P.1))‖ ≤
      N.insertionConst * l ^ (-N.insertionExponent) * sharpNormR4 M g *
        spanClassNorm (toTupleFunctional σ hσ) P' * spanClassNorm (toTupleFunctional σ hσ) P := by
  set u := α 3 - l / 2 with hudef
  set u' := T - α 3 - l / 2 with hu'def
  obtain ⟨G₁, hG₁, hc₁⟩ := hcontr u hu P'
  obtain ⟨G₂, hG₂, hc₂⟩ := hcontr u' hu' P
  rw [smul_timeUnitVec_eq] at hG₁ hG₂
  set r := addPermR (timeVec (-u)) with hr
  have hrI : IsEuclidIsometry ⇑r := isEuclidIsometry_translate _
  have huI : IsEuclidIsometry ⇑(addPermR (timeVec u)) := isEuclidIsometry_translate _
  set h : RealValued := fun x => g (x - timeVec (-(α 3))) with hh
  have hhm : IsC1c h := isC1c_shift hg _
  set y : Fin 3 → ℝ := ![α 0, α 1, α 2] with hy
  have hhs : tsupport h ⊆ closedBallR4 (timeZeroPoint y) (N.insertionRadiusRatio * l) := by
    intro x hx
    have hc : Continuous fun x : AmbientSpace => x - timeVec (-(α 3)) :=
      continuous_id.sub continuous_const
    have h₁ := hs (tsupport_comp_subset_preimage g hc hx)
    have h₂ : euclidNormVec (x - timeVec (-(α 3)) - α) ≤ N.insertionRadiusRatio * l := h₁
    have h₃ : x - timeVec (-(α 3)) - α = x - timeZeroPoint y := by
      funext i
      fin_cases i <;> simp [hy, timeVec, timeIdx]
    rw [h₃] at h₂
    exact h₂
  have hb := hone e l hl hl1 y h hhm hhs G₂ G₁
  have hsharp : sharpNormR4 M h = sharpNormR4 M g := by
    have hI : IsEuclidIsometry ⇑(addPermR (timeVec (-(α 3)))) := isEuclidIsometry_translate _
    exact ((rules _ _ hI hI).1 ℝ g (isLipschitzFor_of_isC1c hg) hg.2).2.2 M hM
  have hEm : basisVec (singleTuple g hg) ∈ spanIn (slabOf T) :=
    Submodule.subset_span ⟨⟨_, singleTuple_mem hg hslab⟩, rfl⟩
  have hd1 : FormalMulDefined (reflectConj P') (basisVec (singleTuple g hg)) :=
    formalMulDefined_of_mem disjoint_timeBelow_slabOf (reflectConj_mem_timeBelow P') hEm
  have hd2 : FormalMulDefined (formalMul (reflectConj P') (basisVec (singleTuple g hg)))
      (pushSpan (translate (timeVec T)) P.1) :=
    formalMulDefined_of_mem
      (Set.disjoint_union_left.2 ⟨disjoint_timeBelow_timeAbove_of hT, disjoint_slabOf_timeAbove⟩)
      (formalMul_mem disjoint_timeBelow_slabOf (reflectConj_mem_timeBelow P') hEm)
      (pushSpan_mem_timeAbove T P)
  obtain ⟨-, -, hmul2, -⟩ := (rules r r hrI hrI).2 _ _ hd2
  obtain ⟨-, -, hmul1, -⟩ := (rules r r hrI hrI).2 _ _ hd1
  have hperm₁ : r * reflPerm = reflPerm * addPermR (timeVec u) := by
    ext x i
    change (timeReflection x + timeVec (-u)) i = timeReflection (x + timeVec u) i
    fin_cases i <;> simp [timeReflection, timeVec, timeIdx]
    ring
  have hrefl : pushSpan r (reflectConj P') = reflectConj G₁ := by
    have e1 := pushSpan_perm_mul rules hrI isEuclidIsometry_reflPerm (conjugation P'.1)
    have e2 := pushSpan_perm_mul rules isEuclidIsometry_reflPerm huI (conjugation P'.1)
    have e3 := conjugation_pushSpan_perm rules huI P'.1
    rw [hperm₁] at e1
    have e4 : reflectConj G₁ = pushSpan timeReflection
        (pushSpan (translate (timeVec u)) (conjugation P'.1)) := by
      unfold reflectConj
      rw [hG₁]
      exact congrArg _ e3
    rw [e4]
    exact e1.symm.trans e2
  have hent : pushSpan r (basisVec (singleTuple g hg)) =
      basisVec (push (translate (timeVec (l / 2))) (singleTuple h hhm)) := by
    have e1 : pushSpan r (basisVec (singleTuple g hg)) = basisVec (push r (singleTuple g hg)) :=
      linearExtend_basisVec _ _
    rw [e1, coe_addPermR, push_translate_single, push_translate_single]
    congr 1
    apply Subtype.ext
    change [_] = [_]
    congr 1
    funext x
    change g (x - timeVec (-u)) = g (x - timeVec (l / 2) - timeVec (-(α 3)))
    congr 1
    rw [sub_sub, ← timeVec_add_eq]
    congr 2
    rw [hudef]
    ring
  have hshift : pushSpan r (pushSpan (translate (timeVec T)) P.1) =
      pushSpan (translate (timeVec l)) G₂.1 := by
    have hTI : IsEuclidIsometry ⇑(addPermR (timeVec T)) := isEuclidIsometry_translate _
    have hlI : IsEuclidIsometry ⇑(addPermR (timeVec l)) := isEuclidIsometry_translate _
    have hu'I : IsEuclidIsometry ⇑(addPermR (timeVec u')) := isEuclidIsometry_translate _
    have e1 := pushSpan_perm_mul rules hrI hTI P.1
    have e2 := pushSpan_perm_mul rules hlI hu'I P.1
    have hperm₂ : r * addPermR (timeVec T) = addPermR (timeVec l) * addPermR (timeVec u') := by
      ext x i
      change (x + timeVec T + timeVec (-u)) i = (x + timeVec u' + timeVec l) i
      rw [add_assoc, add_assoc, ← timeVec_add_eq, ← timeVec_add_eq]
      congr 3
      rw [hudef, hu'def]
      ring
    rw [hperm₂] at e1
    rw [hG₂]
    exact e1.symm.trans e2
  have hkey : pushSpan (translate (timeVec (-u)))
      (formalMul (formalMul (reflectConj P') (basisVec (singleTuple g hg)))
        (pushSpan (translate (timeVec T)) P.1)) =
      formalMul (formalMul (reflectConj G₁)
        (basisVec (push (translate (timeVec (l / 2))) (singleTuple h hhm))))
        (pushSpan (translate (timeVec l)) G₂.1) := by
    rw [← coe_addPermR]
    change pushSpan r _ = _
    rw [hmul2, hmul1, hrefl, hent, hshift]
  rw [← hinvar (timeVec (-u)), hkey]
  have hcell : 0 ≤ N.insertionConst * l ^ (-N.insertionExponent) :=
    mul_nonneg hN.insertionConst_nonneg (Real.rpow_nonneg hlpos.le _)
  have hs0 : 0 ≤ sharpNormR4 M g :=
    le_max_of_le_left (uniformNorm_nonneg_of g)
  have hb' : ‖realSpanLift σ (formalMul (formalMul (reflectConj G₁)
      (basisVec (push (translate (timeVec (l / 2))) (singleTuple h hhm))))
      (pushSpan (translate (timeVec l)) G₂.1))‖ ≤ _ := hb
  rw [hsharp] at hb'
  refine hb'.trans ?_
  have hcs : 0 ≤ N.insertionConst * l ^ (-N.insertionExponent) * sharpNormR4 M g :=
    mul_nonneg hcell hs0
  exact mul_le_mul (mul_le_mul_of_nonneg_left hc₁ hcs) hc₂ (Real.sqrt_nonneg _)
    (mul_nonneg hcs (Real.sqrt_nonneg _))
private theorem sharpNormR4_piece_le {f : RealValued} (hf : IsC1c f) {η l Lr M c : ℝ}
    (hη : 0 < η) (hl : 0 < l) (hc : 0 < c) (hle : η ≤ Lr * l) (hL : 13 ≤ Lr) (hM : 1 ≤ M)
    (hs : tsupport f ⊆ {x | η ≤ timeComponent x ∧ timeComponent x ≤ 3 * η}) {α : AmbientSpace}
    (hp : MeshPartition.PieceProperties (c * l / 2) α f) :
    sharpNormR4 M (MeshPartition.localizedPiece (c * l / 2) α f) ≤
      40 * (1 + 7 / c) * Lr * M * (uniformNorm f + supGrad f) := by
  obtain ⟨-, hsup, -, hlip, -⟩ := hp
  have hG := supGrad_nonneg f
  have hS := uniformNorm_nonneg_of f
  have hS' := uniformNorm_le_of_slab hf hη hs
  have hLf := lipConstR4_le_supGrad hf
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have h7 : 0 < 7 / c := by positivity
  have hterm : Real.pi / (c * l / 2) * uniformNorm f ≤ 7 / c * Lr * supGrad f := by
    have h1 : uniformNorm f ≤ Lr * l * supGrad f :=
      hS'.trans (mul_le_mul_of_nonneg_right hle hG)
    calc Real.pi / (c * l / 2) * uniformNorm f
        ≤ Real.pi / (c * l / 2) * (Lr * l * supGrad f) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * Real.pi / c * (Lr * supGrad f) := by
          field_simp
      _ ≤ 7 / c * (Lr * supGrad f) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact div_le_div_of_nonneg_right (by linarith) hc.le
      _ = 7 / c * Lr * supGrad f := by ring
  have hLip : lipConstR4 (MeshPartition.localizedPiece (c * l / 2) α f) ≤
      (1 + 7 / c) * Lr * supGrad f := by
    have h2 : supGrad f ≤ Lr * supGrad f := by nlinarith
    have h3 : (1 + 7 / c) * Lr * supGrad f =
        Lr * supGrad f + 7 / c * Lr * supGrad f := by ring
    rw [h3]
    linarith
  have hK1 : 1 ≤ 40 * (1 + 7 / c) * Lr * M := by
    have h4 : 1 ≤ 40 * (1 + 7 / c) := by linarith
    have h5 : 1 ≤ 40 * (1 + 7 / c) * Lr := by nlinarith
    nlinarith
  refine max_le ?_ ?_
  · refine hsup.trans ?_
    nlinarith
  · have h4 : 40 * M * lipConstR4 (MeshPartition.localizedPiece (c * l / 2) α f) ≤
        40 * M * ((1 + 7 / c) * Lr * supGrad f) :=
      mul_le_mul_of_nonneg_left hLip (by positivity)
    have h5 : 40 * M * ((1 + 7 / c) * Lr * supGrad f) ≤
        40 * (1 + 7 / c) * Lr * M * (uniformNorm f + supGrad f) := by
      have h6 : 0 ≤ 40 * (1 + 7 / c) * Lr * M * uniformNorm f := by positivity
      nlinarith
    exact h4.trans h5
private theorem prod_mesh_count_le {η l Lr R c : ℝ} (hη : 0 < η) (hl : 0 < l) (hl1 : l ≤ 1)
    (hc : 0 < c) (hle : η ≤ Lr * l) (hL : 13 ≤ Lr) (hR : 0 < R) :
    ∏ μ : Fin 4, ((![R, R, R, 2 * η] : Fin 4 → ℝ) μ / (c * l / 2) + 3) ≤
      (2 / c + 3) ^ 3 * (4 / c + 3) * Lr * max 1 R ^ 3 * (l⁻¹) ^ 3 := by
  set m := max 1 R with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hRm : R ≤ m := le_max_right _ _
  have hinv : 1 ≤ l⁻¹ := (one_le_inv₀ hl).2 hl1
  have h4c : 0 < 4 / c := by positivity
  have ha : R / (c * l / 2) + 3 ≤ (2 / c + 3) * m * l⁻¹ := by
    have h1 : R / (c * l / 2) = 2 / c * R * l⁻¹ := by
      field_simp
    rw [h1]
    have h2 : 2 / c * R * l⁻¹ ≤ 2 / c * m * l⁻¹ := by
      have := mul_le_mul_of_nonneg_right hRm (by positivity : 0 ≤ 2 / c * l⁻¹)
      nlinarith
    have h3 : 3 ≤ 3 * m * l⁻¹ := by nlinarith
    nlinarith
  have hb : 2 * η / (c * l / 2) + 3 ≤ (4 / c + 3) * Lr := by
    have h1 : 2 * η / (c * l / 2) = 4 / c * (η * l⁻¹) := by
      field_simp
      ring
    have h2 : η * l⁻¹ ≤ Lr := by
      rw [← div_eq_mul_inv, div_le_iff₀ hl]
      exact hle
    rw [h1]
    have h3 : 4 / c * (η * l⁻¹) ≤ 4 / c * Lr := mul_le_mul_of_nonneg_left h2 h4c.le
    nlinarith
  rw [Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val]
  calc (R / (c * l / 2) + 3) * (R / (c * l / 2) + 3) * (R / (c * l / 2) + 3) *
        (2 * η / (c * l / 2) + 3)
      ≤ ((2 / c + 3) * m * l⁻¹) * ((2 / c + 3) * m * l⁻¹) * ((2 / c + 3) * m * l⁻¹) *
          ((4 / c + 3) * Lr) := by gcongr
    _ = (2 / c + 3) ^ 3 * (4 / c + 3) * Lr * m ^ 3 * l⁻¹ ^ 3 := by ring
set_option maxHeartbeats 1600000 in
private theorem norm_middle_slab_le (rules : ReflectionsAndOneInsertion.FunctionAndSpanActionLaws)
    (hPart : MeshPartition.MeshPartitionStatement)
    {σ : FinTuple s → ℝ} (hσ : IsTupleFunctional σ)
    (hm : IsMultilin σ)
    (hinvar : ∀ (y : Fin 4 → ℝ) (Ξ : FormalSpan),
      realSpanLift σ (pushSpan (translate y) Ξ) = realSpanLift σ Ξ)
    (hcontr : ∀ (u : ℝ), 0 ≤ u → ∀ F : PositiveSpan, ∃ G : PositiveSpan,
      G.1 = pushSpan (translate (u • ReflectionsAndOneInsertion.timeUnitVec)) F.1 ∧
        spanClassNorm (toTupleFunctional σ hσ) G ≤ spanClassNorm (toTupleFunctional σ hσ) F)
    {L : ℕ} (hLs : Conventions.IsAdmissibleBlockingFactor L) {M : ℝ} {N : BoundConstants}
    (hM : 1 ≤ M) (hN : N.Admissible)
    (hone : SingleCellBound L M N (toTupleFunctional σ hσ))
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {R : ℝ} (hR : 0 < R) {f : RealValued}
    (hf : IsC1c f)
    (hs : tsupport f ⊆ {x | η ≤ timeComponent x ∧ timeComponent x ≤ 3 * η})
    (hd : HasDiameterLE (tsupport f) R) (P' P : PositiveSpan) :
    ‖realSpanLift σ (formalMul (formalMul (reflectConj P')
        (basisVec (singleTuple f hf))) (pushSpan (translate (timeVec (4 * η))) P.1))‖ ≤
      1 / 2 * fieldOperatorConst L M N R * η ^ (-fieldExponent N) *
        (uniformNorm f + supGrad f) *
        spanClassNorm (toTupleFunctional σ hσ) P' * spanClassNorm (toTupleFunctional σ hσ) P := by
  set Lr : ℝ := (L : ℝ) with hLr
  have hL13 : 13 ≤ Lr := by
    have := hLs.2
    rw [hLr]
    exact_mod_cast this
  have hL1 : 1 < Lr := by linarith
  have hLpos : 0 < Lr := by linarith
  obtain ⟨e, he1, he2⟩ := exists_mem_Ico_zpow hη0 hL1
  set l : ℝ := Lr ^ e with hl
  have hlpos : 0 < l := zpow_pos hLpos e
  have hle : η ≤ Lr * l := by
    have h1 : Lr ^ (e + 1) = l * Lr := zpow_add_one₀ hLpos.ne' e
    rw [h1] at he2
    linarith
  have hl1 : l ≤ 1 := he1.trans hη1
  set cf : ℝ := N.insertionRadiusRatio with hcdef
  have hcf0 : 0 < cf := hN.insertionRadiusRatio_mem.1
  have hcf4 : cf ≤ 1 / 4 := hN.insertionRadiusRatio_mem.2
  have hε : 0 < cf * l / 2 := by positivity
  obtain ⟨-, -, hcuts⟩ := hPart (cf * l / 2) hε
  obtain ⟨b, hbox⟩ := exists_boxFrom_cover hf hs hd
  have hlam : ∀ μ, 0 ≤ (![R, R, R, 2 * η] : Fin 4 → ℝ) μ := by
    intro μ
    fin_cases μ <;> simp <;> positivity
  obtain ⟨hfin, hcard, hsum, hfacts⟩ := hcuts f b _ (isLipschitzFor_of_isC1c hf) hlam hbox
  set T : Set (CosineSquaredBump.latticeOfSpacing (cf * l / 2)) :=
    {α | MeshPartition.localizedPiece (cf * l / 2) α f ≠ 0} with hT
  have himage : Subtype.val '' T =
      {α | α ∈ CosineSquaredBump.latticeOfSpacing (cf * l / 2) ∧
        MeshPartition.localizedPiece (cf * l / 2) α f ≠ 0} := by
    ext α
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.2, ha⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨⟨α, h₁⟩, h₂, rfl⟩
  have hTfin : T.Finite := by
    refine Set.Finite.of_finite_image ?_ Subtype.val_injective.injOn
    rw [himage]
    exact hfin
  classical
  set S := hTfin.toFinset with hS
  have hcoe : (S : Set _) = T := hTfin.coe_toFinset
  have hsum' : f = ∑ α ∈ S, MeshPartition.localizedPiece (cf * l / 2) α.1 f := by
    refine hsum.trans (finsum_eq_sum_of_support_subset _ ?_)
    rw [hcoe]
    intro α hα
    exact hα
  have hScard : (S.card : ℝ) ≤ (2 / cf + 3) ^ 3 * (4 / cf + 3) * Lr * max 1 R ^ 3 * (l⁻¹) ^ 3 := by
    have h1 : S.card = T.ncard := (Set.ncard_eq_toFinset_card T hTfin).symm
    have h2 : T.ncard = (Subtype.val '' T).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    rw [h1, h2, himage]
    exact hcard.trans (prod_mesh_count_le hη0 hlpos hl1 hcf0 hle hL13 hR)
  set A := reflectConj P' with hA
  set Bq := pushSpan (translate (timeVec (4 * η))) P.1 with hBq
  have hT4 : 0 < 4 * η := by positivity
  have hslabsub : {x : AmbientSpace | η ≤ timeComponent x ∧ timeComponent x ≤ 3 * η} ⊆
      slabOf (4 * η) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hpt : ∀ α : CosineSquaredBump.latticeOfSpacing (cf * l / 2),
      IsTestOn (slabOf (4 * η)) (MeshPartition.localizedPiece (cf * l / 2) α.1 f) := fun α =>
    ⟨(hfacts α.1 α.2).2.2.2.2 hf,
      (((hfacts α.1 α.2).1.trans Set.inter_subset_left).trans hs).trans hslabsub⟩
  obtain ⟨-, hsw⟩ := middle_finsum hm disjoint_timeBelow_slabOf (disjoint_timeBelow_timeAbove_of hT4)
    disjoint_slabOf_timeAbove (reflectConj_mem_timeBelow P') (pushSpan_mem_timeAbove (4 * η) P) S
    (fun α => MeshPartition.localizedPiece (cf * l / 2) α.1 f) (fun α _ => hpt α)
  have hLam : realSpanLift σ (formalMul (formalMul A
      (basisVec (singleTuple f hf))) Bq) =
      ∑ α ∈ S, middle σ A Bq (MeshPartition.localizedPiece (cf * l / 2) α.1 f) := by
    rw [← middle_eq σ A Bq hf, ← hsw]
    exact congrArg _ hsum'
  set W := uniformNorm f + supGrad f with hW
  have hW0 : 0 ≤ W := add_nonneg (uniformNorm_nonneg_of f) (supGrad_nonneg f)
  set c' := spanClassNorm (toTupleFunctional σ hσ) P' with hc'
  set c := spanClassNorm (toTupleFunctional σ hσ) P with hc
  have hc'0 : 0 ≤ c' := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hpb : ∀ α ∈ S, ‖middle σ A Bq (MeshPartition.localizedPiece (cf * l / 2) α.1 f)‖ ≤
      N.insertionConst * l ^ (-N.insertionExponent) * (40 * (1 + 7 / cf) * Lr * M * W) * c' * c := by
    intro α hα
    have hne : MeshPartition.localizedPiece (cf * l / 2) α.1 f ≠ 0 := by
      have : α ∈ T := by
        rw [← hcoe]
        exact hα
      exact this
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
    have hfa := hfacts α.1 α.2
    have hxs := hfa.1 (subset_tsupport _ hx)
    have hxslab := hs hxs.1
    have hx3 : η ≤ x 3 ∧ x 3 ≤ 3 * η := hxslab
    have hball : tsupport (MeshPartition.localizedPiece (cf * l / 2) α.1 f) ⊆
        closedBallR4 α.1 (N.insertionRadiusRatio * l) := by
      have h2 : 2 * (cf * l / 2) = N.insertionRadiusRatio * l := by
        rw [hcdef]
        ring
      have h3 := hfa.1.trans Set.inter_subset_right
      rwa [h2] at h3
    have hdist : |(x - α.1) 3| ≤ l / 4 := (abs_coord_le_euclidNormVec _ 3).trans (by
      have h3 : euclidNormVec (x - α.1) ≤ 2 * (cf * l / 2) := hxs.2
      have h4 : 2 * (cf * l / 2) ≤ l / 4 := by nlinarith
      exact h3.trans h4)
    have hd3 : (x - α.1) 3 = x 3 - α.1 3 := rfl
    rw [hd3, abs_le] at hdist
    have hu : 0 ≤ α.1 3 - l / 2 := by linarith [hdist.2, hx3.1, he1]
    have hu' : 0 ≤ 4 * η - α.1 3 - l / 2 := by linarith [hdist.1, hx3.2, he1]
    rw [middle_eq σ A Bq (hpt α).1]
    refine (norm_middle_translate_le rules hσ hinvar hcontr hM hN hone (e := e) hl hlpos hl1
      (hpt α).1 hball hT4 hu hu' (hpt α).2 P' P).trans ?_
    have hsh := sharpNormR4_piece_le hf hη0 hlpos hcf0 hle hL13 hM hs hfa
    have h0 : 0 ≤ N.insertionConst * l ^ (-N.insertionExponent) :=
      mul_nonneg hN.insertionConst_nonneg (Real.rpow_nonneg hlpos.le _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsh h0) hc'0) hc0
  rw [hLam]
  have hsumle : ‖∑ α ∈ S, middle σ A Bq (MeshPartition.localizedPiece (cf * l / 2) α.1 f)‖ ≤
      (S.card : ℝ) *
        (N.insertionConst * l ^ (-N.insertionExponent) * (40 * (1 + 7 / cf) * Lr * M * W) * c' * c) := by
    have h1 := norm_sum_le_of_le S hpb
    simpa [Finset.sum_const, nsmul_eq_mul] using h1
  refine hsumle.trans ?_
  set m := max 1 R with hmdef
  have hm0 : 0 ≤ m := le_trans zero_le_one (le_max_left _ _)
  have hM0 : 0 ≤ M := by linarith
  have hCI : 0 ≤ N.insertionConst := hN.insertionConst_nonneg
  set q := N.insertionExponent with hq
  have hq0 : 0 ≤ q := hN.insertionExponent_nonneg
  set Y := N.insertionConst * M * W * c' * c with hY
  have hY0 : 0 ≤ Y := by positivity
  have hinvle : l⁻¹ ≤ Lr * η⁻¹ := by
    rw [inv_le_comm₀ hlpos (by positivity), mul_inv, inv_inv]
    rw [inv_mul_le_iff₀ (by positivity)]
    exact (by linarith : η ≤ Lr * l)
  have hpow : (l⁻¹) ^ 3 * l ^ (-q) ≤ Lr ^ (3 + q) * η ^ (-(3 + q)) := by
    have e1 : (l⁻¹) ^ 3 * l ^ (-q) = (l⁻¹) ^ ((3 : ℝ) + q) := by
      rw [Real.rpow_add (inv_pos.2 hlpos), Real.inv_rpow hlpos.le q, Real.rpow_neg hlpos.le q]
      norm_num
    have e2 : (Lr * η⁻¹) ^ ((3 : ℝ) + q) = Lr ^ (3 + q) * η ^ (-(3 + q)) := by
      rw [Real.mul_rpow hLpos.le (inv_nonneg.2 hη0.le), Real.inv_rpow hη0.le,
        Real.rpow_neg hη0.le]
    rw [e1, ← e2]
    exact Real.rpow_le_rpow (inv_nonneg.2 hlpos.le) hinvle (by linarith)
  have hcalc : (S.card : ℝ) *
      (N.insertionConst * l ^ (-q) * (40 * (1 + 7 / cf) * Lr * M * W) * c' * c) ≤
      ((2 / cf + 3) ^ 3 * (4 / cf + 3) * Lr * m ^ 3 * (l⁻¹) ^ 3) *
        (40 * (1 + 7 / cf) * Lr * l ^ (-q) * Y) := by
    have h1 : N.insertionConst * l ^ (-q) * (40 * (1 + 7 / cf) * Lr * M * W) * c' * c =
        40 * (1 + 7 / cf) * Lr * l ^ (-q) * Y := by
      rw [hY]
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right hScard (by positivity)
  refine hcalc.trans ?_
  have hfinal : ((2 / cf + 3) ^ 3 * (4 / cf + 3) * Lr * m ^ 3 * (l⁻¹) ^ 3) *
      (40 * (1 + 7 / cf) * Lr * l ^ (-q) * Y) =
      (pieceCount cf * Lr ^ 2 * m ^ 3 * Y) * ((l⁻¹) ^ 3 * l ^ (-q)) := by
    unfold pieceCount
    ring
  rw [hfinal]
  have hp0 : 0 ≤ pieceCount cf := by
    unfold pieceCount
    positivity
  have h2 := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ pieceCount cf * Lr ^ 2 * m ^ 3 * Y)
  refine h2.trans (le_of_eq ?_)
  have e5 : Lr ^ (5 + q) = Lr ^ 2 * Lr ^ (3 + q) := by
    have e6 : (5 : ℝ) + q = 2 + (3 + q) := by ring
    rw [e6, Real.rpow_add hLpos]
    norm_num
  simp only [fieldOperatorConst, fieldExponent, hY]
  rw [← hq, ← hmdef, e5]
  ring
private theorem exists_span_real_fieldBound
    (rules : ReflectionsAndOneInsertion.FunctionAndSpanActionLaws)
    (hPart : MeshPartition.MeshPartitionStatement)
    {σ : FinTuple s → ℝ} (hσ : IsTupleFunctional σ)
    (hm : IsMultilin σ)
    (hinvar : ∀ (y : Fin 4 → ℝ) (Ξ : FormalSpan),
      realSpanLift σ (pushSpan (translate y) Ξ) = realSpanLift σ Ξ)
    (hcontr : ∀ (u : ℝ), 0 ≤ u → ∀ F : PositiveSpan, ∃ G : PositiveSpan,
      G.1 = pushSpan (translate (u • ReflectionsAndOneInsertion.timeUnitVec)) F.1 ∧
        spanClassNorm (toTupleFunctional σ hσ) G ≤ spanClassNorm (toTupleFunctional σ hσ) F)
    (hpsd : HilbertSpaceBasics.IsPosSemidef
      (ReflectionPositivity.TupleForm.reflectionForm (toTupleFunctional σ hσ)))
    {L : ℕ} (hLs : Conventions.IsAdmissibleBlockingFactor L) {M : ℝ} {N : BoundConstants}
    (hM : 1 ≤ M) (hN : N.Admissible)
    (hone : SingleCellBound L M N (toTupleFunctional σ hσ))
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {R : ℝ} (hR : 0 < R) {f : RealValued}
    (hf : IsC1c f)
    (hs : tsupport f ⊆ {x | η ≤ timeComponent x ∧ timeComponent x ≤ 3 * η})
    (hd : HasDiameterLE (tsupport f) R) (P : PositiveSpan) :
    ∃ G : PositiveSpan,
      G.1 = formalMul (basisVec (singleTuple f hf))
        (pushSpan (translate (timeVec (4 * η))) P.1) ∧
      spanClassNorm (toTupleFunctional σ hσ) G ≤
        1 / 2 * fieldOperatorConst L M N R * η ^ (-fieldExponent N) *
          (uniformNorm f + supGrad f) * spanClassNorm (toTupleFunctional σ hσ) P := by
  have hT4 : 0 < 4 * η := by positivity
  have hslabsub : {x : AmbientSpace | η ≤ timeComponent x ∧ timeComponent x ≤ 3 * η} ⊆
      slabOf (4 * η) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hEm : basisVec (singleTuple f hf) ∈ spanIn (slabOf (4 * η)) :=
    Submodule.subset_span ⟨⟨_, singleTuple_mem hf (hs.trans hslabsub)⟩, rfl⟩
  have hTm := pushSpan_mem_timeAbove (4 * η) P
  have hGm : formalMul (basisVec (singleTuple f hf))
      (pushSpan (translate (timeVec (4 * η))) P.1) ∈ spanIn upperHalfSpace := by
    refine spanIn_mono_of ?_ (formalMul_mem disjoint_slabOf_timeAbove hEm hTm)
    intro x hx
    rcases hx with hx | hx
    · exact hx.1
    · have h₁ : 4 * η < timeComponent x := hx
      change timeComponent x > 0
      linarith
  refine ⟨⟨_, hGm⟩, rfl, ?_⟩
  set G : PositiveSpan := ⟨_, hGm⟩ with hG
  have hform : ReflectionPositivity.TupleForm.reflectionForm (toTupleFunctional σ hσ) G G =
      realSpanLift σ (formalMul (formalMul (reflectConj G)
        (basisVec (singleTuple f hf))) (pushSpan (translate (timeVec (4 * η))) P.1)) := by
    rw [formalMul_formalMul disjoint_timeBelow_slabOf (disjoint_timeBelow_timeAbove_of hT4)
      disjoint_slabOf_timeAbove (reflectConj_mem_timeBelow G) hEm hTm]
    rfl
  have hb := norm_middle_slab_le rules hPart hσ hm hinvar hcontr hLs hM hN hone hη0 hη1 hR hf hs hd
    G P
  rw [← hform] at hb
  have hsq := (spanClassNorm_sq_le_norm hpsd G).trans hb
  set K := 1 / 2 * fieldOperatorConst L M N R * η ^ (-fieldExponent N) *
    (uniformNorm f + supGrad f) with hK
  have hc0 : 0 ≤ spanClassNorm (toTupleFunctional σ hσ) G := Real.sqrt_nonneg _
  have hcP : 0 ≤ spanClassNorm (toTupleFunctional σ hσ) P := Real.sqrt_nonneg _
  rcases hc0.eq_or_lt with h0 | hpos
  · rw [← h0]
    have hK0 : 0 ≤ K := by
      have hW : 0 ≤ uniformNorm f + supGrad f :=
        add_nonneg (uniformNorm_nonneg_of f) (supGrad_nonneg f)
      have hF : 0 ≤ fieldOperatorConst L M N R :=
        fieldOperatorConst_nonneg (Nat.cast_nonneg L) (by linarith) hN R
      rw [hK]
      positivity
    exact mul_nonneg hK0 hcP
  · have h1 : spanClassNorm (toTupleFunctional σ hσ) G * spanClassNorm (toTupleFunctional σ hσ) G ≤
        (K * spanClassNorm (toTupleFunctional σ hσ) P) * spanClassNorm (toTupleFunctional σ hσ) G := by
      have : spanClassNorm (toTupleFunctional σ hσ) G ^ 2 = spanClassNorm (toTupleFunctional σ hσ) G *
          spanClassNorm (toTupleFunctional σ hσ) G := sq _
      rw [← this]
      linarith
    exact le_of_mul_le_mul_right h1 hpos
private theorem fieldOperatorBound_of_single
    (rules : ReflectionsAndOneInsertion.FunctionAndSpanActionLaws)
    (hPart : MeshPartition.MeshPartitionStatement)
    {σ : FinTuple s → ℝ} (hσ : IsTupleFunctional σ)
    (hm : IsMultilin σ)
    (hinvar : ∀ (y : Fin 4 → ℝ) (Ξ : FormalSpan),
      realSpanLift σ (pushSpan (translate y) Ξ) = realSpanLift σ Ξ)
    (hcontr : ∀ (u : ℝ), 0 ≤ u → ∀ F : PositiveSpan, ∃ G : PositiveSpan,
      G.1 = pushSpan (translate (u • ReflectionsAndOneInsertion.timeUnitVec)) F.1 ∧
        spanClassNorm (toTupleFunctional σ hσ) G ≤ spanClassNorm (toTupleFunctional σ hσ) F)
    (hpsd : HilbertSpaceBasics.IsPosSemidef
      (ReflectionPositivity.TupleForm.reflectionForm (toTupleFunctional σ hσ)))
    (htri : ∀ F F' : PositiveSpan, spanClassNorm (toTupleFunctional σ hσ) (F + F') ≤
      spanClassNorm (toTupleFunctional σ hσ) F + spanClassNorm (toTupleFunctional σ hσ) F')
    {L : ℕ} (hLs : Conventions.IsAdmissibleBlockingFactor L) {M : ℝ} {N : BoundConstants}
    (hM : 1 ≤ M) (hN : N.Admissible)
    (hone : SingleCellBound L M N (toTupleFunctional σ hσ)) :
    FieldOperatorBound L M N (toTupleFunctional σ hσ) := by
  intro η hη0 hη1 R hR f hf hs hd P
  have hf' := ComplexTupleComponents.rePart_isC1c hf
  have hf'' := ComplexTupleComponents.imPart_isC1c hf
  have hsub' := ComplexTupleComponents.tsupport_rePart_subset f
  have hsub'' := ComplexTupleComponents.tsupport_imPart_subset f
  obtain ⟨G₁, hG₁, hb₁⟩ := exists_span_real_fieldBound rules hPart hσ hm hinvar hcontr hpsd hLs hM hN
    hone hη0 hη1 hR hf' (hsub'.trans hs) (fun x hx y hy => hd x (hsub' hx) y (hsub' hy)) P
  obtain ⟨G₂, hG₂, hb₂⟩ := exists_span_real_fieldBound rules hPart hσ hm hinvar hcontr hpsd hLs hM hN
    hone hη0 hη1 hR hf'' (hsub''.trans hs) (fun x hx y hy => hd x (hsub'' hx) y (hsub'' hy)) P
  have hreΦ : ∀ z : ℂ, |Complex.reCLM z| ≤ ‖z‖ := fun z => Complex.abs_re_le_norm z
  have himΦ : ∀ z : ℂ, |Complex.imCLM z| ≤ ‖z‖ := fun z => Complex.abs_im_le_norm z
  have hre : ∀ y, ComplexTestFunctions.rePart f y = Complex.reCLM (f y) := fun y => rfl
  have him : ∀ y, ComplexTestFunctions.imPart f y = Complex.imCLM (f y) := fun y => rfl
  have hW₁ : uniformNorm (ComplexTestFunctions.rePart f) +
      supGrad (ComplexTestFunctions.rePart f) ≤
      uniformNorm f + ⨆ x, gradNorm f x :=
    add_le_add (uniformNorm_comp_clm_le hf Complex.reCLM hreΦ hre)
      (supGrad_comp_clm_le hf Complex.reCLM hreΦ hre)
  have hW₂ : uniformNorm (ComplexTestFunctions.imPart f) +
      supGrad (ComplexTestFunctions.imPart f) ≤
      uniformNorm f + ⨆ x, gradNorm f x :=
    add_le_add (uniformNorm_comp_clm_le hf Complex.imCLM himΦ him)
      (supGrad_comp_clm_le hf Complex.imCLM himΦ him)
  have hC0 : 0 ≤ fieldOperatorConst L M N R :=
    fieldOperatorConst_nonneg (Nat.cast_nonneg L) (by linarith) hN R
  have hc0 : 0 ≤ spanClassNorm (toTupleFunctional σ hσ) P := Real.sqrt_nonneg _
  have hinv0 : 0 ≤ η ^ (-fieldExponent N) := Real.rpow_nonneg hη0.le _
  have hw0 := add_nonneg (uniformNorm_nonneg_of (ComplexTestFunctions.rePart f))
    (supGrad_nonneg (ComplexTestFunctions.rePart f))
  obtain ⟨hadd, hone'⟩ := add_le_of_half_bounds hC0 hinv0 hc0 hW₁ hW₂ hw0 hb₁ hb₂
  by_cases h0 : ComplexTestFunctions.imPart f = 0
  · refine ⟨G₁, ?_, hone'⟩
    rw [hG₁]
    unfold ComplexTupleComponents.singleSpan
    rw [if_pos h0]
  · refine ⟨G₁ + Complex.I • G₂, ?_, ?_⟩
    · unfold ComplexTupleComponents.singleSpan
      rw [if_neg h0]
      simp only [Submodule.coe_add, Submodule.coe_smul, hG₁, hG₂, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply]
    · refine (htri _ _).trans ?_
      rw [spanClassNorm_I_smul_eq]
      exact hadd
private theorem slab_bound_arith {C M η W S c₁ c₂ p₁ p₂ p : ℝ} (hC : 0 ≤ C) (hM : 0 < M) (hη : 0 < η)
    (hW0 : 0 ≤ W) (hW : W ≤ (1 + 1 / (40 * M)) * S) (hc₁0 : 0 ≤ c₁) (hc₂0 : 0 ≤ c₂) (h₁ : c₁ ≤ p₁)
    (h₂ : c₂ ≤ p₂) :
    1 / 2 * C * (η / 16) ^ (-p) * W * c₁ * c₂ ≤
      (16 : ℝ) ^ p * (1 + 1 / (40 * M)) * C * η ^ (-p) * S * p₁ * p₂ := by
  have hv : (η / 16) ^ (-p) = (16 : ℝ) ^ p * η ^ (-p) := by
    rw [Real.div_rpow hη.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16) p,
      div_inv_eq_mul]
    ring
  rw [hv]
  have hS0 : 0 ≤ (1 + 1 / (40 * M)) * S := hW0.trans hW
  have hp₁ : 0 ≤ p₁ := hc₁0.trans h₁
  calc 1 / 2 * C * ((16 : ℝ) ^ p * η ^ (-p)) * W * c₁ * c₂
      = 1 / 2 * ((16 : ℝ) ^ p * C * η ^ (-p) * W * c₁ * c₂) := by ring
    _ ≤ (16 : ℝ) ^ p * C * η ^ (-p) * W * c₁ * c₂ := by
        have : 0 ≤ (16 : ℝ) ^ p * C * η ^ (-p) * W * c₁ * c₂ := by positivity
        linarith
    _ ≤ (16 : ℝ) ^ p * C * η ^ (-p) * ((1 + 1 / (40 * M)) * S) * p₁ * p₂ := by gcongr
    _ = _ := by ring
private theorem freeSlabBound_of_single
    (rules : ReflectionsAndOneInsertion.FunctionAndSpanActionLaws)
    (hPart : MeshPartition.MeshPartitionStatement)
    {σ : FinTuple s → ℝ} (hσ : IsTupleFunctional σ)
    (hm : IsMultilin σ)
    (hinvar : ∀ (y : Fin 4 → ℝ) (Ξ : FormalSpan),
      realSpanLift σ (pushSpan (translate y) Ξ) = realSpanLift σ Ξ)
    (hcontr : ∀ (u : ℝ), 0 ≤ u → ∀ F : PositiveSpan, ∃ G : PositiveSpan,
      G.1 = pushSpan (translate (u • ReflectionsAndOneInsertion.timeUnitVec)) F.1 ∧
        spanClassNorm (toTupleFunctional σ hσ) G ≤ spanClassNorm (toTupleFunctional σ hσ) F)
    {L : ℕ} (hLs : Conventions.IsAdmissibleBlockingFactor L) {M : ℝ} {N : BoundConstants}
    (hM : 1 ≤ M) (hN : N.Admissible)
    (hone : SingleCellBound L M N (toTupleFunctional σ hσ)) :
    FreeSlabBound L M N (toTupleFunctional σ hσ) := by
  intro η hη hη1 y hy k hk hsupp P Q
  have hηr : ballRadiusRatio * η = η / 16 := by
    simp only [ballRadiusRatio]
    ring
  rw [hηr] at hsupp
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, u₀ = η / 8 - y 3 := ⟨_, rfl⟩
  have hy3 : |y 3| ≤ η / 8 := hy
  rw [abs_le] at hy3
  have hu₁ : 0 ≤ η / 4 - u₀ := by linarith [hy3.1]
  have hu₂ : 0 ≤ η / 4 + u₀ - 4 * (η / 16) := by linarith [hy3.2]
  obtain ⟨G₁, hG₁, hc₁⟩ := hcontr _ hu₁ (SlabInsertion.shiftDown hη P)
  obtain ⟨G₂, hG₂, hc₂⟩ := hcontr _ hu₂ (SlabInsertion.shiftDown hη Q)
  rw [smul_timeUnitVec_eq] at hG₁ hG₂
  have hGP : G₁.1 = pushSpan (translate (timeVec (-u₀))) P.1 := by
    rw [hG₁]
    refine (pushSpan_translate_add rules _ _ _).trans ?_
    congr 3
    ring
  have hGQ : pushSpan (translate (timeVec (4 * (η / 16)))) G₂.1 =
      pushSpan (translate (timeVec u₀)) Q.1 := by
    rw [hG₂]
    refine (pushSpan_translate_add rules _ _ _).trans ?_
    have := pushSpan_translate_add rules (4 * (η / 16) + (η / 4 + u₀ - 4 * (η / 16))) (-(η / 4)) Q.1
    have h2 : pushSpan (translate (timeVec (4 * (η / 16)))) (pushSpan
        (translate (timeVec (η / 4 + u₀ - 4 * (η / 16)))) (SlabInsertion.shiftDown hη Q).1) =
        pushSpan (translate (timeVec u₀)) Q.1 := by
      rw [pushSpan_translate_add rules]
      change pushSpan (translate (timeVec (4 * (η / 16) + (η / 4 + u₀ - 4 * (η / 16)))))
        (pushSpan (translate (timeVec (-(η / 4)))) Q.1) = _
      rw [this]
      congr 3
      ring
    rw [← pushSpan_translate_add rules]
    exact h2
  have hfree : tsupport k ⊆ SlabInsertion.centralSlab η := by
    intro x hx
    have h₁ : euclidNormVec (x - y) ≤ η / 16 := hsupp hx
    have h₂ := (abs_coord_le_euclidNormVec _ 3).trans h₁
    have h₃ : (x - y) 3 = x 3 - y 3 := rfl
    rw [h₃, abs_le] at h₂
    change |x 3| < η / 4
    rw [abs_lt]
    constructor <;> linarith [h₂.1, h₂.2, hy3.1, hy3.2]
  obtain ⟨hd1, hd2⟩ := SlabInsertion.formalMulDefined_insertion hη P Q hk hfree
  have hrI : IsEuclidIsometry ⇑(addPermR (timeVec u₀)) := isEuclidIsometry_translate _
  obtain ⟨-, -, hmul2, -⟩ := (rules _ _ hrI hrI).2 _ _ hd2
  obtain ⟨-, -, hmul1, -⟩ := (rules _ _ hrI hrI).2 _ _ hd1
  rw [coe_addPermR] at hmul1 hmul2
  have hf := isC1c_shift hk (timeVec u₀)
  have hent : pushSpan (translate (timeVec u₀)) (basisVec (singleTuple k hk)) =
      basisVec (singleTuple _ hf) :=
    (linearExtend_basisVec _ _).trans (by rw [push_translate_single])
  have hrefl : pushSpan (translate (timeVec u₀)) (SlabInsertion.reflectConj P) =
      reflectConj G₁ := by
    have h1 := pushSpan_translate_reflect_conjugation rules (-u₀) P.1
    rw [neg_neg] at h1
    unfold reflectConj
    rw [hGP]
    exact h1
  have hkey : pushSpan (translate (timeVec u₀))
      (formalMul (formalMul (SlabInsertion.reflectConj P)
        (basisVec (singleTuple k hk))) Q.1) =
      formalMul (formalMul (reflectConj G₁) (basisVec (singleTuple _ hf)))
        (pushSpan (translate (timeVec (4 * (η / 16)))) G₂.1) := by
    rw [hmul2, hmul1, hent, hrefl, hGQ]
  have hη' : 0 < η / 16 := by positivity
  have hη'1 : η / 16 ≤ 1 := by linarith
  have hcent : ∀ x ∈ tsupport (fun x => k (x - timeVec u₀)),
      euclidNormVec (x - (y + timeVec u₀)) ≤ η / 16 := by
    intro x hx
    have hc : Continuous fun x : AmbientSpace => x - timeVec u₀ := continuous_id.sub continuous_const
    have h₁ := hsupp (tsupport_comp_subset_preimage k hc hx)
    have h₂ : euclidNormVec (x - timeVec u₀ - y) ≤ η / 16 := h₁
    have h₃ : x - (y + timeVec u₀) = x - timeVec u₀ - y := by abel
    rw [h₃]
    exact h₂
  have hs : tsupport (fun x => k (x - timeVec u₀)) ⊆
      {x | η / 16 ≤ timeComponent x ∧ timeComponent x ≤ 3 * (η / 16)} := by
    intro x hx
    have h₂ := (abs_coord_le_euclidNormVec _ 3).trans (hcent x hx)
    have h₃ : (x - (y + timeVec u₀)) 3 = x 3 - (y 3 + u₀) := by
      simp [timeVec, timeIdx]
    rw [h₃, abs_le, hu₀] at h₂
    change η / 16 ≤ x 3 ∧ x 3 ≤ 3 * (η / 16)
    constructor <;> linarith [h₂.1, h₂.2]
  have hd : HasDiameterLE (tsupport (fun x => k (x - timeVec u₀))) 1 := by
    intro x hx z hz
    exact (euclidNormVec_sub_le_two_mul_of (hcent x hx) (hcent z hz)).trans (by linarith)
  have hb := norm_middle_slab_le rules hPart hσ hm hinvar hcontr hLs hM hN hone hη' hη'1 one_pos hf
    hs hd G₁ G₂
  rw [← hkey, hinvar] at hb
  have hins : insertionForm (toTupleFunctional σ hσ) P k hk Q = realSpanLift σ
      (formalMul (formalMul (SlabInsertion.reflectConj P)
        (basisVec (singleTuple k hk))) Q.1) := rfl
  rw [hins]
  have hfl := isLipschitzFor_of_isC1c hf
  have hsharp : sharpNormR4 M (fun x => k (x - timeVec u₀)) = sharpNormR4 M k := by
    have hI : IsEuclidIsometry ⇑(addPermR (timeVec u₀)) := isEuclidIsometry_translate _
    exact ((rules _ _ hI hI).1 ℝ k (isLipschitzFor_of_isC1c hk) hk.2).2.2 M hM
  have hM0 : 0 < M := by linarith
  have hW : uniformNorm (fun x => k (x - timeVec u₀)) + supGrad (fun x => k (x - timeVec u₀)) ≤
      (1 + 1 / (40 * M)) * sharpNormR4 M k := by
    rw [← hsharp]
    have h1 : uniformNorm (fun x => k (x - timeVec u₀)) ≤
        sharpNormR4 M (fun x => k (x - timeVec u₀)) := le_max_left _ _
    have h2 : 40 * M * lipConstR4 (fun x => k (x - timeVec u₀)) ≤
        sharpNormR4 M (fun x => k (x - timeVec u₀)) := le_max_right _ _
    have h3 := supGrad_le_lipConstR4 hf
    have h4 : supGrad (fun x => k (x - timeVec u₀)) ≤
        1 / (40 * M) * sharpNormR4 M (fun x => k (x - timeVec u₀)) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  refine hb.trans (slab_bound_arith (fieldOperatorConst_nonneg (Nat.cast_nonneg L) hM0.le hN 1) hM0
    hη (add_nonneg (uniformNorm_nonneg_of _) (supGrad_nonneg _)) hW (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) hc₁ hc₂)
end SingleCellToFieldAndSlab
open SingleCellToFieldAndSlab in
theorem fieldOperatorAndFreeSlabFromSingleCell_proof
    (hmaps : ReflectionsAndOneInsertion.ReflectionsObservablesCells.Statement)
    (hPart : MeshPartition.MeshPartitionStatement) :
    FieldOperatorAndFreeSlabFromSingleCell := by
  intro s K V ρ ν σ hσ L N hLs hN hCl hone
  have rules := (hmaps ⟨s, 1, one_pos⟩).2.2.1
  obtain ⟨hσ', hpsd, -, -, htri, hcontr⟩ := hCl.reflection_positive
  exact ⟨fieldOperatorBound_of_single rules hPart hσ hCl.multilin hCl.translate_invariant hcontr hpsd
      htri hLs V.one_le_M hN hone,
    freeSlabBound_of_single rules hPart hσ hCl.multilin hCl.translate_invariant hcontr hLs V.one_le_M
      hN hone⟩
end SystemsWithFiveBounds
end YangMills.Construction
end
