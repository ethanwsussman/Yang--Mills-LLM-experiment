import YangMills.Construction.EuclideanFunctionals.ReconstructionIsUniqueUpToUnitary
import YangMills.Construction.EuclideanFunctionals.SupportsIsometriesAndConcatenationProof
import YangMills.Construction.EuclideanFunctionals.TwoDefinitionsOfASymmetricEuclideanFunctional
import YangMills.Construction.EuclideanFunctionals.ValuesOfALinearFunctionOnTensors
import YangMills.Construction.LimitTheorem.EuclideanFunctionalOfABoundedApproximation
import YangMills.Construction.ReflectionPositivity.ComplementsToTheReconstructionProof
import YangMills.Construction.SpectralTheory.UnitaryGroupSemigroupCorrespondence
import Mathlib
set_option autoImplicit false
section
noncomputable section
namespace YangMills.Construction.FirstPassageSeqs.BoundedApprox
open EuclideanFunctionals
def toSepTuple (X : sepAll) : SeparatedTuples.SepTuple :=
  ⟨X.1, (R4TupleForms.isDisjointlySupported_iff_mem_separatedAll defaultMirrorData X.1).2 X.2⟩
def toFormalSpan : FreeSep →ₗ[ℂ] SeparatedTuples.FormalSpan :=
  liftLin fun X => SeparatedTuples.basisVec (toSepTuple X)
theorem toFormalSpan_toFree (X : sepAll) :
    toFormalSpan (toFree X.1) = SeparatedTuples.basisVec (toSepTuple X) :=
  liftLin_toFree _ X
theorem toFormalSpan_single (X : sepAll) :
    toFormalSpan (Finsupp.single X 1) = SeparatedTuples.basisVec (toSepTuple X) := by
  rw [← toFree_of_mem X.2]
  exact toFormalSpan_toFree X
theorem freeSep_linearMap_ext {V : Type*} [AddCommMonoid V] [Module ℂ V] {φ ψ : FreeSep →ₗ[ℂ] V}
    (h : ∀ X : sepAll, φ (toFree X.1) = ψ (toFree X.1)) : φ = ψ := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionProofs.linearMap_ext_sep <;> assumption
theorem toFormalSpan_freeConj (F : FreeSep) :
    toFormalSpan (freeConj F) = SeparatedTuples.conjugation (toFormalSpan F) := by
  induction F using Finsupp.induction_linear with
  | zero => simp [freeConj]
  | add F G hF hG =>
    have : freeConj (F + G) = freeConj F + freeConj G := by
      ext X
      simp [freeConj]
    rw [this, map_add, hF, hG, map_add, map_add]
  | single X z =>
    have h1 : freeConj (Finsupp.single X z) = (starRingEnd ℂ z) • Finsupp.single X (1 : ℂ) := by
      ext Y
      by_cases h : X = Y <;> simp [freeConj, h]
    have h2 : (Finsupp.single X z : FreeSep) = z • Finsupp.single X (1 : ℂ) := by
      simp
    rw [h1, h2, map_smul, map_smul, toFormalSpan_single, map_smulₛₗ,
      SeparatedTuples.conjugation_basisVec]
theorem spanExtension_toFormalSpan (τ : SeparatedTuples.TupleFunctional) (S : ConnFamily)
    (hτ : τ.toFun = onSepTuples (centeredFn S)) (F : FreeSep) :
    τ.spanExtension (toFormalSpan F) = centeredFnFree S F := by
  have : τ.spanExtension ∘ₗ toFormalSpan = centeredFnFree S := by
    refine freeSep_linearMap_ext fun X => ?_
    rw [LinearMap.comp_apply, toFormalSpan_toFree, SeparatedTuples.TupleFunctional.spanExtension,
      SeparatedTuples.linearExtend_basisVec, centeredFnFree, liftReal,
      liftLin_toFree]
    rw [hτ]
    rfl
  exact LinearMap.congr_fun this F
theorem toSepTuple_mem_supportedIn {O : Set R4} {X : sepAll} (hX : X.1 ∈ sepIn O) :
    toSepTuple X ∈ SeparatedTuples.supportedIn O :=
  (R4TupleForms.mem_supportedIn_iff_mem_separatedWithin defaultMirrorData O (toSepTuple X)).2 hX
theorem toFormalSpan_mem_spanIn {O : Set R4} {F : FreeSep}
    (hF : F ∈ finCombIn O) :
    toFormalSpan F ∈ SeparatedTuples.spanIn O := by
  rw [finCombIn_eq_freeSpanIn] at hF
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨X, hX, rfl⟩ := hG
    have := toFormalSpan_toFree ⟨X, hX.1⟩
    rw [show toFormalSpan (toFree X) = _ from this]
    exact Submodule.subset_span ⟨⟨_, toSepTuple_mem_supportedIn (X := ⟨X, hX.1⟩) hX⟩, rfl⟩
  | zero => simp
  | add G H _ _ hG hH =>
    rw [map_add]
    exact Submodule.add_mem _ hG hH
  | smul z G _ hG =>
    rw [map_smul]
    exact Submodule.smul_mem _ z hG
theorem actList_mem_sepAll (hT : TupleRules.TupleSpanActionRules) (r : EuclidMotion) {X : FnList}
    (hX : X ∈ sepAll) : r.actList X ∈ sepAll := by
  obtain ⟨-, hI, -⟩ := hT
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hX
  have hU : X ∈ sepNIn n Set.univ :=
    ⟨hn, hX, fun f _ => Set.subset_univ _⟩
  exact (((hI r Set.univ isOpen_univ).2.1 n).1.1 hU).2.1
theorem invMap_coe (r : EuclidMotion) :
    SeparatedTuples.invMap (⇑r) = ⇑(r⁻¹) := by
  funext x
  have hinj : Function.Injective (⇑r : R4 → R4) := fun a b h =>
    (r.inv_apply_apply a).symm.trans ((congrArg (⇑(r⁻¹)) h).trans (r.inv_apply_apply b))
  calc SeparatedTuples.invMap (⇑r) x
      = SeparatedTuples.invMap (⇑r) (r (r⁻¹ x)) := by rw [EuclidMotion.apply_inv_apply]
    _ = r⁻¹ x := Function.leftInverse_invFun hinj _
theorem push_toSepTuple (hT : TupleRules.TupleSpanActionRules) (r : EuclidMotion) (X : sepAll) :
    SeparatedTuples.push (⇑r) (toSepTuple X) = toSepTuple ⟨r.actList X.1, actList_mem_sepAll hT r X.2⟩ := by
  have hl : SeparatedTuples.pushList (⇑r) X.1 = r.actList X.1 := by
    simp only [SeparatedTuples.pushList, invMap_coe, EuclidMotion.actList]
    rfl
  have hs : SeparatedTuples.IsDisjointlySupported (SeparatedTuples.pushList (⇑r) (toSepTuple X).1) := by
    rw [show (toSepTuple X).1 = X.1 from rfl, hl]
    exact (toSepTuple ⟨r.actList X.1, actList_mem_sepAll hT r X.2⟩).2
  unfold SeparatedTuples.push
  rw [dif_pos hs]
  exact Subtype.ext hl
theorem toFormalSpan_actFree (hT : TupleRules.TupleSpanActionRules) (r : EuclidMotion) (F : FreeSep) :
    toFormalSpan (r.actFree F) = SeparatedTuples.pushSpan (⇑r) (toFormalSpan F) := by
  have : toFormalSpan ∘ₗ r.actFree = SeparatedTuples.pushSpan (⇑r) ∘ₗ toFormalSpan := by
    refine freeSep_linearMap_ext fun X => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, toFormalSpan_toFree, EuclidMotion.actFree,
      liftLin_toFree, SeparatedTuples.pushSpan, SeparatedTuples.linearExtend_basisVec,
      push_toSepTuple hT]
    exact toFormalSpan_toFree ⟨r.actList X.1, actList_mem_sepAll hT r X.2⟩
  exact LinearMap.congr_fun this F
theorem toFormalSpan_freeMul_toFree {O O' : Set R4} (hO : Disjoint O O') {X Y : FnList}
    (hX : X ∈ sepIn O) (hY : Y ∈ sepIn O') :
    toFormalSpan (freeMul (toFree X) (toFree Y)) =
      SeparatedTuples.formalMul (toFormalSpan (toFree X)) (toFormalSpan (toFree Y)) := by
  have hXY : listAppend X Y ∈ sepAll := (listAppend_mem_sepIn hO hX hY).1
  have h1 : freeMul (toFree X) (toFree Y) = toFree (listAppend X Y) := by
    rw [freeMul, show liftLin (fun X : sepAll =>
        liftLin fun Y : sepAll => toFree (listAppend X.1 Y.1)) (toFree X) = _ from
        liftLin_toFree _ ⟨X, hX.1⟩]
    exact liftLin_toFree (fun Y : sepAll => toFree (listAppend X Y.1)) ⟨Y, hY.1⟩
  rw [h1, show toFormalSpan (toFree (listAppend X Y)) = _ from toFormalSpan_toFree ⟨_, hXY⟩,
    show toFormalSpan (toFree X) = _ from toFormalSpan_toFree ⟨X, hX.1⟩,
    show toFormalSpan (toFree Y) = _ from toFormalSpan_toFree ⟨Y, hY.1⟩,
    SeparatedTuples.formalMul_basisVec]
  have hd : SeparatedTuples.SepTuple.Composable (toSepTuple ⟨X, hX.1⟩) (toSepTuple ⟨Y, hY.1⟩) :=
    SeparatedTuples.composable_of_mem_supportedIn hO
      (toSepTuple_mem_supportedIn (X := ⟨X, hX.1⟩) hX) (toSepTuple_mem_supportedIn (X := ⟨Y, hY.1⟩) hY)
  congr 1
  refine Subtype.ext ?_
  exact (R4TupleForms.juxt_val_eq_append defaultMirrorData hd).symm
theorem toFormalSpan_freeMul {O O' : Set R4} (hO : Disjoint O O') {F A : FreeSep}
    (hF : F ∈ finCombIn O)
    (hA : A ∈ finCombIn O') :
    toFormalSpan (freeMul F A) =
      SeparatedTuples.formalMul (toFormalSpan F) (toFormalSpan A) := by
  rw [finCombIn_eq_freeSpanIn] at hF hA
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨X, hX, rfl⟩ := hG
    induction hA using Submodule.span_induction with
    | mem G' hG' =>
      obtain ⟨Y, hY, rfl⟩ := hG'
      exact toFormalSpan_freeMul_toFree hO hX hY
    | zero => simp
    | add G H _ _ hG hH => simp only [map_add, hG, hH]
    | smul z G _ hG => simp only [map_smul, hG]
  | zero => simp
  | add G H _ _ hG hH => simp only [map_add, LinearMap.add_apply, hG, hH]
  | smul z G _ hG => simp only [map_smul, LinearMap.smul_apply, hG]
end YangMills.Construction.FirstPassageSeqs.BoundedApprox
end
end
section
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.FirstPassageSeqs.BoundedApprox
open EuclideanFunctionals PeriodicGibbsLimits
open SeparatedTuples (TupleFunctional)
open TwoPoints (euclidNorm euclidDot normalRepresentatives)
theorem centeredFnFree_actFree (hT : TupleRules.TupleSpanActionRules) (τ : TupleFunctional)
    (S : ConnFamily) (hτ : τ.toFun = onSepTuples (centeredFn S)) (r : EuclidMotion)
    (hr : τ.IsInvariant (⇑r)) (F : FreeSep) :
    centeredFnFree S (r.actFree F) = centeredFnFree S F := by
  have hc : τ.spanExtension ∘ₗ SeparatedTuples.pushSpan (⇑r) = τ.spanExtension := by
    refine Finsupp.lhom_ext' fun X => LinearMap.ext_ring ?_
    have h1 : (Finsupp.single X (1 : ℂ)) = SeparatedTuples.basisVec X := rfl
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, h1]
    rw [SeparatedTuples.pushSpan, SeparatedTuples.linearExtend_basisVec,
      SeparatedTuples.TupleFunctional.spanExtension, SeparatedTuples.linearExtend_basisVec,
      SeparatedTuples.linearExtend_basisVec]
    exact congrArg _ (hr X)
  rw [← spanExtension_toFormalSpan τ S hτ, ← spanExtension_toFormalSpan τ S hτ,
    toFormalSpan_actFree hT]
  exact LinearMap.congr_fun hc _
theorem freeConj_mem_finCombIn {O : Set R4} {F : FreeSep}
    (hF : F ∈ finCombIn O) :
    freeConj F ∈ finCombIn O := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionMulRules.freeConj_mem_finCombIn <;> assumption
theorem frameLin_mapsTo_signedUnitVectors (w : PeriodicLattice.SignedFrame) :
    Set.MapsTo (frameLin w) InfiniteLattice.signedUnitVectors InfiniteLattice.signedUnitVectors := by
  have key : ∀ ν : Fin 4, frameLin w (Pi.single ν 1) =
      ((w.2 (w.1⁻¹ ν) : ℤ) : ℝ) • (Pi.single (w.1⁻¹ ν) 1 : InfiniteLattice.AmbientSpace) := by
    intro ν
    funext μ
    change ((w.2 μ : ℤ) : ℝ) * (Pi.single ν (1 : ℝ) : Fin 4 → ℝ) (w.1 μ) = _
    by_cases h : μ = w.1⁻¹ ν
    · subst h
      simp
    · have h' : w.1 μ ≠ ν := fun e => h (by rw [← e]; exact (w.1.symm_apply_apply μ).symm)
      rw [Pi.single_eq_of_ne h', Pi.smul_apply, Pi.single_eq_of_ne h]
      simp
  have hsign : ∀ u : ℤˣ, ((u : ℤ) : ℝ) = 1 ∨ ((u : ℤ) : ℝ) = -1 := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp
  rintro x ⟨ν, rfl | rfl⟩
  · rw [key]
    rcases hsign (w.2 (w.1⁻¹ ν)) with h | h <;> rw [h]
    · exact ⟨w.1⁻¹ ν, Or.inl (one_smul _ _)⟩
    · exact ⟨w.1⁻¹ ν, Or.inr (by simp)⟩
  · rw [map_neg, key]
    rcases hsign (w.2 (w.1⁻¹ ν)) with h | h <;> rw [h]
    · exact ⟨w.1⁻¹ ν, Or.inr (by simp)⟩
    · exact ⟨w.1⁻¹ ν, Or.inl (by simp)⟩
theorem exists_mem_hyperoctahedralLinearGroup_of_signedFrame (w : PeriodicLattice.SignedFrame) :
    ∃ w' ∈ InfiniteLattice.hyperoctahedralLinearGroup, ⇑w' = ⇑(frameLin w) := by
  refine InfiniteLattice.exists_mem_hyperoctahedralLinearGroup (frameLin w)
    ⟨frameLin_mapsTo_signedUnitVectors w, (ofSignedFrame w).lin_injective.injOn, ?_⟩
  intro y hy
  let w₂ : PeriodicLattice.SignedFrame := (w.1⁻¹, fun ν => w.2 (w.1⁻¹ ν))
  have hinv : ∀ x, frameLin w (frameLin w₂ x) = x := by
    intro x
    funext ν
    change ((w.2 ν : ℤ) : ℝ) * (((w.2 (w.1⁻¹ (w.1 ν)) : ℤ) : ℝ) * x (w.1⁻¹ (w.1 ν))) = x ν
    rw [show w.1⁻¹ (w.1 ν) = ν from w.1.symm_apply_apply ν, ← mul_assoc, intUnit_mul_self, one_mul]
  exact ⟨frameLin w₂ y, frameLin_mapsTo_signedUnitVectors w₂ hy, hinv y⟩
theorem transl_mul_mem_cubicMotionGroup (w : EuclidMotion) (hw : w ∈ hyperoctahedral) (v : R4) :
    ((EuclidMotion.transl v * w).toPerm : Equiv.Perm InfiniteLattice.AmbientSpace) ∈
      LimitConventions.cubicMotionGroup := by
  obtain ⟨f, rfl⟩ := hw
  obtain ⟨w', hw', he⟩ := exists_mem_hyperoctahedralLinearGroup_of_signedFrame f
  refine ⟨w', hw', v, fun x => ?_⟩
  rw [he]
  change (EuclidMotion.transl v * ofSignedFrame f) x = _
  rw [EuclidMotion.mul_apply, EuclidMotion.transl_apply]
  exact congrArg (· + v) (add_zero (frameLin f x))
theorem centeredFn_euclidInvariant (hT : TupleRules.TupleSpanActionRules) (τ : TupleFunctional)
    (S : ConnFamily) (hτ : τ.toFun = onSepTuples (centeredFn S))
    (hm : ∀ r ∈ LimitConventions.cubicMotionGroup, τ.IsInvariant r) :
    CenteredIsEuclidInvariant S := by
  intro w hw v F
  exact centeredFnFree_actFree hT τ S hτ _ (hm _ (transl_mul_mem_cubicMotionGroup w hw v)) F
theorem exists_pos_smul_of_mem_normalRepresentatives {n : R4} (hn : n ∈ normalRepresentatives) :
    ∃ (n₀ : InfiniteLattice.AmbientSpace) (t : ℝ), n₀ ∈ Mirrors.sixteenNormals ∧ 0 < t ∧ n = t • n₀ := by
  have hs : 0 < (Real.sqrt 2)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (by norm_num))
  rcases hn with (⟨μ, rfl⟩ | ⟨μ, ν, h, rfl⟩) | ⟨μ, ν, h, rfl⟩
  · exact ⟨_, 1, Or.inl ⟨μ, rfl⟩, one_pos, (one_smul _ _).symm⟩
  · exact ⟨_, _, Or.inr ⟨μ, ν, h, Or.inl rfl⟩, hs, rfl⟩
  · exact ⟨_, _, Or.inr ⟨μ, ν, h, Or.inr rfl⟩, hs, rfl⟩
theorem exists_hyperplane_of_mem_normalRepresentatives {n : R4} (hn : euclidNorm n = 1)
    (hmem : n ∈ normalRepresentatives) :
    ∃ M : Mirrors.ReflectingHyperplane, M.reflect = ⇑(hyperplaneReflection n hn 0) ∧
      M.positiveSide = {x | 0 < euclidDot n x} := by
  obtain ⟨n₀, t, h₀, ht, rfl⟩ := exists_pos_smul_of_mem_normalRepresentatives hmem
  have h1 := euclidDot_self_of_unit hn
  have hnn : n₀ ⬝ᵥ n₀ ≠ 0 := Mirrors.dotProduct_self_ne_zero_of_mem h₀
  have hp : ∀ x : R4, euclidDot (t • n₀) x = t * (n₀ ⬝ᵥ x) := by
    intro x
    simp only [euclidDot, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have h2 : t * (t * (n₀ ⬝ᵥ n₀)) = 1 := by
    have := hp (t • n₀)
    rw [h1, dotProduct_smul, smul_eq_mul] at this
    exact this.symm
  refine ⟨⟨n₀, h₀, 0⟩, ?_, ?_⟩
  · funext x
    refine Eq.trans ?_ (hyperplaneReflection_apply _ hn 0 x).symm
    rw [Mirrors.ReflectingHyperplane.reflect]
    simp only [sub_zero, hp]
    congr 1
    rw [smul_smul]
    congr 1
    field_simp
    linear_combination (-(n₀ ⬝ᵥ x)) * h2
  · ext x
    change n₀ ⬝ᵥ x > 0 ↔ 0 < euclidDot (t • n₀) x
    rw [hp]
    exact (mul_pos_iff_of_pos_left ht).symm
theorem isOpen_euclidDot_pos (n : R4) : IsOpen {x : R4 | 0 < euclidDot n x} := by
  have : Continuous fun x : R4 => euclidDot n x := by
    unfold euclidDot
    fun_prop
  exact isOpen_lt continuous_const this
theorem isOpen_euclidDot_neg (n : R4) : IsOpen {x : R4 | euclidDot n x < 0} := by
  have : Continuous fun x : R4 => euclidDot n x := by
    unfold euclidDot
    fun_prop
  exact isOpen_lt this continuous_const
theorem hyperplaneReflection_image_pos (n : R4) (hn : euclidNorm n = 1) :
    (hyperplaneReflection n hn 0) '' {x : R4 | 0 < euclidDot n x} =
      {x | euclidDot n x < 0} := by
  have h := fun x => euclidDot_hyperplaneReflection n hn 0 x
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := h x
    have hx' : 0 < euclidDot n x := hx
    simp only [sub_zero] at this
    change euclidDot n (hyperplaneReflection n hn 0 x) < 0
    rw [this]
    linarith
  · intro hy
    refine ⟨hyperplaneReflection n hn 0 y, ?_, hyperplaneReflection_hyperplaneReflection n hn 0 y⟩
    have := h y
    have hy' : euclidDot n y < 0 := hy
    simp only [sub_zero] at this
    change 0 < euclidDot n (hyperplaneReflection n hn 0 y)
    rw [this]
    linarith
theorem reflectedConj_mem_finCombIn (hT : TupleRules.TupleSpanActionRules) (n : R4)
    (hn : euclidNorm n = 1) {F : FreeSep}
    (hF : F ∈ finCombIn {x : R4 | 0 < euclidDot n x}) :
    reflectedConj n hn 0 F ∈
      finCombIn {x : R4 | euclidDot n x < 0} := by
  obtain ⟨-, hI, -⟩ := hT
  have h := (hI (hyperplaneReflection n hn 0) _ (isOpen_euclidDot_pos n)).2.2.1
    (freeConj_mem_finCombIn hF)
  rw [show (⇑(hyperplaneReflection n hn 0) '' {x : R4 | 0 < euclidDot n x}) = _ from
    hyperplaneReflection_image_pos n hn] at h
  exact h
theorem disjoint_euclidDot_neg_pos (n : R4) :
    Disjoint {x : R4 | euclidDot n x < 0} {x : R4 | 0 < euclidDot n x} :=
  Set.disjoint_left.2 fun x h h' =>
    lt_asymm (show euclidDot n x < 0 from h) (show 0 < euclidDot n x from h')
theorem mulDefined_reflectedConj (hT : TupleRules.TupleSpanActionRules) (n : R4)
    (hn : euclidNorm n = 1) {F : FreeSep}
    (hF : F ∈ finCombIn {x : R4 | 0 < euclidDot n x}) :
    MulDefined (reflectedConj n hn 0 F) F := by
  have hC := hT.2.2.2.2.1
  exact ((hC _ _ (isOpen_euclidDot_neg n) (isOpen_euclidDot_pos n) (disjoint_euclidDot_neg_pos n)).1 _
    (reflectedConj_mem_finCombIn hT n hn hF) _ hF).1
theorem centeredFnFree_nonneg_of_mem_normalRepresentatives (hT : TupleRules.TupleSpanActionRules)
    (τ : TupleFunctional)
    (S : ConnFamily) (hτ : τ.toFun = onSepTuples (centeredFn S))
    (hp : ∀ M : Mirrors.ReflectingHyperplane, ∀ Z ∈ SeparatedTuples.spanIn M.positiveSide,
      SeparatedTupleFunctionals.IsRealNonneg
        (τ.spanExtension
          (SeparatedTuples.formalMul
            (SeparatedTuples.pushSpan M.reflect (SeparatedTuples.conjugation Z)) Z)))
    {n : R4} (hn : euclidNorm n = 1) (hmem : n ∈ normalRepresentatives) {F : FreeSep}
    (hF : F ∈ finCombIn {x : R4 | 0 < euclidDot n x}) :
    0 ≤ centeredFnFree S (freeMul (reflectedConj n hn 0 F) F) := by
  obtain ⟨M, hM, hO⟩ := exists_hyperplane_of_mem_normalRepresentatives hn hmem
  have hZ := toFormalSpan_mem_spanIn hF
  rw [← hO] at hZ
  have h := hp M _ hZ
  rw [hM, ← toFormalSpan_freeConj, ← toFormalSpan_actFree hT,
    show (hyperplaneReflection n hn 0).actFree (freeConj F) = reflectedConj n hn 0 F from rfl,
    ← toFormalSpan_freeMul (disjoint_euclidDot_neg_pos n) (reflectedConj_mem_finCombIn hT n hn hF) hF,
    spanExtension_toFormalSpan τ S hτ] at h
  exact Complex.le_def.2 ⟨h.2, h.1.symm⟩
theorem hyperplaneReflection_neg (n : R4) (hn : euclidNorm n = 1) (hn' : euclidNorm (-n) = 1) :
    hyperplaneReflection (-n) hn' 0 = hyperplaneReflection n hn 0 := by
  refine EuclidMotion.ext_of_apply fun x => ?_
  rw [hyperplaneReflection_apply, hyperplaneReflection_apply]
  funext μ
  simp [euclidDot]
theorem euclidNorm_neg (n : R4) : euclidNorm (-n) = euclidNorm n := by
  simp [euclidNorm]
theorem actFree_freeMul_reflectedConj (hT : TupleRules.TupleSpanActionRules) (n : R4)
    (hn : euclidNorm n = 1) (hn' : euclidNorm (-n) = 1) {F : FreeSep}
    (hF : F ∈ finCombIn {x : R4 | 0 < euclidDot n x}) :
    (hyperplaneReflection n hn 0).actFree (freeMul (reflectedConj n hn 0 F) F) =
      freeMul (reflectedConj (-n) hn' 0 ((hyperplaneReflection n hn 0).actFree F))
        ((hyperplaneReflection n hn 0).actFree F) := by
  have hD := mulDefined_reflectedConj hT n hn hF
  have hR := (hT.2.2.2.2.2.1 (hyperplaneReflection n hn 0) _ _ hD).2.2.2.2
  have hA := hT.2.2.1
  rw [hR]
  congr 2
  rw [reflectedConj, reflectedConj, hyperplaneReflection_neg n hn hn',
    (hA (hyperplaneReflection n hn 0) 1 F).2.1]
theorem centeredFn_reflectionPositive (hT : TupleRules.TupleSpanActionRules) (τ : TupleFunctional)
    (S : ConnFamily) (hτ : τ.toFun = onSepTuples (centeredFn S))
    (hp : ∀ M : Mirrors.ReflectingHyperplane, ∀ Z ∈ SeparatedTuples.spanIn M.positiveSide,
      SeparatedTupleFunctionals.IsRealNonneg
        (τ.spanExtension
          (SeparatedTuples.formalMul
            (SeparatedTuples.pushSpan M.reflect (SeparatedTuples.conjugation Z)) Z)))
    (hinv : ∀ M : Mirrors.ReflectingHyperplane, τ.IsInvariant M.reflect) :
    CenteredIsReflectionPositive S := by
  intro n hn hmem F hF
  refine ⟨mulDefined_reflectedConj hT n hn hF, ?_⟩
  rcases hmem with hmem | hmem
  · exact centeredFnFree_nonneg_of_mem_normalRepresentatives hT τ S hτ hp hn hmem hF
  · have hn' : euclidNorm (-n) = 1 := by rw [euclidNorm_neg, hn]
    obtain ⟨M, hM, -⟩ := exists_hyperplane_of_mem_normalRepresentatives hn' hmem
    have hr : τ.IsInvariant (⇑(hyperplaneReflection n hn 0)) := by
      have := hinv M
      rwa [hM, hyperplaneReflection_neg n hn hn'] at this
    rw [← centeredFnFree_actFree hT τ S hτ _ hr, actFree_freeMul_reflectedConj hT n hn hn' hF]
    refine centeredFnFree_nonneg_of_mem_normalRepresentatives hT τ S hτ hp hn' hmem ?_
    obtain ⟨-, hI, -⟩ := hT
    have h := (hI (hyperplaneReflection n hn 0) _ (isOpen_euclidDot_pos n)).2.2.1 hF
    rw [show (⇑(hyperplaneReflection n hn 0) '' {x : R4 | 0 < euclidDot n x}) = _ from
      hyperplaneReflection_image_pos n hn] at h
    have hs : {x : R4 | euclidDot n x < 0} = {x : R4 | 0 < euclidDot (-n) x} := by
      ext x
      simp [euclidDot]
    rwa [hs] at h
theorem invariant_and_reflectionPositive (hHalf : ReflectionPositivity.LimitSymmetries.LimitHasSymmetries)
    (hT : TupleRules.TupleSpanActionRules) (Dt : ReflectionPositivity.AxisMirror.MirrorData)
    (T : LimitConventions.ApproxTriple Dt.L) (S : ConnFamily)
    (hB : ReflectionPositivity.ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM Dt T)
    (hRP : LimitConventions.ApproxTriple.IsReflPos T)
    (hL : LimitConventions.ApproxTriple.ConvergesTo T
      (onSepTuples (centeredFn S))) :
    CenteredIsEuclidInvariant S ∧ CenteredIsReflectionPositive S := by
  obtain ⟨h1, -, ⟨hm, hM⟩, hc⟩ := hHalf Dt T _ hB hRP hL
  exact ⟨centeredFn_euclidInvariant hT ⟨_, h1⟩ S rfl hm,
    centeredFn_reflectionPositive hT ⟨_, h1⟩ S rfl (fun M => (hc M).1) (fun M => (hM M).2)⟩
end YangMills.Construction.FirstPassageSeqs.BoundedApprox
end
end
section
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.FirstPassageSeqs.BoundedApprox
open EuclideanFunctionals
open ReflectionPositivity.AxisMirror (Ambient)
open LimitConventions (ApproxTriple)
open ReflectionPositivity.ApproximatingSequences.LatticeApproximation (IsBoundedForSomeM)
theorem isDisjointlySupported_iff_mem_sepAll (Y : FnList) :
    SeparatedTuples.IsDisjointlySupported Y ↔ Y ∈ sepAll :=
  R4TupleForms.isDisjointlySupported_iff_mem_separatedAll defaultMirrorData Y
theorem evalOrZero_of_mem (σ : sepAll → ℝ) {X : FnList} (h : X ∈ sepAll) :
    Ambient.evalOrZero σ X = σ ⟨X, h⟩ :=
  dif_pos h
theorem centeredAt_of_mem (S : ConnFamily) {X : FnList} (h : X ∈ sepAll) :
    centeredAt S X = centeredFn S ⟨X, h⟩ :=
  evalOrZero_of_mem _ h
theorem onSepTuples_of_val (σ : sepAll → ℝ) (Y : SeparatedTuples.SepTuple) {Z : FnList}
    (hZ : Z ∈ sepAll) (h : Y.1 = Z) : onSepTuples σ Y = σ ⟨Z, hZ⟩ := by
  obtain ⟨Y, hY⟩ := Y
  subst h
  rfl
theorem centeredFnFree_toFree (S : ConnFamily) (X : sepAll) :
    centeredFnFree S (toFree X.1) = (centeredFn S X : ℂ) :=
  liftLin_toFree _ X
theorem isDisjointlySupported_ofFn_iff {n : ℕ} (f : Fin n → SeparatedTuples.RealValued) :
    SeparatedTuples.IsDisjointlySupported (List.ofFn f) ↔
      (∀ i, SeparatedTuples.IsC1c (f i)) ∧
        ∀ i j, i ≠ j → Disjoint (tsupport (f i)) (tsupport (f j)) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    have hp := List.pairwise_ofFn.1 h₂
    refine ⟨fun i => h₁ (f i) ((List.mem_ofFn' _ _).2 ⟨i, rfl⟩), fun i j hij => ?_⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact hp h
    · exact (hp h).symm
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun g hg => ?_, List.pairwise_ofFn.2 fun i j hij => h₂ i j hij.ne⟩
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact h₁ i
theorem isDisjointlySupported_update_linearCombination {n : ℕ}
    (f : Fin n → SeparatedTuples.RealValued)
    (i : Fin n) (g : SeparatedTuples.RealValued) (a a' : ℝ)
    (hf : SeparatedTuples.IsDisjointlySupported (List.ofFn f))
    (hg : SeparatedTuples.IsDisjointlySupported (List.ofFn (Function.update f i g))) :
    SeparatedTuples.IsDisjointlySupported (List.ofFn (Function.update f i (a • f i + a' • g))) := by
  obtain ⟨hf₁, hf₂⟩ := (isDisjointlySupported_ofFn_iff f).1 hf
  obtain ⟨hg₁, hg₂⟩ := (isDisjointlySupported_ofFn_iff _).1 hg
  have hgi : SeparatedTuples.IsC1c g := by
    simpa using hg₁ i
  have hu : SeparatedTuples.IsC1c (a • f i + a' • g) := by
    refine ⟨?_, ?_⟩
    · exact (contDiff_const.smul (hf₁ i).1).add (contDiff_const.smul hgi.1)
    · exact ((hf₁ i).2.comp_left (g := fun y : ℝ => a • y) (by simp)).add
        (hgi.2.comp_left (g := fun y : ℝ => a' • y) (by simp))
  have hs : tsupport (a • f i + a' • g) ⊆ tsupport (f i) ∪ tsupport g := by
    refine (closure_mono ?_).trans closure_union.subset
    refine (Function.support_add _ _).trans (Set.union_subset_union ?_ ?_)
    · exact Function.support_const_smul_subset _ _
    · exact Function.support_const_smul_subset _ _
  have hd : ∀ j, j ≠ i → Disjoint (tsupport (a • f i + a' • g)) (tsupport (f j)) := by
    intro j hj
    refine Disjoint.mono_left hs (Disjoint.union_left (hf₂ i j hj.symm) ?_)
    have := hg₂ i j hj.symm
    simpa [Function.update_of_ne hj] using this
  refine (isDisjointlySupported_ofFn_iff _).2 ⟨fun k => ?_, fun k l hkl => ?_⟩
  · by_cases hk : k = i
    · subst hk
      simpa using hu
    · simpa [Function.update_of_ne hk] using hf₁ k
  · by_cases hk : k = i
    · subst hk
      simpa [Function.update_of_ne hkl.symm] using hd l hkl.symm
    · by_cases hl : l = i
      · subst hl
        simpa [Function.update_of_ne hk] using (hd k hk).symm
      · simpa [Function.update_of_ne hk, Function.update_of_ne hl] using hf₂ k l hkl
theorem ofFn_update_eq_take_append_drop {n : ℕ} {α : Type*} (f : Fin n → α) (i : Fin n) (u : α) :
    List.ofFn (Function.update f i u) =
      (List.ofFn f).take i ++ u :: (List.ofFn f).drop (i + 1) := by
  have h : List.ofFn (Function.update f i u) = (List.ofFn f).set i u := by
    refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
    have hk : k < n := by simpa using h₁
    by_cases hki : k = i
    · subst hki
      simp
    · have : (⟨k, hk⟩ : Fin n) ≠ i := fun h => hki (congrArg Fin.val h)
      simp [Function.update_of_ne this, Ne.symm hki]
  rw [h, List.set_eq_take_append_cons_drop]
  simp
theorem symmMultilin_latticeInvariant_osPositive
    (hHalf : ReflectionPositivity.LimitSymmetries.LimitHasSymmetries)
    (hT : TupleRules.TupleSpanActionRules)
    (hVal : TensorValues.EntrywiseLinearValues)
    (Dt : ReflectionPositivity.AxisMirror.MirrorData) (T : ApproxTriple Dt.L) (S : ConnFamily)
    (hB : IsBoundedForSomeM Dt T) (hRP : ApproxTriple.IsReflPos T)
    (hL : ApproxTriple.ConvergesTo T (onSepTuples (centeredFn S)))
    (hInv : CenteredIsEuclidInvariant S) (hPos : CenteredIsReflectionPositive S) :
    IsSymmMultilinReal S ∧ IsLatticeInvariant S ∧
      IsOSPositive S := by
  obtain ⟨h1, ⟨hSym, hMul, -⟩, -, -⟩ := hHalf Dt T _ hB hRP hL
  have hLin : IsEntrywiseLinear (centeredFn S) := by
    intro n f i g _ hf hg a a'
    have hf' := (isDisjointlySupported_iff_mem_sepAll _).2 hf
    have hg' := (isDisjointlySupported_iff_mem_sepAll _).2 hg
    have hu' := isDisjointlySupported_update_linearCombination f i g a a' hf' hg'
    have hu := (isDisjointlySupported_iff_mem_sepAll _).1 hu'
    have hfi : List.ofFn f = (List.ofFn f).take i ++ f i :: (List.ofFn f).drop (i + 1) := by
      conv_lhs => rw [← Function.update_eq_self i f]
      exact ofFn_update_eq_take_append_drop f i (f i)
    have key := hMul ((List.ofFn f).take i) ((List.ofFn f).drop (i + 1)) (f i) g a a'
      ⟨List.ofFn f, hf'⟩ ⟨List.ofFn (Function.update f i g), hg'⟩
      ⟨List.ofFn (Function.update f i (a • f i + a' • g)), hu'⟩ hfi
      (ofFn_update_eq_take_append_drop f i g)
      (ofFn_update_eq_take_append_drop f i _)
    exact ((evalOrZero_of_mem (centeredFn S) hu).trans key).trans
      (congrArg₂ (fun p q => a * p + a' * q) (evalOrZero_of_mem (centeredFn S) hf).symm
        (evalOrZero_of_mem (centeredFn S) hg).symm)
  have hMem : ∀ (r : EuclidMotion) (X : FnList), X ∈ sepAll → r.actList X ∈ sepAll :=
    fun r X hX => actList_mem_sepAll hT r hX
  have hAct : ∀ (w : EuclidMotion), w ∈ hyperoctahedral → ∀ (v : R4) (X : FnList) (hX : X ∈ sepAll),
      centeredAt S (((EuclidMotion.transl v * w)).actList X) = centeredAt S X := by
    intro w hw v X hX
    have h := hInv w hw v (toFree X)
    have h2 : (EuclidMotion.transl v * w).actFree (toFree X) =
        toFree ((EuclidMotion.transl v * w).actList X) :=
      liftLin_toFree (fun X : sepAll => toFree ((EuclidMotion.transl v * w).actList X.1))
        ⟨X, hX⟩
    rw [h2, centeredFnFree_toFree S ⟨_, hMem _ X hX⟩,
      centeredFnFree_toFree S ⟨X, hX⟩] at h
    rw [centeredAt_of_mem S (hMem _ X hX), centeredAt_of_mem S hX]
    exact_mod_cast h
  refine ⟨⟨fun X => ?_, ?_, hLin, ?_⟩, fun X hX => ⟨fun v => ?_, fun w hw => ?_⟩, fun F hF => ?_⟩
  · rw [centeredFnFree_toFree]
    exact Complex.ofReal_im _
  · intro n f hf ς
    have hf' := (isDisjointlySupported_iff_mem_sepAll _).2 hf
    let e : Fin n ≃ Fin (List.ofFn f).length := finCongr List.length_ofFn.symm
    have hl : (SeparatedTuples.SepTuple.reorder ⟨List.ofFn f, hf'⟩ (e.permCongr ς)).1 =
        List.ofFn (f ∘ ς) := by
      refine List.ext_getElem (by simp [SeparatedTuples.SepTuple.reorder]) fun k h₁ h₂ => ?_
      simp [SeparatedTuples.SepTuple.reorder, e, Equiv.permCongr_apply]
    have hs := hSym ⟨List.ofFn f, hf'⟩ (e.permCongr ς)
    have hm : List.ofFn (f ∘ ς) ∈ sepAll := by
      rw [← hl]
      exact (isDisjointlySupported_iff_mem_sepAll _).1 (SeparatedTuples.SepTuple.reorder _ _).2
    rw [centeredAt_of_mem S hm, centeredAt_of_mem S hf]
    exact (onSepTuples_of_val (centeredFn S) _ hm hl).symm.trans (hs.trans
      (onSepTuples_of_val (centeredFn S) ⟨List.ofFn f, hf'⟩ hf rfl))
  · intro n hn F hF F' hF' hc
    exact (hVal _ hLin).2.2.1 n hn F hF F' hF' hc
  · have := hAct 1 hyperoctahedral.one_mem v X hX
    rwa [mul_one] at this
  · have h0 : EuclidMotion.transl 0 * w = w := EuclidMotion.ext_of_apply fun x => by
      rw [EuclidMotion.mul_apply, EuclidMotion.transl_apply, add_zero]
    have := hAct w hw 0 X hX
    rw [h0] at this
    exact this.symm
  · have hmem : (PeriodicLattice.coordVec 3 : R4) ∈ TwoPoints.normalRepresentatives :=
      Or.inl (Or.inl ⟨3, rfl⟩)
    have hn := PeriodicGibbsLimits.euclidNorm_of_mem_normalRepresentatives hmem
    have hprod : ∀ x : R4, TwoPoints.euclidDot (PeriodicLattice.coordVec 3 : R4) x = x 3 := by
      intro x
      simp [TwoPoints.euclidDot, PeriodicLattice.coordVec, Pi.single_apply]
    have hset : {x : R4 | 0 < TwoPoints.euclidDot
        (PeriodicLattice.coordVec 3 : R4) x} = upperHalf := by
      ext x
      simp [upperHalf, hprod]
    have hF' : F ∈ finCombIn {x : R4 | 0 < TwoPoints.euclidDot
        (PeriodicLattice.coordVec 3 : R4) x} := by
      rw [hset, finCombIn_eq_freeSpanIn]
      exact hF
    have hrefl : PeriodicGibbsLimits.hyperplaneReflection _ hn 0 = timeFlip :=
      EuclidMotion.ext_of_apply fun x => by
        rw [PeriodicGibbsLimits.hyperplaneReflection_apply, timeFlip_apply, hprod, sub_zero]
    have hp := (hPos _ hn (Or.inl hmem) F hF').2
    have he : PeriodicGibbsLimits.reflectedConj _ hn 0 F =
        timeFlip.actFree (freeConj F) := by
      rw [PeriodicGibbsLimits.reflectedConj, hrefl]
    rw [he] at hp
    have hp' : 0 ≤ osForm S F F := hp
    exact ⟨(Complex.le_def.1 hp').2.symm, (Complex.le_def.1 hp').1⟩
end YangMills.Construction.FirstPassageSeqs.BoundedApprox
end
end
section
noncomputable section
namespace YangMills.Construction.FirstPassageSeqs.BoundedApprox
open EuclideanFunctionals
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass spanClass vacuum posTupleVec)
open HilbertSpaceBasics (IsPosSemidef)
open ReflectionPositivity.TupleForm (reflectionForm PositiveSpan reflectConj)
theorem timeReflection_eq_timeFlip : TimeAxis.timeReflection = ⇑timeFlip := by
  funext x
  change TimeAxis.timeReflection x = timeFlip x
  rw [timeFlip_apply]
  funext μ
  fin_cases μ <;> simp [TimeAxis.timeReflection, PeriodicLattice.coordVec] <;> ring
def toPositiveSpan : freeSpanIn upperHalf →ₗ[ℂ] PositiveSpan :=
  (toFormalSpan ∘ₗ (freeSpanIn upperHalf).subtype).codRestrict _ fun F =>
    toFormalSpan_mem_spanIn (O := upperHalf)
      ((finCombIn_eq_freeSpanIn _).symm ▸ F.2)
@[simp] theorem toPositiveSpan_val (F : freeSpanIn upperHalf) :
    (toPositiveSpan F).1 = toFormalSpan F.1 := rfl
theorem exists_toFormalSpan_eq {O : Set R4} {G : SeparatedTuples.FormalSpan}
    (hG : G ∈ SeparatedTuples.spanIn O) : ∃ F ∈ freeSpanIn O, toFormalSpan F = G := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨X, rfl⟩ := hG
    have hX : X.1.1 ∈ sepIn O :=
      (R4TupleForms.mem_supportedIn_iff_mem_separatedWithin defaultMirrorData O X.1).1 X.2
    refine ⟨toFree X.1.1, Submodule.subset_span ⟨_, hX, rfl⟩, ?_⟩
    exact toFormalSpan_toFree ⟨X.1.1, hX.1⟩
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add G H _ _ hG hH =>
    obtain ⟨F, hF, rfl⟩ := hG
    obtain ⟨A, hA, rfl⟩ := hH
    exact ⟨F + A, Submodule.add_mem _ hF hA, map_add _ _ _⟩
  | smul z G _ hG =>
    obtain ⟨F, hF, rfl⟩ := hG
    exact ⟨z • F, Submodule.smul_mem _ z hF, map_smul _ _ _⟩
theorem toPositiveSpan_surjective : Function.Surjective toPositiveSpan := fun Z => by
  obtain ⟨F, hF, h⟩ := exists_toFormalSpan_eq (O := upperHalf) Z.2
  exact ⟨⟨F, hF⟩, Subtype.ext h⟩
section Classes
variable (τ : SeparatedTuples.TupleFunctional) (h : IsPosSemidef (reflectionForm τ))
def freeSepClass : freeSpanIn upperHalf →ₗ[ℂ] PhysicalSpace τ h :=
  posClass τ h ∘ₗ toPositiveSpan
theorem freeSepClass_apply (F : freeSpanIn upperHalf) :
    freeSepClass τ h F = posClass τ h (toPositiveSpan F) := rfl
theorem inner_posClass (Z Z' : PositiveSpan) :
    inner ℂ (posClass τ h Z) (posClass τ h Z') = reflectionForm τ Z Z' :=
  UniformSpace.Completion.inner_coe (𝕜 := ℂ)
    (E := HilbertSpaceBasics.FormSpace (reflectionForm τ) h) Z Z'
theorem denseRange_freeSepClass : DenseRange (freeSepClass τ h) := by
  have h₀ : DenseRange (posClass τ h) :=
    UniformSpace.Completion.denseRange_coe (α := HilbertSpaceBasics.FormSpace (reflectionForm τ) h)
  have h₁ : Set.range (freeSepClass τ h) = Set.range (posClass τ h) := by
    have : ⇑(freeSepClass τ h) = ⇑(posClass τ h) ∘ ⇑toPositiveSpan := rfl
    rw [this]
    exact toPositiveSpan_surjective.range_comp _
  rw [DenseRange, h₁]
  exact h₀
theorem classOrZero_freeSepClass {G : FreeSep} (hG : G ∈ freeSpanIn upperHalf) :
    classOrZero (freeSepClass τ h) G = spanClass τ h (toFormalSpan G) := by
  have hm : toFormalSpan G ∈ SeparatedTuples.spanIn TimeAxis.upperHalfSpace :=
    toFormalSpan_mem_spanIn (O := upperHalf) ((finCombIn_eq_freeSpanIn _).symm ▸ hG)
  rw [classOrZero_of_mem _ hG, spanClass, dif_pos hm]
  rfl
theorem freeSepClass_emptyElt : freeSepClass τ h emptyElt = vacuum τ h := by
  rw [freeSepClass_apply, vacuum]
  congr 1
  refine Subtype.ext ?_
  rw [toPositiveSpan_val]
  have hm : ([] : FnList) ∈ sepAll :=
    (ReflectionPositivity.AxisMirror.Ambient.nil_mem_separatedWithin defaultMirrorData
      ReflectionPositivity.AxisMirror.Ambient.euclidean upperHalf).1
  exact (toFormalSpan_toFree ⟨[], hm⟩)
end Classes
theorem actFree_mem_freeSpanIn (hT : TupleRules.TupleSpanActionRules) (r : EuclidMotion)
    (hr : r '' upperHalf ⊆ upperHalf) {F : FreeSep}
    (hF : F ∈ freeSpanIn upperHalf) : r.actFree F ∈ freeSpanIn upperHalf := by
  obtain ⟨-, hI, -⟩ := hT
  have hopen : IsOpen upperHalf :=
    isOpen_lt continuous_const (continuous_apply 3)
  have h₁ := (hI r upperHalf hopen).2.2.mapsTo
    (show F ∈ (finCombIn upperHalf : Set FreeSep) from
      (finCombIn_eq_freeSpanIn _).symm ▸ hF)
  have h₂ : r.actFree F ∈ freeSpanIn (r '' upperHalf) := (finCombIn_eq_freeSpanIn _) ▸ h₁
  refine Submodule.span_mono (Set.image_mono ?_) h₂
  intro X hX
  exact ⟨hX.1, fun f hf => (hX.2 f hf).trans hr⟩
theorem transl_image_upperHalf_subset {v : R4} (hv : 0 ≤ v 3) :
    EuclidMotion.transl v '' upperHalf ⊆ upperHalf := by apply _root_.YangMills.Construction.EuclideanFunctionals.ReconstructionFactsProof.transl_image_upperHalf <;> assumption
theorem timeStabilizer_image_upperHalf_subset (hT : TupleRules.TupleSpanActionRules) {w : EuclidMotion}
    (hw : w ∈ timeStabilizer) : w '' upperHalf ⊆ upperHalf :=
  (hT.2.2.2.2.2.2.2.2.2.2.1 w hw).2.1.le
section Images
variable (τ : SeparatedTuples.TupleFunctional) (h : IsPosSemidef (reflectionForm τ))
theorem classOrZero_actFree (hT : TupleRules.TupleSpanActionRules) (r : EuclidMotion)
    (hr : r '' upperHalf ⊆ upperHalf) (F : freeSpanIn upperHalf) :
    classOrZero (freeSepClass τ h) (r.actFree F.1) =
      spanClass τ h (SeparatedTuples.pushSpan (⇑r) (toPositiveSpan F).1) := by
  rw [classOrZero_freeSepClass τ h (actFree_mem_freeSpanIn hT r hr F.2), toFormalSpan_actFree hT]
  rfl
theorem reflectionForm_toPositiveSpan (hT : TupleRules.TupleSpanActionRules) (S : ConnFamily)
    (hτ : τ.toFun = onSepTuples (centeredFn S)) (F F' : freeSpanIn upperHalf) :
    reflectionForm τ (toPositiveSpan F) (toPositiveSpan F') = osForm S F.1 F'.1 := by
  have hmem : ∀ {G : FreeSep}, G ∈ freeSpanIn upperHalf →
      G ∈ finCombIn {x : R4 | (0 : ℝ) < x 3} :=
    fun {G} hG => (finCombIn_eq_freeSpanIn _).symm ▸ hG
  have hneg : flipConj F.1 ∈
      finCombIn {x : R4 | x 3 < -(0 : ℝ)} :=
    (hT.2.2.2.2.2.2.2.2.2.1.1 0 le_rfl F.1 (hmem F.2) F'.1 (hmem F'.2)).1
  have hd : Disjoint {x : R4 | x 3 < -(0 : ℝ)} {x : R4 | (0 : ℝ) < x 3} := by
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    have h₁ : x 3 < -(0 : ℝ) := hx
    have h₂ : (0 : ℝ) < x 3 := hx'
    linarith
  rw [osForm, ← spanExtension_toFormalSpan τ S hτ,
    show freeMul (timeFlip.actFree (freeConj F.1)) F'.1 = freeMul (flipConj F.1) F'.1 from rfl,
    toFormalSpan_freeMul hd hneg (hmem F'.2), reflectionForm, reflectConj, flipConj,
    toFormalSpan_actFree hT, toFormalSpan_freeConj, timeReflection_eq_timeFlip]
  rfl
theorem inner_freeSepClass (hT : TupleRules.TupleSpanActionRules) (S : ConnFamily)
    (hτ : τ.toFun = onSepTuples (centeredFn S)) (F F' : freeSpanIn upperHalf) :
    inner ℂ (freeSepClass τ h F) (freeSepClass τ h F') = osForm S F.1 F'.1 := by
  rw [freeSepClass_apply, freeSepClass_apply, inner_posClass,
    reflectionForm_toPositiveSpan τ hT S hτ]
end Images
end YangMills.Construction.FirstPassageSeqs.BoundedApprox
end
end
section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ENNReal
noncomputable section
namespace YangMills.Construction.FirstPassageSeqs.BoundedApprox
abbrev toEuclidean (y : Fin 4 → ℝ) : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 y
theorem measurable_toEuclidean : Measurable toEuclidean :=
  (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).measurable
theorem integral_map_toEuclidean {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (μ : Measure (Fin 4 → ℝ)) (f : EuclideanSpace ℝ (Fin 4) → G) :
    ∫ x, f x ∂(μ.map toEuclidean) = ∫ y, f (toEuclidean y) ∂μ :=
  (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).measurableEmbedding.integral_map f
def borelPreimage (B : EuclideanSpectral.BorelSubset 4) :
    SpectralTheory.BorelSets 4 :=
  ⟨toEuclidean ⁻¹' B.1, measurable_toEuclidean B.2⟩
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def onEuclidean (E : SpectralTheory.ProjectionMeasure 4 H) : EuclideanSpectral.ProjMeasure H 4 where
  toFun B := ((E (borelPreimage B) : H →L[ℂ] H) : H →ₗ[ℂ] H)
  isOrthProj B := by
    have hP := E.isStarProjection (borelPreimage B)
    refine ⟨LinearMap.ext fun ψ => ?_, fun φ ψ => ?_⟩
    · exact congrArg (fun T : H →L[ℂ] H => T ψ) hP.isIdempotentElem.eq
    · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP.isSelfAdjoint φ ψ
  univ_eq_id := by
    have h : borelPreimage (EuclideanSpectral.BorelSubset.univ 4) =
        ⟨univ, MeasurableSet.univ⟩ := Subtype.ext rfl
    rw [h, E.map_univ]
    rfl
  hasSum_diag ψ B hB := by
    have hd : Pairwise fun r s => Disjoint (borelPreimage (B r)).1 (borelPreimage (B s)).1 :=
      fun r s hrs => (hB hrs).preimage toEuclidean
    have ht := E.tendsto_sum (fun r => borelPreimage (B r)) hd ψ
    have hu : (⟨⋃ r, (borelPreimage (B r)).1, MeasurableSet.iUnion fun r => (borelPreimage (B r)).2⟩ :
        SpectralTheory.BorelSets 4) =
        borelPreimage (EuclideanSpectral.BorelSubset.unionSeq B) :=
      Subtype.ext preimage_iUnion.symm
    rw [hu] at ht
    have hc : Continuous fun v : H => (⟪ψ, v⟫_ℂ).re := by fun_prop
    have h₁ := (hc.tendsto _).comp ht
    have hre : ∀ A : SpectralTheory.BorelSets 4,
        (⟪ψ, E A ψ⟫_ℂ).re = ‖E A ψ‖ ^ 2 := fun A => by
      have h := congrArg Complex.re (E.spectralValue_eq_norm_sq ψ A)
      rw [Complex.ofReal_re] at h
      exact h
    have h₂ : Tendsto (fun N => ∑ r ∈ Finset.range N, ‖E (borelPreimage (B r)) ψ‖ ^ 2) atTop
        (𝓝 (‖E (borelPreimage (EuclideanSpectral.BorelSubset.unionSeq B)) ψ‖ ^ 2)) := by
      rw [← hre]
      refine h₁.congr fun N => ?_
      simp only [Function.comp_apply, inner_sum, Complex.re_sum]
      exact Finset.sum_congr rfl fun r _ => hre _
    have hs := (hasSum_iff_tendsto_nat_of_nonneg (fun _ => by positivity) _).2 h₂
    have hs' := Complex.ofRealCLM.hasSum hs
    have hv : ∀ A : EuclideanSpectral.BorelSubset 4,
        EuclideanSpectral.diagValue
          (fun B => ((E (borelPreimage B) : H →L[ℂ] H) : H →ₗ[ℂ] H)) ψ A =
        Complex.ofRealCLM (‖E (borelPreimage A) ψ‖ ^ 2) :=
      fun A => E.spectralValue_eq_norm_sq ψ (borelPreimage A)
    simp only [hv]
    exact hs'
theorem onEuclidean_apply (E : SpectralTheory.ProjectionMeasure 4 H)
    (B : EuclideanSpectral.BorelSubset 4)
    (ψ : H) : onEuclidean E B ψ = E (borelPreimage B) ψ := rfl
theorem onEuclidean_eq_zero (E : SpectralTheory.ProjectionMeasure 4 H)
    {B : EuclideanSpectral.BorelSubset 4}
    (h : E (borelPreimage B) = 0) : onEuclidean E B = 0 :=
  LinearMap.ext fun ψ => by rw [onEuclidean_apply, h]; rfl
theorem diagMeasure_onEuclidean
    (hF : EuclideanSpectral.ProjMeasureBasicFacts)
    (E : SpectralTheory.ProjectionMeasure 4 H) (ψ : H) :
    (onEuclidean E).diagMeasure ψ = (E.spectralValueMeasure ψ).map toEuclidean := by
  obtain ⟨-, -, h3, -⟩ := hF H 4 (onEuclidean E)
  obtain ⟨⟨hfin, hval⟩, -, -⟩ := h3 ψ
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply measurable_toEuclidean hB]
  have h1 := congrArg Complex.re (hval ⟨B, hB⟩)
  have h2 : (onEuclidean E).diag ψ ⟨B, hB⟩ = ((‖E (borelPreimage ⟨B, hB⟩) ψ‖ ^ 2 : ℝ) : ℂ) :=
    E.spectralValue_eq_norm_sq ψ (borelPreimage ⟨B, hB⟩)
  rw [h2, Complex.ofReal_re, Complex.ofReal_re] at h1
  have h3' := E.spectralValueMeasure_apply ψ (borelPreimage ⟨B, hB⟩)
  change E.spectralValueMeasure ψ (toEuclidean ⁻¹' B) = _ at h3'
  rw [show (E.spectralValueMeasure ψ) (toEuclidean ⁻¹' B) = _ from h3', h1]
  exact (ofReal_measureReal (μ := (onEuclidean E).diagMeasure ψ) (s := B)).symm
theorem apply_of_eq_toUnboundedOperator
    {A : SpectralTheory.UnboundedOperator H} {T : H →L[ℂ] H}
    (h : A = SpectralTheory.toUnboundedOperator T) (ψ : H)
    (hψ : ψ ∈ A.domain) : A ⟨ψ, hψ⟩ = T ψ := by
  subst h
  rfl
theorem boundedIntegral_onEuclidean
    (hF : EuclideanSpectral.ProjMeasureBasicFacts)
    (hR : SpectralTheory.SpectralIntegralLawsHold)
    (E : SpectralTheory.ProjectionMeasure 4 H) {f : EuclideanSpace ℝ (Fin 4) → ℂ} (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    (onEuclidean E).boundedIntegral f =
      ((E.boundedCalculus fun y => f (toEuclidean y) : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  obtain ⟨-, -, -, -, -, -, h7⟩ := hF H 4 (onEuclidean E)
  obtain ⟨huniq, -⟩ := h7 f hf hb
  have hg : Measurable fun y => f (toEuclidean y) := hf.comp measurable_toEuclidean
  have hgb : SpectralTheory.IsBoundedComplexFn
      fun y => f (toEuclidean y) := by
    obtain ⟨C, hC⟩ := hb
    exact ⟨C, fun x => hC _⟩
  have hrules := hR 4 H E
  have hbd := hrules.isBoundedCalculusOf _ hg hgb
  have hw : (onEuclidean E).IsWeakIntegralOp f
      ((E.boundedCalculus fun y => f (toEuclidean y) : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
    intro ψ
    have hdom : ψ ∈ (E.functionalCalculus fun y => f (toEuclidean y)).domain := by
      rw [hbd]
      exact Submodule.mem_top
    have h1 := hrules.inner_self _ hg ⟨ψ, hdom⟩
    rw [apply_of_eq_toUnboundedOperator hbd ψ hdom] at h1
    rw [diagMeasure_onEuclidean hF, integral_map_toEuclidean]
    exact h1
  have he : (onEuclidean E).IsWeakIntegralOp f ((onEuclidean E).boundedIntegral f) :=
    Classical.epsilon_spec huniq.exists
  exact huniq.unique he hw
theorem boundedIntegralOn_onEuclidean
    (hF : EuclideanSpectral.ProjMeasureBasicFacts)
    (hR : SpectralTheory.SpectralIntegralLawsHold)
    (E : SpectralTheory.ProjectionMeasure 4 H) (B : EuclideanSpectral.BorelSubset 4)
    {f : EuclideanSpace ℝ (Fin 4) → ℂ} (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x ∈ B.1, ‖f x‖ ≤ C) :
    (onEuclidean E).boundedIntegralOn B f =
      ((E.boundedCalculus fun y => B.1.indicator f (toEuclidean y) : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  refine boundedIntegral_onEuclidean hF hR E (hf.indicator B.2) ?_
  obtain ⟨C, hC⟩ := hb
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ B.1
  · rw [indicator_of_mem hx]
    exact (hC x hx).trans (le_max_left _ _)
  · rw [indicator_of_notMem hx, norm_zero]
    exact le_max_right _ _
theorem mem_fnDomain_of_spectralIntegral_eq_zero
    (hF : EuclideanSpectral.ProjMeasureBasicFacts)
    (hR : SpectralTheory.SpectralIntegralLawsHold)
    (hC : EuclideanSpectral.ProjMeasureBoundedCalculus)
    (E : SpectralTheory.ProjectionMeasure 4 H) {u : EuclideanSpace ℝ (Fin 4) → ℂ}
    (hu : Measurable u) (ψ : H)
    (hψ : ψ ∈ (E.functionalCalculus fun y => u (toEuclidean y)).domain)
    (h0 : E.functionalCalculus (fun y => u (toEuclidean y)) ⟨ψ, hψ⟩ = 0) :
    ∃ h : ψ ∈ (onEuclidean E).fnDomain u,
      (onEuclidean E).borelFnOp u ⟨ψ, h⟩ = 0 := by
  have hg : Measurable fun y => u (toEuclidean y) := hu.comp measurable_toEuclidean
  have hrules := hR 4 H E
  obtain ⟨-, -, -, -, -, -, hcalc⟩ := hC H 4 (onEuclidean E)
  obtain ⟨hdom, -, hnorm, -⟩ := hcalc u hu
  have hset : ψ ∈ (onEuclidean E).fnDomainSet u := by
    have h1 : ψ ∈ SpectralTheory.functionalDomain E
        fun y => u (toEuclidean y) := by
      rw [← (hrules.isOperator _ hg).1]
      exact hψ
    change ∫⁻ x, ‖u x‖ₑ ^ 2 ∂((onEuclidean E).diagMeasure ψ) < ⊤
    rw [diagMeasure_onEuclidean hF,
      lintegral_map (by fun_prop) measurable_toEuclidean]
    exact h1
  have hmem : ψ ∈ (onEuclidean E).fnDomain u := by
    rw [← SetLike.mem_coe, hdom]
    exact hset
  refine ⟨hmem, ?_⟩
  have hn := hnorm ⟨ψ, hmem⟩
  have hz := hrules.norm_sq _ hg ⟨ψ, hψ⟩
  rw [h0, norm_zero] at hz
  have he : ‖(onEuclidean E).truncLimit u ⟨ψ, hmem⟩‖ ^ 2 = 0 := by
    rw [hn]
    change ∫ x, ‖u x‖ ^ 2 ∂((onEuclidean E).diagMeasure ψ) = 0
    rw [diagMeasure_onEuclidean hF, integral_map_toEuclidean]
    exact hz.symm.trans (by norm_num)
  exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 he)
end YangMills.Construction.FirstPassageSeqs.BoundedApprox
end
end
section
open MeasureTheory Set
open scoped NNReal
noncomputable section
namespace YangMills.Construction.FirstPassageSeqs.BoundedApprox
open EuclideanFunctionals
open SpectralTheory
open ReflectionPositivity.ReconstructionComplements (compBounded boundedComp heatPhase spatialPart
  octahedralUnitary octahedralUnitaryCLM octahedralUnitaryInvCLM SupportClaim IntertwiningClaim
  UnitaryClaim IsOctahedralUnitary OctahedralFixesTime)
open ReflectionPositivity.LimitReconstruction (TimeSemigroupProperties SpaceShiftProperties)
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass spanClass timeShift spaceShift)
open LimitConventions (SpaceVec spaceDot timeExtension octahedralGroup3)
section General
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem eq_of_toUnboundedOperator_eq {A B : H →L[ℂ] H}
    (h : toUnboundedOperator A = toUnboundedOperator B) :
    A = B := by apply _root_.YangMills.Construction.GeneratorsAndFlows.toUnboundedOperator_injective <;> assumption
variable (E : ProjectionMeasure 4 H)
theorem boundedIntegralOp_congr (hR : E.CalculusLaws) {f g : (Fin 4 → ℝ) → ℂ}
    (hf : Measurable f) (hg : Measurable g) (hfb : IsBoundedComplexFn f) (hgb : IsBoundedComplexFn g)
    (h0 : E ⟨{x | f x ≠ g x}, (measurableSet_eq_fun hf hg).compl⟩ = 0) :
    E.boundedCalculus f = E.boundedCalculus g := by
  apply eq_of_toUnboundedOperator_eq
  rw [← hR.isBoundedCalculusOf f hf hfb, ← hR.isBoundedCalculusOf g hg hgb]
  exact hR.calculus_congr f g hf hg h0
theorem eq_zero_of_agree_on_nonneg (hS : E.SupportLaws)
    (hc : E.IsConcentratedOn ReflectionPositivity.ReconstructionComplements.nonnegEnergy)
    {f g : (Fin 4 → ℝ) → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ y : Fin 4 → ℝ, 0 ≤ y 0 → f y = g y) :
    E ⟨{x | f x ≠ g x}, (measurableSet_eq_fun hf hg).compl⟩ = 0 :=
  hS.vanishesOn_of_subset ⟨ReflectionPositivity.ReconstructionComplements.nonnegEnergy.1ᶜ,
    ReflectionPositivity.ReconstructionComplements.nonnegEnergy.2.compl⟩ _
    (fun x (hx : f x ≠ g x) hx0 => hx (hfg x hx0)) hc
end General
theorem spectralResolution_unique (hD : GeneratorsAndFlows.GeneratorFlowTheorem)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : UnboundedOperator H} {F F₀ : ProjectionMeasure 1 H} (h₁ : HasSpectralResolution A F)
    (h₂ : HasSpectralResolution A F₀) : F₀ = F :=
  ((hD H).1 F).2.2.1.eq_of_generator F₀ (h₂.symm.trans h₁)
def truncatedPhase (t : ℝ≥0) (a : SpaceVec) : (Fin 4 → ℝ) → ℂ :=
  {y | 0 ≤ y 0}.indicator (heatPhase t a)
theorem measurable_heatPhase (t : ℝ≥0) (a : SpaceVec) : Measurable (heatPhase t a) := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.measurable_heatPhase <;> assumption
theorem measurable_truncatedPhase (t : ℝ≥0) (a : SpaceVec) : Measurable (truncatedPhase t a) :=
  (measurable_heatPhase t a).indicator (measurableSet_le measurable_const (measurable_pi_apply 0))
theorem isBoundedComplexFn_truncatedPhase (t : ℝ≥0) (a : SpaceVec) :
    IsBoundedComplexFn (truncatedPhase t a) := by
  refine ⟨1, fun y => ?_⟩
  by_cases hy : 0 ≤ y 0
  · rw [truncatedPhase, indicator_of_mem (show y ∈ {y : Fin 4 → ℝ | 0 ≤ y 0} from hy), heatPhase,
      Complex.norm_exp]
    have : (((-(t : ℝ) * y 0 : ℝ) : ℂ) + Complex.I *
        ((spaceDot a (spatialPart y) : ℝ) : ℂ)).re = -(t : ℝ) * y 0 := by
      simp
    rw [this, Real.exp_le_one_iff]
    have := mul_nonneg t.2 hy
    simpa using this
  · rw [truncatedPhase, indicator_of_notMem (show y ∉ {y : Fin 4 → ℝ | 0 ≤ y 0} from hy)]
    simp
theorem timeBasisVector_eq_timeVec :
    Continuum.AxisPreservingSymmetries.timeBasisVector = (timeVec : R4) := by
  funext ν
  fin_cases ν <;>
    simp [Continuum.AxisPreservingSymmetries.timeBasisVector, TimeAxis.timeIdx,
      PeriodicLattice.coordVec]
theorem exists_octahedral_of_timeStabilizer (hCF : OctahedralFixesTime) (w : timeStabilizer) :
    ∃ w' ∈ octahedralGroup3, ∀ x, (w : EuclidMotion) x = timeExtension w' x := by
  obtain ⟨w, ⟨fr, rfl⟩, hwe⟩ := w
  have hg : ∀ x, (ofSignedFrame fr).linEquiv x = ofSignedFrame fr x := fun x => (add_zero _).symm
  have hmem : (ofSignedFrame fr).linEquiv ∈ InfiniteLattice.hyperoctahedralLinearGroup := by
    rw [InfiniteLattice.mem_hyperoctahedralLinearGroup_iff]
    refine ⟨fr.1, fr.2, fun x μ => ?_⟩
    rw [hg, ofSignedFrame_apply]
    rfl
  have hfix : (ofSignedFrame fr).linEquiv Continuum.AxisPreservingSymmetries.timeBasisVector =
      Continuum.AxisPreservingSymmetries.timeBasisVector := by
    rw [timeBasisVector_eq_timeVec, hg]
    exact hwe
  obtain ⟨w', hw', hgw⟩ := (hCF _).1 ⟨hmem, hfix⟩
  exact ⟨w', hw', fun x => by rw [← hgw, ← hg x]⟩
section Limit
variable (τ : SeparatedTuples.TupleFunctional)
  (h : HilbertSpaceBasics.IsPosSemidef (ReflectionPositivity.TupleForm.reflectionForm τ))
structure LimitInputs : Prop where
  basicFacts : EuclideanSpectral.ProjMeasureBasicFacts
  integralLaws : SpectralTheory.SpectralIntegralLawsHold
  boundedCalculus : EuclideanSpectral.ProjMeasureBoundedCalculus
  concentration : SpectralSupport.ConcentratedOnSupportTheorem
  generators : GeneratorsAndFlows.GeneratorFlowTheorem
  supportClaim : SupportClaim τ h
  timeSemigroup : TimeSemigroupProperties τ h
  spaceShifts : SpaceShiftProperties τ h
variable {τ h}
theorem timeShift_mul_spaceShift (L : LimitInputs τ h) (t : ℝ≥0) (a : SpaceVec) :
    timeShift τ h t * spaceShift τ h a =
      (ReflectionPositivity.ReconstructionComplements.jointMeasure τ h).boundedCalculus
        (truncatedPhase t a) := by
  set E := ReflectionPositivity.ReconstructionComplements.jointMeasure τ h with hE
  have hR : E.CalculusLaws := L.integralLaws 4 _ E
  have hS : E.SupportLaws := L.concentration 4 _ E
  obtain ⟨hcar, F, hF, -, hform⟩ := L.supportClaim
  obtain ⟨-, -, -, -, -, ⟨F₀, hF₀, -, hT⟩, -⟩ := L.timeSemigroup
  obtain rfl := spectralResolution_unique L.generators hF hF₀
  have h1 := hform t a
  rw [← hT t] at h1
  have hcong : E.functionalCalculus (heatPhase t a) = E.functionalCalculus (truncatedPhase t a) :=
    hR.calculus_congr _ _ (measurable_heatPhase t a) (measurable_truncatedPhase t a)
      (eq_zero_of_agree_on_nonneg E hS hcar (measurable_heatPhase t a) (measurable_truncatedPhase t a)
        fun y hy => (indicator_of_mem (show y ∈ {y : Fin 4 → ℝ | 0 ≤ y 0} from hy) _).symm)
  rw [hcong, hR.isBoundedCalculusOf _ (measurable_truncatedPhase t a)
    (isBoundedComplexFn_truncatedPhase t a)] at h1
  ext ψ
  exact apply_of_eq_toUnboundedOperator h1 ψ trivial
theorem timeShift_zero (L : LimitInputs τ h) : timeShift τ h 0 = 1 := by
  obtain ⟨-, -, -, hSg, -⟩ := L.timeSemigroup
  exact hSg.map_zero
theorem spaceShift_zero (L : LimitInputs τ h) : spaceShift τ h 0 = 1 := by
  obtain ⟨-, -, -, hRep, -⟩ := L.spaceShifts
  exact hRep.map_zero
theorem semigroupOp_onEuclidean (L : LimitInputs τ h) (t : ℝ≥0) :
    semigroupOp (onEuclidean (ReflectionPositivity.ReconstructionComplements.jointMeasure τ h)) t =
      ((timeShift τ h t : PhysicalSpace τ h →L[ℂ] PhysicalSpace τ h) :
        PhysicalSpace τ h →ₗ[ℂ] PhysicalSpace τ h) := by
  have hm : Measurable fun p : MomSpace => ((Real.exp (-(t : ℝ) * energyCoord p) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_energyCoord.const_mul _))
  have hb : ∃ C : ℝ, ∀ x ∈ EuclideanFunctionals.nonnegEnergySet.1,
      ‖((Real.exp (-(t : ℝ) * energyCoord x) : ℝ) : ℂ)‖ ≤ C := by
    refine ⟨1, fun x hx => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := mul_nonneg t.2 hx
    simpa using this
  unfold semigroupOp
  rw [boundedIntegralOn_onEuclidean L.basicFacts L.integralLaws _ _ hm hb]
  have hfun : (fun y : Fin 4 → ℝ =>
      EuclideanFunctionals.nonnegEnergySet.1.indicator
        (fun p : MomSpace => ((Real.exp (-(t : ℝ) * energyCoord p) : ℝ) : ℂ)) (toEuclidean y)) =
      truncatedPhase t 0 := by
    funext y
    by_cases hy : 0 ≤ y 0
    · rw [indicator_of_mem (show toEuclidean y ∈ EuclideanFunctionals.nonnegEnergySet.1 from hy),
        truncatedPhase, indicator_of_mem (show y ∈ {y : Fin 4 → ℝ | 0 ≤ y 0} from hy), heatPhase]
      simp [energyCoord, spaceDot, SeparatedTupleFunctionals.dotProd]
    · rw [indicator_of_notMem (show toEuclidean y ∉ EuclideanFunctionals.nonnegEnergySet.1 from hy),
        truncatedPhase, indicator_of_notMem (show y ∉ {y : Fin 4 → ℝ | 0 ≤ y 0} from hy)]
  rw [hfun, ← timeShift_mul_spaceShift L, spaceShift_zero L, mul_one]
theorem spatialShiftOp_onEuclidean (L : LimitInputs τ h) (x : R4) :
    spatialShiftOp (onEuclidean (ReflectionPositivity.ReconstructionComplements.jointMeasure τ h)) x =
      ((spaceShift τ h (LimitConventions.spacePart x) : PhysicalSpace τ h →L[ℂ] PhysicalSpace τ h) :
        PhysicalSpace τ h →ₗ[ℂ] PhysicalSpace τ h) := by
  set E := ReflectionPositivity.ReconstructionComplements.jointMeasure τ h with hE
  have hR : E.CalculusLaws := L.integralLaws 4 _ E
  have hS : E.SupportLaws := L.concentration 4 _ E
  have hcoord : ∀ i : Fin 4, Measurable fun p : MomSpace => p i := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable
  have hm : Measurable fun p : MomSpace =>
      Complex.exp (Complex.I * (spatialDot x p : ℂ)) := by
    refine Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp ?_))
    exact Finset.measurable_sum _ fun j _ => (hcoord j.succ).const_mul _
  have hnorm : ∀ r : ℝ, ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := fun r => by
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I r
  have hb : ∃ C : ℝ, ∀ p : MomSpace,
      ‖Complex.exp (Complex.I * (spatialDot x p : ℂ))‖ ≤ C :=
    ⟨1, fun p => (hnorm _).le⟩
  unfold spatialShiftOp
  rw [boundedIntegral_onEuclidean L.basicFacts L.integralLaws _ hm hb]
  have hcar := L.supportClaim.1
  have hm' : Measurable fun y : Fin 4 → ℝ =>
      Complex.exp (Complex.I * (spatialDot x (toEuclidean y) : ℂ)) :=
    hm.comp measurable_toEuclidean
  have hb' : IsBoundedComplexFn fun y : Fin 4 → ℝ =>
      Complex.exp (Complex.I * (spatialDot x (toEuclidean y) : ℂ)) :=
    ⟨1, fun y => (hnorm _).le⟩
  have hcong := boundedIntegralOp_congr E hR hm'
    (measurable_truncatedPhase 0 (LimitConventions.spacePart x)) hb'
    (isBoundedComplexFn_truncatedPhase 0 (LimitConventions.spacePart x))
    (eq_zero_of_agree_on_nonneg E hS hcar hm'
      (measurable_truncatedPhase 0 (LimitConventions.spacePart x)) fun y hy => by
      rw [truncatedPhase, indicator_of_mem (show y ∈ {y : Fin 4 → ℝ | 0 ≤ y 0} from hy), heatPhase]
      have e : spaceDot (LimitConventions.spacePart x) (spatialPart y) =
          spatialDot x (toEuclidean y) := rfl
      rw [e]
      simp)
  rw [hcong, ← timeShift_mul_spaceShift L, timeShift_zero L, one_mul]
theorem octahedralUnitary_timeShift_comm (L : LimitInputs τ h) {w : SpaceVec ≃ₗ[ℝ] SpaceVec}
    (hI : IntertwiningClaim τ h w) (t : ℝ≥0) (ψ : PhysicalSpace τ h) :
    octahedralUnitary τ h w (timeShift τ h t ψ) =
      timeShift τ h t (octahedralUnitary τ h w ψ) := by
  obtain ⟨-, ⟨F, hF, -, hc⟩, -, -⟩ := hI
  obtain ⟨-, -, -, -, -, ⟨F₀, hF₀, -, hT⟩, -⟩ := L.timeSemigroup
  obtain rfl := spectralResolution_unique L.generators hF hF₀
  have h1 := hc t
  rw [← hT t] at h1
  exact ((unboundedOperator_eq_iff _ _).1 h1).2 ⟨ψ, trivial⟩ ⟨ψ, trivial⟩ rfl
theorem energyFn_vacuum_eq_zero (L : LimitInputs τ h)
    (hOp : ReflectionPositivity.PairMeasureOperators.pairHamiltonian τ h =
      (ReflectionPositivity.ReconstructionComplements.jointMeasure τ h).coordinateOp 0) :
    ∃ hΩ : ReflectionPositivity.Reconstruction.vacuum τ h ∈
        (onEuclidean (ReflectionPositivity.ReconstructionComplements.jointMeasure τ h)).fnDomain
          energyFn,
      (onEuclidean (ReflectionPositivity.ReconstructionComplements.jointMeasure τ h)).borelFnOp
        energyFn ⟨ReflectionPositivity.Reconstruction.vacuum τ h, hΩ⟩ = 0 := by
  obtain ⟨-, -, -, -, -, -, -, hV⟩ := L.timeSemigroup
  have e : ReflectionPositivity.PairMeasureOperators.pairHamiltonian τ h =
      (ReflectionPositivity.ReconstructionComplements.jointMeasure τ h).functionalCalculus
        fun y => energyFn (toEuclidean y) := hOp
  rw [e] at hV
  obtain ⟨hψ, h0⟩ := hV
  exact mem_fnDomain_of_spectralIntegral_eq_zero L.basicFacts L.integralLaws L.boundedCalculus _
    (Complex.measurable_ofReal.comp measurable_energyCoord) _ hψ h0
theorem isUnitaryMap_inv_eq_symm {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (V : H ≃ₗᵢ[ℂ] H)
    (hU : EuclideanSpectral.IsUnitaryMap (V.toLinearEquiv : H →ₗ[ℂ] H))
    (ψ : H) : hU.inv ψ = V.symm ψ := by
  apply V.injective
  rw [V.apply_symm_apply]
  exact (LinearEquiv.ofBijective _ hU.bijective).apply_symm_apply ψ
end Limit
theorem exists_osData
    (hF : EuclideanSpectral.ProjMeasureBasicFacts)
    (hR : SpectralTheory.SpectralIntegralLawsHold)
    (hC : EuclideanSpectral.ProjMeasureBoundedCalculus)
    (hS : SpectralSupport.ConcentratedOnSupportTheorem)
    (hD : GeneratorsAndFlows.GeneratorFlowTheorem)
    (hRec : ReflectionPositivity.LimitReconstruction.LimitReconstructionTheorem)
    (hCmp : ReflectionPositivity.ReconstructionComplements.ComplementsTheorem)
    (hT : TupleRules.TupleSpanActionRules)
    (Dt : ReflectionPositivity.AxisMirror.MirrorData) (T : LimitConventions.ApproxTriple Dt.L)
    (S : ConnFamily) (τ : SeparatedTuples.TupleFunctional)
    (hτ : τ.toFun = onSepTuples (centeredFn S))
    (hB : ReflectionPositivity.ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM Dt T)
    (hRP : LimitConventions.ApproxTriple.IsReflPos T)
    (hL : LimitConventions.ApproxTriple.ConvergesTo T
      (onSepTuples (centeredFn S))) :
    ∃ h : HilbertSpaceBasics.IsPosSemidef (ReflectionPositivity.TupleForm.reflectionForm τ),
      ∃ sys : OSData (PhysicalSpace τ h) S,
        sys.pvm =
            onEuclidean (ReflectionPositivity.ReconstructionComplements.jointMeasure τ h) ∧
          (ReflectionPositivity.ReconstructionComplements.jointMeasure τ h).IsConcentratedOn
            ReflectionPositivity.ReconstructionComplements.forwardCone := by
  have hLτ : LimitConventions.ApproxTriple.ConvergesTo T τ := by
    have e : (⇑τ : SeparatedTuples.SepTuple → ℝ) = onSepTuples (centeredFn S) := hτ
    rw [e]
    exact hL
  obtain ⟨-, -, h, -, hSem, hTr, -⟩ := hRec Dt T τ hB hRP hLτ
  obtain ⟨hCF, hAll⟩ := hCmp
  obtain ⟨h', -, hOp, hCar, hMar, hU⟩ := hAll Dt T τ hB hRP hLτ
  have L : LimitInputs τ h := ⟨hF, hR, hC, hS, hD, hCar, hSem, hTr⟩
  obtain ⟨-, hTT, -⟩ := hSem
  obtain ⟨-, hST, -⟩ := hTr
  choose wc hwc hmap₀ using exists_octahedral_of_timeStabilizer hCF
  have hmap : ∀ (w : timeStabilizer) (x : R4),
      (w : EuclidMotion) x = timeExtension (wc w) x := hmap₀
  have hUw := fun w => hU (wc w) (hwc w)
  refine ⟨h,
    { cls := freeSepClass τ h
      inner_cls := inner_freeSepClass τ h hT S hτ
      denseRange_cls := denseRange_freeSepClass τ h
      pvm := onEuclidean (ReflectionPositivity.ReconstructionComplements.jointMeasure τ h)
      pvm_negEnergy := ?_
      hamiltonian_vac := ?_
      semigroup_cls := ?_
      shift_cls := ?_
      rotOp := fun w => ((octahedralUnitary τ h (wc w)).toLinearEquiv :
        PhysicalSpace τ h →ₗ[ℂ] PhysicalSpace τ h)
      rotOp_unitary := fun w =>
        ⟨(octahedralUnitary τ h (wc w)).bijective, (octahedralUnitary τ h (wc w)).norm_map⟩
      rotOp_cls := ?_
      rotOp_comm_semigroup := ?_
      rotOp_conj_shift := ?_ }, rfl, hMar.2⟩
  · apply onEuclidean_eq_zero
    have e : borelPreimage EuclideanFunctionals.negEnergySet =
        ⟨ReflectionPositivity.ReconstructionComplements.nonnegEnergy.1ᶜ,
          ReflectionPositivity.ReconstructionComplements.nonnegEnergy.2.compl⟩ :=
      Subtype.ext (Set.ext fun y => show y 0 < 0 ↔ ¬ 0 ≤ y 0 from not_le.symm)
    rw [e]
    exact hCar.1
  · rw [freeSepClass_emptyElt τ h]
    exact energyFn_vacuum_eq_zero L hOp.1
  · intro t ht F
    lift t to ℝ≥0 using ht
    rw [semigroupOp_onEuclidean L t, classOrZero_actFree τ h hT _
      (transl_image_upperHalf_subset (by simp [PeriodicLattice.coordVec])) F, freeSepClass_apply]
    exact hTT t (toPositiveSpan F)
  · intro v hv F
    have e : ReflectionPositivity.Reconstruction.embedSpatial (LimitConventions.spacePart v) = v := by
      have hv' : v 3 = 0 := hv
      funext i
      fin_cases i
      · rfl
      · rfl
      · rfl
      · exact hv'.symm
    have h1 := hST (LimitConventions.spacePart v) (toPositiveSpan F)
    rw [e] at h1
    rw [spatialShiftOp_onEuclidean L v, classOrZero_actFree τ h hT _
      (transl_image_upperHalf_subset (le_of_eq (show (0 : ℝ) = v 3 from (show v 3 = 0 from hv).symm))) F,
      freeSepClass_apply]
    exact h1
  · intro w F
    have h1 := (hUw w).1.2 (toPositiveSpan F)
    have hfun : (⇑(timeExtension (wc w)) : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace) =
        ⇑(w : EuclidMotion) := funext fun x => (hmap w x).symm
    rw [classOrZero_actFree τ h hT _ (timeStabilizer_image_upperHalf_subset hT w.2) F,
      freeSepClass_apply, ← hfun]
    exact h1
  · intro w t ht
    lift t to ℝ≥0 using ht
    rw [semigroupOp_onEuclidean L t]
    exact LinearMap.ext fun ψ => octahedralUnitary_timeShift_comm L (hUw w).2 t ψ
  · intro w v _
    rw [spatialShiftOp_onEuclidean L, spatialShiftOp_onEuclidean L]
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨-, -, -, hconj⟩ := (hUw w).2
    have h1 := congrArg (fun B : PhysicalSpace τ h →L[ℂ] PhysicalSpace τ h => B ψ)
      (hconj (LimitConventions.spacePart v))
    have e : LimitConventions.spacePart ((w : EuclidMotion) v) =
        wc w (LimitConventions.spacePart v) := by
      rw [hmap w v]
      simp [timeExtension]
    rw [e]
    refine Eq.trans ?_ h1
    simp only [LinearMap.comp_apply]
    rw [isUnitaryMap_inv_eq_symm]
    rfl
end YangMills.Construction.FirstPassageSeqs.BoundedApprox
end
end
section
noncomputable section
namespace YangMills.Construction.FirstPassageSeqs
open EuclideanFunctionals MeasureTheory
open LimitConventions (ApproxTriple)
open ReflectionPositivity.ApproximatingSequences.LatticeApproximation (IsBoundedForSomeM)
namespace BoundedApprox
theorem exists_withRecon_coneCondition
    (hSame : DefinitionComparison.TwoDefinitionsAgree)
    (hSup : SpectralSupport.ConcentratedOnSupportTheorem)
    (c : SharpScale) (S : ConnFamily) (C : ℕ → ℝ → ℝ → ℝ) (hLB : HasClusterBounds S c C)
    (h₁ : IsSymmMultilinReal S) (h₂ : IsLatticeInvariant S)
    (h₃ : IsOSPositive S)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (sys : OSData H S)
    (E : SpectralTheory.ProjectionMeasure 4 H)
    (hE : sys.pvm = onEuclidean E)
    (hP : E.IsConcentratedOn ReflectionPositivity.ReconstructionComplements.forwardCone) :
    ∃ e : EuclidFunctionalWithRecon c S, e.clusterConst = C ∧ e.ConeCondition := by
  let τ₀ : SymmEuclidFunctional c S :=
    { isSymmMultilinReal := h₁
      isLatticeInvariant := h₂
      isOSPositive := h₃
      clusterConst := C
      hasClusterBounds := hLB
      space := H
      osData := sys }
  obtain ⟨-, -, hr, -⟩ := hSame c S
  obtain ⟨r⟩ := hr τ₀
  refine ⟨r.toRecon, rfl, ?_⟩
  have hOne := r.corresponds.measure_eq
  have hzero : onEuclidean E (energyBelowMom 0) = 0 := by
    refine onEuclidean_eq_zero E ?_
    have hR := hSup 4 H E
    refine hR.vanishesOn_of_subset _ _ ?_ hP
    intro y hy hpy
    have hy' : energyCoord (toEuclidean y) < |momCoord 0 (toEuclidean y)| := hy
    have hp := hpy 0
    exact absurd hp (not_le.2 hy')
  have hval := hOne (energyBelowMom 0)
  change ⇑(sys.pvm (energyBelowMom 0)) = _ at hval
  rw [hE, hzero] at hval
  have hset : SettingsComparison.euclideanToCoords (energyBelowMom 0) =
      SpectralPoint.belowAbsMomentum (SpectralPoint.basisVec 0) := by
    refine Subtype.ext ?_
    ext y
    simp only [SettingsComparison.euclideanToCoords, energyBelowMom,
      SpectralPoint.belowAbsMomentum, SpectralPoint.dot3, SpectralPoint.basisVec,
      SpectralPoint.energyOf, SpectralPoint.momentumOf, energyCoord, momCoord]
    simp [Pi.single_apply]
  rw [hset] at hval
  refine ContinuousLinearMap.ext fun ψ => ?_
  exact (congrFun hval ψ).symm
end BoundedApprox
open BoundedApprox in
theorem boundedApproximationLimitIsEuclidean_holds
    (hHalf : ReflectionPositivity.LimitSymmetries.LimitHasSymmetries)
    (hT : TupleRules.TupleSpanActionRules)
    (hVal : TensorValues.EntrywiseLinearValues)
    (hSame : DefinitionComparison.TwoDefinitionsAgree)
    (hSup : SpectralSupport.ConcentratedOnSupportTheorem)
    (hAny : ReconUnique.statement)
    (hF : EuclideanSpectral.ProjMeasureBasicFacts)
    (hR : SpectralTheory.SpectralIntegralLawsHold)
    (hC : EuclideanSpectral.ProjMeasureBoundedCalculus)
    (hD : GeneratorsAndFlows.GeneratorFlowTheorem)
    (hRec : ReflectionPositivity.LimitReconstruction.LimitReconstructionTheorem)
    (hCmp : ReflectionPositivity.ReconstructionComplements.ComplementsTheorem) :
    BoundedApproximationLimitIsEuclidean := by
  intro Dt T S τ hτ hB hRP hL
  have hInvPos := invariant_and_reflectionPositive hHalf hT Dt T S hB hRP hL
  refine ⟨hInvPos.1, hInvPos.2, fun c C hLB => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ :=
    symmMultilin_latticeInvariant_osPositive hHalf hT hVal Dt T S hB hRP hL hInvPos.1 hInvPos.2
  obtain ⟨hpos, sys, hE, hP⟩ := exists_osData hF hR hC hSup hD hRec hCmp hT Dt T S τ hτ hB hRP hL
  obtain ⟨e₀, he₀, hcone⟩ := exists_withRecon_coneCondition hSame hSup c S C hLB h₁ h₂ h₃ sys _ hE hP
  refine ⟨⟨e₀, he₀⟩, fun e => ?_⟩
  obtain ⟨-, hnull, -⟩ := hAny c S e₀ e.space e.recon
  exact (hnull.1 _).2 hcone
end YangMills.Construction.FirstPassageSeqs
end
end
