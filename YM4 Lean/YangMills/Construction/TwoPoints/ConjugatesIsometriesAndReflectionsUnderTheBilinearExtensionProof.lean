import YangMills.Construction.EuclideanFunctionals.ExpansionTranslationsContinuityAndSmearingOfTheInsertionValueProof
import YangMills.Construction.Continuum.TheRecursionOfTheConnectedFunctionsIsTriangular
import YangMills.Construction.EuclideanFunctionals.TuplesSpansAndActionsProof
import YangMills.Construction.RotationInvariance.ScalarProductsOfBumpVectorsAtRealPointsProof
import YangMills.Construction.TwoPoints.ConjugatesIsometriesAndReflectionsUnderTheBilinearExtension
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.PairFunctions.ConjIsometryReflection
open EuclideanFunctionals (R4 FreeSep toFree freeMul)
open ComplexTestFunctions (ComplexValued)
open TwoPoints (compactC1Complex DisjointSupports)
open PeriodicGibbsLimits (hyperplaneReflection reflectedConj hyperplaneReflection_hyperplaneReflection
  hyperplaneReflection_actFn euclidDot_hyperplaneReflection)
theorem neg_left_mem_sepPairs {u v : R4 → ℝ} (hm : [u, v] ∈ sepPairs) : [-u, v] ∈ sepPairs := by
  have e := linComb_mem_sepPairs (-1) 0 hm hm
  have e' : (-1 : ℝ) • u + (0 : ℝ) • u = -u := by simp
  rwa [e'] at e
theorem evalPair_neg_left {B : sepPairs → ℝ} (hB : IsBilinearOnPairs B) {u v : R4 → ℝ}
    (hm : [u, v] ∈ sepPairs) : evalPair B (-u) v = -evalPair B u v := by
  have e := (hB (-1) 0 u u v hm hm).1
  have e' : (-1 : ℝ) • u + (0 : ℝ) • u = -u := by simp
  rw [e'] at e
  simpa using e
theorem evalPair_neg_right {B : sepPairs → ℝ} (hB : IsBilinearOnPairs B) {u v : R4 → ℝ}
    (hm : [u, v] ∈ sepPairs) : evalPair B v (-u) = -evalPair B v u := by
  have e := (hB (-1) 0 u u v hm hm).2
  have e' : (-1 : ℝ) • u + (0 : ℝ) • u = -u := by simp
  rw [e'] at e
  simpa using e
theorem evalPair_zero_left {B : sepPairs → ℝ} (hB : IsBilinearOnPairs B) {u v : R4 → ℝ}
    (hm : [u, v] ∈ sepPairs) : evalPair B 0 v = 0 := by
  have e := (hB 0 0 u u v hm hm).1
  simpa using e
theorem evalPair_zero_right {B : sepPairs → ℝ} (hB : IsBilinearOnPairs B) {u v : R4 → ℝ}
    (hm : [u, v] ∈ sepPairs) : evalPair B v 0 = 0 := by
  have e := (hB 0 0 u u v hm hm).2
  simpa using e
theorem rePart_conjFun (f : ComplexValued) :
    ComplexTestFunctions.rePart (TwoPoints.conjFun f) = ComplexTestFunctions.rePart f := by
  funext x
  simp [ComplexTestFunctions.rePart, TwoPoints.conjFun]
theorem imPart_conjFun (f : ComplexValued) :
    ComplexTestFunctions.imPart (TwoPoints.conjFun f) = -ComplexTestFunctions.imPart f := by
  funext x
  simp [ComplexTestFunctions.imPart, TwoPoints.conjFun]
theorem complexExtension_conjFun {B : sepPairs → ℝ} (hB : IsBilinearOnPairs B) {f g : ComplexValued}
    (hf : f ∈ compactC1Complex) (hg : g ∈ compactC1Complex) (hd : DisjointSupports f g) :
    complexExtension B (TwoPoints.conjFun f) (TwoPoints.conjFun g) =
      conj (complexExtension B f g) := by
  obtain ⟨p₁, p₂, p₃, p₄⟩ := parts_mem_sepPairs hf hg hd
  have n₂ : evalPair B (-ComplexTestFunctions.imPart f) (-ComplexTestFunctions.imPart g) =
      evalPair B (ComplexTestFunctions.imPart f) (ComplexTestFunctions.imPart g) := by
    rw [evalPair_neg_left hB (swap_mem_sepPairs (neg_left_mem_sepPairs (swap_mem_sepPairs p₂))),
      evalPair_neg_right hB (swap_mem_sepPairs p₂), neg_neg]
  rw [complexExtension_eq, complexExtension_eq, rePart_conjFun, rePart_conjFun,
    imPart_conjFun, imPart_conjFun, n₂, evalPair_neg_right hB (swap_mem_sepPairs p₃),
    evalPair_neg_left hB p₄]
  simp only [map_add, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_neg]
  ring
theorem realPartForm_isDisjointForm {B : sepPairs → ℝ} (hS : IsSymmOnPairs B)
    (hB : IsBilinearOnPairs B) : TwoPoints.IsDisjointForm (realPartForm B) := by
  refine ⟨fun f hf g hg hd => ?_, fun a₁ a₂ f₁ g₁ f₂ g₂ g hg d₁ d₂ => ?_⟩
  · exact hS _ _ (parts_mem_sepPairs hf.1 hg.1 hd).1
  · have e : ComplexTestFunctions.rePart (a₁ • f₁ + a₂ • f₂) =
        a₁ • ComplexTestFunctions.rePart f₁ + a₂ • ComplexTestFunctions.rePart f₂ := by
      funext x
      simp [ComplexTestFunctions.rePart]
    simp only [realPartForm, e]
    exact (hB a₁ a₂ _ _ _ (parts_mem_sepPairs g₁.1 hg.1 d₁).1 (parts_mem_sepPairs g₂.1 hg.1 d₂).1).1
theorem complexExtension_actFn {B : sepPairs → ℝ} (r : EuclideanFunctionals.EuclidMotion)
    (hr : ∀ u v : R4 → ℝ, [u, v] ∈ sepPairs →
      evalPair B (r.actFn u) (r.actFn v) = evalPair B u v)
    {f g : ComplexValued} (hf : f ∈ compactC1Complex) (hg : g ∈ compactC1Complex)
    (hd : DisjointSupports f g) :
    complexExtension B (r.actFn f) (r.actFn g) = complexExtension B f g := by
  obtain ⟨p₁, p₂, p₃, p₄⟩ := parts_mem_sepPairs hf hg hd
  have er : ∀ w : ComplexValued, ComplexTestFunctions.rePart (r.actFn w) =
      r.actFn (ComplexTestFunctions.rePart w) :=
    fun _ => rfl
  have ei : ∀ w : ComplexValued, ComplexTestFunctions.imPart (r.actFn w) =
      r.actFn (ComplexTestFunctions.imPart w) :=
    fun _ => rfl
  rw [complexExtension_eq, complexExtension_eq, er, er, ei, ei, hr _ _ p₁, hr _ _ p₂, hr _ _ p₃,
    hr _ _ p₄]
def IsC1cOnPositiveSide (n : R4) (a : R4 → ℝ) : Prop :=
  SeparatedTuples.IsC1c a ∧
    tsupport a ⊆ {x : R4 | 0 < TwoPoints.euclidDot n x}
theorem continuous_hyperplaneReflection (n : R4) (hn : TwoPoints.euclidNorm n = 1) :
    Continuous fun x : R4 => hyperplaneReflection n hn 0 x :=
  (LinearMap.continuous_of_finiteDimensional _).add continuous_const
theorem tsupport_actFn_reflect_subset_image (n : R4) (hn : TwoPoints.euclidNorm n = 1)
    {a : R4 → ℝ} (ha : IsCompact (tsupport a)) :
    tsupport ((hyperplaneReflection n hn 0).actFn a) ⊆
      (fun x => hyperplaneReflection n hn 0 x) '' tsupport a := by
  refine closure_minimal (fun x hx => ?_) (ha.image (continuous_hyperplaneReflection n hn)).isClosed
  rw [hyperplaneReflection_actFn] at hx
  exact ⟨hyperplaneReflection n hn 0 x, subset_tsupport _ hx,
    hyperplaneReflection_hyperplaneReflection n hn 0 x⟩
theorem isC1c_actFn_reflect {n : R4} (hn : TwoPoints.euclidNorm n = 1) {a : R4 → ℝ}
    (ha : IsC1cOnPositiveSide n a) :
    SeparatedTuples.IsC1c ((hyperplaneReflection n hn 0).actFn a) := by
  have hs := tsupport_actFn_reflect_subset_image n hn ha.1.2
  refine ⟨?_, (ha.1.2.image (continuous_hyperplaneReflection n hn)).of_isClosed_subset
    (isClosed_tsupport _) hs⟩
  rw [hyperplaneReflection_actFn]
  have hc : ContDiff ℝ 1 fun x : R4 => hyperplaneReflection n hn 0 x :=
    (LinearMap.toContinuousLinearMap (hyperplaneReflection n hn 0).lin).contDiff.add contDiff_const
  exact ha.1.1.comp hc
theorem tsupport_actFn_reflect_subset_neg {n : R4} (hn : TwoPoints.euclidNorm n = 1)
    {a : R4 → ℝ} (ha : IsC1cOnPositiveSide n a) :
    tsupport ((hyperplaneReflection n hn 0).actFn a) ⊆
      {x : R4 | TwoPoints.euclidDot n x < 0} := by
  refine (tsupport_actFn_reflect_subset_image n hn ha.1.2).trans ?_
  rintro _ ⟨z, hz, rfl⟩
  have h₁ := euclidDot_hyperplaneReflection n hn 0 z
  have h₂ : 0 < TwoPoints.euclidDot n z := ha.2 hz
  change TwoPoints.euclidDot n (hyperplaneReflection n hn 0 z) < 0
  linarith
theorem disjoint_open_halfspaces (n : R4) :
    Disjoint {x : R4 | TwoPoints.euclidDot n x < 0}
      {x : R4 | 0 < TwoPoints.euclidDot n x} :=
  Set.disjoint_left.2 fun x h₁ h₂ => lt_asymm (a := TwoPoints.euclidDot n x) h₁ h₂
theorem singleton_mem_sepIn {O : Set R4} {a : R4 → ℝ}
    (ha : SeparatedTuples.IsC1c a) (hO : tsupport a ⊆ O) :
    [a] ∈ EuclideanFunctionals.sepIn O := by
  refine ⟨(SeparatedTuplesR4.isDisjointTuple_iff_mem_separatedAll _ _).1
    ⟨fun g hg => ?_, by simp⟩, fun g hg => ?_⟩
  · rw [List.mem_singleton.1 hg]
    exact ha
  · have e : (ReflectionPositivity.AxisMirror.Ambient.closedSupport
        EuclideanFunctionals.defaultMirrorData
        ReflectionPositivity.AxisMirror.Ambient.euclidean a : Set R4) = tsupport a :=
      SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
    rw [List.mem_singleton.1 hg]
    exact e.subset.trans hO
theorem combSupp_subset {O : Set R4} {F : FreeSep}
    (hF : F ∈ EuclideanFunctionals.finCombIn O) :
    EuclideanFunctionals.combSupp F ⊆ O := by apply _root_.YangMills.Construction.EuclideanFunctionals.TupleRules.combSupp_subset <;> assumption
theorem toFree_mem_finCombIn {O : Set R4} {X : EuclideanFunctionals.FnList}
    (hX : X ∈ EuclideanFunctionals.sepIn O) :
    toFree X ∈ EuclideanFunctionals.finCombIn O := by apply _root_.YangMills.Construction.EuclideanFunctionals.TupleRules.toFree_mem_finCombIn <;> assumption
theorem freeConj_toFree {X : EuclideanFunctionals.FnList}
    (hX : X ∈ EuclideanFunctionals.sepAll) :
    EuclideanFunctionals.freeConj (toFree X) = toFree X := by apply _root_.YangMills.Construction.EuclideanFunctionals.MollifierInnerAtRealPoints.freeConj_toFree <;> assumption
theorem freeConj_add_I_smul (A B : FreeSep) :
    EuclideanFunctionals.freeConj (A + Complex.I • B) =
      EuclideanFunctionals.freeConj A +
        (-Complex.I) • EuclideanFunctionals.freeConj B := by
  ext X
  simp [EuclideanFunctionals.freeConj]
theorem actFree_toFree_singleton (r : EuclideanFunctionals.EuclidMotion) {a : R4 → ℝ}
    (ha : [a] ∈ EuclideanFunctionals.sepAll) :
    r.actFree (toFree [a]) = toFree [r.actFn a] :=
  EuclideanFunctionals.liftLin_toFree _ ⟨[a], ha⟩
theorem freeMul_toFree {X Y : EuclideanFunctionals.FnList}
    (hX : X ∈ EuclideanFunctionals.sepAll) (hY : Y ∈ EuclideanFunctionals.sepAll) :
    freeMul (toFree X) (toFree Y) = toFree (EuclideanFunctionals.listAppend X Y) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TensorCompRules.freeMul_toFree <;> assumption
theorem centeredFnFree_freeMul_singletons (hT : TestSpaces.CumulantRecursionTriangular)
    (S : EuclideanFunctionals.ConnFamily) {c b : R4 → ℝ} (hc : [c] ∈ EuclideanFunctionals.sepAll)
    (hb : [b] ∈ EuclideanFunctionals.sepAll) (hm : [c, b] ∈ sepPairs) :
    EuclideanFunctionals.centeredFnFree S (freeMul (toFree [c]) (toFree [b])) =
      (evalPair (S.fn 2 le_rfl) c b : ℂ) := by
  have hs : [c, b] ∈ EuclideanFunctionals.sepAll := Set.mem_iUnion.2 ⟨2, hm⟩
  rw [freeMul_toFree hc hb]
  have h₁ := EuclideanFunctionals.liftLin_toFree
    (fun X : EuclideanFunctionals.sepAll =>
      (EuclideanFunctionals.centeredFn S X : ℂ)) ⟨[c, b], hs⟩
  have h₂ := (hT.2.1.1 S).2.2.2 ((TestSpaces.sepTupleListEquiv _ 2).symm ⟨[c, b], hm⟩)
  have e : TestSpaces.sepTupleListEquiv EuclideanFunctionals.defaultMirrorData 2
      ((TestSpaces.sepTupleListEquiv _ 2).symm ⟨[c, b], hm⟩) = ⟨[c, b], hm⟩ :=
    Equiv.apply_symm_apply _ _
  simp only [TestSpaces.centredOfConnFamily, TestSpaces.connFamilyOnTuples, e] at h₂
  have h₃ := evalPair_of_mem (S.fn 2 le_rfl) hm
  exact h₁.trans (congrArg (fun t : ℝ => (t : ℂ)) (h₂.trans h₃.symm))
theorem parts_isC1cOnPositiveSide {n : R4} {f : ComplexValued}
    (hf : f ∈ TwoPoints.cc1In {x : R4 | 0 < TwoPoints.euclidDot n x}) :
    IsC1cOnPositiveSide n (ComplexTestFunctions.rePart f) ∧
      IsC1cOnPositiveSide n (ComplexTestFunctions.imPart f) := by
  have hc : f ∈ compactC1Complex := ⟨hf.1, hf.2.1, Set.subset_univ _⟩
  exact ⟨⟨rePart_mem_isC1c hc, (ComplexTupleComponents.tsupport_rePart_subset f).trans hf.2.2⟩,
    ⟨imPart_mem_isC1c hc, (ComplexTupleComponents.tsupport_imPart_subset f).trans hf.2.2⟩⟩
theorem reflect_pair_mem_sepPairs {n : R4} (hn : TwoPoints.euclidNorm n = 1) {a b : R4 → ℝ}
    (ha : IsC1cOnPositiveSide n a) (hb : IsC1cOnPositiveSide n b) :
    [(hyperplaneReflection n hn 0).actFn a, b] ∈ sepPairs :=
  (mem_sepPairs_iff _ _).2 ⟨isC1c_actFn_reflect hn ha, hb.1,
    (disjoint_open_halfspaces n).mono (tsupport_actFn_reflect_subset_neg hn ha) hb.2⟩
theorem rePart_reflectFun_conjFun {n : R4} (hn : TwoPoints.euclidNorm n = 1)
    (f : ComplexValued) :
    ComplexTestFunctions.rePart (TwoPoints.reflectFun n (TwoPoints.conjFun f)) =
      (hyperplaneReflection n hn 0).actFn (ComplexTestFunctions.rePart f) := by
  rw [hyperplaneReflection_actFn]
  funext x
  simp [ComplexTestFunctions.rePart, TwoPoints.reflectFun, TwoPoints.conjFun,
    PeriodicGibbsLimits.hyperplaneReflection_zero_apply]
theorem imPart_reflectFun_conjFun {n : R4} (hn : TwoPoints.euclidNorm n = 1)
    (f : ComplexValued) :
    ComplexTestFunctions.imPart (TwoPoints.reflectFun n (TwoPoints.conjFun f)) =
      -(hyperplaneReflection n hn 0).actFn (ComplexTestFunctions.imPart f) := by
  rw [hyperplaneReflection_actFn]
  funext x
  simp [ComplexTestFunctions.imPart, TwoPoints.reflectFun, TwoPoints.conjFun,
    PeriodicGibbsLimits.hyperplaneReflection_zero_apply]
theorem complexExtension_reflectFun_conjFun {B : sepPairs → ℝ} (hB : IsBilinearOnPairs B)
    {n : R4} (hn : TwoPoints.euclidNorm n = 1) {f : ComplexValued}
    (hp : IsC1cOnPositiveSide n (ComplexTestFunctions.rePart f))
    (hq : IsC1cOnPositiveSide n (ComplexTestFunctions.imPart f)) :
    complexExtension B (TwoPoints.reflectFun n (TwoPoints.conjFun f)) f =
      ((evalPair B ((hyperplaneReflection n hn 0).actFn (ComplexTestFunctions.rePart f))
          (ComplexTestFunctions.rePart f) : ℝ) : ℂ) +
        ((evalPair B ((hyperplaneReflection n hn 0).actFn (ComplexTestFunctions.imPart f))
          (ComplexTestFunctions.imPart f) : ℝ) : ℂ) +
        Complex.I * (((evalPair B ((hyperplaneReflection n hn 0).actFn
            (ComplexTestFunctions.rePart f)) (ComplexTestFunctions.imPart f) : ℝ) : ℂ) -
          ((evalPair B ((hyperplaneReflection n hn 0).actFn
            (ComplexTestFunctions.imPart f)) (ComplexTestFunctions.rePart f) : ℝ) : ℂ)) := by
  rw [complexExtension_eq, rePart_reflectFun_conjFun hn, imPart_reflectFun_conjFun hn,
    evalPair_neg_left hB (reflect_pair_mem_sepPairs hn hq hq),
    evalPair_neg_left hB (reflect_pair_mem_sepPairs hn hq hp)]
  push_cast
  ring
theorem complexTuple_singleton_of_real {f : ComplexValued} (hr : ∀ x, (f x).im = 0) :
    EuclideanFunctionals.complexTuple (fun _ : Fin 1 => f) =
      toFree [ComplexTestFunctions.rePart f] := by
  rw [EuclideanFunctionals.complexTuple,
    if_pos (show ∀ _ : Fin 1, EuclideanFunctionals.IsRealValued f from fun _ => hr)]
  simp only [List.ofFn_succ, List.ofFn_zero]
  rfl
theorem complexTuple_singleton_of_not_real {f : ComplexValued} (hr : ¬∀ x, (f x).im = 0) :
    EuclideanFunctionals.complexTuple (fun _ : Fin 1 => f) =
      toFree [ComplexTestFunctions.rePart f] +
        Complex.I • toFree [ComplexTestFunctions.imPart f] := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.singleComponent_of_not_real <;> assumption
theorem reflection_positivity_identity (hT : TestSpaces.CumulantRecursionTriangular)
    {B : sepPairs → ℝ} (hB : IsBilinearOnPairs B) (S : EuclideanFunctionals.ConnFamily)
    (hS : S.fn 2 le_rfl = B) (n : R4) (hn : TwoPoints.euclidNorm n = 1)
    (f : ComplexValued)
    (hf : f ∈ TwoPoints.cc1In {x : R4 | 0 < TwoPoints.euclidDot n x}) :
    let F : FreeSep := EuclideanFunctionals.complexTuple fun _ : Fin 1 => f
    let G : FreeSep := reflectedConj n hn 0 F
    F ∈ EuclideanFunctionals.finCombIn {x : R4 | 0 < TwoPoints.euclidDot n x} ∧
      EuclideanFunctionals.MulDefined G F ∧
      EuclideanFunctionals.centeredFnFree S (freeMul G F) =
        complexExtension B (TwoPoints.reflectFun n (TwoPoints.conjFun f)) f := by
  subst hS
  intro F G
  obtain ⟨hp, hq⟩ := parts_isC1cOnPositiveSide hf
  have sp := singleton_mem_sepIn hp.1 hp.2
  have sq := singleton_mem_sepIn hq.1 hq.2
  have sp' := singleton_mem_sepIn (isC1c_actFn_reflect hn hp) (tsupport_actFn_reflect_subset_neg hn hp)
  have sq' := singleton_mem_sepIn (isC1c_actFn_reflect hn hq) (tsupport_actFn_reflect_subset_neg hn hq)
  have defined : ∀ {A C : FreeSep},
      A ∈ EuclideanFunctionals.finCombIn {x : R4 | TwoPoints.euclidDot n x < 0} →
      C ∈ EuclideanFunctionals.finCombIn {x : R4 | 0 < TwoPoints.euclidDot n x} →
      EuclideanFunctionals.MulDefined A C := fun hA hC =>
    (disjoint_open_halfspaces n).mono (combSupp_subset hA) (combSupp_subset hC)
  by_cases hr : ∀ x, (f x).im = 0
  · have hF : F = toFree [ComplexTestFunctions.rePart f] := complexTuple_singleton_of_real hr
    have hG : G = toFree [(hyperplaneReflection n hn 0).actFn (ComplexTestFunctions.rePart f)] := by
      change (hyperplaneReflection n hn 0).actFree (EuclideanFunctionals.freeConj F) = _
      rw [hF, freeConj_toFree sp.1, actFree_toFree_singleton _ sp.1]
    refine ⟨hF ▸ toFree_mem_finCombIn sp, ?_, ?_⟩
    · rw [hF, hG]
      exact defined (toFree_mem_finCombIn sp') (toFree_mem_finCombIn sp)
    · have hq0 : ComplexTestFunctions.imPart f = 0 := funext hr
      have hM : (hyperplaneReflection n hn 0).actFn (ComplexTestFunctions.imPart f) = 0 := by
        rw [hq0]
        rfl
      have hm0 : [(hyperplaneReflection n hn 0).actFn (ComplexTestFunctions.rePart f),
          (0 : R4 → ℝ)] ∈ sepPairs := by
        rw [← hq0]
        exact reflect_pair_mem_sepPairs hn hp hq
      have t₁ : evalPair (S.fn 2 le_rfl)
          ((hyperplaneReflection n hn 0).actFn (ComplexTestFunctions.imPart f))
          (ComplexTestFunctions.imPart f) = 0 := by
        rw [hM, hq0]
        exact evalPair_zero_left hB hm0
      have t₂ : evalPair (S.fn 2 le_rfl)
          ((hyperplaneReflection n hn 0).actFn (ComplexTestFunctions.imPart f))
          (ComplexTestFunctions.rePart f) = 0 := by
        rw [hM]
        exact evalPair_zero_left hB (reflect_pair_mem_sepPairs hn hp hp)
      have t₃ : evalPair (S.fn 2 le_rfl)
          ((hyperplaneReflection n hn 0).actFn (ComplexTestFunctions.rePart f))
          (ComplexTestFunctions.imPart f) = 0 := by
        rw [hq0]
        exact evalPair_zero_right hB (swap_mem_sepPairs (reflect_pair_mem_sepPairs hn hp hp))
      rw [hF, hG, centeredFnFree_freeMul_singletons hT S sp'.1 sp.1 (reflect_pair_mem_sepPairs hn hp hp),
        complexExtension_reflectFun_conjFun hB hn hp hq, t₁, t₂, t₃]
      simp
  · have hF : F = toFree [ComplexTestFunctions.rePart f] +
        Complex.I • toFree [ComplexTestFunctions.imPart f] := complexTuple_singleton_of_not_real hr
    have hG : G = toFree [(hyperplaneReflection n hn 0).actFn (ComplexTestFunctions.rePart f)] +
        (-Complex.I) •
          toFree [(hyperplaneReflection n hn 0).actFn (ComplexTestFunctions.imPart f)] := by
      change (hyperplaneReflection n hn 0).actFree (EuclideanFunctionals.freeConj F) = _
      rw [hF, freeConj_add_I_smul, freeConj_toFree sp.1, freeConj_toFree sq.1, map_add,
        map_smul, actFree_toFree_singleton _ sp.1, actFree_toFree_singleton _ sq.1]
    have mF : F ∈ EuclideanFunctionals.finCombIn
        {x : R4 | 0 < TwoPoints.euclidDot n x} := by
      rw [hF]
      exact Submodule.add_mem _ (toFree_mem_finCombIn sp)
        (Submodule.smul_mem _ _ (toFree_mem_finCombIn sq))
    have mG : G ∈ EuclideanFunctionals.finCombIn
        {x : R4 | TwoPoints.euclidDot n x < 0} := by
      rw [hG]
      exact Submodule.add_mem _ (toFree_mem_finCombIn sp')
        (Submodule.smul_mem _ _ (toFree_mem_finCombIn sq'))
    refine ⟨mF, defined mG mF, ?_⟩
    rw [hF, hG]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [centeredFnFree_freeMul_singletons hT S sp'.1 sp.1 (reflect_pair_mem_sepPairs hn hp hp),
      centeredFnFree_freeMul_singletons hT S sp'.1 sq.1 (reflect_pair_mem_sepPairs hn hp hq),
      centeredFnFree_freeMul_singletons hT S sq'.1 sp.1 (reflect_pair_mem_sepPairs hn hq hp),
      centeredFnFree_freeMul_singletons hT S sq'.1 sq.1 (reflect_pair_mem_sepPairs hn hq hq),
      complexExtension_reflectFun_conjFun hB hn hp hq]
    linear_combination (-((evalPair (S.fn 2 le_rfl)
      ((hyperplaneReflection n hn 0).actFn (ComplexTestFunctions.imPart f))
      (ComplexTestFunctions.imPart f) : ℝ) : ℂ)) * Complex.I_mul_I
theorem statement_holds (hT : TestSpaces.CumulantRecursionTriangular) : Statement :=
  fun _ hS hB => ⟨⟨fun _ hf _ hg hd => complexExtension_conjFun hB hf hg hd,
      realPartForm_isDisjointForm hS hB⟩,
    fun r hr _ hf _ hg hd => complexExtension_actFn r hr hf hg hd,
    fun S hS' n hn f hf => reflection_positivity_identity hT hB S hS' n hn f hf⟩
end YangMills.Construction.PairFunctions.ConjIsometryReflection
end
