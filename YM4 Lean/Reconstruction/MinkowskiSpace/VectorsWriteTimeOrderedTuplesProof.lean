import YangMills.Construction.Continuum.FlatFunctionsTensorsOfSubTuplesAndSmoothTuples
import Reconstruction.MinkowskiSpace.ScalarProductsOfTheVectorsOfSmoothSequencesProof
import YangMills.Construction.ReflectionPositivity.PropertiesOfTheFormOfAFunctionalProof
import Reconstruction.MinkowskiSpace.ConjugatedInsertionsOfTheKernelsProof
import Reconstruction.MinkowskiSpace.DensityNearTheMiddleOfASlabProof
import Reconstruction.MinkowskiSpace.FormRepresentsItsFunctionalAndIsEuclideanProof
import Reconstruction.MinkowskiSpace.OperatorsAtTheMiddleOfTheDensity
import Reconstruction.MinkowskiSpace.VectorsWriteTimeOrderedTuples
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.TimeOrderedVectors
open YangMills.Construction.SeparatedTuples YangMills.Construction.ReflectionPositivity.TupleForm YangMills.Construction.ReflectionPositivity.FormProperties YangMills.Construction.FieldFormConditions YangMills.Construction.ProjectionMeasures YangMills.Construction.HilbertToolkit YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert YangMills.Construction.MinkowskiSpace YangMills.Construction.FieldForms YangMills.Construction.InsertedFieldForm
theorem imPart_realWickPoint (a : Fin 4 → ℝ) :
    MinkowskiSpace.imPart (realWickPoint a) = mkTimeSpace (a 3) 0 := by
  funext μ
  fin_cases μ <;>
    simp [MinkowskiSpace.imPart, realWickPoint, wickMap, toComplex, mkTimeSpace, Fin.cons]
  all_goals rfl
theorem tubeGap_realWickPoint (a : Fin 4 → ℝ) : tubeGap (realWickPoint a) = a 3 := by
  change coneGap (MinkowskiSpace.imPart (realWickPoint a)) = a 3
  rw [imPart_realWickPoint]
  simp [coneGap, spacePart, mkTimeSpace, spaceNorm]
theorem realWickPoint_mem_futureTube {a : Fin 4 → ℝ} (ha : 0 < a 3) :
    realWickPoint a ∈ futureTube := by
  show tubeGap (realWickPoint a) > 0
  rw [tubeGap_realWickPoint]
  exact ha
theorem realWickPoint_add (a b : Fin 4 → ℝ) :
    realWickPoint (a + b) = realWickPoint a + realWickPoint b := by apply _root_.YangMills.Construction.InsertedFieldForm.realWickPoint_add <;> assumption
theorem realWickPoint_sub (a b : Fin 4 → ℝ) :
    realWickPoint (a - b) = realWickPoint a - realWickPoint b := by
  have h : toComplex (a - b) = toComplex a - toComplex b := by
    funext μ
    simp [toComplex]
  simp [realWickPoint, h, map_sub]
theorem realWickPoint_smul_timeUnitVec (s : ℝ) :
    realWickPoint (s • timeUnitVec) = imagTimeShift s := by apply _root_.YangMills.Construction.CentralDensity.realWickPoint_smul_timeUnitVec <;> assumption
abbrev wickTuple {n : ℕ} (x : TestSpaces.PointTuple n) : Fin n → ComplexVec4 :=
  wickMapTuple (tupleToComplex x)
section Products
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K)
theorem fieldProduct_congr_cast {k k' : ℕ} (h : k = k') (ζ : Fin (k + 1) → ComplexVec4)
    (ζ' : Fin (k' + 1) → ComplexVec4) (hz : ∀ i : Fin (k + 1), ζ i = ζ' (Fin.cast (by omega) i)) :
    fieldProduct E A k ζ = fieldProduct E A k' ζ' := by
  subst h
  congr 1
  funext i
  simpa using hz i
theorem wickTuple_mem_diffCoordsInTube {n : ℕ} {x : TestSpaces.PointTuple n}
    (hx : x ∈ TestSpaces.increasingPositiveTimes n) : wickTuple x ∈ diffCoordsInTube n := by apply _root_.YangMills.Construction.SmoothSeqInner.wickOfReal_mem_diffCoordsInTube <;> assumption
theorem imagTimeShift_one_mem_futureTube : imagTimeShift 1 ∈ futureTube := by apply _root_.YangMills.Construction.MinkowskiSpace.InvariantEuclideanProof.imagTimeShift_one_mem_futureTube <;> assumption
theorem fieldProduct_stateVector_wickTuple (hJoin : FieldProductMulJoin E A)
    (hLast : StateIndepOfLast E Ω A) {y v : Fin 4 → ℝ} (hy : 0 < y 3)
    (hv : y 3 < v 3) {n : ℕ} {x : TestSpaces.PointTuple n}
    (hx : x ∈ TestSpaces.increasingPositiveTimes n) :
    fieldProduct E A 1
        (snocPoint (fun _ : Fin 1 => realWickPoint y) (realWickPoint (v - y)))
        (stateVector E Ω A n (wickTuple x)) =
      stateVector E Ω A (n + 1)
        (wickTuple (Fin.cons y fun i => x i + v : TestSpaces.PointTuple (n + 1))) := by
  have hζ : (fun _ : Fin 1 => realWickPoint y) ∈ WightmanTheory.tubeTuples 1 :=
    fun _ _ => realWickPoint_mem_futureTube hy
  have hα : realWickPoint (v - y) ∈ futureTube :=
    realWickPoint_mem_futureTube (by simpa using hv)
  cases n with
  | zero =>
    have hflat : diffCoords (wickTuple (Fin.cons y fun i => x i + v : TestSpaces.PointTuple 1)) =
        fun _ : Fin 1 => realWickPoint y := by
      funext i
      fin_cases i
      rfl
    show fieldProduct E A 1 _ Ω = fieldProduct E A 1 (snocPoint (diffCoords _) _) Ω
    rw [hflat]
    exact hLast 1 _ hζ _ _ hα imagTimeShift_one_mem_futureTube
  | succ n =>
    have hw := wickTuple_mem_diffCoordsInTube hx
    have hw0 : wickTuple x 0 ∈ futureTube := hw 0 (Set.mem_univ _)
    have hd : snocPoint (successiveDiffs (wickTuple x)) (imagTimeShift 1) ∈
        WightmanTheory.tubeTuples (n + 1) := by
      intro i _
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa [snocPoint] using imagTimeShift_one_mem_futureTube
      · have h := hw i.succ (Set.mem_univ _)
        simpa [snocPoint, diffCoordsOfLength, diffCoords] using h
    have hsplit : snocPoint (diffCoords (wickTuple x)) (imagTimeShift 1) =
        consPoint (wickTuple x 0)
          (snocPoint (successiveDiffs (wickTuple x)) (imagTimeShift 1)) :=
      (Fin.cons_snoc_eq_snoc_cons _ _ _).symm
    show fieldProduct E A 1 _ (fieldProduct E A (n + 1) _ Ω) =
      fieldProduct E A (n + 2) (snocPoint (diffCoords _) _) Ω
    rw [hsplit]
    refine (congrArg (fun B : BddOp K => B Ω) (hJoin 1 (n + 1) _ (realWickPoint (v - y))
      (wickTuple x 0) _ hζ hα hw0 hd)).trans ?_
    refine congrArg (fun B : BddOp K => B Ω)
      (fieldProduct_congr_cast E A (by omega) _ _ fun i => ?_)
    obtain ⟨k, hk⟩ := i
    rcases k with _ | _ | k
    · rfl
    · show realWickPoint (v - y) + realWickPoint (x 0) =
        realWickPoint (x 0 + v) - realWickPoint y
      rw [realWickPoint_sub, realWickPoint_add]
      abel
    · simp only [joinAt, Fin.append, Fin.addCases, snocPoint, Fin.snoc]
      by_cases h : k < n
      · simp [h]
        show realWickPoint (x ⟨k + 1, by omega⟩) - realWickPoint (x ⟨k, by omega⟩) =
          realWickPoint (x ⟨k + 1, by omega⟩ + v) - realWickPoint (x ⟨k, by omega⟩ + v)
        rw [realWickPoint_add, realWickPoint_add]
        abel
      · simp [h]
theorem exists_gap_fieldProduct_eq {y w : Fin 4 → ℝ} (hy : 0 < y 3) (hw : 0 < w 3) :
    ∃ s : ℝ, 0 < s ∧ s ≤ y 3 ∧ s ≤ w 3 ∧
      fieldProduct E A 1 (snocPoint (fun _ : Fin 1 => realWickPoint y) (realWickPoint w)) =
        spectralTranslation E (realWickPoint (y - s • timeUnitVec)) * A s *
          spectralTranslation E (realWickPoint (w - s • timeUnitVec)) := by
  set ζ : Fin 2 → ComplexVec4 := snocPoint (fun _ : Fin 1 => realWickPoint y) (realWickPoint w)
    with hζ
  have h0 : ζ 0 = realWickPoint y := rfl
  have h1 : ζ (Fin.last 1) = realWickPoint w := rfl
  have hm0 : tubeGap (ζ 0) = y 3 := by rw [h0, tubeGap_realWickPoint]
  have hm1 : tubeGap (ζ (Fin.last 1)) = w 3 := by rw [h1, tubeGap_realWickPoint]
  have hpos : 0 < Finset.univ.inf' Finset.univ_nonempty fun k => tubeGap (ζ k) := by
    rw [Finset.lt_inf'_iff]
    intro k _
    fin_cases k
    · exact hm0.symm ▸ hy
    · exact hm1.symm ▸ hw
  have hle : ∀ k, (Finset.univ.inf' Finset.univ_nonempty fun k => tubeGap (ζ k)) ≤
      tubeGap (ζ k) := fun k => Finset.inf'_le _ (Finset.mem_univ k)
  refine ⟨halfMinTubeGap ζ, ?_, ?_, ?_, ?_⟩
  · simp only [halfMinTubeGap]; positivity
  · have := hle 0
    rw [hm0] at this
    simp only [halfMinTubeGap]
    linarith
  · have := hle (Fin.last 1)
    rw [hm1] at this
    simp only [halfMinTubeGap]
    linarith
  · rw [fieldProduct_succ_eq, fieldProductAt, realWickPoint_sub, realWickPoint_sub,
      realWickPoint_smul_timeUnitVec, h0, h1]
    simp
end Products
section Tensors
variable {n : ℕ}
theorem tsupport_tensorProdComplex_subset (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    tsupport (TestSpaces.tensorProdComplex f) ⊆ Set.univ.pi fun i => tsupport (f i) := by apply _root_.YangMills.Construction.RepresentsEuclideanProof.tsupport_tensorProdComplex_subset_pi <;> assumption
end Tensors
section Tuples
variable {n : ℕ}
abbrev realToComplexFn (f : (Fin 4 → ℝ) → ℝ) : (Fin 4 → ℝ) → ℂ := fun x => (f x : ℂ)
theorem tsupport_realToComplexFn (f : (Fin 4 → ℝ) → ℝ) :
    tsupport (realToComplexFn f) = tsupport f := by apply _root_.YangMills.Construction.FlatTensors.tsupport_ofReal_comp <;> assumption
theorem realToComplexFn_mem_c1CompactSupp {f : (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) :
    realToComplexFn f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp hf.1, ?_, Set.subset_univ _⟩
  show IsCompact (tsupport (realToComplexFn f))
  rw [tsupport_realToComplexFn]
  exact hf.2.1
theorem singleton_mem_sepAll {f : (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) :
    [f] ∈ EuclideanFunctionals.sepAll := by
  have hc : f ∈ FourSpace.C1c := ⟨hf.1, hf.2.1⟩
  rw [FourSpace.C1c_eq_compactC1 EuclideanFunctionals.defaultMirrorData] at hc
  exact Set.mem_iUnion.2 ⟨1, rfl, fun g hg => (List.mem_singleton.1 hg) ▸ hc,
    List.pairwise_singleton _ _⟩
theorem addRight_mem_c1CompactSupp {f : (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) (v : Fin 4 → ℝ) :
    (fun x => f (x + v)) ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) :=
  ⟨hf.1.comp (contDiff_id.add contDiff_const), hf.2.1.comp_homeomorph (Homeomorph.addRight v),
    Set.subset_univ _⟩
theorem tsupport_comp_addRight (f : (Fin 4 → ℝ) → ℝ) (v : Fin 4 → ℝ) :
    tsupport (fun x => f (x + v)) = (· + v) ⁻¹' tsupport f :=
  tsupport_comp_eq_preimage f (Homeomorph.addRight v)
def tailSep (X : TestSpaces.SepTupleOfCard (n + 1)) : TestSpaces.SepTupleOfCard n :=
  ⟨fun i => X.1 i.succ, fun i => X.2.1 i.succ,
    fun _ _ hij => X.2.2 ((Fin.succ_injective _).ne hij)⟩
def tailSepShift (X : TestSpaces.SepTupleOfCard (n + 1)) (v : Fin 4 → ℝ) :
    TestSpaces.SepTupleOfCard n :=
  ⟨fun i x => X.1 i.succ (x + v), fun i => addRight_mem_c1CompactSupp (X.2.1 i.succ) v, fun i j hij => by
    simp only [tsupport_comp_addRight]
    exact (X.2.2 ((Fin.succ_injective _).ne hij)).preimage _⟩
theorem toList_mem_supportedIn_of_tsupport {X : TestSpaces.SepTupleOfCard n}
    (h : ∀ i, tsupport (X.1 i) ⊆ TimeAxis.upperHalfSpace) :
    TupleLists.toList ⟨n, X⟩ ∈ supportedIn TimeAxis.upperHalfSpace := by
  intro f hf
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
  exact h i
theorem tsupport_subset_of_toList_mem {X : TestSpaces.SepTupleOfCard n}
    (h : TupleLists.toList ⟨n, X⟩ ∈ supportedIn TimeAxis.upperHalfSpace) (i : Fin n) :
    tsupport (X.1 i) ⊆ TimeAxis.upperHalfSpace :=
  h _ ((List.mem_ofFn' _ _).2 ⟨i, rfl⟩)
theorem spanBasisIn_coe {O : Set (Fin 4 → ℝ)} (X : supportedIn O) :
    ((spanBasisIn O X : spanIn O) : FormalSpan) = basisVec X.1 := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.coe_spanBasisIn <;> assumption
theorem push_translate_tailSepShift (X : TestSpaces.SepTupleOfCard (n + 1)) (v : Fin 4 → ℝ) :
    push (translate v) (TupleLists.toList ⟨n, tailSepShift X v⟩) =
      TupleLists.toList ⟨n, tailSep X⟩ := by
  have hlist : pushList (translate v) (TupleLists.toList ⟨n, tailSepShift X v⟩).1 =
      (TupleLists.toList ⟨n, tailSep X⟩).1 := by
    rw [pushList_translate]
    simp only [TupleLists.toList, List.map_ofFn]
    congr 1
    funext i x
    simp [tailSepShift, tailSep]
  have hsep : IsDisjointlySupported (pushList (translate v)
      (TupleLists.toList ⟨n, tailSepShift X v⟩).1) :=
    hlist ▸ (TupleLists.toList ⟨n, tailSep X⟩).2
  unfold push
  rw [dif_pos hsep]
  exact Subtype.ext hlist
theorem shiftedSpan_spanBasisIn_tailSepShift (X : TestSpaces.SepTupleOfCard (n + 1)) (v : Fin 4 → ℝ)
    (h : TupleLists.toList ⟨n, tailSepShift X v⟩ ∈ supportedIn TimeAxis.upperHalfSpace)
    (h' : TupleLists.toList ⟨n, tailSep X⟩ ∈ supportedIn TimeAxis.upperHalfSpace) :
    (shiftedSpan v (spanBasisIn TimeAxis.upperHalfSpace ⟨_, h⟩)).1 =
      basisVec (TupleLists.toList ⟨n, tailSep X⟩) := by
  have hact : pushSpan (translate v) (spanBasisIn TimeAxis.upperHalfSpace ⟨_, h⟩).1 =
      basisVec (TupleLists.toList ⟨n, tailSep X⟩) := by
    rw [spanBasisIn_coe, pushSpan, linearExtend_basisVec, push_translate_tailSepShift]
  have hmem : pushSpan (translate v) (spanBasisIn TimeAxis.upperHalfSpace ⟨_, h⟩).1 ∈
      spanIn TimeAxis.upperHalfSpace := by
    rw [hact, ← spanBasisIn_coe ⟨_, h'⟩]
    exact Subtype.property _
  rw [shiftedSpan, dif_pos hmem]
  exact hact
theorem formalMul_head_tailSep (X : TestSpaces.SepTupleOfCard (n + 1)) :
    formalMul (WightmanReconstruction.complexTuple (realToComplexFn (X.1 0)))
        (basisVec (TupleLists.toList ⟨n, tailSep X⟩)) =
      basisVec (TupleLists.toList ⟨n + 1, X⟩) := by
  have hs := singleton_mem_sepAll (X.2.1 0)
  rw [WightmanReconstruction.complexTuple_ofReal _ hs, formalMul_basisVec]
  congr 1
  refine Subtype.ext ?_
  have hdef : SepTuple.Composable (WightmanReconstruction.toSepTuple ⟨[X.1 0], hs⟩)
      (TupleLists.toList ⟨n, tailSep X⟩) := by
    intro f hf g hg
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    have hf' : f = X.1 0 := by simpa [WightmanReconstruction.toSepTuple] using hf
    rw [hf']
    exact X.2.2 (Fin.succ_ne_zero i).symm
  rw [SepTuple.juxt_val hdef]
  simp [WightmanReconstruction.toSepTuple, TupleLists.toList, List.ofFn_succ, tailSep]
theorem stateOf_eq_insertedState (σ : TestSpaces.SepTuple → ℝ)
    (X : TestSpaces.SepTupleOfCard (n + 1)) (v : Fin 4 → ℝ)
    (hX : TupleLists.toList ⟨n + 1, X⟩ ∈ supportedIn TimeAxis.upperHalfSpace)
    (h : TupleLists.toList ⟨n, tailSepShift X v⟩ ∈ supportedIn TimeAxis.upperHalfSpace) :
    stateOf σ (spanBasisIn TimeAxis.upperHalfSpace ⟨_, hX⟩) =
      insertedState σ (realToComplexFn (X.1 0)) v (spanBasisIn TimeAxis.upperHalfSpace ⟨_, h⟩) := by
  have h' : TupleLists.toList ⟨n, tailSep X⟩ ∈ supportedIn TimeAxis.upperHalfSpace :=
    toList_mem_supportedIn_of_tsupport fun i => tsupport_subset_of_toList_mem hX i.succ
  have heq : formalMul (WightmanReconstruction.complexTuple (realToComplexFn (X.1 0)))
      (shiftedSpan v (spanBasisIn TimeAxis.upperHalfSpace ⟨_, h⟩)).1 =
        basisVec (TupleLists.toList ⟨n + 1, X⟩) := by
    rw [shiftedSpan_spanBasisIn_tailSepShift X v h h', formalMul_head_tailSep]
  have hmem : formalMul (WightmanReconstruction.complexTuple (realToComplexFn (X.1 0)))
      (shiftedSpan v (spanBasisIn TimeAxis.upperHalfSpace ⟨_, h⟩)).1 ∈
        spanIn TimeAxis.upperHalfSpace := by
    rw [heq, ← spanBasisIn_coe ⟨_, hX⟩]
    exact Subtype.property _
  rw [insertedState, dif_pos hmem]
  congr 1
  exact Subtype.ext ((spanBasisIn_coe _).trans heq.symm)
end Tuples
section Integrands
variable {n : ℕ}
theorem continuous_wickTuple : Continuous (wickTuple : TestSpaces.PointTuple n → _) := by apply _root_.YangMills.Construction.SmoothSeqInner.continuous_wickOfReal <;> assumption
theorem continuousOn_stateVector_wickTuple {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {E : FourBorelSet → BddOp K} {Ω : K} {A : ℝ → BddOp K}
    (hHol : ExpectationsStatesHolomorphic E Ω A) (n : ℕ) :
    ContinuousOn (fun x : TestSpaces.PointTuple n => stateVector E Ω A n (wickTuple x))
      (TestSpaces.increasingPositiveTimes n) := by
  cases n with
  | zero => exact continuousOn_const
  | succ n =>
    exact (hHol n).2.2.2.2.comp continuous_wickTuple.continuousOn
      fun x hx => wickTuple_mem_diffCoordsInTube hx
theorem mem_increasingPositiveTimes_of_cuts {f : Fin n → (Fin 4 → ℝ) → ℝ} {c : Fin (n + 1) → ℝ}
    (hc : WightmanReconstruction.IsCutSequence f c) (h0 : 0 ≤ c 0) {x : TestSpaces.PointTuple n}
    (hx : x ∈ Set.univ.pi fun i => tsupport (f i)) : x ∈ TestSpaces.increasingPositiveTimes n := by
  refine ⟨fun i j hij => ?_, fun h => ?_⟩
  · have hi := (hc.2 i (hx i (Set.mem_univ _))).2
    have hj := (hc.2 j (hx j (Set.mem_univ _))).1
    have hle : c i.succ ≤ c j.castSucc := hc.1.monotone (Fin.succ_le_castSucc_iff.2 hij)
    show x i 3 < x j 3
    linarith
  · have h₁ := (hc.2 ⟨0, h⟩ (hx _ (Set.mem_univ _))).1
    have h₂ : c (Fin.castSucc ⟨0, h⟩) = c 0 := congrArg c (Fin.ext rfl)
    show 0 < x ⟨0, h⟩ 3
    linarith
theorem tsupport_subset_upperHalfSpace_of_cuts {f : Fin n → (Fin 4 → ℝ) → ℝ} {c : Fin (n + 1) → ℝ}
    (hc : WightmanReconstruction.IsCutSequence f c) (h0 : 0 ≤ c 0) (i : Fin n) :
    tsupport (f i) ⊆ TimeAxis.upperHalfSpace := by
  intro x hx
  have h₁ := (hc.2 i hx).1
  have h₂ : c 0 ≤ c i.castSucc := hc.1.monotone (Fin.zero_le _)
  show 0 < x 3
  linarith
theorem continuous_tensorProdComplex {f : Fin n → (Fin 4 → ℝ) → ℝ} (hf : ∀ i, Continuous (f i)) :
    Continuous (TestSpaces.tensorProdComplex f) :=
  Complex.continuous_ofReal.comp (continuous_finsetProd _ fun i _ =>
    (hf i).comp (continuous_apply i))
theorem isCompact_tsupport_tensorProdComplex {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (hf : ∀ i, IsCompact (tsupport (f i))) : IsCompact (tsupport (TestSpaces.tensorProdComplex f)) :=
  (isCompact_univ_pi hf).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_tensorProdComplex_subset f)
theorem continuous_mul_of_tsupport_subset_of_continuousOn {P : Type} [TopologicalSpace P]
    {T g : P → ℂ} {S : Set P}
    (hT : Continuous T) (hS : IsOpen S) (hsub : tsupport T ⊆ S) (hg : ContinuousOn g S) :
    Continuous fun x => T x * g x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x ∈ S
  · exact hT.continuousAt.mul (hg.continuousAt (hS.mem_nhds hx))
  · have hz : T =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hsub h)
    have hz' : (fun x => T x * g x) =ᶠ[𝓝 x] fun _ => 0 := hz.mono fun y hy => by simp [hy]
    exact continuousAt_const.congr hz'.symm
theorem integral_eq_integral_cons_add (Φ : TestSpaces.PointTuple (n + 1) → ℂ)
    (hΦ : MeasureTheory.Integrable Φ) (v : Fin 4 → ℝ) :
    ∫ x, Φ x = ∫ y : Fin 4 → ℝ, ∫ x : TestSpaces.PointTuple n,
      Φ (Fin.cons y fun i => x i + v : TestSpaces.PointTuple (n + 1)) := by
  have hmp := (MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => Fin 4 → ℝ) 0).symm
  have hint : MeasureTheory.Integrable (fun p => Φ ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => Fin 4 → ℝ) 0).symm p))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin 4 → ℝ)).prod MeasureTheory.volume) :=
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hΦ
  rw [← hmp.integral_comp' Φ, MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.integral_prod _ hint]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hsh := MeasureTheory.integral_add_right_eq_self
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (TestSpaces.PointTuple n)))
    (fun x : TestSpaces.PointTuple n => Φ (Fin.cons y x : TestSpaces.PointTuple (n + 1)))
    (fun _ => v)
  have hsym : ∀ x : TestSpaces.PointTuple n, (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => Fin 4 → ℝ) 0).symm (y, x) = Fin.cons y x := by
    intro x
    simp [MeasurableEquiv.piFinSuccAbove]
    rfl
  simp only [hsym]
  exact hsh.symm
theorem tensorProdComplex_cons_add (f : Fin (n + 1) → (Fin 4 → ℝ) → ℝ) (v y : Fin 4 → ℝ)
    (x : TestSpaces.PointTuple n) :
    TestSpaces.tensorProdComplex f (Fin.cons y fun i => x i + v : TestSpaces.PointTuple (n + 1)) =
      realToComplexFn (f 0) y * TestSpaces.tensorProdComplex (fun i x => f i.succ (x + v)) x := by
  simp [TestSpaces.tensorProdComplex, TestSpaces.tensorProd, Fin.prod_univ_succ]
theorem exists_cutSequence_nonneg {f : Fin n → (Fin 4 → ℝ) → ℝ} {c : Fin (n + 1) → ℝ}
    (hcomp : ∀ i, IsCompact (tsupport (f i)))
    (hpos : ∀ i, tsupport (f i) ⊆ TimeAxis.upperHalfSpace)
    (hc : WightmanReconstruction.IsCutSequence f c) :
    ∃ d : Fin (n + 1) → ℝ, WightmanReconstruction.IsCutSequence f d ∧ 0 ≤ d 0 := by
  obtain ⟨δ, hδ, hmin⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i, ∀ x ∈ tsupport (f i), δ < x 3 := by
    have hU : IsCompact (⋃ i, tsupport (f i)) := isCompact_iUnion hcomp
    by_cases hne : (⋃ i, tsupport (f i)).Nonempty
    · obtain ⟨x₀, hx₀, hm⟩ := hU.exists_isMinOn hne
        (continuous_apply (3 : Fin 4)).continuousOn
      obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.1 hx₀
      have hp : 0 < x₀ 3 := hpos i₀ hi₀
      refine ⟨x₀ 3 / 2, by positivity, fun i x hx => ?_⟩
      have : x₀ 3 ≤ x 3 := hm (Set.mem_iUnion.2 ⟨i, hx⟩)
      linarith
    · refine ⟨1, one_pos, fun i x hx => (hne ⟨x, Set.mem_iUnion.2 ⟨i, hx⟩⟩).elim⟩
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set ε : ℝ := δ / ((n : ℝ) + 1) with hε
  have hεpos : 0 < ε := by positivity
  have hle : ∀ i : Fin (n + 1), ((i : ℕ) : ℝ) * ε ≤ δ := by
    intro i
    have hi : ((i : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
      have := i.is_lt
      exact_mod_cast this.le
    calc ((i : ℕ) : ℝ) * ε ≤ ((n : ℝ) + 1) * ε := by gcongr
      _ = δ := by rw [hε]; field_simp
  refine ⟨fun i => max (c i) (((i : ℕ) : ℝ) * ε), ⟨?_, fun i x hx => ?_⟩, ?_⟩
  · exact fun i j hij => max_lt_max (hc.1 hij)
      (mul_lt_mul_of_pos_right (by exact_mod_cast hij) hεpos)
  · have h₁ := hc.2 i hx
    refine ⟨max_lt h₁.1 ((hle _).trans_lt (hmin i x hx)), lt_max_of_lt_left h₁.2⟩
  · exact le_max_of_le_right (by simp)
end Integrands
theorem inner_stateOf_eq_integral (hProducts : FieldProductProperties)
    (hOperators : MidpointOperators.MidpointOperatorFacts)
    {σ : TestSpaces.SepTuple → ℝ} {E : FourBorelSet → BddOp (StateSpace σ)}
    {p C : ℝ} (hcond : Hypotheses σ E p C)
    {G : ℝ → (Fin 4 → ℝ) → BddOp (StateSpace σ)} (hG : IsFieldDensity σ E G)
    {℘ C' : ℝ} (hform : IsBoundedFieldForm E (vacuumState σ) (midpointField σ G) ℘ C') (n : ℕ) :
    ∀ (X : TestSpaces.SepTupleOfCard n) (c : Fin (n + 1) → ℝ)
      (_ : WightmanReconstruction.IsCutSequence X.1 c) (_ : 0 ≤ c 0)
      (hX : TupleLists.toList ⟨n, X⟩ ∈ supportedIn TimeAxis.upperHalfSpace)
      (χ : StateSpace σ),
      ⟪χ, stateOf σ (spanBasisIn TimeAxis.upperHalfSpace ⟨_, hX⟩)⟫_ℂ =
        ∫ x, TestSpaces.tensorProdComplex X.1 x *
          ⟪χ, stateVector E (vacuumState σ) (midpointField σ G) n (wickTuple x)⟫_ℂ := by
  have hP := hProducts (StateSpace σ) E (vacuumState σ) (midpointField σ G) ℘ C' hform
  have hJoin := hP.2.2.1
  have hLast := hP.2.2.2.2.1
  have hHol := hP.2.2.2.2.2.2.2.1
  induction n with
  | zero =>
    intro X c _ _ hX χ
    have hempty : (⟨_, hX⟩ : supportedIn TimeAxis.upperHalfSpace) =
        ⟨SepTuple.nil, nil_mem_supportedIn _⟩ :=
      Subtype.ext (Subtype.ext (by simp [TupleLists.toList, SepTuple.nil]))
    rw [hempty]
    have hvol : (MeasureTheory.volume : MeasureTheory.Measure (TestSpaces.PointTuple 0)) =
        MeasureTheory.Measure.dirac default := MeasureTheory.Measure.volume_pi_eq_dirac _
    rw [hvol, MeasureTheory.integral_dirac]
    simp [TestSpaces.tensorProdComplex, TestSpaces.tensorProd, stateVector]
    rfl
  | succ n ih =>
    intro X c hc h0 hX χ
    set c₁ : ℝ := c (Fin.succ 0) with hc₁def
    set v : Fin 4 → ℝ := c₁ • timeUnitVec with hv
    have hv3 : ∀ x : Fin 4 → ℝ, (x + v) 3 = x 3 + c₁ := by
      intro x
      simp [hv, timeUnitVec, PeriodicLattice.coordVec, TimeAxis.timeIdx]
    have hc₁ : 0 < c₁ := h0.trans_lt (hc.1 (Fin.succ_pos 0))
    have hcuts : WightmanReconstruction.IsCutSequence (tailSepShift X v).1
        (fun i : Fin (n + 1) => c i.succ - c₁) := by
      refine ⟨fun i j hij => sub_lt_sub_right (hc.1 (Fin.succ_lt_succ_iff.2 hij)) _,
        fun i x hx => ?_⟩
      have hx' : x + v ∈ tsupport (X.1 i.succ) := by
        have : x ∈ tsupport (fun x => X.1 i.succ (x + v)) := hx
        rwa [tsupport_comp_addRight] at this
      have h₁ : c i.succ.castSucc < (x + v) 3 ∧ (x + v) 3 < c i.succ.succ := hc.2 i.succ hx'
      rw [hv3] at h₁
      have e : i.succ.castSucc = i.castSucc.succ := rfl
      rw [e] at h₁
      show c i.castSucc.succ - c₁ < x 3 ∧ x 3 < c i.succ.succ - c₁
      exact ⟨by linarith [h₁.1], by linarith [h₁.2]⟩
    have hc0 : 0 ≤ (fun i : Fin (n + 1) => c i.succ - c₁) 0 := by simp [hc₁def]
    have hY : TupleLists.toList ⟨n, tailSepShift X v⟩ ∈
        supportedIn TimeAxis.upperHalfSpace :=
      toList_mem_supportedIn_of_tsupport (tsupport_subset_upperHalfSpace_of_cuts hcuts hc0)
    have hslab : tsupport (realToComplexFn (X.1 0)) ⊆ timeSlab c₁ := by
      rw [tsupport_realToComplexFn]
      intro y hy
      have h₁ : c (Fin.castSucc 0) < y 3 ∧ y 3 < c (Fin.succ 0) := hc.2 0 hy
      have e : c (Fin.castSucc 0) = c 0 := rfl
      rw [e] at h₁
      exact ⟨h0.trans_lt h₁.1, h₁.2⟩
    have hdens := hG.inner_insertedState c₁ (realToComplexFn (X.1 0))
      (spanBasisIn TimeAxis.upperHalfSpace ⟨_, hY⟩) χ hc₁ (realToComplexFn_mem_c1CompactSupp (X.2.1 0)) hslab
    rw [stateOf_eq_insertedState σ X v hX hY, hdens]
    have hsub : tsupport (TestSpaces.tensorProdComplex X.1) ⊆
        TestSpaces.increasingPositiveTimes (n + 1) :=
      fun x hx => mem_increasingPositiveTimes_of_cuts hc h0 (tsupport_tensorProdComplex_subset _ hx)
    set Φ : TestSpaces.PointTuple (n + 1) → ℂ := fun x => TestSpaces.tensorProdComplex X.1 x *
      ⟪χ, stateVector E (vacuumState σ) (midpointField σ G) (n + 1) (wickTuple x)⟫_ℂ with hΦdef
    have hcontΦ : Continuous Φ :=
      continuous_mul_of_tsupport_subset_of_continuousOn
        (continuous_tensorProdComplex fun i => (X.2.1 i).1.continuous)
        (TestSpaces.isOpen_increasingPositiveTimes _) hsub
        (continuousOn_const.inner (continuousOn_stateVector_wickTuple hHol _))
    have hcompΦ : HasCompactSupport Φ :=
      HasCompactSupport.mul_right (f := TestSpaces.tensorProdComplex X.1)
        (isCompact_tsupport_tensorProdComplex fun i => (X.2.1 i).2.1)
    rw [integral_eq_integral_cons_add Φ (hcontΦ.integrable_of_hasCompactSupport hcompΦ) v]
    have hzero : ∀ y, y ∉ tsupport (realToComplexFn (X.1 0)) →
        ∫ x : TestSpaces.PointTuple n,
          Φ (Fin.cons y fun i => x i + v : TestSpaces.PointTuple (n + 1)) = 0 := by
      intro y hy
      have h₀ : realToComplexFn (X.1 0) y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [hΦdef, tensorProdComplex_cons_add, h₀]
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    refine MeasureTheory.setIntegral_congr_fun (isClosed_tsupport _).measurableSet fun y hy => ?_
    have hys := hslab hy
    have hy0 : 0 < y 3 := hys.1
    have hyc : y 3 < c₁ := hys.2
    have hv3' : v 3 = c₁ := by simpa using hv3 0
    have hvlt : y 3 < v 3 := hv3'.symm ▸ hyc
    have hvy : 0 < (v - y) 3 := by
      simp only [Pi.sub_apply]
      linarith
    obtain ⟨s, hs0, hs1, hs2, hB⟩ :=
      exists_gap_fieldProduct_eq E (midpointField σ G) hy0 hvy
    have hs2' : s ≤ c₁ - y TimeAxis.timeIdx := by
      have : (v - y) 3 = c₁ - y 3 := by simp [hv3']
      rw [this] at hs2
      exact hs2
    have hGs := (hOperators σ E p C hcond G hG).2.2 c₁ s y hs0 hs1 hs2'
    have harg : (c₁ - s) • timeUnitVec - y = v - y - s • timeUnitVec := by
      rw [hv, sub_smul]
      abel
    have hGB : G c₁ y = fieldProduct E (midpointField σ G) 1
        (snocPoint (fun _ : Fin 1 => realWickPoint y) (realWickPoint (v - y))) := by
      rw [hGs, hB, harg]
    have hip : ∀ w : StateSpace σ, ⟪χ, G c₁ y w⟫_ℂ =
        ⟪ContinuousLinearMap.adjoint (G c₁ y) χ, w⟫_ℂ :=
      fun w => (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
    show realToComplexFn (X.1 0) y * ⟪χ, G c₁ y (stateOf σ _)⟫_ℂ = _
    rw [hip, ih (tailSepShift X v) _ hcuts hc0 hY, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show realToComplexFn (X.1 0) y * (TestSpaces.tensorProdComplex (tailSepShift X v).1 x * _) =
      TestSpaces.tensorProdComplex X.1 (Fin.cons y fun i => x i + v) * _
    rw [tensorProdComplex_cons_add]
    by_cases hT : TestSpaces.tensorProdComplex (tailSepShift X v).1 x = 0
    · have hT' : TestSpaces.tensorProdComplex (fun i x => X.1 i.succ (x + v)) x = 0 := hT
      rw [hT, hT']
      simp
    · have hx : x ∈ TestSpaces.increasingPositiveTimes n :=
        mem_increasingPositiveTimes_of_cuts hcuts hc0
          (tsupport_tensorProdComplex_subset _ (subset_tsupport _ hT))
      rw [← hip, hGB, fieldProduct_stateVector_wickTuple E _ _ hJoin hLast hy0 hvlt hx, mul_assoc]
      rfl
theorem represents_of_fieldProductProperties (hProducts : FieldProductProperties)
    (hOperators : MidpointOperators.MidpointOperatorFacts) : Represents := by
  intro σ E p C hcond G hG ℘ C' hform m X hX hT
  obtain ⟨-, c, hcut⟩ := hT
  have hcomp : ∀ i, IsCompact (tsupport (X.1 i)) := fun i => (X.2.1 i).2.1
  obtain ⟨d, hd, hd0⟩ := exists_cutSequence_nonneg hcomp (tsupport_subset_of_toList_mem hX) hcut
  have hHol := (hProducts (StateSpace σ) E (vacuumState σ) (midpointField σ G) ℘ C'
    hform).2.2.2.2.2.2.2.1
  have hcompact : IsCompact (tsupport (TestSpaces.tensorProdComplex X.1)) :=
    isCompact_tsupport_tensorProdComplex hcomp
  have hsub : tsupport (TestSpaces.tensorProdComplex X.1) ⊆
      TestSpaces.increasingPositiveTimes (m + 1) :=
    fun x hx => mem_increasingPositiveTimes_of_cuts hd hd0 (tsupport_tensorProdComplex_subset _ hx)
  have hcontΞ : ContinuousOn (realStateVector σ E (midpointField σ G) m)
      (tsupport (TestSpaces.tensorProdComplex X.1)) :=
    (continuousOn_stateVector_wickTuple hHol (m + 1)).mono hsub
  have hweak : HasWeakIntegrandData (tsupport (TestSpaces.tensorProdComplex X.1))
      (realStateVector σ E (midpointField σ G) m) (TestSpaces.tensorProdComplex X.1) :=
    { measurableSet := (isClosed_tsupport _).measurableSet
      norm_bdd := hcompact.exists_bound_of_continuousOn hcontΞ
      continuousOn_inner := fun χ => continuousOn_const.inner hcontΞ
      integrableOn := ((continuous_tensorProdComplex fun i =>
        (X.2.1 i).1.continuous).integrable_of_hasCompactSupport hcompact).integrableOn }
  refine ⟨hweak, ?_⟩
  have hclass : HasWeakIntegral (tsupport (TestSpaces.tensorProdComplex X.1))
      (realStateVector σ E (midpointField σ G) m) (TestSpaces.tensorProdComplex X.1)
      (stateOf σ (spanBasisIn TimeAxis.upperHalfSpace ⟨_, hX⟩)) := by
    intro χ
    rw [inner_stateOf_eq_integral hProducts hOperators hcond hG hform (m + 1) X d hd hd0 hX χ]
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hspec : HasWeakIntegral (tsupport (TestSpaces.tensorProdComplex X.1))
      (realStateVector σ E (midpointField σ G) m) (TestSpaces.tensorProdComplex X.1)
      (weakInt (tsupport (TestSpaces.tensorProdComplex X.1))
        (realStateVector σ E (midpointField σ G) m) (TestSpaces.tensorProdComplex X.1)) :=
    Classical.epsilon_spec (p := HasWeakIntegral (tsupport (TestSpaces.tensorProdComplex X.1))
      (realStateVector σ E (midpointField σ G) m) (TestSpaces.tensorProdComplex X.1)) ⟨_, hclass⟩
  exact ext_inner_left ℂ fun χ => (hclass χ).trans (hspec χ).symm
end YangMills.Construction.TimeOrderedVectors
end
