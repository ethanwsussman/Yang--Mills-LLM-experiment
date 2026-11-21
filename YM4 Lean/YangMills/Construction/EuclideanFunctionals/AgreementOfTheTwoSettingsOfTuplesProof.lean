import YangMills.Construction.EuclideanFunctionals.AgreementOfTheTwoSettingsOfTuples
import YangMills.Construction.LimitsOfLatticeFamilies.LinearRelationsAmongTensors
import YangMills.Construction.RotationInvariance.FunctionalOnTuplesOfRealFunctionsProof
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ENNReal
open YangMills.Construction.ReflectionPositivity.AxisMirror YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TwoSettings
theorem euclidNormVec_eq_iff (u v : R4) :
    euclidNormVec u = euclidNormVec v ↔ u ⬝ᵥ u = v ⬝ᵥ v := by
  have h : ∀ w : R4, ∑ μ, w μ ^ 2 = w ⬝ᵥ w := fun w => by
    simp [dotProduct, sq]
  have h0 : ∀ w : R4, 0 ≤ w ⬝ᵥ w := fun w => by
    rw [← h]
    exact Finset.sum_nonneg fun μ _ => sq_nonneg _
  simp only [euclidNormVec, h]
  exact Real.sqrt_inj (h0 u) (h0 v)
theorem dotProduct_map_of_norm (L : R4 →ₗ[ℝ] R4)
    (hL : ∀ x, euclidNormVec (L x) = euclidNormVec x) (u v : R4) :
    L u ⬝ᵥ L v = u ⬝ᵥ v := by
  have h := fun x => (euclidNormVec_eq_iff (L x) x).1 (hL x)
  have h1 := h (u + v)
  have h2 := h u
  have h3 := h v
  rw [map_add] at h1
  simp only [add_dotProduct, dotProduct_add] at h1
  rw [dotProduct_comm (L v) (L u), dotProduct_comm v u] at h1
  linarith
theorem affineIsometryIffMotion : AffineIsometryIffMotion := by
  intro g
  constructor
  · rintro ⟨Q, hQ, b, hg⟩
    have hQ' : Matrix.transpose Q * Q = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).1 hQ
    refine ⟨⟨Matrix.mulVecLin Q, b, fun x => ?_⟩, fun x => ?_⟩
    · refine (euclidNormVec_eq_iff _ _).2 ?_
      simp only [Matrix.mulVecLin_apply]
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ',
        Matrix.one_mulVec]
    · rw [hg]
      rfl
  · rintro ⟨r, hr⟩
    refine ⟨LinearMap.toMatrix' r.lin, ?_, r.offset, fun x => ?_⟩
    · refine (Matrix.mem_orthogonalGroup_iff' _ _).2 ?_
      ext i j
      have h := dotProduct_map_of_norm r.lin r.lin_norm (Pi.single i 1) (Pi.single j 1)
      have e : ∀ k l, LinearMap.toMatrix' r.lin k l = r.lin (Pi.single l 1) k :=
        fun k l => by simp [LinearMap.toMatrix'_apply]
      have h1 : (Pi.single i 1 : R4) ⬝ᵥ Pi.single j 1 = (1 : Matrix (Fin 4) (Fin 4) ℝ) i j := by
        rcases eq_or_ne i j with rfl | hij
        · simp
        · simp [hij, hij.symm]
      rw [← h1, ← h]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, e, dotProduct]
    · rw [← hr x, LinearMap.toMatrix'_mulVec]
theorem freeMul_toFree (X Y : sepAll) :
    freeMul (toFree X.1) (toFree Y.1) = toFree (listAppend X.1 Y.1) := by
  rw [freeMul, liftLin_toFree, liftLin_toFree]
theorem isBilinMul_freeMul {U U' : Set R4} {F B : FreeSep} (hF : F ∈ finCombIn U)
    (hB : B ∈ finCombIn U') : IsBilinMul U U' F B (freeMul F B) := by
  refine ⟨by rw [← finCombIn_eq_freeSpanIn]; exact hF, by rw [← finCombIn_eq_freeSpanIn]; exact hB, ?_⟩
  intro m m' z X z' Y hX hY
  rw [hX.2, hY.2]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [freeMul_toFree ⟨X b, (hX.1 b).1⟩ ⟨Y b', (hY.1 b').1⟩, mul_comm]
theorem mulAgrees (rules : TupleRules.TupleSpanActionRules) : MulAgrees := by
  obtain ⟨-, -, -, -, hc, -⟩ := rules
  intro U U' U'' hU hU' hU'' h1 h2 h3 F hF B hB B' hB'
  have e : ∀ G H : FreeSep, freeMul G H = mulOverSupport G H := freeMul_apply
  have c1 := (hc U U' hU hU' h1).1 F hF B hB
  have c2 := (hc U U'' hU hU'' h2).1 F hF B' hB'
  have c3 := (hc U' U'' hU' hU'' h3).1 B hB B' hB'
  refine ⟨c1.1, e _ _, isBilinMul_freeMul hF hB, ⟨c1.1, c2.1, c3.1⟩, ?_,
    isBilinMul_freeMul c1.2 hB'⟩
  rw [← e, ← e]
  rfl
theorem complexTuplesAgree (rules : TupleRules.TupleSpanActionRules) :
    ComplexTuplesAgree := by
  obtain ⟨-, -, -, -, -, -, -, ht, -⟩ := rules
  intro n h hh
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, e, -⟩ :=
    ht Set.univ isOpen_univ 1 n h hh fun _ => Set.subset_univ _
  rw [e]
  exact ⟨rfl, ⟨rfl, fun _ _ => rfl⟩, fun _ => rfl⟩
theorem tensorCompFormula : TensorCompFormula := by
  constructor
  · intro X
    rw [tensorCompZero, liftLin_toFree]
    by_cases h : X.1 = []
    · simp [tensorAtZero, tensorOfNil, h]
    · simp [tensorAtZero, h]
  · intro q hq X x
    rw [tensorComp, liftLin_toFree]
    by_cases h : X.1.length = q
    · rw [tensorAt_of_length X h, dif_pos h]
      rfl
    · rw [tensorAt_of_length_ne X h, dif_neg h]
      rfl
abbrev r4Space : LatticeLimits.ModelSpace := LatticeLimits.ModelSpace.euclidean
theorem mem_sepTuplesIn_iff (s : Conventions.StandingParameters) (n : ℕ) (f : Fin n → R4 → ℝ) :
    f ∈ LatticeLimits.ModelSpace.sepTuplesIn s r4Space n ⊤ ↔
      (List.ofFn f : FnList) ∈ sepN n := by
  rw [LatticeLimits.ModelSpace.sepTuplesIn_top]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨List.length_ofFn, ?_, ?_⟩
    · intro g hg
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
      exact ⟨h1 i, h2 i⟩
    · refine List.pairwise_ofFn.2 ?_
      intro i j hij
      exact h3 i j hij.ne
  · rintro ⟨-, h1, h2⟩
    have hm : ∀ i, f i ∈ C1c ℝ := fun i =>
      h1 _ ((List.mem_ofFn' _ _).2 ⟨i, rfl⟩)
    have h2' := List.pairwise_ofFn.1 h2
    refine ⟨fun i => (hm i).1, fun i => (hm i).2, fun i k hik => ?_⟩
    rcases lt_or_gt_of_ne hik with h | h
    · exact h2' h
    · exact (h2' h).symm
theorem sepClassesAgree : SepClassesAgree := mem_sepTuplesIn_iff
theorem cTensor_eq_tensorOfFns (s : Conventions.StandingParameters) {q : ℕ} (f : Fin q → R4 → ℝ) :
    LatticeLimits.ModelSpace.cTensor s r4Space f =
      tensorOfFns fun l x => (f l x : ℂ) := by
  funext y
  change (((∏ l, f l (y l) : ℝ)) : ℂ) = ∏ l, ((f l (y l) : ℝ) : ℂ)
  push_cast
  rfl
theorem supp_ofReal (g : R4 → ℝ) : supp (fun x => (g x : ℂ)) = supp g := by apply _root_.YangMills.Construction.EuclideanFunctionals.RealTuples.supp_ofReal <;> assumption
theorem ofReal_mem_C1c {g : R4 → ℝ} (hg : g ∈ C1c ℝ) :
    (fun x => (g x : ℂ)) ∈ C1c ℂ := by apply _root_.YangMills.Construction.EuclideanFunctionals.RealTuples.ofReal_mem_C1c <;> assumption
theorem components_of_mem_sepN {n : ℕ} {f : Fin n → R4 → ℝ} (h : List.ofFn f ∈ sepN n) :
    (∀ l, f l ∈ C1c ℝ) ∧
      Pairwise fun k l => Disjoint (supp (f k)) (supp (f l)) := by
  obtain ⟨-, h1, h2⟩ := h
  refine ⟨fun i => h1 _ ((List.mem_ofFn' _ _).2 ⟨i, rfl⟩), fun i k hik => ?_⟩
  have h2' := List.pairwise_ofFn.1 h2
  rcases lt_or_gt_of_ne hik with h | h
  · exact h2' h
  · exact (h2' h).symm
theorem complexFamily_ofReal {n : ℕ} (hn : 1 ≤ n) {f : Fin n → R4 → ℝ}
    (h : List.ofFn f ∈ sepN n) : ComplexComponents fun l x => (f l x : ℂ) := by
  obtain ⟨h1, h2⟩ := components_of_mem_sepN h
  refine ⟨hn, fun l => ofReal_mem_C1c (h1 l), fun k l hkl => ?_⟩
  change Disjoint (supp fun x => (f k x : ℂ)) (supp fun x => (f l x : ℂ))
  rw [supp_ofReal, supp_ofReal]
  exact h2 hkl
theorem ofFn_get_cast (X : FnList) {q : ℕ} (h : X.length = q) :
    List.ofFn (fun i : Fin q => X.get (Fin.cast h.symm i)) = X := by
  subst h
  simp
theorem tensorComp_mem_sepTensorsTop (s : Conventions.StandingParameters) (q : ℕ) (F : FreeSep) :
    tensorComp q F ∈ LatticeLimits.ModelSpace.sepTensorsTop s r4Space q := by
  induction F using Finsupp.induction_linear with
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add f g hf hg =>
    rw [map_add]
    exact Submodule.add_mem _ hf hg
  | single X c =>
    have e : Finsupp.single X c = c • toFree X.1 := by
      rw [toFree_of_mem X.2]
      simp
    rw [e, map_smul]
    refine Submodule.smul_mem _ _ ?_
    rw [tensorComp, liftLin_toFree]
    by_cases h : X.1.length = q
    · rw [tensorAt_of_length X h]
      have hm : List.ofFn (fun i : Fin q => X.1.get (Fin.cast h.symm i)) ∈ sepN q := by
        rw [ofFn_get_cast X.1 h]
        exact ⟨h, isSeparatedList_of_mem_sepAll X.2⟩
      have := LatticeLimits.ModelSpace.cTensor_mem ((mem_sepTuplesIn_iff s q _).2 hm)
      rw [cTensor_eq_tensorOfFns] at this
      exact this
    · rw [tensorAt_of_length_ne X h]
      exact Submodule.zero_mem _
theorem tensorSpansAgree (rules : TupleRules.TupleSpanActionRules) : TensorSpansAgree := by
  obtain ⟨-, -, -, -, -, -, -, ht, -⟩ := rules
  intro s q
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [sepTensorSpan, if_pos rfl]
    exact (LatticeLimits.ModelSpace.sepTensors_zero s r4Space ⊤).symm
  · rw [sepTensorSpan, if_neg hq.ne']
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨h, hm, hd, rfl⟩
      obtain ⟨-, -, e, -⟩ :=
        ht Set.univ isOpen_univ 1 q h ⟨hq, hm, hd⟩ fun _ => Set.subset_univ _
      rw [← e]
      exact tensorComp_mem_sepTensorsTop s q _
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨(f : Fin q → R4 → ℝ), hf, rfl⟩
      have hc := complexFamily_ofReal hq ((mem_sepTuplesIn_iff s q f).1 hf)
      have hm : (tensorOfFns fun l x => (f l x : ℂ)) ∈
          Submodule.span ℂ (sepTensors q) :=
        Submodule.subset_span ⟨_, hc.mem, hc.disjoint, rfl⟩
      have e : (LatticeLimits.ModelSpace.cTensor s r4Space f : TestSpaces.PointTuple q → ℂ) =
          tensorOfFns fun l x => (f l x : ℂ) := cTensor_eq_tensorOfFns s f
      exact show (LatticeLimits.ModelSpace.cTensor s r4Space f : TestSpaces.PointTuple q → ℂ) ∈
          Submodule.span ℂ (sepTensors q) from by
        rw [e]
        exact hm
theorem functionNormsFormula (𝕜 : Type) [RCLike 𝕜] : FunctionNormsFormula 𝕜 := by
  intro c f
  refine ⟨?_, ?_, rfl⟩
  · rintro ⟨C, hC⟩
    exact isLUB_ciSup ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  · intro hT
    have hb : BddBelow {C : ℝ | 0 ≤ C ∧
        ∀ x y, ‖f x - f y‖ ≤ C * Euclidean.euclidNorm (x - y)} :=
      ⟨0, fun C hC => hC.1⟩
    have hs : TestFunctions.lipConstR4 f = sInf {C : ℝ | 0 ≤ C ∧
        ∀ x y, ‖f x - f y‖ ≤ C * Euclidean.euclidNorm (x - y)} := rfl
    rw [hs]
    refine ⟨⟨le_csInf hT fun C hC => hC.1, fun x y => ?_⟩, fun C hC => csInf_le hb hC⟩
    have hd : 0 ≤ Euclidean.euclidNorm (x - y) := Real.sqrt_nonneg _
    rcases hd.eq_or_lt with h0 | h0
    · obtain ⟨C, hC⟩ := hT
      have := hC.2 x y
      rw [← h0, mul_zero] at this ⊢
      exact this
    · rw [← div_le_iff₀ h0]
      exact le_csInf hT fun C hC => (div_le_iff₀ h0).2 (hC.2 x y)
theorem ballsAndDistsAgree : BallsAndDistsAgree := by
  refine ⟨fun x R _ => rfl, fun B B' => ⟨rfl, ?_, ?_⟩⟩
  · simp [TestFunctions.setDistR4]
  · simp [TestFunctions.setDistR4]
theorem freeSpaceFormula : FreeSpaceFormula := by
  refine ⟨fun n X hX => hX.1, fun X Y => ?_, fun U _ => finCombIn_eq_freeSpanIn U,
    fun m c X => ?_⟩
  · rw [toFree_of_mem X.2]
    by_cases h : Y = X
    · subst h
      simp
    · simp [h]
  · have e : ∀ F, freeConj F =
        Finsupp.mapRange.addMonoidHom ((starRingEnd ℂ : ℂ →+* ℂ) : ℂ →+ ℂ) F := fun _ => rfl
    rw [e, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← e, toFree_of_mem (X b).2]
    simp [freeConj]
theorem actionFormula : ActionFormula := by
  refine ⟨fun r α f x => ?_, fun r X => rfl, fun r => rfl, fun r X => ?_,
    fun v => ⟨fun x => rfl, fun α f x => EuclidMotion.actFn_transl v f x⟩⟩
  · change f (r⁻¹ (r x)) = f x
    rw [EuclidMotion.inv_apply_apply]
  · exact liftLin_toFree _ X
theorem osFormFormula (rules : TupleRules.TupleSpanActionRules) (S : ConnFamily) :
    OSFormFormula S := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hr, -⟩ := rules
  intro F hF B hB
  exact ⟨(hr.1 0 le_rfl F hF B hB).2, rfl⟩
theorem flipAndGroupsFormula : FlipAndGroupsFormula := by
  refine ⟨fun μ ν => ?_, fun x y => ?_, rfl, fun w => ?_, fun w => Iff.rfl⟩
  · simp [PeriodicLattice.coordVec, Pi.single_apply]
  · constructor
    · rintro rfl
      exact spatialProj_timeFlip x
    · rintro ⟨h1, h2⟩
      have hx := spatialProj_timeFlip x
      funext μ
      refine Fin.lastCases ?_ (fun i => ?_) μ
      · change timeFlip x 3 = y 3
        rw [hx.2, h2]
      · exact congrFun (hx.1.trans h1.symm) i
  · constructor
    · rintro ⟨f, rfl⟩
      refine ⟨rfl, f.1, fun μ => ((f.2 μ : ℤ) : ℝ), fun μ => ?_, fun x μ => rfl⟩
      rcases Int.units_eq_one_or (f.2 μ) with h | h <;> simp [h]
    · rintro ⟨hs, p, ε, hε, hw⟩
      refine ⟨(p, fun μ => if ε μ = 1 then 1 else -1), EuclidMotion.ext_of_apply fun x => ?_⟩
      rw [ofSignedFrame_apply, EuclidMotion.apply_def, hs, add_zero]
      funext μ
      rw [hw]
      rcases hε μ with h | h
      · simp [PeriodicLattice.SignedFrame.actOnVector, h]
      · have h' : ¬ (-1 : ℝ) = 1 := by norm_num
        simp [PeriodicLattice.SignedFrame.actOnVector, h, h']
theorem tensorProdFormula : TensorProdFormula :=
  ⟨fun _ _ _ _ B B' x => tensorFun_apply B B' x, fun _ _ _ => ⟨rfl, rfl⟩⟩
theorem sum_partitions_congr_cast (S : ConnFamily) {m n : ℕ} (e : m = n) (g : Fin m → R4 → ℝ)
    (f : Fin n → R4 → ℝ) (h : ∀ i, g i = f (Fin.cast e i)) :
    ∑ π ∈ SetPartition.nonSingletonPartitions m, ∏ J ∈ π.parts,
        S.evalAt J.card (List.ofFn fun k => g (J.orderEmbOfFin rfl k)) =
      ∑ π ∈ SetPartition.nonSingletonPartitions n, ∏ J ∈ π.parts,
        S.evalAt J.card (List.ofFn fun k => f (J.orderEmbOfFin rfl k)) := by
  subst e
  have : g = f := funext h
  rw [this]
theorem centeredFn_ofFn (S : ConnFamily) {n : ℕ} (f : Fin n → R4 → ℝ)
    (hf : List.ofFn f ∈ sepAll) :
    centeredFn S ⟨List.ofFn f, hf⟩ =
      ∑ π ∈ SetPartition.nonSingletonPartitions n, ∏ J ∈ π.parts,
        S.evalAt J.card (List.ofFn fun k => f (J.orderEmbOfFin rfl k)) :=
  sum_partitions_congr_cast S List.length_ofFn (List.ofFn f).get f fun i => by
    simp
    rfl
theorem centeredAt_of_mem (S : ConnFamily) {X : FnList} (hX : X ∈ sepAll) :
    centeredAt S X = centeredFn S ⟨X, hX⟩ := dif_pos hX
theorem centeredFnFree_toFree (S : ConnFamily) (X : sepAll) :
    centeredFnFree S (toFree X.1) = (centeredFn S X : ℂ) :=
  liftLin_toFree _ X
theorem centeredFnFormula (S : ConnFamily) : CenteredFnFormula S := by
  refine ⟨?_, fun f hf => ?_, fun n _ f hf => ?_, centeredFnFree_toFree S⟩
  · have h0 : ([] : FnList) ∈ sepAll := (Ambient.emptyList _ _).2
    rw [centeredAt_of_mem S h0]
    obtain ⟨π, hπ, hp⟩ := LatticeLimits.ModelSpace.nonSingletonPartitions_zero
    change ∑ π ∈ SetPartition.nonSingletonPartitions 0, _ = _
    rw [hπ]
    simp [hp]
  · rw [centeredAt_of_mem S hf]
    have hb : SetPartition.nonSingletonPartitions 1 = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun π _ h => ?_
      obtain ⟨J, hJ⟩ := π.parts_nonempty (by simp)
      have h2 := h J hJ
      have h1 := Finset.card_le_univ J
      simp at h1
      omega
    change ∑ π ∈ SetPartition.nonSingletonPartitions 1, _ = _
    rw [hb]
    simp
  · have hm : List.ofFn f ∈ sepAll := hf
    rw [centeredAt_of_mem S hm, centeredFn_ofFn]
theorem extend_familyOnSep (S : ConnFamily) (s : Conventions.StandingParameters) {n : ℕ}
    (hn : 2 ≤ n) {w : Fin n → R4 → ℝ}
    (hw : w ∈ LatticeLimits.ModelSpace.sepTuplesIn s r4Space n ⊤) :
    (familyOnSep S s n).extend w = Ambient.evalOrZero (S.fn n hn) (List.ofFn w) := by
  rw [LatticeLimits.ModelSpace.TupleFunctional.extend_of_mem _ hw]
  simp [familyOnSep, Ambient.ConnectedFamily.evalAt, hn]
theorem mem_sepTuplesIn_of_c1 (s : Conventions.StandingParameters) {n : ℕ} {D : Fin n → Set R4}
    (hD : ∀ l k, l ≠ k → Disjoint (D l) (D k)) {w : Fin n → R4 → ℝ}
    (hw : ∀ l, w l ∈ LatticeLimits.ModelSpace.c1CompactSupp s r4Space (D l)) :
    w ∈ LatticeLimits.ModelSpace.sepTuplesIn s r4Space n ⊤ := by
  rw [LatticeLimits.ModelSpace.sepTuplesIn_top]
  exact ⟨fun l => (hw l).1, fun l => (hw l).2.1, fun i k hik =>
    (hD i k hik).mono (hw i).2.2 (hw k).2.2⟩
theorem isMultilinearSeq_familyOnSep (tc : TensorComponents.CenteredSeesTensorComps)
    (S : ConnFamily) (s : Conventions.StandingParameters) :
    LatticeLimits.ModelSpace.IsMultilinearSeq (familyOnSep S s) := by
  intro n hn (D : Fin n → Set R4) _ hdis (g : Fin n → R4 → ℝ) hg i (u : R4 → ℝ) hu
    (v : R4 → ℝ) hv α β
  have hup : ∀ z : R4 → ℝ, z ∈ LatticeLimits.ModelSpace.c1CompactSupp s r4Space (D i) →
      Function.update g i z ∈ LatticeLimits.ModelSpace.sepTuplesIn s r4Space n ⊤ := by
    intro z hz
    refine mem_sepTuplesIn_of_c1 s hdis fun l => ?_
    by_cases h : l = i
    · subst h
      rw [Function.update_self]
      exact hz
    · rw [Function.update_of_ne h]
      exact hg l
  have hu' := (mem_sepTuplesIn_iff s n _).1 (hup u hu)
  have hv' := (mem_sepTuplesIn_iff s n _).1 (hup v hv)
  obtain ⟨h1, -⟩ := tc S
  have hvv : (List.ofFn (Function.update (Function.update g i u) i v) : FnList) ∈
      sepN n := by
    rw [Function.update_idem]
    exact hv'
  obtain ⟨hm, -, h3⟩ := h1 n (by omega) i (Function.update g i u) v hu' hvv α β
  rw [Function.update_self, Function.update_idem] at hm
  have h3' := h3 hn
  rw [Function.update_self] at h3'
  have e1 : Function.update (Function.update g i u) i (α • u + β • v) =
      Function.update g i (α • u + β • v) := Function.update_idem ..
  have e2 : Function.update (Function.update g i u) i v = Function.update g i v :=
    Function.update_idem ..
  have c1 := congrArg (fun Z : Fin n → R4 → ℝ => Ambient.evalOrZero (S.fn n hn) (List.ofFn Z)) e1
  have c2 := congrArg (fun Z : Fin n → R4 → ℝ => Ambient.evalOrZero (S.fn n hn) (List.ofFn Z)) e2
  have a1 := extend_familyOnSep S s hn ((mem_sepTuplesIn_iff s n _).2 hm)
  have a2 := extend_familyOnSep S s hn (hup u hu)
  have a3 := extend_familyOnSep S s hn (hup v hv)
  exact a1.trans (c1.symm.trans (h3'.trans
    (congrArg₂ (fun x y => α * x + β * y) a2.symm (c2.trans a3.symm))))
theorem centredSum_familyOnSep (S : ConnFamily) (s : Conventions.StandingParameters) (q : ℕ)
    (h : Fin q → R4 → ℝ) (hh : h ∈ LatticeLimits.ModelSpace.sepTuplesIn s r4Space q ⊤) :
    LatticeLimits.ModelSpace.centredSum (familyOnSep S s) q ⟨h, hh⟩ =
      centeredAt S (List.ofFn h) := by
  have hm : (List.ofFn h : FnList) ∈ sepAll :=
    Ambient.separatedN_subset_separatedAll _ _ q ((mem_sepTuplesIn_iff s q h).1 hh)
  refine Eq.trans ?_ (centeredAt_of_mem S hm).symm
  refine Eq.trans ?_ (centeredFn_ofFn S h hm).symm
  rfl
theorem complexTuple_ofReal {n : ℕ} (f : Fin n → R4 → ℝ) :
    complexTuple (fun l x => (f l x : ℂ)) = toFree (List.ofFn f) := by
  have h : ∀ l, IsRealValued fun x => (f l x : ℂ) := fun l x => by simp
  rw [complexTuple, if_pos h]
  simp
theorem centeredOnTensor_eq_centredLinearForm (rules : TupleRules.TupleSpanActionRules)
    (tc : TensorComponents.CenteredSeesTensorComps)
    (rel : LatticeLimits.TensorRelations.Claim)
    (S : ConnFamily) (s : Conventions.StandingParameters) (q : ℕ) (hq : 1 ≤ q)
    (T : LatticeLimits.ModelSpace.sepTensors s r4Space q ⊤) :
    centeredOnTensor S q T.1 =
      LatticeLimits.ModelSpace.centredLinearForm (familyOnSep S s) q T := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have hsp := tensorSpansAgree rules s (p + 1)
  have hmem : ∀ B : LatticeLimits.ModelSpace.sepTensors s r4Space (p + 1) ⊤,
      (B.1 : TestSpaces.PointTuple (p + 1) → ℂ) ∈ sepTensorSpan (p + 1) := fun B => by
    rw [hsp]
    exact B.2
  obtain ⟨-, -, ⟨hlin, hnum, hsep, -⟩, -⟩ := tc S
  have hL := (hlin (p + 1)).2.2
  have hadd : ∀ B ∈ sepTensorSpan (p + 1), ∀ B' ∈ sepTensorSpan (p + 1),
      centeredOnTensor S (p + 1) (B + B') =
        centeredOnTensor S (p + 1) B + centeredOnTensor S (p + 1) B' := fun B hB B' hB' => by
    have := hL B hB B' hB' 1 1
    simpa using this
  have hsmul : ∀ (c : ℂ), ∀ B ∈ sepTensorSpan (p + 1),
      centeredOnTensor S (p + 1) (c • B) = c * centeredOnTensor S (p + 1) B := fun c B hB => by
    have := hL B hB 0 (zero_mem _) c 0
    simpa using this
  let Λ : LatticeLimits.ModelSpace.sepTensors s r4Space (p + 1) ⊤ →ₗ[ℂ] ℂ :=
    { toFun := fun B => centeredOnTensor S (p + 1) B.1
      map_add' := fun B B' => hadd _ (hmem B) _ (hmem B')
      map_smul' := fun c B => hsmul c _ (hmem B) }
  have hΛ : LatticeLimits.ModelSpace.IsCentredLinearForm (familyOnSep S s) (p + 1) Λ := by
    intro (h : Fin (p + 1) → R4 → ℝ) hh
    have hm := (mem_sepTuplesIn_iff s (p + 1) h).1 hh
    have hc := complexFamily_ofReal (by omega) hm
    have e1 : centeredOnTensor S (p + 1) (LatticeLimits.ModelSpace.cTensor s r4Space h) =
        centeredOnTensor S (p + 1) (tensorOfFns fun l x => (h l x : ℂ)) :=
      congrArg (centeredOnTensor S (p + 1)) (cTensor_eq_tensorOfFns s h)
    refine e1.trans ?_
    rw [hsep _ _ hc, complexTuple_ofReal]
    have hs : (List.ofFn h : FnList) ∈ sepAll := Ambient.separatedN_subset_separatedAll _ _ _ hm
    refine (centeredFnFree_toFree S ⟨_, hs⟩).trans ?_
    rw [centredSum_familyOnSep S s _ h hh, centeredAt_of_mem S hs]
  have hu := ((rel s r4Space (p + 1) ⊤ (by omega) (by simp)).2 (familyOnSep S s)
    (isMultilinearSeq_familyOnSep tc S s)).2
  have he : LatticeLimits.ModelSpace.IsCentredLinearForm (familyOnSep S s) (p + 1)
      (Classical.epsilon
        (LatticeLimits.ModelSpace.IsCentredLinearForm (familyOnSep S s) (p + 1))) :=
    Classical.epsilon_spec ⟨Λ, hΛ⟩
  have hΛe := hu.unique hΛ he
  change Λ T = _
  rw [hΛe]
  rfl
theorem functionalsAgree (rules : TupleRules.TupleSpanActionRules)
    (tc : TensorComponents.CenteredSeesTensorComps)
    (rel : LatticeLimits.TensorRelations.Claim)
    (S : ConnFamily) (s : Conventions.StandingParameters) : FunctionalsAgree S s :=
  ⟨isMultilinearSeq_familyOnSep tc S s, centredSum_familyOnSep S s,
    fun q hq T => centeredOnTensor_eq_centredLinearForm rules tc rel S s q hq T⟩
theorem twoSettingsAgree (rules : TupleRules.TupleSpanActionRules)
    (tc : TensorComponents.CenteredSeesTensorComps)
    (rel : LatticeLimits.TensorRelations.Claim) : TwoSettingsAgree :=
  ⟨affineIsometryIffMotion, mulAgrees rules, complexTuplesAgree rules, tensorCompFormula,
    tensorSpansAgree rules, sepClassesAgree, functionalsAgree rules tc rel,
    functionNormsFormula ℝ, functionNormsFormula ℂ, ballsAndDistsAgree, freeSpaceFormula,
    actionFormula, fun S => ⟨centeredFnFormula S, osFormFormula rules S⟩, flipAndGroupsFormula,
    tensorProdFormula⟩
end YangMills.Construction.EuclideanFunctionals.TwoSettings
