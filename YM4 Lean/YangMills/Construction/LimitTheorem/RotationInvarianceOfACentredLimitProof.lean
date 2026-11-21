import YangMills.Construction.TwoPoints.GrowthOfTheAxisDecayFunctionAtTheOriginProof
import YangMills.Construction.EuclideanFunctionals.PlateBoundFromTheInsertionBoundWithData
import YangMills.Construction.EuclideanFunctionals.RaisingContractsAnInsertionMovedInTimeAndThePlateBoundAtEveryFraction
import YangMills.Construction.LimitTheorem.EuclideanFunctionalOfABoundedApproximationProof
import YangMills.Construction.SystemsWithFiveBounds.RotationsAtTheChosenConstantsProof
import YangMills.Construction.TwoPoints.ConjugatesIsometriesAndReflectionsUnderTheBilinearExtension
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FirstPassageSeqs.CenteredLimitRotation
open MeasureTheory Filter
open scoped Topology ComplexOrder
open ReflectionPositivity.AxisMirror RealPlane
open EuclideanFunctionals
open EuclideanFunctionals.TwoPointRotationCriterion
open EuclideanFunctionals.TimeShiftAndFractions
open EuclideanFunctionals.SlabInsertionTransfer
open PairFunctions
open TwoPoints (compactC1Real euclideanMotions DisjointSupports)
open ComplexTestFunctions (ComplexValued)
theorem exists_productBoundParams {p C cI : ℝ} (hp : 0 ≤ p) (hC : 0 ≤ C) (h₀ : 0 < cI) (h₁ : cI < 1 / 8) :
    ∃ cS cPar cCau, ProductBoundParams p C cI cS cPar cCau :=
  ⟨1 / 32, cI / 2, 1 / 128, hp, hC, h₀, h₁, by norm_num, by linarith, by norm_num,
    by linarith, by linarith, by norm_num⟩
theorem actFn_ofOrthogonalMatrix {α : Type*} (R : Matrix.orthogonalGroup (Fin 4) ℝ) (f : R4 → α) :
    (EuclidMotion.ofOrthogonalMatrix R).actFn f = TwoPoints.rotateFun R f := by apply _root_.YangMills.SharedProofs.p36578 <;> assumption
theorem exists_orthogonalMatrix_of_offset_eq_zero (r : EuclidMotion) (h : r.offset = 0) :
    ∃ R : Matrix.orthogonalGroup (Fin 4) ℝ, EuclidMotion.ofOrthogonalMatrix R = r := by
  have hn : ∀ x : R4, r.lin x ⬝ᵥ r.lin x = x ⬝ᵥ x := by
    intro x
    have h1 := r.lin_norm x
    simp only [TorusMetric.euclidNormVec] at h1
    have h2 := (Real.sqrt_inj (Finset.sum_nonneg fun μ _ => sq_nonneg _)
      (Finset.sum_nonneg fun μ _ => sq_nonneg _)).1 h1
    simpa [dotProduct, sq] using h2
  have hp : ∀ x y : R4, r.lin x ⬝ᵥ r.lin y = x ⬝ᵥ y := by
    intro x y
    have h1 := hn (x + y)
    simp only [map_add, add_dotProduct, dotProduct_add, hn] at h1
    rw [dotProduct_comm (r.lin y), dotProduct_comm y x] at h1
    linarith
  have hA : ∀ x : R4, (LinearMap.toMatrix' r.lin).mulVec x = r.lin x :=
    fun x => LinearMap.toMatrix'_mulVec _ x
  have hT : (LinearMap.toMatrix' r.lin).transpose * LinearMap.toMatrix' r.lin = 1 := by
    ext i j
    have h1 := hp (Pi.single i 1) (Pi.single j 1)
    rw [← hA, ← hA] at h1
    rw [show (1 : Matrix (Fin 4) (Fin 4) ℝ) i j = if j = i then 1 else 0 by
      simp [Matrix.one_apply, eq_comm]]
    simpa [dotProduct, Matrix.mul_apply, Pi.single_apply] using h1
  refine ⟨⟨LinearMap.toMatrix' r.lin, (Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).2 ?_⟩,
    EuclidMotion.ext_of_apply fun x => ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using hT
  · rw [EuclidMotion.ofOrthogonalMatrix_apply, r.apply_def, h, add_zero]
    exact hA x
theorem imagePlaneRotation_one_offset (t : ℝ) :
    (imagePlaneRotation (1 : EuclideanFunctionals.hyperoctahedral) t).offset = 0 := by
  have hs : ∀ r : EuclidMotion, r.offset = r 0 := fun r => by
    rw [r.apply_def, map_zero, zero_add]
  have hr : rotateMotion t 0 = 0 := by
    rw [← hs]
    rfl
  have h1 : imagePlaneRotation (1 : EuclideanFunctionals.hyperoctahedral) t = rotateMotion t := by
    simp [imagePlaneRotation]
  rw [h1, hs, hr]
section TwoPoint
variable {c : SharpScale} {S : ConnFamily}
theorem ofFn_mem_sepN_two {f h : R4 → ℝ} (hm : [f, h] ∈ sepPairs) : List.ofFn ![f, h] ∈ sepN 2 := by
  simpa using hm
theorem isSymmOnPairs_two (e : EuclidFunctionalWithRecon c S) :
    IsSymmOnPairs (S.fn 2 le_rfl) := by
  intro f h hm
  have key := e.symm 2 le_rfl ![f, h] (ofFn_mem_sepN_two hm) (Equiv.swap 0 1)
  have e₁ : List.ofFn (fun i : Fin 2 => (![f, h] : Fin 2 → R4 → ℝ) ((Equiv.swap (0 : Fin 2) 1) i)) = [h, f] := by
    simp [List.ofFn_succ]
  have e₂ : List.ofFn (![f, h] : Fin 2 → R4 → ℝ) = [f, h] := by
    simp [List.ofFn_succ]
  exact ((congrArg (Ambient.evalOrZero (S.fn 2 le_rfl)) e₁).symm.trans
    (key.trans (congrArg (Ambient.evalOrZero (S.fn 2 le_rfl)) e₂))).symm
theorem exists_hyperoctahedral_transl_of_mem {r : Equiv.Perm R4} (hr : r ∈ euclideanMotions) :
    ∃ w ∈ EuclideanFunctionals.hyperoctahedral, ∃ v : R4, ∀ x, r x = EuclidMotion.transl v (w x) := by
  obtain ⟨w, ⟨π, s, rfl⟩, v, hv⟩ := hr
  refine ⟨EuclideanFunctionals.ofSignedFrame (π, s), ⟨(π, s), rfl⟩, v, fun x => ?_⟩
  rw [hv, EuclidMotion.transl_apply, EuclideanFunctionals.ofSignedFrame_apply]
  rfl
theorem actOn_eq_actFn {α : Type*} {r : Equiv.Perm R4} {q : EuclidMotion} (h : ∀ x, r x = q x) (f : R4 → α) :
    TwoPoints.actOn r f = q.actFn f := by
  funext x
  show f (r⁻¹ x) = f (q⁻¹ x)
  congr 1
  have h₁ : r (q⁻¹ x) = x := by
    rw [h]
    exact q.apply_inv_apply x
  rw [Equiv.Perm.inv_eq_iff_eq]
  exact h₁.symm
theorem actList_mem_sepAll (hT : TupleRules.TupleSpanActionRules) (r : EuclidMotion) {X : FnList}
    (hX : X ∈ sepAll) : r.actList X ∈ sepAll := by apply _root_.YangMills.Construction.FirstPassageSeqs.BoundedApprox.actList_mem_sepAll <;> assumption
theorem actFn_mul {α : Type*} (a b : EuclidMotion) (f : R4 → α) :
    (a * b).actFn f = a.actFn (b.actFn f) := by apply _root_.YangMills.Construction.EuclideanFunctionals.MotionProofs.actFn_mul <;> assumption
theorem evalPair_actOn_motion (hT : TupleRules.TupleSpanActionRules) (e : EuclidFunctionalWithRecon c S)
    {r : Equiv.Perm R4} (hr : r ∈ euclideanMotions) {f h : R4 → ℝ} (hm : [f, h] ∈ sepPairs) :
    evalPair (S.fn 2 le_rfl) (TwoPoints.actOn r f) (TwoPoints.actOn r h) =
      evalPair (S.fn 2 le_rfl) f h := by
  obtain ⟨w, hw, v, hv⟩ := exists_hyperoctahedral_transl_of_mem hr
  have hq : ∀ x, r x = (EuclidMotion.transl v * w) x := fun x => by
    rw [EuclidMotion.mul_apply]
    exact hv x
  rw [actOn_eq_actFn hq, actOn_eq_actFn hq, actFn_mul, actFn_mul]
  have h₁ := ((e.invariant 2 le_rfl [f, h] hm).2 w hw)
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (actList_mem_sepAll hT w (Set.mem_iUnion.2 ⟨2, hm⟩))
  have hm₂ : w.actList [f, h] ∈ sepN 2 := ⟨rfl, hn.2⟩
  have h₂ := (e.invariant 2 le_rfl _ hm₂).1 v
  exact h₂.trans h₁.symm
theorem timeReflection_eq_reflectAcross (x : R4) :
    TimeAxis.timeReflection x = TwoPoints.reflectAcross (PeriodicLattice.coordVec 3) x := by
  funext ν
  fin_cases ν <;>
    simp [TimeAxis.timeReflection, TwoPoints.reflectAcross, TwoPoints.euclidDot, PeriodicLattice.coordVec,
      Fin.sum_univ_four] <;> ring
theorem euclidDot_timeAxis (x : R4) :
    TwoPoints.euclidDot (PeriodicLattice.coordVec 3) x = x 3 := by apply _root_.YangMills.Construction.TwoPoints.AxisDecayGrowthAtZero.euclidDot_coordVec_three <;> assumption
theorem euclidNorm_timeAxis : TwoPoints.euclidNorm (PeriodicLattice.coordVec 3 : R4) = 1 := by
  simp [TwoPoints.euclidNorm, PeriodicLattice.coordVec, Fin.sum_univ_four]
def diagonalUnitNormal : R4 :=
  (Real.sqrt 2)⁻¹ • (PeriodicLattice.coordVec 0 + PeriodicLattice.coordVec 1)
theorem euclidNorm_diagonalUnitNormal : TwoPoints.euclidNorm diagonalUnitNormal = 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e : ∑ μ, diagonalUnitNormal μ ^ 2 = 1 := by
    simp [diagonalUnitNormal, PeriodicLattice.coordVec, Fin.sum_univ_four, mul_pow, inv_pow, h2]
    norm_num
  rw [TwoPoints.euclidNorm, e, Real.sqrt_one]
theorem diagonalUnitNormal_mem_representatives : diagonalUnitNormal ∈ TwoPoints.normalRepresentatives :=
  Or.inl (Or.inr ⟨0, 1, by norm_num, rfl⟩)
theorem diagonalUnitNormal_mem_diagNormals : diagonalUnitNormal ∈ TwoPoints.diagNormals :=
  ⟨0, 1, 1, 1, by norm_num, Or.inl rfl, Or.inl rfl, by simp [diagonalUnitNormal]⟩
theorem isRealNonneg_reflected_pairing (hExt : ConjIsometryReflection.ReflectedTwoPointFunction (S.fn 2 le_rfl))
    (hPos : CenteredIsReflectionPositive S) {n : R4} (hn : TwoPoints.euclidNorm n = 1)
    (h16 : n ∈ TwoPoints.normalRepresentatives) {f : ComplexValued}
    (hf : f ∈ TwoPoints.cc1In {x : R4 | 0 < TwoPoints.euclidDot n x}) :
    TwoPoints.IsRealNonneg (complexExtension (S.fn 2 le_rfl) (TwoPoints.reflectFun n (TwoPoints.conjFun f)) f) := by
  obtain ⟨hF, -, e⟩ := hExt S rfl n hn f hf
  have h := (hPos n hn (Or.inl h16) _ hF).2
  rw [e] at h
  exact ⟨(Complex.le_def.1 h).2.symm, (Complex.le_def.1 h).1⟩
theorem sharpNormR4_ofRealFun (M : ℝ) (g : R4 → ℝ) :
    TestFunctions.sharpNormR4 M (ComplexTestFunctions.ofRealFun g) = TestFunctions.sharpNormR4 M g := by
  have h₁ : TestFunctions.uniformNorm (ComplexTestFunctions.ofRealFun g) = TestFunctions.uniformNorm g := by
    unfold TestFunctions.uniformNorm
    congr 1
    funext x
    simp [ComplexTestFunctions.ofRealFun]
  have h₂ : TestFunctions.lipConstR4 (ComplexTestFunctions.ofRealFun g) = TestFunctions.lipConstR4 g := by
    unfold TestFunctions.lipConstR4 TestFunctions.bestLipschitzConstant
    congr 1
    ext C
    have e : ∀ x y, ‖ComplexTestFunctions.ofRealFun g x - ComplexTestFunctions.ofRealFun g y‖ = ‖g x - g y‖ := fun x y => by
      simp only [ComplexTestFunctions.ofRealFun, ← Complex.ofReal_sub, Complex.norm_real]
    simp only [Set.mem_setOf_eq, e]
  unfold TestFunctions.sharpNormR4
  rw [h₁, h₂]
theorem ofRealFun_rePart {f : ComplexValued} (hf : ∀ x, (f x).im = 0) :
    ComplexTestFunctions.ofRealFun (ComplexTestFunctions.rePart f) = f := by
  funext x
  exact Complex.ext (by simp [ComplexTestFunctions.ofRealFun, ComplexTestFunctions.rePart]) (by
    simp [ComplexTestFunctions.ofRealFun, hf x])
theorem hasBallDecayBound_realPartForm (St : TwoPoints.FixedScale) (hSt : St.scale = c.M) {C : ℕ → ℝ → ℝ → ℝ}
    (hLB : HasClusterBounds S c C) (hP : TwoPointHypotheses S C) :
    TwoPoints.HasBallDecayBound St (realPartForm (S.fn 2 le_rfl)) := by
  refine ⟨fun d R => C 2 d R, hP.nonneg, hP.antitone, fun d R hd hR x x' f hf h hh hbf hbh hdist => ?_⟩
  set g₁ := ComplexTestFunctions.rePart f with hg₁
  set g₂ := ComplexTestFunctions.rePart h with hg₂
  have hs₁ : tsupport g₁ ⊆ tsupport f := ComplexTupleComponents.tsupport_rePart_subset f
  have hs₂ : tsupport g₂ ⊆ tsupport h := ComplexTupleComponents.tsupport_rePart_subset h
  have hdis : DisjointSupports f h := by
    refine Set.disjoint_left.2 fun y hy hy' => ?_
    have := hdist y hy y hy'
    simp [TwoPoints.euclidNorm] at this
    linarith
  have hm : [g₁, g₂] ∈ sepPairs := (parts_mem_sepPairs hf.1 hh.1 hdis).1
  have hsup : ∀ u : R4 → ℝ, EuclideanFunctionals.supp u = tsupport u := fun u =>
    InfiniteLattice.SeparationR4.closedSupport_euclidean_eq_tsupport defaultMirrorData u
  have hpair : ENNReal.ofReal d ≤ TestFunctions.setDistR4 (tsupport g₁) (tsupport g₂) :=
    le_iInf₂ fun y hy => le_iInf₂ fun y' hy' => ENNReal.ofReal_le_ofReal (hdist y (hs₁ hy) y' (hs₂ hy'))
  have hpair' : ENNReal.ofReal d ≤ TestFunctions.setDistR4 (tsupport g₂) (tsupport g₁) :=
    le_iInf₂ fun y hy => le_iInf₂ fun y' hy' => ENNReal.ofReal_le_ofReal (by
      have := hdist y' (hs₁ hy') y (hs₂ hy)
      have e : TorusMetric.euclidNormVec (y - y') = TwoPoints.euclidNorm (y' - y) := by
        rw [TwoPoints.euclidNorm_eq_euclidNormVec]
        simp only [TorusMetric.euclidNormVec, Pi.sub_apply]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e]
      exact this)
  have hb := hLB 2 le_rfl R d hR hd ![g₁, g₂] (ofFn_mem_sepN_two hm) (fun i => by
      fin_cases i
      · refine ⟨x, ?_⟩
        show EuclideanFunctionals.supp g₁ ⊆ _
        rw [hsup]
        exact hs₁.trans hbf
      · refine ⟨x', ?_⟩
        show EuclideanFunctionals.supp g₂ ⊆ _
        rw [hsup]
        exact hs₂.trans hbh) (fun i j hij => by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · show ENNReal.ofReal d ≤ TestFunctions.setDistR4 (EuclideanFunctionals.supp g₁) (EuclideanFunctionals.supp g₂)
        rw [hsup, hsup]
        exact hpair
      · show ENNReal.ofReal d ≤ TestFunctions.setDistR4 (EuclideanFunctionals.supp g₂) (EuclideanFunctionals.supp g₁)
        rw [hsup, hsup]
        exact hpair'
      · exact absurd rfl hij)
  have hX : (⟨[g₁, g₂], hm⟩ : sepPairs) = ⟨List.ofFn ![g₁, g₂], ofFn_mem_sepN_two hm⟩ :=
    Subtype.ext (by simp [List.ofFn_succ])
  have hb₂ : |S.fn 2 le_rfl ⟨[g₁, g₂], hm⟩| ≤ C 2 d R * (c.sharpNorm g₁ * c.sharpNorm g₂) :=
    (congrArg (fun X => |S.fn 2 le_rfl X|) hX).le.trans
      (hb.trans_eq (congrArg (C 2 d R * ·) (Fin.prod_univ_two _)))
  have e₂ : realPartForm (S.fn 2 le_rfl) f h = S.fn 2 le_rfl ⟨[g₁, g₂], hm⟩ := evalPair_of_mem _ hm
  have e₃ : St.sharpNorm f = c.sharpNorm g₁ := by
    show TestFunctions.sharpNormR4 St.scale f = TestFunctions.sharpNormR4 c.M g₁
    rw [hSt, ← sharpNormR4_ofRealFun, hg₁, ofRealFun_rePart hf.2]
  have e₄ : St.sharpNorm h = c.sharpNorm g₂ := by
    show TestFunctions.sharpNormR4 St.scale h = TestFunctions.sharpNormR4 c.M g₂
    rw [hSt, ← sharpNormR4_ofRealFun, hg₂, ofRealFun_rePart hh.2]
  show |realPartForm (S.fn 2 le_rfl) f h| ≤ C 2 d R * St.sharpNorm f * St.sharpNorm h
  rw [e₂, e₃, e₄, mul_assoc]
  exact hb₂
end TwoPoint
theorem invMap_coe (r : EuclidMotion) : SeparatedTuples.invMap (⇑r) = ⇑(r⁻¹) := by apply _root_.YangMills.Construction.FirstPassageSeqs.BoundedApprox.invMap_coe <;> assumption
def realTupleAsComplex (X : SeparatedTuples.SepTuple) : Fin X.1.length → R4 → ℂ :=
  fun l x => ((X.1.get l x : ℝ) : ℂ)
theorem realTupleAsComplex_mem (X : SeparatedTuples.SepTuple) :
    realTupleAsComplex X ∈ disjointComplexTuples X.1.length := by
  have hs : ∀ u : R4 → ℂ, supp u = tsupport u := fun u =>
    SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
  have ht : ∀ l, tsupport (realTupleAsComplex X l) = tsupport (X.1.get l) := fun l => by
    have : Function.support (realTupleAsComplex X l) = Function.support (X.1.get l) := by
      ext x
      simp [realTupleAsComplex, Function.mem_support]
    simp only [tsupport, this]
  refine ⟨fun l => (mem_C1c_iff_mem_compactC1 _).2 ?_, fun k l hkl => ?_⟩
  · have hf := X.2.1 _ (List.get_mem X.1 l)
    exact ⟨Complex.ofRealCLM.contDiff.comp hf.1, hf.2.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)⟩
  · show Disjoint (supp (realTupleAsComplex X k)) (supp (realTupleAsComplex X l))
    rw [hs, hs, ht, ht]
    rcases lt_or_gt_of_ne hkl with h | h
    · exact List.pairwise_iff_get.1 X.2.2 k l h
    · exact (List.pairwise_iff_get.1 X.2.2 l k h).symm
theorem complexTuple_realTupleAsComplex (X : SeparatedTuples.SepTuple) :
    complexTuple (realTupleAsComplex X) = toFree X.1 := by
  unfold complexTuple
  have hr : ∀ l, IsRealValued (realTupleAsComplex X l) := fun l x => by simp [realTupleAsComplex]
  rw [if_pos hr]
  congr 1
  have : (fun (l : Fin X.1.length) x => (realTupleAsComplex X l x).re) = X.1.get := by
    funext l x
    simp [realTupleAsComplex]
  rw [this, List.ofFn_get]
theorem isO4Invariant_of_complexInvariant (hT : TupleRules.TupleSpanActionRules) {S : ConnFamily}
    {τ : SeparatedTuples.TupleFunctional} (hτ : τ.toFun = onSepTuples (centeredFn S))
    (hF : OrthogonalInvariantOnComplexTuples S) : LimitTheorem.IsO4InvariantFunctional τ := by
  intro R X
  have hsX : X.1 ∈ sepAll :=
    (R4TupleForms.isDisjointlySupported_iff_mem_separatedAll defaultMirrorData X.1).1 X.2
  set q := EuclidMotion.ofOrthogonalMatrix R with hq
  have hsY := actList_mem_sepAll hT q hsX
  have key := hF R _ (realTupleAsComplex X) (realTupleAsComplex_mem X)
  rw [complexTuple_realTupleAsComplex, EuclidMotion.actFree, liftLin_toFree _ ⟨X.1, hsX⟩] at key
  have e₁ : ∀ (Y : FnList) (hY : Y ∈ sepAll),
      centeredFnFree S (toFree Y) = ((centeredFn S ⟨Y, hY⟩ : ℝ) : ℂ) :=
    fun Y hY => by
      rw [centeredFnFree, liftReal]
      exact liftLin_toFree _ ⟨Y, hY⟩
  rw [e₁ _ hsY, e₁ _ hsX] at key
  have hcancelled' := Complex.ofReal_injective key
  have hl : SeparatedTuples.pushList (⇑q) X.1 = q.actList X.1 := by
    simp only [SeparatedTuples.pushList, invMap_coe, EuclidMotion.actList]
    rfl
  have hsep : SeparatedTuples.IsDisjointlySupported (SeparatedTuples.pushList (⇑q) X.1) := by
    rw [hl]
    exact (R4TupleForms.isDisjointlySupported_iff_mem_separatedAll defaultMirrorData _).2 hsY
  have hact : SeparatedTuples.push (LimitTheorem.orthogonalMap R) X =
      ⟨SeparatedTuples.pushList (⇑q) X.1, hsep⟩ := by
    have hm : LimitTheorem.orthogonalMap R = ⇑q := rfl
    rw [hm]
    unfold SeparatedTuples.push
    rw [dif_pos hsep]
  have hval : ∀ Y : SeparatedTuples.SepTuple, τ Y = centeredFn S
      ⟨Y.1, (R4TupleForms.isDisjointlySupported_iff_mem_separatedAll defaultMirrorData Y.1).1 Y.2⟩ :=
    fun Y => congrFun hτ Y
  rw [hact, hval, hval]
  refine Eq.trans (congrArg (centeredFn S) (Subtype.ext hl)) hcancelled'
theorem claim_holds (hA : BoundedApproximationLimitIsEuclidean)
    (hSlab : SlabInsertionTransfer.Holds)
    (hPlate : ProductBoundFromInsertion.Main)
    (hRaise : TimeShiftAndFractions.Holds)
    (hDecides : TwoPointCriterion)
    (hExt : ConjIsometryReflection.Statement)
    (hTwo : RotationInvarianceFromReflectedBound.Statement)
    (hT : TupleRules.TupleSpanActionRules) : Claim := by
  intro Dt T S τ hτ hB hRP hL c C hLB hP ς p CI cI hp h₀ h₁ hς hb
  obtain ⟨-, hPos, hE⟩ := hA Dt T S τ hτ hB hRP hL
  obtain ⟨⟨e, -⟩, hcone⟩ := hE c C hLB
  have hIns := hSlab c S e ς p CI cI hp h₀ h₁ hς hb
  obtain ⟨cS, cPar, cCau, hF⟩ := exists_productBoundParams hp hIns.nonneg_constant h₀ h₁
  have hPl := (hPlate c S e p CI cI cS cPar cCau (hcone e) hIns hF).2
  obtain ⟨-, -, -, hr⟩ := hRaise c S e
  have hfr : (1 / 8 : ℝ) ∈ productBoundFractions := by
    constructor <;> norm_num
  have hImage := ((hr _ _ _ hPl).2 _ hfr).2
  obtain ⟨-, -, hOne⟩ := hExt _ (isSymmOnPairs_two e) hP.linear
  have hForm := (hExt _ (isSymmOnPairs_two e) hP.linear).1.2
  let St : TwoPoints.FixedScale := ⟨c.M, lt_of_lt_of_le one_pos c.one_le⟩
  have hThree : TwoPoints.IsAdmissibleForm St (realPartForm (S.fn 2 le_rfl)) := by
    refine ⟨⟨fun r hr' f hf h hh hd => ?_, fun f hf => ?_⟩, hasBallDecayBound_realPartForm St rfl hLB hP, ?_⟩
    · have hm := (parts_mem_sepPairs hf.1 hh.1 hd).1
      exact evalPair_actOn_motion hT e hr' hm
    · have hset : {x : R4 | 0 < TwoPoints.euclidDot (PeriodicLattice.coordVec 3) x} = TimeAxis.upperHalfSpace := by
        ext x
        simp only [Set.mem_ofPred_eq, euclidDot_timeAxis]
        rfl
      have hf' : f ∈ TwoPoints.cc1In {x : R4 | 0 < TwoPoints.euclidDot (PeriodicLattice.coordVec 3) x} := by
        rw [hset]
        exact hf
      have hmir : TwoPoints.timeReflected (TwoPoints.conjFun f) =
          TwoPoints.reflectFun (PeriodicLattice.coordVec 3) (TwoPoints.conjFun f) := by
        funext x
        show TwoPoints.conjFun f (TimeAxis.timeReflection x) = _
        rw [timeReflection_eq_reflectAcross]
        rfl
      rw [hmir]
      exact isRealNonneg_reflected_pairing hOne hPos euclidNorm_timeAxis (Or.inl (Or.inl ⟨3, rfl⟩)) hf'
    · exact ⟨diagonalUnitNormal, diagonalUnitNormal_mem_diagNormals, fun f hf =>
        isRealNonneg_reflected_pairing hOne hPos euclidNorm_diagonalUnitNormal
          diagonalUnitNormal_mem_representatives hf⟩
  have hO2 := hTwo St _ hForm hThree hP.reflectedBound
  have hTwoAngles : TwoPointLocallyRotationInvariant S 1 := by
    refine ⟨1, one_pos, fun t _ f h hf hh hd => ?_⟩
    obtain ⟨R, hR⟩ := exists_orthogonalMatrix_of_offset_eq_zero (imagePlaneRotation 1 t)
      (imagePlaneRotation_one_offset t)
    have hX : [f, h] ∈ EuclideanFunctionals.sepN 2 := by
      refine ⟨rfl, ?_, ?_⟩
      · intro k hk
        rcases List.mem_pair.1 hk with rfl | rfl
        · exact hf
        · exact hh
      · exact List.Pairwise.cons (fun k hk => by
          rw [List.mem_singleton.1 hk]
          exact hd) (List.Pairwise.cons (fun _ hk => absurd hk List.not_mem_nil) List.Pairwise.nil)
    have h3 := hO2 R f h hX
    rw [← actFn_ofOrthogonalMatrix, ← actFn_ofOrthogonalMatrix, hR] at h3
    exact h3
  have hD := hDecides c S e (hcone e) 1 _ (1 / 8) hPl.pos_exponent hfr hImage
  have hO := hD.1.1 hTwoAngles
  exact ⟨hO, hD.2 hTwoAngles hO, isO4Invariant_of_complexInvariant hT hτ (hD.2 hTwoAngles hO)⟩
end YangMills.Construction.FirstPassageSeqs.CenteredLimitRotation
end
