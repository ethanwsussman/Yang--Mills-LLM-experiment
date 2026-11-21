import YangMills.Construction.InfiniteLattice.StatesReflectionPositiveAtEveryLatticeMirror
import YangMills.Construction.ReflectionPositivity.CovarianceAlgebraAndLocalisationOfTheRepresentatives
import YangMills.Construction.ReflectionPositivity.LatticeFormulaForTheScalarProduct
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
open scoped ComplexConjugate ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LatticeScalarProduct
open YangMills.Construction.ReflectionPositivity.AxisMirror (MirrorData)
open YangMills.Construction.ReflectionPositivity.RepresentativeCovariance (RepsLocalized
  RepsCompatible supportHalo)
open YangMills.Construction.ReflectionPositivity.TupleForm (PositiveSpan reflectionForm reflectConj)
open YangMills.Construction.InfiniteLattice (AmbientSpace refinedSpacing latticeSubgroup axisStep)
open YangMills.Construction.LimitConventions (ApproxTriple supDist)
open YangMills.Construction.LatticeConventions (Spacing conjFun supNorm timeAxis)
open YangMills.Construction.LatticeConventions.SiteFrame (upperSpace)
open YangMills.Construction.SeparatedTuples (FormalSpan TupleFunctional SepTuple push pushSpan
  pushList formalMul spanIn conjugation invMap basisVec supportedIn)
theorem mem_supportedIn_of_mem_support {O : Set AmbientSpace} {Z : FormalSpan}
    (hZ : Z ∈ spanIn O) : ∀ X ∈ Z.support, X ∈ supportedIn O := by
  induction hZ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Y, rfl⟩ := hx
    intro X hX
    have h := Finsupp.support_single_subset hX
    rw [Finset.mem_singleton] at h
    rw [h]
    exact Y.2
  | zero => simp
  | add x y _ _ hx hy =>
    classical
    intro X hX
    rcases Finset.mem_union.1 (Finsupp.support_add hX) with h | h
    exacts [hx X h, hy X h]
  | smul c x _ hx =>
    intro X hX
    exact hx X (Finsupp.support_smul hX)
theorem exists_pos_time_lowerBound {K : Set AmbientSpace} (hK : IsCompact K)
    (hpos : K ⊆ TimeAxis.upperHalfSpace) :
    ∃ δ : ℝ, 0 < δ ∧ K ⊆ {x | 2 * δ ≤ TimeAxis.timeComponent x} := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · have hc : Continuous TimeAxis.timeComponent :=
      show Continuous fun x : AmbientSpace => x TimeAxis.timeIdx from continuous_apply _
    obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hc.continuousOn
    refine ⟨TimeAxis.timeComponent x / 2, half_pos (hpos hx), fun y hy => ?_⟩
    have h : TimeAxis.timeComponent x ≤ TimeAxis.timeComponent y := hmin hy
    simp only [Set.mem_ofPred_eq]
    linarith
def unionSupports (Z : FormalSpan) : Set AmbientSpace := ⋃ X ∈ Z.support, ⋃ f ∈ X.1, tsupport f
theorem isCompact_unionSupports (Z : FormalSpan) : IsCompact (unionSupports Z) :=
  Z.support.isCompact_biUnion fun X _ =>
    (List.finite_toSet X.1).isCompact_biUnion fun f hf => (X.2.1 f hf).2
theorem unionSupports_subset_upperHalfSpace {Z : FormalSpan}
    (hZ : Z ∈ spanIn TimeAxis.upperHalfSpace) :
    unionSupports Z ⊆ TimeAxis.upperHalfSpace := by
  intro x hx
  simp only [unionSupports, Set.mem_iUnion] at hx
  obtain ⟨X, hX, f, hf, hx⟩ := hx
  exact mem_supportedIn_of_mem_support hZ X hX f hf hx
theorem supportedAbove_of_unionSupports_subset {δ : ℝ} {Z : FormalSpan}
    (h : unionSupports Z ⊆ {x | 2 * δ ≤ TimeAxis.timeComponent x}) : SupportedAbove δ Z := by
  intro X hX f hf x hx
  refine h ?_
  simp only [unionSupports, Set.mem_iUnion]
  exact ⟨X, hX, f, hf, hx⟩
theorem exists_common_margin (Z W : PositiveSpan) :
    ∃ δ : ℝ, 0 < δ ∧ SupportedAbove δ Z.1 ∧ SupportedAbove δ W.1 := by
  obtain ⟨δ, hδ, h⟩ := exists_pos_time_lowerBound
    ((isCompact_unionSupports Z.1).union (isCompact_unionSupports W.1))
    (Set.union_subset (unionSupports_subset_upperHalfSpace Z.2)
      (unionSupports_subset_upperHalfSpace W.2))
  exact ⟨δ, hδ, supportedAbove_of_unionSupports_subset (Set.subset_union_left.trans h),
    supportedAbove_of_unionSupports_subset (Set.subset_union_right.trans h)⟩
theorem supportHalo_subset_nonneg_time {a δ : ℝ} (ha : 0 < a) (hδ : a ≤ δ) {X : SepTuple}
    (hX : ∀ f ∈ X.1, tsupport f ⊆ {x | 2 * δ ≤ TimeAxis.timeComponent x}) :
    supportHalo a X ⊆ {x : LatticeConventions.Point | 0 ≤ x timeAxis} := by
  intro x hx
  by_contra hneg
  have hneg' : x 3 < 0 := not_le.1 hneg
  have hle : ENNReal.ofReal (2 * δ) ≤ supDist x (⋃ f ∈ X.1, tsupport f) := by
    refine le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal ?_
    simp only [Set.mem_iUnion] at hy
    obtain ⟨f, hf, hy⟩ := hy
    have h1 : 2 * δ ≤ y 3 := hX f hf hy
    have h2 : |(x - y) 3| ≤ supNorm (x - y) :=
      Finset.le_sup' (fun μ => |(x - y) μ|) (Finset.mem_univ 3)
    have h3 := neg_abs_le ((x - y) 3)
    simp only [Pi.sub_apply] at h2 h3
    linarith
  have h := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (hle.trans hx)
  linarith
section Representatives
variable {L : ℕ} (T : ApproxTriple L)
theorem spanRep_eq_sum (j : ℕ+) (Z : FormalSpan) :
    T.spanRep j Z =
      ∑ X ∈ Z.support, Z X • fun U => (T.tupleRep j X U : ℂ) := by
  simp [ApproxTriple.spanRep, SeparatedTuples.linearExtend,
    Finsupp.linearCombination_apply, Finsupp.sum]
theorem spanRep_basisVec (j : ℕ+) (X : SepTuple) :
    T.spanRep j (basisVec X) = fun U => (T.tupleRep j X U : ℂ) :=
  SeparatedTuples.linearExtend_basisVec _ X
theorem spanRep_formalMul (j : ℕ+)
    (hP : ∀ X Y : SepTuple, SepTuple.Composable X Y →
      T.tupleRep j (SepTuple.juxt X Y) =
        T.tupleRep j X * T.tupleRep j Y)
    {A B : FormalSpan} (h : ∀ X ∈ A.support, ∀ Y ∈ B.support, SepTuple.Composable X Y) :
    T.spanRep j (formalMul A B) =
      T.spanRep j A * T.spanRep j B := by
  have hsum : ∀ C : FormalSpan, ∑ X ∈ C.support, C X • basisVec X = C := fun C => by
    conv_rhs => rw [← Finsupp.sum_single C]
    simp [Finsupp.sum, basisVec]
  have hprod := SeparatedTuples.formalMul_sum A.support B.support (fun X => A X)
    (fun Y => B Y) (fun X => X) (fun Y => Y)
  rw [hsum A, hsum B] at hprod
  rw [hprod, spanRep_eq_sum T j A, spanRep_eq_sum T j B,
    Finset.sum_mul_sum]
  simp only [map_sum, map_smul, spanRep_basisVec]
  refine Finset.sum_congr rfl fun X hX => Finset.sum_congr rfl fun Y hY => ?_
  rw [hP X Y (h X hX Y hY)]
  funext U
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring
end Representatives
theorem pushSpan_basisVec (r : AmbientSpace → AmbientSpace) (X : SepTuple) :
    pushSpan r (basisVec X) = basisVec (push r X) :=
  SeparatedTuples.linearExtend_basisVec _ X
theorem conjugation_pushSpan (r : AmbientSpace → AmbientSpace) (Z : FormalSpan) :
    conjugation (pushSpan r Z) = pushSpan r (conjugation Z) := by
  induction Z using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single X c =>
    have h : Finsupp.single X c = c • basisVec X := by simp [basisVec]
    rw [h]
    simp [map_smulₛₗ, SeparatedTuples.conjugation_basisVec, pushSpan_basisVec]
theorem exists_of_mem_support_pushSpan {r : AmbientSpace → AmbientSpace} {Z : FormalSpan}
    {X' : SepTuple} (h : X' ∈ (pushSpan r Z).support) : ∃ X ∈ Z.support, X' = push r X := by
  classical
  have hZ : pushSpan r Z = ∑ X ∈ Z.support, Z X • basisVec (push r X) := by
    simp [pushSpan, SeparatedTuples.linearExtend, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [hZ] at h
  by_contra hno
  push Not at hno
  apply Finsupp.mem_support_iff.1 h
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun X hX => ?_
  simp [basisVec, (hno X hX).symm]
theorem mem_support_of_mem_support_conjugation {Z : FormalSpan} {X : SepTuple}
    (h : X ∈ (conjugation Z).support) : X ∈ Z.support := by
  rw [Finsupp.mem_support_iff] at h ⊢
  intro h0
  apply h
  change (Z.mapRange (starRingEnd ℂ) (map_zero _)) X = 0
  simp [h0]
theorem mem_pushList_of_mem_push {r : AmbientSpace → AmbientSpace} {X : SepTuple}
    {f : SeparatedTuples.RealValued} (hf : f ∈ (push r X).1) : f ∈ pushList r X.1 := by
  unfold push at hf
  split_ifs at hf with h
  · exact hf
  · simp [SepTuple.nil] at hf
theorem timeReflection_involutive_apply (x : AmbientSpace) :
    TimeAxis.timeReflection (TimeAxis.timeReflection x) = x := by
  funext μ
  fin_cases μ <;> simp [TimeAxis.timeReflection]
theorem invMap_timeReflection : invMap TimeAxis.timeReflection = TimeAxis.timeReflection := by
  have hinj : Function.Injective TimeAxis.timeReflection :=
    Function.LeftInverse.injective timeReflection_involutive_apply
  funext x
  calc invMap TimeAxis.timeReflection x
      = invMap TimeAxis.timeReflection
          (TimeAxis.timeReflection (TimeAxis.timeReflection x)) := by
        rw [timeReflection_involutive_apply]
    _ = TimeAxis.timeReflection x := Function.leftInverse_invFun hinj _
theorem continuous_timeReflection : Continuous TimeAxis.timeReflection := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [TimeAxis.timeReflection] <;> fun_prop
theorem reflMulShiftComposable_of_nonneg {δ : ℝ} (hδ : 0 < δ) {Z W : FormalSpan}
    (hZ : SupportedAbove δ Z) (hW : SupportedAbove δ W) {v : AmbientSpace}
    (hv : 0 ≤ TimeAxis.timeComponent v) : ReflMulShiftComposable Z W v := by
  intro X hX Y hY f hf h hh
  have hf' := mem_pushList_of_mem_push hf
  have hh' := mem_pushList_of_mem_push hh
  rw [SeparatedTuples.pushList_translate] at hh'
  simp only [pushList, List.mem_map, invMap_timeReflection] at hf'
  simp only [List.mem_map] at hh'
  obtain ⟨g, hg, rfl⟩ := hf'
  obtain ⟨k, hk, rfl⟩ := hh'
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  have h1 := hZ X hX g hg (tsupport_comp_subset_preimage g continuous_timeReflection hx)
  have hc : Continuous fun x : AmbientSpace => x - v := by fun_prop
  have h2 := hW Y hY k hk (tsupport_comp_subset_preimage k hc hx')
  simp only [Set.mem_ofPred_eq, TimeAxis.timeComponent, TimeAxis.timeReflection,
    TimeAxis.timeIdx, Pi.sub_apply] at h1 h2 hv
  simp at h1
  linarith
theorem siteTimeReflection_toFun_eq (a : Spacing) :
    (LatticeConventions.SiteFrame.timeReflection a).toFun = TimeAxis.timeReflection := by
  rw [LatticeConventions.SiteFrame.timeReflection_toFun]
  funext x μ
  fin_cases μ <;>
    simp [LatticeConventions.SiteFrame.siteReflectionMap, TimeAxis.timeReflection, timeAxis,
      LatticeConventions.basisVector]
  ring
section Approximation
variable (D : MirrorData) (T : ApproxTriple D.L)
theorem refinedSpacing_pos (K : ℕ+) : 0 < refinedSpacing D.L K := (meshOf D K).2
theorem spanRep_mem_upperSpace {j : ℕ+} (hC : RepsLocalized T j) {δ : ℝ}
    (ha : refinedSpacing D.L (T.cutoff j) ≤ δ) {Z : FormalSpan} (hZ : SupportedAbove δ Z) :
    T.spanRep j Z ∈ upperSpace (meshAt D T j) timeAxis := by
  rw [spanRep_eq_sum]
  refine Submodule.sum_mem _ fun X hX => Submodule.smul_mem _ _ ?_
  rw [← SetLike.mem_coe, LatticeConventions.SiteFrame.coe_upperSpace]
  obtain ⟨-, hobs, hb⟩ := hC X
  simp only [InfiniteLattice.localRegionObservables, Set.mem_iUnion]
  refine ⟨supportHalo (refinedSpacing D.L (T.cutoff j)) X, hb, ?_⟩
  rw [Set.inter_eq_right.2
    (supportHalo_subset_nonneg_time (refinedSpacing_pos D _) ha (hZ X hX))]
  exact hobs
theorem conjReflMulShift_eq_spanRep {j : ℕ+}
    (hB : RepsCompatible T j) {Z W : PositiveSpan}
    {v : AmbientSpace} (hv : v ∈ latticeSubgroup (refinedSpacing D.L (T.cutoff j)))
    (hdef : ReflMulShiftComposable Z.1 W.1 v) :
    conjReflMulShift (meshAt D T j) (T.spanRep j Z.1) (T.spanRep j W.1) v =
      T.spanRep j (reflMulShift Z W.1 v) := by
  obtain ⟨hact, hP, hconj⟩ := hB
  have h1 : conjFun ((LatticeConventions.SiteFrame.timeReflection (meshAt D T j)).actOn
      (T.spanRep j Z.1)) = T.spanRep j (reflectConj Z) := by
    have h := hact (LatticeConventions.SiteFrame.timeReflection (meshAt D T j)) Z.1
    rw [siteTimeReflection_toFun_eq] at h
    unfold reflectConj
    rw [← conjugation_pushSpan, ← hconj, ← h]
    rfl
  have h2 : (InfiniteLattice.shift (⟨v, hv⟩ : InfiniteLattice.LatticePoint _)).actOn
      (T.spanRep j W.1) = T.spanRep j
        (pushSpan (SeparatedTuples.translate v) W.1) :=
    hact (InfiniteLattice.shift ⟨v, hv⟩) W.1
  have hsupp : ∀ X ∈ (reflectConj Z).support,
      ∀ Y ∈ (pushSpan (SeparatedTuples.translate v) W.1).support,
        SepTuple.Composable X Y := by
    intro X hX Y hY
    obtain ⟨X', hX', rfl⟩ := exists_of_mem_support_pushSpan hX
    obtain ⟨Y', hY', rfl⟩ := exists_of_mem_support_pushSpan hY
    exact hdef X' (mem_support_of_mem_support_conjugation hX') Y' hY'
  unfold reflMulShift
  rw [spanRep_formalMul T j hP hsupp, ← h1, ← h2]
  unfold conjReflMulShift
  rw [dif_pos hv]
  rfl
theorem tendsto_integral_spanRep (hC : ∀ j, RepsLocalized T j)
    {σ : TupleFunctional} (hσ : T.ConvergesTo σ) (C : FormalSpan) :
    Tendsto (fun j => ∫ U, T.spanRep j C U ∂T.state j) atTop
      (𝓝 (σ.spanExtension C)) := by
  have hint : ∀ (j : ℕ+) (X : SepTuple),
      Integrable (fun U => (T.tupleRep j X U : ℂ)) (T.state j) := by
    intro j X
    obtain ⟨hm, c, hc⟩ := ((hC j X).2.1).1
    exact Integrable.of_bound hm.aestronglyMeasurable c (ae_of_all _ hc)
  have heq : ∀ j : ℕ+, ∫ U, T.spanRep j C U ∂T.state j =
      ∑ X ∈ C.support, C X * ((∫ U, T.tupleRep j X U ∂T.state j : ℝ) : ℂ) := by
    intro j
    rw [spanRep_eq_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finsetSum _ fun X _ => (hint j X).const_mul _]
    refine Finset.sum_congr rfl fun X _ => ?_
    rw [integral_const_mul, integral_complex_ofReal]
  have hs : σ.spanExtension C = ∑ X ∈ C.support, C X * (σ X : ℂ) := by
    simp [TupleFunctional.spanExtension, SeparatedTuples.linearExtend,
      Finsupp.linearCombination_apply, Finsupp.sum]
  simp_rw [heq]
  rw [hs]
  exact tendsto_finsetSum _ fun X _ =>
    ((Complex.continuous_ofReal.tendsto _).comp (hσ X)).const_mul _
end Approximation
theorem refinedSpacing_eq_inv_pow (L K : ℕ) : refinedSpacing L K = ((L : ℝ)⁻¹) ^ K := by
  simp [refinedSpacing, PeriodicLattice.meshSize, zpow_neg]
theorem eventually_refinedSpacing_le {L : ℕ} (hL : 2 ≤ L) (T : ApproxTriple L) {δ : ℝ}
    (hδ : 0 < δ) : ∀ᶠ j in atTop, refinedSpacing L (T.cutoff j) ≤ δ := by
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have h0 : Tendsto (fun K : ℕ => ((L : ℝ)⁻¹) ^ K) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h0.eventually (gt_mem_nhds hδ))
  filter_upwards [T.tendsto_cutoff.eventually (eventually_ge_atTop (⟨N + 1, N.succ_pos⟩ : ℕ+))]
    with j hj
  have hj' : N ≤ (T.cutoff j : ℕ) := by
    have h : N + 1 ≤ (T.cutoff j : ℕ) := hj
    omega
  rw [refinedSpacing_eq_inv_pow]
  exact (hN _ hj').le
theorem eventually_int_mul_refinedSpacing {L : ℕ} (hL : 2 ≤ L) (T : ApproxTriple L) {x : ℝ}
    (hx : x ∈ PeriodicLattice.adicGridPoints L) :
    ∀ᶠ j in atTop, ∃ n : ℤ, x = (n : ℝ) * refinedSpacing L (T.cutoff j) := by
  have hL0 : (L : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  obtain ⟨k, n, rfl⟩ := (PeriodicLattice.mem_adicGridPoints_iff L x).1 hx
  filter_upwards [T.tendsto_cutoff.eventually (eventually_ge_atTop (⟨k + 1, k.succ_pos⟩ : ℕ+))]
    with j hj
  have hk : k ≤ (T.cutoff j : ℕ) := by
    have h : k + 1 ≤ (T.cutoff j : ℕ) := hj
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨n * (L : ℤ) ^ d, ?_⟩
  have h1 : PeriodicLattice.meshSize L (k : ℤ) = ((L : ℝ)⁻¹) ^ k := refinedSpacing_eq_inv_pow L k
  rw [h1, refinedSpacing_eq_inv_pow, hd, pow_add]
  push_cast
  rw [mul_assoc, ← mul_assoc ((L : ℝ) ^ d), mul_comm ((L : ℝ) ^ d), mul_assoc, ← mul_pow,
    mul_inv_cancel₀ hL0]
  simp
theorem sum_axisSteps_eq (a : ℝ) {v : AmbientSpace} (hv : v ∈ latticeSubgroup a) (m : Fin 4 → ℤ)
    (hm : ∀ μ, v μ = (m μ : ℝ) * a) (h3 : 0 ≤ m 3) :
    (m 3).toNat • axisStep a timeAxis +
        ∑ j : LatticeConventions.SpatialDirection, m j.castSucc • axisStep a j.toDirection =
      (⟨v, hv⟩ : InfiniteLattice.LatticePoint a) := by
  apply Subtype.ext
  have hs : ∀ μ : Fin 4, ((axisStep a μ : InfiniteLattice.LatticePoint a) : AmbientSpace) =
      Pi.single μ a := fun _ => rfl
  have h3' : (((m 3).toNat : ℤ) : ℝ) = (m 3 : ℝ) := by rw [Int.toNat_of_nonneg h3]
  funext μ
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_nsmul, Fin.sum_univ_three,
    AddSubgroup.coe_zsmul, hs]
  fin_cases μ <;>
    simp [timeAxis, LatticeConventions.SpatialDirection.toDirection, hm]
  exact Or.inl (by exact_mod_cast h3')
section Matrix
variable (D : MirrorData) (T : ApproxTriple D.L)
theorem transferMatrixElement_eq_latticeExpectation {j : ℕ+} {Z W : FormalSpan}
    (hS : LatticeConventions.ReflectionPositiveStates.SiteFrameMatrixElements
      (meshAt D T j) (T.state j))
    (hZ : T.spanRep j Z ∈ upperSpace (meshAt D T j) timeAxis)
    (hW : T.spanRep j W ∈ upperSpace (meshAt D T j) timeAxis)
    {v : AmbientSpace} (hv : v ∈ latticeSubgroup (refinedSpacing D.L (T.cutoff j)))
    (h0 : 0 ≤ TimeAxis.timeComponent v) :
    transferMatrixElement D T Z W v j = latticeExpectation D T Z W v j := by
  obtain ⟨m, hm⟩ := id hv
  have hapos := refinedSpacing_pos D (T.cutoff j)
  have hq : ∀ μ, intDiv (v μ) (refinedSpacing D.L (T.cutoff j)) = m μ := by
    intro μ
    unfold intDiv
    rw [hm μ, mul_div_cancel_right₀ _ hapos.ne', Int.floor_intCast]
  have h3 : 0 ≤ m 3 := by
    have h : 0 ≤ (m 3 : ℝ) * refinedSpacing D.L (T.cutoff j) := by
      rw [← hm 3]
      exact h0
    exact_mod_cast nonneg_of_mul_nonneg_left h hapos
  have hmat := hS.2.2.2.2.2.2.2 ⟨_, hZ⟩ ⟨_, hW⟩ (m 3).toNat (fun i => m i.castSucc)
  rw [sum_axisSteps_eq _ hv m hm h3] at hmat
  have e1 : siteClassOf (meshAt D T j) (T.state j) (T.spanRep j Z) =
      LatticeConventions.SiteFrame.timeClass (meshAt D T j) (T.state j) ⟨_, hZ⟩ :=
    dif_pos hZ
  have e2 : siteClassOf (meshAt D T j) (T.state j) (T.spanRep j W) =
      LatticeConventions.SiteFrame.timeClass (meshAt D T j) (T.state j) ⟨_, hW⟩ :=
    dif_pos hW
  have e3 : intDiv (TimeAxis.timeComponent v) (refinedSpacing D.L (T.cutoff j)) = m 3 := hq 3
  have e4 : (fun i : LatticeConventions.SpatialDirection =>
      intDiv (v i.castSucc) (refinedSpacing D.L (T.cutoff j))) =
        fun i => m i.castSucc := funext fun i => hq _
  have e5 : conjReflMulShift (meshAt D T j) (T.spanRep j Z) (T.spanRep j W) v = fun U =>
        conjFun ((LatticeConventions.SiteFrame.timeReflection (meshAt D T j)).actOn
          (T.spanRep j Z)) U *
        (InfiniteLattice.shift (⟨v, hv⟩ : InfiniteLattice.LatticePoint _)).actOn
          (T.spanRep j W) U := dif_pos hv
  change ⟪siteClassOf (meshAt D T j) (T.state j) (T.spanRep j Z),
      transferShiftOp (meshAt D T j) (T.state j)
        (intDiv (TimeAxis.timeComponent v) (refinedSpacing D.L (T.cutoff j))).toNat
        (fun i => intDiv (v i.castSucc) (refinedSpacing D.L (T.cutoff j)))
        (siteClassOf (meshAt D T j) (T.state j) (T.spanRep j W))⟫_ℂ =
    ∫ U, conjReflMulShift (meshAt D T j) (T.spanRep j Z) (T.spanRep j W) v U ∂T.state j
  rw [e1, e2, e3, e4, e5]
  simp only [transferShiftOp, ← mul_assoc]
  exact hmat
theorem latticeRepresentatives_and_adicLimitFormula
    (hCov : RepresentativeCovariance.RepresentativesCovariantAndLocal)
    (hOne : LatticeConventions.ReflectionPositiveStates.Statement)
    (hRP : T.IsReflPos) {σ : TupleFunctional} (hlim : T.ConvergesTo σ)
    (Z W : PositiveSpan) {δ : ℝ} (hδ : 0 < δ) (hZ : SupportedAbove δ Z.1)
    (hW : SupportedAbove δ W.1) :
    LatticeRepresentatives D T Z W δ ∧ AdicLimitFormula D T σ Z W := by
  have hL := D.isAdmissible
  have hL2 : 2 ≤ D.L := by
    have h := hL.2
    omega
  have hall := fun j => hCov D.L hL T j
  have hA : LatticeRepresentatives D T Z W δ := fun j ha =>
    ⟨spanRep_mem_upperSpace D T (hall j).2.2.1 ha hZ,
      spanRep_mem_upperSpace D T (hall j).2.2.1 ha hW, fun v hv h0 =>
      ⟨reflMulShiftComposable_of_nonneg hδ hZ hW h0,
        conjReflMulShift_eq_spanRep D T (hall j).2.1 hv
          (reflMulShiftComposable_of_nonneg hδ hZ hW h0)⟩⟩
  refine ⟨hA, fun v hv h0 => ?_⟩
  have hmul : ∀ᶠ j in atTop, ∀ μ, ∃ n : ℤ, v μ = (n : ℝ) * refinedSpacing D.L (T.cutoff j) :=
    eventually_all.2 fun μ => eventually_int_mul_refinedSpacing hL2 T (hv μ)
  have hsite : ∀ᶠ j in atTop, v ∈ latticeSubgroup (refinedSpacing D.L (T.cutoff j)) := by
    filter_upwards [hmul] with j hj
    exact ⟨fun μ => (hj μ).choose, fun μ => (hj μ).choose_spec⟩
  have hlat : Tendsto (latticeExpectation D T Z.1 W.1 v) atTop
      (𝓝 (σ.spanExtension (reflMulShift Z W.1 v))) := by
    refine (tendsto_integral_spanRep D T (fun j => (hall j).2.2.1) hlim _).congr' ?_
    filter_upwards [hsite, eventually_refinedSpacing_le hL2 T hδ] with j hj ha
    unfold latticeExpectation
    rw [((hA j ha).2.2 v hj h0).2]
  refine ⟨?_, hlat, hlat.congr' ?_⟩
  · filter_upwards [hmul] with j hj μ
    obtain ⟨n, hn⟩ := hj μ
    refine ⟨n, ?_⟩
    rw [hn, mul_div_cancel_right₀ _ (refinedSpacing_pos D (T.cutoff j)).ne']
  · filter_upwards [hsite, eventually_refinedSpacing_le hL2 T hδ] with j hj ha
    exact (transferMatrixElement_eq_latticeExpectation D T
      (hOne (meshAt D T j) (T.state j) (hRP j).1 (hRP j).2).2.1
      (hA j ha).1 (hA j ha).2.1 hj h0).symm
theorem classInner_eq_transferMatrixElement_zero (Z W : FormalSpan) (j : ℕ+) :
    classInner D T Z W j = transferMatrixElement D T Z W 0 j := by
  have e1 : intDiv (TimeAxis.timeComponent (0 : AmbientSpace))
      (refinedSpacing D.L (T.cutoff j)) = 0 := by
    simp [intDiv, TimeAxis.timeComponent]
  have e2 : (fun i : LatticeConventions.SpatialDirection =>
      intDiv ((0 : AmbientSpace) i.castSucc) (refinedSpacing D.L (T.cutoff j))) =
        fun _ => 0 := by
    funext i
    simp [intDiv]
  unfold classInner transferMatrixElement
  rw [e1, e2]
  simp [transferShiftOp, ContractionUnitary.zpowOp_zero]
end Matrix
theorem push_translate_zero (X : SepTuple) : push (SeparatedTuples.translate 0) X = X := by
  have h : pushList (SeparatedTuples.translate 0) X.1 = X.1 := by
    rw [SeparatedTuples.pushList_translate]
    simp
  have hs : SeparatedTuples.IsDisjointlySupported
      (pushList (SeparatedTuples.translate 0) X.1) := by
    rw [h]
    exact X.2
  unfold push
  rw [dif_pos hs]
  exact Subtype.ext h
theorem pushSpan_translate_zero (W : FormalSpan) :
    pushSpan (SeparatedTuples.translate 0) W = W := by
  induction W using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single X c =>
    have h : Finsupp.single X c = c • basisVec X := by simp [basisVec]
    rw [h, map_smul, pushSpan_basisVec, push_translate_zero]
theorem zero_mem_adicGridPoints (L : ℕ) : (0 : ℝ) ∈ PeriodicLattice.adicGridPoints L :=
  (PeriodicLattice.mem_adicGridPoints_iff L 0).2 ⟨0, 0, by simp⟩
theorem inner_self_nonneg_complex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x : E) : (0 : ℂ) ≤ ⟪x, x⟫_ℂ := by
  have h : ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [h]
  exact Complex.zero_le_real.2 (sq_nonneg _)
theorem latticeFormula_holds (hCov : RepresentativeCovariance.RepresentativesCovariantAndLocal)
    (hOne : LatticeConventions.ReflectionPositiveStates.Statement) :
    LatticeFormula := by
  intro D T σ hRP _ hlim Z W
  refine ⟨exists_common_margin Z W, fun δ hδ hZ hW => ?_⟩
  obtain ⟨hA, hB⟩ :=
    latticeRepresentatives_and_adicLimitFormula D T hCov hOne hRP hlim Z W hδ hZ hW
  have hzero : ∀ Z' W' : PositiveSpan, SupportedAbove δ Z'.1 → SupportedAbove δ W'.1 →
      Tendsto (classInner D T Z'.1 W'.1) atTop
        (𝓝 (σ.spanExtension (formalMul (reflectConj Z') W'.1))) := by
    intro Z' W' hZ' hW'
    have h := ((latticeRepresentatives_and_adicLimitFormula D T hCov hOne hRP hlim Z' W' hδ hZ'
      hW').2 0 (fun _ => zero_mem_adicGridPoints D.L) le_rfl).2.2
    have e : reflMulShift Z' W'.1 0 = formalMul (reflectConj Z') W'.1 := by
      unfold reflMulShift
      rw [pushSpan_translate_zero]
    rw [e] at h
    exact h.congr fun j => (classInner_eq_transferMatrixElement_zero D T Z'.1 W'.1 j).symm
  refine ⟨hA, hB, rfl, hzero Z W hZ hW, ?_⟩
  exact ge_of_tendsto' (hzero Z Z hZ hZ) fun j => inner_self_nonneg_complex _
end YangMills.Construction.ReflectionPositivity.LatticeScalarProduct
end
