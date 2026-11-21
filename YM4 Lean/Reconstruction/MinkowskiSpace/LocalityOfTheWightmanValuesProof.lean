import YangMills.Construction.MinkowskiSpace.MeasureOfTheTimeTranslationsAndTheVectorsTheyFixProof
import YangMills.Construction.Continuum.RulesOfThePartialDerivatives
import YangMills.Construction.Continuum.TruncationOfSchwartzFunctionsAtInfinity
import Reconstruction.MinkowskiSpace.AcrossTheSpacelikePointsProof
import Reconstruction.MinkowskiSpace.FieldOnTheTensorVectorsProof
import Reconstruction.MinkowskiSpace.LocalityOfTheWightmanValues
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.WightmanLocality
open MinkowskiSpace FieldForms RealPointVectors WightmanTheory ProjectionMeasures OneLoopNotation
theorem exists_hasCompactSupport_schwartzNorm_sub_le (hF : TestSpaces.Elementary.BasicProperties)
    (hR : TestSpaces.DerivRules.Combined)
    (htr : TestSpaces.SchwartzTruncationApprox)
    (f : TestFn) {k : ℕ} (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : TestFn, HasCompactSupport g.1 ∧ tsupport g.1 ⊆ tsupport f.1 ∧
      schwartzNorm k (f.1 - g.1) ≤ ENNReal.ofReal ε := by
  have hfs : asOnePointFn f.1 ∈ TestSpaces.schwartzSet 1 := f.2
  let S : Set (TestSpaces.PointTuple 1) := {p | p 0 ∈ tsupport f.1}
  have hSc : IsClosed S := (isClosed_tsupport f.1).preimage (continuous_apply 0)
  have hzero : ∀ y ∈ Sᶜ, asOnePointFn f.1 y = 0 := fun y hy => by
    change f.1 (y 0) = 0
    exact image_eq_zero_of_notMem_tsupport hy
  have hflat : TestSpaces.VanishesToInfiniteOrderOff (asOnePointFn f.1) (interior S) := by
    obtain ⟨-, hRc, -, -⟩ := hR
    have hrules := hRc 1 (asOnePointFn f.1) hfs.1
    refine ⟨hfs.1, isOpen_interior, fun x hx => ?_⟩
    have hxcl : x ∈ closure Sᶜ := by
      rw [closure_compl]
      exact hx
    refine ⟨hfs.1, ?_, fun α => ?_⟩
    · exact closure_minimal (t := {y | asOnePointFn f.1 y = 0}) hzero
        (isClosed_eq hfs.1.continuous continuous_const) hxcl
    · have hz := hrules.2.2.2.2.2.2.2 _ hSc.isOpen_compl hzero α
      exact closure_minimal (t := {y | TestSpaces.multiDeriv α (asOnePointFn f.1) y = 0}) hz
        (isClosed_eq (hrules.2.2.1 α).continuous continuous_const) hxcl
  obtain ⟨φ₁, hs₁, hc₁, hf₁, hn₁, -⟩ := htr 1 k one_pos hk _ _ hfs hflat ε hε
  let c : (Fin 4 → ℝ) → TestSpaces.PointTuple 1 := fun x _ => x
  have hφ₁ : asOnePointFn (φ₁ ∘ c) = φ₁ := by
    funext p
    have hp : c (p 0) = p := by
      funext i
      rw [Subsingleton.elim i 0]
    simp only [asOnePointFn, Function.comp_apply, hp]
  have hmem : φ₁ ∘ c ∈ WightmanTheory.schwartzR4 := by
    change asOnePointFn (φ₁ ∘ c) ∈ TestSpaces.schwartzSet 1
    rw [hφ₁]
    exact ((hF 1 one_pos).2.2.1 Set.univ isOpen_univ φ₁ ⟨hs₁, hc₁, Set.subset_univ _⟩).1
  have hcemb : Topology.IsClosedEmbedding c :=
    (Homeomorph.funUnique (Fin 1) (Fin 4 → ℝ)).symm.isClosedEmbedding
  refine ⟨⟨φ₁ ∘ c, hmem⟩, hc₁.comp_isClosedEmbedding hcemb, ?_, ?_⟩
  · refine closure_minimal (fun x hx => ?_) (isClosed_tsupport _)
    by_contra hxs
    have hnot : c x ∉ interior S := fun h => hxs (show c x ∈ S from interior_subset h)
    exact hx (hf₁.2.2 _ hnot).2.1
  · have heq : asOnePointFn (f.1 - φ₁ ∘ c) = asOnePointFn f.1 - φ₁ := by
      rw [← hφ₁]
      rfl
    change TestSpaces.weightedSeminorm k (asOnePointFn (f.1 - φ₁ ∘ c)) ≤ _
    rw [heq]
    exact hn₁
theorem sub_mem_schwartzR4 (hF : TestSpaces.Elementary.BasicProperties)
    {f g : (Fin 4 → ℝ) → ℂ} (hf : f ∈ WightmanTheory.schwartzR4)
    (hg : g ∈ WightmanTheory.schwartzR4) :
    f - g ∈ WightmanTheory.schwartzR4 := by
  have h := ((hF 1 one_pos).1.1 _ hf _ hg 1 (-1)).1.1
  have e : TestSpaces.Elementary.linComb 1 (asOnePointFn f) (-1) (asOnePointFn g) =
      asOnePointFn (f - g) := by
    funext x
    simp [TestSpaces.Elementary.linComb, asOnePointFn, sub_eq_add_neg]
  change asOnePointFn (f - g) ∈ TestSpaces.schwartzSet 1
  rwa [← e]
theorem prod_update_eq_mul_prod_erase {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (F : ι → M) (a : ι) (c : M) :
    ∏ i, Function.update F a c i = c * ∏ i ∈ Finset.univ.erase a, F i := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
def testTensor {b : ℕ} (u : Fin (b + 1) → TestFn) : TestSpaces.PointTuple (b + 1) → ℂ :=
  tensorVal fun i => (u i).1
theorem testTensor_apply {b : ℕ} (u : Fin (b + 1) → TestFn)
    (x : TestSpaces.PointTuple (b + 1)) : testTensor u x = ∏ i, (u i).1 (x i) := rfl
theorem testTensor_mem {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {E : FourBorelSet → BddOp K} {Ω : K} {A : ℝ → BddOp K}
    {℘ C : ℝ} (hV : BoundaryVectorFacts E Ω A ℘ C) {b : ℕ} (u : Fin (b + 1) → TestFn) :
    testTensor u ∈ TestSpaces.schwartzSet (b + 1) :=
  hV.tensorVal_mem (b + 1) (fun i => (u i).1) fun i => (u i).2
theorem maxPartialL1_nonneg (k : ℕ) (h : (Fin 4 → ℝ) → ℂ) : 0 ≤ maxPartialL1 k h := by apply _root_.YangMills.Construction.FieldOnTensorVecs.maxPartialL1_nonneg <;> assumption
section OneFactor
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : FourBorelSet → BddOp K} {Ω : K} {A : ℝ → BddOp K} {℘ C : ℝ}
def oneSlotConst (℘ C : ℝ) {b : ℕ} (u : Fin (b + 1) → TestFn) (a : Fin (b + 1)) : ℝ :=
  4 * ((2 : ℝ) ^ ℘ * C) ^ (b + 1) *
    (((b + 1 : ℕ) : ℝ) ^ (2 * (boundOrder ℘ (b + 1)).toNat) *
      ∏ i ∈ Finset.univ.erase a, maxPartialL1 (boundOrder ℘ (b + 1)).toNat (u i).1)
theorem norm_wightmanFunctional_sub_update_le (hform : IsBoundedFieldForm E Ω A ℘ C)
    (hV : BoundaryVectorFacts E Ω A ℘ C) (hF : TestSpaces.Elementary.BasicProperties)
    {b : ℕ} (u : Fin (b + 1) → TestFn) (a : Fin (b + 1)) (g : TestFn) {δ : ℝ}
    (hδ : maxPartialL1 (boundOrder ℘ (b + 1)).toNat ((u a).1 - g.1) ≤ δ) :
    ‖wightmanFunctional E Ω A (b + 1) (testTensor u) -
        wightmanFunctional E Ω A (b + 1) (testTensor (Function.update u a g))‖ ≤
      oneSlotConst ℘ C u a * δ := by
  classical
  have hd : (u a).1 - g.1 ∈ WightmanTheory.schwartzR4 :=
    sub_mem_schwartzR4 hF (u a).2 g.2
  let d : TestFn := ⟨_, hd⟩
  set v := Function.update u a g with hv
  set w := Function.update u a d with hw
  have hsplit : testTensor u = (1 : ℂ) • testTensor v + (1 : ℂ) • testTensor w := by
    funext x
    have h1 : ∏ i, (v i).1 (x i) = g.1 (x a) * ∏ i ∈ Finset.univ.erase a, (u i).1 (x i) := by
      have := prod_update_eq_mul_prod_erase (fun i => (u i).1 (x i)) a (g.1 (x a))
      rw [← this]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i = a
      · subst hi
        simp [hv]
      · simp [hv, Function.update_of_ne hi]
    have h2 : ∏ i, (w i).1 (x i) =
        ((u a).1 (x a) - g.1 (x a)) * ∏ i ∈ Finset.univ.erase a, (u i).1 (x i) := by
      have := prod_update_eq_mul_prod_erase (fun i => (u i).1 (x i)) a ((u a).1 (x a) - g.1 (x a))
      rw [← this]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i = a
      · subst hi
        simp [hw, d]
      · simp [hw, Function.update_of_ne hi]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, testTensor_apply, h1, h2]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
    ring
  have hvs := testTensor_mem hV v
  have hws := testTensor_mem hV w
  have hlin := hV.testState_linear b _ _ hvs hws 1 1
  have hW : wightmanFunctional E Ω A (b + 1) (testTensor u) -
      wightmanFunctional E Ω A (b + 1) (testTensor v) =
      wightmanFunctional E Ω A (b + 1) (testTensor w) := by
    have : wightmanFunctional E Ω A (b + 1) (testTensor u) =
        wightmanFunctional E Ω A (b + 1) (testTensor v) +
          wightmanFunctional E Ω A (b + 1) (testTensor w) := by
      unfold wightmanFunctional
      rw [hsplit, hlin]
      simp
    rw [this]
    ring
  rw [hW]
  have hC : 0 ≤ 4 * ((2 : ℝ) ^ ℘ * C) ^ (b + 1) := by
    have : 0 ≤ (2 : ℝ) ^ ℘ * C :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (le_trans zero_le_one hform.one_le_const)
    positivity
  have hprod : 0 ≤ ∏ i ∈ Finset.univ.erase a,
      maxPartialL1 (boundOrder ℘ (b + 1)).toNat (u i).1 :=
    Finset.prod_nonneg fun _ _ => maxPartialL1_nonneg _ _
  have hbn := hV.fieldFormNorm_tensorProd_le b (fun i => (w i).1) fun i => (w i).2
  have hprodw : ∏ i, maxPartialL1 (boundOrder ℘ (b + 1)).toNat (w i).1 =
      maxPartialL1 (boundOrder ℘ (b + 1)).toNat ((u a).1 - g.1) *
        ∏ i ∈ Finset.univ.erase a,
          maxPartialL1 (boundOrder ℘ (b + 1)).toNat (u i).1 := by
    rw [← prod_update_eq_mul_prod_erase (fun i => maxPartialL1 (boundOrder ℘ (b + 1)).toNat (u i).1)]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i = a
    · subst hi
      simp [hw, d]
    · simp [hw, Function.update_of_ne hi]
  rw [hprodw] at hbn
  calc ‖wightmanFunctional E Ω A (b + 1) (testTensor w)‖
      ≤ 4 * ((2 : ℝ) ^ ℘ * C) ^ (b + 1) * fieldFormNorm ℘ (testTensor w) :=
        hV.norm_wightmanFunctional_le b _ hws
    _ ≤ 4 * ((2 : ℝ) ^ ℘ * C) ^ (b + 1) *
        (((b + 1 : ℕ) : ℝ) ^ (2 * (boundOrder ℘ (b + 1)).toNat) *
          (δ * ∏ i ∈ Finset.univ.erase a,
            maxPartialL1 (boundOrder ℘ (b + 1)).toNat (u i).1)) := by
        refine mul_le_mul_of_nonneg_left (hbn.trans ?_) hC
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδ hprod) (by positivity)
    _ = oneSlotConst ℘ C u a * δ := by
        unfold oneSlotConst
        ring
end OneFactor
section Edge
variable {b : ℕ}
def edgePoint (x : TestSpaces.PointTuple (b + 1)) (Y : TestSpaces.PointTuple b) :
    Fin b → ComplexVec4 :=
  successiveDiffs (tupleToComplex x) + Complex.I • tupleToComplex Y
theorem imPart_edgePoint (x : TestSpaces.PointTuple (b + 1)) (Y : TestSpaces.PointTuple b)
    (k : Fin b) : MinkowskiSpace.imPart (edgePoint x Y k) = Y k := by
  funext μ
  simp [MinkowskiSpace.imPart, edgePoint, successiveDiffs, tupleToComplex, toComplex]
theorem edgePoint_self {x : TestSpaces.PointTuple (b + 1)} {Y : TestSpaces.PointTuple b}
    {j : Fin b} (hY : Y j = 0) : edgePoint x Y j = toComplex (x j.succ - x j.castSucc) := by
  funext μ
  simp [edgePoint, successiveDiffs, tupleToComplex, toComplex, hY]
theorem edgePoint_mem_spacelikeSlab {x : TestSpaces.PointTuple (b + 1)}
    {Y : TestSpaces.PointTuple b} {j : Fin b}
    (hY : Y j = 0) (hYk : ∀ k, k ≠ j → Y k ∈ futureCone)
    (hx : x j.succ - x j.castSucc ∈ spacelikeSet) :
    edgePoint x Y ∈ spacelikeSlab j := by
  refine ⟨⟨_, hx, (edgePoint_self hY).symm⟩, fun k hk => ?_⟩
  change MinkowskiSpace.imPart _ ∈ futureCone
  rw [imPart_edgePoint]
  exact hYk k hk
theorem timeLiftedTuple_edgePoint {x : TestSpaces.PointTuple (b + 1)} {Y : TestSpaces.PointTuple b}
    {j : Fin b} (hY : Y j = 0) (ε : ℝ) :
    timeLiftedTuple j ε (edgePoint x Y) = edgePoint x (Function.update Y j (ε • timeUnit)) := by
  funext k
  by_cases hk : k = j
  · subst hk
    simp only [timeLiftedTuple, Function.update_self, imagTimeShift]
    simp [edgePoint, tupleToComplex, hY]
    rfl
  · simp [timeLiftedTuple, Function.update_of_ne hk, edgePoint, tupleToComplex]
theorem smul_timeUnit_mem_futureCone {ε : ℝ} (hε : 0 < ε) : ε • timeUnit ∈ futureCone := by
  have h : spacePart (ε • timeUnit) = 0 := by
    funext i
    simp [spacePart, timeUnit, mkTimeSpace]
  have h0 : (ε • timeUnit) 0 = ε := by
    simp [timeUnit, mkTimeSpace]
  change (ε • timeUnit) 0 - spaceNorm (spacePart (ε • timeUnit)) > 0
  rw [h, h0]
  simpa [spaceNorm] using hε
theorem origin_mem_closedFutureCone : (0 : RealVec4) ∈ closedFutureCone := by apply _root_.YangMills.Construction.TimeTranslations.zero_mem_futureCone <;> assumption
theorem closedFutureCone_of_futureCone {y : RealVec4} (hy : y ∈ futureCone) :
    y ∈ closedFutureCone := by
  have h : coneGap y > 0 := hy
  exact (show coneGap y ≥ 0 from h.le)
theorem continuous_spaceNorm : Continuous spaceNorm := by apply _root_.YangMills.Construction.MinkowskiSpace.ConeTubeLorentz.continuous_spaceNorm <;> assumption
theorem continuous_rePart : Continuous MinkowskiSpace.rePart :=
  continuous_pi fun μ => Complex.continuous_re.comp (continuous_apply μ)
theorem continuous_spacePart : Continuous (spacePart : RealVec4 → Fin 3 → ℝ) :=
  continuous_pi fun _ => continuous_apply _
theorem continuous_l1Norm : Continuous MinkowskiSpace.l1Norm := by apply _root_.YangMills.Construction.FieldForms.SpacelikeExtension.continuous_l1Norm <;> assumption
theorem continuous_tubeGap : Continuous tubeGap := by apply _root_.YangMills.Construction.FieldForms.SpacelikeExtension.continuous_tubeGap <;> assumption
theorem continuous_edgePoint (Y : TestSpaces.PointTuple b) (k : Fin b) :
    Continuous fun x : TestSpaces.PointTuple (b + 1) => edgePoint x Y k := by
  refine continuous_pi fun μ => ?_
  simp only [edgePoint, successiveDiffs, tupleToComplex, toComplex, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  fun_prop
theorem l1Norm_pos_of_tubeGap_pos {ζ : ComplexVec4} (h : 0 < tubeGap ζ) :
    0 < MinkowskiSpace.l1Norm ζ := by
  have hs : 0 ≤ spaceNorm (spacePart (MinkowskiSpace.imPart ζ)) := Real.sqrt_nonneg _
  have hs' : 0 ≤ spaceNorm (spacePart (MinkowskiSpace.rePart ζ)) := Real.sqrt_nonneg _
  have h0 : 0 < MinkowskiSpace.imPart ζ 0 := by
    have : 0 < MinkowskiSpace.imPart ζ 0 -
      spaceNorm (spacePart (MinkowskiSpace.imPart ζ)) := h
    linarith
  have h1 := abs_nonneg (MinkowskiSpace.rePart ζ 0)
  have h2 := abs_pos.2 h0.ne'
  unfold MinkowskiSpace.l1Norm
  linarith
theorem tubeGap_edgePoint_pos {x : TestSpaces.PointTuple (b + 1)} {Y : TestSpaces.PointTuple b}
    {k : Fin b} (hk : Y k ∈ futureCone) : 0 < tubeGap (edgePoint x Y k) := by
  unfold tubeGap
  rw [imPart_edgePoint]
  exact hk
theorem continuous_maxBoostAngle_edgePoint {Y : TestSpaces.PointTuple b} {j : Fin b}
    (hYk : ∀ k, k ≠ j → Y k ∈ futureCone) :
    Continuous fun x : TestSpaces.PointTuple (b + 1) => maxBoostAngle j (edgePoint x Y) := by
  unfold maxBoostAngle
  by_cases h : (Finset.univ.erase j).Nonempty
  · simp only [dif_pos h]
    refine continuous_const.min (Continuous.finset_inf'_apply h fun k hk => ?_)
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    refine ((continuous_tubeGap.comp (continuous_edgePoint Y k))).div
      (continuous_const.mul (continuous_l1Norm.comp (continuous_edgePoint Y k)))
      fun x => ?_
    have := l1Norm_pos_of_tubeGap_pos (tubeGap_edgePoint_pos (x := x) (hYk k hkj))
    positivity
  · simp only [dif_neg h]
    exact continuous_const
theorem maxBoostAngle_edgePoint_pos {x : TestSpaces.PointTuple (b + 1)}
    {Y : TestSpaces.PointTuple b} {j : Fin b}
    (hYk : ∀ k, k ≠ j → Y k ∈ futureCone) : 0 < maxBoostAngle j (edgePoint x Y) := by
  unfold maxBoostAngle
  split_ifs with h
  · refine lt_min one_pos ((Finset.lt_inf'_iff h).2 fun k hk => ?_)
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    have h1 := tubeGap_edgePoint_pos (x := x) (hYk k hkj)
    have h2 := l1Norm_pos_of_tubeGap_pos h1
    positivity
  · exact one_pos
theorem maxBoostAngle_le_one (j : Fin b) (ζ : Fin b → ComplexVec4) :
    maxBoostAngle j ζ ≤ 1 := by apply _root_.YangMills.Construction.FieldForms.SpacelikeExtension.maxBoostAngle_le_one <;> assumption
end Edge
section Stage
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : FourBorelSet → BddOp K} {Ω : K} {A : ℝ → BddOp K} {℘ C : ℝ}
def edgeBound (℘ C : ℝ) {b : ℕ} (j : Fin b) (Y : TestSpaces.PointTuple b)
    (x : TestSpaces.PointTuple (b + 1)) : ℝ :=
  ((2 : ℝ) ^ ℘ * C) ^ (b + 1) *
    min 1 (Real.sin (maxBoostAngle j (edgePoint x Y)) *
      (spaceNorm (spacePart (MinkowskiSpace.rePart (edgePoint x Y j))) -
        |MinkowskiSpace.rePart (edgePoint x Y j) 0|)) ^
          (-ceilExponent ℘ (b + 1)) *
    ∏ k ∈ Finset.univ.erase j,
      min 1 (tubeGap (edgePoint x Y k) / 2) ^ (-ceilExponent ℘ (b + 1))
theorem continuousOn_edgeBound {b : ℕ} {j : Fin b} {Y : TestSpaces.PointTuple b}
    (hY : Y j = 0) (hYk : ∀ k, k ≠ j → Y k ∈ futureCone)
    {S : Set (TestSpaces.PointTuple (b + 1))}
    (hS : ∀ x ∈ S, x j.succ - x j.castSucc ∈ spacelikeSet) :
    ContinuousOn (edgeBound ℘ C j Y) S := by
  unfold edgeBound
  have hsin : Continuous fun x : TestSpaces.PointTuple (b + 1) =>
      Real.sin (maxBoostAngle j (edgePoint x Y)) :=
    Real.continuous_sin.comp (continuous_maxBoostAngle_edgePoint hYk)
  have hre : Continuous fun x : TestSpaces.PointTuple (b + 1) =>
      MinkowskiSpace.rePart (edgePoint x Y j) :=
    continuous_rePart.comp (continuous_edgePoint Y j)
  have hmargin : Continuous fun x : TestSpaces.PointTuple (b + 1) =>
      spaceNorm (spacePart (MinkowskiSpace.rePart (edgePoint x Y j))) -
        |MinkowskiSpace.rePart (edgePoint x Y j) 0| :=
    (continuous_spaceNorm.comp (continuous_spacePart.comp hre)).sub
      ((continuous_apply 0).comp hre).abs
  refine (continuousOn_const.mul (ContinuousOn.zpow₀
    (continuous_const.min (hsin.mul hmargin)).continuousOn _ fun x hx => Or.inl ?_)).mul
    (continuousOn_finsetProd _ fun k hk => ContinuousOn.zpow₀
      (continuous_const.min ((continuous_tubeGap.comp
        (continuous_edgePoint Y k)).div_const 2)).continuousOn _ fun x _ => Or.inl ?_)
  · have ha := maxBoostAngle_edgePoint_pos (x := x) hYk
    have ha1 := maxBoostAngle_le_one j (edgePoint x Y)
    have hs : Real.sin (maxBoostAngle j (edgePoint x Y)) > 0 :=
      Real.sin_pos_of_pos_of_lt_pi ha (by linarith [Real.pi_gt_three])
    have hsl := rePart_mem_spacelikeSet_of_mem_spacelikeSlab
      (edgePoint_mem_spacelikeSlab hY hYk (hS x hx))
    have hm := (isSpacelikeVec_iff _).1 hsl
    exact (lt_min one_pos (mul_pos hs (sub_pos.2 hm))).ne'
  · have h1 := tubeGap_edgePoint_pos (x := x) (hYk k (Finset.ne_of_mem_erase hk))
    simp only [Function.comp_apply]
    exact (lt_min one_pos (half_pos h1)).ne'
theorem extension_eq_integral_spacelikeContinuation (hV : BoundaryVectorFacts E Ω A ℘ C)
    {b : ℕ} {j : Fin b}
    (hc : SpacelikeContinuationBoundaryValue E Ω A ℘ C j)
    {φ : TestSpaces.PointTuple (b + 1) → ℂ} (hφ : φ ∈ TestSpaces.schwartzSet (b + 1))
    {S : Set (TestSpaces.PointTuple (b + 1))} (hS : IsCompact S) (hzero : ∀ x, x ∉ S → φ x = 0)
    (hsp : ∀ x ∈ S, x j.succ - x j.castSucc ∈ spacelikeSet)
    {F : TestSpaces.PointTuple b → ℂ} (hFc : ContinuousOn F (closedFutureConeTuples b))
    (hFe : ∀ Y' ∈ futureConeTuples b, F Y' = ∫ x, vacuumIntegrand E Ω A φ Y' x)
    {Y : TestSpaces.PointTuple b} (hY : Y j = 0) (hYk : ∀ k, k ≠ j → Y k ∈ futureCone) :
    F Y = ∫ x, spacelikeContinuation E Ω A j (edgePoint x Y) * φ x := by
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn
    (continuousOn_edgeBound (℘ := ℘) (C := C) hY hYk hsp)
  have hopen : ∀ ε : ℝ, 0 < ε → Function.update Y j (ε • timeUnit) ∈ futureConeTuples b := by
    intro ε hε k
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self]
      exact smul_timeUnit_mem_futureCone hε
    · rw [Function.update_of_ne hk]
      exact hYk k hk
  have hclosedY : Y ∈ closedFutureConeTuples b := by
    intro k
    by_cases hk : k = j
    · subst hk
      rw [hY]
      exact origin_mem_closedFutureCone
    · exact closedFutureCone_of_futureCone (hYk k hk)
  have hval : ∀ (ε : ℝ) (x : TestSpaces.PointTuple (b + 1)),
      vacuumIntegrand E Ω A φ (Function.update Y j (ε • timeUnit)) x =
        vacuumExpectation E Ω A (b + 1) (timeLiftedTuple j ε (edgePoint x Y)) * φ x := by
    intro ε x
    rw [timeLiftedTuple_edgePoint hY]
    rfl
  have hφint : Integrable φ := by
    refine hφ.1.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact hS fun x hx => ?_)
    by_contra hxS
    exact hx (hzero x hxS)
  have hint : Tendsto (fun ε : ℝ =>
      ∫ x, vacuumIntegrand E Ω A φ (Function.update Y j (ε • timeUnit)) x)
      (𝓝[>] 0) (𝓝 (∫ x, spacelikeContinuation E Ω A j (edgePoint x Y) * φ x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => M * ‖φ x‖) ?_ ?_
      (hφint.norm.const_mul M) ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hV.integrable_vacuumIntegrand b φ hφ _ (hopen ε hε)).aestronglyMeasurable
    · filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
      refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ S
      · rw [hval, norm_mul]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have hb := (hc _ (edgePoint_mem_spacelikeSlab hY hYk (hsp x hx))).2.2 ε hε.1 hε.2
        exact hb.trans ((Real.le_norm_self _).trans (hM x hx))
      · simp [vacuumIntegrand, hzero x hx]
    · refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ S
      · have hl := (hc _ (edgePoint_mem_spacelikeSlab hY hYk (hsp x hx))).2.1
        simp only [hval]
        exact hl.mul_const _
      · simp [vacuumIntegrand, hzero x hx]
  have hpath : Tendsto (fun ε : ℝ => Function.update Y j (ε • timeUnit)) (𝓝[>] 0) (𝓝 Y) := by
    have hcont : Continuous fun ε : ℝ => Function.update Y j (ε • timeUnit) :=
      continuous_const.update j (continuous_id.smul continuous_const)
    have h0 : Function.update Y j ((0 : ℝ) • timeUnit) = Y := by
      rw [zero_smul, ← hY, Function.update_eq_self]
    have h := hcont.tendsto 0
    simp only [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hself : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := eventually_mem_nhdsWithin
  have hF1 : Tendsto (fun ε : ℝ => F (Function.update Y j (ε • timeUnit))) (𝓝[>] 0)
      (𝓝 (F Y)) :=
    ((hFc Y hclosedY).tendsto).comp (tendsto_nhdsWithin_iff.mpr
      ⟨hpath, hself.mono fun ε hε k => closedFutureCone_of_futureCone (hopen ε hε k)⟩)
  refine tendsto_nhds_unique (hF1.congr' ?_) hint
  filter_upwards [hself] with ε hε
  exact hFe _ (hopen ε hε)
end Stage
section Locality
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : FourBorelSet → BddOp K} {Ω : K} {A : ℝ → BddOp K} {℘ C : ℝ}
theorem neg_mem_spacelikeSet {x : RealVec4} (hx : x ∈ spacelikeSet) :
    -x ∈ spacelikeSet := by
  have h := (isSpacelikeVec_iff x).1 hx
  refine (isSpacelikeVec_iff (-x)).2 ?_
  have hs : spaceNorm (spacePart (-x)) = spaceNorm (spacePart x) := by
    simp [spaceNorm, spacePart]
  rw [hs]
  simpa using h
theorem measurePreserving_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun x : TestSpaces.PointTuple n => x ∘ σ) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin n => Fin 4 → ℝ) σ.symm
  have e : (fun x : TestSpaces.PointTuple n => x ∘ σ) =
      MeasurableEquiv.piCongrLeft (fun _ : Fin n => Fin 4 → ℝ) σ.symm := by
    funext x i
    have hi : i = σ.symm (σ i) := by simp
    conv_rhs => rw [hi]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rfl
  rw [e]
  exact h
theorem integral_spacelikeContinuation_swap {b : ℕ} {j : Fin b}
    (hex : ∀ z : Fin (b + 1) → ComplexVec4,
      adjacentSwapMap j (successiveDiffs z) = successiveDiffs (z ∘ Equiv.swap j.castSucc j.succ))
    (hinv : SpacelikeContinuationSwapInvariant E Ω A j)
    (u : Fin (b + 1) → TestFn) {S : Set (TestSpaces.PointTuple (b + 1))}
    (hzero : ∀ x, x ∉ S → testTensor u x = 0)
    (hsp : ∀ x ∈ S, x j.succ - x j.castSucc ∈ spacelikeSet)
    {Y : TestSpaces.PointTuple b} (hY : Y j = 0) (hYk : ∀ k, k ≠ j → Y k ∈ futureCone) :
    (∫ x, spacelikeContinuation E Ω A j (edgePoint x Y) *
        testTensor (u ∘ Equiv.swap j.castSucc j.succ) x) =
      ∫ x, spacelikeContinuation E Ω A j (edgePoint x Y) * testTensor u x := by
  set σ := Equiv.swap j.castSucc j.succ with hσ
  have hmp := measurePreserving_comp_perm σ
  have hemb : MeasurableEmbedding (fun x : TestSpaces.PointTuple (b + 1) => x ∘ σ) := by
    let e : TestSpaces.PointTuple (b + 1) ≃ᵐ TestSpaces.PointTuple (b + 1) :=
      { toFun := fun x => x ∘ σ
        invFun := fun x => x ∘ σ.symm
        left_inv := fun x => by
          funext i
          simp
        right_inv := fun x => by
          funext i
          simp
        measurable_toFun := measurable_pi_lambda _ fun i => measurable_pi_apply _
        measurable_invFun := measurable_pi_lambda _ fun i => measurable_pi_apply _ }
    exact e.measurableEmbedding
  rw [← hmp.integral_comp hemb]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have htensor : testTensor (u ∘ σ) (x ∘ σ) = testTensor u x := by
    simp only [testTensor_apply, Function.comp_apply]
    exact Equiv.prod_comp σ fun i => (u i).1 (x i)
  have hY' : adjacentSwapMap j (tupleToComplex Y) = tupleToComplex Y := by
    funext k
    have hz : tupleToComplex Y j = 0 := by
      funext μ
      simp [tupleToComplex, toComplex, hY]
    simp only [adjacentSwapMap, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs with h1 h2
    · rw [h1, hz, neg_zero]
    · rw [hz, add_zero]
    · rfl
  have hpt : edgePoint (x ∘ σ) Y = adjacentSwapMap j (edgePoint x Y) := by
    unfold edgePoint
    rw [map_add, map_smul, hY', hex]
    rfl
  change spacelikeContinuation E Ω A j (edgePoint (x ∘ σ) Y) *
    testTensor (u ∘ σ) (x ∘ σ) =
      spacelikeContinuation E Ω A j (edgePoint x Y) * testTensor u x
  rw [htensor, hpt]
  by_cases hx : x ∈ S
  · rw [hinv.2 _ (edgePoint_mem_spacelikeSlab hY hYk (hsp x hx))]
  · rw [hzero x hx, mul_zero, mul_zero]
def SpacelikeSeparatedAt {b : ℕ} (j : Fin b) (u : Fin (b + 1) → TestFn) : Prop :=
  ∀ x ∈ tsupport (u j.castSucc).1, ∀ y ∈ tsupport (u j.succ).1, y - x ∈ spacelikeSet
theorem testTensor_eq_zero_of_not_mem {b : ℕ} (u : Fin (b + 1) → TestFn)
    {x : TestSpaces.PointTuple (b + 1)} (hx : x ∉ Set.pi Set.univ fun i => tsupport (u i).1) :
    testTensor u x = 0 := by
  rw [Set.mem_univ_pi] at hx
  obtain ⟨i, hi⟩ := not_forall.1 hx
  rw [testTensor_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)
theorem swap_invariant_of_hasCompactSupport (hV : BoundaryVectorFacts E Ω A ℘ C) {b : ℕ}
    {j : Fin b}
    (hex : ∀ z : Fin (b + 1) → ComplexVec4,
      adjacentSwapMap j (successiveDiffs z) = successiveDiffs (z ∘ Equiv.swap j.castSucc j.succ))
    (hc : SpacelikeContinuationBoundaryValue E Ω A ℘ C j)
    (hinv : SpacelikeContinuationSwapInvariant E Ω A j)
    (u : Fin (b + 1) → TestFn) (hu : SpacelikeSeparatedAt j u)
    (hcs : ∀ i, HasCompactSupport (u i).1) :
    wightmanFunctional E Ω A (b + 1) (testTensor (u ∘ Equiv.swap j.castSucc j.succ)) =
      wightmanFunctional E Ω A (b + 1) (testTensor u) := by
  set σ := Equiv.swap j.castSucc j.succ with hσ
  have hσ₁ : σ j.castSucc = j.succ := Equiv.swap_apply_left _ _
  have hσ₂ : σ j.succ = j.castSucc := Equiv.swap_apply_right _ _
  have hφ := testTensor_mem hV u
  have hφ' := testTensor_mem hV (u ∘ σ)
  obtain ⟨F, hFc, hFe, hF0⟩ := hV.exists_continuousOn_extension b _ hφ
  obtain ⟨G, hGc, hGe, hG0⟩ := hV.exists_continuousOn_extension b _ hφ'
  have hS : IsCompact (Set.pi Set.univ fun i => tsupport (u i).1) :=
    isCompact_univ_pi fun i => hcs i
  have hS' : IsCompact (Set.pi Set.univ fun i => tsupport ((u ∘ σ) i).1) :=
    isCompact_univ_pi fun i => hcs (σ i)
  have hsp : ∀ x ∈ Set.pi Set.univ (fun i => tsupport (u i).1),
      x j.succ - x j.castSucc ∈ spacelikeSet := fun x hx =>
    hu _ (hx j.castSucc trivial) _ (hx j.succ trivial)
  have hsp' : ∀ x ∈ Set.pi Set.univ (fun i => tsupport ((u ∘ σ) i).1),
      x j.succ - x j.castSucc ∈ spacelikeSet := by
    intro x hx
    have h1 : x j.succ ∈ tsupport (u j.castSucc).1 := by
      have := hx j.succ trivial
      simpa only [Function.comp_apply, hσ₂] using this
    have h2 : x j.castSucc ∈ tsupport (u j.succ).1 := by
      have := hx j.castSucc trivial
      simpa only [Function.comp_apply, hσ₁] using this
    have := neg_mem_spacelikeSet (hu _ h1 _ h2)
    rwa [neg_sub] at this
  have hedge : ∀ Y : TestSpaces.PointTuple b, Y j = 0 → (∀ k, k ≠ j → Y k ∈ futureCone) →
      G Y = F Y := by
    intro Y hY hYk
    rw [extension_eq_integral_spacelikeContinuation hV hc hφ hS
        (fun x hx => testTensor_eq_zero_of_not_mem u hx) hsp hFc hFe hY hYk,
      extension_eq_integral_spacelikeContinuation hV hc hφ' hS'
        (fun x hx => testTensor_eq_zero_of_not_mem (u ∘ σ) hx) hsp' hGc hGe hY hYk]
    exact integral_spacelikeContinuation_swap hex hinv u
      (fun x hx => testTensor_eq_zero_of_not_mem u hx) hsp hY hYk
  let path : ℝ → TestSpaces.PointTuple b := fun t => Function.update (fun _ => t • timeUnit) j 0
  have hpathj : ∀ t, path t j = 0 := fun t => Function.update_self _ _ _
  have hpathk : ∀ t : ℝ, 0 < t → ∀ k, k ≠ j → path t k ∈ futureCone := by
    intro t ht k hk
    simp only [path, Function.update_of_ne hk]
    exact smul_timeUnit_mem_futureCone ht
  have hclosed : ∀ t : ℝ, 0 < t → path t ∈ closedFutureConeTuples b := by
    intro t ht k
    by_cases hk : k = j
    · subst hk
      rw [hpathj]
      exact origin_mem_closedFutureCone
    · exact closedFutureCone_of_futureCone (hpathk t ht k hk)
  have hzeroc : (0 : TestSpaces.PointTuple b) ∈ closedFutureConeTuples b :=
    fun _ => origin_mem_closedFutureCone
  have hcpath : Tendsto path (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous path :=
      (continuous_pi fun _ => continuous_id.smul continuous_const).update j continuous_const
    have h0 : path 0 = 0 := by
      funext k
      by_cases hk : k = j
      · subst hk
        rw [hpathj]
        rfl
      · simp [path, Function.update_of_ne hk]
    simpa [h0] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hself : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  have hto : Tendsto path (𝓝[>] 0) (𝓝[closedFutureConeTuples b] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcpath, hself.mono fun t ht => hclosed t ht⟩
  have hlimF : Tendsto (fun t => F (path t)) (𝓝[>] 0) (𝓝 (F 0)) :=
    ((hFc 0 hzeroc).tendsto).comp hto
  have hlimG : Tendsto (fun t => G (path t)) (𝓝[>] 0) (𝓝 (G 0)) :=
    ((hGc 0 hzeroc).tendsto).comp hto
  have heq : (fun t => G (path t)) =ᶠ[𝓝[>] 0] fun t => F (path t) := by
    filter_upwards [hself] with t ht
    exact hedge _ (hpathj t) (hpathk t ht)
  rw [← hF0, ← hG0]
  exact tendsto_nhds_unique (hlimG.congr' heq) hlimF
theorem swap_invariant (hform : IsBoundedFieldForm E Ω A ℘ C) (hV : BoundaryVectorFacts E Ω A ℘ C)
    (hF : TestSpaces.Elementary.BasicProperties)
    (hR : TestSpaces.DerivRules.Combined)
    (htr : TestSpaces.SchwartzTruncationApprox) {b : ℕ} {j : Fin b}
    (hcpt : ∀ u : Fin (b + 1) → TestFn, SpacelikeSeparatedAt j u →
      (∀ i, HasCompactSupport (u i).1) →
      wightmanFunctional E Ω A (b + 1) (testTensor (u ∘ Equiv.swap j.castSucc j.succ)) =
        wightmanFunctional E Ω A (b + 1) (testTensor u))
    (u : Fin (b + 1) → TestFn) (hu : SpacelikeSeparatedAt j u) :
    wightmanFunctional E Ω A (b + 1) (testTensor (u ∘ Equiv.swap j.castSucc j.succ)) =
      wightmanFunctional E Ω A (b + 1) (testTensor u) := by
  classical
  set σ := Equiv.swap j.castSucc j.succ with hσ
  have key : ∀ S : Finset (Fin (b + 1)), ∀ u : Fin (b + 1) → TestFn,
      SpacelikeSeparatedAt j u → (∀ i, i ∉ S → HasCompactSupport (u i).1) →
      wightmanFunctional E Ω A (b + 1) (testTensor (u ∘ σ)) =
        wightmanFunctional E Ω A (b + 1) (testTensor u) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro u hu hc
      exact hcpt u hu fun i => hc i (Finset.notMem_empty i)
    | insert a S ha ih =>
      intro u hu hc
      have hbound : ∀ ε : ℝ, 0 < ε →
          ‖wightmanFunctional E Ω A (b + 1) (testTensor (u ∘ σ)) -
              wightmanFunctional E Ω A (b + 1) (testTensor u)‖ ≤
            (oneSlotConst ℘ C (u ∘ σ) (σ a) + oneSlotConst ℘ C u a) *
              (Real.pi ^ 2 * ε) := by
        intro ε hε
        obtain ⟨g, hgc, hgs, hgn⟩ := exists_hasCompactSupport_schwartzNorm_sub_le hF hR htr (u a)
          (k := (boundOrder ℘ (b + 1)).toNat + 6) (by omega) hε
        have hd := sub_mem_schwartzR4 hF (u a).2 g.2
        have hδ : maxPartialL1 (boundOrder ℘ (b + 1)).toNat ((u a).1 - g.1) ≤
            Real.pi ^ 2 * ε := by
          have h1 := hV.maxPartialL1_le (boundOrder ℘ (b + 1)).toNat _ hd
          have h2 : ENNReal.ofReal (maxPartialL1 (boundOrder ℘ (b + 1)).toNat
              ((u a).1 - g.1)) ≤ ENNReal.ofReal (Real.pi ^ 2 * ε) := by
            rw [ENNReal.ofReal_mul (by positivity)]
            exact h1.trans (mul_le_mul_right hgn _)
          exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
        set v := Function.update u a g with hv
        have hsub : ∀ i, tsupport (v i).1 ⊆ tsupport (u i).1 := by
          intro i
          by_cases hi : i = a
          · subst hi
            simpa [hv] using hgs
          · simp [hv, Function.update_of_ne hi]
        have hvs : SpacelikeSeparatedAt j v := fun x hx y hy =>
          hu x (hsub _ hx) y (hsub _ hy)
        have hvc : ∀ i, i ∉ S → HasCompactSupport (v i).1 := by
          intro i hi
          by_cases hia : i = a
          · subst hia
            simpa [hv] using hgc
          · simp only [hv, Function.update_of_ne hia]
            exact hc i (by simp [hia, hi])
        have hih := ih v hvs hvc
        have hcomp : v ∘ σ = Function.update (u ∘ σ) (σ a) g := by
          have := Function.update_comp_equiv u σ a g
          rw [hv, this, Equiv.symm_swap]
        have hδ' : maxPartialL1 (boundOrder ℘ (b + 1)).toNat
            (((u ∘ σ) (σ a)).1 - g.1) ≤ Real.pi ^ 2 * ε := by
          simpa [hσ] using hδ
        have h1 := norm_wightmanFunctional_sub_update_le hform hV hF u a g hδ
        have h2 := norm_wightmanFunctional_sub_update_le hform hV hF (u ∘ σ) (σ a) g hδ'
        rw [← hcomp, hih] at h2
        have h3 := norm_sub_le_norm_sub_add_norm_sub
          (wightmanFunctional E Ω A (b + 1) (testTensor (u ∘ σ)))
          (wightmanFunctional E Ω A (b + 1) (testTensor v))
          (wightmanFunctional E Ω A (b + 1) (testTensor u))
        rw [norm_sub_rev (wightmanFunctional E Ω A (b + 1) (testTensor v))] at h3
        calc _ ≤ _ := h3
          _ ≤ _ := add_le_add h2 h1
          _ = _ := by ring
      have hlim : Tendsto (fun ε : ℝ =>
          (oneSlotConst ℘ C (u ∘ σ) (σ a) + oneSlotConst ℘ C u a) *
            (Real.pi ^ 2 * ε)) (𝓝[>] 0) (𝓝 0) := by
        have hcont : Continuous fun ε : ℝ =>
            (oneSlotConst ℘ C (u ∘ σ) (σ a) + oneSlotConst ℘ C u a) *
              (Real.pi ^ 2 * ε) := by
          fun_prop
        have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
        simpa using h
      have hself : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := eventually_mem_nhdsWithin
      have hle := ge_of_tendsto hlim (hself.mono hbound)
      exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)
  exact key Finset.univ u hu fun i hi => absurd (Finset.mem_univ i) hi
end Locality
theorem wightmanLocality (hvec : RealPointVectors.BoundaryVectorsStatement)
    (hjost : FieldForms.SpacelikeExtension.Statement)
    (hF : TestSpaces.Elementary.BasicProperties)
    (hR : TestSpaces.DerivRules.Combined)
    (htr : TestSpaces.SchwartzTruncationApprox) : WightmanLocalityStatement := by
  intro K _ _ _ E Ω A ℘ C hform heuc b j f hf
  have hV := hvec E Ω A ℘ C hform
  obtain ⟨-, hex, -, -, hc, hinv⟩ := hjost K E Ω A ℘ C hform heuc b j
  exact swap_invariant hform hV hF hR htr
    (fun u hu hcs => swap_invariant_of_hasCompactSupport hV hex hc hinv u hu hcs) f hf
end YangMills.Construction.WightmanLocality
