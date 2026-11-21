import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumpsProof
import Reconstruction.MinkowskiSpace.EuclideanFormOfAnInvariantRepresentedSequenceProof
import Reconstruction.MinkowskiSpace.FormRepresentsItsFunctionalAndIsEuclidean
import Reconstruction.MinkowskiSpace.TimeTranslationOfTheVectorsOfSmoothSequencesProof
import YangMills.Construction.ReflectionPositivity.PropertiesOfTheFormOfAFunctionalProof
import Mathlib
set_option autoImplicit false
open Filter Topology MeasureTheory
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.RepresentsEuclideanProof
open TestSpaces MinkowskiSpace Motions SeparatedTuples ReflectionPositivity.TupleForm
  ReflectionPositivity.FormProperties FieldFormConditions ProjectionMeasures HilbertToolkit
  OneLoopNotation ComplexHilbert FieldForms InsertedFieldForm WightmanReconstruction WightmanTheory
theorem coe_spanBasisIn_val (O : Set (Fin 4 → ℝ)) (X : supportedIn O) :
    ((spanBasisIn O X : spanIn O) : FormalSpan) = basisVec X.1 := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.coe_spanBasisIn <;> assumption
theorem juxt_nil_left (X : SeparatedTuples.SepTuple) :
    SeparatedTuples.SepTuple.juxt SeparatedTuples.SepTuple.nil X = X := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.nil_juxt <;> assumption
theorem inner_vacuumState_stateOf (hW : HilbertWellDefined.WellDefinedStatement)
    (hC : FormCompletion.FormCompletionIsHilbertSpace) {σ : TestSpaces.SepTuple → ℝ}
    (hp : PairingPosSemidef σ) (X : supportedIn TimeAxis.upperHalfSpace) :
    ⟪vacuumState σ, stateOf σ (spanBasisIn TimeAxis.upperHalfSpace X)⟫_ℂ =
      ((σ (TupleLists.ofList X.1) : ℝ) : ℂ) := by
  have hH := (hW.1 _ (FieldFormConditions.pairing σ) hp).1
  have hI := (hC _ _ hH).2.1.2.2.2.2.2.2.1
  have hpush : ∀ Y : SeparatedTuples.SepTuple, pushSpan TimeAxis.timeReflection (basisVec Y) =
      basisVec (push TimeAxis.timeReflection Y) := fun Y => linearExtend_basisVec _ Y
  change inner ℂ (FormCompletion.classVec _ _) (FormCompletion.classVec _ _) = _
  rw [hI]
  simp only [FieldFormConditions.pairing, ReflectionPositivity.TupleForm.reflectConj, unitSpan,
    coe_spanBasisIn_val, conjugation_basisVec, hpush, push_nil, formalMul_basisVec, juxt_nil_left]
  exact linearExtend_basisVec _ _
section Tube
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
theorem wickMapTuple_mem_diffCoordsInTube {m : ℕ} {x : PointTuple (m + 1)}
    (hx : x ∈ increasingPositiveTimes (m + 1)) :
    wickMapTuple (tupleToComplex x) ∈ diffCoordsInTube (m + 1) := by apply _root_.YangMills.Construction.MinkowskiSpace.WickTimeShift.wickMapTuple_mem_diffCoordsInTube <;> assumption
theorem inner_stateVector_eq_orderedSchwinger {E : FourBorelSet → BddOp K} {Ω : K}
    {A : ℝ → BddOp K} (h : StatesTranslateInner E Ω A) {m : ℕ}
    {x : PointTuple (m + 1)} (hx : x ∈ increasingPositiveTimes (m + 1)) :
    ⟪Ω, stateVector E Ω A (m + 1) (wickMapTuple (tupleToComplex x))⟫_ℂ =
      orderedSchwinger E Ω A m x := by
  have hw : (Fin.elim0 : Fin 0 → ComplexVec4) ∈ diffCoordsInTube 0 := fun i => i.elim0
  have hω : MinkowskiSpace.imPart (0 : ComplexVec4) ∈ closedFutureCone := by
    have h0 : MinkowskiSpace.imPart (0 : ComplexVec4) = 0 := by
      funext μ
      simp [MinkowskiSpace.imPart]
    rw [h0]
    change coneGap 0 ≥ 0
    simp [coneGap, spacePart, spaceNorm]
  exact (h (m + 1) 0 _ _ 0 (wickMapTuple_mem_diffCoordsInTube hx) hw hω).2.1
end Tube
section Continuity
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
theorem continuousOn_orderedSchwinger {E : FourBorelSet → BddOp K} {Ω : K}
    {A : ℝ → BddOp K} (hd : FieldProductHolomorphic E A) (m : ℕ) :
    ContinuousOn (orderedSchwinger E Ω A m) (increasingTimes (m + 1)) := by apply _root_.YangMills.Construction.MinkowskiSpace.InvariantEuclideanProof.continuousOn_orderedSchwinger <;> assumption
end Continuity
theorem tsupport_tensorProdComplex_subset_pi {n : ℕ} (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    tsupport (tensorProdComplex f) ⊆ Set.univ.pi fun i => tsupport (f i) := by
  refine closure_minimal ?_ (isClosed_set_pi fun i _ => isClosed_tsupport _)
  intro x hx i _
  by_contra h
  apply hx
  have h0 : f i (x i) = 0 := image_eq_zero_of_notMem_tsupport h
  have h1 : tensorProd f x = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h0
  simp [tensorProdComplex, h1]
theorem mem_increasingTimes_of_isCutSequence {n : ℕ} {f : Fin n → (Fin 4 → ℝ) → ℝ}
    {c : Fin (n + 1) → ℝ} (hc : IsCutSequence f c) {x : PointTuple n}
    (hx : ∀ i, x i ∈ tsupport (f i)) : x ∈ increasingTimes n := by
  intro i j hij
  have h₁ := (hc.2 i (hx i)).2
  have h₂ := (hc.2 j (hx j)).1
  have h₃ : c i.succ ≤ c j.castSucc := hc.1.monotone (by
    rw [Fin.le_def]
    simpa using hij)
  exact h₁.trans_le h₃ |>.trans h₂
theorem pairwise_disjoint_tsupport_of_isCutSequence {n : ℕ} {f : Fin n → (Fin 4 → ℝ) → ℝ}
    {c : Fin (n + 1) → ℝ} (hc : IsCutSequence f c) :
    Pairwise fun i i' => Disjoint (tsupport (f i)) (tsupport (f i')) := by
  have key : ∀ i j : Fin n, i < j → Disjoint (tsupport (f i)) (tsupport (f j)) := by
    intro i j hij
    refine Set.disjoint_left.2 fun u h₁ h₂ => ?_
    have h₃ : c i.succ ≤ c j.castSucc := hc.1.monotone (by
      rw [Fin.le_def]
      simpa using hij)
    exact absurd ((hc.2 i h₁).2.trans_le h₃ |>.trans (hc.2 j h₂).1) (lt_irrefl _)
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm
section Represents
variable {σ : TestSpaces.SepTuple → ℝ} {E : FourBorelSet → BddOp (StateSpace σ)}
  {A : ℝ → BddOp (StateSpace σ)}
theorem eq_orderedIntegral_of_upperHalf (hW : HilbertWellDefined.WellDefinedStatement)
    (hC : FormCompletion.FormCompletionIsHilbertSpace) (hp : PairingPosSemidef σ)
    (hv : StatesTranslateInner E (vacuumState σ) A) (hwr : HasTimeOrderedIntegral σ E A)
    (m : ℕ) (X : SepTupleOfCard (m + 1))
    (hX : TupleLists.toList ⟨m + 1, X⟩ ∈ supportedIn TimeAxis.upperHalfSpace)
    (hT : IsTimeOrdered X.1) :
    ((σ ⟨m + 1, X⟩ : ℝ) : ℂ) = orderedIntegral E (vacuumState σ) A m (tensorProdComplex X.1) := by
  obtain ⟨hint, hcl⟩ := hwr m X hX hT
  have hwi := (hW.2.2.2 _ _ _ _ _ hint).1 (vacuumState σ)
  rw [← hcl, inner_vacuumState_stateOf hW hC hp ⟨_, hX⟩, TupleLists.ofList_toList] at hwi
  rw [hwi]
  obtain ⟨-, c, hc⟩ := hT
  have hsup : tsupport (tensorProdComplex X.1) ⊆ increasingPositiveTimes (m + 1) := by
    intro x hx
    have hx' := tsupport_tensorProdComplex_subset_pi X.1 hx
    refine ⟨mem_increasingTimes_of_isCutSequence hc fun i => hx' i (Set.mem_univ i), fun _ => ?_⟩
    have hf : X.1 0 ∈ (TupleLists.toList ⟨m + 1, X⟩).1 := (List.mem_ofFn' _ _).2 ⟨0, rfl⟩
    exact hX _ hf (hx' 0 (Set.mem_univ 0))
  unfold orderedIntegral
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport (tensorProdComplex X.1))
    (μ := volume) (f := (increasingTimes (m + 1)).indicator
      fun y => tensorProdComplex X.1 y * orderedSchwinger E (vacuumState σ) A m y)]
  · refine setIntegral_congr_fun (isClosed_tsupport (tensorProdComplex X.1)).measurableSet
      fun x hx => ?_
    rw [Set.indicator_of_mem (hsup hx).1]
    congr 1
    exact inner_stateVector_eq_orderedSchwinger hv (hsup hx)
  · intro x hx
    have h0 : tensorProdComplex X.1 x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [h0]
theorem orderedIntegral_translate {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K)
    (m : ℕ) (v : Fin 4 → ℝ) (φ φ' : PointTuple (m + 1) → ℂ)
    (h : ∀ u : PointTuple (m + 1), φ' (fun i => u i + v) = φ u) :
    orderedIntegral E Ω A m φ' = orderedIntegral E Ω A m φ := by
  unfold orderedIntegral
  rw [← integral_add_right_eq_self _ (fun _ => v : PointTuple (m + 1))]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  have hmem : (u + fun _ => v) ∈ increasingTimes (m + 1) ↔ u ∈ increasingTimes (m + 1) := by
    simp only [increasingTimes, Set.mem_ofPred_eq, StrictMono, timeCoord, Pi.add_apply,
      add_lt_add_iff_right]
  have hd : FieldForms.wickDiffs (u + fun _ => v) = FieldForms.wickDiffs u := by
    funext i μ
    fin_cases μ <;>
      simp [FieldForms.wickDiffs, successiveDiffs, wickMapTuple, tupleToComplex, wickMap,
        MinkowskiSpace.toComplex, mul_add]
  have ho : orderedSchwinger E Ω A m (u + fun _ => v) = orderedSchwinger E Ω A m u :=
    congrArg (vacuumExpectation E Ω A (m + 1)) hd
  beta_reduce
  by_cases hu : u ∈ increasingTimes (m + 1)
  · rw [Set.indicator_of_mem (hmem.2 hu), Set.indicator_of_mem hu, ho]
    exact congrArg (· * _) (h u)
  · rw [Set.indicator_of_notMem (fun h' => hu (hmem.1 h')), Set.indicator_of_notMem hu]
theorem eq_orderedIntegral (hW : HilbertWellDefined.WellDefinedStatement)
    (hC : FormCompletion.FormCompletionIsHilbertSpace) (hp : PairingPosSemidef σ)
    (hinv : ∀ r : RigidMotion, IsMotionInvariant σ r)
    (hv : StatesTranslateInner E (vacuumState σ) A) (hwr : HasTimeOrderedIntegral σ E A)
    (m : ℕ) (X : SepTupleOfCard (m + 1)) (hT : IsTimeOrdered X.1) :
    ((σ ⟨m + 1, X⟩ : ℝ) : ℂ) = orderedIntegral E (vacuumState σ) A m (tensorProdComplex X.1) := by
  obtain ⟨-, c, hc⟩ := id hT
  set v : Fin 4 → ℝ := (-(c 0)) • timeUnitVec with hvdef
  have hv3 : v 3 = -(c 0) := by
    simp [hvdef, timeUnitVec, PeriodicLattice.coordVec, TimeAxis.timeIdx]
  set r := UpperHalfTensors.translateMotion v with hr
  set Y : SepTupleOfCard (m + 1) := (UpperHalfTensors.actOnSTuple r ⟨m + 1, X⟩).2 with hY
  have hσ : σ ⟨m + 1, Y⟩ = σ ⟨m + 1, X⟩ := hinv r ⟨m + 1, X⟩
  have hYa : ∀ i u, Y.1 i u = X.1 i (u - v) := fun i u =>
    UpperHalfTensors.translateFun_apply v (X.1 i) u
  have hYs : ∀ i, ∀ u ∈ tsupport (Y.1 i), u - v ∈ tsupport (X.1 i) := by
    intro i u hu
    have h := UpperHalfTensors.tsupport_actOnPointFun r (X.1 i)
    have hu' : u ∈ tsupport (actOnPointFun r (X.1 i)) := hu
    rw [h] at hu'
    have he : (UpperHalfTensors.rigidHomeomorph r).symm u = u - v := by
      simp [UpperHalfTensors.rigidHomeomorph, RigidMotion.invFun, hr,
        UpperHalfTensors.translateMotion]
    rw [Set.mem_preimage, he] at hu'
    exact hu'
  have hcY : IsCutSequence Y.1 fun k => c k - c 0 := by
    refine ⟨fun a b hab => sub_lt_sub_right (hc.1 hab) _, fun i u hu => ?_⟩
    have h := hc.2 i (hYs i u hu)
    have e : (u - v) 3 = u 3 + c 0 := by simp [hv3]
    simp only [Set.mem_ofPred_eq, e] at h
    constructor <;> simp only <;> linarith [h.1, h.2]
  have hTY : IsTimeOrdered Y.1 := ⟨Y.2, _, hcY⟩
  have hpos : TupleLists.toList ⟨m + 1, Y⟩ ∈ supportedIn TimeAxis.upperHalfSpace := by
    intro f hf u hu
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    have h₁ := (hcY.2 i hu).1
    have h₂ : (0 : ℝ) ≤ c i.castSucc - c 0 := sub_nonneg.2 (hc.1.monotone (Fin.zero_le _))
    exact lt_of_le_of_lt h₂ h₁
  rw [← hσ, eq_orderedIntegral_of_upperHalf hW hC hp hv hwr m Y hpos hTY]
  refine orderedIntegral_translate E (vacuumState σ) A m v _ _ fun u => ?_
  simp only [tensorProdComplex, tensorProd, hYa, add_sub_cancel_right]
end Represents
section Mollifiers
open TorusMetric (euclidNormVec)
def shiftedMollifier (ε : ℝ) (a : Fin 4 → ℝ) : (Fin 4 → ℝ) → ℝ :=
  fun u => scaledMollifier ε (u - a)
theorem euclidNormVec_smul (c : ℝ) (v : Fin 4 → ℝ) :
    euclidNormVec (c • v) = |c| * euclidNormVec v := by apply _root_.YangMills.SharedProofs.p37834 <;> assumption
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
variable {ε : ℝ}
theorem dist_le_of_shiftedMollifier_ne_zero (hj : IsStandardMollifier stdMollifier) (hε : 0 < ε)
    {a u : Fin 4 → ℝ} (h : shiftedMollifier ε a u ≠ 0) : dist u a ≤ ε := by
  have h1 : stdMollifier (ε⁻¹ • (u - a)) ≠ 0 := fun h0 =>
    h (by simp [shiftedMollifier, scaledMollifier, h0])
  have h2 : euclidNormVec (ε⁻¹ • (u - a)) < 1 := by
    by_contra hn
    exact h1 (hj.2.2.2.1 _ (not_lt.1 hn))
  rw [euclidNormVec_smul, abs_of_pos (inv_pos.2 hε)] at h2
  have h3 : euclidNormVec (u - a) < ε := by
    rwa [inv_mul_lt_iff₀ hε, mul_one] at h2
  refine (dist_pi_le_iff hε.le).2 fun μ => ?_
  rw [Real.dist_eq]
  exact (abs_apply_le_euclidNormVec (u - a) μ).trans h3.le
theorem tsupport_shiftedMollifier_subset (hj : IsStandardMollifier stdMollifier) (hε : 0 < ε)
    (a : Fin 4 → ℝ) : tsupport (shiftedMollifier ε a) ⊆ Metric.closedBall a ε :=
  closure_minimal (fun _ hu => dist_le_of_shiftedMollifier_ne_zero hj hε hu)
    Metric.isClosed_closedBall
theorem contDiff_shiftedMollifier (hj : IsStandardMollifier stdMollifier) (a : Fin 4 → ℝ) :
    ContDiff ℝ ∞ (shiftedMollifier ε a) :=
  contDiff_const.mul (hj.1.1.comp ((contDiff_id.sub contDiff_const).const_smul ε⁻¹))
theorem shiftedMollifier_mem_c1CompactSupp (hj : IsStandardMollifier stdMollifier) (hε : 0 < ε)
    (a : Fin 4 → ℝ) : shiftedMollifier ε a ∈ c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) :=
  ⟨(contDiff_shiftedMollifier hj a).of_le (by exact_mod_cast le_top),
    (isCompact_closedBall a ε).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_shiftedMollifier_subset hj hε a), Set.subset_univ _⟩
theorem shiftedMollifier_nonneg (hj : IsStandardMollifier stdMollifier) (hε : 0 < ε)
    (a u : Fin 4 → ℝ) : 0 ≤ shiftedMollifier ε a u :=
  mul_nonneg (zpow_nonneg hε.le _) (hj.2.1 _)
theorem integral_shiftedMollifier (hj : IsStandardMollifier stdMollifier) (hε : 0 < ε)
    (a : Fin 4 → ℝ) : ∫ u, shiftedMollifier ε a u = 1 := by
  have h1 : ∫ u, shiftedMollifier ε a u = ∫ u, scaledMollifier ε u :=
    integral_sub_right_eq_self (scaledMollifier ε) a
  rw [h1]
  simp only [scaledMollifier]
  rw [integral_const_mul, Measure.integral_comp_inv_smul, hj.2.2.1]
  have hne : ε ≠ 0 := hε.ne'
  simp [abs_of_pos hε, hne]
theorem shiftedMollifier_mulVec (hj : IsStandardMollifier stdMollifier)
    {R : Matrix (Fin 4) (Fin 4) ℝ} (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (a u : Fin 4 → ℝ) :
    shiftedMollifier ε (R.mulVec a) (R.mulVec u) = shiftedMollifier ε a u := by
  simp only [shiftedMollifier, scaledMollifier]
  have h : ε⁻¹ • (R.mulVec u - R.mulVec a) = R.mulVec (ε⁻¹ • (u - a)) := by
    rw [← Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [h, hj.2.2.2.2 R hR]
def mollifierFamily (ε : ℝ) {n : ℕ} (p : PointTuple n) : Fin n → (Fin 4 → ℝ) → ℝ :=
  fun i => shiftedMollifier ε (p i)
theorem isTimeOrdered_mollifierFamily (hj : IsStandardMollifier stdMollifier) {m : ℕ}
    {p : PointTuple (m + 1)} (hε : 0 < ε)
    (hgap : ∀ k : Fin m, 4 * ε < timeCoord p k.succ - timeCoord p k.castSucc) :
    IsTimeOrdered (mollifierFamily ε p) := by
  set c : Fin (m + 2) → ℝ :=
    Fin.snoc (α := fun _ => ℝ) (fun k : Fin (m + 1) => timeCoord p k - 2 * ε)
      (timeCoord p (Fin.last m) + 2 * ε) with hcdef
  have hc0 : ∀ k : Fin (m + 1), c k.castSucc = timeCoord p k - 2 * ε := fun k => by
    simp [hcdef]
  have hcl : c (Fin.last (m + 1)) = timeCoord p (Fin.last m) + 2 * ε := by
    simp [hcdef]
  have hcs : ∀ k : Fin (m + 1), timeCoord p k + ε < c k.succ := by
    intro k
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · rw [Fin.succ_last, hcl]
      linarith
    · rw [Fin.succ_castSucc, hc0]
      linarith [hgap k']
  have hcuts : IsCutSequence (mollifierFamily ε p) c := by
    refine ⟨Fin.strictMono_iff_lt_succ.2 fun k => ?_, fun i u hu => ?_⟩
    · rw [hc0]
      linarith [hcs k]
    · have h := tsupport_shiftedMollifier_subset hj hε (p i) hu
      have h3 : dist (u 3) (p i 3) ≤ ε := (dist_le_pi_dist u (p i) 3).trans h
      rw [Real.dist_eq, abs_le] at h3
      have h4 := hcs i
      have h5 := hc0 i
      simp only [timeCoord] at h4 h5
      constructor <;> linarith [h3.1, h3.2]
  exact ⟨⟨fun i => shiftedMollifier_mem_c1CompactSupp hj hε (p i),
    pairwise_disjoint_tsupport_of_isCutSequence hcuts⟩, c, hcuts⟩
theorem integral_tensorProd_mollifierFamily (hj : IsStandardMollifier stdMollifier) (hε : 0 < ε)
    {n : ℕ} (p : PointTuple n) : ∫ u, tensorProd (mollifierFamily ε p) u = 1 := by
  simp only [tensorProd, mollifierFamily]
  rw [integral_fintype_prod_volume_eq_prod (𝕜 := ℝ) (fun i u => shiftedMollifier ε (p i) u)]
  simp [integral_shiftedMollifier hj hε]
theorem tendsto_integral_mollifierFamily (hj : IsStandardMollifier stdMollifier) {m : ℕ}
    {V : Set (PointTuple (m + 1))} (hV : IsOpen V) {s : PointTuple (m + 1) → ℂ}
    (hs : ContinuousOn s V) {p : PointTuple (m + 1)} (hp : p ∈ V) :
    Tendsto (fun ε => ∫ u, V.indicator (fun y => tensorProdComplex (mollifierFamily ε p) y * s y) u)
      (𝓝[>] 0) (𝓝 (s p)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ₁, hδ₁, hb⟩ := Metric.isOpen_iff.1 hV p hp
  obtain ⟨δ₂, hδ₂, hc⟩ := Metric.continuousAt_iff.1 (hs.continuousAt (hV.mem_nhds hp)) (η / 2)
    (half_pos hη)
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ₁ hδ₂)] with ε hε
  have hε0 : 0 < ε := hε.1
  have hεδ₁ : ε < δ₁ := hε.2.trans_le (min_le_left _ _)
  have hεδ₂ : ε < δ₂ := hε.2.trans_le (min_le_right _ _)
  set φ : PointTuple (m + 1) → ℝ := tensorProd (mollifierFamily ε p) with hφ
  have hφ0 : ∀ u, 0 ≤ φ u := fun u =>
    Finset.prod_nonneg fun i _ => shiftedMollifier_nonneg hj hε0 _ _
  have hφ1 : ∫ u, φ u = 1 := integral_tensorProd_mollifierFamily hj hε0 p
  have hφc : Continuous φ := continuous_finsetProd _ fun i _ =>
    (contDiff_shiftedMollifier hj (p i)).continuous.comp (continuous_apply i)
  have hφs : ∀ u, φ u ≠ 0 → u ∈ Metric.closedBall p ε := fun u hu =>
    (dist_pi_le_iff hε0.le).2 fun i =>
      dist_le_of_shiftedMollifier_ne_zero hj hε0 (Finset.prod_ne_zero_iff.1 hu i (Finset.mem_univ i))
  have hφ00 : ∀ u, u ∉ Metric.closedBall p ε → φ u = 0 := fun u hu => by
    by_contra h
    exact hu (hφs u h)
  have hball : Metric.closedBall p ε ⊆ V := fun u hu =>
    hb (Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hu) hεδ₁))
  have hφi : Integrable φ :=
    hφc.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall p ε) hφ00)
  set F : PointTuple (m + 1) → ℂ :=
    V.indicator fun y => tensorProdComplex (mollifierFamily ε p) y * s y with hFdef
  have hFv : ∀ u ∈ V, F u = (φ u : ℂ) * s u := fun u hu => by
    rw [hFdef, Set.indicator_of_mem hu]
    rfl
  have hF0 : ∀ u, u ∉ Metric.closedBall p ε → F u = 0 := fun u hu => by
    by_cases huV : u ∈ V
    · rw [hFv u huV, hφ00 u hu]
      simp
    · rw [hFdef, Set.indicator_of_notMem huV]
  have hFi : Integrable F := by
    have hon : IntegrableOn F (Metric.closedBall p ε) := by
      have hcont : ContinuousOn F (Metric.closedBall p ε) := by
        have h1 : ContinuousOn (fun u => (φ u : ℂ) * s u) (Metric.closedBall p ε) :=
          (Complex.continuous_ofReal.comp hφc).continuousOn.mul (hs.mono hball)
        exact h1.congr fun u hu => hFv u (hball hu)
      exact hcont.integrableOn_compact (isCompact_closedBall p ε)
    exact (integrableOn_iff_integrable_of_support_subset fun u hu => by
      by_contra h
      exact hu (hF0 u h)).1 hon
  have hφC : Integrable fun u => (φ u : ℂ) * s p := hφi.ofReal.mul_const _
  have hcst : ∫ u, (φ u : ℂ) * s p = s p := by
    rw [integral_mul_const, integral_complex_ofReal, hφ1]
    simp
  have hdiff : (∫ u, F u) - s p = ∫ u, (F u - (φ u : ℂ) * s p) := by
    rw [integral_sub hFi hφC, hcst]
  have hbound : ∀ u, ‖F u - (φ u : ℂ) * s p‖ ≤ φ u * (η / 2) := by
    intro u
    by_cases hu : u ∈ Metric.closedBall p ε
    · rw [hFv u (hball hu), ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hφ0 u)]
      refine mul_le_mul_of_nonneg_left ?_ (hφ0 u)
      have h := hc (lt_of_le_of_lt (Metric.mem_closedBall.1 hu) hεδ₂)
      rw [dist_eq_norm] at h
      exact h.le
    · rw [hF0 u hu, hφ00 u hu]
      simp
  have hfin := norm_integral_le_of_norm_le (hφi.mul_const (η / 2)) (ae_of_all _ hbound)
  rw [integral_mul_const, hφ1, one_mul] at hfin
  rw [dist_eq_norm, hdiff]
  linarith
end Mollifiers
section Euclidean
variable {σ : TestSpaces.SepTuple → ℝ} {E : FourBorelSet → BddOp (StateSpace σ)}
  {A : ℝ → BddOp (StateSpace σ)}
theorem eventually_four_mul_lt_timeGap {m : ℕ} {p : PointTuple (m + 1)}
    (hp : p ∈ increasingTimes (m + 1)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ k : Fin m, 4 * ε < timeCoord p k.succ - timeCoord p k.castSucc := by
  rw [Filter.eventually_all]
  intro k
  have h : 0 < timeCoord p k.succ - timeCoord p k.castSucc := sub_pos.2 (hp Fin.castSucc_lt_succ)
  filter_upwards [Ioo_mem_nhdsGT (div_pos h (by norm_num : (0 : ℝ) < 4))] with ε hε
  linarith [hε.2]
theorem eq_of_rotatePermute (hj : IsStandardMollifier stdMollifier)
    (hsym : IsPermutationInvariant σ) (hinv : ∀ r : RigidMotion, IsMotionInvariant σ r)
    {m : ℕ} {ε : ℝ} {x : PointTuple (m + 1)} (R : Matrix.orthogonalGroup (Fin 4) ℝ)
    (ς : Equiv.Perm (Fin (m + 1))) (X Y : SepTupleOfCard (m + 1))
    (hX : X.1 = mollifierFamily ε x) (hY : Y.1 = mollifierFamily ε (rotatePermute R ς x)) :
    σ ⟨m + 1, Y⟩ = σ ⟨m + 1, X⟩ := by
  set r : RigidMotion := ⟨R.1, R.2, 0⟩ with hr
  set RX : SepTupleOfCard (m + 1) := (UpperHalfTensors.actOnSTuple r ⟨m + 1, X⟩).2 with hRX
  have hYe : Y = permuteComponents RX ς := by
    refine Subtype.ext (funext fun i => funext fun u => ?_)
    have hu : R.1.mulVec (r.invFun u) = u := by
      have h := r.toFun_invFun u
      simpa [RigidMotion.toFun, hr] using h
    change Y.1 i u = X.1 (ς i) (r.invFun u)
    rw [hX, hY]
    change shiftedMollifier ε (R.1.mulVec (x (ς i))) u = shiftedMollifier ε (x (ς i)) (r.invFun u)
    rw [← shiftedMollifier_mulVec hj R.2 (x (ς i)) (r.invFun u), hu]
  rw [hYe, hsym (m + 1) (Nat.succ_pos m) RX ς]
  exact hinv r ⟨m + 1, X⟩
theorem isEuclidean_of_hypotheses (hW : HilbertWellDefined.WellDefinedStatement)
    (hC : FormCompletion.FormCompletionIsHilbertSpace) (hj : IsStandardMollifier stdMollifier)
    (hp : PairingPosSemidef σ) (hsym : IsPermutationInvariant σ)
    (hinv : ∀ r : RigidMotion, IsMotionInvariant σ r)
    (hv : StatesTranslateInner E (vacuumState σ) A)
    (hd : FieldProductHolomorphic E A) (hwr : HasTimeOrderedIntegral σ E A) :
    IsEuclidean E (vacuumState σ) A := by
  intro m x hx R ς hy
  have hs := continuousOn_orderedSchwinger (Ω := vacuumState σ) hd m
  have hO := isOpen_increasingTimes (m + 1)
  refine tendsto_nhds_unique_of_eventuallyEq (tendsto_integral_mollifierFamily hj hO hs hy)
    (tendsto_integral_mollifierFamily hj hO hs hx) ?_
  filter_upwards [eventually_four_mul_lt_timeGap hx, eventually_four_mul_lt_timeGap hy,
    self_mem_nhdsWithin] with ε h₁ h₂ hε
  have hTx := isTimeOrdered_mollifierFamily hj hε h₁
  have hTy := isTimeOrdered_mollifierFamily hj hε h₂
  have hrx := eq_orderedIntegral hW hC hp hinv hv hwr m ⟨_, hTx.1⟩ hTx
  have hry := eq_orderedIntegral hW hC hp hinv hv hwr m ⟨_, hTy.1⟩ hTy
  have hσ := eq_of_rotatePermute hj hsym hinv R ς ⟨_, hTx.1⟩ ⟨_, hTy.1⟩ rfl rfl
  rw [hσ, hrx] at hry
  exact hry.symm
end Euclidean
theorem representsOfTimeOrdered_holds (hW : HilbertWellDefined.WellDefinedStatement)
    (hC : FormCompletion.FormCompletionIsHilbertSpace)
    (ht : WightmanReconstruction.SmoothToolkit.Toolkit)
    (hP : FieldForms.FieldProductProperties)
    (hS : FieldForms.EuclideanSchwingerProperties) : InsertedFieldForm.RepresentsOfTimeOrdered := by
  intro σ E p C hcond A ℘ C' hF hwr
  have hprod := hP _ E (vacuumState σ) A ℘ C' hF
  have hv : StatesTranslateInner E (vacuumState σ) A := hprod.2.2.2.2.2.2.2.2.2.1
  have hd : FieldProductHolomorphic E A := hprod.2.2.2.2.2.2.1
  have hj : IsStandardMollifier stdMollifier := isStandardMollifier_stdMollifier ht.1
  have hsym := hcond.symmInvariant.1
  have hinv := hcond.symmInvariant.2
  have hrep : RepresentsFunctional E (vacuumState σ) A σ :=
    ⟨hcond.isSepFunctional, fun m X hT =>
      eq_orderedIntegral hW hC hcond.posSemidef hinv hv hwr m X hT⟩
  have hE := isEuclidean_of_hypotheses hW hC hj hcond.posSemidef hsym hinv hv hd hwr
  exact ⟨hrep, hE, fun m X =>
    (hS _ E (vacuumState σ) A ℘ C' hF hE m).2.2.2.2 σ hrep hsym (fun R => hinv ⟨R.1, R.2, 0⟩) X⟩
end YangMills.Construction.RepresentsEuclideanProof
end
