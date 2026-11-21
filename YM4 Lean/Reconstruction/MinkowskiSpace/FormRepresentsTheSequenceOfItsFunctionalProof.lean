import Reconstruction.Continuum.OrderedTimes
import YangMills.Construction.Continuum.DistributionsOffTheDiagonalsAndTranslationsInSpaceProof
import Reconstruction.Continuum.TwoApproximationsAtOrderedTimes
import Reconstruction.MinkowskiSpace.FormRepresentsItsFunctionalAndIsEuclideanProof
import Reconstruction.MinkowskiSpace.FormRepresentsTheSequenceOfItsFunctional
import Mathlib
set_option autoImplicit false
open Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.RepresentedSequence
open YangMills.Construction.TestSpaces YangMills.Construction.MinkowskiSpace YangMills.Construction.FieldForms YangMills.Construction.ProjectionMeasures YangMills.Construction.OneLoopNotation YangMills.Construction.WightmanReconstruction YangMills.Construction.WightmanTheory YangMills.Construction.TestSpaces.OrderedApprox YangMills.Construction.TestSpaces.TestSpaceFacts
section Continuity
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem continuousOn_orderedSchwinger {E : FourBorelSet → BddOp H} {Ω : H}
    {A : ℝ → BddOp H} (hd : FieldProductHolomorphic E A) (m : ℕ) :
    ContinuousOn (orderedSchwinger E Ω A m) (increasingTimes (m + 1)) := by apply _root_.YangMills.Construction.MinkowskiSpace.InvariantEuclideanProof.continuousOn_orderedSchwinger <;> assumption
end Continuity
section Support
variable {q : ℕ} {V : Set (PointTuple q)}
theorem linComb_mem_smoothCompactSupp {f g : PointTuple q → ℂ}
    (hf : f ∈ (smoothCompactSupp V : Set (PointTuple q → ℂ)))
    (hg : g ∈ (smoothCompactSupp V : Set (PointTuple q → ℂ))) (a b : ℂ) :
    a • f + b • g ∈ (smoothCompactSupp V : Set (PointTuple q → ℂ)) := by apply _root_.YangMills.Construction.TestSpaces.OffDiagonal.smoothCompactSupp_linComb_mem <;> assumption
theorem zero_mem_smoothCompactSupp :
    (0 : PointTuple q → ℂ) ∈ (smoothCompactSupp V : Set (PointTuple q → ℂ)) := by apply _root_.YangMills.Construction.TestSpaces.OffDiagonal.smoothCompactSupp_zero_mem <;> assumption
theorem increasingTimes_subset_distinctArgs :
    increasingTimes q ⊆ ConfigSpace.distinctArgs q := by apply _root_.YangMills.Construction.TestSpaces.increasingTimes_subset_distinctLocus <;> assumption
theorem mem_schwartzFlatOffDiagonal (hK : ConfigSpace.CompactSupportTensorFacts)
    (hq : 1 ≤ q) {f : PointTuple q → ℂ}
    (hf : f ∈ (smoothCompactSupp (increasingTimes q) : Set (PointTuple q → ℂ))) :
    f ∈ ConfigSpace.schwartzFlatOffDiagonal q :=
  (hK q hq).2.1 ⟨ConfigSpace.isOpen_distinctArgs, hf.1, hf.2.1,
    hf.2.2.trans increasingTimes_subset_distinctArgs⟩
theorem tsupport_tensorProdComplex_subset (g : Fin q → (Fin 4 → ℝ) → ℝ) :
    tsupport (tensorProdComplex g) ⊆ Set.univ.pi fun i => tsupport (g i) := by apply _root_.YangMills.Construction.RepresentsEuclideanProof.tsupport_tensorProdComplex_subset_pi <;> assumption
theorem tensorProdComplex_mem {X : Fin q → (Fin 4 → ℝ) → ℝ}
    (hs : HasSmoothComponents Set.univ X) (hT : IsTimeOrdered X) :
    tensorProdComplex X ∈
      (smoothCompactSupp (increasingTimes q) : Set (PointTuple q → ℂ)) := by
  obtain ⟨-, c, hc⟩ := hT
  refine ⟨?_, ?_, ?_⟩
  · have h : ContDiff ℝ ∞ (tensorProd X) := by
      unfold tensorProd
      exact contDiff_prod fun i _ => (hs i).1.comp (contDiff_apply ℝ (Fin 4 → ℝ) i)
    exact Complex.ofRealCLM.contDiff.comp h
  · exact (isCompact_univ_pi fun i => (hs i).2.1).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_tensorProdComplex_subset X)
  · intro x hx i j hij
    have hx' := tsupport_tensorProdComplex_subset X hx
    have h₁ := (hc.2 i (hx' i (Set.mem_univ i))).2
    have h₂ := (hc.2 j (hx' j (Set.mem_univ j))).1
    have h₃ : c i.succ ≤ c j.castSucc := hc.1.monotone (by
      rw [Fin.le_def]
      simpa using hij)
    exact h₁.trans_le h₃ |>.trans h₂
theorem ofReal_norm_le_weightedSeminorm (k : ℕ) (f : PointTuple q → ℂ) (x : PointTuple q) :
    ENNReal.ofReal ‖f x‖ ≤ weightedSeminorm k f := by
  refine le_iSup_of_le x (le_iSup_of_le (0 : MultiIdx4 q) (le_iSup_of_le ?_ ?_))
  · simp [idxOrder]
  · refine ENNReal.ofReal_le_ofReal ?_
    have e : multiDeriv (0 : MultiIdx4 q) f = f := ConfigSpace.iteratedPartial_zero f
    rw [e]
    have h : (1 : ℝ) ≤ 1 + tupleNorm x ^ 2 := by nlinarith [sq_nonneg (tupleNorm x)]
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_rpow h (by positivity))
end Support
section Integral
variable {q : ℕ} {V : Set (PointTuple q)} {s : PointTuple q → ℂ}
theorem indicator_mul_eq {f : PointTuple q → ℂ} {D : Set (PointTuple q)} (hD : tsupport f ⊆ D)
    (hV : D ⊆ V) :
    V.indicator (fun y => f y * s y) = D.indicator fun y => f y * s y := by
  funext y
  by_cases hy : y ∈ D
  · rw [Set.indicator_of_mem (hV hy), Set.indicator_of_mem hy]
  · have h0 : f y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hD h)
    rw [Set.indicator_of_notMem hy]
    by_cases h : y ∈ V
    · simp [Set.indicator_of_mem h, h0]
    · exact Set.indicator_of_notMem h _
theorem integrable_indicator_mul (hs : ContinuousOn s V) {f : PointTuple q → ℂ}
    (hf : f ∈ (smoothCompactSupp V : Set (PointTuple q → ℂ))) :
    Integrable (V.indicator fun y => f y * s y) := by
  have hi : IntegrableOn (fun y => f y * s y) (tsupport f) :=
    (hf.1.continuous.continuousOn.mul (hs.mono hf.2.2)).integrableOn_compact hf.2.1
  rw [indicator_mul_eq subset_rfl hf.2.2,
    integrable_indicator_iff (isClosed_tsupport f).measurableSet]
  exact hi
theorem integral_indicator_linComb (hs : ContinuousOn s V) {f g : PointTuple q → ℂ}
    (hf : f ∈ (smoothCompactSupp V : Set (PointTuple q → ℂ)))
    (hg : g ∈ (smoothCompactSupp V : Set (PointTuple q → ℂ))) (a b : ℂ) :
    ∫ x, V.indicator (fun y => (a • f + b • g) y * s y) x =
      a * (∫ x, V.indicator (fun y => f y * s y) x) +
        b * ∫ x, V.indicator (fun y => g y * s y) x := by
  have e : V.indicator (fun y => (a • f + b • g) y * s y) = fun x =>
      a * V.indicator (fun y => f y * s y) x + b * V.indicator (fun y => g y * s y) x := by
    funext x
    by_cases hx : x ∈ V
    · simp only [Set.indicator_of_mem hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [Set.indicator_of_notMem hx, mul_zero, add_zero]
  rw [e, integral_add ((integrable_indicator_mul hs hf).const_mul a)
    ((integrable_indicator_mul hs hg).const_mul b), integral_const_mul, integral_const_mul]
theorem norm_integral_indicator_le (hs : ContinuousOn s V) {D : Set (PointTuple q)}
    (hD : IsCompact D) (hDV : D ⊆ V) {f : PointTuple q → ℂ} (hf : tsupport f ⊆ D) {ε : ℝ}
    (hε : ∀ x, ‖f x‖ ≤ ε) :
    ‖∫ x, V.indicator (fun y => f y * s y) x‖ ≤
      ε * ∫ x, D.indicator (fun y => ‖s y‖) x := by
  have hi : Integrable (D.indicator fun y => ‖s y‖) := by
    rw [integrable_indicator_iff hD.measurableSet]
    exact (hs.mono hDV).norm.integrableOn_compact hD
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hi.const_mul ε) (ae_of_all _ fun x => ?_)
  rw [indicator_mul_eq hf hDV]
  by_cases hx : x ∈ D
  · simp only [Set.indicator_of_mem hx, norm_mul]
    exact mul_le_mul_of_nonneg_right (hε x) (norm_nonneg _)
  · simp [Set.indicator_of_notMem hx]
end Integral
section Main
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : FourBorelSet → BddOp H} {Ω : H} {A : ℝ → BddOp H}
  {σ : TestSpaces.SepTuple → ℝ} {S : ConfigSpace.FlatSequence}
def OrderedAgreement (E : FourBorelSet → BddOp H) (Ω : H) (A : ℝ → BddOp H)
    (S : ConfigSpace.FlatSequence) (m : ℕ) (f : PointTuple (m + 1) → ℂ) : Prop :=
  f ∈ (smoothCompactSupp (increasingTimes (m + 1)) : Set (PointTuple (m + 1) → ℂ)) ∧
    ∃ h : f ∈ ConfigSpace.schwartzFlatOffDiagonal (m + 1),
      S.atSucc m ⟨f, h⟩ = orderedIntegral E Ω A m f
theorem OrderedAgreement.linComb {m : ℕ} (hK : ConfigSpace.CompactSupportTensorFacts)
    (hs : ContinuousOn (orderedSchwinger E Ω A m) (increasingTimes (m + 1)))
    (hl : ConfigSpace.IsLinearFunctionalSeq S) {f g : PointTuple (m + 1) → ℂ}
    (hf : OrderedAgreement E Ω A S m f) (hg : OrderedAgreement E Ω A S m g) (a b : ℂ) :
    OrderedAgreement E Ω A S m (a • f + b • g) := by
  obtain ⟨h₁, f₁, e⟩ := hf
  obtain ⟨h₁', f₁', e'⟩ := hg
  have hm := linComb_mem_smoothCompactSupp h₁ h₁' a b
  have hfl := mem_schwartzFlatOffDiagonal hK (Nat.succ_pos m) hm
  refine ⟨hm, hfl, ?_⟩
  rw [hl.2 m a b ⟨f, f₁⟩ ⟨g, f₁'⟩ ⟨_, hfl⟩ rfl, e, e']
  exact (integral_indicator_linComb hs h₁ h₁' a b).symm
theorem orderedAgreement_tensor {m : ℕ} (hK : ConfigSpace.CompactSupportTensorFacts)
    (hr : RepresentsFunctional E Ω A σ)
    (hv : ReflectionPositivityFromValues.AgreesOnTensors σ S)
    {X : Fin (m + 1) → (Fin 4 → ℝ) → ℝ} (hX : X ∈ smoothDisjointTuples Set.univ (m + 1))
    (hT : IsTimeOrdered X) : OrderedAgreement E Ω A S m (tensorProdComplex X) := by
  have hm := tensorProdComplex_mem hX.2 hT
  have hfl := mem_schwartzFlatOffDiagonal hK (Nat.succ_pos m) hm
  refine ⟨hm, hfl, ?_⟩
  rw [hv m ⟨X, hX.1⟩ hX.2 hfl]
  exact hr.2 m ⟨X, hX.1⟩ hT
theorem orderedAgreement_zero {m : ℕ} (hK : ConfigSpace.CompactSupportTensorFacts)
    (hl : ConfigSpace.IsLinearFunctionalSeq S) : OrderedAgreement E Ω A S m 0 := by
  have hfl := mem_schwartzFlatOffDiagonal hK (Nat.succ_pos m) zero_mem_smoothCompactSupp
  refine ⟨zero_mem_smoothCompactSupp, hfl, ?_⟩
  rw [hl.2 m 0 0 ⟨0, hfl⟩ ⟨0, hfl⟩ ⟨0, hfl⟩ (by simp)]
  simp [orderedIntegral]
theorem orderedAgreement_tensorCombination {m M : ℕ}
    (hK : ConfigSpace.CompactSupportTensorFacts)
    (hs : ContinuousOn (orderedSchwinger E Ω A m) (increasingTimes (m + 1)))
    (hl : ConfigSpace.IsLinearFunctionalSeq S) (hr : RepresentsFunctional E Ω A σ)
    (hv : ReflectionPositivityFromValues.AgreesOnTensors σ S)
    (c : Fin M → ℂ) (X : Fin M → Fin (m + 1) → (Fin 4 → ℝ) → ℝ)
    (hX : ∀ ι, X ι ∈ smoothDisjointTuples Set.univ (m + 1) ∧ IsTimeOrdered (X ι)) :
    OrderedAgreement E Ω A S m (tensorCombination c X) := by
  have key : ∀ T : Finset (Fin M),
      OrderedAgreement E Ω A S m fun x => ∑ ι ∈ T, c ι * ((tensorProd (X ι) x : ℝ) : ℂ) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have e : (fun x : PointTuple (m + 1) => ∑ ι ∈ (∅ : Finset (Fin M)),
          c ι * ((tensorProd (X ι) x : ℝ) : ℂ)) = 0 := by
        funext x
        simp
      rw [e]
      exact orderedAgreement_zero hK hl
    | insert ι T hι ih =>
      have e : (fun x : PointTuple (m + 1) => ∑ ι' ∈ insert ι T,
          c ι' * ((tensorProd (X ι') x : ℝ) : ℂ)) =
            c ι • tensorProdComplex (X ι) + (1 : ℂ) • fun x =>
              ∑ ι' ∈ T, c ι' * ((tensorProd (X ι') x : ℝ) : ℂ) := by
        funext x
        simp [Finset.sum_insert hι, tensorProdComplex]
      rw [e]
      exact (orderedAgreement_tensor hK hr hv (hX ι).1 (hX ι).2).linComb hK hs hl ih _ _
  exact key Finset.univ
theorem tsupport_sub_subset_union {q : ℕ} (f g : PointTuple q → ℂ) :
    tsupport (f - g) ⊆ tsupport f ∪ tsupport g := by
  refine closure_minimal (fun x hx => ?_) ((isClosed_tsupport _).union (isClosed_tsupport _))
  by_contra hn
  rw [Set.mem_union, not_or] at hn
  have e₁ : f x = 0 := image_eq_zero_of_notMem_tsupport hn.1
  have e₂ : g x = 0 := image_eq_zero_of_notMem_tsupport hn.2
  exact hx (by simp [e₁, e₂])
end Main
theorem represented_sequence_proof (hA : TestSpaces.OrderedApprox.Statement)
    (hP : FieldForms.FieldProductProperties)
    (hK : ConfigSpace.CompactSupportTensorFacts) : Statement := by
  intro H _ _ _ E Ω A P C hb σ S hr hl hc hv
  refine ⟨hl, fun m φ hφ h => ?_⟩
  obtain ⟨-, k, D, hk, hD, hbd⟩ := hc m
  obtain ⟨Cc, hCc, hCV, φs, hφs, hlim⟩ := (hA (m + 1) k (Nat.succ_pos m) hk).2.1 φ hφ
  have hs : ContinuousOn (orderedSchwinger E Ω A m) (increasingTimes (m + 1)) :=
    continuousOn_orderedSchwinger (hP H E Ω A P C hb).2.2.2.2.2.2.1 m
  have hDc : IsCompact (Cc ∪ tsupport φ) := hCc.union hφ.2.1
  have hDV : Cc ∪ tsupport φ ⊆ increasingTimes (m + 1) := Set.union_subset hCV hφ.2.2
  set B : ℝ := ∫ x, (Cc ∪ tsupport φ).indicator
    (fun y => ‖orderedSchwinger E Ω A m y‖) x with hB
  set w : ℕ → ℝ := fun j => (weightedSeminorm k (φ - φs j)).toReal with hwdef
  have hw : Tendsto w atTop (𝓝 0) := by
    have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    rw [ENNReal.toReal_zero] at h0
    exact h0
  have hbound : ∀ j, ‖S.atSucc m ⟨φ, h⟩ - orderedIntegral E Ω A m φ‖ ≤ (D + B) * w j := by
    intro j
    obtain ⟨hsup, M, c, X, hX, hj⟩ := hφs j
    have ag : OrderedAgreement E Ω A S m (φs j) := by
      rw [hj]
      exact orderedAgreement_tensorCombination hK hs hl hr hv c X hX
    obtain ⟨a₁, f₁, e₁⟩ := ag
    have hd : (1 : ℂ) • φ + (-1 : ℂ) • φs j = φ - φs j := by
      simp [sub_eq_add_neg]
    have hdm : φ - φs j ∈ (smoothCompactSupp (increasingTimes (m + 1)) :
        Set (PointTuple (m + 1) → ℂ)) := hd ▸ linComb_mem_smoothCompactSupp hφ a₁ 1 (-1)
    have hdf := mem_schwartzFlatOffDiagonal hK (Nat.succ_pos m) hdm
    have hT : S.atSucc m ⟨φ - φs j, hdf⟩ =
        S.atSucc m ⟨φ, h⟩ - S.atSucc m ⟨φs j, f₁⟩ := by
      rw [hl.2 m 1 (-1) ⟨φ, h⟩ ⟨φs j, f₁⟩ ⟨_, hdf⟩ hd.symm]
      ring
    have hI : orderedIntegral E Ω A m (φ - φs j) =
        orderedIntegral E Ω A m φ - orderedIntegral E Ω A m (φs j) := by
      have h0 := integral_indicator_linComb hs hφ a₁ 1 (-1)
      rw [hd] at h0
      unfold orderedIntegral
      rw [h0]
      ring
    have eq : S.atSucc m ⟨φ, h⟩ - orderedIntegral E Ω A m φ =
        S.atSucc m ⟨φ - φs j, hdf⟩ - orderedIntegral E Ω A m (φ - φs j) := by
      rw [hT, hI, e₁]
      ring
    rw [eq]
    have h1 : ‖S.atSucc m ⟨φ - φs j, hdf⟩‖ ≤ D * w j := hbd ⟨_, hdf⟩
    have hfin : weightedSeminorm k (φ - φs j) ≠ ⊤ := (hdf.1.2 k hk).ne
    have hsup' : ∀ x, ‖(φ - φs j) x‖ ≤ w j := fun x =>
      (ENNReal.ofReal_le_iff_le_toReal hfin).1 (ofReal_norm_le_weightedSeminorm k (φ - φs j) x)
    have hts : tsupport (φ - φs j) ⊆ Cc ∪ tsupport φ :=
      (tsupport_sub_subset_union φ (φs j)).trans
        (Set.union_subset Set.subset_union_right (hsup.trans Set.subset_union_left))
    have h2 := norm_integral_indicator_le hs hDc hDV hts hsup'
    calc _ ≤ ‖S.atSucc m ⟨φ - φs j, hdf⟩‖ + ‖orderedIntegral E Ω A m (φ - φs j)‖ :=
          norm_sub_le _ _
      _ ≤ D * w j + w j * B := add_le_add h1 h2
      _ = (D + B) * w j := by ring
  have hz : ‖S.atSucc m ⟨φ, h⟩ - orderedIntegral E Ω A m φ‖ ≤ 0 :=
    ge_of_tendsto' (by simpa using hw.const_mul (D + B)) hbound
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hz)
end YangMills.Construction.RepresentedSequence
end
