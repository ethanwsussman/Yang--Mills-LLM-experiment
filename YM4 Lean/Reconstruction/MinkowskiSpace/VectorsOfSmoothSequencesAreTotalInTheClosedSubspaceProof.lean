import YangMills.Construction.Continuum.CompactSupportAndTensorsOfSeparatedTuples
import YangMills.Construction.Continuum.ChosenSmoothFunctionsPartitionsOfUnityRotationsAndIntegrability
import YangMills.Construction.HilbertSpaces.CompletionsAdjointsAndWeakIntegralsAreWellDefined
import Reconstruction.MinkowskiSpace.VectorsAtRealPointsOfABoundedFieldForm
import Reconstruction.MinkowskiSpace.VectorsOfSmoothSequencesAreTotalInTheClosedSubspace
import Reconstruction.MinkowskiSpace.VectorsOfSmoothSequencesLieInTheClosedSubspace
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.MinkowskiSpace.SmoothSeqTotal
theorem mem_schwartzFlatOffPosTime (hC : ConfigSpace.CompactSupportTensorFacts) {q : ℕ}
    {φ : TestSpaces.PointTuple (q + 1) → ℂ}
    (hφ : φ ∈ TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes (q + 1))) :
    φ ∈ ConfigSpace.schwartzFlatOffPosTime (q + 1) := by
  refine (hC (q + 1) (Nat.succ_pos q)).2.2.1 ⟨ConfigSpace.isOpen_posTimeSet, hφ.1, hφ.2.1, ?_⟩
  exact hφ.2.2.trans (TestSpaces.increasingPositiveTimes_subset_positiveTimeLocus (q + 1))
theorem zero_mem_smoothCompactSupp (q : ℕ) :
    (fun _ => 0 : TestSpaces.PointTuple (q + 1) → ℂ) ∈
      TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes (q + 1)) := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · exact HasCompactSupport.zero
  · have hempty : tsupport (fun _ => 0 : TestSpaces.PointTuple (q + 1) → ℂ) = ∅ := tsupport_zero
    rw [hempty]
    exact Set.empty_subset _
def singleMembers (hC : ConfigSpace.CompactSupportTensorFacts) (c : ℂ) (q : ℕ)
    (φ : TestSpaces.PointTuple (q + 1) → ℂ)
    (hφ : φ ∈ ConfigSpace.schwartzFlatOffPosTime (q + 1)) : ConfigSpace.PosTimeSeq
  | 0 => ⟨c, Set.mem_univ _⟩
  | k + 1 =>
    if h : k = q then by subst h; exact ⟨φ, hφ⟩
    else ⟨fun _ => 0, mem_schwartzFlatOffPosTime hC (zero_mem_smoothCompactSupp k)⟩
def singleSeq (hC : ConfigSpace.CompactSupportTensorFacts) (c : ℂ) (q : ℕ)
    (φ : TestSpaces.PointTuple (q + 1) → ℂ)
    (hφ : φ ∈ ConfigSpace.schwartzFlatOffPosTime (q + 1)) : ConfigSpace.AdmissibleSeq :=
  ⟨singleMembers hC c q φ hφ, by
    refine Set.Finite.subset (Set.finite_Iic (q + 1)) fun k hk => ?_
    by_contra hlt
    apply hk
    cases k with
    | zero => simp at hlt
    | succ j =>
      have hj : j ≠ q := by
        intro h
        apply hlt
        simp [h]
      show (singleMembers hC c q φ hφ (j + 1)).1 = _
      rw [singleMembers, dif_neg hj]
      rfl⟩
theorem succMember_singleSeq_self (hC : ConfigSpace.CompactSupportTensorFacts) (c : ℂ)
    (q : ℕ) (φ : TestSpaces.PointTuple (q + 1) → ℂ)
    (hφ : φ ∈ ConfigSpace.schwartzFlatOffPosTime (q + 1)) :
    FormReconstruction.succMember (singleSeq hC c q φ hφ) q = φ := by
  show (singleMembers hC c q φ hφ (q + 1)).1 = φ
  rw [singleMembers, dif_pos rfl]
theorem succMember_singleSeq_of_ne (hC : ConfigSpace.CompactSupportTensorFacts) (c : ℂ)
    (q : ℕ) (φ : TestSpaces.PointTuple (q + 1) → ℂ)
    (hφ : φ ∈ ConfigSpace.schwartzFlatOffPosTime (q + 1)) {k : ℕ} (hk : k ≠ q) :
    FormReconstruction.succMember (singleSeq hC c q φ hφ) k = fun _ => 0 := by
  show (singleMembers hC c q φ hφ (k + 1)).1 = _
  rw [singleMembers, dif_neg hk]
theorem zerothScalar_singleSeq (hC : ConfigSpace.CompactSupportTensorFacts)
    (c : ℂ) (q : ℕ) (φ : TestSpaces.PointTuple (q + 1) → ℂ)
    (hφ : φ ∈ ConfigSpace.schwartzFlatOffPosTime (q + 1)) :
    FormReconstruction.zerothScalar (singleSeq hC c q φ hφ) = c :=
  rfl
theorem isSmoothPositiveTimeSeq_singleSeq (hC : ConfigSpace.CompactSupportTensorFacts) (c : ℂ)
    (q : ℕ) {φ : TestSpaces.PointTuple (q + 1) → ℂ}
    (hφ : φ ∈ TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes (q + 1))) :
    FormReconstruction.IsSmoothPositiveTimeSeq
      (singleSeq hC c q φ (mem_schwartzFlatOffPosTime hC hφ)) := by
  intro k
  by_cases hk : k = q
  · subst hk
    rw [succMember_singleSeq_self]
    exact hφ
  · rw [succMember_singleSeq_of_ne hC c q φ _ hk]
    exact zero_mem_smoothCompactSupp k
section States
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
theorem weakInt_zero_fun {P : Type} [TopologicalSpace P] [MeasureSpace P] (D : Set P)
    (Ξ : P → K) : ProjectionMeasures.weakInt D Ξ (fun _ => 0) = 0 := by
  have h0 : ProjectionMeasures.HasWeakIntegral D Ξ (fun _ => (0 : ℂ)) (0 : K) := by
    intro χ
    simp
  have hspec := Classical.epsilon_spec
    (p := ProjectionMeasures.HasWeakIntegral D Ξ (fun _ => (0 : ℂ))) ⟨_, h0⟩
  have h1 := hspec (ProjectionMeasures.weakInt D Ξ fun _ => 0)
  simp only [zero_mul, integral_zero] at h1
  exact inner_self_eq_zero.mp h1
variable (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp K) (Ω : K)
  (A : ℝ → OneLoopNotation.BddOp K)
theorem smoothSeqState_singleSeq (hC : ConfigSpace.CompactSupportTensorFacts) (c : ℂ)
    (q : ℕ) (φ : TestSpaces.PointTuple (q + 1) → ℂ)
    (hφ : φ ∈ ConfigSpace.schwartzFlatOffPosTime (q + 1)) :
    FormReconstruction.smoothSeqState E Ω A (singleSeq hC c q φ hφ) =
      c • Ω + ProjectionMeasures.weakInt (tsupport φ)
        (FormReconstruction.wickStateAt E Ω A q) φ := by
  unfold FormReconstruction.smoothSeqState
  rw [zerothScalar_singleSeq, finsum_eq_single _ q, succMember_singleSeq_self]
  intro k hk
  rw [succMember_singleSeq_of_ne hC c q φ hφ hk]
  exact weakInt_zero_fun _ _
end States
theorem smoothSeqStatesTotal_holds
    (hT : WightmanReconstruction.SmoothToolkit.Toolkit)
    (hC : ConfigSpace.CompactSupportTensorFacts)
    (hW : HilbertWellDefined.WellDefinedStatement)
    (hV : RealPointVectors.BoundaryVectorsStatement)
    (hS : MinkowskiSpace.SmoothSeqStateMemTensorHilbert) : MinkowskiSpace.SmoothSeqStatesTotal := by
  intro K _ _ _ E Ω A ℘ C hform χ hχ horth
  have hzero := zero_mem_smoothCompactSupp 0
  have hΩ : ⟪χ, Ω⟫_ℂ = 0 := by
    have h := horth _ (isSmoothPositiveTimeSeq_singleSeq hC 1 0 hzero)
    rw [smoothSeqState_singleSeq, weakInt_zero_fun, add_zero, one_smul] at h
    exact h
  have hdata : ∀ (q : ℕ) {φ : TestSpaces.PointTuple (q + 1) → ℂ},
      φ ∈ TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes (q + 1)) →
      ProjectionMeasures.HasWeakIntegrandData (tsupport φ)
        (FormReconstruction.wickStateAt E Ω A q) φ := by
    intro q φ hφ
    have h := (hS E Ω A ℘ C hform _ (isSmoothPositiveTimeSeq_singleSeq hC 0 q hφ)).1 q
    rwa [succMember_singleSeq_self] at h
  have hint : ∀ (q : ℕ) {φ : TestSpaces.PointTuple (q + 1) → ℂ},
      φ ∈ TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes (q + 1)) →
      ∫ x in tsupport φ, φ x * ⟪χ, FormReconstruction.wickStateAt E Ω A q x⟫_ℂ = 0 := by
    intro q φ hφ
    have h := horth _ (isSmoothPositiveTimeSeq_singleSeq hC 0 q hφ)
    rw [smoothSeqState_singleSeq, zero_smul, zero_add] at h
    rw [← (hW.2.2.2 K (TestSpaces.PointTuple (q + 1)) _ _ _ (hdata q hφ)).1 χ]
    exact h
  have hcont : ∀ q : ℕ,
      ContinuousOn (fun x => ⟪χ, FormReconstruction.wickStateAt E Ω A q x⟫_ℂ)
        (TestSpaces.increasingPositiveTimes (q + 1)) := by
    intro q x hx
    have hU := (TestSpaces.isOpen_increasingPositiveTimes (q + 1)).mem_nhds hx
    obtain ⟨f, hfs, hfc, hfd, -, hf1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hU
    have hφ : (fun y => (f y : ℂ)) ∈
        TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes (q + 1)) := by
      have hts : tsupport (fun y => (f y : ℂ)) = tsupport f := by
        unfold tsupport
        congr 1
        ext y
        simp
      refine ⟨Complex.ofRealCLM.contDiff.comp hfd, ?_, ?_⟩
      · show IsCompact (tsupport _)
        rw [hts]
        exact hfc
      · rw [hts]
        exact hfs
    have hc := (hdata q hφ).continuousOn_inner χ
    have hnhds : tsupport (fun y => (f y : ℂ)) ∈ 𝓝 x := by
      refine Filter.mem_of_superset ?_ (subset_tsupport _)
      have hopen : IsOpen (Function.support fun y => (f y : ℂ)) :=
        (Complex.continuous_ofReal.comp hfd.continuous).isOpen_support
      refine hopen.mem_nhds ?_
      simp [hf1]
    exact ((hc x (mem_of_mem_nhds hnhds)).continuousAt hnhds).continuousWithinAt
  have hvan : ∀ (q : ℕ), ∀ x ∈ TestSpaces.increasingPositiveTimes (q + 1),
      ⟪χ, FormReconstruction.wickStateAt E Ω A q x⟫_ℂ = 0 := by
    intro q
    refine hT.2.2.2.2.1 (q + 1) (Nat.succ_pos q) _ _
      (TestSpaces.isOpen_increasingPositiveTimes (q + 1)) (hcont q) fun h hh => ?_
    have hts : tsupport (fun y => (h y : ℂ)) = tsupport h := by
      unfold tsupport
      congr 1
      ext y
      simp
    have hφ : (fun y => (h y : ℂ)) ∈
        TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes (q + 1)) := by
      refine ⟨Complex.ofRealCLM.contDiff.comp hh.1, ?_, ?_⟩
      · show IsCompact (tsupport _)
        rw [hts]
        exact hh.2.1
      · rw [hts]
        exact hh.2.2
    rw [← hint q hφ]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    have hx0 : (h x : ℂ) = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => (h y : ℂ)) hx
    rw [hx0, zero_mul]
  have hgen : ∀ v ∈ RealPointVectors.euclideanStates E Ω A, ⟪χ, v⟫_ℂ = 0 := by
    rintro v ⟨n, x, hx, rfl⟩
    cases n with
    | zero => exact hΩ
    | succ q => exact hvan q x hx
  have hspan : ∀ v ∈ Submodule.span ℂ (RealPointVectors.euclideanStates E Ω A),
      ⟪χ, v⟫_ℂ = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact hgen v hv
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_right, ha, mul_zero]
  have hmem : χ ∈ SesquilinearForms.closedLinSpan (RealPointVectors.euclideanStates E Ω A) := by
    rw [← (hV E Ω A ℘ C hform).tensorDomainClosure_eq, ← FieldFormHilbert.coe_tensorHilbert]
    exact hχ
  obtain ⟨u, hu, hlim⟩ := hmem
  have hself : ⟪χ, χ⟫_ℂ = 0 := by
    have h1 : Tendsto (fun n => ⟪χ, u n⟫_ℂ) atTop (𝓝 ⟪χ, χ⟫_ℂ) :=
      (continuous_const.inner continuous_id).continuousAt.tendsto.comp hlim
    have h2 : (fun n => ⟪χ, u n⟫_ℂ) = fun _ => 0 := funext fun n => hspan _ (hu n)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  exact inner_self_eq_zero.mp hself
end YangMills.Construction.MinkowskiSpace.SmoothSeqTotal
end
