import YangMills.Construction.SpectralTheory.BoundedOperatorsOfTheEarlierSettings
import YangMills.Construction.SpectralTheory.CommutingBoundedOperatorsOfTheEarlierSettings
import YangMills.Construction.SpectralTheory.EverySelfAdjointOperatorIsResolved
import YangMills.Construction.SpectralTheory.MarginalsOfSpectralMeasure
import YangMills.Construction.SpectralTheory.SpectralMeasurePushforwardTheorem
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace ComplexOrder
noncomputable section
namespace YangMills.Construction.SettingsComparison.CommutingBoundedProof
open BorelSpectral
open HilbertSpaceBasics (UnboundedOp ofBounded)
open JointSpectral (IsCommutingInBox IsJointRepresentation closedBox coordFn)
open SpectralTheorem (IsSpectralIntegralOf spectralIntegralOp spectralMeasure)
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem isPositive_of_re_inner_nonneg {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (hre : ∀ v, 0 ≤ (⟪T v, v⟫_ℂ).re) : T.IsPositive := by
  refine (ContinuousLinearMap.isPositive_iff' T).2 ⟨hT, fun v => ?_⟩
  have hsymm : ⟪T v, v⟫_ℂ = ⟪v, T v⟫_ℂ :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT v v
  have him : (⟪T v, v⟫_ℂ).im = 0 := by
    have hconj := inner_conj_symm (𝕜 := ℂ) (T v) v
    rw [← hsymm] at hconj
    exact Complex.conj_eq_iff_im.1 hconj
  exact Complex.le_def.2 ⟨by simpa using hre v, by simpa using him.symm⟩
omit [CompleteSpace H] in
theorem abs_re_inner_le_opNorm_mul_sq (A : H →L[ℂ] H) (v : H) :
    |(⟪A v, v⟫_ℂ).re| ≤ ‖A‖ * ‖v‖ ^ 2 := by
  calc |(⟪A v, v⟫_ℂ).re| ≤ ‖⟪A v, v⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖A v‖ * ‖v‖ := norm_inner_le_norm _ _
    _ ≤ ‖A‖ * ‖v‖ * ‖v‖ := by gcongr; exact A.le_opNorm v
    _ = ‖A‖ * ‖v‖ ^ 2 := by ring
omit [CompleteSpace H] in
theorem re_inner_real_smul_one (t : ℝ) (v : H) :
    (⟪(((t : ℝ) : ℂ) • (1 : H →L[ℂ] H)) v, v⟫_ℂ).re = t * ‖v‖ ^ 2 := by
  simp [inner_self_eq_norm_sq_to_K]
  norm_cast
  exact Or.inl rfl
theorem isSelfAdjoint_real_smul_one (t : ℝ) :
    IsSelfAdjoint (((t : ℝ) : ℂ) • (1 : H →L[ℂ] H)) := by
  rw [_root_.isSelfAdjoint_iff, star_smul, star_one]
  simp
theorem neg_opNorm_succ_le_and_le_opNorm_succ {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
    (((-(‖A‖ + 1) : ℝ) : ℂ) • (1 : H →L[ℂ] H)) ≤ A ∧
      A ≤ (((‖A‖ + 1 : ℝ) : ℂ) • (1 : H →L[ℂ] H)) := by
  constructor
  · rw [ContinuousLinearMap.le_def]
    refine isPositive_of_re_inner_nonneg (hA.sub (isSelfAdjoint_real_smul_one _)) fun v => ?_
    have habs := abs_le.1 (abs_re_inner_le_opNorm_mul_sq A v)
    have hsm := re_inner_real_smul_one (H := H) (-(‖A‖ + 1)) v
    rw [sub_apply, inner_sub_left, Complex.sub_re, hsm]
    nlinarith [habs.1, sq_nonneg ‖v‖]
  · rw [ContinuousLinearMap.le_def]
    refine isPositive_of_re_inner_nonneg ((isSelfAdjoint_real_smul_one _).sub hA) fun v => ?_
    have habs := abs_le.1 (abs_re_inner_le_opNorm_mul_sq A v)
    have hsm := re_inner_real_smul_one (H := H) (‖A‖ + 1) v
    rw [sub_apply, inner_sub_left, Complex.sub_re, hsm]
    nlinarith [habs.2, sq_nonneg ‖v‖]
theorem spectralIntegralOp_eq_of_isSpectralIntegralOf {n : ℕ} {S : Set (Fin n → ℝ)}
    {E : SpectralMeasure S H} {f : S → ℂ} {T : UnboundedOp H}
    (hT : IsSpectralIntegralOf T E f) : spectralIntegralOp E f = T := by
  have hspec : IsSpectralIntegralOf (spectralIntegralOp E f) E f :=
    Classical.epsilon_spec (p := fun T => IsSpectralIntegralOf T E f) ⟨T, hT⟩
  refine LinearPMap.ext ?_ ?_
  · ext φ
    exact (hspec.1 φ).trans (hT.1 φ).symm
  · intro u hu hu'
    exact (hspec.2 ⟨u, hu⟩).trans (hT.2 ⟨u, hu'⟩).symm
theorem isSpectralIntegralOf_coordFn_extendCarrier
    (hPush : BorelCalculus.SpectralPushforwardTheorem) {m : ℕ}
    {S : Set (Fin m → ℝ)} (P : SpectralMeasure S H) (T : H →L[ℂ] H) (i : Fin m) (b : ℝ)
    (hb : ∀ s : S, ‖coordFn i s‖ ≤ b) (hT : T = P.integralOp (coordFn i)) :
    IsSpectralIntegralOf (ofBounded T) (P.extendCarrier (subset_univ _) MeasurableSet.univ)
      (coordFn i) := by
  have hmeas : Measurable (coordFn (Y := (univ : Set (Fin m → ℝ))) i) := by
    unfold coordFn
    exact Complex.measurable_ofReal.comp ((measurable_pi_apply i).comp measurable_subtype_coe)
  obtain ⟨hdom, hval⟩ := (hPush H m S P).integral_pushforward P.one_le_dimension
    MeasurableSet.univ (inclusion (subset_univ S)) (measurable_subtype_coe.subtype_mk)
    (coordFn i) hmeas
  have hcomp : coordFn (Y := (univ : Set (Fin m → ℝ))) i ∘ inclusion (subset_univ S) =
      coordFn i := rfl
  rw [hcomp] at hdom hval
  have hall := P.integralDom_eq_univ hb
  refine ⟨fun φ => ?_, fun φ => ?_⟩
  · have hmem : φ ∈ (P.extendCarrier (subset_univ _) MeasurableSet.univ).integralDom
        (coordFn i) := by
      change φ ∈ (P.pushforward P.one_le_dimension MeasurableSet.univ (inclusion (subset_univ S))
        (measurable_subtype_coe.subtype_mk)).integralDom (coordFn i)
      rw [hdom, hall]
      exact mem_univ φ
    exact ⟨fun _ => hmem, fun _ => Submodule.mem_top⟩
  · have heq := hval (φ : H) (by rw [hall]; exact mem_univ _)
    refine Eq.trans ?_ heq.symm
    rw [P.integralApply_eq_integralOp hb, ← hT]
    rfl
theorem commutingBoundedOpsAgreeForAllSpaces_holds
    (hBd : SettingsComparison.BoundedOpsAgreeForAllSpaces)
    (hDiag : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hJoint : JointSpectral.JointSpectralTheorem)
    (hPush : BorelCalculus.SpectralPushforwardTheorem)
    (hMarg : BorelCalculus.MarginalsHold) :
    SettingsComparison.CommutingBoundedOpsAgreeForAllSpaces := by
  intro H _ _ _
  have hsc : ∀ {m : ℕ}, 1 ≤ m → ∀ A : Fin m → H →L[ℂ] H,
      (∀ i, OperatorTransport.IsSelfAdjointCLM (A i)) →
      (∀ i j, Commute (A i) (A j)) →
        ∀ i j, ResolvedOps.StronglyCommute (ofBounded (A i)) (ofBounded (A j)) :=
    fun _ A hA hcomm i j => (hDiag.1 H).2.1 (A i) (A j) (hA i) (hA j) (hcomm i j)
  refine { stronglyCommute := hsc, jointSpectralMeasure_eq := ?_ }
  intro m hm A hA hcomm
  have hsa : ∀ i, IsSelfAdjoint (A i) :=
    fun i => ((hBd H).isSelfAdjointCLM_iff (A i)).1 (hA i)
  have hlt := JointSpectral.normBoundLower_lt_normBoundUpper A
  have hinbox : IsCommutingInBox A (JointSpectral.normBoundLower A)
      (JointSpectral.normBoundUpper A) :=
    ⟨hsa, hcomm, hlt, fun i => (neg_opNorm_succ_le_and_le_opNorm_succ (hsa i)).1,
      fun i => (neg_opNorm_succ_le_and_le_opNorm_succ (hsa i)).2⟩
  have hrep : IsJointRepresentation (JointSpectral.jointMeasureOnBox hm A _ _ hlt) A :=
    ((hJoint H m hm).1 A _ _ hinbox).2.1
  have hmarg : ∀ i, spectralMeasure (ofBounded (A i)) =
      (JointSpectral.jointMeasureOnSpace hm A).coordMarginal i := by
    intro i
    have hmeas : Measurable fun s : (univ : Set (Fin m → ℝ)) => s.1 i :=
      (measurable_pi_apply i).comp measurable_subtype_coe
    have hbound : ∀ s : closedBox (JointSpectral.normBoundLower A)
        (JointSpectral.normBoundUpper A), ‖coordFn i s‖ ≤ ‖A i‖ + 1 := by
      intro s
      have hs := s.2 i (mem_univ i)
      have hlo : -(‖A i‖ + 1) ≤ s.1 i := hs.1
      have hhi : s.1 i ≤ ‖A i‖ + 1 := hs.2
      simpa [coordFn] using abs_le.2 ⟨hlo, hhi⟩
    have hint := isSpectralIntegralOf_coordFn_extendCarrier hPush
      (JointSpectral.jointMeasureOnBox hm A _ _ hlt) (A i) i _ hbound (hrep i)
    have hop : ResolvedFacts.realSpectralIntegral
        (JointSpectral.jointMeasureOnSpace hm A) (fun s => s.1 i) = ofBounded (A i) :=
      spectralIntegralOp_eq_of_isSpectralIntegralOf hint
    have hfacts := ((hDiag.2.1 H).2.2.2.2.2.1 m univ (JointSpectral.jointMeasureOnSpace hm A)
      univ_nonempty).1 _ hmeas
    have hgoal := hfacts.2.1
    rw [hop] at hgoal
    exact hgoal
  have hdiag : ∀ i, ResolvedOps.IsDiagonalized (ofBounded (A i)) :=
    fun i => ((hDiag.1 H).1 (A i) (hA i)).1
  obtain ⟨⟨E, -, huniq⟩, hjointE, -⟩ := (hDiag.2.2 H).1 m hm (fun i => ofBounded (A i)) hdiag
    (fun i j _ => hsc hm A hA hcomm i j)
  have hP : ResolvedOps.IsJointSpectralMeasure (fun i => ofBounded (A i))
      (JointSpectral.jointMeasureOnSpace hm A) := by
    intro D
    have hfun : (fun i => spectralMeasure (ofBounded (A i)) (realLineSet (D i))) =
        fun i => (JointSpectral.jointMeasureOnSpace hm A).coordMarginal i (realLineSet (D i)) :=
      funext fun i => by rw [hmarg i]
    rw [hfun]
    exact (hMarg H m (JointSpectral.jointMeasureOnSpace hm A)).apply_boxProduct D
  exact (huniq _ hjointE).trans (huniq _ hP).symm
end YangMills.Construction.SettingsComparison.CommutingBoundedProof
