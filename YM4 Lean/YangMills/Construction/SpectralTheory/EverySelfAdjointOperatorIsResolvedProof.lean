import YangMills.Construction.SpectralTheory.EverySelfAdjointOperatorIsResolved
import YangMills.Construction.SpectralTheory.SpectralTheoremForSelfAdjointOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace ComplexOrder
noncomputable section
namespace YangMills.Construction.SelfAdjointResolution
open HilbertSpaceBasics (UnboundedOp IsGE IsContraction IsSelfAdjointOp addConst ofBounded)
open OperatorTransport (IsBoundedAdjoint IsSelfAdjointCLM)
open BorelSpectral
open BorelSpectral.SpectralMeasure (OpCommutes)
open SpectralTheorem
  (IsBoundedInverse IsSpectralIntegralOf IsSpectralMeasureFor RealLineSet spectralIntegralOp coordVar
    spectralMeasure)
open ResolvedOps (StronglyCommute IsDiagonalized)
open JointSpectral (IsCommutingInBox)
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
omit [CompleteSpace H] in
theorem eq_of_inner_eq_on_dense {D : Set H} (hD : Dense D) {x y : H}
    (h : ∀ v ∈ D, ⟪x, v⟫_ℂ = ⟪y, v⟫_ℂ) : x = y := by
  have hcl : IsClosed {v : H | ⟪x, v⟫_ℂ = ⟪y, v⟫_ℂ} :=
    isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
  have hsub : closure D ⊆ {v : H | ⟪x, v⟫_ℂ = ⟪y, v⟫_ℂ} := hcl.closure_subset_iff.2 h
  rw [hD.closure_eq] at hsub
  exact ext_inner_right ℂ fun v => hsub (mem_univ v)
omit [CompleteSpace H] in
theorem isSelfAdjointOp_iff_unbounded (A : UnboundedOp H) :
    IsSelfAdjointOp A ↔ OperatorTransport.IsSelfAdjointUnbounded A := by
  constructor
  · rintro ⟨hd, hdom, hval⟩
    refine ⟨hd, fun φ χ => ⟨?_, fun h => ?_⟩⟩
    · rintro ⟨hφ, rfl⟩ ψ
      exact hval ⟨φ, hφ⟩ ψ
    · have hφ : φ ∈ A.domain := (hdom φ).2 ⟨χ, h⟩
      refine ⟨hφ, eq_of_inner_eq_on_dense hd fun v hv => ?_⟩
      rw [← h ⟨v, hv⟩]
      exact (hval ⟨φ, hφ⟩ ⟨v, hv⟩).symm
  · rintro ⟨hd, h⟩
    refine ⟨hd, fun φ => ⟨fun hφ => ⟨A ⟨φ, hφ⟩, (h φ _).1 ⟨hφ, rfl⟩⟩, ?_⟩,
      fun φ ψ => (h φ _).1 ⟨φ.2, rfl⟩ ψ⟩
    rintro ⟨η, hη⟩
    obtain ⟨hφ, -⟩ := (h φ η).2 hη
    exact hφ
omit [CompleteSpace H] in
theorem isSelfAdjointUnbounded_ofBounded {B : H →L[ℂ] H} (hB : IsSelfAdjointCLM B) :
    OperatorTransport.IsSelfAdjointUnbounded (ofBounded B) := by
  refine ⟨?_, fun φ χ => ⟨?_, fun h => ?_⟩⟩
  · show Dense ((⊤ : Submodule ℂ H) : Set H)
    simp
  · rintro ⟨hφ, rfl⟩ ψ
    exact hB φ ψ
  · refine ⟨Submodule.mem_top, ext_inner_right ℂ fun v => ?_⟩
    exact (hB φ v).symm.trans (h ⟨v, Submodule.mem_top⟩)
omit [CompleteSpace H] in
theorem isSelfAdjoint_of_isSelfAdjointCLM {B : H →L[ℂ] H} (hB : IsSelfAdjointCLM B)
    [CompleteSpace H] : IsSelfAdjoint B :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun x y => (hB x y).symm
omit [CompleteSpace H] in
theorem inner_apply_self_im_and_re_bound {B : H →L[ℂ] H} (hB : IsSelfAdjointCLM B) {c : ℝ}
    (hc : ‖B‖ ≤ c) (ψ : H) :
    (⟪ψ, B ψ⟫_ℂ).im = 0 ∧ |(⟪ψ, B ψ⟫_ℂ).re| ≤ c * ‖ψ‖ ^ 2 := by
  constructor
  · have h : (starRingEnd ℂ) ⟪ψ, B ψ⟫_ℂ = ⟪ψ, B ψ⟫_ℂ :=
      (inner_conj_symm (B ψ) ψ).trans (hB ψ ψ).symm
    exact Complex.conj_eq_iff_im.1 h
  · calc |(⟪ψ, B ψ⟫_ℂ).re| ≤ ‖⟪ψ, B ψ⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖ψ‖ * ‖B ψ‖ := norm_inner_le_norm _ _
      _ ≤ ‖ψ‖ * (‖B‖ * ‖ψ‖) := by gcongr; exact B.le_opNorm ψ
      _ ≤ ‖ψ‖ * (c * ‖ψ‖) := by gcongr
      _ = c * ‖ψ‖ ^ 2 := by ring
omit [CompleteSpace H] in
theorem inner_real_smul_one_apply (c : ℝ) (ψ : H) :
    ⟪ψ, ((c : ℂ) • (1 : H →L[ℂ] H)) ψ⟫_ℂ = ((c * ‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  simp only [smul_apply, one_apply_eq_self, inner_smul_right,
    inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
theorem isSelfAdjoint_real_smul_one (c : ℝ) : IsSelfAdjoint ((c : ℂ) • (1 : H →L[ℂ] H)) :=
  IsSelfAdjoint.smul (by simp [isSelfAdjoint_iff]) (IsSelfAdjoint.one _)
theorem isGE_neg_bound {B : H →L[ℂ] H} (hB : IsSelfAdjointCLM B) {c : ℝ} (hc : ‖B‖ ≤ c) :
    IsGE B (((-c : ℝ) : ℂ) • (1 : H →L[ℂ] H)) := by
  have sB := isSelfAdjoint_of_isSelfAdjointCLM hB
  refine ⟨sB, isSelfAdjoint_real_smul_one _, ⟨sB.sub (isSelfAdjoint_real_smul_one _), fun ψ => ?_⟩⟩
  obtain ⟨him, hre⟩ := inner_apply_self_im_and_re_bound hB hc ψ
  rw [sub_apply, inner_sub_right, inner_real_smul_one_apply, Complex.le_def]
  refine ⟨?_, ?_⟩
  · simp only [Complex.zero_re, Complex.sub_re, Complex.ofReal_re]
    have := (abs_le.1 hre).1
    linarith
  · rw [Complex.sub_im, Complex.ofReal_im, him]
    simp
theorem bound_isGE {B : H →L[ℂ] H} (hB : IsSelfAdjointCLM B) {c : ℝ} (hc : ‖B‖ ≤ c) :
    IsGE ((c : ℂ) • (1 : H →L[ℂ] H)) B := by
  have sB := isSelfAdjoint_of_isSelfAdjointCLM hB
  refine ⟨isSelfAdjoint_real_smul_one _, sB, ⟨(isSelfAdjoint_real_smul_one _).sub sB, fun ψ => ?_⟩⟩
  obtain ⟨him, hre⟩ := inner_apply_self_im_and_re_bound hB hc ψ
  rw [sub_apply, inner_sub_right, inner_real_smul_one_apply, Complex.le_def]
  refine ⟨?_, ?_⟩
  · simp only [Complex.zero_re, Complex.sub_re, Complex.ofReal_re]
    have := (abs_le.1 hre).2
    linarith
  · rw [Complex.sub_im, Complex.ofReal_im, him]
    simp
theorem isPositive_of_isPositiveOp {P : H →L[ℂ] H} (h : HilbertSpaceBasics.IsPositiveOp P) :
    P.IsPositive := by apply _root_.YangMills.Construction.SpectralTheorem.isPositive_of_isPositiveOp <;> assumption
section Bounded
variable (hspec : SpectralTheorem.SpectralTheoremHolds)
  (hjoint : JointSpectral.JointSpectralTheorem)
include hspec
theorem spectralMeasure_ofBounded_eq_and_isCarriedBy {B : H →L[ℂ] H} (hB : IsSelfAdjointCLM B)
    {c : ℝ} (hc : ‖B‖ ≤ c) (hc₀ : 0 < c) :
    spectralMeasure (ofBounded B) = JointSpectral.jointMeasureOnSpace le_rfl (fun _ : Fin 1 => B) ∧
      (spectralMeasure (ofBounded B)).IsCarriedBy (realLineSet ⟨Icc (-c) c, measurableSet_Icc⟩) := by
  obtain ⟨-, -, -, -, -, -, -, -, hlast⟩ :=
    hspec H (ofBounded B)
      ((isSelfAdjointOp_iff_unbounded _).2 (isSelfAdjointUnbounded_ofBounded hB))
  exact hlast B (-c) c rfl (by linarith) (isGE_neg_bound hB hc) (bound_isGE hB hc)
theorem spectralMeasure_ofBounded_isCarriedBy_norm {B : H →L[ℂ] H} (hB : IsSelfAdjointCLM B) :
    (spectralMeasure (ofBounded B)).IsCarriedBy
      (realLineSet ⟨Icc (-‖B‖) ‖B‖, measurableSet_Icc⟩) := by
  set E := spectralMeasure (ofBounded B) with hE
  let c : ℕ → ℝ := fun k => ‖B‖ + 1 / ((k : ℝ) + 1)
  have hk : ∀ k, ‖B‖ ≤ c k ∧ 0 < c k := fun k => by
    have : 0 < 1 / ((k : ℝ) + 1) := by positivity
    have := norm_nonneg B
    simp only [c]
    constructor <;> linarith
  let S : ℕ → BorelSubsets RealLineSet := fun k =>
    ⟨(realLineSet ⟨Icc (-c k) (c k), measurableSet_Icc⟩).1ᶜ,
      (realLineSet ⟨Icc (-c k) (c k), measurableSet_Icc⟩).2.compl⟩
  have hS : ∀ k, E (S k) = 0 := fun k =>
    (spectralMeasure_ofBounded_eq_and_isCarriedBy hspec hB (hk k).1 (hk k).2).2
  let T : BorelSubsets RealLineSet :=
    ⟨(realLineSet ⟨Icc (-‖B‖) ‖B‖, measurableSet_Icc⟩).1ᶜ,
      (realLineSet ⟨Icc (-‖B‖) ‖B‖, measurableSet_Icc⟩).2.compl⟩
  have hT : T.1 ⊆ ⋃ k, (S k).1 := by
    intro y hy
    have hy' : y.1 0 ∉ Icc (-‖B‖) ‖B‖ := hy
    have hlim : Filter.Tendsto c Filter.atTop (nhds (‖B‖ + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at hlim
    have hlt : ‖B‖ < |y.1 0| := by
      by_contra hle
      exact hy' (abs_le.1 (not_lt.1 hle))
    obtain ⟨k, hk'⟩ := (hlim.eventually (gt_mem_nhds hlt)).exists
    refine mem_iUnion.2 ⟨k, fun hmem => ?_⟩
    have hmem' : y.1 0 ∈ Icc (-c k) (c k) := hmem
    exact absurd (abs_le.2 hmem') (not_le.2 hk')
  change E T = 0
  ext ψ
  have hnull : E.diagMeasure ψ T.1 = 0 := by
    refine measure_mono_null hT (measure_iUnion_null fun k => ?_)
    rw [show (S k).1 = (S k).1 from rfl, SpectralMeasure.diagMeasure_apply, hS k]
    simp
  rw [SpectralMeasure.diagMeasure_apply, ENNReal.ofReal_eq_zero] at hnull
  have : ‖E T ψ‖ = 0 := by
    have h0 := norm_nonneg (E T ψ)
    nlinarith
  simpa using this
include hjoint
theorem opCommutes_of_commute {B C : H →L[ℂ] H} (hB : IsSelfAdjointCLM B)
    (hC : Commute C B) : OpCommutes C (spectralMeasure (ofBounded B)) := by
  have hc : ‖B‖ ≤ ‖B‖ + 1 := by linarith
  have hE := (spectralMeasure_ofBounded_eq_and_isCarriedBy hspec hB hc (by positivity)).1
  have sB := isSelfAdjoint_of_isSelfAdjointCLM hB
  have hbox : IsCommutingInBox (fun _ : Fin 1 => B)
      (JointSpectral.normBoundLower fun _ : Fin 1 => B)
      (JointSpectral.normBoundUpper fun _ : Fin 1 => B) := by
    refine ⟨fun _ => sB, fun _ _ => Commute.refl _,
      JointSpectral.normBoundLower_lt_normBoundUpper _, fun _ => ?_, fun _ => ?_⟩
    · rw [ContinuousLinearMap.le_def]
      have h := (isGE_neg_bound hB hc).2.2
      exact isPositive_of_isPositiveOp (by simpa [JointSpectral.normBoundLower] using h)
    · rw [ContinuousLinearMap.le_def]
      have h := (bound_isGE hB hc).2.2
      exact isPositive_of_isPositiveOp (by simpa [JointSpectral.normBoundUpper] using h)
  obtain ⟨-, hrep, -, hcomm⟩ := (hjoint H 1 le_rfl).1 _ _ _ hbox
  intro Δ
  rw [hE]
  exact hcomm _ hrep C (fun _ => hC) _
theorem stronglyCommute_of_commute {B B' : H →L[ℂ] H} (hB : IsSelfAdjointCLM B)
    (hB' : IsSelfAdjointCLM B') (hc : Commute B B') :
    StronglyCommute (ofBounded B) (ofBounded B') := by
  intro Δ Δ'
  have hΔ : Commute (spectralMeasure (ofBounded B) Δ) B' :=
    (opCommutes_of_commute hspec hjoint hB hc.symm Δ).symm
  exact opCommutes_of_commute hspec hjoint hB' hΔ Δ'
end Bounded
theorem selfAdjointResolventFacts_holds (hspec : SpectralTheorem.SpectralTheoremHolds) :
    SelfAdjointResolventFacts H := by
  intro A hA
  have hA' := (isSelfAdjointOp_iff_unbounded A).2 hA
  obtain ⟨-, hbp, hbm, ⟨R, R', hR, hR', hn, -, -, hstar, e₁, e₂⟩, -⟩ := hspec H A hA'
  have hI : (2 * Complex.I) ≠ 0 := by simp
  subst hstar
  refine ⟨fun φ ψ => ?_, hbp, hbm, R, star R, hR, hR', hn,
    (norm_star R).le.trans hn, fun x y => ?_, ?_, ?_⟩
  · have hs : ⟪A φ, (ψ : H)⟫_ℂ = ⟪(φ : H), A ψ⟫_ℂ := (hA'.2.2 φ ψ).symm
    refine ⟨hs.symm, ?_, ?_⟩
    · simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        Complex.conj_I, hs]
      linear_combination (-⟪(φ : H), (ψ : H)⟫_ℂ) * Complex.I_mul_I
    · simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        Complex.conj_I, hs]
      linear_combination (-⟪(φ : H), (ψ : H)⟫_ℂ) * Complex.I_mul_I
  · rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  · have h : star R - R = (2 * Complex.I) • (R * star R) := by
      have h' := congrArg Neg.neg e₂
      rw [neg_sub] at h'
      rw [h', ← neg_smul]
      congr 1
      ring
    rw [h, smul_smul, one_div, inv_mul_cancel₀ hI, one_smul]
  · have h : star R - R = (2 * Complex.I) • (star R * R) := by
      have h' := congrArg Neg.neg e₁
      rw [neg_sub] at h'
      rw [h', ← neg_smul]
      congr 1
      ring
    rw [h, smul_smul, one_div, inv_mul_cancel₀ hI, one_smul]
omit [CompleteSpace H] in
theorem eq_spectralIntegralOp [CompleteSpace H] {n : ℕ} {Y : Set (Fin n → ℝ)} {A : UnboundedOp H}
    {E : SpectralMeasure Y H} {g : Y → ℂ} (hA : IsSpectralIntegralOf A E g) :
    A = spectralIntegralOp E g := by
  have hB : IsSpectralIntegralOf (spectralIntegralOp E g) E g :=
    Classical.epsilon_spec (p := fun B => IsSpectralIntegralOf B E g) ⟨A, hA⟩
  refine LinearPMap.ext ?_ ?_
  · ext ψ
    exact (hA.1 ψ).trans (hB.1 ψ).symm
  · intro x hx hy
    exact (hA.2 ⟨x, hx⟩).trans (hB.2 ⟨x, hy⟩).symm
theorem selfAdjointDiagonalizationTheorem_holds (hspec : SpectralTheorem.SpectralTheoremHolds)
    (hjoint : JointSpectral.JointSpectralTheorem)
    (hfacts : ResolvedFacts.DiagonalizedFacts)
    (hgen : JointSpectralGenerators.JointMeasureGeneratorsCommutation) :
    SelfAdjointDiagonalizationTheorem := by
  refine ⟨?_, hfacts, hgen⟩
  intro H _ _ _
  have hdiag : ∀ A : UnboundedOp H, OperatorTransport.IsSelfAdjointUnbounded A →
      IsDiagonalized A := fun A hA => by
    obtain ⟨-, -, -, -, ⟨E, hE, -⟩, -⟩ := hspec H A ((isSelfAdjointOp_iff_unbounded A).2 hA)
    exact ⟨E, hE⟩
  refine ⟨fun B hB => ⟨hdiag _ (isSelfAdjointUnbounded_ofBounded hB),
      spectralMeasure_ofBounded_isCarriedBy_norm hspec hB,
      fun C hC => opCommutes_of_commute hspec hjoint hB hC⟩,
    fun B B' hB hB' hc => stronglyCommute_of_commute hspec hjoint hB hB' hc,
    selfAdjointResolventFacts_holds hspec, hdiag,
    fun A => ⟨fun ⟨E, hE⟩ => ?_, hdiag A⟩, fun A hA => ?_⟩
  · rw [eq_spectralIntegralOp hE]
    exact ((hfacts H).1 E).1
  · obtain ⟨-, -, -, -, hu, hs, -⟩ := hspec H A ((isSelfAdjointOp_iff_unbounded A).2 hA)
    exact ⟨hu, hs⟩
end YangMills.Construction.SelfAdjointResolution
