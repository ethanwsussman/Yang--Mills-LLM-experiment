import YangMills.Construction.InfiniteLattice.BoxRepresentsTheTorusAndItsThinBoundaryLayer
import YangMills.Construction.InfiniteLattice.FinitenessOfATorusNormalisersAndExtendedMeasures
import YangMills.Construction.InfiniteLattice.LowerTangentsAtAConstantFunction
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.NormalFamilies
noncomputable section
namespace YangMills.Construction.InfiniteLattice.ConstantTangents
theorem observableSupport_const (c : ℂ) : observableSupport (fun _ : GaugeField 1 => c) = ∅ := by
  apply Set.eq_empty_of_subset_empty
  exact Set.sInter_subset_of_mem
    ⟨fun b hb => absurd hb (Set.notMem_empty b), Set.finite_empty, fun _ _ _ => rfl⟩
theorem translate_const {𝔸 : LocalObservableArray} {c : ℝ}
    (h : 𝔸.IsSingleGenerated (fun _ => (c : ℂ))) (i : 𝔸.Label) :
    𝔸.translate i = fun _ => (c : ℂ) := by
  funext V
  simp only [LocalObservableArray.translate]
  rw [h.2 i.2]
  rfl
theorem boxCoverNumber_le (ϱ : ℕ+) : (boxCoverNumber ϱ : ℝ) ≤ 17 * ((ϱ : ℕ) : ℝ) ^ 4 := by
  have h1 : (1 : ℝ) ≤ ((ϱ : ℕ) : ℝ) := by exact_mod_cast ϱ.pos
  have h2 : ((ϱ : ℕ) : ℝ) + 1 ≤ 2 * ((ϱ : ℕ) : ℝ) := by linarith
  have h3 : (((ϱ : ℕ) : ℝ) + 1) ^ 4 ≤ (2 * ((ϱ : ℕ) : ℝ)) ^ 4 :=
    pow_le_pow_left₀ (by linarith) h2 4
  have h4 : (1 : ℝ) ≤ ((ϱ : ℕ) : ℝ) ^ 4 := one_le_pow₀ h1
  simp only [boxCoverNumber]
  push_cast
  nlinarith [h3, h4]
theorem supNorm_nonneg (A : GaugeField 1 → ℂ) : 0 ≤ observableSupNorm A :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem shellDefect_le (F : OrthogonalNormalFrame) (s : Fin 4 → ℕ+) (ϱ : ℕ+) (A : GaugeField 1 → ℂ)
    {β : ℝ} (hβ : 0 < β) (t : ℝ) (hD : 0 < ((F.fundamentalBox s).ncard : ℝ))
    (hshell : ((F.boundaryShell s ϱ).ncard : ℝ) ≤
      (Constants.BoxTorus.layerNumber : ℝ) * ((ϱ : ℕ) : ℝ) * ((F.fundamentalBox s).ncard : ℝ) *
        ∑ i, (((s i : ℕ) : ℝ))⁻¹) :
    0 ≤ LocalObservableArray.shellDefect F s ϱ A β t ∧
      LocalObservableArray.shellDefect F s ϱ A β t ≤ LocalObservableArray.sideDefect s ϱ A β t := by
  have hX : 0 ≤ β + |t| * observableSupNorm A :=
    add_nonneg hβ.le (mul_nonneg (abs_nonneg t) (supNorm_nonneg A))
  have hq : 0 ≤ ((F.boundaryShell s ϱ).ncard : ℝ) / ((F.fundamentalBox s).ncard : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hD.le
  have hq' : ((F.boundaryShell s ϱ).ncard : ℝ) / ((F.fundamentalBox s).ncard : ℝ) ≤
      4 * ((ϱ : ℕ) : ℝ) * ∑ i, (((s i : ℕ) : ℝ))⁻¹ := by
    rw [div_le_iff₀ hD]
    calc ((F.boundaryShell s ϱ).ncard : ℝ) ≤ _ := hshell
      _ = _ := by
        simp only [Constants.BoxTorus.layerNumber]
        push_cast
        ring
  have hT : (Constants.BoxTorus.tangentNumber : ℝ) = 24 := by
    rw [Constants.BoxTorus.tangentNumber_eq]; norm_num
  have hT' : (Constants.BoxTorus.tangentSideNumber : ℝ) = 1632 := by
    rw [Constants.BoxTorus.tangentSideNumber_eq]; norm_num
  constructor
  · simp only [LocalObservableArray.shellDefect]
    rw [hT]
    positivity
  · simp only [LocalObservableArray.shellDefect, LocalObservableArray.sideDefect]
    rw [hT, hT']
    have hbq : (boxCoverNumber ϱ : ℝ) *
        (((F.boundaryShell s ϱ).ncard : ℝ) / ((F.fundamentalBox s).ncard : ℝ)) ≤
        (17 * ((ϱ : ℕ) : ℝ) ^ 4) * (4 * ((ϱ : ℕ) : ℝ) * ∑ i, (((s i : ℕ) : ℝ))⁻¹) :=
      mul_le_mul (boxCoverNumber_le ϱ) hq' hq (by positivity)
    calc 24 * (β + |t| * observableSupNorm A) * (boxCoverNumber ϱ : ℝ) *
          (((F.boundaryShell s ϱ).ncard : ℝ) / ((F.fundamentalBox s).ncard : ℝ))
        = 24 * (β + |t| * observableSupNorm A) * ((boxCoverNumber ϱ : ℝ) *
          (((F.boundaryShell s ϱ).ncard : ℝ) / ((F.fundamentalBox s).ncard : ℝ))) := by ring
      _ ≤ 24 * (β + |t| * observableSupNorm A) * ((17 * ((ϱ : ℕ) : ℝ) ^ 4) *
          (4 * ((ϱ : ℕ) : ℝ) * ∑ i, (((s i : ℕ) : ℝ))⁻¹)) :=
          mul_le_mul_of_nonneg_left hbq (by positivity)
      _ = 1632 * (β + |t| * observableSupNorm A) * ((ϱ : ℕ) : ℝ) ^ 5 *
          ∑ i, (((s i : ℕ) : ℝ))⁻¹ := by ring
theorem stateEval_const (ν : Measure (GaugeField 1)) [IsProbabilityMeasure ν] (c : ℝ) :
    (stateEval ν fun _ : GaugeField 1 => (c : ℂ)).re = c := by
  simp [stateEval]
theorem constantLowerTangentClaim_of (hbox : FundamentalBox.RepresentsQuotientWithThinShell)
    (hfin : FiniteTorusPartitionsAndLifts) : ConstantLowerTangentClaim := by
  intro F s Γ hrect 𝔸 hle c hgen β hβ t
  obtain ⟨-, hcard, -, hshell⟩ := hbox F s Γ hrect
  obtain ⟨hfinQ, hnorm⟩ := hfin β hβ Γ
  have hunder := hfinQ 𝔸.sublattice hle
  have hZ0 : 0 < 𝔸.untiltedTorusPartition Γ β :=
    (hnorm 𝔸 hle 0).1.tiltedPartition_pos
  have hidx : Γ.periods.index ≠ 0 := hunder.periods_finiteIndex.index_ne_zero
  have hncard : (F.fundamentalBox s).ncard = Γ.periods.index := by
    rw [Set.ncard, hcard]
    simp
  have hD : 0 < ((F.fundamentalBox s).ncard : ℝ) := by
    rw [hncard]
    exact_mod_cast Nat.pos_of_ne_zero hidx
  have hQ : 𝔸.sublattice.index ≠ 0 := 𝔸.sublattice_finiteIndex.index_ne_zero
  have hcosets : ((Γ.periods.addSubgroupOf 𝔸.sublattice).index : ℝ) =
      𝔸.invIndex * ((F.fundamentalBox s).ncard : ℝ) := by
    rw [hncard, hunder.index_mul, LocalObservableArray.invIndex]
    push_cast
    have : (𝔸.sublattice.index : ℝ) ≠ 0 := by exact_mod_cast hQ
    field_simp
  have hsum : ∀ V, 𝔸.periodicSum Γ V =
      ((Γ.periods.addSubgroupOf 𝔸.sublattice).index : ℝ) * c := by
    intro V
    have : Finite (𝔸.Cosets Γ) := hunder.finite_cosets
    have : Fintype (𝔸.Cosets Γ) := Fintype.ofFinite _
    have hval : ∀ i : 𝔸.Cosets Γ × Fin 𝔸.size,
        (Γ.periodize (𝔸.translate (𝔸.cosetRep Γ i.1, i.2)) V).re = c := by
      intro i
      rw [translate_const hgen]
      simp [PeriodSublattice.periodize]
    simp only [LocalObservableArray.periodicSum, hval]
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, hgen.1, nsmul_eq_mul, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
    simp
  have hZ : 𝔸.tiltedPartition Γ β t =
      Real.exp (t * c * 𝔸.invIndex * ((F.fundamentalBox s).ncard : ℝ)) *
        𝔸.untiltedTorusPartition Γ β := by
    simp only [LocalObservableArray.untiltedTorusPartition, LocalObservableArray.tiltedPartition]
    rw [← integral_const_mul]
    congr 1
    funext V
    simp only [LocalObservableArray.tiltedWeight]
    rw [← Real.exp_add, hsum V, hcosets]
    congr 1
    ring
  have hlog : 𝔸.logTiltRatioPerSite Γ F s β t = t * 𝔸.invIndex * c := by
    rw [LocalObservableArray.logTiltRatioPerSite, hZ, mul_div_assoc, div_self hZ0.ne', mul_one,
      Real.log_exp]
    field_simp
  have hdefects := fun ϱ : ℕ+ =>
    shellDefect_le F s ϱ (fun _ => (c : ℂ)) hβ t hD (hshell ϱ)
  refine ⟨observableSupport_const _, ?_, hZ, ?_, ?_, ?_⟩
  · intro W
    apply Set.eq_empty_of_forall_notMem
    rintro i ⟨b, hb, -⟩
    rw [translate_const hgen, observableSupport_const] at hb
    exact hb
  · intro ν hν
    rw [hlog, stateEval_const]
  · intro ν ϱ hν
    rw [LocalObservableArray.IsLowerTangent, hlog, stateEval_const]
    have := hdefects ϱ
    constructor <;> linarith [this.1, this.2]
  · intro ϱ
    exact ⟨(hdefects ϱ).1, (hdefects ϱ).1.trans (hdefects ϱ).2⟩
end YangMills.Construction.InfiniteLattice.ConstantTangents
