import YangMills.Construction.TransferOperators.GaugeAveragesOfFunctionsOfLayersProof
import YangMills.Construction.TransferOperators.ReversalInvarianceAtContinuousFunctionsInTheNextStack
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
namespace YangMills.Construction
open InfiniteLattice SpinHarmonics Matrices.ComplexMatrix2
namespace TransferOperators.ReversalInvariantContinuousNextStack
variable {μ : Fin 4}
theorem continuous_transportedLinkVariable (S : Stack) (j : ℤ) (b : SliceLink μ) :
    Continuous fun U : GaugeField 1 => S.transportedLinkVariable μ U j b := by apply _root_.YangMills.Construction.TransferOperators.SliceMean.continuous_transportedLinkVariable <;> assumption
theorem parallelTransport_centeredStack_succ (i k : ℤ) (hk : 1 ≤ k) (U : GaugeField 1) {j : ℤ}
    (hj : i - k + 1 ≤ j) (y : SliceSite μ) :
    (centeredStack i (k + 1) (by omega)).parallelTransport μ U j y =
      temporalLinkVariable μ U (i - k) y * (centeredStack i k hk).parallelTransport μ U j y := by
  have hn : (j - (centeredStack i (k + 1) (by omega)).lower).toNat =
      (j - (centeredStack i k hk).lower).toNat + 1 := by
    simp only [centeredStack]
    omega
  have h₀ : (centeredStack i (k + 1) (by omega)).lower + ((0 : ℕ) : ℤ) = i - k := by
    simp only [centeredStack]
    push_cast
    ring
  unfold Stack.parallelTransport
  rw [hn, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, h₀]
  refine congrArg (temporalLinkVariable μ U (i - k) y * ·) (congrArg List.prod
    (List.map_congr_left fun n _ => ?_))
  have h₁ : (centeredStack i (k + 1) (by omega)).lower + ((n.succ : ℕ) : ℤ) =
      (centeredStack i k hk).lower + (n : ℤ) := by
    simp only [centeredStack]
    push_cast
    ring
  simp only [Function.comp_apply, h₁]
theorem transportedLinkVariable_centeredStack_succ (i k : ℤ) (hk : 1 ≤ k) (v : Set (SliceSite μ))
    (U : GaugeField 1) :
    (fun p : centeredLinkPairs i k v =>
        (centeredStack i (k + 1) (by omega)).transportedLinkVariable μ U p.1.1 p.1.2) =
      diagonalGaugeAct (snd_mem_linksWithin i k v)
        (fun y : v => temporalLinkVariable μ U (i - k) y.1)
        (fun p => (centeredStack i k hk).transportedLinkVariable μ U p.1.1 p.1.2) := by
  funext p
  simp only [diagonalGaugeAct, Stack.transportedLinkVariable]
  rw [parallelTransport_centeredStack_succ i k hk U p.2.1,
    parallelTransport_centeredStack_succ i k hk U p.2.1]
  simp only [mul_inv_rev, mul_assoc]
theorem tendsto_integral_comp_of_tendstoUniformly {K : Type} [Finite K] (ρ : Measure (GaugeField 1))
    [IsProbabilityMeasure ρ] {P : ℕ → (K → specialUnitary) → ℂ} (A : C(K → specialUnitary, ℂ))
    (hP : ∀ n, Continuous (P n)) (h : TendstoUniformly P A atTop)
    {W : GaugeField 1 → K → specialUnitary} (hW : Continuous W) :
    Tendsto (fun n => ∫ U, P n (W U) ∂ρ) atTop (𝓝 (∫ U, A (W U) ∂ρ)) := by
  have h₁ := Metric.tendstoUniformly_iff.mp h 1 one_pos
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖A‖ + 1) ?_ ?_
    (integrable_const _) ?_
  · exact Eventually.of_forall fun n => ((hP n).comp hW).measurable.aestronglyMeasurable
  · filter_upwards [h₁] with n hn
    refine ae_of_all _ fun U => ?_
    have h₂ := hn (W U)
    rw [dist_comm, dist_eq_norm] at h₂
    have h₃ := norm_sub_norm_le (P n (W U)) (A (W U))
    have h₄ := A.norm_coe_le_norm (W U)
    linarith
  · exact ae_of_all _ fun U => h.tendsto_at (W U)
theorem holds
    (hStates : GibbsHaarKernels.Statement)
    (hAvg : SliceGaugeMeanProperties) : Statement := by
  intro μ β hβ ν hν i k hk hinv v _ Ψ hne hreal
  have hprob : IsProbabilityMeasure ν := hν.1.1
  have hG : ν ∈ gibbsClass (zero_lt_one (α := ℝ)) β :=
    ((hStates.1 β hβ ν hprob).1).mp hν.1
  obtain ⟨b, hb⟩ := id hne
  have hvne : v.Nonempty := ⟨b.source, hb.1⟩
  have hJne : (centeredLinkPairs i k v).Nonempty := ⟨(i, b), by omega, by omega, hb⟩
  have hI := snd_mem_linksWithin i k v
  obtain ⟨⟨hcont, -, -, -, hrealav, -⟩, -, hlim, hexch, hint⟩ :=
    hAvg μ β hβ v (centeredLinkPairs i k v) hvne hJne hI
  obtain ⟨hc, hinvav⟩ := hcont Ψ
  obtain ⟨A, hA⟩ : ∃ A : C(centeredLinkPairs i k v → specialUnitary, ℂ), ⇑A = sliceGaugeMean hI Ψ :=
    ⟨⟨_, hc⟩, rfl⟩
  have hAinv : IsDiagonalGaugeInvariant hI (A : (centeredLinkPairs i k v → specialUnitary) → ℂ) := by
    rw [hA]
    exact hinvav
  have hAreal : IsRealValuedSliceFunction (A : (centeredLinkPairs i k v → specialUnitary) → ℂ) := by
    rw [hA]
    exact hrealav Ψ hreal
  obtain ⟨P, hP, hPA⟩ := hlim A hAreal hAinv
  have hex := hexch (reflectPairPerm i k v) (isLevelExchange_reflectPairPerm i k v)
  have hcomm : sliceGaugeMean hI (levelExchanged (reflectPairPerm i k v) Ψ) =
      permuteArgs (reflectPairPerm i k v) A := by
    rw [hA]
    exact (hex Ψ).1
  have hRinv := (hex A).2.2.1 hAinv
  have hWin : Continuous fun U : GaugeField 1 => fun p : centeredLinkPairs i k v =>
      (centeredStack i k hk).transportedLinkVariable μ U p.1.1 p.1.2 :=
    continuous_pi fun p => continuous_transportedLinkVariable _ _ _
  have hstack : ∀ Φ : (centeredLinkPairs i k v → specialUnitary) → ℂ,
      IsDiagonalGaugeInvariant hI Φ → ∀ U : GaugeField 1,
      Φ (fun p => (centeredStack i (k + 1) (by omega)).transportedLinkVariable μ U p.1.1 p.1.2) =
        Φ (fun p => (centeredStack i k hk).transportedLinkVariable μ U p.1.1 p.1.2) := by
    intro Φ hΦ U
    rw [transportedLinkVariable_centeredStack_succ i k hk v U]
    exact hΦ _ _
  have hbounds : ∀ p ∈ centeredLinkPairs i k v,
      (centeredStack i (k + 1) (by omega)).lower ≤ p.1 ∧
        p.1 ≤ (centeredStack i (k + 1) (by omega)).upper := by
    intro p hp
    have h₁ := hp.1
    have h₂ := hp.2.1
    simp only [centeredStack]
    omega
  have h₁ := hint (centeredStack i (k + 1) (by omega)) hbounds ν hG Ψ
  have h₂ := hint (centeredStack i (k + 1) (by omega)) hbounds ν hG
    (levelExchanged (reflectPairPerm i k v) Ψ)
  have hPc : ∀ n, Continuous (P n) := fun n => (hP n).1.1.continuous
  have hmid : ∫ U, A (fun p => (centeredStack i k hk).transportedLinkVariable μ U p.1.1 p.1.2) ∂ν =
      ∫ U, levelExchanged (reflectPairPerm i k v) A
        (fun p => (centeredStack i k hk).transportedLinkVariable μ U p.1.1 p.1.2) ∂ν := by
    have hL := tendsto_integral_comp_of_tendstoUniformly ν A hPc hPA hWin
    have hR := tendsto_integral_comp_of_tendstoUniformly ν (levelExchanged (reflectPairPerm i k v) A)
      (P := fun n => levelReversal i k v (P n))
      (fun n => (hPc n).comp (continuous_pi fun p => continuous_apply _))
      (hPA.comp fun (u : centeredLinkPairs i k v → specialUnitary) p => u (reflectPair i k v p)) hWin
    refine tendsto_nhds_unique hL (hR.congr fun n => ?_)
    exact (hinv v (P n) hne (hP n).1 (hP n).2).symm
  calc ∫ U, Ψ (fun p => (centeredStack i (k + 1) (by omega)).transportedLinkVariable μ U p.1.1 p.1.2) ∂ν
      = ∫ U, A (fun p => (centeredStack i (k + 1) (by omega)).transportedLinkVariable μ U p.1.1 p.1.2) ∂ν := by
        rw [hA]
        exact h₁.symm
    _ = ∫ U, A (fun p => (centeredStack i k hk).transportedLinkVariable μ U p.1.1 p.1.2) ∂ν :=
        integral_congr_ae (ae_of_all _ fun U => hstack _ hAinv U)
    _ = ∫ U, levelExchanged (reflectPairPerm i k v) A
        (fun p => (centeredStack i k hk).transportedLinkVariable μ U p.1.1 p.1.2) ∂ν := hmid
    _ = ∫ U, levelExchanged (reflectPairPerm i k v) A
        (fun p => (centeredStack i (k + 1) (by omega)).transportedLinkVariable μ U p.1.1 p.1.2) ∂ν :=
        integral_congr_ae (ae_of_all _ fun U => (hstack _ hRinv U).symm)
    _ = ∫ U, sliceGaugeMean hI (levelExchanged (reflectPairPerm i k v) Ψ)
        (fun p => (centeredStack i (k + 1) (by omega)).transportedLinkVariable μ U p.1.1 p.1.2) ∂ν := by
        rw [hcomm]
        rfl
    _ = ∫ U, levelReversal i k v Ψ
        (fun p => (centeredStack i (k + 1) (by omega)).transportedLinkVariable μ U p.1.1 p.1.2) ∂ν := h₂
end TransferOperators.ReversalInvariantContinuousNextStack
end YangMills.Construction
end
