import YangMills.Construction.ColdStepAtMirrorFrames.PlainChainAtLevelZeroProof
import YangMills.Construction.SummableBoundsOfTheFlow.BoundedDerivativesOnASet
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOfATameObservable
import YangMills.Construction.SummableBoundsOfTheFlow.SlicesOfASmoothFunction
import YangMills.Construction.SummableBoundsOfTheFlow.TheTopDerivativesOfATameMeanAreCumulants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ColdStepAtMirrorFrames UniformDerivativeBounds SmoothSlices Cumulants MeasureTheory Set Filter
open BlockAverages hiding bondSpread
open scoped Topology
namespace ScaledVariables
namespace TiltedMeanSmoothness
variable {F : BlockFrame}
abbrev StepVars (F : BlockFrame) : Type := StepVariable (finiteCells F)
theorem bondDeriv_fin_zero {j : ℕ} (g : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (c : Fin 0 → F.Site j × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv g W c X = g W := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
def scaledBalls (F : BlockFrame) (ρ l : ℝ) : Set (StepVars F) := {ζ | MemScaledBalls ρ l ζ}
theorem isOpen_scaledBalls (ρ l : ℝ) : IsOpen (scaledBalls F ρ l) := by
  have : scaledBalls F ρ l = ⋂ b, {ζ : StepVars F | l * ‖ζ b‖ < ρ} := by
    ext ζ
    simp [scaledBalls, MemScaledBalls]
  rw [this]
  exact isOpen_iInter_of_finite fun b => isOpen_lt (by fun_prop) continuous_const
def admissibleScales (ρ lo hi : ℝ) (ζ : StepVars F) : Set ℝ := {l | lo < l ∧ l < hi ∧ MemScaledBalls ρ l ζ}
theorem isOpen_admissibleScales (ρ lo hi : ℝ) (ζ : StepVars F) : IsOpen (admissibleScales ρ lo hi ζ) := by
  have : admissibleScales ρ lo hi ζ = Ioo lo hi ∩ ⋂ b, {l : ℝ | l * ‖ζ b‖ < ρ} := by
    ext l
    simp [admissibleScales, MemScaledBalls, and_assoc]
  rw [this]
  exact isOpen_Ioo.inter (isOpen_iInter_of_finite fun b => isOpen_lt (by fun_prop) continuous_const)
theorem admissibleScales_subset_Ioo (ρ lo hi : ℝ) (ζ : StepVars F) :
    admissibleScales ρ lo hi ζ ⊆ Ioo lo hi := fun _ h => ⟨h.1, h.2.1⟩
theorem scaledBalls_subset_closedBall {ρ lo l : ℝ} (hρ : 0 < ρ) (hlo : 0 < lo) (hl : lo < l) :
    scaledBalls F ρ l ⊆ Metric.closedBall (0 : StepVars F) (ρ / lo) := by
  intro ζ hζ
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
  intro b
  rw [le_div_iff₀ hlo]
  have h1 := hζ b
  have h2 : lo * ‖ζ b‖ ≤ l * ‖ζ b‖ := mul_le_mul_of_nonneg_right hl.le (norm_nonneg _)
  linarith
theorem contDiffAt_bondDeriv_scale_var (hS : IteratedFDerivSlices) {s ρ lo hi D : ℝ}
    {O : ℝ → StepVars F → F.GaugeField F.top → ℝ} (hO : IsTameOnScales s ρ lo hi D O) {V' : F.GaugeField F.top}
    (hV : IsSmallCurvature s V') {l : ℝ} {ζ : StepVars F} (h1 : lo < l) (h2 : l < hi)
    (h3 : MemScaledBalls ρ l ζ) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hk : k ≤ 3) :
    ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun p : ℝ × StepVars F => bondDeriv (O p.1 p.2) V' c X) (l, ζ) := by
  have h6 := hO.contDiffAt V' hV l ζ k c X h1 h2 h3
  have hG : ContDiffAt ℝ ((3 + k : ℕ) : WithTop ℕ∞)
      (fun q : (Fin k → ℝ) × (ℝ × StepVars F) => O q.2.1 q.2.2 (leftTranslate (bondSpread c X q.1) V'))
      ((0 : Fin k → ℝ), (l, ζ)) := by
    have h7 : ContDiffAt ℝ ((3 + k : ℕ) : WithTop ℕ∞) (fun q : (ℝ × StepVars F) × (Fin k → ℝ) =>
        O q.1.1 q.1.2 (leftTranslate (bondSpread c X q.2) V')) (((0 : Fin k → ℝ), (l, ζ)).swap) :=
      h6.of_le (by exact_mod_cast (show 3 + k ≤ 6 by omega))
    exact ContDiffAt.comp (f := fun q : (Fin k → ℝ) × (ℝ × StepVars F) => (q.2, q.1)) _ h7
      (contDiff_snd.prodMk contDiff_fst).contDiffAt
  exact hS.2.1 (Fin k → ℝ) (ℝ × StepVars F) _ k 3 _ (l, ζ) hG
theorem uniformlyBoundedDerivs_bondDeriv (hR : ClosureProperties) (hS : IteratedFDerivSlices)
    {s ρ lo hi D : ℝ} {O : ℝ → StepVars F → F.GaugeField F.top → ℝ} (hO : IsTameOnScales s ρ lo hi D O)
    {V' : F.GaugeField F.top} (hV : IsSmallCurvature s V') {m : ℕ} (c : Fin m → F.Site F.top × Fin 4)
    (X : Fin m → imaginaryQuaternions) (hX : AreUnitVectors X) (n : ℕ) (hm : m ≤ 3) (hn : n ≤ 3)
    (hread : ∀ j, j ≤ n → IsControlledOrder m j) (ζ : StepVars F) :
    UniformlyBoundedDerivs n D (admissibleScales ρ lo hi ζ) fun l => bondDeriv (O l ζ) V' c X := by
  refine hR.of_contDiff n D _ _ (isOpen_admissibleScales ρ lo hi ζ) (fun x hx => ?_) fun j hj x hx => ?_
  · have h1 := contDiffAt_bondDeriv_scale_var hS hO hV hx.1 hx.2.1 hx.2.2 c X hm
    have h2 : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun l : ℝ => (l, ζ)) x :=
      (contDiff_id.prodMk contDiff_const).contDiffAt
    exact (ContDiffAt.comp x h1 h2).of_le
      (by exact_mod_cast hn : ((n : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞))
  · exact hO.deriv_le V' hV m j c X x ζ (hread j hj) hX hx.1 hx.2.1 hx.2.2
theorem isControlledOrder_of_le {k n : ℕ} (hk : k ≤ 3) (hn : n = if k = 3 then 2 else 3) {m : ℕ} (hm : m ≤ k) :
    ∀ j, j ≤ n → IsControlledOrder m j := by
  intro j hj
  by_cases h3 : k = 3
  · rw [if_pos h3] at hn
    exact Or.inl ⟨by omega, by omega⟩
  · rw [if_neg h3] at hn
    exact Or.inr ⟨by omega, by omega⟩
theorem contDiff_scaledCutoff {w : ℝ → ℝ} (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) (ζ : StepVars F) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun l => scaledCutoff w l ζ := by
  unfold scaledCutoff
  exact contDiff_prod fun b _ => hw.comp (contDiff_id.mul contDiff_const)
theorem continuous_scaledCutoff {w : ℝ → ℝ} (hw : Continuous w) (l : ℝ) :
    Continuous fun ζ : StepVars F => scaledCutoff w l ζ := by
  unfold scaledCutoff
  exact continuous_finsetProd _ fun b _ => hw.comp (by fun_prop)
theorem scaledCutoff_iteratedDeriv_bounded (hS : IteratedFDerivSlices) {w : ℝ → ℝ}
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) (n : ℕ) (lo hi R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j, j ≤ n → ∀ l ∈ Ioo lo hi, ∀ ζ : StepVars F, ‖ζ‖ ≤ R →
      |iteratedDeriv j (fun l => scaledCutoff w l ζ) l| ≤ B := by
  classical
  set ι := ↥(chordBonds (finiteCells F)) with hι
  set Φ : ℝ × (ι → ℝ) → ℝ := fun p => ∏ b, w (p.1 * p.2 b) with hΦ
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := by
    refine contDiff_prod fun b _ => hw.comp ?_
    exact contDiff_fst.mul ((contDiff_apply ℝ ℝ b).comp contDiff_snd)
  set v : ℝ × (ι → ℝ) := (1, 0) with hv
  have hc : ∀ j : ℕ, Continuous fun p => iteratedFDeriv ℝ j Φ p fun _ => v := fun j =>
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℝ × (ι → ℝ)) ℝ fun _ => v).continuous.comp
      (hsm.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hK : IsCompact (Icc lo hi ×ˢ Metric.closedBall (0 : ι → ℝ) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hb : ∀ j : ℕ, ∃ C : ℝ, ∀ p ∈ Icc lo hi ×ˢ Metric.closedBall (0 : ι → ℝ) R,
      ‖iteratedFDeriv ℝ j Φ p fun _ => v‖ ≤ C := fun j =>
    hK.exists_bound_of_continuousOn (hc j).continuousOn
  choose C hC using hb
  refine ⟨∑ j ∈ Finset.range (n + 1), |C j|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun j hj l hl ζ hζ => ?_⟩
  set t : ι → ℝ := fun b => ‖ζ b‖ with ht
  have hmem : (l, t) ∈ Icc lo hi ×ˢ Metric.closedBall (0 : ι → ℝ) R := by
    refine ⟨Ioo_subset_Icc_self hl, ?_⟩
    have hR : 0 ≤ R := (norm_nonneg ζ).trans hζ
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR]
    intro b
    simpa [ht] using (norm_le_pi_norm ζ b).trans hζ
  have e1 := hS.1 (ℝ × (ι → ℝ)) ℝ Φ (ContinuousLinearMap.inl ℝ ℝ (ι → ℝ)) (0, t) l j (fun _ => 1)
    (hsm.contDiffAt.of_le (by exact_mod_cast le_top))
  have e2 : (fun z => Φ ((0, t) + ContinuousLinearMap.inl ℝ ℝ (ι → ℝ) z)) = fun l => scaledCutoff w l ζ := by
    funext z
    simp only [hΦ, scaledCutoff]
    refine Finset.prod_congr rfl fun b _ => ?_
    simp [ht]
  have e3 : ((0, t) : ℝ × (ι → ℝ)) + ContinuousLinearMap.inl ℝ ℝ (ι → ℝ) l = (l, t) := by simp
  have e4 : (fun _ : Fin j => ContinuousLinearMap.inl ℝ ℝ (ι → ℝ) (1 : ℝ)) = fun _ => v := by
    funext _
    simp [hv]
  rw [e2, e3, e4] at e1
  rw [iteratedDeriv_eq_iteratedFDeriv, e1]
  have h1 := hC j (l, t) hmem
  rw [Real.norm_eq_abs] at h1
  exact (h1.trans (le_abs_self _)).trans (Finset.single_le_sum (f := fun j => |C j|)
    (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega)))
theorem iteratedDeriv_eq_zero_of_eq_zero_right {C : ℝ → ℝ} (hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) C)
    {x : ℝ} (h : ∀ y, x ≤ y → C y = 0) (j : ℕ) : iteratedDeriv j C x = 0 := by
  have hcont : Continuous (iteratedDeriv j C) := hC.continuous_iteratedDeriv j (by exact_mod_cast le_top)
  have hz : ∀ y : ℝ, x < y → iteratedDeriv j C y = 0 := by
    intro y hy
    have ev : C =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hy] with u hu
      exact h u (le_of_lt hu)
    rw [(Filter.EventuallyEq.iteratedDeriv ev j).self_of_nhds]
    simp
  have ht : Tendsto (iteratedDeriv j C) (𝓝[>] x) (𝓝 (iteratedDeriv j C x)) :=
    hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hz' : iteratedDeriv j C =ᶠ[𝓝[>] x] fun _ => (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with y hy using hz y hy
  exact tendsto_nhds_unique (ht.congr' hz') tendsto_const_nhds
theorem scaledCutoff_eq_zero {w : ℝ → ℝ} {ρ x : ℝ} (hx : 0 < x) (h0 : ∀ u, ρ ≤ u → w u = 0)
    {ζ : StepVars F} (hζ : ¬ MemScaledBalls ρ x ζ) (y : ℝ) (hy : x ≤ y) : scaledCutoff w y ζ = 0 := by
  unfold MemScaledBalls at hζ
  simp only [not_forall, not_lt] at hζ
  obtain ⟨b, hb⟩ := hζ
  unfold scaledCutoff
  refine Finset.prod_eq_zero (Finset.mem_univ b) (h0 _ (hb.trans ?_))
  exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
theorem continuousOn_bondDeriv (hS : IteratedFDerivSlices) {s ρ lo hi D : ℝ}
    {O : ℝ → StepVars F → F.GaugeField F.top → ℝ} (hO : IsTameOnScales s ρ lo hi D O)
    {V' : F.GaugeField F.top} (hV : IsSmallCurvature s V') {l : ℝ} (h1 : lo < l) (h2 : l < hi) {m : ℕ}
    (c : Fin m → F.Site F.top × Fin 4) (X : Fin m → imaginaryQuaternions) (hm : m ≤ 3) :
    ContinuousOn (fun ζ => bondDeriv (O l ζ) V' c X) (scaledBalls F ρ l) := by
  intro ζ hζ
  have h3 := (contDiffAt_bondDeriv_scale_var hS hO hV h1 h2 hζ c X hm).continuousAt
  have h4 : ContinuousAt (fun ζ' : StepVars F => (l, ζ')) ζ :=
    (continuous_const.prodMk continuous_id).continuousAt
  exact (ContinuousAt.comp (g := fun p : ℝ × StepVars F => bondDeriv (O p.1 p.2) V' c X) h3 h4).continuousWithinAt
theorem uniformlyBoundedDerivs_exp (hR : ClosureProperties) (hS : IteratedFDerivSlices) {s ρ lo hi D : ℝ}
    (hD : 0 ≤ D) {A : ℝ → StepVars F → F.GaugeField F.top → ℝ} (hA : IsTameOnScales s ρ lo hi D A)
    {V : F.GaugeField F.top} (hV : IsSmallCurvature s V) (n : ℕ) (hn : n ≤ 3) : ∃ D' : ℝ, 0 ≤ D' ∧
      ∀ ζ : StepVars F, UniformlyBoundedDerivs n D' (admissibleScales ρ lo hi ζ) fun l => Real.exp (A l ζ V) := by
  obtain ⟨D', h0, h⟩ := hR.exp n D hD
  refine ⟨D', h0, fun ζ => h _ _ ?_⟩
  have h1 := uniformlyBoundedDerivs_bondDeriv hR hS hA hV (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
    (Fin.elim0 : Fin 0 → imaginaryQuaternions) (fun i => i.elim0) n (by omega) hn
    (fun j hj => Or.inr ⟨by omega, by omega⟩) ζ
  simpa only [bondDeriv_fin_zero] using h1
theorem contDiffAt_integral_tiltedWeight (hR : ClosureProperties) (hS : IteratedFDerivSlices)
    {s ρ lo hi D a : ℝ} {w : ℝ → ℝ} {q : StepVars F → ℝ} {A : ℝ → StepVars F → F.GaugeField F.top → ℝ}
    {V : F.GaugeField F.top} (hρ : 0 < ρ) (hlo : 0 < lo) (ha1 : lo < a) (ha2 : a < hi) (hD : 0 ≤ D)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) (hw0 : ∀ u, ρ ≤ u → w u = 0) (hq : Continuous q)
    (hA : IsTameOnScales s ρ lo hi D A) (hV : IsSmallCurvature s V) (n : ℕ) (hn : n ≤ 3)
    (e : ℝ → StepVars F → ℝ) (De : ℝ) (hDe : 0 ≤ De)
    (he : ∀ ζ, UniformlyBoundedDerivs n De (admissibleScales ρ lo hi ζ) fun l => e l ζ)
    (hc : ∀ l, lo < l → l < hi → ContinuousOn (e l) (scaledBalls F ρ l)) :
    ContDiffAt ℝ n (fun l => ∫ ζ, e l ζ * tiltedWeight w q A l V ζ) a := by
  classical
  set Bd : Set (StepVars F) := Metric.closedBall (0 : StepVars F) (ρ / lo) with hBd
  obtain ⟨B, hB0, hB⟩ := scaledCutoff_iteratedDeriv_bounded (F := F) hS hw n lo hi (ρ / lo)
  obtain ⟨DA, hDA, hexp⟩ := uniformlyBoundedDerivs_exp hR hS hD hA hV n hn
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : StepVars F) (ρ / lo)).exists_bound_of_continuousOn
    (f := fun ζ => Real.exp (-q ζ)) (by fun_prop)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Metric.mem_closedBall_self (by positivity)))
  set H : StepVars F → ℝ → ℝ := fun ζ l => e l ζ * Real.exp (A l ζ V) * Real.exp (-q ζ) with hH
  set D₁ : ℝ := 2 ^ n * (2 ^ n * De * DA) * M with hD₁
  have hD₁0 : 0 ≤ D₁ := by positivity
  have hHas : ∀ ζ ∈ Bd, UniformlyBoundedDerivs n D₁ (admissibleScales ρ lo hi ζ) (H ζ) := by
    intro ζ hζ
    have h1 := hR.mul n De DA _ _ _ hDe hDA (he ζ) (hexp ζ)
    have h2 := hR.const n (admissibleScales ρ lo hi ζ) (Real.exp (-q ζ))
    have h3 := hR.mul n _ _ _ _ _ (by positivity) (abs_nonneg _) h1 h2
    refine hR.mono n _ _ _ _ ?_ h3
    have h4 : |Real.exp (-q ζ)| ≤ M := by simpa using hM ζ hζ
    exact mul_le_mul_of_nonneg_left h4 (by positivity)
  set Q : ℝ → StepVars F → ℝ := fun l ζ =>
    (admissibleScales ρ lo hi ζ).indicator (fun l' => H ζ l' * scaledCutoff w l' ζ) l with hQ
  have hQhas : ∀ ζ ∈ Bd, UniformlyBoundedDerivs n (2 ^ n * D₁ * B) (Ioo lo hi) fun l => Q l ζ := by
    intro ζ hζ
    have hζn : ‖ζ‖ ≤ ρ / lo := by simpa [hBd] using hζ
    refine hR.indicator_mul_flat n D₁ B _ _ (H ζ) _ (isOpen_admissibleScales ρ lo hi ζ)
      (admissibleScales_subset_Ioo ρ lo hi ζ) hD₁0 hB0
      (contDiff_scaledCutoff hw ζ) (fun x hx j => ?_) (fun j hj x hx => hB j hj x hx ζ hζn) (hHas ζ hζ)
    have hx0 : 0 < x := hlo.trans hx.1.1
    have hnot : ¬ MemScaledBalls ρ x ζ := fun h => hx.2 ⟨hx.1.1, hx.1.2, h⟩
    exact iteratedDeriv_eq_zero_of_eq_zero_right (contDiff_scaledCutoff hw ζ)
      (scaledCutoff_eq_zero hx0 hw0 hnot) j
  have hmeasB : MeasurableSet Bd := Metric.isClosed_closedBall.measurableSet
  have hQball : ∀ l, lo < l → l < hi → ∀ ζ, Q l ζ =
      (scaledBalls F ρ l).indicator (fun ζ => H ζ l * scaledCutoff w l ζ) ζ := by
    intro l h1 h2 ζ
    by_cases hζ : ζ ∈ scaledBalls F ρ l
    · rw [indicator_of_mem hζ]
      simp only [hQ]
      rw [indicator_of_mem (show l ∈ admissibleScales ρ lo hi ζ from ⟨h1, h2, hζ⟩)]
    · rw [indicator_of_notMem hζ]
      simp only [hQ]
      exact indicator_of_notMem (fun h => hζ h.2.2) _
  have hfin : IsFiniteMeasure ((volume : Measure (StepVars F)).restrict Bd) :=
    ⟨by simpa using (isCompact_closedBall (0 : StepVars F) (ρ / lo)).measure_lt_top⟩
  have hmeas : ∀ l ∈ Ioo lo hi, AEStronglyMeasurable (Q l) ((volume : Measure (StepVars F)).restrict Bd) := by
    intro l hl
    have hcont : ContinuousOn (fun ζ => H ζ l * scaledCutoff w l ζ) (scaledBalls F ρ l) := by
      have hAc : ContinuousOn (fun ζ => A l ζ V) (scaledBalls F ρ l) := by
        have := continuousOn_bondDeriv hS hA hV hl.1 hl.2 (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
          (Fin.elim0 : Fin 0 → imaginaryQuaternions) (by omega)
        simpa only [bondDeriv_fin_zero] using this
      exact (((hc l hl.1 hl.2).mul hAc.rexp).mul (by fun_prop)).mul
        (continuous_scaledCutoff hw.continuous l).continuousOn
    have hmb : MeasurableSet (scaledBalls F ρ l) := (isOpen_scaledBalls ρ l).measurableSet
    have h1 : AEStronglyMeasurable ((scaledBalls F ρ l).indicator fun ζ => H ζ l * scaledCutoff w l ζ)
        (volume : Measure (StepVars F)) :=
      (aestronglyMeasurable_indicator_iff hmb).2 (hcont.aestronglyMeasurable hmb)
    have h2 : Q l = (scaledBalls F ρ l).indicator fun ζ => H ζ l * scaledCutoff w l ζ :=
      funext (hQball l hl.1 hl.2)
    rw [h2]
    exact h1.restrict
  have hint := hR.integral (StepVars F) ((volume : Measure (StepVars F)).restrict Bd) n (2 ^ n * D₁ * B)
    (Ioo lo hi) Q isOpen_Ioo ((ae_restrict_iff' hmeasB).2 (Eventually.of_forall hQhas)) hmeas
  have hcd := (hR.contDiffOn n _ _ _ isOpen_Ioo hint).contDiffAt (Ioo_mem_nhds ha1 ha2)
  refine hcd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ha1 ha2] with l hl
  have hsub := scaledBalls_subset_closedBall (F := F) hρ hlo hl.1
  have hpt : ∀ ζ, Q l ζ = e l ζ * tiltedWeight w q A l V ζ := by
    intro ζ
    rw [hQball l hl.1 hl.2]
    by_cases hζ : ζ ∈ scaledBalls F ρ l
    · rw [indicator_of_mem hζ]
      simp only [hH, tiltedWeight]
      ring
    · rw [indicator_of_notMem hζ]
      simp only [tiltedWeight]
      rw [scaledCutoff_eq_zero (hlo.trans hl.1) hw0 hζ l le_rfl]
      ring
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_congr_ae (Eventually.of_forall hpt) |>.symm ▸ rfl
  · intro ζ hζ
    rw [hQball l hl.1 hl.2, indicator_of_notMem (fun h => hζ (hsub h))]
theorem uniformlyBoundedDerivs_blockProd (hR : ClosureProperties) (hS : IteratedFDerivSlices)
    {s ρ lo hi D : ℝ} {A Ob : ℝ → StepVars F → F.GaugeField F.top → ℝ} {V : F.GaugeField F.top} (hD : 0 ≤ D)
    (hA : IsTameOnScales s ρ lo hi D A) (hOb : IsTameOnScales s ρ lo hi D Ob) (hV : IsSmallCurvature s V)
    {k n : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X)
    (hk : k ≤ 3) (hn : n = if k = 3 then 2 else 3) (hn3 : n ≤ 3)
    (I : Finset (Fin k)) (J : Finset (Option (Finset (Fin k)))) :
    ∃ De : ℝ, 0 ≤ De ∧ (∀ ζ : StepVars F, UniformlyBoundedDerivs n De (admissibleScales ρ lo hi ζ) fun l =>
        blockProd (cumulantEntries A Ob l V c X I) J ζ) ∧
      ∀ l, lo < l → l < hi →
        ContinuousOn (blockProd (cumulantEntries A Ob l V c X I) J) (scaledBalls F ρ l) := by
  classical
  have hcard : ∀ J' : Finset (Fin k), J'.card ≤ k := fun J' => by simpa using Finset.card_le_univ J'
  have hent : ∀ o : Option (Finset (Fin k)),
      (∀ ζ : StepVars F, UniformlyBoundedDerivs n D (admissibleScales ρ lo hi ζ) fun l =>
        cumulantEntries A Ob l V c X I o ζ) ∧
      ∀ l, lo < l → l < hi → ContinuousOn (cumulantEntries A Ob l V c X I o) (scaledBalls F ρ l) := by
    intro o
    cases o with
    | none =>
      exact ⟨fun ζ => uniformlyBoundedDerivs_bondDeriv hR hS hOb hV _ _ (fun i => hX _) n
          ((hcard I).trans hk) hn3 (isControlledOrder_of_le hk hn (hcard I)) ζ,
        fun l h1 h2 => continuousOn_bondDeriv hS hOb hV h1 h2 _ _ ((hcard I).trans hk)⟩
    | some J' =>
      exact ⟨fun ζ => uniformlyBoundedDerivs_bondDeriv hR hS hA hV _ _ (fun i => hX _) n
          ((hcard J').trans hk) hn3 (isControlledOrder_of_le hk hn (hcard J')) ζ,
        fun l h1 h2 => continuousOn_bondDeriv hS hA hV h1 h2 _ _ ((hcard J').trans hk)⟩
  induction J using Finset.induction_on with
  | empty =>
    refine ⟨1, zero_le_one, fun ζ => ?_, fun l _ _ => ?_⟩
    · have := hR.const n (admissibleScales ρ lo hi ζ) 1
      simpa [blockProd] using this
    · have e : blockProd (cumulantEntries A Ob l V c X I) ∅ = fun _ => (1 : ℝ) := by
        funext ζ
        simp [blockProd]
      rw [e]
      exact continuousOn_const
  | insert o J ho ih =>
    obtain ⟨De, h0, h1, h2⟩ := ih
    refine ⟨2 ^ n * D * De, by positivity, fun ζ => ?_, fun l hl1 hl2 => ?_⟩
    · have := hR.mul n D De _ _ _ hD h0 ((hent o).1 ζ) (h1 ζ)
      simpa only [blockProd, Finset.prod_insert ho] using this
    · have := ((hent o).2 l hl1 hl2).mul (h2 l hl1 hl2)
      have e : blockProd (cumulantEntries A Ob l V c X I) (insert o J) =
          fun ζ => cumulantEntries A Ob l V c X I o ζ * blockProd (cumulantEntries A Ob l V c X I) J ζ := by
        funext ζ
        simp only [blockProd, Finset.prod_insert ho]
      rw [e]
      exact this
end TiltedMeanSmoothness
open TiltedMeanSmoothness in
theorem tiltedMeanDerivSmoothInScale_holds (hR : closureProperties_statement) (hS : IteratedFDerivSlices)
    (hC : tiltedMeanDerivEqCumulantsStatement) : TiltedMeanDerivSmoothInScale := by
  intro F s ρ lo hi D a w q A Ob V k c X hF hρ hlo ha1 ha2 hD hw hwp hw0 hq hA hOb hV hX hk
  classical
  obtain ⟨n, hn, hn3, hcast⟩ : ∃ n : ℕ, n = (if k = 3 then 2 else 3) ∧ n ≤ 3 ∧
      (if k = 3 then (2 : WithTop ℕ∞) else 3) = (n : WithTop ℕ∞) := by
    by_cases h3 : k = 3
    · exact ⟨2, by simp [h3], by omega, by simp [h3]⟩
    · exact ⟨3, by simp [h3], by omega, by simp [h3]⟩
  rw [hcast]
  have hden : ContDiffAt ℝ n (fun l => ∫ ζ, tiltedWeight w q A l V ζ) a := by
    have h := contDiffAt_integral_tiltedWeight hR hS hρ hlo ha1 ha2 hD hw hw0 hq hA hV n hn3
      (fun _ _ => 1) 1 zero_le_one
      (fun ζ => by
        have := hR.const n (admissibleScales ρ lo hi ζ) 1
        simpa using this)
      (fun l _ _ => continuousOn_const)
    simpa only [one_mul] using h
  have hpos := (hC F s ρ lo hi D a w q A Ob V k c X hF hρ hlo ha1 ha2 hD hw hwp hw0 hq hA hOb hV hX hk).1
  have hterm : ∀ (I : Finset (Fin k)) (J : Finset (Option (Finset (Fin k)))),
      ContDiffAt ℝ n (fun l => tiltedAverage w q A l V (blockProd (cumulantEntries A Ob l V c X I) J)) a := by
    intro I J
    obtain ⟨De, h0, h1, h2⟩ := uniformlyBoundedDerivs_blockProd hR hS hD hA hOb hV c X hX hk hn hn3 I J
    have hnum := contDiffAt_integral_tiltedWeight hR hS hρ hlo ha1 ha2 hD hw hw0 hq hA hV n hn3
      (fun l => blockProd (cumulantEntries A Ob l V c X I) J) De h0 h1 h2
    exact hnum.div hden hpos.ne'
  have hall : ContDiffAt ℝ n (fun l => ∑ I ∈ (Finset.univ : Finset (Fin k)).powerset,
      ∑ π : Finpartition (Finset.univ \ I),
        jointCumulant (tiltedAverage w q A l V) (insert none (π.parts.image some))
          (cumulantEntries A Ob l V c X I)) a := by
    refine ContDiffAt.sum fun I _ => ContDiffAt.sum fun π _ => ?_
    unfold jointCumulant
    refine ContDiffAt.sum fun π' _ => contDiffAt_const.mul ?_
    exact contDiffAt_prod fun J _ => hterm I J
  refine hall.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ha1 ha2] with l hl
  exact (hC F s ρ lo hi D l w q A Ob V k c X hF hρ hlo hl.1 hl.2 hD hw hwp hw0 hq hA hOb hV hX hk).2
end ScaledVariables
end YangMills.Construction
end
