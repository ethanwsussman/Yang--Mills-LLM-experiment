import YangMills.Construction.SummableBoundsOfTheFlow.MeanOfATameObservableProof
import YangMills.Construction.ColdStepAtMirrorFrames.PlainChainAtLevelZeroProof
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongAMoveNearATop
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongParametersIsASumOfCumulants
import YangMills.Construction.SummableBoundsOfTheFlow.SlicesOfASmoothFunction
import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessOfTheDensitiesIsSmallProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheTopDerivativesOfATameMeanAreCumulants
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages hiding bondSpread
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.DensityMeans YangMills.Construction.Cumulants MeasureTheory Set Filter
open scoped Topology
namespace YangMills.Construction.ScaledVariables
namespace TiltedMeanCumulantAux
variable {F : BlockFrame}
abbrev StepVars (F : BlockFrame) : Type := StepVariable (finiteCells F)
theorem leftTranslate_bondSpread_zero {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (W : F.GaugeField j) :
    leftTranslate (bondSpread c X 0) W = W := by apply _root_.YangMills.SharedProofs.p1939 <;> assumption
theorem eventually_isSmallCurvature_bondSpread {k : ℕ} (hF : ∀ i, F.extent i ≠ 0) (s : ℝ)
    (V : F.GaugeField F.top) (hV : IsSmallCurvature s V) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by apply _root_.YangMills.SharedProofs.p8866 <;> assumption
theorem bondDeriv_fin_zero {j : ℕ} (g : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : Fin 0 → F.Site j × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv g W c X = g W := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
def scaledBalls (F : BlockFrame) (ρ l : ℝ) : Set (StepVars F) := {ζ | MemScaledBalls ρ l ζ}
theorem isOpen_scaledBalls (ρ l : ℝ) : IsOpen (scaledBalls F ρ l) := by apply _root_.YangMills.Construction.ScaledVariables.TiltedMeanSmoothness.isOpen_scaledBalls <;> assumption
theorem scaledBalls_subset_closedBall {ρ lo l : ℝ} (hρ : 0 < ρ) (hlo : 0 < lo) (hl : lo < l) :
    scaledBalls F ρ l ⊆ Metric.closedBall (0 : StepVars F) (ρ / lo) := by apply _root_.YangMills.Construction.ScaledVariables.TiltedMeanSmoothness.scaledBalls_subset_closedBall <;> assumption
theorem continuousOn_bondDeriv (hS : SmoothSlices.IteratedFDerivSlices) {s ρ lo hi D : ℝ}
    {O : ℝ → StepVars F → F.GaugeField F.top → ℝ} (hO : IsTameOnScales s ρ lo hi D O) {V' : F.GaugeField F.top}
    (hV : IsSmallCurvature s V') {l : ℝ} (h1 : lo < l) (h2 : l < hi) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3) :
    ContinuousOn (fun ζ => bondDeriv (O l ζ) V' c X) (scaledBalls F ρ l) := by apply _root_.YangMills.Construction.ScaledVariables.TiltedMeanSmoothness.continuousOn_bondDeriv <;> assumption
theorem continuousOn_value (hS : SmoothSlices.IteratedFDerivSlices) {s ρ lo hi D : ℝ}
    {O : ℝ → StepVars F → F.GaugeField F.top → ℝ} (hO : IsTameOnScales s ρ lo hi D O) {V' : F.GaugeField F.top}
    (hV : IsSmallCurvature s V') {l : ℝ} (h1 : lo < l) (h2 : l < hi) :
    ContinuousOn (fun ζ => O l ζ V') (scaledBalls F ρ l) := by
  have := continuousOn_bondDeriv hS hO hV h1 h2 (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
    (Fin.elim0 : Fin 0 → imaginaryQuaternions) (by omega)
  simpa only [bondDeriv_fin_zero] using this
theorem iteratedFDeriv_single_eq_bondDeriv (hS : SmoothSlices.IteratedFDerivSlices) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (V : F.GaugeField F.top) (g : F.GaugeField F.top → ℝ) (I : Finset (Fin k))
    (h : ContDiffAt ℝ (I.card : ℕ) (fun τ : Fin k → ℝ => g (leftTranslate (bondSpread c X τ) V)) 0) :
    iteratedFDeriv ℝ I.card (fun τ : Fin k → ℝ => g (leftTranslate (bondSpread c X τ) V)) 0
        (fun j => Pi.single (I.orderEmbOfFin rfl j) 1) =
      bondDeriv g V (c ∘ I.orderEmbOfFin rfl) (X ∘ I.orderEmbOfFin rfl) := by
  classical
  set e := I.orderEmbOfFin rfl with he
  set L : (Fin I.card → ℝ) →L[ℝ] (Fin k → ℝ) := ∑ j, (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin I.card => ℝ) j).smulRight (Pi.single (e j) (1 : ℝ)) with hL
  have hLa : ∀ (σ : Fin I.card → ℝ) (l : Fin k), L σ l = ∑ j, if e j = l then σ j else 0 := by
    intro σ l
    simp only [hL, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : e j = l
    · simp [hj]
    · simp [hj, Ne.symm hj]
  have hLs : ∀ j, L (Pi.single j 1) = Pi.single (e j) 1 := by
    intro j
    funext l
    rw [hLa]
    by_cases hj : e j = l
    · subst hj
      rw [Finset.sum_eq_single j]
      · simp
      · intro j' _ hne
        have : e j' ≠ e j := fun h => hne (e.injective h)
        simp [this]
      · simp
    · rw [Pi.single_apply, if_neg (Ne.symm hj)]
      refine Finset.sum_eq_zero fun j' _ => ?_
      by_cases h' : e j' = l
      · have : j' ≠ j := fun hh => hj (hh ▸ h')
        rw [if_pos h', Pi.single_apply, if_neg this]
      · rw [if_neg h']
  have hsp : ∀ σ : Fin I.card → ℝ, bondSpread (c ∘ e) (X ∘ e) σ = bondSpread c X (L σ) := by
    intro σ
    funext y i
    unfold bondSpread
    have h1 : ∀ l : Fin k, (if c l = (y, i) then L σ l • X l else 0) =
        ∑ j, if e j = l then (if c l = (y, i) then σ j • X l else 0) else 0 := by
      intro l
      rw [hLa]
      by_cases hc : c l = (y, i)
      · simp only [hc, if_true, Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
      · simp [hc]
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Function.comp]
  have e1 := hS.1 (Fin k → ℝ) (Fin I.card → ℝ) (fun τ : Fin k → ℝ => g (leftTranslate (bondSpread c X τ) V))
    L 0 0 I.card (fun j => Pi.single j 1) (by simpa using h)
  simp only [zero_add, map_zero, hLs] at e1
  rw [← e1]
  unfold bondDeriv
  simp only [hsp]
theorem norm_iteratedFDeriv_exp_le {k : ℕ} {f : (Fin k → ℝ) → ℝ} {B : Set (Fin k → ℝ)} {M : ℝ} (hB : IsOpen B)
    (hf : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) f B) (hM : 1 ≤ M)
    (hb : ∀ τ ∈ B, ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i f τ‖ ≤ M) {τ : Fin k → ℝ} (hτ : τ ∈ B) {j : ℕ} (hj : j ≤ 3) :
    ‖iteratedFDeriv ℝ j (fun τ => Real.exp (f τ)) τ‖ ≤ 6 * Real.exp M * M ^ 3 := by
  have hg : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) Real.exp univ := Real.contDiff_exp.contDiffOn
  have hC : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i Real.exp univ (f τ)‖ ≤ Real.exp M := by
    intro i _
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
      Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
    have := hb τ hτ 0 (by omega)
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hD : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDerivWithin ℝ i f B τ‖ ≤ M ^ i := by
    intro i h1 h2
    rw [iteratedFDerivWithin_of_isOpen i hB hτ]
    exact (hb τ hτ i (by omega)).trans (le_self_pow₀ hM (by omega))
  have h := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (N := ((3 : ℕ) : WithTop ℕ∞)) hg hf
    (by exact_mod_cast hj) uniqueDiffOn_univ hB.uniqueDiffOn (mapsTo_univ _ _) hτ hC hD
  rw [iteratedFDerivWithin_of_isOpen j hB hτ] at h
  have hf6 : ((j.factorial : ℕ) : ℝ) ≤ 6 := by
    have : j.factorial ≤ Nat.factorial 3 := Nat.factorial_le hj
    have h6 : Nat.factorial 3 = 6 := rfl
    exact_mod_cast h6 ▸ this
  have hMj : M ^ j ≤ M ^ 3 := pow_le_pow_right₀ hM hj
  calc _ ≤ (j.factorial : ℝ) * Real.exp M * M ^ j := h
    _ ≤ 6 * Real.exp M * M ^ 3 := by gcongr
theorem continuous_scaledCutoff {w : ℝ → ℝ} (hw : Continuous w) (l : ℝ) :
    Continuous fun ζ : StepVars F => scaledCutoff w l ζ := by apply _root_.YangMills.Construction.ScaledVariables.TiltedMeanSmoothness.continuous_scaledCutoff <;> assumption
theorem scaledCutoff_eq_zero {w : ℝ → ℝ} {ρ x : ℝ} (h0 : ∀ u, ρ ≤ u → w u = 0) {ζ : StepVars F}
    (hζ : ¬ MemScaledBalls ρ x ζ) : scaledCutoff w x ζ = 0 := by
  unfold MemScaledBalls at hζ
  simp only [not_forall, not_lt] at hζ
  obtain ⟨b, hb⟩ := hζ
  unfold scaledCutoff
  exact Finset.prod_eq_zero (Finset.mem_univ b) (h0 _ hb)
theorem card_le_of_fin {k : ℕ} (J : Finset (Fin k)) : J.card ≤ k := by
  simpa using Finset.card_le_univ J
theorem abs_bondDeriv_le {s ρ lo hi D : ℝ} {O : ℝ → StepVars F → F.GaugeField F.top → ℝ}
    (hO : IsTameOnScales s ρ lo hi D O)
    {V' : F.GaugeField F.top} (hV : IsSmallCurvature s V') {l : ℝ} (h1 : lo < l) (h2 : l < hi) {ζ : StepVars F}
    (hζ : MemScaledBalls ρ l ζ) {m : ℕ} (c : Fin m → F.Site F.top × Fin 4) (X : Fin m → imaginaryQuaternions)
    (hX : AreUnitVectors X) (hm : m ≤ 3) : |bondDeriv (O l ζ) V' c X| ≤ D := by
  have := hO.deriv_le V' hV m 0 c X l ζ (Or.inl ⟨hm, by omega⟩) hX h1 h2 hζ
  simpa [scaleDeriv] using this
end TiltedMeanCumulantAux
open TiltedMeanCumulantAux in
theorem tiltedMeanDerivEqCumulants (hM : DensityMeans.DensityMeanCumulantExpansion)
    (hN : Estimates.ContDiffBoundOnParameterBall) (hS : SmoothSlices.IteratedFDerivSlices) :
    tiltedMeanDerivEqCumulantsStatement := by
  intro F s ρ lo hi D l w q A Ob V k c X hF hρ hlo hl1 hl2 hD hw hwp hw0 hq hA hOb hV hX hk
  classical
  have hwn : ∀ u, 0 ≤ w u := fun u => by
    by_cases h : u < ρ
    · exact (hwp u h).le
    · exact (hw0 u (not_lt.1 h)).ge
  set wt : StepVars F → ℝ := fun ζ => scaledCutoff w l ζ * Real.exp (-q ζ) with hwt
  have hwtc : Continuous wt := (continuous_scaledCutoff hw.continuous l).mul (by fun_prop)
  have hwt0 : ∀ ζ, 0 ≤ wt ζ := fun ζ =>
    mul_nonneg (Finset.prod_nonneg fun b _ => hwn _) (Real.exp_pos _).le
  set R : Set (StepVars F) := scaledBalls F ρ l with hR
  have hRo : IsOpen R := isOpen_scaledBalls ρ l
  have hRm : MeasurableSet R := hRo.measurableSet
  have hwtz : ∀ ζ, ζ ∉ R → wt ζ = 0 := fun ζ hζ => by
    simp only [hwt]
    rw [scaledCutoff_eq_zero hw0 hζ, zero_mul]
  have hwtp : ∀ ζ ∈ R, 0 < wt ζ := fun ζ hζ =>
    mul_pos (Finset.prod_pos fun b _ => hwp _ (hζ b)) (Real.exp_pos _)
  have hRsub : R ⊆ Metric.closedBall (0 : StepVars F) (ρ / lo) := scaledBalls_subset_closedBall hρ hlo hl1
  have hvolR : (volume : Measure (StepVars F)) R < ⊤ :=
    (measure_mono hRsub).trans_lt (isCompact_closedBall _ _).measure_lt_top
  have hfinR : IsFiniteMeasure ((volume : Measure (StepVars F)).restrict R) := ⟨by simpa using hvolR⟩
  obtain ⟨Bw, hBw⟩ :=
    (isCompact_closedBall (0 : StepVars F) (ρ / lo)).exists_bound_of_continuousOn hwtc.continuousOn
  set μ : Measure (StepVars F) :=
    ((volume : Measure (StepVars F)).restrict R).withDensity fun ζ => ENNReal.ofReal (wt ζ) with hμ
  have hfin : IsFiniteMeasure μ := by
    refine isFiniteMeasure_withDensity_ofReal (HasFiniteIntegral.of_bounded (C := Bw) ?_)
    filter_upwards [ae_restrict_mem hRm] with ζ hζ using hBw ζ (hRsub hζ)
  have hint : ∀ g : StepVars F → ℝ, ∫ ζ, g ζ ∂μ = ∫ ζ, wt ζ * g ζ := by
    intro g
    have h1 : Measurable fun ζ => Real.toNNReal (wt ζ) := hwtc.measurable.real_toNNReal
    have h2 := integral_withDensity_eq_integral_smul (μ := (volume : Measure (StepVars F)).restrict R) h1 g
    have h3 : ∫ ζ, g ζ ∂μ =
        ∫ ζ, Real.toNNReal (wt ζ) • g ζ ∂((volume : Measure (StepVars F)).restrict R) := h2
    rw [h3]
    have h4 : ∀ ζ, Real.toNNReal (wt ζ) • g ζ = wt ζ * g ζ := fun ζ => by
      rw [NNReal.smul_def, Real.coe_toNNReal _ (hwt0 ζ), smul_eq_mul]
    simp only [h4]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun ζ hζ => by rw [hwtz ζ hζ, zero_mul]
  have hac : μ ≪ (volume : Measure (StepVars F)).restrict R := withDensity_absolutelyContinuous _ _
  have hae : ∀ᵐ ζ ∂μ, ζ ∈ R := hac.ae_le (ae_restrict_mem hRm)
  obtain ⟨r₀, C, hr₀, hC, hnear⟩ := hN F F.top k c X
  obtain ⟨ε, hε, hcold⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_isSmallCurvature_bondSpread hF s V hV c X)
  set r : ℝ := min r₀ ε with hr
  have hr0 : 0 < r := lt_min hr₀ hε
  set B : Set (Fin k → ℝ) := Metric.ball (0 : Fin k → ℝ) r with hB
  have hBo : IsOpen B := Metric.isOpen_ball
  have h0B : (0 : Fin k → ℝ) ∈ B := Metric.mem_ball_self hr0
  set Vt : (Fin k → ℝ) → F.GaugeField F.top := fun τ => leftTranslate (bondSpread c X τ) V with hVt
  have hVt0 : Vt 0 = V := leftTranslate_bondSpread_zero c X V
  have hcoldB : ∀ τ ∈ B, IsSmallCurvature s (Vt τ) := fun τ hτ =>
    hcold τ (Metric.ball_subset_ball (min_le_right _ _) hτ)
  have hnearO : ∀ O : ℝ → StepVars F → F.GaugeField F.top → ℝ, IsTameOnScales s ρ lo hi D O → ∀ ζ ∈ R,
      ContDiffOn ℝ 3 (fun τ => O l ζ (Vt τ)) B ∧
        ∀ τ ∈ B, ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i (fun τ => O l ζ (Vt τ)) τ‖ ≤ C * D := by
    intro O hO ζ hζ
    refine hnear r hr0 (min_le_left _ _) V (O l ζ) D hD (fun τ hτ m c' X' _ => ?_)
      (fun τ hτ i c' X' hi hX' => abs_bondDeriv_le hO (hcoldB τ hτ) hl1 hl2 hζ c' X' hX' hi)
    have h6 := hO.contDiffAt (Vt τ) (hcoldB τ hτ) l ζ m c' X' hl1 hl2 hζ
    have h7 := ContDiffAt.comp (f := fun σ : Fin m → ℝ => ((l, ζ), σ)) (0 : Fin m → ℝ) h6
      ((contDiff_const.prodMk contDiff_id).contDiffAt)
    exact h7.of_le (by norm_num)
  set G : (Fin k → ℝ) → StepVars F → ℝ := fun τ ζ => Ob l ζ (Vt τ) with hG
  set Z : (Fin k → ℝ) → StepVars F → ℝ := fun τ ζ => Real.exp (A l ζ (Vt τ)) with hZ
  have hk3 : ((k : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have hGd : IsDominatedSmoothFamily μ k B (C * D) G := by
    refine ⟨fun τ hτ => ?_, ?_, ?_⟩
    · exact ((continuousOn_value hS hOb (hcoldB τ hτ) hl1 hl2).aestronglyMeasurable hRm).mono_ac hac
    · filter_upwards [hae] with ζ hζ
      exact (hnearO Ob hOb ζ hζ).1.of_le hk3
    · filter_upwards [hae] with ζ hζ j hj τ hτ
      exact (hnearO Ob hOb ζ hζ).2 τ hτ j (hj.trans hk)
  set M : ℝ := C * D + 1 with hMdef
  have hCD : 0 ≤ C * D := mul_nonneg hC hD
  have hM1 : 1 ≤ M := by simp only [hMdef]; linarith
  set tw : StepVars F → ℝ := tiltedWeight w q A l V with htw
  have htw_eq : ∀ ζ, tw ζ = wt ζ * Real.exp (A l ζ V) := fun ζ => rfl
  have htw0 : ∀ ζ, 0 ≤ tw ζ := fun ζ => by
    rw [htw_eq]
    exact mul_nonneg (hwt0 ζ) (Real.exp_pos _).le
  have hAc : ContinuousOn (fun ζ => A l ζ V) R := continuousOn_value hS hA hV hl1 hl2
  have hsupp : Function.support tw ⊆ R := by
    intro ζ hζ
    by_contra hn
    exact hζ (by rw [htw_eq, hwtz ζ hn, zero_mul])
  have htwc : ContinuousOn tw R := hwtc.continuousOn.mul hAc.rexp
  have hAb : ∀ ζ ∈ R, |A l ζ V| ≤ D := fun ζ hζ => by
    have := abs_bondDeriv_le hA hV hl1 hl2 hζ (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
      (Fin.elim0 : Fin 0 → imaginaryQuaternions) (fun i => i.elim0) (by omega)
    rwa [bondDeriv_fin_zero] at this
  have htwi : Integrable tw (volume : Measure (StepVars F)) := by
    refine (integrableOn_iff_integrable_of_support_subset hsupp).1 ?_
    refine Integrable.of_bound (htwc.aestronglyMeasurable hRm) (Bw * Real.exp D) ?_
    filter_upwards [ae_restrict_mem hRm] with ζ hζ
    rw [htw_eq, norm_mul]
    have h1 : ‖wt ζ‖ ≤ Bw := hBw ζ (hRsub hζ)
    have h2 : ‖Real.exp (A l ζ V)‖ ≤ Real.exp D := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 ((le_abs_self _).trans (hAb ζ hζ))
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  have hpos : 0 < ∫ ζ, tw ζ := by
    refine (integral_pos_iff_support_of_nonneg htw0 htwi).2 ?_
    have h0R : (0 : StepVars F) ∈ R := fun b => by simpa using hρ
    have h1 : 0 < (volume : Measure (StepVars F)) R := hRo.measure_pos _ ⟨0, h0R⟩
    refine h1.trans_le (measure_mono fun ζ hζ => ?_)
    rw [Function.mem_support, htw_eq]
    exact (mul_pos (hwtp ζ hζ) (Real.exp_pos _)).ne'
  have hZ0 : ∀ ζ, Z 0 ζ = Real.exp (A l ζ V) := fun ζ => by
    simp only [hZ, hVt0]
  have hlog : ∀ J : Finset (Fin k), ∀ ζ ∈ R, mixedDerivAt (logDensity Z) J ζ =
      bondDeriv (A l ζ) V (c ∘ J.orderEmbOfFin rfl) (X ∘ J.orderEmbOfFin rfl) := by
    intro J ζ hζ
    have e1 : (fun τ => logDensity Z τ ζ) = fun τ => A l ζ (Vt τ) := by
      funext τ
      simp [logDensity, hZ, Real.log_exp]
    unfold mixedDerivAt
    rw [e1]
    exact iteratedFDeriv_single_eq_bondDeriv hS c X V (A l ζ) J
      (((hnearO A hA ζ hζ).1.contDiffAt (hBo.mem_nhds h0B)).of_le
        (by exact_mod_cast (card_le_of_fin J).trans hk))
  have hZd : IsFlatDensity μ B (6 * Real.exp M * M ^ 3) Z := by
    refine ⟨⟨fun τ hτ => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · exact ((continuousOn_value hS hA (hcoldB τ hτ) hl1 hl2).rexp.aestronglyMeasurable hRm).mono_ac hac
    · filter_upwards [hae] with ζ hζ
      exact ((hnearO A hA ζ hζ).1.exp).of_le hk3
    · filter_upwards [hae] with ζ hζ j hj τ hτ
      exact norm_iteratedFDeriv_exp_le hBo (by exact_mod_cast (hnearO A hA ζ hζ).1) hM1
        (fun τ' hτ' i hi => ((hnearO A hA ζ hζ).2 τ' hτ' i hi).trans (by simp only [hMdef]; linarith))
        hτ (hj.trans hk)
    · exact Eventually.of_forall fun ζ τ _ => (Real.exp_pos _).le
    · exact Eventually.of_forall fun ζ τ _ h => absurd h (Real.exp_pos _).ne'
    · rw [hint]
      have : ∀ ζ, wt ζ * Z 0 ζ = tw ζ := fun ζ => by rw [hZ0, htw_eq]
      simp only [this]
      exact hpos
    · intro S π
      set fc : StepVars F → ℝ := fun ζ => (∏ J ∈ π.parts,
        bondDeriv (A l ζ) V (c ∘ J.orderEmbOfFin rfl) (X ∘ J.orderEmbOfFin rfl)) * Real.exp (A l ζ V) with hfcd
      have hfc : ContinuousOn fc R :=
        (continuousOn_finsetProd _ fun J _ =>
          continuousOn_bondDeriv hS hA hV hl1 hl2 _ _ ((card_le_of_fin J).trans hk)).mul hAc.rexp
      have hb : ∀ ζ ∈ R, ‖fc ζ‖ ≤ D ^ π.parts.card * Real.exp D := by
        intro ζ hζ
        rw [hfcd]
        simp only
        rw [norm_mul, norm_prod]
        have h1 : ∏ J ∈ π.parts, ‖bondDeriv (A l ζ) V (c ∘ J.orderEmbOfFin rfl) (X ∘ J.orderEmbOfFin rfl)‖ ≤
            ∏ _J ∈ π.parts, D := Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun J _ =>
          abs_bondDeriv_le hA hV hl1 hl2 hζ _ _ (fun i => hX _) ((card_le_of_fin J).trans hk)
        rw [Finset.prod_const] at h1
        have h2 : ‖Real.exp (A l ζ V)‖ ≤ Real.exp D := by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.2 ((le_abs_self _).trans (hAb ζ hζ))
        exact mul_le_mul h1 h2 (norm_nonneg _) (pow_nonneg hD _)
      have hI : Integrable fc μ := Integrable.of_bound ((hfc.aestronglyMeasurable hRm).mono_ac hac) _
        (by filter_upwards [hae] with ζ hζ using hb ζ hζ)
      refine hI.congr ?_
      filter_upwards [hae] with ζ hζ
      simp only [hfcd]
      rw [hZ0]
      congr 1
      exact Finset.prod_congr rfl fun J _ => (hlog J ζ hζ).symm
  obtain ⟨-, hform⟩ := hM (StepVars F) μ k B (C * D) (6 * Real.exp M * M ^ 3) G Z hBo h0B hGd hZd
  refine ⟨hpos, ?_⟩
  have hmeanEq : ∀ τ, tiltedMean w q A Ob l (Vt τ) = densityMean μ (Z τ) (G τ) := by
    intro τ
    unfold tiltedMean tiltedAverage densityMean
    rw [hint, hint]
    congr 1
    · refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
      simp only [tiltedWeight, hwt, hG, hZ]
      ring
  have hL : bondDeriv (tiltedMean w q A Ob l) V c X =
      iteratedFDeriv ℝ k (fun τ => densityMean μ (Z τ) (G τ)) 0 (fun i => Pi.single i 1) := by
    have e : (fun τ => tiltedMean w q A Ob l (Vt τ)) = fun τ => densityMean μ (Z τ) (G τ) := funext hmeanEq
    unfold bondDeriv
    exact congrArg (fun g => iteratedFDeriv ℝ k g 0 (fun i => Pi.single i 1)) e
  rw [hL, hform]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun π _ => ?_
  unfold jointCumulant
  refine Finset.sum_congr rfl fun π' _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun J _ => ?_
  have hent : ∀ ζ ∈ R, blockProd (cumulantEntry G Z I) J ζ = blockProd (cumulantEntries A Ob l V c X I) J ζ := by
    intro ζ hζ
    unfold blockProd
    refine Finset.prod_congr rfl fun o _ => ?_
    cases o with
    | none =>
      exact iteratedFDeriv_single_eq_bondDeriv hS c X V (Ob l ζ) I
        (((hnearO Ob hOb ζ hζ).1.contDiffAt (hBo.mem_nhds h0B)).of_le
          (by exact_mod_cast (card_le_of_fin I).trans hk))
    | some J' => exact hlog J' ζ hζ
  unfold densityMean tiltedAverage
  rw [hint, hint]
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    change wt ζ * (blockProd (cumulantEntry G Z I) J ζ * Z 0 ζ) =
      blockProd (cumulantEntries A Ob l V c X I) J ζ * tw ζ
    by_cases hζ : ζ ∈ R
    · rw [hent ζ hζ, hZ0, htw_eq]
      ring
    · rw [htw_eq, hwtz ζ hζ]
      ring
  · refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    change wt ζ * Z 0 ζ = tw ζ
    rw [hZ0, htw_eq]
end YangMills.Construction.ScaledVariables
end
