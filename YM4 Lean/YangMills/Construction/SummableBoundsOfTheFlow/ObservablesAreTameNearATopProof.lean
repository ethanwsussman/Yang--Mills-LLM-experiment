import YangMills.Construction.SummableBoundsOfTheFlow.MeanOfATameObservableProof
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongARotation
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfMeansConverge
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothObservablesOfTheStep
import Mathlib
import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessOfTheDensitiesIsSmallProof
set_option autoImplicit false

noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.GibbsMeans YangMills.Construction.ScaledVariables
namespace YangMills.Construction.ScaledVariables
variable {F : BlockFrame}
open Classical in
def observableOnScaledBalls (ρ : ℝ) (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    ℝ → (Fin k → ℝ) → StepVariable (finiteCells F) → ℝ :=
  fun l τ ζ => if MemScaledBalls ρ l ζ then Ob l ζ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) else 0
def SmoothObservablesModerateNearField : Prop :=
  ∀ (F : BlockFrame) (s κ ρ : ℝ) (V : F.GaugeField F.top) (k n : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions),
    (∀ i, F.extent i ≠ 0) → 0 ≤ κ → 0 < ρ → n ≤ 3 → IsSmallCurvature s V →
    ∃ r : ℝ, 0 < r ∧ (∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r,
      IsSmallCurvature s (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) ∧
      ∀ (l₁ K : ℝ) (Y : F.Cell) (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ),
      0 < l₁ → 0 ≤ K → IsSmoothAtSmallCurvature s κ ρ l₁ K Y Ob → ∀ r' : ℝ, 0 < r' → r' ≤ r →
      IsModerate l₁ (Metric.ball (0 : Fin k → ℝ) r') (fun ζ : StepVariable (finiteCells F) => 1 + ‖ζ‖) n
        (observableOnScaledBalls ρ Ob V c X)
end YangMills.Construction.ScaledVariables
end

noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages hiding bondSpread
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.GibbsMeans YangMills.Construction.IteratedDerivative YangMills.Construction.Estimates Set
namespace YangMills.Construction.ScaledVariables
variable {F : BlockFrame}
private theorem leftTranslate_bondSpread_zero {j k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (W : F.GaugeField j) :
    leftTranslate (bondSpread c X 0) W = W := by apply _root_.YangMills.SharedProofs.p1939 <;> assumption
private theorem eventually_isSmallCurvature_translate {k : ℕ} (hF : ∀ i, F.extent i ≠ 0) (s : ℝ)
    (V : F.GaugeField F.top) (hV : IsSmallCurvature s V) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by apply _root_.YangMills.SharedProofs.p8866 <;> assumption
private theorem isOpen_setOf_memScaledBalls (ρ l : ℝ) :
    IsOpen {ζ : StepVariable (finiteCells F) | MemScaledBalls ρ l ζ} := by apply _root_.YangMills.Construction.ScaledVariables.TiltedMeanSmoothness.isOpen_scaledBalls <;> assumption
abbrev _root_.YangMills.SharedProofs.p7210 := @isOpen_setOf_memScaledBalls
private theorem memScaledBalls_zero_scale {ρ : ℝ} (hρ : 0 < ρ) (ζ : StepVariable (finiteCells F)) :
    MemScaledBalls ρ 0 ζ := by
  intro b
  simpa using hρ
private theorem eventually_small_scale {ρ l₁ : ℝ} (hρ : 0 < ρ) (hl₁ : 0 < l₁) (ζ : StepVariable (finiteCells F)) :
    ∀ᶠ l in 𝓝[>] (0 : ℝ), 0 < l ∧ l ≤ l₁ ∧ MemScaledBalls ρ l ζ := by
  have hpos : 0 < 1 + ‖ζ‖ := by positivity
  have hb : 0 < min l₁ (ρ / (1 + ‖ζ‖)) := lt_min hl₁ (div_pos hρ hpos)
  filter_upwards [Ioo_mem_nhdsGT hb] with l hl
  refine ⟨hl.1, hl.2.le.trans (min_le_left _ _), fun b => ?_⟩
  have h1 : l < ρ / (1 + ‖ζ‖) := hl.2.trans_le (min_le_right _ _)
  have h2 : l * (1 + ‖ζ‖) < ρ := (lt_div_iff₀ hpos).1 h1
  have h3 : ‖ζ b‖ ≤ ‖ζ‖ := norm_le_pi_norm ζ b
  nlinarith [hl.1, norm_nonneg (ζ b)]
abbrev _root_.YangMills.SharedProofs.p125245 := @eventually_small_scale
private theorem localWeight_le_card_mul_norm {κ : ℝ} (hκ : 0 ≤ κ) (Y : F.Cell) (ζ : StepVariable (finiteCells F)) :
    localWeight κ Y ζ ≤ (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ) * ‖ζ‖ := by
  unfold localWeight
  calc ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(2 ^ 4 * κ * cellSupDist (enclosingCell b.1.1) Y)) * ‖ζ b‖
      ≤ ∑ _b : ↥(chordBonds (finiteCells F)), ‖ζ‖ := by
        refine Finset.sum_le_sum fun b _ => ?_
        have h1 : Real.exp (-(2 ^ 4 * κ * cellSupDist (enclosingCell b.1.1) Y)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : (0 : ℝ) ≤ 2 ^ 4 * κ * cellSupDist (enclosingCell b.1.1) Y := by positivity
          linarith
        calc Real.exp (-(2 ^ 4 * κ * cellSupDist (enclosingCell b.1.1) Y)) * ‖ζ b‖ ≤ 1 * ‖ζ b‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ ≤ ‖ζ‖ := by simpa using norm_le_pi_norm ζ b
    _ = (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ) * ‖ζ‖ := by simp
private def polynomialBound (F : BlockFrame) (K : ℝ) (ζ : StepVariable (finiteCells F)) : ℝ :=
  K * (1 + (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ)) ^ 7 * (1 + ‖ζ‖) ^ 7
private theorem abs_bondDeriv_le_of_pos {κ ρ l₁ K : ℝ} {Y : F.Cell}
    {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {V' : F.GaugeField F.top} (hκ : 0 ≤ κ) (hK : 0 ≤ K) (hO : IsSmoothObservable κ ρ l₁ K Y V' Ob) {q : ℕ}
    (c' : Fin q → F.Site F.top × Fin 4) (X' : Fin q → imaginaryQuaternions) (hq : q ≤ 3) (hX : AreUnitVectors X')
    {l : ℝ} (hl : 0 < l) (hll : l ≤ l₁) {ζ : StepVariable (finiteCells F)} (hζ : MemScaledBalls ρ l ζ) :
    |bondDeriv (Ob l ζ) V' c' X'| ≤ polynomialBound F K ζ := by
  have h := hO.deriv_le q 0 c' X' l ζ (Or.inl ⟨hq, Nat.zero_le 2⟩) hX hl hll hζ
  have e : scaleDeriv Ob V' c' X' 0 ζ l = bondDeriv (Ob l ζ) V' c' X' := by
    simp [scaleDeriv]
  rw [e] at h
  refine h.trans ?_
  have h1 : Real.exp (-(2 ^ 4 * κ * bondSpan Y c')) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ 2 ^ 4 * κ * bondSpan Y c' := by positivity
    linarith
  have hn0 : 0 ≤ localWeight κ Y ζ := by
    unfold localWeight
    exact Finset.sum_nonneg fun b _ => by positivity
  have h2 : 1 + localWeight κ Y ζ ≤ (1 + (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ)) * (1 + ‖ζ‖) := by
    have := localWeight_le_card_mul_norm hκ Y ζ
    nlinarith [norm_nonneg ζ]
  have h3 : (1 + localWeight κ Y ζ) ^ 7 ≤
      (1 + (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ)) ^ 7 * (1 + ‖ζ‖) ^ 7 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) h2 7
  unfold polynomialBound
  calc K * (1 + localWeight κ Y ζ) ^ 7 * Real.exp (-(2 ^ 4 * κ * bondSpan Y c'))
      ≤ K * (1 + localWeight κ Y ζ) ^ 7 * 1 :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hK (pow_nonneg (by linarith) 7))
    _ = K * (1 + localWeight κ Y ζ) ^ 7 := mul_one _
    _ ≤ K * ((1 + (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ)) ^ 7 * (1 + ‖ζ‖) ^ 7) :=
        mul_le_mul_of_nonneg_left h3 hK
    _ = _ := by ring
private theorem tendsto_bondDeriv_scale_zero {κ ρ l₁ K : ℝ} {Y : F.Cell}
    {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {V' : F.GaugeField F.top} (hρ : 0 < ρ) (hl₁ : 0 < l₁) (hO : IsSmoothObservable κ ρ l₁ K Y V' Ob) {q : ℕ}
    (c' : Fin q → F.Site F.top × Fin 4) (X' : Fin q → imaginaryQuaternions) (hq : q ≤ 3)
    (ζ : StepVariable (finiteCells F)) :
    Filter.Tendsto (fun l => bondDeriv (Ob l ζ) V' c' X') (𝓝[>] 0) (𝓝 (bondDeriv (Ob 0 ζ) V' c' X')) := by
  have hc := hO.continuousOn q 0 c' X' ‖ζ‖ (Or.inl ⟨hq, Nat.zero_le 2⟩)
  have hmem : ((0 : ℝ), ζ) ∈ {p : ℝ × StepVariable (finiteCells F) | 0 ≤ p.1 ∧ p.1 ≤ l₁ ∧
      MemScaledBalls ρ p.1 p.2 ∧ ∀ b, ‖p.2 b‖ ≤ ‖ζ‖} :=
    ⟨le_rfl, hl₁.le, memScaledBalls_zero_scale hρ ζ, fun b => norm_le_pi_norm ζ b⟩
  have hpath : Filter.Tendsto (fun l : ℝ => (l, ζ)) (𝓝[>] 0) (𝓝[{p : ℝ × StepVariable (finiteCells F) |
      0 ≤ p.1 ∧ p.1 ≤ l₁ ∧ MemScaledBalls ρ p.1 p.2 ∧ ∀ b, ‖p.2 b‖ ≤ ‖ζ‖}] ((0 : ℝ), ζ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((Continuous.prodMk continuous_id continuous_const).tendsto' 0 _ rfl).mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_small_scale hρ hl₁ ζ] with l hl
      exact ⟨hl.1.le, hl.2.1, hl.2.2, fun b => norm_le_pi_norm ζ b⟩
  have h := (hc _ hmem).tendsto.comp hpath
  simpa [scaleDeriv, Function.comp_def] using h
private theorem abs_bondDeriv_le_polynomialBound {κ ρ l₁ K : ℝ} {Y : F.Cell}
    {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {V' : F.GaugeField F.top} (hκ : 0 ≤ κ) (hρ : 0 < ρ) (hl₁ : 0 < l₁) (hK : 0 ≤ K)
    (hO : IsSmoothObservable κ ρ l₁ K Y V' Ob) {q : ℕ}
    (c' : Fin q → F.Site F.top × Fin 4) (X' : Fin q → imaginaryQuaternions) (hq : q ≤ 3) (hX : AreUnitVectors X')
    {l : ℝ} (hl : l ∈ Icc 0 l₁) {ζ : StepVariable (finiteCells F)} (hζ : MemScaledBalls ρ l ζ) :
    |bondDeriv (Ob l ζ) V' c' X'| ≤ polynomialBound F K ζ := by
  rcases hl.1.eq_or_lt with h0 | hpos
  · subst h0
    refine le_of_tendsto (tendsto_bondDeriv_scale_zero hρ hl₁ hO c' X' hq ζ).abs ?_
    filter_upwards [eventually_small_scale hρ hl₁ ζ] with l' hl'
    exact abs_bondDeriv_le_of_pos hκ hK hO c' X' hq hX hl'.1 hl'.2.1 hl'.2.2
  · exact abs_bondDeriv_le_of_pos hκ hK hO c' X' hq hX hpos hl.2 hζ
private theorem contDiffAt_observable_translate {κ ρ l₁ K : ℝ} {Y : F.Cell}
    {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {V' : F.GaugeField F.top} (hO : IsSmoothObservable κ ρ l₁ K Y V' Ob) {q : ℕ}
    (c' : Fin q → F.Site F.top × Fin 4) (X' : Fin q → imaginaryQuaternions) {l : ℝ} (hl : 0 ≤ l)
    {ζ : StepVariable (finiteCells F)} (hζ : MemScaledBalls ρ l ζ) :
    ContDiffAt ℝ 3 (fun v : Fin q → ℝ => Ob l ζ (leftTranslate (bondSpread c' X' v) V')) 0 := by
  have h := hO.contDiffAt l ζ q c' X' (by rwa [abs_of_nonneg hl])
  have h3 := h.of_le (m := 3) (by norm_num)
  exact ContDiffAt.comp (g := fun p : (ℝ × StepVariable (finiteCells F)) × (Fin q → ℝ) =>
      Ob p.1.1 p.1.2 (leftTranslate (bondSpread c' X' p.2) V')) (f := fun v : Fin q → ℝ => ((l, ζ), v)) 0 h3
    (contDiffAt_const.prodMk contDiffAt_id)
private theorem continuousOn_observable_scaledBalls {κ ρ l₁ K : ℝ} {Y : F.Cell}
    {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {V' : F.GaugeField F.top} (hO : IsSmoothObservable κ ρ l₁ K Y V' Ob) {l : ℝ} (hl : 0 ≤ l) :
    ContinuousOn (fun ζ => Ob l ζ V') {ζ | MemScaledBalls ρ l ζ} := by
  intro ζ hζ
  have h := hO.contDiffAt l ζ 0 Fin.elim0 Fin.elim0 (by rwa [abs_of_nonneg hl])
  have h1 := h.continuousAt
  have hz : ContinuousAt (fun ζ' : StepVariable (finiteCells F) => ((l, ζ'), (0 : Fin 0 → ℝ))) ζ := by fun_prop
  have h2 := ContinuousAt.comp (g := fun p : (ℝ × StepVariable (finiteCells F)) × (Fin 0 → ℝ) =>
      Ob p.1.1 p.1.2 (leftTranslate (bondSpread (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions) p.2) V'))
    (f := fun ζ' : StepVariable (finiteCells F) => ((l, ζ'), (0 : Fin 0 → ℝ))) (x := ζ) h1 hz
  have e : ∀ ζ' : StepVariable (finiteCells F), Ob l ζ' (leftTranslate (bondSpread
      (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
      (Fin.elim0 : Fin 0 → imaginaryQuaternions) (0 : Fin 0 → ℝ)) V') = Ob l ζ' V' := fun ζ' => by
    rw [leftTranslate_bondSpread_zero]
  simp only [Function.comp_def, e] at h2
  exact h2.continuousWithinAt
private def coordinateEmbedding {j k : ℕ} (m : Fin j → Fin k) : (Fin j → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin j → ℝ) →L[ℝ] ℝ).smulRight (Pi.single (m i) (1 : ℝ))
private theorem coordinateEmbedding_single {j k : ℕ} (m : Fin j → Fin k) (q : Fin j) :
    coordinateEmbedding m (Pi.single q 1) = Pi.single (m q) 1 := by
  simp [coordinateEmbedding, Pi.single_apply]
private theorem coordinateEmbedding_apply {j k : ℕ} (m : Fin j → Fin k) (v : Fin j → ℝ) (l : Fin k) :
    coordinateEmbedding m v l = ∑ q, if m q = l then v q else 0 := by
  simp [coordinateEmbedding, Finset.sum_apply, Pi.single_apply, eq_comm]
private theorem bondSpread_comp_eq {j k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (m : Fin j → Fin k) (v : Fin j → ℝ) :
    bondSpread (c ∘ m) (X ∘ m) v = bondSpread c X (coordinateEmbedding m v) := by
  funext y i
  simp only [bondSpread, Function.comp]
  calc ∑ q, (if c (m q) = (y, i) then v q • X (m q) else 0)
      = ∑ q, ∑ l, (if m q = l then (if c l = (y, i) then v q • X l else 0) else 0) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_ite_eq Finset.univ (m q)]
        simp
    _ = ∑ l, ∑ q, (if m q = l then (if c l = (y, i) then v q • X l else 0) else 0) := Finset.sum_comm
    _ = ∑ l, (if c l = (y, i) then coordinateEmbedding m v l • X l else 0) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [coordinateEmbedding_apply]
        split_ifs with h
        · rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun q _ => ?_
          split_ifs <;> simp
        · simp
private theorem iteratedFDeriv_single_eq_bondDeriv (hA : DerivAlongRulesHold) (G : F.GaugeField F.top → ℝ)
    (V : F.GaugeField F.top) {j k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (m : Fin j → Fin k)
    (hg : ContDiffAt ℝ j (fun τ => G (leftTranslate (bondSpread c X τ) V)) 0) :
    iteratedFDeriv ℝ j (fun τ => G (leftTranslate (bondSpread c X τ) V)) 0 (fun i => Pi.single (m i) 1) =
      bondDeriv G V (c ∘ m) (X ∘ m) := by
  let g : (Fin k → ℝ) → ℝ := fun τ => G (leftTranslate (bondSpread c X τ) V)
  have e : (fun v => G (leftTranslate (bondSpread (c ∘ m) (X ∘ m) v) V)) =
      fun v => g (0 + coordinateEmbedding m v) := by
    funext v
    simp [g, bondSpread_comp_eq]
  have e0 : (0 : Fin k → ℝ) + coordinateEmbedding m 0 = 0 := by simp
  have hg' : ContDiffAt ℝ j g 0 := hg
  have hgc : ContDiffAt ℝ j (fun v => g (0 + coordinateEmbedding m v)) 0 :=
    ContDiffAt.comp (g := g) (f := fun v => 0 + coordinateEmbedding m v) (0 : Fin j → ℝ)
      (by show ContDiffAt ℝ j g (0 + coordinateEmbedding m 0); rw [e0]; exact hg')
      (contDiff_const.add (coordinateEmbedding m).contDiff).contDiffAt
  let un : Fin j → (Fin j → ℝ) := fun l => Pi.single l 1
  have h2 := hA.2 (Fin k → ℝ) (Fin j → ℝ) ℝ g (coordinateEmbedding m) 0 0 (List.ofFn un)
    (by rw [e0, List.length_ofFn]; exact hg')
  unfold bondDeriv
  rw [e, (hA.1 _ _).iteratedFDeriv_eq _ _ j un hgc, h2, e0, List.map_ofFn]
  show iteratedFDeriv ℝ j g 0 _ = _
  rw [(hA.1 _ _).iteratedFDeriv_eq _ _ j _ hg']
  congr 2
  funext q
  simp [un, coordinateEmbedding_single]
theorem smoothObservablesModerateNearField_holds (hT : ContDiffBoundAlongTranslation)
    (hD : GibbsMeanDerivativesConverge) (hA : DerivAlongRulesHold) :
    SmoothObservablesModerateNearField := by
  intro F s κ ρ V k n c X hF hκ hρ hn hV
  have hper : ∀ i, F.period F.top i ≠ 0 := fun i => by simp [BlockFrame.period, hF i]
  obtain ⟨r₀, M, hr₀, hM₀, hB⟩ := hT F F.top k c X V hper
  obtain ⟨r₁, hr₁, hcold⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_isSmallCurvature_translate hF s V hV c X)
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, fun τ hτ => hcold τ (Metric.ball_subset_ball (min_le_right _ _) hτ),
    fun l₁ K Y Ob hl₁ hK hO r hr hle => ?_⟩
  have hcold' : ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r,
      IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := fun τ hτ =>
    hcold τ (Metric.ball_subset_ball (hle.trans (min_le_right _ _)) hτ)
  have hN : 0 ≤ K * (1 + (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ)) ^ 7 := by positivity
  have data : ∀ l ∈ Icc 0 l₁, ∀ ζ, MemScaledBalls ρ l ζ →
      ContDiffOn ℝ 3 (fun τ => Ob l ζ (leftTranslate (bondSpread c X τ) V)) (Metric.ball 0 r) ∧
      ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ (j : ℕ) (m : Fin j → Fin k), j ≤ 3 →
        |iteratedFDeriv ℝ j (fun τ' => Ob l ζ (leftTranslate (bondSpread c X τ') V)) τ
          fun i => Pi.single (m i) 1| ≤ M * polynomialBound F K ζ := by
    intro l hl ζ hζ
    refine hB r (Ob l ζ) (polynomialBound F K ζ) (hle.trans (min_le_left _ _)) ?_ fun τ hτ => ⟨?_, ?_⟩
    · unfold polynomialBound
      positivity
    · intro q c' X'
      exact contDiffAt_observable_translate (hO _ (hcold' τ hτ)) c' X' hl.1 hζ
    · intro q c' X' hq hX
      exact abs_bondDeriv_le_polynomialBound hκ hρ hl₁ hK (hO _ (hcold' τ hτ)) c' X' hq hX hl hζ
  have h0 : (0 : Fin k → ℝ) ∈ Metric.ball (0 : Fin k → ℝ) r := Metric.mem_ball_self hr
  have fam_pos : ∀ {l : ℝ} {ζ : StepVariable (finiteCells F)}, MemScaledBalls ρ l ζ →
      (fun τ => observableOnScaledBalls ρ Ob V c X l τ ζ) =
        fun τ => Ob l ζ (leftTranslate (bondSpread c X τ) V) := by
    intro l ζ h
    funext τ
    simp [observableOnScaledBalls, h]
  have fam_neg : ∀ {l : ℝ} {ζ : StepVariable (finiteCells F)}, ¬ MemScaledBalls ρ l ζ →
      (fun τ => observableOnScaledBalls ρ Ob V c X l τ ζ) = fun _ => 0 := by
    intro l ζ h
    funext τ
    simp [observableOnScaledBalls, h]
  have hn' : ((n : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hn
  refine hD.2.2 _ k n l₁ _ _ _ hl₁ Metric.isOpen_ball h0 ?_ ?_ ?_ ?_
  · intro l hl τ hτ
    classical
    have hcont := continuousOn_observable_scaledBalls (hO _ (hcold' τ hτ)) hl.1
    have e : observableOnScaledBalls ρ Ob V c X l τ =
        ({ζ | MemScaledBalls ρ l ζ} : Set (StepVariable (finiteCells F))).piecewise
          (fun ζ => Ob l ζ (leftTranslate (bondSpread c X τ) V)) (fun _ => 0) := by
      funext ζ
      by_cases h : MemScaledBalls ρ l ζ <;> simp [observableOnScaledBalls, Set.piecewise, h]
    rw [e]
    exact hcont.measurable_piecewise continuousOn_const (isOpen_setOf_memScaledBalls ρ l).measurableSet
  · intro l hl ζ
    by_cases h : MemScaledBalls ρ l ζ
    · rw [fam_pos h]
      exact (data l hl ζ h).1.of_le hn'
    · rw [fam_neg h]
      exact contDiffOn_const
  · refine ⟨M * (K * (1 + (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ)) ^ 7), 7,
      fun j m hj l hl τ hτ ζ => ?_⟩
    unfold coordIteratedDeriv
    by_cases h : MemScaledBalls ρ l ζ
    · rw [fam_pos h]
      refine ((data l hl ζ h).2 τ hτ j m (hj.trans hn)).trans (le_of_eq ?_)
      unfold polynomialBound
      ring
    · rw [fam_neg h, iteratedFDeriv_fun_zero]
      have : (0 : ℝ) ≤ 1 + ‖ζ‖ := by positivity
      simpa using mul_nonneg (mul_nonneg hM₀ hN) (pow_nonneg this 7)
  · intro j m hj ζ
    have key : ∀ l ∈ Icc 0 l₁, MemScaledBalls ρ l ζ →
        coordIteratedDeriv (observableOnScaledBalls ρ Ob V c X) m l 0 ζ =
          bondDeriv (Ob l ζ) V (c ∘ m) (X ∘ m) := by
      intro l hl h
      unfold coordIteratedDeriv
      rw [fam_pos h]
      refine iteratedFDeriv_single_eq_bondDeriv hA (Ob l ζ) V c X m ?_
      have hj' : ((j : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hj.trans hn
      exact ((data l hl ζ h).1.contDiffAt (Metric.isOpen_ball.mem_nhds h0)).of_le hj'
    rw [key 0 ⟨le_rfl, hl₁.le⟩ (memScaledBalls_zero_scale hρ ζ)]
    refine (tendsto_bondDeriv_scale_zero hρ hl₁ (hO V hV) (c ∘ m) (X ∘ m) (hj.trans hn) ζ).congr' ?_
    filter_upwards [eventually_small_scale hρ hl₁ ζ] with l hl
    exact (key l ⟨hl.1.le, hl.2.1⟩ hl.2.2).symm
end YangMills.Construction.ScaledVariables
end
