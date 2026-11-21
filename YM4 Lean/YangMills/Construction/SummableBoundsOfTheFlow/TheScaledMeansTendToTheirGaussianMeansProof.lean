import YangMills.Construction.ColdStepAtMirrorFrames.RimMeanIsAWeightedMean
import YangMills.Construction.RunningCouplingSlope.HaarDensityAtTheLeastFieldHasKernelsProof
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesAreTameNearATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledLawsTendToTheirGaussiansProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansTendToTheirGaussianMeans
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages hiding bondSpread
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.GibbsMeans MeasureTheory Set
namespace YangMills.Construction.ScaledVariables
variable {F : BlockFrame}
private theorem memScaledBalls_zero {ρ : ℝ} (hρ : 0 < ρ) (ζ : StepVariable (finiteCells F)) : MemScaledBalls ρ 0 ζ := by
  intro b
  simpa using hρ
private theorem leftTranslate_bondSpread_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (V : F.GaugeField F.top) :
    leftTranslate (bondSpread c X 0) V = V := by apply _root_.YangMills.SharedProofs.p2043 <;> assumption
private theorem IsSmoothObservable.mono_scale {κ ρ l₁ l₂ K : ℝ} {Y : F.Cell} {V : F.GaugeField F.top}
    {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} (hle : l₁ ≤ l₂)
    (h : IsSmoothObservable κ ρ l₂ K Y V Ob) :
    IsSmoothObservable κ ρ l₁ K Y V Ob where
  even := h.even
  contDiffAt := h.contDiffAt
  exists_smooth_extension k c X := by
    obtain ⟨G, h₁, h₂⟩ := h.exists_smooth_extension k c X
    exact ⟨G, h₁.mono fun τ hτ l ζ h0 hl hz => hτ l ζ h0 (hl.trans hle) hz,
      fun l ζ h0 hl hz => h₂ l ζ h0 (hl.trans hle) hz⟩
  deriv_le k i c X l ζ hr hX h0 hl hz := h.deriv_le k i c X l ζ hr hX h0 (hl.trans hle) hz
  partialDeriv_le k i c X l ζ b e hr hX h0 hl hz he := h.partialDeriv_le k i c X l ζ b e hr hX h0 (hl.trans hle) hz he
  continuousOn k i c X R hr := (h.continuousOn k i c X R hr).mono fun q hq => ⟨hq.1, hq.2.1.trans hle, hq.2.2⟩
private theorem mem_finiteCells (hfin : Finite F.Cell) (Y : F.Cell) : Y ∈ finiteCells F := by apply _root_.YangMills.SharedProofs.p8277 <;> assumption
open Classical in
private theorem sum_centredExpansion_eq (hfin : Finite F.Cell) (a ρA : ℝ) (f : LocalFamily) (l : ℝ) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) :
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion true a ρA 0 f y (l • ζ) V =
      ∑ Y ∈ finiteCells F, rescaledCellExpansion a ρA f l Y V ζ := by
  unfold rescaledCellExpansion cellCentredExpansion
  exact (Finset.sum_fiberwise_of_maps_to (fun y _ => mem_finiteCells hfin (enclosingCell y)) _).symm
private theorem sum_cell_sq_eq (hfin : Finite F.Cell) (ζ : StepVariable (finiteCells F)) :
    ∑ Y ∈ finiteCells F, ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y then ‖ζ b‖ ^ 2 else 0) =
      ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq (finiteCells F), if_pos (mem_finiteCells hfin _)]
private theorem rescaledExponent_eq_sum (hfin : Finite F.Cell) (a ρA lam : ℝ) (f : LocalFamily) (ν l : ℝ)
    (V : F.GaugeField F.top) (ζ : StepVariable (finiteCells F)) :
    rescaledExponent a ρA f ν l V ζ = (∑ Y ∈ finiteCells F, rescaledCellRemainder a ρA lam l Y V ζ) +
      lam / 2 * (∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2) -
        ν * ∑ Y ∈ finiteCells F, rescaledCellExpansion a ρA f l Y V ζ := by
  unfold rescaledExponent
  have h1 : ∑ Y ∈ finiteCells F, rescaledCellTerm a ρA l Y V ζ =
      (∑ Y ∈ finiteCells F, rescaledCellRemainder a ρA lam l Y V ζ) +
      lam / 2 * ∑ Y ∈ finiteCells F, ∑ b : ↥(chordBonds (finiteCells F)),
        (if enclosingCell b.1.1 = Y then ‖ζ b‖ ^ 2 else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Y _ => ?_
    unfold rescaledCellRemainder
    ring
  rw [h1, sum_centredExpansion_eq hfin, sum_cell_sq_eq hfin]
private def lawObservable (a ρA lam : ℝ) (f : LocalFamily) (law : StepLaw) :
    ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  fun l ζ V' => rescaledLawExponent a ρA lam f l V' law ζ
private theorem isModerate_finsetSum {Ω : Type} [MeasurableSpace Ω] {k n : ℕ} {l₀ : ℝ} {B : Set (Fin k → ℝ)}
    {s : Ω → ℝ} {ι : Type}
    (hC : IsModerateLinearCombination) (hl : 0 < l₀) (hB : IsOpen B) (h0 : (0 : Fin k → ℝ) ∈ B) (hs : ∀ ω, 1 ≤ s ω)
    {H₀ : ℝ → (Fin k → ℝ) → Ω → ℝ} (hH₀ : IsModerate l₀ B s n H₀) (S : Finset ι) (H : ι → ℝ → (Fin k → ℝ) → Ω → ℝ)
    (hH : ∀ i ∈ S, IsModerate l₀ B s n (H i)) :
    IsModerate l₀ B s n fun l τ ω => ∑ i ∈ S, H i l τ ω := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h := hC Ω k n l₀ B s 0 0 H₀ H₀ hl hB h0 hs hH₀ hH₀
    simpa using h
  | insert i S hi ih =>
    have h := hC Ω k n l₀ B s 1 1 (H i) _ hl hB h0 hs (hH i (Finset.mem_insert_self i S))
      (ih fun j hj => hH j (Finset.mem_insert_of_mem hj))
    have e : (fun l τ ω => ∑ j ∈ insert i S, H j l τ ω) =
        fun l τ ω => 1 * H i l τ ω + 1 * ∑ j ∈ S, H j l τ ω := by
      funext l τ ω
      rw [Finset.sum_insert hi]
      ring
    rw [e]
    exact h
private theorem isOpen_scaledBalls (ρ l : ℝ) : IsOpen {ζ : StepVariable (finiteCells F) | MemScaledBalls ρ l ζ} := by apply _root_.YangMills.SharedProofs.p7210 <;> assumption
private theorem eventually_small_scale {ρ l₁ : ℝ} (hρ : 0 < ρ) (hl₁ : 0 < l₁) (ζ : StepVariable (finiteCells F)) :
    ∀ᶠ l in 𝓝[>] (0 : ℝ), 0 < l ∧ l ≤ l₁ ∧ MemScaledBalls ρ l ζ := by apply _root_.YangMills.SharedProofs.p125245 <;> assumption
private theorem isModerate_of_free {k n : ℕ} {l₀ ρ C : ℝ} {m : ℕ} {B : Set (Fin k → ℝ)}
    (hD : IsModerateOfCoordDerivBounds)
    (hl : 0 < l₀) (hρ : 0 < ρ) (hB : IsOpen B) (h0 : (0 : Fin k → ℝ) ∈ B) (V : F.GaugeField F.top)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {φ : StepVariable (finiteCells F) → ℝ}
    (hφ : Continuous φ) (hb : ∀ ζ, |φ ζ| ≤ C * (1 + ‖ζ‖) ^ m) :
    IsModerate l₀ B (fun ζ : StepVariable (finiteCells F) => 1 + ‖ζ‖) n
      (observableOnScaledBalls ρ (fun _ ζ _ => φ ζ) V c X) := by
  have hC : 0 ≤ C := by
    have h := (abs_nonneg _).trans (hb 0)
    simpa using h
  have fam : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)),
      (fun τ => observableOnScaledBalls ρ (fun _ ζ _ => φ ζ) V c X l τ ζ) =
        fun _ => observableOnScaledBalls ρ (fun _ ζ _ => φ ζ) V c X l 0 ζ := by
    intro l ζ
    funext τ
    simp [observableOnScaledBalls]
  have deriv0 : ∀ (j : ℕ) (q : Fin j → Fin k) (l : ℝ) (τ : Fin k → ℝ) (ζ : StepVariable (finiteCells F)),
      coordIteratedDeriv (observableOnScaledBalls ρ (fun _ ζ _ => φ ζ) V c X) q l τ ζ =
        if j = 0 then observableOnScaledBalls ρ (fun _ ζ _ => φ ζ) V c X l 0 ζ else 0 := by
    intro j q l τ ζ
    unfold coordIteratedDeriv
    rw [fam l ζ]
    cases j with
    | zero => simp
    | succ j => simp [iteratedFDeriv_succ_const]
  refine hD _ k n l₀ B _ _ hl hB h0 ?_ ?_ ?_ ?_
  · intro l _ τ _
    classical
    have e : observableOnScaledBalls ρ (fun _ ζ _ => φ ζ) V c X l τ =
        ({ζ | MemScaledBalls ρ l ζ} : Set (StepVariable (finiteCells F))).piecewise φ (fun _ => 0) := by
      funext ζ
      by_cases h : MemScaledBalls ρ l ζ <;> simp [observableOnScaledBalls, Set.piecewise, h]
    rw [e]
    exact hφ.continuousOn.measurable_piecewise continuousOn_const (isOpen_scaledBalls ρ l).measurableSet
  · intro l _ ζ
    rw [fam l ζ]
    exact contDiffOn_const
  · refine ⟨C, m, fun j q _ l _ τ _ ζ => ?_⟩
    rw [deriv0]
    have hp : 0 ≤ C * (1 + ‖ζ‖) ^ m := by positivity
    split_ifs
    · unfold observableOnScaledBalls
      split_ifs
      · exact hb ζ
      · simpa using hp
    · simpa using hp
  · intro j q _ ζ
    simp only [deriv0]
    split_ifs
    · have e0 : observableOnScaledBalls ρ (fun _ ζ _ => φ ζ) V c X 0 0 ζ = φ ζ := by
        simp [observableOnScaledBalls, memScaledBalls_zero hρ ζ]
      rw [e0]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_small_scale hρ hl ζ] with l hl'
      simp [observableOnScaledBalls, hl'.2.2]
    · exact tendsto_const_nhds
private def scaledMeasure (F : BlockFrame) (ρ : ℝ) (p : ℝ → ℝ) (l : ℝ) : Measure (StepVariable (finiteCells F)) :=
  if l = 0 then volume else (cutoffLaw F ρ p).map fun η => l⁻¹ • η
private theorem measurable_inv_smul (l : ℝ) :
    Measurable (fun η : StepVariable (finiteCells F) => l⁻¹ • η) :=
  (continuous_const_smul l⁻¹).measurable
private theorem gibbsMean_scaledMeasure (hR : CutoffMeanIsGibbsMean) {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    {l : ℝ} (hl : 0 < l) {A f : StepVariable (finiteCells F) → ℝ} (hA : Measurable A) (hf : Measurable f)
    (Ψ G : StepVariable (finiteCells F) → ℝ)
    (hΨ : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → A (l⁻¹ • η) = Ψ η)
    (hG : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → f (l⁻¹ • η) = G η) :
    gibbsMean (scaledMeasure F ρ p l) A f = cutoffMean ρ p Ψ G := by
  obtain ⟨-, -, hae, hmean⟩ := hR F ρ p hρ hp
  have hm := measurable_inv_smul (F := F) l
  rw [hmean]
  unfold scaledMeasure gibbsMean
  rw [if_neg hl.ne',
    integral_map (f := fun ω => f ω * Real.exp (-A ω)) hm.aemeasurable (hf.mul hA.neg.exp).aestronglyMeasurable,
    integral_map (f := fun ω => Real.exp (-A ω)) hm.aemeasurable hA.neg.exp.aestronglyMeasurable]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [hae] with η hη
    rw [hΨ η hη, hG η hη]
  · refine integral_congr_ae ?_
    filter_upwards [hae] with η hη
    rw [hΨ η hη]
private theorem integrable_pow_mul_gaussian_floor {ι : Type} [Fintype ι] {A Bc : ℝ} (hA : 0 < A) (hB : 0 ≤ Bc)
    (M : ℕ) :
    Integrable (fun ζ : BondField ι =>
      (1 + ‖ζ‖) ^ M * Real.exp (-(A * ∑ b, ‖ζ b‖ ^ 2 - Bc * ∑ b, ‖ζ b‖))) := by apply _root_.YangMills.SharedProofs.p40209 <;> assumption
private theorem integrable_scaledMeasure (hR : CutoffMeanIsGibbsMean) {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) {l : ℝ} (hl : 0 < l) (C : ℝ) (m j : ℕ) :
    Integrable (fun ζ : StepVariable (finiteCells F) => (1 + ‖ζ‖) ^ j * Real.exp (|C| * (1 + ‖ζ‖) ^ m))
      (scaledMeasure F ρ p l) := by
  obtain ⟨hfin, -, hae, -⟩ := hR F ρ p hρ hp
  have hm := measurable_inv_smul (F := F) l
  have hc : Continuous (fun ζ : StepVariable (finiteCells F) => (1 + ‖ζ‖) ^ j * Real.exp (|C| * (1 + ‖ζ‖) ^ m)) := by
    fun_prop
  unfold scaledMeasure
  rw [if_neg hl.ne', integrable_map_measure hc.aestronglyMeasurable hm.aemeasurable]
  have hlinv : 0 < l⁻¹ := inv_pos.2 hl
  have hcm : Continuous (fun η : StepVariable (finiteCells F) => l⁻¹ • η) := continuous_const_smul l⁻¹
  have := hfin
  refine Integrable.of_bound (hc.comp hcm).aestronglyMeasurable
    ((1 + l⁻¹ * ρ) ^ j * Real.exp (|C| * (1 + l⁻¹ * ρ) ^ m)) ?_
  filter_upwards [hae] with η hη
  have hn : ‖l⁻¹ • η‖ ≤ l⁻¹ * ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlinv]
    exact mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg hρ.le).2 fun b => (hη b).le) hlinv.le
  have h1 : 1 + ‖l⁻¹ • η‖ ≤ 1 + l⁻¹ * ρ := by linarith
  have h0 : 0 ≤ 1 + ‖l⁻¹ • η‖ := by positivity
  simp only [Function.comp]
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul (pow_le_pow_left₀ h0 h1 _)
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 _) (abs_nonneg _)))
    (Real.exp_pos _).le (by positivity)
private theorem isModerateValue_of_isModerate {Ω : Type} [MeasurableSpace Ω] {k : ℕ} {l₀ : ℝ} {B : Set (Fin k → ℝ)}
    {s : Ω → ℝ} {H : ℝ → (Fin k → ℝ) → Ω → ℝ} : ∀ n : ℕ, IsModerate l₀ B s n H → IsModerateValue l₀ B s H
  | 0, h => h
  | _ + 1, h => h.1
theorem scaledMeansTendToGaussianMeans_proof (hL : scaledLawsTendToGaussian)
    (hFl : rescaledExponentFloorStatement) (hP : YangMills.Construction.StepDensities.rescaledPartsSmoothStatement)
    (hR : CutoffMeanIsGibbsMean) (hD : GibbsMeanDerivativesConverge)
    (hO : SmoothObservablesModerateNearField) : scaledMeansTendToGaussianMeans := by
  unfold scaledMeansTendToGaussianMeans ForallSmoothObservables
  refine EventuallyOrdered.mono (hL.and (hFl.and hP)) ?_
  rintro T hT hn ⟨gL, gF, gP⟩ e
  obtain ⟨a₁, ha₁, kL⟩ := gL e
  obtain ⟨a₂, ha₂, kF⟩ := gF e
  obtain ⟨a₃, K₃, ha₃, hK₃, kP⟩ := gP e
  refine ⟨min a₁ (min a₂ a₃), 1, lt_min ha₁ (lt_min ha₂ ha₃), one_pos,
    fun l₁ hl₁ hle t f F V Y law K Ob k c X hf hTop hV hlaw hK hObs hX hk => ?_⟩
  have e₁ : l₁ ≤ a₁ := hle.trans (min_le_left _ _)
  have e₂ : l₁ ≤ a₂ := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e₃ : l₁ ≤ a₃ := hle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hcut : IsCutoff T.ballRadius T.p := hT.cutoff
  have hlam : 0 < T.lam := hT.chain_admissible.positivity.2.2.1
  have hκ : 0 ≤ T.κ := hT.κ_pos.le
  have hside : ∀ i, F.extent i ≠ 0 := by
    obtain ⟨_, _, n, hn', hn₀⟩ := hTop
    intro i
    rw [hn' i]
    omega
  have hfin : Finite F.Cell := by
    have h : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by simp [BlockFrame.period, hside i]⟩
    exact Pi.finite
  obtain ⟨r, hr, hcold, hOb⟩ := hO F (5 / 4 * T.σ) T.κ T.ballRadius V k k c X hside hκ hρ hk hV
  have h0 : (0 : Fin k → ℝ) ∈ Metric.ball (0 : Fin k → ℝ) r := Metric.mem_ball_self hr
  have hopen : IsOpen (Metric.ball (0 : Fin k → ℝ) r) := Metric.isOpen_ball
  have hs : ∀ ζ : StepVariable (finiteCells F), 1 ≤ 1 + ‖ζ‖ := fun ζ => by linarith [norm_nonneg ζ]
  have hH : IsModerate l₁ (Metric.ball (0 : Fin k → ℝ) r) (fun ζ : StepVariable (finiteCells F) => 1 + ‖ζ‖) k
      (observableOnScaledBalls T.ballRadius Ob V c X) :=
    hOb l₁ K Y Ob hl₁ hK (fun V' hV' => (hObs V' hV').mono_scale (by linarith)) r hr le_rfl
  have hBirth : ∀ Y' : F.Cell, IsModerate l₁ (Metric.ball (0 : Fin k → ℝ) r)
      (fun ζ : StepVariable (finiteCells F) => 1 + ‖ζ‖) k
      (observableOnScaledBalls T.ballRadius (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y' V' ζ) V c X) :=
    fun Y' => hOb l₁ K₃ Y' _ hl₁ hK₃ (fun V' hV' => (kP l₁ hl₁ e₃ t f F V' Y' hf hTop hV').1) r hr le_rfl
  have hRow : ∀ Y' : F.Cell, IsModerate l₁ (Metric.ball (0 : Fin k → ℝ) r)
      (fun ζ : StepVariable (finiteCells F) => 1 + ‖ζ‖) k
      (observableOnScaledBalls T.ballRadius (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y' V' ζ) V c X) :=
    fun Y' => hOb l₁ K₃ Y' _ hl₁ hK₃ (fun V' hV' => (kP l₁ hl₁ e₃ t f F V' Y' hf hTop hV').2) r hr le_rfl
  have hQ : IsModerate l₁ (Metric.ball (0 : Fin k → ℝ) r) (fun ζ : StepVariable (finiteCells F) => 1 + ‖ζ‖) k
      (observableOnScaledBalls T.ballRadius
        (fun _ ζ _ => T.lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2) V c X) := by
    refine isModerate_of_free (C := T.lam / 2 * (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ)) (m := 2) hD.2.2
      hl₁ hρ hopen h0 V c X (by fun_prop) fun ζ => ?_
    have hsum : ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2 ≤
        (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ) * (1 + ‖ζ‖) ^ 2 := by
      calc ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2 ≤
            ∑ _b : ↥(chordBonds (finiteCells F)), (1 + ‖ζ‖) ^ 2 :=
            Finset.sum_le_sum fun b _ => pow_le_pow_left₀ (norm_nonneg _)
              ((norm_le_pi_norm ζ b).trans (by linarith)) 2
        _ = _ := by simp
    have hnn : 0 ≤ T.lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2 := by positivity
    rw [abs_of_nonneg hnn, mul_assoc]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hC := hD.2.1
  have hBS := isModerate_finsetSum hC hl₁ hopen h0 hs hH (finiteCells F) _ fun Y' _ => hBirth Y'
  have hRS := isModerate_finsetSum hC hl₁ hopen h0 hs hH (finiteCells F) _ fun Y' _ => hRow Y'
  have hBQ := hC _ k k l₁ _ _ 1 1 _ _ hl₁ hopen h0 hs hBS hQ
  have hU : IsModerate l₁ (Metric.ball (0 : Fin k → ℝ) r) (fun ζ : StepVariable (finiteCells F) => 1 + ‖ζ‖) k
      (observableOnScaledBalls T.ballRadius (lawObservable T.a T.ρA T.lam f law) V c X) := by
    cases law with
    | tilted ν₀ =>
      have h := hC _ k k l₁ _ _ 1 (-ν₀) _ _ hl₁ hopen h0 hs hBQ hRS
      convert h using 1
      funext l τ ζ
      by_cases hz : MemScaledBalls T.ballRadius l ζ
      · simp only [observableOnScaledBalls, if_pos hz, lawObservable, rescaledLawExponent]
        rw [rescaledExponent_eq_sum hfin T.a T.ρA T.lam f ν₀ l _ ζ]
        ring
      · simp [observableOnScaledBalls, hz]
    | interpolated θ =>
      have h := hC _ k k l₁ _ _ θ (1 - θ) _ _ hl₁ hopen h0 hs hBQ hQ
      convert h using 1
      funext l τ ζ
      by_cases hz : MemScaledBalls T.ballRadius l ζ
      · simp only [observableOnScaledBalls, if_pos hz, lawObservable, rescaledLawExponent]
        rw [rescaledExponent_eq_sum hfin T.a T.ρA T.lam f 0 l _ ζ]
        ring
      · simp [observableOnScaledBalls, hz]
  have hUv := isModerateValue_of_isModerate k hU
  have hHv := isModerateValue_of_isModerate k hH
  obtain ⟨CU, mU, hCU⟩ := hUv.abs_le_pow
  have floors := fun (τ : Fin k → ℝ) (hτ : τ ∈ Metric.ball (0 : Fin k → ℝ) r) =>
    kF t f F (leftTranslate (bondSpread c X τ) V) law hf hTop (hcold τ hτ) hlaw
  have id1 : ∀ l : ℝ, 0 < l → l ≤ l₁ → ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r,
      ∀ f₁ g₁ : StepVariable (finiteCells F) → ℝ,
      Measurable f₁ → (∀ ζ, MemScaledBalls T.ballRadius l ζ → f₁ ζ = g₁ ζ) →
      gibbsMean (scaledMeasure F T.ballRadius T.p l)
        (observableOnScaledBalls T.ballRadius (lawObservable T.a T.ρA T.lam f law) V c X l τ) f₁ =
        rescaledMean T.a T.ρA T.ballRadius T.lam l T.p f law (leftTranslate (bondSpread c X τ) V) g₁ := by
    intro l hl hll τ hτ f₁ g₁ hf₁ hfg
    have hball : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        MemScaledBalls T.ballRadius l (l⁻¹ • η) := by
      intro η hη b
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl), ← mul_assoc,
        mul_inv_cancel₀ hl.ne', one_mul]
      exact hη b
    refine gibbsMean_scaledMeasure hR hρ hcut hl (hUv.measurable l ⟨hl.le, hll⟩ τ hτ) hf₁ _ _ (fun η hη => ?_)
      fun η hη => hfg _ (hball η hη)
    have hz := hball η hη
    have h2 := (floors τ hτ).2.1 l (l⁻¹ • η) hl (hll.trans e₂) hz
    rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul] at h2
    simp only [observableOnScaledBalls, if_pos hz, lawObservable]
    exact h2.symm
  have id2 : ∀ (τ : Fin k → ℝ) (f₁ : StepVariable (finiteCells F) → ℝ),
      gibbsMean (scaledMeasure F T.ballRadius T.p 0)
        (observableOnScaledBalls T.ballRadius (lawObservable T.a T.ρA T.lam f law) V c X 0 τ) f₁ =
        gaussianMean T.a T.ρA T.lam f (leftTranslate (bondSpread c X τ) V) law f₁ := by
    intro τ f₁
    have eU : observableOnScaledBalls T.ballRadius (lawObservable T.a T.ρA T.lam f law) V c X 0 τ =
        fun ζ => rescaledLawExponent T.a T.ρA T.lam f 0 (leftTranslate (bondSpread c X τ) V) law ζ := by
      funext ζ
      simp [observableOnScaledBalls, memScaledBalls_zero hρ ζ, lawObservable]
    rw [eU]
    unfold gibbsMean gaussianMean gaussianWeight scaledMeasure
    rw [if_pos rfl]
    set E := rescaledLawExponent T.a T.ρA T.lam f 0 (leftTranslate (bondSpread c X τ) V) law with hE
    have w : ∀ ζ, Real.exp (-(E ζ - E 0)) = Real.exp (E 0) * Real.exp (-E ζ) := fun ζ => by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [w]
    have n1 : ∀ ζ, f₁ ζ * (Real.exp (E 0) * Real.exp (-E ζ)) = Real.exp (E 0) * (f₁ ζ * Real.exp (-E ζ)) :=
      fun ζ => by ring
    simp only [n1]
    rw [integral_const_mul, integral_const_mul, mul_div_mul_left _ _ (Real.exp_pos _).ne']
  have hdom : ∀ l ∈ Icc 0 l₁, ∃ W : StepVariable (finiteCells F) → ℝ,
      (∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ ζ,
        Real.exp (-observableOnScaledBalls T.ballRadius (lawObservable T.a T.ρA T.lam f law) V c X l τ ζ) ≤ W ζ) ∧
      ∀ m : ℕ, Integrable (fun ζ => (1 + ‖ζ‖) ^ m * W ζ) (scaledMeasure F T.ballRadius T.p l) := by
    intro l hl
    rcases hl.1.eq_or_lt with h00 | hpos
    · subst h00
      refine ⟨fun ζ => Real.exp |CU| * Real.exp (-(T.lam / 4 * ∑ b, ‖ζ b‖ ^ 2 - Real.sqrt T.lam / 2 * ∑ b, ‖ζ b‖)),
        fun τ hτ ζ => ?_, fun m => ?_⟩
      · have hfl := (floors τ hτ).1 0 ζ le_rfl ha₂.le (memScaledBalls_zero hρ ζ)
        have hz : ∀ ζ' : StepVariable (finiteCells F),
            observableOnScaledBalls T.ballRadius (lawObservable T.a T.ρA T.lam f law) V c X 0 τ ζ' =
            rescaledLawExponent T.a T.ρA T.lam f 0 (leftTranslate (bondSpread c X τ) V) law ζ' := fun ζ' => by
          simp [observableOnScaledBalls, memScaledBalls_zero hρ ζ', lawObservable]
        have hb0 := hCU 0 hl τ hτ (0 : StepVariable (finiteCells F))
        rw [hz] at hb0
        rw [hz]
        beta_reduce
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have hb1 : |rescaledLawExponent T.a T.ρA T.lam f 0 (leftTranslate (bondSpread c X τ) V) law 0| ≤ |CU| := by
          refine hb0.trans ?_
          simpa using le_abs_self CU
        have hb2 := (abs_le.1 hb1).1
        linarith
      · have h := (integrable_pow_mul_gaussian_floor (ι := ↥(chordBonds (finiteCells F))) (A := T.lam / 4)
          (Bc := Real.sqrt T.lam / 2) (by positivity) (by positivity) m).const_mul (Real.exp |CU|)
        unfold scaledMeasure
        rw [if_pos rfl]
        refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
        simp only
        ring
    · refine ⟨fun ζ => Real.exp (|CU| * (1 + ‖ζ‖) ^ mU), fun τ hτ ζ => ?_, fun m =>
        integrable_scaledMeasure hR hρ hcut hpos CU mU m⟩
      refine Real.exp_le_exp.2 ?_
      have h1 := hCU l hl τ hτ ζ
      have h2 : CU * (1 + ‖ζ‖) ^ mU ≤ |CU| * (1 + ‖ζ‖) ^ mU :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      have h3 := (abs_le.1 (h1.trans h2)).1
      linarith
  have hne : ∀ l ∈ Icc 0 l₁, NeZero (scaledMeasure F T.ballRadius T.p l) := by
    intro l hl
    refine ⟨?_⟩
    rcases hl.1.eq_or_lt with h00 | hpos
    · subst h00
      unfold scaledMeasure
      rw [if_pos rfl]
      exact NeZero.ne _
    · unfold scaledMeasure
      rw [if_neg hpos.ne']
      intro h
      exact (hR F T.ballRadius T.p hρ hcut).2.1
        ((Measure.map_eq_zero_iff (measurable_inv_smul l).aemeasurable).1 h)
  have hLaws : AreDominatedGibbsLaws l₁ (Metric.ball (0 : Fin k → ℝ) r)
      (fun ζ : StepVariable (finiteCells F) => 1 + ‖ζ‖) (scaledMeasure F T.ballRadius T.p)
      (observableOnScaledBalls T.ballRadius (lawObservable T.a T.ρA T.lam f law) V c X) := by
    refine ⟨hdom, fun l hl τ hτ => ?_⟩
    obtain ⟨W, hW, hWi⟩ := hdom l hl
    have := hne l hl
    have h0' : Integrable W (scaledMeasure F T.ballRadius T.p l) := by simpa using hWi 0
    refine integral_exp_pos (Integrable.mono' h0' (hUv.measurable l hl τ hτ).neg.exp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ζ => ?_))
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hW τ hτ ζ
  have hlim : ∀ H' : ℝ → (Fin k → ℝ) → StepVariable (finiteCells F) → ℝ,
      IsModerateValue l₁ (Metric.ball (0 : Fin k → ℝ) r) (fun ζ : StepVariable (finiteCells F) => 1 + ‖ζ‖) H' →
      Filter.Tendsto (fun l => gibbsMean (scaledMeasure F T.ballRadius T.p l)
        (observableOnScaledBalls T.ballRadius (lawObservable T.a T.ρA T.lam f law) V c X l 0) (H' l 0)) (𝓝[>] 0)
        (𝓝 (gibbsMean (scaledMeasure F T.ballRadius T.p 0)
          (observableOnScaledBalls T.ballRadius (lawObservable T.a T.ρA T.lam f law) V c X 0 0) (H' 0 0))) := by
    intro H' hH'
    obtain ⟨C', m', hC'⟩ := hH'.abs_le_pow
    classical
    let Hc : ℝ → StepVariable (finiteCells F) → ℝ := fun l => if l ≤ l₁ then H' l 0 else 0
    have key := kL t f F V law Hc (H' 0 0) |C'| m' hf hTop hV hlaw ?_ ?_ ?_
    · rw [id2 0, leftTranslate_bondSpread_zero]
      refine key.congr' ?_
      filter_upwards [Ioc_mem_nhdsGT hl₁] with l hl
      have hm := hH'.measurable l ⟨hl.1.le, hl.2⟩ 0 h0
      rw [id1 l hl.1 hl.2 0 h0 (H' l 0) (Hc l) hm fun ζ _ => by simp [Hc, hl.2], leftTranslate_bondSpread_zero]
    · intro l _ _
      by_cases h : l ≤ l₁
      · by_cases h' : 0 ≤ l
        · simpa [Hc, h] using hH'.measurable l ⟨h', h⟩ 0 h0
        · exfalso
          linarith
      · simp only [Hc, if_neg h]
        exact measurable_const
    · intro l ζ hl _ _
      by_cases h : l ≤ l₁
      · simp only [Hc, if_pos h]
        refine (hC' l ⟨hl.le, h⟩ 0 h0 ζ).trans ?_
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      · simp only [Hc, if_neg h]
        simpa using mul_nonneg (abs_nonneg C') (by positivity : (0 : ℝ) ≤ (1 + ‖ζ‖) ^ m')
    · intro ζ
      refine (hH'.tendsto_zero ζ).congr' ?_
      filter_upwards [Ioc_mem_nhdsGT hl₁] with l hl
      simp [Hc, hl.2]
  have main := hD.1 _ k k l₁ _ _ (scaledMeasure F T.ballRadius T.p)
    (observableOnScaledBalls T.ballRadius (lawObservable T.a T.ρA T.lam f law) V c X)
    (observableOnScaledBalls T.ballRadius Ob V c X) hl₁ hopen h0 hs hLaws hU hH hlim
  have lim := main.2 fun i => Pi.single i 1
  unfold bondDeriv
  have eZero : (fun τ => observableGaussianMean T.a T.ρA T.lam f law Ob (leftTranslate (bondSpread c X τ) V)) =
      fun τ => gibbsMean (scaledMeasure F T.ballRadius T.p 0)
        (observableOnScaledBalls T.ballRadius (lawObservable T.a T.ρA T.lam f law) V c X 0 τ)
        (observableOnScaledBalls T.ballRadius Ob V c X 0 τ) := by
    funext τ
    rw [id2 τ]
    unfold observableGaussianMean
    congr 1
    funext ζ
    simp [observableOnScaledBalls, memScaledBalls_zero hρ ζ]
  rw [eZero]
  refine lim.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hl₁] with l hl
  have hev : (fun τ => gibbsMean (scaledMeasure F T.ballRadius T.p l)
      (observableOnScaledBalls T.ballRadius (lawObservable T.a T.ρA T.lam f law) V c X l τ)
      (observableOnScaledBalls T.ballRadius Ob V c X l τ)) =ᶠ[𝓝 0]
      fun τ => observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l (leftTranslate (bondSpread c X τ) V) :=
    Filter.eventually_of_mem (hopen.mem_nhds h0) fun τ hτ => by
      refine id1 l hl.1 hl.2 τ hτ _ _ (hHv.measurable l ⟨hl.1.le, hl.2⟩ τ hτ) fun ζ hz => ?_
      simp [observableOnScaledBalls, hz]
  rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev k).eq_of_nhds]
end YangMills.Construction.ScaledVariables
end
