import YangMills.Construction.ColdStepAtMirrorFrames.DensityNearTheFrameProof
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionDensityOnTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAtTheFlatTop
import YangMills.Construction.ColdStepAtMirrorFrames.FreezingOfTheMeans
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfTheStepAreSmooth
import YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivativeOfTheExpansionDensity
import YangMills.Construction.ColdStepAtMirrorFrames.TransportOfTheExpansion
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongATiltProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.DerivativeInterpolation MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace StepDensityLocality
variable {F : BlockFrame}
private theorem leftTranslate_bondSpread_zero {j k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField j) :
    leftTranslate (bondSpread c X 0) V = V := by apply _root_.YangMills.SharedProofs.p1939 <;> assumption
private theorem bondDeriv_zero {j : ℕ} (G : F.GaugeField j → ℝ) (V : F.GaugeField j)
    (c : Fin 0 → F.Site j × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G V c X = G V := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
private theorem bondDeriv_sub_const {j k : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (b : ℝ) (h1 : 1 ≤ k) (hk : k ≤ 3)
    (hG : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0) :
    bondDeriv (fun W' => G W' - b) W c X = bondDeriv G W c X := by
  unfold bondDeriv
  have hk' : ((k : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have e : (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W) - b) =
      (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) + fun _ => -b := by
    funext τ
    simp [sub_eq_add_neg]
  rw [e, iteratedFDeriv_add_apply (hG.of_le hk') contDiffAt_const,
    iteratedFDeriv_const_of_ne (by omega)]
  simp
private theorem gibbsMean_congr_ae {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {A A' H H' : Ω → ℝ}
    (hA : A =ᵐ[μ] A') (hH : H =ᵐ[μ] H') : gibbsMean μ A H = gibbsMean μ A' H' := by apply _root_.YangMills.Construction.InterpolatedBirths.gibbsMean_congr_ae <;> assumption
private theorem integrable_exp_neg_of_bdd {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {A : Ω → ℝ} {R : ℝ} (hAm : AEStronglyMeasurable A μ)
    (hAb : ∀ᵐ ω ∂μ, |A ω| ≤ R) :
    Integrable (fun ω => Real.exp (- A ω)) μ := by apply _root_.YangMills.SharedProofs.p11234 <;> assumption
private theorem integral_exp_neg_pos {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} (hμ : μ ≠ 0)
    {A : Ω → ℝ} (hint : Integrable (fun ω => Real.exp (- A ω)) μ) :
    0 < ∫ ω, Real.exp (- A ω) ∂μ := by apply _root_.YangMills.SharedProofs.p23099 <;> assumption
private theorem continuousOn_gibbsMean {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (hμ : μ ≠ 0) {A : ℝ → Ω → ℝ} {H : Ω → ℝ} {R : ℝ}
    (hAm : ∀ v ∈ Set.Icc (0 : ℝ) 1, AEStronglyMeasurable (A v) μ)
    (hHm : AEStronglyMeasurable H μ)
    (hAb : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ ω ∂μ, |A v ω| ≤ R)
    (hHb : ∀ᵐ ω ∂μ, |H ω| ≤ R)
    (hc : ∀ ω, ContinuousOn (fun v => A v ω) (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun v => gibbsMean μ (A v) H) (Set.Icc (0 : ℝ) 1) := by
  have hexpm : ∀ v ∈ Set.Icc (0 : ℝ) 1, AEStronglyMeasurable (fun ω => Real.exp (- A v ω)) μ :=
    fun v hv => Real.continuous_exp.comp_aestronglyMeasurable (hAm v hv).neg
  have hexpb : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ ω ∂μ, ‖Real.exp (- A v ω)‖ ≤ Real.exp R := fun v hv => by
    filter_upwards [hAb v hv] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hω).1])
  have hD : ContinuousOn (fun v => ∫ ω, Real.exp (- A v ω) ∂μ) (Set.Icc (0 : ℝ) 1) := by
    apply continuousOn_of_dominated hexpm hexpb (integrable_const _)
    exact Filter.Eventually.of_forall fun ω => Real.continuous_exp.comp_continuousOn (hc ω).neg
  have hN : ContinuousOn (fun v => ∫ ω, H ω * Real.exp (- A v ω) ∂μ) (Set.Icc (0 : ℝ) 1) := by
    apply continuousOn_of_dominated (bound := fun _ => |R| * Real.exp R)
      (fun v hv => hHm.mul (hexpm v hv)) _ (integrable_const _)
    · exact Filter.Eventually.of_forall fun ω =>
        continuousOn_const.mul (Real.continuous_exp.comp_continuousOn (hc ω).neg)
    · intro v hv
      filter_upwards [hHb, hexpb v hv] with ω h1 h2
      change ‖H ω * Real.exp (- A v ω)‖ ≤ _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (le_trans h1 (le_abs_self R)) h2 (norm_nonneg _) (abs_nonneg _)
  exact hN.div hD fun v hv =>
    (integral_exp_neg_pos hμ (integrable_exp_neg_of_bdd (hAm v hv) (hAb v hv))).ne'
private theorem abs_le_of_dominated {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ}
    {G : (Fin k → ℝ) → Ω → ℝ} {B : Set (Fin k → ℝ)} {K : ℝ} {τ : Fin k → ℝ}
    (hG : IsDominatedSmoothFamily μ 3 B K G) (hτ : τ ∈ B) : ∀ᵐ ω ∂μ, |G τ ω| ≤ K := by
  filter_upwards [hG.norm_iteratedFDeriv_le] with ω hω
  have h0 := hω 0 (Nat.zero_le _) τ hτ
  rwa [norm_iteratedFDeriv_zero] at h0
private theorem dominated_mono {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ}
    {B : Set (Fin k → ℝ)} {K K' : ℝ} {G : (Fin k → ℝ) → Ω → ℝ} (hK : K ≤ K')
    (h : IsDominatedSmoothFamily μ 3 B K G) : IsDominatedSmoothFamily μ 3 B K' G := by
  refine ⟨h.aestronglyMeasurable, h.contDiffOn, ?_⟩
  filter_upwards [h.norm_iteratedFDeriv_le] with ω hω j hj τ hτ using le_trans (hω j hj τ hτ) hK
private theorem intervalIntegrable_cutoffMean {a ρA ρ x κ δ E E₃ C : ℝ} {L m : ℕ} {p : ℝ → ℝ}
    {f : LocalFamily} {V : F.GaugeField F.top} (hρ : 0 < ρ) (hcut : IsCutoff ρ p)
    (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedFamilyOnClosedBalls)
    (hE : CellExponentBounds false a ρA ρ x κ C m V)
    (hR : CentredExpansionBounds false a ρA ρ κ δ E E₃ C L m f V) (Y : F.Cell) :
    IntervalIntegrable (fun v => cutoffMean ρ p (stepExponent false a ρA x m f v V) fun η =>
      cellCentredExpansion false a ρA m f Y η V) volume 0 1 := by
  classical
  set c : Fin 0 → F.Site F.top × Fin 4 := Fin.elim0 with hc
  set X : Fin 0 → imaginaryQuaternions := Fin.elim0 with hX
  set Vt : (Fin 0 → ℝ) → F.GaugeField F.top := fun τ => leftTranslate (bondSpread c X τ) V with hVt
  have hVt0 : Vt 0 = V := leftTranslate_bondSpread_zero c X V
  set Sv := StepVariable (finiteCells F) with hSv
  obtain ⟨hfinμ, hμ0, hμb, hμm⟩ := hRim F ρ p hρ hcut
  set μ := cutoffLaw F ρ p with hμ
  have hμc : ∀ᵐ η ∂μ, ∀ b, ‖η b‖ ≤ ρ := by
    filter_upwards [hμb] with η hη b using (hη b).le
  set P0 : (Fin 0 → ℝ) × Sv → ℝ := fun z =>
    ∑ Y' ∈ finiteCells F, cellExponent false a ρA x m Y' (Vt z.1) z.2 with hP0
  set R0 : (Fin 0 → ℝ) × Sv → ℝ := fun z =>
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false a ρA m f y z.2 (Vt z.1) with hR0
  set FY : (Fin 0 → ℝ) × Sv → ℝ := fun z => cellCentredExpansion false a ρA m f Y z.2 (Vt z.1) with hFY
  have sP0 : ∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 P0 (0, η) := fun η hη =>
    ContDiffAt.sum fun Y' _ => hE.smooth Y' η 0 c X hη
  have sR0 : ∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 R0 (0, η) := fun η hη =>
    ContDiffAt.sum fun y _ => hR.smooth y η 0 c X hη
  have sFY : ∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 FY (0, η) := fun η hη => by
    have : FY = fun z => ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter
        (fun y => enclosingCell y = Y), centredExpansion false a ρA m f y z.2 (Vt z.1) := rfl
    rw [this]
    exact ContDiffAt.sum fun y _ => hR.smooth y η 0 c X hη
  set π : (Fin 0 → ℝ) × (ℝ × Sv) → (Fin 0 → ℝ) × Sv := fun z => (z.1, z.2.2) with hπ
  have hπs : ContDiff ℝ 3 π := contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
  have hvs : ContDiff ℝ 3 fun z : (Fin 0 → ℝ) × (ℝ × Sv) => z.2.1 := contDiff_fst.comp contDiff_snd
  have lift : ∀ {G : (Fin 0 → ℝ) × Sv → ℝ}, (∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 G (0, η)) →
      ∀ (v : ℝ) (η : Sv), (∀ b, ‖η b‖ ≤ ρ) →
        ContDiffAt ℝ 3 (fun z : (Fin 0 → ℝ) × (ℝ × Sv) => G (π z)) (0, v, η) := fun {G} hG v η hη =>
    ContDiffAt.comp (g := G) (f := π) (0, v, η) (hG η hη) hπs.contDiffAt
  obtain ⟨r₃, M₃, hr₃, hD₃⟩ := hDom _ 0 ρ μ
    (fun z => P0 (π z) - z.2.1 * R0 (π z)) hμc (fun v η _ hη =>
      (lift sP0 v η hη).sub (hvs.contDiffAt.mul (lift sR0 v η hη)))
  obtain ⟨r₄, M₄, hr₄, hD₄⟩ := hDom _ 0 ρ μ
    (fun z => FY (π z)) hμc (fun v η _ hη => lift sFY v η hη)
  have h3 : (0 : Fin 0 → ℝ) ∈ Metric.ball (0 : Fin 0 → ℝ) r₃ := Metric.mem_ball_self hr₃
  have h4 : (0 : Fin 0 → ℝ) ∈ Metric.ball (0 : Fin 0 → ℝ) r₄ := Metric.mem_ball_self hr₄
  set K : ℝ := max M₃ M₄ with hK
  set A : ℝ → Sv → ℝ := fun v η => P0 (0, η) - v * R0 (0, η) with hA
  set H : Sv → ℝ := fun η => FY (0, η) with hH
  have v0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hcont : ContinuousOn (fun v => gibbsMean μ (A v) H) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_gibbsMean hμ0 (R := K) (fun v hv => (hD₃ v hv).aestronglyMeasurable 0 h3)
      ((hD₄ 0 v0).aestronglyMeasurable 0 h4)
      (fun v hv => abs_le_of_dominated (dominated_mono (le_max_left _ _) (hD₃ v hv)) h3)
      (abs_le_of_dominated (dominated_mono (le_max_right _ _) (hD₄ 0 v0)) h4)
      (fun η => by fun_prop)
  have he : (fun v => cutoffMean ρ p (stepExponent false a ρA x m f v V) fun η =>
      cellCentredExpansion false a ρA m f Y η V) = fun v => gibbsMean μ (A v) H := by
    funext v
    rw [hμm]
    apply gibbsMean_congr_ae
    · filter_upwards [hμb] with η hη
      have h1 := hE.sum_eq η hη
      have h2 : stepExponent false a ρA x m f v V η =
          stepExponent false a ρA x m (fun _ _ _ => 0) 0 V η -
          v * ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false a ρA m f y η V := by
        simp [stepExponent]
      rw [h2, h1]
      simp only [hA, hP0, hR0, hVt0]
    · exact Filter.Eventually.of_forall fun η => by
        simp only [hH, hFY, hVt0]
  rw [he]
  exact hcont.intervalIntegrable_of_Icc zero_le_one
private theorem torusDecayFactor_pos (L : ℕ) (δ r : ℝ) : 0 < torusDecayFactor L δ r := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
private theorem one_le_torusDecayFactor {L : ℕ} {δ r : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r) :
    1 ≤ torusDecayFactor L δ r := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.one_le_decayWeight <;> assumption
private theorem torusDecayFactor_mono {L : ℕ} {δ r r' : ℝ} (hL : 0 < L) (hδ : 0 ≤ δ) (h0 : 0 ≤ r)
    (h : r ≤ r') : torusDecayFactor L δ r ≤ torusDecayFactor L δ r' := by
  unfold torusDecayFactor
  have hc : (0 : ℝ) < (L : ℝ) ^ (1 / 640 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hL) _
  have h1 : (r / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000 ≤ (r' / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000 :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right h hc.le) _
  refine mul_le_mul (max_le_max le_rfl h1) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
    (le_trans zero_le_one (le_max_left _ _))
  exact mul_le_mul_of_nonneg_left h hδ
abbrev _root_.YangMills.SharedProofs.p54195 := @torusDecayFactor_mono
private theorem exists_radius_decay_le {L : ℕ} {δ B e : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hB : 0 < B)
    (he : 0 < e) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r → B * Real.exp (-(2 * δ * r)) ≤ e / torusDecayFactor L δ r := by
  have hc : (0 : ℝ) < (L : ℝ) ^ (1 / 640 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hL) _
  set c := (L : ℝ) ^ (1 / 640 : ℝ) with hcdef
  set D : ℝ := (δ * c) ^ 16000 with hD
  have hD0 : 0 < D := by positivity
  have t1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 16000
  have t2 := Real.tendsto_exp_neg_atTop_nhds_zero
  have e1 : ∀ᶠ u : ℝ in Filter.atTop, u ^ 16000 * Real.exp (-u) < e * D / B :=
    (tendsto_order.1 t1).2 _ (by positivity)
  have e2 : ∀ᶠ u : ℝ in Filter.atTop, Real.exp (-u) < e / B :=
    (tendsto_order.1 t2).2 _ (by positivity)
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.1 (e1.and e2)
  refine ⟨⌈U / δ⌉₊, fun r hr => ?_⟩
  have hr' : U ≤ δ * r := by
    have : U / δ ≤ r := le_trans (Nat.le_ceil _) (by exact_mod_cast hr)
    rw [div_le_iff₀ hδ] at this
    linarith
  obtain ⟨u1, u2⟩ := hU _ hr'
  rw [le_div_iff₀ (torusDecayFactor_pos _ _ _)]
  unfold torusDecayFactor
  have hsplit : Real.exp (-(2 * δ * r)) * Real.exp (δ * r) = Real.exp (-(δ * r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hrew : ∀ M : ℝ, B * Real.exp (-(2 * δ * r)) * (M * Real.exp (δ * r)) =
      B * M * Real.exp (-(δ * r)) := fun M => by
    rw [← hsplit]
    ring
  rw [hrew]
  rcases max_cases (1 : ℝ) (((r : ℝ) / c) ^ 16000) with ⟨hm, -⟩ | ⟨hm, -⟩
  · rw [hm, mul_one]
    have := (lt_div_iff₀ hB).mp u2
    linarith
  · rw [hm]
    have h1 := (lt_div_iff₀ hB).mp u1
    have h2 : ((r : ℝ) / c) ^ 16000 * D = (δ * r) ^ 16000 := by
      rw [hD, ← mul_pow]
      congr 1
      field_simp
    have h3 : B * ((r : ℝ) / c) ^ 16000 * Real.exp (-(δ * r)) * D =
        (δ * r) ^ 16000 * Real.exp (-(δ * r)) * B := by
      rw [← h2]
      ring
    have h4 : B * ((r : ℝ) / c) ^ 16000 * Real.exp (-(δ * r)) * D ≤ e * D := by
      rw [h3]
      exact h1.le
    exact le_of_mul_le_mul_right h4 hD0
private theorem interpolation_bound_le {κ c τ : ℝ} {r k : ℕ} (hκ : 0 < κ) (hc : 0 < c) (hτ : 0 < τ)
    (hk1 : 1 ≤ k) (hk2 : k ≤ 2) :
    c * Real.exp (-(κ * r / 2 ^ 7)) / τ ^ k +
        (c * Real.exp (-(κ * r / 2 ^ 7))) ^ (1 - (k : ℝ) / 3) * c ^ ((k : ℝ) / 3) ≤
      c * (1 + 1 / τ + (1 / τ) ^ 2) * Real.exp (-(κ / 2 ^ 9 * r)) := by apply _root_.YangMills.Construction.InterpolatedBirths.interpolation_sum_le <;> assumption
private theorem eventuallyInParameters_of_coupling_floor {P Q : StepParameters → Prop}
    (H : EventuallyInParameters P)
    (hQ : ∀ T : StepParameters, T.IsOrdered → ∃ y : ℝ, ∀ y₁ : ℝ, y ≤ y₁ → 64 ≤ T.n₀ →
      P { T with coupling := y₁ } → Q { T with coupling := y₁ }) :
    EventuallyInParameters Q := by
  intro a ha
  obtain ⟨L₀, h⟩ := H a ha
  refine ⟨L₀, fun L hL hLe c hc => ?_⟩
  obtain ⟨Ct₀, h⟩ := h L hL hLe c hc
  refine ⟨Ct₀, fun Ct hCt => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h Ct hCt
  refine ⟨κ₀, hκ₀, fun κ hκ hκ' => ?_⟩
  obtain ⟨η₀, hη₀, h⟩ := h κ hκ hκ'
  refine ⟨η₀, hη₀, fun η₃ h1 h2 h3 => ?_⟩
  obtain ⟨N₀, h⟩ := h η₃ h1 h2 h3
  refine ⟨N₀, fun nss hn => ?_⟩
  obtain ⟨σ₀, hσ₀, h⟩ := h nss hn
  refine ⟨σ₀, hσ₀, fun σ hσ hσ' p hp => ?_⟩
  obtain ⟨C₀, h⟩ := h σ hσ hσ' p hp
  refine ⟨C₀, fun Cs hCs E hE => ?_⟩
  obtain ⟨m₀, h⟩ := h Cs hCs E hE
  refine ⟨max m₀ 64, fun n₀ hn₀ => ?_⟩
  obtain ⟨C₁, h⟩ := h n₀ (le_trans (le_max_left _ _) hn₀)
  refine ⟨C₁, fun CE hCE => ?_⟩
  obtain ⟨y₀, h⟩ := h CE hCE
  obtain ⟨y₂, h'⟩ := hQ ⟨a, L, c, Ct, κ, η₃, nss, σ, p, Cs, E, n₀, CE, 0⟩
    ⟨ha, hL, hc, hκ, h1, h2, hσ, hp, hE⟩
  exact ⟨max y₀ y₂, fun y₁ hy₁ => h' y₁ (le_trans (le_max_right _ _) hy₁)
    (le_trans (le_max_right _ _) hn₀) (h y₁ (le_trans (le_max_left _ _) hy₁))⟩
private def InterpolationBound (C : ℝ) : Prop :=
  ∀ (F F' : BlockFrame) (G : F.GaugeField F.top → ℝ) (G' : F'.GaugeField F'.top → ℝ)
    (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (c' : Fin k → F'.Site F'.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ₀ M₀ M₃ : ℝ),
    1 ≤ k → k ≤ 2 → 0 < τ₀ → 0 < M₀ → 0 ≤ M₃ →
    (∀ ς : Fin k → ℝ, (∀ l, ς l = 1 ∨ ς l = -1) →
      IsControlledAlongLine G V c (fun l => ς l • X l) τ₀ M₃ ∧
      IsControlledAlongLine G' V' c' (fun l => ς l • X l) τ₀ M₃ ∧
      ∀ s : ℝ, |s| ≤ τ₀ → |G (alongLine c (fun l => ς l • X l) s V) -
        G' (alongLine c' (fun l => ς l • X l) s V')| ≤ M₀) →
    |bondDeriv G V c X - bondDeriv G' V' c' X| ≤
      C * (M₀ / τ₀ ^ k + M₀ ^ (1 - (k : ℝ) / 3) * M₃ ^ ((k : ℝ) / 3))
private def sizeConstant (T : StepParameters) : ℝ := |T.CE| + T.energyRatio + 1
private def tailConstant (T : StepParameters) (C : ℝ) : ℝ :=
  (2 + C * (1 + 1 / (T.σ / 64) + (1 / (T.σ / 64)) ^ 2)) * sizeConstant T
private theorem isSmallCurvature_uniformField {F : BlockFrame} {s : ℝ} (hs : 0 < s) :
    IsSmallCurvature s (uniformField F F.top) := by apply _root_.YangMills.Construction.BlockMeans.SegmentMean.isSmallCurvature_uniformField <;> assumption
set_option maxHeartbeats 1600000 in
private theorem stepDensityIsLocal_of_params (T : StepParameters) (hT : T.IsOrdered) (h64 : 64 ≤ T.n₀)
    (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedFamilyOnClosedBalls)
    (hLines : SmallCurvatureAlongLineAndAgreeOn) (hFlat : stepFramesAtUniformTop)
    {C : ℝ} (hC : 0 < C) (hTw : InterpolationBound C) (N : ℕ)
    (hfar : ∀ r : ℕ, N ≤ r → tailConstant T C * Real.exp (-(T.κ / 2 ^ 9 * r)) ≤
      2⁻¹ ^ 4 * T.E / torusDecayFactor T.L T.decayRate r)
    (hfl : ∀ x : ℝ, T.coupling ≤ x → 1 ≤ x ∧ 16 ≤ frameRadius x ∧
      4 * (|T.CE| * x ^ (-(1 / 2 : ℝ))) ≤ 2⁻¹ ^ 5 * T.E / torusDecayFactor T.L T.decayRate N)
    (hN : StepDensityNearFrame T) (hD : StepDensityThirdDeriv T)
    (hTr : expansionTransportAt T) (hFr : MeansLocalizeAt T) (hSm : MeansContDiffThreeAt T)
    (hX : CellExponentsBoundedAt T) (hR : CentredExpansionsBoundedAt T) :
    StepDensityIsLocal T := by
  intro t x f hx hf F F' hF hF' Y Y' V V' r k h X hV hV' hag hk hbox hU
  beta_reduce
  obtain ⟨hx1, hm16, hxe⟩ := hfl x hx
  have hσ : 0 < T.σ := hT.σ_pos
  have hκ : 0 < T.κ := hT.κ_pos
  have hE0 : 0 < T.E := by linarith [hT.one_le_E]
  have hE₃ : 0 < T.energyRatio := div_pos hE0 hT.η₃_pos
  have hδ : 0 < T.decayRate := by
    show 0 < T.κ / 2 ^ 10
    positivity
  have hLpos : 0 < T.L := hT.odd_L.pos
  have hρ : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  have hτ : 0 < T.σ / 64 := hρ
  have hmono : ∀ {F₁ : BlockFrame} {W : F₁.GaugeField F₁.top}, IsSmallCurvature (9 / 8 * T.σ) W →
      IsSmallCurvature (5 / 4 * T.σ) W := fun h p hp => (h p hp).trans_le (by nlinarith)
  have hV5 := hmono hV
  have hV5' := hmono hV'
  have hσ5 : 0 < 5 / 4 * T.σ := by positivity
  have hag0 : AgreeOnBall (finiteCells F) (uniformField F F.top) (finiteCells F')
      (uniformField F' F'.top) Y Y' r :=
    ⟨hag.1, hag.2.1, hag.2.2.1, fun _ _ => rfl⟩
  set c : ℝ := sizeConstant T with hcdef
  have hc0 : 0 < c := by
    have := abs_nonneg T.CE
    simp only [hcdef, sizeConstant]
    linarith
  have hCEc : T.CE ≤ c := by
    have := le_abs_self T.CE
    simp only [hcdef, sizeConstant]
    linarith
  have hint : ∀ (F₁ : BlockFrame), IsCubicTopTorus T.L t T.n₀ F₁ → ∀ (Y₁ : F₁.Cell)
      (W : F₁.GaugeField F₁.top), IsSmallCurvature (5 / 4 * T.σ) W →
      IntervalIntegrable (fun v => cutoffMean T.ballRadius T.p
        (stepExponent false T.a T.chainParams.ρA x (frameRadius x) f v W) fun η =>
          cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) f Y₁ η W) volume 0 1 :=
    fun F₁ hF₁ Y₁ W hW => intervalIntegrable_cutoffMean hρ hT.cutoff hRim hDom
      (hX t x F₁ W false hx hF₁ hW).1 (hR t x f F₁ W false hx hf hF₁ hW) Y₁
  have hval : ∀ (W : F.GaugeField F.top) (W' : F'.GaugeField F'.top),
      IsSmallCurvature (5 / 4 * T.σ) W → IsSmallCurvature (5 / 4 * T.σ) W' →
      AgreeOnBall (finiteCells F) W (finiteCells F') W' Y Y' r →
      |stepDensityFamily T x f F Y W - stepDensityFamily T x f F' Y' W'| ≤
        c * Real.exp (-(T.κ * r / 2 ^ 7)) := by
    intro W W' hW hW' hagW
    have hfr := hFr t x f F W hx hf hF hW false F' W' Y Y' r hF' hW' hagW
    have e : stepDensityFamily T x f F Y W - stepDensityFamily T x f F' Y' W' =
        ∫ v in (0 : ℝ)..1, (cutoffMean T.ballRadius T.p
          (stepExponent false T.a T.chainParams.ρA x (frameRadius x) f v W) (fun η =>
            cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) f Y η W) -
          cutoffMean T.ballRadius T.p
          (stepExponent false T.a T.chainParams.ρA x (frameRadius x) f v W') (fun η =>
            cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) f Y' η W')) := by
      rw [intervalIntegral.integral_sub (hint F hF Y W hW) (hint F' hF' Y' W' hW')]
      rfl
    rw [e]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := T.CE * Real.exp (-(T.κ * r / 2 ^ 7)))
      (f := fun v => cutoffMean T.ballRadius T.p
          (stepExponent false T.a T.chainParams.ρA x (frameRadius x) f v W) (fun η =>
            cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) f Y η W) -
          cutoffMean T.ballRadius T.p
          (stepExponent false T.a T.chainParams.ρA x (frameRadius x) f v W') (fun η =>
            cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) f Y' η W')) (fun v hv => by
        rw [Set.uIoc_of_le zero_le_one] at hv
        rw [Real.norm_eq_abs]
        exact (hfr v hv.1.le hv.2).2)
    have hb' : |∫ v in (0 : ℝ)..1, (cutoffMean T.ballRadius T.p
          (stepExponent false T.a T.chainParams.ρA x (frameRadius x) f v W) (fun η =>
            cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) f Y η W) -
          cutoffMean T.ballRadius T.p
          (stepExponent false T.a T.chainParams.ρA x (frameRadius x) f v W') (fun η =>
            cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) f Y' η W'))| ≤
        T.CE * Real.exp (-(T.κ * r / 2 ^ 7)) := by
      simpa using hb
    exact hb'.trans (mul_le_mul_of_nonneg_right hCEc (Real.exp_pos _).le)
  set e' : ℝ := |T.CE| * x ^ (-(1 / 2 : ℝ)) with he'
  have hx0 : 0 ≤ x := by linarith
  have hxp : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0 _
  have hxle : x ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hlee : ∀ n : ℕ, T.CE * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 * n)) ≤ e' := by
    intro n
    have he1 : Real.exp (-(T.κ / 2 ^ 6 * n)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ T.κ / 2 ^ 6 * n := by positivity
      linarith
    have h1 : T.CE * x ^ (-(1 / 2 : ℝ)) ≤ e' :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hxp
    have h0 : 0 ≤ e' := by positivity
    calc T.CE * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 * n))
        ≤ e' * Real.exp (-(T.κ / 2 ^ 6 * n)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ e' * 1 := mul_le_mul_of_nonneg_left he1 h0
      _ = e' := mul_one _
  have hnear0 : ∀ (F₁ : BlockFrame), IsCubicTopTorus T.L t T.n₀ F₁ → ∀ (Y₁ : F₁.Cell)
      (W : F₁.GaugeField F₁.top), IsSmallCurvature (5 / 4 * T.σ) W →
      |stepDensityFamily T x f F₁ Y₁ W - expansionAtFrameFamily T false x f F₁ Y₁ W| ≤ e' :=
    fun F₁ hF₁ Y₁ W hW =>
      ((hN t x f hx hf F₁ hF₁ Y₁ W hW).1).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hxp)
  have hzero : ∀ (F₁ : BlockFrame), IsCubicTopTorus T.L t T.n₀ F₁ → ∀ Y₁ : F₁.Cell,
      expansionAtFrameFamily T false x f F₁ Y₁ (uniformField F₁ F₁.top) = 0 := by
    intro F₁ hF₁ Y₁
    have hch : IsBlockTorus T.L F₁ := by
      obtain ⟨hL, -, n, hs, hn⟩ := hF₁
      exact ⟨hL, n, by omega, hs⟩
    have h2 := (hFlat T.a T.L T.chainParams (frameRadius x) hT.one_le_a hT.odd_L hT.chain_admissible
      hm16 F₁ false hch).2
    show cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) f Y₁ 0 (uniformField F₁ F₁.top) = 0
    unfold cellCentredExpansion centredExpansion
    rw [h2]
    simp [subtractTrivial]
  have hloc := (hTr t x f F V hx hf hF hV5 false).2 F' V' Y Y' r hF' hV5' hag k h X hk hbox hU
  set g : ℝ := 2⁻¹ ^ 5 * T.E / torusDecayFactor T.L T.decayRate r with hg
  have htarget : 2⁻¹ ^ 4 * T.E / torusDecayFactor T.L T.decayRate r = 2 * g := by
    rw [hg]
    ring
  have hsmall : r < N → 4 * e' ≤ g := fun hr => hxe.trans <|
    div_le_div_of_nonneg_left (by positivity) (torusDecayFactor_pos _ _ _)
      (torusDecayFactor_mono hLpos hδ.le (Nat.cast_nonneg _) (by exact_mod_cast hr.le))
  have hE01 : Real.exp (-(T.κ * r / 2 ^ 7)) ≤ Real.exp (-(T.κ / 2 ^ 9 * r)) := by
    apply Real.exp_le_exp.mpr
    have e : T.κ / 2 ^ 9 * r = T.κ * r / 2 ^ 9 := by ring
    have hr : 0 ≤ T.κ * r := by positivity
    rw [e]
    nlinarith
  set J : ℝ := 1 + 1 / (T.σ / 64) + (1 / (T.σ / 64)) ^ 2 with hJ
  have hfarc : tailConstant T C = (2 + C * J) * c := rfl
  set E₁ := Real.exp (-(T.κ / 2 ^ 9 * r)) with hE₁
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [bondDeriv_zero, bondDeriv_zero]
    rw [bondDeriv_zero, bondDeriv_zero] at hloc
    show |(stepDensityFamily T x f F Y V - stepDensityFamily T x f F Y (uniformField F F.top)) -
      (stepDensityFamily T x f F' Y' V' - stepDensityFamily T x f F' Y' (uniformField F' F'.top))| ≤ _
    rw [htarget]
    by_cases hr : r < N
    · have hloc' : |expansionAtFrameFamily T false x f F Y V - expansionAtFrameFamily T false x f F' Y' V'| ≤ g :=
        hloc
      have n1 := hnear0 F hF Y V hV5
      have n2 := hnear0 F hF Y _ (isSmallCurvature_uniformField hσ5)
      have n3 := hnear0 F' hF' Y' V' hV5'
      have n4 := hnear0 F' hF' Y' _ (isSmallCurvature_uniformField hσ5)
      rw [hzero F hF Y, sub_zero] at n2
      rw [hzero F' hF' Y', sub_zero] at n4
      have hs := hsmall hr
      rw [abs_le] at n1 n2 n3 n4 hloc' ⊢
      constructor <;> linarith [n1.1, n1.2, n2.1, n2.2, n3.1, n3.2, n4.1, n4.2, hloc'.1, hloc'.2]
    · have hfr : tailConstant T C * E₁ ≤ 2 * g := by
        have h0 := hfar r (not_lt.1 hr)
        rwa [htarget] at h0
      have v1 := hval V V' hV5 hV5' hag
      have v2 := hval _ _ (isSmallCurvature_uniformField hσ5) (isSmallCurvature_uniformField hσ5) hag0
      have hcE : c * Real.exp (-(T.κ * r / 2 ^ 7)) ≤ c * E₁ := mul_le_mul_of_nonneg_left hE01 hc0.le
      have h3 : 2 * (c * E₁) ≤ tailConstant T C * E₁ := by
        rw [hfarc]
        have : 0 ≤ C * J * (c * E₁) := by positivity
        nlinarith
      rw [abs_le] at v1 v2 ⊢
      constructor <;> linarith [v1.1, v1.2, v2.1, v2.2]
  · have hk2 : k ≤ 2 := hk
    have hsm : ∀ (F₁ : BlockFrame), IsCubicTopTorus T.L t T.n₀ F₁ → ∀ (Y₁ : F₁.Cell)
        (W : F₁.GaugeField F₁.top), IsSmallCurvature (5 / 4 * T.σ) W →
        ContDiffThreeAlongBonds (stepDensityFamily T x f F₁ Y₁) W :=
      fun F₁ hF₁ Y₁ W hW => (hSm t x hx f hf F₁ hF₁ Y₁ W hW).2
    have d1 : bondDeriv (centredFamily (stepDensityFamily T x f) F Y) V (bondsAt Y h) X =
        bondDeriv (stepDensityFamily T x f F Y) V (bondsAt Y h) X :=
      bondDeriv_sub_const _ V _ X _ hk0 (by omega) (hsm F hF Y V hV5 k _ X)
    have d2 : bondDeriv (centredFamily (stepDensityFamily T x f) F' Y') V' (bondsAt Y' h) X =
        bondDeriv (stepDensityFamily T x f F' Y') V' (bondsAt Y' h) X :=
      bondDeriv_sub_const _ V' _ X _ hk0 (by omega) (hsm F' hF' Y' V' hV5' k _ X)
    rw [d1, d2, htarget]
    by_cases hr : r < N
    · have n1 := ((hN t x f hx hf F hF Y V hV5).2 k (bondsAt Y h) X hk0 hk2 hU).trans (hlee _)
      have n2 := ((hN t x f hx hf F' hF' Y' V' hV5').2 k (bondsAt Y' h) X hk0 hk2 hU).trans (hlee _)
      have hloc' : |bondDeriv (expansionAtFrameFamily T false x f F Y) V (bondsAt Y h) X -
          bondDeriv (expansionAtFrameFamily T false x f F' Y') V' (bondsAt Y' h) X| ≤ g := hloc
      have hs := hsmall hr
      have h0 : 0 ≤ e' := by positivity
      rw [abs_le] at n1 n2 hloc' ⊢
      constructor <;> linarith [n1.1, n1.2, n2.1, n2.2, hloc'.1, hloc'.2]
    · have hfr : tailConstant T C * E₁ ≤ 2 * g := by
        have h0 := hfar r (not_lt.1 hr)
        rwa [htarget] at h0
      have hM₀ : 0 < c * Real.exp (-(T.κ * r / 2 ^ 7)) := by positivity
      have hmove : ∀ (ς : Fin k → ℝ), (∀ l, ς l = 1 ∨ ς l = -1) → ∀ l, ‖ς l • X l‖ = 1 := by
        intro ς hς l
        rw [norm_smul, hU l, mul_one]
        rcases hς l with h1 | h1 <;> simp [h1]
      have hline : ∀ {F₁ : BlockFrame} (V₁ : F₁.GaugeField F₁.top) (c₁ : Fin k → F₁.Site F₁.top × Fin 4)
          (X₁ : Fin k → imaginaryQuaternions) (s : ℝ), (∀ l, ‖X₁ l‖ = 1) → |s| ≤ T.σ / 64 →
          IsSmallCurvature (9 / 8 * T.σ) V₁ →
          IsSmallCurvature (5 / 4 * T.σ) (alongLine c₁ X₁ s V₁) := by
        intro F₁ V₁ c₁ X₁ s hu hs hV₁ p hp
        have h1 := hLines.1 F₁ V₁ k c₁ X₁ s (9 / 8 * T.σ) (fun l => (hu l).le) hV₁ p hp
        refine h1.trans_le ?_
        have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
        nlinarith
      have hthird : ∀ (F₁ : BlockFrame), IsCubicTopTorus T.L t T.n₀ F₁ → ∀ (Y₁ : F₁.Cell)
          (W : F₁.GaugeField F₁.top) (c₁ : Fin 3 → F₁.Site F₁.top × Fin 4)
          (X₁ : Fin 3 → imaginaryQuaternions), IsSmallCurvature (5 / 4 * T.σ) W →
          AreUnitVectors X₁ → |bondDeriv (stepDensityFamily T x f F₁ Y₁) W c₁ X₁| ≤ c := by
        intro F₁ hF₁ Y₁ W c₁ X₁ hW hX₁
        have h1 := hD t x f hx hf F₁ hF₁ Y₁ W c₁ X₁ hW hX₁
        have h2 := hlee (bondSpan Y₁ c₁)
        have h3 : 2⁻¹ ^ 6 * T.energyRatio / torusDecayFactor T.L T.decayRate (bondSpan Y₁ c₁) ≤
            2⁻¹ ^ 6 * T.energyRatio :=
          div_le_self (by positivity) (one_le_torusDecayFactor hδ.le (Nat.cast_nonneg _))
        have h5 : e' ≤ |T.CE| := by
          have := mul_le_mul_of_nonneg_left hxle (abs_nonneg T.CE)
          simpa [he'] using this
        have h6 : c = |T.CE| + T.energyRatio + 1 := rfl
        linarith
      have hread : ∀ (F₁ : BlockFrame), IsCubicTopTorus T.L t T.n₀ F₁ → ∀ (Y₁ : F₁.Cell)
          (V₁ : F₁.GaugeField F₁.top) (c₁ : Fin k → F₁.Site F₁.top × Fin 4)
          (X₁ : Fin k → imaginaryQuaternions), (∀ l, ‖X₁ l‖ = 1) →
          IsSmallCurvature (9 / 8 * T.σ) V₁ →
          IsControlledAlongLine (stepDensityFamily T x f F₁ Y₁) V₁ c₁ X₁ (T.σ / 64) c := by
        intro F₁ hF₁ Y₁ V₁ c₁ X₁ hu hV₁
        exact ⟨fun s hs => hsm F₁ hF₁ Y₁ _ (hline V₁ c₁ X₁ s hu hs hV₁), fun s hs e =>
          hthird F₁ hF₁ Y₁ _ (c₁ ∘ e) (X₁ ∘ e) (hline V₁ c₁ X₁ s hu hs hV₁) (fun l => hu (e l))⟩
      have h1 := hTw F F' (stepDensityFamily T x f F Y) (stepDensityFamily T x f F' Y') V V' k
        (bondsAt Y h) (bondsAt Y' h) X (T.σ / 64) (c * Real.exp (-(T.κ * r / 2 ^ 7))) c hk0 hk2 hτ
        hM₀ hc0.le
        (fun ς hς =>
          ⟨hread F hF Y V _ _ (hmove ς hς) hV, hread F' hF' Y' V' _ _ (hmove ς hς) hV', fun s hs =>
            hval _ _ (hline V _ _ s (hmove ς hς) hs hV) (hline V' _ _ s (hmove ς hς) hs hV')
              (hLines.2 F F' V V' Y Y' r k h _ s hag hbox)⟩)
      have h2 := interpolation_bound_le (r := r) hκ hc0 hτ hk0 hk2
      have h3 : C * (c * J * E₁) ≤ tailConstant T C * E₁ := by
        rw [hfarc]
        have : 0 ≤ c * E₁ := by positivity
        nlinarith
      exact h1.trans ((mul_le_mul_of_nonneg_left h2 hC.le).trans (h3.trans hfr))
end StepDensityLocality
open StepDensityLocality in
theorem stepDensityIsLocalStatement_holds (hJ : EventuallyInParametersCombines)
    (hN : stepDensityNearFrameStatement) (hD : stepDensityThirdDerivStatement)
    (hTr : expansionTransportStatement) (hFr : MeansLocalizeEventually) (hSm : meansContDiffThree)
    (hX : CellExponentsBounded) (hR : CentredExpansionsBounded)
    (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedFamilyOnClosedBalls)
    (hTw : DerivDiffLeOfCloseAlongLines) (hLines : SmallCurvatureAlongLineAndAgreeOn)
    (hFlat : stepFramesAtUniformTop) : stepDensityIsLocalStatement := by
  obtain ⟨join, -⟩ := hJ
  obtain ⟨C, hC, hTw⟩ := hTw
  show EventuallyInParameters StepDensityIsLocal
  refine eventuallyInParameters_of_coupling_floor
    (join _ _ hN (join _ _ hD (join _ _ hTr (join _ _ hFr (join _ _ hSm (join _ _ hX hR))))))
    fun T hT => ?_
  have hκ : 0 < T.κ := hT.κ_pos
  have hσ : 0 < T.σ := hT.σ_pos
  have hE0 : 0 < T.E := by linarith [hT.one_le_E]
  have hE₃ : 0 < T.energyRatio := div_pos hE0 hT.η₃_pos
  have hδ : 0 < T.decayRate := by
    show 0 < T.κ / 2 ^ 10
    positivity
  have hLpos : 0 < T.L := hT.odd_L.pos
  have hc0 : 0 < sizeConstant T := by
    have := abs_nonneg T.CE
    unfold sizeConstant
    linarith
  have hB : 0 < tailConstant T C := by
    unfold tailConstant
    positivity
  obtain ⟨N, hNb⟩ := exists_radius_decay_le (L := T.L) (δ := T.decayRate) (B := tailConstant T C)
    (e := 2⁻¹ ^ 4 * T.E) hLpos hδ hB (by positivity)
  set D : ℝ := 2⁻¹ ^ 5 * T.E / torusDecayFactor T.L T.decayRate N with hDdef
  have hD0 : 0 < D := div_pos (by positivity) (torusDecayFactor_pos _ _ _)
  refine ⟨max ((32768 : ℝ) ^ 100) (((4 * |T.CE| + 1) / D) ^ 2), fun y₁ hy h64 H => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := H
  refine stepDensityIsLocal_of_params { T with coupling := y₁ } ⟨hT.one_le_a, hT.odd_L,
    hT.chain_admissible, hT.κ_pos, hT.η₃_pos, hT.η₃_le_one, hT.σ_pos, hT.cutoff, hT.one_le_E⟩ h64
    hRim hDom hLines hFlat hC hTw N (fun r hr => ?_) (fun x hx => ?_) a1 a2 a3 a4 a5 a6 a7
  · have h := hNb r hr
    have e : 2 * T.decayRate * (r : ℝ) = T.κ / 2 ^ 9 * r := by
      show 2 * (T.κ / 2 ^ 10) * (r : ℝ) = _
      ring
    rw [e] at h
    exact h
  · have hyx : max ((32768 : ℝ) ^ 100) (((4 * |T.CE| + 1) / D) ^ 2) ≤ x := le_trans hy hx
    have hxA : (32768 : ℝ) ^ 100 ≤ x := le_trans (le_max_left _ _) hyx
    have hxB : ((4 * |T.CE| + 1) / D) ^ 2 ≤ x := le_trans (le_max_right _ _) hyx
    have hx1 : 1 ≤ x := le_trans (one_le_pow₀ (by norm_num)) hxA
    have hx0 : 0 ≤ x := by linarith
    refine ⟨hx1, ?_, ?_⟩
    · unfold frameRadius
      have h1 : (32768 : ℝ) ≤ x ^ (1 / 100 : ℝ) := by
        have h2 := Real.rpow_le_rpow (by positivity) hxA (show (0 : ℝ) ≤ 1 / 100 by norm_num)
        have e : ((32768 : ℝ) ^ 100) ^ (1 / 100 : ℝ) = 32768 := by
          have e2 : (1 / 100 : ℝ) = (((100 : ℕ) : ℝ))⁻¹ := by norm_num
          rw [e2]
          exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
        rwa [e] at h2
      have h2 : 32768 ≤ ⌈x ^ (1 / 100 : ℝ)⌉₊ := by
        have h3 : ((32768 : ℕ) : ℝ) ≤ ⌈x ^ (1 / 100 : ℝ)⌉₊ :=
          le_trans (by exact_mod_cast h1) (Nat.le_ceil _)
        exact_mod_cast h3
      exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
    · have hs : (4 * |T.CE| + 1) / D ≤ Real.sqrt x :=
        le_trans (le_abs_self _) (Real.abs_le_sqrt hxB)
      have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
      have e : x ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt x := by
        rw [Real.rpow_neg hx0, ← Real.sqrt_eq_rpow, one_div]
      have h3 : 4 * |T.CE| + 1 ≤ Real.sqrt x * D := (div_le_iff₀ hD0).mp hs
      show 4 * (|T.CE| * x ^ (-(1 / 2 : ℝ))) ≤ D
      rw [e]
      have h4 : 4 * (|T.CE| * (1 / Real.sqrt x)) = 4 * |T.CE| / Real.sqrt x := by ring
      rw [h4, div_le_iff₀ hs0]
      linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
