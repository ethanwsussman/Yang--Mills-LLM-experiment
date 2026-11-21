import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongARotationOfTheTop
import YangMills.Construction.SummableBoundsOfTheFlow.TheBirthsBetweenProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheCurvatureOfTheScaledMeansAtOneTopProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansAreSmoothInTheTop
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Quaternion
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames
namespace ScaledVariables
variable {F : BlockFrame}
private theorem eventually_isSmallCurvature_leftTranslate {k : ℕ} (hfin : Finite F.Cell) {s : ℝ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature s V) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0, IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by apply _root_.YangMills.Construction.InterpolatedBirths.eventually_isSmallCurvature_translate <;> assumption
private theorem bondDeriv_order_zero (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G V c X = G V := by apply _root_.YangMills.SharedProofs.p1654 <;> assumption
private theorem IsDominatedSmoothFamily.mono_bound {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ}
    {B : Set (Fin k → ℝ)} {K K' : ℝ} {G : (Fin k → ℝ) → Ω → ℝ} (hK : K ≤ K')
    (h : IsDominatedSmoothFamily μ 3 B K G) : IsDominatedSmoothFamily μ 3 B K' G := by
  refine ⟨h.aestronglyMeasurable, h.contDiffOn, ?_⟩
  filter_upwards [h.norm_iteratedFDeriv_le] with ω hω j hj τ hτ using le_trans (hω j hj τ hτ) hK
private theorem IsDominatedSmoothFamily.add' {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ}
    {B : Set (Fin k → ℝ)} (hB : IsOpen B) {K K' : ℝ} {G G' : (Fin k → ℝ) → Ω → ℝ}
    (h : IsDominatedSmoothFamily μ 3 B K G) (h' : IsDominatedSmoothFamily μ 3 B K' G') :
    IsDominatedSmoothFamily μ 3 B (K + K') fun τ ω => G τ ω + G' τ ω := by
  refine ⟨fun τ hτ => (h.aestronglyMeasurable τ hτ).add (h'.aestronglyMeasurable τ hτ), ?_, ?_⟩
  · filter_upwards [h.contDiffOn, h'.contDiffOn] with ω a b using a.add b
  · filter_upwards [h.contDiffOn, h'.contDiffOn, h.norm_iteratedFDeriv_le, h'.norm_iteratedFDeriv_le]
      with ω a b c d j hj τ hτ
    have hj' : ((j : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hj
    have ca : ContDiffAt ℝ j (fun τ => G τ ω) τ := (a.contDiffAt (hB.mem_nhds hτ)).of_le hj'
    have cb : ContDiffAt ℝ j (fun τ => G' τ ω) τ := (b.contDiffAt (hB.mem_nhds hτ)).of_le hj'
    have e : (fun τ => G τ ω + G' τ ω) = (fun τ => G τ ω) + fun τ => G' τ ω := rfl
    rw [e, iteratedFDeriv_add_apply ca cb]
    exact (norm_add_le _ _).trans (add_le_add (c j hj τ hτ) (d j hj τ hτ))
private theorem IsDominatedSmoothFamily.const_mul' {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ}
    {B : Set (Fin k → ℝ)} (hB : IsOpen B) {K : ℝ} {G : (Fin k → ℝ) → Ω → ℝ} (w : ℝ)
    (h : IsDominatedSmoothFamily μ 3 B K G) :
    IsDominatedSmoothFamily μ 3 B (|w| * K) fun τ ω => w * G τ ω := by
  refine ⟨fun τ hτ => (h.aestronglyMeasurable τ hτ).const_mul w, ?_, ?_⟩
  · filter_upwards [h.contDiffOn] with ω a using contDiffOn_const.mul a
  · filter_upwards [h.contDiffOn, h.norm_iteratedFDeriv_le] with ω a c j hj τ hτ
    have hj' : ((j : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hj
    have ca : ContDiffAt ℝ j (fun τ => G τ ω) τ := (a.contDiffAt (hB.mem_nhds hτ)).of_le hj'
    have e : (fun τ => w * G τ ω) = w • fun τ => G τ ω := rfl
    rw [e, iteratedFDeriv_const_smul_apply ca, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (c j hj τ hτ) (abs_nonneg _)
private theorem exists_isDominatedSmoothFamily_finset_sum {Ω ι : Type} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ}
    {B : Set (Fin k → ℝ)} (hB : IsOpen B) (S : Finset ι) {G : ι → (Fin k → ℝ) → Ω → ℝ}
    (h : ∀ i ∈ S, ∃ K, IsDominatedSmoothFamily μ 3 B K (G i)) :
    ∃ K, IsDominatedSmoothFamily μ 3 B K fun τ ω => ∑ i ∈ S, G i τ ω := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨0, fun τ _ => by simpa using aestronglyMeasurable_const, ?_, ?_⟩
    · exact Eventually.of_forall fun ω => by simpa using contDiffOn_const
    · refine Eventually.of_forall fun ω j _ τ _ => ?_
      simp
  | insert a S ha ih =>
    obtain ⟨K, hK⟩ := h a (Finset.mem_insert_self a S)
    obtain ⟨K', hK'⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨K + K', ?_⟩
    have := IsDominatedSmoothFamily.add' hB hK hK'
    simpa [Finset.sum_insert ha] using this
private theorem isDominatedSmoothFamily_const {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ}
    {B : Set (Fin k → ℝ)} {K : ℝ} (hK : 0 ≤ K) {g : Ω → ℝ} (hm : AEStronglyMeasurable g μ)
    (hb : ∀ᵐ ω ∂μ, |g ω| ≤ K) : IsDominatedSmoothFamily μ 3 B K fun _ ω => g ω := by
  refine ⟨fun _ _ => hm, Eventually.of_forall fun ω => contDiffOn_const, ?_⟩
  filter_upwards [hb] with ω hω j _ τ _
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    simpa [norm_iteratedFDeriv_zero] using hω
  · rw [iteratedFDeriv_const_of_ne h.ne', Pi.zero_apply, norm_zero]
    exact hK
private theorem gibbsMean_congr_ae {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {A A' H H' : Ω → ℝ}
    (hA : A =ᵐ[μ] A') (hH : H =ᵐ[μ] H') : gibbsMean μ A H = gibbsMean μ A' H' := by apply _root_.YangMills.Construction.InterpolatedBirths.gibbsMean_congr_ae <;> assumption
private theorem memScaledBalls_inv_smul {ρ s : ℝ} (hs : 0 < s) {η : StepVariable (finiteCells F)}
    (hη : ∀ b, ‖η b‖ < ρ) : MemScaledBalls ρ s (s⁻¹ • η) := by apply _root_.YangMills.SharedProofs.p27453 <;> assumption
private theorem isOpen_setOf_forall_norm_lt (ρ : ℝ) :
    IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < ρ} := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.isOpen_bondBall <;> assumption
private theorem exists_isDominatedSmoothFamily_of_isSmoothObservable {μ : Measure (StepVariable (finiteCells F))}
    {κ ρ s s' K r C₄ : ℝ} {k : ℕ}
    {Y : F.Cell} {V : F.GaugeField F.top} {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} (hρ : 0 < ρ) (hs : 0 < s) (hss : s ≤ s')
    (hκ : 0 < κ) (hK : 0 ≤ K) (hμ : ∀ᵐ η ∂μ, ∀ b, ‖η b‖ < ρ)
    (hchart : ∀ (f : F.GaugeField F.top → ℝ) (B' : ℝ), 0 ≤ B' →
      (∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ContDiffThreeAlongBonds f (leftTranslate (bondSpread c X τ) V)) →
      (∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ (j : ℕ) (c' : Fin j → F.Site F.top × Fin 4)
        (X' : Fin j → imaginaryQuaternions),
        j ≤ 3 → AreUnitVectors X' → |bondDeriv f (leftTranslate (bondSpread c X τ) V) c' X'| ≤ B') →
      ContDiffOn ℝ 3 (fun τ => f (leftTranslate (bondSpread c X τ) V)) (Metric.ball 0 r) ∧
        ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ j : ℕ, j ≤ 3 →
          ‖iteratedFDeriv ℝ j (fun τ => f (leftTranslate (bondSpread c X τ) V)) τ‖ ≤ C₄ * B')
    (hsm : ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r,
      IsSmoothObservable κ ρ s' K Y (leftTranslate (bondSpread c X τ) V) Ob) :
    ∃ K₁, IsDominatedSmoothFamily μ 3 (Metric.ball (0 : Fin k → ℝ) r) K₁
      fun τ η => Ob s (s⁻¹ • η) (leftTranslate (bondSpread c X τ) V) := by
  set N₀ : ℝ := (Fintype.card ↥(chordBonds (finiteCells F))) * (ρ / s) with hN₀
  set K₁ : ℝ := K * (1 + N₀) ^ 7 with hK₁
  have hK₁p : 0 ≤ K₁ := by positivity
  have hlocal : ∀ ζ : StepVariable (finiteCells F), MemScaledBalls ρ s ζ → localWeight κ Y ζ ≤ N₀ := by
    intro ζ hζ
    unfold localWeight
    calc _ ≤ ∑ _b : ↥(chordBonds (finiteCells F)), ρ / s := Finset.sum_le_sum fun b _ => by
          have h1 : Real.exp (-(2 ^ 4 * κ * cellSupDist (enclosingCell b.1.1) Y)) ≤ 1 := by
            apply Real.exp_le_one_iff.mpr
            have : 0 ≤ 2 ^ 4 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ) := by positivity
            linarith
          have h2 : ‖ζ b‖ ≤ ρ / s := by
            rw [le_div_iff₀ hs, mul_comm]
            exact (hζ b).le
          calc _ ≤ 1 * ‖ζ b‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
            _ ≤ _ := by simpa using h2
      _ = N₀ := by simp [hN₀]
  have hnonneg : ∀ ζ : StepVariable (finiteCells F), 0 ≤ localWeight κ Y ζ := fun ζ =>
    Finset.sum_nonneg fun b _ => by positivity
  have hkey : ∀ ζ : StepVariable (finiteCells F), MemScaledBalls ρ s ζ →
      ContDiffOn ℝ 3 (fun τ => Ob s ζ (leftTranslate (bondSpread c X τ) V)) (Metric.ball 0 r) ∧
        ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ j : ℕ, j ≤ 3 →
          ‖iteratedFDeriv ℝ j (fun τ => Ob s ζ (leftTranslate (bondSpread c X τ) V)) τ‖ ≤ C₄ * K₁ := by
    intro ζ hζ
    refine hchart (Ob s ζ) K₁ hK₁p (fun τ hτ k' c' X' => ?_) (fun τ hτ j c' X' hj hX' => ?_)
    · have h1 := (hsm τ hτ).contDiffAt s ζ k' c' X' (by rwa [abs_of_pos hs])
      have h2 : ContDiffAt ℝ 6 (fun τ' : Fin k' → ℝ =>
          (((s, ζ), τ') : (ℝ × StepVariable (finiteCells F)) × (Fin k' → ℝ))) 0 :=
        contDiffAt_const.prodMk contDiffAt_id
      exact (ContDiffAt.comp (0 : Fin k' → ℝ) h1 h2).of_le (by norm_num)
    · have h1 := (hsm τ hτ).deriv_le j 0 c' X' s ζ (Or.inl ⟨hj, by norm_num⟩) hX' hs hss hζ
      have e : scaleDeriv Ob (leftTranslate (bondSpread c X τ) V) c' X' 0 ζ s =
          bondDeriv (Ob s ζ) (leftTranslate (bondSpread c X τ) V) c' X' := by
        simp [scaleDeriv, iteratedDeriv_zero]
      rw [e] at h1
      refine h1.trans ?_
      have h2 : Real.exp (-(2 ^ 4 * κ * bondSpan Y c')) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have : 0 ≤ 2 ^ 4 * κ * (bondSpan Y c' : ℝ) := by positivity
        linarith
      have h3 : (1 + localWeight κ Y ζ) ^ 7 ≤ (1 + N₀) ^ 7 :=
        pow_le_pow_left₀ (by linarith [hnonneg ζ]) (by linarith [hlocal ζ hζ]) 7
      calc _ ≤ K * (1 + localWeight κ Y ζ) ^ 7 * 1 :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hK (pow_nonneg (by linarith [hnonneg ζ]) 7))
        _ ≤ K₁ := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left h3 hK
  refine ⟨C₄ * K₁, fun τ hτ => ?_, ?_, ?_⟩
  · have hc := (hsm τ hτ).continuousOn 0 0 Fin.elim0 Fin.elim0 (ρ / s + 1) (Or.inl ⟨by norm_num, by norm_num⟩)
    have hmeq : μ.restrict {η | ∀ b, ‖η b‖ < ρ} = μ := Measure.restrict_eq_self_of_ae_mem hμ
    rw [← hmeq]
    refine ContinuousOn.aestronglyMeasurable ?_ (isOpen_setOf_forall_norm_lt ρ).measurableSet
    have hcomp : ContinuousOn
        (fun η : StepVariable (finiteCells F) => ((s, s⁻¹ • η) : ℝ × StepVariable (finiteCells F)))
        {η | ∀ b, ‖η b‖ < ρ} := (continuous_const.prodMk (continuous_const_smul _)).continuousOn
    refine (hc.comp hcomp ?_).congr ?_
    · intro η hη
      have hz := memScaledBalls_inv_smul hs hη
      refine ⟨hs.le, hss, hz, fun b => ?_⟩
      · have h1 : s * ‖(s⁻¹ • η) b‖ < ρ := hz b
        have h2 : ‖(s⁻¹ • η) b‖ < ρ / s := by
          rw [lt_div_iff₀ hs, mul_comm]
          exact h1
        linarith
    · intro η _
      simp only [Function.comp, scaleDeriv, iteratedDeriv_zero]
      rw [bondDeriv_order_zero]
  · filter_upwards [hμ] with η hη using (hkey _ (memScaledBalls_inv_smul hs hη)).1
  · filter_upwards [hμ] with η hη j hj τ hτ using (hkey _ (memScaledBalls_inv_smul hs hη)).2 τ hτ j hj
private def quaternionI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
private def unitQuaternionI : imaginaryQuaternions := ⟨quaternionI, rfl⟩
private theorem norm_unitQuaternionI : ‖unitQuaternionI‖ = 1 := by
  show ‖quaternionI‖ = 1
  have h := Quaternion.normSq_eq_norm_mul_self quaternionI
  have e : Quaternion.normSq quaternionI = 1 := by
    rw [Quaternion.normSq_def']
    simp [quaternionI]
  rw [e] at h
  nlinarith [norm_nonneg quaternionI, sq_nonneg (‖quaternionI‖ - 1), sq_nonneg (‖quaternionI‖ + 1)]
open Classical in
private theorem exists_unitVectors_bondSpread_eq {k : ℕ} (X : Fin k → imaginaryQuaternions) :
    ∃ (u : Fin k → imaginaryQuaternions) (d : Fin k → ℝ), AreUnitVectors u ∧
      ∀ (c : Fin k → F.Site F.top × Fin 4) (τ : Fin k → ℝ),
        bondSpread c X τ = bondSpread c u fun l => d l * τ l := by
  refine ⟨fun l => if X l = 0 then unitQuaternionI else ‖X l‖⁻¹ • X l, fun l => ‖X l‖, fun l => ?_, fun c τ => ?_⟩
  · by_cases h : X l = 0
    · show ‖if X l = 0 then unitQuaternionI else ‖X l‖⁻¹ • X l‖ = 1
      rw [if_pos h]
      exact norm_unitQuaternionI
    · show ‖if X l = 0 then unitQuaternionI else ‖X l‖⁻¹ • X l‖ = 1
      rw [if_neg h, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]
  · funext y i
    unfold bondSpread
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h₁ : c l = (y, i)
    · rw [if_pos h₁, if_pos h₁]
      by_cases h₂ : X l = 0
      · simp [h₂]
      · show τ l • X l = (‖X l‖ * τ l) • (if X l = 0 then unitQuaternionI else ‖X l‖⁻¹ • X l)
        rw [if_neg h₂, smul_smul]
        have : ‖X l‖ * τ l * ‖X l‖⁻¹ = τ l := by
          have := norm_ne_zero_iff.2 h₂
          field_simp
        rw [this]
    · rw [if_neg h₁, if_neg h₁]
theorem observableMeanContDiffThreeStatement_holds (hS : StepDensities.rescaledPartsSmoothStatement)
    (hFl : rescaledExponentFloorStatement) (hSum : lawExponentDecompositionStatement)
    (hC : Estimates.ContDiffBoundAlongRotationOfTop) (hRim : CutoffMeanIsGibbsMean)
    (hW : GibbsMeanDifferentiation) : observableMeanContDiffThreeStatement := by
  unfold observableMeanContDiffThreeStatement ForallSmoothObservables
  refine EventuallyOrdered.mono (EventuallyOrdered.and hS hFl) ?_
  rintro T hT hn₁ ⟨gS, gF⟩ e
  obtain ⟨l₂, K₂, hl₂, hK₂, gS⟩ := gS e
  obtain ⟨l₃, hl₃, gF⟩ := gF e
  refine ⟨min l₂ l₃, 1, lt_min hl₂ hl₃, one_pos,
    fun l₁ hl hle t f F V Y law K Ob _ _ _ hf hF hV hLw hK hO _ s hs hs₁ k c' X' => ?_⟩
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    show 0 < T.σ / 64
    positivity
  have hκ := hT.κ_pos
  have hs₂ : s ≤ l₂ := hs₁.trans (hle.trans (min_le_left _ _))
  have hs₃ : s ≤ l₃ := hs₁.trans (hle.trans (min_le_right _ _))
  have hfin : Finite F.Cell := by
    obtain ⟨-, -, n, hside, hn⟩ := hF
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      rw [hper, hside]
      omega⟩
    exact Pi.finite
  obtain ⟨X, d, hX, hsp⟩ := exists_unitVectors_bondSpread_eq (F := F) X'
  obtain ⟨C₄, hC₄, chart⟩ := hC k
  obtain ⟨r₀, hr₀, hcold⟩ :=
    Metric.eventually_nhds_iff_ball.mp (eventually_isSmallCurvature_leftTranslate hfin c' X hV)
  set r : ℝ := min r₀ (1 / (k + 1)) with hr
  have hrpos : 0 < r := lt_min hr₀ (by positivity)
  have hkr : (k : ℝ) * r ≤ 1 := by
    have h1 : r ≤ 1 / (k + 1) := min_le_right _ _
    calc (k : ℝ) * r ≤ k * (1 / (k + 1)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        linarith
  have cold : ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r,
      IsSmallCurvature (5 / 4 * T.σ) (leftTranslate (bondSpread c' X τ) V) :=
    fun τ hτ => hcold τ (Metric.ball_subset_ball (min_le_left _ _) hτ)
  have chartL := fun (f' : F.GaugeField F.top → ℝ) (B' : ℝ) (hB' : 0 ≤ B') ha hb =>
    chart F V c' X f' r B' hX hrpos hkr hB' ha hb
  obtain ⟨hfinμ, hμ0, hμb, hμm⟩ := hRim F T.ballRadius T.p hρ hT.cutoff
  set μ := cutoffLaw F T.ballRadius T.p with hμ
  set B := Metric.ball (0 : Fin k → ℝ) r with hB
  have hBo : IsOpen B := Metric.isOpen_ball
  obtain ⟨KH, dH⟩ := exists_isDominatedSmoothFamily_of_isSmoothObservable (μ := μ) (Ob := Ob) (κ := T.κ) (s := s)
    (s' := 2 * l₁) (K := K) hρ hs (by linarith) hκ hK hμb chartL (fun τ hτ => hO _ (cold τ hτ))
  have dP : ∀ Y' ∈ finiteCells F, ∃ K', IsDominatedSmoothFamily μ 3 B K' fun τ η =>
      rescaledCellRemainder T.a T.ρA T.lam s Y' (leftTranslate (bondSpread c' X τ) V) (s⁻¹ • η) := fun Y' _ =>
    exists_isDominatedSmoothFamily_of_isSmoothObservable (μ := μ)
      (Ob := fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y' V' ζ) (κ := T.κ) (s := s)
      (s' := s) (K := K₂) hρ hs le_rfl hκ hK₂ hμb chartL
      (fun τ hτ => (gS s hs hs₂ t f F _ Y' hf hF (cold τ hτ)).1)
  have dR : ∀ Y' ∈ finiteCells F, ∃ K', IsDominatedSmoothFamily μ 3 B K' fun τ η =>
      rescaledCellExpansion T.a T.ρA f s Y' (leftTranslate (bondSpread c' X τ) V) (s⁻¹ • η) := fun Y' _ =>
    exists_isDominatedSmoothFamily_of_isSmoothObservable (μ := μ)
      (Ob := fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y' V' ζ) (κ := T.κ) (s := s)
      (s' := s) (K := K₂) hρ hs le_rfl hκ hK₂ hμb chartL
      (fun τ hτ => (gS s hs hs₂ t f F _ Y' hf hF (cold τ hτ)).2)
  obtain ⟨KP, dP⟩ := exists_isDominatedSmoothFamily_finset_sum hBo (finiteCells F) dP
  obtain ⟨KR, dR⟩ := exists_isDominatedSmoothFamily_finset_sum hBo (finiteCells F) dR
  set sq : StepVariable (finiteCells F) → ℝ :=
    fun η => T.lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖(s⁻¹ • η) b‖ ^ 2 with hsq
  have hsqc : Continuous sq := by
    refine continuous_const.mul (continuous_finsetSum _ fun b _ => ?_)
    exact ((continuous_apply b).comp (continuous_const_smul _)).norm.pow 2
  obtain ⟨Ksq, hKsq₀, hKsq⟩ : ∃ Ksq : ℝ, 0 ≤ Ksq ∧ ∀ᵐ η ∂μ, |sq η| ≤ Ksq := by
    refine ⟨|T.lam / 2| * ∑ _b : ↥(chordBonds (finiteCells F)), (T.ballRadius / s) ^ 2, by positivity, ?_⟩
    filter_upwards [hμb] with η hη
    have hz := memScaledBalls_inv_smul hs hη
    simp only [hsq]
    have hs0 : 0 ≤ ∑ b : ↥(chordBonds (finiteCells F)), ‖(s⁻¹ • η) b‖ ^ 2 :=
      Finset.sum_nonneg fun b _ => by positivity
    rw [abs_mul, abs_of_nonneg hs0]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) (abs_nonneg _)
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    rw [le_div_iff₀ hs, mul_comm]
    exact (hz b).le
  have dA := IsDominatedSmoothFamily.add' hBo
    (IsDominatedSmoothFamily.add' hBo (IsDominatedSmoothFamily.const_mul' hBo (remainderCoefficient law) dP)
      (isDominatedSmoothFamily_const (B := B) hKsq₀ hsqc.aestronglyMeasurable hKsq))
    (IsDominatedSmoothFamily.const_mul' hBo (-expansionCoefficient law) dR)
  have := hfinμ
  have hM := (hW.2 _ μ k B (max _ KH) _ _ hBo hμ0 (IsDominatedSmoothFamily.mono_bound (le_max_left _ _) dA)
    (IsDominatedSmoothFamily.mono_bound (le_max_right _ _) dH)).1
  have hB0 : B ∈ 𝓝 (0 : Fin k → ℝ) := Metric.ball_mem_nhds _ hrpos
  have hψ : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ =>
      observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob s (leftTranslate (bondSpread c' X τ) V)) 0 := by
    refine (hM.contDiffAt hB0).congr_of_eventuallyEq ?_
    filter_upwards [hB0] with τ hτ
    unfold observableMean rescaledMean
    rw [hμm]
    apply gibbsMean_congr_ae
    · filter_upwards [hμb] with η hη
      have h1 := (gF t f F _ law hf hF (cold τ hτ) hLw).2.1 s (s⁻¹ • η) hs hs₃ (memScaledBalls_inv_smul hs hη)
      rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul] at h1
      rw [h1, hSum F T.a T.ρA T.lam s f law _ _ hfin]
      simp only [hsq]
      ring
    · exact Filter.EventuallyEq.rfl
  have e : (fun τ : Fin k → ℝ =>
      observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob s (leftTranslate (bondSpread c' X' τ) V)) =
      (fun τ : Fin k → ℝ =>
        observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob s (leftTranslate (bondSpread c' X τ) V)) ∘
        fun τ l => d l * τ l := by
    funext τ
    simp only [Function.comp]
    rw [hsp c' τ]
  show ContDiffAt ℝ 3 (fun τ : Fin k → ℝ =>
    observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob s (leftTranslate (bondSpread c' X' τ) V)) 0
  rw [e]
  have hz : (fun l : Fin k => d l * (0 : Fin k → ℝ) l) = 0 := by
    funext l
    simp
  refine ContDiffAt.comp (0 : Fin k → ℝ) (by rw [hz]; exact hψ) ?_
  exact (contDiff_pi.2 fun l => contDiff_const.mul (contDiff_apply ℝ ℝ l)).contDiffAt
end ScaledVariables
end YangMills.Construction
end
