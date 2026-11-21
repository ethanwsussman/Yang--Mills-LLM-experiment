import YangMills.Construction.ClusterExpansionOfAStep.CovarianceOfAFunctionOfSomeBondsProof
import YangMills.Construction.ClusterExpansionOfAStep.FlowWhereTheExpansionReturns
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.ColdExpansionIsAnExpansionBelow
import YangMills.Construction.ResponseInTheExpansion.MomentsOfTheColdLawAtGivenParameters
import YangMills.Construction.ResponseInTheExpansion.MomentsOfTheFluctuationsOfAStep
import YangMills.Construction.ResponseInTheExpansion.OneStepDownKeepsTheBoxClear
import YangMills.Construction.ResponseInTheExpansion.OneStepIsTheLawOfTheMirror
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfTheMeanOfAPartProof
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
private theorem pow_le_add_inv_mul_pow {a ε : ℝ} (q r : ℕ) (ha : 0 ≤ a) (hε : 0 < ε) :
    a ^ q ≤ ε ^ q + (ε ^ r)⁻¹ * a ^ (q + r) := by
  rcases le_or_gt a ε with h | h
  · have h1 := pow_le_pow_left₀ ha h q
    have h2 : 0 ≤ (ε ^ r)⁻¹ * a ^ (q + r) := by positivity
    linarith
  · have h1 : ε ^ r ≤ a ^ r := pow_le_pow_left₀ hε.le h.le r
    have h2 : a ^ q * ε ^ r ≤ a ^ (q + r) := by
      rw [pow_add]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : a ^ q ≤ (ε ^ r)⁻¹ * a ^ (q + r) := by
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
      exact h2
    have := pow_nonneg hε.le q
    linarith
private theorem finsetSupNonneg_nonneg {α : Type} (S : Finset α) (f : α → ℝ) : 0 ≤ finsetSupNonneg S f :=
  (Finset.le_fold_max 0).2 (Or.inl le_rfl)
private theorem finsetSupNonneg_le {α : Type} {S : Finset α} {f : α → ℝ} {c : ℝ} (h0 : 0 ≤ c)
    (h : ∀ b ∈ S, f b ≤ c) : finsetSupNonneg S f ≤ c :=
  (Finset.fold_max_le c).2 ⟨h0, h⟩
private theorem le_finsetSupNonneg {α : Type} {S : Finset α} {f : α → ℝ} {b : α} (hb : b ∈ S) :
    f b ≤ finsetSupNonneg S f :=
  (Finset.le_fold_max _).2 (Or.inr ⟨b, hb, le_rfl⟩)
private theorem finsetSupNonneg_mono {α : Type} {S : Finset α} {f g : α → ℝ} (h : ∀ b ∈ S, f b ≤ g b) :
    finsetSupNonneg S f ≤ finsetSupNonneg S g :=
  finsetSupNonneg_le (finsetSupNonneg_nonneg _ _) fun b hb => (h b hb).trans (le_finsetSupNonneg hb)
private theorem finsetSupNonneg_congr {α : Type} {S : Finset α} {f g : α → ℝ} (h : ∀ b ∈ S, f b = g b) :
    finsetSupNonneg S f = finsetSupNonneg S g :=
  le_antisymm (finsetSupNonneg_mono fun b hb => (h b hb).le) (finsetSupNonneg_mono fun b hb => (h b hb).ge)
private theorem finsetSupNonneg_pow_le {α : Type} (S : Finset α) (g : α → ℝ) (hg : ∀ b ∈ S, 0 ≤ g b)
    {ε : ℝ} (hε : 0 < ε) (q r : ℕ) :
    finsetSupNonneg S g ^ q ≤ ε ^ q + (ε ^ r)⁻¹ * ∑ b ∈ S, g b ^ (q + r) := by
  have hs : 0 ≤ (ε ^ r)⁻¹ := by positivity
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have h0 : finsetSupNonneg (∅ : Finset α) g = 0 := by simp [finsetSupNonneg]
    rw [h0, Finset.sum_empty, mul_zero, add_zero]
    exact pow_le_pow_left₀ le_rfl hε.le q
  · obtain ⟨b₀, hb₀, hmax⟩ := S.exists_max_image g hne
    have h1 : finsetSupNonneg S g ≤ g b₀ := finsetSupNonneg_le (hg b₀ hb₀) hmax
    have h2 := pow_le_pow_left₀ (finsetSupNonneg_nonneg S g) h1 q
    have h3 := pow_le_add_inv_mul_pow q r (hg b₀ hb₀) hε
    have h4 : g b₀ ^ (q + r) ≤ ∑ b ∈ S, g b ^ (q + r) :=
      Finset.single_le_sum (f := fun b => g b ^ (q + r)) (fun b hb => pow_nonneg (hg b hb) _) hb₀
    have h5 := mul_le_mul_of_nonneg_left h4 hs
    linarith
section Mean
variable {ι : Type} [Fintype ι]
private theorem ballDensity_nonneg (ρ : ℝ) (p : ℝ → ℝ) (Ψ : ColdStepAtMirrorFrames.BondField ι → ℝ)
    (η : ColdStepAtMirrorFrames.BondField ι) :
    0 ≤ ColdStepAtMirrorFrames.ballDensity (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ η := by apply _root_.YangMills.Construction.ConvexMeasures.LocalCovariance.ballDensity_nonneg <;> assumption
private theorem ballDensity_eq_zero_of_not_mem {ρ : ℝ} {p : ℝ → ℝ}
    {Ψ : ColdStepAtMirrorFrames.BondField ι → ℝ} {η : ColdStepAtMirrorFrames.BondField ι}
    (h : ¬ ∀ b, ‖η b‖ < ρ) : ColdStepAtMirrorFrames.ballDensity (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ η = 0 := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.ballDensity_eq_zero_of_not_mem <;> assumption
private theorem ballExpectation_le_of_le_sum {ρ : ℝ} {p : ℝ → ℝ} {Ψ H : ColdStepAtMirrorFrames.BondField ι → ℝ}
    {J : Type} (S : Finset J) (g : J → ColdStepAtMirrorFrames.BondField ι → ℝ) {A c G : ℝ} (hA : 0 ≤ A)
    (hg : ∀ j ∈ S, Continuous (g j))
    (hgb : ∀ j ∈ S, ∀ η : ColdStepAtMirrorFrames.BondField ι, (∀ b, ‖η b‖ < ρ) → |g j η| ≤ G)
    (hH0 : ∀ η, 0 ≤ H η)
    (hH : ∀ η : ColdStepAtMirrorFrames.BondField ι, (∀ b, ‖η b‖ < ρ) → H η ≤ A + c * ∑ j ∈ S, g j η) :
    ColdStepAtMirrorFrames.ballExpectation (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ H ≤
      A + c * ∑ j ∈ S, ColdStepAtMirrorFrames.ballExpectation (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ (g j) := by
  set D := ColdStepAtMirrorFrames.ballDensity (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ with hD
  have hD0 : ∀ η, 0 ≤ D η := ballDensity_nonneg ρ p Ψ
  have hZ : 0 ≤ ∫ η, D η := integral_nonneg hD0
  rcases hZ.eq_or_lt with hZ0 | hZpos
  · simp only [ColdStepAtMirrorFrames.ballExpectation, ← hD, ← hZ0, div_zero, Finset.sum_const_zero,
      mul_zero, add_zero]
    exact hA
  have hDi : Integrable D := by
    by_contra h
    rw [integral_undef h] at hZpos
    exact lt_irrefl _ hZpos
  have hgi : ∀ j ∈ S, Integrable (fun η => g j η * D η) := fun j hj => by
    refine Integrable.mono' (hDi.const_mul G) ((hg j hj).aestronglyMeasurable.mul hDi.1)
      (ae_of_all _ fun η => ?_)
    by_cases hη : ∀ b, ‖η b‖ < ρ
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hD0 η)]
      exact mul_le_mul_of_nonneg_right (hgb j hj η hη) (hD0 η)
    · have : D η = 0 := ballDensity_eq_zero_of_not_mem hη
      simp [this]
  have hsum : Integrable (fun η => ∑ j ∈ S, g j η * D η) := integrable_finsetSum _ hgi
  have hint : Integrable (fun η => A * D η + c * ∑ j ∈ S, g j η * D η) :=
    (hDi.const_mul A).add (hsum.const_mul c)
  have key : ∫ η, H η * D η ≤ ∫ η, (A * D η + c * ∑ j ∈ S, g j η * D η) := by
    refine integral_mono_of_nonneg (ae_of_all _ fun η => mul_nonneg (hH0 η) (hD0 η)) hint
      (ae_of_all _ fun η => ?_)
    by_cases hη : ∀ b, ‖η b‖ < ρ
    · have h1 := mul_le_mul_of_nonneg_right (hH η hη) (hD0 η)
      have e : (A + c * ∑ j ∈ S, g j η) * D η = A * D η + c * ∑ j ∈ S, g j η * D η := by
        rw [add_mul, mul_assoc, Finset.sum_mul]
      simpa only [e] using h1
    · have : D η = 0 := ballDensity_eq_zero_of_not_mem hη
      simp [this]
  have ev : ∫ η, (A * D η + c * ∑ j ∈ S, g j η * D η) =
      A * (∫ η, D η) + c * ∑ j ∈ S, ∫ η, g j η * D η := by
    rw [integral_add (hDi.const_mul A) (hsum.const_mul c), integral_const_mul, integral_const_mul,
      integral_finsetSum _ hgi]
  unfold ColdStepAtMirrorFrames.ballExpectation
  rw [← hD, div_le_iff₀ hZpos, add_mul, mul_assoc, Finset.sum_mul]
  have e2 : ∀ j ∈ S, (∫ η, g j η * D η) / (∫ η, D η) * (∫ η, D η) = ∫ η, g j η * D η := fun j _ =>
    div_mul_cancel₀ _ hZpos.ne'
  rw [Finset.sum_congr rfl e2, ← ev]
  exact key
end Mean
section Capped
private def tripleNorm {α : Type} (v : α × Fin 3 → ℝ) (b : α) : ℝ :=
  Real.sqrt (v (b, 0) ^ 2 + v (b, 1) ^ 2 + v (b, 2) ^ 2)
private theorem tripleNorm_imaginaryComponentsOn {n : ℕ} (Z : Finset (TorusFields.TorusBond n))
    (e : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) (b : ↥Z) :
    tripleNorm (imaginaryComponentsOn Z e) b = ‖(e b.1 : ℍ[ℝ])‖ := by
  have hre : ((e b.1 : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]).re = 0 := (e b.1).2
  have h1 := Quaternion.normSq_eq_norm_mul_self ((e b.1 : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])
  rw [Quaternion.normSq_def', hre] at h1
  unfold tripleNorm imaginaryComponentsOn BlockAverages.imaginaryComponent
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [show ((e b.1 : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]).imI ^ 2 +
      ((e b.1 : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]).imJ ^ 2 +
      ((e b.1 : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]).imK ^ 2 =
    ‖((e b.1 : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ *
      ‖((e b.1 : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ by linarith [h1]]
  exact Real.sqrt_mul_self (norm_nonneg _)
open Classical in
private def truncatedNormAt {n : ℕ} (Z : Finset (TorusFields.TorusBond n)) (ρ : ℝ) (v : ↥Z × Fin 3 → ℝ)
    (b : TorusFields.TorusBond n) : ℝ :=
  if h : b ∈ Z then min ρ (tripleNorm v ⟨b, h⟩) else 0
private def truncatedSupPow {n : ℕ} (Z : Finset (TorusFields.TorusBond n)) (ρ : ℝ) (q : ℕ)
    (v : ↥Z × Fin 3 → ℝ) : ℝ :=
  finsetSupNonneg Z (truncatedNormAt Z ρ v) ^ q
private theorem measurable_finsetSupNonneg {α X : Type} [MeasurableSpace X] (S : Finset α) (f : α → X → ℝ)
    (hf : ∀ b ∈ S, Measurable (f b)) : Measurable fun v => finsetSupNonneg S (fun b => f b v) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa [finsetSupNonneg] using measurable_const
  | insert a s ha ih =>
    have e : (fun v => finsetSupNonneg (insert a s) (fun b => f b v)) =
        fun v => max (f a v) (finsetSupNonneg s (fun b => f b v)) := by
      funext v
      simp [finsetSupNonneg, Finset.fold_insert ha]
    rw [e]
    exact (hf a (Finset.mem_insert_self a s)).max (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))
private theorem truncatedSupPow_measurable {n : ℕ} (Z : Finset (TorusFields.TorusBond n)) (ρ : ℝ) (q : ℕ) :
    Measurable (truncatedSupPow Z ρ q) := by
  classical
  unfold truncatedSupPow
  refine (measurable_finsetSupNonneg Z (fun b v => truncatedNormAt Z ρ v b) fun b _ => ?_).pow_const q
  unfold truncatedNormAt
  by_cases h : b ∈ Z
  · simp only [h, dite_true]
    refine measurable_const.min (Real.continuous_sqrt.measurable.comp ?_)
    fun_prop
  · simp only [h, dite_false]
    exact measurable_const
private theorem abs_truncatedSupPow_le {n : ℕ} (Z : Finset (TorusFields.TorusBond n)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (q : ℕ) (v : ↥Z × Fin 3 → ℝ) : |truncatedSupPow Z ρ q v| ≤ ρ ^ q := by
  unfold truncatedSupPow
  have h0 := finsetSupNonneg_nonneg Z (truncatedNormAt Z ρ v)
  rw [abs_of_nonneg (pow_nonneg h0 _)]
  refine pow_le_pow_left₀ h0 (finsetSupNonneg_le hρ fun b hb => ?_) q
  unfold truncatedNormAt
  rw [dif_pos hb]
  exact min_le_left _ _
private theorem truncatedNormAt_imaginaryComponentsOn {n : ℕ} (Z : Finset (TorusFields.TorusBond n)) (ρ : ℝ)
    (e : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) {b : TorusFields.TorusBond n}
    (hb : b ∈ Z) : truncatedNormAt Z ρ (imaginaryComponentsOn Z e) b = min ρ ‖(e b : ℍ[ℝ])‖ := by
  unfold truncatedNormAt
  rw [dif_pos hb, tripleNorm_imaginaryComponentsOn]
private theorem truncatedSupPow_eq_of_lt {n : ℕ} (Z : Finset (TorusFields.TorusBond n)) (ρ : ℝ) (q : ℕ)
    (e : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) (h : ∀ b ∈ Z, ‖(e b : ℍ[ℝ])‖ < ρ) :
    truncatedSupPow Z ρ q (imaginaryComponentsOn Z e) = finsetSupNonneg Z (fun b => ‖(e b : ℍ[ℝ])‖) ^ q := by
  unfold truncatedSupPow
  rw [finsetSupNonneg_congr (g := fun b => ‖(e b : ℍ[ℝ])‖) fun b hb => ?_]
  rw [truncatedNormAt_imaginaryComponentsOn Z ρ e hb, min_eq_right (h b hb).le]
private theorem truncatedSupPow_le {n : ℕ} (Z : Finset (TorusFields.TorusBond n)) {ρ : ℝ} (hρ : 0 ≤ ρ) (q : ℕ)
    (e : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) :
    truncatedSupPow Z ρ q (imaginaryComponentsOn Z e) ≤ finsetSupNonneg Z (fun b => ‖(e b : ℍ[ℝ])‖) ^ q := by
  unfold truncatedSupPow
  refine pow_le_pow_left₀ (finsetSupNonneg_nonneg _ _) (finsetSupNonneg_mono fun b hb => ?_) q
  rw [truncatedNormAt_imaginaryComponentsOn Z ρ e hb]
  exact min_le_right _ _
end Capped
section Mirror
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) :
    ‖((ColdStepAtMirrorFrames.toImaginary v : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ = ‖v‖ := by apply _root_.YangMills.Construction.BlockTrees.norm_toImaginary <;> assumption
private theorem reflectedStepMean_truncatedSupPow_le (R : StepSettings.StepSetup) (m : ℕ) {n : ℕ} [NeZero n]
    (o : TorusFields.TorusSite n) (V : TorusFields.TorusField n)
    (Z : Finset (TorusFields.TorusBond (n * R.params.side))) (hρ : 0 < R.ballRadius) (q r Q : ℕ)
    (hqr : q + r = 2 * Q) (hQ : 1 ≤ Q) {ε Cm : ℝ} (hε : 0 < ε) (hCm : 0 ≤ Cm)
    (hmom : ∀ b : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells
        (reflectedTorusFrame R.params.side R.depth m n))),
      ColdStepAtMirrorFrames.ballExpectation (ColdStepAtMirrorFrames.cutoffFactor R.ballRadius R.barrierFn)
        (ColdStepAtMirrorFrames.stepExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach
          (ColdStepAtMirrorFrames.localFamilyOfDensity R.density) 1
          (reflectedTopField R.params.side R.depth m o V)) (fun η => ‖η b‖ ^ (2 * Q)) ≤ Cm) :
    reflectedStepMean R m o V (fun η => truncatedSupPow Z R.ballRadius q
        (imaginaryComponentsOn Z (reflectedCoordinateAt R.params.side R.depth m o η))) ≤
      ε ^ q + (ε ^ r)⁻¹ * ((Z.card : ℝ) * Cm) := by
  classical
  set Fm := reflectedTorusFrame R.params.side R.depth m n with hFm
  set Ψ := ColdStepAtMirrorFrames.stepExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach
    (ColdStepAtMirrorFrames.localFamilyOfDensity R.density) 1
    (reflectedTopField R.params.side R.depth m o V) with hΨ
  let g : TorusFields.TorusBond (n * R.params.side) →
      ColdStepAtMirrorFrames.BondField ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells Fm)) → ℝ :=
    fun b η => ‖(reflectedCoordinateAt R.params.side R.depth m o η b : ℍ[ℝ])‖ ^ (2 * Q)
  have hcase : ∀ b : TorusFields.TorusBond (n * R.params.side),
      (∃ b' : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells Fm)),
        g b = fun η => ‖η b'‖ ^ (2 * Q)) ∨ g b = fun _ => 0 := by
    intro b
    by_cases hb : reflectedBondPosition R.params.side R.depth m o b ∈
        BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells Fm)
    · refine Or.inl ⟨⟨_, hb⟩, ?_⟩
      funext η
      simp only [g, reflectedCoordinateAt, ColdStepAtMirrorFrames.stepCoordinates]
      rw [dif_pos hb]
      exact congrArg (· ^ (2 * Q))
        (norm_toImaginary (η ⟨reflectedBondPosition R.params.side R.depth m o b, hb⟩))
    · refine Or.inr ?_
      funext η
      simp only [g, reflectedCoordinateAt, ColdStepAtMirrorFrames.stepCoordinates]
      rw [dif_neg hb]
      have hq : 2 * Q ≠ 0 := by omega
      simp [hq]
  have hcont : ∀ b ∈ Z, Continuous (g b) := fun b _ => by
    rcases hcase b with ⟨b', h⟩ | h
    · rw [h]
      exact ((continuous_apply b').norm).pow _
    · rw [h]
      exact continuous_const
  have hbd : ∀ b ∈ Z, ∀ η : ColdStepAtMirrorFrames.BondField
      ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells Fm)), (∀ b', ‖η b'‖ < R.ballRadius) →
      |g b η| ≤ R.ballRadius ^ (2 * Q) := fun b _ η hη => by
    rcases hcase b with ⟨b', h⟩ | h
    · rw [h]
      simp only
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hη b').le _
    · rw [h]
      simp only [abs_zero]
      positivity
  have hH0 : ∀ η : ColdStepAtMirrorFrames.BondField
      ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells Fm)),
      0 ≤ truncatedSupPow Z R.ballRadius q
        (imaginaryComponentsOn Z (reflectedCoordinateAt R.params.side R.depth m o η)) := fun η =>
    pow_nonneg (finsetSupNonneg_nonneg _ _) _
  have hH : ∀ η : ColdStepAtMirrorFrames.BondField
      ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells Fm)), (∀ b', ‖η b'‖ < R.ballRadius) →
      truncatedSupPow Z R.ballRadius q
        (imaginaryComponentsOn Z (reflectedCoordinateAt R.params.side R.depth m o η)) ≤
        ε ^ q + (ε ^ r)⁻¹ * ∑ b ∈ Z, g b η := fun η _ => by
    refine (truncatedSupPow_le Z hρ.le q _).trans ?_
    have := finsetSupNonneg_pow_le Z
      (fun b => ‖(reflectedCoordinateAt R.params.side R.depth m o η b : ℍ[ℝ])‖)
      (fun _ _ => norm_nonneg _) hε q r
    simpa only [g, hqr] using this
  have hmain := ballExpectation_le_of_le_sum (p := R.barrierFn) (Ψ := Ψ) Z g (pow_nonneg hε.le q)
    hcont hbd hH0 hH
  have hsum : ∑ b ∈ Z, ColdStepAtMirrorFrames.ballExpectation
      (ColdStepAtMirrorFrames.cutoffFactor R.ballRadius R.barrierFn) Ψ (g b) ≤ (Z.card : ℝ) * Cm := by
    have : ∀ b ∈ Z, ColdStepAtMirrorFrames.ballExpectation
        (ColdStepAtMirrorFrames.cutoffFactor R.ballRadius R.barrierFn) Ψ (g b) ≤ Cm := fun b _ => by
      rcases hcase b with ⟨b', h⟩ | h
      · rw [h]
        exact hmom b'
      · rw [h]
        simpa [ColdStepAtMirrorFrames.ballExpectation] using hCm
    simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul Z _ Cm this
  have hinv : 0 ≤ (ε ^ r)⁻¹ := by positivity
  have h2 := mul_le_mul_of_nonneg_left hsum hinv
  exact hmain.trans (by linarith)
private theorem isSmallCurvature_reflectedTopField {L t m n : ℕ} [NeZero n] (hm : 0 < m) {s : ℝ} (hs : 0 < s)
    (o : TorusFields.TorusSite n) (V : TorusFields.TorusField n) (hc : IsColdOnBall s V o m) :
    ColdStepAtMirrorFrames.IsSmallCurvature s (reflectedTopField L t m o V) := by
  have h0 : TorusFields.IsCold s (TorusMirror.mirrorField m o V) :=
    TorusMirror.isCold_mirrorField hm o V hs fun a μ ν hlt hd => by
    refine hc (o + TorusFields.siteOfInt a, μ, ν) ?_
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt, fun z hz => ?_⟩
    obtain ⟨d, hd', rfl⟩ := (TorusLumps.mem_plaquetteVertices_iff_offset _ _ _ _).1 hz
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have h1 := hd d hd'
    have e : o + TorusFields.siteOfInt a + TorusFields.siteOfInt d - o = TorusFields.siteOfInt (a + d) := by
      rw [TorusFields.siteOfInt_add]
      abel
    have h2 : TorusFields.supDist (o + TorusFields.siteOfInt a + TorusFields.siteOfInt d) o ≤ m := by
      rw [TorusFields.supDist_le_iff]
      intro i
      have hi : (o + TorusFields.siteOfInt a + TorusFields.siteOfInt d : TorusFields.TorusSite n) i - o i =
          (((a + d) i : ℤ) : ZMod n) := congrFun e i
      rw [hi]
      refine (TorusFields.natAbs_valMinAbs_intCast_le _).trans ?_
      have := h1 i
      rw [Int.abs_eq_natAbs] at this
      exact_mod_cast this
    exact_mod_cast h2
  haveI : NeZero (4 * m) := ⟨by omega⟩
  intro p hp
  obtain ⟨z, μ, ν⟩ := p
  show BlockAverages.plaquetteDefect (ColdStepAtMirrorFrames.reflectedField m
    (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top o)
    (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V)) (z, μ, ν) < s
  rw [TopLevelSites.reflectedField_readAtLevel (F := TorusFields.torusFrame L t n) (fun _ => rfl) hm o V,
    TopLevelSites.plaquetteDefect_readAtLevel_eq (N := 4 * m) (fun i => by rw [TopLevelSites.period_top]; rfl)]
  exact h0 _ _ _ hp
end Mirror
section Numbers
private theorem exp_neg_floor_rpow_le_inv_pow {c : ℝ} (hc : 0 < c) (q : ℕ) : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    Real.exp (-(c * (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ))) ≤ (x ^ q)⁻¹ := by
  have hN := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (20 * q)
  have hδ : 0 < c ^ (20 * q) * Real.exp (-c) := by positivity
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.1 (hN.eventually (gt_mem_nhds hδ))
  set U' := max U 1 with hU'
  have hU1 : 0 < U' / c := div_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) hc
  refine ⟨max 1 ((U' / c) ^ (20 : ℝ)), fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  set w := x ^ ((1 : ℝ) / 20) with hw
  have hwU : U' / c ≤ w := by
    have h1 : (U' / c) ^ (20 : ℝ) ≤ x := (le_max_right _ _).trans hx
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hU1.le _) h1 (by norm_num : (0 : ℝ) ≤ 1 / 20)
    rwa [← Real.rpow_mul hU1.le, show (20 : ℝ) * (1 / 20) = 1 by norm_num, Real.rpow_one] at h2
  have hcw : U ≤ c * w := by
    have h1 : U' ≤ c * w := by
      have := (div_le_iff₀ hc).1 hwU
      linarith
    exact (le_max_left _ _).trans h1
  have h3 := hU (c * w) hcw
  have hxq : w ^ (20 * q) = x ^ q := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  rw [mul_pow, hxq] at h3
  have hfl : w - 1 ≤ (⌊w⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one w
    linarith
  have h4 : Real.exp (-(c * (⌊w⌋₊ : ℝ))) ≤ Real.exp c * Real.exp (-(c * w)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hxq0 : 0 < x ^ q := by positivity
  have hcp : 0 < c ^ (20 * q) := by positivity
  have h5 : x ^ q * Real.exp (-(c * w)) ≤ Real.exp (-c) := by
    have h6 : c ^ (20 * q) * (x ^ q * Real.exp (-(c * w))) ≤ c ^ (20 * q) * Real.exp (-c) := by
      have : c ^ (20 * q) * x ^ q * Real.exp (-(c * w)) < c ^ (20 * q) * Real.exp (-c) := h3
      rw [← mul_assoc]
      exact this.le
    exact le_of_mul_le_mul_left h6 hcp
  have h7 : Real.exp c * Real.exp (-(c * w)) ≤ (x ^ q)⁻¹ := by
    rw [← one_div, le_div_iff₀ hxq0]
    calc Real.exp c * Real.exp (-(c * w)) * x ^ q = Real.exp c * (x ^ q * Real.exp (-(c * w))) := by ring
      _ ≤ Real.exp c * Real.exp (-c) := mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  exact h4.trans h7
private theorem three_terms_le {x xt e a Cm K w C Nc : ℝ} {q r Q : ℕ} (hx : 1 ≤ x) (hxt : x / 2 ≤ xt)
    (he1 : -1 ≤ e) (he0 : e ≤ 0) (hN0 : 0 ≤ Nc) (hN : Nc ≤ x ^ a) (hCm : 0 ≤ Cm) (hK : 0 ≤ K)
    (hw : w ≤ (x ^ q)⁻¹) (hqr : q + r = 2 * Q) (hq : 1 ≤ q) (hexp : a - 2 * e * Q - Q ≤ 0)
    (hC : 1 + 2 ^ Q * Cm + K ≤ C) :
    (x ^ e) ^ q + ((x ^ e) ^ r)⁻¹ * (Nc * (Cm * (xt ^ Q)⁻¹)) + K * w ≤ (C * x ^ e) ^ q := by
  have hx0 : 0 < x := by linarith
  set ε := x ^ e with hε
  have hxt0 : 0 < xt := by linarith
  have pw : ∀ (s : ℝ) (i : ℕ), (x ^ s) ^ i = x ^ (s * i) := fun s i => by
    rw [Real.rpow_mul hx0.le, Real.rpow_natCast]
  have hinv : (xt ^ Q)⁻¹ ≤ 2 ^ Q * (x ^ Q)⁻¹ := by
    have h1 : (x / 2) ^ Q ≤ xt ^ Q := pow_le_pow_left₀ (by linarith) hxt Q
    have h2 : (xt ^ Q)⁻¹ ≤ ((x / 2) ^ Q)⁻¹ := inv_anti₀ (by positivity) h1
    refine h2.trans (le_of_eq ?_)
    rw [div_pow, inv_div, div_eq_mul_inv]
  have hmid : (ε ^ r)⁻¹ * (Nc * (Cm * (xt ^ Q)⁻¹)) ≤ 2 ^ Q * Cm * ε ^ q := by
    have h1 : Nc * (Cm * (xt ^ Q)⁻¹) ≤ x ^ a * (Cm * (2 ^ Q * (x ^ Q)⁻¹)) :=
      mul_le_mul hN (mul_le_mul_of_nonneg_left hinv hCm) (by positivity) (by positivity)
    have h2 : (ε ^ r)⁻¹ * (Nc * (Cm * (xt ^ Q)⁻¹)) ≤ (ε ^ r)⁻¹ * (x ^ a * (Cm * (2 ^ Q * (x ^ Q)⁻¹))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    refine h2.trans ?_
    have h3 : (ε ^ r)⁻¹ * x ^ a * (x ^ Q)⁻¹ ≤ ε ^ q := by
      rw [hε, pw, pw, ← Real.rpow_neg hx0.le, ← Real.rpow_natCast x Q, ← Real.rpow_neg hx0.le,
        ← Real.rpow_add hx0, ← Real.rpow_add hx0]
      refine Real.rpow_le_rpow_of_exponent_le hx ?_
      have hr : (r : ℝ) = 2 * Q - q := by
        have : ((q + r : ℕ) : ℝ) = ((2 * Q : ℕ) : ℝ) := by rw [hqr]
        push_cast at this
        linarith
      rw [hr]
      nlinarith
    have h4 : 0 ≤ 2 ^ Q * Cm := by positivity
    calc (ε ^ r)⁻¹ * (x ^ a * (Cm * (2 ^ Q * (x ^ Q)⁻¹)))
        = 2 ^ Q * Cm * ((ε ^ r)⁻¹ * x ^ a * (x ^ Q)⁻¹) := by ring
      _ ≤ 2 ^ Q * Cm * ε ^ q := mul_le_mul_of_nonneg_left h3 h4
  have hlast : K * w ≤ K * ε ^ q := by
    refine mul_le_mul_of_nonneg_left (hw.trans ?_) hK
    rw [hε, pw, ← Real.rpow_natCast x q, ← Real.rpow_neg hx0.le]
    refine Real.rpow_le_rpow_of_exponent_le hx ?_
    nlinarith
  have hC1 : 1 ≤ C := by
    have : 0 ≤ 2 ^ Q * Cm := by positivity
    linarith
  have hCq : C ≤ C ^ q := by
    calc C = C ^ 1 := (pow_one C).symm
      _ ≤ C ^ q := pow_le_pow_right₀ hC1 hq
  rw [mul_pow]
  have hεq : 0 < ε ^ q := by positivity
  have : (1 + 2 ^ Q * Cm + K) * ε ^ q ≤ C ^ q * ε ^ q :=
    mul_le_mul_of_nonneg_right (hC.trans hCq) hεq.le
  nlinarith
end Numbers
section Step
variable {ℓ : TorusLumps.StepParameters}
private abbrev clearEvent (T : WeightedResponses.StageTower ℓ) (k j m : ℕ) {n : ℕ} [NeZero n]
    (o : TorusFields.TorusSite n) : Set (WeightedResponses.MarkedSample ℓ (k + j + 1) n) :=
  {u' | Disjoint (WeightedResponses.stageState T (k + j + 1) n u').2.1 (supBall o m) ∧ StepAvoids T (k + j) m o u'}
private abbrev stepDeviationOf (T : WeightedResponses.StageTower ℓ) (k j : ℕ) {n : ℕ}
    (u' : WeightedResponses.MarkedSample ℓ (k + j + 1) n) :
    TorusFields.TorusBond (n * ℓ.side) → BlockAverages.imaginaryQuaternions :=
  stepDeviation T (k + j) u'.2.2.1 (WeightedResponses.topField ℓ (k + j) (n * ℓ.side) u'.1)
private theorem indicator_pow_ae_eq_truncated (T : WeightedResponses.StageTower ℓ) (β : ℝ) (k j n : ℕ) [NeZero n]
    (m : ℕ) (o : TorusFields.TorusSite n) (Z : Finset (TorusFields.TorusBond (n * ℓ.side))) (q : ℕ)
    (hZ : Z ⊆ MarkedIntegrals.chartBondsInBlocks ℓ.side (supBall o m))
    (hclear : ∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β (k + j + 1) n),
      Disjoint (WeightedResponses.stageState T (k + j + 1) n u).2.1 (supBall o m) →
      StepAvoids T (k + j) m o u → ∀ b ∈ MarkedIntegrals.chartBondsInBlocks ℓ.side (supBall o m),
        ‖(stepDeviationOf T k j u b : ℍ[ℝ])‖ < ℓ.threshold / 64) :
    Set.indicator (clearEvent T k j m o)
        (fun u' => finsetSupNonneg Z (fun b => ‖(stepDeviationOf T k j u' b : ℍ[ℝ])‖) ^ q)
      =ᵐ[WeightedResponses.markedSampleLaw T β (k + j + 1) n]
    Set.indicator (clearEvent T k j m o)
        (fun u' => truncatedSupPow Z (ℓ.threshold / 64) q (imaginaryComponentsOn Z (stepDeviationOf T k j u'))) := by
  filter_upwards [hclear] with u' hu'
  by_cases hE : u' ∈ clearEvent T k j m o
  · rw [Set.indicator_of_mem hE, Set.indicator_of_mem hE,
      truncatedSupPow_eq_of_lt Z _ q _ fun b hb => hu' hE.1 hE.2 b (hZ hb)]
  · rw [Set.indicator_of_notMem hE, Set.indicator_of_notMem hE]
private theorem condExp_indicator_le (T : WeightedResponses.StageTower ℓ) (β : ℝ) (k j n : ℕ) [NeZero n]
    (m : ℕ) (o : TorusFields.TorusSite n) (Z : Finset (TorusFields.TorusBond (n * ℓ.side)))
    (hσ : 0 < ℓ.threshold) (hm : 0 < m) (q r Q : ℕ) (hqr : q + r = 2 * Q) (hQ : 1 ≤ Q)
    {ε Cm K : ℝ} (hε : 0 < ε) (hCm : 0 ≤ Cm)
    (hZ : Z ⊆ MarkedIntegrals.chartBondsInBlocks ℓ.side (supBall o m))
    (hone : ∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β (k + j + 1) n),
      Disjoint (WeightedResponses.stageState T (k + j + 1) n u).2.1 (supBall o m) →
      |((WeightedResponses.markedSampleLaw T β (k + j + 1) n)[Set.indicator (clearEvent T k j m o)
            (fun u' => truncatedSupPow Z (ℓ.threshold / 64) q (imaginaryComponentsOn Z (stepDeviationOf T k j u')))
            | WeightedResponses.stageSigma T (k + j + 1) n]) u -
        reflectedStepMean (T.stage (k + j)).toStepSetup m o u.2.2.1
          (fun η => truncatedSupPow Z (ℓ.threshold / 64) q
            (imaginaryComponentsOn Z (reflectedCoordinateAt ℓ.side (T.stage (k + j)).depth m o η)))| ≤ K)
    (hcold : ∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β (k + j + 1) n),
      Disjoint (WeightedResponses.stageState T (k + j + 1) n u).2.1 (supBall o m) →
      IsColdOnBall ℓ.threshold u.2.2.1 o m)
    (hae : Set.indicator (clearEvent T k j m o)
        (fun u' => finsetSupNonneg Z (fun b => ‖(stepDeviationOf T k j u' b : ℍ[ℝ])‖) ^ q)
      =ᵐ[WeightedResponses.markedSampleLaw T β (k + j + 1) n]
      Set.indicator (clearEvent T k j m o)
        (fun u' => truncatedSupPow Z (ℓ.threshold / 64) q (imaginaryComponentsOn Z (stepDeviationOf T k j u'))))
    (hmom : ∀ V : TorusFields.TorusField n,
      ColdStepAtMirrorFrames.IsSmallCurvature ℓ.threshold (reflectedTopField ℓ.side (T.stage (k + j)).depth m o V) →
      ∀ b : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells
        (reflectedTorusFrame ℓ.side (T.stage (k + j)).depth m n))),
      ColdStepAtMirrorFrames.ballExpectation
        (ColdStepAtMirrorFrames.cutoffFactor (ℓ.threshold / 64) (T.stage (k + j)).barrierFn)
        (ColdStepAtMirrorFrames.stepExponent false ℓ.coupling (T.stage (k + j)).anchorRadius
          (T.stage (k + j)).coupling (T.stage (k + j)).toStepSetup.frameReach
          (ColdStepAtMirrorFrames.localFamilyOfDensity (T.stage (k + j)).density) 1
          (reflectedTopField ℓ.side (T.stage (k + j)).depth m o V)) (fun η => ‖η b‖ ^ (2 * Q)) ≤ Cm) :
    ∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β (k + j + 1) n),
      Disjoint (WeightedResponses.stageState T (k + j + 1) n u).2.1 (supBall o m) →
      ((WeightedResponses.markedSampleLaw T β (k + j + 1) n)[Set.indicator (clearEvent T k j m o)
            (fun u' => finsetSupNonneg Z (fun b => ‖(stepDeviationOf T k j u' b : ℍ[ℝ])‖) ^ q)
            | WeightedResponses.stageSigma T (k + j + 1) n]) u ≤
        ε ^ q + (ε ^ r)⁻¹ * ((Z.card : ℝ) * Cm) + K := by
  have hce := condExp_congr_ae (m := WeightedResponses.stageSigma T (k + j + 1) n) hae
  filter_upwards [hone, hcold, hce] with u h1 h2 h3 hd
  rw [h3]
  have h4 := (abs_le.1 (h1 hd)).2
  have hρ : 0 < (T.stage (k + j)).toStepSetup.ballRadius := by
    show 0 < ℓ.threshold / 64
    positivity
  have hM := reflectedStepMean_truncatedSupPow_le (T.stage (k + j)).toStepSetup m o u.2.2.1 Z hρ q r Q hqr hQ
    hε hCm (hmom _ (isSmallCurvature_reflectedTopField hm hσ o _ (h2 hd)))
  have hM' : reflectedStepMean (T.stage (k + j)).toStepSetup m o u.2.2.1
      (fun η => truncatedSupPow Z (ℓ.threshold / 64) q
        (imaginaryComponentsOn Z (reflectedCoordinateAt ℓ.side (T.stage (k + j)).depth m o η))) ≤
      ε ^ q + (ε ^ r)⁻¹ * ((Z.card : ℝ) * Cm) := hM
  linarith
end Step
private theorem finsetSupNonneg_singleton {α : Type} (b : α) (g : α → ℝ) (h : 0 ≤ g b) :
    finsetSupNonneg {b} g = g b := by
  simp [finsetSupNonneg, max_eq_left h]
private theorem eventually_large_coupling {B : ℝ} (hB : 0 < B) (N : ℝ) : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    1 ≤ x ∧ 8 * B * Real.log x ^ 2 ≤ x ∧ N ≤ x ^ ((1 : ℝ) / 20) := by
  have h1 := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (show 0 < 1 / (8 * B) by positivity)
  have h2 := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 20 by norm_num)).eventually_ge_atTop N
  obtain ⟨x₀, h⟩ := Filter.eventually_atTop.1 (h1.and (h2.and (Filter.eventually_ge_atTop 1)))
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨a, b, c⟩ := h x hx
  refine ⟨c, ?_, b⟩
  have hx0 : 0 ≤ x := by linarith
  simp only [id, Real.norm_eq_abs, abs_of_nonneg hx0, abs_of_nonneg (sq_nonneg (Real.log x))] at a
  have : 8 * B * (Real.log x ^ 2) ≤ 8 * B * (1 / (8 * B) * x) := mul_le_mul_of_nonneg_left a (by positivity)
  have e : 8 * B * (1 / (8 * B) * x) = x := by field_simp
  linarith
section Table
variable (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ)
private theorem stepDeviationMomentsAt_of (hD : Tb.Admissible) (hy : Tb.floorMin ≤ y)
    (hOne : oneStepReflectedLawAt Tb y) (hClear : descentKeepsBallClearAt Tb y)
    (hMom : coldHalfLawMomentsAt Tb y)
    (hScaleFlow : ∀ β : ℝ, y ≤ β → ClusterExpansionOfAStep.FlowHasExpansionAt (Tb.stepParameters y) β)
    (hTP : TwoPointByTotalCovarianceStatement) (hRow : ColdStepAtMirrorFrames.ColdExpansionRegular)
    (hEnds : Interpolation.interpolationAtEndpoints) : stepDeviationMomentsAt Tb y := by
  classical
  have hfits : (Tb.stepParameters y).Admissible := hD.fits y hy
  have hσ : 0 < (Tb.stepParameters y).threshold := hD.σ_pos
  have hB : 1 ≤ (Tb.stepParameters y).B := hD.B_ge
  obtain ⟨C₁, c, x₁, hc, hOne⟩ := hOne
  obtain ⟨x₂, hClear⟩ := hClear
  obtain ⟨cn, nss, hties, hMA⟩ := hMom
  intro q
  obtain ⟨Ca, hCa⟩ := hMA q
  obtain ⟨Cb, hCb⟩ := hMA (q + 500)
  obtain ⟨x₃, hx₃⟩ := exp_neg_floor_rpow_le_inv_pow hc q
  obtain ⟨x₄, hx₄⟩ := eventually_large_coupling (B := (Tb.stepParameters y).B) (by linarith) ((Tb.n₀ : ℝ) + 1)
  set ρ : ℝ := (Tb.stepParameters y).threshold / 64 with hρdef
  have hρ : 0 < ρ := by positivity
  set K0 : ℝ := |C₁| * ρ ^ q with hK0
  have hK00 : 0 ≤ K0 := by positivity
  refine ⟨1 + 2 ^ q * |Ca| + 2 ^ (q + 500) * |Cb| + K0, max (max x₁ x₂) (max x₃ x₄),
    fun T β k n _ nn j o Z hloc hLn hj hZ hcard => ?_⟩
  have hfl := hloc.floor_le
  have hfl' : max (max x₁ x₂) (max x₃ x₄) ≤ flowCouplings (Tb.stepParameters y) β k := hfl
  have hxx₁ : x₁ ≤ flowCouplings (Tb.stepParameters y) β k :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hfl'
  have hxx₂ : x₂ ≤ flowCouplings (Tb.stepParameters y) β k :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hfl'
  have hxx₃ : x₃ ≤ flowCouplings (Tb.stepParameters y) β k :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hfl'
  have hxx₄ : x₄ ≤ flowCouplings (Tb.stepParameters y) β k :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hfl'
  have hloc₁ : IsLocalChainAbove Tb y T β k n nn x₁ := { hloc with floor_le := hxx₁ }
  have hloc₂ : IsLocalChainAbove Tb y T β k n nn x₂ := { hloc with floor_le := hxx₂ }
  have hO := fun (Z' : Finset (TorusFields.TorusBond (n * (Tb.stepParameters y).side)))
      (F : (↥Z' × Fin 3 → ℝ) → ℝ) (B : ℝ) hZ' hF hb =>
    hOne T β k n nn j o Z' F B hloc₁ hLn hj hZ' hF hb
  have hC := hClear T β k n nn j o hloc₂ hLn hj
  set x := flowCouplings (Tb.stepParameters y) β k with hxdef
  set m := localBlockSide (Tb.stepParameters y) β k with hmdef
  have hsub : ∀ Z' : Finset (TorusFields.TorusBond (n * (Tb.stepParameters y).side)),
      Z' ⊆ MarkedIntegrals.chartBondsInBlocks (Tb.stepParameters y).side (supBall o ((m : ℝ) / 8)) →
      Z' ⊆ MarkedIntegrals.chartBondsInBlocks (Tb.stepParameters y).side (supBall o m) := fun Z' h b hb => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 (h hb)
    refine Finset.mem_filter.2 ⟨h1, ?_⟩
    obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h2
    refine Finset.mem_filter.2 ⟨h3, h4.trans ?_⟩
    have : (0 : ℝ) ≤ m := by positivity
    linarith
  have hEta : ∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β (k + j + 1) n),
      Disjoint (WeightedResponses.stageState T (k + j + 1) n u).2.1 (supBall o m) →
      StepAvoids T (k + j) m o u →
      ∀ b ∈ MarkedIntegrals.chartBondsInBlocks (Tb.stepParameters y).side (supBall o m),
        ‖(stepDeviationOf T k j u b : ℍ[ℝ])‖ < (Tb.stepParameters y).threshold / 64 := by
    filter_upwards [hC] with u hu hd hs b hb
    exact (((hu hd).2 hs).2 b hb).2
  have hCold : ∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β (k + j + 1) n),
      Disjoint (WeightedResponses.stageState T (k + j + 1) n u).2.1 (supBall o m) →
      IsColdOnBall (Tb.stepParameters y).threshold u.2.2.1 o m := by
    filter_upwards [hC] with u hu hd
    exact (hu hd).1
  have hae := fun (Z' : Finset (TorusFields.TorusBond (n * (Tb.stepParameters y).side)))
      (h : Z' ⊆ MarkedIntegrals.chartBondsInBlocks (Tb.stepParameters y).side (supBall o ((m : ℝ) / 8))) =>
    indicator_pow_ae_eq_truncated T β k j n m o Z' q (hsub Z' h) hEta
  have hcap := fun (Z' : Finset (TorusFields.TorusBond (n * (Tb.stepParameters y).side)))
      (h : Z' ⊆ MarkedIntegrals.chartBondsInBlocks (Tb.stepParameters y).side (supBall o ((m : ℝ) / 8))) =>
    hO Z' (truncatedSupPow Z' ρ q) (ρ ^ q) h (truncatedSupPow_measurable Z' ρ q) (abs_truncatedSupPow_le Z' hρ.le q)
  have hint : ∀ (Z' : Finset (TorusFields.TorusBond (n * (Tb.stepParameters y).side))),
      Z' ⊆ MarkedIntegrals.chartBondsInBlocks (Tb.stepParameters y).side (supBall o ((m : ℝ) / 8)) →
      Integrable (Set.indicator (clearEvent T k j m o)
        (fun u' => finsetSupNonneg Z' (fun b => ‖(stepDeviationOf T k j u' b : ℍ[ℝ])‖) ^ q))
        (WeightedResponses.markedSampleLaw T β (k + j + 1) n) :=
    fun Z' h => (hcap Z' h).1.congr (hae Z' h).symm
  have hsing : ∀ b ∈ Z, ({b} : Finset (TorusFields.TorusBond (n * (Tb.stepParameters y).side))) ⊆
      MarkedIntegrals.chartBondsInBlocks (Tb.stepParameters y).side (supBall o ((m : ℝ) / 8)) :=
    fun b hb => Finset.singleton_subset_iff.2 (hZ hb)
  have hfun : ∀ b : TorusFields.TorusBond (n * (Tb.stepParameters y).side),
      (fun u' : WeightedResponses.MarkedSample (Tb.stepParameters y) (k + j + 1) n =>
        finsetSupNonneg ({b} : Finset (TorusFields.TorusBond (n * (Tb.stepParameters y).side)))
          (fun b' => ‖(stepDeviationOf T k j u' b' : ℍ[ℝ])‖) ^ q) =
        fun u' => ‖(stepDeviationOf T k j u' b : ℍ[ℝ])‖ ^ q := fun b => by
    funext u'
    rw [finsetSupNonneg_singleton b (fun b' => ‖(stepDeviationOf T k j u' b' : ℍ[ℝ])‖) (norm_nonneg _)]
  refine ⟨fun b hb => ?_, hint Z hZ, ?_⟩
  · have := hint {b} (hsing b hb)
    rwa [hfun b] at this
  rcases Nat.eq_zero_or_pos q with hq0 | hq
  · obtain ⟨hprob, hle, -⟩ := hTP (Tb.stepParameters y) hfits hD.L_gt T hloc.cutoff hloc.measurable β
      (fun _ => 0) (k + j + 1) n
    haveI := hprob
    have one : ∀ g : WeightedResponses.MarkedSample (Tb.stepParameters y) (k + j + 1) n → ℝ, (∀ u', g u' = 1) →
        Integrable (Set.indicator (clearEvent T k j m o) g) (WeightedResponses.markedSampleLaw T β (k + j + 1) n) →
        ∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β (k + j + 1) n),
          ((WeightedResponses.markedSampleLaw T β (k + j + 1) n)[Set.indicator (clearEvent T k j m o) g
            | WeightedResponses.stageSigma T (k + j + 1) n]) u ≤ 1 := by
      intro g hg hi
      have h1 := condExp_mono (m := WeightedResponses.stageSigma T (k + j + 1) n) hi (integrable_const (1 : ℝ))
        (ae_of_all _ fun u' => by
          by_cases hE : u' ∈ clearEvent T k j m o
          · rw [Set.indicator_of_mem hE, hg]
          · rw [Set.indicator_of_notMem hE]
            exact zero_le_one)
      rw [condExp_const hle (1 : ℝ)] at h1
      exact h1
    have hA : ∀ b ∈ Z, ∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β (k + j + 1) n),
        ((WeightedResponses.markedSampleLaw T β (k + j + 1) n)[Set.indicator (clearEvent T k j m o)
          (fun u' => ‖(stepDeviationOf T k j u' b : ℍ[ℝ])‖ ^ q)
          | WeightedResponses.stageSigma T (k + j + 1) n]) u ≤ 1 := fun b hb => by
      refine one _ (fun u' => by rw [hq0, pow_zero]) ?_
      have := hint {b} (hsing b hb)
      rwa [hfun b] at this
    have hA' := (Filter.eventually_all_finset Z).2 hA
    filter_upwards [hA', one _ (fun u' => by rw [hq0, pow_zero]) (hint Z hZ)] with u h1 h2 _
    refine ⟨fun b hb => ?_, ?_⟩
    · simpa [hq0] using h1 b hb
    · simpa [hq0] using h2
  have hβ : y ≤ β := hloc.coupling_ge 0 (Nat.zero_le _)
  have hrun := hScaleFlow β hβ
  have hK : k + j ≤ k + 2 * WeightedResponses.chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 := by
    have : j < 2 * WeightedResponses.chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 := hj
    omega
  have hstep : ∀ i, i < 2 * WeightedResponses.chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 →
      |flowCouplings (Tb.stepParameters y) β (k + i + 1) - flowCouplings (Tb.stepParameters y) β (k + i)| ≤
        2 * (Tb.stepParameters y).B := fun i hi =>
    (hrun (k + i)).2 fun j' hj' => hloc.coupling_ge j' (by omega)
  have hclose : ∀ i, i ≤ 2 * WeightedResponses.chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 →
      |flowCouplings (Tb.stepParameters y) β (k + i) - x| ≤ 2 * (Tb.stepParameters y).B * i := by
    intro i
    induction i with
    | zero => intro _; simp [hxdef]
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := hstep i (by omega)
      have h3 : |flowCouplings (Tb.stepParameters y) β (k + (i + 1)) - x| ≤
          |flowCouplings (Tb.stepParameters y) β (k + i + 1) - flowCouplings (Tb.stepParameters y) β (k + i)| +
            |flowCouplings (Tb.stepParameters y) β (k + i) - x| := by
        have := abs_sub_le (flowCouplings (Tb.stepParameters y) β (k + i + 1))
          (flowCouplings (Tb.stepParameters y) β (k + i)) x
        simpa [add_assoc] using this
      push_cast
      linarith
  obtain ⟨hx1, hxlog, hxN⟩ := hx₄ x hxx₄
  have hx0 : 0 < x := by linarith
  set xt := flowCouplings (Tb.stepParameters y) β (k + j) with hxtdef
  have hxt : x / 2 ≤ xt := by
    have h1 := (abs_le.1 (hclose j (by
      have : j < 2 * WeightedResponses.chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 := hj
      omega))).1
    have h2 : (j : ℝ) ≤ 2 * Real.log x ^ 2 := by
      have h3 : (j : ℝ) ≤ 2 * (WeightedResponses.chainDepth x : ℝ) := by
        have : j < 2 * WeightedResponses.chainDepth x := hj
        exact_mod_cast this.le
      have h4 : (WeightedResponses.chainDepth x : ℝ) ≤ Real.log x ^ 2 := Nat.floor_le (by positivity)
      linarith
    have h5 : 2 * (Tb.stepParameters y).B * j ≤ 2 * (Tb.stepParameters y).B * (2 * Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    nlinarith
  have hxt0 : 0 < xt := by linarith
  have hxR : (T.stage (k + j)).coupling = xt := hloc.onFamily.coupling_eq (k + j) (by omega)
  have hR := hloc.onFamily.onFamily (k + j) hK
  have hmN : Tb.n₀ + 1 ≤ m := by
    refine Nat.le_floor ?_
    push_cast
    exact hxN
  have hm : 0 < m := by omega
  have hn₀ : Tb.n₀ ≤ 4 * m := by omega
  have hmomQ : ∀ (Q : ℕ) (Cq : ℝ), (∀ (t : ℕ) (x' : ℝ) (f : ColdStepAtMirrorFrames.LocalFamily)
      (F : BlockAverages.BlockFrame) (V : F.GaugeField F.top)
      (b : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F))),
      (Tb.stepParamsAt cn nss y).coupling ≤ x' →
      ColdStepAtMirrorFrames.IsRegularFamily (Tb.stepParamsAt cn nss y).L t (Tb.stepParamsAt cn nss y).n₀
        (Tb.stepParamsAt cn nss y).σ (Tb.stepParamsAt cn nss y).decayRate (Tb.stepParamsAt cn nss y).E
        (Tb.stepParamsAt cn nss y).energyRatio f →
      ColdStepAtMirrorFrames.IsCubicTopTorus (Tb.stepParamsAt cn nss y).L t (Tb.stepParamsAt cn nss y).n₀ F →
      ColdStepAtMirrorFrames.IsSmallCurvature (Tb.stepParamsAt cn nss y).σ V →
      (WeightedResponses.coldHalfLawAt (Tb.stepParamsAt cn nss y) x' f).expectation V
        (fun η => ‖η b‖ ^ (2 * Q)) ≤ Cq * (x' ^ Q)⁻¹) →
      ∀ V : TorusFields.TorusField n, ColdStepAtMirrorFrames.IsSmallCurvature (Tb.stepParameters y).threshold
        (reflectedTopField (Tb.stepParameters y).side (T.stage (k + j)).depth m o V) →
      ∀ b : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells
        (reflectedTorusFrame (Tb.stepParameters y).side (T.stage (k + j)).depth m n))),
      ColdStepAtMirrorFrames.ballExpectation
        (ColdStepAtMirrorFrames.cutoffFactor ((Tb.stepParameters y).threshold / 64) (T.stage (k + j)).barrierFn)
        (ColdStepAtMirrorFrames.stepExponent false (Tb.stepParameters y).coupling (T.stage (k + j)).anchorRadius
          (T.stage (k + j)).coupling (T.stage (k + j)).toStepSetup.frameReach
          (ColdStepAtMirrorFrames.localFamilyOfDensity (T.stage (k + j)).density) 1
          (reflectedTopField (Tb.stepParameters y).side (T.stage (k + j)).depth m o V))
        (fun η => ‖η b‖ ^ (2 * Q)) ≤ |Cq| * (xt ^ Q)⁻¹ := by
    intro Q Cq hCq V hV b
    have hrowb := hRow (Tb.stepParameters y) (T.stage (k + j)).depth (T.stage (k + j)).coupling
      (T.stage (k + j)).functional (T.stage (k + j)).density hfits rfl hR.isStep.1.1
    have h1 := hCq (T.stage (k + j)).depth (T.stage (k + j)).coupling
      (ColdStepAtMirrorFrames.localFamilyOfDensity (T.stage (k + j)).density)
      (reflectedTorusFrame (Tb.stepParameters y).side (T.stage (k + j)).depth m n)
      (reflectedTopField (Tb.stepParameters y).side (T.stage (k + j)).depth m o V) b hR.le_coupling hrowb
      ⟨rfl, rfl, 4 * m, fun _ => rfl, hn₀⟩ hV
    have hρA : (Tb.stepParamsAt cn nss y).chainParams.ρA = (T.stage (k + j)).anchorRadius :=
      hties.2.2.1.trans hR.anchorRadius_eq.symm
    have hp : (Tb.stepParamsAt cn nss y).p = (T.stage (k + j)).barrierFn := hR.barrierFn_eq.symm
    have hfe : Interpolation.familyLawExponent 1 (Tb.stepParameters y).coupling (T.stage (k + j)).anchorRadius
          (T.stage (k + j)).coupling (T.stage (k + j)).toStepSetup.frameReach
          (ColdStepAtMirrorFrames.localFamilyOfDensity (T.stage (k + j)).density)
          (reflectedTopField (Tb.stepParameters y).side (T.stage (k + j)).depth m o V) =
        ColdStepAtMirrorFrames.stepExponent false (Tb.stepParameters y).coupling (T.stage (k + j)).anchorRadius
          (T.stage (k + j)).coupling (T.stage (k + j)).toStepSetup.frameReach
          (ColdStepAtMirrorFrames.localFamilyOfDensity (T.stage (k + j)).density) 1
          (reflectedTopField (Tb.stepParameters y).side (T.stage (k + j)).depth m o V) := by
      funext η
      have := (hEnds (reflectedTorusFrame (Tb.stepParameters y).side (T.stage (k + j)).depth m n) false
        (Tb.stepParameters y).coupling (T.stage (k + j)).anchorRadius 0
        (T.stage (k + j)).coupling 0 (T.stage (k + j)).toStepSetup.frameReach
        (reflectedTopField (Tb.stepParameters y).side (T.stage (k + j)).depth m o V)).2.2.2.2.2.1
        (ColdStepAtMirrorFrames.localFamilyOfDensity (T.stage (k + j)).density) η
      simpa [Interpolation.segmentEnd] using this
    have e : (WeightedResponses.coldHalfLawAt (Tb.stepParamsAt cn nss y) (T.stage (k + j)).coupling
        (ColdStepAtMirrorFrames.localFamilyOfDensity (T.stage (k + j)).density)).expectation
        (reflectedTopField (Tb.stepParameters y).side (T.stage (k + j)).depth m o V) (fun η => ‖η b‖ ^ (2 * Q)) =
        ColdStepAtMirrorFrames.ballExpectation
          (ColdStepAtMirrorFrames.cutoffFactor ((Tb.stepParameters y).threshold / 64) (T.stage (k + j)).barrierFn)
          (ColdStepAtMirrorFrames.stepExponent false (Tb.stepParameters y).coupling (T.stage (k + j)).anchorRadius
            (T.stage (k + j)).coupling (T.stage (k + j)).toStepSetup.frameReach
            (ColdStepAtMirrorFrames.localFamilyOfDensity (T.stage (k + j)).density) 1
            (reflectedTopField (Tb.stepParameters y).side (T.stage (k + j)).depth m o V))
          (fun η => ‖η b‖ ^ (2 * Q)) := by
      rw [← hfe]
      show ColdStepAtMirrorFrames.ballExpectation
        (ColdStepAtMirrorFrames.cutoffFactor ((Tb.stepParameters y).threshold / 64) (Tb.stepParamsAt cn nss y).p)
        (Interpolation.familyLawExponent 1 (Tb.stepParameters y).coupling (Tb.stepParamsAt cn nss y).chainParams.ρA
          (T.stage (k + j)).coupling (T.stage (k + j)).toStepSetup.frameReach
          (ColdStepAtMirrorFrames.localFamilyOfDensity (T.stage (k + j)).density)
          (reflectedTopField (Tb.stepParameters y).side (T.stage (k + j)).depth m o V)) _ = _
      rw [hρA, hp]
    rw [← e]
    refine h1.trans ?_
    rw [hxR]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have hKw : C₁ * ρ ^ q * Real.exp (-(c * (m : ℝ))) ≤ K0 * Real.exp (-(c * (m : ℝ))) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) (Real.exp_pos _).le
  have hw : Real.exp (-(c * (m : ℝ))) ≤ (x ^ q)⁻¹ := hx₃ x hxx₃
  have hCa0 : 0 ≤ |Ca| := abs_nonneg _
  have hCb0 : 0 ≤ |Cb| := abs_nonneg _
  have hp1 : (0 : ℝ) ≤ 2 ^ q * |Ca| := by positivity
  have hp2 : (0 : ℝ) ≤ 2 ^ (q + 500) * |Cb| := by positivity
  have hA : ∀ b ∈ Z, ∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β (k + j + 1) n),
      Disjoint (WeightedResponses.stageState T (k + j + 1) n u).2.1 (supBall o m) →
      ((WeightedResponses.markedSampleLaw T β (k + j + 1) n)[Set.indicator (clearEvent T k j m o)
        (fun u' => ‖(stepDeviationOf T k j u' b : ℍ[ℝ])‖ ^ q) | WeightedResponses.stageSigma T (k + j + 1) n]) u ≤
      ((1 + 2 ^ q * |Ca| + 2 ^ (q + 500) * |Cb| + K0) * x ^ (-(1 / 2 : ℝ))) ^ q := fun b hb => by
    have hs := condExp_indicator_le T β k j n m o {b} hσ hm q q q (by ring) hq (ε := x ^ (-(1 / 2 : ℝ)))
      (Cm := |Ca| * (xt ^ q)⁻¹) (K := C₁ * ρ ^ q * Real.exp (-(c * (m : ℝ))))
      (Real.rpow_pos_of_pos hx0 _) (by positivity) (hsub _ (hsing b hb)) (hcap _ (hsing b hb)).2 hCold
      (hae _ (hsing b hb)) (hmomQ q Ca hCa)
    rw [hfun b] at hs
    filter_upwards [hs] with u h1 hd
    refine (h1 hd).trans ?_
    have hf := three_terms_le (Nc := 1) (a := 0) (Cm := |Ca|) (K := K0) (w := Real.exp (-(c * (m : ℝ))))
      (C := 1 + 2 ^ q * |Ca| + 2 ^ (q + 500) * |Cb| + K0) (q := q) (r := q) (Q := q)
      hx1 hxt (e := -(1 / 2 : ℝ)) (by norm_num) (by norm_num) zero_le_one (by simp) hCa0 hK00 hw (by ring) hq
      (by push_cast; ring_nf; exact le_rfl) (by linarith)
    simp only [Finset.card_singleton, Nat.cast_one]
    linarith
  have hA' := (Filter.eventually_all_finset Z).2 hA
  have hs := condExp_indicator_le T β k j n m o Z hσ hm q (q + 1000) (q + 500) (by ring) (by omega)
    (ε := x ^ (-(1 / 2 : ℝ) + 1 / 1000)) (Cm := |Cb| * (xt ^ (q + 500))⁻¹)
    (K := C₁ * ρ ^ q * Real.exp (-(c * (m : ℝ))))
    (Real.rpow_pos_of_pos hx0 _) (by positivity) (hsub _ hZ) (hcap _ hZ).2 hCold (hae _ hZ)
    (hmomQ (q + 500) Cb hCb)
  filter_upwards [hA', hs] with u h1 h2 hd
  refine ⟨fun b hb => h1 b hb hd, (h2 hd).trans ?_⟩
  have hf := three_terms_le (Nc := (Z.card : ℝ)) (a := 1) (Cm := |Cb|) (K := K0)
    (w := Real.exp (-(c * (m : ℝ))))
    (C := 1 + 2 ^ q * |Ca| + 2 ^ (q + 500) * |Cb| + K0) (q := q) (r := q + 1000) (Q := q + 500)
    hx1 hxt (e := -(1 / 2 : ℝ) + 1 / 1000) (by norm_num) (by norm_num) (by positivity)
    (by rw [Real.rpow_one]; exact hcard) hCb0 hK00 hw (by ring) hq
    (by
      have hq0 : (0 : ℝ) ≤ q := by positivity
      push_cast
      nlinarith) (by linarith)
  linarith
end Table
theorem stepDeviationMomentsStatement_proof (hOne : oneStepReflectedLawStatement)
    (hClear : descentKeepsBallClearStatement) (hMom : coldHalfLawMomentsStatement)
    (hTP : TwoPointByTotalCovarianceStatement) (hScaleFlow : ClusterExpansionOfAStep.FlowWhereExpansionReturns)
    (hRow : ColdStepAtMirrorFrames.ColdExpansionRegular) (hEnds : Interpolation.interpolationAtEndpoints) :
    stepDeviationMomentsStatement := by
  obtain ⟨Cr, hScaleFlow⟩ := hScaleFlow
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, h₁⟩ := hOne a ha
  obtain ⟨L₂, r₂, C₂, hr₂, h₂⟩ := hClear a ha
  obtain ⟨L₃, r₃, C₃, hr₃, h₃⟩ := hMom a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (r₁ c) (min (r₂ c) (r₃ c)), max Cr (max C₁ (max C₂ C₃)),
    fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (hr₃ c)), fun L hL hLL T hTa hTL hD hS hH hrt hCd => ?_⟩
  obtain ⟨y₁, g₁⟩ := h₁ L hL ((le_max_left _ _).trans hLL) T hTa hTL hD hS hH
    (hrt.trans (min_le_left _ _)) (((le_max_left _ _).trans (le_max_right _ _)).trans hCd)
  obtain ⟨y₂, g₂⟩ := h₂ L hL (((le_max_left _ _).trans (le_max_right _ _)).trans hLL) T hTa hTL hD hS hH
    (hrt.trans ((min_le_right _ _).trans (min_le_left _ _)))
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hCd)
  obtain ⟨y₃, g₃⟩ := h₃ L hL (((le_max_right _ _).trans (le_max_right _ _)).trans hLL) T hTa hTL hD hS hH
    (hrt.trans ((min_le_right _ _).trans (min_le_right _ _)))
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hCd)
  refine ⟨max T.floorMin (max y₁ (max y₂ y₃)), fun y hy hRR hW => ?_⟩
  have hy₀ : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hy₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy₂ : y₂ ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hy₃ : y₃ ≤ y := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hfits : (T.stepParameters y).Admissible := hD.fits y hy₀
  have hrun := (hScaleFlow (T.stepParameters y) hfits ((le_max_left _ _).trans hCd) hRR).2
  exact stepDeviationMomentsAt_of T y hD hy₀ (g₁ y hy₁ hRR hW) (g₂ y hy₂ hRR hW) (g₃ y hy₃ hRR hW)
    (fun β hβ => (hrun β hβ).1) hTP hRow hEnds
end YangMills.Construction.ResponseInTheExpansion
end
