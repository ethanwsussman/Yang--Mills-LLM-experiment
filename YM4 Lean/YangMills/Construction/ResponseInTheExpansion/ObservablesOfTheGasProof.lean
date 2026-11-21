import YangMills.Construction.ResponseInTheExpansion.FarVariableUnderATiltProof
import YangMills.Construction.ResponseInTheExpansion.ObservablesOfTheGas
import YangMills.Construction.ResponseInTheExpansion.TwoGroundsAtOscillations
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open Dobrushin
namespace ResponseInTheExpansion
open ClusterExpansionOfAStep StepGas StepSettings RenormalizationStepParameters TorusLumps TorusFields CoreColumns
namespace GasObservables
section SingleSpin
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
theorem lintegral_spin_le (hM : MeanOfProductStatement) (A : PairConstraint S) (m : ∀ i, Measure (S i))
    [∀ i, SigmaFinite (m i)] (W : (∀ i, S i) → ℝ) (z : I → ℝ) (h : A.IsActivityBounded m W z)
    [IsProbabilityMeasure (A.gibbsLaw m W)] (i : I) (g : S i → ℝ) (hg : Measurable g) (g0 : ∀ v, 0 ≤ g v)
    (ga : g (A.vacant i) = 0) {B : ℝ} (hB : 0 ≤ B)
    (hp : ∀ σ, A.IsAdmissible σ → ∫⁻ v in {A.vacant i}ᶜ, ENNReal.ofReal (g v) * A.weightDensity W (Function.update σ i v) ∂m i ≤
      ENNReal.ofReal B * A.weightDensity W (Function.update σ i (A.vacant i))) :
    ∫⁻ σ, ENNReal.ofReal (g (σ i)) ∂A.gibbsLaw m W ≤ ENNReal.ofReal B := by apply _root_.YangMills.Construction.TiltedGasResponse.lintegral_single_spin_le <;> assumption
end SingleSpin
theorem integrable_and_integral_le_of_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Measurable f) (h0 : ∀ a, 0 ≤ f a) {b : ℝ} (hb : 0 ≤ b)
    (h : ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≤ ENNReal.ofReal b) :
    Integrable f μ ∧ ∫ a, f a ∂μ ≤ b := by
  refine ⟨⟨hf.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ h0)]
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0) hf.aestronglyMeasurable]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal hb] at this
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem core_nonempty (G : GasGround R n) (i : G.GasSpin) : i.1.core.Nonempty := by apply _root_.YangMills.Construction.StepGas.core_nonempty_of_gasSpin <;> assumption
theorem coreWeightFrom_pos (G : GasGround R n) (Y : TorusSite n) (i : G.GasSpin) : 0 < G.coreWeightFrom Y i := by apply _root_.YangMills.Construction.GasComparison.coreWeightFrom_pos <;> assumption
theorem hasDobrushinColumns (G : GasGround R n) (Y : TorusSite n) {c : ℝ} {off : G.GasSpin → Prop}
    {h : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff off) G.weight (G.spinActivity c)}
    (hs : G.HasSmallColumns off c h) :
    G.pairConstraint.HasDobrushinColumns (G.referenceMeasureOff off) h.measurable_weightDensity
      (G.influenceMatrix c) (G.coreWeightFrom Y) where
  coeff_nonneg := hs.influenceMatrix_nonneg
  weight_pos := coreWeightFrom_pos G Y
  kernel_le := hs.kernel_le
  column_sum_le j := by
    have h1 := hs.column_le Y j
    have h2 := hs.exp_le_half
    have h3 := coreWeightFrom_pos G Y j
    nlinarith
theorem spinActivity_nonneg (G : GasGround R n) (i : G.GasSpin) (c : ℝ) : 0 ≤ G.spinActivity c i := by apply _root_.YangMills.Construction.GasComparison.spinActivity_nonneg <;> assumption
theorem restrictAdmissible_of_admissible (G : GasGround R n) (F : G.Config → ℝ) {σ : G.Config}
    (h : G.pairConstraint.IsAdmissible σ) : restrictAdmissible G F σ = F σ := by
  unfold restrictAdmissible
  rw [if_pos h]
theorem restrictAdmissible_of_not_admissible (G : GasGround R n) (F : G.Config → ℝ) {σ : G.Config}
    (h : ¬ G.pairConstraint.IsAdmissible σ) : restrictAdmissible G F σ = 0 := by
  unfold restrictAdmissible
  rw [if_neg h]
theorem allVacant_admissible (G : GasGround R n) : G.pairConstraint.IsAdmissible G.allVacant :=
  fun i j _ => G.pairConstraint.vacant_compatible i j _
structure GibbsData (G : GasGround R n) (c : ℝ) where
  activityBounded : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff fun i => i.1.Touches ∅) G.weight
    (G.spinActivity c)
  smallColumns : G.HasSmallColumns (fun i => i.1.Touches ∅) c activityBounded
def truncate (G : GasGround R n) (p s : G.Config → ℝ) (L : ℝ) (σ : G.Config) : ℝ :=
  open Classical in if restrictAdmissible G s σ ≤ L then restrictAdmissible G p σ else 0
section SingleGround
variable {G : GasGround R n} {Y : TorusSite n} {c C u s₀ : ℝ} {D₀ : ℕ} {p s : G.Config → ℝ}
theorem measurable_truncate (ob : IsGasObservable G Y c C u s₀ D₀ p s) (L : ℝ) :
    Measurable (truncate G p s L) := by
  classical
  unfold truncate
  exact Measurable.ite (measurableSet_le ob.measurable_score measurable_const) ob.measurable_value measurable_const
theorem abs_truncate_le (ob : IsGasObservable G Y c C u s₀ D₀ p s) {L : ℝ} (hL : 0 ≤ L) (σ : G.Config) :
    |truncate G p s L σ| ≤ (C + L) * u := by
  classical
  have hC := ob.one_le
  have hu := ob.amplitude_nonneg
  unfold truncate
  split_ifs with h
  · by_cases ha : G.pairConstraint.IsAdmissible σ
    · rw [restrictAdmissible_of_admissible G _ ha] at h ⊢
      refine (ob.abs_le σ ha).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith) hu
    · rw [restrictAdmissible_of_not_admissible G _ ha, abs_zero]
      positivity
  · rw [abs_zero]
    positivity
theorem truncate_allVacant (ob : IsGasObservable G Y c C u s₀ D₀ p s) {L : ℝ} (hL : s₀ ≤ L) :
    truncate G p s L G.allVacant = p G.allVacant := by
  classical
  have ha := allVacant_admissible G
  obtain ⟨H, e, he⟩ := ob.controlled
  have hs : s G.allVacant ≤ s₀ := by
    rcases he.score_le _ ha with h | ⟨i, -, h, -⟩
    · exact h
    · exact absurd rfl h
  unfold truncate
  rw [restrictAdmissible_of_admissible G _ ha, restrictAdmissible_of_admissible G _ ha, if_pos (hs.trans hL)]
theorem truncate_oscillationControlled (ob : IsGasObservable G Y c C u s₀ D₀ p s) {L c₀ : ℝ} (hL : 0 ≤ L)
    (hrt : 0 ≤ R.params.rt) :
    G.pairConstraint.OscillationControlled (G.coreWeightFrom Y)
      (2 * (C + 1 + L) * u * Real.exp (R.params.rt / 2 ^ 6 * D₀))
      (fun σ => truncate G p s L σ - c₀) := by
  classical
  have hC := ob.one_le
  have hu := ob.amplitude_nonneg
  have hK : 0 ≤ 2 * (C + 1 + L) * u * Real.exp (R.params.rt / 2 ^ 6 * D₀) := by positivity
  have hbr : 1 ≤ Real.exp (R.params.rt / 2 ^ 6 * D₀) := Real.one_le_exp (by positivity)
  refine ⟨hK, (measurable_truncate ob L).sub measurable_const, ⟨(C + L) * u + |c₀|, fun σ => ?_⟩,
    ⟨fun i => mul_nonneg hK (coreWeightFrom_pos G Y i).le, ?_⟩⟩
  · exact (abs_sub _ _).trans (by linarith [abs_truncate_le ob hL σ])
  intro i σ σ' hσ hσ' hd
  have hw := coreWeightFrom_pos G Y i
  have e0 : (truncate G p s L σ - c₀) - (truncate G p s L σ' - c₀) =
      truncate G p s L σ - truncate G p s L σ' := by ring
  dsimp only
  rw [e0]
  by_cases hg : D₀ ≤ setGap {Y} i.1.core
  · obtain ⟨e1, e2⟩ := ob.local_far i σ σ' hσ hσ' hd hg
    unfold truncate
    rw [restrictAdmissible_of_admissible G _ hσ, restrictAdmissible_of_admissible G _ hσ',
      restrictAdmissible_of_admissible G _ hσ, restrictAdmissible_of_admissible G _ hσ', ← e1]
    by_cases hsl : s σ ≤ L
    · rw [if_pos hsl, if_pos hsl]
      refine e2.trans ?_
      have h0 := ob.score_nonneg σ hσ
      have h1 : 2 * (1 + s σ) * u ≤ 2 * (C + 1 + L) * u * Real.exp (R.params.rt / 2 ^ 6 * D₀) := by
        have h2 : 2 * (1 + s σ) * u ≤ 2 * (C + 1 + L) * u := by
          refine mul_le_mul_of_nonneg_right ?_ hu
          linarith
        have h3 : 0 ≤ 2 * (C + 1 + L) * u := by positivity
        nlinarith
      calc 2 * (1 + s σ) * G.coreWeightFrom Y i * u = 2 * (1 + s σ) * u * G.coreWeightFrom Y i := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 hw.le
    · rw [if_neg hsl, if_neg hsl, sub_self, abs_zero]
      exact mul_nonneg hK hw.le
  · have hlt : (setGap {Y} i.1.core : ℝ) ≤ D₀ := by
      exact_mod_cast (not_le.mp hg).le
    have h1 := abs_truncate_le ob hL σ
    have h2 := abs_truncate_le ob hL σ'
    have h3 : |truncate G p s L σ - truncate G p s L σ'| ≤ 2 * (C + L) * u := by
      refine (abs_sub _ _).trans ?_
      linarith
    refine h3.trans ?_
    have hcard : (1 : ℝ) ≤ (i.1.core.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (core_nonempty G i)
    have h4 : 1 ≤ Real.exp (R.params.rt / 2 ^ 6 * D₀) * G.coreWeightFrom Y i := by
      unfold GasGround.coreWeightFrom coreWeight
      have h5 : 1 ≤ Real.exp (R.params.rt / 2 ^ 6 * D₀) *
          Real.exp (-(R.params.rt / 2 ^ 6 * (setGap {Y} i.1.core : ℝ))) := by
        rw [← Real.exp_add]
        refine Real.one_le_exp ?_
        have : R.params.rt / 2 ^ 6 * (setGap {Y} i.1.core : ℝ) ≤ R.params.rt / 2 ^ 6 * D₀ :=
          mul_le_mul_of_nonneg_left hlt (by positivity)
        linarith
      calc (1 : ℝ) ≤ (i.1.core.card : ℝ) * (Real.exp (R.params.rt / 2 ^ 6 * D₀) *
            Real.exp (-(R.params.rt / 2 ^ 6 * (setGap {Y} i.1.core : ℝ)))) :=
            one_le_mul_of_one_le_of_one_le hcard h5
        _ = _ := by ring
    have h5 : 0 ≤ 2 * (C + 1 + L) * u := by positivity
    calc 2 * (C + L) * u ≤ 2 * (C + 1 + L) * u := by
          refine mul_le_mul_of_nonneg_right ?_ hu
          linarith
      _ ≤ 2 * (C + 1 + L) * u * (Real.exp (R.params.rt / 2 ^ 6 * D₀) * G.coreWeightFrom Y i) :=
          le_mul_of_one_le_right h5 h4
      _ = _ := by ring
variable (hM : MeanOfProductStatement) (B : GibbsData G c)
include hM B in
theorem integral_spin_le (i : G.GasSpin) (g : G.SpinValue i → ℝ) (hg : Measurable g) (g0 : ∀ v, 0 ≤ g v)
    (ga : g (Sum.inl ()) = 0) {b : ℝ} (hb : 0 ≤ b)
    (hp : ∀ σ, G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (g v) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i v)
        ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal b * G.pairConstraint.weightDensity G.weight
        (Function.update σ i (G.pairConstraint.vacant i))) :
    Integrable (fun σ : G.Config => g (σ i)) (G.gibbsLaw ∅) ∧ ∫ σ, g (σ i) ∂G.gibbsLaw ∅ ≤ b := by
  have : IsProbabilityMeasure (G.pairConstraint.gibbsLaw (G.referenceMeasureOff fun i => i.1.Touches ∅) G.weight) :=
    B.smallColumns.isProbabilityMeasure
  have key := lintegral_spin_le hM G.pairConstraint (G.referenceMeasureOff fun i => i.1.Touches ∅) G.weight
    (G.spinActivity c) B.activityBounded i g hg g0 ga hb hp
  exact integrable_and_integral_le_of_lintegral (hg.comp (measurable_pi_apply i)) (fun σ => g0 _) hb key
include B in
theorem expectation_eq (F : G.Config → ℝ) :
    G.expectation ∅ F = ∫ σ, restrictAdmissible G F σ ∂G.gibbsLaw ∅ := by
  refine integral_congr_ae ?_
  filter_upwards [B.smallColumns.isSpecification.ae_admissible] with σ hσ
  exact (restrictAdmissible_of_admissible G F hσ).symm
include hM B in
theorem abs_integral_sub_truncate_le (ob : IsGasObservable G Y c C u s₀ D₀ p s) {S Z : ℝ} (hS : 0 ≤ S)
    (hZ : ∀ H : Finset G.GasSpin, (∀ i ∈ H, Y ∈ i.1.core) → ∑ i ∈ H, G.spinActivity c i ≤ Z) :
    Integrable (restrictAdmissible G p) (G.gibbsLaw ∅) ∧
      |∫ σ, restrictAdmissible G p σ ∂G.gibbsLaw ∅ - ∫ σ, truncate G p s (s₀ + S) σ ∂G.gibbsLaw ∅| ≤
        (C + 2) * u * Real.exp (-(S / 2)) * Z := by
  classical
  have : IsProbabilityMeasure (G.gibbsLaw ∅) := B.smallColumns.isProbabilityMeasure
  obtain ⟨H, e, he⟩ := ob.controlled
  have hC := ob.one_le
  have hu := ob.amplitude_nonneg
  have hs₀ := ob.baseScore_nonneg
  set b₀ : ℝ := (C + 2) * u * Real.exp (-(S / 2)) with hb₀
  have hb₀0 : 0 ≤ b₀ := by positivity
  let tl : ∀ i : G.GasSpin, G.SpinValue i → ℝ := fun i v => if S < e i v then (C + e i v) * u else 0
  have htlm : ∀ i, Measurable (tl i) := fun i =>
    Measurable.ite (measurableSet_lt measurable_const (he.measurable i))
      ((measurable_const.add (he.measurable i)).mul measurable_const) measurable_const
  have htl0 : ∀ i v, 0 ≤ tl i v := by
    intro i v
    simp only [tl]
    split_ifs
    · have := he.nonneg i v
      positivity
    · exact le_rfl
  have htla : ∀ i, tl i (Sum.inl ()) = 0 := by
    intro i
    simp only [tl]
    rw [he.vacant_eq_zero i, if_neg (not_lt.mpr hS)]
  have htle : ∀ i v, tl i v ≤ b₀ * Real.exp (e i v) := by
    intro i v
    have hev := he.nonneg i v
    simp only [tl]
    split_ifs with h
    · have h1 : C + e i v ≤ (C + 2) * Real.exp (e i v / 2) := by
        have := Real.add_one_le_exp (e i v / 2)
        nlinarith
      have h2 : 1 ≤ Real.exp ((e i v - S) / 2) := Real.one_le_exp (by linarith)
      have h3 : Real.exp (e i v / 2) * Real.exp ((e i v - S) / 2) = Real.exp (-(S / 2)) * Real.exp (e i v) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc (C + e i v) * u ≤ ((C + 2) * Real.exp (e i v / 2)) * u := mul_le_mul_of_nonneg_right h1 hu
        _ ≤ ((C + 2) * Real.exp (e i v / 2)) * Real.exp ((e i v - S) / 2) * u := by
            refine mul_le_mul_of_nonneg_right ?_ hu
            exact le_mul_of_one_le_right (by positivity) h2
        _ = (C + 2) * (Real.exp (e i v / 2) * Real.exp ((e i v - S) / 2)) * u := by ring
        _ = _ := by rw [h3, hb₀]; ring
    · positivity
  have hone : ∀ i ∈ H, Integrable (fun σ : G.Config => tl i (σ i)) (G.gibbsLaw ∅) ∧
      ∫ σ, tl i (σ i) ∂G.gibbsLaw ∅ ≤ b₀ * G.spinActivity c i := by
    intro i hi
    refine integral_spin_le hM B i (tl i) (htlm i) (htl0 i) (htla i)
      (mul_nonneg hb₀0 (spinActivity_nonneg G i c)) fun σ hσ => ?_
    have h1 := he.activity_bound i hi σ hσ
    calc ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (tl i v) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i)
        ≤ ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal b₀ *
            (ENNReal.ofReal (Real.exp (e i v)) *
              G.pairConstraint.weightDensity G.weight (Function.update σ i v))
          ∂(G.referenceMeasure ∅ i) := by
          refine lintegral_mono fun v => ?_
          dsimp only
          rw [← mul_assoc, ← ENNReal.ofReal_mul hb₀0]
          gcongr
          exact htle i v
      _ = ENNReal.ofReal b₀ * ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (e i v)) *
            G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal b₀ * (ENNReal.ofReal (G.spinActivity c i) *
            G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i))) := by
          gcongr
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hb₀0]
  set Tl : G.Config → ℝ := fun σ => ∑ i ∈ H, tl i (σ i) with hTl
  have hTi : Integrable Tl (G.gibbsLaw ∅) := integrable_finsetSum _ fun i hi => (hone i hi).1
  have hTs : ∫ σ, Tl σ ∂G.gibbsLaw ∅ ≤ b₀ * Z := by
    rw [hTl, integral_finsetSum _ fun i hi => (hone i hi).1]
    refine (Finset.sum_le_sum fun i hi => (hone i hi).2).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hZ H he.core_mem) hb₀0
  have hL : 0 ≤ s₀ + S := by linarith
  have hcm := measurable_truncate ob (s₀ + S)
  have hci : Integrable (truncate G p s (s₀ + S)) (G.gibbsLaw ∅) :=
    (integrable_const ((C + (s₀ + S)) * u)).mono' hcm.aestronglyMeasurable
      (ae_of_all _ fun σ => abs_truncate_le ob hL σ)
  have hpt : ∀ᵐ σ ∂G.gibbsLaw ∅, |restrictAdmissible G p σ - truncate G p s (s₀ + S) σ| ≤ Tl σ := by
    filter_upwards [B.smallColumns.isSpecification.ae_admissible] with σ hσ
    have hT0 : ∀ i ∈ H, 0 ≤ tl i (σ i) := fun i _ => htl0 i _
    unfold truncate
    rw [restrictAdmissible_of_admissible G _ hσ, restrictAdmissible_of_admissible G _ hσ]
    split_ifs with hsl
    · rw [sub_self, abs_zero]
      exact Finset.sum_nonneg hT0
    · rw [sub_zero]
      have hsl' := not_le.mp hsl
      rcases he.score_le σ hσ with h | ⟨i, hi, -, h⟩
      · exfalso
        linarith
      · have hSe : S < e i (σ i) := by linarith
        have h1 : tl i (σ i) = (C + e i (σ i)) * u := by
          simp only [tl]
          rw [if_pos hSe]
        have h2 : tl i (σ i) ≤ Tl σ := Finset.single_le_sum hT0 hi
        refine (ob.abs_le σ hσ).trans (le_trans ?_ h2)
        rw [h1]
        exact mul_le_mul_of_nonneg_right (by linarith) hu
  have hPm : AEStronglyMeasurable (restrictAdmissible G p) (G.gibbsLaw ∅) :=
    ob.measurable_value.aestronglyMeasurable
  have hPi : Integrable (restrictAdmissible G p) (G.gibbsLaw ∅) := by
    have h1 : Integrable (fun σ => restrictAdmissible G p σ - truncate G p s (s₀ + S) σ) (G.gibbsLaw ∅) :=
      hTi.mono' (hPm.sub hcm.aestronglyMeasurable) hpt
    have h2 := h1.add hci
    refine h2.congr (ae_of_all _ fun σ => ?_)
    simp
  refine ⟨hPi, ?_⟩
  rw [← integral_sub hPi hci]
  refine (abs_integral_le_integral_abs).trans (le_trans (integral_mono_ae (hPi.sub hci).abs hTi hpt) hTs)
include hM B in
theorem abs_integral_le (ob : IsGasObservable G Y c C u s₀ D₀ p s) {Z : ℝ}
    (hZ : ∀ H : Finset G.GasSpin, (∀ i ∈ H, Y ∈ i.1.core) → ∑ i ∈ H, G.spinActivity c i ≤ Z) :
    |∫ σ, restrictAdmissible G p σ ∂G.gibbsLaw ∅| ≤ (C + s₀ + Z) * u := by
  classical
  have : IsProbabilityMeasure (G.gibbsLaw ∅) := B.smallColumns.isProbabilityMeasure
  obtain ⟨H, e, he⟩ := ob.controlled
  have hu := ob.amplitude_nonneg
  have hs₀ := ob.baseScore_nonneg
  have hone : ∀ i ∈ H, Integrable (fun σ : G.Config => e i (σ i)) (G.gibbsLaw ∅) ∧
      ∫ σ, e i (σ i) ∂G.gibbsLaw ∅ ≤ G.spinActivity c i := by
    intro i hi
    refine integral_spin_le hM B i (e i) (he.measurable i) (he.nonneg i) (he.vacant_eq_zero i)
      (spinActivity_nonneg G i c) fun σ hσ => ?_
    refine le_trans (lintegral_mono fun v => ?_) (he.activity_bound i hi σ hσ)
    dsimp only
    gcongr
    have := Real.add_one_le_exp (e i v)
    linarith
  set Tl : G.Config → ℝ := fun σ => ∑ i ∈ H, e i (σ i) with hTl
  have hTi : Integrable Tl (G.gibbsLaw ∅) := integrable_finsetSum _ fun i hi => (hone i hi).1
  have hTs : ∫ σ, Tl σ ∂G.gibbsLaw ∅ ≤ Z := by
    rw [hTl, integral_finsetSum _ fun i hi => (hone i hi).1]
    exact (Finset.sum_le_sum fun i hi => (hone i hi).2).trans (hZ H he.core_mem)
  have hdom : Integrable (fun σ => (C + s₀ + Tl σ) * u) (G.gibbsLaw ∅) :=
    ((integrable_const (C + s₀)).add hTi).mul_const u
  have hpt : ∀ᵐ σ ∂G.gibbsLaw ∅, |restrictAdmissible G p σ| ≤ (C + s₀ + Tl σ) * u := by
    filter_upwards [B.smallColumns.isSpecification.ae_admissible] with σ hσ
    rw [restrictAdmissible_of_admissible G _ hσ]
    have hT0 : ∀ i ∈ H, 0 ≤ e i (σ i) := fun i _ => he.nonneg i _
    have hT : 0 ≤ Tl σ := Finset.sum_nonneg hT0
    refine (ob.abs_le σ hσ).trans (mul_le_mul_of_nonneg_right ?_ hu)
    rcases he.score_le σ hσ with h | ⟨i, hi, -, h⟩
    · linarith
    · have : e i (σ i) ≤ Tl σ := Finset.single_le_sum hT0 hi
      linarith
  have hPi : Integrable (fun σ => |restrictAdmissible G p σ|) (G.gibbsLaw ∅) :=
    hdom.mono' ob.measurable_value.aestronglyMeasurable.norm
      (hpt.mono fun σ h => by simpa using h)
  refine (abs_integral_le_integral_abs).trans ((integral_mono_ae hPi hdom hpt).trans ?_)
  rw [integral_mul_const, integral_add (integrable_const _) hTi, integral_const, probReal_univ, one_smul]
  exact mul_le_mul_of_nonneg_right (by linarith) hu
end SingleGround
section Estimates
theorem single_ground_arith {C u s₀ W ch x br : ℝ} (hC : 1 ≤ C) (hu : 0 ≤ u) (hs : 0 ≤ s₀) (hW : 0 ≤ W)
    (hQ : 2 ^ 8 * (C + 2) * W + 1 ≤ ch * x) (hbr : br ≤ Real.exp (ch * x)) (hbr0 : 0 ≤ br) :
    (C + 2) * u * Real.exp (-(0 / 2)) * (Real.exp (-(8 * ch * x)) * W) +
        2 * (C + 1 + (s₀ + 0)) * u * br * (4 * (Real.exp (-(8 * ch * x)) * W)) ≤
      (1 + s₀) * Real.exp (-(6 * ch * x)) * u := by
  set A := Real.exp (ch * x) with hA
  set E := Real.exp (-(8 * ch * x)) with hE
  have hWnn : 0 ≤ (C + 2) * W := by positivity
  have hAx : ch * x + 1 ≤ A := Real.add_one_le_exp _
  have e6 : Real.exp (-(6 * ch * x)) = E * (A * A) := by
    rw [hE, hA, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hWA : 9 * (C + 2) * W ≤ A := by nlinarith
  have b0 : C + 1 + s₀ ≤ (1 + s₀) * (C + 1) := by nlinarith
  have b1 : 8 * (C + 1 + s₀) * br ≤ 8 * ((1 + s₀) * (C + 1)) * A := by
    have : 0 ≤ (1 + s₀) * (C + 1) := by positivity
    exact mul_le_mul (by linarith) hbr hbr0 (by positivity)
  have b2 : C + 2 ≤ (1 + s₀) * (C + 2) * A := by
    nlinarith
  have b3 : 8 * ((1 + s₀) * (C + 1)) * A ≤ 8 * ((1 + s₀) * (C + 2)) * A := by
    have : (1 + s₀) * (C + 1) ≤ (1 + s₀) * (C + 2) := by nlinarith
    nlinarith
  have k1 : (C + 2) + 8 * (C + 1 + s₀) * br ≤ (1 + s₀) * (9 * (C + 2)) * A := by linarith
  have k2 : ((C + 2) + 8 * (C + 1 + s₀) * br) * W ≤ (1 + s₀) * A * A := by
    calc _ ≤ (1 + s₀) * (9 * (C + 2)) * A * W := mul_le_mul_of_nonneg_right k1 hW
      _ = (1 + s₀) * A * (9 * (C + 2) * W) := by ring
      _ ≤ (1 + s₀) * A * A := mul_le_mul_of_nonneg_left hWA (by positivity)
  have hEu : 0 ≤ E * u := by positivity
  have k3 := mul_le_mul_of_nonneg_left k2 hEu
  rw [e6]
  have e0 : Real.exp (-(0 / 2 : ℝ)) = 1 := by simp
  rw [e0]
  calc _ = E * u * (((C + 2) + 8 * (C + 1 + s₀) * br) * W) := by ring
    _ ≤ _ := k3
    _ = _ := by ring
theorem activity_sum_arith {C W ch x : ℝ} (hC : 1 ≤ C) (hW : 0 ≤ W) (hQ : 2 ^ 8 * (C + 2) * W + 1 ≤ ch * x) :
    Real.exp (-(8 * ch * x)) * W ≤ Real.exp (-(6 * ch * x)) := by
  set A := Real.exp (ch * x) with hA
  have hAx : ch * x + 1 ≤ A := Real.add_one_le_exp _
  have hWnn : 0 ≤ (C + 2) * W := by positivity
  have e6 : Real.exp (-(6 * ch * x)) = Real.exp (-(8 * ch * x)) * (A * A) := by
    rw [hA, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [e6]
  have : W ≤ A * A := by nlinarith
  exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
theorem two_grounds_arith {C u s₀ W ch x rt br v N N₂ : ℝ} (hC : 1 ≤ C) (hu : 0 ≤ u) (hs : 0 ≤ s₀) (hW : 0 ≤ W)
    (hv : v = rt / 2 ^ 8 * N) (hv0 : 0 ≤ v) (hrt : 0 < rt) (hN₂ : 15 / 16 * N ≤ N₂)
    (hQ : 2 ^ 8 * (C + 2) * W + 1 ≤ ch * x) (hbr : br ≤ Real.exp (ch * x)) (hbr0 : 0 ≤ br) :
    (16 * (2 * (C + 1 + (s₀ + 2 * v)) * u * br) * Real.exp (-(2 * (rt / 2 ^ 8) * N₂)) +
          (2 * (1 + (s₀ + 2 * v)) * Real.exp (-(15 / 16 * rt * N / 2 ^ 5)) * u) * Real.exp (rt / 2 ^ 8 * N)) *
        (Real.exp (-(8 * ch * x)) * W) +
      2 * ((C + 2) * u * Real.exp (-(2 * v / 2)) * (Real.exp (-(8 * ch * x)) * W)) ≤
      (1 + s₀) * Real.exp (-(2 * ch * x) - rt * N / 2 ^ 8) * u := by
  set A := Real.exp (ch * x) with hA
  set E := Real.exp (-(8 * ch * x)) with hE
  set e₁ := Real.exp (-v) with he₁
  have hE0 : 0 < E := Real.exp_pos _
  have hAx : ch * x + 1 ≤ A := Real.add_one_le_exp _
  have hWnn : 0 ≤ (C + 2) * W := by positivity
  have hA1 : 1 ≤ A := by
    have : 0 ≤ 2 ^ 8 * ((C + 2) * W) := by positivity
    nlinarith
  have hA0 : 0 ≤ A := by linarith
  have hb : 0 ≤ 1 + s₀ := by linarith
  have hexp : 1 + 2 * v ≤ 4 * Real.exp (v / 2) := by
    have := Real.add_one_le_exp (v / 2)
    linarith
  have hP1 : C + 1 + (s₀ + 2 * v) ≤ (1 + s₀) * (C + 1) * (4 * Real.exp (v / 2)) := by
    have h1 : C + 1 + (s₀ + 2 * v) ≤ (1 + s₀) * (C + 1) * (1 + 2 * v) := by
      have a1 : 0 ≤ s₀ * v := mul_nonneg hs hv0
      have a2 : 0 ≤ s₀ * C := mul_nonneg hs (by linarith)
      have a3 : 0 ≤ C * v := mul_nonneg (by linarith) hv0
      have a4 : 0 ≤ s₀ * C * v := mul_nonneg a2 hv0
      nlinarith
    exact h1.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hP2 : 1 + (s₀ + 2 * v) ≤ (1 + s₀) * (4 * Real.exp (v / 2)) := by
    have h1 : 1 + (s₀ + 2 * v) ≤ (1 + s₀) * (1 + 2 * v) := by nlinarith [mul_nonneg hs hv0]
    exact h1.trans (mul_le_mul_of_nonneg_left hexp hb)
  have hE₂ : Real.exp (-(2 * (rt / 2 ^ 8) * N₂)) ≤ Real.exp (-(15 / 8 * v)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [hv]
    have : rt / 2 ^ 8 * (15 / 16 * N) ≤ rt / 2 ^ 8 * N₂ := mul_le_mul_of_nonneg_left hN₂ (by positivity)
    nlinarith
  have hEr : Real.exp (-(15 / 16 * rt * N / 2 ^ 5)) = Real.exp (-(15 / 2 * v)) := by
    congr 1
    rw [hv]
    ring
  have hv' : Real.exp (rt / 2 ^ 8 * N) = Real.exp v := by rw [hv]
  have c1 : Real.exp (v / 2) * Real.exp (-(15 / 8 * v)) ≤ e₁ := by
    rw [he₁, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    linarith
  have c2 : Real.exp (v / 2) * (Real.exp (-(15 / 2 * v)) * Real.exp v) ≤ e₁ := by
    rw [he₁, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    linarith
  have t1 : (C + 1 + (s₀ + 2 * v)) * br * Real.exp (-(2 * (rt / 2 ^ 8) * N₂)) ≤
      (1 + s₀) * (C + 1) * (4 * A) * e₁ := by
    have h1 := mul_le_mul (mul_le_mul hP1 hbr hbr0 (by positivity)) hE₂ (Real.exp_pos _).le (by positivity)
    refine h1.trans ?_
    have h2 : 0 ≤ (1 + s₀) * (C + 1) * (4 * A) := by positivity
    calc _ = (1 + s₀) * (C + 1) * (4 * A) * (Real.exp (v / 2) * Real.exp (-(15 / 8 * v))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left c1 h2
  have t2 : (1 + (s₀ + 2 * v)) * (Real.exp (-(15 / 2 * v)) * Real.exp v) ≤ (1 + s₀) * 4 * e₁ := by
    have h1 := mul_le_mul_of_nonneg_right hP2 (by positivity : 0 ≤ Real.exp (-(15 / 2 * v)) * Real.exp v)
    refine h1.trans ?_
    calc _ = (1 + s₀) * 4 * (Real.exp (v / 2) * (Real.exp (-(15 / 2 * v)) * Real.exp v)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left c2 (by positivity)
  have e3 : Real.exp (-(2 * v / 2)) = e₁ := by
    rw [he₁]
    congr 1
    ring
  rw [hEr, hv', e3]
  set X := (1 + s₀) * u with hX
  have t3 : 16 * (2 * (C + 1 + (s₀ + 2 * v)) * u * br) * Real.exp (-(2 * (rt / 2 ^ 8) * N₂)) +
      (2 * (1 + (s₀ + 2 * v)) * Real.exp (-(15 / 2 * v)) * u) * Real.exp v ≤
      X * e₁ * (128 * (C + 1) * A + 8) := by
    have h1 := mul_le_mul_of_nonneg_left t1 (by positivity : 0 ≤ 32 * u)
    have h2 := mul_le_mul_of_nonneg_left t2 (by positivity : 0 ≤ 2 * u)
    calc _ = 32 * u * ((C + 1 + (s₀ + 2 * v)) * br * Real.exp (-(2 * (rt / 2 ^ 8) * N₂))) +
          2 * u * ((1 + (s₀ + 2 * v)) * (Real.exp (-(15 / 2 * v)) * Real.exp v)) := by ring
      _ ≤ 32 * u * ((1 + s₀) * (C + 1) * (4 * A) * e₁) + 2 * u * ((1 + s₀) * 4 * e₁) := add_le_add h1 h2
      _ = _ := by rw [hX]; ring
  have hEW : 0 ≤ E * W := by positivity
  have t4 : (C + 2) * u * e₁ ≤ X * e₁ * (C + 2) := by
    have h1 : u ≤ X := by
      rw [hX]
      nlinarith
    have h2 : 0 ≤ (C + 2) * e₁ := by positivity
    calc (C + 2) * u * e₁ = u * ((C + 2) * e₁) := by ring
      _ ≤ X * ((C + 2) * e₁) := mul_le_mul_of_nonneg_right h1 h2
      _ = _ := by ring
  have t5 : (128 * (C + 1) * A + 8) + 2 * (C + 2) ≤ 2 ^ 8 * (C + 2) * A := by
    have a1 : (C + 1) * A ≤ (C + 2) * A := mul_le_mul_of_nonneg_right (by linarith) hA0
    have a3 : C + 2 ≤ (C + 2) * A := le_mul_of_one_le_right (by linarith) hA1
    have a2 : 1 ≤ (C + 2) * A := by linarith
    linarith
  have t6 : E * (2 ^ 8 * (C + 2) * A * W) ≤ Real.exp (-(2 * ch * x)) := by
    have h1 : 2 ^ 8 * (C + 2) * W ≤ A := by linarith
    have h2 : E * (A * A) = Real.exp (-(6 * ch * x)) := by
      rw [hE, hA, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have h3 : Real.exp (-(6 * ch * x)) ≤ Real.exp (-(2 * ch * x)) := by
      refine Real.exp_le_exp.mpr ?_
      linarith
    refine le_trans ?_ h3
    rw [← h2]
    refine mul_le_mul_of_nonneg_left ?_ hE0.le
    calc 2 ^ 8 * (C + 2) * A * W = A * (2 ^ 8 * (C + 2) * W) := by ring
      _ ≤ A * A := mul_le_mul_of_nonneg_left h1 hA0
  have e4 : (1 + s₀) * Real.exp (-(2 * ch * x) - rt * N / 2 ^ 8) * u = X * e₁ * Real.exp (-(2 * ch * x)) := by
    have : Real.exp (-(2 * ch * x) - rt * N / 2 ^ 8) = e₁ * Real.exp (-(2 * ch * x)) := by
      rw [he₁, ← Real.exp_add, hv]
      congr 1
      ring
    rw [this, hX]
    ring
  rw [e4]
  have hXe : 0 ≤ X * e₁ := by positivity
  calc _ ≤ X * e₁ * (128 * (C + 1) * A + 8) * (E * W) + 2 * (X * e₁ * (C + 2) * (E * W)) := by
        refine add_le_add (mul_le_mul_of_nonneg_right t3 hEW) (mul_le_mul_of_nonneg_left ?_ (by norm_num))
        exact mul_le_mul_of_nonneg_right t4 hEW
    _ = X * e₁ * (((128 * (C + 1) * A + 8) + 2 * (C + 2)) * (E * W)) := by ring
    _ ≤ X * e₁ * ((2 ^ 8 * (C + 2) * A) * (E * W)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right t5 hEW) hXe
    _ = X * e₁ * (E * (2 ^ 8 * (C + 2) * A * W)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left t6 hXe
end Estimates
end GasObservables
open GasObservables in
theorem gasObservableBoundsStatement_holds (hM : MeanOfProductStatement) (hCmp : oscillationComparisonStatement)
    (hTG : twoGroundsOscillationComparison) (hCol : GasColumnsSmall) (hGS : GasSumNearBlockBound)
    (hCF : CouplingFloorExists) : gasObservableBoundsStatement := by
  classical
  obtain ⟨r₁, p₁, h₁⟩ := hCol
  obtain ⟨r₂, p₂, h₂⟩ := hTG
  refine ⟨fun c => min (r₁ c) (r₂ c), fun c => lt_min (p₁ c) (p₂ c), fun T hT hle C => ?_⟩
  have c₁ := hle.trans (min_le_left _ _)
  have c₂ := hle.trans (min_le_right _ _)
  obtain ⟨y₁, hy₁⟩ := h₁ T hT c₁
  obtain ⟨y₂, hy₂⟩ := h₂ T hT c₂
  have hrt := hT.rt_pos
  have hκ₁ : 0 < T.κ₁ := lt_min (div_pos hT.κ_pos (by norm_num))
    (div_pos hT.cE_pos (by have := hT.σ_pos; positivity))
  have hch : 0 < T.gasRate := by
    have h1 : 0 < T.κ * T.threshold ^ 2 := mul_pos hT.κ_pos (pow_pos hT.σ_pos 2)
    have h2 : 0 < T.κ₁ * T.threshold ^ 2 := mul_pos hκ₁ (pow_pos hT.σ_pos 2)
    exact mul_pos (by norm_num) (lt_min hT.cE_pos (lt_min h1 h2))
  have hρ : 0 < T.rt / 2 ^ 8 := by positivity
  obtain ⟨y₈, hy₈⟩ := hCF T.gasRate T.side T.rt hch
  set W : ℝ := blockSumConstant (T.rt / 2 ^ 8) with hWdef
  have hW0 : 0 ≤ W := by
    have h1 : Real.exp (-(T.rt / 2 ^ 8 / 4)) < 1 := Real.exp_lt_one_iff.mpr (by
      have : 0 < T.rt / 2 ^ 8 / 4 := by positivity
      linarith)
    have h2 : 0 < 1 - Real.exp (-(T.rt / 2 ^ 8 / 4)) := by linarith
    rw [hWdef]
    unfold blockSumConstant
    positivity
  set Q : ℝ := 2 ^ 8 * (|C| + 2) * W + 1 with hQ
  have hQ0 : 0 < Q := by
    have : 0 ≤ 2 ^ 8 * (|C| + 2) * W := by positivity
    linarith
  refine ⟨max y₁ (max y₂ (max y₈ (max T.floorMin (Q / T.gasRate)))), fun y hy R hR hx' => ?_⟩
  obtain ⟨a₁, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₂, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₈, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₉, a₁₀⟩ := max_le_iff.mp hy
  have hLL : R.params.side = T.side := by
    rw [hR.params_eq]
    rfl
  have hrtR : R.params.rt = T.rt := by
    rw [hR.params_eq]
    rfl
  have hy1R : R.params.y₁ = y := by
    rw [hR.params_eq]
    rfl
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hT.fits y a₉
  have hx : y ≤ R.coupling := hR.le_coupling
  have hcf : R.params.RangeFloor T.gasRate := by
    intro x hxx
    rw [hy1R] at hxx
    have := hy₈ x (a₈.trans hxx)
    rw [hLL, hrtR]
    exact this
  have hrtR0 : 0 < R.params.rt := hrtR ▸ hrt
  have hκ : 0 < R.params.rt / 2 ^ 8 := by positivity
  have hQx : Q ≤ T.gasRate * R.coupling := by
    have h1 : Q / T.gasRate ≤ R.coupling := a₁₀.trans hx
    rw [div_le_iff₀ hch] at h1
    linarith
  have hZ : ∀ (p : ℕ) [NeZero p] (G : GasGround R p) (Y : TorusSite p) (H : Finset G.GasSpin),
      (∀ i ∈ H, Y ∈ i.1.core) →
      ∑ i ∈ H, G.spinActivity T.gasRate i ≤ Real.exp (-(8 * T.gasRate * R.coupling)) * W := by
    intro p _ G Y H hH
    have key := hGS R p G T.gasRate (R.params.rt / 2 ^ 8) 1 Y H (fun i => G.spinActivity T.gasRate i) hfit hch hcf
      (hy1R ▸ hx) hκ zero_le_one (fun i hi => by
        have h0 : setGap {Y} i.1.core = 0 := by
          unfold setGap
          exact Nat.le_zero.mp (Nat.sInf_le ⟨Y, by simp, Y, hH i hi, supDist_self Y⟩)
        have hc1 : (1 : ℝ) ≤ (i.1.core.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr (core_nonempty G i)
        have hc4 : (1 : ℝ) ≤ (i.1.core.card : ℝ) ^ 4 := one_le_pow₀ hc1
        have hed : (1 : ℝ) ≤ Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ)) := Real.one_le_exp (by positivity)
        have h2 := one_le_mul_of_one_le_of_one_le hc4 hed
        have hp := spinActivity_nonneg G i T.gasRate
        rw [h0]
        simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one, one_mul]
        calc G.spinActivity T.gasRate i ≤ G.spinActivity T.gasRate i * _ := le_mul_of_one_le_right hp h2
          _ = _ := by ring)
    rw [hrtR, one_mul] at key
    exact key
  have hSum : ∀ (p : ℕ) [NeZero p] (G : GasGround R p) (Y : TorusSite p),
      ∑ i, G.coreWeightFrom Y i * G.spinActivity T.gasRate i ≤ Real.exp (-(8 * T.gasRate * R.coupling)) * W := by
    intro p _ G Y
    have key := hGS R p G T.gasRate (R.params.rt / 2 ^ 8) 1 Y Finset.univ
      (fun i => G.coreWeightFrom Y i * G.spinActivity T.gasRate i) hfit hch hcf
      (hy1R ▸ hx) hκ zero_le_one (fun i _ => by
        have hc1 : (1 : ℝ) ≤ (i.1.core.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr (core_nonempty G i)
        have hc4 : (i.1.core.card : ℝ) ≤ (i.1.core.card : ℝ) ^ 4 := le_self_pow₀ hc1 (by norm_num)
        have hed : (1 : ℝ) ≤ Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ)) := Real.one_le_exp (by positivity)
        have hp := spinActivity_nonneg G i T.gasRate
        have hg0 : (0 : ℝ) ≤ setGap {Y} i.1.core := Nat.cast_nonneg _
        have he : Real.exp (-(R.params.rt / 2 ^ 6 * (setGap {Y} i.1.core : ℝ))) ≤
            Real.exp (-(R.params.rt / 2 ^ 8 * (setGap {Y} i.1.core : ℝ))) := by
          refine Real.exp_le_exp.mpr ?_
          nlinarith [mul_nonneg hrtR0.le hg0]
        unfold GasGround.coreWeightFrom coreWeight
        have h1 : (i.1.core.card : ℝ) * Real.exp (-(R.params.rt / 2 ^ 6 * (setGap {Y} i.1.core : ℝ))) ≤
            (i.1.core.card : ℝ) ^ 4 * Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ)) *
              Real.exp (-(R.params.rt / 2 ^ 8 * (setGap {Y} i.1.core : ℝ))) := by
          refine mul_le_mul ?_ he (Real.exp_pos _).le (by positivity)
          exact hc4.trans (le_mul_of_one_le_right (by positivity) hed)
        calc _ ≤ ((i.1.core.card : ℝ) ^ 4 * Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ)) *
              Real.exp (-(R.params.rt / 2 ^ 8 * (setGap {Y} i.1.core : ℝ)))) * G.spinActivity T.gasRate i :=
              mul_le_mul_of_nonneg_right h1 hp
          _ = _ := by ring)
    rw [hrtR, one_mul] at key
    exact key
  refine ⟨?_, ?_⟩
  · intro n _ G Y u s₀ D₀ p s hG ob hD
    obtain ⟨w₁, s₁⟩ := hy₁ y a₁ R hR hx' n G hG (fun i => i.1.Touches ∅)
    have B : GibbsData G T.gasRate := ⟨w₁, s₁⟩
    have hC := ob.one_le
    have hu := ob.amplitude_nonneg
    have hs₀ := ob.baseScore_nonneg
    have hQC : 2 ^ 8 * (C + 2) * W + 1 ≤ T.gasRate * R.coupling := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ C)] at hQ
      linarith
    have hbr : Real.exp (T.rt / 2 ^ 6 * D₀) ≤ Real.exp (T.gasRate * R.coupling) := Real.exp_le_exp.mpr hD
    obtain ⟨-, hcut⟩ := abs_integral_sub_truncate_le hM B ob (S := 0) le_rfl (hZ n G Y)
    have hosc := truncate_oscillationControlled (c₀ := 0) ob (L := s₀ + 0) (by linarith) hrtR0.le
    have key := hCmp.1 G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasureOff fun i => i.1.Touches ∅)
      G.weight (G.spinActivity T.gasRate) (G.influenceMatrix T.gasRate) (G.coreWeightFrom Y) _ _ w₁
      (hasDobrushinColumns G Y s₁) hosc
    simp only [sub_zero] at key
    have hlaw : G.pairConstraint.gibbsLaw (G.referenceMeasureOff fun i => i.1.Touches ∅) G.weight =
        G.gibbsLaw ∅ := rfl
    rw [hlaw] at key
    have hcab : truncate G p s (s₀ + 0) G.pairConstraint.vacant = p G.allVacant :=
      truncate_allVacant ob (by linarith)
    rw [hcab, hrtR] at key
    refine ⟨?_, ?_⟩
    · rw [expectation_eq B p]
      have tri := abs_sub_le (∫ σ, restrictAdmissible G p σ ∂G.gibbsLaw ∅)
        (∫ σ, truncate G p s (s₀ + 0) σ ∂G.gibbsLaw ∅) (p G.allVacant)
      have hfin := single_ground_arith (C := C) (u := u) (s₀ := s₀) (W := W) (ch := T.gasRate) (x := R.coupling)
        (br := Real.exp (T.rt / 2 ^ 6 * D₀)) hC hu hs₀ hW0 hQC hbr (Real.exp_pos _).le
      refine tri.trans (le_trans (add_le_add hcut (key.trans ?_)) hfin)
      have hK0 : 0 ≤ 2 * (C + 1 + (s₀ + 0)) * u * Real.exp (T.rt / 2 ^ 6 * D₀) := by positivity
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hSum n G Y) (by norm_num)) hK0
    · rw [expectation_eq B p]
      refine (abs_integral_le hM B ob (hZ n G Y)).trans (mul_le_mul_of_nonneg_right ?_ hu)
      have := activity_sum_arith (C := C) (W := W) (ch := T.gasRate) (x := R.coupling) hC hW0 hQC
      linarith
  · intro n n' _ _ G G' Y Y' N hG hG' hN hAg
    obtain ⟨g, hadm, hcmp⟩ := hy₂ y a₂ R hR hx' n n' G G' Y Y' N ∅ ∅ hG hG' hN hAg (fun h _ => by simp)
    refine ⟨g, fun u s₀ D₀ p s p' s' ob ob' hD hnear => ?_⟩
    obtain ⟨w₁, s₁⟩ := hy₁ y a₁ R hR hx' n G hG (fun i => i.1.Touches ∅)
    obtain ⟨w₂, s₂⟩ := hy₁ y a₁ R hR hx' n' G' hG' (fun i => i.1.Touches ∅)
    have B : GibbsData G T.gasRate := ⟨w₁, s₁⟩
    have B' : GibbsData G' T.gasRate := ⟨w₂, s₂⟩
    have : IsProbabilityMeasure (G.gibbsLaw ∅) := s₁.isProbabilityMeasure
    have : IsProbabilityMeasure (G'.gibbsLaw ∅) := s₂.isProbabilityMeasure
    have hC := ob.one_le
    have hu := ob.amplitude_nonneg
    have hs₀ := ob.baseScore_nonneg
    have hQC : 2 ^ 8 * (C + 2) * W + 1 ≤ T.gasRate * R.coupling := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ C)] at hQ
      linarith
    have hbr : Real.exp (T.rt / 2 ^ 6 * D₀) ≤ Real.exp (T.gasRate * R.coupling) := Real.exp_le_exp.mpr hD
    set v : ℝ := T.rt / 2 ^ 8 * N with hv
    have hv0 : 0 ≤ v := by positivity
    set L : ℝ := s₀ + 2 * v with hL
    have hL0 : 0 ≤ L := by positivity
    set E : ℝ := Real.exp (-(15 / 16 * T.rt * N / 2 ^ 5)) with hE
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    set p₀ := p G.allVacant with hp₀
    set p₀' := p' G'.allVacant with hp₀'
    obtain ⟨hi, hcut⟩ := abs_integral_sub_truncate_le hM B ob (S := 2 * v) (by positivity) (hZ n G Y)
    obtain ⟨hi', hcut'⟩ := abs_integral_sub_truncate_le hM B' ob' (S := 2 * v) (by positivity) (hZ n' G' Y')
    have hosc := truncate_oscillationControlled (c₀ := p₀) ob (L := L) hL0 hrtR0.le
    have hosc' := truncate_oscillationControlled (c₀ := p₀') ob' (L := L) hL0 hrtR0.le
    have hab₁ : truncate G p s L G.allVacant = p₀ := truncate_allVacant ob (by linarith)
    have hab₂ : truncate G' p' s' L G'.allVacant = p₀' := truncate_allVacant ob' (by linarith)
    have hfa : ∀ j, (fun _ => Sum.inl () : g.Config) j = Sum.inl () := fun _ => rfl
    have hfirst : g.extendFirst (fun _ => Sum.inl ()) = G.allVacant := by
      funext i
      unfold SharedInnerGas.extendFirst PairConstraint.embedConfig
      split_ifs with h
      · obtain ⟨j, rfl⟩ := h
        have : ∀ (j' : G.InnerSpin Y (N - R.frameReach - 1) ∅) (e : j'.1 = j.1),
            (e ▸ (Sum.inl () : G.SpinValue j'.1)) = (Sum.inl () : G.SpinValue j.1) := by
          intro j' e
          obtain rfl := Subtype.ext e
          rfl
        exact this _ _
      · rfl
    have hsecond : g.extendSecond (fun _ => Sum.inl ()) = G'.allVacant := by
      funext i
      unfold SharedInnerGas.extendSecond PairConstraint.embedConfig
      split_ifs with h
      · obtain ⟨j, rfl⟩ := h
        have : ∀ (j' : G.InnerSpin Y (N - R.frameReach - 1) ∅) (e : (g.spinEquiv j').1 = (g.spinEquiv j).1),
            (e ▸ g.valueEquiv j' (Sum.inl ()) : G'.SpinValue (g.spinEquiv j).1) =
              (Sum.inl () : G'.SpinValue (g.spinEquiv j).1) := by
          intro j' e
          obtain rfl := g.spinEquiv.injective (Subtype.ext e)
          exact g.map_vacant j'
        exact this _ _
      · rfl
    have hs_abs : s G.allVacant ≤ s₀ := by
      obtain ⟨H, e, he⟩ := ob.controlled
      rcases he.score_le _ (allVacant_admissible G) with h | ⟨i, -, h, -⟩
      · exact h
      · exact absurd rfl h
    have habs := hnear (fun _ => Sum.inl ()) (by rw [hfirst]; exact allVacant_admissible G)
      (by rw [hsecond]; exact allVacant_admissible G')
    rw [hfirst, hsecond] at habs
    have hp₀d : |p₀ - p₀'| ≤ (1 + L) * E * u := by
      refine habs.2.trans ?_
      have : (1 + s G.allVacant) * E ≤ (1 + L) * E := mul_le_mul_of_nonneg_right (by linarith) hE0
      exact mul_le_mul_of_nonneg_right this hu
    have hnearF : ∀ τ : g.Config, G.pairConstraint.IsAdmissible (g.extendFirst τ) →
        |(truncate G p s L (g.extendFirst τ) - p₀) - (truncate G' p' s' L (g.extendSecond τ) - p₀')| ≤
          2 * (1 + L) * E * u := by
      intro τ hτ
      have hτ' := hadm τ hτ
      obtain ⟨e1, e2⟩ := hnear τ hτ hτ'
      unfold truncate
      rw [restrictAdmissible_of_admissible G _ hτ, restrictAdmissible_of_admissible G _ hτ,
        restrictAdmissible_of_admissible G' _ hτ', restrictAdmissible_of_admissible G' _ hτ', ← e1]
      by_cases hsl : s (g.extendFirst τ) ≤ L
      · rw [if_pos hsl, if_pos hsl]
        have h1 : |p (g.extendFirst τ) - p' (g.extendSecond τ)| ≤ (1 + L) * E * u := by
          refine e2.trans ?_
          have : (1 + s (g.extendFirst τ)) * E ≤ (1 + L) * E := mul_le_mul_of_nonneg_right (by linarith) hE0
          exact mul_le_mul_of_nonneg_right this hu
        have e0 : (p (g.extendFirst τ) - p₀) - (p' (g.extendSecond τ) - p₀') =
            (p (g.extendFirst τ) - p' (g.extendSecond τ)) - (p₀ - p₀') := by
          ring
        rw [e0]
        refine (abs_sub _ _).trans ?_
        linarith
      · rw [if_neg hsl, if_neg hsl]
        have e0 : ((0 : ℝ) - p₀) - (0 - p₀') = -(p₀ - p₀') := by ring
        rw [e0, abs_neg]
        have : 0 ≤ (1 + L) * E * u := by positivity
        linarith
    have hcomp := hcmp _ _ _ (2 * (1 + L) * E * u) (by positivity) hosc hosc' hnearF (by
      rw [hab₁, hab₂, sub_self, sub_self])
    have hm₁ : Integrable (truncate G p s L) (G.gibbsLaw ∅) :=
      (integrable_const ((C + L) * u)).mono' (measurable_truncate ob L).aestronglyMeasurable
        (ae_of_all _ fun σ => abs_truncate_le ob hL0 σ)
    have hm₂ : Integrable (truncate G' p' s' L) (G'.gibbsLaw ∅) :=
      (integrable_const ((C + L) * u)).mono' (measurable_truncate ob' L).aestronglyMeasurable
        (ae_of_all _ fun σ => abs_truncate_le ob' hL0 σ)
    have ef₁ : G.expectation ∅ (fun σ => truncate G p s L σ - p₀) = ∫ σ, truncate G p s L σ ∂G.gibbsLaw ∅ - p₀ := by
      unfold GasGround.expectation
      rw [integral_sub hm₁ (integrable_const _), integral_const, probReal_univ, one_smul]
    have ef₂ : G'.expectation ∅ (fun σ => truncate G' p' s' L σ - p₀') =
        ∫ σ, truncate G' p' s' L σ ∂G'.gibbsLaw ∅ - p₀' := by
      unfold GasGround.expectation
      rw [integral_sub hm₂ (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [ef₁, ef₂] at hcomp
    rw [expectation_eq B p, expectation_eq B' p']
    set a₁' := ∫ σ, restrictAdmissible G p σ ∂G.gibbsLaw ∅
    set a₂' := ∫ σ, restrictAdmissible G' p' σ ∂G'.gibbsLaw ∅
    set b₁' := ∫ σ, truncate G p s L σ ∂G.gibbsLaw ∅
    set b₂' := ∫ σ, truncate G' p' s' L σ ∂G'.gibbsLaw ∅
    have tri : |(a₁' - p₀) - (a₂' - p₀')| ≤ |(b₁' - p₀) - (b₂' - p₀')| + |a₁' - b₁'| + |a₂' - b₂'| := by
      have e0 : (a₁' - p₀) - (a₂' - p₀') = ((b₁' - p₀) - (b₂' - p₀')) + (a₁' - b₁') - (a₂' - b₂') := by ring
      rw [e0]
      exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have hm₀ : 15 / 16 * (N : ℝ) ≤ ((N - R.frameReach : ℕ) : ℝ) := by
      have h1 : R.frameReach ≤ N := by omega
      rw [Nat.cast_sub h1]
      have h2 : (16 : ℝ) * R.frameReach ≤ N := by exact_mod_cast hN
      linarith
    have hfin := two_grounds_arith (C := C) (u := u) (s₀ := s₀) (W := W) (ch := T.gasRate) (x := R.coupling)
      (rt := T.rt) (br := Real.exp (T.rt / 2 ^ 6 * D₀)) (v := v) (N := N) (N₂ := ((N - R.frameReach : ℕ) : ℝ))
      hC hu hs₀ hW0 hv hv0 hrt hm₀ hQC hbr (Real.exp_pos _).le
    refine tri.trans (le_trans ?_ hfin)
    have hK : 2 * (C + 1 + L) * u * Real.exp (R.params.rt / 2 ^ 6 * D₀) =
        2 * (C + 1 + (s₀ + 2 * v)) * u * Real.exp (T.rt / 2 ^ 6 * D₀) := by rw [hrtR, hL]
    rw [hK] at hcomp
    have e4 : ∀ q : ℝ, q = Real.exp (-(8 * T.gasRate * R.coupling)) * W → True := fun _ _ => trivial
    calc _ ≤ (16 * (2 * (C + 1 + (s₀ + 2 * v)) * u * Real.exp (T.rt / 2 ^ 6 * D₀)) *
            Real.exp (-(2 * (T.rt / 2 ^ 8) * ((N - R.frameReach : ℕ) : ℝ))) +
          (2 * (1 + L) * E * u) * Real.exp (T.rt / 2 ^ 8 * (N : ℝ))) *
            (Real.exp (-(8 * T.gasRate * R.coupling)) * W) +
          (C + 2) * u * Real.exp (-(2 * v / 2)) * (Real.exp (-(8 * T.gasRate * R.coupling)) * W) +
          (C + 2) * u * Real.exp (-(2 * v / 2)) * (Real.exp (-(8 * T.gasRate * R.coupling)) * W) :=
          add_le_add (add_le_add hcomp hcut) hcut'
      _ = _ := by rw [hL]; ring
end ResponseInTheExpansion
end YangMills.Construction
end
