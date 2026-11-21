import YangMills.Construction.ResponseInTheExpansion.FarSpinsMoveAVariableAtOneLevel
import YangMills.Construction.ResponseInTheExpansion.FarVariablesSplitOverTheGasProof
import YangMills.Construction.ResponseInTheExpansion.TiltOfALawOfSpinsProof
import YangMills.Construction.ResponseInTheExpansion.TwoTiltsOfFarObservables
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction
open Dobrushin
namespace ResponseInTheExpansion
open ClusterExpansionOfAStep BlockAverages FreeEnergies StepGas StepSettings RenormalizationStepParameters StepFloors TorusLumps TorusFields CoreColumns
namespace SeparatedWeightTilts
set_option linter.unusedSectionVars false
section Numbers
theorem abs_div_sub_div_le_of_relClose {b₁ b₂ a₁ a₂ e : ℝ} (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (he : 0 ≤ e) (h₁ : |a₁ - b₁| ≤ e * b₁) (h₂ : |a₂ - b₂| ≤ e * b₂) :
    |b₁ / (1 + b₁ + b₂) - a₁ / (1 + a₁ + a₂)| ≤ 2 * e * (b₁ + b₂) := by
  have hd₁ : 0 < 1 + b₁ + b₂ := by linarith
  have hd₂ : 0 < 1 + a₁ + a₂ := by linarith
  rw [div_sub_div _ _ hd₁.ne' hd₂.ne', abs_div, abs_of_pos (mul_pos hd₁ hd₂), div_le_iff₀ (mul_pos hd₁ hd₂)]
  set x := a₁ - b₁ with hx
  set w := a₂ - b₂ with hw
  have e₁ : b₁ * (1 + a₁ + a₂) - (1 + b₁ + b₂) * a₁ = -x + b₁ * w - x * b₂ := by
    rw [hx, hw]
    ring
  rw [e₁]
  have k₁ : |-x + b₁ * w - x * b₂| ≤ e * b₁ + b₁ * (e * b₂) + e * b₁ * b₂ := by
    calc |-x + b₁ * w - x * b₂| ≤ |-x + b₁ * w| + |x * b₂| := abs_sub _ _
      _ ≤ |-x| + |b₁ * w| + |x * b₂| := by gcongr; exact abs_add_le _ _
      _ = |x| + b₁ * |w| + |x| * b₂ := by
          rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hb₁, abs_of_nonneg hb₂]
      _ ≤ e * b₁ + b₁ * (e * b₂) + e * b₁ * b₂ := by gcongr
  refine k₁.trans ?_
  have hE : 0 ≤ e * b₁ := by positivity
  have hE₂ : 0 ≤ e * b₂ := by positivity
  have hS : 0 ≤ 2 * e * (b₁ + b₂) := by positivity
  have hD : 1 + b₁ + b₂ ≤ (1 + b₁ + b₂) * (1 + a₁ + a₂) := by nlinarith
  have k₂ : 2 * e * (b₁ + b₂) * (1 + b₁ + b₂) ≤ 2 * e * (b₁ + b₂) * ((1 + b₁ + b₂) * (1 + a₁ + a₂)) :=
    mul_le_mul_of_nonneg_left hD hS
  have k₃ : e * b₁ + b₁ * (e * b₂) + e * b₁ * b₂ ≤ 2 * e * (b₁ + b₂) * (1 + b₁ + b₂) := by
    have p₁ : 0 ≤ e * b₁ * b₁ := by positivity
    have p₂ : 0 ≤ e * b₁ * b₂ := by positivity
    have p₃ : 0 ≤ e * b₂ * b₂ := by positivity
    nlinarith
  linarith
theorem abs_indicator_div_sub_le_of_relClose {t b₁ b₂ a₁ a₂ e : ℝ} (ht : t = 0 ∨ t = 1) (hb₁ : 0 ≤ b₁)
    (hb₂ : 0 ≤ b₂) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (he : 0 ≤ e) (h₁ : |a₁ - b₁| ≤ e * b₁) (h₂ : |a₂ - b₂| ≤ e * b₂) :
    |(t + b₁) / (1 + b₁ + b₂) - (t + a₁) / (1 + a₁ + a₂)| ≤ 2 * e * (b₁ + b₂) := by
  rcases ht with rfl | rfl
  · simpa using abs_div_sub_div_le_of_relClose hb₁ hb₂ ha₁ ha₂ he h₁ h₂
  · have k := abs_div_sub_div_le_of_relClose hb₂ hb₁ ha₂ ha₁ he h₂ h₁
    have e₁ : (1 + b₁) / (1 + b₁ + b₂) = 1 - b₂ / (1 + b₂ + b₁) := by
      have : 1 + b₂ + b₁ = 1 + b₁ + b₂ := by ring
      rw [this]
      field_simp
      ring
    have e₂ : (1 + a₁) / (1 + a₁ + a₂) = 1 - a₂ / (1 + a₂ + a₁) := by
      have : 1 + a₂ + a₁ = 1 + a₁ + a₂ := by ring
      rw [this]
      field_simp
      ring
    rw [e₁, e₂]
    have e₃ : 1 - b₂ / (1 + b₂ + b₁) - (1 - a₂ / (1 + a₂ + a₁)) = -(b₂ / (1 + b₂ + b₁) - a₂ / (1 + a₂ + a₁)) := by ring
    rw [e₃, abs_neg]
    calc _ ≤ 2 * e * (b₂ + b₁) := k
      _ = _ := by ring
theorem abs_div_sub_div_le_of_sum_le {b₁ b₂ a₁ a₂ z : ℝ} (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hb : b₁ + b₂ ≤ z) (ha : a₁ + a₂ ≤ 3 * z) :
    |b₁ / (1 + b₁ + b₂) - a₁ / (1 + a₁ + a₂)| ≤ 3 * z := by
  have p₁ : 0 ≤ b₁ / (1 + b₁ + b₂) := by positivity
  have p₂ : 0 ≤ a₁ / (1 + a₁ + a₂) := by positivity
  have q₁ : b₁ / (1 + b₁ + b₂) ≤ b₁ := div_le_self hb₁ (by linarith)
  have q₂ : a₁ / (1 + a₁ + a₂) ≤ a₁ := div_le_self ha₁ (by linarith)
  rw [abs_le]
  constructor <;> linarith
theorem abs_indicator_div_sub_le_of_sum_le {t b₁ b₂ a₁ a₂ z : ℝ} (ht : t = 0 ∨ t = 1) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hb : b₁ + b₂ ≤ z) (ha : a₁ + a₂ ≤ 3 * z) :
    |(t + b₁) / (1 + b₁ + b₂) - (t + a₁) / (1 + a₁ + a₂)| ≤ 3 * z := by
  rcases ht with rfl | rfl
  · simpa using abs_div_sub_div_le_of_sum_le hb₁ hb₂ ha₁ ha₂ hb ha
  · have k := abs_div_sub_div_le_of_sum_le hb₂ hb₁ ha₂ ha₁ (by linarith) (by linarith)
    have e₁ : (1 + b₁) / (1 + b₁ + b₂) = 1 - b₂ / (1 + b₂ + b₁) := by
      have : 1 + b₂ + b₁ = 1 + b₁ + b₂ := by ring
      rw [this]
      field_simp
      ring
    have e₂ : (1 + a₁) / (1 + a₁ + a₂) = 1 - a₂ / (1 + a₂ + a₁) := by
      have : 1 + a₂ + a₁ = 1 + a₁ + a₂ := by ring
      rw [this]
      field_simp
      ring
    rw [e₁, e₂]
    have e₃ : 1 - b₂ / (1 + b₂ + b₁) - (1 - a₂ / (1 + a₂ + a₁)) = -(b₂ / (1 + b₂ + b₁) - a₂ / (1 + a₂ + a₁)) := by ring
    rw [e₃, abs_neg]
    exact k
end Numbers
section Laws
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)] {C : PairConstraint S}
  {m : ∀ i, Measure (S i)} [∀ i, SigmaFinite (m i)] {G Y : (∀ i, S i) → ℝ} {z z' : I → ℝ}
theorem isAdmissible_update_vacant {σ : ∀ i, S i} (hσ : C.IsAdmissible σ) (i : I) :
    C.IsAdmissible (Function.update σ i (C.vacant i)) := by apply _root_.YangMills.Construction.Dobrushin.VacantSpin.isAdmissible_update_vacant <;> assumption
def vacantRatio (C : PairConstraint S) (m : ∀ i, Measure (S i)) (G : (∀ i, S i) → ℝ) (i : I) (σ : ∀ i, S i)
    (B : Set (S i)) : ℝ :=
  (∫⁻ s in B \ {C.vacant i}, C.weightDensity G (Function.update σ i s) ∂m i).toReal /
    (C.weightDensity G (Function.update σ i (C.vacant i))).toReal
theorem weightDensity_update_vacant_pos (h : C.IsActivityBounded m G z) {σ : ∀ i, S i} (hσ : C.IsAdmissible σ) (i : I) :
    0 < C.weightDensity G (Function.update σ i (C.vacant i)) := by
  exact _root_.YangMills.Construction.LinearResponse.SingleSiteTilt.weightDensity_update_vacant_pos
    (m := m) h hσ i
theorem weightDensity_update_vacant_ne_top {σ : ∀ i, S i} (i : I) :
    C.weightDensity G (Function.update σ i (C.vacant i)) ≠ ⊤ := by apply _root_.YangMills.Construction.LinearResponse.SingleSiteTilt.weightDensity_update_vacant_ne_top <;> assumption
theorem setLIntegral_diff_vacant_le (h : C.IsActivityBounded m G z) {σ : ∀ i, S i} (hσ : C.IsAdmissible σ) (i : I)
    (B : Set (S i)) :
    ∫⁻ s in B \ {C.vacant i}, C.weightDensity G (Function.update σ i s) ∂m i ≤
      ENNReal.ofReal (z i) * C.weightDensity G (Function.update σ i (C.vacant i)) := by apply _root_.YangMills.Construction.LinearResponse.SingleSiteTilt.setLIntegral_diff_vacant_le <;> assumption
theorem setLIntegral_diff_vacant_ne_top (h : C.IsActivityBounded m G z) {σ : ∀ i, S i} (hσ : C.IsAdmissible σ) (i : I)
    (B : Set (S i)) :
    ∫⁻ s in B \ {C.vacant i}, C.weightDensity G (Function.update σ i s) ∂m i ≠ ⊤ := by apply _root_.YangMills.Construction.LinearResponse.SingleSiteTilt.setLIntegral_diff_vacant_ne_top <;> assumption
theorem setLIntegral_eq_vacant_add (h : C.IsActivityBounded m G z) (σ : ∀ i, S i) (i : I) {B : Set (S i)}
    (hB : MeasurableSet B) :
    ∫⁻ s in B, C.weightDensity G (Function.update σ i s) ∂m i =
      (open Classical in if C.vacant i ∈ B then C.weightDensity G (Function.update σ i (C.vacant i)) else 0) +
        ∫⁻ s in B \ {C.vacant i}, C.weightDensity G (Function.update σ i s) ∂m i := by apply _root_.YangMills.Construction.LinearResponse.SingleSiteTilt.setLIntegral_eq_vacant_add_diff <;> assumption
theorem conditionalMass_eq (h : C.IsActivityBounded m G z) (σ : ∀ i, S i) (i : I) :
    C.conditionalMass m G i σ = C.weightDensity G (Function.update σ i (C.vacant i)) +
      ∫⁻ s in Set.univ \ {C.vacant i}, C.weightDensity G (Function.update σ i s) ∂m i := by apply _root_.YangMills.Construction.LinearResponse.SingleSiteTilt.conditionalMass_eq <;> assumption
theorem singleSiteKernel_real_eq (h : C.IsActivityBounded m G z) {σ : ∀ i, S i} (hσ : C.IsAdmissible σ) (i : I)
    {B : Set (S i)} (hB : MeasurableSet B) :
    (C.singleSiteKernel m h.measurable_weightDensity i σ).real B =
      ((open Classical in if C.vacant i ∈ B then 1 else 0) + vacantRatio C m G i σ B) /
        (1 + vacantRatio C m G i σ B + vacantRatio C m G i σ Bᶜ) := by apply _root_.YangMills.Construction.LinearResponse.SingleSiteTilt.singleSiteKernel_real_eq <;> assumption
theorem vacantRatio_nonneg (i : I) (σ : ∀ i, S i) (B : Set (S i)) : 0 ≤ vacantRatio C m G i σ B := by apply _root_.YangMills.Construction.LinearResponse.SingleSiteTilt.vacancyRatio_nonneg <;> assumption
theorem vacantRatio_add_compl_le (h : C.IsActivityBounded m G z) {σ : ∀ i, S i} (hσ : C.IsAdmissible σ) (i : I)
    {B : Set (S i)} (hB : MeasurableSet B) : vacantRatio C m G i σ B + vacantRatio C m G i σ Bᶜ ≤ z i := by apply _root_.YangMills.Construction.LinearResponse.SingleSiteTilt.vacancyRatio_add_compl_le <;> assumption
theorem abs_vacantRatio_mul_sub_le (h : C.IsActivityBounded m G z) (hY : ∀ σ, C.IsAdmissible σ → 0 < Y σ)
    {σ : ∀ i, S i} (hσ : C.IsAdmissible σ) (i : I) {e : ℝ} (he0 : 0 ≤ e)
    (hnear : ∀ s : S i, C.IsAdmissible (Function.update σ i s) → s ≠ C.vacant i →
      |Y (Function.update σ i s) - Y (Function.update σ i (C.vacant i))| ≤
        e * Y (Function.update σ i (C.vacant i))) {B : Set (S i)} (hB : MeasurableSet B) :
    |vacantRatio C m (fun σ => G σ * Y σ) i σ B - vacantRatio C m G i σ B| ≤ e * vacantRatio C m G i σ B := by
  classical
  set y₀ := Y (Function.update σ i (C.vacant i)) with hy₀
  have hadm := isAdmissible_update_vacant hσ i
  have hy0 : 0 < y₀ := hY _ hadm
  have hset := h.measurableSet_vacant i
  have hBd : MeasurableSet (B \ {C.vacant i}) := hB.diff hset
  set g₀ := C.weightDensity G (Function.update σ i (C.vacant i)) with hg₀
  have hg0 : 0 < g₀ := weightDensity_update_vacant_pos h hσ i
  have hgt : g₀ ≠ ⊤ := weightDensity_update_vacant_ne_top i
  have hg0r : 0 < g₀.toReal := ENNReal.toReal_pos hg0.ne' hgt
  have hG0 : 0 < G (Function.update σ i (C.vacant i)) := h.pos_of_admissible _ hadm
  have hg'₀ : (C.weightDensity (fun σ => G σ * Y σ) (Function.update σ i (C.vacant i))).toReal = g₀.toReal * y₀ := by
    rw [hg₀]
    unfold PairConstraint.weightDensity
    rw [if_pos hadm, if_pos hadm, ENNReal.toReal_ofReal (mul_nonneg hG0.le hy0.le), ENNReal.toReal_ofReal hG0.le]
  set c := max (1 - e) 0 with hc
  have hc0 : 0 ≤ c := le_max_right _ _
  have up : ∀ s ∈ B \ {C.vacant i}, C.weightDensity (fun σ => G σ * Y σ) (Function.update σ i s) ≤
      ENNReal.ofReal ((1 + e) * y₀) * C.weightDensity G (Function.update σ i s) := by
    intro s hs
    unfold PairConstraint.weightDensity
    by_cases ha : C.IsAdmissible (Function.update σ i s)
    · rw [if_pos ha, if_pos ha, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have h1 := hnear s ha hs.2
      have h2 := (abs_le.mp h1).2
      have h3 := h.pos_of_admissible _ ha
      nlinarith
    · rw [if_neg ha, if_neg ha]
      simp
  have lo : ∀ s ∈ B \ {C.vacant i}, ENNReal.ofReal (c * y₀) * C.weightDensity G (Function.update σ i s) ≤
      C.weightDensity (fun σ => G σ * Y σ) (Function.update σ i s) := by
    intro s hs
    unfold PairConstraint.weightDensity
    by_cases ha : C.IsAdmissible (Function.update σ i s)
    · have h0 : 0 ≤ c * y₀ := mul_nonneg hc0 hy0.le
      rw [if_pos ha, if_pos ha, ← ENNReal.ofReal_mul h0]
      apply ENNReal.ofReal_le_ofReal
      have h1 := hnear s ha hs.2
      have h2 := (abs_le.mp h1).1
      have h3 := h.pos_of_admissible _ ha
      have h4 : c * y₀ ≤ Y (Function.update σ i s) := by
        rcases le_total (1 - e) 0 with hh | hh
        · rw [hc, max_eq_right hh, zero_mul]
          exact (hY _ ha).le
        · rw [hc, max_eq_left hh]
          linarith
      nlinarith
    · rw [if_neg ha, if_neg ha]
      simp
  have i₁ := setLIntegral_mono' (μ := m i) hBd up
  have i₂ := setLIntegral_mono' (μ := m i) hBd lo
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at i₁ i₂
  set u := ∫⁻ s in B \ {C.vacant i}, C.weightDensity G (Function.update σ i s) ∂m i with hu
  set u' := ∫⁻ s in B \ {C.vacant i}, C.weightDensity (fun σ => G σ * Y σ) (Function.update σ i s) ∂m i with hu'
  have hut : u ≠ ⊤ := setLIntegral_diff_vacant_ne_top h hσ i B
  have hu't : u' ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hut) i₁
  have r₁ := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hut) i₁
  have r₂ := ENNReal.toReal_mono hu't i₂
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at r₁
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hc0 hy0.le)] at r₂
  have ex : vacantRatio C m G i σ B = u.toReal / g₀.toReal := rfl
  have ex' : vacantRatio C m (fun σ => G σ * Y σ) i σ B = u'.toReal / (g₀.toReal * y₀) := by
    unfold vacantRatio
    rw [hg'₀]
  rw [ex, ex']
  have hden : 0 < g₀.toReal * y₀ := by positivity
  have hb0 : 0 ≤ u.toReal / g₀.toReal := by positivity
  have k₁ : u'.toReal / (g₀.toReal * y₀) ≤ (1 + e) * (u.toReal / g₀.toReal) := by
    rw [div_le_iff₀ hden]
    calc u'.toReal ≤ (1 + e) * y₀ * u.toReal := r₁
      _ = _ := by field_simp
  have k₂ : c * (u.toReal / g₀.toReal) ≤ u'.toReal / (g₀.toReal * y₀) := by
    rw [le_div_iff₀ hden]
    calc c * (u.toReal / g₀.toReal) * (g₀.toReal * y₀) = c * y₀ * u.toReal := by
          field_simp
      _ ≤ _ := r₂
  have k₃ : (1 - e) * (u.toReal / g₀.toReal) ≤ c * (u.toReal / g₀.toReal) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hb0
  rw [abs_le]
  constructor <;> nlinarith
theorem abs_singleSiteKernel_sub_le (h : C.IsActivityBounded m G z)
    (h' : C.IsActivityBounded m (fun σ => G σ * Y σ) fun i => 3 * z i)
    {σ : ∀ i, S i} (hσ : C.IsAdmissible σ) (i : I) {B : Set (S i)} (hB : MeasurableSet B) :
    |(C.singleSiteKernel m h.measurable_weightDensity i σ).real B -
        (C.singleSiteKernel m h'.measurable_weightDensity i σ).real B| ≤ 3 * z i := by
  classical
  rw [singleSiteKernel_real_eq h hσ i hB, singleSiteKernel_real_eq h' hσ i hB]
  have ht : ((if C.vacant i ∈ B then 1 else 0) : ℝ) = 0 ∨ ((if C.vacant i ∈ B then 1 else 0) : ℝ) = 1 := by
    split_ifs <;> simp
  exact abs_indicator_div_sub_le_of_sum_le ht (vacantRatio_nonneg i σ B) (vacantRatio_nonneg i σ Bᶜ)
    (vacantRatio_nonneg i σ B) (vacantRatio_nonneg i σ Bᶜ)
    (vacantRatio_add_compl_le h hσ i hB) (vacantRatio_add_compl_le h' hσ i hB)
theorem abs_singleSiteKernel_sub_le_of_near (h : C.IsActivityBounded m G z)
    (h' : C.IsActivityBounded m (fun σ => G σ * Y σ) fun i => 3 * z i)
    (hY : ∀ σ, C.IsAdmissible σ → 0 < Y σ) {σ : ∀ i, S i} (hσ : C.IsAdmissible σ) (i : I) {e : ℝ} (he0 : 0 ≤ e)
    (hnear : ∀ s : S i, C.IsAdmissible (Function.update σ i s) → s ≠ C.vacant i →
      |Y (Function.update σ i s) - Y (Function.update σ i (C.vacant i))| ≤
        e * Y (Function.update σ i (C.vacant i))) {B : Set (S i)} (hB : MeasurableSet B) :
    |(C.singleSiteKernel m h.measurable_weightDensity i σ).real B -
        (C.singleSiteKernel m h'.measurable_weightDensity i σ).real B| ≤
      2 * e * z i := by
  classical
  rw [singleSiteKernel_real_eq h hσ i hB, singleSiteKernel_real_eq h' hσ i hB]
  have ht : ((if C.vacant i ∈ B then 1 else 0) : ℝ) = 0 ∨ ((if C.vacant i ∈ B then 1 else 0) : ℝ) = 1 := by
    split_ifs <;> simp
  have k := abs_indicator_div_sub_le_of_relClose ht (vacantRatio_nonneg i σ B) (vacantRatio_nonneg i σ Bᶜ)
    (vacantRatio_nonneg (G := fun σ => G σ * Y σ) i σ B)
    (vacantRatio_nonneg (G := fun σ => G σ * Y σ) i σ Bᶜ) he0 (abs_vacantRatio_mul_sub_le h hY hσ i he0 hnear hB)
    (abs_vacantRatio_mul_sub_le h hY hσ i he0 hnear hB.compl)
  refine k.trans ?_
  exact mul_le_mul_of_nonneg_left (vacantRatio_add_compl_le h hσ i hB) (by positivity)
end Laws
section Preliminaries
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
theorem one_le_spinScore {A : WeightedResponses.ResponseSetup R} (hs : ∀ w, 0 ≤ A.score w)
    (S : Finset (TorusSite (n * R.params.side))) (σ : G.Config) :
    1 ≤ spinScore A G S σ := by apply _root_.YangMills.Construction.ResponseInTheExpansion.Decorrelation.one_le_spinScore <;> assumption
theorem measurable_spinScore {A : WeightedResponses.ResponseSetup R} (hb : Measurable A.score)
    (S : Finset (TorusSite (n * R.params.side))) :
    Measurable (spinScore A G S) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.Decorrelation.measurable_spinScore <;> assumption
theorem spinScore_update_le {A : WeightedResponses.ResponseSetup R} (hs : ∀ w, 0 ≤ A.score w)
    (S : Finset (TorusSite (n * R.params.side))) (σ : G.Config)
    (i : G.GasSpin) (v : G.SpinValue i) :
    spinScore A G S (Function.update σ i v) ≤
      spinScore A G S (Function.update σ i (G.pairConstraint.vacant i)) *
        Real.exp (∑ y ∈ S, spinLabelScore A.score G i y v) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.Decorrelation.spinScore_update_le <;> assumption
theorem spinScore_update_eq {B : WeightedResponses.ResponseSetup R} {S : Finset (TorusSite (n * R.params.side))}
    {σ : G.Config} {i : G.GasSpin} (v : G.SpinValue i)
    (hS : ∀ y ∈ S, y ∉ i.1.2) :
    spinScore B G S (Function.update σ i v) = spinScore B G S (Function.update σ i (G.pairConstraint.vacant i)) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.Decorrelation.spinScore_update_eq <;> assumption
theorem setGap_le_supDist {X X' : Finset (TorusSite n)} {y y' : TorusSite n} (hy : y ∈ X) (hy' : y' ∈ X') :
    setGap X X' ≤ supDist y y' :=
  Nat.sInf_le ⟨y, hy, y', hy', rfl⟩
theorem setGap_le_setGap_singleton {Q : Finset (TorusSite n)} {Y : TorusSite n} (hY : Y ∈ Q) (i : G.GasSpin) :
    setGap Q i.1.core ≤ setGap {Y} i.1.core := by apply _root_.YangMills.Construction.TiltedGasResponse.setGap_le_setGap_singleton <;> assumption
theorem isAdmissible_update_vacant_of_update {σ : G.Config} {i : G.GasSpin} {v : G.SpinValue i}
    (h : G.pairConstraint.IsAdmissible (Function.update σ i v)) :
    G.pairConstraint.IsAdmissible (Function.update σ i (G.pairConstraint.vacant i)) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasColumns.isAdmissible_update_vacant <;> assumption
theorem isActivityBounded_mul_tilt {A₀ : WeightedResponses.ResponseSetup R} {Q : Finset (TorusSite n)}
    {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ}
    {Yt : G.Config → ℝ} (hs : ∀ w, 0 ≤ A₀.score w)
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A₀ i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    (ht : IsGasTilt G A₀.score Q B e Yt) :
    G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) (fun σ => G.weight σ * Yt σ)
      fun i => 3 * G.spinActivity c i := by apply _root_.YangMills.Construction.ResponseInTheExpansion.Decorrelation.isActivityBounded_tilt <;> assumption
end Preliminaries
section Tilts
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n} {ι : Type}
theorem abs_prod_sub_prod_le {a b P : ι → ℝ} {e : ℝ} (he : 0 ≤ e) (J : Finset ι) (hP : ∀ i ∈ J, 0 ≤ P i)
    (ha : ∀ i ∈ J, |a i| ≤ P i) (hb : ∀ i ∈ J, |b i| ≤ P i) (hab : ∀ i ∈ J, |a i - b i| ≤ e * P i) :
    |∏ i ∈ J, a i - ∏ i ∈ J, b i| ≤ J.card * e * ∏ i ∈ J, P i := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hs : ∀ j, j ∈ s → j ∈ insert i s := fun j hj => Finset.mem_insert_of_mem hj
    have h1 := ih (fun j hj => hP j (hs j hj)) (fun j hj => ha j (hs j hj)) (fun j hj => hb j (hs j hj))
      (fun j hj => hab j (hs j hj))
    have hi' := Finset.mem_insert_self i s
    have hA : |∏ j ∈ s, a j| ≤ ∏ j ∈ s, P j := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun j hj => ha j (hs j hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have e1 : a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j =
        (a i - b i) * ∏ j ∈ s, a j + b i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) := by ring
    rw [e1]
    calc _ ≤ |a i - b i| * |∏ j ∈ s, a j| + |b i| * |∏ j ∈ s, a j - ∏ j ∈ s, b j| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ (e * P i) * (∏ j ∈ s, P j) + P i * (s.card * e * ∏ j ∈ s, P j) :=
          add_le_add (mul_le_mul (hab i hi') hA (abs_nonneg _) (mul_nonneg he (hP i hi')))
            (mul_le_mul (hb i hi') h1 (abs_nonneg _) (hP i hi'))
      _ = _ := by push_cast; ring
variable (A : WeightedResponses.ResponseSetup R)
  (f : ι → WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide R.params.side (R.depth + 1) n)) (G)
def factorBound (j : ι) (σ : G.Config) : ℝ :=
  4 * lowerSizeConst A (f j) * spinScore A G (lowerSites (f j)) σ
def admissibleMean (j : ι) (σ : G.Config) : ℝ :=
  open Classical in if G.pairConstraint.IsAdmissible σ then gasSupportMean A G (f j) σ else 0
structure FactorHypotheses (J : Finset ι) : Prop where
  score_nonneg : ∀ w, 0 ≤ A.score w
  measurable_score : Measurable A.score
  measurable_mean : ∀ j ∈ J, Measurable (admissibleMean G A f j)
  abs_mean_le : ∀ j ∈ J, ∀ σ, G.pairConstraint.IsAdmissible σ → |gasSupportMean A G (f j) σ| ≤ factorBound G A f j σ
  abs_mean_update_sub_le : ∀ j ∈ J, ∀ (σ : G.Config) (i : G.GasSpin) (v : G.SpinValue i) (m : ℕ),
    G.pairConstraint.IsAdmissible (Function.update σ i v) → (R.range : ℝ) / (4 * R.params.side) ≤ m →
    (∀ Y ∈ upperSites (f j), m + 2 ≤ setGap {Y} i.1.core) →
    |gasSupportMean A G (f j) (Function.update σ i v) -
        gasSupportMean A G (f j) (Function.update σ i (G.pairConstraint.vacant i))| ≤
      factorBound G A f j (Function.update σ i (G.pairConstraint.vacant i)) * Real.exp (-(R.params.rt * m / 2 ^ 5))
  lowerSizeConst_pos : ∀ j ∈ J, 0 < lowerSizeConst A (f j)
  parentBlock_mem : ∀ j ∈ J, ∀ y ∈ lowerSites (f j), parentBlock R.params.side y ∈ upperSites (f j)
  disjoint_lowerSites : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → Disjoint (lowerSites (f j)) (lowerSites (f k))
variable {A f G} {J : Finset ι}
theorem gasMajorantProduct_eq (σ : G.Config) : gasMajorantProduct A G f J σ = ∏ j ∈ J, factorBound G A f j σ := rfl
theorem gasMeanProduct_eq (σ : G.Config) : gasMeanProduct A G f J σ = ∏ j ∈ J, admissibleMean G A f j σ := rfl
theorem FactorHypotheses.factorBound_pos (h : FactorHypotheses G A f J) {j : ι} (hj : j ∈ J) (σ : G.Config) :
    0 < factorBound G A f j σ := by
  have h1 := one_le_spinScore (G := G) h.score_nonneg (lowerSites (f j)) σ
  have h2 := h.lowerSizeConst_pos j hj
  unfold factorBound
  positivity
theorem FactorHypotheses.gasMajorantProduct_pos (h : FactorHypotheses G A f J) (σ : G.Config) :
    0 < gasMajorantProduct A G f J σ :=
  Finset.prod_pos fun _ hj => h.factorBound_pos hj σ
theorem FactorHypotheses.measurable_gasMajorantProduct (h : FactorHypotheses G A f J) :
    Measurable (gasMajorantProduct A G f J) :=
  Finset.measurable_fun_prod _ fun _ _ => (measurable_spinScore h.measurable_score _).const_mul _
theorem FactorHypotheses.measurable_gasMeanProduct (h : FactorHypotheses G A f J) :
    Measurable (gasMeanProduct A G f J) :=
  Finset.measurable_fun_prod _ fun j hj => h.measurable_mean j hj
theorem FactorHypotheses.abs_admissibleMean_le (h : FactorHypotheses G A f J) {j : ι} (hj : j ∈ J) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) :
    |admissibleMean G A f j σ| ≤ factorBound G A f j σ := by
  classical
  unfold admissibleMean
  rw [if_pos hσ]
  exact h.abs_mean_le j hj σ hσ
theorem FactorHypotheses.abs_gasMeanProduct_le (h : FactorHypotheses G A f J) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) :
    |gasMeanProduct A G f J σ| ≤ gasMajorantProduct A G f J σ := by
  rw [gasMajorantProduct_eq, gasMeanProduct_eq, Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun j hj => h.abs_admissibleMean_le hj hσ
theorem FactorHypotheses.gasMajorantProduct_update_le (h : FactorHypotheses G A f J) (σ : G.Config) (i : G.GasSpin)
    (v : G.SpinValue i) :
    gasMajorantProduct A G f J (Function.update σ i v) ≤
      gasMajorantProduct A G f J (Function.update σ i (G.pairConstraint.vacant i)) *
        Real.exp (∑ y ∈ unionLowerSites f J, spinLabelScore A.score G i y v) := by
  classical
  have hdis : (J : Set ι).PairwiseDisjoint fun j => lowerSites (f j) := fun j hj k hk hjk =>
    h.disjoint_lowerSites j hj k hk hjk
  have e1 : ∑ y ∈ unionLowerSites f J, spinLabelScore A.score G i y v =
      ∑ j ∈ J, ∑ y ∈ lowerSites (f j), spinLabelScore A.score G i y v :=
    Finset.sum_biUnion hdis
  rw [e1, Real.exp_sum, gasMajorantProduct_eq, gasMajorantProduct_eq, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun j hj => (h.factorBound_pos hj _).le) fun j hj => ?_
  have h1 := spinScore_update_le (G := G) h.score_nonneg (lowerSites (f j)) σ i v
  have h2 := (h.lowerSizeConst_pos j hj).le
  unfold factorBound
  calc _ ≤ 4 * lowerSizeConst A (f j) *
        (spinScore A G (lowerSites (f j)) (Function.update σ i (G.pairConstraint.vacant i)) *
          Real.exp (∑ y ∈ lowerSites (f j), spinLabelScore A.score G i y v)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring
theorem FactorHypotheses.not_mem_support_of_lowerSites (h : FactorHypotheses G A f J) {j : ι} (hj : j ∈ J)
    {i : G.GasSpin} {m : ℕ}
    (hg : ∀ Y ∈ unionUpperSites f J, m + 2 ≤ setGap {Y} i.1.core) : ∀ y ∈ lowerSites (f j), y ∉ i.1.2 := by
  classical
  intro y hy hyi
  have h1 : parentBlock R.params.side y ∈ i.1.core := GasSupport.parentBlock_mem_core (Finset.mem_union_right _ hyi)
  have h2 := setGap_le_supDist (Finset.mem_singleton_self (parentBlock R.params.side y)) h1
  rw [supDist_self] at h2
  have h3 := hg _ (Finset.mem_biUnion.mpr ⟨j, hj, h.parentBlock_mem j hj y hy⟩)
  omega
theorem FactorHypotheses.gasMajorantProduct_update_eq (h : FactorHypotheses G A f J) {i : G.GasSpin} {m : ℕ}
    (hg : ∀ Y ∈ unionUpperSites f J, m + 2 ≤ setGap {Y} i.1.core) (σ : G.Config) (v : G.SpinValue i) :
    gasMajorantProduct A G f J (Function.update σ i v) =
      gasMajorantProduct A G f J (Function.update σ i (G.pairConstraint.vacant i)) := by
  rw [gasMajorantProduct_eq, gasMajorantProduct_eq]
  unfold factorBound
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [spinScore_update_eq v (h.not_mem_support_of_lowerSites hj hg)]
theorem FactorHypotheses.isGasTilt_majorant (h : FactorHypotheses G A f J) {e : ℝ} (he : 0 ≤ e) :
    IsGasTilt G A.score (unionUpperSites f J) (unionLowerSites f J) e fun σ => 2 * gasMajorantProduct A G f J σ where
  measurable := h.measurable_gasMajorantProduct.const_mul 2
  pos σ _ := by
    have := h.gasMajorantProduct_pos σ
    positivity
  update_le σ i v _ := by
    have h1 := h.gasMajorantProduct_update_le σ i v
    have h0 := (h.gasMajorantProduct_pos (Function.update σ i (G.pairConstraint.vacant i))).le
    have hE := Real.exp_pos (∑ y ∈ unionLowerSites f J, spinLabelScore A.score G i y v)
    nlinarith [mul_nonneg h0 hE.le]
  abs_update_sub_le σ i v m _ _ hg := by
    rw [h.gasMajorantProduct_update_eq hg σ v, sub_self, abs_zero]
    have h0 := (h.gasMajorantProduct_pos (Function.update σ i (G.pairConstraint.vacant i))).le
    positivity
theorem FactorHypotheses.isGasTilt_majorant_add_product (h : FactorHypotheses G A f J) {e : ℝ}
    (he : (J.card : ℝ) ≤ e) :
    IsGasTilt G A.score (unionUpperSites f J) (unionLowerSites f J) e
      fun σ => 2 * gasMajorantProduct A G f J σ + gasMeanProduct A G f J σ where
  measurable := (h.measurable_gasMajorantProduct.const_mul 2).add h.measurable_gasMeanProduct
  pos σ hσ := by
    have h1 := h.abs_gasMeanProduct_le hσ
    have h2 := h.gasMajorantProduct_pos σ
    have h3 := (abs_le.mp h1).1
    linarith
  update_le σ i v hv := by
    have h₀ := isAdmissible_update_vacant_of_update hv
    have h1 := h.gasMajorantProduct_update_le σ i v
    have h2 := (abs_le.mp (h.abs_gasMeanProduct_le hv)).2
    have h3 := (abs_le.mp (h.abs_gasMeanProduct_le h₀)).1
    have hU := h.gasMajorantProduct_pos (Function.update σ i (G.pairConstraint.vacant i))
    set Ex := Real.exp (∑ y ∈ unionLowerSites f J, spinLabelScore A.score G i y v) with hEx
    have hE : 0 < Ex := Real.exp_pos _
    set Y₀ := 2 * gasMajorantProduct A G f J (Function.update σ i (G.pairConstraint.vacant i)) +
      gasMeanProduct A G f J (Function.update σ i (G.pairConstraint.vacant i)) with hY₀
    have h4 : gasMajorantProduct A G f J (Function.update σ i (G.pairConstraint.vacant i)) ≤ Y₀ := by
      rw [hY₀]
      linarith
    calc _ ≤ 3 * gasMajorantProduct A G f J (Function.update σ i v) := by linarith
      _ ≤ 3 * (gasMajorantProduct A G f J (Function.update σ i (G.pairConstraint.vacant i)) * Ex) := by linarith
      _ ≤ 3 * (Y₀ * Ex) := by
          have := mul_le_mul_of_nonneg_right h4 hE.le
          linarith
      _ = _ := by ring
  abs_update_sub_le σ i v m hv hm hg := by
    have h₀ := isAdmissible_update_vacant_of_update hv
    set σ₁ := Function.update σ i v with hσ₁
    set σ₀ := Function.update σ i (G.pairConstraint.vacant i) with hσ₀
    set E := Real.exp (-(R.params.rt * m / 2 ^ 5)) with hE
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hUe : gasMajorantProduct A G f J σ₁ = gasMajorantProduct A G f J σ₀ := h.gasMajorantProduct_update_eq hg σ v
    have hbe : ∀ j ∈ J, factorBound G A f j σ₁ = factorBound G A f j σ₀ := fun j hj => by
      unfold factorBound
      rw [hσ₁, spinScore_update_eq v (h.not_mem_support_of_lowerSites hj hg)]
    have key := abs_prod_sub_prod_le (a := fun j => admissibleMean G A f j σ₁)
      (b := fun j => admissibleMean G A f j σ₀)
      (P := fun j => factorBound G A f j σ₀) hE0 J (fun j hj => (h.factorBound_pos hj _).le)
      (fun j hj => (h.abs_admissibleMean_le hj hv).trans (hbe j hj).le) (fun j hj => h.abs_admissibleMean_le hj h₀)
      (fun j hj => by
        classical
        simp only [admissibleMean, if_pos hv, if_pos h₀]
        have h1 := h.abs_mean_update_sub_le j hj σ i v m hv hm fun Y hY => hg Y (Finset.mem_biUnion.mpr ⟨j, hj, hY⟩)
        rw [mul_comm E]
        exact h1)
    have e1 : (2 * gasMajorantProduct A G f J σ₁ + gasMeanProduct A G f J σ₁) -
        (2 * gasMajorantProduct A G f J σ₀ + gasMeanProduct A G f J σ₀) =
        ∏ j ∈ J, admissibleMean G A f j σ₁ - ∏ j ∈ J, admissibleMean G A f j σ₀ := by
      rw [hUe, gasMeanProduct_eq, gasMeanProduct_eq]
      ring
    rw [e1]
    refine key.trans ?_
    have hU := h.gasMajorantProduct_pos σ₀
    have h3 := (abs_le.mp (h.abs_gasMeanProduct_le h₀)).1
    have h4 : gasMajorantProduct A G f J σ₀ ≤ 2 * gasMajorantProduct A G f J σ₀ + gasMeanProduct A G f J σ₀ := by
      linarith
    have hc0 : (0 : ℝ) ≤ J.card := Nat.cast_nonneg _
    calc (J.card : ℝ) * E * ∏ j ∈ J, factorBound G A f j σ₀ = (J.card : ℝ) * E * gasMajorantProduct A G f J σ₀ := rfl
      _ ≤ e * E * gasMajorantProduct A G f J σ₀ := by gcongr
      _ ≤ e * E * (2 * gasMajorantProduct A G f J σ₀ + gasMeanProduct A G f J σ₀) :=
          mul_le_mul_of_nonneg_left h4 (mul_nonneg (hc0.trans he) hE0)
end Tilts
section Blocks
theorem parentBlock_mem_weightSupportSites {L t n : ℕ} [NeZero L] [NeZero n]
    (f : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide L (t + 1) n)) {y : TorusSite (n * L)}
    (hy : y ∈ weightSupportSites L t (n * L) f) : parentBlock L y ∈ weightSupportSites L (t + 1) n f := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.parentBlock_mem_weightSupportSites <;> assumption
theorem image_parentBlock_weightSupportSites {L t n : ℕ} [NeZero L] [NeZero n]
    (f : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide L (t + 1) n)) :
    (open Classical in (weightSupportSites L t (n * L) f).image (parentBlock L)) = weightSupportSites L (t + 1) n f := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.image_parentBlock_weightSupportSites <;> assumption
end Blocks
section Main
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
theorem abs_update_sub_le_of_setGap {Q : Finset (TorusSite n)} {s : R.labels.Ω → ℝ}
    {B : Finset (TorusSite (n * R.params.side))} {e : ℝ} {Yt : G.Config → ℝ}
    (ht : IsGasTilt G s Q B e Yt) (hr : 8 * (R.params.side : ℝ) ≤ R.range) (i : G.GasSpin)
    (hl : (R.range : ℝ) / (2 * R.params.side) ≤ setGap Q i.1.core) (σ : G.Config) (v : G.SpinValue i)
    (hv : G.pairConstraint.IsAdmissible (Function.update σ i v)) :
    |Yt (Function.update σ i v) - Yt (Function.update σ i (G.pairConstraint.vacant i))| ≤
      e * Real.exp (-(R.params.rt * ((setGap Q i.1.core : ℝ) - 2) / 2 ^ 5)) *
        Yt (Function.update σ i (G.pairConstraint.vacant i)) := by
  have hL : (0 : ℝ) < R.params.side := by
    have : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
    exact_mod_cast this
  set l := setGap Q i.1.core with hld
  have hq : (2 : ℝ) ≤ (R.range : ℝ) / (4 * R.params.side) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hh : (R.range : ℝ) / (2 * R.params.side) = 2 * ((R.range : ℝ) / (4 * R.params.side)) := by
    field_simp
    ring
  have hl2' : 2 ≤ l := by
    have : (2 : ℝ) ≤ l := by linarith
    exact_mod_cast this
  have e1 : ((l - 2 : ℕ) : ℝ) = (l : ℝ) - 2 := by
    rw [Nat.cast_sub hl2']
    norm_num
  have hm : (R.range : ℝ) / (4 * R.params.side) ≤ ((l - 2 : ℕ) : ℝ) := by
    rw [e1]
    rw [hh] at hl
    linarith
  have k := ht.abs_update_sub_le σ i v (l - 2) hv hm fun Y hY => by
    have := setGap_le_setGap_singleton hY i
    omega
  rw [e1] at k
  exact k
theorem separatedWeightTiltsStatement_of (hfar : gasSupportMeanFarSpinBoundOneLevel)
    (hpaid : clusterScoreIntegralBound)
    (hgas : ClusterExpansionOfAStep.GasIsActivityBounded) (hfl : EventuallyFloorConditions) :
    separatedWeightTiltsStatement := by
  classical
  obtain ⟨r₁, p₁, H₁⟩ := hfar
  obtain ⟨r₂, p₂, H₂⟩ := hpaid
  obtain ⟨r₃, p₃, H₃⟩ := hgas
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (r₃ c)), fun c => lt_min (p₁ c) (lt_min (p₂ c) (p₃ c)),
    fun T hT hrt K => ?_⟩
  have t₁ := hrt.trans (min_le_left _ _)
  have t₂ := (hrt.trans (min_le_right _ _)).trans (min_le_left _ _)
  have t₃ := (hrt.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨y₁, H₁⟩ := H₁ T hT t₁ K
  obtain ⟨y₂, H₂⟩ := H₂ T hT t₂ K
  obtain ⟨y₃, H₃⟩ := H₃ T hT t₃
  have hLc : (0 : ℝ) < 8 * (T.side : ℝ) + 1 := by positivity
  obtain ⟨y₄, H₄⟩ := hfl T hT (8 * (T.side : ℝ) + 1) 1 hLc one_pos
  refine ⟨max T.floorMin (max y₁ (max y₂ (max y₃ (max y₄ (200 * T.B))))), fun y hy R A hK hAT => ?_⟩
  intro n _ G hG ι I J f D hSA hJI hJne Yt hYt
  have fl : ∀ {a : ℝ}, a ≤ max y₁ (max y₂ (max y₃ (max y₄ (200 * T.B)))) → a ≤ y :=
    fun h => h.trans ((le_max_right _ _).trans hy)
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hy1 : y₁ ≤ y := fl (le_max_left _ _)
  have hy2 : y₂ ≤ y := fl ((le_max_left _ _).trans (le_max_right _ _))
  have hy3 : y₃ ≤ y := fl ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hy4 : y₄ ≤ y :=
    fl ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hy6 : 200 * T.B ≤ y :=
    fl ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hOT := hAT.onFamily
  obtain ⟨hR, hρA, hpc, hyx, hstep⟩ := id hOT
  have hL : R.params.side = T.side := by rw [hR]; rfl
  have hx' : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAT.abs_sub_le).2
    have hx1 : 1 ≤ R.coupling := by
      have h1 : (1 : ℝ) ≤ T.floorMin := hT.yC_ge.trans (le_max_left _ _)
      linarith only [h1, hy0, hyx]
    linarith only [h1, hy6, hyx, hx1]
  have hr8 : 8 * (R.params.side : ℝ) ≤ R.range := by
    have h1 : 8 * (T.side : ℝ) + 1 ≤ (clusterRange R.coupling : ℝ) := (H₄ R.coupling (hy4.trans hyx)).range_ge
    have h2 : (R.range : ℝ) = (clusterRange R.coupling : ℝ) := rfl
    rw [hL, h2]
    linarith only [h1]
  have hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity T.gasRate) :=
    H₃ y hy3 R hOT hx' n G hG fun j => j.1.Touches ∅
  have paid := H₂ y hy2 R A hK hAT n G hG
  have hs0 : ∀ w, 0 ≤ A.score w := hAT.admissible.price.nonneg
  have hsb : Measurable A.score := hAT.admissible.price.borel
  have hmv := fun i (hi : i ∈ I) => H₁ y hy1 R A hK hAT n G hG (f i) (hSA.weightNorm_le i hi) (hSA.nonempty i hi)
  have hC₀ : 1 ≤ A.responseParams.C₀ := by
    have hl := hAT.admissible.params_admissible
    have h1 := hl.C₀_eq
    have h2 := hl.N₀_nonneg
    have h3 := hl.Kc_ge
    have h4 : 1 ≤ R.params.coupling := by
      have : R.params.coupling = T.coupling := by rw [hR]; rfl
      rw [this]
      exact hT.a_ge
    linarith only [h1, h2, h3, h4]
  have hself : ∀ {S : Finset (TorusSite n)} {Y : TorusSite n}, Y ∈ S → Y ∈ thickening 2 S := fun {S Y} h => by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Y, h, ?_⟩
    rw [supDist_self]
    omega
  have hblock : ∀ j, ∀ y ∈ lowerSites (f j), parentBlock R.params.side y ∈ upperSites (f j) := fun j y hy =>
    parentBlock_mem_weightSupportSites (f j) hy
  have hF : FactorHypotheses G A f J := {
    score_nonneg := hs0
    measurable_score := hsb
    measurable_mean := fun j hj => (hmv j (hJI hj)).1
    abs_mean_le := fun j hj => (hmv j (hJI hj)).2.1
    abs_mean_update_sub_le := fun j hj => (hmv j (hJI hj)).2.2
    lowerSizeConst_pos := fun j hj => by
      have hc : (0 : ℝ) < ((lowerSites (f j)).card : ℝ) := by
        obtain ⟨Y, hY⟩ := hSA.nonempty j (hJI hj)
        have hpar : (open Classical in (lowerSites (f j)).image (parentBlock R.params.side)) = upperSites (f j) :=
          image_parentBlock_weightSupportSites (f j)
        rw [← hpar] at hY
        obtain ⟨y', hy', -⟩ := Finset.mem_image.mp hY
        exact_mod_cast Finset.card_pos.mpr ⟨y', hy'⟩
      unfold lowerSizeConst
      have h0 : 0 < A.responseParams.C₀ := by linarith only [hC₀]
      exact mul_pos h0 hc
    parentBlock_mem := fun j _ => hblock j
    disjoint_lowerSites := fun j hj k hk hjk => by
      refine Finset.disjoint_left.mpr fun y h1 h2 => ?_
      have := hSA.separated j (hJI hj) k (hJI hk) hjk _ (hself (hblock j y h1)) _ (hself (hblock k y h2))
      rw [supDist_self] at this
      have := hSA.eight_lt
      omega }
  have ht : IsGasTilt G A.score (unionUpperSites f J) (unionLowerSites f J) (J.card : ℝ) Yt := by
    rcases hYt with rfl | rfl
    · exact hF.isGasTilt_majorant_add_product le_rfl
    · exact hF.isGasTilt_majorant (Nat.cast_nonneg _)
  have hw' := isActivityBounded_mul_tilt hs0 hw paid ht
  refine ⟨ht, hw, hw', fun i σ hσ B hB => ?_⟩
  have hz : 0 ≤ G.spinActivity T.gasRate i := hw.activity_nonneg i
  have hall := abs_singleSiteKernel_sub_le hw hw' hσ i hB
  unfold tiltActivity
  split_ifs with hl
  · rw [mul_min_of_nonneg _ _ (by positivity)]
    refine le_min (by linarith only [hall, hz]) ?_
    set ε := (J.card : ℝ) * Real.exp (-(R.params.rt * ((setGap (unionUpperSites f J) i.1.core : ℝ) - 2) / 2 ^ 5))
      with hε
    have hε0 : 0 ≤ ε := by positivity
    have hn := abs_singleSiteKernel_sub_le_of_near hw hw' ht.pos hσ i hε0
      (fun v hv _ => abs_update_sub_le_of_setGap ht hr8 i hl σ v hv) hB
    calc _ ≤ 2 * (2 * ε * G.spinActivity T.gasRate i) := mul_le_mul_of_nonneg_left hn (by norm_num)
      _ = _ := by ring
  · linarith only [hall, hz]
end Main
end SeparatedWeightTilts
theorem separatedWeightTiltsStatement_holds (hfar : gasSupportMeanFarSpinBoundOneLevel)
    (hpaid : clusterScoreIntegralBound)
    (hgas : ClusterExpansionOfAStep.GasIsActivityBounded) (hfl : EventuallyFloorConditions) :
    separatedWeightTiltsStatement := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SeparatedWeightTilts.separatedWeightTiltsStatement_of <;> assumption
end ResponseInTheExpansion
end YangMills.Construction
end
