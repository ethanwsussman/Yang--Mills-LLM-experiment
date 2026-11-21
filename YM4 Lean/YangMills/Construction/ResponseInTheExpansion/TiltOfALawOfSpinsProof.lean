import YangMills.Construction.ClusterExpansionOfAStep.ComparisonOfHeldGasesProof
import YangMills.Construction.ResponseInTheExpansion.TiltOfALawOfSpins
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory YangMills.Construction.Dobrushin
open scoped ENNReal
namespace YangMills.Construction.LinearResponse
namespace SingleSiteTilt
set_option linter.unusedSectionVars false
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)] {A : PairConstraint S}
  {m : ∀ i, Measure (S i)} [∀ i, SigmaFinite (m i)] {G Y : (∀ i, S i) → ℝ} {z z' : I → ℝ}
theorem isAdmissible_update_vacant {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) (i : I) :
    A.IsAdmissible (Function.update σ i (A.vacant i)) := by apply _root_.YangMills.Construction.Dobrushin.VacantSpin.isAdmissible_update_vacant <;> assumption
def vacancyRatio (A : PairConstraint S) (m : ∀ i, Measure (S i)) (G : (∀ i, S i) → ℝ) (i : I) (σ : ∀ i, S i) (B : Set (S i)) : ℝ :=
  (∫⁻ s in B \ {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i).toReal /
    (A.weightDensity G (Function.update σ i (A.vacant i))).toReal
theorem weightDensity_update_vacant_pos (h : A.IsActivityBounded m G z) {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) (i : I) :
    0 < A.weightDensity G (Function.update σ i (A.vacant i)) := by
  classical
  unfold PairConstraint.weightDensity
  rw [if_pos (isAdmissible_update_vacant hσ i)]
  exact ENNReal.ofReal_pos.mpr (h.pos_of_admissible _ (isAdmissible_update_vacant hσ i))
theorem weightDensity_update_vacant_ne_top {σ : ∀ i, S i} (i : I) :
    A.weightDensity G (Function.update σ i (A.vacant i)) ≠ ⊤ := by
  classical
  unfold PairConstraint.weightDensity
  split_ifs
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.zero_ne_top
theorem setLIntegral_diff_vacant_le (h : A.IsActivityBounded m G z) {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) (i : I) (B : Set (S i)) :
    ∫⁻ s in B \ {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i ≤
      ENNReal.ofReal (z i) * A.weightDensity G (Function.update σ i (A.vacant i)) := by
  refine le_trans (lintegral_mono_set fun s hs => ?_) (h.lintegral_compl_vacant_le i σ hσ)
  exact hs.2
theorem setLIntegral_diff_vacant_ne_top (h : A.IsActivityBounded m G z) {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) (i : I) (B : Set (S i)) :
    ∫⁻ s in B \ {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (weightDensity_update_vacant_ne_top i))
    (setLIntegral_diff_vacant_le h hσ i B)
theorem setLIntegral_eq_vacant_add_diff (h : A.IsActivityBounded m G z) (σ : ∀ i, S i) (i : I) {B : Set (S i)} (hB : MeasurableSet B) :
    ∫⁻ s in B, A.weightDensity G (Function.update σ i s) ∂m i =
      (open Classical in if A.vacant i ∈ B then A.weightDensity G (Function.update σ i (A.vacant i)) else 0) +
        ∫⁻ s in B \ {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i := by
  classical
  have hset := h.measurableSet_vacant i
  have hd : Disjoint (B ∩ {A.vacant i}) (B \ {A.vacant i}) := by
    rw [Set.disjoint_left]
    rintro s ⟨_, h2⟩ ⟨_, h3⟩
    exact h3 h2
  have hu : B = (B ∩ {A.vacant i}) ∪ (B \ {A.vacant i}) := by
    rw [Set.inter_union_diff]
  have h1 : ∫⁻ s in B, A.weightDensity G (Function.update σ i s) ∂m i =
      ∫⁻ s in B ∩ {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i +
        ∫⁻ s in B \ {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i := by
    conv_lhs => rw [hu]
    exact lintegral_union (hB.diff hset) hd
  rw [h1]
  congr 1
  by_cases ha : A.vacant i ∈ B
  · rw [if_pos ha]
    have e : B ∩ {A.vacant i} = {A.vacant i} := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · exact fun h => h.2
      · rintro rfl
        exact ⟨ha, rfl⟩
    rw [e]
    have : ∫⁻ s in {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i =
        ∫⁻ _s in {A.vacant i}, A.weightDensity G (Function.update σ i (A.vacant i)) ∂m i := by
      refine setLIntegral_congr_fun hset fun s hs => ?_
      have : s = A.vacant i := hs
      rw [this]
    rw [this, setLIntegral_const, h.measure_vacant, mul_one]
  · rw [if_neg ha]
    have e : B ∩ {A.vacant i} = ∅ := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro hs rfl
      exact ha hs
    rw [e]
    simp
theorem conditionalMass_eq (h : A.IsActivityBounded m G z) (σ : ∀ i, S i) (i : I) :
    A.conditionalMass m G i σ = A.weightDensity G (Function.update σ i (A.vacant i)) +
      ∫⁻ s in Set.univ \ {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i := by
  have := setLIntegral_eq_vacant_add_diff h σ i MeasurableSet.univ
  rw [if_pos (Set.mem_univ _)] at this
  rw [← this]
  simp [PairConstraint.conditionalMass]
theorem singleSiteKernel_real_eq (h : A.IsActivityBounded m G z) {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) (i : I) {B : Set (S i)}
    (hB : MeasurableSet B) :
    (A.singleSiteKernel m h.measurable_weightDensity i σ).real B =
      ((open Classical in if A.vacant i ∈ B then 1 else 0) + vacancyRatio A m G i σ B) /
        (1 + vacancyRatio A m G i σ B + vacancyRatio A m G i σ Bᶜ) := by
  classical
  set g₀ := A.weightDensity G (Function.update σ i (A.vacant i)) with hg₀
  have hg0 : 0 < g₀ := weightDensity_update_vacant_pos h hσ i
  have hgt : g₀ ≠ ⊤ := weightDensity_update_vacant_ne_top i
  set u₁ := ∫⁻ s in B \ {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i with hu₁
  set u₂ := ∫⁻ s in Bᶜ \ {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i with hu₂
  have hu₁t : u₁ ≠ ⊤ := setLIntegral_diff_vacant_ne_top h hσ i B
  have hu₂t : u₂ ≠ ⊤ := setLIntegral_diff_vacant_ne_top h hσ i Bᶜ
  have hset := h.measurableSet_vacant i
  have huniv : ∫⁻ s in Set.univ \ {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i = u₁ + u₂ := by
    have hd : Disjoint (B \ {A.vacant i}) (Bᶜ \ {A.vacant i}) := by
      rw [Set.disjoint_left]
      rintro s ⟨h1, _⟩ ⟨h2, _⟩
      exact h2 h1
    have hu : Set.univ \ {A.vacant i} = (B \ {A.vacant i}) ∪ (Bᶜ \ {A.vacant i}) := by
      ext s
      by_cases hs : s ∈ B <;> simp [hs]
    rw [hu]
    exact lintegral_union (hB.compl.diff hset) hd
  have hmass : A.conditionalMass m G i σ = g₀ + (u₁ + u₂) := by
    rw [conditionalMass_eq h, huniv]
  have hmt : A.conditionalMass m G i σ ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.add_ne_top.mpr ⟨hgt, ENNReal.add_ne_top.mpr ⟨hu₁t, hu₂t⟩⟩
  have hmp : 0 < A.conditionalMass m G i σ := by
    rw [hmass]
    exact lt_of_lt_of_le hg0 le_self_add
  have hcond : (A.singleSiteKernel m h.measurable_weightDensity i σ) = A.singleSiteLaw m G i σ := rfl
  have hval : (A.singleSiteKernel m h.measurable_weightDensity i σ) B = (A.conditionalMass m G i σ)⁻¹ *
      ∫⁻ s in B, A.weightDensity G (Function.update σ i s) ∂m i := by
    rw [hcond]
    unfold PairConstraint.singleSiteLaw
    rw [if_pos ⟨hmp, hmt⟩]
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [withDensity_apply _ hB]
  rw [Measure.real, hval, setLIntegral_eq_vacant_add_diff h σ i hB, ENNReal.toReal_mul, ENNReal.toReal_inv, hmass]
  have hg0r : 0 < g₀.toReal := ENNReal.toReal_pos hg0.ne' hgt
  have ex₁ : vacancyRatio A m G i σ B = u₁.toReal / g₀.toReal := rfl
  have ex₂ : vacancyRatio A m G i σ Bᶜ = u₂.toReal / g₀.toReal := rfl
  rw [ex₁, ex₂]
  rw [ENNReal.toReal_add hgt (ENNReal.add_ne_top.mpr ⟨hu₁t, hu₂t⟩), ENNReal.toReal_add hu₁t hu₂t]
  by_cases ha : A.vacant i ∈ B
  · simp only [if_pos ha]
    rw [ENNReal.toReal_add hgt hu₁t]
    field_simp
    ring
  · simp only [if_neg ha]
    rw [zero_add, zero_add]
    have e0 : (∫⁻ s in B \ {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i).toReal = u₁.toReal := rfl
    rw [e0]
    field_simp
    ring
theorem vacancyRatio_nonneg (i : I) (σ : ∀ i, S i) (B : Set (S i)) : 0 ≤ vacancyRatio A m G i σ B :=
  div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
theorem vacancyRatio_add_compl_le (h : A.IsActivityBounded m G z) {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) (i : I) {B : Set (S i)}
    (hB : MeasurableSet B) : vacancyRatio A m G i σ B + vacancyRatio A m G i σ Bᶜ ≤ z i := by
  classical
  set g₀ := A.weightDensity G (Function.update σ i (A.vacant i)) with hg₀
  have hg0 : 0 < g₀ := weightDensity_update_vacant_pos h hσ i
  have hgt : g₀ ≠ ⊤ := weightDensity_update_vacant_ne_top i
  have hg0r : 0 < g₀.toReal := ENNReal.toReal_pos hg0.ne' hgt
  have hset := h.measurableSet_vacant i
  have hd : Disjoint (B \ {A.vacant i}) (Bᶜ \ {A.vacant i}) := by
    rw [Set.disjoint_left]
    rintro s ⟨h1, _⟩ ⟨h2, _⟩
    exact h2 h1
  have hu : Set.univ \ {A.vacant i} = (B \ {A.vacant i}) ∪ (Bᶜ \ {A.vacant i}) := by
    ext s
    by_cases hs : s ∈ B <;> simp [hs]
  have e1 : ∫⁻ s in Set.univ \ {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i =
      (∫⁻ s in B \ {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i) +
        ∫⁻ s in Bᶜ \ {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i := by
    rw [hu]
    exact lintegral_union (hB.compl.diff hset) hd
  have h2 := setLIntegral_diff_vacant_le h hσ i Set.univ
  rw [e1] at h2
  have t₁ := setLIntegral_diff_vacant_ne_top h hσ i B
  have t₂ := setLIntegral_diff_vacant_ne_top h hσ i Bᶜ
  have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgt) h2
  rw [ENNReal.toReal_add t₁ t₂, ENNReal.toReal_mul, ENNReal.toReal_ofReal (h.activity_nonneg i)] at h3
  unfold vacancyRatio
  rw [← add_div, div_le_iff₀ hg0r]
  exact h3
theorem ratio_le_ratio_add_of_near {t b₁ b₂ a₁ a₂ e : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (he : 0 ≤ e)
    (h₁ : (1 - e) * b₁ ≤ a₁) (h₁' : a₁ ≤ (1 + e) * b₁) (h₂ : (1 - e) * b₂ ≤ a₂) (h₂' : a₂ ≤ (1 + e) * b₂)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb : b₁ + b₂ ≤ 1) :
    (t + b₁) / (1 + b₁ + b₂) ≤ (t + a₁) / (1 + a₁ + a₂) + 4 * e * (b₁ + b₂) := by
  have hd₁ : 0 < 1 + b₁ + b₂ := by linarith
  have hd₂ : 0 < 1 + a₁ + a₂ := by linarith
  rw [div_add' _ _ _ hd₂.ne', div_le_div_iff₀ hd₁ hd₂]
  set E := e * (b₁ + b₂) with hE
  have k1 : a₁ + a₂ - b₁ - b₂ ≤ E := by rw [hE]; nlinarith
  have k2 : t * (a₁ + a₂ - b₁ - b₂) ≤ E := by
    by_cases hx : 0 ≤ a₁ + a₂ - b₁ - b₂
    · nlinarith
    · have := mul_nonneg ht0 (le_of_lt (not_le.mp hx) |> fun h => neg_nonneg.mpr h)
      nlinarith
  have k3 : (1 - e) * b₁ * b₂ ≤ a₁ * b₂ := mul_le_mul_of_nonneg_right h₁ hb₂
  have k4 : b₁ * a₂ ≤ b₁ * ((1 + e) * b₂) := mul_le_mul_of_nonneg_left h₂' hb₁
  have k5 : 2 * (b₁ * b₂) ≤ b₁ + b₂ := by nlinarith
  have k6 : 2 * e * (b₁ * b₂) ≤ E := by
    rw [hE]
    nlinarith
  have hprod : 1 ≤ (1 + a₁ + a₂) * (1 + b₁ + b₂) := by nlinarith
  have hbig : 4 * E ≤ 4 * E * ((1 + a₁ + a₂) * (1 + b₁ + b₂)) := by nlinarith
  have hE' : 4 * e * (b₁ + b₂) = 4 * E := by rw [hE]; ring
  rw [hE']
  nlinarith
theorem vacancyRatio_tilt_bounds (h : A.IsActivityBounded m G z) (hY : ∀ σ, A.IsAdmissible σ → 0 < Y σ) {σ : ∀ i, S i}
    (hσ : A.IsAdmissible σ) (i : I) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hnear : ∀ s : S i, A.IsAdmissible (Function.update σ i s) → s ≠ A.vacant i →
      |Y (Function.update σ i s) - Y (Function.update σ i (A.vacant i))| ≤
        e * Y (Function.update σ i (A.vacant i))) {B : Set (S i)} (hB : MeasurableSet B) :
    (1 - e) * vacancyRatio A m G i σ B ≤ vacancyRatio A m (fun σ => G σ * Y σ) i σ B ∧
      vacancyRatio A m (fun σ => G σ * Y σ) i σ B ≤ (1 + e) * vacancyRatio A m G i σ B := by
  classical
  set y₀ := Y (Function.update σ i (A.vacant i)) with hy₀
  have hadm := isAdmissible_update_vacant hσ i
  have hy0 : 0 < y₀ := hY _ hadm
  have hset := h.measurableSet_vacant i
  have hBd : MeasurableSet (B \ {A.vacant i}) := hB.diff hset
  set g₀ := A.weightDensity G (Function.update σ i (A.vacant i)) with hg₀
  have hg0 : 0 < g₀ := weightDensity_update_vacant_pos h hσ i
  have hgt : g₀ ≠ ⊤ := weightDensity_update_vacant_ne_top i
  have hg0r : 0 < g₀.toReal := ENNReal.toReal_pos hg0.ne' hgt
  have hG0 : 0 < G (Function.update σ i (A.vacant i)) := h.pos_of_admissible _ hadm
  have hg'₀ : (A.weightDensity (fun σ => G σ * Y σ) (Function.update σ i (A.vacant i))).toReal = g₀.toReal * y₀ := by
    rw [hg₀]
    unfold PairConstraint.weightDensity
    rw [if_pos hadm, if_pos hadm, ENNReal.toReal_ofReal (mul_nonneg hG0.le hy0.le), ENNReal.toReal_ofReal hG0.le]
  have up : ∀ s ∈ B \ {A.vacant i}, A.weightDensity (fun σ => G σ * Y σ) (Function.update σ i s) ≤
      ENNReal.ofReal ((1 + e) * y₀) * A.weightDensity G (Function.update σ i s) := by
    intro s hs
    unfold PairConstraint.weightDensity
    by_cases ha : A.IsAdmissible (Function.update σ i s)
    · rw [if_pos ha, if_pos ha, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have h1 := hnear s ha hs.2
      have h2 := (abs_le.mp h1).2
      have h3 := h.pos_of_admissible _ ha
      nlinarith
    · rw [if_neg ha, if_neg ha]
      simp
  have lo : ∀ s ∈ B \ {A.vacant i}, ENNReal.ofReal ((1 - e) * y₀) * A.weightDensity G (Function.update σ i s) ≤
      A.weightDensity (fun σ => G σ * Y σ) (Function.update σ i s) := by
    intro s hs
    unfold PairConstraint.weightDensity
    by_cases ha : A.IsAdmissible (Function.update σ i s)
    · have h0 : 0 ≤ (1 - e) * y₀ := mul_nonneg (by linarith) hy0.le
      rw [if_pos ha, if_pos ha, ← ENNReal.ofReal_mul h0]
      apply ENNReal.ofReal_le_ofReal
      have h1 := hnear s ha hs.2
      have h2 := (abs_le.mp h1).1
      have h3 := h.pos_of_admissible _ ha
      nlinarith
    · rw [if_neg ha, if_neg ha]
      simp
  have i₁ := setLIntegral_mono' (μ := m i) hBd up
  have i₂ := setLIntegral_mono' (μ := m i) hBd lo
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at i₁ i₂
  set u := ∫⁻ s in B \ {A.vacant i}, A.weightDensity G (Function.update σ i s) ∂m i with hu
  set u' := ∫⁻ s in B \ {A.vacant i}, A.weightDensity (fun σ => G σ * Y σ) (Function.update σ i s) ∂m i with hu'
  have hut : u ≠ ⊤ := setLIntegral_diff_vacant_ne_top h hσ i B
  have hu't : u' ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hut) i₁
  have r₁ := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hut) i₁
  have r₂ := ENNReal.toReal_mono hu't i₂
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at r₁
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (by linarith) hy0.le)] at r₂
  have ex : vacancyRatio A m G i σ B = u.toReal / g₀.toReal := rfl
  have ex' : vacancyRatio A m (fun σ => G σ * Y σ) i σ B = u'.toReal / (g₀.toReal * y₀) := by
    unfold vacancyRatio
    rw [hg'₀]
  rw [ex, ex']
  have hden : 0 < g₀.toReal * y₀ := by positivity
  constructor
  · rw [le_div_iff₀ hden]
    calc (1 - e) * (u.toReal / g₀.toReal) * (g₀.toReal * y₀) = (1 - e) * y₀ * u.toReal := by
          field_simp
      _ ≤ _ := r₂
  · rw [div_le_iff₀ hden]
    calc u'.toReal ≤ (1 + e) * y₀ * u.toReal := r₁
      _ = _ := by field_simp
theorem tiltedGibbsComparison_of (hD : Dobrushin.ComparisonStatement) (hC : Dobrushin.ActivityConditionalLawsStatement) :
    TiltedGibbsComparison := by
  intro I _ _ S _ A m _ G Y z z' h h' c b w hY hz1 hc hb hw hmove hcol hbi
  obtain ⟨p1, g1, c1, -⟩ := hC I S A m G z h
  obtain ⟨p2, g2, c2, -⟩ := hC I S A m _ z' h'
  refine hD I S A (A.gibbsLaw m G) (A.gibbsLaw m fun σ => G σ * Y σ) _ _ c b w h.measurableSet_admissible g1 g2 hc hb hw hmove ?_ hcol
  intro i σ hσ B hB
  have m1 := g1.isMarkovKernel i
  have m2 := g2.isMarkovKernel i
  rcases hbi i with hcr | ⟨e, he0, he1, heb, hnear⟩
  · have hz0 := h.activity_nonneg i
    have hz0' := h'.activity_nonneg i
    have hset := h.measurableSet_vacant i
    classical
    by_cases ha : A.vacant i ∈ B
    · have k1 : (A.singleSiteKernel m h.measurable_weightDensity i σ).real B ≤ 1 := measureReal_le_one
      have k2 : (A.singleSiteKernel m h'.measurable_weightDensity i σ).real B +
          (A.singleSiteKernel m h'.measurable_weightDensity i σ).real Bᶜ = 1 := by
        rw [measureReal_add_measureReal_compl hB]
        simp
      have k3 : (A.singleSiteKernel m h'.measurable_weightDensity i σ).real Bᶜ ≤
          (A.singleSiteKernel m h'.measurable_weightDensity i σ).real {A.vacant i}ᶜ :=
        measureReal_mono (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr ha))
      have k4 := c2 i σ hσ
      linarith
    · have k1 : (A.singleSiteKernel m h.measurable_weightDensity i σ).real B ≤
          (A.singleSiteKernel m h.measurable_weightDensity i σ).real {A.vacant i}ᶜ :=
        measureReal_mono fun s hs hs' => ha (by rw [← Set.mem_singleton_iff.mp hs']; exact hs)
      have k2 := c1 i σ hσ
      have k3 : 0 ≤ (A.singleSiteKernel m h'.measurable_weightDensity i σ).real B := measureReal_nonneg
      linarith
  · rw [singleSiteKernel_real_eq h hσ i hB, singleSiteKernel_real_eq h' hσ i hB]
    classical
    obtain ⟨l₁, u₁⟩ := vacancyRatio_tilt_bounds h hY hσ i he0 he1 (fun s ha hs => hnear σ s ha hs) hB
    obtain ⟨l₂, u₂⟩ := vacancyRatio_tilt_bounds h hY hσ i he0 he1 (fun s ha hs => hnear σ s ha hs) hB.compl
    have hs := vacancyRatio_add_compl_le h hσ i hB
    have ht0 : (0 : ℝ) ≤ (if A.vacant i ∈ B then 1 else 0) := by split_ifs <;> norm_num
    have ht1 : ((if A.vacant i ∈ B then 1 else 0) : ℝ) ≤ 1 := by split_ifs <;> norm_num
    have key := ratio_le_ratio_add_of_near ht0 ht1 (vacancyRatio_nonneg i σ B) (vacancyRatio_nonneg i σ Bᶜ) he0 l₁ u₁ l₂ u₂
      (vacancyRatio_nonneg i σ B) (vacancyRatio_nonneg i σ Bᶜ) (hs.trans (hz1 i))
    have h4 : 4 * e * (vacancyRatio A m G i σ B + vacancyRatio A m G i σ Bᶜ) ≤ 4 * e * z i :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    linarith
end SingleSiteTilt
theorem tiltedGibbsComparison_holds (hD : Dobrushin.ComparisonStatement) (hC : Dobrushin.ActivityConditionalLawsStatement) :
    TiltedGibbsComparison := SingleSiteTilt.tiltedGibbsComparison_of hD hC
end YangMills.Construction.LinearResponse
end
