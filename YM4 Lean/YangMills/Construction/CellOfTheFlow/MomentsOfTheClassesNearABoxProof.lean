import YangMills.Construction.CellOfTheFlow.DeepClassesAreInTheLowerWindow
import YangMills.Construction.CellOfTheFlow.LongHullsAreRare
import YangMills.Construction.CellOfTheFlow.MomentOfTheLowerMajorant
import YangMills.Construction.CellOfTheFlow.MomentOfTheMajorant
import YangMills.Construction.CellOfTheFlow.MomentsOfTheClassesNearABox
import YangMills.Construction.CellOfTheFlow.TheLowerMajorantIsBelowTheMajorant
import YangMills.Construction.FreeEnergiesOfTheFlow.StateOfAStepIsBorelProof
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import YangMills.Construction.ResponseInTheExpansion.WhatTheChainReadsIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows.NearBoxMoments
open TorusFields TorusLumps WeightedResponses StepSettings RenormalizationStepParameters ResponseInTheExpansion
section Measures
variable {Ω : Type} [MeasurableSpace Ω]
private theorem moment_le_of_exp_moment (μ : Measure Ω) [IsProbabilityMeasure μ] {U : Ω → ℝ} (hU : Measurable U)
    (hU0 : ∀ ω, 0 ≤ U ω) {A : ℝ} (hA : 0 ≤ A)
    (hexp : ∫⁻ ω, ENNReal.ofReal (Real.exp (U ω)) ∂μ ≤ ENNReal.ofReal (Real.exp A)) (q : ℕ) (hq : 1 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal (U ω ^ q) ∂μ ≤ ENNReal.ofReal (((q : ℝ) + A) ^ q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set B : ℝ := q + A with hB
  have hB0 : 0 < B := by linarith
  set θ : ℝ := q / B with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hB0]
    linarith
  set κ : ℝ := B ^ q * Real.exp (-(q : ℝ)) * Real.exp (θ * A) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hpt : ∀ ω, U ω ^ q ≤ κ * (1 - θ) + κ * (θ * Real.exp (-A)) * Real.exp (U ω) := by
    intro ω
    have h1 : U ω ≤ B * Real.exp (U ω / B - 1) := by
      have h2 := Real.add_one_le_exp (U ω / B - 1)
      have h3 : U ω / B ≤ Real.exp (U ω / B - 1) := by linarith
      calc U ω = B * (U ω / B) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 hB0.le
    have h3 : U ω ^ q ≤ B ^ q * Real.exp (θ * U ω - q) := by
      calc U ω ^ q ≤ (B * Real.exp (U ω / B - 1)) ^ q := pow_le_pow_left₀ (hU0 ω) h1 q
        _ = B ^ q * Real.exp (θ * U ω - q) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2
          rw [hθ]
          field_simp
    have h4 : Real.exp (θ * (U ω - A)) ≤ (1 - θ) + θ * Real.exp (U ω - A) := by
      have h5 := Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.2 hθ1) hθ0 zero_le_one
        (Real.exp_pos (U ω - A)).le (by ring)
      rw [Real.one_rpow, one_mul, ← Real.exp_mul, mul_one, mul_comm (U ω - A)] at h5
      exact h5
    have h5 : Real.exp (θ * U ω - q) =
        Real.exp (-(q : ℝ)) * Real.exp (θ * A) * Real.exp (θ * (U ω - A)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have h6 : Real.exp (U ω - A) = Real.exp (-A) * Real.exp (U ω) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc U ω ^ q ≤ B ^ q * Real.exp (θ * U ω - q) := h3
      _ = κ * Real.exp (θ * (U ω - A)) := by
        rw [h5, hκ]
        ring
      _ ≤ κ * ((1 - θ) + θ * Real.exp (U ω - A)) := mul_le_mul_of_nonneg_left h4 hκ0
      _ = _ := by
        rw [h6]
        ring
  have hm : Measurable fun ω => ENNReal.ofReal (Real.exp (U ω)) :=
    (Real.measurable_exp.comp hU).ennreal_ofReal
  have hc1 : 0 ≤ κ * (1 - θ) := mul_nonneg hκ0 (sub_nonneg.2 hθ1)
  have hc2 : 0 ≤ κ * (θ * Real.exp (-A)) := by positivity
  have hκB : κ ≤ B ^ q := by
    have h1 : θ * A ≤ q := by
      rw [hθ, div_mul_eq_mul_div, div_le_iff₀ hB0]
      nlinarith
    have h2 : Real.exp (-(q : ℝ)) * Real.exp (θ * A) ≤ 1 := by
      rw [← Real.exp_add]
      exact Real.exp_le_one_iff.2 (by linarith)
    calc κ = B ^ q * (Real.exp (-(q : ℝ)) * Real.exp (θ * A)) := by rw [hκ]; ring
      _ ≤ B ^ q * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = B ^ q := mul_one _
  calc ∫⁻ ω, ENNReal.ofReal (U ω ^ q) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal (κ * (1 - θ)) +
          ENNReal.ofReal (κ * (θ * Real.exp (-A))) * ENNReal.ofReal (Real.exp (U ω))) ∂μ := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul hc2, ← ENNReal.ofReal_add hc1 (mul_nonneg hc2 (Real.exp_pos _).le)]
        exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (κ * (1 - θ)) + ENNReal.ofReal (κ * (θ * Real.exp (-A))) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp (U ω)) ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul _ hm, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (κ * (1 - θ)) + ENNReal.ofReal (κ * (θ * Real.exp (-A))) *
          ENNReal.ofReal (Real.exp A) := by
        gcongr
    _ = ENNReal.ofReal κ := by
        rw [← ENNReal.ofReal_mul hc2, ← ENNReal.ofReal_add hc1 (mul_nonneg hc2 (Real.exp_pos _).le)]
        congr 1
        have h7 : Real.exp (-A) * Real.exp A = 1 := by
          rw [← Real.exp_add]
          simp
        calc κ * (1 - θ) + κ * (θ * Real.exp (-A)) * Real.exp A
            = κ * (1 - θ) + κ * θ * (Real.exp (-A) * Real.exp A) := by ring
          _ = κ := by
            rw [h7]
            ring
    _ ≤ ENNReal.ofReal (B ^ q) := ENNReal.ofReal_le_ofReal hκB
private theorem lintegral_indicator_pow_le (μ : Measure Ω) {g : Ω → ℝ} (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω)
    (p : ℕ) {E : Set Ω} (hE : MeasurableSet E) {M t : ℝ} (hM : 0 ≤ M) (ht : 0 ≤ t)
    (h1 : ∫⁻ ω, ENNReal.ofReal (g ω ^ (2 * p)) ∂μ ≤ ENNReal.ofReal (M ^ 2))
    (h2 : μ E ≤ ENNReal.ofReal (t ^ 2)) :
    ∫⁻ ω, E.indicator (fun ω => ENNReal.ofReal (g ω ^ p)) ω ∂μ ≤ ENNReal.ofReal (M * t) := by
  classical
  set F : Ω → ENNReal := fun ω => ENNReal.ofReal (g ω ^ p) with hF
  set I : Ω → ENNReal := E.indicator 1 with hI
  have hFm : Measurable F := ((hg.pow_const p)).ennreal_ofReal
  have hIm : Measurable I := measurable_one.indicator hE
  have e1 : (fun ω => E.indicator F ω) = F * I := by
    funext ω
    by_cases hω : ω ∈ E <;> simp [hI, hω]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hFm.aemeasurable hIm.aemeasurable
  have e2 : ∫⁻ ω, F ω ^ (2 : ℝ) ∂μ = ∫⁻ ω, ENNReal.ofReal (g ω ^ (2 * p)) ∂μ := by
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.rpow_two, hF]
    show ENNReal.ofReal (g ω ^ p) ^ 2 = _
    rw [← ENNReal.ofReal_pow (pow_nonneg (hg0 ω) p), ← pow_mul, mul_comm p 2]
  have e3 : ∫⁻ ω, I ω ^ (2 : ℝ) ∂μ = μ E := by
    have e4 : (fun ω => I ω ^ (2 : ℝ)) = I := by
      funext ω
      by_cases hω : ω ∈ E <;> simp [hI, hω]
    rw [e4, hI]
    exact lintegral_indicator_one hE
  have s1 : ∀ {w : ℝ}, 0 ≤ w → ENNReal.ofReal (w ^ 2) ^ (1 / (2 : ℝ)) = ENNReal.ofReal w := by
    intro w hw
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow, Real.sqrt_sq hw]
  rw [e1]
  calc ∫⁻ ω, (F * I) ω ∂μ ≤ (∫⁻ ω, F ω ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫⁻ ω, I ω ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hH
    _ ≤ ENNReal.ofReal (M ^ 2) ^ (1 / (2 : ℝ)) * ENNReal.ofReal (t ^ 2) ^ (1 / (2 : ℝ)) := by
      rw [e2, e3]
      gcongr
    _ = ENNReal.ofReal (M * t) := by
      rw [s1 hM, s1 ht, ENNReal.ofReal_mul hM]
private theorem lintegral_pow_le_of_windows (μ : Measure Ω) (d : Ω → ℕ) (l : ℕ → ℕ) (g : ℕ → Ω → ℝ) (f : Ω → ℝ)
    (a₀ a₁ p : ℕ) (hal : a₀ ≤ a₁) (hg : ∀ a, Measurable (g a)) (hf0 : ∀ ω, 0 ≤ f ω)
    (hdeep : ∀ a, a₀ ≤ a → a ≤ a₁ → ∀ ω, 8 * d ω ≤ l a → f ω ≤ g a ω)
    (htop : ∀ ω, f ω ≤ g (a₁ + 1) ω) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ ≤ ∫⁻ ω, ENNReal.ofReal (g a₀ ω ^ p) ∂μ +
      ∑ a ∈ Finset.Ico a₀ (a₁ + 1), ∫⁻ ω, (toMeasurable μ {ω | l a < 8 * d ω}).indicator
        (fun ω => ENNReal.ofReal (g (a + 1) ω ^ p)) ω ∂μ := by
  have hF : ∀ a, Measurable fun ω => ENNReal.ofReal (g a ω ^ p) := fun a => ((hg a).pow_const p).ennreal_ofReal
  have hmono : ∀ a ω, f ω ≤ g a ω → ENNReal.ofReal (f ω ^ p) ≤ ENNReal.ofReal (g a ω ^ p) := fun a ω h =>
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hf0 ω) h p)
  have hpt : ∀ ω, ENNReal.ofReal (f ω ^ p) ≤ ENNReal.ofReal (g a₀ ω ^ p) +
      ∑ a ∈ Finset.Ico a₀ (a₁ + 1), (toMeasurable μ {ω | l a < 8 * d ω}).indicator
        (fun ω => ENNReal.ofReal (g (a + 1) ω ^ p)) ω := by
    intro ω
    by_cases h0 : 8 * d ω ≤ l a₀
    · exact (hmono a₀ ω (hdeep a₀ le_rfl hal ω h0)).trans le_self_add
    · have hex : ∃ a ∈ Finset.Ico a₀ (a₁ + 1), l a < 8 * d ω ∧ f ω ≤ g (a + 1) ω := by
        by_contra H
        push Not at H
        have hall : ∀ a, a₀ ≤ a → a ≤ a₁ → l a < 8 * d ω := by
          intro a ha
          induction a, ha using Nat.le_induction with
          | base => intro _; omega
          | succ a ha ih =>
            intro h1
            have h2 := ih (by omega)
            have h3 := H a (Finset.mem_Ico.2 ⟨ha, by omega⟩) h2
            by_contra h4
            exact absurd (hdeep (a + 1) (by omega) h1 ω (by omega)) (not_le.2 h3)
        exact absurd (htop ω) (not_le.2 (H a₁ (Finset.mem_Ico.2 ⟨hal, by omega⟩) (hall a₁ hal le_rfl)))
      obtain ⟨a, ha, h1, h2⟩ := hex
      have h3 : ω ∈ toMeasurable μ {ω | l a < 8 * d ω} := subset_toMeasurable μ _ h1
      refine le_add_left ?_
      refine le_trans ?_ (Finset.single_le_sum (f := fun a => (toMeasurable μ {ω | l a < 8 * d ω}).indicator
        (fun ω => ENNReal.ofReal (g (a + 1) ω ^ p)) ω) (fun _ _ => bot_le) ha)
      show _ ≤ (toMeasurable μ {ω | l a < 8 * d ω}).indicator (fun ω => ENNReal.ofReal (g (a + 1) ω ^ p)) ω
      rw [Set.indicator_of_mem h3]
      exact hmono _ ω h2
  have hI : ∀ a, Measurable ((toMeasurable μ {ω | l a < 8 * d ω}).indicator
      (fun ω => ENNReal.ofReal (g (a + 1) ω ^ p))) := fun a => (hF (a + 1)).indicator (measurableSet_toMeasurable _ _)
  calc ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal (g a₀ ω ^ p) + ∑ a ∈ Finset.Ico a₀ (a₁ + 1),
          (toMeasurable μ {ω | l a < 8 * d ω}).indicator (fun ω => ENNReal.ofReal (g (a + 1) ω ^ p)) ω) ∂μ :=
        lintegral_mono hpt
    _ = _ := by
        rw [lintegral_add_left (hF a₀), lintegral_finsetSum _ fun a _ => hI a]
private theorem sum_pow_mul_exp_neg_le {Lr c : ℝ} (hL : 2 ≤ Lr) (hc : 0 < c) (N a₀ a₁ : ℕ) :
    ∑ a ∈ Finset.Ico a₀ a₁, (Lr ^ a) ^ N * Real.exp (-c * Lr ^ a) ≤
      2 * (((N + 1).factorial : ℝ) / c ^ (N + 1)) := by
  set D : ℝ := ((N + 1).factorial : ℝ) / c ^ (N + 1) with hD
  have hD0 : 0 ≤ D := by positivity
  have hterm : ∀ a : ℕ, (Lr ^ a) ^ N * Real.exp (-c * Lr ^ a) ≤ D * (1 / 2 : ℝ) ^ a := by
    intro a
    have hw2 : (2 : ℝ) ^ a ≤ Lr ^ a := pow_le_pow_left₀ (by norm_num) hL a
    have hw0 : 0 < Lr ^ a := by positivity
    set w : ℝ := Lr ^ a with hw
    have h1 := Real.pow_div_factorial_le_exp (x := c * w) (by positivity) (N + 1)
    have h2 : w ^ (N + 1) ≤ D * Real.exp (c * w) := by
      rw [hD, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity), mul_pow] at h1
      nlinarith
    have h3 : w ^ N * Real.exp (-c * w) * w ≤ D := by
      have h4 : Real.exp (-c * w) * Real.exp (c * w) = 1 := by
        rw [← Real.exp_add]
        simp
      calc w ^ N * Real.exp (-c * w) * w = w ^ (N + 1) * Real.exp (-c * w) := by ring
        _ ≤ D * Real.exp (c * w) * Real.exp (-c * w) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = D * (Real.exp (-c * w) * Real.exp (c * w)) := by ring
        _ = D := by rw [h4, mul_one]
    have h5 : (1 / 2 : ℝ) ^ a * 2 ^ a = 1 := by
      rw [← mul_pow]
      norm_num
    have h6 : 0 ≤ w ^ N * Real.exp (-c * w) := by positivity
    calc w ^ N * Real.exp (-c * w) = w ^ N * Real.exp (-c * w) * ((1 / 2 : ℝ) ^ a * 2 ^ a) := by
          rw [h5, mul_one]
      _ ≤ w ^ N * Real.exp (-c * w) * ((1 / 2 : ℝ) ^ a * w) := by
          refine mul_le_mul_of_nonneg_left ?_ h6
          exact mul_le_mul_of_nonneg_left hw2 (by positivity)
      _ = (w ^ N * Real.exp (-c * w) * w) * (1 / 2 : ℝ) ^ a := by ring
      _ ≤ D * (1 / 2 : ℝ) ^ a := mul_le_mul_of_nonneg_right h3 (by positivity)
  calc ∑ a ∈ Finset.Ico a₀ a₁, (Lr ^ a) ^ N * Real.exp (-c * Lr ^ a)
      ≤ ∑ a ∈ Finset.Ico a₀ a₁, D * (1 / 2 : ℝ) ^ a := Finset.sum_le_sum fun a _ => hterm a
    _ ≤ ∑ a ∈ Finset.range a₁, D * (1 / 2 : ℝ) ^ a := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro a ha
        exact Finset.mem_range.2 (Finset.mem_Ico.1 ha).2
    _ = D * ∑ a ∈ Finset.range a₁, (1 / 2 : ℝ) ^ a := by rw [Finset.mul_sum]
    _ ≤ D * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le a₁) hD0
    _ = 2 * D := by ring
end Measures
section Sites
variable {n : ℕ} [NeZero n]
open Classical in
private theorem chainComponents_pairwiseDisjoint {r : ℕ} {Y : Finset (TorusSite n)} {P : Finset (Finset (TorusSite n))}
    (hP : P ⊆ chainComponents r Y) : (P : Set (Finset (TorusSite n))).PairwiseDisjoint id := by
  intro X hX X' hX' hne
  show Disjoint X X'
  rw [Finset.disjoint_left]
  intro z hz hz'
  exact hne (eq_of_chainConnected_of_mem_chainComponents (hP hX) (hP hX') hz hz' Relation.ReflTransGen.refl)
open Classical in
private theorem sum_chainComponents_le {r : ℕ} {Y H : Finset (TorusSite n)} {P : Finset (Finset (TorusSite n))}
    (hP : P ⊆ chainComponents r Y) (hH : ∀ X ∈ P, X ⊆ H) (f : TorusSite n → ℝ) (hf : ∀ z, 0 ≤ f z) :
    ∑ X ∈ P, ∑ y ∈ X, f y ≤ ∑ y ∈ H, f y := by
  have e := Finset.sum_biUnion (s := P) (t := id) (f := f) (chainComponents_pairwiseDisjoint hP)
  simp only [id] at e
  rw [← e]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun z _ _ => hf z
  intro z hz
  obtain ⟨X, hX, hzX⟩ := Finset.mem_biUnion.1 hz
  exact hH X hX hzX
private def gridCentredAt (l : ℕ) (y₀ : TorusSite n) : CellGrid :=
  ⟨l, fun i => (((y₀ i).val : ℕ) : ℤ) - ((l : ℤ) - 1) / 2⟩
private theorem mem_gridCentredAt_cell {l : ℕ} (hl : 1 ≤ l) {y₀ v : TorusSite n} (h : supDist v y₀ ≤ (l - 1) / 2) :
    v ∈ (gridCentredAt l y₀).cell n 0 := by
  classical
  have hb : ∀ i, ((v i - y₀ i).valMinAbs).natAbs ≤ (l - 1) / 2 := fun i =>
    le_trans (Finset.le_sup (f := fun i => ((v i - y₀ i).valMinAbs).natAbs) (Finset.mem_univ i)) h
  simp only [CellGrid.cell, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun i => (v i - y₀ i).valMinAbs + ((l : ℤ) - 1) / 2, fun i => ?_, ?_⟩
  · have := hb i
    show 0 ≤ (v i - y₀ i).valMinAbs + ((l : ℤ) - 1) / 2 ∧ (v i - y₀ i).valMinAbs + ((l : ℤ) - 1) / 2 < (l : ℤ)
    omega
  · funext i
    simp only [siteOfInt, gridCentredAt, Pi.zero_apply, mul_zero, add_zero]
    push_cast
    simp only [ZMod.natCast_zmod_val]
    ring
private theorem subset_interiorAtDepth_of_near {l r D Rn : ℕ} {X : Finset (TorusSite n)} {y₀ z₀ w : TorusSite n}
    (hz₀ : z₀ ∈ X) (hw : supDist w y₀ ≤ Rn) (h1 : supDist z₀ w ≤ 1) (hd : siteDiameter X ≤ D) (hD : 8 * D ≤ l)
    (hR : 8 * Rn ≤ l) (hr : 2 ^ 7 * r ≤ l) (hl : 6 ≤ l) :
    X ⊆ interiorAtDepth (2 ^ 4 * r) ((gridCentredAt l y₀).cell n 0) := by
  classical
  intro z hz
  have hzz : supDist z z₀ ≤ D :=
    le_trans (le_trans (Finset.le_sup (f := fun z' => supDist z z') hz₀)
      (Finset.le_sup (f := fun y => X.sup fun z' => supDist y z') hz)) hd
  have tz : supDist z y₀ ≤ D + 1 + Rn := by
    have a1 := supDist_triangle z z₀ y₀
    have a2 := supDist_triangle z₀ w y₀
    omega
  simp only [interiorAtDepth, Finset.mem_filter]
  refine ⟨mem_gridCentredAt_cell (by omega) (by omega), fun v hv => ?_⟩
  by_contra hc
  apply hv
  refine mem_gridCentredAt_cell (by omega) ?_
  have a1 := supDist_triangle v z y₀
  have a2 : supDist v z = supDist z v := supDist_comm _ _
  norm_num at hc hr
  omega
end Sites
section Measurability
private theorem measurable_sigma_of_forall {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] {γ : Type}
    [MeasurableSpace γ] {f : Sigma β → γ} (h : ∀ a, Measurable fun y : β a => f ⟨a, y⟩) : Measurable f := by apply _root_.YangMills.SharedProofs.p3239 <;> assumption
private theorem measurableSet_sigma_fst_eq {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
variable {X : Type} [MeasurableSpace X]
private theorem measurableSet_eq_of_fibres₃ {A B C D : Type} [Countable A] [Countable B] [Countable C]
    {f₁ : X → A} {f₂ : X → B} {f₃ : X → C} (h₁ : ∀ a, MeasurableSet {x | f₁ x = a})
    (h₂ : ∀ a, MeasurableSet {x | f₂ x = a}) (h₃ : ∀ a, MeasurableSet {x | f₃ x = a}) (g : A → B → C → D) (d : D) :
    MeasurableSet {x | g (f₁ x) (f₂ x) (f₃ x) = d} := by
  have e : {x | g (f₁ x) (f₂ x) (f₃ x) = d} = ⋃ a, ⋃ b, ⋃ c, ⋃ (_ : g a b c = d),
      {x | f₁ x = a} ∩ ({x | f₂ x = b} ∩ {x | f₃ x = c}) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    constructor
    · intro h
      exact ⟨_, _, _, h, rfl, rfl, rfl⟩
    · rintro ⟨a, b, c, h, rfl, rfl, rfl⟩
      exact h
  rw [e]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun c =>
    MeasurableSet.iUnion fun _ => (h₁ a).inter ((h₂ b).inter (h₃ c))
private theorem measurableSet_eq_of_fibres {A D : Type} [Countable A] {f : X → A}
    (h : ∀ a, MeasurableSet {x | f x = a}) (g : A → D) (d : D) : MeasurableSet {x | g (f x) = d} := by
  have e : {x | g (f x) = d} = ⋃ a, ⋃ (_ : g a = d), {x | f x = a} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨a, h, rfl⟩
      exact h
  rw [e]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun _ => h a
abbrev _root_.YangMills.SharedProofs.p22983 := @measurableSet_eq_of_fibres
private theorem measurableSet_mem_of_fibres {A : Type} [Countable A] {f : X → Finset A}
    (h : ∀ a, MeasurableSet {x | f x = a}) (y : A) : MeasurableSet {x | y ∈ f x} := by
  have e : {x | y ∈ f x} = ⋃ a : Finset A, ⋃ (_ : y ∈ a), {x | f x = a} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨a, h, rfl⟩
      exact h
  rw [e]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun _ => h a
variable {ℓ : StepParameters}
private theorem measurable_sum_siteScore {Ωl : Type} [MeasurableSpace Ωl] {n : ℕ} [NeZero n] {s : Ωl → ℝ}
    (hs : Measurable s) :
    Measurable fun z : (Σ Y : Finset (TorusSite n), (Y → Ωl)) => ∑ y ∈ z.1, siteScore s z.1 z.2 y := by
  classical
  refine measurable_sigma_of_forall fun Y => ?_
  refine Finset.measurable_sum _ fun y _ => ?_
  by_cases hy : y ∈ Y
  · have e : (fun ω : Y → Ωl => siteScore s Y ω y) = fun ω => s (ω ⟨y, hy⟩) := by
      funext ω
      simp [siteScore, hy]
    rw [e]
    exact hs.comp (measurable_pi_apply _)
  · have e : (fun ω : Y → Ωl => siteScore s Y ω y) = fun _ => 0 := by
      funext ω
      simp [siteScore, hy]
    rw [e]
    exact measurable_const
private theorem measurable_hullMajorantSum (T : StageTower ℓ) (s₀ s₁ : ℝ) (t n : ℕ) [NeZero n]
    (hq : Measurable (stageState T t n)) (hs : Measurable (labelMajorant T s₀ s₁ t)) :
    Measurable (hullMajorantSum T s₀ s₁ t n) :=
  (measurable_sum_siteScore hs).comp (measurable_snd.comp hq)
private theorem measurableSet_stageHull_eq (T : StageTower ℓ) (t n : ℕ) [NeZero n]
    (hq : Measurable (stageState T t n)) (a : Finset (TorusSite n)) : MeasurableSet {ω | stageHull T t n ω = a} := by
  have h : MeasurableSet {z : StageState T t n | z.2.1 = a} := measurable_snd (measurableSet_sigma_fst_eq a)
  exact hq h
section LowerScores
variable (T : StageTower ℓ) (k : ℕ)
private theorem measurableSet_lowerHull_eq (hC : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (hq : ∀ (n : ℕ) [NeZero n], Measurable (stageState T 0 n)) (s : ℕ) :
    ∀ (n : ℕ) [NeZero n] (c a : Finset (TorusSite n)),
      MeasurableSet {ω : MarkedSample ℓ s n | lowerHull T k s n ω c = a} := by
  induction s with
  | zero =>
    intro n _ c a
    exact measurableSet_eq_of_fibres (measurableSet_stageHull_eq T 0 n (hq n))
      (fun Y => Y ∩ interiorAtDepth (windowDepth T k 0) c) a
  | succ s ih =>
    intro n _ c a
    have h₁ : ∀ a : Finset (TorusSite n), MeasurableSet
        {ω : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n |
          hotCoreSites (T.stage s).toStepSetup ω.2.2.1 = a} := fun a =>
      (measurable_fst.comp (measurable_snd.comp measurable_snd)) (hC (T.stage s).toStepSetup n a)
    have h₂ : ∀ a : Finset (TorusBond (n * ℓ.side)), MeasurableSet
        {ω : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n |
          (ω.2.2.2 : Finset (TorusBond (n * ℓ.side))) = a} := by
      intro a
      have hm : Measurable fun ω : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => ω.2.2.2 :=
        measurable_snd.comp (measurable_snd.comp measurable_snd)
      have hs : MeasurableSet ({a} : Set (BondSet (n * ℓ.side))) := MeasurableSpace.measurableSet_top
      exact hm hs
    have h₃ : ∀ a : Finset (TorusSite (n * ℓ.side)), MeasurableSet
        {ω : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n |
          lowerHull T k s (n * ℓ.side) ω.1 (sitesInBlocks ℓ.side c) = a} := fun a =>
      measurable_fst (ih (n * ℓ.side) (sitesInBlocks ℓ.side c) a)
    exact measurableSet_eq_of_fibres₃ h₁ h₂ h₃
      (fun C b Y => thickening (stageRange T (s + 1) / 2) (lowerZone T k s C b Y c)) a
private theorem measurable_lowerScore_at (hC : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (hq : ∀ (n : ℕ) [NeZero n], Measurable (stageState T 0 n)) (s₀ s₁ : ℝ) (s : ℕ) :
    ∀ (n : ℕ) [NeZero n] (c : Finset (TorusSite n)) (y : TorusSite n),
      Measurable fun ω : MarkedSample ℓ s n => lowerScore T k s₀ s₁ s n ω c y := by
  classical
  induction s with
  | zero =>
    intro n _ c y
    have hH := measurableSet_mem_of_fibres (measurableSet_lowerHull_eq T k hC hq 0 n c) y
    exact Measurable.ite hH measurable_const measurable_const
  | succ s ih =>
    intro n _ c y
    have hH := measurableSet_mem_of_fibres (measurableSet_lowerHull_eq T k hC hq (s + 1) n c) y
    have h₁ : ∀ a : Finset (TorusSite n), MeasurableSet
        {ω : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n |
          hotCoreSites (T.stage s).toStepSetup ω.2.2.1 = a} := fun a =>
      (measurable_fst.comp (measurable_snd.comp measurable_snd)) (hC (T.stage s).toStepSetup n a)
    have h₂ : ∀ a : Finset (TorusBond (n * ℓ.side)), MeasurableSet
        {ω : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n |
          (ω.2.2.2 : Finset (TorusBond (n * ℓ.side))) = a} := by
      intro a
      have hm : Measurable fun ω : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => ω.2.2.2 :=
        measurable_snd.comp (measurable_snd.comp measurable_snd)
      have hs : MeasurableSet ({a} : Set (BondSet (n * ℓ.side))) := MeasurableSpace.measurableSet_top
      exact hm hs
    have h₃ : ∀ a : Finset (TorusSite (n * ℓ.side)), MeasurableSet
        {ω : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n |
          lowerHull T k s (n * ℓ.side) ω.1 (sitesInBlocks ℓ.side c) = a} := fun a =>
      measurable_fst (measurableSet_lowerHull_eq T k hC hq s (n * ℓ.side) (sitesInBlocks ℓ.side c) a)
    have hZ : MeasurableSet {ω : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n |
        y ∈ lowerZone T k s (hotCoreSites (T.stage s).toStepSetup ω.2.2.1) ω.2.2.2
          (lowerHull T k s (n * ℓ.side) ω.1 (sitesInBlocks ℓ.side c)) c} :=
      measurableSet_mem_of_fibres (f := fun ω : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
        lowerZone T k s (hotCoreSites (T.stage s).toStepSetup ω.2.2.1) ω.2.2.2
          (lowerHull T k s (n * ℓ.side) ω.1 (sitesInBlocks ℓ.side c)) c)
        (fun a => measurableSet_eq_of_fibres₃ h₁ h₂ h₃ (fun C b Y => lowerZone T k s C b Y c) a) y
    have hsum : Measurable fun ω : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
        ∑ z ∈ sitesInBlocks ℓ.side {y}, lowerScore T k s₀ s₁ s (n * ℓ.side) ω.1 (sitesInBlocks ℓ.side c) z :=
      Finset.measurable_sum _ fun z _ => (ih (n * ℓ.side) (sitesInBlocks ℓ.side c) z).comp measurable_fst
    exact Measurable.ite hH (measurable_const.add (Measurable.ite hZ hsum measurable_const)) measurable_const
private theorem measurable_lowerScoreSum_at (hC : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (hq : ∀ (n : ℕ) [NeZero n], Measurable (stageState T 0 n)) (s₀ s₁ : ℝ) (s n : ℕ) [NeZero n]
    (c : Finset (TorusSite n)) : Measurable fun ω : MarkedSample ℓ s n => lowerScoreSum T k s₀ s₁ s n ω c := by
  classical
  have e : (fun ω : MarkedSample ℓ s n => lowerScoreSum T k s₀ s₁ s n ω c) = fun ω =>
      ∑ y : TorusSite n, if y ∈ lowerHull T k s n ω c then lowerScore T k s₀ s₁ s n ω c y else 0 := by
    funext ω
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    rfl
  rw [e]
  refine Finset.measurable_sum _ fun y _ => ?_
  exact Measurable.ite (measurableSet_mem_of_fibres (measurableSet_lowerHull_eq T k hC hq s n c) y)
    (measurable_lowerScore_at T k hC hq s₀ s₁ s n c y) measurable_const
end LowerScores
private theorem coarseLabelScore_mul {Ωl : Type} {L : ℕ} (c s₁ : ℝ) (s s' : Ωl → ℝ) (h : ∀ w, s' w = c * s w)
    (w : CoarseLabel Ωl L) : coarseLabelScore (L := L) (c * s₁) s' w = c * coarseLabelScore (L := L) s₁ s w := by
  cases w with
  | inl _ => rfl
  | inr st =>
    show c * s₁ + ∑ o : BlockOffset L, Sum.elim (fun _ => 0) s' (st.siteLabel o) =
      c * (s₁ + ∑ o : BlockOffset L, Sum.elim (fun _ => 0) s (st.siteLabel o))
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun o _ => ?_
    cases st.siteLabel o with
    | inl _ => simp
    | inr v => simpa using h v
private theorem labelMajorant_mul (T : StageTower ℓ) (c s₀ s₁ : ℝ) (t : ℕ) :
    ∀ w, labelMajorant T (c * s₀) (c * s₁) t w = c * labelMajorant T s₀ s₁ t w := by
  induction t with
  | zero => intro w; rfl
  | succ t ih =>
    intro w
    exact coarseLabelScore_mul c s₁ _ _ ih w
private theorem siteMajorant_mul (T : StageTower ℓ) (c s₀ s₁ : ℝ) (t n : ℕ) [NeZero n] (ω : MarkedSample ℓ t n)
    (y : TorusSite n) : siteMajorant T (c * s₀) (c * s₁) t n ω y = c * siteMajorant T s₀ s₁ t n ω y := by
  classical
  simp only [siteMajorant, siteScore]
  split_ifs with h
  · exact labelMajorant_mul T c s₀ s₁ t _
  · simp
private theorem hullMajorantSum_mul (T : StageTower ℓ) (c s₀ s₁ : ℝ) (t n : ℕ) [NeZero n] (ω : MarkedSample ℓ t n) :
    hullMajorantSum T (c * s₀) (c * s₁) t n ω = c * hullMajorantSum T s₀ s₁ t n ω := by
  simp only [hullMajorantSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => siteMajorant_mul T c s₀ s₁ t n ω y
end Measurability
section MomentBound
variable {Ω : Type} [MeasurableSpace Ω]
private theorem lintegral_pow_le_of_window_bounds (μ : Measure Ω) [IsProbabilityMeasure μ] {L b e a₀ p : ℕ}
    {K lam CR c : ℝ} (hL : 16 ≤ L) (hp : 1 ≤ p) (hK : 0 ≤ K) (hlam : 1 ≤ lam) (hCR : 0 ≤ CR) (hc : 0 < c)
    {f U : Ω → ℝ} {S : ℕ → Ω → ℝ} {d : Ω → ℕ} (hf0 : ∀ ω, 0 ≤ f ω)
    (hU : Measurable U) (hU0 : ∀ ω, 0 ≤ U ω) (hfU : ∀ ω, f ω ≤ U ω)
    (hUe : ∫⁻ ω, ENNReal.ofReal (Real.exp (U ω)) ∂μ ≤
      ENNReal.ofReal (Real.exp (K * lam * (2 * (L : ℝ) ^ e) ^ 4)))
    (hS : ∀ a, Measurable (S a)) (hS0 : ∀ a ω, 0 ≤ S a ω)
    (hSe : ∀ a, a₀ ≤ a → b + a ≤ e → ∫⁻ ω, ENNReal.ofReal (Real.exp (S a ω)) ∂μ ≤
      ENNReal.ofReal (Real.exp (K * lam * ((L : ℝ) ^ (b + a)) ^ 4)))
    (hdeep : ∀ a, a₀ ≤ a → b + a ≤ e → ∀ ω, 8 * d ω ≤ L ^ (b + a) → f ω ≤ S a ω)
    (htail : ∀ a, a₀ ≤ a → b + a ≤ e → μ {ω | L ^ (b + a) < 8 * d ω} ≤
      ENNReal.ofReal (CR * Real.exp (-(2 * c) * (L : ℝ) ^ a))) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ ≤ ENNReal.ofReal (((2 * (p : ℝ) + K) * lam * ((L : ℝ) ^ b) ^ 4) ^ p *
      ((L : ℝ) ^ (4 * (a₀ + 1) * p) + (L : ℝ) ^ (4 * p) * Real.sqrt CR *
        (2 * (((4 * p + 1).factorial : ℝ) / c ^ (4 * p + 1))))) := by
  classical
  set Lr : ℝ := (L : ℝ) with hLr
  have hL16 : (16 : ℝ) ≤ Lr := by
    rw [hLr]
    exact_mod_cast hL
  have hL1 : 1 ≤ Lr := by linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hlam0 : 0 ≤ lam := by linarith
  set Q : ℝ := (2 * (p : ℝ) + K) * lam * (Lr ^ b) ^ 4 with hQ
  set X : ℕ → ℝ := fun a => (Lr ^ b) ^ 4 * Lr ^ (4 * (a + 1)) with hX
  have hX1 : ∀ a, 1 ≤ X a := fun a =>
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (one_le_pow₀ hL1)) (one_le_pow₀ hL1)
  have hlamX : ∀ a, 1 ≤ lam * X a := fun a => one_le_mul_of_one_le_of_one_le hlam (hX1 a)
  have hq : ∀ (q : ℕ) (a : ℕ), q ≤ 2 * p → (q : ℝ) + K * lam * X a ≤ Q * Lr ^ (4 * (a + 1)) := by
    intro q a hqp
    have h1 : (q : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast hqp
    have h2 : 2 * (p : ℝ) ≤ 2 * (p : ℝ) * (lam * X a) := le_mul_of_one_le_right (by linarith) (hlamX a)
    have e : Q * Lr ^ (4 * (a + 1)) = 2 * (p : ℝ) * (lam * X a) + K * lam * X a := by
      simp only [hQ, hX]
      ring
    rw [e]
    linarith
  have hXtop : ∀ a, e ≤ b + a → (2 * Lr ^ e) ^ 4 ≤ X a := by
    intro a hea
    have h1 : (Lr ^ e) ^ 4 ≤ (Lr ^ (b + a)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 hea) 4
    have h2 : (16 : ℝ) ≤ Lr ^ 4 := by
      calc (16 : ℝ) ≤ Lr := hL16
        _ ≤ Lr ^ 4 := le_self_pow₀ hL1 (by norm_num)
    have e1 : X a = Lr ^ 4 * (Lr ^ (b + a)) ^ 4 := by
      simp only [hX]
      ring
    rw [e1, mul_pow]
    have h3 : (0 : ℝ) ≤ (Lr ^ e) ^ 4 := by positivity
    calc 2 ^ 4 * (Lr ^ e) ^ 4 ≤ Lr ^ 4 * (Lr ^ e) ^ 4 := by
          refine mul_le_mul_of_nonneg_right ?_ h3
          norm_num
          exact h2
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hKl : 0 ≤ K * lam := mul_nonneg hK hlam0
  set W₀ : ℝ := Lr ^ (4 * (a₀ + 1) * p) with hW₀
  set D : ℝ := ((4 * p + 1).factorial : ℝ) / c ^ (4 * p + 1) with hD
  set W₁ : ℝ := Lr ^ (4 * p) * Real.sqrt CR * (2 * D) with hW₁
  have hfirst : (Q * Lr ^ (4 * (a₀ + 1))) ^ p = Q ^ p * W₀ := by
    rw [mul_pow, hW₀, ← pow_mul]
  by_cases hcase : b + a₀ ≤ e
  · set a₁ : ℕ := e - b with ha₁
    have hal : a₀ ≤ a₁ := by omega
    set g : ℕ → Ω → ℝ := fun a => if a ≤ a₁ then S a else U with hg
    have hgS : ∀ a, a ≤ a₁ → g a = S a := fun a ha => by simp only [hg, if_pos ha]
    have hgU : ∀ a, ¬ a ≤ a₁ → g a = U := fun a ha => by simp only [hg, if_neg ha]
    have hgm : ∀ a, Measurable (g a) := by
      intro a
      by_cases ha : a ≤ a₁
      · rw [hgS a ha]
        exact hS a
      · rw [hgU a ha]
        exact hU
    have hg0 : ∀ a ω, 0 ≤ g a ω := by
      intro a ω
      by_cases ha : a ≤ a₁
      · rw [hgS a ha]
        exact hS0 a ω
      · rw [hgU a ha]
        exact hU0 ω
    have hdec := lintegral_pow_le_of_windows μ d (fun a => L ^ (b + a)) g f a₀ a₁ p hal hgm hf0
      (fun a h1 h2 ω h3 => by
        rw [hgS a h2]
        exact hdeep a h1 (by omega) ω h3)
      (fun ω => by
        rw [hgU (a₁ + 1) (by omega)]
        exact hfU ω)
    have hT₀ : ∫⁻ ω, ENNReal.ofReal (g a₀ ω ^ p) ∂μ ≤ ENNReal.ofReal (Q ^ p * W₀) := by
      rw [hgS a₀ hal]
      have h1 := moment_le_of_exp_moment μ (hS a₀) (hS0 a₀) (A := K * lam * (Lr ^ (b + a₀)) ^ 4)
        (mul_nonneg hKl (by positivity)) (hSe a₀ le_rfl hcase) p hp
      refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [← hfirst]
      refine pow_le_pow_left₀ (by positivity) ?_ p
      have h2 : (Lr ^ (b + a₀)) ^ 4 ≤ X a₀ := by
        have e1 : X a₀ = Lr ^ 4 * (Lr ^ (b + a₀)) ^ 4 := by
          simp only [hX]
          ring
        rw [e1]
        exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hL1)
      have h3 := hq p a₀ (by omega)
      have h4 := mul_le_mul_of_nonneg_left h2 hKl
      linarith
    have hterm : ∀ a ∈ Finset.Ico a₀ (a₁ + 1),
        ∫⁻ ω, (toMeasurable μ {ω | L ^ (b + a) < 8 * d ω}).indicator
          (fun ω => ENNReal.ofReal (g (a + 1) ω ^ p)) ω ∂μ ≤
        ENNReal.ofReal ((Q * Lr ^ (4 * (a + 1))) ^ p * (Real.sqrt CR * Real.exp (-c * Lr ^ a))) := by
      intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_Ico.1 ha
      have hexp : ∫⁻ ω, ENNReal.ofReal (Real.exp (g (a + 1) ω)) ∂μ ≤
          ENNReal.ofReal (Real.exp (K * lam * X a)) := by
        by_cases h1 : a + 1 ≤ a₁
        · rw [hgS (a + 1) h1]
          refine (hSe (a + 1) (by omega) (by omega)).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
          refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hKl
          simp only [hX]
          ring
        · rw [hgU (a + 1) h1]
          refine hUe.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
          exact mul_le_mul_of_nonneg_left (hXtop a (by omega)) hKl
      have hm := moment_le_of_exp_moment μ (hgm (a + 1)) (hg0 (a + 1)) (A := K * lam * X a)
        (mul_nonneg hKl (by linarith [hX1 a])) hexp (2 * p) (by omega)
      refine lintegral_indicator_pow_le μ (hgm (a + 1)) (hg0 (a + 1)) p (measurableSet_toMeasurable _ _)
        (by positivity) (by positivity) (hm.trans (ENNReal.ofReal_le_ofReal ?_)) ?_
      · rw [← pow_mul, mul_comm p 2]
        refine pow_le_pow_left₀ (by positivity) ?_ (2 * p)
        have := hq (2 * p) a le_rfl
        simpa using this
      · rw [measure_toMeasurable]
        refine (htail a ha1 (by omega)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
        rw [mul_pow, Real.sq_sqrt hCR, ← Real.exp_nat_mul]
        congr 2
        push_cast
        ring
    have hsum : ∑ a ∈ Finset.Ico a₀ (a₁ + 1),
        ((Q * Lr ^ (4 * (a + 1))) ^ p * (Real.sqrt CR * Real.exp (-c * Lr ^ a))) ≤ Q ^ p * W₁ := by
      have e1 : ∀ a, (Q * Lr ^ (4 * (a + 1))) ^ p * (Real.sqrt CR * Real.exp (-c * Lr ^ a)) =
          (Q ^ p * Lr ^ (4 * p) * Real.sqrt CR) * ((Lr ^ a) ^ (4 * p) * Real.exp (-c * Lr ^ a)) := by
        intro a
        have e2 : (Lr ^ (4 * (a + 1))) ^ p = Lr ^ (4 * p) * (Lr ^ a) ^ (4 * p) := by
          rw [← pow_mul, ← pow_mul, ← pow_add]
          congr 1
          ring
        rw [mul_pow, e2]
        ring
      simp only [e1, ← Finset.mul_sum]
      have h1 := sum_pow_mul_exp_neg_le (Lr := Lr) (by linarith) hc (4 * p) a₀ (a₁ + 1)
      calc _ ≤ (Q ^ p * Lr ^ (4 * p) * Real.sqrt CR) * (2 * D) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = Q ^ p * W₁ := by
            rw [hW₁]
            ring
    have hsum0 : ∀ a ∈ Finset.Ico a₀ (a₁ + 1),
        0 ≤ (Q * Lr ^ (4 * (a + 1))) ^ p * (Real.sqrt CR * Real.exp (-c * Lr ^ a)) := fun a _ => by positivity
    calc ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (g a₀ ω ^ p) ∂μ + ∑ a ∈ Finset.Ico a₀ (a₁ + 1), ∫⁻ ω,
            (toMeasurable μ {ω | L ^ (b + a) < 8 * d ω}).indicator
              (fun ω => ENNReal.ofReal (g (a + 1) ω ^ p)) ω ∂μ := hdec
      _ ≤ ENNReal.ofReal (Q ^ p * W₀) + ∑ a ∈ Finset.Ico a₀ (a₁ + 1),
            ENNReal.ofReal ((Q * Lr ^ (4 * (a + 1))) ^ p * (Real.sqrt CR * Real.exp (-c * Lr ^ a))) :=
          add_le_add hT₀ (Finset.sum_le_sum hterm)
      _ = ENNReal.ofReal (Q ^ p * W₀) + ENNReal.ofReal (∑ a ∈ Finset.Ico a₀ (a₁ + 1),
            ((Q * Lr ^ (4 * (a + 1))) ^ p * (Real.sqrt CR * Real.exp (-c * Lr ^ a)))) := by
          rw [ENNReal.ofReal_sum_of_nonneg hsum0]
      _ ≤ ENNReal.ofReal (Q ^ p * W₀) + ENNReal.ofReal (Q ^ p * W₁) := by
          gcongr
      _ = ENNReal.ofReal (Q ^ p * (W₀ + W₁)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), mul_add]
  · have h1 := moment_le_of_exp_moment μ hU hU0 (A := K * lam * (2 * Lr ^ e) ^ 4)
      (mul_nonneg hKl (by positivity)) hUe p hp
    calc ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ ≤ ∫⁻ ω, ENNReal.ofReal (U ω ^ p) ∂μ :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hf0 ω) (hfU ω) p)
      _ ≤ _ := h1
      _ ≤ ENNReal.ofReal (Q ^ p * (W₀ + W₁)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h2 : ((p : ℝ) + K * lam * (2 * Lr ^ e) ^ 4) ^ p ≤ Q ^ p * W₀ := by
            rw [← hfirst]
            refine pow_le_pow_left₀ (by positivity) ?_ p
            have h3 := hq p a₀ (by omega)
            have h4 := mul_le_mul_of_nonneg_left (hXtop a₀ (by omega)) hKl
            linarith
          have h3 : 0 ≤ Q ^ p * W₁ := by positivity
          rw [mul_add]
          linarith
private theorem add_mul_le_of_abs_add_le {D₁ D₂ K lam V : ℝ} (hK : |D₁| + |D₂| ≤ K) (hlam : 1 ≤ lam) (hV : 0 ≤ V) :
    (D₁ + D₂ * lam) * V ≤ K * lam * V := by
  refine mul_le_mul_of_nonneg_right ?_ hV
  have h1 : D₁ ≤ |D₁| * lam :=
    (le_abs_self D₁).trans (le_mul_of_one_le_right (abs_nonneg _) hlam)
  have h2 : D₂ * lam ≤ |D₂| * lam := mul_le_mul_of_nonneg_right (le_abs_self D₂) (by linarith)
  have h3 : (|D₁| + |D₂|) * lam ≤ K * lam := mul_le_mul_of_nonneg_right hK (by linarith)
  nlinarith
private theorem mul_exp_le_abs_mul_exp {CR x y A₀ c w l0 M : ℝ} (hA : 0 < A₀) (hxy : y ≤ x) (hy : 0 < y)
    (hw : 0 < w) (hl0 : 0 < l0) (hM : l0 * w ≤ 16 * M) (hc : c = y * A₀ / 10240) :
    CR * Real.exp (-(x * A₀) * (M / (320 * l0))) ≤ |CR| * Real.exp (-(2 * c) * w) := by
  have htw : w / 5120 ≤ M / (320 * l0) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hx1 : y * A₀ * (w / 5120) ≤ x * A₀ * (M / (320 * l0)) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hxy hA.le) htw (by positivity)
      (mul_nonneg (by linarith) hA.le)
  have e2 : -(2 * c) * w = -(y * A₀ * (w / 5120)) := by
    rw [hc]
    ring
  rw [e2]
  calc CR * Real.exp (-(x * A₀) * (M / (320 * l0))) ≤ |CR| * Real.exp (-(x * A₀) * (M / (320 * l0))) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (abs_nonneg _)
end MomentBound
set_option maxHeartbeats 2000000 in
theorem majorantNearBoxMoments_holds (hL : longHullsRareStatement) (hS : majorantExpMomentStatement)
    (hM : lowerScoreMomentStatement) (hD : deepComponentsInLowerHullStatement)
    (hB : lowerScoreLeMajorantStatement) (hQ : StageStatesMeasurableStatement)
    (hW : chainMeasurabilityStatement) : majorantNearBoxMomentsStatement := by
  classical
  intro a ha
  obtain ⟨L₁, r₁, hr₁, h₁⟩ := hL a ha
  obtain ⟨L₂, r₂, C₂, hr₂, h₂⟩ := hS a ha
  obtain ⟨L₃, r₃, C₃, hr₃, h₃⟩ := hM a ha
  obtain ⟨L₄, r₄, hr₄, h₄⟩ := hD a ha
  refine ⟨max L₁ (max L₂ (max L₃ L₄)), fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (r₄ c))), max C₂ C₃,
    fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (lt_min (hr₃ c) (hr₄ c))), ?_⟩
  intro L hLodd hLge Tb hTa hTL hDr hCold hHalf hrt hCder C s₁ hC0 hs₁0
  obtain ⟨y₁, g₁⟩ := h₁ L hLodd ((le_max_left _ _).trans hLge) Tb hTa hTL hDr (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, g₂⟩ := h₂ L hLodd (((le_max_left _ _).trans (le_max_right _ _)).trans hLge) Tb hTa hTL hDr hCold hHalf
    (hrt.trans ((min_le_left _ _).trans' (min_le_right _ _))) ((le_max_left _ _).trans hCder) (16 * C) (16 * s₁)
    (by positivity) (by positivity)
  obtain ⟨y₃, g₃⟩ := h₃ L hLodd (((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hLge)
    Tb hTa hTL hDr hCold hHalf
    (hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    ((le_max_right _ _).trans hCder) C s₁ hC0 hs₁0
  obtain ⟨y₄, g₄⟩ := h₄ L hLodd (((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hLge)
    Tb hTa hTL hDr (hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨max y₁ (max y₂ (max y₃ (max y₄ Tb.floorMin))), fun y hy hRet hWil => ?_⟩
  have hy₁ : y₁ ≤ y := (le_max_left _ _).trans hy
  have hy₂ : y₂ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy₃ : y₃ ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have hy₄ : y₄ ≤ y :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hy
  have hy₅ : Tb.floorMin ≤ y :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hy
  have G₁ := g₁ y hy₁ hRet hWil
  obtain ⟨D₁, D₂, G₂⟩ := g₂ y hy₂ hRet hWil
  obtain ⟨E₁, E₂, G₃⟩ := g₃ y hy₃ hRet hWil
  have G₄ := g₄ y hy₄ hRet hWil
  have hfit : (Tb.stepParameters y).Admissible := hDr.fits y hy₅
  have hy3 : (3 : ℝ) ≤ y := by
    have h1 : (2 : ℝ) ^ 1600 ≤ Tb.floorMin := le_max_right _ _
    have h2 : (3 : ℝ) ≤ 2 ^ 1600 :=
      calc (3 : ℝ) ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ 1600 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    exact (h2.trans h1).trans hy₅
  have hLbig : 2 ^ 16 ≤ (Tb.stepParameters y).side := hfit.L_ge
  intro R p hR hp
  obtain ⟨CR, Gt⟩ := G₁ R hR
  have hκ₁ : 0 < Tb.κ₁ := hfit.κ₁_pos
  have hσ : 0 < Tb.threshold := hfit.σ_pos
  set A₀ : ℝ := Tb.κ₁ * Tb.threshold ^ 2 / 2 ^ 5 with hA₀
  have hA₀0 : 0 < A₀ := by positivity
  set c : ℝ := y * A₀ / 10240 with hc
  have hy0 : 0 < y := by linarith
  have hc0 : 0 < c := by positivity
  set Rn : ℕ := ⌈R⌉₊ with hRn
  set K : ℝ := |D₁| + |D₂| + |E₁| + |E₂| with hK
  have hK0 : 0 ≤ K := by positivity
  have hKD : |D₁| + |D₂| ≤ K := by
    have := abs_nonneg E₁
    have := abs_nonneg E₂
    simp only [hK]
    linarith
  have hKE : |E₁| + |E₂| ≤ K := by
    have := abs_nonneg D₁
    have := abs_nonneg D₂
    simp only [hK]
    linarith
  set Lr : ℝ := ((Tb.stepParameters y).side : ℝ) with hLr
  have hLr1 : 1 ≤ Lr := by
    rw [hLr]
    exact_mod_cast (by omega : 1 ≤ (Tb.stepParameters y).side)
  set W : ℝ := Lr ^ (4 * (Rn + 1 + 1) * p) + Lr ^ (4 * p) * Real.sqrt |CR| *
    (2 * (((4 * p + 1).factorial : ℝ) / c ^ (4 * p + 1))) with hWdef
  have hW0 : 0 ≤ W := by positivity
  set A₁ : ℝ := (2 * (p : ℝ) + K) * (2 ^ 28 * Lr ^ 4) with hA₁
  have hA₁0 : 0 ≤ A₁ := by positivity
  have main : ∀ (T : StageTower (Tb.stepParameters y)) (β s₀ : ℝ) (k : ℕ), IsTowerAtParametersMeasurable Tb y T β k →
      0 ≤ s₀ → s₀ ≤ C * (clusterRange β : ℝ) ^ 4 → PaysMajorant Tb y T (16 * s₀) (16 * s₁) k →
      ∀ (e : ℕ), (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ 2 * (Tb.stepParameters y).side ^ e →
      ∀ y₀ : TorusSite (2 * (Tb.stepParameters y).side ^ e),
        ∫⁻ ω, ENNReal.ofReal (majorantNearBox T s₀ s₁ k _ ω y₀ R ^ p)
            ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ e)) ≤
          ENNReal.ofReal (A₁ ^ p * W * ((stageRange T k : ℝ) ^ 4 * Real.log (T.stage k).coupling) ^ p) := by
    intro T β s₀ k hT h0 h1 hcar e he
    have hcut : ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn := by
      have h2 : T.base.barrierFn = Tb.cutoff := (hT.onFamily.onFamily 0 (by omega)).barrierFn_eq
      rw [h2]
      exact hDr.cut
    have hxy : y ≤ (T.stage k).coupling := (hT.onFamily.onFamily k le_rfl).le_coupling
    set x : ℝ := (T.stage k).coupling with hx
    have hx0 : 0 < x := by linarith
    have hlam : 1 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0]
      have := Real.exp_one_lt_d9
      linarith
    set r : ℕ := stageRange T k with hr
    have hr1 : 1 ≤ r := by
      have h2 : 0 < x ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos hx0 _
      exact Nat.ceil_pos.2 h2
    set L : ℕ := (Tb.stepParameters y).side with hLdef
    have hL1 : 1 < L := by omega
    set b : ℕ := Nat.clog L (2 ^ 7 * r) with hb
    have hcell : baseCellSide L r = L ^ b := rfl
    have hlow : 2 ^ 7 * r ≤ L ^ b := Nat.le_pow_clog hL1 _
    have hup : L ^ b ≤ L * (2 ^ 7 * r) := by
      have hb0 : 0 < b := Nat.clog_pos hL1 (by omega)
      have h2 := Nat.pow_pred_clog_lt_self hL1 (x := 2 ^ 7 * r) (by omega)
      have h3 : L ^ b = L * L ^ b.pred := by
        conv_lhs => rw [← Nat.succ_pred_eq_of_pos hb0]
        rw [pow_succ, mul_comm]
      rw [h3]
      exact Nat.mul_le_mul_left L h2.le
    set n : ℕ := 2 * L ^ e with hn
    intro y₀
    have hprob : IsProbabilityMeasure (markedSampleLaw T β k n) :=
      (hW.2.2 (Tb.stepParameters y) hfit hfit.depth_lt T hcut hT.measurable β k n).1
    have hmaj : ∀ (ω : MarkedSample (Tb.stepParameters y) k n) (c' : Finset (TorusSite n)) (z : TorusSite n),
        0 ≤ lowerScore T k s₀ s₁ k n ω c' z ∧ lowerScore T k s₀ s₁ k n ω c' z ≤ siteMajorant T s₀ s₁ k n ω z :=
      fun ω c' z => (hB (Tb.stepParameters y) T k s₀ s₁ h0 hs₁0 k n ω c').1 z
    have hmaj0 : ∀ ω z, 0 ≤ siteMajorant T s₀ s₁ k n ω z := fun ω z =>
      (hmaj ω ∅ z).1.trans (hmaj ω ∅ z).2
    have hfT : ∀ ω, majorantNearBox T s₀ s₁ k n ω y₀ R ≤ hullMajorantSum T s₀ s₁ k n ω := fun ω =>
      sum_chainComponents_le (r := stageRange T k) (Y := stageHull T k n ω) (H := stageHull T k n ω)
        (Finset.filter_subset _ _) (fun X hX => subset_of_mem_chainComponents (Finset.mem_filter.1 hX).1) _ (hmaj0 ω)
    have hT0 : ∀ ω, 0 ≤ hullMajorantSum T s₀ s₁ k n ω := fun ω => Finset.sum_nonneg fun z _ => hmaj0 ω z
    have hf0 : ∀ ω, 0 ≤ majorantNearBox T s₀ s₁ k n ω y₀ R := fun ω =>
      Finset.sum_nonneg fun X _ => Finset.sum_nonneg fun z _ => hmaj0 ω z
    have hq0 : ∀ (m : ℕ) [NeZero m], Measurable (stageState T 0 m) := fun m _ => hQ _ hfit T 0 m
    have hLpos : 0 < L := by omega
    have hle : ∀ a, b + a ≤ e → 2 * L ^ (b + a) ≤ n := fun a hae =>
      Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hLpos hae)
    have hidx : ∀ a, b + a ≤ e → (0 : Fin 4 → ℤ) ∈ (gridCentredAt (L ^ (b + a)) y₀).indices n := by
      intro a hae
      have h2 : 0 < n / L ^ (b + a) := Nat.div_pos (by have := hle a hae; omega) (pow_pos hLpos _)
      simp only [CellGrid.indices, Fintype.mem_piFinset, Finset.mem_Ico]
      intro i
      refine ⟨le_rfl, ?_⟩
      show (0 : ℤ) < ((n / L ^ (b + a) : ℕ) : ℤ)
      exact_mod_cast h2
    have hbig : ∀ a, Rn + 1 ≤ a → 8 * Rn ≤ L ^ (b + a) ∧ 2 ^ 7 * r ≤ L ^ (b + a) ∧ 6 ≤ L ^ (b + a) := by
      intro a ha
      have h2 : L ^ (Rn + 1) ≤ L ^ (b + a) := Nat.pow_le_pow_right hLpos (by omega)
      have h3 : Rn < L ^ Rn := Nat.lt_pow_self hL1
      have h4 : L ^ (Rn + 1) = L ^ Rn * L := pow_succ _ _
      have h5 : (Rn + 1) * 16 ≤ L ^ Rn * L := Nat.mul_le_mul h3 (by omega)
      have h6 : L ^ b ≤ L ^ (b + a) := Nat.pow_le_pow_right hLpos (by omega)
      omega
    have key := lintegral_pow_le_of_window_bounds (markedSampleLaw T β k n) (L := L) (b := b) (e := e)
      (a₀ := Rn + 1) (p := p) (K := K) (lam := Real.log x) (CR := |CR|) (c := c) (by omega) hp hK0 hlam
      (abs_nonneg _) hc0
      (f := fun ω => majorantNearBox T s₀ s₁ k n ω y₀ R)
      (U := hullMajorantSum T (16 * s₀) (16 * s₁) k n)
      (S := fun a ω => lowerScoreSum T k s₀ s₁ k n ω ((gridCentredAt (L ^ (b + a)) y₀).cell n 0))
      (d := fun ω => maxDiameterNearBox T k n ω y₀ R)
      hf0
      (measurable_hullMajorantSum T _ _ k n (hQ _ hfit T k n) (hcar k le_rfl).borel)
      (fun ω => by
        rw [hullMajorantSum_mul]
        have := hT0 ω
        positivity)
      (fun ω => by
        rw [hullMajorantSum_mul]
        have h2 := hT0 ω
        have h3 := hfT ω
        linarith)
      (by
        have h2 := G₂ T β (16 * s₀) k hT (by positivity) (by nlinarith) hcar e he
        refine h2.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
        exact add_mul_le_of_abs_add_le hKD hlam (by positivity))
      (fun a => measurable_lowerScoreSum_at T k hW.1 hq0 s₀ s₁ k n _)
      (fun a ω => Finset.sum_nonneg fun z _ => (hmaj ω _ z).1)
      (fun a ha hae => by
        have hs1 : (gridCentredAt (L ^ (b + a)) y₀).side = baseCellSide L r * L ^ a := by
          show L ^ (b + a) = L ^ b * L ^ a
          exact pow_add _ _ _
        have hs2 : 2 * (gridCentredAt (L ^ (b + a)) y₀).side ≤ n := hle a hae
        have hκ : (0 : Fin 4 → ℤ) ∈ (gridCentredAt (L ^ (b + a)) y₀).indices n := hidx a hae
        have h2 := (G₃ T β s₀ k hT h0 h1 hcar e a (gridCentredAt (L ^ (b + a)) y₀) 0 hs1 hs2 hκ).1
        refine h2.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
        have hcast : (((gridCentredAt (L ^ (b + a)) y₀).side : ℕ) : ℝ) = (L : ℝ) ^ (b + a) := by
          show ((L ^ (b + a) : ℕ) : ℝ) = _
          push_cast
          rfl
        rw [hcast]
        exact add_mul_le_of_abs_add_le hKE hlam (by positivity))
      (fun a ha hae ω hd => by
        have hfG : (gridCentredAt (L ^ (b + a)) y₀).Compatible n :=
          ⟨pow_pos hLpos _, Nat.mul_dvd_mul_left 2 (pow_dvd_pow L hae)⟩
        obtain ⟨hR8, hr7, hl6⟩ := hbig a ha
        have hprops : ∀ X ∈ componentsNearBox T k n ω y₀ R,
            X ⊆ lowerHull T k k n ω ((gridCentredAt (L ^ (b + a)) y₀).cell n 0) ∧
            ∀ z ∈ X, lowerScore T k s₀ s₁ k n ω ((gridCentredAt (L ^ (b + a)) y₀).cell n 0) z =
              siteMajorant T s₀ s₁ k n ω z := by
          intro X hX
          obtain ⟨hXc, z₀, hz₀, w, hw, hzw⟩ := Finset.mem_filter.1 hX
          have hw' : supDist w y₀ ≤ Rn := by
            have h2 : (supDist w y₀ : ℝ) ≤ (Rn : ℝ) := hw.trans (Nat.le_ceil R)
            exact_mod_cast h2
          have hdX : X ⊆ interiorAtDepth (2 ^ 4 * r) ((gridCentredAt (L ^ (b + a)) y₀).cell n 0) :=
            subset_interiorAtDepth_of_near hz₀ hw' hzw (Finset.le_sup (f := siteDiameter) hX) hd hR8 hr7 hl6
          have h2 := G₄ T β k hT k 0 rfl n ω (gridCentredAt (L ^ (b + a)) y₀) 0 hfG X hXc hdX
          exact ⟨h2.1, fun z hz => h2.2 s₀ s₁ z hz⟩
        show majorantNearBox T s₀ s₁ k n ω y₀ R ≤
          lowerScoreSum T k s₀ s₁ k n ω ((gridCentredAt (L ^ (b + a)) y₀).cell n 0)
        calc majorantNearBox T s₀ s₁ k n ω y₀ R
            = ∑ X ∈ componentsNearBox T k n ω y₀ R, ∑ z ∈ X,
                lowerScore T k s₀ s₁ k n ω ((gridCentredAt (L ^ (b + a)) y₀).cell n 0) z :=
              Finset.sum_congr rfl fun X hX => Finset.sum_congr rfl fun z hz => ((hprops X hX).2 z hz).symm
          _ ≤ _ := sum_chainComponents_le (r := stageRange T k) (Y := stageHull T k n ω) (Finset.filter_subset _ _)
              (fun X hX => (hprops X hX).1) _ fun z => (hmaj ω _ z).1)
      (fun a ha hae => by
        set m : ℕ := L ^ (b + a) / 8 with hm
        have hsub : {ω | L ^ (b + a) < 8 * maxDiameterNearBox T k n ω y₀ R} ⊆
            {ω | m < maxDiameterNearBox T k n ω y₀ R} := fun ω hω => by
          have h2 : L ^ (b + a) < 8 * maxDiameterNearBox T k n ω y₀ R := hω
          show m < _
          omega
        have hLa : L ≤ L ^ a := Nat.le_self_pow (by omega) L
        have hmul : L ^ (b + a) = L ^ b * L ^ a := pow_add _ _ _
        have hb8 : L ^ b * 16 ≤ L ^ (b + a) := by
          rw [hmul]
          exact Nat.mul_le_mul_left _ (by omega)
        have hb1 : 1 ≤ L ^ b := Nat.one_le_pow _ _ hLpos
        have hc1 : baseCellSide L r ≤ m := by
          rw [hcell, hm, Nat.le_div_iff_mul_le (by norm_num)]
          omega
        have hle0 : 2 * baseCellSide L r ≤ n := by
          rw [hcell]
          exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hLpos (by omega))
        have h2 := Gt T β k hT e hle0 y₀ m hc1
        refine (measure_mono hsub).trans (h2.trans (ENNReal.ofReal_le_ofReal ?_))
        have hm16 : L ^ (b + a) ≤ 16 * m := by omega
        set w : ℝ := (L : ℝ) ^ a with hw
        set l0 : ℝ := ((baseCellSide L r : ℕ) : ℝ) with hl0
        have hl0e : l0 = (L : ℝ) ^ b := by
          rw [hl0, hcell]
          push_cast
          rfl
        have hw0 : 0 < w := by
          have : (0 : ℝ) < L := by exact_mod_cast hLpos
          positivity
        have hl00 : 0 < l0 := by
          rw [hl0e]
          have : (0 : ℝ) < L := by exact_mod_cast hLpos
          positivity
        have hm16r : l0 * w ≤ 16 * (m : ℝ) := by
          rw [hl0e, hw, ← pow_add]
          exact_mod_cast hm16
        have e1 : cellEventBound Tb x ^ ((m : ℝ) / (320 * l0)) =
            Real.exp (-(x * A₀) * ((m : ℝ) / (320 * l0))) := by
          rw [cellEventBound, ← Real.exp_mul]
          congr 2
          simp only [hA₀]
          ring
        rw [e1]
        exact mul_exp_le_abs_mul_exp hA₀0 hxy hy0 hw0 hl00 hm16r hc)
    refine key.trans (ENNReal.ofReal_le_ofReal ?_)
    have hLr0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
    have hupr : (L : ℝ) ^ b ≤ (L : ℝ) * (2 ^ 7 * (r : ℝ)) := by exact_mod_cast hup
    have hpow4 : ((L : ℝ) ^ b) ^ 4 ≤ 2 ^ 28 * (L : ℝ) ^ 4 * (r : ℝ) ^ 4 := by
      calc ((L : ℝ) ^ b) ^ 4 ≤ ((L : ℝ) * (2 ^ 7 * (r : ℝ))) ^ 4 := pow_le_pow_left₀ (by positivity) hupr 4
        _ = _ := by ring
    have hlam0 : 0 ≤ Real.log x := by linarith
    have hpK : 0 ≤ 2 * (p : ℝ) + K := by positivity
    have hQle : (2 * (p : ℝ) + K) * Real.log x * ((L : ℝ) ^ b) ^ 4 ≤ A₁ * ((r : ℝ) ^ 4 * Real.log x) := by
      calc (2 * (p : ℝ) + K) * Real.log x * ((L : ℝ) ^ b) ^ 4
          ≤ (2 * (p : ℝ) + K) * Real.log x * (2 ^ 28 * (L : ℝ) ^ 4 * (r : ℝ) ^ 4) :=
            mul_le_mul_of_nonneg_left hpow4 (mul_nonneg hpK hlam0)
        _ = _ := by
            simp only [hA₁, hLr]
            ring
    calc ((2 * (p : ℝ) + K) * Real.log x * ((L : ℝ) ^ b) ^ 4) ^ p * W
        ≤ (A₁ * ((r : ℝ) ^ 4 * Real.log x)) ^ p * W :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hQle p) hW0
      _ = A₁ ^ p * W * ((r : ℝ) ^ 4 * Real.log x) ^ p := by
          rw [mul_pow]
          ring
  refine ⟨A₁ ^ p * W, main, fun Ξ => ⟨A₁ ^ p * W * ((clusterRange Ξ : ℝ) ^ 4 * Real.log Ξ) ^ p, ?_⟩⟩
  intro T β s₀ k hT hxΞ h0 h1 hcar e he y₀
  refine (main T β s₀ k hT h0 h1 hcar e he y₀).trans (ENNReal.ofReal_le_ofReal ?_)
  have hxy : y ≤ (T.stage k).coupling := (hT.onFamily.onFamily k le_rfl).le_coupling
  have hx0 : 0 < (T.stage k).coupling := by linarith
  have hlog0 : 0 ≤ Real.log (T.stage k).coupling := Real.log_nonneg (by linarith)
  have hlog : Real.log (T.stage k).coupling ≤ Real.log Ξ := Real.log_le_log hx0 hxΞ
  have hrng : (stageRange T k : ℝ) ≤ (clusterRange Ξ : ℝ) := by
    have h2 : stageRange T k ≤ clusterRange Ξ :=
      Nat.ceil_mono (Real.rpow_le_rpow hx0.le hxΞ (by norm_num))
    exact_mod_cast h2
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ p) (by positivity)
  exact mul_le_mul (pow_le_pow_left₀ (by positivity) hrng 4) hlog hlog0 (by positivity)
end YangMills.Construction.CellWindows.NearBoxMoments
end
