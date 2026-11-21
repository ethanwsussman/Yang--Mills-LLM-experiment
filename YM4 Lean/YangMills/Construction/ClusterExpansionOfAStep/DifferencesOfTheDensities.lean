import YangMills.Construction.ClusterExpansionOfAStep.AdmissionReadsVOnItsHullProof
import YangMills.Construction.ClusterExpansionOfAStep.DensitiesAlongMoves
import YangMills.Construction.ClusterExpansionOfAStep.ExponentialSumsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages TorusFields FieldMoves StepSettings TorusLumps ExponentialSums ColdStepAtMirrorFrames
variable {R : StepSetup} {n : ℕ} [NeZero n] {s : ChartSetting R n}
theorem TorusFields.two_mul_supDist_le {m : ℕ} [NeZero m] (x y : TorusSite m) : 2 * supDist x y ≤ m := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.two_mul_supDist_le <;> assumption
theorem TorusFields.supDist_add_le_of_offsetInBox {m : ℕ} [NeZero m] (y : TorusSite m) {v : Fin 4 → ℤ} {k : ℕ}
    (hb : OffsetInBox k v) : supDist y (y + siteOfInt v) ≤ k := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.supDist_add_le_of_inBox <;> assumption
theorem StepSettings.ChartSetting.Hypotheses.clusterFactor_ne_zero (h : s.Hypotheses) {θ : ℝ}
    {W : TorusField (n * R.params.side)} (hg : s.IsNear θ W) :
    ∀ X ∈ chainComponents (clusterRange R.coupling) s.support,
      R.clusterFactor (n * R.params.side) W s.support s.labelling X ≠ 0 := fun X hX => by
  rw [hg.clusterFactor_eq h hX]
  exact h.clusterFactor_fine_ne_zero hX
theorem StepSettings.ChartSetting.Hypotheses.abs_siteDensity_sub_le_of_agree (h : s.Hypotheses) {θ θ' : ℝ}
    {W W' : TorusField (n * R.params.side)} (hg : s.IsNear θ W)
    (hg' : s.IsNear θ' W') (β : TorusBond (n * R.params.side)) (hag : ∀ x i, (x, i) ≠ β → W x i = W' x i)
    (y : TorusSite (n * R.params.side)) (m : ℕ) (hm : m + 2 ≤ supDist y β.1) (hr : (R.range : ℝ) / 64 ≤ m) :
    |R.siteDensity (n * R.params.side) y W s.support s.labelling -
        R.siteDensity (n * R.params.side) y W' s.support s.labelling| ≤
      Real.exp (-R.params.decayRate * m) := by
  have hside : 2 * m + 2 < n * R.params.side := by
    have := two_mul_supDist_le y β.1
    omega
  refine h.hullExpansion.forget (n * R.params.side) (n * R.params.side) h.isBlockTorusSide h.isBlockTorusSide W W'
    s.support s.support s.labelling s.labelling y y m
    (hg.isHullState h) (hg'.isHullState h) (h.clusterFactor_ne_zero hg) (h.clusterFactor_ne_zero hg') hr
    ⟨hside, hside, ?_, fun _ _ => Iff.rfl, fun _ _ _ _ _ => rfl, fun _ i => by simp⟩
  intro b hb
  refine hag _ _ fun e => ?_
  have h1 := supDist_add_le_of_offsetInBox y hb.1
  have h2 : (bondFrom y b).1 = β.1 := congrArg Prod.fst e
  simp only [bondFrom] at h2
  rw [h2] at h1
  omega
theorem FieldMoves.perturb_eq_of_ne {m : ℕ} (c : Fin 2 → TorusBond m) (X : Fin 2 → imaginaryQuaternions)
    (W : TorusField m) (j : Fin 2) {σ σ' : Fin 2 → ℝ}
    (hσ : ∀ l, l ≠ j → σ l = σ' l) (x : TorusSite m) (i : Fin 4) (hne : (x, i) ≠ c j) :
    perturb c X σ W x i = perturb c X σ' W x i := by
  simp only [perturb_apply]
  congr 2
  unfold bondShift
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l = j
  · subst hl
    simp [Ne.symm hne]
  · rw [hσ l hl]
theorem FieldMoves.norm_bondShift_le {m : ℕ} (c : Fin 2 → TorusBond m) {X : Fin 2 → imaginaryQuaternions}
    (hu : AreUnitVectors X) {σ : Fin 2 → ℝ} {τ : ℝ}
    (hτ : ∀ l, |σ l| ≤ τ) (β : TorusBond m) : ‖bondShift c X σ β‖ ≤ 2 * τ := by
  have h0 : 0 ≤ τ := (abs_nonneg _).trans (hτ 0)
  have h1 : ∀ l, ‖(if c l = β then σ l • X l else 0 : imaginaryQuaternions)‖ ≤ τ := by
    intro l
    split_ifs
    · rw [norm_smul, hu l, mul_one, Real.norm_eq_abs]
      exact hτ l
    · simpa using h0
  rw [bondShift_pair]
  refine (norm_add_le _ _).trans ?_
  linarith [h1 0, h1 1]
theorem FieldMoves.norm_perturb_sub_le {m : ℕ} {τ ε : ℝ}
    (hstep : ∀ a : imaginaryQuaternions, ‖a‖ ≤ 2 * τ → ‖((expUnit a : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (c : Fin 2 → TorusBond m) {X : Fin 2 → imaginaryQuaternions} (hu : AreUnitVectors X) {σ : Fin 2 → ℝ}
    (hτ : ∀ l, |σ l| ≤ τ) (W : TorusField m)
    (x : TorusSite m) (i : Fin 4) : ‖((perturb c X σ W x i : UnitQuaternion) : ℍ[ℝ]) - W x i‖ ≤ ε := by
  rw [perturb_apply, Submonoid.coe_mul]
  have e : ((expUnit (bondShift c X σ (x, i)) : UnitQuaternion) : ℍ[ℝ]) * (W x i : UnitQuaternion) -
      (W x i : UnitQuaternion) =
      (((expUnit (bondShift c X σ (x, i)) : UnitQuaternion) : ℍ[ℝ]) - 1) * (W x i : UnitQuaternion) := by
    rw [sub_mul, one_mul]
  rw [e, norm_mul, norm_unitQuaternion, mul_one]
  exact hstep _ (norm_bondShift_le c hu hτ _)
theorem StepSettings.ChartSetting.Hypotheses.isNear_perturb (h : s.Hypotheses) {τ ε θ : ℝ}
    (hstep : ∀ a : imaginaryQuaternions, ‖a‖ ≤ 2 * τ → ‖((expUnit a : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (hθ : θ + 4 * ε ≤ R.params.threshold)
    {W : TorusField (n * R.params.side)} (hg : s.IsNear θ W) {c : Fin 2 → TorusBond (n * R.params.side)}
    (hc : ∀ l, c l ∈ s.free)
    {X : Fin 2 → imaginaryQuaternions} (hu : AreUnitVectors X) {σ : Fin 2 → ℝ} (hτ : ∀ l, |σ l| ≤ τ) :
    s.IsNear (θ + 4 * ε) (perturb c X σ W) :=
  ChartSetting.IsNear.of_close h hg (fun x i hx => perturb_apply_of_not_mem_free hc X σ W x i hx)
    (norm_perturb_sub_le hstep c hu hτ W) hθ
theorem StepSettings.ChartSetting.Hypotheses.alongPair_bounds (h : s.Hypotheses) {N₃ : ℝ}
    (hA : s.ActionSmooth N₃) {τ ε θ : ℝ}
    (hstep : ∀ a : imaginaryQuaternions, ‖a‖ ≤ 2 * τ → ‖((expUnit a : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (hθ : θ + 4 * ε < R.params.threshold)
    {W : TorusField (n * R.params.side)} (hg : s.IsNear θ W) {c : Fin 2 → TorusBond (n * R.params.side)}
    (hc : ∀ l, c l ∈ s.free)
    {X : Fin 2 → imaginaryQuaternions} (hu : AreUnitVectors X) (hcomm : CommutingPair c X) (hx : 0 ≤ R.coupling)
    {σ : Fin 2 → ℝ} (hτ : ∀ l, |σ l| ≤ τ) :
    ContDiffAt ℝ 3 (alongPair s.densityAt c X W) σ ∧ ∀ (k : ℕ) (ι : Fin k → Fin 2), 2 ≤ k → k ≤ 3 →
      |iteratedFDeriv ℝ k (alongPair s.densityAt c X W) σ fun l => Pi.single (ι l) 1| ≤
        (R.params.derivBound * R.coupling) ^ k + R.coupling * N₃ := by
  have hg₁ := h.isNear_perturb hstep hθ.le hg hc hu hτ
  have hC : ContDiffAt ℝ 3 (alongPair s.densityAt c X W) σ :=
    contDiffAt_alongPair hcomm σ (hg₁.densityAt_smooth h hA hθ hc X).1
  refine ⟨hC, fun k ι k2 k3 => ?_⟩
  have hCk : ContDiffAt ℝ k (alongPair s.densityAt c X W) σ := hC.of_le (by exact_mod_cast k3)
  rw [← mixedDeriv_perturb_eq_iteratedFDeriv hcomm ι σ hCk]
  exact (hg₁.densityAt_smooth h hA hθ (fun l => hc (ι l)) (X ∘ ι)).2 k2 k3 (fun l => hu (ι l)) hx
theorem DensityDifferences.abs_second_difference_le {a b c d e : ℝ} (h1 : |a - c| ≤ e) (h2 : |b - d| ≤ e) :
    |a - b - c + d| ≤ 2 * e := by
  rw [abs_le] at *
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
theorem DensityDifferences.abs_second_difference_le' {a b c d e : ℝ} (h1 : |a - b| ≤ e) (h2 : |c - d| ≤ e) :
    |a - b - c + d| ≤ 2 * e := by
  rw [abs_le] at *
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
theorem FieldMoves.perturb_corner_fst {m : ℕ} (c : Fin 2 → TorusBond m) (X : Fin 2 → imaginaryQuaternions)
    (W : TorusField m) (u t : ℝ) (x : TorusSite m)
    (i : Fin 4) (hne : (x, i) ≠ c 0) : perturb c X ![u, t] W x i = perturb c X ![0, t] W x i :=
  perturb_eq_of_ne c X W 0 (fun l hl => by
    have : l = 1 := by omega
    subst this
    simp) x i hne
theorem FieldMoves.perturb_corner_snd {m : ℕ} (c : Fin 2 → TorusBond m) (X : Fin 2 → imaginaryQuaternions)
    (W : TorusField m) (u t : ℝ) (x : TorusSite m)
    (i : Fin 4) (hne : (x, i) ≠ c 1) : perturb c X ![t, u] W x i = perturb c X ![t, 0] W x i :=
  perturb_eq_of_ne c X W 1 (fun l hl => by
    have : l = 0 := by omega
    subst this
    simp) x i hne
def StepSettings.StepSetup.differenceConstant (R : StepSetup) : ℝ :=
  4 * Real.exp (3 * R.params.decayRate) * expLatticeSum (R.params.decayRate / 2)
theorem DensityDifferences.pair_zero : (![0, 0] : Fin 2 → ℝ) = 0 := by
  funext i
  fin_cases i <;> simp
theorem StepSettings.ChartSetting.Hypotheses.abs_second_difference_alongPair_le (h : s.Hypotheses) {τ ε θ : ℝ}
    (hstep : ∀ a : imaginaryQuaternions, ‖a‖ ≤ 2 * τ → ‖((expUnit a : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (hθ : θ + 4 * ε ≤ R.params.threshold)
    {W : TorusField (n * R.params.side)} (hg : s.IsNear θ W) {c : Fin 2 → TorusBond (n * R.params.side)}
    (hc : ∀ l, c l ∈ s.free)
    {X : Fin 2 → imaginaryQuaternions} (hu : AreUnitVectors X) (hfar : (R.range : ℝ) / 2 < supDist (c 0).1 (c 1).1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ τ) (hδ : 0 < R.params.decayRate) :
    |alongPair s.densityAt c X W ![t, t] - alongPair s.densityAt c X W ![t, 0] -
        alongPair s.densityAt c X W ![0, t] + alongPair s.densityAt c X W 0| ≤
      R.differenceConstant * Real.exp (-R.params.decayRate * supDist (c 0).1 (c 1).1 / 4) := by
  set δ := R.params.decayRate with hδd
  set d : ℝ := ((supDist (c 0).1 (c 1).1 : ℕ) : ℝ) with hd
  have hstepd : ∀ σ : Fin 2 → ℝ, (∀ l, σ l = 0 ∨ σ l = t) → s.IsNear (θ + 4 * ε) (perturb c X σ W) := by
    intro σ hσ
    refine h.isNear_perturb hstep hθ hg hc hu fun l => ?_
    rcases hσ l with e | e <;> rw [e]
    · simpa using ht0.trans ht
    · rwa [abs_of_nonneg ht0]
  have g11 := hstepd ![t, t] (fun l => by fin_cases l <;> simp)
  have g10 := hstepd ![t, 0] (fun l => by fin_cases l <;> simp)
  have g01 := hstepd ![0, t] (fun l => by fin_cases l <;> simp)
  have g00 := hstepd ![0, 0] (fun l => by fin_cases l <;> simp)
  rw [← DensityDifferences.pair_zero]
  have hr := h.range_large
  have hrr : (2 : ℝ) ^ 20 ≤ R.range := by
    have : 2 ^ 20 ≤ R.range := by omega
    exact_mod_cast this
  have site : ∀ y : TorusSite (n * R.params.side),
      |R.siteDensity (n * R.params.side) y (perturb c X ![t, t] W) s.support s.labelling -
        R.siteDensity (n * R.params.side) y (perturb c X ![t, 0] W) s.support s.labelling -
        R.siteDensity (n * R.params.side) y (perturb c X ![0, t] W) s.support s.labelling +
        R.siteDensity (n * R.params.side) y (perturb c X ![0, 0] W) s.support s.labelling| ≤
      2 * Real.exp (2 * δ) * Real.exp (-δ * d / 4) * Real.exp (-(δ / 2) * supDist y (c 0).1) := by
    intro y
    set d₀ : ℕ := supDist y (c 0).1 with hd₀
    set d₁ : ℕ := supDist y (c 1).1 with hd₁
    have tri : supDist (c 0).1 (c 1).1 ≤ d₀ + d₁ := by
      have := supDist_triangle (c 0).1 y (c 1).1
      rw [supDist_comm (c 0).1 y] at this
      exact this
    have triR : d ≤ (d₀ : ℝ) + d₁ := by rw [hd]; exact_mod_cast tri
    have key : ∀ mx : ℕ, d₀ ≤ mx → d₁ ≤ mx → 2 ≤ mx → (R.range : ℝ) / 64 ≤ ((mx - 2 : ℕ) : ℝ) →
        Real.exp (-δ * ((mx - 2 : ℕ) : ℝ)) ≤
          Real.exp (2 * δ) * Real.exp (-δ * d / 4) * Real.exp (-(δ / 2) * d₀) := by
      intro mx h0 h1 h2 _
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have c1 : ((mx - 2 : ℕ) : ℝ) = (mx : ℝ) - 2 := by
        rw [Nat.cast_sub h2]
        norm_num
      have c2 : (d₀ : ℝ) ≤ mx := by exact_mod_cast h0
      have c3 : (d₁ : ℝ) ≤ mx := by exact_mod_cast h1
      rw [c1]
      nlinarith
    by_cases hcase : d₁ ≤ d₀
    · have hmx : (d / 2 : ℝ) ≤ d₀ := by
        have : (d₁ : ℝ) ≤ d₀ := by exact_mod_cast hcase
        linarith
      have h2 : 2 ≤ d₀ := by
        have : (2 : ℝ) ≤ d₀ := by nlinarith
        exact_mod_cast this
      have hm : (R.range : ℝ) / 64 ≤ ((d₀ - 2 : ℕ) : ℝ) := by
        rw [Nat.cast_sub h2]
        push_cast
        nlinarith
      have k1 := key d₀ le_rfl hcase h2 hm
      have b1 := h.abs_siteDensity_sub_le_of_agree g11 g01 (c 0)
        (fun x i hne => perturb_corner_fst c X W t t x i hne) y (d₀ - 2) (by omega) hm
      have b2 := h.abs_siteDensity_sub_le_of_agree g10 g00 (c 0)
        (fun x i hne => perturb_corner_fst c X W t 0 x i hne) y (d₀ - 2) (by omega) hm
      have := DensityDifferences.abs_second_difference_le (b1.trans k1) (b2.trans k1)
      linarith
    · have hcase' : d₀ ≤ d₁ := by omega
      have hmx : (d / 2 : ℝ) ≤ d₁ := by
        have : (d₀ : ℝ) ≤ d₁ := by exact_mod_cast hcase'
        linarith
      have h2 : 2 ≤ d₁ := by
        have : (2 : ℝ) ≤ d₁ := by nlinarith
        exact_mod_cast this
      have hm : (R.range : ℝ) / 64 ≤ ((d₁ - 2 : ℕ) : ℝ) := by
        rw [Nat.cast_sub h2]
        push_cast
        nlinarith
      have k1 := key d₁ hcase' le_rfl h2 hm
      have b1 := h.abs_siteDensity_sub_le_of_agree g11 g10 (c 1)
        (fun x i hne => perturb_corner_snd c X W t t x i hne) y (d₁ - 2) (by omega) hm
      have b2 := h.abs_siteDensity_sub_le_of_agree g01 g00 (c 1)
        (fun x i hne => perturb_corner_snd c X W t 0 x i hne) y (d₁ - 2) (by omega) hm
      have := DensityDifferences.abs_second_difference_le' (b1.trans k1) (b2.trans k1)
      linarith
  have e : alongPair s.densityAt c X W ![t, t] - alongPair s.densityAt c X W ![t, 0] -
        alongPair s.densityAt c X W ![0, t] + alongPair s.densityAt c X W ![0, 0] =
      ∑ y, (R.siteDensity (n * R.params.side) y (perturb c X ![t, t] W) s.support s.labelling -
        R.siteDensity (n * R.params.side) y (perturb c X ![t, 0] W) s.support s.labelling -
        R.siteDensity (n * R.params.side) y (perturb c X ![0, t] W) s.support s.labelling +
        R.siteDensity (n * R.params.side) y (perturb c X ![0, 0] W) s.support s.labelling) := by
    simp only [alongPair, ChartSetting.densityAt, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [e]
  have hδ2 : 0 < δ / 2 := by linarith
  have hL : 0 < expLatticeSum (δ / 2) := expLatticeSum_pos hδ2
  calc _ ≤ ∑ y : TorusSite (n * R.params.side),
        |R.siteDensity (n * R.params.side) y (perturb c X ![t, t] W) s.support s.labelling -
        R.siteDensity (n * R.params.side) y (perturb c X ![t, 0] W) s.support s.labelling -
        R.siteDensity (n * R.params.side) y (perturb c X ![0, t] W) s.support s.labelling +
        R.siteDensity (n * R.params.side) y (perturb c X ![0, 0] W) s.support s.labelling| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y : TorusSite (n * R.params.side), 2 * Real.exp (2 * δ) * Real.exp (-δ * d / 4) *
        Real.exp (-(δ / 2) * supDist y (c 0).1) := Finset.sum_le_sum fun y _ => site y
    _ = 2 * Real.exp (2 * δ) * Real.exp (-δ * d / 4) *
        ∑ y : TorusSite (n * R.params.side), Real.exp (-(δ / 2) * supDist y (c 0).1) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * Real.exp (2 * δ) * Real.exp (-δ * d / 4) * expLatticeSum (δ / 2) :=
        mul_le_mul_of_nonneg_left (sum_torus_exp_le hδ2 _) (by positivity)
    _ ≤ R.differenceConstant * Real.exp (-δ * d / 4) := by
        have h1 : Real.exp (2 * δ) ≤ Real.exp (3 * δ) := Real.exp_le_exp.mpr (by linarith)
        have h2 : 0 < Real.exp (-δ * d / 4) := Real.exp_pos _
        unfold StepSetup.differenceConstant
        have h3 : 2 * Real.exp (2 * δ) ≤ 4 * Real.exp (3 * δ) := by
          have := Real.exp_pos (2 * δ)
          linarith
        calc 2 * Real.exp (2 * δ) * Real.exp (-δ * d / 4) * expLatticeSum (δ / 2)
            = (2 * Real.exp (2 * δ)) * (expLatticeSum (δ / 2) * Real.exp (-δ * d / 4)) := by ring
          _ ≤ (4 * Real.exp (3 * δ)) * (expLatticeSum (δ / 2) * Real.exp (-δ * d / 4)) :=
              mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = 4 * Real.exp (3 * δ) * expLatticeSum (δ / 2) * Real.exp (-δ * d / 4) := by ring
theorem FieldMoves.mixedDeriv_eq_iteratedFDeriv_two (F : TorusField n → ℝ) (W : TorusField n)
    (c : Fin 2 → TorusBond n) (X : Fin 2 → imaginaryQuaternions) :
    mixedDeriv F W c X = iteratedFDeriv ℝ 2 (alongPair F c X W) 0 fun l => Pi.single l 1 := rfl
theorem StepSettings.ChartSetting.Hypotheses.abs_mixedDeriv_le (h : s.Hypotheses) {N₃ : ℝ}
    (hA : s.ActionSmooth N₃) {τ ε θ : ℝ}
    (hstep : ∀ a : imaginaryQuaternions, ‖a‖ ≤ 2 * τ → ‖((expUnit a : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (hθ : θ + 4 * ε < R.params.threshold)
    {W : TorusField (n * R.params.side)} (hg : s.IsNear θ W) {c : Fin 2 → TorusBond (n * R.params.side)}
    (hc : ∀ l, c l ∈ s.free)
    {X : Fin 2 → imaginaryQuaternions} (hu : AreUnitVectors X) (hcomm : CommutingPair c X)
    (hfar : (R.range : ℝ) / 2 < supDist (c 0).1 (c 1).1) (hx : 0 ≤ R.coupling) (hδ : 0 < R.params.decayRate)
    {t : ℝ} (ht0 : 0 < t) (ht : t ≤ τ) :
    |mixedDeriv s.densityAt W c X| ≤
      R.differenceConstant * Real.exp (-R.params.decayRate * supDist (c 0).1 (c 1).1 / 4) / t ^ 2 +
        2 * ((R.params.derivBound * R.coupling) ^ 3 + R.coupling * N₃) * t := by
  rw [mixedDeriv_eq_iteratedFDeriv_two]
  have sq : ∀ σ : Fin 2 → ℝ, (∀ i, 0 ≤ σ i ∧ σ i ≤ t) → ∀ l, |σ l| ≤ τ := fun σ hσ l => by
    rw [abs_of_nonneg (hσ l).1]
    exact (hσ l).2.trans ht
  exact abs_iteratedFDeriv_two_le_of_mixed_difference ht0
    (fun σ hσ => (h.alongPair_bounds hA hstep hθ hg hc hu hcomm hx (sq σ hσ)).1)
    (fun σ hσ ι => (h.alongPair_bounds hA hstep hθ hg hc hu hcomm hx (sq σ hσ)).2 3 ι (by norm_num) le_rfl)
    (h.abs_second_difference_alongPair_le hstep hθ.le hg hc hu hfar ht0.le ht hδ)
end YangMills.Construction
end
