import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderOfADensityAtConstantCurvatureProof
import YangMills.Construction.SummableBoundsOfTheFlow.LinesOfTwoTops
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreNearTheirLimits
import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessOfTheDensitiesIsLocal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames DerivativeInterpolation
namespace StepDensities
private theorem rpow_add_le_mul_rpow_of_le {m u v p q : ℝ} (hm : 0 < m) (hmu : m ≤ u) (hmv : m ≤ v) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    m ^ (p + q) ≤ u ^ p * v ^ q := by
  rw [Real.rpow_add hm]
  exact mul_le_mul (Real.rpow_le_rpow hm.le hmu hp) (Real.rpow_le_rpow hm.le hmv hq)
    (Real.rpow_nonneg hm.le _) (Real.rpow_nonneg (hm.le.trans hmu) _)
private theorem min_le_weightedGeomMean {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    min u v ≤ u ^ (3 / 4 : ℝ) * v ^ (1 / 4 : ℝ) := by
  have h := rpow_add_le_mul_rpow_of_le (lt_min hu hv) (min_le_left u v) (min_le_right u v)
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rwa [show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num, Real.rpow_one] at h
private theorem min_rpow_mul_le_weightedGeomMean_first {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (min u v) ^ (2 / 3 : ℝ) * u ^ (1 / 3 : ℝ) ≤ u ^ (3 / 4 : ℝ) * v ^ (1 / 4 : ℝ) := by
  have h := rpow_add_le_mul_rpow_of_le (lt_min hu hv) (min_le_left u v) (min_le_right u v)
    (by norm_num : (0 : ℝ) ≤ 5 / 12) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [show (5 / 12 : ℝ) + 1 / 4 = 2 / 3 by norm_num] at h
  calc (min u v) ^ (2 / 3 : ℝ) * u ^ (1 / 3 : ℝ)
      ≤ u ^ (5 / 12 : ℝ) * v ^ (1 / 4 : ℝ) * u ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hu.le _)
    _ = (u ^ (5 / 12 : ℝ) * u ^ (1 / 3 : ℝ)) * v ^ (1 / 4 : ℝ) := by ring
    _ = _ := by rw [← Real.rpow_add hu]; norm_num
private theorem min_rpow_mul_le_weightedGeomMean_second {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (min u v) ^ (1 / 3 : ℝ) * u ^ (2 / 3 : ℝ) ≤ u ^ (3 / 4 : ℝ) * v ^ (1 / 4 : ℝ) := by
  have h := rpow_add_le_mul_rpow_of_le (lt_min hu hv) (min_le_left u v) (min_le_right u v)
    (by norm_num : (0 : ℝ) ≤ 1 / 12) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [show (1 / 12 : ℝ) + 1 / 4 = 1 / 3 by norm_num] at h
  calc (min u v) ^ (1 / 3 : ℝ) * u ^ (2 / 3 : ℝ)
      ≤ u ^ (1 / 12 : ℝ) * v ^ (1 / 4 : ℝ) * u ^ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hu.le _)
    _ = (u ^ (1 / 12 : ℝ) * u ^ (2 / 3 : ℝ)) * v ^ (1 / 4 : ℝ) := by ring
    _ = _ := by rw [← Real.rpow_add hu]; norm_num
variable {F : BlockFrame}
private theorem expUnit_zero_eq_one : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem bondDeriv_of_order_zero (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G V c X = G V := by
  unfold bondDeriv
  rw [iteratedFDeriv_zero_apply]
  congr 1
  funext y i
  unfold leftTranslate ColdStepAtMirrorFrames.bondSpread
  simp [expUnit_zero_eq_one]
abbrev _root_.YangMills.SharedProofs.p1654 := @bondDeriv_of_order_zero
private theorem bondDeriv_sub_const (G : F.GaugeField F.top → ℝ) (d : ℝ) (V : F.GaugeField F.top) {k : ℕ} (hk : k ≠ 0)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hG : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0) :
    bondDeriv (fun V' => G V' - d) V c X = bondDeriv G V c X := by
  unfold bondDeriv
  have hc : ContDiffAt ℝ k (fun _ : Fin k → ℝ => d) 0 := contDiffAt_const
  have h := iteratedFDeriv_sub_apply hG hc
  have h2 : (fun τ : Fin k → ℝ => G (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) - d) =
      (fun τ : Fin k → ℝ => G (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) - fun _ => d := rfl
  rw [h2, h, iteratedFDeriv_const_of_ne hk]
  simp
abbrev _root_.YangMills.SharedProofs.p7768 := @bondDeriv_sub_const
private theorem pathHolonomy_uniformField_eq_one {j : ℕ} (l : List PathStep) :
    ∀ x : F.Site j, pathHolonomy (uniformField F j) x l = 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.pathHolonomy_uniformField <;> assumption
private theorem isSmallCurvature_uniformField (s : ℝ) (hs : 0 < s) {j : ℕ} :
    IsSmallCurvature s (uniformField F j) := by
  intro p _
  unfold plaquetteDefect plaquetteHolonomy
  rw [pathHolonomy_uniformField_eq_one]
  simpa using hs
abbrev _root_.YangMills.SharedProofs.p20907 := @isSmallCurvature_uniformField
private theorem isSmallCurvature_mono {s s' : ℝ} {j : ℕ} (h : s ≤ s') {W : F.GaugeField j}
    (hW : IsSmallCurvature s W) : IsSmallCurvature s' W := fun p hp => lt_of_lt_of_le (hW p hp) h
theorem densitiesNearLimits (hS : densityExcessSmallStatement)
    (hL : densityExcessLocalStatement) (hTw : DerivDiffLeOfCloseAlongLines)
    (hLn : SmallCurvatureAlongLineAndAgreeOn) : densitiesNearLimitsStatement := by
  obtain ⟨C₂, hC₂, tw⟩ := hTw
  obtain ⟨ln₁, ln₂⟩ := hLn
  refine EventuallyOrdered.mono (hS.and hL) ?_
  rintro T hT hn ⟨cS, cL⟩ hroom
  obtain ⟨y₁, C₁, hy₁, hC₁, gS⟩ := cS hroom
  obtain ⟨y₂, C₃, hy₂, hC₃, gL⟩ := cL hroom
  have hσ := hT.σ_pos
  have hκ := hT.κ_pos
  set τ₀ : ℝ := T.σ / 64 with hτ₀
  have hτ₀p : 0 < τ₀ := by positivity
  set c : ℝ := 2 * C₁ + C₃ with hc
  have hcp : 0 < c := by positivity
  set Cf : ℝ := 2 * (2 * c) + C₂ * (c * (τ₀⁻¹ + (τ₀ ^ 2)⁻¹ + 1)) with hCf
  refine ⟨max (max y₁ y₂) 1, Cf, by positivity, by positivity, ?_⟩
  intro t x hx
  have hxy₁ : y₁ ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxy₂ : y₂ ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hx)
  have hC₁f : C₁ ≤ Cf := by
    have h0 : 0 ≤ C₂ * (c * (τ₀⁻¹ + (τ₀ ^ 2)⁻¹ + 1)) := by positivity
    rw [hCf, hc]
    nlinarith
  refine ⟨fun F Y V k c' X hF hV hk hX => ?_, ?_⟩
  · refine ((gS t x hxy₁ F Y V hF hV).2 k c' X hk hX).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right hC₁f (inv_pos.mpr hx0).le
  intro F F' hF hF' Y Y' V V' r k h X hV hV' hag hk hb hX
  set G := densityExcess T t x F Y with hG
  set G' := densityExcess T t x F' Y' with hG'
  set a : ℝ := x⁻¹ with ha
  have ha0 : 0 < a := inv_pos.mpr hx0
  set b : ℝ := Real.exp (-(T.κ * r / 2 ^ 7)) with hb'
  have hb0 : 0 < b := Real.exp_pos _
  set m : ℝ := min a b with hm
  have hm0 : 0 < m := lt_min ha0 hb0
  set W : ℝ := a ^ (3 / 4 : ℝ) * b ^ (1 / 4 : ℝ) with hW
  have hW0 : 0 < W := mul_pos (Real.rpow_pos_of_pos ha0 _) (Real.rpow_pos_of_pos hb0 _)
  have hgoal : W = x ^ (-(3 / 4 : ℝ)) * Real.exp (-(T.κ / 2 ^ 9 * r)) := by
    rw [hW, ha, Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le, hb', ← Real.exp_mul]
    congr 2
    ring
  have hsize : ∀ (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → |densityExcess T t x F Y V| ≤ C₁ * a := by
    intro F Y V hF hV
    have h1 := (gS t x hxy₁ F Y V hF hV).2 0 Fin.elim0 Fin.elim0 (by norm_num) (fun l => l.elim0)
    rw [bondDeriv_of_order_zero] at h1
    have h2 : Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ T.κ / 2 ^ 6 * (bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) : ℝ) := by positivity
      linarith
    calc _ ≤ C₁ * a * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))) := h1
      _ ≤ C₁ * a * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := mul_one _
  have hclose : ∀ (V₁ : F.GaugeField F.top) (V₁' : F'.GaugeField F'.top), IsSmallCurvature (5 / 4 * T.σ) V₁ →
      IsSmallCurvature (5 / 4 * T.σ) V₁' → AgreeOnBall (finiteCells F) V₁ (finiteCells F') V₁' Y Y' r →
      |G V₁ - G' V₁'| ≤ c * m := by
    intro V₁ V₁' c₁ c₂ ag
    have e1 : |G V₁ - G' V₁'| ≤ 2 * C₁ * a := by
      have := hsize F Y V₁ hF c₁
      have := hsize F' Y' V₁' hF' c₂
      calc |G V₁ - G' V₁'| ≤ |G V₁| + |G' V₁'| := abs_sub _ _
        _ ≤ _ := by linarith
    have e2 : |G V₁ - G' V₁'| ≤ C₃ * b := gL t x hxy₂ F F' Y Y' V₁ V₁' r hF hF' c₁ c₂ ag
    rcases min_choice a b with h | h
    · rw [hm, h]
      calc _ ≤ 2 * C₁ * a := e1
        _ ≤ c * a := mul_le_mul_of_nonneg_right (by rw [hc]; linarith) ha0.le
    · rw [hm, h]
      calc _ ≤ C₃ * b := e2
        _ ≤ c * b := mul_le_mul_of_nonneg_right (by rw [hc]; linarith) hb0.le
  have h98 : (9 / 8 : ℝ) * T.σ ≤ 5 / 4 * T.σ := by nlinarith
  have hcV : IsSmallCurvature (5 / 4 * T.σ) V := isSmallCurvature_mono h98 hV
  have hcV' : IsSmallCurvature (5 / 4 * T.σ) V' := isSmallCurvature_mono h98 hV'
  have hmW : m ≤ W := min_le_weightedGeomMean ha0 hb0
  have hbound : ∀ B : ℝ, B ≤ Cf * W → B ≤ Cf * x ^ (-(3 / 4 : ℝ)) * Real.exp (-(T.κ / 2 ^ 9 * r)) := by
    intro B hB
    rw [hgoal] at hB
    rw [mul_assoc]
    exact hB
  apply hbound
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    rw [bondDeriv_of_order_zero, bondDeriv_of_order_zero]
    unfold centredFamily
    have f1 := hclose V V' hcV hcV' hag
    have f2 := hclose (uniformField F F.top) (uniformField F' F'.top)
      (isSmallCurvature_uniformField _ (by positivity)) (isSmallCurvature_uniformField _ (by positivity))
      ⟨hag.1, hag.2.1, hag.2.2.1, fun _ _ => rfl⟩
    have hcW : c * m ≤ c * W := mul_le_mul_of_nonneg_left hmW hcp.le
    have e : G V - G (uniformField F F.top) - (G' V' - G' (uniformField F' F'.top)) =
        (G V - G' V') - (G (uniformField F F.top) - G' (uniformField F' F'.top)) := by ring
    show |G V - G (uniformField F F.top) - (G' V' - G' (uniformField F' F'.top))| ≤ _
    rw [e]
    have h3 : |(G V - G' V') - (G (uniformField F F.top) - G' (uniformField F' F'.top))| ≤ 2 * (c * W) := by
      calc _ ≤ |G V - G' V'| + |G (uniformField F F.top) - G' (uniformField F' F'.top)| := abs_sub _ _
        _ ≤ _ := by linarith
    refine h3.trans ?_
    have h5 : 2 * (c * W) = (2 * c) * W := by ring
    rw [h5]
    apply mul_le_mul_of_nonneg_right _ hW0.le
    have h6 : 0 ≤ C₂ * (c * (τ₀⁻¹ + (τ₀ ^ 2)⁻¹ + 1)) := by positivity
    rw [hCf]
    linarith
  · have hne : k ≠ 0 := hk0.ne'
    have sm : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (leftTranslate (ColdStepAtMirrorFrames.bondSpread (bondsAt Y h) X τ) V)) 0 :=
      ((gS t x hxy₁ F Y V hF hcV).1 k _ X).of_le (by exact_mod_cast (by omega : k ≤ 3))
    have sm' : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G' (leftTranslate (ColdStepAtMirrorFrames.bondSpread (bondsAt Y' h) X τ) V')) 0 :=
      ((gS t x hxy₁ F' Y' V' hF' hcV').1 k _ X).of_le (by exact_mod_cast (by omega : k ≤ 3))
    have d₁ : bondDeriv (centredFamily (densityExcess T t x) F Y) V (bondsAt Y h) X =
        bondDeriv G V (bondsAt Y h) X := bondDeriv_sub_const G _ V hne _ X sm
    have d₂ : bondDeriv (centredFamily (densityExcess T t x) F' Y') V' (bondsAt Y' h) X =
        bondDeriv G' V' (bondsAt Y' h) X := bondDeriv_sub_const G' _ V' hne _ X sm'
    rw [d₁, d₂]
    have hline : ∀ {F : BlockFrame} (V : F.GaugeField F.top) (cc : Fin k → F.Site F.top × Fin 4)
        (ς : Fin k → ℝ) (s : ℝ), (∀ l, ς l = 1 ∨ ς l = -1) → |s| ≤ τ₀ →
        IsSmallCurvature (9 / 8 * T.σ) V →
        IsSmallCurvature (5 / 4 * T.σ) (alongLine cc (fun l => ς l • X l) s V) := by
      intro F V cc ς s hς hs hV
      have hn : ∀ l, ‖ς l • X l‖ ≤ 1 := by
        intro l
        rw [norm_smul, hX l, mul_one, Real.norm_eq_abs]
        rcases hς l with h | h <;> simp [h]
      have := ln₁ F V k cc _ s (9 / 8 * T.σ) hn hV
      refine isSmallCurvature_mono ?_ this
      have hk2 : (k : ℝ) ≤ 2 := by exact_mod_cast (by omega : k ≤ 2)
      have hs0 := abs_nonneg s
      nlinarith
    have hread : ∀ {F : BlockFrame} (Y : F.Cell) (V : F.GaugeField F.top) (cc : Fin k → F.Site F.top × Fin 4)
        (ς : Fin k → ℝ), IsCubicTopTorus T.L t T.n₀ F → (∀ l, ς l = 1 ∨ ς l = -1) →
        IsSmallCurvature (9 / 8 * T.σ) V →
        IsControlledAlongLine (densityExcess T t x F Y) V cc (fun l => ς l • X l) τ₀ (c * a) := by
      intro F Y V cc ς hF hς hV
      refine ⟨fun s hs => (gS t x hxy₁ F Y _ hF (hline V cc ς s hς hs hV)).1, fun s hs e => ?_⟩
      have hu : AreUnitVectors ((fun l => ς l • X l) ∘ e) := by
        intro l
        simp only [Function.comp]
        rw [norm_smul, hX (e l), mul_one, Real.norm_eq_abs]
        rcases hς (e l) with h | h <;> simp [h]
      have h1 := (gS t x hxy₁ F Y _ hF (hline V cc ς s hς hs hV)).2 3 (cc ∘ e) _ (by norm_num) hu
      have h2 : Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y (cc ∘ e))) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have : 0 ≤ T.κ / 2 ^ 6 * (bondSpan Y (cc ∘ e) : ℝ) := by positivity
        linarith
      calc _ ≤ C₁ * a * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y (cc ∘ e))) := h1
        _ ≤ C₁ * a * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ c * a := by
          rw [mul_one]
          apply mul_le_mul_of_nonneg_right _ ha0.le
          rw [hc]
          linarith
    have hmain := tw F F' G G' V V' k (bondsAt Y h) (bondsAt Y' h) X τ₀ (c * m) (c * a) hk0 (by omega)
      hτ₀p (by positivity) (by positivity) fun ς hς =>
        ⟨hread Y V _ ς hF hς hV, hread Y' V' _ ς hF' hς hV', fun s hs =>
          hclose _ _ (hline V _ ς s hς hs hV) (hline V' _ ς s hς hs hV')
            (ln₂ F F' V V' Y Y' r k h _ s hag hb)⟩
    refine hmain.trans ?_
    have hcm : c * m / τ₀ ^ k ≤ c * W * (τ₀⁻¹ + (τ₀ ^ 2)⁻¹) := by
      have h1 : (τ₀ ^ k)⁻¹ ≤ τ₀⁻¹ + (τ₀ ^ 2)⁻¹ := by
        have hp1 : 0 < τ₀⁻¹ := inv_pos.mpr hτ₀p
        have hp2 : 0 < (τ₀ ^ 2)⁻¹ := by positivity
        have hk12 : k = 1 ∨ k = 2 := by omega
        rcases hk12 with h | h
        · rw [h, pow_one]
          linarith
        · rw [h]
          linarith
      rw [div_eq_mul_inv]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hmW hcp.le) h1 (by positivity) (by positivity)
    have hmix : (c * m) ^ (1 - (k : ℝ) / 3) * (c * a) ^ ((k : ℝ) / 3) ≤ c * W := by
      rw [Real.mul_rpow hcp.le hm0.le, Real.mul_rpow hcp.le ha0.le]
      have hcc : c ^ (1 - (k : ℝ) / 3) * c ^ ((k : ℝ) / 3) = c := by
        rw [← Real.rpow_add hcp, sub_add_cancel, Real.rpow_one]
      have hk12 : k = 1 ∨ k = 2 := by omega
      have hgeo : m ^ (1 - (k : ℝ) / 3) * a ^ ((k : ℝ) / 3) ≤ W := by
        rcases hk12 with h | h
        · subst h
          have := min_rpow_mul_le_weightedGeomMean_first ha0 hb0
          norm_num at this ⊢
          exact this
        · subst h
          have := min_rpow_mul_le_weightedGeomMean_second ha0 hb0
          norm_num at this ⊢
          exact this
      calc c ^ (1 - (k : ℝ) / 3) * m ^ (1 - (k : ℝ) / 3) * (c ^ ((k : ℝ) / 3) * a ^ ((k : ℝ) / 3))
          = (c ^ (1 - (k : ℝ) / 3) * c ^ ((k : ℝ) / 3)) * (m ^ (1 - (k : ℝ) / 3) * a ^ ((k : ℝ) / 3)) := by ring
        _ = c * (m ^ (1 - (k : ℝ) / 3) * a ^ ((k : ℝ) / 3)) := by rw [hcc]
        _ ≤ c * W := mul_le_mul_of_nonneg_left hgeo hcp.le
    have hsum : C₂ * (c * m / τ₀ ^ k + (c * m) ^ (1 - (k : ℝ) / 3) * (c * a) ^ ((k : ℝ) / 3)) ≤
        C₂ * (c * (τ₀⁻¹ + (τ₀ ^ 2)⁻¹ + 1)) * W := by
      have : c * m / τ₀ ^ k + (c * m) ^ (1 - (k : ℝ) / 3) * (c * a) ^ ((k : ℝ) / 3) ≤
          c * (τ₀⁻¹ + (τ₀ ^ 2)⁻¹ + 1) * W := by
        calc _ ≤ c * W * (τ₀⁻¹ + (τ₀ ^ 2)⁻¹) + c * W := add_le_add hcm hmix
          _ = _ := by ring
      calc _ ≤ C₂ * (c * (τ₀⁻¹ + (τ₀ ^ 2)⁻¹ + 1) * W) := mul_le_mul_of_nonneg_left this hC₂.le
        _ = _ := by ring
    refine hsum.trans ?_
    apply mul_le_mul_of_nonneg_right _ hW0.le
    rw [hCf]
    linarith
end StepDensities
end YangMills.Construction
end
