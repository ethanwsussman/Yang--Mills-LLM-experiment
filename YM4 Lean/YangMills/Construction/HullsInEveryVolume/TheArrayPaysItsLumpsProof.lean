import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfAnExpansion
import YangMills.Construction.HullsInEveryVolume.TheArrayPaysItsLumps
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction.HullsInEveryVolume
open TorusLumps TorusFields BlockAverages LumpContours
section Hull
variable {ℓ : StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional} {f : LocalDensity} {n : ℕ} [NeZero n]
  {Λ : LabelSpace} {Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
  {Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ}
  {φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
private theorem lintegral_glueLabel_aux {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    {Y Y' : Finset (TorusSite n)} (h : Y' = Y) (G : (Y → Ω) → ENNReal) (ω₀ : Y → Ω) :
    ∫⁻ ν, G (glueLabel Y Y' ω₀ ν) ∂(Measure.pi fun _ : Y' => μ) = ∫⁻ ω, G ω ∂(Measure.pi fun _ : Y => μ) := by
  subst h
  have : ∀ ν : Y' → Ω, glueLabel Y' Y' ω₀ ν = ν := by
    intro ν
    funext z
    simp [glueLabel, z.2]
  simp only [this]
abbrev _root_.YangMills.SharedProofs.p29218 := @lintegral_glueLabel_aux
open Classical in
private theorem hullState_lintegral_le (h3 : ExpansionBasicBounds) (hfit : ℓ.Admissible) (hE : 1 ≤ ℓ.E) (hx : 0 < x)
    (hfl : 4 * ℓ.n₀ + 2 ^ 16 ≤ clusterRange x) (hc : ColdExpansion ℓ t x D f) (hh : HullExpansion ℓ t x D f Λ Dq Φ φ)
    (hs : IsBlockTorusSide ℓ n) (W : TorusField n) (Y : Finset (TorusSite n)) (hY : IsHullState ℓ (clusterRange x) W Y) (q : ℝ)
    (hq : q ≤ x * ℓ.κ * ℓ.threshold ^ 2 * (((torusHotLumps ℓ W).filter (· ⊆ Y)).card : ℝ) +
      ℓ.κ₁ * x * ℓ.threshold ^ 2 * (excessLength ℓ (clusterRange x) Y W : ℝ)) :
    ∫⁻ ω, ENNReal.ofReal (Dq n W Y ω) ∂(Measure.pi fun _ : Y => Λ.μ) ≤
      ENNReal.ofReal (D n (trivialField n) * Real.exp (2 * ℓ.E * Fintype.card (TorusSite n) -
        x * actionAtLevel ℓ.coupling ℓ.side t (Finset.univ \ TorusLumps.thickening lumpRange (torusHotSites ℓ W)) W - q)) := by
  have hfacts := h3 ℓ t x D f Λ Dq Φ φ hfit hE hx hfl hc hh
  have hflat : IsCold ℓ.threshold (trivialField n) := fun z μ ν _ => by
    simp only [curvature, holonomy_trivialField]
    simpa using hfit.σ_pos
  have hn₀ : ℓ.n₀ ≤ n := by
    have h1 := hs.2
    have h2 : 1 * ℓ.n₀ ≤ ℓ.side * ℓ.n₀ := Nat.mul_le_mul_right _ (by have := hfit.L_ge; omega)
    omega
  have hD1 : 0 < D n (trivialField n) := hc.positive n hn₀ _ hflat
  set A : ℝ := actionAtLevel ℓ.coupling ℓ.side t (Finset.univ \ TorusLumps.thickening lumpRange (torusHotSites ℓ W)) W with hA
  set c : ℝ := D n (trivialField n) * Real.exp (2 * ℓ.E * Fintype.card (TorusSite n) - x * A) with hcdef
  have hc0 : 0 ≤ c := by positivity
  by_cases hne : Nonempty (Y → Λ.Ω)
  · obtain ⟨ω₀⟩ := hne
    set P := chainComponents (clusterRange x) Y with hP
    have hU : P.biUnion id = Y := biUnion_chainComponents
    have hp := hh.price n hs W Y ω₀ P hY subset_rfl
      (fun X hX => absurd (Finset.mem_sdiff.mp hX).1 (Finset.mem_sdiff.mp hX).2)
    let G : (Y → Λ.Ω) → ENNReal := fun ω =>
      if ∃ X ∈ P, Φ n W Y ω X = 0 then 0 else
        ENNReal.ofReal ((∏ X ∈ P, Φ n W Y ω X) *
          Real.exp (∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
              ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange x : ℝ) / 4),
            φ n y W Y ω))
    have hG : ∫⁻ ω, G ω ∂(Measure.pi fun _ : Y => Λ.μ) ≤ ENNReal.ofReal (Real.exp (-q)) := by
      rw [← lintegral_glueLabel_aux Λ.μ hU G ω₀]
      refine hp.trans ?_
      apply ENNReal.ofReal_le_ofReal
      rw [hU]
      apply Real.exp_le_exp.mpr
      linarith
    have hpt : ∀ ω, ENNReal.ofReal (Dq n W Y ω) ≤ ENNReal.ofReal c * G ω := by
      intro ω
      by_cases hz : ∃ X ∈ P, Φ n W Y ω X = 0
      · obtain ⟨X, hX, h0⟩ := hz
        rw [hh.form n hs W Y ω hY, Finset.prod_eq_zero hX h0, mul_zero]
        simp
      · have hGω : G ω = ENNReal.ofReal ((∏ X ∈ P, Φ n W Y ω X) *
            Real.exp (∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
                ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange x : ℝ) / 4), φ n y W Y ω)) := by
          simp only [G]
          rw [if_neg hz]
        push Not at hz
        rw [hGω, ← ENNReal.ofReal_mul hc0]
        apply ENNReal.ofReal_le_ofReal
        rw [hh.form n hs W Y ω hY]
        set near := Finset.univ.filter (fun y : TorusSite n =>
                ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange x : ℝ) / 4) with hnear
        have hsplit : ∑ y, φ n y W Y ω = ∑ y ∈ near, φ n y W Y ω +
            ∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
              ¬ ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange x : ℝ) / 4), φ n y W Y ω :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
        have hfarsum : ∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
              ¬ ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange x : ℝ) / 4), φ n y W Y ω ≤
            2 * ℓ.E * Fintype.card (TorusSite n) := by
          have h1 : ∀ y ∈ Finset.univ.filter (fun y : TorusSite n =>
              ¬ ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange x : ℝ) / 4),
              φ n y W Y ω ≤ 2 * ℓ.E := by
            intro y hy
            have hy2 := (Finset.mem_filter.mp hy).2
            push Not at hy2
            rw [hU] at hy2
            exact (le_abs_self _).trans (hfacts.2.1 n hs W Y ω y hY hz hy2)
          have h2 := Finset.sum_le_card_nsmul _ _ _ h1
          rw [nsmul_eq_mul] at h2
          have h3 : ((Finset.univ.filter (fun y : TorusSite n =>
              ¬ ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange x : ℝ) / 4)).card : ℝ) ≤
              Fintype.card (TorusSite n) := by
            exact_mod_cast Finset.card_le_univ _
          nlinarith
        have hprod : 0 ≤ ∏ X ∈ P, Φ n W Y ω X :=
          Finset.prod_nonneg fun X _ => hh.factor_nonneg n hs W Y ω X
        have hexp : Real.exp (-x * A + ∑ y, φ n y W Y ω) ≤
            Real.exp (2 * ℓ.E * Fintype.card (TorusSite n) - x * A) * Real.exp (∑ y ∈ near, φ n y W Y ω) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          rw [hsplit]
          linarith
        calc D n (trivialField n) * _ * _ ≤ D n (trivialField n) * (Real.exp (2 * ℓ.E * Fintype.card (TorusSite n) - x * A) *
              Real.exp (∑ y ∈ near, φ n y W Y ω)) * ∏ X ∈ P, Φ n W Y ω X := by gcongr
          _ = c * ((∏ X ∈ P, Φ n W Y ω X) * Real.exp (∑ y ∈ near, φ n y W Y ω)) := by
            rw [hcdef]
            ring
    calc ∫⁻ ω, ENNReal.ofReal (Dq n W Y ω) ∂(Measure.pi fun _ : Y => Λ.μ)
        ≤ ∫⁻ ω, ENNReal.ofReal c * G ω ∂(Measure.pi fun _ : Y => Λ.μ) := lintegral_mono hpt
      _ = ENNReal.ofReal c * ∫⁻ ω, G ω ∂(Measure.pi fun _ : Y => Λ.μ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-q)) := by gcongr
      _ = ENNReal.ofReal (c * Real.exp (-q)) := (ENNReal.ofReal_mul hc0).symm
      _ = _ := by
        congr 1
        rw [hcdef, mul_assoc, ← Real.exp_add]
        congr 2
  · have : IsEmpty (Y → Λ.Ω) := not_nonempty_iff.mp hne
    simp
open Classical in
private theorem functional_le_of_hull_expansion (h3 : ExpansionBasicBounds) (hfit : ℓ.Admissible) (hE : 1 ≤ ℓ.E) (hx : 0 < x)
    (hfl : 4 * ℓ.n₀ + 2 ^ 16 ≤ clusterRange x) (hc : ColdExpansion ℓ t x D f) (hh : HullExpansion ℓ t x D f Λ Dq Φ φ)
    (hs : IsBlockTorusSide ℓ n) (W : TorusField n) :
    D n W ≤ (2 : ℝ) ^ Fintype.card (TorusSite n) * (D n (trivialField n) * Real.exp (2 * ℓ.E * Fintype.card (TorusSite n) -
        x * actionAtLevel ℓ.coupling ℓ.side t (Finset.univ \ TorusLumps.thickening lumpRange (torusHotSites ℓ W)) W -
        x * ℓ.κ * ℓ.threshold ^ 2 * ((torusHotLumps ℓ W).card : ℝ))) := by
  have hflat : IsCold ℓ.threshold (trivialField n) := fun z μ ν _ => by
    simp only [curvature, holonomy_trivialField]
    simpa using hfit.σ_pos
  have hn₀ : ℓ.n₀ ≤ n := by
    have h1 := hs.2
    have h2 : 1 * ℓ.n₀ ≤ ℓ.side * ℓ.n₀ := Nat.mul_le_mul_right _ (by have := hfit.L_ge; omega)
    omega
  have hD1 : 0 < D n (trivialField n) := hc.positive n hn₀ _ hflat
  set B : ℝ := D n (trivialField n) * Real.exp (2 * ℓ.E * Fintype.card (TorusSite n) -
        x * actionAtLevel ℓ.coupling ℓ.side t (Finset.univ \ TorusLumps.thickening lumpRange (torusHotSites ℓ W)) W -
        x * ℓ.κ * ℓ.threshold ^ 2 * ((torusHotLumps ℓ W).card : ℝ)) with hB
  have hkey : ∀ Y ∈ Finset.univ.filter (IsHullState ℓ (clusterRange x) W),
      ∫⁻ ω, ENNReal.ofReal (Dq n W Y ω) ∂(Measure.pi fun _ : Y => Λ.μ) ≤ ENNReal.ofReal B := by
    intro Y hYm
    have hY : IsHullState ℓ (clusterRange x) W Y := (Finset.mem_filter.mp hYm).2
    have hfil : (torusHotLumps ℓ W).filter (· ⊆ Y) = torusHotLumps ℓ W := by
      refine Finset.filter_true_of_mem fun l hl z hz => hY.1 ?_
      exact (TorusFields.mem_thickening _ _ _).mpr ⟨z, Finset.mem_biUnion.mpr ⟨l, hl, hz⟩, by rw [supDist_self]; omega⟩
    refine hullState_lintegral_le h3 hfit hE hx hfl hc hh hs W Y hY _ ?_
    rw [hfil]
    have hk : 0 ≤ ℓ.κ₁ * x * ℓ.threshold ^ 2 * (excessLength ℓ (clusterRange x) Y W : ℝ) := by
      have := hfit.κ₁_pos
      positivity
    linarith
  have hsum := hh.sum n hs W
  have hle : ENNReal.ofReal (D n W) ≤ ENNReal.ofReal ((2 : ℝ) ^ Fintype.card (TorusSite n)) * ENNReal.ofReal B := by
    rw [← hsum]
    refine (Finset.sum_le_card_nsmul _ _ _ hkey).trans ?_
    rw [nsmul_eq_mul]
    have hcard : (Finset.univ.filter (IsHullState ℓ (clusterRange x) W)).card ≤ 2 ^ Fintype.card (TorusSite n) := by
      refine (Finset.card_le_univ _).trans ?_
      rw [Fintype.card_finset]
    have h1 : ((Finset.univ.filter (IsHullState ℓ (clusterRange x) W)).card : ENNReal) ≤
        ((2 ^ Fintype.card (TorusSite n) : ℕ) : ENNReal) := by exact_mod_cast hcard
    have h2e : ((2 ^ Fintype.card (TorusSite n) : ℕ) : ENNReal) =
        ENNReal.ofReal ((2 : ℝ) ^ Fintype.card (TorusSite n)) := by
      rw [show ((2 : ℝ) ^ Fintype.card (TorusSite n)) = ((2 ^ Fintype.card (TorusSite n) : ℕ) : ℝ) by
        push_cast; rfl, ENNReal.ofReal_natCast]
    rw [h2e] at h1
    exact mul_le_mul' h1 (le_refl _)
  rw [← ENNReal.ofReal_mul (by positivity)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
end Hull
theorem functionalBoundByLumpPrice_of_expansionBasicBounds (h3 : ExpansionBasicBounds) : functionalBoundByLumpPrice :=
  fun _ _ _ _ _ _ _ _ _ hfit hE hx hfl hc hh _ _ hs W => functional_le_of_hull_expansion h3 hfit hE hx hfl hc hh hs W
end YangMills.Construction.HullsInEveryVolume
end
