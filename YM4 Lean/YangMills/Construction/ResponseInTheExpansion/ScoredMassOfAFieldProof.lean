import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfAnExpansionProof
import YangMills.Construction.ResponseInTheExpansion.ScoredMassOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusLumps TorusFields BlockAverages LumpContours
private theorem blockFit_nonneg {F : BlockFrame} {j : ℕ} (X : F.GaugeField j) (X' : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) : 0 ≤ blockFit X X' c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.blockFit_nonneg <;> assumption
private theorem wilsonAction_nonneg {F : BlockFrame} (S : Finset F.Cell) (U : F.GaugeField 0) :
    0 ≤ BlockAverages.wilsonAction S U := by apply _root_.YangMills.Construction.TorusLumps.wilsonAction_nonneg <;> assumption
private theorem minimalAction_nonneg {F : BlockFrame} {a : ℝ} (ha : 0 ≤ a) (S : Finset F.Cell) :
    ∀ (j : ℕ) (X : F.GaugeField j), 0 ≤ minimalAction a S j X
  | 0, U => wilsonAction_nonneg S U
  | j + 1, V => by
    refine Real.iInf_nonneg fun W => ?_
    exact add_nonneg (minimalAction_nonneg ha S j W)
      (mul_nonneg ha (Finset.sum_nonneg fun c _ => blockFit_nonneg _ _ _))
private theorem actionAtLevel_nonneg {n : ℕ} [NeZero n] {a : ℝ} (ha : 0 ≤ a) (L : ℕ) :
    ∀ (t : ℕ) (S : Finset (TorusSite n)) (W : TorusField n), 0 ≤ actionAtLevel a L t S W
  | 0, _, W => Finset.sum_nonneg fun _ _ => TorusFields.plaquetteEnergy_nonneg W _ _ _
  | _ + 1, _, _ => minimalAction_nonneg ha _ _ _
private theorem lintegral_glueLabel_of_eq {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [SigmaFinite μ] [NeZero n] {Y Y' : Finset (TorusSite n)} (h : Y' = Y) (G : (Y → Ω) → ENNReal) (ω₀ : Y → Ω) :
    ∫⁻ ν, G (glueLabel Y Y' ω₀ ν) ∂(Measure.pi fun _ : Y' => μ) = ∫⁻ ω, G ω ∂(Measure.pi fun _ : Y => μ) := by apply _root_.YangMills.Construction.TorusLumps.lintegral_glueLabel <;> assumption
private theorem sum_subtype_of_eq {n : ℕ} {Y Y' : Finset (TorusSite n)} (h : Y' = Y)
    (hc : ∀ y : Y', (y : TorusSite n) ∈ Y) (g : Y → ℝ) : ∑ y : Y, g y = ∑ y : Y', g ⟨y, hc y⟩ := by
  subst h
  rfl
theorem scoredMassStatement_holds (h3 : ExpansionBasicBounds) : ScoredMassStatement := by
  intro ℓ t x D f Λ Dq Φ φ s hfit hE hx hfl hc hh hprice n _ hs W
  classical
  have hfar := (h3 ℓ t x D f Λ Dq Φ φ hfit hE hx hfl hc hh).2.1
  have hn₀ : ℓ.n₀ ≤ n := by
    have h1 := hs.2
    have h2 : 1 ≤ ℓ.side := Nat.pos_of_ne_zero (NeZero.ne _)
    nlinarith
  have htriv : IsCold ℓ.threshold (trivialField n) := by
    intro z μ ν _
    have hz : curvature (trivialField n) z μ ν = 0 := by simp [curvature, holonomy, trivialField]
    rw [hz]
    exact hfit.σ_pos
  have hD1 : 0 < D n (trivialField n) := hc.positive n hn₀ _ htriv
  set c : ℝ := D n (trivialField n) * Real.exp (2 * ℓ.E * Fintype.card (TorusSite n)) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have key : ∀ Y ∈ Finset.univ.filter (IsHullState ℓ (clusterRange x) W),
      ∫⁻ ω, ENNReal.ofReal (Dq n W Y ω * Real.exp (∑ y : Y, s (ω y))) ∂(Measure.pi fun _ : Y => Λ.μ) ≤
        ENNReal.ofReal c := by
    intro Y hYm
    have hY : IsHullState ℓ (clusterRange x) W Y := (Finset.mem_filter.mp hYm).2
    by_cases hne : Nonempty (Y → Λ.Ω)
    · obtain ⟨ω₀⟩ := hne
      set P := chainComponents (clusterRange x) Y with hP
      have hU : P.biUnion id = Y := biUnion_chainComponents
      have hcast : ∀ y : (P.biUnion id : Finset (TorusSite n)), (y : TorusSite n) ∈ Y := fun y => hU ▸ y.2
      have hp := hprice.price n hs W Y ω₀ P hY subset_rfl
        (fun X hX => absurd (Finset.mem_sdiff.mp hX).1 (Finset.mem_sdiff.mp hX).2)
      let G : (Y → Λ.Ω) → ENNReal := fun ω =>
        if ∃ X ∈ P, Φ n W Y ω X = 0 then 0 else
          ENNReal.ofReal ((∏ X ∈ P, Φ n W Y ω X) *
            Real.exp (∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
                ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange x : ℝ) / 4),
              φ n y W Y ω) *
            Real.exp (∑ y : (P.biUnion id : Finset (TorusSite n)), s (ω ⟨y, hcast y⟩)))
      have hG : ∫⁻ ω, G ω ∂(Measure.pi fun _ : Y => Λ.μ) ≤ 1 := by
        rw [← lintegral_glueLabel_of_eq Λ.μ hU G ω₀]
        have hgl : ∀ (ν : ↥(P.biUnion id) → Λ.Ω) (y : ↥(P.biUnion id)),
              glueLabel Y (P.biUnion id) ω₀ ν ⟨y, hcast y⟩ = ν y := by
          intro ν y
          simp only [glueLabel]
          rw [dif_pos y.2]
        simp only [G, hgl]
        refine hp.trans ?_
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        rw [Real.exp_le_one_iff]
        have h1 := hfit.κ_pos
        have h2 := hfit.κ₁_pos
        have hσ := hfit.σ_pos
        have h3' : 0 ≤ x * ℓ.κ * ℓ.threshold ^ 2 *
            (((torusHotLumps ℓ W).filter (· ⊆ P.biUnion id)).card : ℝ) := by
          positivity
        have h4 : 0 ≤ ℓ.κ₁ * x * ℓ.threshold ^ 2 *
            (excessLength ℓ (clusterRange x) (P.biUnion id) W : ℝ) := by
          positivity
        linarith
      have hpt : ∀ ω, ENNReal.ofReal (Dq n W Y ω * Real.exp (∑ y : Y, s (ω y))) ≤
          ENNReal.ofReal c * G ω := by
        intro ω
        by_cases hz : ∃ X ∈ P, Φ n W Y ω X = 0
        · obtain ⟨X, hX, h0⟩ := hz
          rw [hh.form n hs W Y ω hY, Finset.prod_eq_zero hX h0, mul_zero, zero_mul]
          simp
        · have hGω : G ω = ENNReal.ofReal ((∏ X ∈ P, Φ n W Y ω X) *
              Real.exp (∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
                  ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange x : ℝ) / 4), φ n y W Y ω) *
              Real.exp (∑ y : (P.biUnion id : Finset (TorusSite n)), s (ω ⟨y, hcast y⟩))) := by
            simp only [G]
            rw [if_neg hz]
          push Not at hz
          rw [hGω, ← ENNReal.ofReal_mul hc0]
          apply ENNReal.ofReal_le_ofReal
          rw [hh.form n hs W Y ω hY, sum_subtype_of_eq hU hcast fun y => s (ω y)]
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
              exact (le_abs_self _).trans (hfar n hs W Y ω y hY hz hy2)
            have h2 := Finset.sum_le_card_nsmul _ _ _ h1
            rw [nsmul_eq_mul] at h2
            have h3' : ((Finset.univ.filter (fun y : TorusSite n =>
                ¬ ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange x : ℝ) / 4)).card : ℝ) ≤
                Fintype.card (TorusSite n) := by
              exact_mod_cast Finset.card_le_univ _
            have h4 : 0 ≤ 2 * ℓ.E := by linarith
            nlinarith
          have hA : 0 ≤ x * actionAtLevel ℓ.coupling ℓ.side t
              (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W :=
            mul_nonneg hx.le (actionAtLevel_nonneg (by linarith [hfit.a_ge]) _ _ _ _)
          have hprod : 0 ≤ ∏ X ∈ P, Φ n W Y ω X :=
            Finset.prod_nonneg fun X _ => hh.factor_nonneg n hs W Y ω X
          have hexp : Real.exp (-x * actionAtLevel ℓ.coupling ℓ.side t
                (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W + ∑ y, φ n y W Y ω) ≤
              Real.exp (2 * ℓ.E * Fintype.card (TorusSite n)) * Real.exp (∑ y ∈ near, φ n y W Y ω) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            rw [hsplit]
            linarith
          calc D n (trivialField n) * _ * _ * _ ≤ D n (trivialField n) *
                (Real.exp (2 * ℓ.E * Fintype.card (TorusSite n)) *
                Real.exp (∑ y ∈ near, φ n y W Y ω)) * (∏ X ∈ P, Φ n W Y ω X) *
                Real.exp (∑ y : (P.biUnion id : Finset (TorusSite n)), s (ω ⟨y, hcast y⟩)) := by gcongr
            _ = c * ((∏ X ∈ P, Φ n W Y ω X) * Real.exp (∑ y ∈ near, φ n y W Y ω) *
                Real.exp (∑ y : (P.biUnion id : Finset (TorusSite n)), s (ω ⟨y, hcast y⟩))) := by
              rw [hcdef]
              ring
      calc ∫⁻ ω, ENNReal.ofReal (Dq n W Y ω * Real.exp (∑ y : Y, s (ω y))) ∂(Measure.pi fun _ : Y => Λ.μ)
          ≤ ∫⁻ ω, ENNReal.ofReal c * G ω ∂(Measure.pi fun _ : Y => Λ.μ) := lintegral_mono hpt
        _ = ENNReal.ofReal c * ∫⁻ ω, G ω ∂(Measure.pi fun _ : Y => Λ.μ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal c * 1 := by gcongr
        _ = ENNReal.ofReal c := mul_one _
    · have : IsEmpty (Y → Λ.Ω) := not_nonempty_iff.mp hne
      simp
  have hgoal : D n (trivialField n) * 2 ^ Fintype.card (TorusSite n) *
      Real.exp (2 * ℓ.E * Fintype.card (TorusSite n)) = 2 ^ Fintype.card (TorusSite n) * c := by
    rw [hcdef]
    ring
  rw [hgoal]
  refine (Finset.sum_le_card_nsmul _ _ _ key).trans ?_
  rw [nsmul_eq_mul, show ENNReal.ofReal (2 ^ Fintype.card (TorusSite n) * c) =
    ENNReal.ofReal (2 ^ Fintype.card (TorusSite n)) * ENNReal.ofReal c from
    ENNReal.ofReal_mul (by positivity)]
  have hcard : (Finset.univ.filter (IsHullState ℓ (clusterRange x) W)).card ≤
      2 ^ Fintype.card (TorusSite n) := by
    refine (Finset.card_le_univ _).trans ?_
    rw [Fintype.card_finset]
  have : ((Finset.univ.filter (IsHullState ℓ (clusterRange x) W)).card : ENNReal) ≤
      ((2 ^ Fintype.card (TorusSite n) : ℕ) : ENNReal) := by exact_mod_cast hcard
  have h2e : ((2 ^ Fintype.card (TorusSite n) : ℕ) : ENNReal) =
      ENNReal.ofReal ((2 : ℝ) ^ Fintype.card (TorusSite n)) := by
    rw [show ((2 : ℝ) ^ Fintype.card (TorusSite n)) = ((2 ^ Fintype.card (TorusSite n) : ℕ) : ℝ) by
      push_cast; rfl, ENNReal.ofReal_natCast]
  rw [h2e] at this
  exact mul_le_mul' this (le_refl _)
end YangMills.Construction.ResponseInTheExpansion
end
