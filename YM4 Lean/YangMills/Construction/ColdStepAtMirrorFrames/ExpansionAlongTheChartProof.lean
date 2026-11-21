import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAlongTheChart
import YangMills.Construction.ColdStepAtMirrorFrames.SecondDerivativeThroughTheChart
import YangMills.Construction.ColdStepAtMirrorFrames.SumsAgainstFlatResponsesProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages FamilyNorms
namespace ColdStepAtMirrorFrames
namespace CentredFamilyInChart
theorem one_le_torusDecayFactor (L : ℕ) {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) : 1 ≤ torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.one_le_decayWeight <;> assumption
variable {F : BlockFrame}
theorem bondSpan_singleton {j : ℕ} (y : F.Site j) (b : F.Site j × Fin 4) : bondSpan y ![b] = siteSupDist y b.1 := by
  unfold bondSpan
  have e₁ : (Finset.univ.sup fun l : Fin 1 => siteSupDist y ((![b] : Fin 1 → F.Site j × Fin 4) l).1) = siteSupDist y b.1 := by
    simp
  have e₂ : (Finset.univ.sup fun l : Fin 1 => Finset.univ.sup fun l' : Fin 1 =>
      siteSupDist ((![b] : Fin 1 → F.Site j × Fin 4) l).1 ((![b] : Fin 1 → F.Site j × Fin 4) l').1) = 0 := by
    simp [siteSupDist]
  rw [e₁, e₂]
  simp
end CentredFamilyInChart
open CentredFamilyInChart in
theorem centredFamilyInChartBounds_of_secondDeriv (hsecond : ChartSecondDerivBound) :
    CentredFamilyInChartBounds := by
  obtain ⟨C, hC, hsd⟩ := hsecond
  refine ⟨C ^ 2 + C + 1, by positivity, ?_⟩
  intro L t n₀ σ δ ε ε₃ f hδ hε hfam F w V y hT hcold hw
  have hs := hfam.smooth F hT y _ hcold
  obtain ⟨hcd, _, hbd⟩ := hsd F V w ℝ (f F y) hw hs
  have e₀ : readInChart (subtractTrivial f F y) w V =
      fun η => readInChart (f F y) w V η - f F y (uniformField F F.depth) := rfl
  have hfd : ∀ ζ, fderiv ℝ (readInChart (subtractTrivial f F y) w V) ζ = fderiv ℝ (readInChart (f F y) w V) ζ := fun ζ => by
    rw [e₀]
    exact fderiv_sub_const _
  have hsec : ∀ u v, secondDerivAlong (readInChart (subtractTrivial f F y) w V) 0 u v =
      fderiv ℝ (fun ζ => fderiv ℝ (readInChart (f F y) w V) ζ u) 0 v := fun u v => by
    unfold secondDerivAlong
    simp only [hfd]
  have hB := hbd (fun b => ε / torusDecayFactor L δ (siteSupDist y b.1.1)) (fun _ _ => ε)
    (fun b X hX => by
      have h := hfam.decay F hT y _ 1 ![b.1] ![X] hcold le_rfl (by norm_num) (fun l => by
        fin_cases l
        exact hX)
      rw [bondSpan_singleton] at h
      simpa using h)
    (fun b b' X X' hX hX' => by
      have h := hfam.decay F hT y _ 2 ![b'.1, b.1] ![X', X] hcold (by norm_num) (by norm_num) (fun l => by
        fin_cases l
        · exact hX'
        · exact hX)
      have hw₁ := one_le_torusDecayFactor L (x := bondSpan y ![b'.1, b.1]) hδ (by positivity)
      have h₂ : ε / torusDecayFactor L δ (bondSpan y ![b'.1, b.1]) ≤ ε :=
        div_le_self hε hw₁
      rw [Real.norm_eq_abs]
      refine h.trans ?_
      simpa using h₂)
  refine ⟨?_, fun b e => ?_, fun b e => ?_⟩
  · rw [e₀]
    exact hcd.sub contDiffAt_const
  · rw [hfd]
    have h := (hB b b e e).1
    rw [Real.norm_eq_abs] at h
    have hw₁ := one_le_torusDecayFactor L (x := siteSupDist y b.1.1) hδ (by positivity)
    have hpos : 0 < torusDecayFactor L δ (siteSupDist y b.1.1) := by linarith
    refine h.trans ?_
    have e₁ : C * (ε / torusDecayFactor L δ (siteSupDist y b.1.1)) * ‖e‖ =
        C * ε * ‖e‖ / torusDecayFactor L δ (siteSupDist y b.1.1) := by ring
    rw [e₁]
    refine div_le_div_of_nonneg_right ?_ hpos.le
    have h₀ : 0 ≤ ε * ‖e‖ := by positivity
    nlinarith [sq_nonneg C]
  · rw [hsec]
    have h := (hB b b e e).2
    simp only [if_true] at h
    rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    have hw₁ := one_le_torusDecayFactor L (x := siteSupDist y b.1.1) hδ (by positivity)
    have h₂ : ε / torusDecayFactor L δ (siteSupDist y b.1.1) ≤ ε := div_le_self hε hw₁
    have hen : 0 ≤ ‖e‖ * ‖e‖ := by positivity
    calc (C ^ 2 * ε + C * (ε / torusDecayFactor L δ (siteSupDist y b.1.1))) * ‖e‖ * ‖e‖
        ≤ (C ^ 2 * ε + C * ε) * ‖e‖ * ‖e‖ := by
          have hCε : C * (ε / torusDecayFactor L δ (siteSupDist y b.1.1)) ≤ C * ε := mul_le_mul_of_nonneg_left h₂ hC.le
          nlinarith [mul_le_mul_of_nonneg_right hCε hen]
      _ ≤ (C ^ 2 + C + 1) * ε * ‖e‖ ^ 2 := by nlinarith [mul_nonneg hε hen]
end ColdStepAtMirrorFrames
end YangMills.Construction
end
