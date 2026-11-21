import YangMills.Construction.ColdStepAtMirrorFrames.DistancesOfSitesAndCells
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionTermsOfTheExponent
import YangMills.Construction.ColdStepAtMirrorFrames.SecondDerivativeThroughTheChart
import YangMills.Construction.ColdStepAtMirrorFrames.SecondDerivativesOfSums
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames.SeriesExpansionTerms
variable {F : BlockFrame}
theorem exp_le_torusDecayFactor {L : ℕ} {δ x : ℝ} : Real.exp (δ * x) ≤ torusDecayFactor L δ x := by
  unfold torusDecayFactor
  have h1 : (1 : ℝ) ≤ max 1 ((x / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) := le_max_left _ _
  have h2 := Real.exp_pos (δ * x)
  nlinarith
theorem div_torusDecayFactor_le {L : ℕ} {δ x E : ℝ} (hE : 0 ≤ E) :
    E / torusDecayFactor L δ x ≤ E * Real.exp (-(δ * x)) := by
  rw [Real.exp_neg, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ hE
  exact inv_anti₀ (Real.exp_pos _) exp_le_torusDecayFactor
theorem contDiffThreeAlongBonds_subtractTrivial {f : LocalFamily} {y : F.Site F.depth}
    {W : F.GaugeField F.depth} (h : ContDiffThreeAlongBonds (f F y) W) :
    ContDiffThreeAlongBonds (subtractTrivial f F y) W := fun k c X =>
  (h k c X).sub contDiffAt_const
theorem bondDeriv_subtractTrivial {f : LocalFamily} {y : F.Site F.depth} {W : F.GaugeField F.depth}
    (h : ContDiffThreeAlongBonds (f F y) W) {k : ℕ} (hk : 1 ≤ k) (hk3 : k ≤ 3)
    (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv (subtractTrivial f F y) W c X = bondDeriv (f F y) W c X := by
  unfold bondDeriv subtractTrivial
  have hc : ContDiffAt ℝ k (fun τ : Fin k → ℝ => f F y (leftTranslate (bondSpread c X τ) W)) 0 :=
    (h k c X).of_le (by exact_mod_cast hk3)
  have h1 : (fun τ : Fin k → ℝ => f F y (leftTranslate (bondSpread c X τ) W) -
      f F y (uniformField F F.depth)) =
        (fun τ : Fin k → ℝ => f F y (leftTranslate (bondSpread c X τ) W)) +
        fun _ => -f F y (uniformField F F.depth) := by
    funext τ
    simp [sub_eq_add_neg]
  rw [h1, iteratedFDeriv_add_apply hc contDiffAt_const,
    iteratedFDeriv_const_of_ne (by omega : k ≠ 0)]
  simp
theorem siteSupDist_le_bondSpan_one (y : F.Site F.depth) (b : F.Site F.depth × Fin 4) :
    siteSupDist y b.1 ≤ bondSpan y ![b] := by
  unfold bondSpan
  refine le_trans ?_ (le_max_left _ _)
  exact Finset.le_sup (f := fun l : Fin 1 => siteSupDist y ((![b] : Fin 1 → _) l).1) (Finset.mem_univ 0)
theorem siteSupDist_le_bondSpan_two (y : F.Site F.depth) (b b' : F.Site F.depth × Fin 4) :
    siteSupDist y b.1 ≤ bondSpan y ![b, b'] ∧ siteSupDist y b'.1 ≤ bondSpan y ![b, b'] ∧
      siteSupDist b.1 b'.1 ≤ bondSpan y ![b, b'] := by
  unfold bondSpan
  refine ⟨le_trans ?_ (le_max_left _ _), le_trans ?_ (le_max_left _ _),
    le_trans ?_ (le_max_right _ _)⟩
  · exact Finset.le_sup (f := fun l : Fin 2 => siteSupDist y ((![b, b'] : Fin 2 → _) l).1)
      (Finset.mem_univ 0)
  · exact Finset.le_sup (f := fun l : Fin 2 => siteSupDist y ((![b, b'] : Fin 2 → _) l).1)
      (Finset.mem_univ 1)
  · have h1 : siteSupDist b.1 b'.1 ≤ Finset.univ.sup fun l' : Fin 2 =>
        siteSupDist ((![b, b'] : Fin 2 → _) 0).1 ((![b, b'] : Fin 2 → _) l').1 :=
      Finset.le_sup (f := fun l' : Fin 2 => siteSupDist ((![b, b'] : Fin 2 → _) 0).1
        ((![b, b'] : Fin 2 → _) l').1) (Finset.mem_univ 1)
    exact h1.trans (Finset.le_sup (f := fun l : Fin 2 => Finset.univ.sup fun l' : Fin 2 =>
      siteSupDist ((![b, b'] : Fin 2 → _) l).1 ((![b, b'] : Fin 2 → _) l').1) (Finset.mem_univ 0))
set_option maxHeartbeats 2000000 in
theorem expansionTermsChartBounds_holds (hC : ChartSecondDerivBound) (hSum : Calculus.FderivFinsetSum)
    (hD : SupDistCellComparison) : ExpansionTermsChartBounds := by
  classical
  obtain ⟨C, hCpos, hC⟩ := hC
  refine ⟨C ^ 2 + C, by positivity, ?_⟩
  intro L t n₀ σ δ E E₃ f F V w hδ hE hrow hF hw hcold
  set W : F.GaugeField F.depth := chartedField w V with hW
  have hF' : F.depth = t := hF.2.1
  subst hF'
  set Sy := sitesOfCells (finiteCells F) F.depth with hSy
  have hsm : ∀ y : F.Site F.depth, ContDiffThreeAlongBonds (f F y) W := fun y =>
    hrow.smooth F hF y W hcold
  have hun1 : ∀ (y : F.Site F.depth) (b : ↥(chordBonds (finiteCells F))) (X : imaginaryQuaternions),
      ‖X‖ = 1 → ‖bondDeriv (subtractTrivial f F y) W ![b.1] ![X]‖ ≤
        E * Real.exp (-(δ * (siteSupDist y b.1.1 : ℝ))) := by
    intro y b X hX
    rw [bondDeriv_subtractTrivial (hsm y) le_rfl (by norm_num), Real.norm_eq_abs]
    have h1 := hrow.decay F hF y W 1 ![b.1] ![X] hcold le_rfl (by norm_num)
      (by intro l; fin_cases l; simpa using hX)
    simp only [show ¬ (1 : ℕ) = 3 by norm_num, if_false] at h1
    refine h1.trans (div_torusDecayFactor_le hE |>.trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ hE
    rw [Real.exp_le_exp]
    have h2 : (siteSupDist y b.1.1 : ℝ) ≤ bondSpan y ![b.1] := by
      exact_mod_cast siteSupDist_le_bondSpan_one y b.1
    have := mul_le_mul_of_nonneg_left h2 hδ
    linarith
  have hsymm : ∀ y z : F.Site F.depth, siteSupDist y z = siteSupDist z y := fun y z =>
    (hD.1 F F.depth y z y).2.1
  have hun2 : ∀ (y : F.Site F.depth) (b b' : ↥(chordBonds (finiteCells F)))
      (X X' : imaginaryQuaternions), ‖X‖ = 1 →
      ‖X'‖ = 1 → ‖bondDeriv (subtractTrivial f F y) W ![b'.1, b.1] ![X', X]‖ ≤
        E * Real.exp (-(δ / 3 * ((siteSupDist y b.1.1 : ℝ) + siteSupDist y b'.1.1 +
          siteSupDist b.1.1 b'.1.1))) := by
    intro y b b' X X' hX hX'
    rw [bondDeriv_subtractTrivial (hsm y) (by norm_num) (by norm_num), Real.norm_eq_abs]
    have h1 := hrow.decay F hF y W 2 ![b'.1, b.1] ![X', X] hcold (by norm_num) (by norm_num)
      (by intro l; fin_cases l <;> simpa using ‹_›)
    simp only [show ¬ (2 : ℕ) = 3 by norm_num, if_false] at h1
    refine h1.trans (div_torusDecayFactor_le hE |>.trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ hE
    rw [Real.exp_le_exp]
    obtain ⟨s1, s2, s3⟩ := siteSupDist_le_bondSpan_two y b'.1 b.1
    have r1 : (siteSupDist y b'.1.1 : ℝ) ≤ bondSpan y ![b'.1, b.1] := by exact_mod_cast s1
    have r2 : (siteSupDist y b.1.1 : ℝ) ≤ bondSpan y ![b'.1, b.1] := by exact_mod_cast s2
    have r3 : (siteSupDist b.1.1 b'.1.1 : ℝ) ≤ bondSpan y ![b'.1, b.1] := by
      rw [hsymm]
      exact_mod_cast s3
    have h4 : (siteSupDist y b.1.1 : ℝ) + siteSupDist y b'.1.1 + siteSupDist b.1.1 b'.1.1 ≤
        3 * (bondSpan y ![b'.1, b.1] : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_left h4 hδ
    linarith
  have hch : ∀ y : F.Site F.depth, _ := fun y =>
    hC F V w ℝ (subtractTrivial f F y) hw (contDiffThreeAlongBonds_subtractTrivial (hsm y))
  have hread : readInChart (centredExpansionSum f) w V =
      fun ζ => ∑ y ∈ Sy, readInChart (subtractTrivial f F y) w V ζ := rfl
  have hsum := hSum (StepVariable (finiteCells F)) (F.Site F.depth) Sy
    (fun y => readInChart (subtractTrivial f F y) w V) 0 (fun y _ => (hch y).1)
  rw [hread]
  refine ⟨hsum.1, fun b b' e e' => ?_⟩
  obtain ⟨hf1, hf2⟩ := hsum.2 (bondVariation b e) (bondVariation b' e')
  have hbd : ∀ y, _ := fun y => (hch y).2.2
    (fun b => E * Real.exp (-(δ * (siteSupDist y b.1.1 : ℝ))))
    (fun b' b => E * Real.exp (-(δ / 3 * ((siteSupDist y b.1.1 : ℝ) + siteSupDist y b'.1.1 +
      siteSupDist b.1.1 b'.1.1)))) (hun1 y) (hun2 y) b b' e e'
  have hne := norm_nonneg e
  have hne' := norm_nonneg e'
  constructor
  · rw [hf1]
    calc _ ≤ ∑ y ∈ Sy, |fderiv ℝ (readInChart (subtractTrivial f F y) w V) 0 (bondVariation b e)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ Sy, C * (E * Real.exp (-(δ * (siteSupDist y b.1.1 : ℝ)))) * ‖e‖ :=
          Finset.sum_le_sum fun y _ => by simpa using (hbd y).1
      _ = C * E * (∑ y ∈ Sy, Real.exp (-(δ * (siteSupDist y b.1.1 : ℝ)))) * ‖e‖ := by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
      _ ≤ _ := by
          have hs : 0 ≤ ∑ y ∈ Sy, Real.exp (-(δ * (siteSupDist y b.1.1 : ℝ))) :=
            Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
          have : 0 ≤ C ^ 2 * E * (∑ y ∈ Sy, Real.exp (-(δ * (siteSupDist y b.1.1 : ℝ)))) * ‖e‖ := by
            positivity
          nlinarith
  · rw [hf2]
    have hterm : ∀ y ∈ Sy, |fderiv ℝ (fun ζ => fderiv ℝ (readInChart (subtractTrivial f F y) w V) ζ
        (bondVariation b e)) 0 (bondVariation b' e')| ≤
        (C ^ 2 + C) * E * Real.exp (-(δ / 3 * ((siteSupDist y b.1.1 : ℝ) +
          siteSupDist y b'.1.1 + siteSupDist b.1.1 b'.1.1))) * ‖e‖ * ‖e'‖ := by
      intro y _
      have h1 := (hbd y).2
      rw [Real.norm_eq_abs] at h1
      refine h1.trans ?_
      have hx := Real.exp_pos (-(δ / 3 * ((siteSupDist y b.1.1 : ℝ) + siteSupDist y b'.1.1 +
        siteSupDist b.1.1 b'.1.1)))
      have hee : 0 ≤ ‖e‖ * ‖e'‖ := by positivity
      by_cases hbb : b = b'
      · subst hbb
        simp only [if_true]
        have hself : siteSupDist b.1.1 b.1.1 = 0 := (hD.1 F F.depth b.1.1 b.1.1 b.1.1).1
        have h2 : Real.exp (-(δ * (siteSupDist y b.1.1 : ℝ))) ≤ Real.exp (-(δ / 3 *
            ((siteSupDist y b.1.1 : ℝ) + siteSupDist y b.1.1 + siteSupDist b.1.1 b.1.1))) := by
          rw [Real.exp_le_exp, hself]
          have : 0 ≤ δ * (siteSupDist y b.1.1 : ℝ) := by positivity
          push_cast
          nlinarith
        have h3 : C * (E * Real.exp (-(δ * (siteSupDist y b.1.1 : ℝ)))) ≤
            C * (E * Real.exp (-(δ / 3 * ((siteSupDist y b.1.1 : ℝ) + siteSupDist y b.1.1 +
              siteSupDist b.1.1 b.1.1)))) := by gcongr
        calc _ = (C ^ 2 * (E * Real.exp (-(δ / 3 * ((siteSupDist y b.1.1 : ℝ) +
                siteSupDist y b.1.1 + siteSupDist b.1.1 b.1.1)))) +
                C * (E * Real.exp (-(δ * (siteSupDist y b.1.1 : ℝ))))) *
              (‖e‖ * ‖e'‖) := by ring
          _ ≤ (C ^ 2 * (E * Real.exp (-(δ / 3 * ((siteSupDist y b.1.1 : ℝ) +
                siteSupDist y b.1.1 + siteSupDist b.1.1 b.1.1)))) +
                C * (E * Real.exp (-(δ / 3 * ((siteSupDist y b.1.1 : ℝ) +
                siteSupDist y b.1.1 + siteSupDist b.1.1 b.1.1))))) * (‖e‖ * ‖e'‖) := by gcongr
          _ = _ := by ring
      · simp only [hbb, if_false, add_zero]
        have : 0 ≤ C * E * Real.exp (-(δ / 3 * ((siteSupDist y b.1.1 : ℝ) + siteSupDist y b'.1.1 +
            siteSupDist b.1.1 b'.1.1))) * ‖e‖ * ‖e'‖ := by positivity
        nlinarith
    calc _ ≤ ∑ y ∈ Sy, |fderiv ℝ (fun ζ => fderiv ℝ (readInChart (subtractTrivial f F y) w V) ζ
          (bondVariation b e)) 0 (bondVariation b' e')| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum hterm
      _ = _ := by
          unfold expansionDecayKernel
          rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
end YangMills.Construction.ColdStepAtMirrorFrames.SeriesExpansionTerms
end
