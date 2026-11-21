import YangMills.Construction.LawOnABoxOfTheFlow.BorelBackgroundOfAFilling
import YangMills.Construction.LawOnABoxOfTheFlow.CurlOnTheSliceIsGaussian
import YangMills.Construction.LawOnABoxOfTheFlow.ToolsOfAChart
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields ResponseInTheExpansion BlockAverages RenormalizationStepParameters
set_option synthInstance.maxSize 1024
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
theorem borelBackgroundStatement_holds (hCurl : sliceCurlGaussianStatement)
    (hEll : ellipsoidBoundsStatement) (hHess : cubeHessianStatement) :
    borelBackgroundStatement := by
  intro Tb hTb κ₀ h1 h2
  obtain ⟨C, x₁, hc⟩ := hCurl Tb hTb κ₀ h1 h2
  obtain ⟨CQ, R₀, hCQ, hf⟩ := hHess Tb hTb
  have hC₀ : 0 < CQ * 2 ^ 13 := by positivity
  obtain ⟨K, x₂, hK1, hb⟩ := hEll Tb hTb κ₀ h1 h2 (CQ * 2 ^ 13) hC₀
  refine ⟨C, max (max x₁ x₂) (((R₀ : ℝ) + 2) ^ 27), ?_⟩
  intro x R k n _ o hx hR hn
  have hx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx₂ : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hfl : ((R₀ + 1 : ℕ) + 1 : ℝ) ^ 27 ≤ x := by
    have := le_trans (le_max_right _ _) hx
    push_cast
    calc ((R₀ : ℝ) + 1 + 1) ^ 27 = ((R₀ : ℝ) + 2) ^ 27 := by ring
      _ ≤ x := this
  have hRR : R₀ + 1 ≤ R := by
    rw [hR]
    exact le_boxRadius κ₀ x h1 (R₀ + 1) hfl
  have hR1 : 1 ≤ R := by omega
  obtain ⟨-, -, -, hlin, hqf, -, hform⟩ := hf k n o R (by omega) hn
  set δ := boxScale x with hδ
  set S := supBall o (2 * (R : ℝ)) with hS
  classical
  have hex : ∀ A : TorusBond n → imaginaryQuaternions, IsAxialSmall o R δ A →
      ∃ B : TorusBond n → imaginaryQuaternions, B - A ∈ gaugeSlice o R A ∧
      (∀ η : TorusBond n → imaginaryQuaternions, (∀ b, b ∉ bondsTouching o R → η b = 0) →
        hessianForm Tb.coupling Tb.side k S B η = 0) ∧
      curlNormSq S B ≤ C * (R : ℝ) ^ 4 * δ ^ 2 ∧
      (∀ b ∈ bondsWithin S, ‖B b‖ ≤ C * (R : ℝ) ^ 3 * δ) ∧
      hessianForm Tb.coupling Tb.side k S B B ≤ hessianForm Tb.coupling Tb.side k S A A ∧
      ∀ u : TorusPlaquette n → Fin 3 → ℝ,
        (sliceGaussian Tb.coupling Tb.side k o R x A).map
            (fun ζ => colourPairing S u fun p => lieFormCurl (A + ζ) p - lieFormCurl B p) =
          gaussianReal 0 (x⁻¹ * curlQuadForm Tb.coupling Tb.side k o R u).toNNReal := fun A hA =>
    hc x R k n o A hx₁ hR hn hA
  let φ : (TorusBond n → imaginaryQuaternions) → TorusBond n → imaginaryQuaternions := fun A =>
    if h : IsAxialSmall o R δ A then (hex A h).choose - A else 0
  have hφ : ∀ A (h : IsAxialSmall o R δ A), A + φ A = (hex A h).choose := by
    intro A h
    simp only [φ, dif_pos h]
    abel
  have hEc : IsClosed {A | IsAxialSmall o R δ A} := isClosed_setOf_isAxialSmall o R δ
  have hcut : ∀ v : TorusBond n → imaginaryQuaternions,
      Continuous fun u : TorusBond n → imaginaryQuaternions =>
        hessianForm Tb.coupling Tb.side k S u v := by
    intro v
    have : (fun u : TorusBond n → imaginaryQuaternions =>
        hessianForm Tb.coupling Tb.side k S u v) = fun u =>
        ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
          mixedDeriv (actionAtLevel Tb.coupling Tb.side k S) (trivialField n) ![b, b']
              ![imaginaryUnitI, imaginaryUnitI] *
            imaginaryComponent e (u b) * imaginaryComponent e (v b') := funext fun u => hform u v
    rw [this]
    refine continuous_finset_sum _ fun e _ => continuous_finset_sum _ fun b _ =>
      continuous_finset_sum _ fun b' _ => ?_
    exact (continuous_const.mul ((continuous_imaginaryComponent e).comp (continuous_apply b))).mul
      continuous_const
  let Gr : Set ((TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions)) :=
    {p | p.2 ∈ gaugeSlice o R p.1} ∩
      ⋂ η ∈ {η : TorusBond n → imaginaryQuaternions | ∀ b, b ∉ bondsTouching o R → η b = 0},
        {p | hessianForm Tb.coupling Tb.side k S (p.1 + p.2) η = 0}
  have hGr : IsClosed Gr := by
    refine (isClosed_gaugeSlice_graph o R).inter (isClosed_biInter fun η _ => ?_)
    exact isClosed_eq ((hcut η).comp (continuous_fst.add continuous_snd)) continuous_const
  set M : ℝ := K * (R : ℝ) ^ 3 * δ with hM
  let Kb : Set (TorusBond n → imaginaryQuaternions) :=
    Set.pi Set.univ fun _ => Metric.closedBall 0 M
  have hKb : IsCompact Kb := isCompact_univ_pi fun _ => isCompact_closedBall 0 M
  have hKφ : ∀ A, IsAxialSmall o R δ A → φ A ∈ Kb := by
    intro A hA b _
    have hs := (hex A hA).choose_spec
    have he : φ A = (hex A hA).choose - A := by simp only [φ, dif_pos hA]
    have hell : φ A ∈ sliceEllipsoid Tb.coupling Tb.side k o R A
        (CQ * 2 ^ 13 * (R : ℝ) ^ 4 * δ ^ 2) := by
      refine ⟨he ▸ hs.1, ?_⟩
      rw [hφ A hA]
      refine le_trans hs.2.2.2.2.1 (le_trans (hqf A).2 ?_)
      have := hA.curlNormSq_le
      nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ CQ)]
    have := (hb x R k n o A hx₂ hR hn hA).2 _ hell
    simpa [M, mem_closedBall_zero_iff] using this.2.1 b
  have hone : ∀ A ∈ {A | IsAxialSmall o R δ A}, ∀ v, (A, v) ∈ Gr → v ∈ Kb → v = φ A := by
    rintro A (hA : IsAxialSmall o R δ A) v hv -
    have hs := (hex A hA).choose_spec
    have he : φ A = (hex A hA).choose - A := by simp only [φ, dif_pos hA]
    have hsl : φ A ∈ gaugeSlice o R A := he ▸ hs.1
    have hvs : v ∈ gaugeSlice o R A := hv.1
    set η := v - φ A with hη
    have hηs : η ∈ gaugeSlice o R A := (gaugeSlice o R A).sub_mem hvs hsl
    have hsupp : ∀ b, b ∉ bondsTouching o R → η b = 0 := hηs.1
    have e1 : hessianForm Tb.coupling Tb.side k S (A + v) η = 0 := by
      have := Set.mem_iInter₂.1 hv.2 η hsupp
      exact this
    have e2 : hessianForm Tb.coupling Tb.side k S (A + φ A) η = 0 := by
      rw [hφ A hA]
      exact hs.2.1 η hsupp
    have e3 : hessianForm Tb.coupling Tb.side k S η η = 0 := by
      have hdec : η = (1 : ℝ) • (A + v) + (-(A + φ A)) := by
        rw [hη]; simp; abel
      have hneg : (-(A + φ A)) = (-1 : ℝ) • (A + φ A) + 0 := by
        rw [add_zero]
        funext b
        simp
        abel
      have h0 : hessianForm Tb.coupling Tb.side k S 0 η = 0 := by
        have h := hlin 1 0 0 η
        simp only [smul_zero, add_zero, one_mul] at h
        linarith
      rw [show hessianForm Tb.coupling Tb.side k S η η =
          hessianForm Tb.coupling Tb.side k S ((1 : ℝ) • (A + v) + (-(A + φ A))) η by
        rw [← hdec], hlin, hneg, hlin, e1, e2, h0]
      ring
    have hco := (hb x R k n o A hx₂ hR hn hA).1 η hηs
    rw [e3] at hco
    have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
    have hcK := hTb.cK_pos
    have hzero : bondNormSq S η ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      have : 0 < 2 * Tb.coercivity * ((R : ℝ) ^ 2)⁻¹ * bondNormSq S η := by positivity
      linarith
    have hall : ∀ b ∈ bondsWithin S, ‖η b‖ ^ 2 = 0 := by
      have hsum : ∑ b ∈ bondsWithin S, ‖η b‖ ^ 2 = 0 :=
        le_antisymm hzero (Finset.sum_nonneg fun b _ => by positivity)
      exact (Finset.sum_eq_zero_iff_of_nonneg fun b _ => by positivity).1 hsum
    have hηz : η = 0 := by
      funext b
      by_cases hbi : b ∈ bondsTouching o R
      · have := hall b (mem_bondsWithin_of_mem_bondsTouching hR1 hbi)
        simpa using this
      · exact hsupp b hbi
    exact sub_eq_zero.1 hηz
  have hcont : ContinuousOn φ {A | IsAxialSmall o R δ A} := by
    refine continuousOn_of_isClosed_graph_of_isCompact hKb hEc hGr
      (fun A (hA : IsAxialSmall o R δ A) => ?_) hone
    have hs := (hex A hA).choose_spec
    have he : φ A = (hex A hA).choose - A := by simp only [φ, dif_pos hA]
    refine ⟨⟨he ▸ hs.1, ?_⟩, hKφ A hA⟩
    refine Set.mem_iInter₂.2 fun η hη => ?_
    show hessianForm Tb.coupling Tb.side k S (A + φ A) η = 0
    rw [hφ A hA]
    exact hs.2.1 η hη
  refine ⟨{A | IsAxialSmall o R δ A}.piecewise (fun A => A + φ A) (fun _ => 0), ?_, ?_⟩
  · exact (continuousOn_id.add hcont).measurable_piecewise continuousOn_const hEc.measurableSet
  · intro A hA
    have hpw : {A | IsAxialSmall o R δ A}.piecewise (fun A => A + φ A) (fun _ => 0) A =
        (hex A hA).choose := by
      rw [Set.piecewise_eq_of_mem _ _ _ (show A ∈ {A | IsAxialSmall o R δ A} from hA), hφ A hA]
    rw [hpw]
    have hs := (hex A hA).choose_spec
    exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.2⟩
end YangMills.Construction.BoxGaussian
end
