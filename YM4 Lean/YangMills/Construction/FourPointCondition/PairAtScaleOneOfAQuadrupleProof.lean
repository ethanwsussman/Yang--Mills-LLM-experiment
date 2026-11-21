import YangMills.Construction.Continuum.ChosenSmoothFunctionsPartitionsOfUnityRotationsAndIntegrabilityProof
import YangMills.Construction.FourPointCondition.PairAtScaleOneOfAQuadruple
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPair
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace YangMills.Construction
open TestFunctions TorusMetric
namespace FourPointBounds
private theorem euclidNormVec_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (v : Fin 4 → ℝ) :
    euclidNormVec (c • v) = c * euclidNormVec v := by apply _root_.YangMills.Construction.WightmanReconstruction.SmoothToolkit.euclidNormVec_smul_of_nonneg <;> assumption
private theorem euclidDistR4_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (x y : Fin 4 → ℝ) :
    euclidDistR4 (c • x) (c • y) = c * euclidDistR4 x y := by
  unfold euclidDistR4
  rw [← smul_sub, euclidNormVec_smul_of_nonneg hc]
private theorem tsupport_dilate_div {d c : ℝ} (hd : d ≠ 0) (hc : c ≠ 0) (u : (Fin 4 → ℝ) → ℝ) :
    tsupport (fun y => u (d • y) / c) = (fun y : Fin 4 → ℝ => d • y) ⁻¹' tsupport u := by
  have hpre := (Homeomorph.smulOfNeZero d hd (α := Fin 4 → ℝ)).preimage_closure (Function.support u)
  have hsupp : Function.support (fun y => u (d • y) / c) =
      (Homeomorph.smulOfNeZero d hd (α := Fin 4 → ℝ)) ⁻¹' Function.support u := by
    ext y
    simp [Function.mem_support, hc]
  unfold tsupport
  rw [hsupp, ← hpre]
  rfl
private theorem setDistR4_eq_mul_preimage_dilate {d : ℝ} (hd : 0 < d) (A B : Set (Fin 4 → ℝ)) :
    setDistR4 A B =
      ENNReal.ofReal d * setDistR4 ((fun y : Fin 4 → ℝ => d • y) ⁻¹' A)
        ((fun y : Fin 4 → ℝ => d • y) ⁻¹' B) := by
  have hsurj : Function.Surjective (fun y : Fin 4 → ℝ => d • y) := fun z =>
    ⟨d⁻¹ • z, by simp [smul_smul, hd.ne']⟩
  have hzero : ENNReal.ofReal d ≠ 0 := by simpa using hd
  have htop : ENNReal.ofReal d ≠ ∞ := ENNReal.ofReal_ne_top
  conv_lhs => rw [← image_preimage_eq A hsurj, ← image_preimage_eq B hsurj]
  unfold setDistR4
  simp only [iInf_image, ENNReal.mul_iInf_of_ne hzero htop]
  refine iInf_congr fun a => iInf_congr fun _ => iInf_congr fun b => iInf_congr fun _ => ?_
  rw [← smul_sub, euclidNormVec_smul_of_nonneg hd.le, ENNReal.ofReal_mul hd.le]
private theorem isShapedBump_unit_of_rescale {d κ : ℝ} (hd : 0 < d) (hκ : 0 < κ) {x : Fin 4 → ℝ}
    {u : (Fin 4 → ℝ) → ℝ}
    (hu : IsShapedBump euclidDistR4 closedBallR4 (fun f => ∫ y, f y) d κ x u) (hbd : IsBoundedFun u) :
    0 < uniformNorm u ∧
      IsShapedBump euclidDistR4 closedBallR4 (fun f => ∫ y, f y) 1 κ (d⁻¹ • x)
        (fun y => u (d • y) / uniformNorm u) ∧
      uniformNorm (fun y => u (d • y) / uniformNorm u) = 1 := by
  obtain ⟨hLip, hnonneg, ⟨y₀, hy₀⟩, hsupp, hmass, hlipc⟩ := hu
  obtain ⟨M, hM⟩ := hbd
  have hbdd : BddAbove (range fun y => ‖u y‖) := ⟨M, by rintro _ ⟨y, rfl⟩; exact hM y⟩
  have hle : ∀ y, ‖u y‖ ≤ uniformNorm u := fun y => le_ciSup hbdd y
  have hNpos : 0 < uniformNorm u := lt_of_lt_of_le (norm_pos_iff.2 hy₀) (hle y₀)
  set N := uniformNorm u with hNdef
  have hnormdiv : ∀ y, ‖u (d • y) / N‖ = ‖u (d • y)‖ / N := fun y => by
    rw [norm_div, Real.norm_of_nonneg hNpos.le]
  have hunit : uniformNorm (fun y => u (d • y) / N) = 1 := by
    have hbdd' : BddAbove (range fun y => ‖u (d • y) / N‖) :=
      ⟨1, by
        rintro _ ⟨y, rfl⟩
        simp only [hnormdiv]
        exact (div_le_one hNpos).2 (hle _)⟩
    refine le_antisymm ?_ ?_
    · refine ciSup_le fun y => ?_
      rw [hnormdiv]
      exact (div_le_one hNpos).2 (hle _)
    · have hmul : N ≤ uniformNorm (fun y => u (d • y) / N) * N := by
        refine ciSup_le fun z => ?_
        have hz : ‖u (d • d⁻¹ • z) / N‖ ≤ uniformNorm (fun y => u (d • y) / N) := le_ciSup hbdd' (d⁻¹ • z)
        have hzz : d • d⁻¹ • z = z := by simp [smul_smul, hd.ne']
        rw [hnormdiv, hzz] at hz
        have hz' := mul_le_mul_of_nonneg_right hz hNpos.le
        rwa [div_mul_cancel₀ _ hNpos.ne'] at hz'
      exact le_of_mul_le_mul_right (by simpa using hmul) hNpos
  have hconst : ∀ C : ℝ, (0 ≤ C ∧ ∀ a b, ‖u a - u b‖ ≤ C * euclidDistR4 a b) →
      (0 ≤ C * d / N ∧ ∀ a b, ‖u (d • a) / N - u (d • b) / N‖ ≤ C * d / N * euclidDistR4 a b) := by
    rintro C ⟨hC, hCab⟩
    refine ⟨by positivity, fun a b => ?_⟩
    rw [← sub_div, norm_div, Real.norm_of_nonneg hNpos.le, div_le_iff₀ hNpos]
    have hab := hCab (d • a) (d • b)
    rw [euclidDistR4_smul_of_nonneg hd.le] at hab
    calc _ ≤ _ := hab
      _ = _ := by field_simp
  refine ⟨hNpos, ⟨?_, fun y => div_nonneg (hnonneg _) hNpos.le, ⟨d⁻¹ • y₀, ?_⟩, ?_, ?_, ?_⟩, hunit⟩
  · obtain ⟨C, hC, hCab⟩ := hLip
    exact ⟨C * d / N, (hconst C ⟨hC, hCab⟩).1, (hconst C ⟨hC, hCab⟩).2⟩
  · have hyy : d • d⁻¹ • y₀ = y₀ := by simp [smul_smul, hd.ne']
    simp only [hyy]
    exact div_ne_zero hy₀ hNpos.ne'
  · rw [tsupport_dilate_div hd.ne' hNpos.ne']
    intro y hy
    have hin := hsupp hy
    have hball : euclidNormVec (d • y - x) ≤ d := hin
    have hshift : d • y - x = d • (y - d⁻¹ • x) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
    rw [hshift, euclidNormVec_smul_of_nonneg hd.le] at hball
    change euclidNormVec (y - d⁻¹ • x) ≤ 1
    exact le_of_mul_le_mul_left (by simpa using hball) hd
  · rw [hunit]
    have hint : (∫ y, u (d • y) / N) = (d ^ 4)⁻¹ * (∫ y, u y) / N := by
      rw [integral_div, Measure.integral_comp_smul]
      simp [abs_of_pos hd]
    change κ * 1 * 1 ^ 4 ≤ ∫ y, u (d • y) / N
    rw [hint]
    rw [le_div_iff₀ hNpos, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    linarith
  · rw [hunit]
    have hne : {C : ℝ | 0 ≤ C ∧ ∀ a b, ‖u a - u b‖ ≤ C * euclidDistR4 a b}.Nonempty := by
      obtain ⟨C, hC, hCab⟩ := hLip
      exact ⟨C, hC, hCab⟩
    have hbelow : BddBelow {C : ℝ | 0 ≤ C ∧ ∀ a b, ‖u (d • a) / N - u (d • b) / N‖ ≤ C * euclidDistR4 a b} :=
      ⟨0, fun C hC => hC.1⟩
    set L := bestLipschitzConstant euclidDistR4 (fun y => u (d • y) / N) with hL
    have hcmp : N / d * L ≤ bestLipschitzConstant euclidDistR4 u := by
      refine le_csInf hne fun C hC => ?_
      have hLC : L ≤ C * d / N := csInf_le hbelow (hconst C hC)
      have hLC' := mul_le_mul_of_nonneg_left hLC (by positivity : 0 ≤ N / d)
      calc _ ≤ _ := hLC'
        _ = C := by field_simp
    have hchain := hcmp.trans hlipc
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hd (by positivity)] at hchain
    rw [mul_one, le_div_iff₀ hκ]
    have hprod : N * (L * κ * d) ≤ N * d := by nlinarith
    have hcancel := le_of_mul_le_mul_left hprod hNpos
    exact le_of_mul_le_mul_right (by simpa using hcancel) hd
theorem unitScalePairOfQuadruple_of_geometry (hG : TestPairs.GeometryAndKernelBounds) :
    UnitScalePairOfQuadruple := by
  rintro s d κ f ⟨-, g, -, hg, -⟩
  obtain ⟨⟨hd, hκ⟩, hq⟩ := hg
  have hpair : (g 0, g 1) ∈ separatedPairsR4 d κ := hq.2 0 1 (by decide)
  obtain ⟨x₁, x₂, hu₁, hu₂, hlow, hhigh⟩ := id hpair
  have hcent : IsCentrePairR4 d κ x₁ x₂ (g 0, g 1) :=
    ⟨⟨hu₁.2.2.2.1, hu₁.2.2.2.2.1, hu₁.2.2.2.2.2⟩, ⟨hu₂.2.2.2.1, hu₂.2.2.2.2.1, hu₂.2.2.2.2.2⟩, hlow, hhigh⟩
  have hker := ((hG.1 d κ ⟨hd, hκ⟩ x₁ x₂ (g 0) (g 1) hpair hcent).1).2.2.2.1
  obtain ⟨hN₁, hv₁, hn₁⟩ := isShapedBump_unit_of_rescale (u := g 0) hd hκ.1 hu₁ hker.1
  obtain ⟨hN₂, hv₂, hn₂⟩ := isShapedBump_unit_of_rescale (u := g 1) hd hκ.1 hu₂ hker.2.1
  have hdist := setDistR4_eq_mul_preimage_dilate hd (tsupport (g 0)) (tsupport (g 1))
  have hzero : ENNReal.ofReal d ≠ 0 := by simpa using hd
  have htop : ENNReal.ofReal d ≠ ∞ := ENNReal.ofReal_ne_top
  have hlow' : ENNReal.ofReal d ≤ setDistR4 (tsupport (g 0)) (tsupport (g 1)) := hlow
  have hhigh' : setDistR4 (tsupport (g 0)) (tsupport (g 1)) ≤ ENNReal.ofReal (6 * d) := hhigh
  rw [hdist] at hlow' hhigh'
  refine ⟨_, _, ⟨d⁻¹ • x₁, d⁻¹ • x₂, hv₁, hv₂, ?_, ?_⟩, hn₁, hn₂⟩
  · simp only [tsupport_dilate_div hd.ne' hN₁.ne', tsupport_dilate_div hd.ne' hN₂.ne']
    refine (ENNReal.mul_le_mul_iff_right hzero htop).1 ?_
    rw [ENNReal.ofReal_one, mul_one]
    exact hlow'
  · simp only [tsupport_dilate_div hd.ne' hN₁.ne', tsupport_dilate_div hd.ne' hN₂.ne']
    refine (ENNReal.mul_le_mul_iff_right hzero htop).1 ?_
    rw [← ENNReal.ofReal_mul hd.le, mul_one, mul_comm d 6]
    exact hhigh'
end FourPointBounds
end YangMills.Construction
end
