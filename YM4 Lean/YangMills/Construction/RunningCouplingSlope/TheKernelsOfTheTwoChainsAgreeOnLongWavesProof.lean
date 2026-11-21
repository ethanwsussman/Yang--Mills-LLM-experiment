import YangMills.Construction.RunningCouplingSlope.SizesOfTheLongWaves
import YangMills.Construction.RunningCouplingSlope.TheChainIsItsFunctionAtTheResponse
import YangMills.Construction.RunningCouplingSlope.TheKernelsOfTheTwoChainsAgreeOnLongWaves
import YangMills.Construction.RunningCouplingSlope.TheNormaliserReadsTheResponseOnLongWaves
import YangMills.Construction.RunningCouplingSlope.TheWaveOfTheKernelOfTheChain
import YangMills.Construction.RunningCouplingSlope.TheWaveOfTheKernelOfTheDifference
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
private theorem wave_term_le {c V t E tq nq wq : ℝ} (hc : 0 ≤ c) (hV : 0 < V) (ht : |t| ≤ 1)
    (hE : 0 ≤ E) (htq : tq ≤ c * V) (hnq : nq ≤ c * V * t ^ 4) (hwq : wq ≤ c * V) :
    Real.sqrt nq * Real.sqrt (Real.sqrt nq * Real.sqrt tq) + E * Real.sqrt wq * Real.sqrt nq + nq ≤
      V * (2 * c * |t| ^ 3 + E * c) := by
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have hcV : 0 ≤ c * V := by positivity
  have sq_le : ∀ {x y : ℝ}, 0 ≤ y → x ≤ y * y → Real.sqrt x ≤ y := fun hy h =>
    Real.sqrt_le_iff.mpr ⟨hy, by nlinarith⟩
  set q := Real.sqrt (c * V) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q * q = c * V := Real.mul_self_sqrt hcV
  have h1 : Real.sqrt tq ≤ q := sq_le hq0 (by rw [hq2]; exact htq)
  have h2 : Real.sqrt nq ≤ q * t ^ 2 := by
    refine sq_le (by positivity) ?_
    calc nq ≤ c * V * t ^ 4 := hnq
      _ = (q * t ^ 2) * (q * t ^ 2) := by rw [← hq2]; ring
  have h3 : Real.sqrt wq ≤ q := sq_le hq0 (by rw [hq2]; exact hwq)
  have h4 : Real.sqrt nq * Real.sqrt tq ≤ (q * |t|) * (q * |t|) := by
    calc Real.sqrt nq * Real.sqrt tq ≤ (q * t ^ 2) * q :=
          mul_le_mul h2 h1 (Real.sqrt_nonneg _) (by positivity)
      _ = (q * |t|) * (q * |t|) := by rw [← sq_abs t]; ring
  have h5 : Real.sqrt (Real.sqrt nq * Real.sqrt tq) ≤ q * |t| := sq_le (by positivity) h4
  have h6 : Real.sqrt nq * Real.sqrt (Real.sqrt nq * Real.sqrt tq) ≤ c * V * |t| ^ 3 := by
    calc _ ≤ (q * t ^ 2) * (q * |t|) := mul_le_mul h2 h5 (Real.sqrt_nonneg _) (by positivity)
      _ = q * q * |t| ^ 3 := by rw [← sq_abs t]; ring
      _ = _ := by rw [hq2]
  have h7 : E * Real.sqrt wq * Real.sqrt nq ≤ E * c * V := by
    have ht2 : t ^ 2 ≤ 1 := by
      rw [← sq_abs t]
      nlinarith
    calc _ ≤ E * q * (q * t ^ 2) := by gcongr
      _ = E * (c * V) * t ^ 2 := by rw [← hq2]; ring
      _ ≤ E * (c * V) * 1 := by gcongr
      _ = _ := by ring
  have h8 : nq ≤ c * V * |t| ^ 3 := by
    have h9 : t ^ 4 ≤ |t| ^ 3 := by
      rw [show t ^ 4 = |t| ^ 3 * |t| by rw [← pow_succ, show (3 + 1 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]]
      have : 0 ≤ |t| ^ 3 := by positivity
      nlinarith
    calc nq ≤ c * V * t ^ 4 := hnq
      _ ≤ _ := by gcongr
  calc _ ≤ c * V * |t| ^ 3 + E * c * V + c * V * |t| ^ 3 := by linarith
    _ = _ := by ring
private theorem abs_sub_sub_le_of_identities {V χ ν δ AC AS HC HS DC DS C₁ c₂ t3 E εv C₅ : ℝ}
    (hV : 0 < V)
    (hχ : V * χ = AC + AS) (hδ : V * δ = HC - DC + (HS - DS))
    (hν : |ν - V⁻¹ * (DC + DS)| ≤ C₅ * t3 + εv)
    (hC : |AC - HC| ≤ C₁ * (V * (2 * c₂ * t3 + E * c₂)))
    (hS : |AS - HS| ≤ C₁ * (V * (2 * c₂ * t3 + E * c₂))) :
    |χ - ν - δ| ≤ (4 * C₁ * c₂ + C₅) * t3 + 2 * C₁ * c₂ * E + εv := by
  have e : χ - ν - δ = V⁻¹ * ((AC - HC) + (AS - HS)) - (ν - V⁻¹ * (DC + DS)) := by
    have h1 : χ = V⁻¹ * (AC + AS) := by
      rw [← hχ]
      field_simp
    have h2 : δ = V⁻¹ * (HC - DC + (HS - DS)) := by
      rw [← hδ]
      field_simp
    rw [h1, h2]
    ring
  have hVi : 0 < V⁻¹ := inv_pos.mpr hV
  have h3 : |V⁻¹ * ((AC - HC) + (AS - HS))| ≤ 2 * C₁ * (2 * c₂ * t3 + E * c₂) := by
    rw [abs_mul, abs_of_pos hVi]
    have h4 : |(AC - HC) + (AS - HS)| ≤ 2 * (C₁ * (V * (2 * c₂ * t3 + E * c₂))) := by
      have := abs_add_le (AC - HC) (AS - HS)
      linarith
    calc V⁻¹ * _ ≤ V⁻¹ * (2 * (C₁ * (V * (2 * c₂ * t3 + E * c₂)))) :=
          mul_le_mul_of_nonneg_left h4 hVi.le
      _ = _ := by field_simp
  rw [e]
  calc _ ≤ |V⁻¹ * ((AC - HC) + (AS - HS))| + |ν - V⁻¹ * (DC + DS)| := abs_sub _ _
    _ ≤ 2 * C₁ * (2 * c₂ * t3 + E * c₂) + (C₅ * t3 + εv) := add_le_add h3 hν
    _ = _ := by ring
theorem chainKernelsAgreeOnLongWaves_holds (h₁ : SecondDerivAlongWaveNearResponseHessian)
    (h₂ : LongWaveSizeBounds) (h₃ : ChainKernelCosineSum)
    (h₄ : DifferenceKernelCosineSum)
    (h₅ : NormaliserHessianOnLongWaves) :
    ChainKernelsAgreeOnLongWaves := by
  intro a ha L _ hLs k hk ρ hρ hρ1
  obtain ⟨C₁, c, hC₁, hc, hB⟩ := h₁ a ha L hLs k hk ρ hρ hρ1
  obtain ⟨c₂, r₂, hc₂, hr₂, hS⟩ := h₂ L hLs k hk
  obtain ⟨C₅, r₅, hC₅, hr₅, hN⟩ := h₅ L hLs k hk
  have hLr : (1 : ℝ) < L := by
    have := hLs.2
    exact_mod_cast (by omega : 1 < L)
  refine ⟨4 * C₁ * c₂ + C₅, min 1 (min r₂ r₅), lt_min one_pos (lt_min hr₂ hr₅), ?_⟩
  intro n₀ m t ht htr ε hε
  have ht1 : |t| ≤ 1 := (lt_of_lt_of_le htr (min_le_left _ _)).le
  have ht2 : |t| < r₂ := lt_of_lt_of_le htr ((min_le_right _ _).trans (min_le_left _ _))
  have ht5 : |t| < r₅ := lt_of_lt_of_le htr ((min_le_right _ _).trans (min_le_right _ _))
  have hε2 : 0 < ε / 2 := half_pos hε
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(c * (2 * (L : ℝ) ^ n)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.const_mul_atTop hc (Tendsto.const_mul_atTop two_pos
        (tendsto_pow_atTop_atTop_of_one_lt hLr)))
  have hsmall : ∀ᶠ n : ℕ in atTop, 2 * C₁ * c₂ * Real.exp (-(c * (2 * (L : ℝ) ^ n))) ≤ ε / 2 := by
    have h := hexp.const_mul (2 * C₁ * c₂)
    rw [mul_zero] at h
    filter_upwards [h.eventually_lt_const hε2] with n hn using hn.le
  filter_upwards [hB, hS n₀ m t ht ht2, h₃ a ha L hLs k ρ hρ hρ1 n₀ m t ht,
    h₄ a ha L hLs k hk n₀ m t ht, hN n₀ m t ht ht5 (ε / 2) hε2, hsmall] with n hBn hSn h3 h4 hNn hE
  obtain ⟨A, B, hAB, hsz⟩ := hSn
  have hLn : (0 : ℝ) < 2 * (L : ℝ) ^ n := by positivity
  have hV : (0 : ℝ) < (2 * (L : ℝ) ^ n) ^ 4 := by positivity
  have hE0 : 0 ≤ Real.exp (-(c * (2 * (L : ℝ) ^ n))) := (Real.exp_pos _).le
  have bound : ∀ (f : TorusFields.TorusSite (2 * L ^ n) → ℝ) (D : Tower.edgeFormSpace L n k k),
      (D : Tower.Edge L n k k → Matrices.ComplexMatrix2) = planeWaveValues L n k f →
      D ∈ ({A, B} : Set (Tower.edgeFormSpace L n k k)) →
      |SlopeCoefficient.secondDerivAlong (SlopeCoefficient.chainLogarithm a ρ L k) (2 * L ^ n)
          (planeWaveOnTorus f) - freeEnergyHessianAtResponse a D| ≤
        C₁ * ((2 * (L : ℝ) ^ n) ^ 4 *
          (2 * c₂ * |t| ^ 3 + Real.exp (-(c * (2 * (L : ℝ) ^ n))) * c₂)) := by
    intro f D hD hm
    obtain ⟨s1, s2, s3⟩ := hsz D hm
    exact (hBn f D hD).trans (mul_le_mul_of_nonneg_left
      (wave_term_le hc₂ hV ht1 hE0 s1 s2 s3) hC₁)
  have key := abs_sub_sub_le_of_identities hV h3 (h4 A B hAB) (hNn A B hAB)
    (bound _ A hAB.1 (by simp)) (bound _ B hAB.2 (by simp))
  refine key.trans ?_
  linarith
end YangMills.Construction.RunningCouplingSlope
end
