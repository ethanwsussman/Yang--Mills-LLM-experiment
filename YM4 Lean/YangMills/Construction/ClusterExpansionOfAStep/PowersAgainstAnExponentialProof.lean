import YangMills.Construction.ClusterExpansionOfAStep.PowersAgainstAnExponential
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace YangMills.Construction.TorusLumps
theorem polynomialBelowExponential : PolynomialBelowExponential := by
  intro a κ B p q hκ hB
  set C := max B 1 with hC
  have hC1 : 1 ≤ C := le_max_right _ _
  set c := max a 0 * C ^ (100 * p) * Real.exp κ with hc
  have hr : |Real.exp (-κ)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hlim : Tendsto (fun k : ℕ => ((k : ℝ)) ^ (100 * p + q) * Real.exp (-κ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one _ hr
  have hlim' : Tendsto (fun k : ℕ => c * (((k + 1 : ℕ) : ℝ) ^ (100 * p + q) * Real.exp (-κ) ^ (k + 1))) atTop (𝓝 0) := by
    have := (hlim.comp (tendsto_add_atTop_nat 1)).const_mul c
    simpa using this
  have hev := (hlim'.eventually (gt_mem_nhds (zero_lt_one' ℝ)))
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  refine ⟨max 1 ((C * (K + 1)) ^ 100), le_max_left _ _, fun x hx k hk => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx2 : (C * (K + 1)) ^ 100 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hroot : x ^ ((1 : ℝ) / 100) ≤ clusterRange x := Nat.le_ceil _
  have hxr : x ≤ (clusterRange x : ℝ) ^ 100 := by
    have h1 : (x ^ ((1 : ℝ) / 100)) ^ 100 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    calc x = (x ^ ((1 : ℝ) / 100)) ^ 100 := h1.symm
      _ ≤ (clusterRange x : ℝ) ^ 100 := by gcongr
  have hrC : (clusterRange x : ℝ) ≤ C * k := by
    have h3 := (div_le_iff₀ hB).mp hk
    have : (k : ℝ) * B ≤ C * k := by
      rw [mul_comm]
      gcongr
      exact le_max_left _ _
    linarith
  have hCK : C * (K + 1) ≤ x ^ ((1 : ℝ) / 100) := by
    have hpos : 0 ≤ C * (K + 1) := by positivity
    have := Real.rpow_le_rpow (by positivity) hx2 (show (0 : ℝ) ≤ 1 / 100 by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos] at this
    norm_num at this
    simpa using this
  have hkK : K ≤ k := by
    have h4 : C * (K + 1) ≤ C * k := hCK.trans (hroot.trans hrC)
    have h5 : (K : ℝ) + 1 ≤ k := le_of_mul_le_mul_left h4 (by linarith)
    have : (K : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hmain := hK k hkK
  have hxk : x ^ p ≤ C ^ (100 * p) * ((k : ℝ) + 1) ^ (100 * p) := by
    have h6 : x ≤ (C * ((k : ℝ) + 1)) ^ 100 := by
      refine hxr.trans ?_
      gcongr
      refine hrC.trans ?_
      gcongr
      linarith
    calc x ^ p ≤ ((C * ((k : ℝ) + 1)) ^ 100) ^ p := by gcongr
      _ = C ^ (100 * p) * ((k : ℝ) + 1) ^ (100 * p) := by
          rw [← pow_mul, mul_pow]
  have hexp : Real.exp (-(κ * k)) = Real.exp κ * Real.exp (-κ) ^ (k + 1) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc a * x ^ p * ((k : ℝ) + 1) ^ q * Real.exp (-(κ * k))
      ≤ max a 0 * x ^ p * ((k : ℝ) + 1) ^ q * Real.exp (-(κ * k)) := by
        gcongr
        exact le_max_left _ _
    _ ≤ max a 0 * (C ^ (100 * p) * ((k : ℝ) + 1) ^ (100 * p)) * ((k : ℝ) + 1) ^ q * Real.exp (-(κ * k)) := by
        gcongr
    _ = c * (((k + 1 : ℕ) : ℝ) ^ (100 * p + q) * Real.exp (-κ) ^ (k + 1)) := by
        rw [hexp, hc, pow_add]
        push_cast
        ring
    _ ≤ 1 := hmain.le
end YangMills.Construction.TorusLumps
end
