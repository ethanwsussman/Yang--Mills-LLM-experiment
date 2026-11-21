import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import YangMills.Construction.FourPointCondition.RiemannSumOfTheBareTracesProof
import YangMills.Construction.LawInAState.ReflectionKernelAtADistanceProof
import YangMills.Construction.ResponseInTheExpansion.CurvatureKernelVariesSlowly
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearResponse
private theorem abs_sqrt_sqNorm_sub_le (x y : Fin 4 → ℝ) :
    |Real.sqrt (sqNorm x) - Real.sqrt (sqNorm y)| ≤ Real.sqrt (sqNorm (x - y)) := by apply _root_.YangMills.DeltaSharedProofs.p501537 <;> assumption
private theorem abs_coord_div_sqrt_le_one (x : Fin 4 → ℝ) (hx : 0 < sqNorm x) (i : Fin 4) :
    |x i / Real.sqrt (sqNorm x)| ≤ 1 := by
  have hp := Real.sqrt_pos.mpr hx
  rw [abs_div, abs_of_pos hp, div_le_one hp]
  refine Real.abs_le_sqrt ?_
  exact Finset.single_le_sum (f := fun i => x i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
private theorem abs_coord_le_sqrt_sqNorm (x : Fin 4 → ℝ) (i : Fin 4) : |x i| ≤ Real.sqrt (sqNorm x) := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem hyperplaneReflection_eq_unit (x : Fin 4 → ℝ) (hx : 0 < sqNorm x) (i j : Fin 4) :
    hyperplaneReflection x i j = (if i = j then 1 else 0) -
      2 * (x i / Real.sqrt (sqNorm x)) * (x j / Real.sqrt (sqNorm x)) := by
  have h2 : Real.sqrt (sqNorm x) * Real.sqrt (sqNorm x) = sqNorm x := Real.mul_self_sqrt hx.le
  simp only [hyperplaneReflection]
  congr 1
  field_simp
  rw [pow_two, h2]
private theorem abs_hyperplaneReflection_le (x : Fin 4 → ℝ) (hx : 0 < sqNorm x) (i j : Fin 4) :
    |hyperplaneReflection x i j| ≤ 3 := by apply _root_.YangMills.SharedProofs.p8496 <;> assumption
private theorem abs_unit_coord_sub_le (r : ℝ) (hr : 0 < r) (x y : Fin 4 → ℝ) (hxr : r ^ 2 ≤ sqNorm x)
    (hyr : r ^ 2 ≤ sqNorm y) (i : Fin 4) :
    |x i / Real.sqrt (sqNorm x) - y i / Real.sqrt (sqNorm y)| ≤
      2 * Real.sqrt (sqNorm (x - y)) / r := by
  have hx : 0 < sqNorm x := lt_of_lt_of_le (by positivity) hxr
  have hy : 0 < sqNorm y := lt_of_lt_of_le (by positivity) hyr
  set a := Real.sqrt (sqNorm x) with ha
  set b := Real.sqrt (sqNorm y) with hb
  set e := Real.sqrt (sqNorm (x - y)) with he
  have ha0 : 0 < a := Real.sqrt_pos.mpr hx
  have hb0 : 0 < b := Real.sqrt_pos.mpr hy
  have har : r ≤ a := Real.le_sqrt_of_sq_le hxr
  have he0 : 0 ≤ e := Real.sqrt_nonneg _
  have h1 : |x i - y i| ≤ e := by
    have := abs_coord_le_sqrt_sqNorm (x - y) i
    simpa using this
  have h2 : |a - b| ≤ e := abs_sqrt_sqNorm_sub_le x y
  have hsplit : x i / a - y i / b = (x i - y i) / a + (y i / b) * ((b - a) / a) := by
    field_simp
    ring
  have hq : |y i / b| ≤ 1 := abs_coord_div_sqrt_le_one y hy i
  have hinv : e / a ≤ e / r := div_le_div_of_nonneg_left he0 hr har
  rw [hsplit]
  calc _ ≤ |(x i - y i) / a| + |(y i / b) * ((b - a) / a)| := abs_add_le _ _
    _ ≤ e / a + 1 * (e / a) := by
      refine add_le_add ?_ ?_
      · rw [abs_div, abs_of_pos ha0]
        exact div_le_div_of_nonneg_right h1 ha0.le
      · rw [abs_mul]
        refine mul_le_mul hq ?_ (abs_nonneg _) zero_le_one
        rw [abs_div, abs_of_pos ha0, abs_sub_comm]
        exact div_le_div_of_nonneg_right h2 ha0.le
    _ ≤ e / r + e / r := by linarith
    _ = 2 * e / r := by ring
private theorem abs_hyperplaneReflection_sub_le (r : ℝ) (hr : 0 < r) (x y : Fin 4 → ℝ) (hxr : r ^ 2 ≤ sqNorm x)
    (hyr : r ^ 2 ≤ sqNorm y) (i j : Fin 4) :
    |hyperplaneReflection x i j - hyperplaneReflection y i j| ≤ 8 * Real.sqrt (sqNorm (x - y)) / r := by
  have hx : 0 < sqNorm x := lt_of_lt_of_le (by positivity) hxr
  have hy : 0 < sqNorm y := lt_of_lt_of_le (by positivity) hyr
  rw [hyperplaneReflection_eq_unit x hx, hyperplaneReflection_eq_unit y hy]
  have d1 := abs_unit_coord_sub_le r hr x y hxr hyr i
  have d2 := abs_unit_coord_sub_le r hr x y hxr hyr j
  have b1 := abs_coord_div_sqrt_le_one x hx j
  have b2 := abs_coord_div_sqrt_le_one y hy i
  set u := x i / Real.sqrt (sqNorm x)
  set v := x j / Real.sqrt (sqNorm x)
  set u' := y i / Real.sqrt (sqNorm y)
  set v' := y j / Real.sqrt (sqNorm y)
  set E := 2 * Real.sqrt (sqNorm (x - y)) / r with hE
  have hE0 : 0 ≤ E := by positivity
  have hsplit : (if i = j then (1 : ℝ) else 0) - 2 * u * v - ((if i = j then 1 else 0) - 2 * u' * v') =
      -(2 * ((u - u') * v + u' * (v - v'))) := by ring
  rw [hsplit, abs_neg, abs_mul, abs_two]
  have h1 : |(u - u') * v| ≤ E := by
    rw [abs_mul]
    calc _ ≤ E * 1 := mul_le_mul d1 b1 (abs_nonneg _) hE0
      _ = E := mul_one _
  have h2 : |u' * (v - v')| ≤ E := by
    rw [abs_mul]
    calc _ ≤ 1 * E := mul_le_mul b2 d2 (abs_nonneg _) zero_le_one
      _ = E := one_mul _
  have h3 := abs_add_le ((u - u') * v) (u' * (v - v'))
  have : 8 * Real.sqrt (sqNorm (x - y)) / r = 4 * E := by rw [hE]; ring
  rw [this]
  linarith
private def kernelNumerator (x : Fin 4 → ℝ) (μ ν ρ τ : Fin 4) : ℝ :=
  hyperplaneReflection x μ ρ * hyperplaneReflection x ν τ - hyperplaneReflection x μ τ * hyperplaneReflection x ν ρ
private theorem abs_kernelNumerator_le (x : Fin 4 → ℝ) (hx : 0 < sqNorm x) (μ ν ρ τ : Fin 4) :
    |kernelNumerator x μ ν ρ τ| ≤ 18 := by apply _root_.YangMills.DeltaSharedProofs.p500912 <;> assumption
private theorem abs_kernelNumerator_sub_le (r : ℝ) (hr : 0 < r) (x y : Fin 4 → ℝ) (hxr : r ^ 2 ≤ sqNorm x)
    (hyr : r ^ 2 ≤ sqNorm y) (μ ν ρ τ : Fin 4) :
    |kernelNumerator x μ ν ρ τ - kernelNumerator y μ ν ρ τ| ≤ 96 * Real.sqrt (sqNorm (x - y)) / r := by
  have hx : 0 < sqNorm x := lt_of_lt_of_le (by positivity) hxr
  have hy : 0 < sqNorm y := lt_of_lt_of_le (by positivity) hyr
  set E := 8 * Real.sqrt (sqNorm (x - y)) / r with hE
  have hE0 : 0 ≤ E := by positivity
  have key : ∀ a b a' b' : ℝ, |a| ≤ 3 → |b'| ≤ 3 → |a - a'| ≤ E → |b - b'| ≤ E → |a * b - a' * b'| ≤ 6 * E := by
    intro a b a' b' ha hb hd1 hd2
    have hs : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
    rw [hs]
    calc _ ≤ |a * (b - b')| + |(a - a') * b'| := abs_add_le _ _
      _ ≤ 3 * E + E * 3 := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul ha hd2 (abs_nonneg _) (by norm_num)) (mul_le_mul hd1 hb (abs_nonneg _) hE0)
      _ = 6 * E := by ring
  have k1 := key _ _ _ _ (abs_hyperplaneReflection_le x hx μ ρ) (abs_hyperplaneReflection_le y hy ν τ)
    (abs_hyperplaneReflection_sub_le r hr x y hxr hyr μ ρ) (abs_hyperplaneReflection_sub_le r hr x y hxr hyr ν τ)
  have k2 := key _ _ _ _ (abs_hyperplaneReflection_le x hx μ τ) (abs_hyperplaneReflection_le y hy ν ρ)
    (abs_hyperplaneReflection_sub_le r hr x y hxr hyr μ τ) (abs_hyperplaneReflection_sub_le r hr x y hxr hyr ν ρ)
  have hsplit : kernelNumerator x μ ν ρ τ - kernelNumerator y μ ν ρ τ =
      (hyperplaneReflection x μ ρ * hyperplaneReflection x ν τ - hyperplaneReflection y μ ρ * hyperplaneReflection y ν τ) -
      (hyperplaneReflection x μ τ * hyperplaneReflection x ν ρ - hyperplaneReflection y μ τ * hyperplaneReflection y ν ρ) := by
    simp only [kernelNumerator]
    ring
  rw [hsplit]
  have : 96 * Real.sqrt (sqNorm (x - y)) / r = 12 * E := by rw [hE]; ring
  rw [this]
  calc _ ≤ _ := abs_sub _ _
    _ ≤ 6 * E + 6 * E := add_le_add k1 k2
    _ = 12 * E := by ring
private theorem one_le_pi_sq : (1 : ℝ) ≤ Real.pi ^ 2 := by apply _root_.YangMills.Construction.ReflectionKernel.one_le_pi_sq <;> assumption
theorem continuumCurvatureKernel_bound_and_lipschitz : ContinuumCurvatureKernelBoundAndLipschitz := by
  intro r x y μ ν ρ τ hr hxr hyr
  have hx : 0 < sqNorm x := lt_of_lt_of_le (by positivity) hxr
  have hy : 0 < sqNorm y := lt_of_lt_of_le (by positivity) hyr
  have hpi := one_le_pi_sq
  have hC : ∀ w : Fin 4 → ℝ, continuumCurvatureKernel w μ ν ρ τ = kernelNumerator w μ ν ρ τ / (Real.pi ^ 2 * sqNorm w ^ 2) := fun w => rfl
  have hr4 : 0 < r ^ 4 := by positivity
  have hsq : r ^ 4 ≤ sqNorm x ^ 2 := by nlinarith [sq_nonneg (r ^ 2)]
  constructor
  · rw [hC, abs_div, abs_of_pos (by positivity : 0 < Real.pi ^ 2 * sqNorm x ^ 2)]
    refine div_le_div₀ (by norm_num) (abs_kernelNumerator_le x hx μ ν ρ τ) hr4 ?_
    nlinarith [sq_nonneg (sqNorm x)]
  · set a := Real.sqrt (sqNorm x) with ha
    set b := Real.sqrt (sqNorm y) with hb
    set e := Real.sqrt (sqNorm (x - y)) with he
    have ha0 : 0 < a := Real.sqrt_pos.mpr hx
    have hb0 : 0 < b := Real.sqrt_pos.mpr hy
    have har : r ≤ a := Real.le_sqrt_of_sq_le hxr
    have hbr : r ≤ b := Real.le_sqrt_of_sq_le hyr
    have he0 : 0 ≤ e := Real.sqrt_nonneg _
    have ha2 : sqNorm x = a ^ 2 := (Real.sq_sqrt hx.le).symm
    have hb2 : sqNorm y = b ^ 2 := (Real.sq_sqrt hy.le).symm
    have hab : |a - b| ≤ e := abs_sqrt_sqNorm_sub_le x y
    have hinv : ∀ t : ℝ, r ≤ t → t⁻¹ ≤ r⁻¹ := fun t ht => inv_anti₀ hr ht
    set p := a⁻¹ with hp
    set s := b⁻¹ with hs2
    have hp0 : 0 < p := inv_pos.mpr ha0
    have hs0 : 0 < s := inv_pos.mpr hb0
    have hpr : p ≤ r⁻¹ := hinv a har
    have hsr : s ≤ r⁻¹ := hinv b hbr
    have hps : |p ^ 4 - s ^ 4| ≤ 4 * e * r⁻¹ ^ 5 := by
      have hfac : p ^ 4 - s ^ 4 = (b - a) * (p * s) * (p ^ 3 + p ^ 2 * s + p * s ^ 2 + s ^ 3) := by
        have e1 : (b - a) * (p * s) = p - s := by
          simp only [hp, hs2]
          field_simp
        rw [e1]
        ring
      rw [hfac, abs_mul, abs_mul]
      have hR : 0 < r⁻¹ := inv_pos.mpr hr
      have h1 : |b - a| ≤ e := by rwa [abs_sub_comm]
      have h2 : |p * s| ≤ r⁻¹ ^ 2 := by
        rw [abs_of_pos (by positivity)]
        nlinarith
      have h3 : |p ^ 3 + p ^ 2 * s + p * s ^ 2 + s ^ 3| ≤ 4 * r⁻¹ ^ 3 := by
        rw [abs_of_pos (by positivity)]
        have t1 : p ^ 3 ≤ r⁻¹ ^ 3 := pow_le_pow_left₀ hp0.le hpr 3
        have t2 : s ^ 3 ≤ r⁻¹ ^ 3 := pow_le_pow_left₀ hs0.le hsr 3
        have t3 : p ^ 2 * s ≤ r⁻¹ ^ 3 := by
          have : p ^ 2 ≤ r⁻¹ ^ 2 := pow_le_pow_left₀ hp0.le hpr 2
          calc _ ≤ r⁻¹ ^ 2 * r⁻¹ := mul_le_mul this hsr hs0.le (by positivity)
            _ = _ := by ring
        have t4 : p * s ^ 2 ≤ r⁻¹ ^ 3 := by
          have : s ^ 2 ≤ r⁻¹ ^ 2 := pow_le_pow_left₀ hs0.le hsr 2
          calc _ ≤ r⁻¹ * r⁻¹ ^ 2 := mul_le_mul hpr this (by positivity) (by positivity)
            _ = _ := by ring
        linarith
      calc _ ≤ (e * r⁻¹ ^ 2) * (4 * r⁻¹ ^ 3) := by
            refine mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) he0) h3 (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hCa : continuumCurvatureKernel x μ ν ρ τ = kernelNumerator x μ ν ρ τ * p ^ 4 / Real.pi ^ 2 := by
      rw [hC, ha2, hp]
      field_simp
    have hCb : continuumCurvatureKernel y μ ν ρ τ = kernelNumerator y μ ν ρ τ * s ^ 4 / Real.pi ^ 2 := by
      rw [hC, hb2, hs2]
      field_simp
    have hd := abs_kernelNumerator_sub_le r hr x y hxr hyr μ ν ρ τ
    have hb18 := abs_kernelNumerator_le y hy μ ν ρ τ
    have hR : 0 < r⁻¹ := inv_pos.mpr hr
    have hp4 : p ^ 4 ≤ r⁻¹ ^ 4 := pow_le_pow_left₀ hp0.le hpr 4
    rw [hCa, hCb, ← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < Real.pi ^ 2)]
    have hsplit : kernelNumerator x μ ν ρ τ * p ^ 4 - kernelNumerator y μ ν ρ τ * s ^ 4 =
        (kernelNumerator x μ ν ρ τ - kernelNumerator y μ ν ρ τ) * p ^ 4 + kernelNumerator y μ ν ρ τ * (p ^ 4 - s ^ 4) := by ring
    have hmain : |kernelNumerator x μ ν ρ τ * p ^ 4 - kernelNumerator y μ ν ρ τ * s ^ 4| ≤ 168 * e * r⁻¹ ^ 5 := by
      rw [hsplit]
      calc _ ≤ |(kernelNumerator x μ ν ρ τ - kernelNumerator y μ ν ρ τ) * p ^ 4| + |kernelNumerator y μ ν ρ τ * (p ^ 4 - s ^ 4)| := abs_add_le _ _
        _ ≤ (96 * e * r⁻¹) * r⁻¹ ^ 4 + 18 * (4 * e * r⁻¹ ^ 5) := by
          rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < p ^ 4)]
          refine add_le_add (mul_le_mul ?_ hp4 (by positivity) (by positivity))
            (mul_le_mul hb18 hps (abs_nonneg _) (by norm_num))
          simpa [div_eq_mul_inv] using hd
        _ = _ := by ring
    have hfin : 168 * e * r⁻¹ ^ 5 ≤ 200 * e / r ^ 5 := by
      have : 200 * e / r ^ 5 = 200 * e * r⁻¹ ^ 5 := by
        rw [div_eq_mul_inv, inv_pow]
      rw [this]
      have : 0 ≤ e * r⁻¹ ^ 5 := by positivity
      nlinarith
    calc _ ≤ 168 * e * r⁻¹ ^ 5 / Real.pi ^ 2 := div_le_div_of_nonneg_right hmain (by positivity)
      _ ≤ 168 * e * r⁻¹ ^ 5 := div_le_self (by positivity) hpi
      _ ≤ _ := hfin
end YangMills.Construction.LinearResponse
end
