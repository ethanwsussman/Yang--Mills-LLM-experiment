import YangMills.Construction.ColdChainAtEveryLevel.LocalFormOfTheLinesProof
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.LawInAState.SumsOverTheBondsOfALattice
import YangMills.Construction.FormsOnATorus.PropertiesOfTheSymbol
import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormOfTheCubeProof
import YangMills.Construction.ResponseInTheExpansion.SecondMomentOfTheMaxwellKernel
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps LevelAction LimitForms BoxGaussian LinearResponse WeightedResponses
  RenormalizationStepParameters TorusComparison
namespace ResponseInTheExpansion.MaxwellMoment
private theorem hasSum_iff_of_eq {α : Type*} {f g : α → ℝ} {a : ℝ} (h : ∀ z, f z = g z) : HasSum f a ↔ HasSum g a := by
  rw [funext h]
private def supNormZ (u : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun i => (u i).natAbs
private theorem natAbs_le_supNormZ (u : Fin 4 → ℤ) (i : Fin 4) : (u i).natAbs ≤ supNormZ u := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
private theorem abs_le_supNormZ (u : Fin 4 → ℤ) (i : Fin 4) : |(u i : ℝ)| ≤ supNormZ u := by apply _root_.YangMills.Construction.BlockAverages.abs_coord_le_supNorm <;> assumption
private def bondPhase (P : Fin 4 → ℝ) (i j : Fin 4) (z : Fin 4 → ℤ) : ℝ :=
  ∑ l, P l * ((z l : ℝ) + (if l = j then 1 / 2 else 0) - (if l = i then 1 / 2 else 0))
private theorem bondPhase_eq (P : Fin 4 → ℝ) (i j : Fin 4) (z : Fin 4 → ℤ) :
    bondPhase P i j z = ∑ l, P l * (z l : ℝ) + (P j - P i) / 2 := by
  have h1 : ∀ w : Fin 4, ∑ l, P l * (if l = w then (1 / 2 : ℝ) else 0) = P w / 2 := by
    intro w
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  unfold bondPhase
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, h1]
  ring
private theorem bondPhase_sq_le (P : Fin 4 → ℝ) (i j : Fin 4) (z : Fin 4 → ℤ) :
    bondPhase P i j z ^ 2 ≤ sqNorm P * (4 * (1 + (supNormZ z : ℝ)) ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ P
    (fun l => (z l : ℝ) + (if l = j then 1 / 2 else 0) - (if l = i then 1 / 2 else 0))
  have hb : ∀ l : Fin 4, ((z l : ℝ) + (if l = j then 1 / 2 else 0) - (if l = i then 1 / 2 else 0)) ^ 2 ≤
      (1 + (supNormZ z : ℝ)) ^ 2 := by
    intro l
    have h1 := abs_le.mp (abs_le_supNormZ z l)
    apply sq_le_sq'
    · split_ifs <;> linarith [h1.1]
    · split_ifs <;> linarith [h1.2]
  have hs : ∑ l, ((z l : ℝ) + (if l = j then 1 / 2 else 0) - (if l = i then 1 / 2 else 0)) ^ 2 ≤
      4 * (1 + (supNormZ z : ℝ)) ^ 2 := by
    refine (Finset.sum_le_sum fun l _ => hb l).trans ?_
    simp
  have hP : 0 ≤ sqNorm P := Finset.sum_nonneg fun l _ => sq_nonneg _
  calc bondPhase P i j z ^ 2 ≤ _ := h
    _ ≤ sqNorm P * (4 * (1 + (supNormZ z : ℝ)) ^ 2) := mul_le_mul_of_nonneg_left hs hP
section Sums
private theorem valMinAbs_intCast_of_small {n : ℕ} [NeZero n] {u : ℤ} (h : 2 * |u| < (n : ℤ)) :
    ((u : ZMod n)).valMinAbs = u := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
private theorem abs_eq_of_intCast_eq {n : ℕ} [NeZero n] {u v : ℤ} (h : (u : ZMod n) = (v : ZMod n))
    (hu : 2 * |u| ≤ (n : ℤ)) (hv : 2 * |v| ≤ (n : ℤ)) : |u| = |v| ∧ (2 * |u| < (n : ℤ) → u = v) := by
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub u v n).1 h
  have hn : (0 : ℤ) < n := by
    have := NeZero.pos n
    exact_mod_cast this
  have hb : |(n : ℤ) * q| ≤ n := by
    rw [← hq]
    have a1 := abs_le.mp (le_refl |u|)
    have a2 := abs_le.mp (le_refl |v|)
    rw [abs_le]
    constructor <;> omega
  have hq1 : |q| ≤ 1 := by
    by_contra hc
    push_neg at hc
    rw [abs_mul, abs_of_pos hn] at hb
    nlinarith
  have hq2 := abs_le.mp hq1
  obtain ⟨h1, h2⟩ := hq2
  simp only [Int.abs_eq_natAbs] at hu hv ⊢
  interval_cases q
  · simp only [mul_neg, mul_one] at hq
    constructor
    · omega
    · intro h3
      omega
  · simp only [mul_zero] at hq
    constructor
    · omega
    · intro _
      omega
  · simp only [mul_one] at hq
    constructor
    · omega
    · intro h3
      omega
private theorem summable_exp_neg_supNormZ {δ : ℝ} (hδ : 0 < δ) :
    Summable fun u : Fin 4 → ℤ => Real.exp (-δ * supNormZ u) := by apply _root_.YangMills.Construction.LatticeSums.summable_exp_neg_offsetSupNorm <;> assumption
private theorem one_add_pow_le_exp (p : ℕ) {β : ℝ} (hβ : 0 < β) : ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ, 0 ≤ u →
    (1 + u) ^ p ≤ K * Real.exp (β * u) := by
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = min (β / (p + 1)) 1 := ⟨_, rfl⟩
  have hp0 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have he0 : 0 < e := by
    rw [he]
    exact lt_min (div_pos hβ hp0) one_pos
  have he1 : e ≤ 1 := he ▸ min_le_right _ _
  have he2 : e * ((p : ℝ) + 1) ≤ β := by
    have : e ≤ β / (p + 1) := he ▸ min_le_left _ _
    rwa [le_div_iff₀ hp0] at this
  refine ⟨(e⁻¹) ^ p, by positivity, fun u hu => ?_⟩
  have h1 : 1 + u ≤ e⁻¹ * Real.exp (e * u) := by
    have h2 := Real.add_one_le_exp (e * u)
    rw [inv_mul_eq_div, le_div_iff₀ he0]
    linarith
  calc (1 + u) ^ p ≤ (e⁻¹ * Real.exp (e * u)) ^ p := pow_le_pow_left₀ (by linarith) h1 p
    _ = (e⁻¹) ^ p * Real.exp ((p : ℝ) * (e * u)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
    _ ≤ (e⁻¹) ^ p * Real.exp (β * u) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      nlinarith
private theorem summable_exp_mul_pow {δ : ℝ} (hδ : 0 < δ) (p : ℕ) :
    Summable fun u : Fin 4 → ℤ => Real.exp (-δ * supNormZ u) * (1 + (supNormZ u : ℝ)) ^ p := by
  obtain ⟨K, hK, H⟩ := one_add_pow_le_exp p (half_pos hδ)
  refine Summable.of_nonneg_of_le (fun u => by positivity) (fun u => ?_)
    ((summable_exp_neg_supNormZ (half_pos hδ)).mul_left K)
  have h := H (supNormZ u) (by positivity)
  calc Real.exp (-δ * supNormZ u) * (1 + (supNormZ u : ℝ)) ^ p ≤
        Real.exp (-δ * supNormZ u) * (K * Real.exp (δ / 2 * supNormZ u)) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = K * Real.exp (-(δ / 2) * supNormZ u) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
end Sums
section Moment
private theorem hasSum_indicator_mul (f : (Fin 4 → ℤ) → ℝ) (w : Fin 4 → ℤ) :
    HasSum (fun z => (if z = w then (1 : ℝ) else 0) * f z) (f w) := by
  have h := hasSum_ite_eq w (f w)
  refine (hasSum_iff_of_eq fun z => ?_).mpr h
  split_ifs with hz
  · simp [hz]
  · simp
private theorem hasSum_gaugeTerm (Q : IntBond → IntBond → ℝ) (i j : Fin 4) (f : (Fin 4 → ℤ) → ℝ) :
    HasSum (fun z => (gaugeFixedKernel Q (0, i) (z, j) - Q (0, i) (z, j)) * f z)
      (f 0 - f (-Pi.single j 1) - f (Pi.single i 1) + f (Pi.single i 1 - Pi.single j 1)) := by
  have h := (((hasSum_indicator_mul f 0).sub (hasSum_indicator_mul f (-Pi.single j 1))).sub
    (hasSum_indicator_mul f (Pi.single i 1))).add (hasSum_indicator_mul f (Pi.single i 1 - Pi.single j 1))
  refine (hasSum_iff_of_eq fun z => ?_).mpr h
  have e1 : ((0 : Fin 4 → ℤ) = z) ↔ z = 0 := eq_comm
  have e2 : ((0 : Fin 4 → ℤ) = z + Pi.single j 1) ↔ z = -Pi.single j 1 := by
    constructor
    · intro h
      exact eq_neg_of_add_eq_zero_left h.symm
    · intro h
      rw [h]
      simp
  have e3 : ((0 : Fin 4 → ℤ) + Pi.single i 1 = z) ↔ z = Pi.single i 1 := by
    rw [zero_add]
    exact eq_comm
  have e4 : ((0 : Fin 4 → ℤ) + Pi.single i 1 = z + Pi.single j 1) ↔ z = Pi.single i 1 - Pi.single j 1 := by
    rw [zero_add]
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      rw [h]
      simp
  simp only [gaugeFixedKernel, e1, e2, e3, e4]
  ring
private theorem tendsto_one_sub_cos_div_sq (x : ℝ) :
    Tendsto (fun n : ℕ => (1 - Real.cos ((1 / ((n : ℝ) + 1)) * x)) / (1 / ((n : ℝ) + 1)) ^ 2) atTop
      (𝓝 (x ^ 2 / 2)) := by
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb : Tendsto (fun n : ℕ => x ^ 2 / 2 + (1 / ((n : ℝ) + 1)) ^ 2 * x ^ 4) atTop (𝓝 (x ^ 2 / 2)) := by
    have := ((ht.pow 2).mul_const (x ^ 4)).const_add (x ^ 2 / 2)
    simpa using this
  have hb' : Tendsto (fun n : ℕ => x ^ 2 / 2 - (1 / ((n : ℝ) + 1)) ^ 2 * x ^ 4) atTop (𝓝 (x ^ 2 / 2)) := by
    have := ((ht.pow 2).mul_const (x ^ 4)).const_sub (x ^ 2 / 2)
    simpa using this
  have hsmall : ∀ᶠ n : ℕ in atTop, |(1 / ((n : ℝ) + 1)) * x| ≤ 1 := by
    have h := ht.mul_const x
    rw [zero_mul] at h
    have := h.abs
    rw [abs_zero] at this
    exact this.eventually (Iic_mem_nhds one_pos)
  have hkey : ∀ᶠ n : ℕ in atTop, |(1 - Real.cos ((1 / ((n : ℝ) + 1)) * x)) / (1 / ((n : ℝ) + 1)) ^ 2 - x ^ 2 / 2| ≤
      (1 / ((n : ℝ) + 1)) ^ 2 * x ^ 4 := by
    filter_upwards [hsmall] with n hn
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
    rw [← ht] at hn ⊢
    have ht0 : 0 < t := by
      rw [ht]
      positivity
    have hc := Real.cos_bound hn
    have e : (1 - Real.cos (t * x)) / t ^ 2 - x ^ 2 / 2 = -(Real.cos (t * x) - (1 - (t * x) ^ 2 / 2)) / t ^ 2 := by
      field_simp
      ring
    rw [e, abs_div, abs_neg, abs_of_pos (by positivity : 0 < t ^ 2), div_le_iff₀ (by positivity)]
    have e2 : |t * x| ^ 4 = t ^ 4 * x ^ 4 := by
      rw [Even.pow_abs (by decide), mul_pow]
    nlinarith [mul_nonneg (by positivity : 0 ≤ t ^ 4) (by positivity : 0 ≤ x ^ 4)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hb' hb ?_ ?_
  · filter_upwards [hkey] with n hn
    linarith [(abs_le.mp hn).1]
  · filter_upwards [hkey] with n hn
    linarith [(abs_le.mp hn).2]
private theorem secondMoment_of_symbol (Q : IntBond → IntBond → ℝ) {c C C' : ℝ} (hc : 0 < c)
    (hdec : ∀ (z : Fin 4 → ℤ) (i j : Fin 4), |Q (0, i) (z, j)| ≤ C * Real.exp (-c * supNormZ z))
    (i j : Fin 4)
    (hsym : ∀ p ∈ brillouinBox, ‖midpointSymbol Q i j p - (if i = j then (momentumNormSq p : ℂ) else 0)‖ ≤
      C' * momentumNormSq p ^ 2)
    (P : Fin 4 → ℝ) :
    HasSum (fun z => Q (0, i) (z, j) * bondPhase P i j z ^ 2)
      (-2 * (sqNorm P * (if i = j then 1 else 0) - P i * P j)) := by
  obtain ⟨S, hS⟩ : ∃ S, S = sqNorm P := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (Fin 4 → ℤ) → ℝ, a = fun z => gaugeFixedKernel Q (0, i) (z, j) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : (Fin 4 → ℤ) → ℝ, g = fun z => Q (0, i) (z, j) := ⟨_, rfl⟩
  have hgb : ∀ z, |g z| ≤ |C| * Real.exp (-c * supNormZ z) := fun z => by
    rw [hg]
    exact (hdec z i j).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
  have hgs : Summable g :=
    Summable.of_norm_bounded ((summable_exp_neg_supNormZ hc).mul_left |C|) (fun z => by simpa using hgb z)
  have hgs2 : Summable fun z => g z * bondPhase P i j z ^ 2 := by
    refine Summable.of_norm_bounded ((summable_exp_mul_pow hc 2).mul_left (|C| * (S * 4))) fun z => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (bondPhase P i j z))]
    calc |g z| * bondPhase P i j z ^ 2 ≤
          (|C| * Real.exp (-c * supNormZ z)) * (S * (4 * (1 + (supNormZ z : ℝ)) ^ 2)) :=
          mul_le_mul (hgb z) (hS ▸ bondPhase_sq_le P i j z) (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have hdd1 : Summable fun z => a z - g z := by
    have h := (hasSum_gaugeTerm Q i j fun _ => 1).summable
    simp only [mul_one] at h
    rw [ha, hg]
    exact h
  have hdd2 : HasSum (fun z => (a z - g z) * bondPhase P i j z ^ 2)
      (bondPhase P i j 0 ^ 2 - bondPhase P i j (-Pi.single j 1) ^ 2 - bondPhase P i j (Pi.single i 1) ^ 2 +
        bondPhase P i j (Pi.single i 1 - Pi.single j 1) ^ 2) := by
    have h := hasSum_gaugeTerm Q i j fun z => bondPhase P i j z ^ 2
    rw [ha, hg]
    exact h
  have has : Summable a := by
    have h := hgs.add hdd1
    refine (summable_congr fun z => ?_).mp h
    ring
  have ha2 : Summable fun z => a z * bondPhase P i j z ^ 2 := by
    have h := hgs2.add hdd2.summable
    refine (summable_congr fun z => ?_).mp h
    ring
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ → ℝ, R = fun t => (midpointSymbol Q i j fun l => t * P l).re := ⟨_, rfl⟩
  have hphase : ∀ (t : ℝ) (z : Fin 4 → ℤ),
      (∑ l, (t * P l) * ((z l : ℝ) + (if l = j then 1 / 2 else 0) - (if l = i then 1 / 2 else 0))) =
        t * bondPhase P i j z := by
    intro t z
    unfold bondPhase
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hre : ∀ t, HasSum (fun z => a z * Real.cos (t * bondPhase P i j z)) (R t) := by
    intro t
    have hsumm : Summable fun z : Fin 4 → ℤ => ((gaugeFixedKernel Q (0, i) (z, j) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((∑ l, (t * P l) *
          ((z l : ℝ) + (if l = j then 1 / 2 else 0) - (if l = i then 1 / 2 else 0)) : ℝ) : ℂ)) := by
      refine Summable.of_norm ?_
      have has' : Summable fun z : Fin 4 → ℤ => ‖gaugeFixedKernel Q (0, i) (z, j)‖ := by
        rw [ha] at has
        exact has.norm
      refine (summable_congr fun z => ?_).mpr has'
      rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
    have h := Complex.reCLM.hasSum hsumm.hasSum
    have e : Complex.reCLM (∑' z : Fin 4 → ℤ, ((gaugeFixedKernel Q (0, i) (z, j) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((∑ l, (t * P l) *
          ((z l : ℝ) + (if l = j then 1 / 2 else 0) - (if l = i then 1 / 2 else 0)) : ℝ) : ℂ))) = R t := by
      rw [hRdef]
      rfl
    rw [e] at h
    refine (hasSum_iff_of_eq fun z => ?_).mpr h
    rw [hphase, Complex.reCLM_apply, mul_comm Complex.I, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, ha]
  have hmsq : ∀ t : ℝ, momentumNormSq (fun l => t * P l) = t ^ 2 * S := by
    intro t
    rw [hS]
    unfold momentumNormSq sqNorm
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = if i = j then S else 0 := ⟨_, rfl⟩
  have hR : ∀ t, (fun l => t * P l) ∈ brillouinBox → |R t - t ^ 2 * D| ≤ C' * (t ^ 2 * S) ^ 2 := by
    intro t hp
    have h := hsym _ hp
    rw [hmsq] at h
    have h2 := (Complex.abs_re_le_norm _).trans h
    have e : (if i = j then ((t ^ 2 * S : ℝ) : ℂ) else 0).re = t ^ 2 * D := by
      rw [hDdef]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij, Complex.ofReal_re]
      · rw [if_neg hij, if_neg hij]
        simp
    rw [Complex.sub_re, e] at h2
    rw [hRdef]
    exact h2
  have h0box : (fun l => (0 : ℝ) * P l) ∈ brillouinBox := by
    constructor <;> intro l <;> simp <;> linarith [Real.pi_pos]
  have hR0 : R 0 = 0 := by
    have h := hR 0 h0box
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero, sub_zero] at h
    exact abs_nonpos_iff.mp h
  have ha0 : HasSum a 0 := by
    have h := hre 0
    rw [hR0] at h
    refine (hasSum_iff_of_eq fun z => ?_).mpr h
    simp
  have h1c : ∀ t, HasSum (fun z => a z * (1 - Real.cos (t * bondPhase P i j z))) (-R t) := by
    intro t
    have h := ha0.sub (hre t)
    rw [zero_sub] at h
    refine (hasSum_iff_of_eq fun z => ?_).mpr h
    ring
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, u = fun n : ℕ => 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hu0 : ∀ n, 0 < u n := fun n => by
    rw [hu]
    positivity
  have hut : Tendsto u atTop (𝓝 0) := by
    rw [hu]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hF : ∀ n, HasSum (fun z => a z * ((1 - Real.cos (u n * bondPhase P i j z)) / u n ^ 2))
      (-R (u n) / u n ^ 2) := by
    intro n
    refine (hasSum_iff_of_eq fun z => ?_).mpr ((h1c (u n)).div_const (u n ^ 2))
    ring
  have hlim := tendsto_tsum_of_dominated_convergence
    (f := fun n z => a z * ((1 - Real.cos (u n * bondPhase P i j z)) / u n ^ 2))
    (g := fun z => a z * (bondPhase P i j z ^ 2 / 2)) (𝓕 := atTop)
    (bound := fun z => ‖a z * bondPhase P i j z ^ 2‖ / 2) (ha2.norm.div_const 2)
    (fun z => by
      have h := (tendsto_one_sub_cos_div_sq (bondPhase P i j z)).const_mul (a z)
      rw [hu]
      exact h)
    (Eventually.of_forall fun n z => by
      have hn := hu0 n
      have h1 := Real.one_sub_sq_div_two_le_cos (x := u n * bondPhase P i j z)
      have h2 := Real.cos_le_one (u n * bondPhase P i j z)
      have h3 : |(1 - Real.cos (u n * bondPhase P i j z)) / u n ^ 2| ≤ bondPhase P i j z ^ 2 / 2 := by
        rw [abs_of_nonneg (div_nonneg (by linarith) (by positivity)), div_le_iff₀ (by positivity)]
        nlinarith
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (bondPhase P i j z))]
      calc |a z| * |(1 - Real.cos (u n * bondPhase P i j z)) / u n ^ 2| ≤ |a z| * (bondPhase P i j z ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ = _ := by ring)
  have hlim2 : Tendsto (fun n => -R (u n) / u n ^ 2) atTop (𝓝 (∑' z, a z * (bondPhase P i j z ^ 2 / 2))) := by
    refine hlim.congr fun n => (hF n).tsum_eq
  have hbox : ∀ᶠ n in atTop, (fun l => u n * P l) ∈ brillouinBox := by
    have hall : ∀ l : Fin 4, ∀ᶠ n in atTop, u n * P l ∈ Set.Ioo (-Real.pi) Real.pi := by
      intro l
      have h := hut.mul_const (P l)
      rw [zero_mul] at h
      exact h.eventually (Ioo_mem_nhds (by linarith [Real.pi_pos]) Real.pi_pos)
    filter_upwards [eventually_all.mpr hall] with n hn
    constructor
    · intro l
      exact (hn l).1.le
    · intro l
      exact (hn l).2.le
  have hlim3 : Tendsto (fun n => -R (u n) / u n ^ 2) atTop (𝓝 (-D)) := by
    have hz : Tendsto (fun n => -R (u n) / u n ^ 2 + D) atTop (𝓝 0) := by
      have hb : Tendsto (fun n => C' * S ^ 2 * u n ^ 2) atTop (𝓝 0) := by
        have := (hut.pow 2).const_mul (C' * S ^ 2)
        simpa using this
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [hbox] with n hn
      have h := hR (u n) hn
      have hn0 := hu0 n
      have e : -R (u n) / u n ^ 2 + D = -(R (u n) - u n ^ 2 * D) / u n ^ 2 := by
        field_simp
        ring
      rw [e, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (by positivity : 0 < u n ^ 2),
        div_le_iff₀ (by positivity)]
      refine h.trans (le_of_eq ?_)
      ring
    have := hz.add_const (-D)
    simpa using this
  have hval := tendsto_nhds_unique hlim2 hlim3
  have hT : ∑' z, a z * bondPhase P i j z ^ 2 = -2 * D := by
    have h := ha2.hasSum.div_const 2
    have e : (fun z => a z * bondPhase P i j z ^ 2 / 2) = fun z => a z * (bondPhase P i j z ^ 2 / 2) := by
      funext z
      ring
    rw [e] at h
    have := h.tsum_eq
    rw [hval] at this
    linarith
  have hfin := ha2.hasSum.sub hdd2
  rw [hT] at hfin
  have hsing : ∀ w : Fin 4, ∑ l, P l * (((Pi.single w 1 : Fin 4 → ℤ) l : ℤ) : ℝ) = P w := by
    intro w
    simp [Pi.single_apply]
  have hp1 : bondPhase P i j 0 = (P j - P i) / 2 := by
    rw [bondPhase_eq]
    simp
  have hp2 : bondPhase P i j (-Pi.single j 1) = -P j + (P j - P i) / 2 := by
    rw [bondPhase_eq]
    simp only [Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib, hsing]
  have hp3 : bondPhase P i j (Pi.single i 1) = P i + (P j - P i) / 2 := by
    rw [bondPhase_eq, hsing]
  have hp4 : bondPhase P i j (Pi.single i 1 - Pi.single j 1) = P i - P j + (P j - P i) / 2 := by
    rw [bondPhase_eq]
    simp only [Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib, hsing]
  rw [hp1, hp2, hp3, hp4] at hfin
  have hfin2 : HasSum (fun z => g z * bondPhase P i j z ^ 2) _ :=
    (hasSum_iff_of_eq fun z => by ring).mpr hfin
  rw [hg] at hfin2
  convert hfin2 using 1
  rw [hDdef, ← hS]
  by_cases hij : i = j
  · simp only [hij, if_true]
    ring
  · simp only [hij, if_false]
    ring
end Moment
section Torus
variable {n : ℕ} [NeZero n]
private def liftSite (x : TorusSite n) : Fin 4 → ℤ := fun i => ((x i).val : ℤ) - n * round (((x i).val : ℝ) / n)
private theorem torusDisplacement_zero_eq (x : TorusSite n) (i : Fin 4) :
    torusDisplacement (0 : TorusSite n) x i = (liftSite x i : ℝ) := by
  unfold torusDisplacement circleSub liftSite
  simp
private theorem siteOfInt_liftSite (x : TorusSite n) : (siteOfInt (liftSite x) : TorusSite n) = x := by
  funext i
  simp [siteOfInt, liftSite]
private theorem two_mul_abs_liftSite_le (x : TorusSite n) (i : Fin 4) : 2 * |liftSite x i| ≤ (n : ℤ) := by
  have hn : (0 : ℝ) < n := by
    have := NeZero.pos n
    exact_mod_cast this
  have h := abs_sub_round (((x i).val : ℝ) / n)
  have e : ((liftSite x i : ℤ) : ℝ) = n * (((x i).val : ℝ) / n - round (((x i).val : ℝ) / n)) := by
    unfold liftSite
    push_cast
    field_simp
  have h2 : 2 * |((liftSite x i : ℤ) : ℝ)| ≤ n := by
    rw [e, abs_mul, abs_of_pos hn]
    nlinarith
  have h3 : ((2 * |liftSite x i| : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by
    push_cast
    exact h2
  exact_mod_cast h3
private theorem intCast_liftSite (x : TorusSite n) (i : Fin 4) : ((liftSite x i : ℤ) : ZMod n) = x i :=
  congrFun (siteOfInt_liftSite x) i
private theorem supNormZ_liftSite_le (x : TorusSite n) : supNormZ (liftSite x) ≤ supDist x 0 := by
  refine Finset.sup_le fun i _ => ?_
  have hv : ((x i).valMinAbs : ZMod n) = x i := ZMod.coe_valMinAbs _
  have hb : 2 * |(x i).valMinAbs| ≤ (n : ℤ) := by
    have := ZMod.natAbs_valMinAbs_le (x i)
    rw [Int.abs_eq_natAbs]
    omega
  have h := (abs_eq_of_intCast_eq ((intCast_liftSite x i).trans hv.symm) (two_mul_abs_liftSite_le x i) hb).1
  have h2 : (liftSite x i).natAbs = ((x i).valMinAbs).natAbs := by
    simp only [Int.abs_eq_natAbs] at h
    omega
  rw [h2]
  have h3 := Finset.le_sup (f := fun i => ((x i - (0 : TorusSite n) i).valMinAbs).natAbs) (Finset.mem_univ i)
  simpa [supDist] using h3
private theorem liftSite_injective : Function.Injective (liftSite (n := n)) := fun x y h => by
  rw [← siteOfInt_liftSite x, ← siteOfInt_liftSite y, h]
private theorem liftSite_siteOfInt {z : Fin 4 → ℤ} (hz : ∀ i, 2 * |z i| < (n : ℤ)) :
    liftSite (siteOfInt z : TorusSite n) = z := by
  funext i
  have h := abs_eq_of_intCast_eq (intCast_liftSite (siteOfInt z : TorusSite n) i) (two_mul_abs_liftSite_le _ i)
    (by have := hz i; omega)
  have h2 := (abs_eq_of_intCast_eq (intCast_liftSite (siteOfInt z : TorusSite n) i).symm (by have := hz i; omega)
    (two_mul_abs_liftSite_le _ i)).2 (hz i)
  exact h2.symm
private theorem two_mul_supNormZ_liftSite_le (x : TorusSite n) : 2 * supNormZ (liftSite x) ≤ n := by
  have h : supNormZ (liftSite x) ≤ n / 2 := by
    refine Finset.sup_le fun i _ => ?_
    have := two_mul_abs_liftSite_le x i
    rw [Int.abs_eq_natAbs] at this
    omega
  omega
end Torus
section Compare
private theorem add_siteOfInt_mem_supBall {n : ℕ} [NeZero n] (o : TorusSite n) {u : Fin 4 → ℤ} {r : ℕ}
    (hu : OffsetInBox r u) : o + siteOfInt u ∈ supBall o (r : ℝ) := by apply _root_.YangMills.SharedProofs.p7847 <;> assumption
private theorem supBall_isRegularRegion {n : ℕ} [NeZero n] (o : TorusSite n) {r : ℕ} (hr : 2048 ≤ r)
    (hn : 4 * r < n) : IsRegularRegion (supBall o (r : ℝ)) 1024 := by apply _root_.YangMills.SharedProofs.p31712 <;> assumption
private theorem univ_isRegularRegion {n : ℕ} [NeZero n] :
    IsRegularRegion (Finset.univ : Finset (TorusSite n)) 1024 :=
  fun _ => ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ _ _ _ _ _ => Finset.mem_univ _⟩
private theorem trivialField_isColdOn {n : ℕ} [NeZero n] {s : ℝ} (hs : 0 < s) (X : Finset (TorusSite n)) :
    IsColdOn s X (trivialField n) := by apply _root_.YangMills.SharedProofs.p25190 <;> assumption
private theorem imaginaryUnitI_pair_areUnitVectors : AreUnitVectors ![imaginaryUnitI, imaginaryUnitI] := by apply _root_.YangMills.SharedProofs.p1192 <;> assumption
private def TwoTorusComparison (a δ : ℝ) (L : ℕ) (C : ℝ) : Prop :=
  ∀ (t n n' : ℕ) [NeZero n] [NeZero n'] (X : Finset (TorusSite n)) (X' : Finset (TorusSite n'))
    (z : TorusSite n) (z' : TorusSite n') (m r : ℕ), 64 ≤ n → 64 ≤ n' → IsRegularRegion X 1024 →
    IsRegularRegion X' 1024 → 4 * m + 2 < n → 4 * m + 2 < n' → 4 * r + 4 ≤ m →
    (∀ h, OffsetInBox (2 * m) h → (z + siteOfInt h ∈ X ↔ z' + siteOfInt h ∈ X')) →
    ∀ (k : ℕ) (c : Fin k → (Fin 4 → ℤ) × Fin 4) (Xs : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 2 →
      AreUnitVectors Xs → (∀ l, OffsetInBox r (c l).1) →
      |mixedDeriv (actionAtLevel a L t X) (trivialField n) (fun l => bondFrom z (c l)) Xs -
          mixedDeriv (actionAtLevel a L t X') (trivialField n') (fun l => bondFrom z' (c l)) Xs| ≤
        C * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8)
private theorem abs_mixedDeriv_sub_limit_le {a δ C : ℝ} {L k : ℕ} (hB : TwoTorusComparison a δ L C)
    {Q : IntBond → IntBond → ℝ}
    (hQ : ∀ b b', Tendsto (fun N => cubeEntry a L k N b b') atTop (𝓝 (Q b b'))) {n : ℕ} [NeZero n] (hn : 64 ≤ n)
    {m d : ℕ} (hm : 4 * m + 2 < n) (hd : 4 * d + 4 ≤ m) {b b' : IntBond} (hb : OffsetInBox d b.1)
    (hb' : OffsetInBox d b'.1) :
    |mixedDeriv (actionAtLevel a L k (Finset.univ : Finset (TorusSite n))) (trivialField n)
        ![bondFrom 0 b, bondFrom 0 b'] ![imaginaryUnitI, imaginaryUnitI] - Q b b'| ≤
      C * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8) := by
  refine le_of_tendsto ((tendsto_const_nhds.sub (hQ b b')).abs) ?_
  filter_upwards [eventually_ge_atTop (2 * m + 2048)] with M hM
  have key := hB k n (16 * (M + 1)) Finset.univ (supBall 0 (M : ℝ)) 0 0 m d hn (by omega) univ_isRegularRegion
    (supBall_isRegularRegion 0 (by omega) (by omega)) hm (by omega) hd (fun h hh => ?_) 2 ![b, b']
    ![imaginaryUnitI, imaginaryUnitI] (by norm_num) (by norm_num) imaginaryUnitI_pair_areUnitVectors (by
      intro l
      fin_cases l
      · exact hb
      · exact hb')
  · have hf : ∀ (p : ℕ) [NeZero p], (fun l => bondFrom (0 : TorusSite p) ((![b, b'] : Fin 2 → IntBond) l)) =
        ![bondFrom 0 b, bondFrom 0 b'] := by
      intro p _
      funext l
      fin_cases l <;> rfl
    rw [hf, hf] at key
    exact key
  · have hh' : OffsetInBox M h := fun i => (hh i).trans (by exact_mod_cast (by omega : 2 * m ≤ M))
    exact ⟨fun _ => add_siteOfInt_mem_supBall 0 hh', fun _ => Finset.mem_univ _⟩
end Compare
section Assemble
private theorem abs_finsetSum_sub_hasSum_le (D : Finset (Fin 4 → ℤ)) {E q s W e : (Fin 4 → ℤ) → ℝ}
    {p ε K T : ℝ} (hp : 0 ≤ p) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hs0 : ∀ z, 0 ≤ s z) (hsW : ∀ z, s z ≤ p * W z)
    (hW : ∀ z, 0 ≤ W z) (he : ∀ z, 0 ≤ e z) (hw : Summable fun z => e z * W z)
    (h1 : ∀ z ∈ D, |E z - q z| ≤ ε + K * e z) (h2 : ∀ z, z ∉ D → |q z| ≤ K * e z)
    (hT : HasSum (fun z => q z * s z) T) :
    |∑ z ∈ D, E z * s z - T| ≤ p * (ε * ∑ z ∈ D, W z + 2 * K * ∑' z, e z * W z) := by
  classical
  obtain ⟨h, hh⟩ : ∃ h : (Fin 4 → ℤ) → ℝ, h = fun z => if z ∈ D then 0 else q z * s z := ⟨_, rfl⟩
  have hfin : HasSum (fun z => q z * s z - h z) (∑ z ∈ D, (q z * s z - h z)) :=
    hasSum_sum_of_ne_finset_zero fun z hz => by
      rw [hh]
      simp [hz]
  have hh' : HasSum h (T - ∑ z ∈ D, (q z * s z - h z)) := by
    have := hT.sub hfin
    refine (hasSum_iff_of_eq fun z => ?_).mpr this
    ring
  have hD : ∑ z ∈ D, (q z * s z - h z) = ∑ z ∈ D, q z * s z := by
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [hh]
    simp [hz]
  rw [hD] at hh'
  have hbnd : ∀ z, ‖h z‖ ≤ p * K * (e z * W z) := by
    intro z
    rw [hh]
    by_cases hz : z ∈ D
    · simp only [hz, if_true, norm_zero]
      exact mul_nonneg (mul_nonneg hp hK) (mul_nonneg (he z) (hW z))
    · simp only [hz, if_false, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hs0 z)]
      calc |q z| * s z ≤ (K * e z) * (p * W z) := mul_le_mul (h2 z hz) (hsW z) (hs0 z) (mul_nonneg hK (he z))
        _ = _ := by ring
  have htail : |T - ∑ z ∈ D, q z * s z| ≤ p * K * ∑' z, e z * W z := by
    have := tsum_of_norm_bounded (hw.hasSum.mul_left (p * K)) hbnd
    rwa [hh'.tsum_eq, Real.norm_eq_abs] at this
  have hsum : |∑ z ∈ D, (E z - q z) * s z| ≤ p * (ε * ∑ z ∈ D, W z + K * ∑' z, e z * W z) := by
    have hsub : ∑ z ∈ D, e z * W z ≤ ∑' z, e z * W z :=
      hw.sum_le_tsum D fun z _ => mul_nonneg (he z) (hW z)
    calc |∑ z ∈ D, (E z - q z) * s z| ≤ ∑ z ∈ D, |(E z - q z) * s z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z ∈ D, p * (ε * W z + K * (e z * W z)) := by
        refine Finset.sum_le_sum fun z hz => ?_
        rw [abs_mul, abs_of_nonneg (hs0 z)]
        calc |E z - q z| * s z ≤ (ε + K * e z) * (p * W z) :=
              mul_le_mul (h1 z hz) (hsW z) (hs0 z) (add_nonneg hε (mul_nonneg hK (he z)))
          _ = _ := by ring
      _ = p * (ε * ∑ z ∈ D, W z + K * ∑ z ∈ D, e z * W z) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ hp
        have := mul_le_mul_of_nonneg_left hsub hK
        linarith
  have e1 : ∑ z ∈ D, E z * s z - T = ∑ z ∈ D, (E z - q z) * s z - (T - ∑ z ∈ D, q z * s z) := by
    have e2 : ∑ z ∈ D, (E z - q z) * s z = ∑ z ∈ D, E z * s z - ∑ z ∈ D, q z * s z := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [e2]
    ring
  rw [e1]
  exact ((abs_sub _ _).trans (add_le_add hsum htail)).trans (le_of_eq (by ring))
end Assemble
section Assemble2
private theorem exp_neg_le_exp_half_mul {c₃ u d : ℝ} (hc : 0 < c₃) (hu : d ≤ u) :
    Real.exp (-c₃ * u) ≤ Real.exp (-(c₃ / 2) * d) * Real.exp (-(c₃ / 2) * u) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)
private theorem near_term_le {C₁ K₁ δ c : ℝ} {m N : ℕ} (hC₁ : 0 < C₁) (hK₁ : 0 < K₁) (hδ : 0 < δ)
    (hc1 : c ≤ δ / 80) (hpoly : (1 + (N : ℝ)) ^ 10 ≤ K₁ * Real.exp (δ / 80 * N)) (hm1 : (N : ℝ) / 5 - 1 ≤ m)
    (hmN : (m : ℝ) + 1 ≤ 1 + N) :
    C₁ * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8) * (4 * (1 + (N : ℝ)) ^ 6) ≤
      4 * C₁ * K₁ * Real.exp (δ / 8) * Real.exp (-(c * N)) := by
  have h1 : ((m : ℝ) + 1) ^ 4 ≤ (1 + (N : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) hmN 4
  have h3 : Real.exp (-δ * m / 8) * Real.exp (δ / 80 * N) ≤ Real.exp (δ / 8) * Real.exp (-(c * N)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  calc C₁ * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8) * (4 * (1 + (N : ℝ)) ^ 6)
      ≤ C₁ * (1 + (N : ℝ)) ^ 4 * Real.exp (-δ * m / 8) * (4 * (1 + (N : ℝ)) ^ 6) := by gcongr
    _ = 4 * C₁ * Real.exp (-δ * m / 8) * (1 + (N : ℝ)) ^ 10 := by ring
    _ ≤ 4 * C₁ * Real.exp (-δ * m / 8) * (K₁ * Real.exp (δ / 80 * N)) := by gcongr
    _ = 4 * C₁ * K₁ * (Real.exp (-δ * m / 8) * Real.exp (δ / 80 * N)) := by ring
    _ ≤ 4 * C₁ * K₁ * (Real.exp (δ / 8) * Real.exp (-(c * N))) := by gcongr
    _ = _ := by ring
private theorem far_term_le {C₃ Aw c₃ c : ℝ} {d N : ℕ} (hC₃ : 0 < C₃) (hAw : 0 ≤ Aw) (hc₃ : 0 < c₃)
    (hc2 : c ≤ c₃ / 64) (hd1 : (N : ℝ) / 32 - 1 ≤ d) :
    2 * (C₃ * Real.exp (-(c₃ / 2) * d)) * Aw ≤ 2 * C₃ * Aw * Real.exp (c₃ / 2) * Real.exp (-(c * N)) := by
  have h3 : Real.exp (-(c₃ / 2) * d) ≤ Real.exp (c₃ / 2) * Real.exp (-(c * N)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  calc 2 * (C₃ * Real.exp (-(c₃ / 2) * d)) * Aw = 2 * C₃ * Aw * Real.exp (-(c₃ / 2) * d) := by ring
    _ ≤ 2 * C₃ * Aw * (Real.exp (c₃ / 2) * Real.exp (-(c * N))) := by gcongr
    _ = _ := by ring
private theorem sum_weights_image_liftSite_le (N : ℕ) [NeZero N] :
    ∑ z ∈ (Finset.univ : Finset (TorusSite N)).image liftSite, 4 * (1 + (supNormZ z : ℝ)) ^ 2 ≤
      4 * (1 + (N : ℝ)) ^ 6 := by
  have hcard : (((Finset.univ : Finset (TorusSite N)).image liftSite).card : ℝ) ≤ (N : ℝ) ^ 4 := by
    have h1 : ((Finset.univ : Finset (TorusSite N)).image liftSite).card ≤ Fintype.card (TorusSite N) :=
      Finset.card_image_le
    have h2 : Fintype.card (TorusSite N) = N ^ 4 := by
      simp [TorusSite, ZMod.card]
    rw [h2] at h1
    exact_mod_cast h1
  have hone : ∀ z ∈ (Finset.univ : Finset (TorusSite N)).image liftSite,
      4 * (1 + (supNormZ z : ℝ)) ^ 2 ≤ 4 * (1 + (N : ℝ)) ^ 2 := by
    intro z hz
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz
    have h1 := two_mul_supNormZ_liftSite_le x
    have h2 : (supNormZ (liftSite x) : ℝ) ≤ N := by
      exact_mod_cast (by omega : supNormZ (liftSite x) ≤ N)
    have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + (supNormZ (liftSite x) : ℝ))
      (by linarith : 1 + (supNormZ (liftSite x) : ℝ) ≤ 1 + N) 2
    linarith
  calc ∑ z ∈ (Finset.univ : Finset (TorusSite N)).image liftSite, 4 * (1 + (supNormZ z : ℝ)) ^ 2
      ≤ ∑ _z ∈ (Finset.univ : Finset (TorusSite N)).image liftSite, 4 * (1 + (N : ℝ)) ^ 2 :=
        Finset.sum_le_sum hone
    _ = (((Finset.univ : Finset (TorusSite N)).image liftSite).card : ℝ) * (4 * (1 + (N : ℝ)) ^ 2) := by simp
    _ ≤ (N : ℝ) ^ 4 * (4 * (1 + (N : ℝ)) ^ 2) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ (1 + (N : ℝ)) ^ 4 * (4 * (1 + (N : ℝ)) ^ 2) := by
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) 4) (by positivity)
    _ = _ := by ring
private theorem sum_sites_eq_sum_liftSite (N : ℕ) [NeZero N] (P : Fin 4 → ℝ) (μ ν : Fin 4)
    (F : TorusSite N → ℝ) (E : (Fin 4 → ℤ) → ℝ) (hE : ∀ x, E (liftSite x) = F x) :
    ∑ x : TorusSite N, F x * (∑ i, P i * (torusDisplacement (0 : TorusSite N) x i +
        ((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2)) ^ 2 =
      ∑ z ∈ (Finset.univ : Finset (TorusSite N)).image liftSite, E z * bondPhase P μ ν z ^ 2 := by
  rw [Finset.sum_image liftSite_injective.injOn]
  refine Finset.sum_congr rfl fun x _ => ?_
  have e2 : bondPhase P μ ν (liftSite x) = ∑ i, P i * (torusDisplacement (0 : TorusSite N) x i +
      ((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2) := by
    unfold bondPhase
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [torusDisplacement_zero_eq]
    split_ifs <;> ring
  rw [hE, e2]
private theorem abs_entry_le_exp {N : ℕ} [NeZero N] {G : TorusField N → ℝ} {C₂ δ : ℝ} (hC₂ : 0 < C₂)
    (hδ : 0 < δ)
    (h : ∀ (c : Fin 2 → TorusBond N) (Xs : Fin 2 → imaginaryQuaternions), AreUnitVectors Xs →
      |mixedDeriv G (trivialField N) c Xs| ≤ C₂ * Real.exp (-δ * bondListSpread c))
    (μ ν : Fin 4) (x : TorusSite N) :
    |mixedDeriv G (trivialField N) ![bondFrom 0 ((0 : Fin 4 → ℤ), μ), bondFrom 0 (liftSite x, ν)]
        ![imaginaryUnitI, imaginaryUnitI]| ≤ C₂ * Real.exp (-δ * supNormZ (liftSite x)) := by
  refine (h _ _ imaginaryUnitI_pair_areUnitVectors).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC₂.le)
  obtain ⟨c, hc⟩ : ∃ c : Fin 2 → TorusBond N,
      c = ![bondFrom 0 ((0 : Fin 4 → ℤ), μ), bondFrom 0 (liftSite x, ν)] := ⟨_, rfl⟩
  rw [← hc]
  have h1 : supDist (c 0).1 (c 1).1 ≤ bondListSpread c :=
    le_trans (Finset.le_sup (f := fun l' => supDist (c 0).1 (c l').1) (Finset.mem_univ (1 : Fin 2)))
      (Finset.le_sup (f := fun l => Finset.univ.sup fun l' => supDist (c l).1 (c l').1)
        (Finset.mem_univ (0 : Fin 2)))
  have h2 : supDist (c 0).1 (c 1).1 = supDist x 0 := by
    have b1 : (c 0).1 = 0 := by
      rw [hc]
      show (0 : TorusSite N) + siteOfInt 0 = 0
      funext i
      simp [siteOfInt]
    have b2 : (c 1).1 = x := by
      rw [hc]
      show (0 : TorusSite N) + siteOfInt (liftSite x) = x
      rw [zero_add]
      exact siteOfInt_liftSite x
    rw [b1, b2, supDist_comm]
  have h4 : (supNormZ (liftSite x) : ℝ) ≤ bondListSpread c := by
    exact_mod_cast (supNormZ_liftSite_le x).trans (h2 ▸ h1)
  nlinarith
private theorem maxwellKernel_eq_mixedDeriv (a : ℝ) (L k N : ℕ) [NeZero N] (μ ν : Fin 4) (z : Fin 4 → ℤ) :
    maxwellKernel a L k ((0 : TorusSite N), μ) ((siteOfInt z : TorusSite N), ν) =
      mixedDeriv (actionAtLevel a L k (Finset.univ : Finset (TorusSite N))) (trivialField N)
        ![bondFrom 0 ((0 : Fin 4 → ℤ), μ), bondFrom 0 (z, ν)] ![imaginaryUnitI, imaginaryUnitI] := by
  have b1 : bondFrom (0 : TorusSite N) ((0 : Fin 4 → ℤ), μ) = ((0 : TorusSite N), μ) := by
    simp only [bondFrom, zero_add]
    refine Prod.ext ?_ rfl
    funext i
    simp [siteOfInt]
  have b2 : bondFrom (0 : TorusSite N) (z, ν) = ((siteOfInt z : TorusSite N), ν) := by
    simp [bondFrom]
  rw [b1, b2]
  rfl
private theorem secondMomentAt_of_parameters (tbl : ParameterAssignment) (y : ℝ) (hD : tbl.Admissible)
    (hC : cubeLimitFormStatement) (hT : FlatActionDerivativesAgree) (hA : ActionSmoothAlongMoves)
    (hS : ∀ c₁ C₁ : ℝ, 0 < c₁ → ∃ C : ℝ, ∀ (k : ℕ) (Q : IntBond → IntBond → ℝ),
      IsLimitForm tbl.coupling tbl.coercivity c₁ C₁ tbl.side k Q → ∀ (i j : Fin 4) (p : Fin 4 → ℝ),
        p ∈ brillouinBox →
        ‖midpointSymbol Q i j p - (if i = j then (momentumNormSq p : ℂ) else 0)‖ ≤ C * momentumNormSq p ^ 2) :
    MaxwellKernelSecondMomentAt tbl y := by
  have hc := hD.chain
  have hδ : 0 < tbl.δ₁ := hD.δ₁_pos
  have ha : 0 < tbl.coupling := by linarith [hD.a_ge]
  obtain ⟨C₁, hC₁, hB⟩ := hT tbl.coupling tbl.δ₁ tbl.side tbl.lam tbl.ρA tbl.σA tbl.cg tbl.N ha hD.L_odd hc
  have hB' : TwoTorusComparison tbl.coupling tbl.δ₁ tbl.side C₁ := fun t n n' _ _ => hB t n n'
  obtain ⟨C₂, hC₂, hSp⟩ := hA tbl.coupling tbl.δ₁ tbl.side tbl.lam tbl.ρA tbl.σA tbl.cg tbl.N ha hD.L_odd hc
  have hσ : 0 < tbl.σA := by
    obtain ⟨-, -, -, -, -, h, -, -, -⟩ := hc
    exact h
  obtain ⟨cQ, CQ, R₀, hcQ, HQ⟩ := hC tbl hD
  obtain ⟨C', HS⟩ := hS cQ CQ hcQ
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = tbl.δ₁ := ⟨_, rfl⟩
  rw [← hδdef] at hδ
  obtain ⟨c₃, hc₃def⟩ : ∃ c₃, c₃ = min δ cQ := ⟨_, rfl⟩
  have hc₃ : 0 < c₃ := hc₃def ▸ lt_min hδ hcQ
  have hc₃δ : c₃ ≤ δ := hc₃def ▸ min_le_left _ _
  have hc₃Q : c₃ ≤ cQ := hc₃def ▸ min_le_right _ _
  obtain ⟨C₃, hC₃def⟩ : ∃ C₃, C₃ = C₂ + |CQ| := ⟨_, rfl⟩
  have hC₃ : 0 < C₃ := by
    rw [hC₃def]
    positivity
  have hw : Summable fun z : Fin 4 → ℤ => Real.exp (-(c₃ / 2) * supNormZ z) * (4 * (1 + (supNormZ z : ℝ)) ^ 2) := by
    have h := (summable_exp_mul_pow (half_pos hc₃) 2).mul_left 4
    refine (summable_congr fun z => ?_).mp h
    ring
  obtain ⟨Aw, hAw⟩ : ∃ Aw, Aw = ∑' z : Fin 4 → ℤ,
      Real.exp (-(c₃ / 2) * supNormZ z) * (4 * (1 + (supNormZ z : ℝ)) ^ 2) := ⟨_, rfl⟩
  have hAw0 : 0 ≤ Aw := hAw ▸ tsum_nonneg fun z => by positivity
  obtain ⟨K₁, hK₁, hpoly⟩ := one_add_pow_le_exp 10 (by positivity : 0 < δ / 80)
  obtain ⟨c, hcdef⟩ : ∃ c, c = min (δ / 80) (c₃ / 64) := ⟨_, rfl⟩
  have hc0 : 0 < c := hcdef ▸ lt_min (by positivity) (by positivity)
  have hc1 : c ≤ δ / 80 := hcdef ▸ min_le_left _ _
  have hc2 : c ≤ c₃ / 64 := hcdef ▸ min_le_right _ _
  refine ⟨(4 * C₁ * K₁ * Real.exp (δ / 8) + 2 * C₃ * Aw * Real.exp (c₃ / 2)) / 2, c, hc0,
    fun k N _ hN P μ ν => ?_⟩
  have hN4 : 4096 ≤ N := hD.n₀_ge.trans hN
  obtain ⟨Q, hQ, -⟩ := HQ k
  obtain ⟨m, hmdef⟩ : ∃ m, m = N / 5 := ⟨_, rfl⟩
  obtain ⟨d, hddef⟩ : ∃ d, d = N / 32 := ⟨_, rfl⟩
  have hm : 4 * m + 2 < N := by omega
  have hd : 4 * d + 4 ≤ m := by omega
  have hdN : 2 * d < N := by omega
  have hdec : ∀ (z : Fin 4 → ℤ) (i j : Fin 4), |Q (0, i) (z, j)| ≤ CQ * Real.exp (-cQ * supNormZ z) := by
    intro z i j
    have h := hQ.decay (0, i) (z, j)
    have e : bondSupDist ((0 : Fin 4 → ℤ), i) (z, j) = supNormZ z := by
      unfold bondSupDist supNormZ
      simp
    rw [e] at h
    refine h.trans (le_of_eq ?_)
    congr 2
    ring
  have hmom := secondMoment_of_symbol Q hcQ hdec μ ν (HS k Q hQ μ ν) P
  obtain ⟨Ez, hEzdef⟩ : ∃ Ez : (Fin 4 → ℤ) → ℝ,
      Ez = fun z => maxwellKernel tbl.coupling tbl.side k ((0 : TorusSite N), μ) ((siteOfInt z : TorusSite N), ν) :=
    ⟨_, rfl⟩
  have hEz : ∀ z, Ez z = mixedDeriv (actionAtLevel tbl.coupling tbl.side k (Finset.univ : Finset (TorusSite N)))
      (trivialField N) ![bondFrom 0 ((0 : Fin 4 → ℤ), μ), bondFrom 0 (z, ν)] ![imaginaryUnitI, imaginaryUnitI] := by
    intro z
    rw [hEzdef]
    exact maxwellKernel_eq_mixedDeriv _ _ _ _ _ _ _
  obtain ⟨Dn, hDn⟩ : ∃ Dn : Finset (Fin 4 → ℤ), Dn = (Finset.univ : Finset (TorusSite N)).image liftSite :=
    ⟨_, rfl⟩
  have hfar : ∀ x : TorusSite N, |Ez (liftSite x)| ≤ C₂ * Real.exp (-δ * supNormZ (liftSite x)) := by
    intro x
    rw [hEz, hδdef]
    refine abs_entry_le_exp hC₂ (hδdef ▸ hδ) (fun c Xs hX => ?_) μ ν x
    exact (hSp k N (by omega) Finset.univ (trivialField N) univ_isRegularRegion
      (trivialField_isColdOn hσ _)).2.1 2 c Xs (by norm_num) (by norm_num) hX
  have hsmall : ∀ z : Fin 4 → ℤ, ¬ OffsetInBox d z → (d : ℝ) ≤ supNormZ z := by
    intro z hz
    have : d ≤ supNormZ z := by
      by_contra hlt
      push_neg at hlt
      apply hz
      intro i
      have := natAbs_le_supNormZ z i
      rw [Int.abs_eq_natAbs]
      omega
    exact_mod_cast this
  have hq_le : ∀ z, |Q (0, μ) (z, ν)| ≤ |CQ| * Real.exp (-c₃ * supNormZ z) := by
    intro z
    refine (hdec z μ ν).trans ?_
    refine mul_le_mul (le_abs_self _) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (abs_nonneg _)
    have : (0 : ℝ) ≤ supNormZ z := by positivity
    nlinarith
  have hK0 : 0 ≤ C₃ * Real.exp (-(c₃ / 2) * d) := by positivity
  have hε0 : 0 ≤ C₁ * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8) := by positivity
  have hS0 : 0 ≤ sqNorm P := Finset.sum_nonneg fun l _ => sq_nonneg _
  have key := abs_finsetSum_sub_hasSum_le Dn (E := Ez) (q := fun z => Q (0, μ) (z, ν))
    (s := fun z => bondPhase P μ ν z ^ 2)
    (W := fun z => 4 * (1 + (supNormZ z : ℝ)) ^ 2) (e := fun z => Real.exp (-(c₃ / 2) * supNormZ z)) hS0 hε0 hK0
    (fun z => sq_nonneg _) (fun z => bondPhase_sq_le P μ ν z) (fun z => by positivity)
    (fun z => (Real.exp_pos _).le) hw (fun z hz => ?_) (fun z hz => ?_) hmom
  · have hsum := sum_sites_eq_sum_liftSite N P μ ν
      (fun x => maxwellKernel tbl.coupling tbl.side k ((0 : TorusSite N), μ) (x, ν)) Ez (fun x => by
        rw [hEzdef]
        simp only [siteOfInt_liftSite])
    have hW := sum_weights_image_liftSite_le N
    rw [← hDn] at hsum hW
    have hm1 : (N : ℝ) / 5 - 1 ≤ m := by
      have h1 : N ≤ 5 * m + 4 := by omega
      have h2 : (N : ℝ) ≤ 5 * m + 4 := by exact_mod_cast h1
      linarith
    have hd1 : (N : ℝ) / 32 - 1 ≤ d := by
      have h1 : N ≤ 32 * d + 31 := by omega
      have h2 : (N : ℝ) ≤ 32 * d + 31 := by exact_mod_cast h1
      linarith
    have hmN : (m : ℝ) + 1 ≤ 1 + N := by
      have h1 : m ≤ N := by omega
      have h2 : (m : ℝ) ≤ N := by exact_mod_cast h1
      linarith
    have t1 := near_term_le (c := c) hC₁ hK₁ hδ hc1 (hpoly N (by positivity)) hm1 hmN
    have t2 := far_term_le (c := c) hC₃ hAw0 hc₃ hc2 hd1
    have hside : (ParameterAssignment.stepParameters tbl y).side = tbl.side := rfl
    rw [hside, hsum]
    rw [← hAw] at key
    have hfin : |∑ z ∈ Dn, Ez z * bondPhase P μ ν z ^ 2 -
        -2 * (sqNorm P * (if μ = ν then 1 else 0) - P μ * P ν)| ≤
        sqNorm P * ((4 * C₁ * K₁ * Real.exp (δ / 8) + 2 * C₃ * Aw * Real.exp (c₃ / 2)) * Real.exp (-(c * N))) := by
      refine key.trans (mul_le_mul_of_nonneg_left ?_ hS0)
      have h1 := mul_le_mul_of_nonneg_left hW hε0
      linarith
    have e : (1 / 2 : ℝ) * ∑ z ∈ Dn, Ez z * bondPhase P μ ν z ^ 2 +
        (sqNorm P * (if μ = ν then 1 else 0) - P μ * P ν) =
        (1 / 2) * (∑ z ∈ Dn, Ez z * bondPhase P μ ν z ^ 2 -
          -2 * (sqNorm P * (if μ = ν then 1 else 0) - P μ * P ν)) := by ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc _ ≤ (1 / 2 : ℝ) * _ := mul_le_mul_of_nonneg_left hfin (by norm_num)
      _ = _ := by ring
  · rw [hDn] at hz
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz
    by_cases hb : OffsetInBox d (liftSite x)
    · have h := abs_mixedDeriv_sub_limit_le (k := k) hB' hQ.tendsto (n := N) (by omega) hm hd
        (b := ((0 : Fin 4 → ℤ), μ)) (b' := (liftSite x, ν)) (fun i => by simp) hb
      rw [← hEz, ← hδdef] at h
      refine h.trans (le_add_of_nonneg_right ?_)
      positivity
    · have h0 := hsmall _ hb
      have h1 := hfar x
      have h2 := hq_le (liftSite x)
      have h3 : Real.exp (-δ * supNormZ (liftSite x)) ≤ Real.exp (-c₃ * supNormZ (liftSite x)) := by
        refine Real.exp_le_exp.mpr ?_
        have : (0 : ℝ) ≤ supNormZ (liftSite x) := by positivity
        nlinarith
      have h4 := exp_neg_le_exp_half_mul hc₃ h0
      have h5 : |Ez (liftSite x) - Q (0, μ) (liftSite x, ν)| ≤ C₃ * Real.exp (-c₃ * supNormZ (liftSite x)) := by
        refine (abs_sub _ _).trans ?_
        rw [hC₃def, add_mul]
        exact add_le_add (h1.trans (mul_le_mul_of_nonneg_left h3 hC₂.le)) h2
      refine h5.trans ?_
      calc C₃ * Real.exp (-c₃ * supNormZ (liftSite x)) ≤
            C₃ * (Real.exp (-(c₃ / 2) * d) * Real.exp (-(c₃ / 2) * supNormZ (liftSite x))) :=
            mul_le_mul_of_nonneg_left h4 hC₃.le
        _ = C₃ * Real.exp (-(c₃ / 2) * d) * Real.exp (-(c₃ / 2) * supNormZ (liftSite x)) := by ring
        _ ≤ _ := le_add_of_nonneg_left hε0
  · have hb : ¬ OffsetInBox d z := by
      intro hb
      apply hz
      rw [hDn]
      refine Finset.mem_image.mpr ⟨siteOfInt z, Finset.mem_univ _, liftSite_siteOfInt fun i => ?_⟩
      have := hb i
      omega
    have h0 := hsmall _ hb
    have h4 := exp_neg_le_exp_half_mul hc₃ h0
    refine (hq_le z).trans ?_
    calc |CQ| * Real.exp (-c₃ * supNormZ z) ≤ C₃ * Real.exp (-c₃ * supNormZ z) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          rw [hC₃def]
          linarith
      _ ≤ C₃ * (Real.exp (-(c₃ / 2) * d) * Real.exp (-(c₃ / 2) * supNormZ z)) :=
          mul_le_mul_of_nonneg_left h4 hC₃.le
      _ = _ := by ring
end Assemble2
theorem maxwellKernelSecondMoment_proof (h₁ : cubeLimitFormStatement) (h₂ : FlatActionDerivativesAgree)
    (h₃ : ActionSmoothAlongMoves) (h₄ : symbolPropertiesStatement) : maxwellKernelSecondMomentStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, hrt, H⟩ := h₄ a ha
  refine ⟨L₀, rt₀, 0, hrt, fun L hL hL₀ T hTa hTL hD _ _ hrt' _ => ?_⟩
  obtain ⟨y₀, Hy⟩ := H L hL hL₀ T hTa hTL hD hrt'
  refine ⟨y₀, fun y hy hret hrow => ?_⟩
  have hcl := Hy y hy hret hrow
  exact secondMomentAt_of_parameters T y hD h₁ h₂ h₃ fun c₁ C₁ hc₁ => by
    obtain ⟨c, C, D, -, HH⟩ := hcl c₁ C₁ hc₁
    exact ⟨C, fun k Q hQ => (HH k Q hQ).1.2.2⟩
end ResponseInTheExpansion.MaxwellMoment
end YangMills.Construction
end
