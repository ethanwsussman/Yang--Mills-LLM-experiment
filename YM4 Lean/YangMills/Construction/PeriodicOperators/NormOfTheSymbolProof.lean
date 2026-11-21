import YangMills.Construction.Lattice.ClosedFormsWithVanishingAveragesAreDifferencesProof
import YangMills.Construction.PeriodicOperators.NormOfTheSymbol
import YangMills.Construction.PeriodicOperators.OrbitsOfAPeriodicIndexSet
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.PeriodicOperators.SeriesOfTheSymbol
import YangMills.Construction.PeriodicOperators.SymbolOnClassesAndPlaneWaves
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SymbolNorm
def intCube (N : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N
theorem mem_intCube {N : ℕ} {n : Fin 4 → ℤ} : n ∈ intCube N ↔ ∀ μ, -(N : ℤ) ≤ n μ ∧ n μ ≤ N := by apply _root_.YangMills.Construction.PeriodicLattice.VanishingAverageGradients.mem_cubeBox <;> assumption
theorem card_intCube (N : ℕ) : ((intCube N).card : ℝ) = (2 * (N : ℝ) + 1) ^ 4 := by
  have h : (intCube N).card = (2 * N + 1) ^ 4 := by
    simp only [intCube, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Int.card_Icc]
    congr 1
    omega
  rw [h]
  push_cast
  ring
def leavingSet (N : ℕ) (m : Fin 4 → ℤ) : Finset (Fin 4 → ℤ) :=
  (intCube N).filter fun n => n + m ∉ intCube N
theorem card_leavingSet_le {N M : ℕ} {m : Fin 4 → ℤ} (hM : ∀ μ, |m μ| ≤ M) (hN : M ≤ N) :
    ((leavingSet N m).card : ℝ) ≤
      (2 * (N : ℝ) + 1) ^ 4 - (2 * ((N - M : ℕ) : ℝ) + 1) ^ 4 := by
  have hsub : intCube (N - M) ⊆ (intCube N).filter fun n => n + m ∈ intCube N := by
    intro n hn
    rw [mem_intCube] at hn
    simp only [Finset.mem_filter, mem_intCube, Pi.add_apply]
    refine ⟨fun μ => ?_, fun μ => ?_⟩
    · have h1 := hn μ
      omega
    · have h1 := hn μ
      have h2 := abs_le.mp (hM μ)
      omega
  have hc : ((intCube N).filter fun n => n + m ∈ intCube N).card + (leavingSet N m).card =
      (intCube N).card := by
    unfold leavingSet
    exact Finset.card_filter_add_card_filter_not _
  have h1 := Finset.card_le_card hsub
  have h2 : ((intCube (N - M)).card : ℝ) ≤
      (((intCube N).filter fun n => n + m ∈ intCube N).card : ℝ) := by
    exact_mod_cast h1
  have h3 : (((intCube N).filter fun n => n + m ∈ intCube N).card : ℝ) +
      ((leavingSet N m).card : ℝ) = ((intCube N).card : ℝ) := by
    exact_mod_cast hc
  rw [card_intCube] at h2 h3
  linarith
theorem tendsto_card_leavingSet_div (m : Fin 4 → ℤ) :
    Tendsto (fun N : ℕ => ((leavingSet N m).card : ℝ) / (2 * (N : ℝ) + 1) ^ 4) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ μ, |m μ| ≤ M := by
    refine ⟨∑ μ, (m μ).natAbs, fun μ => ?_⟩
    have h : (m μ).natAbs ≤ ∑ μ, (m μ).natAbs :=
      Finset.single_le_sum (f := fun μ => (m μ).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ μ)
    have h' : ((m μ).natAbs : ℤ) ≤ ((∑ μ, (m μ).natAbs : ℕ) : ℤ) := by exact_mod_cast h
    rwa [Int.natCast_natAbs] at h'
  have hden : Tendsto (fun N : ℕ => 2 * (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hupper : Tendsto (fun N : ℕ => (8 * (M : ℝ)) / (2 * (N : ℝ) + 1)) atTop (𝓝 0) :=
    hden.const_div_atTop _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun N => by positivity) ?_
  filter_upwards [eventually_ge_atTop M] with N hN
  have hle := card_leavingSet_le hM hN
  set a : ℝ := 2 * (N : ℝ) + 1 with ha
  set b : ℝ := 2 * ((N - M : ℕ) : ℝ) + 1 with hb
  have hapos : 0 < a := by positivity
  have hbpos : 0 ≤ b := by positivity
  have hab : a - b = 2 * (M : ℝ) := by
    rw [ha, hb, Nat.cast_sub hN]
    ring
  have hba : b ≤ a := by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have h4 : a ^ 4 - b ^ 4 ≤ 8 * (M : ℝ) * a ^ 3 := by
    have e1 : a ^ 4 - b ^ 4 = (a - b) * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) := by ring
    have e2 : a ^ 2 * b ≤ a ^ 3 := by nlinarith [sq_nonneg a]
    have e3 : a * b ^ 2 ≤ a ^ 3 := by
      have : b ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hbpos hba 2
      nlinarith
    have e4 : b ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ hbpos hba 3
    rw [e1, hab]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith
  rw [div_le_div_iff₀ (by positivity) hapos]
  have h5 : ((leavingSet N m).card : ℝ) ≤ 8 * (M : ℝ) * a ^ 3 := hle.trans h4
  calc ((leavingSet N m).card : ℝ) * a ≤ 8 * (M : ℝ) * a ^ 3 * a :=
        mul_le_mul_of_nonneg_right h5 hapos.le
    _ = 8 * (M : ℝ) * a ^ 4 := by ring
theorem tendsto_boundaryMass (t : (Fin 4 → ℤ) → ℝ) (ht0 : ∀ m, 0 ≤ t m) (ht : Summable t) :
    Tendsto (fun N : ℕ => ((2 * (N : ℝ) + 1) ^ 4)⁻¹ *
      ∑ n ∈ intCube N, ∑' m, (if n + m ∈ intCube N then 0 else t m)) atTop (𝓝 0) := by
  have hsum : ∀ (N : ℕ) (n : Fin 4 → ℤ),
      Summable fun m => if n + m ∈ intCube N then 0 else t m := fun N n =>
    Summable.of_nonneg_of_le (fun m => by split_ifs <;> simp [ht0 m])
      (fun m => by split_ifs <;> simp [ht0 m]) ht
  have hrew : ∀ N : ℕ, ((2 * (N : ℝ) + 1) ^ 4)⁻¹ *
      ∑ n ∈ intCube N, ∑' m, (if n + m ∈ intCube N then 0 else t m) =
      ∑' m, t m * (((leavingSet N m).card : ℝ) / (2 * (N : ℝ) + 1) ^ 4) := by
    intro N
    rw [← Summable.tsum_finsetSum fun n _ => hsum N n, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    have hcount : ∑ n ∈ intCube N, (if n + m ∈ intCube N then (0 : ℝ) else t m) =
        ((leavingSet N m).card : ℝ) * t m := by
      unfold leavingSet
      rw [Finset.card_filter]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases h : n + m ∈ intCube N <;> simp [h]
    rw [hcount]
    ring
  simp only [hrew]
  have hlim : Tendsto (fun N : ℕ =>
      ∑' m, t m * (((leavingSet N m).card : ℝ) / (2 * (N : ℝ) + 1) ^ 4)) atTop
      (𝓝 (∑' _ : Fin 4 → ℤ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := t) ht (fun m => ?_)
      (Eventually.of_forall fun N m => ?_)
    · simpa using (tendsto_card_leavingSet_div m).const_mul (t m)
    · have hcard : ((leavingSet N m).card : ℝ) ≤ (2 * (N : ℝ) + 1) ^ 4 := by
        rw [← card_intCube]
        exact_mod_cast Finset.card_filter_le _ _
      have hpos : (0 : ℝ) < (2 * (N : ℝ) + 1) ^ 4 := by positivity
      have hq : ((leavingSet N m).card : ℝ) / (2 * (N : ℝ) + 1) ^ 4 ≤ 1 :=
        (div_le_one hpos).mpr hcard
      have hq0 : 0 ≤ ((leavingSet N m).card : ℝ) / (2 * (N : ℝ) + 1) ^ 4 := by positivity
      rw [Real.norm_of_nonneg (mul_nonneg (ht0 m) hq0)]
      nlinarith [ht0 m]
  simpa using hlim
def cubeScale (N : ℕ) : ℝ := ((2 * (N : ℝ) + 1) ^ 2)⁻¹
theorem cubeScale_pos (N : ℕ) : 0 < cubeScale N := by
  unfold cubeScale
  positivity
theorem cubeScale_sq (N : ℕ) : cubeScale N ^ 2 = ((2 * (N : ℝ) + 1) ^ 4)⁻¹ := by
  unfold cubeScale
  rw [inv_pow]
  ring_nf
theorem card_mul_cubeScale_sq (N : ℕ) : ((intCube N).card : ℝ) * cubeScale N ^ 2 = 1 := by
  rw [card_intCube, cubeScale_sq]
  exact mul_inv_cancel₀ (by positivity)
section Product
variable {C C' A A' : Type} [Fintype C] [Fintype C']
  (e : C × (Fin 4 → ℤ) ≃ A) (e' : C' × (Fin 4 → ℤ) ≃ A')
def truncate (N : ℕ) (u : A → ℂ) : A → ℂ :=
  fun a => if (e.symm a).2 ∈ intCube N then (cubeScale N : ℂ) * u a else 0
omit [Fintype C] in
theorem truncate_apply (N : ℕ) (u : A → ℂ) (c : C) (n : Fin 4 → ℤ) :
    truncate e N u (e (c, n)) = if n ∈ intCube N then (cubeScale N : ℂ) * u (e (c, n)) else 0 := by
  simp [truncate]
theorem summable_of_support_intCube (N : ℕ) (G : A → ℝ)
    (h : ∀ c n, n ∉ intCube N → G (e (c, n)) = 0) :
    Summable G := by
  refine (e.summable_iff).mp (summable_of_ne_finset_zero (s := Finset.univ ×ˢ intCube N) ?_)
  rintro ⟨c, n⟩ hp
  exact h c n (by simpa using hp)
theorem tsum_of_support_intCube (N : ℕ) (G : A → ℝ)
    (h : ∀ c n, n ∉ intCube N → G (e (c, n)) = 0) :
    ∑' a, G a = ∑ c, ∑ n ∈ intCube N, G (e (c, n)) := by
  rw [← e.tsum_eq G, tsum_eq_sum (s := Finset.univ ×ˢ intCube N), Finset.sum_product]
  rintro ⟨c, n⟩ hp
  exact h c n (by simpa using hp)
theorem truncate_normSummable (N : ℕ) (w : A → ℝ) (u : A → ℂ) :
    NormSummable w (truncate e N u) := by
  unfold NormSummable
  refine summable_of_support_intCube e N _ fun c n hn => ?_
  simp [truncate_apply, hn]
theorem tsum_weight_truncate_sq (N : ℕ) {w : A → ℝ} {W : C → ℝ} (hw : ∀ c n, w (e (c, n)) = W c)
    {u : A → ℂ} {p : C → ℝ} (hu : ∀ c n, ‖u (e (c, n))‖ = p c) :
    ∑' a, w a * ‖truncate e N u a‖ ^ 2 = ∑ c, W c * p c ^ 2 := by
  rw [tsum_of_support_intCube e N _ fun c n hn => by simp [truncate_apply, hn]]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hterm : ∀ n ∈ intCube N, w (e (c, n)) * ‖truncate e N u (e (c, n))‖ ^ 2 =
      W c * p c ^ 2 * cubeScale N ^ 2 := by
    intro n hn
    rw [truncate_apply, if_pos hn, hw, norm_mul, hu, Complex.norm_real,
      Real.norm_of_nonneg (cubeScale_pos N).le]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  calc ((intCube N).card : ℝ) * (W c * p c ^ 2 * cubeScale N ^ 2)
      = W c * p c ^ 2 * (((intCube N).card : ℝ) * cubeScale N ^ 2) := by ring
    _ = W c * p c ^ 2 := by rw [card_mul_cubeScale_sq, mul_one]
omit [Fintype C'] in
theorem norm_scale_applyKernel_sub_le (N : ℕ) (K : A' → A → ℂ) (t : C' → C → (Fin 4 → ℤ) → ℝ)
    (hK : ∀ c' c n m, ‖K (e' (c', n)) (e (c, n + m))‖ = t c' c m)
    {u : A → ℂ} {p : C → ℝ} (hu : ∀ c n, ‖u (e (c, n))‖ = p c) (c' : C') (n' : Fin 4 → ℤ)
    (hsum : ApplySummableAt K u (e' (c', n')))
    (hcut : ApplySummableAt K (truncate e N u) (e' (c', n'))) :
    ‖(cubeScale N : ℂ) * applyKernel K u (e' (c', n')) -
        applyKernel K (truncate e N u) (e' (c', n'))‖ ≤
      cubeScale N * ∑ c, p c * ∑' m, (if n' + m ∈ intCube N then 0 else t c' c m) := by
  set a' := e' (c', n') with ha'
  have hS1 : Summable fun a => K a' a * u a := Summable.of_norm hsum
  have hS2 : Summable fun a => K a' a * truncate e N u a := Summable.of_norm hcut
  let Gd : A → ℝ := fun a =>
    if (e.symm a).2 ∈ intCube N then 0 else cubeScale N * ‖K a' a * u a‖
  have hGs : Summable Gd := by
    refine Summable.of_nonneg_of_le (fun a => ?_) (fun a => ?_)
      ((show Summable fun a => ‖K a' a * u a‖ from hsum).mul_left (cubeScale N))
    · have := cubeScale_pos N
      simp only [Gd]
      split_ifs <;> positivity
    · have := cubeScale_pos N
      simp only [Gd]
      split_ifs <;> first | positivity | exact le_rfl
  have hD : ∀ a, ‖(cubeScale N : ℂ) * (K a' a * u a) - K a' a * truncate e N u a‖ ≤ Gd a := by
    intro a
    simp only [Gd, truncate]
    split_ifs with h
    · have : (cubeScale N : ℂ) * (K a' a * u a) - K a' a * ((cubeScale N : ℂ) * u a) = 0 := by ring
      simp [this]
    · simp only [mul_zero, sub_zero, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (cubeScale_pos N).le, le_refl]
  have heq : (cubeScale N : ℂ) * applyKernel K u a' - applyKernel K (truncate e N u) a' =
      ∑' a, ((cubeScale N : ℂ) * (K a' a * u a) - K a' a * truncate e N u a) := by
    simp only [applyKernel]
    rw [← tsum_mul_left, ← (hS1.mul_left _).tsum_sub hS2]
  rw [heq]
  refine (tsum_of_norm_bounded hGs.hasSum hD).trans (le_of_eq ?_)
  have hprod : Summable (Gd ∘ e) := (e.summable_iff).mpr hGs
  rw [← e.tsum_eq Gd, show (∑' p, Gd (e p)) = ∑' p, (Gd ∘ e) p from rfl, hprod.tsum_prod,
    tsum_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← (Equiv.addLeft n').tsum_eq, ← mul_assoc, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  simp only [Function.comp, Gd, Equiv.coe_addLeft, Equiv.symm_apply_apply, norm_mul, hu]
  split_ifs
  · simp
  · rw [ha', hK]
    ring
theorem sum_weight_sq_le_of_intCube (N : ℕ) {w : A → ℝ} {w' : A' → ℝ} {W : C → ℝ} {W' : C' → ℝ}
    (hW' : ∀ c, 0 ≤ W' c) (hw : ∀ c n, w (e (c, n)) = W c) (hw' : ∀ c n, w' (e' (c, n)) = W' c)
    (hw'0 : ∀ a, 0 ≤ w' a) (K : A' → A → ℂ) (t : C' → C → (Fin 4 → ℤ) → ℝ)
    (hK : ∀ c' c n m, ‖K (e' (c', n)) (e (c, n + m))‖ = t c' c m)
    {u : A → ℂ} {p : C → ℝ} (hu : ∀ c n, ‖u (e (c, n))‖ = p c)
    {F : A' → ℂ} {q : C' → ℝ} (hq : ∀ c, 0 ≤ q c) (hF : ∀ c n, ‖F (e' (c, n))‖ = q c)
    (hKu : ∀ a', ApplySummableAt K u a' ∧ applyKernel K u a' = F a') {B : ℝ}
    (hB : ∀ f, NormSummable w f → wNorm w f ≤ 1 →
      (∀ a', ApplySummableAt K f a') ∧ NormSummable w' (applyKernel K f) ∧
        wNorm w' (applyKernel K f) ≤ B)
    (hp1 : ∑ c, W c * p c ^ 2 ≤ 1) :
    ∑ c, W' c * q c ^ 2 ≤ Real.sqrt (∑ c, W' c * q c ^ 2) * B +
      ∑ c', ∑ c, W' c' * q c' * p c * (((2 * (N : ℝ) + 1) ^ 4)⁻¹ *
        ∑ n ∈ intCube N, ∑' m, (if n + m ∈ intCube N then 0 else t c' c m)) := by
  have hs := cubeScale_pos N
  have hnorm : wNorm w (truncate e N u) ≤ 1 := by
    unfold wNorm
    rw [tsum_weight_truncate_sq e N hw hu]
    exact Real.sqrt_le_one.mpr hp1
  obtain ⟨hform, hG, hGB⟩ := hB _ (truncate_normSummable e N w u) hnorm
  set G := applyKernel K (truncate e N u) with hGdef
  set Q := ∑ c, W' c * q c ^ 2 with hQ
  let P : Finset (C' × (Fin 4 → ℤ)) := Finset.univ ×ˢ intCube N
  let y : C' × (Fin 4 → ℤ) → ℝ := fun r => ‖G (e' r)‖
  let d : C' × (Fin 4 → ℤ) → ℝ := fun r => ‖(cubeScale N : ℂ) * F (e' r) - G (e' r)‖
  have hxyd : ∀ r, cubeScale N * q r.1 ≤ y r + d r := by
    rintro ⟨c, n⟩
    have h := norm_le_norm_add_norm_sub' ((cubeScale N : ℂ) * F (e' (c, n))) (G (e' (c, n)))
    rwa [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le, hF] at h
  have hQP : ∑ r ∈ P, W' r.1 * (cubeScale N * q r.1) ^ 2 = Q := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun c _ => ?_
    change ∑ _n ∈ intCube N, W' c * (cubeScale N * q c) ^ 2 = _
    rw [Finset.sum_const, nsmul_eq_mul]
    calc ((intCube N).card : ℝ) * (W' c * (cubeScale N * q c) ^ 2)
        = W' c * q c ^ 2 * (((intCube N).card : ℝ) * cubeScale N ^ 2) := by ring
      _ = W' c * q c ^ 2 := by rw [card_mul_cubeScale_sq, mul_one]
  have hmain : ∑ r ∈ P, W' r.1 * (cubeScale N * q r.1) * y r ≤ Real.sqrt Q * B := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt P
      (fun r => Real.sqrt (W' r.1) * (cubeScale N * q r.1)) (fun r => Real.sqrt (W' r.1) * y r)
    have e1 : ∑ r ∈ P, (Real.sqrt (W' r.1) * (cubeScale N * q r.1)) * (Real.sqrt (W' r.1) * y r) =
        ∑ r ∈ P, W' r.1 * (cubeScale N * q r.1) * y r := by
      refine Finset.sum_congr rfl fun r _ => ?_
      have := Real.mul_self_sqrt (hW' r.1)
      calc (Real.sqrt (W' r.1) * (cubeScale N * q r.1)) * (Real.sqrt (W' r.1) * y r)
          = (Real.sqrt (W' r.1) * Real.sqrt (W' r.1)) * (cubeScale N * q r.1) * y r := by ring
        _ = W' r.1 * (cubeScale N * q r.1) * y r := by rw [this]
    have e2 : ∑ r ∈ P, (Real.sqrt (W' r.1) * (cubeScale N * q r.1)) ^ 2 = Q := by
      rw [← hQP]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [mul_pow, Real.sq_sqrt (hW' r.1)]
    have e3 : ∑ r ∈ P, (Real.sqrt (W' r.1) * y r) ^ 2 ≤ ∑' a, w' a * ‖G a‖ ^ 2 := by
      have hsumm : Summable fun a => w' a * ‖G a‖ ^ 2 := by
        refine Summable.of_abs ?_
        simpa [NormSummable] using hG
      have hterm : ∀ r ∈ P, (Real.sqrt (W' r.1) * y r) ^ 2 = w' (e' r) * ‖G (e' r)‖ ^ 2 := by
        rintro ⟨c, n⟩ _
        simp only [mul_pow, Real.sq_sqrt (hW' c), hw', y]
      rw [Finset.sum_congr rfl hterm, ← e'.tsum_eq fun a => w' a * ‖G a‖ ^ 2]
      exact ((e'.summable_iff).mpr hsumm).sum_le_tsum P
        (fun r _ => mul_nonneg (hw'0 _) (by positivity))
    rw [e1, e2] at hcs
    refine hcs.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    exact (Real.sqrt_le_sqrt e3).trans hGB
  have herr : ∑ r ∈ P, W' r.1 * (cubeScale N * q r.1) * d r ≤
      ∑ c', ∑ c, W' c' * q c' * p c * (((2 * (N : ℝ) + 1) ^ 4)⁻¹ *
        ∑ n ∈ intCube N, ∑' m, (if n + m ∈ intCube N then 0 else t c' c m)) := by
    rw [Finset.sum_product]
    refine Finset.sum_le_sum fun c' _ => ?_
    have hbound : ∀ n ∈ intCube N, W' c' * (cubeScale N * q c') * d (c', n) ≤
        ∑ c, W' c' * q c' * p c * (cubeScale N ^ 2 *
          ∑' m, (if n + m ∈ intCube N then 0 else t c' c m)) := by
      intro n _
      have hdb := norm_scale_applyKernel_sub_le e e' N K t hK hu c' n (hKu _).1 (hform _)
      rw [(hKu _).2] at hdb
      have hc : 0 ≤ W' c' * (cubeScale N * q c') :=
        mul_nonneg (hW' c') (mul_nonneg hs.le (hq c'))
      refine (mul_le_mul_of_nonneg_left hdb hc).trans (le_of_eq ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    refine (Finset.sum_le_sum hbound).trans (le_of_eq ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [cubeScale_sq, Finset.mul_sum, Finset.mul_sum]
  have hsplit : Q ≤ ∑ r ∈ P, W' r.1 * (cubeScale N * q r.1) * y r +
      ∑ r ∈ P, W' r.1 * (cubeScale N * q r.1) * d r := by
    rw [← Finset.sum_add_distrib, ← hQP]
    refine Finset.sum_le_sum fun r _ => ?_
    have hc : 0 ≤ W' r.1 * (cubeScale N * q r.1) :=
      mul_nonneg (hW' _) (mul_nonneg hs.le (hq _))
    calc W' r.1 * (cubeScale N * q r.1) ^ 2
        = W' r.1 * (cubeScale N * q r.1) * (cubeScale N * q r.1) := by ring
      _ ≤ W' r.1 * (cubeScale N * q r.1) * (y r + d r) := mul_le_mul_of_nonneg_left (hxyd r) hc
      _ = _ := by ring
  linarith
theorem sqrt_sum_le_of_product {w : A → ℝ} {w' : A' → ℝ} {W : C → ℝ} {W' : C' → ℝ}
    (hW' : ∀ c, 0 ≤ W' c) (hw : ∀ c n, w (e (c, n)) = W c) (hw' : ∀ c n, w' (e' (c, n)) = W' c)
    (hw'0 : ∀ a, 0 ≤ w' a) (K : A' → A → ℂ) (t : C' → C → (Fin 4 → ℤ) → ℝ)
    (hK : ∀ c' c n m, ‖K (e' (c', n)) (e (c, n + m))‖ = t c' c m)
    (ht : ∀ c' c, Summable (t c' c))
    {u : A → ℂ} {p : C → ℝ} (hu : ∀ c n, ‖u (e (c, n))‖ = p c)
    {F : A' → ℂ} {q : C' → ℝ} (hq : ∀ c, 0 ≤ q c) (hF : ∀ c n, ‖F (e' (c, n))‖ = q c)
    (hKu : ∀ a', ApplySummableAt K u a' ∧ applyKernel K u a' = F a') {B : ℝ}
    (hB : ∀ f, NormSummable w f → wNorm w f ≤ 1 →
      (∀ a', ApplySummableAt K f a') ∧ NormSummable w' (applyKernel K f) ∧
        wNorm w' (applyKernel K f) ≤ B)
    (hp1 : ∑ c, W c * p c ^ 2 ≤ 1) :
    Real.sqrt (∑ c, W' c * q c ^ 2) ≤ B := by
  have hB0 : 0 ≤ B := by
    have h0 : NormSummable w (0 : A → ℂ) := by simp [NormSummable]
    have h := (hB 0 h0 (by simp [wNorm])).2.2
    exact (Real.sqrt_nonneg _).trans h
  set Q := ∑ c, W' c * q c ^ 2 with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun c _ => mul_nonneg (hW' c) (by positivity)
  have hlimit : Tendsto (fun N : ℕ => Real.sqrt Q * B +
      ∑ c', ∑ c, W' c' * q c' * p c * (((2 * (N : ℝ) + 1) ^ 4)⁻¹ *
        ∑ n ∈ intCube N, ∑' m, (if n + m ∈ intCube N then 0 else t c' c m))) atTop
      (𝓝 (Real.sqrt Q * B + ∑ _c' : C', ∑ _c : C, 0)) := by
    refine tendsto_const_nhds.add (tendsto_finsetSum _ fun c' _ =>
      tendsto_finsetSum _ fun c _ => ?_)
    have h0 : ∀ m, 0 ≤ t c' c m := fun m => by
      rw [← hK c' c 0 m]
      exact norm_nonneg _
    simpa using (tendsto_boundaryMass (t c' c) h0 (ht c' c)).const_mul (W' c' * q c' * p c)
  have hle : Q ≤ Real.sqrt Q * B := by
    have h := ge_of_tendsto' hlimit fun N =>
      sum_weight_sq_le_of_intCube e e' N hW' hw hw' hw'0 K t hK hu hq hF hKu hB hp1
    simpa using h
  rcases hQ0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.sqrt_zero]
    exact hB0
  · have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hpos
    have hmul : Real.sqrt Q * Real.sqrt Q ≤ Real.sqrt Q * B := by
      rwa [Real.mul_self_sqrt hQ0]
    exact le_of_mul_le_mul_left hmul hs
end Product
variable {I I' : PeriodicData}
theorem mkQuot_translate (n : Fin 4 → ℤ) (a : I.Carrier) :
    I.mkQuot 1 (I.translate n a) = I.mkQuot 1 a :=
  (Quot.sound ⟨n, by simp⟩ : I.mkQuot 1 a = I.mkQuot 1 (I.translate n a)).symm
def rep (I : PeriodicData) (c : I.UnitQuot) : I.Carrier := Quot.out c
theorem mkQuot_rep (c : I.UnitQuot) : I.mkQuot 1 (rep I c) = c := Quot.out_eq c
def prodEquiv (hO : QuotOrbits.Claim) (hI : IsPeriodic I) :
    I.UnitQuot × (Fin 4 → ℤ) ≃ I.Carrier :=
  Equiv.ofBijective (fun r => I.translate r.2 (rep I r.1)) (by
    have h := (hO I hI).2 1 one_pos (rep I) mkQuot_rep
    simpa using h)
theorem prodEquiv_apply (hO : QuotOrbits.Claim) (hI : IsPeriodic I)
    (c : I.UnitQuot) (n : Fin 4 → ℤ) : prodEquiv hO hI (c, n) = I.translate n (rep I c) := rfl
theorem norm_exp_I_bilinDot (a b : InfiniteLattice.AmbientSpace) :
    ‖Complex.exp (Complex.I * bilinDot (toComplexVec a) (toComplexVec b))‖ = 1 := by
  have h : Complex.I * bilinDot (toComplexVec a) (toComplexVec b) =
      ((∑ μ, a μ * b μ : ℝ) : ℂ) * Complex.I := by
    simp [bilinDot, toComplexVec, mul_comm]
  rw [h, Complex.norm_exp_ofReal_mul_I]
theorem norm_blochWave (I : PeriodicData) (κ : InfiniteLattice.AmbientSpace) (φ : I.UnitQuot → ℂ)
    (ι : I.Carrier) :
    ‖blochWave I (toComplexVec κ) φ ι‖ = ‖φ (I.mkQuot 1 ι)‖ := by
  unfold blochWave
  rw [norm_mul, norm_exp_I_bilinDot, one_mul]
theorem quotWeight_nonneg (hI : IsPeriodic I)
    (hw : ∀ ι, I.quotWeight 1 (I.mkQuot 1 ι) = I.weightOf ι) (c : I.UnitQuot) :
    0 ≤ I.quotWeight 1 c := by
  have h := hw (rep I c)
  rw [mkQuot_rep] at h
  rw [h]
  exact (hI.weight_pos _).le
theorem symbolNormBound_holds (hSeries : SymbolSeriesClaim)
    (hClasses : SymbolOnQuotients.Claim)
    (hOrbits : QuotOrbits.Claim)
    (hQuotients : Quotients.QuotientTransposeNorm) : SymbolNormBound := by
  intro I I' hI hI' T hT κ
  have hT' := hT
  obtain ⟨hcov, C₀, δ, hC₀, hδ, hbound⟩ := hT'
  have hstrip : toComplexVec κ ∈ strictImStrip δ := by
    simp [strictImStrip, imVec, toComplexVec, TorusMetric.euclidNormVec, hδ]
  have hform : SymbolSummableAt I I' T (toComplexVec κ) :=
    (hSeries I I' hI hI' T δ ⟨hδ, C₀, hC₀, hbound⟩).summableOn_strip _ hstrip
  have hfacts := hClasses I I' hI hI' T hT
  obtain ⟨-, hwI, -, hacts⟩ := hQuotients I I' hI hI' 1 one_pos
  obtain ⟨-, hwI', -, -⟩ := hQuotients I' I hI' hI 1 one_pos
  have hweight := (hwI 1 (Or.inl rfl)).1.2
  have hweight' := (hwI' 1 (Or.inl rfl)).1.2
  obtain ⟨hacts1, -, hfinite⟩ := hacts T hT
  have : Finite I.UnitQuot := hI.finite_quot
  have : Finite I'.UnitQuot := hI'.finite_quot
  let _ : Fintype I.UnitQuot := Fintype.ofFinite _
  let _ : Fintype I'.UnitQuot := Fintype.ofFinite _
  have hfinite' : kernelOpNorm I I' T ≠ ∞ := hfinite.ne
  refine (iSup₂_le fun φ hφ => ?_ : wOpNorm _ _ _ _ ≤ _)
  rw [← ENNReal.ofReal_toReal hfinite', ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg]
  set ψ := applyKernel (quotSymbol I I' T (toComplexVec κ)) φ with hψ
  have hnormψ : wNorm (I'.quotWeight 1) ψ =
      Real.sqrt (∑ c, I'.quotWeight 1 c * ‖ψ c‖ ^ 2) := by
    rw [wNorm, tsum_fintype]
  have hφ1 : ∑ c, I.quotWeight 1 c * ‖φ c‖ ^ 2 ≤ 1 := by
    have h := hφ.2.2
    rw [wNorm, tsum_fintype] at h
    exact Real.sqrt_le_one.mp h
  rw [hnormψ]
  let e := prodEquiv hOrbits hI
  let e' := prodEquiv hOrbits hI'
  refine sqrt_sum_le_of_product e e' (w := I.weightOf) (w' := I'.weightOf)
    (W := I.quotWeight 1) (W' := I'.quotWeight 1)
    (quotWeight_nonneg hI' hweight') ?_ ?_ (fun a => (hI'.weight_pos _).le) T
    (fun c' c m => ‖T (rep I' c') (I.translate m (rep I c))‖) ?_ ?_
    (u := blochWave I (toComplexVec κ) φ) (p := fun c => ‖φ c‖) ?_
    (F := blochWave I' (toComplexVec κ) ψ) (q := fun c => ‖ψ c‖) (fun c => norm_nonneg _) ?_
    ?_ ?_ hφ1
  · intro c n
    rw [prodEquiv_apply, ← hweight, mkQuot_translate, mkQuot_rep]
  · intro c n
    rw [prodEquiv_apply, ← hweight', mkQuot_translate, mkQuot_rep]
  · intro c' c n m
    rw [prodEquiv_apply, prodEquiv_apply, add_comm n m, hI.translate_add, hcov]
  · intro c' c
    have h := hform (rep I' c') (rep I c)
    refine h.congr fun m => ?_
    rw [symbolSummand, norm_mul, norm_exp_I_bilinDot, mul_one]
  · intro c n
    rw [prodEquiv_apply, norm_blochWave, mkQuot_translate, mkQuot_rep]
  · intro c n
    rw [prodEquiv_apply, norm_blochWave, mkQuot_translate, mkQuot_rep]
  · intro a'
    exact hfacts.applyKernel_blochWave _ hform φ a' |> fun h => ⟨h.1, h.2⟩
  · intro f hf hf1
    obtain ⟨h1, h2⟩ := hacts1 f hf
    refine ⟨h1, h2, ?_⟩
    have hle : ENNReal.ofReal (wNorm I'.weightOf (applyKernel T f)) ≤
        kernelOpNorm I I' T :=
      le_iSup₂ (f := fun f (_ : f ∈ wUnitBall I.weightOf (normSummableSet I)) =>
        ENNReal.ofReal (wNorm I'.weightOf (applyKernel T f))) f ⟨hf, hf, hf1⟩
    exact (ENNReal.ofReal_le_iff_le_toReal hfinite').mp hle
end YangMills.Construction.PeriodicOperators.SymbolNorm
end
