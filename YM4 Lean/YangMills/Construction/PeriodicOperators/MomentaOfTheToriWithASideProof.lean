import YangMills.Construction.PeriodicOperators.MomentaOfTheToriWithASide
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators
open InfiniteLattice (AmbientSpace)
namespace DualLatticeDensity
theorem mem_dualLattice {s : ℕ} {x : AmbientSpace} :
    x ∈ dualLattice s ↔ ∃ k : Fin 4 → ℤ, ∀ μ, x μ = (k μ : ℝ) * (2 * Real.pi / s) :=
  Iff.rfl
theorem dualLattice_mono {L n₀ n : ℕ} (hL : 0 < L) (h : n₀ ≤ n) :
    (dualLattice (2 * L ^ n₀) : Set AmbientSpace) ⊆ dualLattice (2 * L ^ n) := by
  intro x hx
  obtain ⟨k, hk⟩ := mem_dualLattice.1 hx
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  refine mem_dualLattice.2 ⟨fun μ => k μ * (L : ℤ) ^ d, fun μ => ?_⟩
  rw [hk μ]
  push_cast
  field_simp
  ring
theorem dense_iUnion_dualLattice {L : ℕ} (hL : 2 ≤ L) :
    Dense (⋃ (n : ℕ) (_ : 1 ≤ n), (dualLattice (2 * L ^ n) : Set AmbientSpace)) := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨m, hm⟩ := exists_nat_gt (Real.pi / r)
  have hm0 : (0 : ℝ) < m := lt_trans (div_pos Real.pi_pos hr) hm
  have hm1 : 1 ≤ m := by
    have : 0 < m := by exact_mod_cast hm0
    omega
  have hpow : (m : ℝ) < (L : ℝ) ^ m := by
    exact_mod_cast Nat.lt_pow_self (by omega : 1 < L)
  have hLpos : (0 : ℝ) < (L : ℝ) ^ m := lt_trans hm0 hpow
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * Real.pi / ((2 * L ^ m : ℕ) : ℝ) := ⟨_, rfl⟩
  have hae : a = Real.pi / (L : ℝ) ^ m := by
    rw [ha]
    push_cast
    field_simp
  have ha0 : 0 < a := by
    rw [hae]
    exact div_pos Real.pi_pos hLpos
  have har : a < r := by
    rw [hae, div_lt_iff₀ hLpos]
    have h1 : Real.pi < m * r := (div_lt_iff₀ hr).1 hm
    nlinarith
  refine ⟨fun μ => (⌊x μ / a⌋ : ℝ) * a, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_pi_lt_iff hr]
    intro μ
    have h1 : (⌊x μ / a⌋ : ℝ) * a ≤ x μ := by
      calc (⌊x μ / a⌋ : ℝ) * a ≤ x μ / a * a :=
            mul_le_mul_of_nonneg_right (Int.floor_le _) ha0.le
        _ = x μ := div_mul_cancel₀ _ ha0.ne'
    have h2 : x μ < ((⌊x μ / a⌋ : ℝ) + 1) * a := by
      calc x μ = x μ / a * a := (div_mul_cancel₀ _ ha0.ne').symm
        _ < ((⌊x μ / a⌋ : ℝ) + 1) * a :=
            mul_lt_mul_of_pos_right (Int.lt_floor_add_one _) ha0
    rw [Real.dist_eq, abs_lt]
    constructor <;> nlinarith
  · refine Set.mem_iUnion₂.2 ⟨m, hm1, mem_dualLattice.2 ⟨fun μ => ⌊x μ / a⌋, fun μ => ?_⟩⟩
    rw [← ha]
theorem eq_zero_of_eq_zero_on_reals {δ : ℝ} (hδ : 0 ≤ δ) {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, |z.im| ≤ δ → ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f w)
    (h0 : ∀ t : ℝ, f t = 0) {z : ℂ} (hz : |z.im| ≤ δ) : f z = 0 := by
  have hA : AnalyticOnNhd ℂ f {w : ℂ | |w.im| ≤ δ} := fun w hw =>
    Complex.analyticAt_iff_eventually_differentiableAt.2 (hf w hw)
  have hconv : Convex ℝ {w : ℂ | |w.im| ≤ δ} := by
    have he : {w : ℂ | |w.im| ≤ δ} = Complex.imLm ⁻¹' Set.Icc (-δ) δ := by
      ext w
      simp [abs_le]
    rw [he]
    exact (convex_Icc _ _).linear_preimage _
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), f w = 0 :=
    ht.frequently (Eventually.frequently (Eventually.of_forall h0))
  have hmem : (0 : ℂ) ∈ {w : ℂ | |w.im| ≤ δ} := by simpa using hδ
  simpa using
    hA.eqOn_zero_of_preconnected_of_frequently_eq_zero hconv.isPreconnected hmem hfreq hz
theorem update_mem_imStrip {δ : ℝ} {κ : Fin 4 → ℂ} (hκ : κ ∈ imStrip δ) (i : Fin 4) {z : ℂ}
    (hz : |z.im| ≤ δ) : Function.update κ i z ∈ imStrip δ := by
  intro μ
  by_cases h : μ = i
  · subst h
    simpa using hz
  · simpa [Function.update_of_ne h] using hκ μ
theorem update_eq_update_add_smul (κ : Fin 4 → ℂ) (i : Fin 4) (z w : ℂ) :
    Function.update κ i w =
      Function.update κ i z + (w - z) • Coordinates.ComplexCoordinates.stdBasisVector i := by
  funext μ
  by_cases h : μ = i
  · subst h
    simp [Coordinates.ComplexCoordinates.stdBasisVector]
  · simp [Coordinates.ComplexCoordinates.stdBasisVector, Function.update_of_ne h,
      Pi.single_eq_of_ne h]
theorem eq_zero_on_imStrip {δ : ℝ} (hδ : 0 ≤ δ) {G : (Fin 4 → ℂ) → ℂ}
    {O : Set (Coordinates.ComplexCoordinates 4)} (hsub : imStrip δ ⊆ O)
    (hG : Coordinates.ComplexCoordinates.IsHolomorphicIn O
      fun (z : Coordinates.ComplexCoordinates 4) (_ : Fin 1) => G z)
    (hreal : ∀ y, G (toComplexVec y) = 0) : ∀ κ ∈ imStrip δ, G κ = 0 := by
  have hline : ∀ κ ∈ imStrip δ, ∀ i : Fin 4, ∀ z : ℂ, |z.im| ≤ δ →
      ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (fun w : ℂ => G (Function.update κ i w)) w := by
    intro κ hκ i z hz
    have h1 := hG.2.2 _ (hsub (update_mem_imStrip hκ i hz)) i
    have htend : Tendsto (fun w : ℂ => w - z) (𝓝 z) (𝓝 0) := by
      have hc : Continuous fun w : ℂ => w - z := by fun_prop
      simpa using hc.tendsto z
    filter_upwards [htend.eventually h1] with w hw
    have h2 := differentiableAt_pi.1 hw 0
    have h3 := DifferentiableAt.comp w h2 (differentiableAt_id.sub_const z)
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
    show G (Function.update κ i u) = G _
    rw [update_eq_update_add_smul κ i z u]
    rfl
  have hall : ∀ S : Finset (Fin 4), ∀ κ ∈ imStrip δ, (∀ μ, μ ∉ S → (κ μ).im = 0) → G κ = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro κ _ him
      have : κ = toComplexVec fun μ => (κ μ).re := by
        funext μ
        apply Complex.ext
        · simp [toComplexVec]
        · simpa [toComplexVec] using him μ (by simp)
      rw [this]
      exact hreal _
    | insert i S _ ih =>
      intro κ hκ him
      have hval := eq_zero_of_eq_zero_on_reals hδ (hline κ hκ i)
        (fun t => ih _ (update_mem_imStrip hκ i (by simpa using hδ)) (fun μ hμ => by
          by_cases h : μ = i
          · subst h
            simp
          · simpa [Function.update_of_ne h] using
              him μ (by simp [Finset.mem_insert, h, hμ]))) (hκ i)
      simpa using hval
  intro κ hκ
  exact hall Finset.univ κ hκ (fun μ hμ => absurd (Finset.mem_univ μ) hμ)
end DualLatticeDensity
theorem DualLatticeDensity.claim_holds : DualLatticeDensity.Claim := by
  intro L hL
  have hL13 : 13 ≤ L := hL.2
  have hsub : ∀ n₀ n : ℕ, n₀ ≤ n →
      (dualLattice (2 * L ^ n₀) : Set AmbientSpace) ⊆ dualLattice (2 * L ^ n) :=
    fun n₀ n h => DualLatticeDensity.dualLattice_mono (by omega) h
  have hdense := DualLatticeDensity.dense_iUnion_dualLattice (L := L) (by omega)
  refine ⟨fun n₀ n _ h => hsub n₀ n h, hdense, ?_⟩
  intro g n₁ ε hg _ _ hε hbound
  have hzero : ∀ y, g y = 0 := by
    have hon : Set.EqOn g (fun _ => 0)
        (⋃ (n : ℕ) (_ : 1 ≤ n), (dualLattice (2 * L ^ n) : Set AmbientSpace)) := by
      intro p hp
      obtain ⟨m, _, hpm⟩ := Set.mem_iUnion₂.1 hp
      have hle : ‖g p‖ ≤ 0 :=
        ge_of_tendsto hε (eventually_atTop.2 ⟨max m n₁, fun n hn =>
          hbound n (le_trans (le_max_right _ _) hn) p
            (hsub m n (le_trans (le_max_left _ _) hn) hpm)⟩)
      exact norm_le_zero_iff.1 hle
    exact fun y => congrFun (Continuous.ext_on hdense hg continuous_const hon) y
  refine ⟨hzero, ?_⟩
  rintro δ G hδ ⟨O, hO, hhol⟩ hGg
  exact DualLatticeDensity.eq_zero_on_imStrip hδ.le hO hhol
    (fun y => (hGg y).trans (hzero y))
end YangMills.Construction.PeriodicOperators
end
