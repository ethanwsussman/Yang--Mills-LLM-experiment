import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfMeansConverge
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames Set
open scoped Topology
namespace YangMills.Construction.GibbsMeans
variable {Ω : Type} [MeasurableSpace Ω] {k : ℕ} {l₀ : ℝ} {B : Set (Fin k → ℝ)} {s : Ω → ℝ}
private theorem continuousLinearMap_eq_sum_proj (L : (Fin k → ℝ) →L[ℝ] ℝ) :
    L = ∑ i, L (Pi.single i 1) • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ) := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = ∑ i, v i • (Pi.single i (1 : ℝ) : Fin k → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
private theorem continuousLinearMap_apply_eq_sum (L : (Fin k → ℝ) →L[ℝ] ℝ) (v : Fin k → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by
  conv_lhs => rw [continuousLinearMap_eq_sum_proj L]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
abbrev _root_.YangMills.SharedProofs.p81775 := @continuousLinearMap_apply_eq_sum
private theorem eventually_mem_Icc_nhdsGT (hl : 0 < l₀) : ∀ᶠ l in 𝓝[>] (0 : ℝ), l ∈ Icc 0 l₀ := by
  filter_upwards [Ioc_mem_nhdsGT hl] with l h using ⟨h.1.le, h.2⟩
private theorem abs_le_abs_mul_pow_of_le {x y C : ℝ} {m n : ℕ} (hx : 1 ≤ x) (h : |y| ≤ C * x ^ m)
    (hmn : m ≤ n) : |y| ≤ |C| * x ^ n := by
  have h1 : (0 : ℝ) ≤ x ^ m := by positivity
  calc |y| ≤ C * x ^ m := h
    _ ≤ |C| * x ^ m := mul_le_mul_of_nonneg_right (le_abs_self C) h1
    _ ≤ |C| * x ^ n := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hmn) (abs_nonneg C)
private theorem IsModerateValue.congr {H H' : ℝ → (Fin k → ℝ) → Ω → ℝ} (hl : 0 < l₀)
    (h0 : (0 : Fin k → ℝ) ∈ B) (h : IsModerateValue l₀ B s H)
    (e : ∀ l ∈ Icc 0 l₀, ∀ τ ∈ B, ∀ ω, H' l τ ω = H l τ ω) :
    IsModerateValue l₀ B s H' where
  measurable l hl' τ hτ := by
    have : H' l τ = H l τ := funext (e l hl' τ hτ)
    rw [this]
    exact h.measurable l hl' τ hτ
  abs_le_pow := by
    obtain ⟨C, m, hC⟩ := h.abs_le_pow
    exact ⟨C, m, fun l hl' τ hτ ω => by rw [e l hl' τ hτ ω]; exact hC l hl' τ hτ ω⟩
  continuousOn l hl' ω := (h.continuousOn l hl' ω).congr fun τ hτ => e l hl' τ hτ ω
  tendsto_zero ω := by
    rw [e 0 ⟨le_rfl, hl.le⟩ 0 h0 ω]
    refine (h.tendsto_zero ω).congr' ?_
    filter_upwards [eventually_mem_Icc_nhdsGT hl] with l hl'
    exact (e l hl' 0 h0 ω).symm
private theorem IsModerateValue.linComb {H K : ℝ → (Fin k → ℝ) → Ω → ℝ} (hs : ∀ ω, 1 ≤ s ω) (a b : ℝ)
    (hH : IsModerateValue l₀ B s H) (hK : IsModerateValue l₀ B s K) :
    IsModerateValue l₀ B s (fun l τ ω => a * H l τ ω + b * K l τ ω) where
  measurable l hl τ hτ :=
    ((hH.measurable l hl τ hτ).const_mul a).add ((hK.measurable l hl τ hτ).const_mul b)
  abs_le_pow := by
    obtain ⟨C, m, hC⟩ := hH.abs_le_pow
    obtain ⟨D, n, hD⟩ := hK.abs_le_pow
    refine ⟨|a| * |C| + |b| * |D|, m + n, fun l hl τ hτ ω => ?_⟩
    have e1 := abs_le_abs_mul_pow_of_le (hs ω) (hC l hl τ hτ ω) (Nat.le_add_right m n)
    have e2 := abs_le_abs_mul_pow_of_le (hs ω) (hD l hl τ hτ ω) (Nat.le_add_left n m)
    calc |a * H l τ ω + b * K l τ ω| ≤ |a| * |H l τ ω| + |b| * |K l τ ω| := by
          rw [← abs_mul, ← abs_mul]
          exact abs_add_le _ _
      _ ≤ |a| * (|C| * s ω ^ (m + n)) + |b| * (|D| * s ω ^ (m + n)) :=
          add_le_add (mul_le_mul_of_nonneg_left e1 (abs_nonneg a))
            (mul_le_mul_of_nonneg_left e2 (abs_nonneg b))
      _ = (|a| * |C| + |b| * |D|) * s ω ^ (m + n) := by ring
  continuousOn l hl ω :=
    ((hH.continuousOn l hl ω).const_smul a).add ((hK.continuousOn l hl ω).const_smul b)
  tendsto_zero ω := ((hH.tendsto_zero ω).const_mul a).add ((hK.tendsto_zero ω).const_mul b)
private theorem IsModerateValue.mul {H K : ℝ → (Fin k → ℝ) → Ω → ℝ} (hs : ∀ ω, 1 ≤ s ω)
    (hH : IsModerateValue l₀ B s H) (hK : IsModerateValue l₀ B s K) :
    IsModerateValue l₀ B s (fun l τ ω => H l τ ω * K l τ ω) where
  measurable l hl τ hτ := (hH.measurable l hl τ hτ).mul (hK.measurable l hl τ hτ)
  abs_le_pow := by
    obtain ⟨C, m, hC⟩ := hH.abs_le_pow
    obtain ⟨D, n, hD⟩ := hK.abs_le_pow
    refine ⟨|C| * |D|, m + n, fun l hl τ hτ ω => ?_⟩
    have e1 := abs_le_abs_mul_pow_of_le (hs ω) (hC l hl τ hτ ω) le_rfl
    have e2 := abs_le_abs_mul_pow_of_le (hs ω) (hD l hl τ hτ ω) le_rfl
    have p : (0 : ℝ) ≤ s ω := by linarith [hs ω]
    rw [abs_mul]
    calc |H l τ ω| * |K l τ ω| ≤ (|C| * s ω ^ m) * (|D| * s ω ^ n) :=
          mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
      _ = |C| * |D| * s ω ^ (m + n) := by rw [pow_add]; ring
  continuousOn l hl ω := (hH.continuousOn l hl ω).mul (hK.continuousOn l hl ω)
  tendsto_zero ω := (hH.tendsto_zero ω).mul (hK.tendsto_zero ω)
private theorem IsModerate.toValue :
    ∀ {n : ℕ} {H : ℝ → (Fin k → ℝ) → Ω → ℝ}, IsModerate l₀ B s n H → IsModerateValue l₀ B s H
  | 0, _, h => h
  | _ + 1, _, h => h.1
private theorem IsModerate.mono :
    ∀ (n : ℕ) {H : ℝ → (Fin k → ℝ) → Ω → ℝ}, IsModerate l₀ B s (n + 1) H → IsModerate l₀ B s n H
  | 0, _, h => h.1
  | n + 1, _, h => ⟨h.1, h.2.1, fun i => IsModerate.mono n (h.2.2 i)⟩
private theorem IsModerate.one :
    ∀ (n : ℕ) {H : ℝ → (Fin k → ℝ) → Ω → ℝ}, IsModerate l₀ B s (n + 1) H → IsModerate l₀ B s 1 H
  | 0, _, h => h
  | n + 1, _, h => IsModerate.one n (IsModerate.mono (n + 1) h)
private theorem IsModerate.congr (hl : 0 < l₀) (hB : IsOpen B) (h0 : (0 : Fin k → ℝ) ∈ B) :
    ∀ (n : ℕ) {H H' : ℝ → (Fin k → ℝ) → Ω → ℝ}, IsModerate l₀ B s n H →
      (∀ l ∈ Icc 0 l₀, ∀ τ ∈ B, ∀ ω, H' l τ ω = H l τ ω) → IsModerate l₀ B s n H'
  | 0, _, _, h, e => IsModerateValue.congr hl h0 h e
  | n + 1, H, H', h, e => by
    refine ⟨IsModerateValue.congr hl h0 h.1 e, fun l hl' τ hτ ω => ?_, fun i => ?_⟩
    · exact (h.2.1 l hl' τ hτ ω).congr_of_eventuallyEq
        (Filter.eventually_of_mem (hB.mem_nhds hτ) fun τ' hτ' => e l hl' τ' hτ' ω)
    · refine IsModerate.congr hl hB h0 n (h.2.2 i) fun l hl' τ hτ ω => ?_
      unfold partialFamily
      rw [Filter.EventuallyEq.fderiv_eq
        (Filter.eventually_of_mem (hB.mem_nhds hτ) fun τ' hτ' => e l hl' τ' hτ' ω)]
private theorem IsModerate.linComb (hs : ∀ ω, 1 ≤ s ω) (hl : 0 < l₀) (hB : IsOpen B)
    (h0 : (0 : Fin k → ℝ) ∈ B) (a b : ℝ) :
    ∀ (n : ℕ) {H K : ℝ → (Fin k → ℝ) → Ω → ℝ}, IsModerate l₀ B s n H → IsModerate l₀ B s n K →
      IsModerate l₀ B s n (fun l τ ω => a * H l τ ω + b * K l τ ω)
  | 0, _, _, hH, hK => IsModerateValue.linComb hs a b hH hK
  | n + 1, H, K, hH, hK => by
    refine ⟨IsModerateValue.linComb hs a b hH.1 hK.1, fun l hl' τ hτ ω => ?_, fun i => ?_⟩
    · exact ((hH.2.1 l hl' τ hτ ω).const_mul a).add ((hK.2.1 l hl' τ hτ ω).const_mul b)
    · refine IsModerate.congr hl hB h0 n
        (IsModerate.linComb hs hl hB h0 a b n (hH.2.2 i) (hK.2.2 i)) fun l hl' τ hτ ω => ?_
      have d : HasFDerivAt (fun τ' => a * H l τ' ω + b * K l τ' ω) _ τ :=
        ((hH.2.1 l hl' τ hτ ω).hasFDerivAt.const_mul a).add
          ((hK.2.1 l hl' τ hτ ω).hasFDerivAt.const_mul b)
      unfold partialFamily
      show fderiv ℝ (fun τ' => a * H l τ' ω + b * K l τ' ω) τ _ = _
      rw [d.fderiv]
      simp
private theorem IsModerate.mul (hs : ∀ ω, 1 ≤ s ω) (hl : 0 < l₀) (hB : IsOpen B)
    (h0 : (0 : Fin k → ℝ) ∈ B) :
    ∀ (n : ℕ) {H K : ℝ → (Fin k → ℝ) → Ω → ℝ}, IsModerate l₀ B s n H → IsModerate l₀ B s n K →
      IsModerate l₀ B s n (fun l τ ω => H l τ ω * K l τ ω)
  | 0, _, _, hH, hK => IsModerateValue.mul hs hH hK
  | n + 1, H, K, hH, hK => by
    refine ⟨IsModerateValue.mul hs hH.1 hK.1, fun l hl' τ hτ ω => ?_, fun i => ?_⟩
    · exact (hH.2.1 l hl' τ hτ ω).mul (hK.2.1 l hl' τ hτ ω)
    · have a1 := IsModerate.mul hs hl hB h0 n (hH.2.2 i) (IsModerate.mono n hK)
      have a2 := IsModerate.mul hs hl hB h0 n (IsModerate.mono n hH) (hK.2.2 i)
      refine IsModerate.congr hl hB h0 n (IsModerate.linComb hs hl hB h0 1 1 n a1 a2)
        fun l hl' τ hτ ω => ?_
      have d : HasFDerivAt (fun τ' => H l τ' ω * K l τ' ω) _ τ :=
        (hH.2.1 l hl' τ hτ ω).hasFDerivAt.mul (hK.2.1 l hl' τ hτ ω).hasFDerivAt
      unfold partialFamily
      show fderiv ℝ (fun τ' => H l τ' ω * K l τ' ω) τ _ = _
      rw [d.fderiv]
      simp
      ring
private theorem IsModerate.const (c : ℝ) :
    ∀ n : ℕ, IsModerate (Ω := Ω) l₀ B s n (fun _ _ _ => c) := by
  have hv : ∀ c : ℝ, IsModerateValue (Ω := Ω) l₀ B s (fun _ _ _ => c) := fun c =>
    { measurable := fun _ _ _ _ => measurable_const
      abs_le_pow := ⟨|c|, 0, fun _ _ _ _ _ => by simp⟩
      continuousOn := fun _ _ _ => continuousOn_const
      tendsto_zero := fun _ => tendsto_const_nhds }
  intro n
  induction n generalizing c with
  | zero => exact hv c
  | succ n ih =>
    refine ⟨hv c, fun _ _ _ _ _ => differentiableAt_const _, fun i => ?_⟩
    have e : partialFamily (fun (_ : ℝ) (_ : Fin k → ℝ) (_ : Ω) => c) i = fun _ _ _ => 0 := by
      funext l τ ω
      simp [partialFamily]
    rw [e]
    exact ih 0
private def HasConvergentValue (l₀ : ℝ) (B : Set (Fin k → ℝ)) (φ : ℝ → (Fin k → ℝ) → ℝ) : Prop :=
  (∀ l ∈ Icc 0 l₀, ContinuousOn (φ l) B) ∧
    Filter.Tendsto (fun l => φ l 0) (𝓝[>] 0) (𝓝 (φ 0 0))
private def HasConvergentDerivs (l₀ : ℝ) (B : Set (Fin k → ℝ)) :
    ℕ → (ℝ → (Fin k → ℝ) → ℝ) → Prop
  | 0, φ => HasConvergentValue l₀ B φ
  | n + 1, φ => HasConvergentValue l₀ B φ ∧ (∀ l ∈ Icc 0 l₀, ∀ τ ∈ B, DifferentiableAt ℝ (φ l) τ) ∧
      ∀ i : Fin k, HasConvergentDerivs l₀ B n fun l τ => fderiv ℝ (φ l) τ (Pi.single i 1)
private theorem HasConvergentValue.congr {φ ψ : ℝ → (Fin k → ℝ) → ℝ} (hl : 0 < l₀)
    (h0 : (0 : Fin k → ℝ) ∈ B) (h : HasConvergentValue l₀ B φ)
    (e : ∀ l ∈ Icc 0 l₀, ∀ τ ∈ B, ψ l τ = φ l τ) : HasConvergentValue l₀ B ψ := by
  refine ⟨fun l hl' => (h.1 l hl').congr fun τ hτ => e l hl' τ hτ, ?_⟩
  rw [e 0 ⟨le_rfl, hl.le⟩ 0 h0]
  refine h.2.congr' ?_
  filter_upwards [eventually_mem_Icc_nhdsGT hl] with l hl'
  exact (e l hl' 0 h0).symm
private theorem HasConvergentDerivs.congr (hl : 0 < l₀) (hB : IsOpen B) (h0 : (0 : Fin k → ℝ) ∈ B) :
    ∀ (n : ℕ) {φ ψ : ℝ → (Fin k → ℝ) → ℝ}, HasConvergentDerivs l₀ B n φ →
      (∀ l ∈ Icc 0 l₀, ∀ τ ∈ B, ψ l τ = φ l τ) → HasConvergentDerivs l₀ B n ψ
  | 0, _, _, h, e => HasConvergentValue.congr hl h0 h e
  | n + 1, φ, ψ, h, e => by
    refine ⟨HasConvergentValue.congr hl h0 h.1 e, fun l hl' τ hτ => ?_, fun i => ?_⟩
    · exact (h.2.1 l hl' τ hτ).congr_of_eventuallyEq
        (Filter.eventually_of_mem (hB.mem_nhds hτ) fun τ' hτ' => e l hl' τ' hτ')
    · refine HasConvergentDerivs.congr hl hB h0 n (h.2.2 i) fun l hl' τ hτ => ?_
      rw [Filter.EventuallyEq.fderiv_eq
        (Filter.eventually_of_mem (hB.mem_nhds hτ) fun τ' hτ' => e l hl' τ' hτ')]
private theorem HasConvergentDerivs.mono :
    ∀ (n : ℕ) {φ : ℝ → (Fin k → ℝ) → ℝ}, HasConvergentDerivs l₀ B (n + 1) φ →
      HasConvergentDerivs l₀ B n φ
  | 0, _, h => h.1
  | n + 1, _, h => ⟨h.1, h.2.1, fun i => HasConvergentDerivs.mono n (h.2.2 i)⟩
private theorem HasConvergentDerivs.add (hl : 0 < l₀) (hB : IsOpen B) (h0 : (0 : Fin k → ℝ) ∈ B) :
    ∀ (n : ℕ) {φ ψ : ℝ → (Fin k → ℝ) → ℝ}, HasConvergentDerivs l₀ B n φ →
      HasConvergentDerivs l₀ B n ψ → HasConvergentDerivs l₀ B n fun l τ => φ l τ + ψ l τ
  | 0, _, _, h, g => ⟨fun l hl' => (h.1 l hl').add (g.1 l hl'), h.2.add g.2⟩
  | n + 1, φ, ψ, h, g => by
    refine ⟨⟨fun l hl' => (h.1.1 l hl').add (g.1.1 l hl'), h.1.2.add g.1.2⟩,
      fun l hl' τ hτ => (h.2.1 l hl' τ hτ).add (g.2.1 l hl' τ hτ), fun i => ?_⟩
    refine HasConvergentDerivs.congr hl hB h0 n
      (HasConvergentDerivs.add hl hB h0 n (h.2.2 i) (g.2.2 i)) fun l hl' τ hτ => ?_
    have d : HasFDerivAt (fun τ' => φ l τ' + ψ l τ') _ τ :=
      (h.2.1 l hl' τ hτ).hasFDerivAt.add (g.2.1 l hl' τ hτ).hasFDerivAt
    show fderiv ℝ (fun τ' => φ l τ' + ψ l τ') τ _ = _
    rw [d.fderiv]
    simp
private theorem HasConvergentDerivs.mul (hl : 0 < l₀) (hB : IsOpen B) (h0 : (0 : Fin k → ℝ) ∈ B) :
    ∀ (n : ℕ) {φ ψ : ℝ → (Fin k → ℝ) → ℝ}, HasConvergentDerivs l₀ B n φ →
      HasConvergentDerivs l₀ B n ψ → HasConvergentDerivs l₀ B n fun l τ => φ l τ * ψ l τ
  | 0, _, _, h, g => ⟨fun l hl' => (h.1 l hl').mul (g.1 l hl'), h.2.mul g.2⟩
  | n + 1, φ, ψ, h, g => by
    refine ⟨⟨fun l hl' => (h.1.1 l hl').mul (g.1.1 l hl'), h.1.2.mul g.1.2⟩,
      fun l hl' τ hτ => (h.2.1 l hl' τ hτ).mul (g.2.1 l hl' τ hτ), fun i => ?_⟩
    have a1 := HasConvergentDerivs.mul hl hB h0 n (h.2.2 i) (HasConvergentDerivs.mono n g)
    have a2 := HasConvergentDerivs.mul hl hB h0 n (HasConvergentDerivs.mono n h) (g.2.2 i)
    refine HasConvergentDerivs.congr hl hB h0 n (HasConvergentDerivs.add hl hB h0 n a1 a2)
      fun l hl' τ hτ => ?_
    have d : HasFDerivAt (fun τ' => φ l τ' * ψ l τ') _ τ :=
      (h.2.1 l hl' τ hτ).hasFDerivAt.mul (g.2.1 l hl' τ hτ).hasFDerivAt
    show fderiv ℝ (fun τ' => φ l τ' * ψ l τ') τ _ = _
    rw [d.fderiv]
    simp
    ring
private theorem HasConvergentDerivs.contDiffOn (hB : IsOpen B) :
    ∀ (n : ℕ) {φ : ℝ → (Fin k → ℝ) → ℝ}, HasConvergentDerivs l₀ B n φ →
      ∀ l ∈ Icc 0 l₀, ContDiffOn ℝ n (φ l) B
  | 0, φ, h, l, hl => by
    have h' : ContDiffOn ℝ 0 (φ l) B := contDiffOn_zero.2 (h.1 l hl)
    simpa using h'
  | n + 1, φ, h, l, hl => by
    have e : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [e, contDiffOn_succ_iff_fderiv_of_isOpen hB]
    refine ⟨fun τ hτ => (h.2.1 l hl τ hτ).differentiableWithinAt, fun hn => ?_, ?_⟩
    · exact absurd hn (by simp)
    · rw [contDiffOn_clm_apply]
      intro y
      have hi := fun i => HasConvergentDerivs.contDiffOn hB n (h.2.2 i) l hl
      have hsum : ContDiffOn ℝ n
          (fun τ => ∑ i : Fin k, y i • fderiv ℝ (φ l) τ (Pi.single i 1)) B :=
        ContDiffOn.sum (s := Finset.univ) fun i _ => (hi i).const_smul (y i)
      refine hsum.congr fun τ _ => ?_
      rw [continuousLinearMap_apply_eq_sum (fderiv ℝ (φ l) τ) y]
      simp
private theorem iteratedFDeriv_fderiv_apply {f : (Fin k → ℝ) → ℝ} {n : ℕ} {τ : Fin k → ℝ}
    (hf : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f τ) (m : Fin n → Fin k → ℝ) (v : Fin k → ℝ) :
    iteratedFDeriv ℝ n (fun τ' => fderiv ℝ f τ' v) τ m = iteratedFDeriv ℝ n (fderiv ℝ f) τ m v := by
  have hg : ContDiffAt ℝ (n : WithTop ℕ∞) (fderiv ℝ f) τ :=
    hf.fderiv_right (m := (n : WithTop ℕ∞)) (by push_cast; exact le_rfl)
  have h := (ContinuousLinearMap.apply ℝ ℝ v).iteratedFDeriv_comp_left hg (i := n) le_rfl
  have h' := congrArg (fun T => T m) h
  simpa [Function.comp_def] using h'
private theorem iteratedFDeriv_succ_eq_sum {f : (Fin k → ℝ) → ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f 0) (m : Fin (n + 1) → Fin k → ℝ) :
    iteratedFDeriv ℝ (n + 1) f 0 m = ∑ i, m (Fin.last n) i *
      iteratedFDeriv ℝ n (fun τ => fderiv ℝ f τ (Pi.single i 1)) 0 (Fin.init m) := by
  rw [iteratedFDeriv_succ_apply_right, continuousLinearMap_apply_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [iteratedFDeriv_fderiv_apply hf]
private theorem HasConvergentDerivs.tendsto (hl : 0 < l₀) (hB : IsOpen B) (h0 : (0 : Fin k → ℝ) ∈ B) :
    ∀ (n : ℕ) {φ : ℝ → (Fin k → ℝ) → ℝ}, HasConvergentDerivs l₀ B n φ → ∀ m : Fin n → Fin k → ℝ,
      Filter.Tendsto (fun l => iteratedFDeriv ℝ n (φ l) 0 m) (𝓝[>] 0)
        (𝓝 (iteratedFDeriv ℝ n (φ 0) 0 m))
  | 0, φ, h, m => by
    simpa using h.2
  | n + 1, φ, h, m => by
    have hc : ∀ l ∈ Icc 0 l₀, ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (φ l) 0 := fun l hl' =>
      (HasConvergentDerivs.contDiffOn hB (n + 1) h l hl').contDiffAt (hB.mem_nhds h0)
    rw [iteratedFDeriv_succ_eq_sum (hc 0 ⟨le_rfl, hl.le⟩) m]
    have hs := tendsto_finsetSum (Finset.univ : Finset (Fin k)) fun i _ =>
      (HasConvergentDerivs.tendsto hl hB h0 n (h.2.2 i) (Fin.init m)).const_mul (m (Fin.last n) i)
    refine hs.congr' ?_
    filter_upwards [eventually_mem_Icc_nhdsGT hl] with l hl'
    exact (iteratedFDeriv_succ_eq_sum (hc l hl') m).symm
private theorem norm_mul_exp_neg_le {W A f : Ω → ℝ} {C : ℝ} {m : ℕ} (hs : ∀ ω, 1 ≤ s ω)
    (hW : ∀ ω, Real.exp (-A ω) ≤ W ω) (hb : ∀ ω, |f ω| ≤ C * s ω ^ m) (ω : Ω) :
    ‖f ω * Real.exp (-A ω)‖ ≤ |C| * (s ω ^ m * W ω) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have e1 := abs_le_abs_mul_pow_of_le (hs ω) (hb ω) le_rfl
  calc |f ω| * Real.exp (-A ω) ≤ (|C| * s ω ^ m) * W ω :=
        mul_le_mul e1 (hW ω) (Real.exp_pos _).le (le_trans (abs_nonneg _) e1)
    _ = |C| * (s ω ^ m * W ω) := by ring
variable {ν : ℝ → Measure Ω} {U H : ℝ → (Fin k → ℝ) → Ω → ℝ}
private theorem hasFDerivAt_integral_mul_exp_neg (hs : ∀ ω, 1 ≤ s ω) (hl₀ : 0 < l₀) (hB : IsOpen B)
    (h0 : (0 : Fin k → ℝ) ∈ B) (hL : AreDominatedGibbsLaws l₀ B s ν U) (hU : IsModerate l₀ B s 1 U)
    (hH : IsModerate l₀ B s 1 H) {l : ℝ} (hl : l ∈ Icc 0 l₀) {τ : Fin k → ℝ} (hτ : τ ∈ B) :
    DifferentiableAt ℝ (fun τ' => ∫ ω, H l τ' ω * Real.exp (-U l τ' ω) ∂ν l) τ ∧
    ∀ i, fderiv ℝ (fun τ' => ∫ ω, H l τ' ω * Real.exp (-U l τ' ω) ∂ν l) τ (Pi.single i 1) =
      ∫ ω, (partialFamily H i l τ ω - H l τ ω * partialFamily U i l τ ω) *
        Real.exp (-U l τ ω) ∂ν l := by
  obtain ⟨W, hW, hWi⟩ := hL.dominated l hl
  have hg : ∀ i, IsModerateValue l₀ B s
      (fun l τ ω => partialFamily H i l τ ω - H l τ ω * partialFamily U i l τ ω) := fun i => by
    have := IsModerateValue.linComb hs 1 (-1) (IsModerate.toValue (hH.2.2 i))
      (IsModerateValue.mul hs hH.1 (IsModerate.toValue (hU.2.2 i)))
    exact IsModerateValue.congr hl₀ h0 this fun l _ τ _ ω => by ring
  choose C m hC using fun i => (hg i).abs_le_pow
  have hUm : ∀ τ ∈ B, Measurable (U l τ) := fun τ hτ => hU.1.measurable l hl τ hτ
  let c : Fin k → (Fin k → ℝ) → Ω → ℝ := fun i τ ω =>
    (partialFamily H i l τ ω - H l τ ω * partialFamily U i l τ ω) * Real.exp (-U l τ ω)
  let F' : (Fin k → ℝ) → Ω → ((Fin k → ℝ) →L[ℝ] ℝ) := fun τ ω =>
    ∑ i, c i τ ω • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)
  have hcm : ∀ i, ∀ τ ∈ B, Measurable (c i τ) := fun i τ hτ =>
    ((hg i).measurable l hl τ hτ).mul (hUm τ hτ).neg.exp
  have hcb : ∀ i, ∀ τ ∈ B, ∀ ω, ‖c i τ ω‖ ≤ |C i| * (s ω ^ m i * W ω) := fun i τ hτ ω =>
    norm_mul_exp_neg_le hs (hW τ hτ) (fun ω => hC i l hl τ hτ ω) ω
  have hderiv : ∀ τ' ∈ B, ∀ ω,
      HasFDerivAt (fun τ'' => H l τ'' ω * Real.exp (-U l τ'' ω)) (F' τ' ω) τ' := by
    intro τ' hτ' ω
    have a := (hH.2.1 l hl τ' hτ' ω).hasFDerivAt
    have b := (hU.2.1 l hl τ' hτ' ω).hasFDerivAt
    refine (a.mul b.neg.exp).congr_fderiv ?_
    refine (continuousLinearMap_eq_sum_proj _).trans (Finset.sum_congr rfl fun i _ => ?_)
    congr 1
    simp [c, partialFamily]
    ring
  have hnorm : ∀ τ' ∈ B, ∀ ω, ‖F' τ' ω‖ ≤ ∑ i, |C i| * (s ω ^ m i * W ω) := by
    intro τ' hτ' ω
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    have hp : ‖(ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
        simpa using norm_le_pi_norm v i
    calc ‖c i τ' ω‖ * ‖(ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)‖ ≤ ‖c i τ' ω‖ * 1 :=
          mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ ≤ |C i| * (s ω ^ m i * W ω) := by simpa using hcb i τ' hτ' ω
  have hint : Integrable (fun ω => ∑ i, |C i| * (s ω ^ m i * W ω)) (ν l) :=
    integrable_finsetSum _ fun i _ => (hWi (m i)).const_mul _
  have hmeas : AEStronglyMeasurable (F' τ) (ν l) :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hcm i τ hτ).aestronglyMeasurable.smul_const _
  obtain ⟨CH, mH, hCH⟩ := hH.1.abs_le_pow
  have hFint : Integrable (fun ω => H l τ ω * Real.exp (-U l τ ω)) (ν l) := by
    refine Integrable.mono' ((hWi mH).const_mul |CH|)
      ((hH.1.measurable l hl τ hτ).mul (hUm τ hτ).neg.exp).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    exact norm_mul_exp_neg_le hs (hW τ hτ) (fun ω => hCH l hl τ hτ ω) ω
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := ν l)
    (F := fun τ' ω => H l τ' ω * Real.exp (-U l τ' ω)) (F' := F') (x₀ := τ)
    (bound := fun ω => ∑ i, |C i| * (s ω ^ m i * W ω)) (s := B) (hB.mem_nhds hτ)
    (Filter.eventually_of_mem (hB.mem_nhds hτ) fun τ' hτ' =>
      ((hH.1.measurable l hl τ' hτ').mul (hUm τ' hτ').neg.exp).aestronglyMeasurable)
    hFint hmeas (Filter.Eventually.of_forall fun ω τ' hτ' => hnorm τ' hτ' ω) hint
    (Filter.Eventually.of_forall fun ω τ' hτ' => hderiv τ' hτ' ω)
  refine ⟨key.differentiableAt, fun i => ?_⟩
  have hFi : Integrable (F' τ) (ν l) :=
    Integrable.mono' hint hmeas (Filter.Eventually.of_forall (hnorm τ hτ))
  rw [key.fderiv, ContinuousLinearMap.integral_apply hFi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp [F', c, Pi.single_apply]
private theorem gibbsMean_fderiv (hs : ∀ ω, 1 ≤ s ω) (hl₀ : 0 < l₀) (hB : IsOpen B)
    (h0 : (0 : Fin k → ℝ) ∈ B) (hL : AreDominatedGibbsLaws l₀ B s ν U) (hU : IsModerate l₀ B s 1 U)
    (hH : IsModerate l₀ B s 1 H) {l : ℝ} (hl : l ∈ Icc 0 l₀) {τ : Fin k → ℝ} (hτ : τ ∈ B) :
    DifferentiableAt ℝ (fun τ' => gibbsMean (ν l) (U l τ') (H l τ')) τ ∧
    ∀ i, fderiv ℝ (fun τ' => gibbsMean (ν l) (U l τ') (H l τ')) τ (Pi.single i 1) =
      gibbsMean (ν l) (U l τ)
          (fun ω => partialFamily H i l τ ω - H l τ ω * partialFamily U i l τ ω) +
        gibbsMean (ν l) (U l τ) (H l τ) * gibbsMean (ν l) (U l τ) (partialFamily U i l τ) := by
  have hN := hasFDerivAt_integral_mul_exp_neg hs hl₀ hB h0 hL hU hH hl hτ
  have hD := hasFDerivAt_integral_mul_exp_neg hs hl₀ hB h0 hL hU (H := fun _ _ _ => 1)
    (IsModerate.const 1 1) hl hτ
  simp only [one_mul] at hD
  set N : (Fin k → ℝ) → ℝ := fun τ' => ∫ ω, H l τ' ω * Real.exp (-U l τ' ω) ∂ν l with hNdef
  set D : (Fin k → ℝ) → ℝ := fun τ' => ∫ ω, Real.exp (-U l τ' ω) ∂ν l with hDdef
  have hpos : D τ ≠ 0 := (hL.integral_pos l hl τ hτ).ne'
  have hinv := (hasDerivAt_inv hpos).comp_hasFDerivAt τ hD.1.hasFDerivAt
  have hM : HasFDerivAt (fun τ' => N τ' * (Inv.inv ∘ D) τ') _ τ := hN.1.hasFDerivAt.mul hinv
  have e : (fun τ' => gibbsMean (ν l) (U l τ') (H l τ')) = fun τ' => N τ' * (Inv.inv ∘ D) τ' := by
    funext τ'
    simp [gibbsMean, N, D, div_eq_mul_inv]
  rw [e]
  refine ⟨hM.differentiableAt, fun i => ?_⟩
  rw [hM.fderiv]
  have hb : fderiv ℝ D τ (Pi.single i 1) =
      -∫ ω, partialFamily U i l τ ω * Real.exp (-U l τ ω) ∂ν l := by
    rw [hD.2 i, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [partialFamily]
  have ha := hN.2 i
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Function.comp_apply]
  rw [ha, hb]
  have w1 : gibbsMean (ν l) (U l τ)
      (fun ω => partialFamily H i l τ ω - H l τ ω * partialFamily U i l τ ω) =
      (∫ ω, (partialFamily H i l τ ω - H l τ ω * partialFamily U i l τ ω) *
        Real.exp (-U l τ ω) ∂ν l) / D τ := rfl
  have w2 : gibbsMean (ν l) (U l τ) (H l τ) = N τ / D τ := rfl
  have w3 : gibbsMean (ν l) (U l τ) (partialFamily U i l τ) =
      (∫ ω, partialFamily U i l τ ω * Real.exp (-U l τ ω) ∂ν l) / D τ := rfl
  rw [w1, w2, w3]
  generalize (∫ ω, (partialFamily H i l τ ω - H l τ ω * partialFamily U i l τ ω) *
    Real.exp (-U l τ ω) ∂ν l) = a
  generalize (∫ ω, partialFamily U i l τ ω * Real.exp (-U l τ ω) ∂ν l) = b
  generalize N τ = n at *
  generalize D τ = d at *
  field_simp
  ring
private theorem continuousOn_integral_mul_exp_neg (hs : ∀ ω, 1 ≤ s ω)
    (hL : AreDominatedGibbsLaws l₀ B s ν U) (hU : IsModerateValue l₀ B s U)
    (hH : IsModerateValue l₀ B s H) {l : ℝ} (hl : l ∈ Icc 0 l₀) :
    ContinuousOn (fun τ => ∫ ω, H l τ ω * Real.exp (-U l τ ω) ∂ν l) B := by
  obtain ⟨W, hW, hWi⟩ := hL.dominated l hl
  obtain ⟨C, m, hC⟩ := hH.abs_le_pow
  refine continuousOn_of_dominated (bound := fun ω => |C| * (s ω ^ m * W ω))
    (fun τ hτ =>
      ((hH.measurable l hl τ hτ).mul (hU.measurable l hl τ hτ).neg.exp).aestronglyMeasurable)
    (fun τ hτ =>
      Filter.Eventually.of_forall (norm_mul_exp_neg_le hs (hW τ hτ) fun ω => hC l hl τ hτ ω))
    ((hWi m).const_mul _) (Filter.Eventually.of_forall fun ω => ?_)
  exact (hH.continuousOn l hl ω).mul
    (Real.continuous_exp.comp_continuousOn (hU.continuousOn l hl ω).neg)
private theorem continuousOn_gibbsMean (hs : ∀ ω, 1 ≤ s ω) (hL : AreDominatedGibbsLaws l₀ B s ν U)
    (hU : IsModerateValue l₀ B s U) (hH : IsModerateValue l₀ B s H) {l : ℝ} (hl : l ∈ Icc 0 l₀) :
    ContinuousOn (fun τ => gibbsMean (ν l) (U l τ) (H l τ)) B := by
  have hN := continuousOn_integral_mul_exp_neg hs hL hU hH hl
  have hD := continuousOn_integral_mul_exp_neg hs hL hU (H := fun _ _ _ => 1)
    (IsModerate.toValue (IsModerate.const 1 0)) hl
  simp only [one_mul] at hD
  exact hN.div hD fun τ hτ => (hL.integral_pos l hl τ hτ).ne'
private theorem gibbsMean_hasConvergentDerivs (hs : ∀ ω, 1 ≤ s ω) (hl₀ : 0 < l₀) (hB : IsOpen B)
    (h0 : (0 : Fin k → ℝ) ∈ B) (hL : AreDominatedGibbsLaws l₀ B s ν U)
    (hlim : ∀ H' : ℝ → (Fin k → ℝ) → Ω → ℝ, IsModerateValue l₀ B s H' →
      Filter.Tendsto (fun l => gibbsMean (ν l) (U l 0) (H' l 0)) (𝓝[>] 0)
        (𝓝 (gibbsMean (ν 0) (U 0 0) (H' 0 0)))) :
    ∀ (n : ℕ) {H : ℝ → (Fin k → ℝ) → Ω → ℝ}, IsModerate l₀ B s n U → IsModerate l₀ B s n H →
      HasConvergentDerivs l₀ B n fun l τ => gibbsMean (ν l) (U l τ) (H l τ)
  | 0, H, hU, hH => ⟨fun l hl => continuousOn_gibbsMean hs hL hU hH hl, hlim H hH⟩
  | n + 1, H, hU, hH => by
    have hU1 := IsModerate.one n hU
    have hH1 := IsModerate.one n hH
    have hUn := IsModerate.mono n hU
    have hHn := IsModerate.mono n hH
    refine ⟨⟨fun l hl => continuousOn_gibbsMean hs hL hU.1 hH.1 hl, hlim H hH.1⟩,
      fun l hl τ hτ => (gibbsMean_fderiv hs hl₀ hB h0 hL hU1 hH1 hl hτ).1, fun i => ?_⟩
    have A := IsModerate.linComb hs hl₀ hB h0 1 (-1) n (hH.2.2 i)
      (IsModerate.mul hs hl₀ hB h0 n hHn (hU.2.2 i))
    have c1 := gibbsMean_hasConvergentDerivs hs hl₀ hB h0 hL hlim n hUn A
    have c2 := gibbsMean_hasConvergentDerivs hs hl₀ hB h0 hL hlim n hUn hHn
    have c3 := gibbsMean_hasConvergentDerivs hs hl₀ hB h0 hL hlim n hUn (hU.2.2 i)
    refine HasConvergentDerivs.congr hl₀ hB h0 n
      (HasConvergentDerivs.add hl₀ hB h0 n c1 (HasConvergentDerivs.mul hl₀ hB h0 n c2 c3))
      fun l hl τ hτ => ?_
    rw [(gibbsMean_fderiv hs hl₀ hB h0 hL hU1 hH1 hl hτ).2 i]
    congr 2
    funext ω
    ring
private theorem measurable_fderiv_apply_single {G : (Fin k → ℝ) → Ω → ℝ} (hB : IsOpen B)
    {τ : Fin k → ℝ} (hτ : τ ∈ B) (i : Fin k) (hm : ∀ τ' ∈ B, Measurable (G τ'))
    (hd : ∀ ω, DifferentiableAt ℝ (fun τ' => G τ' ω) τ) :
    Measurable fun ω => fderiv ℝ (fun τ' => G τ' ω) τ (Pi.single i 1) := by
  have hline : Filter.Tendsto (fun t : ℝ => τ + t • (Pi.single i (1 : ℝ) : Fin k → ℝ)) (𝓝 0)
      (𝓝 τ) := by
    have h : Continuous fun t : ℝ => τ + t • (Pi.single i (1 : ℝ) : Fin k → ℝ) := by fun_prop
    simpa using h.tendsto 0
  have hseq : Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) Filter.atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2
      ⟨tendsto_one_div_add_atTop_nhds_zero_nat.congr fun N => by simp, ?_⟩
    exact Filter.Eventually.of_forall fun N => by
      have : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      exact (inv_pos.2 this).ne'
  have hin : ∀ᶠ N : ℕ in Filter.atTop,
      τ + ((N : ℝ) + 1)⁻¹ • (Pi.single i (1 : ℝ) : Fin k → ℝ) ∈ B :=
    (hline.comp (hseq.mono_right nhdsWithin_le_nhds)).eventually (hB.mem_nhds hτ)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hin
  refine measurable_of_tendsto_metrizable
    (f := fun (N : ℕ) ω => ((((N + N₀ : ℕ) : ℝ) + 1)⁻¹)⁻¹ •
      (G (τ + (((N + N₀ : ℕ) : ℝ) + 1)⁻¹ • (Pi.single i (1 : ℝ) : Fin k → ℝ)) ω - G τ ω))
    (fun N => ((hm _ (hN₀ (N + N₀) (Nat.le_add_left _ _))).sub (hm τ hτ)).const_smul
      ((((N + N₀ : ℕ) : ℝ) + 1)⁻¹)⁻¹) ?_
  rw [tendsto_pi_nhds]
  intro ω
  have hl := (hd ω).hasFDerivAt.hasLineDerivAt (Pi.single i (1 : ℝ))
  have hs := (hasDerivAt_iff_tendsto_slope_zero.1 hl).comp
    (hseq.comp (Filter.tendsto_add_atTop_nat N₀))
  refine hs.congr fun N => ?_
  simp [Function.comp]
private theorem coordIteratedDeriv_partialFamily {G : ℝ → (Fin k → ℝ) → Ω → ℝ} {n j : ℕ}
    (hB : IsOpen B) {l : ℝ} {ω : Ω} (hG : ContDiffOn ℝ (n + 1 : ℕ) (fun τ => G l τ ω) B)
    (hj : j ≤ n) (i : Fin k) (c : Fin j → Fin k) {τ : Fin k → ℝ} (hτ : τ ∈ B) :
    coordIteratedDeriv (partialFamily G i) c l τ ω =
      coordIteratedDeriv G (Fin.snoc c i : Fin (j + 1) → Fin k) l τ ω := by
  have hf : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (fun τ => G l τ ω) τ :=
    (hG.of_le (by exact_mod_cast Nat.succ_le_succ hj)).contDiffAt (hB.mem_nhds hτ)
  unfold coordIteratedDeriv partialFamily
  rw [iteratedFDeriv_fderiv_apply hf, iteratedFDeriv_succ_apply_right]
  congr 2
  · funext q
    simp [Fin.init_snoc, Fin.init]
  · simp
private theorem isModerate_of_coordIteratedDeriv {l₀' : ℝ} (hl₀ : 0 < l₀') (hB : IsOpen B)
    (h0 : (0 : Fin k → ℝ) ∈ B) :
    ∀ (n : ℕ) (G : ℝ → (Fin k → ℝ) → Ω → ℝ), (∀ l ∈ Icc 0 l₀', ∀ τ ∈ B, Measurable (G l τ)) →
      (∀ l ∈ Icc 0 l₀', ∀ ω, ContDiffOn ℝ n (fun τ => G l τ ω) B) →
      (∃ (C : ℝ) (m : ℕ), ∀ (j : ℕ) (c : Fin j → Fin k), j ≤ n → ∀ l ∈ Icc 0 l₀', ∀ τ ∈ B, ∀ ω,
        |coordIteratedDeriv G c l τ ω| ≤ C * s ω ^ m) →
      (∀ (j : ℕ) (c : Fin j → Fin k), j ≤ n → ∀ ω,
        Filter.Tendsto (fun l => coordIteratedDeriv G c l 0 ω) (𝓝[>] 0)
          (𝓝 (coordIteratedDeriv G c 0 0 ω))) →
      IsModerate l₀' B s n G := by
  have value : ∀ (n : ℕ) (G : ℝ → (Fin k → ℝ) → Ω → ℝ),
      (∀ l ∈ Icc 0 l₀', ∀ τ ∈ B, Measurable (G l τ)) →
      (∀ l ∈ Icc 0 l₀', ∀ ω, ContDiffOn ℝ n (fun τ => G l τ ω) B) →
      (∃ (C : ℝ) (m : ℕ), ∀ (j : ℕ) (c : Fin j → Fin k), j ≤ n → ∀ l ∈ Icc 0 l₀', ∀ τ ∈ B, ∀ ω,
        |coordIteratedDeriv G c l τ ω| ≤ C * s ω ^ m) →
      (∀ (j : ℕ) (c : Fin j → Fin k), j ≤ n → ∀ ω,
        Filter.Tendsto (fun l => coordIteratedDeriv G c l 0 ω) (𝓝[>] 0)
          (𝓝 (coordIteratedDeriv G c 0 0 ω))) →
      IsModerateValue l₀' B s G := by
    intro n G hm hc hb hl
    have e : ∀ l τ ω, coordIteratedDeriv G (Fin.elim0 : Fin 0 → Fin k) l τ ω = G l τ ω := by
      intro l τ ω
      simp [coordIteratedDeriv]
    refine ⟨hm, ?_, fun l hl' ω => (hc l hl' ω).continuousOn, fun ω => ?_⟩
    · obtain ⟨C, m, h⟩ := hb
      exact ⟨C, m, fun l hl' τ hτ ω => by
        have := h 0 Fin.elim0 (Nat.zero_le n) l hl' τ hτ ω
        rwa [e] at this⟩
    · have := hl 0 Fin.elim0 (Nat.zero_le n) ω
      simpa only [e] using this
  intro n
  induction n with
  | zero => exact fun G hm hc hb hl => value 0 G hm hc hb hl
  | succ n ih =>
    intro G hm hc hb hl
    have hdiff : ∀ l ∈ Icc 0 l₀', ∀ τ ∈ B, ∀ ω, DifferentiableAt ℝ (fun τ' => G l τ' ω) τ :=
      fun l hl' τ hτ ω => ((hc l hl' ω).contDiffAt (hB.mem_nhds hτ)).differentiableAt (by simp)
    refine ⟨value (n + 1) G hm hc hb hl, hdiff, fun i => ih _ ?_ ?_ ?_ ?_⟩
    · intro l hl' τ hτ
      exact measurable_fderiv_apply_single hB hτ i (hm l hl') (hdiff l hl' τ hτ)
    · intro l hl' ω
      have e : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
      have h := hc l hl' ω
      rw [e, contDiffOn_succ_iff_fderiv_of_isOpen hB] at h
      exact h.2.2.clm_apply contDiffOn_const
    · obtain ⟨C, m, h⟩ := hb
      refine ⟨C, m, fun j c hj l hl' τ hτ ω => ?_⟩
      rw [coordIteratedDeriv_partialFamily hB (hc l hl' ω) hj i c hτ]
      exact h (j + 1) _ (Nat.succ_le_succ hj) l hl' τ hτ ω
    · intro j c hj ω
      rw [coordIteratedDeriv_partialFamily hB (hc 0 ⟨le_rfl, hl₀.le⟩ ω) hj i c h0]
      refine (hl (j + 1) (Fin.snoc c i : Fin (j + 1) → Fin k) (Nat.succ_le_succ hj) ω).congr' ?_
      filter_upwards [eventually_mem_Icc_nhdsGT hl₀] with l hl'
      exact (coordIteratedDeriv_partialFamily hB (hc l hl' ω) hj i c h0).symm
theorem gibbsMeanDerivativesConverge : GibbsMeanDerivativesConverge := by
  refine ⟨?_, ?_, ?_⟩
  · intro Ω _ k n l₀ B s ν U H hl₀ hB h0 hs hL hU hH hlim
    have h := gibbsMean_hasConvergentDerivs hs hl₀ hB h0 hL hlim n hU hH
    exact ⟨HasConvergentDerivs.contDiffOn hB n h, HasConvergentDerivs.tendsto hl₀ hB h0 n h⟩
  · intro Ω _ k n l₀ B s a b H K hl₀ hB h0 hs hH hK
    exact IsModerate.linComb hs hl₀ hB h0 a b n hH hK
  · intro Ω _ k n l₀ B s G hl₀ hB h0 hm hc hb hl
    exact isModerate_of_coordIteratedDeriv hl₀ hB h0 n G hm hc hb hl
end YangMills.Construction.GibbsMeans
end
