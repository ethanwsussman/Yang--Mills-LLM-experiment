import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Thresholds
def degreeZero (A₀ : ℝ) (𝔭₀ : ℕ) (g' : ℝ) : ℝ :=
  A₀ * Real.log (g' ^ (-2 : ℤ)) ^ 𝔭₀
def degreeOne (𝔭₁ : ℝ) (g' : ℝ) : ℝ :=
  Real.log (g' ^ (-2 : ℤ)) ^ 𝔭₁
def couplingAt (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  x k ^ (-(1 / 2) : ℝ)
def epsThreshold (A₀ : ℝ) (𝔭₀ : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  couplingAt x k * degreeZero A₀ 𝔭₀ (couplingAt x k)
def deltaThreshold (A₀ A₁ : ℝ) (𝔭₀ : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  (A₁ / A₀) * epsThreshold A₀ 𝔭₀ x k
def deltaPrimeThreshold (A₁ 𝔭₁ : ℝ) (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  couplingAt x k * A₁ * degreeOne 𝔭₁ (couplingAt x k)
def deltaFlatThreshold (A₀ A₁ Θ₁ : ℝ) (𝔭₀ : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  deltaThreshold A₀ A₁ 𝔭₀ x k / (4 * Θ₁)
def couplingRadius (C : Fin 2 → ℝ) (q : ℕ) (x : ℕ → ℝ) (i : Fin 2) (k : ℕ) : ℝ :=
  couplingAt x k * C i * Real.log (x k) ^ q
def blockSizeCandidates (L r : ℕ) (y : ℝ) : Set ℕ :=
  {n | ∃ b : ℕ, n = L ^ b ∧ Real.log y ^ r ≤ (n : ℝ)}
def blockSize (L r : ℕ) (y : ℝ) : ℕ :=
  sInf (blockSizeCandidates L r y)
def runningMinCoupling (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one x
def minBlockSize (L r : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℕ :=
  blockSize L r (runningMinCoupling x k)
def delayDepth (L r : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℕ :=
  minBlockSize L r x k
def delayCandidates (L r : ℕ) (x : ℕ → ℝ) (k : ℕ) : Set ℕ :=
  {N | 1 ≤ N ∧ N ≤ k + 1 ∧ L ^ (N - 1) = minBlockSize L r x (k + 1 - N)}
def DelayDefined (L r : ℕ) (x : ℕ → ℝ) (k : ℕ) : Prop :=
  (delayCandidates L r x k).Nonempty
def minDelay (L r : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℕ :=
  sInf (delayCandidates L r x k)
def delayLevel (L r : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℤ :=
  (k : ℤ) - (minDelay L r x k : ℤ)
theorem blockSizeCandidates_nonempty {L : ℕ} (hL : 2 ≤ L) (r : ℕ) (y : ℝ) :
    (blockSizeCandidates L r y).Nonempty := by
  have hL1 : (1 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 1 < L)
  obtain ⟨b, hb⟩ := pow_unbounded_of_one_lt (Real.log y ^ r) hL1
  exact ⟨L ^ b, b, rfl, by push_cast; exact hb.le⟩
theorem blockSize_eq_pow {L : ℕ} (hL : 2 ≤ L) (r : ℕ) (y : ℝ) :
    ∃ b : ℕ, blockSize L r y = L ^ b := by
  obtain ⟨b, hb, -⟩ := Nat.sInf_mem (blockSizeCandidates_nonempty hL r y)
  exact ⟨b, hb⟩
theorem minBlockSize_eq_pow {L : ℕ} (hL : 2 ≤ L) (r : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    ∃ b : ℕ, minBlockSize L r x k = L ^ b :=
  blockSize_eq_pow hL r _
theorem one_le_minBlockSize {L : ℕ} (hL : 2 ≤ L) (r : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    1 ≤ minBlockSize L r x k := by
  obtain ⟨b, hb⟩ := minBlockSize_eq_pow hL r x k
  rw [hb]
  exact Nat.one_le_pow _ _ (by omega)
theorem one_lt_runningMinCoupling {x : ℕ → ℝ} {k : ℕ} (hx : ∀ i ≤ k, 1 < x i) :
    1 < runningMinCoupling x k := by
  refine (Finset.lt_inf'_iff _).2 fun i hi => hx i ?_
  have := Finset.mem_range.1 hi
  omega
theorem runningMinCoupling_antitone (x : ℕ → ℝ) {i j : ℕ} (hij : i ≤ j) :
    runningMinCoupling x j ≤ runningMinCoupling x i := by
  refine Finset.inf'_mono x (fun n hn => ?_) _
  have := Finset.mem_range.1 hn
  exact Finset.mem_range.2 (by omega)
theorem minBlockSize_antitone {L : ℕ} (hL : 2 ≤ L) (r : ℕ) {x : ℕ → ℝ} {i j : ℕ} (hij : i ≤ j)
    (hx : ∀ n ≤ j, 1 < x n) : minBlockSize L r x j ≤ minBlockSize L r x i := by
  have hj : 1 < runningMinCoupling x j := one_lt_runningMinCoupling hx
  have hji : runningMinCoupling x j ≤ runningMinCoupling x i := runningMinCoupling_antitone x hij
  obtain ⟨b, hpow, hb⟩ := Nat.sInf_mem (blockSizeCandidates_nonempty hL r (runningMinCoupling x i))
  show sInf (blockSizeCandidates L r (runningMinCoupling x j)) ≤
    sInf (blockSizeCandidates L r (runningMinCoupling x i))
  refine Nat.sInf_le ⟨b, hpow, le_trans ?_ hb⟩
  exact pow_le_pow_left₀ (Real.log_nonneg hj.le)
    (Real.log_le_log (by linarith) hji) r
end YangMills.Construction.Thresholds
