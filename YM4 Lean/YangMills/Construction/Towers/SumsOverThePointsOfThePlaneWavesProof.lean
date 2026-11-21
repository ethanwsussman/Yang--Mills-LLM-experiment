import YangMills.Construction.Towers.SumsOverThePointsOfThePlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace PlaneWaveSums
open PlaneWaves
theorem sum_Icc_symm_eq_sum_range {β : Type*} [AddCommMonoid β] (M : ℕ) (f : ℤ → β) :
    ∑ j ∈ Finset.Icc (-(M : ℤ)) M, f j = ∑ a ∈ Finset.range (2 * M + 1), f ((a : ℤ) - M) := by
  symm
  apply Finset.sum_bij (fun (a : ℕ) _ => (a : ℤ) - M)
  · intro a ha
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Icc]
    omega
  · intro a _ b _ h
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    exact ⟨(j + M).toNat, by simp only [Finset.mem_range]; omega, by omega⟩
  · intro a _
    rfl
theorem card_Icc_neg_self (M : ℕ) : (Finset.Icc (-(M : ℤ)) M).card = 2 * M + 1 := by
  rw [Int.card_Icc]
  omega
theorem sum_exp_int_mul_div_eq_zero (M N : ℕ) (hN : N = 2 * M + 1) (n : ℤ) (hn : n ≠ 0)
    (hlt : |n| < N) :
    ∑ m ∈ Finset.Icc (-(M : ℤ)) M,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (m : ℂ) / (N : ℂ)) = 0 := by
  have hN0 : (N : ℂ) ≠ 0 := by
    rw [hN]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  have h2 : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero]
  obtain ⟨ω, hω⟩ : ∃ ω, ω = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (N : ℂ)) :=
    ⟨_, rfl⟩
  have hω1 : ω ≠ 1 := by
    intro h
    rw [hω] at h
    obtain ⟨c, hc⟩ := Complex.exp_eq_one_iff.mp h
    rw [div_eq_iff hN0] at hc
    have e₁ : (n : ℂ) = ((c * (N : ℤ) : ℤ) : ℂ) := by
      apply mul_left_cancel₀ h2
      push_cast
      linear_combination hc
    have e₂ : n = c * (N : ℤ) := by exact_mod_cast e₁
    exact hn (Int.eq_zero_of_abs_lt_dvd ⟨c, by rw [e₂, mul_comm]⟩ hlt)
  have hωN : ω ^ N = 1 := by
    rw [hω, ← Complex.exp_nat_mul]
    refine Complex.exp_eq_one_iff.mpr ⟨n, ?_⟩
    field_simp
  have hω0 : ω ≠ 0 := by
    rw [hω]
    exact Complex.exp_ne_zero _
  have hterm : ∀ m : ℤ,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (m : ℂ) / (N : ℂ)) = ω ^ m := by
    intro m
    rw [hω, ← Complex.exp_int_mul]
    congr 1
    ring
  have hshift : ∀ a : ℕ, ω ^ ((a : ℤ) - (M : ℤ)) = ω ^ a * (ω ^ M)⁻¹ := by
    intro a
    rw [zpow_sub₀ hω0, zpow_natCast, zpow_natCast, div_eq_mul_inv]
  rw [sum_Icc_symm_eq_sum_range, ← hN]
  simp only [hterm, hshift]
  rw [← Finset.sum_mul, geom_sum_eq hω1, hωN]
  simp
theorem finestMesh_eq_and_freqWindow_eq (L k : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L) :
    ∃ M : ℕ, finestMesh L k = ((2 * M + 1 : ℕ) : ℝ)⁻¹ ∧
      freqWindow L k = Finset.Icc (-(M : ℤ)) M := by
  obtain ⟨M, hM⟩ : Odd (L ^ k) := hL.1.pow
  have hs : finestMesh L k = ((2 * M + 1 : ℕ) : ℝ)⁻¹ := by
    rw [finestMesh, meshAt, ← hM]
    push_cast
    rw [zero_sub, zpow_neg, zpow_natCast]
  refine ⟨M, hs, ?_⟩
  have hf : ⌊1 / 2 * ((finestMesh L k)⁻¹ - 1)⌋ = (M : ℤ) := by
    have e : 1 / 2 * ((finestMesh L k)⁻¹ - 1) = ((M : ℤ) : ℝ) := by
      rw [hs, inv_inv]
      push_cast
      ring
    rw [e, Int.floor_intCast]
  rw [freqWindow, hf]
theorem conj_dirichletSum_ofReal (L k M : ℕ) (hr : freqWindow L k = Finset.Icc (-(M : ℤ)) M)
    (t : ℝ) : (starRingEnd ℂ) (dirichletSum L k (t : ℂ)) = dirichletSum L k (t : ℂ) := by
  rw [dirichletSum, hr, map_mul, map_sum, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_nbij' (fun j => -j) (fun j => -j) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j _
    simp
  · intro j _
    simp
  · intro j _
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]
    push_cast
    ring
theorem norm_dirichletSum_ofReal_le (L k M : ℕ) (hs : finestMesh L k = ((2 * M + 1 : ℕ) : ℝ)⁻¹)
    (hr : freqWindow L k = Finset.Icc (-(M : ℤ)) M) (t : ℝ) :
    ‖dirichletSum L k (t : ℂ)‖ ≤ 1 := by
  have hpos : (0 : ℝ) < ((2 * M + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
  have hterm : ∀ j ∈ Finset.Icc (-(M : ℤ)) M,
      ‖Complex.exp (Complex.I * ((finestMesh L k : ℝ) : ℂ) * (j : ℂ) * (t : ℂ))‖ ≤ 1 := by
    intro j _
    have e : Complex.I * ((finestMesh L k : ℝ) : ℂ) * (j : ℂ) * (t : ℂ) =
        ((finestMesh L k * j * t : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e, Complex.norm_exp_ofReal_mul_I]
  have hsum := norm_sum_le_of_le (Finset.Icc (-(M : ℤ)) M) hterm
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_Icc_neg_self] at hsum
  rw [dirichletSum, hr, norm_mul, Complex.norm_real, hs,
    Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  calc _ ≤ ((2 * M + 1 : ℕ) : ℝ)⁻¹ * ((2 * M + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by rw [← hs]; exact hsum) (inv_nonneg.mpr hpos.le)
    _ = 1 := inv_mul_cancel₀ hpos.ne'
theorem sum_dirichletSum_shift_sq (L k M : ℕ) (hs : finestMesh L k = ((2 * M + 1 : ℕ) : ℝ)⁻¹)
    (hr : freqWindow L k = Finset.Icc (-(M : ℤ)) M) (t : ℝ) :
    ∑ m ∈ freqWindow L k,
      dirichletSum L k ((t : ℂ) + 2 * (Real.pi : ℂ) * (m : ℂ)) ^ 2 = 1 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 2 * M + 1 := ⟨_, rfl⟩
  have hNc : (N : ℂ) ≠ 0 := by
    rw [hN]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  obtain ⟨e, he⟩ : ∃ e : ℂ, e = ((finestMesh L k : ℝ) : ℂ) := ⟨_, rfl⟩
  have heN : e = (N : ℂ)⁻¹ := by
    rw [he, hs, ← hN]
    push_cast
    rfl
  obtain ⟨E, hE⟩ : ∃ E : ℤ → ℂ, E = fun j : ℤ => Complex.exp (Complex.I * e * (j : ℂ) * (t : ℂ)) :=
    ⟨_, rfl⟩
  have hexp : ∀ j m : ℤ,
      Complex.exp (Complex.I * e * (j : ℂ) * ((t : ℂ) + 2 * (Real.pi : ℂ) * (m : ℂ))) =
        E j * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (m : ℂ) / (N : ℂ)) := by
    intro j m
    rw [hE]
    simp only
    rw [← Complex.exp_add]
    congr 1
    rw [heN]
    field_simp
  have hsq : ∀ m : ℤ, dirichletSum L k ((t : ℂ) + 2 * (Real.pi : ℂ) * (m : ℂ)) ^ 2 =
      e ^ 2 * ∑ j ∈ Finset.Icc (-(M : ℤ)) M, ∑ j' ∈ Finset.Icc (-(M : ℤ)) M, E j * E j' *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j + j' : ℤ) : ℂ) * (m : ℂ) / (N : ℂ)) := by
    intro m
    rw [dirichletSum, hr, ← he]
    simp only [hexp]
    rw [mul_pow, sq (∑ j ∈ Finset.Icc (-(M : ℤ)) M, _), Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    have e₁ : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j + j' : ℤ) : ℂ) * (m : ℂ) / (N : ℂ)) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (m : ℂ) / (N : ℂ)) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j' : ℂ) * (m : ℂ) / (N : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e₁]
    ring
  have hEE : ∀ j : ℤ, E j * E (-j) = 1 := by
    intro j
    rw [hE]
    simp only
    rw [← Complex.exp_add]
    have e₁ : Complex.I * e * (j : ℂ) * (t : ℂ) + Complex.I * e * ((-j : ℤ) : ℂ) * (t : ℂ) = 0 := by
      push_cast
      ring
    rw [e₁, Complex.exp_zero]
  have hcard : ((Finset.Icc (-(M : ℤ)) M).card : ℂ) = (N : ℂ) := by
    rw [card_Icc_neg_self, hN]
  have hinner : ∀ j ∈ Finset.Icc (-(M : ℤ)) M,
      ∑ m ∈ Finset.Icc (-(M : ℤ)) M, ∑ j' ∈ Finset.Icc (-(M : ℤ)) M, E j * E j' *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j + j' : ℤ) : ℂ) * (m : ℂ) / (N : ℂ)) =
        (N : ℂ) := by
    intro j hj
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    rw [Finset.sum_eq_single (-j)]
    · rw [hEE, one_mul, add_neg_cancel]
      simp only [Int.cast_zero, mul_zero, zero_mul, zero_div, Complex.exp_zero, Finset.sum_const,
        nsmul_eq_mul, mul_one]
      exact hcard
    · intro j' hj' hne
      have hne' : j + j' ≠ 0 := fun h => hne (by omega)
      have hlt : |j + j'| < (N : ℤ) := by
        simp only [Finset.mem_Icc] at hj hj'
        rw [abs_lt, hN]
        push_cast
        omega
      rw [sum_exp_int_mul_div_eq_zero M N hN (j + j') hne' hlt, mul_zero]
    · intro h
      exfalso
      apply h
      simp only [Finset.mem_Icc] at hj ⊢
      omega
  rw [hr]
  simp only [hsq]
  rw [← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl hinner, Finset.sum_const,
    nsmul_eq_mul, hcard, heN]
  field_simp
theorem ofReal_norm_sq_of_conj_eq {z : ℂ} (h : (starRingEnd ℂ) z = z) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) = z ^ 2 := by
  obtain ⟨r, rfl⟩ := Complex.conj_eq_iff_real.mp h
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  push_cast
  rfl
theorem claim_holds : Claim := by
  intro L hL k _ ϰ
  obtain ⟨M, hs, hr⟩ := finestMesh_eq_and_freqWindow_eq L k hL
  have hcast : ∀ (m : Fin 4 → ℤ) (ν : Fin 4),
      shiftedFreq (fun ν => (ϰ ν : ℂ)) m ν = ((ϰ ν + 2 * Real.pi * (m ν : ℝ) : ℝ) : ℂ) := by
    intro m ν
    simp only [shiftedFreq]
    push_cast
    rfl
  have hv : ∑ m ∈ freqBox L k,
      PlaneWaves.vertexWeight L k (shiftedFreq (fun ν => (ϰ ν : ℂ)) m) ^ 2 = 1 := by
    have e₁ : ∀ m : Fin 4 → ℤ,
        PlaneWaves.vertexWeight L k (shiftedFreq (fun ν => (ϰ ν : ℂ)) m) ^ 2 =
          ∏ ν, dirichletSum L k ((ϰ ν : ℂ) + 2 * (Real.pi : ℂ) * (m ν : ℂ)) ^ 2 := by
      intro m
      rw [PlaneWaves.vertexWeight, ← Finset.prod_pow]
      rfl
    simp only [e₁, freqBox]
    rw [← Finset.prod_univ_sum (fun _ : Fin 4 => freqWindow L k)
      (fun ν j => dirichletSum L k ((ϰ ν : ℂ) + 2 * (Real.pi : ℂ) * (j : ℂ)) ^ 2)]
    simp only [sum_dirichletSum_shift_sq L k M hs hr]
    simp
  have hconj : ∀ m : Fin 4 → ℤ,
      (starRingEnd ℂ) (PlaneWaves.vertexWeight L k (shiftedFreq (fun ν => (ϰ ν : ℂ)) m)) =
        PlaneWaves.vertexWeight L k (shiftedFreq (fun ν => (ϰ ν : ℂ)) m) := by
    intro m
    rw [PlaneWaves.vertexWeight, map_prod]
    refine Finset.prod_congr rfl fun ν _ => ?_
    rw [hcast]
    exact conj_dirichletSum_ofReal L k M hr _
  have hvn : ∑ m ∈ freqBox L k,
      ‖PlaneWaves.vertexWeight L k (shiftedFreq (fun ν => (ϰ ν : ℂ)) m)‖ ^ 2 = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_one, ← hv]
    exact Finset.sum_congr rfl fun m _ => ofReal_norm_sq_of_conj_eq (hconj m)
  refine ⟨fun μ => ?_, hv⟩
  rw [← hvn]
  refine Finset.sum_le_sum fun m _ => ?_
  have hexp : ‖Complex.exp (Complex.I * (1 - ((finestMesh L k : ℝ) : ℂ)) *
      shiftedFreq (fun ν => (ϰ ν : ℂ)) m μ / 2)‖ = 1 := by
    rw [hcast]
    have e₁ : Complex.I * (1 - ((finestMesh L k : ℝ) : ℂ)) *
        ((ϰ μ + 2 * Real.pi * (m μ : ℝ) : ℝ) : ℂ) / 2 =
        (((1 - finestMesh L k) * (ϰ μ + 2 * Real.pi * (m μ : ℝ)) / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e₁, Complex.norm_exp_ofReal_mul_I]
  have hside : ‖dirichletSum L k (shiftedFreq (fun ν => (ϰ ν : ℂ)) m μ)‖ ≤ 1 := by
    rw [hcast]
    exact norm_dirichletSum_ofReal_le L k M hs hr _
  rw [PlaneWaves.edgeWeight]
  rw [norm_mul, norm_mul, hexp, one_mul, mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _)
    (pow_le_one₀ (norm_nonneg _) hside)
end PlaneWaveSums
end Tower
end YangMills.Construction
end
