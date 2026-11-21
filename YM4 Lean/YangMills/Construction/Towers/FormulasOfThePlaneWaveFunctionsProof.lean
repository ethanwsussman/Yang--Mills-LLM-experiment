import YangMills.Construction.Towers.FormulasOfThePlaneWaveFunctions
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.PlaneWaveSymbolFormulas
open PlaneWaveCalculus PlaneWaves
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (toComplexVec)
theorem forwardFactor_mul_forwardFactor_neg (e q : ℂ) :
    (e⁻¹ * (Complex.exp (Complex.I * e * q) - 1)) *
        (e⁻¹ * (Complex.exp (Complex.I * e * (-q)) - 1)) =
      2 * e⁻¹ ^ 2 * (1 - Complex.cos (e * q)) := by
  have hA : Complex.exp (Complex.I * e * q) =
      Complex.cos (e * q) + Complex.sin (e * q) * Complex.I := by
    rw [← Complex.exp_mul_I]
    congr 1
    ring
  have hB : Complex.exp (Complex.I * e * (-q)) =
      Complex.cos (e * q) - Complex.sin (e * q) * Complex.I := by
    have h : Complex.I * e * (-q) = (-(e * q)) * Complex.I := by ring
    rw [h, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  have hs := Complex.sin_sq_add_cos_sq (e * q)
  rw [hA, hB]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (e⁻¹ ^ 2) * hs -
    (e⁻¹ ^ 2 * Complex.sin (e * q) ^ 2) * hI
theorem sum_range_shift_eq_sum_Icc (n : ℕ) (f : ℤ → ℂ) :
    ∑ l ∈ Finset.range (2 * n + 1), f ((l : ℤ) - n) = ∑ j ∈ Finset.Icc (-(n : ℤ)) n, f j := by
  apply Finset.sum_nbij' (fun l : ℕ => (l : ℤ) - n) (fun j : ℤ => (j + n).toNat)
  · intro l hl
    simp only [Finset.mem_range, Finset.mem_Icc] at hl ⊢
    omega
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢
    omega
  · intro l _
    simp
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    omega
  · intro l _
    rfl
theorem sum_Icc_neg (n : ℕ) (f : ℤ → ℂ) :
    ∑ j ∈ Finset.Icc (-(n : ℤ)) n, f (-j) = ∑ j ∈ Finset.Icc (-(n : ℤ)) n, f j := by
  apply Finset.sum_nbij' (fun j : ℤ => -j) (fun j : ℤ => -j)
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
    rfl
theorem sum_range_exp_eq_mul_sum_Icc (e τ : ℂ) (n : ℕ) :
    ∑ l ∈ Finset.range (2 * n + 1), Complex.exp (Complex.I * e * (l : ℂ) * τ) =
      Complex.exp (Complex.I * e * (n : ℂ) * τ) *
        ∑ j ∈ Finset.Icc (-(n : ℤ)) n, Complex.exp (Complex.I * e * (j : ℂ) * τ) := by
  rw [← sum_range_shift_eq_sum_Icc n (fun j : ℤ => Complex.exp (Complex.I * e * (j : ℂ) * τ)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem sin_mul_sum_Icc_exp (e τ : ℂ) (n : ℕ) (hn : e * (2 * (n : ℂ) + 1) = 1) :
    Complex.sin (e * τ / 2) *
        ∑ j ∈ Finset.Icc (-(n : ℤ)) n, Complex.exp (Complex.I * e * (j : ℂ) * τ) =
      Complex.sin (τ / 2) := by
  set S := ∑ j ∈ Finset.Icc (-(n : ℤ)) n, Complex.exp (Complex.I * e * (j : ℂ) * τ) with hSdef
  set G := ∑ l ∈ Finset.range (2 * n + 1), Complex.exp (Complex.I * e * (l : ℂ) * τ) with hGdef
  set a := Complex.exp (e * τ / 2 * Complex.I) with ha
  set a' := Complex.exp (-(e * τ / 2) * Complex.I) with ha'
  set b := Complex.exp (τ / 2 * Complex.I) with hb
  set b' := Complex.exp (-(τ / 2) * Complex.I) with hb'
  set x := Complex.exp (Complex.I * e * τ) with hx
  set c := Complex.exp (Complex.I * e * (n : ℂ) * τ) with hc
  set c' := Complex.exp (-(Complex.I * e * (n : ℂ) * τ)) with hc'
  have haa : a * a' = 1 := by
    rw [ha, ha', ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  have hbb : b * b' = 1 := by
    rw [hb, hb', ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  have hcc : c' * c = 1 := by
    rw [hc, hc', ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  have hxa : x = a * a := by
    rw [hx, ha, ← Complex.exp_add]
    congr 1
    ring
  have hac : a' * c' = b' := by
    rw [ha', hc', hb', ← Complex.exp_add]
    congr 1
    linear_combination (-(Complex.I * τ / 2)) * hn
  have hcS : c * S = G := by
    rw [hGdef, sum_range_exp_eq_mul_sum_Icc e τ n]
  have hS : S = c' * G := by
    rw [← hcS]
    linear_combination (-S) * hcc
  have hGx : G * (x - 1) = b * b - 1 := by
    have hterm : ∀ l ∈ Finset.range (2 * n + 1),
        Complex.exp (Complex.I * e * (l : ℂ) * τ) = x ^ l := by
      intro l _
      rw [hx, ← Complex.exp_nat_mul]
      congr 1
      ring
    have hpow : x ^ (2 * n + 1) = b * b := by
      rw [hx, ← Complex.exp_nat_mul, hb, ← Complex.exp_add]
      congr 1
      push_cast
      linear_combination (Complex.I * τ) * hn
    rw [hGdef, Finset.sum_congr rfl hterm, geom_sum_mul, hpow]
  have h1 : a' - a = a' * (1 - x) := by
    rw [hxa]
    linear_combination a * haa
  have h2 : (a' - a) * S = b' - b := by
    rw [h1, hS]
    calc a' * (1 - x) * (c' * G) = -(a' * c') * (G * (x - 1)) := by ring
      _ = -b' * (b * b - 1) := by rw [hac, hGx]
      _ = b' - b := by linear_combination (-b) * hbb
  rw [Complex.sin, Complex.sin]
  linear_combination (Complex.I / 2) * h2
theorem finestMesh_inv (L k : ℕ) : (finestMesh L k)⁻¹ = (L : ℝ) ^ k := by
  simp [finestMesh, meshAt, zpow_neg]
theorem exists_odd_freqWindow {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    ∃ n : ℕ, L ^ k = 2 * n + 1 ∧ freqWindow L k = Finset.Icc (-(n : ℤ)) n ∧
      meshC L k * (2 * (n : ℂ) + 1) = 1 := by
  obtain ⟨n, hn⟩ := hL.1.pow (n := k)
  have hcast : (finestMesh L k)⁻¹ = 2 * (n : ℝ) + 1 := by
    rw [finestMesh_inv]
    exact_mod_cast hn
  refine ⟨n, hn, ?_, ?_⟩
  · have hfl : ⌊1 / 2 * ((finestMesh L k)⁻¹ - 1)⌋ = (n : ℤ) := by
      have h : 1 / 2 * ((finestMesh L k)⁻¹ - 1) = (n : ℝ) := by
        rw [hcast]
        ring
      rw [h, Int.floor_natCast]
    rw [freqWindow, hfl]
  · have hne : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have h : finestMesh L k * (2 * (n : ℝ) + 1) = 1 := by
      rw [← hcast]
      have h0 : finestMesh L k ≠ 0 := by
        intro h0
        rw [h0, inv_zero] at hcast
        exact hne hcast.symm
      exact mul_inv_cancel₀ h0
    have h' : ((finestMesh L k * (2 * (n : ℝ) + 1) : ℝ) : ℂ) = 1 := by
      rw [h]
      simp
    push_cast at h'
    exact h'
theorem meshC_ne_zero {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    meshC L k ≠ 0 := by
  obtain ⟨n, -, -, h⟩ := exists_odd_freqWindow hL k
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h
theorem symbolSquare_eq_sum_cos (L k : ℕ) (q : Fin 4 → ℂ) : symbolSquare L k q =
    ∑ μ, 2 * (meshC L k)⁻¹ ^ 2 * (1 - Complex.cos (meshC L k * q μ)) := by
  refine Finset.sum_congr rfl fun μ _ => ?_
  exact forwardFactor_mul_forwardFactor_neg (meshC L k) (q μ)
theorem conj_forwardSymbol (L k : ℕ) (q : AmbientSpace) (ν : Fin 4) :
    conj (forwardSymbol L k (toComplexVec q) ν) = forwardSymbol L k (-toComplexVec q) ν := by
  simp only [forwardSymbol, map_mul, map_sub, map_inv₀, Complex.conj_ofReal, map_one,
    ← Complex.exp_conj, Complex.conj_I, Pi.neg_apply, toComplexVec]
  congr 3
  ring
theorem dirichletSum_eq_Icc {L k n : ℕ} (h : freqWindow L k = Finset.Icc (-(n : ℤ)) n) (τ : ℂ) :
    dirichletSum L k τ = meshC L k *
      ∑ j ∈ Finset.Icc (-(n : ℤ)) n, Complex.exp (Complex.I * meshC L k * (j : ℂ) * τ) := by
  rw [dirichletSum, h]
theorem dirichletSum_even {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (τ : ℂ) :
    dirichletSum L k (-τ) = dirichletSum L k τ := by
  obtain ⟨n, -, hr, -⟩ := exists_odd_freqWindow hL k
  rw [dirichletSum_eq_Icc hr, dirichletSum_eq_Icc hr,
    ← sum_Icc_neg n (fun j : ℤ => Complex.exp (Complex.I * meshC L k * (j : ℂ) * τ))]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  push_cast
  ring
theorem conj_dirichletSum {L k : ℕ} (τ : ℝ) :
    conj (dirichletSum L k (τ : ℂ)) = dirichletSum L k (-(τ : ℂ)) := by
  simp only [dirichletSum, map_mul, map_sum, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I, map_intCast]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  congr 1
  ring
theorem holds : Holds := by
  intro L hL k _
  obtain ⟨n, hpow, hr, hn⟩ := exists_odd_freqWindow hL k
  have h0 := meshC_ne_zero hL k
  refine
    { symbolSquare_eq := symbolSquare_eq_sum_cos L k
      symbolSquare_neg := ?_
      symbolSquare_periodic := ?_
      conj_symbolSquare := ?_
      symbolSquare_ofReal := ?_
      sin_mul_dirichletSum := ?_
      dirichletSum_neg := fun τ => dirichletSum_even hL (τ : ℂ)
      dirichletSum_im := ?_
      geom_sum_eq := ?_ }
  · intro q
    rw [symbolSquare_eq_sum_cos, symbolSquare_eq_sum_cos]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have h : meshC L k * (-q) μ = -(meshC L k * q μ) := by
      simp
    rw [h, Complex.cos_neg]
  · intro q e
    rw [symbolSquare_eq_sum_cos, symbolSquare_eq_sum_cos]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have h : meshC L k * periodShift L k q e μ =
        meshC L k * q μ + (e μ : ℂ) * (2 * (Real.pi : ℂ)) := by
      rw [periodShift]
      field_simp
    rw [h, Complex.cos_add_int_mul_two_pi]
  · intro q
    rw [symbolSquare_eq_sum_cos, symbolSquare_eq_sum_cos, map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [map_mul, map_sub, map_pow, map_inv₀, map_one, Complex.conj_ofReal, map_ofNat,
      ← Complex.cos_conj, conjVec]
  · intro q'
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← conj_forwardSymbol, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · intro τ
    have hs := sin_mul_sum_Icc_exp (meshC L k) τ n hn
    rw [dirichletSum_eq_Icc hr, ← hs]
    field_simp
  · intro τ
    have h : conj (dirichletSum L k (τ : ℂ)) = dirichletSum L k (τ : ℂ) := by
      rw [conj_dirichletSum, dirichletSum_even hL]
    exact Complex.conj_eq_iff_im.mp h
  · intro τ
    rw [hpow, sum_range_exp_eq_mul_sum_Icc, dirichletSum_eq_Icc hr]
    have h : Complex.exp (Complex.I * meshC L k * (n : ℂ) * τ) =
        Complex.exp (Complex.I * (1 - meshC L k) * τ / 2) := by
      congr 1
      linear_combination (Complex.I * τ / 2) * hn
    rw [h]
    ring
end YangMills.Construction.Tower.PlaneWaveSymbolFormulas
end
