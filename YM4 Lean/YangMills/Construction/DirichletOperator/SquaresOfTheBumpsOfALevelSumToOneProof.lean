import YangMills.Construction.DirichletOperator.SquaresOfTheBumpsOfALevelSumToOne
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.PartitionCubes.LevelBumpSquares
theorem sqPartitionBump_eq_zero_of_one_le_abs {y : ℝ} (h : 1 ≤ |y|) : sqPartitionBump y = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hy
  have hm := sqPartitionBump_spec.support_subset hy
  have : |y| < 1 := abs_lt.2 ⟨by linarith [hm.1], by linarith [hm.2]⟩
  linarith
def intWindow (u : ℝ) (N : ℕ) : Finset ℤ := Finset.Ioc ⌊u - (N : ℝ) / 2⌋ (⌊u - (N : ℝ) / 2⌋ + N)
theorem mem_intWindow_bounds {u : ℝ} {N : ℕ} {k : ℤ} (hk : k ∈ intWindow u N) :
    -((N : ℝ) / 2) ≤ u - k ∧ u - k < (N : ℝ) / 2 := by
  obtain ⟨h₁, h₂⟩ := Finset.mem_Ioc.1 hk
  have f₁ := Int.floor_le (u - (N : ℝ) / 2)
  have f₂ := Int.lt_floor_add_one (u - (N : ℝ) / 2)
  have g₁ : ((⌊u - (N : ℝ) / 2⌋ : ℤ) : ℝ) + 1 ≤ k := by exact_mod_cast h₁
  have g₂ : (k : ℝ) ≤ ((⌊u - (N : ℝ) / 2⌋ : ℤ) : ℝ) + N := by exact_mod_cast h₂
  constructor <;> linarith
theorem sum_intWindow_sq (u : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ intWindow u N, sqPartitionBump (u - k) ^ 2 = 1 := by
  have hs := sqPartitionBump_spec.sum_squares u
  have hsupp : (Function.support fun k : ℤ => sqPartitionBump (u - k) ^ 2) ⊆
      (intWindow u N : Set ℤ) := by
    intro k hk
    by_contra hn
    apply hk
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have f₁ := Int.floor_le (u - (N : ℝ) / 2)
    have f₂ := Int.lt_floor_add_one (u - (N : ℝ) / 2)
    have hfar : 1 ≤ |u - k| := by
      have hnot : ¬(⌊u - (N : ℝ) / 2⌋ < k ∧ k ≤ ⌊u - (N : ℝ) / 2⌋ + N) := fun hh =>
        hn (Finset.mem_coe.2 (Finset.mem_Ioc.2 hh))
      rcases not_and_or.1 hnot with h | h
      · have g : (k : ℝ) ≤ ((⌊u - (N : ℝ) / 2⌋ : ℤ) : ℝ) := by exact_mod_cast not_lt.1 h
        exact le_trans (by linarith) (le_abs_self _)
      · have g : ((⌊u - (N : ℝ) / 2⌋ : ℤ) : ℝ) + N + 1 ≤ k := by
          exact_mod_cast (by omega : ⌊u - (N : ℝ) / 2⌋ + (N : ℤ) + 1 ≤ k)
        exact le_trans (by linarith) (neg_le_abs _)
    simp [sqPartitionBump_eq_zero_of_one_le_abs hfar]
  rw [finsum_eq_sum_of_support_subset _ hsupp] at hs
  exact hs
theorem exists_mem_intWindow_modEq (u : ℝ) {N : ℕ} (hN : 0 < N) (j : ℤ) :
    ∃ k ∈ intWindow u N, ∃ c : ℤ, j = k + c * N := by
  set F : ℤ := ⌊u - (N : ℝ) / 2⌋ with hF
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have e₁ := Int.emod_nonneg (j - F - 1) hN'.ne'
  have e₂ := Int.emod_lt_of_pos (j - F - 1) hN'
  have e₃ := Int.mul_ediv_add_emod (j - F - 1) N
  refine ⟨F + 1 + (j - F - 1) % N, Finset.mem_Ioc.2 ⟨by omega, by omega⟩, (j - F - 1) / N, ?_⟩
  linarith [mul_comm ((j - F - 1) / (N : ℤ)) (N : ℤ)]
theorem eq_of_mem_intWindow {u : ℝ} {N : ℕ} {k k' c : ℤ} (hk : k ∈ intWindow u N)
    (hk' : k' ∈ intWindow u N) (h : k = k' + c * N) : k = k' := by
  obtain ⟨h₁, h₂⟩ := Finset.mem_Ioc.1 hk
  obtain ⟨h₃, h₄⟩ := Finset.mem_Ioc.1 hk'
  have hc : c = 0 := by
    rcases lt_trichotomy c 0 with hc | hc | hc
    · nlinarith
    · exact hc
    · nlinarith
  simpa [hc] using h
theorem coe_halfShift_eq_iff {S σ : ℝ} {N : ℕ} (hσ : 0 < σ) (hS : S = N * σ) (j k : ℤ) :
    ((((j : ℝ) + 1 / 2) * σ : ℝ) : AddCircle S) = ((((k : ℝ) + 1 / 2) * σ : ℝ) : AddCircle S) ↔
      ∃ c : ℤ, j = k + c * N := by
  constructor
  · intro h
    have h₀ : (((((j : ℝ) + 1 / 2) * σ - ((k : ℝ) + 1 / 2) * σ : ℝ)) : AddCircle S) = 0 := by
      rw [AddCircle.coe_sub, h, sub_self]
    rw [AddCircle.coe_eq_zero_iff] at h₀
    obtain ⟨c, hc⟩ := h₀
    refine ⟨c, ?_⟩
    rw [zsmul_eq_mul, hS] at hc
    have hr : (j : ℝ) = k + c * N := by
      have : ((c : ℝ) * N - (j - k)) * σ = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · exact absurd h' hσ.ne'
    exact_mod_cast hr
  · rintro ⟨c, rfl⟩
    have e : (((k + c * (N : ℤ) : ℤ) : ℝ) + 1 / 2) * σ = ((k : ℝ) + 1 / 2) * σ + (c : ℝ) * S := by
      rw [hS]
      push_cast
      ring
    have z : (((c : ℝ) * S : ℝ) : AddCircle S) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨c, by simp⟩
    rw [e, AddCircle.coe_add, z, add_zero]
theorem circleCentredRep_coe {S v : ℝ} (hS : 0 < S) (hv : v ∈ Ico (-(S / 2)) (S / 2)) :
    circleCentredRep (v : AddCircle S) = v := by
  have hex : ∃ w : ℝ, w ∈ Ico (-(S / 2)) (S / 2) ∧ (w : AddCircle S) = (v : AddCircle S) :=
    ⟨v, hv, rfl⟩
  obtain ⟨h₁, h₂⟩ := Classical.epsilon_spec hex
  unfold circleCentredRep
  set w : ℝ := Classical.epsilon fun w : ℝ =>
    w ∈ Ico (-(S / 2)) (S / 2) ∧ (w : AddCircle S) = (v : AddCircle S) with hw
  have h₀ : ((w - v : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_sub, h₂, sub_self]
  rw [AddCircle.coe_eq_zero_iff] at h₀
  obtain ⟨c, hc⟩ := h₀
  rw [zsmul_eq_mul] at hc
  have a₁ : (c : ℝ) < 1 := by
    by_contra hn
    nlinarith [not_lt.1 hn, h₁.2, hv.1]
  have a₂ : (-1 : ℝ) < c := by
    by_contra hn
    nlinarith [not_lt.1 hn, h₁.1, hv.2]
  have b₁ : c < 1 := by exact_mod_cast a₁
  have b₂ : -1 < c := by exact_mod_cast a₂
  have hc0 : c = 0 := by omega
  simp only [hc0, Int.cast_zero, zero_mul] at hc
  linarith
theorem cubeSide_pos {𝒮 : RegionSequence.NestedRegions} {M : ℕ} (hM : 0 < M) (n : ℕ) :
    0 < cubeSide 𝒮 M n := by
  have hL : (0 : ℝ) < 𝒮.L := by exact_mod_cast (by have := 𝒮.thirteen_le_L; omega : 0 < 𝒮.L)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  unfold cubeSide RegionSequence.NestedRegions.scale scaleSpacing
  exact mul_pos hM' (mul_pos (zpow_pos hL _) 𝒮.ξ_pos)
theorem exists_side_eq_mul_cubeSide {𝒮 : RegionSequence.NestedRegions} {K m M R₁ n : ℕ}
    (h : 𝒮.IsLevelUnitChain K m M R₁) (hn : n ≤ topLevel 𝒮) :
    ∃ N : ℕ, 2 ≤ N ∧ 𝒮.side = N * cubeSide 𝒮 M n := by
  obtain ⟨k, hk, hS⟩ := h.separated.period_eq_even_mul
  have hLpos : 0 < 𝒮.L := by have := 𝒮.thirteen_le_L; omega
  refine ⟨2 * (k * 𝒮.L ^ (topLevel 𝒮 - n)), ?_, ?_⟩
  · have : 0 < k * 𝒮.L ^ (topLevel 𝒮 - n) := Nat.mul_pos hk (pow_pos hLpos _)
    omega
  · have hpow : (𝒮.L : ℝ) ^ topLevel 𝒮 = (𝒮.L : ℝ) ^ (topLevel 𝒮 - n) * (𝒮.L : ℝ) ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hn]
    have hS' : 𝒮.side = 2 * (k : ℝ) * ((M : ℝ) * ((𝒮.L : ℝ) ^ topLevel 𝒮 * 𝒮.ξ)) := by
      rw [hS]
      simp [scaleSpacing, topLevel]
    rw [hS', hpow]
    simp only [cubeSide, RegionSequence.NestedRegions.scale, scaleSpacing, zpow_natCast]
    push_cast
    ring
def halfCube {𝒮 : RegionSequence.NestedRegions} (M : ℕ) {n : ℕ} (hn : n ≤ topLevel 𝒮)
    (k : Fin 4 → ℤ) : LevelCube 𝒮 M where
  level := n
  centre := torusProj 4 𝒮.side fun μ => ((k μ : ℝ) + 1 / 2) * cubeSide 𝒮 M n
  level_le := hn
  centre_mem := by
    refine ⟨torusProj 4 𝒮.side fun μ => (k μ : ℝ) * cubeSide 𝒮 M n, ⟨k, rfl⟩, fun _ => 1,
      fun _ => Or.inl rfl, ?_⟩
    funext μ
    have e : ((k μ : ℝ) + 1 / 2) * cubeSide 𝒮 M n =
        (k μ : ℝ) * cubeSide 𝒮 M n + 1 * (cubeSide 𝒮 M n / 2) := by ring
    simp only [torusProj, Pi.add_apply]
    rw [e, AddCircle.coe_add]
theorem exists_halfShift_of_mem_cornerSet {𝒮 : RegionSequence.NestedRegions} {M n : ℕ}
    {z : 𝒮.Point} (hz : z ∈ cornerSet 𝒮 M n) :
    ∃ j : Fin 4 → ℤ, z = torusProj 4 𝒮.side fun μ => ((j μ : ℝ) + 1 / 2) * cubeSide 𝒮 M n := by
  obtain ⟨c, ⟨k, rfl⟩, ε, hε, rfl⟩ := hz
  have hj : ∀ μ, ∃ j : ℤ, (k μ : ℝ) * cubeSide 𝒮 M n + ε μ * (cubeSide 𝒮 M n / 2) =
      ((j : ℝ) + 1 / 2) * cubeSide 𝒮 M n := by
    intro μ
    rcases hε μ with h | h
    · exact ⟨k μ, by rw [h]; ring⟩
    · exact ⟨k μ - 1, by rw [h]; push_cast; ring⟩
  choose j hj using hj
  refine ⟨j, ?_⟩
  funext μ
  simp only [torusProj, Pi.add_apply]
  rw [← hj μ, AddCircle.coe_add]
theorem bijOn_halfCube {𝒮 : RegionSequence.NestedRegions} {M n N : ℕ} (hn : n ≤ topLevel 𝒮)
    (hσ : 0 < cubeSide 𝒮 M n) (hN : 0 < N) (hS : 𝒮.side = N * cubeSide 𝒮 M n)
    (u : Fin 4 → ℝ) :
    BijOn (halfCube M hn) (Fintype.piFinset fun μ => intWindow (u μ) N : Finset (Fin 4 → ℤ))
      {Q : LevelCube 𝒮 M | Q.level = n} := by
  refine ⟨fun k _ => rfl, ?_, ?_⟩
  · intro k hk k' hk' hkk
    have hk₁ := Fintype.mem_piFinset.1 (Finset.mem_coe.1 hk)
    have hk₂ := Fintype.mem_piFinset.1 (Finset.mem_coe.1 hk')
    funext μ
    have hc := congrFun (congrArg LevelCube.centre hkk) μ
    obtain ⟨c, hc⟩ := (coe_halfShift_eq_iff hσ hS (k μ) (k' μ)).1 hc
    exact eq_of_mem_intWindow (hk₁ μ) (hk₂ μ) hc
  · rintro ⟨l, z, hl, hz⟩ hQ
    obtain rfl : l = n := hQ
    obtain ⟨j, rfl⟩ := exists_halfShift_of_mem_cornerSet hz
    choose k hk c hc using fun μ => exists_mem_intWindow_modEq (u μ) hN (j μ)
    refine ⟨k, Finset.mem_coe.2 (Fintype.mem_piFinset.2 hk), ?_⟩
    refine LevelCube.ext rfl ?_
    funext μ
    exact (coe_halfShift_eq_iff hσ hS (k μ) (j μ)).2 ⟨-c μ, by rw [hc μ]; ring⟩
theorem productBump_halfCube {𝒮 : RegionSequence.NestedRegions} {M n N : ℕ}
    (hn : n ≤ topLevel 𝒮) (hσ : 0 < cubeSide 𝒮 M n) (hS : 𝒮.side = N * cubeSide 𝒮 M n)
    (x : 𝒮.Point) {a : Fin 4 → ℝ} (ha : ∀ μ, (a μ : AddCircle 𝒮.side) = x μ)
    {k : Fin 4 → ℤ} (hk : ∀ μ, k μ ∈ intWindow (a μ / cubeSide 𝒮 M n - 1 / 2) N) :
    (halfCube M hn k).productBump x =
      ∏ μ, sqPartitionBump (a μ / cubeSide 𝒮 M n - 1 / 2 - k μ) := by
  refine Finset.prod_congr rfl fun μ _ => ?_
  congr 1
  set σ := cubeSide 𝒮 M n with hσdef
  obtain ⟨b₁, b₂⟩ := mem_intWindow_bounds (hk μ)
  have e : a μ - ((k μ : ℝ) + 1 / 2) * σ = (a μ / σ - 1 / 2 - k μ) * σ := by
    field_simp
    ring
  have hd : x μ - (halfCube M hn k).centre μ =
      ((a μ - ((k μ : ℝ) + 1 / 2) * σ : ℝ) : AddCircle 𝒮.side) := by
    rw [AddCircle.coe_sub, ha]
    rfl
  have hmem : a μ - ((k μ : ℝ) + 1 / 2) * σ ∈ Ico (-(𝒮.side / 2)) (𝒮.side / 2) := by
    rw [e, hS]
    constructor
    · nlinarith
    · nlinarith
  rw [hd, circleCentredRep_coe 𝒮.side_pos hmem, e]
  show (a μ / σ - 1 / 2 - k μ) * σ / σ = _
  field_simp
theorem statement_holds : Statement := by
  intro 𝒮 K m M R₁ h n hn x
  obtain ⟨N, hN, hS⟩ := exists_side_eq_mul_cubeSide h hn
  have hM : 0 < M := by
    have h₁ := h.separated.blockSize_isPowerGe.1
    have h₂ := 𝒮.thirteen_le_L
    omega
  have hσ : 0 < cubeSide 𝒮 M n := cubeSide_pos hM n
  choose a ha using fun μ => QuotientAddGroup.mk_surjective (x μ)
  have ha' : ∀ μ, (a μ : AddCircle 𝒮.side) = x μ := ha
  set u : Fin 4 → ℝ := fun μ => a μ / cubeSide 𝒮 M n - 1 / 2 with hu
  have hsum : ∑ᶠ k ∈ ((Fintype.piFinset fun μ => intWindow (u μ) N : Finset (Fin 4 → ℤ)) :
        Set (Fin 4 → ℤ)), (∏ μ, sqPartitionBump (u μ - k μ)) ^ 2 =
      ∑ᶠ Q ∈ {Q : LevelCube 𝒮 M | Q.level = n}, Q.productBump x ^ 2 := by
    refine finsum_mem_eq_of_bijOn (halfCube M hn) (bijOn_halfCube hn hσ (by omega) hS u) ?_
    intro k hk
    rw [productBump_halfCube hn hσ hS x ha' (Fintype.mem_piFinset.1 (Finset.mem_coe.1 hk))]
  rw [← hsum, finsum_mem_coe_finset]
  have hprod := Finset.prod_univ_sum (fun μ => intWindow (u μ) N)
    (fun μ (k : ℤ) => sqPartitionBump (u μ - k) ^ 2)
  simp only [sum_intWindow_sq _ hN, Finset.prod_const_one] at hprod
  simp only [← Finset.prod_pow]
  exact hprod.symm
end YangMills.Construction.PartitionCubes.LevelBumpSquares
