import YangMills.Construction.MirrorGridsOfEverySide.FiniteSetsOfCellsLieInACoarserCellAtEveryMirrorGrid
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
private theorem exists_index_bound_of_finite {D : GridSetup} (Γ : ChessboardTori.ReflectionGrid D)
    {O : Set (Set InfiniteLattice.AmbientSpace)} (hO : O.Finite) (hsub : O ⊆ Γ.cellSet) :
    ∃ M : ℕ, ∀ S ∈ O, ∃ k : Fin 4 → ℤ, Γ.cell k = S ∧ ∀ μ, (k μ).natAbs ≤ M := by
  have hidx : ∀ S ∈ O, ∃ k : Fin 4 → ℤ, Γ.cell k = S := fun S hS => hsub hS
  choose! idx hidx using hidx
  refine ⟨hO.toFinset.sup fun S => ∑ μ, (idx S μ).natAbs,
    fun S hS => ⟨idx S, hidx S hS, fun μ => ?_⟩⟩
  calc (idx S μ).natAbs ≤ ∑ ν, (idx S ν).natAbs :=
        Finset.single_le_sum (f := fun ν => (idx S ν).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ μ)
    _ ≤ _ := Finset.le_sup (f := fun S => ∑ ν, (idx S ν).natAbs) (hO.mem_toFinset.mpr hS)
theorem allGridsFiniteCellsInCoarserCell_holds : AllGridsFiniteCellsInCoarserCell := by
  intro D Γ hΓ O hO hsub
  obtain ⟨M, hM⟩ := exists_index_bound_of_finite Γ hO hsub
  have hL1 : (1 : ℝ) < D.L := D.one_lt_factor
  have hL0 : (D.L : ℝ) ≠ 0 := by linarith
  have hside : 0 < Γ.cellSide := zpow_pos (by linarith) _
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((2 * M + 1 : ℕ) : ℝ) hL1
  let u : Fin 4 → ℤ := fun _ => -(M : ℤ)
  let Γ' : ChessboardTori.ReflectionGrid D :=
    ⟨Γ.q + (n : ℤ), by have := Γ.one_sub_K_le_q; omega,
      fun μ => Γ.origin μ + Γ.cellSide * u μ,
      fun μ => by
        obtain ⟨i, hi⟩ := Γ.origin_mem μ
        refine ⟨i + Γ.cellRatio * u μ, ?_⟩
        rw [hi, Γ.cellSide_eq]
        push_cast
        ring⟩
  have hside' : Γ'.cellSide = (D.L : ℝ) ^ n * Γ.cellSide := by
    change (D.L : ℝ) ^ (Γ.q + (n : ℤ)) = (D.L : ℝ) ^ n * (D.L : ℝ) ^ Γ.q
    rw [zpow_add₀ hL0, zpow_natCast, mul_comm]
  have hpow : (1 : ℝ) ≤ (D.L : ℝ) ^ n := one_le_pow₀ hL1.le
  refine ⟨Γ', ?_, ⟨⟨n, hside'⟩, ?_⟩, Γ'.cell 0, ⟨0, rfl⟩, ?_⟩
  · refine ⟨⟨Γ.q + (n : ℤ), rfl⟩, hΓ.2.trans ?_⟩
    rw [hside']
    gcongr
    nlinarith
  · rintro _ ⟨⟨μ, k⟩, rfl⟩
    refine ⟨⟨μ, u μ + k * (D.L : ℤ) ^ n⟩, ?_⟩
    ext x
    simp only [ChessboardTori.ReflectionGrid.wall, mem_ofPred_eq]
    have horigin : Γ'.origin μ = Γ.origin μ + Γ.cellSide * u μ := rfl
    rw [horigin, hside']
    push_cast
    constructor <;> intro hx <;> rw [hx] <;> ring
  · intro S hS
    obtain ⟨k, rfl, hk⟩ := hM S hS
    intro x hx μ
    have hxμ := hx μ
    have horigin : Γ'.origin μ = Γ.origin μ + Γ.cellSide * u μ := rfl
    have hkμ : |k μ| ≤ (M : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hk μ
    have hlo : ((-(M : ℤ) : ℤ) : ℝ) ≤ k μ := by
      exact_mod_cast (abs_le.mp hkμ).1
    have hhi : (k μ : ℝ) ≤ M := by
      exact_mod_cast (abs_le.mp hkμ).2
    have hu : ((u μ : ℤ) : ℝ) = -(M : ℝ) := by simp [u]
    obtain ⟨hx0, hx1⟩ := hxμ
    rw [horigin, hside']
    simp only [Pi.zero_apply, Int.cast_zero, mul_zero, add_zero, hu, mem_Icc]
    push_cast at hlo hn
    constructor
    · nlinarith
    · have hwide : (2 * (M : ℝ) + 1) * Γ.cellSide ≤ (D.L : ℝ) ^ n * Γ.cellSide :=
        mul_le_mul_of_nonneg_right hn.le hside.le
      nlinarith
end YangMills.Construction.MirrorGridsAllSides
end
