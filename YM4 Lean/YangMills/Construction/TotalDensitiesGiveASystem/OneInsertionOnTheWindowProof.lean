import YangMills.Construction.ChessboardTori.BoundByMultipleReflections
import YangMills.Construction.TotalDensitiesGiveASystem.OneInsertionOnTheWindow
import YangMills.Construction.TotalDensitiesGiveASystem.TheCentredCellValueOnTheWindow
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Set
namespace YangMills.Construction.TotalDensitiesGiveASystem
section
variable {D : ChessboardTori.ChessboardSetup}
private theorem exists_positiveMultiple_side (c : ChessboardTori.GridCell D) :
    ∃ u : InfiniteLattice.positiveMultiples D.mesh,
      (u : ℝ) = c.side ∧ InfiniteLattice.timeStep u = c.timeStep 1 := by
  have hL : 0 < D.L := by
    have := D.one_lt_factor
    exact_mod_cast (by linarith : (0 : ℝ) < D.L)
  have hpos : 0 < D.L ^ (c.grid.q + ((D.K : ℕ) : ℤ)).toNat := Nat.pow_pos hL
  have hside : c.side = ((D.L ^ (c.grid.q + ((D.K : ℕ) : ℤ)).toNat : ℕ) : ℝ) * D.mesh := by
    have := c.grid.cellSide_eq
    simpa [ChessboardTori.GridCell.side, ChessboardTori.ReflectionGrid.cellRatio] using this
  refine ⟨⟨c.side, _, hpos, hside⟩, rfl, ?_⟩
  apply Subtype.ext
  funext μ
  by_cases h : μ = InfiniteLattice.timeAxis
  · subst h
    simp [InfiniteLattice.timeStep, ChessboardTori.GridCell.timeStep, ReflectionsAndOneInsertion.timeUnitVec,
      ChessboardTori.coordVec]
  · simp [InfiniteLattice.timeStep, ChessboardTori.GridCell.timeStep, ReflectionsAndOneInsertion.timeUnitVec,
      ChessboardTori.coordVec, Pi.single_eq_of_ne h]
private theorem isAdmissibleSideSequence_id (c : ChessboardTori.GridCell D) (hs : c.side ≤ 1) :
    c.IsAdmissibleSideSequence fun r => r := by
  have hL : (1 : ℝ) < D.L := D.one_lt_factor
  refine ⟨fun r => ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ (D.L : ℝ) ^ (r : ℕ) := one_le_pow₀ hL.le
    have h2 : PeriodicLattice.torusSide D.L r = 2 * (D.L : ℝ) ^ (r : ℕ) := rfl
    rw [h2]
    linarith
  · have h1 : Tendsto (fun r : ℕ+ => (r : ℕ)) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨⟨b + 1, Nat.succ_pos b⟩, fun a ha => by
        have h : b + 1 ≤ (a : ℕ) := ha
        omega⟩
    have h2 := (tendsto_pow_atTop_atTop_of_one_lt hL).comp h1
    exact h2.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
end
theorem windowInsertion_of_reflections (hrefl : ChessboardTori.MultipleReflectionBound.Statement)
    (hcell : TotalDensities.WindowCentredCell.Statement) : TotalDensities.WindowInsertion.Statement := by
  obtain ⟨A, hA, f₀⟩ := hcell
  refine ⟨A, hA, fun T hT hM => ?_⟩
  obtain ⟨y₀, f₁⟩ := f₀ T hT hM
  refine ⟨y₀, fun y hy Bs hBs => ?_⟩
  obtain ⟨y₂, f₂⟩ := f₁ y hy Bs hBs
  refine ⟨y₂, fun g hg hy₂ => ?_⟩
  obtain ⟨CI, q, hCI, hq, f₃⟩ := f₂ g hg hy₂
  refine ⟨CI, q, hCI, hq, fun M hM' => ?_⟩
  intro D hDL hp c h hh hsup hside ρ hρ ν hν P hP Q hQ
  obtain ⟨hF, hval⟩ := f₃ M hM' D hDL hp c h hh hsup hside ν hν
  obtain ⟨u, hu, hstep⟩ := exists_positiveMultiple_side c
  have hm := isAdmissibleSideSequence_id c hside
  have h1 := (hrefl D ρ hρ c c.baseTime rfl u hu _ hm).1 _ hF P hP Q hQ
  rw [hstep] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hval _ hm) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
end YangMills.Construction.TotalDensitiesGiveASystem
end
