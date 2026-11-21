import YangMills.Construction.ChessboardTori.InvarianceUnderTheGroupsOfGrids
import YangMills.Construction.ChessboardTori.JensenAgainstTheChessboard
import YangMills.Construction.ChessboardTori.JensenForPeriodicGibbsStates
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
namespace PeriodicJensen
theorem surfaceFactor_mul_β_nonneg (D : ChessboardSetup) :
    0 ≤ (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β :=
  mul_nonneg (Nat.cast_nonneg _) D.beta_pos.le
theorem unitReflectionGrid_cellSide (D : ChessboardSetup) : D.unitReflectionGrid.cellSide = 1 := by
  simp [ReflectionGrid.cellSide, ChessboardSetup.unitReflectionGrid]
theorem two_mul_unit_cellSide_le_torusSide (D : ChessboardSetup) (n : ℕ+) :
    2 * D.unitReflectionGrid.cellSide ≤ PeriodicLattice.torusSide D.L n := by
  rw [unitReflectionGrid_cellSide, mul_one]
  have h : (1 : ℝ) ≤ (D.L : ℝ) ^ (n : ℕ) := one_le_pow₀ D.one_lt_factor.le
  simp only [PeriodicLattice.torusSide]
  linarith
theorem surface_term_at_unit (D : ChessboardSetup) (n : ℕ+) :
    (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β * D.unitReflectionGrid.cellSide ^ 4 /
        (D.mesh ^ 3 * PeriodicLattice.torusSide D.L n) =
      (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
          (PeriodicLattice.torusSide D.L n / D.mesh) ^ 3 /
        PeriodicLattice.torusSide D.L n ^ 4 := by
  have ha : D.mesh ≠ 0 := D.mesh_pos.ne'
  have hl : PeriodicLattice.torusSide D.L n ≠ 0 := by
    have h := two_mul_unit_cellSide_le_torusSide D n
    rw [unitReflectionGrid_cellSide] at h
    intro h0
    rw [h0] at h
    norm_num at h
  rw [unitReflectionGrid_cellSide]
  field_simp
theorem one_le_two_mul_index_pow_four {α : Type*} [AddGroup α] (H : AddSubgroup α) (q : ℕ)
    (hH : H.FiniteIndex) (hq : H.index = q) : (1 : ℝ) ≤ (2 * (q : ℝ)) ^ 4 := by
  have hq0 : q ≠ 0 := hq ▸ hH.index_ne_zero
  have h1 : (1 : ℝ) ≤ q := Nat.one_le_cast.2 (Nat.pos_of_ne_zero hq0)
  exact one_le_pow₀ (by linarith)
theorem le_add_mul_of_le_add {x y t c : ℝ} (h : x ≤ y + t) (ht : 0 ≤ t) (hc : 1 ≤ c) :
    x ≤ y + c * t := by
  nlinarith
end PeriodicJensen
open PeriodicJensen in
theorem PeriodicJensen.statement_holds
    (hbound : JensenChessboardBound.Statement)
    (hinv : GridGroupInvariance.Statement) :
    PeriodicJensen.Statement := by
  intro D ν hν
  have hall := ((hinv D).2.2 ν hν).1
  have key : ∀ g : ReflectionGrid D, g.IsCoarse → ∀ F : D.GaugeField → ℝ,
      (fun U => (F U : ℂ)) ∈ ReflectionGrid.cellObservables (D := D) g.baseCell →
      (∀ n : ℕ+, 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L n →
        ∫ U, F U ∂ν ≤
          Real.log (g.normAtExponent n g.baseCell fun U => Complex.exp (F U)) +
            (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β * g.cellSide ^ 4 /
              (D.mesh ^ 3 * PeriodicLattice.torusSide D.L n)) ∧
      ∫ U, F U ∂ν ≤ Real.log (g.limChessboardNorm fun U => Complex.exp (F U)) :=
    fun g hg F hF => hbound D g hg ν hν.1 (hall g hg) F hF
  have unit : ∀ F : D.GaugeField → ℝ,
      (fun U => (F U : ℂ)) ∈ ReflectionGrid.cellObservables (D := D) D.unitReflectionGrid.baseCell →
      ∀ n : ℕ+,
        ∫ U, F U ∂ν ≤
          Real.log (D.unitReflectionGrid.normAtExponent n D.unitReflectionGrid.baseCell
              fun U => Complex.exp (F U)) +
            (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
                (PeriodicLattice.torusSide D.L n / D.mesh) ^ 3 /
              PeriodicLattice.torusSide D.L n ^ 4 := by
    intro F hF n
    have h := (key D.unitReflectionGrid D.unitReflectionGrid_isCoarse F hF).1 n
      (two_mul_unit_cellSide_le_torusSide D n)
    rwa [surface_term_at_unit] at h
  have hl : ∀ n : ℕ+, 0 ≤ PeriodicLattice.torusSide D.L n := fun n => by
    have h := two_mul_unit_cellSide_le_torusSide D n
    rw [unitReflectionGrid_cellSide] at h
    linarith
  refine ⟨key, unit, ?_⟩
  intro H q hH hq _
  have hc := one_le_two_mul_index_pow_four H q hH hq
  have hs := surfaceFactor_mul_β_nonneg D
  refine ⟨fun g hg F hF n hn => ?_, fun F hF n => ?_⟩
  · have h := (key g hg F hF).1 n hn
    have hside : 0 ≤ g.cellSide := zpow_nonneg (by linarith [D.one_lt_factor]) _
    have ht : 0 ≤ (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β * g.cellSide ^ 4 /
        (D.mesh ^ 3 * PeriodicLattice.torusSide D.L n) :=
      div_nonneg (mul_nonneg hs (pow_nonneg hside 4))
        (mul_nonneg (pow_nonneg D.mesh_pos.le 3) (hl n))
    have h' := le_add_mul_of_le_add h ht hc
    rw [show (2 * (q : ℝ)) ^ 4 * (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
          g.cellSide ^ 4 / (D.mesh ^ 3 * PeriodicLattice.torusSide D.L n) =
        (2 * (q : ℝ)) ^ 4 * ((Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
          g.cellSide ^ 4 / (D.mesh ^ 3 * PeriodicLattice.torusSide D.L n)) by ring]
    exact h'
  · have h := unit F hF n
    have ht : 0 ≤ (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
        (PeriodicLattice.torusSide D.L n / D.mesh) ^ 3 / PeriodicLattice.torusSide D.L n ^ 4 :=
      div_nonneg (mul_nonneg hs (pow_nonneg (div_nonneg (hl n) D.mesh_pos.le) 3))
        (pow_nonneg (hl n) 4)
    have h' := le_add_mul_of_le_add h ht hc
    rw [show (2 * (q : ℝ)) ^ 4 * (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
          (PeriodicLattice.torusSide D.L n / D.mesh) ^ 3 / PeriodicLattice.torusSide D.L n ^ 4 =
        (2 * (q : ℝ)) ^ 4 * ((Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
          (PeriodicLattice.torusSide D.L n / D.mesh) ^ 3 / PeriodicLattice.torusSide D.L n ^ 4) by ring]
    exact h'
end YangMills.Construction.ChessboardTori
end
