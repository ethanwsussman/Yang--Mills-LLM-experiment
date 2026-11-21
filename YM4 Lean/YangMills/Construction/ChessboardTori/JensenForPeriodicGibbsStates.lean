import YangMills.Construction.ChessboardTori.LimitingChessboardSeminorm
import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import YangMills.Construction.ChessboardTori.UnitAndStandardGrids
import YangMills.Construction.Constants.SurfaceTermNumbers
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
def PeriodicJensen.Statement : Prop :=
  ∀ (D : ChessboardSetup) (ν : Measure D.GaugeField), ν ∈ D.periodicStates →
    (∀ g : ReflectionGrid D, g.IsCoarse →
      ∀ H : D.GaugeField → ℝ,
        (fun U => (H U : ℂ)) ∈ ReflectionGrid.cellObservables (D := D) g.baseCell →
        (∀ m' : ℕ+, 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m' →
          ∫ U, H U ∂ν ≤
            Real.log (g.normAtExponent m' g.baseCell fun U => Complex.exp (H U)) +
              (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β * g.cellSide ^ 4 /
                (D.mesh ^ 3 * PeriodicLattice.torusSide D.L m')) ∧
        ∫ U, H U ∂ν ≤ Real.log (g.limChessboardNorm fun U => Complex.exp (H U))) ∧
    (∀ H : D.GaugeField → ℝ,
      (fun U => (H U : ℂ)) ∈ ReflectionGrid.cellObservables (D := D) D.unitReflectionGrid.baseCell →
      ∀ m' : ℕ+,
        ∫ U, H U ∂ν ≤
          Real.log (D.unitReflectionGrid.normAtExponent m' D.unitReflectionGrid.baseCell
              fun U => Complex.exp (H U)) +
            (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
                (PeriodicLattice.torusSide D.L m' / D.mesh) ^ 3 /
              PeriodicLattice.torusSide D.L m' ^ 4) ∧
    ∀ (Γ : AddSubgroup (InfiniteLattice.LatticePoint D.mesh)) (q : ℕ), Γ.FiniteIndex → Γ.index = q →
      (∀ v ∈ Γ, InfiniteLattice.IsSymmetricUnder ν (InfiniteLattice.shift v)) →
      (∀ g : ReflectionGrid D, g.IsCoarse →
        ∀ H : D.GaugeField → ℝ,
          (fun U => (H U : ℂ)) ∈ ReflectionGrid.cellObservables (D := D) g.baseCell →
          ∀ m' : ℕ+, 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m' →
            ∫ U, H U ∂ν ≤
              Real.log (g.normAtExponent m' g.baseCell fun U => Complex.exp (H U)) +
                (2 * (q : ℝ)) ^ 4 * (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
                    g.cellSide ^ 4 /
                  (D.mesh ^ 3 * PeriodicLattice.torusSide D.L m')) ∧
      ∀ H : D.GaugeField → ℝ,
        (fun U => (H U : ℂ)) ∈
            ReflectionGrid.cellObservables (D := D) D.unitReflectionGrid.baseCell →
        ∀ m' : ℕ+,
          ∫ U, H U ∂ν ≤
            Real.log (D.unitReflectionGrid.normAtExponent m' D.unitReflectionGrid.baseCell
                fun U => Complex.exp (H U)) +
              (2 * (q : ℝ)) ^ 4 * (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
                  (PeriodicLattice.torusSide D.L m' / D.mesh) ^ 3 /
                PeriodicLattice.torusSide D.L m' ^ 4
end YangMills.Construction.ChessboardTori
end
