import YangMills.Construction.ChessboardTori.ChessboardEstimate
import YangMills.Construction.ChessboardTori.NamesOfAMirrorGridOnATorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
def ChessboardSetup.AgreeOnCompactFields (D : ChessboardSetup)
    (F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) : Prop :=
  ∀ U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ), F U = F' U
def TorusReduction.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D),
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    (∀ S ∈ g.cellSet,
      BijOn D.projLink (ReflectionGrid.interiorLinks (D := D) S)
        (g.torusCellLinks (D.proj '' S)) ∧
      (∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
        D.liftedObservable F ∈ g.torusCellObservables (D.proj '' S)) ∧
      (∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
        ∀ F' ∈ ReflectionGrid.cellObservables (D := D) S, ∀ c : ℂ,
        D.liftedObservable (F + F') = D.liftedObservable F + D.liftedObservable F' ∧
        D.liftedObservable (c • F) = c • D.liftedObservable F ∧
        D.liftedObservable (F * F') = D.liftedObservable F * D.liftedObservable F' ∧
        D.liftedObservable (fun U => starRingEnd ℂ (F U)) =
          fun U => starRingEnd ℂ (D.liftedObservable F U)) ∧
      D.liftedObservable (fun _ => 1) = (fun _ => 1) ∧
      ∀ F' ∈ g.torusCellObservables (D.proj '' S),
        ∃ F ∈ ReflectionGrid.cellObservables (D := D) S,
          D.AgreeOnCompactFields (D.liftedObservable F) F') ∧
    (∀ S ∈ g.cellSet, ∀ S' ∈ g.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
      D.AgreeOnCompactFields (D.liftedObservable (g.transportTo S S' F))
        (g.torusTransportTo (D.proj '' S) (D.proj '' S') (D.liftedObservable F))) ∧
    (∀ H : D.GaugeField → ℂ, InfiniteLattice.IsBoundedObservable H →
      D.liftedExpectation H = D.periodicExpectation (D.liftedObservable H)) ∧
    (∀ B ∈ g.blocks, ∀ S ∈ g.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
      D.AgreeOnCompactFields (D.liftedObservable (g.productOfTransports S B F))
        (g.torusProduct (D.liftedObservable F))) ∧
    (∀ S ∈ g.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
      (D.periodicExpectation (g.torusProduct (D.liftedObservable F))).im = 0 ∧
      0 ≤ (D.periodicExpectation (g.torusProduct (D.liftedObservable F))).re ∧
      g.chessboardNorm S F = g.torusChessboardNorm (D.liftedObservable F)) ∧
    (∀ C ∈ g.torusCellSet, ∀ F ∈ g.torusCellObservables C,
      (D.periodicExpectation (g.torusProduct F)).im = 0 ∧
      0 ≤ (D.periodicExpectation (g.torusProduct F)).re ∧
      (∀ C' ∈ g.torusCellSet,
        g.torusChessboardNorm (g.torusTransportTo C C' F) = g.torusChessboardNorm F) ∧
      g.torusChessboardNorm F = g.torusChessboardNorm (fun U => starRingEnd ℂ (F U))) ∧
    ∀ F : Set D.Torus → (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ,
      (∀ C ∈ g.torusCellSet, F C ∈ g.torusCellObservables C) →
        ‖D.periodicExpectation fun U => ∏ᶠ C ∈ g.torusCellSet, F C U‖ ≤
          ∏ᶠ C ∈ g.torusCellSet, g.torusChessboardNorm (F C)
end YangMills.Construction.ChessboardTori
end
