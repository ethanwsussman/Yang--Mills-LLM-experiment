import YangMills.Construction.ChessboardTori.ChessboardEstimate
import YangMills.Construction.ChessboardTori.CoarseGridsOfAGrid
import YangMills.Construction.ChessboardTori.NamesOfAMirrorGridOnATorus
import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import YangMills.Construction.Constants.SurfaceTermNumbers
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ReflectionGrid
variable {D : ChessboardSetup}
def cellFamilyProduct (O : Set (Set AmbientSpace)) (F : Set AmbientSpace → D.GaugeField → ℂ) :
    D.GaugeField → ℂ :=
  fun U => ∏ᶠ S ∈ O, F S U
def rotatedRealPart (φ : ℝ) (O : Set (Set AmbientSpace))
    (F : Set AmbientSpace → D.GaugeField → ℂ) : D.GaugeField → ℝ :=
  fun U => (Complex.exp (-(Complex.I * φ)) * cellFamilyProduct O F U).re
def logOnePlusRotated (φ t : ℝ) (O : Set (Set AmbientSpace))
    (F : Set AmbientSpace → D.GaugeField → ℂ) : D.GaugeField → ℝ :=
  fun U => Real.log (1 + t * rotatedRealPart φ O F U)
def onePlusRotated (φ t : ℝ) (O : Set (Set AmbientSpace))
    (F : Set AmbientSpace → D.GaugeField → ℂ) : D.GaugeField → ℂ :=
  fun U => ((1 + t * rotatedRealPart φ O F U : ℝ) : ℂ)
variable (g : ReflectionGrid D)
def chessboardNormProduct (O : Set (Set AmbientSpace))
    (F : Set AmbientSpace → D.GaugeField → ℂ) : ℝ :=
  ∏ᶠ S ∈ O, g.chessboardNorm S (F S)
def baseCellMover (S : Set AmbientSpace) : D.LatticeSym :=
  g.toLatticeSym (g.mover g.baseCell S)
def transportedProduct (J : Finset (Set AmbientSpace)) (f : D.GaugeField → ℂ) :
    D.GaugeField → ℂ :=
  fun U => ∏ S ∈ J, g.transportTo g.baseCell S f U
def RotatedPartLogBound (O : Set (Set AmbientSpace)) (F : Set AmbientSpace → D.GaugeField → ℂ)
    (φ t : ℝ) : Prop :=
  (fun U => ((rotatedRealPart φ O F U : ℝ) : ℂ)) ∈
      cellObservables (D := D) (g.enclosingCoarsening O).baseCell ∧
    (fun U => ((logOnePlusRotated φ t O F U : ℝ) : ℂ)) ∈
      cellObservables (D := D) (g.enclosingCoarsening O).baseCell ∧
    (∀ U, |t * rotatedRealPart φ O F U| ≤ 1 / 2) ∧
    ∀ ν : Measure D.GaugeField, IsProbabilityMeasure ν →
      Complex.exp (-(Complex.I * φ)) * ∫ U, cellFamilyProduct O F U ∂ν =
          ((‖∫ U, cellFamilyProduct O F U ∂ν‖ : ℝ) : ℂ) →
        t * ‖∫ U, cellFamilyProduct O F U ∂ν‖ -
            t ^ 2 * InfiniteLattice.observableSupNorm (cellFamilyProduct O F) ^ 2 ≤
          ∫ U, logOnePlusRotated φ t O F U ∂ν
open Classical in
def TransportedProductExpansion (O : Set (Set AmbientSpace))
    (F : Set AmbientSpace → D.GaugeField → ℂ) (φ t : ℝ) (J : Finset (Set AmbientSpace)) : Prop :=
  ∀ U : D.GaugeField,
    (g.enclosingCoarsening O).transportedProduct J (onePlusRotated φ t O F) U =
      ∑ T ∈ J.powerset, ((t : ℂ) / 2) ^ T.card * ∑ σ : T → ℤˣ,
        (∏ c : T, Complex.exp (-(Complex.I * (((σ c : ℤˣ) : ℤ) : ℂ) * φ))) *
          ∏ c : T, ∏ᶠ S ∈ O, Conventions.signedConjFun (σ c)
            (((g.enclosingCoarsening O).baseCellMover c.1).actOn (F S)) U
def TransportedProductBound (O : Set (Set AmbientSpace))
    (F : Set AmbientSpace → D.GaugeField → ℂ) (φ t : ℝ) (J : Finset (Set AmbientSpace)) : Prop :=
  (D.periodicExpectation (D.liftedObservable
      ((g.enclosingCoarsening O).transportedProduct J (onePlusRotated φ t O F)))).im = 0 ∧
    0 < (D.periodicExpectation (D.liftedObservable
      ((g.enclosingCoarsening O).transportedProduct J (onePlusRotated φ t O F)))).re ∧
    (D.periodicExpectation (D.liftedObservable
      ((g.enclosingCoarsening O).transportedProduct J (onePlusRotated φ t O F)))).re ≤
      (1 + t * g.chessboardNormProduct O F) ^ J.card
def GibbsLogSumBound (O : Set (Set AmbientSpace)) (F : Set AmbientSpace → D.GaugeField → ℂ)
    (φ t : ℝ) (J : Finset (Set AmbientSpace)) : Prop :=
  ∀ ν : Measure D.GaugeField, InfiniteLattice.IsGibbs D.β ν →
    ∑ S ∈ J, ∫ U, ((g.enclosingCoarsening O).baseCellMover S).actOn
        (logOnePlusRotated φ t O F) U ∂ν ≤
      (J.card : ℝ) * t * g.chessboardNormProduct O F +
        (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
          (PeriodicLattice.torusSide D.L D.m / D.mesh) ^ 3
end ReflectionGrid
def GibbsBoundOnOneTorus.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.IsCoarse →
    ∀ O : Set (Set AmbientSpace), g.IsFiniteCellFamily O →
    ∀ F : Set AmbientSpace → D.GaugeField → ℂ,
      (∀ S ∈ O, F S ∈ ReflectionGrid.cellObservables (D := D) S) →
      2 * (g.enclosingCoarsening O).cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    ∀ φ t : ℝ, 0 < t →
      t < (2 * InfiniteLattice.observableSupNorm (ReflectionGrid.cellFamilyProduct O F) + 1)⁻¹ →
      g.RotatedPartLogBound O F φ t ∧
        ∀ J : Finset (Set AmbientSpace),
          (J : Set (Set AmbientSpace)) ⊆
            (g.enclosingCoarsening O).cellsWithin (g.enclosingCoarsening O).fundamentalBlock →
          g.TransportedProductExpansion O F φ t J ∧
            g.TransportedProductBound O F φ t J ∧
            g.GibbsLogSumBound O F φ t J
end YangMills.Construction.ChessboardTori
end
