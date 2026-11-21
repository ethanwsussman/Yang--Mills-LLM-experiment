import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open Tower Matrices
variable {L m k j : ℕ}
def contourLeg (y : Vertex L m k (j + 1)) (x : Vertex L m k j) (σ : Equiv.Perm (Fin 4)) :
    List (Edge L m k j) :=
  PeriodicLattice.stepsThroughAxes (PeriodicLattice.blockOffset y x)
    (y.toSublattice (PeriodicLattice.levelDepth k j)) ((List.finRange 4).map σ)
def contourHolonomy (V : Edge L m k j → ComplexMatrix2) (e : Edge L m k (j + 1)) (x : Vertex L m k j)
    (σ : Equiv.Perm (Fin 4)) : ComplexMatrix2 :=
  PeriodicLattice.pathHolonomy V (contourLeg e.source x σ) *
    PeriodicLattice.pathHolonomy V (PeriodicLattice.crossingPath e x) *
    (PeriodicLattice.pathHolonomy V (contourLeg e.target (PeriodicLattice.shiftAcross e x) σ))⁻¹
def contourMean (V : Edge L m k j → ComplexMatrix2) (e : Edge L m k (j + 1)) : ComplexMatrix2 :=
  ((1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L) •
    ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) e.source,
      ∑ σ : Equiv.Perm (Fin 4), contourHolonomy V e x σ
def meanRadius (V : Edge L m k j → ComplexMatrix2) (e : Edge L m k (j + 1)) : ℂ :=
  (Matrix.det (contourMean V e)) ^ (1 / 2 : ℂ)
def normalizedMean (V : Edge L m k j → ComplexMatrix2) : Edge L m k (j + 1) → ComplexMatrix2 :=
  fun e => (meanRadius V e)⁻¹ • contourMean V e
structure ChainPoint (L m k : ℕ) where
  fine : Edge L m k 0 → ComplexMatrix2
  noise : (i : Fin k) → PositiveEdge L m k (i + 1) → ComplexMatrix2
def levelField (X : ChainPoint L m k) : (j : ℕ) → Edge L m k j → ComplexMatrix2
  | 0 => X.fine
  | j + 1 =>
    if h : j < k then
      fieldOfPositiveValues fun e => X.noise ⟨j, h⟩ e * normalizedMean (levelField X j) e.1
    else normalizedMean (levelField X j)
def unitPoint (L m k : ℕ) : ChainPoint L m k := ⟨fun _ => 1, fun _ _ => 1⟩
def traceDefect (g : ComplexMatrix2) : ℝ := 1 - (ComplexMatrix2.halfTrace g).re
def chainAction (a : ℝ) (X : ChainPoint L m k) : ℝ :=
  plaquetteAction L m k X.fine + a * ∑ i : Fin k, ∑ᶠ e : PositiveEdge L m k (i + 1),
    (meanRadius (levelField X i) e.1).re * traceDefect (X.noise i e)
def logRadiusSum (X : ChainPoint L m k) : ℝ :=
  ∑ i : Fin k, ∑ᶠ e : PositiveEdge L m k (i + 1), Real.log (meanRadius (levelField X i) e.1).re
abbrev LevelForms (L m k : ℕ) : Type :=
  edgeFormSpace L m k 0 × ((i : Fin k) → edgeFormSpace L m k (i + 1))
abbrev LevelValues (L m k : ℕ) : Type :=
  (Edge L m k 0 → ComplexMatrix2) × ((i : Fin k) → Edge L m k (i + 1) → ComplexMatrix2)
def formValues (ξ : LevelForms L m k) : LevelValues L m k :=
  (ξ.1, fun i => ξ.2 i)
def levelPairing (ξ η : LevelValues L m k) : ℝ :=
  (edgeFormPairing ξ.1 η.1).re + ∑ i : Fin k, (edgeFormPairing (ξ.2 i) (η.2 i)).re
def expMove (ξ : LevelForms L m k) (X : ChainPoint L m k) : ChainPoint L m k :=
  ⟨PeriodicLattice.expTwist ξ.1 X.fine,
    fun i e => ComplexMatrix2.matExp (Complex.I • (ξ.2 i : Edge L m k (i + 1) → ComplexMatrix2) e) * X.noise i e⟩
def leftDeriv (F : ChainPoint L m k → ℝ) (X : ChainPoint L m k)
    (ξ : LevelForms L m k) : ℝ :=
  deriv (fun t : ℝ => F (expMove (t • ξ) X)) 0
def leftSecondDeriv (F : ChainPoint L m k → ℝ) (X : ChainPoint L m k)
    (ξ η : LevelForms L m k) : ℝ :=
  deriv (fun s : ℝ => deriv (fun t : ℝ => F (expMove (s • ξ + t • η) X)) 0) 0
def tangentTransport (X : ChainPoint L m k) (ξ : LevelForms L m k) :
    (j : ℕ) → Edge L m k j → ComplexMatrix2
  | 0 => ξ.1
  | j + 1 =>
    if h : j < k then
      extendOddly fun e =>
        (open Classical in
          if he : e.IsPositivelyOriented then
            ComplexMatrix2.conjugateBy (X.noise ⟨j, h⟩ ⟨e, he⟩)
              (leftDifferential normalizedMean (levelField X j) (tangentTransport X ξ j) e)
          else 0) + (ξ.2 ⟨j, h⟩ : Edge L m k (j + 1) → ComplexMatrix2) e
    else 0
def IsTopDeriv (X : ChainPoint L m k)
    (T : LevelForms L m k →ₗ[ℝ] edgeFormSpace L m k k) : Prop :=
  ∀ ξ, (T ξ : Edge L m k k → ComplexMatrix2) = tangentTransport X ξ k
def topDeriv (X : ChainPoint L m k) : LevelForms L m k →ₗ[ℝ] edgeFormSpace L m k k :=
  Classical.epsilon (IsTopDeriv X)
def gaugeOrbitValues (X : ChainPoint L m k) (f : Vertex L m k 0 → ComplexMatrix2) : LevelValues L m k :=
  (covDiff X.fine f, fun i => extendOddly fun e =>
    open Classical in
      if he : e.IsPositivelyOriented then
        ComplexMatrix2.conjugateBy (X.noise i ⟨e, he⟩) (restrictVertexFunction (i + 1) f e.source) -
          restrictVertexFunction (i + 1) f e.source
      else 0)
def IsGaugeOrbitMap (X : ChainPoint L m k) (T : vertexFunctionSpace L m k 0 →ₗ[ℝ] LevelForms L m k) : Prop :=
  ∀ f, formValues (T f) = gaugeOrbitValues X f
def gaugeOrbitMap (X : ChainPoint L m k) : vertexFunctionSpace L m k 0 →ₗ[ℝ] LevelForms L m k :=
  Classical.epsilon (IsGaugeOrbitMap X)
def composedCubeAverage (X : ChainPoint L m k) :
    (j : ℕ) → (Vertex L m k 0 → ComplexMatrix2) → Vertex L m k j → ComplexMatrix2
  | 0, f => f
  | j + 1, f => adjointCubeAverage (levelField X j) (composedCubeAverage X j f)
def chainDrift (X : ChainPoint L m k) (ξ : LevelForms L m k) :
    (j : ℕ) → Vertex L m k j → ComplexMatrix2
  | 0 => 0
  | j + 1 =>
    adjointCubeAverage (levelField X j) (chainDrift X ξ j) +
      contourLogDrift (levelField X j) (tangentTransport X ξ j)
def shiftedGaugeValues (X : ChainPoint L m k) (ξ : LevelForms L m k) : Edge L m k k → ComplexMatrix2 :=
  tangentTransport X ξ k + covDiff (levelField X k) (chainDrift X ξ k)
def IsShiftedGaugeMap (X : ChainPoint L m k)
    (T : LevelForms L m k →ₗ[ℝ] edgeFormSpace L m k k) : Prop :=
  ∀ ξ, (T ξ : Edge L m k k → ComplexMatrix2) = shiftedGaugeValues X ξ
def shiftedGaugeMap (X : ChainPoint L m k) : LevelForms L m k →ₗ[ℝ] edgeFormSpace L m k k :=
  Classical.epsilon (IsShiftedGaugeMap X)
def gaugeCorrection (X : ChainPoint L m k) (ξ : LevelForms L m k) : Vertex L m k 0 → ComplexMatrix2 :=
  extendByZero (chainDrift X ξ k)
def chainBracket (X : ChainPoint L m k) (f : Vertex L m k 0 → ComplexMatrix2) (ξ : LevelValues L m k) :
    LevelValues L m k :=
  (bracketTerm X.fine f ξ.1, fun i => extendOddly fun e =>
    open Classical in
      if he : e.IsPositivelyOriented then
        (Complex.I / 2) • ⁅restrictVertexFunction (i + 1) f e.source +
          ComplexMatrix2.conjugateBy (X.noise i ⟨e, he⟩) (restrictVertexFunction (i + 1) f e.source), ξ.2 i e⁆
      else 0)
def topLog (X : ChainPoint L m k) (ξ : LevelForms L m k)
    (e : PositiveEdge L m k k) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (levelField (expMove ξ X) k e.1 * (levelField X k e.1)⁻¹)
def topSecondVariation (X : ChainPoint L m k) (ξ η : LevelForms L m k) :
    PositiveEdge L m k k → ComplexMatrix2 :=
  fun e => deriv (fun s : ℝ => deriv (fun t : ℝ => topLog X (s • ξ + t • η) e) 0) 0
end RunningCouplingSlope
end YangMills.Construction
end
