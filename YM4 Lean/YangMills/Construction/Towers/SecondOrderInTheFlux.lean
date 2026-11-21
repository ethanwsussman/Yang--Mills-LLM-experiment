import YangMills.Construction.Towers.HolomorphicSymbolsAndTheCalculusAtFluxZero
import YangMills.Construction.Towers.TheDensityOfAnAbelianField
import Mathlib
set_option autoImplicit false
open Filter Asymptotics
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.MagneticWeyl
namespace FluxSecondOrder
open InfiniteLattice (AmbientSpace)
open Massive (resolvent latticeSymbol)
open PeriodicOperators (torusAverage toComplexVec castVec)
open OperatorCalculus (addScalar opLog)
open UnitLatticeL2 (IsBoundedBelowBy)
variable {n : ℕ} [NeZero n]
def resolventAtReal (z : ℝ) (x : AmbientSpace) : ℂ := resolvent (z : ℂ) (toComplexVec x)
def symbolSecondDerivFirst (x : AmbientSpace) : ℂ :=
  Massive.partialIn 0 (Massive.partialIn 0 latticeSymbol)
    (toComplexVec x)
def symbolSecondDerivSecond (x : AmbientSpace) : ℂ :=
  Massive.partialIn 1 (Massive.partialIn 1 latticeSymbol)
    (toComplexVec x)
structure Hypotheses (L : ℕ) (z D C : ℝ) (a₁ a₂ : AmbientSpace → Matrix (Fin n) (Fin n) ℂ)
    (a : ℝ → AmbientSpace → Matrix (Fin n) (Fin n) ℂ)
    (e : ℝ → AmbientSpace → Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : Prop where
  isFiniteFourierSymbol : IsFiniteFourierSymbol (a t)
  isHermitian : ∀ x, pointwiseAdjoint (a t) x = a t x
  fourierCoeff_eq_zero : ∀ m : Fin 4 → ℤ, D < TorusMetric.euclidNormVec (castVec m) →
    fourierCoeff (a t) m = 0
  eq_add : ∀ x, a t x = latticeSymbol (toComplexVec x) • (1 : Matrix (Fin n) (Fin n) ℂ) +
    (t : ℂ) • a₁ x + (t : ℂ) ^ 2 • a₂ x + e t x
  error_isWeylSymbol : IsWeylSymbol (e t)
  error_norm_le : weightedCoeffNorm 3 (e t) ≤ C * |t| ^ 3
  boundedBelow : IsBoundedBelowBy (addScalar (weylQuant L t (a t)) z) (z / 2)
def constantTerm (n : ℕ) [NeZero n] (z : ℝ) : ℂ :=
  torusAverage fun x => Matrices.RectangularMatrix.diagSum
    (Complex.log (latticeSymbol (toComplexVec x) + z) • (1 : Matrix (Fin n) (Fin n) ℂ))
def linearTerm (z : ℝ) (a₁ : AmbientSpace → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  torusAverage fun x => resolventAtReal z x * Matrices.RectangularMatrix.diagSum (a₁ x)
def quadraticTerm (z : ℝ) (a₁ a₂ : AmbientSpace → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  torusAverage fun x =>
    -(1 / 2) * resolventAtReal z x ^ 2 * Matrices.RectangularMatrix.diagSum (a₁ x ^ 2) +
      resolventAtReal z x * Matrices.RectangularMatrix.diagSum (a₂ x) +
      (n : ℂ) / 24 * resolventAtReal z x ^ 2 * symbolSecondDerivFirst x * symbolSecondDerivSecond x
def logTrace (L : ℕ) (z t : ℝ) (b : AmbientSpace → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  AbelianFieldDensity.vecTraceAt (opLog (addScalar (weylQuant L t b) z)) 0
end FluxSecondOrder
open FluxSecondOrder in
def FluxSecondOrder.Claim : Prop :=
  ∀ (L n : ℕ) [NeZero n] (z : ℝ), 0 < z →
    ∀ (D C r : ℝ) (a₁ a₂ : InfiniteLattice.AmbientSpace → Matrix (Fin n) (Fin n) ℂ)
      (a e : ℝ → InfiniteLattice.AmbientSpace → Matrix (Fin n) (Fin n) ℂ), 0 < r →
      (∀ t : ℝ, |t| ≤ r → Hypotheses L z D C a₁ a₂ a e t) →
      IsFiniteFourierSymbol a₁ ∧ IsFiniteFourierSymbol a₂ ∧
        Continuous a₁ ∧ Continuous a₂ ∧
        (fun t : ℝ => logTrace L z t (a t) -
            (constantTerm n z + (t : ℂ) * linearTerm z a₁ +
              (t : ℂ) ^ 2 * quadraticTerm z a₁ a₂)) =O[𝓝 0]
          fun t : ℝ => |t| ^ 3
end YangMills.Construction.Tower.MagneticWeyl
end
