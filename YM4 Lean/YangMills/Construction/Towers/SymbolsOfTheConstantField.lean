import YangMills.Construction.Towers.HolomorphicSymbolsAndTheCalculusAtFluxZero
import YangMills.Construction.Towers.LogarithmsSectorsAndDensityDefs
import YangMills.Construction.Towers.TheCoefficientAsAResponseToAConstantField
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (toComplexVec castVec)
open UnitLatticeL2
open MagneticWeyl AbelianFieldDensity AbelianFieldDensity.SectorDecomposition
def scalarMultiplier (q : AmbientSpace) : Matrix (Fin 1) (Fin 1) ℂ :=
  Massive.latticeSymbol (toComplexVec q) • (1 : Matrix (Fin 1) (Fin 1) ℂ)
def faceRow (q : AmbientSpace) : Matrix (Fin 1) (Fin 4) ℂ :=
  Matrix.of fun _ =>
    ![1 - Complex.exp (Complex.I * (q 1 : ℂ)), Complex.exp (Complex.I * (q 0 : ℂ)) - 1, 0, 0]
def faceGram (q : AmbientSpace) : Matrix (Fin 4) (Fin 4) ℂ := (faceRow q)ᴴ * faceRow q
def neutralSectorSymbol (f : ℝ) (q : AmbientSpace) : Matrix (Fin 4) (Fin 4) ℂ :=
  Massive.latticeSymbol (toComplexVec q) • (1 : Matrix (Fin 4) (Fin 4) ℂ) +
    ((Real.cos f - 1 : ℝ) : ℂ) • faceGram q
structure ChargedSymbolExpansion (D C : ℝ) (τ₁ τ₂ : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ)
    (τ τr : ℝ → AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ) : Prop where
  linear_isFiniteFourierSymbol : IsFiniteFourierSymbol τ₁
  quadratic_isFiniteFourierSymbol : IsFiniteFourierSymbol τ₂
  linear_isHermitian : ∀ q, (τ₁ q).IsHermitian
  quadratic_isHermitian : ∀ q, (τ₂ q).IsHermitian
  isFiniteFourierSymbol : ∀ φ : ℝ, |φ| ≤ Real.pi → IsFiniteFourierSymbol (τ φ)
  isHermitian : ∀ φ : ℝ, |φ| ≤ Real.pi → ∀ q, pointwiseAdjoint (τ φ) q = τ φ q
  fourierCoeff_eq_zero : ∀ φ : ℝ, |φ| ≤ Real.pi → ∀ m : Fin 4 → ℤ,
    D < TorusMetric.euclidNormVec (castVec m) → MagneticWeyl.fourierCoeff (τ φ) m = 0
  eq_add : ∀ φ : ℝ, |φ| ≤ Real.pi → ∀ q,
    τ φ q = Massive.latticeSymbol (toComplexVec q) • (1 : Matrix (Fin 4) (Fin 4) ℂ) +
      (φ : ℂ) • τ₁ q + (φ : ℂ) ^ 2 • τ₂ q + τr φ q
  error_isWeylSymbol : ∀ φ : ℝ, |φ| ≤ Real.pi → IsWeylSymbol (τr φ)
  error_norm_le : ∀ φ : ℝ, |φ| ≤ Real.pi → weightedCoeffNorm 3 (τr φ) ≤ C * |φ| ^ 3
  massiveOp_eq : ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ f : ℝ, |f| ≤ Real.pi / 2 →
    ∀ v : VectorL2 L 4,
      AbelianFieldDensity.massiveOp (scaledLinearAngle L f) (edgeTensor v raisingPauli) =
        edgeTensor (weylQuant L (2 * f) (τ (2 * f)) v) raisingPauli
end YangMills.Construction.Tower.ConstantFieldSymbols
end
