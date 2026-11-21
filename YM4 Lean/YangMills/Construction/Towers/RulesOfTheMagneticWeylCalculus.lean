import YangMills.Construction.Towers.TheDensityOfAnAbelianField
import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tower.UnitLatticeL2 Tower.UnitaryCombinations Tower.AbelianFieldDensity OneLoopNotation
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (torusAverage castVec)
namespace Tower
namespace MagneticWeyl
def boundedMagneticWeyl (L : ℕ) (φ : ℝ) (m : Fin 4 → ℤ) :
    BddOpBetween (ScalarL2 L) (ScalarL2 L) :=
  (magneticWeyl L φ m).mkContinuous 1 fun v => by
    rw [(magneticWeyl_isUnitary φ m).2 v, one_mul]
def componentwise (N : ℕ) {L : ℕ} (V : ScalarL2 L →ₗ[ℂ] ScalarL2 L) :
    BddOpBetween (VectorL2 L N) (VectorL2 L N) :=
  matMulUnitaryOp (1 : Matrix (Fin N) (Fin N) ℂ) V
def TranslationIdentities (L : ℕ) (φ : ℝ) : Prop :=
  (∀ (v : FullSpace.Vertex L 0 0 → ℂ) (x : FullSpace.Vertex L 0 0),
    FullSpace.chargedShift (halfFluxAngle L φ) 1 v x =
        Complex.exp (Complex.I * (φ : ℂ) * (((x : AmbientSpace) 0 : ℝ) : ℂ)) *
          v (x + InfiniteLattice.axisStep _ 1) ∧
      ∀ μ : Fin 4, μ ≠ 1 →
        FullSpace.chargedShift (halfFluxAngle L φ) μ v x = v (x + InfiniteLattice.axisStep _ μ)) ∧
  (∀ μ : Fin 4,
    IsUnitaryOp
        ((magneticTranslation L φ μ).toLinearEquiv : ScalarL2 L →ₗ[ℂ] ScalarL2 L) ∧
      ∀ (v : ScalarL2 L) (x : FullSpace.Vertex L 0 0),
        magneticTranslation L φ μ v x 0 =
          FullSpace.chargedShift (halfFluxAngle L φ) μ (fun y => v y 0) x) ∧
  (∀ v : ScalarL2 L,
    magneticTranslation L φ 0 (magneticTranslation L φ 1 v) =
      Complex.exp (Complex.I * (φ : ℂ)) • magneticTranslation L φ 1 (magneticTranslation L φ 0 v)) ∧
  ∀ μ ν : Fin 4, μ ≠ ν → ¬(μ = 0 ∧ ν = 1) → ¬(μ = 1 ∧ ν = 0) → ∀ v : ScalarL2 L,
    magneticTranslation L φ μ (magneticTranslation L φ ν v) =
      magneticTranslation L φ ν (magneticTranslation L φ μ v)
def WeylCommutation (L : ℕ) (φ : ℝ) : Prop :=
  ∀ m m' : Fin 4 → ℤ,
    (∀ v : ScalarL2 L, magneticWeyl L φ m (magneticWeyl L φ m' v) =
      Complex.exp (Complex.I / 2 * (φ : ℂ) * (symplecticForm m m' : ℂ)) • magneticWeyl L φ (m + m') v) ∧
    opAdjoint (boundedMagneticWeyl L φ m) = boundedMagneticWeyl L φ (-m) ∧
    matrixAtZero (boundedMagneticWeyl L φ m) 0 0 = (kronecker m 0 : ℂ)
section Symbols
variable {N' N'' N''' : ℕ} [NeZero N'] [NeZero N''] [NeZero N''']
def QuantRules (L : ℕ) (φ : ℝ) (s : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) : Prop :=
  opNormOf (weylQuant L φ s) ≤ weightedCoeffNorm 0 s ∧
  IsWeylSymbol (pointwiseAdjoint s) ∧
  opAdjoint (weylQuant L φ s) = weylQuant L φ (pointwiseAdjoint s) ∧
  (∀ m : Fin 4 → ℤ, fourierCoeff s m =
    matrixAtZero ((componentwise N' (magneticWeyl L φ (-m))).comp (weylQuant L φ s))) ∧
  ∀ r : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ, IsWeylSymbol r →
    weylQuant L φ s = weylQuant L φ r → s = r
def QuantTrace (L : ℕ) (φ : ℝ) (s : AmbientSpace → Matrix (Fin N') (Fin N') ℂ) : Prop :=
  vecTraceAt (weylQuant L φ s) 0 = Matrices.RectangularMatrix.diagSum (fourierCoeff s 0) ∧
  Matrices.RectangularMatrix.diagSum (fourierCoeff s 0) =
    torusAverage fun q => Matrices.RectangularMatrix.diagSum (s q)
def MoyalProductRules (L : ℕ) (φ : ℝ) (s : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ)
    (s' : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ) : Prop :=
  (∀ j : ℕ, j ≤ 3 →
    Summable (fun m => Matrices.RectangularMatrix.opNormValue (moyalCoeff φ s s' m) *
      (1 + TorusMetric.euclidNormVec (castVec m)) ^ j) ∧
    ∑' m, Matrices.RectangularMatrix.opNormValue (moyalCoeff φ s s' m) *
      (1 + TorusMetric.euclidNormVec (castVec m)) ^ j ≤
        weightedCoeffNorm j s * weightedCoeffNorm j s') ∧
  IsWeylSymbol (moyalProduct φ s s') ∧
  (∀ j : ℕ, j ≤ 3 →
    weightedCoeffNorm j (moyalProduct φ s s') ≤ weightedCoeffNorm j s * weightedCoeffNorm j s') ∧
  (weylQuant L φ s).comp (weylQuant L φ s') = weylQuant L φ (moyalProduct φ s s')
def MoyalConstantFactor (φ : ℝ) (s : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) : Prop :=
  ∀ (M : ℕ) [NeZero M],
    (∀ c : Matrix (Fin N'') (Fin M) ℂ, moyalProduct φ s (fun _ => c) = fun q => s q * c) ∧
    ∀ c : Matrix (Fin M) (Fin N') ℂ, moyalProduct φ (fun _ => c) s = fun q => c * s q
def moyalRemainder (φ : ℝ) (s : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ)
    (s' : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ) (q : AmbientSpace) :
    Matrix (Fin N') (Fin N''') ℂ :=
  moyalProduct φ s s' q - s q * s' q + (Complex.I / 2 * (φ : ℂ)) • poissonBracket s s' q +
    ((1 / 8 : ℂ) * (φ : ℂ) ^ 2) • secondPoissonBracket s s' q
def MoyalSecondOrder (φ : ℝ) (s : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ)
    (s' : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ) : Prop :=
  HasAbsSummableFourier (moyalRemainder φ s s') ∧
  weightedCoeffNorm 0 (moyalRemainder φ s s') ≤
    1 / 48 * |φ| ^ 3 * weightedCoeffNorm 3 s * weightedCoeffNorm 3 s'
end Symbols
end MagneticWeyl
open MagneticWeyl in
def MagneticWeylCalculusRules : Prop :=
  ∀ (L : ℕ) (φ : ℝ),
    TranslationIdentities L φ ∧ WeylCommutation L φ ∧
    (∀ (N' N'' : ℕ) [NeZero N'] [NeZero N''] (s : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ),
      IsWeylSymbol s → QuantRules L φ s ∧ MoyalConstantFactor φ s) ∧
    (∀ (N' : ℕ) [NeZero N'] (s : AmbientSpace → Matrix (Fin N') (Fin N') ℂ), IsWeylSymbol s →
      QuantTrace L φ s) ∧
    ∀ (N' N'' N''' : ℕ) [NeZero N'] [NeZero N''] [NeZero N''']
      (s : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ)
      (s' : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ),
      IsWeylSymbol s → IsWeylSymbol s' → MoyalProductRules L φ s s' ∧ MoyalSecondOrder φ s s'
end Tower
end YangMills.Construction
end
