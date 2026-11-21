import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.UnitaryCombinations YangMills.Construction.OneLoopNotation
open YangMills.Construction.PeriodicOperators (imStrip toComplexVec castVec matrixCoeffs
  HolomorphicOnEntrywise BoundedOnEntrywise)
noncomputable section
namespace YangMills.Construction.Tower.MagneticWeyl
open InfiniteLattice (AmbientSpace)
variable {N' N'' N''' : ℕ}
def IsFiniteFourierSymbol [NeZero N'] [NeZero N'']
    (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) : Prop :=
  IsWeylSymbol a ∧ {m | fourierCoeff a m ≠ 0}.Finite
namespace FluxZeroCalculus
def realRestrict (a : (Fin 4 → ℂ) → Matrix (Fin N') (Fin N'') ℂ) :
    AmbientSpace → Matrix (Fin N') (Fin N'') ℂ :=
  fun q => a (toComplexVec q)
def IsLatticePeriodicOnStrip (υ : ℝ) (a : (Fin 4 → ℂ) → Matrix (Fin N') (Fin N'') ℂ) : Prop :=
  ∀ κ ∈ imStrip υ, ∀ p ∈ InfiniteLattice.latticeSubgroup (2 * Real.pi),
    a (κ + toComplexVec p) = a κ
def IsAnalyticNearStrip (υ : ℝ) (a : (Fin 4 → ℂ) → Matrix (Fin N') (Fin N'') ℂ) : Prop :=
  ∃ O, imStrip υ ⊆ O ∧ HolomorphicOnEntrywise matrixCoeffs O a
def stripSupNorm [NeZero N'] [NeZero N''] (υ : ℝ)
    (a : (Fin 4 → ℂ) → Matrix (Fin N') (Fin N'') ℂ) : ℝ :=
  ⨆ κ : imStrip υ, Matrices.RectangularMatrix.opNormValue (a κ)
def expWeight (υ : ℝ) (m : Fin 4 → ℤ) : ℝ := Real.exp (-υ * ∑ μ, |(m μ : ℝ)|)
def weightedTerm (υ : ℝ) (m : Fin 4 → ℤ) : ℝ :=
  expWeight υ m * (1 + TorusMetric.euclidNormVec (castVec m)) ^ 3
def StripSymbolBounds (N' N'' : ℕ) [NeZero N'] [NeZero N''] : Prop :=
  ∀ (υ : ℝ) (a : (Fin 4 → ℂ) → Matrix (Fin N') (Fin N'') ℂ), 0 < υ →
    IsLatticePeriodicOnStrip υ a → IsAnalyticNearStrip υ a →
    BoundedOnEntrywise matrixCoeffs (imStrip υ) a →
    IsWeylSymbol (realRestrict a) ∧
      (∀ m, Matrices.RectangularMatrix.opNormValue (fourierCoeff (realRestrict a) m) ≤
        stripSupNorm υ a * expWeight υ m) ∧
      Summable (weightedTerm υ) ∧
      weightedCoeffNorm 3 (realRestrict a) ≤ stripSupNorm υ a * ∑' m, weightedTerm υ m
def latticePoint (L : ℕ) (m : Fin 4 → ℤ) : FullSpace.Vertex L 0 0 :=
  ⟨castVec m, m, fun μ => by simp [castVec, meshAt]⟩
def MagneticWeylIsTranslation (L : ℕ) : Prop :=
  ∀ (m x : Fin 4 → ℤ) (w : ScalarL2 L),
    magneticWeyl L 0 m w (latticePoint L x) = w (latticePoint L (x + m))
def MoyalProductIsPointwise (N' N'' N''' : ℕ) [NeZero N'] [NeZero N''] [NeZero N'''] : Prop :=
  ∀ (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) (b : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ),
    IsWeylSymbol a → IsWeylSymbol b → moyalProduct 0 a b = fun q => a q * b q
def planeWaveVec (q : AmbientSpace) (v : EuclideanSpace ℂ (Fin N'')) (x : Fin 4 → ℤ) :
    EuclideanSpace ℂ (Fin N'') :=
  fourierChar x q • v
def ActsOnPlaneWavesByMultiplication (N' N'' : ℕ) [NeZero N'] [NeZero N''] : Prop :=
  ∀ a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ, IsFiniteFourierSymbol a →
    ∀ (q : AmbientSpace) (v : EuclideanSpace ℂ (Fin N'')) (x : Fin 4 → ℤ),
      ∑ᶠ m, Matrix.toEuclideanLin (fourierCoeff a m) (planeWaveVec q v (x + m)) =
        fourierChar x q • Matrix.toEuclideanLin (a q) v
def FiniteTranslationSumsAreQuantized (L N' N'' : ℕ) [NeZero N'] [NeZero N''] : Prop :=
  ∀ (S : Finset (Fin 4 → ℤ)) (t : (Fin 4 → ℤ) → Matrix (Fin N') (Fin N'') ℂ),
    IsFiniteFourierSymbol (fun q => ∑ m ∈ S, fourierChar m q • t m) ∧
      ∑ m ∈ S, matMulUnitaryOp (t m) (magneticWeyl L 0 m) =
        weylQuant L 0 fun q => ∑ m ∈ S, fourierChar m q • t m
def InverseOfFiniteFourierSymbol (L N' : ℕ) [NeZero N'] : Prop :=
  ∀ a : AmbientSpace → Matrix (Fin N') (Fin N') ℂ, IsFiniteFourierSymbol a → (∀ q, IsUnit (a q)) →
    IsWeylSymbol (fun q => (a q)⁻¹) ∧
      (weylQuant L 0 a).comp (weylQuant L 0 fun q => (a q)⁻¹) =
        ContinuousLinearMap.id ℂ (VectorL2 L N') ∧
      (weylQuant L 0 fun q => (a q)⁻¹).comp (weylQuant L 0 a) =
        ContinuousLinearMap.id ℂ (VectorL2 L N')
def Claim : Prop :=
  ∀ (L N' N'' N''' : ℕ) [NeZero N'] [NeZero N''] [NeZero N'''],
    StripSymbolBounds N' N'' ∧
      MagneticWeylIsTranslation L ∧
      MoyalProductIsPointwise N' N'' N''' ∧
      ActsOnPlaneWavesByMultiplication N' N'' ∧
      FiniteTranslationSumsAreQuantized L N' N'' ∧
      InverseOfFiniteFourierSymbol L N'
end FluxZeroCalculus
end YangMills.Construction.Tower.MagneticWeyl
end
