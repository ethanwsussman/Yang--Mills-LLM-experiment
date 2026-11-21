import YangMills.Construction.PeriodicOperators.LocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
section Kernels
variable (I I' : PeriodicData)
def IsPhaseCovariant (q : Fin 4 → ℂ) (K : I'.Carrier → I.Carrier → ℂ) : Prop :=
  ∀ (n : Fin 4 → ℤ) a b,
    K (I'.translate n a) (I.translate n b) =
      Complex.exp (Complex.I * bilinDot q (toComplexVec (castVec n))) * K a b
def VanishesOutsideRadius (R : ℝ) (K : I'.Carrier → I.Carrier → ℂ) : Prop :=
  ∀ a b, ¬ TorusMetric.euclidNormVec (I'.pos a - I.pos b) ≤ R → K a b = 0
def dephasedKernel (q : Fin 4 → ℂ) (K : I'.Carrier → I.Carrier → ℂ) : I'.Carrier → I.Carrier → ℂ :=
  fun a b => Complex.exp (-(Complex.I * bilinDot q (toComplexVec (I'.pos a)))) * K a b
structure IsFiniteRangeAllRates (Z : I'.Carrier → I.Carrier → ℂ) : Prop where
  periodic : IsPeriodicKernel I I' Z
  finiteRange : IsFiniteRange I I' Z
  decays : ∀ δ : ℝ, 0 < δ → IsDecayRate I I' Z δ
  summable : SymbolSummableOn I I' Z univ
def SymbolIsExponentialSum (Z : I'.Carrier → I.Carrier → ℂ) : Prop :=
  ∀ a b, ∃ (m : ℕ) (c : Fin m → ℂ) (y : Fin m → InfiniteLattice.AmbientSpace), ∀ k : Fin 4 → ℂ,
    fourierSymbol I I' Z k a b = ∑ j, c j * Complex.exp (Complex.I * bilinDot k (toComplexVec (y j)))
def SymbolIsEntire (Z : I'.Carrier → I.Carrier → ℂ) : Prop :=
  ∀ a b, Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) (univ : Set (Fin 4 → ℂ))
    fun k _ => fourierSymbol I I' Z k a b
def ActsOnBlochWaves (q : Fin 4 → ℂ) (K : I'.Carrier → I.Carrier → ℂ) : Prop :=
  ∀ (k : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ) (a : I'.Carrier),
    (Function.support fun b => K a b * blochWave I k φ b).Finite ∧
      applyKernel K (blochWave I k φ) a =
        blochWave I' (k + q)
          (applyKernel (quotSymbol I I' (dephasedKernel I I' q K) k) φ) a
end Kernels
open Classical in
def idKernel (I : PeriodicData) : I.Carrier → I.Carrier → ℂ :=
  fun a b => if a = b then 1 else 0
open Classical in
def quotOne (I : PeriodicData) : I.UnitQuot → I.UnitQuot → ℂ :=
  fun c d => if c = d then 1 else 0
def CovariantFiniteRange.Claim : Prop :=
  (∀ I : PeriodicData, IsPeriodic I →
    (∀ (y : InfiniteLattice.AmbientSpace) (r : ℝ), (nearIndices I y r).Finite) ∧
      IsPeriodicKernel I I (idKernel I) ∧ IsFiniteRange I I (idKernel I) ∧
      ∀ k : Fin 4 → ℂ, quotSymbol I I (idKernel I) k = quotOne I) ∧
    ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
      ∀ (q : Fin 4 → ℂ) (R : ℝ) (K : I'.Carrier → I.Carrier → ℂ),
        IsPhaseCovariant I I' q K → VanishesOutsideRadius I I' R K →
          IsFiniteRangeAllRates I I' (dephasedKernel I I' q K) ∧
            SymbolIsExponentialSum I I' (dephasedKernel I I' q K) ∧
            SymbolIsEntire I I' (dephasedKernel I I' q K) ∧
            ActsOnBlochWaves I I' q K
end YangMills.Construction.PeriodicOperators
end
