import YangMills.Construction.Towers.PlaneWavePropagatorCalculusFacts
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace FinestFourierSums
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (castVec intShift)
open YangMills.Construction.Tower.PlaneWaves (VertexClass fourierCoeff freqBox shiftedFreq)
open YangMills.Construction.Tower.PlaneWaveCalculus (integerWave tracelessPairing expWave)
def IsIntPeriodic {V : Type} (L k : ℕ) (g : FullSpace.Vertex L k 0 → V) : Prop :=
  ∀ (v : Fin 4 → ℤ) (x : FullSpace.Vertex L k 0), g (FullSpace.vertexImage (intShift v) x) = g x
structure FourierFacts (L k : ℕ) : Prop where
  finite_vertexClass : Finite (VertexClass L k)
  coe_vertexImage : ∀ (v : Fin 4 → ℤ) (x : FullSpace.Vertex L k 0),
    ((FullSpace.vertexImage (intShift v) x : FullSpace.Vertex L k 0) : AmbientSpace) =
      (x : AmbientSpace) + castVec v
  integerWave_periodic : ∀ m : Fin 4 → ℤ,
    IsIntPeriodic L k fun x : FullSpace.Vertex L k 0 => integerWave m (x : AmbientSpace)
  expWave_mul_integerWave : ∀ (κ : Fin 4 → ℂ) (m : Fin 4 → ℤ) (x : AmbientSpace),
    expWave κ x * integerWave m x = expWave (shiftedFreq κ m) x
  orthonormal : ∀ m ∈ freqBox L k, ∀ m' ∈ freqBox L k,
    ((finestMesh L k ^ 4 : ℝ) : ℂ) * ∑ᶠ d : VertexClass L k,
        conj (integerWave m (Quot.out d : FullSpace.Vertex L k 0)) *
          integerWave m' (Quot.out d : FullSpace.Vertex L k 0) =
      if m = m' then 1 else 0
  span : ∀ φ : FullSpace.Vertex L k 0 → ℂ, IsIntPeriodic L k φ →
    ∃ z : (Fin 4 → ℤ) → ℂ, ∀ x : FullSpace.Vertex L k 0,
      φ x = ∑ m ∈ freqBox L k, z m * integerWave m (x : AmbientSpace)
  expansion : ∀ g : FullSpace.Vertex L k 0 → Matrices.ComplexMatrix2, IsIntPeriodic L k g →
    ∀ x : FullSpace.Vertex L k 0,
      g x = ∑ m ∈ freqBox L k, integerWave m (x : AmbientSpace) • fourierCoeff L k g m
  norm_sq : ∀ c : Fin 3 × FullSpace.Vertex L k 0 → ℂ,
    (∀ a, IsIntPeriodic L k fun x => c (a, x)) →
    finestMesh L k ^ 4 * ∑ a, ∑ᶠ d : VertexClass L k, ‖c (a, Quot.out d)‖ ^ 2 =
      ∑ m ∈ freqBox L k, pauliNorm (fourierCoeff L k (ofPauliCoeffs c) m) ^ 2
  pairing_eq : ∀ c c' : Fin 3 × FullSpace.Vertex L k 0 → ℂ,
    (∀ a, IsIntPeriodic L k fun x => c (a, x)) → (∀ a, IsIntPeriodic L k fun x => c' (a, x)) →
    ((finestMesh L k ^ 4 : ℝ) : ℂ) *
        ∑ a, ∑ᶠ d : VertexClass L k, c (a, Quot.out d) * c' (a, Quot.out d) =
      ∑ m ∈ freqBox L k,
        tracelessPairing (fourierCoeff L k (ofPauliCoeffs c) m)
          (fourierCoeff L k (ofPauliCoeffs c') (-m))
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → FourierFacts L k
end FinestFourierSums
end Tower
end YangMills.Construction
end
