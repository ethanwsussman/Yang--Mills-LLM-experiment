import YangMills.Construction.Towers.CompositionWithAStepOfTheCriticalBranch
import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import YangMills.Construction.Towers.SignsOfTheResponseOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.Tempered.OneStep
open Tower
open PeriodicOperators (colourEdges toComplexVec)
open Tower.PlaneWaves (edgeFourierCoeff freqBox shiftedFreq)
open Tower.PlaneWaveCalculus (topEdgeComponent expWave)
open Tower.ResponseProperties (responseSymbolForm)
open Tower.CriticalBranchResponse (meshScaledResponse)
variable {L : ℕ}
def topLevelForm (L n k : ℕ) (B : UnitEdge L n → Matrices.ComplexMatrix2) :
    Tower.Edge L n k k → Matrices.ComplexMatrix2 :=
  B ∘ topEdgeEquiv L n k
def stepPushforward (hL : 0 < L) (n i : ℕ) (B : UnitEdge L n → Matrices.ComplexMatrix2) :
    UnitEdge L (n + 1) → Matrices.ComplexMatrix2 :=
  transportTotal (stepEdgeEquiv hL n i)
    (crossingSmoothingIter L n (i + 1) i
      (meshScaledResponse L n (i + 1) (topLevelForm L n (i + 1) B) :
        Tower.Edge L n (i + 1) 0 → Matrices.ComplexMatrix2))
def complexStepPushforward (hL : 0 < L) (n i : ℕ) (B : UnitEdge L n → Matrices.ComplexMatrix2) :
    UnitEdge L (n + 1) → Matrices.ComplexMatrix2 :=
  stepPushforward hL n i (realComponent B) + Complex.I • stepPushforward hL n i (imagComponent B)
def crossingPoint (w : Fin 4 → ℤ) (t : ℕ) (ρ : Fin 4) : InfiniteLattice.AmbientSpace :=
  fun ν => (w ν : ℝ) + if ν = ρ then (t : ℝ) else 0
def stepMean (L i : ℕ) (ρ : Fin 4) (q : Fin 4 → ℂ) : ℂ :=
  ((L : ℂ) ^ (5 * i))⁻¹ * ∑ w ∈ freqBox L i, ∑ t ∈ Finset.range (L ^ i),
    expWave q (finestMesh L (i + 1) • crossingPoint w t ρ)
def responseCoeff (L k : ℕ) (κ : Fin 4 → ℂ) (ρ μ : Fin 4) (m : Fin 4 → ℤ) : ℂ :=
  Classical.epsilon fun c : ℂ => ∀ (a : Fin 3) (z : (colourEdges L k k).UnitQuot → ℂ),
    (∀ ν, topEdgeComponent L k z ν = if ν = μ then Matrices.ComplexMatrix2.pauliFamily a else 0) →
      edgeFourierCoeff L k (responseSymbolForm L k κ z) ρ m = c • Matrices.ComplexMatrix2.pauliFamily a
open Classical in
def stepEntry (L i : ℕ) (m' : Fin 4 → ℤ) (κ : Fin 4 → ℂ) (ρ μ : Fin 4) : ℂ :=
  ∑ m ∈ (freqBox L (i + 1)).filter (fun m => ∀ ν, (L : ℤ) ∣ m ν - m' ν),
    stepMean L i ρ (shiftedFreq κ m) * responseCoeff L (i + 1) κ ρ μ m
def residueBox (L : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Ico 0 (L : ℤ)
def rescaledFreq (L : ℕ) (κ : Fin 4 → ℂ) (m' : Fin 4 → ℤ) : Fin 4 → ℂ :=
  fun ρ => shiftedFreq κ m' ρ / (L : ℂ)
def rescaledMomentum (L : ℕ) (p : InfiniteLattice.AmbientSpace) (m' : Fin 4 → ℤ) :
    InfiniteLattice.AmbientSpace :=
  fun ρ => (p ρ + 2 * Real.pi * (m' ρ : ℝ)) / (L : ℝ)
def stepSymbolArray (L i : ℕ) (π : SymbolArray) : SymbolArray :=
  fun μ ν κ => (L : ℂ) ^ 2 * ∑ m' ∈ residueBox L, ∑ ρ, ∑ σ,
    stepEntry L i m' κ ρ μ * π ρ σ (rescaledFreq L κ m') * stepEntry L i (-m') (-κ) σ ν
end YangMills.Construction.PeriodicOperators.Tempered.OneStep
end
