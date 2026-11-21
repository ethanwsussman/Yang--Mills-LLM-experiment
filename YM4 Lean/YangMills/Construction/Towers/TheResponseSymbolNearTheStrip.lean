import YangMills.Construction.Towers.TheSymbolOfTheSecondDifferentialOfTheFunctional
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.ResponseSymbolNearStrip
open PeriodicOperators
open BackgroundFieldResponse (responseKernel responseDefect)
open FullSpace (planeWaveOfConstant defectOfWave responseSymbol backgroundResponseSymbol
  coarseResponseSymbol sourceResponseSymbol crossingSmoothingTranspose)
def IsTracelessTuple (ε : Fin 4 → Matrices.ComplexMatrix2) : Prop :=
  ∀ ρ, ε ρ ∈ Matrices.ComplexMatrix2.traceless
def EntriesHolomorphicBoundedOn {C : Type} (O : Set (Fin 4 → ℂ))
    (a : (Fin 4 → ℂ) → C → ℂ) : Prop :=
  HolomorphicOnEntrywise (n := 4) (fun (φ : C → ℂ) c => φ c) O a ∧
    BoundedOnEntrywise (fun (φ : C → ℂ) c => φ c) O a
structure HoldsOn (L k : ℕ) (hL : 0 < L) (O : Set (Fin 4 → ℂ)) : Prop where
  map_smul_add : ∀ p ∈ O, ∀ (c : ℂ) (ε ε' : Fin 4 → Matrices.ComplexMatrix2), IsTracelessTuple ε →
    IsTracelessTuple ε' →
      responseSymbol L k hL p (c • ε + ε') =
        c • responseSymbol L k hL p ε + responseSymbol L k hL p ε'
  symbol_entries : ∀ ε, IsTracelessTuple ε →
    EntriesHolomorphicBoundedOn O fun p => responseSymbol L k hL p ε
  background_entries : ∀ ε, IsTracelessTuple ε →
    EntriesHolomorphicBoundedOn O fun p => backgroundResponseSymbol L k p ε
  source_entries : ∀ ε, IsTracelessTuple ε →
    EntriesHolomorphicBoundedOn O fun p => sourceResponseSymbol L k p ε
  coarse_entries : ∀ ε, IsTracelessTuple ε →
    EntriesHolomorphicBoundedOn O fun p => coarseResponseSymbol L k p ε
  background_wave : ∀ p ∈ O, ∀ ε, IsTracelessTuple ε →
    (∀ j, ApplySummableAt (responseKernel L k) (planeWaveOfConstant L k p ε) j) ∧
      blochWave (colourEdges L k 0) p (backgroundResponseSymbol L k p ε) =
        ((finestMesh L k : ℝ) : ℂ) • applyKernel (responseKernel L k) (planeWaveOfConstant L k p ε)
  source_wave : ∀ p ∈ O, ∀ ε, IsTracelessTuple ε →
    blochWave (colourEdges L k 0) p (sourceResponseSymbol L k p ε) =
      crossingSmoothingTranspose L k (defectOfWave L k p ε)
  coarse_wave : ∀ p ∈ O, ∀ ε, IsTracelessTuple ε →
    (∀ j, ApplySummableAt (responseDefect L k) (planeWaveOfConstant L k p ε) j) ∧
      blochWave (colourEdges L k k) p (coarseResponseSymbol L k p ε) =
        defectOfWave L k p ε
def ResponseSymbolHolomorphicNearStrip : Prop :=
  ∃ δ₀ ∈ FreeStrip.halfSupRate, ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L →
    ∀ k : ℕ, 1 ≤ k → ExistsOpenNear IsOpen (imStrip (2 * δ₀)) (HoldsOn L k hL)
end YangMills.Construction.Tower.ResponseSymbolNearStrip
end
