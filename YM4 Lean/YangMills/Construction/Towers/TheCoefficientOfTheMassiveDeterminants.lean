import YangMills.Construction.Towers.HolomorphicSymbolsAndTheCalculusAtFluxZero
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (torusAverage toComplexVec)
noncomputable section
namespace YangMills.Construction.Tower
namespace Massive
def quadraticIntegrand (τ₁ τ₂ : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ) (w : ℝ) (k : AmbientSpace) : ℂ :=
  1 / 2 * Massive.resolvent w (toComplexVec k) ^ 2 * ((τ₁ k) ^ 2).trace -
    1 / 12 * Massive.resolvent w (toComplexVec k) ^ 2 *
        partialIn 0 (partialIn 0 latticeSymbol) (toComplexVec k) *
        partialIn 1 (partialIn 1 latticeSymbol) (toComplexVec k) -
      Massive.resolvent w (toComplexVec k) * (τ₂ k).trace
def linearIntegrand (w : ℝ) (k : AmbientSpace) : ℂ :=
  Massive.resolvent w (toComplexVec k) *
    (axisSymbol 0 (toComplexVec k) + axisSymbol 1 (toComplexVec k))
def uvDeviation {L : ℕ} (hL : 0 < L) (w : ℝ) : ℝ :=
  |massiveStiffness hL w - 11 / (6 * Real.pi ^ 2) * Real.log (1 / w)| +
    |w * massiveStiffnessDeriv hL w| +
      |w ^ 2 * massiveStiffnessDeriv2 hL w|
def IsUVSupremum (M : ℝ) : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ hL : 0 < L,
    IsLUB (uvDeviation hL '' Set.Ioc 0 1) M
def uvConstant : ℝ := Classical.epsilon IsUVSupremum
end Massive
open MagneticWeyl (IsFiniteFourierSymbol)
open Massive
def MassiveStiffnessAsymptotics : Prop :=
  (∃ τ₁ τ₂ : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ,
      IsFiniteFourierSymbol τ₁ ∧ IsFiniteFourierSymbol τ₂ ∧
      (∀ k, (τ₁ k).IsHermitian) ∧ (∀ k, (τ₂ k).IsHermitian) ∧
      ((τ₁ 0) ^ 2).trace = 8 ∧
      ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ hL : 0 < L, ∀ w : ℝ, 0 < w →
        MassiveStiffnessExists hL w ∧
        (massiveStiffness hL w : ℂ) =
          8 * torusAverage (quadraticIntegrand τ₁ τ₂ w) + 1 / 2 * torusAverage (linearIntegrand w)) ∧
    (∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ hL : 0 < L,
      ContDiffOn ℝ 2 (massiveStiffness hL) (Set.Ioi 0)) ∧
    IsUVSupremum uvConstant ∧
    ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ hL : 0 < L, ∀ w : ℝ, 0 < w → w ≤ 1 →
      uvDeviation hL w ≤ uvConstant
end YangMills.Construction.Tower
end
