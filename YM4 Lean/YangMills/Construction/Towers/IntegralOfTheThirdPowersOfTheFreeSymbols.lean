import YangMills.Construction.Conventions.RealPowerAndLogarithm
import YangMills.Construction.Towers.TheFreePropagatorsAndTheirRoots
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.Tower.FreeResolvents.CubicSumIntegral
open YangMills.Construction.PeriodicOperators (toComplexVec imStrip)
open YangMills.Construction.Tower.PlaneWaves
open YangMills.Construction.RealPower (rpowPos)
def decayMajorant (q : Fin 4 → ℝ) : ℝ :=
  ((1 + 4 / Real.pi ^ 2 * ∑ ν, q ν ^ 2) ^ 3)⁻¹
def cubicBound : ℝ :=
  (10 / 9) ^ 3 * ((2 * Real.pi) ^ 4)⁻¹ * ∫ q, decayMajorant q
def cubicResolventSum (L k : ℕ) (ϑ : Fin 4 → ℂ) (κ : InfiniteLattice.AmbientSpace) : ℝ :=
  ∑ m ∈ freqBox L k, rpowPos ‖shiftedSymbolPow L k (-1) (shiftedFreq (toComplexVec κ + ϑ) m)‖ 3
def Claim : Prop :=
  Integrable decayMajorant ∧
    ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ ϑ ∈ imStrip (1 / 8),
      Continuous (cubicResolventSum L k ϑ) ∧
        ((2 * Real.pi) ^ 4)⁻¹ * ∫ κ in Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi),
          cubicResolventSum L k ϑ κ ≤ cubicBound
end YangMills.Construction.Tower.FreeResolvents.CubicSumIntegral
end
