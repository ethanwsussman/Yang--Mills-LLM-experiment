import YangMills.Construction.OneLoopLaw.KernelsAndTensorFormOfASymbol
import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import YangMills.Construction.Towers.TheFamiliesOfTheTotalNormaliser
import YangMills.Construction.Towers.TheSymbolOfTheSecondDifferentialOfTheFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.NormaliserTempered
def SymbolFormula (L k : ℕ) (hL : 0 < L) (p : Fin 4 → ℂ) : Prop :=
  ∀ (a b : Fin 3) (μ ν : Fin 4),
    (if a = b then PeriodicOperators.Tempered.hessianSymbol L (Tower.logNormaliserFamily L k) μ ν p
      else 0) =
      Tower.FullSpace.secondVariationSymbol L k hL p
        (Tower.FullSpace.responseSymbol L k hL p (Tower.FullSpace.axisPauliElement μ a))
        (Tower.FullSpace.responseSymbol L k hL (-p) (Tower.FullSpace.axisPauliElement ν b))
def SymbolOnStrips (δ₀ : ℝ) (L k : ℕ) (hL : 0 < L) : Prop :=
  ∀ δ : ℝ, Tower.FullSpace.IsJointInvertibilityWidth L k hL δ →
    ∀ p ∈ PeriodicOperators.imStrip δ ∩ PeriodicOperators.imStrip (2 * δ₀),
      p ∈ PeriodicOperators.Tempered.symbolDomain L (Tower.logNormaliserFamily L k) ∧
        SymbolFormula L k hL p
def SymbolAsymptotics (L k : ℕ) (hL : 0 < L) : Prop :=
  ∃ C : ℝ, ∃ N ∈ nhds (0 : Fin 4 → ℂ),
    N ⊆ PeriodicOperators.Tempered.symbolDomain L (Tower.logNormaliserFamily L k) ∩
        Tower.FullSpace.freePolarizationDomain L k hL ∧
      ∀ p ∈ N, ∀ μ ν : Fin 4,
        ‖PeriodicOperators.Tempered.hessianSymbol L (Tower.logNormaliserFamily L k) μ ν p -
            Tower.FullSpace.freePolarizationMatrix L k hL p μ ν‖ ≤
          C * Tower.ResponseProperties.euclidNorm p ^ 3
def TemperedAndStiffness : Prop :=
  ∃ δ₀ ∈ Tower.FreeStrip.halfSupRate, ∀ (L : ℕ) (hL : 0 < L),
    Conventions.IsAdmissibleBlockingFactor L →
    ∀ k : ℕ, 1 ≤ k →
      PeriodicOperators.Tempered.IsTemperedFunctional L (Tower.logNormaliserFamily L k) ∧
        SymbolOnStrips δ₀ L k hL ∧ SymbolAsymptotics L k hL ∧
        ((OneLoopLaw.FunctionalStiffness.stiffnessConstant hL (Tower.logNormaliserFamily L k) : ℝ) : ℂ) =
          -OneLoopLaw.TemperedStiffness.secondPartialAtZero
            (Tower.FullSpace.freePolarizationEntry L k hL 0 1) 0 1
end YangMills.Construction.Tower.NormaliserTempered
end
