import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import YangMills.Construction.ResponseInTheExpansion.OneStepToSecondOrder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ResponseInTheExpansion
open Classical
open MeasureTheory
def quadraticForm {I : Type} [Fintype I] (κ : Matrix I I ℝ) (G : I → imaginaryQuaternions) : ℝ :=
  (1 / 2) * ∑ a, ∑ b, κ a b * ∑ e : Fin 3, imaginaryComponent e (G a) * imaginaryComponent e (G b)
def kernelCycleTrace {I : Type} [Fintype I] {q : ℕ} (κ : Fin (q + 1) → Matrix I I ℝ) (Tc : Matrix I I ℝ)
    (s : Equiv.Perm (Fin (q + 1))) : ℝ :=
  Matrix.trace (List.ofFn fun i : Fin (q + 1) => κ (s i) * Tc).prod
def cyclicTraceSum {I : Type} [Fintype I] {q : ℕ} (κ : Fin (q + 1) → Matrix I I ℝ) (Tc : Matrix I I ℝ) : ℝ :=
  (3 / 2) * ∑ s ∈ (Finset.univ : Finset (Equiv.Perm (Fin (q + 1)))).filter (fun s => s 0 = 0),
    kernelCycleTrace κ Tc s
def quadraticFormCumulantsStatement : Prop :=
  ∀ (q : ℕ) (B : ℝ), 1 ≤ q → q ≤ 3 → ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : Set Ω) (I : Type) [Fintype I] (G : Ω → I → imaginaryQuaternions)
    (Tc : Matrix I I ℝ) (x ε Bg : ℝ) (κ : Fin (q + 1) → Matrix I I ℝ),
    MeasurableSet A → (∀ i, (κ i).IsSymm) →
    (∀ (a : I) (e : Fin 3), Measurable fun ω => imaginaryComponent e (G ω a)) →
    (∀ ω a e, |imaginaryComponent e (G ω a)| ≤ Bg) → 1 ≤ x → Tc.IsSymm → (∀ a b, |Tc a b| ≤ B) → 0 ≤ ε → ε ≤ 1 →
    (∀ (r : ℕ) (a : Fin r → I) (e : Fin r → Fin 3), r ≤ 2 * (q + 1) →
      |∫ ω, Set.indicator A (fun ω => ∏ i, imaginaryComponent (e i) (G ω (a i))) ω ∂μ -
        x ^ (-(r : ℝ) / 2) * wickPairingSum fun i i' => if e i = e i' then Tc (a i) (a i') else 0| ≤ ε) →
    ‖Cumulants.mixedCumulant μ (fun i => Set.indicator A fun ω => quadraticForm (κ i) (G ω)) -
        ((x ^ (-((q : ℝ) + 1)) * cyclicTraceSum κ Tc : ℝ) : ℂ)‖ ≤
      C * (∏ i, ∑ a, ∑ b, |κ i a b|) * ε
end ResponseInTheExpansion
end YangMills.Construction
end
