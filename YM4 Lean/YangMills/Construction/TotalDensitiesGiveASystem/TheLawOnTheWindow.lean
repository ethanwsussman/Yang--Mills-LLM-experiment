import YangMills.Construction.SystemsWithFiveBounds.SystemWithFiveBounds
import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
structure WindowScaleModulus (d₀ : ℝ) (η : ℝ → ℝ) : Prop where
  scale_mem : d₀ ∈ Ioo (0 : ℝ) 1
  modulus_monotoneOn : MonotoneOn η (Ioc 0 d₀)
  modulus_mem : ∀ d ∈ Ioc 0 d₀, η d ∈ Icc (0 : ℝ) (1 / 3)
  modulus_tendsto_zero : Tendsto η (𝓝[>] 0) (𝓝 0)
def TwoPointLawOnWindowAt (p : TorusLumps.StepParameters) (Bs g θ d₀ : ℝ) (η : ℝ → ℝ) (K₀ : ℝ → ℕ) : Prop :=
  ∀ d ∈ Ioc 0 d₀, ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePoint p Bs g K β → K₀ d ≤ (K : ℕ) →
    ∀ ν ∈ InfiniteLattice.periodicGibbsSet p.side K β,
      ∀ f h : InfiniteLattice.AmbientSpace → ℝ, (f, h) ∈ TestFunctions.separatedPairsR4 d θ →
        ∃ t : ℝ, InfiniteLattice.smearedEnergyCumulant ν ![f, h] = (t : ℂ) ∧
          SystemsWithFiveBounds.SatisfiesTwoPointLaw η d t f h
def twoPointLawOnWindow : Prop :=
  HoldsAtAdmissibleParameters fun T y => ∀ Bs : ℝ, 2 * T.B ≤ Bs → ForSmallCoupling fun g =>
    ∀ θ ∈ Ioc (0 : ℝ) 1, ∃ (d₀ : ℝ) (η : ℝ → ℝ) (K₀ : ℝ → ℕ),
      WindowScaleModulus d₀ η ∧ TwoPointLawOnWindowAt (T.stepParameters y) Bs g θ d₀ η K₀
end YangMills.Construction.TotalDensities
end
