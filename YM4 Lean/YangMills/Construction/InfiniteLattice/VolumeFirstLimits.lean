import YangMills.Construction.Continuum.SchwingerFunctions
import YangMills.Construction.PolymerActivities.FlowOfTheConstruction
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
open ParameterChoice FlowConstants PeriodicLattice.CubesOfStep
abbrev CutoffRemainders (a : FullChoice) : Type :=
  ∀ K : ℕ, FlowRemainders a.toChoiceUpToDegreeConstants K
def IsSeparatedC1cTuple {n : ℕ} (f : Fin n → AmbientSpace → ℝ) : Prop :=
  (∀ i, SchwingerFunctions.IsC1c (f i)) ∧ ∃ d : ℝ, TestFunctions.HasSeparatedSupportsR4 f d
structure VolumeFirstApproximants (T : DerivedConstants) (a : FullChoice)
    (s : PeriodicLattice.ActivityDomainKind) (ρ : CutoffRemainders a) (g : ℝ) where
  K : ℕ+ → ℕ+
  tendsto_K : Tendsto (fun k => (K k : ℕ)) atTop atTop
  β : ℕ+ → ℝ
  β_mem_window : ∀ k, β k ∈ flowFirstPassageWindow T a (K k) s (ρ (K k)) g
  ν : ∀ k, Measure (GaugeField (PeriodicLattice.meshSize a.L (((K k : ℕ)) : ℤ)))
  isInfiniteVolumeLimit : ∀ k, IsInfiniteVolumeLimit a.L (K k) (β k) (ν k)
def VolumeFirstApproximants.ConvergesTo {T : DerivedConstants} {a : FullChoice}
    {s : PeriodicLattice.ActivityDomainKind} {ρ : CutoffRemainders a} {g : ℝ}
    (Q : VolumeFirstApproximants T a s ρ g) (S : (n : ℕ) → (Fin n → AmbientSpace → ℝ) → ℂ) : Prop :=
  ∀ n, 2 ≤ n → ∀ f : Fin n → AmbientSpace → ℝ, IsSeparatedC1cTuple f →
    Tendsto (fun k => smearedEnergyCumulant (Q.ν k) f) atTop (𝓝 (S n f))
end InfiniteLattice
end YangMills.Construction
end
