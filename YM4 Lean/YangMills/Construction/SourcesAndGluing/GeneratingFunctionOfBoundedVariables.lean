import YangMills.Construction.SourcesAndGluing.LogarithmDerivativesPartitionsCumulantsAndConnectedFunctions
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
section Family
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
def famMGF (ν : Measure Ω) (Y : ι → Ω → ℝ) (s : ι → ℂ) : ℂ :=
  ∫ x, Complex.exp (∑ p, s p * (Y p x : ℂ)) ∂ν
theorem famMGF_eq_momentGeneratingFunction {n : ℕ} (ν : Measure Ω)
    (X : Fin n → Ω → ℝ) : famMGF ν X = YangMills.Construction.Cumulants.momentGeneratingFunction ν X :=
  rfl
def l1Norm (s : ι → ℂ) : ℝ := ∑ p, ‖s p‖
def famSeriesTerm (ν : Measure Ω) (Y : ι → Ω → ℝ) (k : ℕ) (s : ι → ℂ) : ℂ :=
  1 / (k.factorial : ℂ) * ∫ x, (∑ p, s p * (Y p x : ℂ)) ^ k ∂ν
def l1Ball (ρ : ℝ) : Set (ι → ℂ) := {s | l1Norm s < ρ}
def famLogMGF (ν : Measure Ω) (Y : ι → Ω → ℝ) (s : ι → ℂ) : ℂ :=
  principalLog (famMGF ν Y s)
def IsLogRadius (ν : Measure Ω) (Y : ι → Ω → ℝ) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ s ∈ l1Ball (ι := ι) ρ, ‖famMGF ν Y s - 1‖ < 1
end Family
def boundRadius (C : ℝ) : ℝ := if 0 < C then Real.log 2 / C else 1
namespace BoundedMGF
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [LinearOrder ι]
structure SeriesExpansion (ν : Measure Ω) (Y : ι → Ω → ℝ) (C : ℝ) : Prop where
  tendsto_sum : ∀ s, Tendsto
    (fun k₀ => ∑ k ∈ Finset.range (k₀ + 1), famSeriesTerm ν Y k s) atTop
    (𝓝 (famMGF ν Y s))
  term_eq : ∀ (k : ℕ) (s : ι → ℂ), famSeriesTerm ν Y k s =
    1 / (k.factorial : ℂ) *
      ∑ q : Fin k → ι, (∏ i, s (q i)) * ((∫ x, ∏ i, Y (q i) x ∂ν : ℝ) : ℂ)
  homogeneous : ∀ k : ℕ, ∃ f : MvPolynomial ι ℂ,
    f.IsHomogeneous k ∧ ∀ s, MvPolynomial.eval s f = famSeriesTerm ν Y k s
  norm_term_le : ∀ (k : ℕ) (s : ι → ℂ),
    ‖famSeriesTerm ν Y k s‖ ≤ (C * l1Norm s) ^ k / (k.factorial : ℝ)
  tendstoUniformlyOn : ∀ B : Set (ι → ℂ), Bornology.IsBounded B → TendstoUniformlyOn
    (fun (k₀ : ℕ) s => ∑ k ∈ Finset.range (k₀ + 1), famSeriesTerm ν Y k s)
    (famMGF ν Y) atTop B
  entire : EntireFun (famMGF ν Y)
  tendsto_sum_partials : ∀ (l : List ι) (s : ι → ℂ), Tendsto
    (fun k₀ => ∑ k ∈ Finset.range (k₀ + 1), iteratedPartials l (famSeriesTerm ν Y k) s) atTop
    (𝓝 (iteratedPartials l (famMGF ν Y) s))
  value_at_zero : famMGF ν Y 0 = 1
structure LogExpansion (ν : Measure Ω) (Y : ι → Ω → ℝ) (C : ℝ) : Prop where
  exists_radius : ∃ ρ, IsLogRadius ν Y ρ
  holomorphic : ∀ ρ, IsLogRadius ν Y ρ →
    HolomorphicOnSet (l1Ball ρ) (famLogMGF ν Y)
  value_at_zero : famLogMGF ν Y 0 = 0
  exp_eq : ∀ ρ, IsLogRadius ν Y ρ → ∀ s ∈ l1Ball (ι := ι) ρ,
    Complex.exp (famLogMGF ν Y s) = famMGF ν Y s
  radius_of_bound : IsLogRadius ν Y (boundRadius C)
def Statement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν],
    (∀ (ι : Type) [Fintype ι] [LinearOrder ι] [Nonempty ι] (Y : ι → Ω → ℝ) (C : ℝ),
      (∀ p, Measurable (Y p)) → 0 ≤ C → (∀ p x, |Y p x| ≤ C) →
        SeriesExpansion ν Y C ∧
        (∀ J : Finset ι, setPartial J (famMGF ν Y) 0 =
          ((∫ x, ∏ p ∈ J, Y p x ∂ν : ℝ) : ℂ)) ∧
        LogExpansion ν Y C) ∧
    ∀ (n : ℕ) (X : Fin n → Ω → ℝ), BoundedRVFamily ν X →
      ∃ W : Set (Fin n → ℂ), 0 ∈ W ∧
        HolomorphicOnSet W fun z => principalLog (YangMills.Construction.Cumulants.momentGeneratingFunction ν X z)
end BoundedMGF
end YangMills.Construction.SourcesAndGluing
end
