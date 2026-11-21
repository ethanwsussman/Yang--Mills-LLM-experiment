import YangMills.Construction.InfiniteLattice.VolumeFirstLimits
import YangMills.Construction.Lattice.ConstructionOfTheRange
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ParameterChoice
namespace PeriodicLattice.CubesOfStep
open RangeConstruction EffectiveDensities OperationList LargeFieldExpansion ClassOperations
abbrev fixedParameterFlowOfRemainders (T : DerivedConstants) (a : FullChoice) (s : ActivityDomainKind) (K : ℕ) (hK : 0 < K) (m : ℕ+)
    (m' : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor a.L) (hM : a.M = a.L ^ m') (hr : ExponentLowerBound (a.r : ℝ)) (β : ℝ)
    (r : ∀ n : ℕ, ℕ → LocalActivities a.L n K) : FixedParameterFlow where
  derived := T
  params := a
  isAdmissible := hL
  K := ⟨K, hK⟩
  m := m
  m' := m'
  M_eq_pow := hM
  two_le_r := hr
  β := β
  activityDomain := s
  remainders := fun _ => r
def MakesRemaindersThroughLevel (T : DerivedConstants) (a : FullChoice) (s : ActivityDomainKind) (K : ℕ) (β : ℝ) (l : ℕ)
    (r : ∀ n : ℕ, ℕ → LocalActivities a.L n K) : Prop :=
  ∃ (hK : 0 < K) (m : ℕ+) (m' : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor a.L) (hM : a.M = a.L ^ m')
    (hr : ExponentLowerBound (a.r : ℝ))
    (hF : ∀ n k, Finite (SiteAtLevel a.L n K k))
    (φ : CollarTestForm) (τ : BackgroundVariant) (form : DisplayForm) (α : ℝ) (x : ℕ → ℝ)
    (c : ∀ n : ℕ, CourseChoices a n K x α) (t : ∀ n : ℕ, FlowTerms a n K x)
    (u : ∀ n : ℕ, ResultTerms T a n K x)
    (P : FlowExpansions (degreeChoice a) K ![a.C₀, a.C₁] s l x),
    (∀ k : Fin l, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → n ∈ (P k).sizes.sizes) ∧
      @IsSelfConsistentFlow (fixedParameterFlowOfRemainders T a s K hK m m' hL hM hr β r) hF φ τ form .viaCubes α l x c t u P r
def AreConstructionRemainders (T : DerivedConstants) (a : FullChoice) (s : ActivityDomainKind) (K : ℕ) (β : ℝ)
    (r : ∀ n : ℕ, ℕ → LocalActivities a.L n K) : Prop :=
  ∃ l : ℕ, MakesRemaindersThroughLevel T a s K β l r ∧
    ∀ (l' : ℕ) (r' : ∀ n : ℕ, ℕ → LocalActivities a.L n K), MakesRemaindersThroughLevel T a s K β l' r' → l' ≤ l
def constructionRemainders (T : DerivedConstants) (a : FullChoice) (s : ActivityDomainKind) :
    InfiniteLattice.CutoffRemainders a :=
  fun K β => Classical.epsilon (AreConstructionRemainders T a s K β)
end PeriodicLattice.CubesOfStep
end YangMills.Construction
end
