import YangMills.Construction.TorusOrFourSpace.ArbitraryFamilyOfDenseSets
import YangMills.Construction.TorusOrFourSpace.DiagonalExtractionDefs
import YangMills.Construction.TorusOrFourSpace.EquicontinuityInequalities
import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsAndProductsOfClasses
import YangMills.Construction.TorusOrFourSpace.NeighbourhoodsInTheDiagonalExtraction
import YangMills.Construction.TorusOrFourSpace.StandingSignsOfTheSupportAdaptedFamily
import Mathlib
set_option autoImplicit false
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.DiagonalLimits
section Thickenings
variable (D : Params) (E : Kind)
def approxDefect {n : ℕ} (f : Kind.FnTuple D E n) (ε : ℝ) : ℝ :=
  ∑ i, 40 * D.M * ε * ∏ l ∈ Finset.univ.erase i, (Kind.sharpNormReal D E (f l) + 40 * D.M * ε)
variable {n : ℕ} (f : Kind.FnTuple D E n) (hf : f ∈ Kind.sepC1Tuples D E n) (d : ℝ) (hd : 0 < d)
def openSupportThickening (i : Fin n) : Set (E.Pt D) :=
  openNhdWidth D E (Kind.supportQ D E (f i)) (hf.2.1 i) (d / 3) (div_pos hd three_pos)
def closedSupportThickening (i : Fin n) : Set (E.Pt D) :=
  closedNhdWidth D E (Kind.supportQ D E (f i)) (hf.2.1 i) (d / 3) (div_pos hd three_pos)
abbrev thickeningC1Product : Set (Kind.FnTuple D E n) :=
  Kind.productSet D E fun l => Kind.c1SupportedIn D E (closedSupportThickening D E f hf d hd l)
def ThickeningsCompactSeparated : Prop :=
  (∀ i, Kind.IsCompactQ D E (closedSupportThickening D E f hf d hd i)) ∧
    PairwiseSetDistGe D E (closedSupportThickening D E f hf d hd) (d / 3) ∧
    ∀ ρ : ℝ≥0∞, 0 < ρ → ρ < ∞ → (∀ i, Kind.supportQ D E (f i) ⊆ Kind.centredBall D E ρ) →
      ∀ i, closedSupportThickening D E f hf d hd i ⊆
        Kind.closedBallAbout D E (Kind.origin D E) (ρ.toReal + d / 3)
def IsFamilyApproximant (F : Kind.DenseChoiceFamily D E) (ε : ℝ) (φ : Kind.FnTuple D E n) :
    Prop :=
  (⟨n, φ⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ F.tuples ∧
    ∀ i, SupportAdapted.c1EuclidNorm D E (f i - φ i) ≤ ENNReal.ofReal ε ∧
      Kind.sharpNormQ D E (f i - φ i) ≤ ENNReal.ofReal (40 * D.M * ε) ∧
      Kind.supportQ D E (φ i) ⊆ openSupportThickening D E f hf d hd i ∧
      openSupportThickening D E f hf d hd i ⊆ closedSupportThickening D E f hf d hd i
def MultilinearStableUnderApprox (F : Kind.DenseChoiceFamily D E) (ε : ℝ) : Prop :=
  ∀ φ : Kind.FnTuple D E n, IsFamilyApproximant D E f hf d hd F ε φ →
    ∀ c : ℝ, 0 ≤ c →
    ∀ Ψ : thickeningC1Product D E f hf d hd → ℝ,
      Kind.IsMultilinearOnProduct D E (thickeningC1Product D E f hf d hd)
        (fun l => Kind.c1SupportedIn D E (closedSupportThickening D E f hf d hd l)) Ψ →
      (∀ h : thickeningC1Product D E f hf d hd,
        ENNReal.ofReal |Ψ h| ≤ ENNReal.ofReal c * ∏ l, Kind.sharpNormQ D E (h.1 l)) →
      ∃ (hfP : f ∈ thickeningC1Product D E f hf d hd)
        (hφP : φ ∈ thickeningC1Product D E f hf d hd),
        |Ψ ⟨f, hfP⟩ - Ψ ⟨φ, hφP⟩| ≤ c * approxDefect D E f ε
end Thickenings
namespace FamilyApproximation
def Statement : Prop :=
  ∀ (D : Params) (E : Kind) (F : Kind.DenseChoiceFamily D E) (n : ℕ), 2 ≤ n →
    ∀ (f : Kind.FnTuple D E n) (hf : f ∈ Kind.sepC1Tuples D E n) (d : ℝ) (hd : 0 < d),
      ENNReal.ofReal d ≤ Kind.supportGap D E f →
      ∀ ε : ℝ, 0 < ε →
        ThickeningsCompactSeparated D E f hf d hd ∧
        (∃ φ : Kind.FnTuple D E n, IsFamilyApproximant D E f hf d hd F ε φ) ∧
        MultilinearStableUnderApprox D E f hf d hd F ε ∧
        Filter.Tendsto (approxDefect D E f) (𝓝[>] 0) (𝓝 0)
end FamilyApproximation
end YangMills.Construction.PeriodicSpace.DiagonalLimits
