import YangMills.Construction.ComplexAnalysis.BanachValuedHolomorphy
import Mathlib
noncomputable section
namespace YangMills.Construction.BanachValued.AffineCoordinates
open YangMills.Construction.Coordinates (ComplexCoordinates)
open YangMills.Construction.PowerSeries (MultiIndex)
variable {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
def maxAbsRowSum (J : Matrix (Fin n) (Fin n) ℂ) : ℝ := ⨆ i, ∑ j, ‖J i j‖
abbrev ExpandedIndex (n : ℕ) : Type :=
  Σ γ : MultiIndex n, ∀ i : Fin n, Fin (γ i) → Fin n
def chosenEntryProd (J : Matrix (Fin n) (Fin n) ℂ) (t : ExpandedIndex n) : ℂ :=
  ∏ i, ∏ k, J i (t.2 i k)
def collectedExponent (t : ExpandedIndex n) : MultiIndex n :=
  fun j => ∑ i, (Finset.univ.filter fun k => t.2 i k = j).card
def expandedSeriesTerm (J : Matrix (Fin n) (Fin n) ℂ) (a : MultiIndex n → Y)
    (w : ComplexCoordinates n) (t : ExpandedIndex n) : Y :=
  (chosenEntryProd J t * MultiIndex.monomial w (collectedExponent t)) • a t.1
def majorantSeriesTerm (J : Matrix (Fin n) (Fin n) ℂ) (a : MultiIndex n → Y)
    (w : ComplexCoordinates n) (γ : MultiIndex n) : ℝ :=
  ‖a γ‖ * ∏ i, (∑ j, ‖J i j‖ * ‖w j‖) ^ γ i
structure SeriesAtIncrement (J : Matrix (Fin n) (Fin n) ℂ) (b : ComplexCoordinates n)
    (f : ComplexCoordinates n → Y) (z w : ComplexCoordinates n) (ρ : ℝ) (a : MultiIndex n → Y) :
    Prop where
  hasSum : HasSum (fun γ : MultiIndex n => MultiIndex.monomial (J.mulVec w) γ • a γ)
    (f (J.mulVec (z + w) + b))
  summable_norm_expanded : Summable fun t : ExpandedIndex n => ‖expandedSeriesTerm J a w t‖
  summable_majorant : Summable (majorantSeriesTerm J a w)
  summable_norm_mul_pow : Summable fun γ : MultiIndex n => ‖a γ‖ * ρ ^ MultiIndex.order γ
  tsum_norm_expanded_le :
    ∑' t : ExpandedIndex n, ‖expandedSeriesTerm J a w t‖ ≤ ∑' γ, majorantSeriesTerm J a w γ
  tsum_majorant_le :
    ∑' γ, majorantSeriesTerm J a w γ ≤ ∑' γ : MultiIndex n, ‖a γ‖ * ρ ^ MultiIndex.order γ
  hasSum_collected : HasSum
    (fun β : MultiIndex n =>
      ∑' t : {t : ExpandedIndex n // collectedExponent t = β}, expandedSeriesTerm J a w t.1)
    (f (J.mulVec (z + w) + b))
def HolomorphicCompositionProperties : Prop :=
  ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y] (n : ℕ), 1 ≤ n →
    ∀ (O : Set (ComplexCoordinates n)) (f : ComplexCoordinates n → Y), IsHolomorphicOnOpen O f →
      ContinuousOn f O ∧
      (∀ l : Y →L[ℂ] ℂ, IsHolomorphicOnOpen O fun z => l (f z)) ∧
      ∀ (J : Matrix (Fin n) (Fin n) ℂ) (b : ComplexCoordinates n), IsUnit J →
        IsHolomorphicOnOpen {z | J.mulVec z + b ∈ O} (fun z => f (J.mulVec z + b)) ∧
        ∀ (z : ComplexCoordinates n) (ρ : ℝ) (a : MultiIndex n → Y),
          IsPowerSeriesDataAt O f (J.mulVec z + b) ρ a →
          ∀ w : ComplexCoordinates n, ‖w‖ * maxAbsRowSum J ≤ ρ → SeriesAtIncrement J b f z w ρ a
end YangMills.Construction.BanachValued.AffineCoordinates
