import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.PowerSeries.MultiIndexNotation
import Mathlib
noncomputable section
namespace YangMills.Construction.BanachValued
variable {n : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
def closedPolyball (c : Coordinates.ComplexCoordinates n) (ρ : ℝ) :
    Set (Coordinates.ComplexCoordinates n) := {z | ‖z - c‖ ≤ ρ}
structure IsPowerSeriesDataAt (O : Set (Coordinates.ComplexCoordinates n))
    (f : Coordinates.ComplexCoordinates n → Y) (c : Coordinates.ComplexCoordinates n) (ρ : ℝ)
    (a : PowerSeries.MultiIndex n → Y) : Prop where
  pos : 0 < ρ
  subset : closedPolyball c ρ ⊆ O
  summable : Summable fun γ : PowerSeries.MultiIndex n => ‖a γ‖ * ρ ^ PowerSeries.MultiIndex.order γ
  hasSum : ∀ w : Coordinates.ComplexCoordinates n, ‖w‖ ≤ ρ →
    HasSum (fun γ : PowerSeries.MultiIndex n => PowerSeries.MultiIndex.monomial w γ • a γ) (f (c + w))
def IsHolomorphicOnOpen (O : Set (Coordinates.ComplexCoordinates n))
    (f : Coordinates.ComplexCoordinates n → Y) : Prop :=
  IsOpen O ∧
    ((1 ≤ n ∧ ∀ c ∈ O, ∃ (ρ : ℝ) (a : PowerSeries.MultiIndex n → Y), IsPowerSeriesDataAt O f c ρ a) ∨
      (n = 0 ∧ ∃ p, O = {p}))
def IsOperatorHolomorphicOn {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (O : Set (Coordinates.ComplexCoordinates n))
    (f : Coordinates.ComplexCoordinates n → K →L[ℂ] K) : Prop :=
  IsHolomorphicOnOpen O f
end YangMills.Construction.BanachValued
