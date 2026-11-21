import YangMills.Construction.GrowingTori.TuplesOfFourSpaceAndTheirRestrictionToATorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.BallTuples
open Probability (IsBoundedRealRV)
open TestFunctions (IsLipschitzFor euclidDistTorus)
open SourcesAndGluing (ballR4)
namespace ConnectedMultilinearity
def MixedCumulantMultilinear : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ) (l : Fin n)
    (X : Fin n → Ω → ℝ) (Y Z : Ω → ℝ) (a b : ℝ),
    (∀ i, IsBoundedRealRV (X i)) → IsBoundedRealRV Y →
    IsBoundedRealRV Z → X l = (fun ω => a * Y ω + b * Z ω) →
    (Cumulants.mixedCumulant ν X).im = 0 ∧
      Cumulants.mixedCumulant ν X =
        (a : ℂ) * Cumulants.mixedCumulant ν (Function.update X l Y) +
          (b : ℂ) * Cumulants.mixedCumulant ν (Function.update X l Z)
variable (P : PeriodicSpace.Params) (K : ℕ+) {β : ℝ}
abbrev couplingData (hβ : 0 < β) : ConnectedFunctions.CouplingData :=
  { L := P.L, isAdmissible := P.isAdmissible, K := K, m := P.m, coupling := β,
    coupling_pos := hβ }
def connectedOfReal (hβ : 0 < β) {n : ℕ} (u : Fin n → P.Torus → ℝ) : ℂ :=
  (couplingData P K hβ).connected fun i x => ((u i x : ℝ) : ℂ)
def IsPeriodizationOn (ρ : ℝ) (f : R4Fun) (v : P.Torus → ℝ) : Prop :=
  (∀ x ∈ ballR4 ρ, v (TorusMetric.torusProj P.side x) = f x) ∧
    ∀ u, u ∉ TorusMetric.torusProj P.side '' ballR4 ρ → v u = 0
structure RealLipschitzLinearity (hβ : 0 < β) (n : ℕ) : Prop where
  im_eq_zero : ∀ u : Fin n → P.Torus → ℝ, (∀ i, IsLipschitzFor euclidDistTorus (u i)) →
    (connectedOfReal P K hβ u).im = 0
  map_update_add : ∀ (u : Fin n → P.Torus → ℝ) (l : Fin n) (g h : P.Torus → ℝ) (a b : ℝ),
    (∀ i, IsLipschitzFor euclidDistTorus (u i)) → IsLipschitzFor euclidDistTorus g →
    IsLipschitzFor euclidDistTorus h →
    connectedOfReal P K hβ (Function.update u l fun x => a * g x + b * h x) =
      (a : ℂ) * connectedOfReal P K hβ (Function.update u l g) +
        (b : ℂ) * connectedOfReal P K hβ (Function.update u l h)
  eq_of_disjointSupp : ∀ u : Fin n → P.Torus → ℝ, (∀ i, IsLipschitzFor euclidDistTorus (u i)) →
    ReflectionPositivity.CutoffMirrors.MirrorData.PairwiseDisjointSupp
      (D := (couplingData P K hβ).withDir 0) u →
    SchwingerFunctions.IsTorusTestFamily u ∧
      connectedOfReal P K hβ u = SchwingerFunctions.connectedSchwinger P.L P.m K β u
structure SeparatedTupleLinearity (β : ℝ) (n : ℕ) : Prop where
  indep_radius : ∀ (ρ : ℝ) (X : FnTuple n) (v : Fin n → P.Torus → ℝ), IsPeriodizable P ρ X →
    (∀ l, IsPeriodizationOn P ρ (X l) (v l)) →
    connectedFn P K β X = SchwingerFunctions.connectedSchwinger P.L P.m K β v
  im_eq_zero : ∀ ρ : ℝ, 0 < ρ → ρ ≤ BallPeriodization.ballRadius P →
    ∀ X ∈ lipTuplesBall n ρ, (connectedFn P K β X).im = 0
  map_update_add : ∀ ρ : ℝ, 0 < ρ → ρ ≤ BallPeriodization.ballRadius P →
    ∀ (X : FnTuple n) (l : Fin n) (g h : R4Fun) (a b : ℝ),
      Function.update X l g ∈ lipTuplesBall n ρ →
      Function.update X l h ∈ lipTuplesBall n ρ →
      Function.update X l (a • g + b • h) ∈ lipTuplesBall n ρ →
      connectedFn P K β (Function.update X l (a • g + b • h)) =
        (a : ℂ) * connectedFn P K β (Function.update X l g) +
          (b : ℂ) * connectedFn P K β (Function.update X l h)
  eq_zero_of_eq_zero : ∀ ρ : ℝ, 0 < ρ → ρ ≤ BallPeriodization.ballRadius P →
    ∀ X ∈ lipTuplesBall n ρ, ∀ l : Fin n, X l = 0 → connectedFn P K β X = 0
end ConnectedMultilinearity
open ConnectedMultilinearity in
def ConnectedMultilinearity.Statement : Prop :=
  MixedCumulantMultilinear ∧
    ∀ (P : PeriodicSpace.Params) (K : ℕ+) (β : ℝ) (hβ : 0 < β) (n : ℕ), 2 ≤ n →
      RealLipschitzLinearity P K hβ n ∧ SeparatedTupleLinearity P K β n
end YangMills.Construction.BallTuples
end
