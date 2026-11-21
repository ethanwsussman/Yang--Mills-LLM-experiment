import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.EuclideanIsometries
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
structure Params where
  L : ℕ
  isAdmissible : Conventions.IsAdmissibleBlockingFactor L
  m : ℕ+
  M : ℝ
  one_le_M : 1 ≤ M
namespace Params
def ofStanding (s : Conventions.StandingParameters) (M : ℝ) (hM : 1 ≤ M) : Params :=
  ⟨s.L, s.isAdmissible, s.m, M, hM⟩
variable (D : Params)
abbrev side : ℝ := PeriodicLattice.torusSide D.L D.m
abbrev Torus : Type := PeriodicLattice.FourTorus D.L D.m
end Params
inductive Kind where
  | euclidean
  | torus
namespace Kind
variable (D : Params)
def Pt : Kind → Type
  | euclidean => Fin 4 → ℝ
  | torus => D.Torus
instance instAddCommGroupPt : (E : Kind) → AddCommGroup (E.Pt D)
  | euclidean => inferInstanceAs (AddCommGroup (Fin 4 → ℝ))
  | torus => inferInstanceAs (AddCommGroup D.Torus)
def quotMap : (E : Kind) → (Fin 4 → ℝ) → E.Pt D
  | euclidean, x => x
  | torus, x => TorusMetric.torusProj D.side x
def periodGroup : Kind → AddSubgroup (Fin 4 → ℝ)
  | euclidean => ⊥
  | torus => InfiniteLattice.latticeSubgroup D.side
variable (E : Kind)
def IsLift (y : E.Pt D) (x : Fin 4 → ℝ) : Prop := E.quotMap D x = y
def IsGammaPeriodic {Z : Type*} (F : (Fin 4 → ℝ) → Z) : Prop :=
  ∀ x, ∀ k ∈ E.periodGroup D, F (x + k) = F x
def quotDist (y y' : E.Pt D) : ℝ :=
  sInf {r | ∃ x x', IsLift D E y x ∧ IsLift D E y' x' ∧ ∃ k ∈ E.periodGroup D,
    r = TorusMetric.euclidNormVec (x - x' - k)}
def setInfDist (S S' : Set (E.Pt D)) : ℝ≥0∞ :=
  ⨅ z ∈ S, ⨅ z' ∈ S', ENNReal.ofReal (quotDist D E z z')
def infDistPt (y : E.Pt D) (S : Set (E.Pt D)) : ℝ≥0∞ := setInfDist D E {y} S
def setDiam (S : Set (E.Pt D)) : ℝ≥0∞ :=
  ⨆ z ∈ S, ⨆ z' ∈ S, ENNReal.ofReal (quotDist D E z z')
abbrev IsOpenQ (S : Set (E.Pt D)) : Prop := MetricNotions.IsOpenWrt (quotDist D E) S
abbrev IsClosedQ (S : Set (E.Pt D)) : Prop := MetricNotions.IsClosedWrt (quotDist D E) S
abbrev IsCompactQ (S : Set (E.Pt D)) : Prop := MetricNotions.IsCompactWrt (quotDist D E) S
abbrev closureQ (S : Set (E.Pt D)) : Set (E.Pt D) :=
  MetricNotions.closureWrt (quotDist D E) S
abbrev IsContinuousQ {Z : Type*} [PseudoMetricSpace Z] (u : E.Pt D → Z) : Prop :=
  MetricNotions.IsContinuousWrt (quotDist D E) dist u
end Kind
end YangMills.Construction.PeriodicSpace
end
