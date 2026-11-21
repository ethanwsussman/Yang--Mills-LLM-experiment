import YangMills.Construction.TorusOrFourSpace.SpaceQuotientMapAndDistance
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
abbrev Coords (p : ℕ+) : Type := Fin (4 * (p : ℕ)) → ℝ
abbrev CoordIndex (p : ℕ+) : Type := Fin (4 * (p : ℕ)) → ℕ
def CoordIndex.degree {p : ℕ+} (α : CoordIndex p) : ℕ := ∑ j, α j
namespace Coords
variable {p : ℕ+}
def block (x : Coords p) (i : Fin (p : ℕ)) : Fin 4 → ℝ :=
  fun μ => x ⟨4 * (i : ℕ) + (μ : ℕ), by have := i.2; have := μ.2; omega⟩
def partialAlong (j : Fin (4 * (p : ℕ))) (G : Coords p → ℂ) : Coords p → ℂ :=
  fun x => lineDeriv ℝ G x (Pi.single j 1)
def iterPartial (α : CoordIndex p) (G : Coords p → ℂ) : Coords p → ℂ :=
  (List.finRange (4 * (p : ℕ))).foldr (fun j H => (partialAlong j)^[α j] H) G
def ContPartialsUpTo : ℕ → (Coords p → ℂ) → Prop
  | 0, G => Continuous G
  | ν + 1, G =>
    Continuous G ∧ ∀ j : Fin (4 * (p : ℕ)),
      (∀ x, LineDifferentiableAt ℝ G x (Pi.single j 1)) ∧
        ContPartialsUpTo ν (partialAlong j G)
end Coords
namespace Kind
abbrev Tuple (D : Params) (E : Kind) (p : ℕ+) : Type := Fin (p : ℕ) → Pt D E
namespace Tuple
variable (D : Params) (E : Kind) {p : ℕ+}
def proj (x : Coords p) : Tuple D E p :=
  fun i => quotMap D E (Coords.block x i)
def IsLiftOf (y : Tuple D E p) (x : Coords p) : Prop := proj D E x = y
def periodSet (p : ℕ+) : Set (Coords p) := {x | ∀ i, Coords.block x i ∈ periodGroup D E}
def tupleDist (y y' : Tuple D E p) : ℝ :=
  Real.sqrt (∑ i, quotDist D E (y i) (y' i) ^ 2)
abbrev IsOpenT (S : Set (Tuple D E p)) : Prop :=
  MetricNotions.IsOpenWrt (tupleDist D E) S
abbrev IsClosedT (S : Set (Tuple D E p)) : Prop :=
  MetricNotions.IsClosedWrt (tupleDist D E) S
abbrev IsCompactT (S : Set (Tuple D E p)) : Prop :=
  MetricNotions.IsCompactWrt (tupleDist D E) S
abbrev closureT (S : Set (Tuple D E p)) : Set (Tuple D E p) :=
  MetricNotions.closureWrt (tupleDist D E) S
abbrev IsContinuousT {Z : Type*} [PseudoMetricSpace Z] (F : Tuple D E p → Z) :
    Prop :=
  MetricNotions.IsContinuousWrt (tupleDist D E) dist F
def IsNhd (K N : Set (Tuple D E p)) : Prop :=
  ∃ U, IsOpenT D E U ∧ K ⊆ U ∧ U ⊆ N
def IsClassC (ν : ℕ) (F : Tuple D E p → ℂ) : Prop :=
  Coords.ContPartialsUpTo ν (F ∘ proj D E)
def IsSmoothT (F : Tuple D E p → ℂ) : Prop := ∀ ν, IsClassC D E ν F
def partialDeriv (α : CoordIndex p) (F : Tuple D E p → ℂ) :
    Tuple D E p → ℂ :=
  Classical.epsilon fun H =>
    H ∘ proj D E = Coords.iterPartial α (F ∘ proj D E)
def cNorm (ν : ℕ) (F : Tuple D E p → ℂ) : ℝ≥0∞ :=
  ⨆ α : CoordIndex p, ⨆ _ : CoordIndex.degree α ≤ ν, ⨆ y, ENNReal.ofReal ‖partialDeriv D E α F y‖
def supportT (F : Tuple D E p → ℂ) : Set (Tuple D E p) :=
  closureT D E {y | F y ≠ 0}
def tensorProd (φ : Fin (p : ℕ) → Pt D E → ℂ) : Tuple D E p → ℂ :=
  fun y => ∏ i, φ i (y i)
def ofSingle {Z : Type*} (φ : Pt D E → Z) : Tuple D E 1 → Z :=
  fun y => φ (y ⟨0, (1 : ℕ+).pos⟩)
def c1NormSingle (φ : Pt D E → ℂ) : ℝ≥0∞ := cNorm D E 1 (ofSingle D E φ)
def c1NormSingleReal (u : Pt D E → ℝ) : ℝ≥0∞ :=
  c1NormSingle D E fun y => (u y : ℂ)
end Tuple
end Kind
end YangMills.Construction.PeriodicSpace
