import YangMills.Construction.ResponseInTheExpansion.CurvatureOnTheBareTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ChessboardGrids
open TorusFields WeightedResponses
structure MirrorGrid where
  side : ℕ
  offset : Fin 4 → ℤ
namespace MirrorGrid
variable (g : MirrorGrid) {N : ℕ}
def cellIndices (N : ℕ) : Finset (Fin 4 → ℕ) := Fintype.piFinset fun _ => Finset.range (N / g.side)
def evenTranslations (N : ℕ) : Finset (Fin 4 → ℕ) := Fintype.piFinset fun _ => Finset.range (N / (2 * g.side))
def cellIndex [NeZero N] (x : TorusSite N) : Fin 4 → ℕ :=
  fun i => (x i - ((g.offset i + 1 : ℤ) : ZMod N)).val / g.side
open Classical in
def cellSites (N : ℕ) [NeZero N] (c : Fin 4 → ℕ) : Finset (TorusSite N) :=
  Finset.univ.filter fun x => g.cellIndex x = c
def recentre (c : Fin 4 → ℕ) : MirrorGrid := ⟨g.side, fun i => g.offset i + (c i : ℤ) * (g.side : ℤ)⟩
def atDepth (L v : ℕ) : MirrorGrid :=
  ⟨g.side * L ^ v, fun i => (L : ℤ) ^ v * g.offset i + ((L : ℤ) ^ v - 1) / 2⟩
def cellParity (c : Fin 4 → ℕ) (i : Fin 4) : Bool := decide (c i % 2 = 1)
def reflectSite (τ : Fin 4 → Bool) (x : TorusSite N) : TorusSite N :=
  fun i => if τ i then ((2 * g.offset i + 2 * (g.side : ℤ) + 1 : ℤ) : ZMod N) - x i else x i
def reflectField (τ : Fin 4 → Bool) (W : TorusField N) : TorusField N :=
  fun x k => if τ k then (W (g.reflectSite τ x - unitStep N k) k)⁻¹ else W (g.reflectSite τ x) k
def evenShift (c : Fin 4 → ℕ) : TorusSite N := siteOfInt fun i => ((c i - c i % 2 : ℕ) : ℤ) * (g.side : ℤ)
def cellCopy (F : TorusField N → ℝ) (c : Fin 4 → ℕ) (W : TorusField N) : ℝ :=
  F (g.reflectField (cellParity c) (TorusFields.translate (g.evenShift c) W))
def chessboardNorm (β : ℝ) (N : ℕ) [NeZero N] (F : TorusField N → ℝ) : ℝ :=
  (∫ W, ∏ c ∈ g.cellIndices N, g.cellCopy F c W ∂(wilsonLaw β N)) ^ (1 / ((g.cellIndices N).card : ℝ))
def chessboardNormAt (β : ℝ) (N : ℕ) [NeZero N] (c : Fin 4 → ℕ) (F : TorusField N → ℝ) : ℝ :=
  (g.recentre c).chessboardNorm β N F
end MirrorGrid
variable {N : ℕ}
def DependsOnBondsIn (S : Finset (TorusSite N)) (F : TorusField N → ℝ) : Prop :=
  ∀ W W' : TorusField N, (∀ b : TorusBond N, b.1 ∈ S → b.1 + unitStep N b.2 ∈ S → W b.1 b.2 = W' b.1 b.2) → F W = F W'
structure IsCellFunction (g : MirrorGrid) (N : ℕ) [NeZero N] (c : Fin 4 → ℕ) (F : TorusField N → ℝ) : Prop where
  measurable : Measurable F
  bounded : ∃ C : ℝ, ∀ W, |F W| ≤ C
  nonneg : ∀ W, 0 ≤ F W
  depends : DependsOnBondsIn (g.cellSites N c) F
def IsGridOfTorus (g : MirrorGrid) (L M : ℕ) : Prop := ∃ p : ℕ, 1 ≤ p ∧ p ≤ M ∧ g.side = L ^ p
def leastPowerAbove (L a : ℕ) : ℕ := L ^ Nat.clog L a
def numCells (n l : ℕ) : ℕ := (n / l) ^ 4
end ChessboardGrids
end YangMills.Construction
end
