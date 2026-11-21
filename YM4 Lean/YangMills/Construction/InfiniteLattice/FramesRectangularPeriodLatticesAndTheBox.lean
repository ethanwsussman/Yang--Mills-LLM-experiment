import YangMills.Construction.InfiniteLattice.MirrorVectors
import YangMills.Construction.InfiniteLattice.PeriodLatticesToriAndTheirWilsonMeasures
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open YangMills.Construction.InfiniteLattice
structure OrthogonalNormalFrame where
  vec : Fin 4 → AmbientSpace
  isNormal : ∀ i, IsNormalVector (vec i)
  pairwise_orthogonal : Pairwise fun i j => vec i ⬝ᵥ vec j = 0
namespace OrthogonalNormalFrame
variable (F : OrthogonalNormalFrame) (s : Fin 4 → ℕ+)
def lengthSq (i : Fin 4) : ℝ := NormalFamilies.normSq (F.vec i)
def dual (i : Fin 4) : AmbientSpace := NormalFamilies.dualVector (F.vec i)
def sideVec (i : Fin 4) : AmbientSpace := ((s i : ℕ) : ℝ) • F.dual i
def sideSpan : Set AmbientSpace :=
  {v | ∃ k : Fin 4 → ℤ, v = ∑ i, (k i : ℝ) • F.sideVec s i}
def fundamentalBox : Set (LatticePoint 1) :=
  {x | ∀ i, 0 ≤ linearHeight (F.vec i) (x : AmbientSpace) ∧
    linearHeight (F.vec i) (x : AmbientSpace) < ((s i : ℕ) : ℝ)}
def boxLinks : Set (Link 1) :=
  {b | ∃ x ∈ F.fundamentalBox s, ∃ μ : Fin 4, b = Link.forwardFrom x μ}
def boundaryShell (ϱ : ℕ+) : Set (LatticePoint 1) :=
  {x | x ∈ F.fundamentalBox s ∧ ∃ y : LatticePoint 1, y ∉ F.fundamentalBox s ∧
    ‖(y : AmbientSpace) - (x : AmbientSpace)‖ ≤ ((ϱ : ℕ) : ℝ)}
end OrthogonalNormalFrame
end YangMills.Construction.NormalFamilies
namespace YangMills.Construction.InfiniteLattice
open YangMills.Construction.NormalFamilies
def PeriodSublattice.IsBoxShaped (Γ : PeriodSublattice 1) (F : OrthogonalNormalFrame)
    (s : Fin 4 → ℕ+) : Prop :=
  (fun γ : LatticePoint 1 => (γ : AmbientSpace)) '' (Γ.periods : Set (LatticePoint 1)) =
      F.sideSpan s ∧
    ∀ i, F.sideVec s i ∈ latticeSubgroup 1
end YangMills.Construction.InfiniteLattice
