import YangMills.Construction.Towers.CovariantLinearAverages
import YangMills.Construction.Towers.PolydiscsOfDoubleBlocks
import YangMills.Construction.Towers.TheHolomorphicActionOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace StepKernelHolomorphy
open Matrices
def IsHolomorphicOnProduct {σ : Type} [Fintype σ] (W : Set (σ → ComplexMatrix2))
    (φ : (σ → ComplexMatrix2) → ℂ) : Prop :=
  ∀ β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
    GroupLieProduct.IsHolomorphicToCoords β (Equiv.funUnique (Fin 1) ℂ).symm
      (DoubleBlockPolydisc.leftComponents ⁻¹' W) (φ ∘ DoubleBlockPolydisc.leftComponents)
variable {L n k j : ℕ}
def smoothingDerivCoeff (V : Edge L n k j → ComplexMatrix2) (c : Edge L n k (j + 1))
    (e : PositiveEdge L n k j) (a' a : Fin 3) : ℂ :=
  pauliCoeff a' (covariantSmoothingDeriv V (basisForm a e) c)
def conjugationCoeff (V : Edge L n k j → ComplexMatrix2) (y : Vertex L n k (j + 1))
    (x : Vertex L n k j) (a' a : Fin 3) : ℂ :=
  pauliCoeff a' (ComplexMatrix2.conjugateBy
    (PeriodicLattice.complexMeanContourHolonomy V y x) (ComplexMatrix2.pauliFamily a))
structure KernelHolomorphyAt (ρ : ℝ) (c : Edge L n k (j + 1)) : Prop where
  polydisc_open : ComplexMatrix2.IsRelativelyOpen
    (GroupLieProduct.unimodularPi (DoubleBlockPolydisc.positiveDoubleBlockBonds c))
    (DoubleBlockPolydisc.polydiscPositive ρ c)
  smoothing_local : ∀ V ∈ nearIdentityPolydisc ρ c, ∀ V' ∈ nearIdentityPolydisc ρ c,
    EqOn V V' (DoubleBlockPolydisc.doubleBlockBonds c) → ∀ e : PositiveEdge L n k j,
      e.1 ∈ DoubleBlockPolydisc.doubleBlockBonds c →
      ∀ a' a, smoothingDerivCoeff V c e a' a = smoothingDerivCoeff V' c e a' a
  conjugation_local : ∀ V ∈ nearIdentityPolydisc ρ c, ∀ V' ∈ nearIdentityPolydisc ρ c,
    EqOn V V' (DoubleBlockPolydisc.doubleBlockBonds c) →
      ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        ∀ a' a, conjugationCoeff V y x a' a = conjugationCoeff V' y x a' a
  smoothing_holomorphic : ∀ e : PositiveEdge L n k j,
    e.1 ∈ DoubleBlockPolydisc.doubleBlockBonds c → ∀ a' a,
    ∃ _ : Fintype (DoubleBlockPolydisc.positiveDoubleBlockBonds c),
      IsHolomorphicOnProduct (DoubleBlockPolydisc.polydiscPositive ρ c) fun v =>
        smoothingDerivCoeff (DoubleBlockPolydisc.fieldOfValues c v) c e a' a
  conjugation_holomorphic : ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y, ∀ a' a,
      ∃ _ : Fintype (DoubleBlockPolydisc.positiveDoubleBlockBonds c),
        IsHolomorphicOnProduct (DoubleBlockPolydisc.polydiscPositive ρ c) fun v =>
          conjugationCoeff (DoubleBlockPolydisc.fieldOfValues c v) y x a' a
def StepKernelsHolomorphic : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j < k →
    ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      KernelHolomorphyAt (3 / 4 * polydiscRadius L) c
end StepKernelHolomorphy
end Tower
end YangMills.Construction
end
