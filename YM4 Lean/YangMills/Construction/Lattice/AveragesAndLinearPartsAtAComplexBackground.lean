import YangMills.Construction.Lattice.AssertionsOfTheAveragesAtAComplexBackground
import YangMills.Construction.Lattice.CommonCeiling
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Averaging.ComplexStepSetting (straightenedCurvatureConstant)
open Classical in
structure ComplexBackgroundConstants (L : ℕ) (c₀ C₀ C₃ : ℝ) : Prop where
  pos : 0 < c₀
  le_quarter_radius : c₀ ≤ nearRealAverageRadius L / 4
  le_sharedCeiling : c₀ ≤ sharedCeiling L
  sharedCeiling_le : sharedCeiling L ≤ straightenedCurvatureConstant L
  one_le_linear : 1 ≤ C₀
  one_le_kernel : 1 ≤ C₃
  holds : ∀ m K k : ℕ, 0 < m →
    ∀ (_ : ∀ (n : ℕ) (c' : BondAtLevel L m K (n + 1)),
        Fintype (PositiveBondsOf (doubleBlockSymmetricSet c')))
      (c : BondAtLevel L m K k) (hc : c.IsPositivelyOriented) (_ : Fintype (FineBondIndex c))
      (α₀ : ℝ) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2), α₀ ≤ c₀ →
      IsFinestBlockPairData k c α₀ U 0 0 →
      BackgroundAveragesHolomorphic c α₀ U ∧
      (∀ (v : FineBondIndex c) (X : ↥Matrices.ComplexMatrix2.traceless)
        (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless),
        Matrices.GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
          (Matrices.GroupLieProduct.supBall _ c₀) fun t =>
            (twistedStraightenedKernel c hc (bareTwist k (fineFormOfFamily c t) U) v X :
              Matrices.ComplexMatrix2)) ∧
      (∀ y ∈ bondEndpoints c, ∀ (x : ↥(blockSitesAtLevel 0 y))
        (X : ↥Matrices.ComplexMatrix2.traceless)
        (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless),
        Matrices.GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
          (Matrices.GroupLieProduct.supBall _ c₀) fun t =>
            (twistedBlockAverageOperator c (bareTwist k (fineFormOfFamily c t) U) y
              (Pi.single x X) : Matrices.ComplexMatrix2)) ∧
      (∀ A' : BondAtLevel L m K 0 → Matrices.ComplexMatrix2, IsFinestBlockPairData k c α₀ U A' 0 →
        blockPairSupNormAt 0 c A' < c₀ →
          BackgroundLinearParts C₀ c hc α₀ U A') ∧
      (∀ n ≤ k, ∀ (v : PositiveBondsOf (blockPairSymmetricBondsAt n c))
        (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless),
        Matrices.GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
          (backgroundPolydisc c c₀) fun t =>
            (twistedStraightenedAverage c (bareTwist k (fineFormOfValues c (pairFirst t)) U)
              (fineFormOfValues c (pairSecond t)) n v : Matrices.ComplexMatrix2)) ∧
      ∀ A' A : BondAtLevel L m K 0 → Matrices.ComplexMatrix2, IsFinestBlockPairData k c α₀ U A' A →
        blockPairSupNormAt 0 c A' < c₀ → blockPairSupNormAt 0 c A < c₀ →
          BackgroundStraightenedAverages C₀ C₃ c hc α₀ U A' A ∧
          TwistedAverageFactorization c (bareTwist k A' U) A
def complexBackgroundConstants (L : ℕ) : ℝ × ℝ × ℝ :=
  Classical.epsilon fun x => ComplexBackgroundConstants L x.1 x.2.1 x.2.2
def complexBackgroundRadius (L : ℕ) : ℝ := (complexBackgroundConstants L).1
def complexBackgroundLinearConstant (L : ℕ) : ℝ := (complexBackgroundConstants L).2.1
def complexBackgroundKernelConstant (L : ℕ) : ℝ := (complexBackgroundConstants L).2.2
end YangMills.Construction.PeriodicLattice
