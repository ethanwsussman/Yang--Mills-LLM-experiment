import YangMills.Construction.Towers.PlaneWavePropagatorCalculusFacts
import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperators
import YangMills.Construction.Towers.TheResponseInTheBackgroundGauge
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace ResponseInverses
open PeriodicOperators
open FreeResolvents (trivialRescaledOperators)
open FreeStrip (edges topEdges)
open BackgroundFieldResponse (xiInv blockCovariance blockCovarianceInv)
open PlaneWaveCalculus (IsRealColourTrivial)
def xiHat (L k : ℕ) (κ : Fin 4 → ℂ) : QuotHom (edges L k) (edges L k) :=
  symbolHom (edges L k) (edges L k) (trivialRescaledOperators L k).Xi κ
def blockCovarianceHat (L k : ℕ) (κ : Fin 4 → ℂ) : QuotHom (topEdges L k) (topEdges L k) :=
  (symbolHom (edges L k) (topEdges L k) (trivialRescaledOperators L k).Q κ).comp
    ((quotHomInverse (xiHat L k κ)).comp
      (symbolHom (topEdges L k) (edges L k) (trivialRescaledOperators L k).Qt κ))
structure SymbolsSummable (L k : ℕ) : Prop where
  xi : SymbolSummableOn (edges L k) (edges L k) (trivialRescaledOperators L k).Xi univ
  avg : SymbolSummableOn (edges L k) (topEdges L k) (trivialRescaledOperators L k).Q univ
  avg_transpose : SymbolSummableOn (topEdges L k) (edges L k) (trivialRescaledOperators L k).Qt univ
structure HolomorphicInversesOn (L k : ℕ) (O : Set (Fin 4 → ℂ)) : Prop where
  xi_isInvertible : ∀ κ ∈ O, IsInvertibleQuotHom (xiHat L k κ)
  cov_isInvertible : ∀ κ ∈ O, IsInvertibleQuotHom (blockCovarianceHat L k κ)
  xi_holomorphic : QuotHomFamilyHolomorphicOn (n := 4) O fun κ => quotHomInverse (xiHat L k κ)
  cov_holomorphic :
    QuotHomFamilyHolomorphicOn (n := 4) O fun κ => quotHomInverse (blockCovarianceHat L k κ)
structure MatrixInversesAt (L k : ℕ) (υ : ℝ) : Prop where
  near : ExistsOpenNear IsOpen (imStrip υ) (HolomorphicInversesOn L k)
  xi_bounded : QuotHomFamilyBoundedOn (imStrip υ) fun κ => quotHomInverse (xiHat L k κ)
  cov_bounded :
    QuotHomFamilyBoundedOn (imStrip υ) fun κ => quotHomInverse (blockCovarianceHat L k κ)
def IsInverseRadius (δ₀ : ℝ) (L k : ℕ) (υ : ℝ) : Prop :=
  υ ∈ Ioo (2 * δ₀) (1 / 9) ∧ MatrixInversesAt L k υ
structure HasTwoSidedInverse (I : PeriodicData) (T : I.Carrier → I.Carrier → ℂ) : Prop where
  invertible_on_reals : SymbolInvertibleOnReals I T
  periodic : IsPeriodicKernel I I (periodicInverse I T)
  left_summable : ∀ ι' ι, CompSummableAt (periodicInverse I T) T ι' ι
  right_summable : ∀ ι' ι, CompSummableAt T (periodicInverse I T) ι' ι
  left_inv : compKernel (periodicInverse I T) T = idKernel I
  right_inv : compKernel T (periodicInverse I T) = idKernel I
structure BlockCovarianceWellFormed (L k : ℕ) : Prop where
  left_pair : ∀ ι' ι, CompSummableAt (trivialRescaledOperators L k).Q (xiInv L k) ι' ι
  left_assoc : ∀ ι' ι, CompSummableAt (compKernel (trivialRescaledOperators L k).Q (xiInv L k))
    (trivialRescaledOperators L k).Qt ι' ι
  right_pair : ∀ ι' ι, CompSummableAt (xiInv L k) (trivialRescaledOperators L k).Qt ι' ι
  right_assoc : ∀ ι' ι, CompSummableAt (trivialRescaledOperators L k).Q
    (compKernel (xiInv L k) (trivialRescaledOperators L k).Qt) ι' ι
  assoc_eq : blockCovariance L k =
    compKernel (trivialRescaledOperators L k).Q (compKernel (xiInv L k) (trivialRescaledOperators L k).Qt)
  periodic : IsPeriodicKernel (topEdges L k) (topEdges L k) (blockCovariance L k)
structure OperatorInverses (L k : ℕ) : Prop where
  xi : HasTwoSidedInverse (edges L k) (trivialRescaledOperators L k).Xi
  cov_formed : BlockCovarianceWellFormed L k
  cov : HasTwoSidedInverse (topEdges L k) (blockCovariance L k)
  xi_real : IsRealColourTrivial (xiInv L k)
  cov_real : IsRealColourTrivial (blockCovarianceInv L k)
def Claim : Prop :=
  ∃ δ₀ ∈ FreeStrip.halfSupRate, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    SymbolsSummable L k ∧ (∃ υ, IsInverseRadius δ₀ L k υ) ∧ OperatorInverses L k
end ResponseInverses
end Tower
end YangMills.Construction
end
