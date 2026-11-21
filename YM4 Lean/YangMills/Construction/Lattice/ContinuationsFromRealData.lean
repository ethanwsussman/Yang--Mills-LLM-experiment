import YangMills.Construction.Lattice.MinimalConfigurationsAtComplexData
import YangMills.Construction.Matrices.ValueConjugation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set Matrices
namespace PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def selfAdjointFunctions (Z : Type) : Set (Z → ComplexMatrix2) :=
  {f | f ∈ GroupLieProduct.tracelessPi Z ∧ ComplexMatrix2.algebraConjPointwise f = f}
def IsHolomorphicMatrixValued {σ τ : Type} [Fintype σ] [Fintype τ] (O : Set (σ → ComplexMatrix2))
    (f : (σ → ComplexMatrix2) → τ → ComplexMatrix2) : Prop :=
  ∀ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (ν : τ ≃ Fin (Fintype.card τ)),
    GroupLieProduct.IsHolomorphicOnTraceless b (GroupLieProduct.matrixPiEquiv ν) O f
def IsBallDatum (ε εBar : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) : Prop :=
  V₀ ∈ activeRegularRealFields εBar K k Ω ∧ HasActiveCriticalOrbit ε K k Ω V₀
def realFamilyBall (rB : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) :
    Set (ActiveFamily L m K k Ω) :=
  complexFamilyBall (activeBondSet K k Ω) rB ∩
    selfAdjointFunctions (PositiveBondIn (activeBondSet K k Ω))
def IsRealNhdZero (rB : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (N : Set (ActiveFamily L m K k Ω)) : Prop :=
  N ⊆ realFamilyBall rB K k Ω ∧
    ∃ D : Set (ActiveFamily L m K k Ω),
      ComplexMatrix2.IsRelativelyOpen (realFamilyBall rB K k Ω) D ∧ 0 ∈ D ∧ D ⊆ N
def IsMinimizerContinuation (ε εBar rB : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2)
    (Φ : ActiveFamily L m K k Ω → BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  IsBallDatum ε εBar K k Ω V₀ ∧
    (∃ (_ : Fintype (PositiveBondIn (activeBondSet K k Ω)))
      (_ : Fintype (bondsInside (Ω 0) : Set (BondAtLevel L m K 0))),
      IsHolomorphicMatrixValued (complexFamilyBall (activeBondSet K k Ω) rB)
        fun (B : ActiveFamily L m K k Ω) (c : (bondsInside (Ω 0) : Set (BondAtLevel L m K 0))) =>
          Φ B c) ∧
    (∀ B ∈ complexFamilyBall (activeBondSet K k Ω) rB,
      IsGaugeField complexGaugeGroup (bondsInside (Ω 0)) (Φ B) ∧
        ∀ c ∉ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)), Φ B c = 1) ∧
    ∃ N : Set (ActiveFamily L m K k Ω), IsRealNhdZero rB K k Ω N ∧
      ∀ B ∈ N, HasActiveGaugeRepresentative ε K k Ω (expTwistedDatum B V₀) ∧
        Φ B = activeGaugeRepresentative ε K k Ω (expTwistedDatum B V₀)
def HasUniqueMinimizerContinuation (ε εBar rB : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) : Prop :=
  ∃ Φ, IsMinimizerContinuation ε εBar rB K k Ω V₀ Φ ∧
    ∀ Φ', IsMinimizerContinuation ε εBar rB K k Ω V₀ Φ' →
      EqOn Φ' Φ (complexFamilyBall (activeBondSet K k Ω) rB)
def minimizerContinuation (ε εBar rB : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) :
    ActiveFamily L m K k Ω → BondAtLevel L m K 0 → ComplexMatrix2 :=
  Classical.epsilon (IsMinimizerContinuation ε εBar rB K k Ω V₀)
def continuedMinimalField (ε εBar rB : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) (B : ActiveFamily L m K k Ω) :
    BondAtLevel L m K 0 → ComplexMatrix2 :=
  minimizerContinuation ε εBar rB K k Ω V₀ B
def HasContinuedTowerField (ε εBar rB ξ : ℝ) (K n : ℕ) (Ω' : ℕ → Set (FourTorus L m))
    (X : Set (FourTorus L m)) (W U : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  HasTowerField ε εBar rB ξ K n Ω' X W U ∧
    HasUniqueMinimizerContinuation ε εBar rB K n Ω'
      (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U)
def continuedTowerField (ε εBar rB : ℝ) (K n : ℕ) (Ω' : ℕ → Set (FourTorus L m))
    (X : Set (FourTorus L m)) (W U : BondAtLevel L m K 0 → ComplexMatrix2) :
    BondAtLevel L m K 0 → ComplexMatrix2 :=
  continuedMinimalField ε εBar rB K n Ω'
    (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U) (logRatioFamily K n Ω' X W U)
end PeriodicLattice
end YangMills.Construction
