import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Lattice.BareDoubleBlocks
import YangMills.Construction.Lattice.BlockAxialGaugeOutsideTheNodes
import YangMills.Construction.Lattice.InwardBondsAndSetsInForce
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def IsCompleteSequence (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) : Prop :=
  ∀ j ≤ k, ∀ c ∈ activeBondsAt K k Ω j, bareBlockPair c ⊆ Ω 0
def IsActiveLinkDatum (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) : Prop :=
  IsLinkDatum (activeBondSet K k Ω) V
def activeAveragingMap {K : ℕ} (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) (j : ℕ)
    (c : BondAtLevel L m K j) : Matrices.ComplexMatrix2 :=
  partialBareBlockField (Averaging.smoothingRadius L) U c
def activeConstraintSet (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {U | IsCompleteSequence K k Ω ∧ U ∈ gaugeFieldsInside K (Ω 0) ∧
    ∀ q ∈ activeBondSet K k Ω, activeAveragingMap U q.1 q.2 = V q.1 q.2}
def IsActiveCritical (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  U ∈ activeConstraintSet K k Ω V ∧
    ∀ (δ : ℝ) (γ : ℝ → BondAtLevel L m K 0 → Matrices.ComplexMatrix2), 0 < δ →
      (∀ t ∈ Ioo (-δ) δ, γ t ∈ activeConstraintSet K k Ω V) →
      (∀ b r s, DifferentiableOn ℝ (fun t => γ t b r s) (Ioo (-δ) δ)) → γ 0 = U →
      deriv (fun t => actionInside K (Ω 0) (γ t)) 0 = 0
def activeRegularCriticalSet (ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {U | IsActiveCritical K k Ω V U ∧ IsRegularField ε K k Ω U}
def HasMinimalOrbit (ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) : Prop :=
  IsCompleteSequence K k Ω ∧ ∃ U ∈ activeRegularCriticalSet ε K k Ω V,
    activeRegularCriticalSet ε K k Ω V = endpointFixingOrbit Ω (activeBondSet K k Ω) U
def IsActiveMinimalField (ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  HasMinimalOrbit ε K k Ω V ∧ U ∈ activeRegularCriticalSet ε K k Ω V
def activeMinimalField (ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  Classical.epsilon (IsActiveMinimalField ε K k Ω V)
end PeriodicLattice
end YangMills.Construction
