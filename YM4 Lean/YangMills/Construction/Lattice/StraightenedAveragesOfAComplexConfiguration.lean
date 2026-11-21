import YangMills.Construction.Lattice.CubesAndPillars
import YangMills.Construction.Lattice.DataOnTheBareDoubleBlockOfABond
import YangMills.Construction.Lattice.IteratesOfAComplexConfiguration
import YangMills.Construction.Lattice.OneStepOperatorsAtAComplexReference
import YangMills.Construction.Lattice.TowersOverSetsOfSites
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K k n : ℕ}
def blockPairComplexAverage (c : BondAtLevel L m K k) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (n : ℕ) : BondAtLevel L m K n → Matrices.ComplexMatrix2 :=
  complexIterate (bareBondsInBlockPair c) U n
def BlockPairComplexAveragesDefined (c : BondAtLevel L m K k)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  IsComplexIterationData k (bareBondsInBlockPair c) U ∧
    ∀ n ≤ k, ∀ b ∈ blockPairBondsAt n c,
      ComplexIterateDefinedAt (bareBondsInBlockPair c) U n b
def blockPairFineForm (c : BondAtLevel L m K k) (A : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    LieBondField (blockPairSymmetricBondsAt 0 c) :=
  fun b => toTraceless (A b.1)
def restrictToStepBonds {P : SymmetricBondSet L m K n} (c' : BondAtLevel L m K (n + 1))
    (a : LieBondField P) : LieBondField (doubleBlockSymmetricSet c') :=
  fun b => a.eval b.1
def restrictToStepBondsLinearMap (P : SymmetricBondSet L m K n) (c' : BondAtLevel L m K (n + 1)) :
    LieBondField P →ₗ[ℂ] LieBondField (doubleBlockSymmetricSet c') where
  toFun := restrictToStepBonds c'
  map_add' a a' := funext fun b => LieBondField.eval_add a a' b.1
  map_smul' z a := by
    funext b
    exact LieBondField.eval_smul z a b.1
def twistedStraightenedAverage (c : BondAtLevel L m K k) (U A : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    (n : ℕ) → LieBondField (blockPairSymmetricBondsAt n c)
  | 0 => ((finestMeshInLevelUnits L k : ℝ) : ℂ) • blockPairFineForm c A
  | n + 1 => fun c' => twistedStepMap (blockPairComplexAverage c U n) c'.1
      (restrictToStepBonds c'.1 (twistedStraightenedAverage c U A n))
def TwistedStraightenedAverageDefined (c : BondAtLevel L m K k)
    (U A : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) (n : ℕ) : Prop :=
  n ≤ k ∧ ∀ j < n, ∀ c' : PositiveBondsOf (blockPairSymmetricBondsAt (j + 1) c),
    StepVariableDefined .centred c'.1
        (restrictToStepBonds c'.1 (twistedStraightenedAverage c U A j))
        (blockPairComplexAverage c U j) ∧
      stepVariable .centred c'.1
        (restrictToStepBonds c'.1 (twistedStraightenedAverage c U A j))
        (blockPairComplexAverage c U j) ∈ Matrices.ComplexMatrix2.traceless
def twistedStepFactor (c : BondAtLevel L m K k) (U A : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) (n : ℕ)
    (y : SiteAtLevel L m K (n + 1)) : Matrices.ComplexMatrix2 :=
  stepGauge .centred (Bond.forwardFrom y 0)
    (restrictToStepBonds (Bond.forwardFrom y 0) (twistedStraightenedAverage c U A n))
    (blockPairComplexAverage c U n) y
def twistedAccumulatedGauge (c : BondAtLevel L m K k) (U A : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    (n : ℕ) → SiteAtLevel L m K n → Matrices.ComplexMatrix2
  | 0 => fun _ => 1
  | n + 1 => fun y => twistedAccumulatedGauge c U A n (y.toSublattice (levelDepth K n)) *
      twistedStepFactor c U A n y
def TwistedAccumulatedGaugeDefined (c : BondAtLevel L m K k)
    (U A : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) (n : ℕ) : Prop :=
  n ≤ k ∧ ∀ j < n, TwistedStraightenedAverageDefined c U A j ∧
    ∀ y ∈ (sitesIn (SeparatedSequences.BondKinds.bondBlockPairAt (j + 1) c) :
        Set (SiteAtLevel L m K (j + 1))),
      StepGaugeDefinedAt .centred (Bond.forwardFrom y 0)
        (restrictToStepBonds (Bond.forwardFrom y 0) (twistedStraightenedAverage c U A j))
        (blockPairComplexAverage c U j) y
section StepDerivatives
variable [∀ (n : ℕ) (c' : BondAtLevel L m K (n + 1)),
  Fintype (PositiveBondsOf (doubleBlockSymmetricSet c'))]
def BlockPairStepDerivativesDefined (c : BondAtLevel L m K k)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  ∀ n < k, ∀ c' : PositiveBondsOf (blockPairSymmetricBondsAt (n + 1) c),
    TwistedStepDerivativeDefined (blockPairComplexAverage c U n) c'.1
def blockPairStepDerivative (c : BondAtLevel L m K k) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (n : ℕ) :
    LieBondField (blockPairSymmetricBondsAt n c) →ₗ[ℂ]
      LieBondField (blockPairSymmetricBondsAt (n + 1) c) :=
  LinearMap.pi fun c' => twistedStepDerivative (blockPairComplexAverage c U n) c'.1 ∘ₗ
    restrictToStepBondsLinearMap (blockPairSymmetricBondsAt n c) c'.1
def blockPairDerivativeProduct (c : BondAtLevel L m K k) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    (n : ℕ) → LieBondField (blockPairSymmetricBondsAt 0 c) →ₗ[ℂ]
      LieBondField (blockPairSymmetricBondsAt n c)
  | 0 => LinearMap.id
  | n + 1 => blockPairStepDerivative c U n ∘ₗ blockPairDerivativeProduct c U n
def blockPairTopBond (c : BondAtLevel L m K k) (hc : c.IsPositivelyOriented) :
    PositiveBondsOf (blockPairSymmetricBondsAt k c) :=
  ⟨c, Or.inl (Or.inr ⟨rfl, rfl⟩), hc⟩
def twistedStraightenedOperator (c : BondAtLevel L m K k) (hc : c.IsPositivelyOriented)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    LieBondField (blockPairSymmetricBondsAt 0 c) →ₗ[ℂ] ↥Matrices.ComplexMatrix2.traceless :=
  ((finestMeshInLevelUnits L k : ℝ) : ℂ) •
    (LinearMap.proj (blockPairTopBond c hc) ∘ₗ blockPairDerivativeProduct c U k)
open Classical in
def twistedStraightenedKernel (c : BondAtLevel L m K k) (hc : c.IsPositivelyOriented)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (b : PositiveBondsOf (blockPairSymmetricBondsAt 0 c)) :
    ↥Matrices.ComplexMatrix2.traceless →ₗ[ℂ] ↥Matrices.ComplexMatrix2.traceless :=
  twistedStraightenedOperator c hc U ∘ₗ
    LinearMap.single ℂ
      (fun _ : PositiveBondsOf (blockPairSymmetricBondsAt 0 c) => ↥Matrices.ComplexMatrix2.traceless) b
end StepDerivatives
def iteratedTwistedBlockAverage (c : BondAtLevel L m K k) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (l : SiteAtLevel L m K 0 → ↥Matrices.ComplexMatrix2.traceless) :
    (n : ℕ) → SiteAtLevel L m K n → ↥Matrices.ComplexMatrix2.traceless
  | 0 => l
  | n + 1 => fun y => twistedBlockAverage (blockPairComplexAverage c U n) y
      fun x => iteratedTwistedBlockAverage c U l n x.1
open Classical in
def twistedBlockAverageOperator (c : BondAtLevel L m K k) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (y : SiteAtLevel L m K k) (l : LieSiteField (blockSitesAtLevel 0 y)) :
    ↥Matrices.ComplexMatrix2.traceless :=
  iteratedTwistedBlockAverage c U
    (fun x => if h : x ∈ blockSitesAtLevel 0 y then l ⟨x, h⟩ else 0) k y
def twistedBlockTransport (c : BondAtLevel L m K k) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    (n : ℕ) → SiteAtLevel L m K n → SiteAtLevel L m K 0 → Matrices.ComplexMatrix2
  | 0, _, _ => 1
  | n + 1, y, x => contourHolonomy .centred (blockPairComplexAverage c U n) y
      (Pillars.coarserSite n x) *
    twistedBlockTransport c U n (Pillars.coarserSite n x) x
end YangMills.Construction.PeriodicLattice
