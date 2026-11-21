import YangMills.Construction.Lattice.AveragingOnPart
import YangMills.Construction.Lattice.ConsistencyOfLiftsAndAveragesSetting
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K n : ℕ}
def OneOfFourHolds (A B C D : Prop) : Prop :=
  (A ∧ ¬B ∧ ¬C ∧ ¬D) ∨ (¬A ∧ B ∧ ¬C ∧ ¬D) ∨ (¬A ∧ ¬B ∧ C ∧ ¬D) ∨ (¬A ∧ ¬B ∧ ¬C ∧ D)
def DoubleBlockBondClassification (c : BondAtLevel L m K (n + 1)) : Prop :=
  unitBlock c.source ∩ unitBlock c.target = ∅ ∧
  (∀ v ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)),
    OneOfFourHolds
      ((v.source : FourTorus L m) ∈ unitBlock c.source ∧ (v.target : FourTorus L m) ∈ unitBlock c.source)
      ((v.source : FourTorus L m) ∈ unitBlock c.target ∧ (v.target : FourTorus L m) ∈ unitBlock c.target)
      (v ∈ (bondCorridor c : Set (BondAtLevel L m K n)))
      (v.opposite ∈ (bondCorridor c : Set (BondAtLevel L m K n)))) ∧
  IsReversalClosed (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) ∧
  (bondsInDoubleBlock c.opposite : Set (BondAtLevel L m K n)) = bondsInDoubleBlock c ∧
  (bondCorridor c.opposite : Set (BondAtLevel L m K n)) = Bond.opposite '' bondCorridor c
def ContoursStayInBlocks (c : BondAtLevel L m K (n + 1)) : Prop :=
  ∀ y : SiteAtLevel L m K (n + 1), y = c.source ∨ y = c.target →
    ∀ x ∈ sitesInBlock (levelDepth K n) y, ∀ Γ ∈ contourSet y x,
      (∀ z ∈ pathSites (y.toSublattice (levelDepth K n)) x Γ, (z : FourTorus L m) ∈ unitBlock y) ∧
      ∀ v ∈ Γ, v ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))
def AxialPathsSpanDoubleBlock (c : BondAtLevel L m K (n + 1)) : Prop :=
  (∀ x ∈ sitesInBlock (levelDepth K n) c.source,
    (shiftAcross c x : FourTorus L m) ∈ unitBlock c.target ∧
    (∃ (μ : Fin 4) (k : ℤ), IsAxialDisplacement x (shiftAcross c x) μ k) ∧
    (crossingPath c x).length = L ∧
    (∀ z ∈ pathSites x (shiftAcross c x) (crossingPath c x), (z : FourTorus L m) ∈ bondDoubleBlock c) ∧
    ∀ v ∈ crossingPath c x, v ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))) ∧
  (bondCorridor c : Set (BondAtLevel L m K n)).Nonempty
def DoubleBlockPlaquetteBondsInside (c : BondAtLevel L m K (n + 1)) : Prop :=
  ∀ p ∈ (doubleBlockPlaquettes c : Set (PlaquetteAtLevel L m K n)),
    ∀ v ∈ p.boundaryBonds, v ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))
def AverageDependsOnDoubleBlock (c : BondAtLevel L m K (n + 1)) : Prop :=
  ∀ U ∈ compactGaugeFields L m (levelDepth K n), ∀ U' ∈ compactGaugeFields L m (levelDepth K n),
    (∀ v ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), U v = U' v) →
    (U ∈ smallFieldsAtSmoothingRadius c ↔ U' ∈ smallFieldsAtSmoothingRadius c) ∧
    ((IsRegularAveragingCase (Averaging.smoothingRadius L) U c ∧
        IsRegularAveragingCase (Averaging.smoothingRadius L) U' c) ∨
      (IsSecondAveragingCase (Averaging.smoothingRadius L) U c ∧
        IsSecondAveragingCase (Averaging.smoothingRadius L) U' c) ∨
      (IsThirdAveragingCase (Averaging.smoothingRadius L) U c ∧
        IsThirdAveragingCase (Averaging.smoothingRadius L) U' c)) ∧
    blockAverageAtSmoothingRadius U c = blockAverageAtSmoothingRadius U' c
def DoubleBlockStructure.Statement : Prop :=
  ∀ L m K n : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → n < K →
    ∀ c : BondAtLevel L m K (n + 1),
      DoubleBlockBondClassification c ∧
      ContoursStayInBlocks c ∧
      AxialPathsSpanDoubleBlock c ∧
      DoubleBlockPlaquetteBondsInside c ∧
      (c.IsPositivelyOriented → AverageDependsOnDoubleBlock c)
end PeriodicLattice
end YangMills.Construction
