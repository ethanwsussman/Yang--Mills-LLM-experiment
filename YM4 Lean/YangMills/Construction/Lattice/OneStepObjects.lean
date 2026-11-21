import YangMills.Construction.Lattice.LieFieldsOnBondSets
import YangMills.Construction.Lattice.OneStepSchemes
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
def doubleBlockSymmetricSet (c : BondAtLevel L m K (n + 1)) : SymmetricBondSet L m K n where
  bonds := bondsInDoubleBlock c
  opposite_mem := fun _ hb => ⟨hb.2, hb.1⟩
def twistedConfig (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c))
    (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2) :
    BondAtLevel L m K n → Matrices.ComplexMatrix2 :=
  expTwist (fun b => (a.eval b : Matrices.ComplexMatrix2)) W₀
def stepRatio (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c))
    (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) (x : SiteAtLevel L m K n) : Matrices.ComplexMatrix2 :=
  contourHolonomy s (twistedConfig c a W₀) y x * (contourHolonomy s W₀ y x)⁻¹
def stepLog (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c))
    (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) (x : SiteAtLevel L m K n) : Matrices.ComplexMatrix2 :=
  Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries (stepRatio s c a W₀ y x)
def stepGauge (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c))
    (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) : Matrices.ComplexMatrix2 :=
  Matrices.ComplexMatrix2.matExp (Complex.I • (inverseFourthPowerWeight L •
    ∑ᶠ x ∈ sitesInBlock (levelDepth K n) y, stepLog s c a W₀ y x))
def stepProduct (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c))
    (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  (stepGauge s c a W₀ c.source)⁻¹ * schemeBlockAverage s (twistedConfig c a W₀) c *
    stepGauge s c a W₀ c.target * (schemeBlockAverage s W₀ c)⁻¹
def stepVariable (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c))
    (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries (stepProduct s c a W₀)
def straightenedMap (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (a : LieBondField (doubleBlockSymmetricSet c)) : Matrices.ComplexMatrix2 :=
  inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
    ((crossingPath c x).map fun b => Matrices.ComplexMatrix2.conjugateBy
      (contourHolonomy s W₀ c.source x * pathHolonomy W₀ (axialPath x b.source))
      (a.eval b : Matrices.ComplexMatrix2)).sum
def StepLogsDefined (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c))
    (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2) : Prop :=
  AreContourHolonomiesDefined s (twistedConfig c a W₀) c ∧
    AreContourHolonomiesDefined s W₀ c ∧
    (∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      Matrices.ComplexMatrix2.operatorNorm (stepRatio s c a W₀ c.source x - 1) < 1) ∧
    ∀ x ∈ sitesInBlock (levelDepth K n) c.target,
      Matrices.ComplexMatrix2.operatorNorm (stepRatio s c a W₀ c.target x - 1) < 1
def StepVariableDefined (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c))
    (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2) : Prop :=
  StepLogsDefined s c a W₀ ∧ IsSchemeAverageDefined s (twistedConfig c a W₀) c ∧
    IsSchemeAverageDefined s W₀ c ∧
    Matrices.ComplexMatrix2.operatorNorm (stepProduct s c a W₀ - 1) < 1
end YangMills.Construction.PeriodicLattice
