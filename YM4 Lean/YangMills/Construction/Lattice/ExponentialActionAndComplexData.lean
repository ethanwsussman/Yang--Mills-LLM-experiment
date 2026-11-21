import YangMills.Construction.Lattice.InwardBondsAndSetsInForce
import YangMills.Construction.Lattice.LieFieldsOnBondSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K n : ℕ}
def LieBondField.expTwistOn {P : SymmetricBondSet L m K n} (a : LieBondField P)
    (W : BondAtLevel L m K n → Matrices.ComplexMatrix2) : BondAtLevel L m K n → Matrices.ComplexMatrix2 :=
  expTwist (fun b => (a.eval b : Matrices.ComplexMatrix2)) W
def IsComplexCutDatum (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (F : Set (Σ j : ℕ, BondAtLevel L m K j))
    (X : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) : Prop :=
  ∀ j ≤ k, IsGaugeField complexGaugeGroup (determiningBondsAtDiff K k Ω F j) (X j)
def IsComplexSiteMap (S : Set (SiteAtLevel L m K 0))
    (v : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  ∀ x ∈ S, v x ∈ complexGaugeGroup
def gaugeTransformDatum (v : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (X : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2 :=
  fun j => gaugeTransform (restrictGaugeMap j v) (X j)
theorem gaugeTransformDatum_apply (v : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (X : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) (j : ℕ) (c : BondAtLevel L m K j) :
    gaugeTransformDatum v X j c =
      v (c.source.toSublattice (levelDepth K 0)) * X j c *
        (v (c.target.toSublattice (levelDepth K 0)))⁻¹ :=
  rfl
end PeriodicLattice
end YangMills.Construction
