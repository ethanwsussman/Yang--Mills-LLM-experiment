import YangMills.Construction.Lattice.AveragesAndLinearPartsAtAComplexBackground
import YangMills.Construction.Lattice.FlatDeterminingSetOfASeparatedSequence
import YangMills.Construction.Lattice.OneFormsInTheUnitsOfALevel
import YangMills.Construction.Lattice.SeparatedSequenceInLastUnits
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set Matrices
namespace PeriodicLattice
variable {L m K : ℕ}
def restrictToDoubleBlockLinear {n : ℕ} (c : BondAtLevel L m K (n + 1)) :
    LieBondFunction L m (levelDepth K n) →ₗ[ℂ] LieBondField (doubleBlockSymmetricSet c) where
  toFun := doubleBlockRestriction c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
section LinearParts
variable [∀ (n : ℕ) (d : BondAtLevel L m K (n + 1)),
  Fintype (PositiveBondsOf (doubleBlockSymmetricSet d))]
def linearStepMap {n : ℕ} (W : BondAtLevel L m K n → ComplexMatrix2) :
    LieBondFunction L m (levelDepth K n) →ₗ[ℂ] LieBondFunction L m (levelDepth K (n + 1)) :=
  LinearMap.pi fun c => twistedStepDerivative W c.1 ∘ₗ restrictToDoubleBlockLinear c.1
def linearStepProduct (B : Set (BondAtLevel L m K 0)) (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    (n : ℕ) → LieBondFunction L m (levelDepth K 0) →ₗ[ℂ] LieBondFunction L m (levelDepth K n)
  | 0 => LinearMap.id
  | n + 1 => linearStepMap (complexIterate B U n) ∘ₗ linearStepProduct B U n
end LinearParts
def blockAverageProduct (B : Set (BondAtLevel L m K 0)) (U : BondAtLevel L m K 0 → ComplexMatrix2)
    (μ : SiteAtLevel L m K 0 → ↥ComplexMatrix2.traceless) :
    (n : ℕ) → SiteAtLevel L m K n → ↥ComplexMatrix2.traceless
  | 0 => μ
  | n + 1 => fun y => twistedBlockAverage (complexIterate B U n) y
      fun x => blockAverageProduct B U μ n x.1
end PeriodicLattice
namespace SeparatedSequences
open PeriodicLattice
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
def classCeiling (L : ℕ) : ℝ := ((L : ℝ) ^ 2)⁻¹ * complexBackgroundRadius L
def IsClassDecomposition (α₀ α₁ : ℝ) (W U A : FineBond L m S → ComplexMatrix2) : Prop :=
  IsGaugeField compactGaugeGroup (bondsInside (Ω 0)) U ∧
    A ∈ Bare.bondFormSpace (Ω 0) ∧
    (∀ v ∈ (bondsInside (Ω 0) : Set (FineBond L m S)),
      W v = expTwist (fun c => ((S.finestMesh L : ℝ) : ℂ) • A c) U v) ∧
    ∀ n ≤ S.top,
      (∀ p ∈ (plaquettesInside (Ω 0) : Set (PlaquetteAtLevel L m S.levels 0)),
        (p.origin : FourTorus L m) ∈ layerSet S Ω n →
          ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) <
            α₀ * S.finestMesh L ^ 2 * (S.levelMesh L n)⁻¹ ^ 2) ∧
      ∀ v ∈ (bondsInside (Ω 0) : Set (FineBond L m S)), v.IsPositivelyOriented →
        (v.source : FourTorus L m) ∈ layerSet S Ω n →
          S.levelMesh L n * ComplexMatrix2.operatorNorm (A v) < α₁
def admissibleClass (α₀ α₁ : ℝ) : Set (FineBond L m S → ComplexMatrix2) :=
  {W | Bare.IsComplexGaugeFieldInside (Ω 0) W ∧
    (∀ v ∉ (bondsInside (Ω 0) : Set (FineBond L m S)), W v = 1) ∧
    ∃ U A : FineBond L m S → ComplexMatrix2, IsClassDecomposition S Ω α₀ α₁ W U A}
section SeriesExpansions
variable [∀ (n : ℕ) (c : BondAtLevel L m S.levels (n + 1)),
  Fintype (PositiveBondsOf (doubleBlockSymmetricSet c))]
def averagingExpansionMap (W : FineBond L m S → ComplexMatrix2) :
    (k : ℕ) → (FineBond L m S → ComplexMatrix2) →
      PositivelyOrientedBond L m (levelDepth S.levels k) → ComplexMatrix2
  | 0, A, c => A c.1
  | k + 1, A, c => (((S.levelMesh L (k + 1))⁻¹ : ℝ) : ℂ) •
      (linearStepProduct (bondsInside (Ω 0)) W (k + 1)
        (fun v => toTraceless (bondFunction S A v.1)) c : ComplexMatrix2)
abbrev PositiveLevelBonds (T : Set (Σ k : ℕ, BondAtLevel L m S.levels k)) : Type :=
  {q : Σ k : ℕ, BondAtLevel L m S.levels k // q ∈ T ∧ q.2.IsPositivelyOriented}
def rowsOn (T : Set (Σ k : ℕ, BondAtLevel L m S.levels k)) (W A : FineBond L m S → ComplexMatrix2) :
    PositiveLevelBonds S T → ComplexMatrix2 :=
  fun c => averagingExpansionMap S Ω W c.1.1 A ⟨c.1.2, c.2.2⟩
def interiorOutwardExpansions (W A : FineBond L m S → ComplexMatrix2) :
    PositiveLevelBonds S (BondKinds.interiorOutwardSet S Ω) → ComplexMatrix2 :=
  rowsOn S Ω (BondKinds.interiorOutwardSet S Ω) W A
end SeriesExpansions
def siteExpansionMap (W : FineBond L m S → ComplexMatrix2) :
    (k : ℕ) → (SiteAtLevel L m S.levels 0 → ComplexMatrix2) →
      SiteAtLevel L m S.levels k → ComplexMatrix2
  | 0, μ, y => μ y
  | k + 1, μ, y =>
      (blockAverageProduct (bondsInside (Ω 0)) W (fun x => toTraceless (μ x)) (k + 1) y :
        ComplexMatrix2)
def layerSiteValue (W : FineBond L m S → ComplexMatrix2)
    (μ : SiteAtLevel L m S.levels 0 → ComplexMatrix2) (y : FourTorus L m) : ComplexMatrix2 :=
  siteExpansionMap S Ω W (layerLevel S Ω y) μ
    (Classical.epsilon fun x : SiteAtLevel L m S.levels (layerLevel S Ω y) =>
      (x : FourTorus L m) = y)
end SeparatedSequences
end YangMills.Construction
end
