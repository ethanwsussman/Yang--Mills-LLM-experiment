import YangMills.Construction.Lattice.InteriorRegionsNearbyCurvature
import YangMills.Construction.Lattice.SitesNearASiteAndTheirCells
import YangMills.Construction.Lattice.SolutionsAndSourcesOfTheSystemOfATriple
import YangMills.Construction.Lattice.StoredBondFieldSystems
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.SeparatedSequences YangMills.Construction.SeparatedRegions YangMills.Construction.Matrices
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SequenceTriples
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
def sitesNearBase : Set (SiteAtLevel L m S.levels 0) :=
  {x | IsWithinFinestMesh S.levels S.unitLevel (x : FourTorus L m) (Ω 0)}
def bondsNearBase : Set (FineBond L m S) :=
  {b | b.IsPositivelyOriented ∧ b.source ∈ sitesNearBase S Ω ∧
    b.target ∈ sitesNearBase S Ω}
def IsReadAtLayerPoint (y : FourTorus L m) (b : FineBond L m S) : Prop :=
  (b.source : FourTorus L m) ∈ nearbyCellsUnion S Ω y ∨
    (b.source : FourTorus L m) ∉ Ω 0 ∧
      IsWithinFinestMesh S.levels S.unitLevel (b.source : FourTorus L m) (nearbyCellsUnion S Ω y)
def IsBondTranslate (c b : FineBond L m S) (ν : Fin 4) : Prop :=
  c.source = b.source + unitStep L m (levelDepth S.levels 0) ν ∧
    c.target = b.target + unitStep L m (levelDepth S.levels 0) ν
structure IsSmallLog (ε : ℝ) (U A : FineBond L m S → ComplexMatrix2) : Prop where
  mem_algebra : ∀ b ∈ bondsNearBase S Ω, A b ∈ complexLieAlgebra
  eq_exp : ∀ b ∈ bondsNearBase S Ω,
    U b = ComplexMatrix2.matExp (Complex.I • (((S.finestMesh L : ℝ) : ℂ) • A b))
  norm_le : ∀ y ∈ layerPoints S Ω, ∀ b ∈ bondsNearBase S Ω, IsReadAtLayerPoint S Ω y b →
    layerPointMesh S Ω y * ComplexMatrix2.operatorNorm (A b) ≤ ε
  diff_norm_le : ∀ y ∈ layerPoints S Ω, ∀ b ∈ bondsNearBase S Ω,
    ∀ c ∈ bondsNearBase S Ω, ∀ ν : Fin 4, IsBondTranslate S c b ν →
      IsReadAtLayerPoint S Ω y b →
        layerPointMesh S Ω y ^ 2 * ComplexMatrix2.operatorNorm (A c - A b) ≤ ε * S.finestMesh L
structure HasTrivialGaugeBounds (ε : ℝ) (U J : FineBond L m S → ComplexMatrix2)
    (j : LeveledBond L m S → ComplexMatrix2) : Prop where
  log : ∃ A : FineBond L m S → ComplexMatrix2, IsSmallLog S Ω ε U A
  bondSeminorm_le : ∀ y ∈ layerPoints S Ω, (localSeminorms S Ω y).onBonds (-3) J ≤ ENNReal.ofReal ε
  expansionSeminorm_le : ∀ y ∈ layerPoints S Ω, (localSeminorms S Ω y).onExpansions (-3) j ≤ ENNReal.ofReal ε
def gaugeConjugateBonds (u : SiteAtLevel L m S.levels 0 → ComplexMatrix2)
    (j : LeveledBond L m S → ComplexMatrix2) : LeveledBond L m S → ComplexMatrix2 :=
  fun c => ComplexMatrix2.conjugateBy (u (SiteAtLevel.toBareSite c.2.source)) (j c)
structure IsSmallInTrivialGauge (g ε : ℝ) (A : Set (FourTorus L m))
    (U J : FineBond L m S → ComplexMatrix2) (j : LeveledBond L m S → ComplexMatrix2) : Prop where
  interior : IsInteriorRegion S.levels S.unitLevel (Ω 0) A
  epsilon_pos : 0 < ε
  triple : IsAmbientTriple S Ω g A U J j
  bounds : HasTrivialGaugeBounds S Ω ε U J j
structure IsSmallTriple (g ε : ℝ) (A : Set (FourTorus L m))
    (U J : FineBond L m S → ComplexMatrix2) (j : LeveledBond L m S → ComplexMatrix2) : Prop where
  interior : IsInteriorRegion S.levels S.unitLevel (Ω 0) A
  epsilon_pos : 0 < ε
  triple : IsAmbientTriple S Ω g A U J j
  gauge : ∃ u : SiteAtLevel L m S.levels 0 → ComplexMatrix2,
    (∀ x ∈ sitesNearBase S Ω, u x ∈ compactGaugeGroup) ∧
      HasTrivialGaugeBounds S Ω ε (gaugeTransform u U) (conjugateBondForm u J)
        (gaugeConjugateBonds S u j)
end YangMills.Construction.SequenceTriples
end
