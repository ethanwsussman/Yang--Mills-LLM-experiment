import YangMills.Construction.Lattice.SeparatedSequencesIndexSetsPositionsAndSeminorms
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SeparatedRegions
open YangMills.Construction.PeriodicLattice YangMills.Construction.SeparatedSequences YangMills.Construction.Matrices
inductive IndexKind
  | sites
  | bonds
  | bondAxes
  | tops
  | leveled
namespace IndexKind
def Carrier (L m : ℕ) (S : ScaleData) : IndexKind → Type
  | sites => SiteAtLevel L m S.levels 0
  | bonds => FineBond L m S
  | bondAxes => FineBond L m S × Fin 4
  | tops => FourTorus L m
  | leveled => LeveledBond L m S
variable {L m : ℕ} (S : ScaleData)
def indexSet (Ω : ℕ → Set (FourTorus L m)) : (k : IndexKind) → Set (k.Carrier L m S)
  | sites => siteIndexSet S (Ω 0)
  | bonds => bondIndexSet S (Ω 0)
  | bondAxes => bondAxisIndexSet S (Ω 0)
  | tops => layerPoints S Ω
  | leveled => leveledIndexSet S Ω
def location (Ω : ℕ → Set (FourTorus L m)) : (k : IndexKind) → k.Carrier L m S → FourTorus L m
  | sites => siteLocation S Ω
  | bonds => bondLocation S Ω
  | bondAxes => bondAxisLocation S Ω
  | tops => id
  | leveled => leveledLocation S Ω
end IndexKind
variable {L m : ℕ} (S : ScaleData)
def l2LocalNorm {ι : Type*} (Ω : ℕ → Set (FourTorus L m)) (I : Set ι) (pos : ι → FourTorus L m)
    (s : ℝ) (f : ι → ComplexMatrix2) (y : FourTorus L m) : ℝ≥0∞ :=
  ENNReal.ofReal (layerPointMesh S Ω y ^ (-s - 2)) *
    (ENNReal.ofReal (S.finestMesh L ^ 4) *
      ∑' i : {i // i ∈ I ∧ pos i = y}, ENNReal.ofReal (ComplexMatrix2.operatorNorm (f i)) ^ 2) ^ (1 / 2 : ℝ)
def supLocalNorm (Ω : ℕ → Set (FourTorus L m)) (k : IndexKind) (s : ℝ)
    (f : k.Carrier L m S → ComplexMatrix2) (y : FourTorus L m) : ℝ≥0∞ :=
  scaledLocalMax S Ω (k.indexSet S Ω) (k.location S Ω) s f y
def localNorm (Ω : ℕ → Set (FourTorus L m)) : (k : IndexKind) → ℝ →
    (k.Carrier L m S → ComplexMatrix2) → FourTorus L m → ℝ≥0∞
  | .sites => l2LocalNorm S Ω (IndexKind.sites.indexSet S Ω)
      (IndexKind.sites.location S Ω)
  | .bonds => l2LocalNorm S Ω (IndexKind.bonds.indexSet S Ω)
      (IndexKind.bonds.location S Ω)
  | .bondAxes => l2LocalNorm S Ω (IndexKind.bondAxes.indexSet S Ω)
      (IndexKind.bondAxes.location S Ω)
  | .tops => supLocalNorm S Ω .tops
  | .leveled => supLocalNorm S Ω .leveled
end YangMills.Construction.SeparatedRegions
