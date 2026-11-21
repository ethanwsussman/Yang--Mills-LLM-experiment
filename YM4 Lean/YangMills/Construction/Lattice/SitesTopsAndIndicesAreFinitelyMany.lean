import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.SeparatedSequencesIndexSetsPositionsAndSeminorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice SeparatedSequences Matrices
namespace SeparatedRegions
def tracelessFunctionsOn {ι : Type*} (I : Set ι) : Submodule ℂ (ι → ComplexMatrix2) where
  carrier := {f | (∀ i, f i ∈ ComplexMatrix2.traceless) ∧ ∀ i, i ∉ I → f i = 0}
  add_mem' := by
    rintro f g ⟨hf, hf0⟩ ⟨hg, hg0⟩
    exact ⟨fun i => ComplexMatrix2.traceless.add_mem (hf i) (hg i), fun i hi => by
      simp only [Pi.add_apply, hf0 i hi, hg0 i hi, add_zero]⟩
  zero_mem' := ⟨fun _ => ComplexMatrix2.traceless.zero_mem, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨hf, hf0⟩
    exact ⟨fun i => ComplexMatrix2.traceless.smul_mem c (hf i), fun i hi => by
      simp only [Pi.smul_apply, hf0 i hi, smul_zero]⟩
def IsFiniteWithFiniteDimFunctions {ι : Type*} (I : Set ι) : Prop :=
  I.Finite ∧ Module.Finite ℂ (tracelessFunctionsOn I)
def LevelLatticeFinite (L m K n : ℕ) : Prop :=
  Nat.card (SiteAtLevel L m K n) = (2 * L ^ (m + K - n)) ^ 4 ∧
    Finite (BondAtLevel L m K n) ∧ Finite (PlaquetteAtLevel L m K n)
def SeparatedSequenceFinite {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m)) : Prop :=
  (∀ n ≤ S.top, IsFiniteWithFiniteDimFunctions (layerLatticeSites S Ω n)) ∧
    IsFiniteWithFiniteDimFunctions (layerPoints S Ω) ∧
    IsFiniteWithFiniteDimFunctions (siteIndexSet S (Ω 0)) ∧
    IsFiniteWithFiniteDimFunctions (bondIndexSet S (Ω 0)) ∧
    IsFiniteWithFiniteDimFunctions (bondAxisIndexSet S (Ω 0)) ∧
    IsFiniteWithFiniteDimFunctions (leveledIndexSet S Ω) ∧
    (cubeOfPoint S Ω '' layerPoints S Ω).Finite
def FinitenessOfSitesTopsAndIndices : Prop :=
  ∀ L m : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    (∀ K n : ℕ, 0 < K → n ≤ K → LevelLatticeFinite L m K n) ∧
    ∀ S : ScaleData, 0 < S.levels →
      ∀ (g : ℝ) (Ω : ℕ → Set (FourTorus L m)), IsSeparatedWithGap S g Ω →
        SeparatedSequenceFinite S Ω
end SeparatedRegions
end YangMills.Construction
end
