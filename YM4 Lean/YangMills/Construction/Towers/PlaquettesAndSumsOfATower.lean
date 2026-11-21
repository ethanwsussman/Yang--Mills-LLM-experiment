import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.FormsOnTowers
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FaceSums
def finSuppLieFields (ι : Type*) : Submodule ℝ (ι → Matrices.ComplexMatrix2) where
  carrier := {f | (∀ σ, f σ ∈ Matrices.ComplexMatrix2.hermitianTraceless) ∧ HasFiniteSupp f}
  add_mem' := by
    rintro f g ⟨hf, sf⟩ ⟨hg, sg⟩
    refine ⟨fun σ => Matrices.ComplexMatrix2.hermitianTraceless.add_mem (hf σ) (hg σ), ?_⟩
    exact (sf.union sg).subset (Function.support_add f g)
  zero_mem' := ⟨fun _ => Matrices.ComplexMatrix2.hermitianTraceless.zero_mem, by simp [HasFiniteSupp]⟩
  smul_mem' := by
    rintro a f ⟨hf, sf⟩
    refine ⟨fun σ => Matrices.ComplexMatrix2.hermitianTraceless.smul_mem a (hf σ), ?_⟩
    exact sf.subset (Function.support_const_smul_subset a f)
def PairingIsInner (ι : Type*) : Prop :=
  (∀ f g : ι → Matrices.ComplexMatrix2, (∀ σ, f σ ∈ Matrices.ComplexMatrix2.hermitianTraceless) →
    (∀ σ, g σ ∈ Matrices.ComplexMatrix2.hermitianTraceless) →
    (HasFiniteSupp f ∨ HasFiniteSupp g) →
    (Function.support fun σ => Matrices.ComplexMatrix2.halfTrace (f σ * g σ)).Finite ∧
      (traceFinsumPairing f g).im = 0) ∧
  ∃ c : InnerProductSpace.Core ℝ (finSuppLieFields ι),
    ∀ f g : finSuppLieFields ι,
      ((c.inner f g : ℝ) : ℂ) =
        traceFinsumPairing (f : ι → Matrices.ComplexMatrix2) (g : ι → Matrices.ComplexMatrix2)
def HasLieFieldDim {ι : Type*} (S : Set ι) : Prop :=
  S.Finite ∧ (∀ f : S → Matrices.ComplexMatrix2, HasFiniteSupp f) ∧
    FiniteDimensional ℝ (finSuppLieFields S) ∧
    Module.finrank ℝ (finSuppLieFields S) = 3 * S.ncard
def FaceVerticesPeriodic (L n k j : ℕ) : Prop :=
  ∀ (x x' : Vertex L n k j) (μ ν μ' ν' : Fin 4) (h : μ < ν) (h' : μ' < ν'),
    [x, x + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ,
      x + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ +
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) ν,
      x + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) ν].Nodup ∧
    (PeriodicLattice.Plaquette.vertices (⟨x, μ, ν, h⟩ : Face L n k j) =
        PeriodicLattice.Plaquette.vertices (⟨x', μ', ν', h'⟩ : Face L n k j) →
      (x, μ, ν) = (x', μ', ν'))
def FaceVerticesFullSpace (L k j : ℕ) : Prop :=
  ∀ (x x' : FullSpace.Vertex L k j) (μ ν μ' ν' : Fin 4) (h : μ < ν) (h' : μ' < ν'),
    [x, x + InfiniteLattice.axisStep (meshAt L k j) μ,
      x + InfiniteLattice.axisStep (meshAt L k j) μ +
        InfiniteLattice.axisStep (meshAt L k j) ν,
      x + InfiniteLattice.axisStep (meshAt L k j) ν].Nodup ∧
    (FullSpace.faceCorners (⟨x, μ, ν, h⟩ : FullSpace.Face L k j) =
        FullSpace.faceCorners (⟨x', μ', ν', h'⟩ : FullSpace.Face L k j) →
      (x, μ, ν) = (x', μ', ν'))
def FacesAndPairings : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j ≤ k →
    (∀ n : ℕ, 0 < n →
      FaceVerticesPeriodic L n k j ∧
      (∀ S : Set (Vertex L n k j), PairingIsInner S ∧ HasLieFieldDim S) ∧
      (∀ S : Set (PositiveEdge L n k j), PairingIsInner S ∧ HasLieFieldDim S) ∧
      (∀ S : Set (Face L n k j), PairingIsInner S ∧ HasLieFieldDim S)) ∧
    FaceVerticesFullSpace L k j ∧
    (∀ S : Set (FullSpace.Vertex L k j), PairingIsInner S) ∧
    (∀ S : Set (FullSpace.PositiveEdge (meshAt L k j)), PairingIsInner S) ∧
    (∀ S : Set (FullSpace.Face L k j), PairingIsInner S)
end YangMills.Construction.Tower.FaceSums
end
