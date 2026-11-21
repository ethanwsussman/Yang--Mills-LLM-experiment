import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open Set
open scoped ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices
namespace EmbeddedSubmanifold
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
structure Chart (M : Set E) where
  dim : ℕ
  source : Set (Fin dim → ℝ)
  param : (Fin dim → ℝ) → E
  isOpen_source : IsOpen source
  contDiffOn_param : ContDiffOn ℝ ∞ param source
  injective_fderiv_param : ∀ u ∈ source, Function.Injective (fderiv ℝ param u)
  injOn_param : InjOn param source
  isRelativelyOpen_image : ∀ W ⊆ source, IsOpen W → ComplexMatrix2.IsRelativelyOpen M (param '' W)
def Chart.coords {M : Set E} (c : Chart M) (O : Set E) : Set (Fin c.dim → ℝ) :=
  c.source ∩ c.param ⁻¹' O
def Chart.pullback {M : Set E} (c : Chart M) (f : E → F) : (Fin c.dim → ℝ) → F :=
  f ∘ c.param
def DifferentiableOnOpen (M O : Set E) (f : E → F) : Prop :=
  ComplexMatrix2.IsRelativelyOpen M O ∧ ∀ c : Chart M, DifferentiableOn ℝ (c.pullback f) (c.coords O)
def tangentSpace (M : Set E) (p : E) : Submodule ℝ E :=
  ⨆ (c : Chart M) (u : Fin c.dim → ℝ) (_ : u ∈ c.source ∧ c.param u = p),
    LinearMap.range (fderiv ℝ c.param u : (Fin c.dim → ℝ) →ₗ[ℝ] E)
def IsTangentDifferential (M : Set E) (f : E → F) (p : E) (L : tangentSpace M p →ₗ[ℝ] F) : Prop :=
  ∀ (c : Chart M) (u : Fin c.dim → ℝ), u ∈ c.source → c.param u = p →
    ∀ (w : Fin c.dim → ℝ) (v : tangentSpace M p), (v : E) = fderiv ℝ c.param u w →
      L v = fderiv ℝ (c.pullback f) u w
def tangentDifferential (M : Set E) (f : E → F) (p : E) : tangentSpace M p →ₗ[ℝ] F :=
  Classical.epsilon (IsTangentDifferential M f p)
def HasDifferentiablePartialsOn (M O : Set E) (f : E → F) : Prop :=
  DifferentiableOnOpen M O f ∧ ∀ (c : Chart M) (k : Fin c.dim),
    DifferentiableOn ℝ (fun u => fderiv ℝ (c.pullback f) u (Pi.single k 1)) (c.coords O)
end EmbeddedSubmanifold
def specialUnitaryPower (σ : Type) : Set (σ → ComplexMatrix2) :=
  ComplexMatrix2.compactProduct fun _ => ComplexMatrix2.FactorKind.group
namespace specialUnitaryPower
variable {σ τ : Type} [Fintype σ] [Fintype τ]
def IsOpenSubset (O : Set (σ → ComplexMatrix2)) : Prop :=
  ComplexMatrix2.IsRelativelyOpen (specialUnitaryPower σ) O
def IsDifferentiableInto (O : Set (σ → ComplexMatrix2)) (f : (σ → ComplexMatrix2) → τ → ComplexMatrix2) : Prop :=
  EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower σ) O f ∧ MapsTo f O (specialUnitaryPower τ)
end specialUnitaryPower
end YangMills.Construction.Matrices
