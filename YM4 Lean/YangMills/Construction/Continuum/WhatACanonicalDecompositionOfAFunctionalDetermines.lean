import YangMills.Construction.LimitTheorem.AssertionsAtGivenConstants
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set Topology
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.CanonicalDecompositionUniqueness
open SeparatedTuples ReflectionPositivity.TupleForm
open LimitTheorem (transportedDecomposition)
open ReflectionPositivity.Reconstruction (posTupleVec timeBasisVec)
def IsUniquelyIsomorphic (A B : SeparatedTuples.DecompositionData) : Prop :=
  ∃ h : A.space → B.space, (∀ ξ, B.comp (h ξ) = A.comp ξ) ∧
    (∀ k : A.space → B.space, (∀ ξ, B.comp (k ξ) = A.comp ξ) → k = h) ∧
      IsHomeomorph h ∧ A.law.map h = B.law
def componentValues (A : SeparatedTuples.DecompositionData) (F : FormalSpan) : A.space → ℂ :=
  fun ξ => (A.comp ξ).spanExtension F
structure ComponentsInvariantAndClustering (A : SeparatedTuples.DecompositionData) : Prop where
  shift_invariant : ∀ ξ v, (A.comp ξ).IsInvariant (SeparatedTuples.translate v)
  reflect_invariant : ∀ ξ, (A.comp ξ).IsInvariant TimeAxis.timeReflection
  cluster_uniform : ∀ X ∈ supportedIn TimeAxis.upperHalfSpace, ∀ Y ∈ supportedIn TimeAxis.upperHalfSpace,
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ ξ,
      |A.comp ξ (SepTuple.juxt X (push (SeparatedTuples.translate (t • timeBasisVec)) Y)) -
        A.comp ξ X * A.comp ξ Y| ≤ ε
section Kernel
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
def vacuumVector (c : PositiveSpan →ₗ[ℂ] ℋ) : ℋ :=
  c (posTupleVec ⟨SepTuple.nil, nil_mem_supportedIn _⟩)
structure IsPlateauSpace (σ : TupleFunctional) (c : PositiveSpan →ₗ[ℂ] ℋ)
    (K : Submodule ℂ ℋ) (Q : ℋ →L[ℂ] ℋ) : Prop where
  denseRange : DenseRange c
  isClosed : IsClosed (K : Set ℋ)
  proj_mem : ∀ ψ, Q ψ ∈ K
  proj_fix : ∀ ψ ∈ K, Q ψ = ψ
  proj_symm : ∀ φ ψ, ⟪Q φ, ψ⟫_ℂ = ⟪φ, Q ψ⟫_ℂ
  vacuum_mem : vacuumVector c ∈ K
  tendsto_inner : ∀ F F' : PositiveSpan,
    Tendsto (fun t : ℝ => σ.spanExtension (formalMul (reflectConj F)
      (pushSpan (SeparatedTuples.translate (t • timeBasisVec)) F'.1))) atTop (𝓝 ⟪c F, Q (c F')⟫_ℂ)
def IsValueExtension (A : SeparatedTuples.DecompositionData) (c : PositiveSpan →ₗ[ℂ] ℋ)
    (K : Submodule ℂ ℋ) (Q : ℋ →L[ℂ] ℋ) (U : K ≃ₗᵢ[ℂ] Lp ℂ 2 A.law) : Prop :=
  ∀ F : PositiveSpan, ∃ hF : Q (c F) ∈ K,
    (U ⟨_, hF⟩ : A.space → ℂ) =ᵐ[A.law] componentValues A F.1
def KernelIsL2 (A : SeparatedTuples.DecompositionData) (c : PositiveSpan →ₗ[ℂ] ℋ)
    (K : Submodule ℂ ℋ) (Q : ℋ →L[ℂ] ℋ) : Prop :=
  (∀ F F', ⟪Q (c F), Q (c F')⟫_ℂ =
    ∫ ξ, conj (componentValues A F.1 ξ) * componentValues A F'.1 ξ ∂A.law) ∧
  ∃ U : K ≃ₗᵢ[ℂ] Lp ℂ 2 A.law, IsValueExtension A c K Q U ∧
    (∀ U' : K ≃ₗᵢ[ℂ] Lp ℂ 2 A.law, IsValueExtension A c K Q U' → U' = U) ∧
    (∃ hΩ : vacuumVector c ∈ K, (U ⟨_, hΩ⟩ : A.space → ℂ) =ᵐ[A.law] fun _ => 1) ∧
    ENat.card A.space = Cardinal.toENat (Module.rank ℂ K)
end Kernel
def DecompositionDeterminations : Prop :=
  ∀ σ : TupleFunctional,
    (∀ A B : SeparatedTuples.DecompositionData, A.IsCanonical σ → B.IsCanonical σ →
      IsUniquelyIsomorphic A B) ∧
    (∀ A B : SeparatedTuples.DecompositionData, A.IsCanonical σ → B.IsCanonical σ →
      Set.range A.comp = Set.range B.comp) ∧
    (∀ A : SeparatedTuples.DecompositionData, A.IsCanonical σ →
      ∀ r, IsEuclidIsometry r → σ.IsInvariant r →
        (transportedDecomposition A r).IsCanonical σ ∧
          IsUniquelyIsomorphic (transportedDecomposition A r) A) ∧
    ∀ A : SeparatedTuples.DecompositionData, A.IsCanonical σ → ComponentsInvariantAndClustering A →
      ∀ (ℋ : Type) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
        (c : PositiveSpan →ₗ[ℂ] ℋ) (K : Submodule ℂ ℋ) (Q : ℋ →L[ℂ] ℋ),
        IsPlateauSpace σ c K Q → KernelIsL2 A c K Q
end YangMills.Construction.CanonicalDecompositionUniqueness
end
