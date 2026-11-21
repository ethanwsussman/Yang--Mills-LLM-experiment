import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Spectral
abbrev BorelSubset (X : Type*) [MeasurableSpace X] : Type _ := {S : Set X // MeasurableSet S}
variable {X X' 𝓗 : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X']
  [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
structure IsSpectralMeasure (P : BorelSubset X → 𝓗 →L[ℂ] 𝓗) : Prop where
  isStarProjection_apply : ∀ S, IsStarProjection (P S)
  apply_univ : P ⟨univ, MeasurableSet.univ⟩ = 1
  hasSum_inner_iUnion : ∀ (v : 𝓗) (S : ℕ → BorelSubset X),
    Pairwise (fun i j => Disjoint (S i).1 (S j).1) →
      HasSum (fun i => inner ℂ v (P (S i) v))
        (inner ℂ v (P ⟨⋃ i, (S i).1, MeasurableSet.iUnion fun i => (S i).2⟩ v))
variable (X 𝓗) in
structure ProjValuedMeasure where
  toFun : BorelSubset X → 𝓗 →L[ℂ] 𝓗
  isSpectralMeasure : IsSpectralMeasure toFun
namespace ProjValuedMeasure
instance : CoeFun (ProjValuedMeasure X 𝓗) (fun _ => BorelSubset X → 𝓗 →L[ℂ] 𝓗) := ⟨toFun⟩

variable (P : ProjValuedMeasure X 𝓗)
set_option linter.unusedSectionVars false
def form (u v : 𝓗) (S : BorelSubset X) : ℂ := inner ℂ u (P S v)
end ProjValuedMeasure
end YangMills.Construction.Spectral
