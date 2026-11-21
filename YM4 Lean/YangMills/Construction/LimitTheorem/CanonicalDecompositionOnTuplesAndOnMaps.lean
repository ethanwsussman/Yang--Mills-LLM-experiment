import YangMills.Construction.Continuum.CanonicalDecompositionOfAFamilyOnSeparatedTuples
import YangMills.Construction.Continuum.CanonicalDecompositionOfAFunctional
import YangMills.Construction.LimitTheorem.FunctionalDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitTheorem.DecompositionOnListsAndMaps
open TestSpaces (SepTuple sepTupleNil)
open SeparatedTuples (DecompositionData TupleFunctional)
open CanonicalDecomposition (DecompositionTriple)
open LimitTheorem (CumulantFamily centredOf evalOnMap)
open TupleLists (ofList)
def listFunctional (f : SepTuple → ℝ) (hf : f sepTupleNil = 1) : TupleFunctional where
  toFun X := f (ofList X)
  map_nil := by
    rw [← TupleLists.toList_sepTupleNil, TupleLists.ofList_toList]
    exact hf
def mapTriple (A : DecompositionData) : DecompositionTriple where
  space := A.space
  law := A.law
  comp ξ := evalOnMap (A.comp ξ)
def listData (B : DecompositionTriple) (hB : ∀ ξ, B.comp ξ sepTupleNil = 1) : DecompositionData where
  space := B.space
  law := B.law
  comp ξ := listFunctional (B.comp ξ) (hB ξ)
def ListAndMapFormsAgree : Prop :=
  (∀ (S : CumulantFamily) (A : DecompositionData),
    A.IsCanonical (centredOf S) ↔
      (mapTriple A).IsCanonical S) ∧
  (∀ (S : CumulantFamily) (B : DecompositionTriple) (hB : B.IsCanonical S),
    mapTriple (listData B fun ξ => (hB.comp_isSepFunctional ξ).1) = B) ∧
  ∀ A A' : DecompositionData,
    A.Isomorphic A' ↔ (mapTriple A).Isomorphic (mapTriple A')
end YangMills.Construction.LimitTheorem.DecompositionOnListsAndMaps
end
