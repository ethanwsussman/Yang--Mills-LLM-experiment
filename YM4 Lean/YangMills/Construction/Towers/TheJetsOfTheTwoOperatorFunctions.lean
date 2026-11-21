import YangMills.Construction.PeriodicOperators.Jets
import YangMills.Construction.Towers.TheFieldsAndTheTwoOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
def PeriodicData.disjSum (I I' : PeriodicData) : PeriodicData where
  Carrier := I.Carrier ⊕ I'.Carrier
  translate := fun m => Sum.map (I.translate m) (I'.translate m)
  pos := Sum.elim I.pos I'.pos
  Component := I.Component ⊕ I'.Component
  componentOf := Sum.map I.componentOf I'.componentOf
  weight := Sum.elim I.weight I'.weight
def HasInvertibleJetsAtWidth (F I : PeriodicData)
    (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ p ∈ imStrip δ, ∀ εPos εNeg : F.UnitQuot → ℂ,
    JetQuad.IsInvertibleJet δ p (jetAlong F I I T p εPos εNeg)
end YangMills.Construction.PeriodicOperators
namespace YangMills.Construction.Tower.FullSpace
open YangMills.Construction.PeriodicOperators
abbrev fieldPeriodicData (L k : ℕ) (hL : 0 < L) : PeriodicData :=
  (YangMills.Construction.LocalKernels.fieldIndices L k hL).toPeriodicData L
abbrev vectorIndices (L k : ℕ) : PeriodicData :=
  (colourEdges L k 0).disjSum (colourEdges L k k)
abbrev ghostIndices (L k : ℕ) : PeriodicData :=
  (colourVertices L k 0).disjSum (colourVertices L k k)
def vectorOpFn (L k : ℕ) (hL : 0 < L) :
    ((fieldPeriodicData L k hL).Carrier → ℂ) →
      (vectorIndices L k).Carrier → (vectorIndices L k).Carrier → ℂ :=
  vectorOpOfCoeffs hL
def ghostOpFn (L k : ℕ) (hL : 0 < L) :
    ((fieldPeriodicData L k hL).Carrier → ℂ) →
      (ghostIndices L k).Carrier → (ghostIndices L k).Carrier → ℂ :=
  ghostOpOfCoeffs hL
def vectorJet (L k : ℕ) (hL : 0 < L) (p : Fin 4 → ℂ)
    (εPos εNeg : (fieldPeriodicData L k hL).UnitQuot → ℂ) :
    JetQuad (vectorIndices L k) (vectorIndices L k) :=
  jetAlong (fieldPeriodicData L k hL) (vectorIndices L k) (vectorIndices L k) (vectorOpFn L k hL) p
    εPos εNeg
def ghostJet (L k : ℕ) (hL : 0 < L) (p : Fin 4 → ℂ)
    (εPos εNeg : (fieldPeriodicData L k hL).UnitQuot → ℂ) :
    JetQuad (ghostIndices L k) (ghostIndices L k) :=
  jetAlong (fieldPeriodicData L k hL) (ghostIndices L k) (ghostIndices L k) (ghostOpFn L k hL) p
    εPos εNeg
def IsJointInvertibilityWidth (L k : ℕ) (hL : 0 < L) (δ : ℝ) : Prop :=
  HasInvertibleJetsAtWidth (fieldPeriodicData L k hL) (vectorIndices L k) (vectorOpFn L k hL) δ ∧
    HasInvertibleJetsAtWidth (fieldPeriodicData L k hL) (ghostIndices L k) (ghostOpFn L k hL) δ
def crossingSmoothingTranspose (L k : ℕ) :
    ((colourEdges L k k).Carrier → ℂ) → (colourEdges L k 0).Carrier → ℂ :=
  YangMills.Construction.Tower.PauliComponentsOfSymmetricKernel.transposeOnCoeffs (edgePauliCoordinates L k 0) (edgePauliCoordinates L k k)
    (crossingSmoothingIter L k k)
end YangMills.Construction.Tower.FullSpace
end
