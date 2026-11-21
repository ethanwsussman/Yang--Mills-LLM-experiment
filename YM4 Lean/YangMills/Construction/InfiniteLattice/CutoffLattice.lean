import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace CutoffLattice
open YangMills.Construction.InfiniteLattice
variable {a : ℝ}
abbrev spacingAt (L K : ℕ) : ℝ := PeriodicLattice.meshSize L (K : ℤ)
theorem spacingAt_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ) :
    0 < spacingAt L K :=
  zpow_pos (by exact_mod_cast (by have := hL.2; omega : 0 < L)) _
abbrev latticeAt (L K : ℕ) : AddSubgroup AmbientSpace := latticeSubgroup (spacingAt L K)
def positiveLinks (a : ℝ) : Set (Link a) :=
  {b | ∃ (x : LatticePoint a) (μ : Fin 4), b = Link.forwardFrom x μ}
abbrev positiveLinksAt (L K : ℕ) : Set (Link (spacingAt L K)) := positiveLinks (spacingAt L K)
def endpoints (b : Link a) : Set (LatticePoint a) := {b.initial, b.terminal}
abbrev FieldsAt (L K : ℕ) : Type := GaugeField (spacingAt L K)
def restrictField (S : Set (Link a)) (U : GaugeField a) :
    S → Matrices.ComplexMatrix2.specialUnitary := fun b => U b
def DependsOnlyOn {E : Type*} (F : GaugeField a → E) (S : Set (Link a)) : Prop :=
  S ⊆ positiveLinks a ∧ ∀ U U' : GaugeField a, restrictField S U = restrictField S U' → F U = F U'
def DependsOnFinitelyMany {E : Type*} (F : GaugeField a → E) : Prop :=
  ∃ S : Set (Link a), S.Finite ∧ DependsOnlyOn F S
def valuesOnPositive (U : GaugeField a) : positiveLinks a → Matrices.ComplexMatrix2.specialUnitary :=
  restrictField (positiveLinks a) U
theorem opposite_mem_positiveLinks_of_not_mem {b : Link a} (h : b ∉ positiveLinks a) :
    b.opposite ∈ positiveLinks a := by
  obtain ⟨μ, hμ | hμ⟩ := b.isAdjacent
  · refine absurd ⟨b.initial, μ, Link.ext rfl ?_⟩ h
    change b.terminal = b.initial + axisStep a μ
    rw [← hμ]
    abel
  · refine ⟨b.terminal, μ, Link.ext rfl ?_⟩
    change b.initial = b.terminal + axisStep a μ
    rw [sub_eq_iff_eq_add] at hμ
    rw [hμ]
    abel
theorem opposite_not_mem_positiveLinks (ha : 0 < a) {b : Link a} (h : b ∈ positiveLinks a) :
    b.opposite ∉ positiveLinks a := by apply _root_.YangMills.Construction.InfiniteLattice.opposite_notMem_positiveLinks <;> assumption
open Classical in
def fieldOfValues (ha : 0 < a) (v : positiveLinks a → Matrices.ComplexMatrix2.specialUnitary) :
    GaugeField a :=
  ⟨fun b => if h : b ∈ positiveLinks a then v ⟨b, h⟩
      else (v ⟨b.opposite, opposite_mem_positiveLinks_of_not_mem h⟩)⁻¹,
    fun b => by
      beta_reduce
      by_cases h : b ∈ positiveLinks a
      · rw [dif_neg (opposite_not_mem_positiveLinks ha h), dif_pos h]
        rfl
      · rw [dif_pos (opposite_mem_positiveLinks_of_not_mem h), dif_neg h, inv_inv]⟩
def fieldEquivValues (ha : 0 < a) :
    GaugeField a ≃ (positiveLinks a → Matrices.ComplexMatrix2.specialUnitary) where
  toFun := valuesOnPositive
  invFun := fieldOfValues ha
  left_inv U := by
    refine Subtype.ext (funext fun b => ?_)
    by_cases h : b ∈ positiveLinks a
    · exact dif_pos h
    · refine (dif_neg h).trans ?_
      change (U b.opposite)⁻¹ = U b
      rw [U.2 b, inv_inv]
  right_inv v := by
    funext b
    exact dif_pos b.2
def face (x : LatticePoint a) (μ lam : Fin 4) (h : μ < lam) : ElementaryPlaquette a :=
  ⟨x, μ, lam, h⟩
def faceLinks (p : ElementaryPlaquette a) : Set (Link a) := {b | b ∈ p.edges}
def FaceHasLink (p : ElementaryPlaquette a) (b : Link a) : Prop := b ∈ faceLinks p
def faceOfPair (y : LatticePoint a) (μ lam : Fin 4) (h : μ ≠ lam) : ElementaryPlaquette a :=
  if hlt : μ < lam then face y μ lam hlt
  else face y lam μ (lt_of_le_of_ne (not_lt.mp hlt) h.symm)
def translateLink (b : Link a) (v : LatticePoint a) : Link a where
  initial := b.initial + v
  terminal := b.terminal + v
  isAdjacent := by
    rw [add_sub_add_right_eq_sub]
    exact b.isAdjacent
def translateFace (p : ElementaryPlaquette a) (v : LatticePoint a) : ElementaryPlaquette a :=
  face (p.corner + v) p.lowAxis p.highAxis p.lowAxis_lt_highAxis
end CutoffLattice
end YangMills.Construction
end
