import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K j : ℕ}
def SiteAtLevel.toBareSite {i : ℕ} (y : SiteAtLevel L m K i) : SiteAtLevel L m K 0 :=
  Site.toSublattice y (levelDepth K 0)
theorem conjugateBy_mem_hermitianTraceless (V : ComplexMatrix2.specialUnitary)
    (A : ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy (V : ComplexMatrix2) (A : ComplexMatrix2) ∈
      ComplexMatrix2.hermitianTraceless := by
  have hV : (V : ComplexMatrix2) * star (V : ComplexMatrix2) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp V.2).1
  have hV' : star (V : ComplexMatrix2) * (V : ComplexMatrix2) = 1 := mul_eq_one_comm.mp hV
  have hinv : (V : ComplexMatrix2)⁻¹ = star (V : ComplexMatrix2) := Matrix.inv_eq_right_inv hV
  obtain ⟨hA, tA⟩ := A.2
  refine ⟨?_, ?_⟩
  · rw [ComplexMatrix2.conjugateBy, hinv, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← hA, mul_assoc]
  · rw [ComplexMatrix2.conjugateBy, hinv, ComplexMatrix2.fullTrace, Matrix.trace_mul_comm,
      ← mul_assoc, hV', one_mul]
    exact tA
def adjointOnLieAlgebra (V : ComplexMatrix2.specialUnitary)
    (A : ComplexMatrix2.hermitianTraceless) : ComplexMatrix2.hermitianTraceless :=
  ⟨ComplexMatrix2.conjugateBy (V : ComplexMatrix2) (A : ComplexMatrix2),
    conjugateBy_mem_hermitianTraceless V A⟩
def valueAtSource {i : ℕ} (u : SiteAtLevel L m K 0 → ComplexMatrix2.specialUnitary)
    (b : BondAtLevel L m K i) : ComplexMatrix2.specialUnitary :=
  u (SiteAtLevel.toBareSite b.source)
@[ext]
structure StoredBonds (L m K j : ℕ) where
  sets : (i : Fin j) → Set (BondAtLevel L m K i)
  positivelyOriented : ∀ i, ∀ b ∈ sets i, Bond.IsPositivelyOriented b
namespace StoredBonds
variable (S : StoredBonds L m K j)
abbrev FieldSystem : Type := (i : Fin j) → S.sets i → ComplexMatrix2.hermitianTraceless
def conjugateSystem (u : SiteAtLevel L m K 0 → ComplexMatrix2.specialUnitary)
    (f : S.FieldSystem) : S.FieldSystem :=
  fun i b => adjointOnLieAlgebra (valueAtSource u b.1) (f i b)
def IsConjugationStable (Φ : Set S.FieldSystem) : Prop :=
  ∀ f ∈ Φ, ∀ u : SiteAtLevel L m K 0 → ComplexMatrix2.specialUnitary, S.conjugateSystem u f ∈ Φ
def bondsNear (X : Set (FourTorus L m)) (i : Fin j) : Set (BondAtLevel L m K i) :=
  S.sets i ∩ bondsMeeting X
abbrev FieldsNear (X : Set (FourTorus L m)) : Type :=
  (i : Fin j) → S.bondsNear X i → ComplexMatrix2.hermitianTraceless
def restrictNear (X : Set (FourTorus L m)) (f : S.FieldSystem) : S.FieldsNear X :=
  fun i b => f i ⟨b.1, b.2.1⟩
def restrictSetNear (X : Set (FourTorus L m)) (Φ : Set S.FieldSystem) : Set (S.FieldsNear X) :=
  S.restrictNear X '' Φ
def conjugateNear (X : Set (FourTorus L m))
    (u : SiteAtLevel L m K 0 → ComplexMatrix2.specialUnitary) (φ : S.FieldsNear X) :
    S.FieldsNear X :=
  fun i b => adjointOnLieAlgebra (valueAtSource u b.1) (φ i b)
end StoredBonds
end YangMills.Construction.PeriodicLattice
