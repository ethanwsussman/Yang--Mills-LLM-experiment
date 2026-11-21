import YangMills.Construction.ReflectionPositivity.DescentToASplitTorus
import Mathlib
set_option autoImplicit false
open scoped Matrix ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
namespace PeriodSublattice
variable (Γ : PeriodSublattice 1)
def siteHeights (n : AmbientSpace) (z : ℤ) (s : Γ.QuotientTorus) : Set ℝ :=
  {u | ∃ x : LatticePoint 1, Γ.quotientMap x = s ∧
    ∃ k : ℤ, u = n ⬝ᵥ (x : AmbientSpace) + 2 * (z : ℝ) * (k : ℝ)}
def HasHeight (n : AmbientSpace) (z : ℤ) (s : Γ.QuotientTorus) (u : ℝ) : Prop :=
  u ∈ Γ.siteHeights n z s
def slab (n : AmbientSpace) (z : ℤ) (c₁ c₂ : ℝ) : Set Γ.QuotientTorus :=
  {s | ∃ u ∈ Γ.siteHeights n z s, c₁ ≤ u ∧ u ≤ c₂}
def plusHalf (n : AmbientSpace) (z : ℤ) (c : ℝ) : Set Γ.QuotientTorus :=
  Γ.slab n z c (c + (z : ℝ))
def minusHalf (n : AmbientSpace) (z : ℤ) (c : ℝ) : Set Γ.QuotientTorus :=
  Γ.slab n z (c + (z : ℝ)) (c + 2 * (z : ℝ))
def linksInside (T : Set Γ.QuotientTorus) : Set Γ.QuotientLink :=
  {b | Γ.linkEndpoints b ⊆ T}
def plusLinks (n : AmbientSpace) (z : ℤ) (c : ℝ) : Set Γ.QuotientLink :=
  Γ.linksInside (Γ.plusHalf n z c)
def minusLinks (n : AmbientSpace) (z : ℤ) (c : ℝ) : Set Γ.QuotientLink :=
  Γ.linksInside (Γ.minusHalf n z c)
def sharedLinks (n : AmbientSpace) (z : ℤ) (c : ℝ) : Set Γ.QuotientLink :=
  Γ.plusLinks n z c ∩ Γ.minusLinks n z c
def crossingLinks (n : AmbientSpace) (z : ℤ) (c : ℝ) : Set Γ.QuotientLink :=
  (Γ.plusLinks n z c ∪ Γ.minusLinks n z c)ᶜ
def IsSplitPlaquette (n : AmbientSpace) (z : ℤ) (c : ℝ) (P : Γ.QuotientPlaquette) : Prop :=
  ¬ Γ.plaquetteLinks P ⊆ Γ.plusLinks n z c ∧ ¬ Γ.plaquetteLinks P ⊆ Γ.minusLinks n z c
def boundedAlgebra (M : Set Γ.QuotientLink) : Subalgebra ℂ (Γ.QuotientField → ℂ) where
  carrier := {F | Measurable F ∧ (∃ C : ℝ, ∀ U, ‖F U‖ ≤ C) ∧ DependsOnlyOn F M}
  mul_mem' := by
    rintro F G ⟨hF, ⟨C, hC⟩, dF⟩ ⟨hG, ⟨D, hD⟩, dG⟩
    refine ⟨hF.mul hG, ⟨C * D, fun U => ?_⟩, fun U V h => ?_⟩
    · rw [Pi.mul_apply, norm_mul]
      exact mul_le_mul (hC U) (hD U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
    · simp only [Pi.mul_apply, dF U V h, dG U V h]
  add_mem' := by
    rintro F G ⟨hF, ⟨C, hC⟩, dF⟩ ⟨hG, ⟨D, hD⟩, dG⟩
    refine ⟨hF.add hG, ⟨C + D, fun U => ?_⟩, fun U V h => ?_⟩
    · exact (norm_add_le _ _).trans (add_le_add (hC U) (hD U))
    · simp only [Pi.add_apply, dF U V h, dG U V h]
  algebraMap_mem' := fun w =>
    ⟨measurable_const, ⟨‖w‖, fun _ => le_rfl⟩, fun _ _ _ => rfl⟩
theorem mem_boundedAlgebra {M : Set Γ.QuotientLink} {F : Γ.QuotientField → ℂ} :
    F ∈ Γ.boundedAlgebra M ↔
      Measurable F ∧ (∃ C : ℝ, ∀ U, ‖F U‖ ≤ C) ∧ DependsOnlyOn F M :=
  Iff.rfl
def plusAlgebra (n : AmbientSpace) (z : ℤ) (c : ℝ) : Subalgebra ℂ (Γ.QuotientField → ℂ) :=
  Γ.boundedAlgebra (Γ.plusLinks n z c)
def minusAlgebra (n : AmbientSpace) (z : ℤ) (c : ℝ) : Subalgebra ℂ (Γ.QuotientField → ℂ) :=
  Γ.boundedAlgebra (Γ.minusLinks n z c)
def linkImage (r : LatticeSymmetry 1) (b : Γ.QuotientLink) : Γ.QuotientLink :=
  open Classical in
  if h : Γ.OrientedIsPositive (Γ.descendOrientedLink r (Γ.orientedOfLink b)) then
    Γ.linkClass ⟨Γ.orientedRep (Γ.descendOrientedLink r (Γ.orientedOfLink b)), h⟩
  else
    Γ.linkClass ⟨(Γ.orientedRep
      (Γ.descendOrientedLink r (Γ.orientedOfLink b))).opposite,
        isPositivelyOriented_opposite_of_not h⟩
def pullbackField (r : LatticeSymmetry 1) (U : Γ.QuotientField) : Γ.QuotientField :=
  fun b => Γ.orientedValue U (Γ.orientedClass (r.linkMap (Γ.linkRep b).1))
theorem pullbackField_linkClass {r : LatticeSymmetry 1} (hr : Γ.MapsOrbits r)
    (U : Γ.QuotientField) (b : PositiveLink 1) :
    Γ.pullbackField r U (Γ.linkClass b) =
      Γ.orientedValue U (Γ.orientedClass (r.linkMap b.1)) := by
  obtain ⟨γ, hγ, h⟩ := Γ.exists_linkRep_eq b
  have hmem : r.linkMap (b.1.shiftBy γ) ∈ Γ.orientedOrbit (r.linkMap b.1) := by
    rw [← hr.links_orbit b.1]
    exact ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
  obtain ⟨δ, hδ, h'⟩ := hmem
  have hrep : (Γ.linkRep (Γ.linkClass b)).1 = b.1.shiftBy γ :=
    congrArg Subtype.val h
  rw [pullbackField, hrep, h', Γ.orientedClass_shiftBy _ hδ]
def compPullback {E : Type*} (r : LatticeSymmetry 1) (F : Γ.QuotientField → E) :
    Γ.QuotientField → E :=
  fun U => F (Γ.pullbackField r U)
def conjReflect (P : NormalFamilies.NormalLevelPair 1) (F : Γ.QuotientField → ℂ) :
    Γ.QuotientField → ℂ :=
  fun U => conj (Γ.compPullback P.reflectSymmetry F U)
end PeriodSublattice
end InfiniteLattice
end YangMills.Construction
