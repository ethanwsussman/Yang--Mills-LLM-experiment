import YangMills.Construction.SourcesAndGluing.ConfigurationsUnderLatticeSimilaritiesOfFourSpaceProof
import YangMills.Construction.SourcesAndGluing.LinksUnderLatticeSimilaritiesOfFourSpaceForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.ScaledMotionLinks
open InfiniteLattice (LatticePoint Link axisStep)
variable {D : GluingSetup} {e : ScaleExponent D} {Φ : ScaledLatticeMotion e}
theorem onPoint_add_axisStep_of_signs_eq_one (h : Φ.IsDilatingBijectionOfSpace)
    (x : LatticePoint D.mesh) (μ : Fin 4) (hs : Φ.signs μ = 1) :
    Φ.onPoint (x + axisStep D.mesh μ) = Φ.onPoint x + axisStep e.target.mesh (Φ.perm μ) := by apply _root_.YangMills.Construction.SourcesAndGluing.FieldsUnderScaledMotionsOfSpace.onPoint_add_axisStep_of_one <;> assumption
theorem onPoint_add_axisStep_of_signs_eq_neg_one (h : Φ.IsDilatingBijectionOfSpace)
    (x : LatticePoint D.mesh) (μ : Fin 4) (hs : Φ.signs μ = -1) :
    Φ.onPoint (x + axisStep D.mesh μ) = Φ.onPoint x - axisStep e.target.mesh (Φ.perm μ) := by apply _root_.YangMills.Construction.SourcesAndGluing.FieldsUnderScaledMotionsOfSpace.onPoint_add_axisStep_of_neg_one <;> assumption
theorem onPoint_injective (h : Φ.IsDilatingBijectionOfSpace) :
    Function.Injective Φ.onPoint := fun _ _ hxy =>
  Subtype.ext (h.1.1 (congrArg Subtype.val hxy))
theorem onPoint_surjective (h : Φ.IsDilatingBijectionOfSpace) :
    Function.Surjective Φ.onPoint := by
  intro x'
  have hx' : (x' : Fin 4 → ℝ) ∈ (e.target.gridPoints : Set (Fin 4 → ℝ)) := x'.2
  rw [← h.2.2.2.2] at hx'
  obtain ⟨x, hx, hxx'⟩ := hx'
  exact ⟨⟨x, hx⟩, Subtype.ext hxx'⟩
theorem onLink_injective (h : Φ.IsDilatingBijectionOfSpace) :
    Function.Injective Φ.onLink := by
  intro c c' hcc'
  exact Link.ext (onPoint_injective h (congrArg Link.initial hcc'))
    (onPoint_injective h (congrArg Link.terminal hcc'))
theorem exists_onLink_eq (c' : Link e.target.mesh) (x y : LatticePoint D.mesh) (μ : Fin 4)
    (hx : Φ.onPoint x = c'.initial) (hy : Φ.onPoint y = c'.terminal)
    (hxy : y - x = axisStep D.mesh μ ∨ y - x = -axisStep D.mesh μ) : ∃ c, Φ.onLink c = c' :=
  ⟨⟨x, y, μ, hxy⟩, Link.ext hx hy⟩
theorem onLink_surjective (h : Φ.IsDilatingBijectionOfSpace) :
    Function.Surjective Φ.onLink := by
  intro c'
  obtain ⟨x, hx⟩ := onPoint_surjective h c'.initial
  obtain ⟨ν, hν⟩ := c'.isAdjacent
  obtain ⟨μ, rfl⟩ := Φ.perm.surjective ν
  have hadd : c'.terminal = Φ.onPoint x + axisStep e.target.mesh (Φ.perm μ) ∨
      c'.terminal = Φ.onPoint x - axisStep e.target.mesh (Φ.perm μ) := by
    rcases hν with hν | hν
    · exact Or.inl (by rw [hx, ← hν]; abel)
    · exact Or.inr (by rw [hx, sub_eq_add_neg, ← hν]; abel)
  rcases Int.units_eq_one_or (Φ.signs μ) with hs | hs
  · rcases hadd with hadd | hadd
    · exact exists_onLink_eq c' x (x + axisStep D.mesh μ) μ hx
        (by rw [onPoint_add_axisStep_of_signs_eq_one h x μ hs, hadd]) (Or.inl (by abel))
    · refine exists_onLink_eq c' x (x - axisStep D.mesh μ) μ hx ?_ (Or.inr (by abel))
      have hstep := onPoint_add_axisStep_of_signs_eq_one h (x - axisStep D.mesh μ) μ hs
      rw [sub_add_cancel] at hstep
      rw [hadd, hstep]
      abel
  · rcases hadd with hadd | hadd
    · refine exists_onLink_eq c' x (x - axisStep D.mesh μ) μ hx ?_ (Or.inr (by abel))
      have hstep := onPoint_add_axisStep_of_signs_eq_neg_one h (x - axisStep D.mesh μ) μ hs
      rw [sub_add_cancel] at hstep
      rw [hadd, hstep]
      abel
    · exact exists_onLink_eq c' x (x + axisStep D.mesh μ) μ hx
        (by rw [onPoint_add_axisStep_of_signs_eq_neg_one h x μ hs, hadd]) (Or.inl (by abel))
theorem holds (hDilation : ScaledMotionDilationOfSpaceClaim) :
    ScaledMotionLinksOfSpaceClaim := by
  intro D e Φ
  have h := hDilation D e Φ
  refine ⟨⟨onLink_injective h, onLink_surjective h⟩, fun c => rfl, fun x μ => ⟨fun hs => ?_,
    fun hs => ?_⟩⟩
  · refine ⟨Φ.perm μ, ?_⟩
    change Φ.onPoint (x + axisStep D.mesh μ) - Φ.onPoint x = _
    rw [onPoint_add_axisStep_of_signs_eq_one h x μ hs]
    abel
  · refine ⟨Φ.perm μ, ?_⟩
    change Φ.onPoint x - Φ.onPoint (x + axisStep D.mesh μ) = _
    rw [onPoint_add_axisStep_of_signs_eq_neg_one h x μ hs]
    abel
end YangMills.Construction.SourcesAndGluing.ScaledMotionLinks
end
