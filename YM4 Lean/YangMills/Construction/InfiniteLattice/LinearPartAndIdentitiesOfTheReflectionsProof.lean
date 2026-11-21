import YangMills.Construction.InfiniteLattice.PropertiesOfTheSixteenFamiliesProof
import YangMills.Construction.InfiniteLattice.AllMirrorsAtSpacingOneProof
import YangMills.Construction.InfiniteLattice.LinearPartAndIdentitiesOfTheReflections
import YangMills.Construction.InfiniteLattice.ReflectionsOfOneFamily
import YangMills.Construction.InfiniteLattice.RulesOfTheActionOfTheLatticeIsometries
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open InfiniteLattice
namespace ReflectionIdentities
theorem latticeSymmetry_ext {r s : LatticeSymmetry 1} (h : r.toFun = s.toFun) : r = s := by apply _root_.YangMills.Construction.InfiniteLattice.UnitMeshReflectionPositivity.latticeSymmetry_ext_toFun <;> assumption
theorem isLinearMap_linearReflect (n : AmbientSpace) : IsLinearMap ℝ (linearReflect n) := by apply _root_.YangMills.Construction.NormalFamilies.Properties.isLinearMap_reflectAcross_zero <;> assumption
theorem linearReflect_normal {n : AmbientSpace} (hn : n ∈ normalSet) :
    linearReflect n n = -n := by
  have h := dotProduct_dualVector hn
  rw [dualVector, dotProduct_smul, smul_eq_mul, ← normSq_eq_dotProduct n] at h
  rw [linearReflect_apply, ← normSq_eq_dotProduct n, dualVector, smul_smul,
    show 2 * normSq n * (normSq n)⁻¹ = 2 by linear_combination 2 * h]
  module
theorem reflectAcross_add (n : AmbientSpace) (c : ℝ) (x y : AmbientSpace) :
    reflectAcross n c (x + y) = reflectAcross n c x + linearReflect n y := by
  simp only [linearReflect_apply, reflectAcross, dotProduct_add]
  module
theorem isAllowedLevel_zero (n : AmbientSpace) : IsAllowedLevel 1 n 0 :=
  ⟨fun _ => ⟨0, by simp⟩, fun _ => ⟨0, by simp⟩⟩
theorem linearReflect_mem_latticeSubgroup {n : AmbientSpace} (hn : n ∈ normalSet)
    (v : LatticePoint 1) :
    linearReflect n (v : AmbientSpace) ∈ latticeSubgroup 1 := by
  have h := (NormalLevelPair.reflectSymmetry ⟨n, hn, 0, isAllowedLevel_zero n⟩).image_eq
  change linearReflect n (v : AmbientSpace) ∈ (latticeSubgroup 1 : Set AmbientSpace)
  rw [← h]
  exact ⟨v, v.2, rfl⟩
theorem reflectSymmetry_comp_shift (P : NormalLevelPair 1) (v w : LatticePoint 1)
    (hw : (w : AmbientSpace) = linearReflect P.normal (v : AmbientSpace)) :
    P.reflectSymmetry.comp (shift v) = (shift w).comp P.reflectSymmetry := by
  refine latticeSymmetry_ext (funext fun x => ?_)
  change reflectAcross P.normal P.level (x + (v : AmbientSpace)) =
    reflectAcross P.normal P.level x + (w : AmbientSpace)
  rw [hw, reflectAcross_add]
end ReflectionIdentities
open ReflectionIdentities in
theorem ReflectionLinearPart.statement_holds
    (hRules : InfiniteLattice.SymmetryActionRules.Statement)
    (hRefl : ReflectionIdentities.Statement) :
    ReflectionLinearPart.Statement := by
  intro n hn c c' hc hc' v P P'
  obtain ⟨h1, h2, h3, h4, h5, ⟨w, hw, -, hwF⟩, h7, h8, h9, h10, h11, h12, -, -⟩ :=
    hRefl n hn c c' hc hc' v
  refine ⟨P.reflectSymmetry.preservesDist, P.reflectSymmetry.image_eq, rfl, isAllowedLevel_zero n,
    isLinearMap_linearReflect n, ?_, linearReflect_normal hn,
    fun x => reflectAcross_add n c x _, ?_, funext h1, h2, funext h3, funext h4, h5,
    ⟨w, hw, hwF⟩, h7, h8, h9, h10, h11, ?_, ?_⟩
  · intro x hx
    rw [linearReflect_apply, hx]
    simp
  · refine ⟨⟨_, linearReflect_mem_latticeSubgroup hn v⟩, rfl, fun F hF => ?_⟩
    have key := reflectSymmetry_comp_shift P v ⟨_, linearReflect_mem_latticeSubgroup hn v⟩ rfl
    have a1 := (hRules P.reflectSymmetry (shift v)).1 F hF
    have a2 := (hRules (shift ⟨_, linearReflect_mem_latticeSubgroup hn v⟩) P.reflectSymmetry).1 F hF
    exact a1.trans ((congrArg (fun r : LatticeSymmetry 1 => r.actOn F) key).trans a2.symm)
  · have e := h12 1
    simp only [halfSpaceObservables, closedHalfSpace_one, closedHalfSpace_neg_one] at e
    exact e
  · have e := h12 (-1)
    rw [neg_neg] at e
    simp only [halfSpaceObservables, closedHalfSpace_one, closedHalfSpace_neg_one] at e
    exact e
end YangMills.Construction.NormalFamilies
