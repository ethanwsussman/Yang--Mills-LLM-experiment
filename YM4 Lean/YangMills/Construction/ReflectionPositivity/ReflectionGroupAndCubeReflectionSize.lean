import YangMills.Construction.ReflectionPositivity.CubeAndCubeVectors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField AmbientSpace UnitLatticeSymmetry latticeSubgroup)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass siteReflect)
theorem siteReflect_coord (l i : Fin 4) (x : AmbientSpace) :
    (siteReflect l).toFun x i = (if i = l then -1 else 1) * x i := by
  rw [YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.siteReflect_apply]
  by_cases h : i = l
  · subst h
    simp [YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.basisVec]
    ring
  · simp [YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.basisVec, h]
theorem siteReflect_involutive (l : Fin 4) :
    Function.Involutive (siteReflect l).toFun := by
  intro x
  funext i
  rw [siteReflect_coord, siteReflect_coord]
  split_ifs <;> ring
def siteReflectPerm (l : Fin 4) : Equiv.Perm AmbientSpace :=
  (siteReflect_involutive l).toPerm
def axisReflectionGroup : Subgroup (Equiv.Perm AmbientSpace) :=
  Subgroup.closure (Set.range siteReflectPerm)
theorem axisReflectionGroup_isometry {g : Equiv.Perm AmbientSpace}
    (hg : g ∈ axisReflectionGroup) :
    (∀ x y, YangMills.Construction.TorusMetric.euclidNormVec (g x - g y) =
        YangMills.Construction.TorusMetric.euclidNormVec (x - y)) ∧
      g '' (latticeSubgroup 1 : Set AmbientSpace) = latticeSubgroup 1 := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨l, rfl⟩ := hg
    exact ⟨(siteReflect l).preservesDist, (siteReflect l).image_eq⟩
  | one => simp
  | mul g h _ _ ihg ihh =>
    refine ⟨fun x y => (ihg.1 _ _).trans (ihh.1 x y), ?_⟩
    rw [Equiv.Perm.coe_mul, Set.image_comp, ihh.2, ihg.2]
  | inv g _ ih =>
    refine ⟨fun x y => ?_, ?_⟩
    · have h := ih.1 (g⁻¹ x) (g⁻¹ y)
      simpa using h.symm
    · conv_lhs => rw [← ih.2]
      ext x
      simp
theorem exists_signs_of_mem_axisReflectionGroup {g : Equiv.Perm AmbientSpace}
    (hg : g ∈ axisReflectionGroup) :
    ∃ ε : Fin 4 → ℤˣ, ∀ x i, g x i = ((ε i : ℤ) : ℝ) * x i := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨l, rfl⟩ := hg
    refine ⟨fun i => if i = l then -1 else 1, fun x i => ?_⟩
    change (siteReflect l).toFun x i = _
    rw [siteReflect_coord]
    by_cases h : i = l <;> simp [h]
  | one => exact ⟨1, fun x i => by simp⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨ε, hε⟩ := ihg
    obtain ⟨ε', hε'⟩ := ihh
    refine ⟨ε * ε', fun x i => ?_⟩
    rw [Equiv.Perm.mul_apply, hε, hε']
    simp [mul_assoc]
  | inv g _ ih =>
    obtain ⟨ε, hε⟩ := ih
    refine ⟨ε, fun x i => ?_⟩
    have h := hε (g⁻¹ x) i
    have e : g (g⁻¹ x) = x := by simp
    rw [e] at h
    rw [h]
    rcases Int.units_eq_one_or (ε i) with e | e <;> simp [e]
instance : Finite axisReflectionGroup := by
  choose ε hε using fun g : axisReflectionGroup =>
    exists_signs_of_mem_axisReflectionGroup g.2
  refine Finite.of_injective ε fun g h e => ?_
  refine Subtype.ext (Equiv.ext fun x => funext fun i => ?_)
  rw [hε, hε, e]
def axisReflectionGroup.toUnitLatticeSymmetry (γ : axisReflectionGroup) :
    UnitLatticeSymmetry where
  toFun := γ.1
  preservesDist := (axisReflectionGroup_isometry γ.2).1
  image_eq := (axisReflectionGroup_isometry γ.2).2
def cubeVectorSqNorms (ν : unitPositiveClass) (r : ℕ+)
    (A : GaugeField (1 : ℝ) → ℂ) : Set ℝ :=
  Set.range fun p : Fin 4 × axisReflectionGroup =>
    ‖cubeVector ν p.1 r
      ((axisReflectionGroup.toUnitLatticeSymmetry p.2).actOn A)‖ ^ 2
def cubeReflectionNorm (ν : unitPositiveClass) (r : ℕ+)
    (A : GaugeField (1 : ℝ) → ℂ) : ℝ :=
  sSup (cubeVectorSqNorms ν r A)
theorem isGreatest_cubeReflectionNorm (ν : unitPositiveClass) (r : ℕ+)
    (A : GaugeField (1 : ℝ) → ℂ) :
    IsGreatest (cubeVectorSqNorms ν r A) (cubeReflectionNorm ν r A) := by
  have hf : (cubeVectorSqNorms ν r A).Finite := Set.finite_range _
  exact ⟨(Set.range_nonempty _).csSup_mem hf, fun _ hs => le_csSup hf.bddAbove hs⟩
end YangMills.Construction.ReflectionPositivity.DirectionPictures
