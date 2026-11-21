import YangMills.Construction.InfiniteLattice.UnfoldedAndFoldedArraysOfALadder
import YangMills.Construction.ReflectionPositivity.HalvesOfASplitTorus
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction
namespace NormalFamilies
open InfiniteLattice
theorem IsAllowedLevel.add_intCast {v : AmbientSpace} {c : ℝ} (hc : IsAllowedLevel 1 v c) (m : ℤ) :
    IsAllowedLevel 1 v (c + (m : ℝ)) := by
  refine ⟨fun hq => ?_, fun hq => ?_⟩
  · obtain ⟨k, hk⟩ := hc.1 hq
    exact ⟨k + 2 * m, by rw [hk]; push_cast; ring⟩
  · obtain ⟨k, hk⟩ := hc.2 hq
    exact ⟨k + m, by rw [hk]; push_cast; ring⟩
theorem two_smul_dualVector_mem {v : AmbientSpace} (hv : v ∈ normalSet) :
    (2 : ℝ) • dualVector v ∈ latticeSubgroup 1 := by apply _root_.YangMills.Construction.NormalFamilies.two_smul_dualVector_mem_latticeSubgroup <;> assumption
end NormalFamilies
namespace InfiniteLattice
open NormalFamilies
namespace PeriodSublattice
variable (Γ : PeriodSublattice 1)
theorem slab_add_two_mul_mul (v : AmbientSpace) (z m : ℤ) (c₁ c₂ : ℝ) :
    Γ.slab v z (c₁ + 2 * (z : ℝ) * (m : ℝ)) (c₂ + 2 * (z : ℝ) * (m : ℝ)) =
      Γ.slab v z c₁ c₂ := by
  ext s
  constructor
  · rintro ⟨_, ⟨x, hx, k, rfl⟩, h₁, h₂⟩
    refine ⟨_, ⟨x, hx, k - m, rfl⟩, ?_, ?_⟩ <;> push_cast <;> linarith
  · rintro ⟨_, ⟨x, hx, k, rfl⟩, h₁, h₂⟩
    refine ⟨_, ⟨x, hx, k + m, rfl⟩, ?_, ?_⟩ <;> push_cast <;> linarith
@[ext]
structure TorusMap where
  pointMap : Γ.QuotientTorus → Γ.QuotientTorus
  linkMap : Γ.OrientedLink → Γ.OrientedLink
  faceMap : Γ.QuotientPlaquette → Γ.QuotientPlaquette
def descendedTorusMap (r : LatticeSymmetry 1) : Γ.TorusMap where
  pointMap := Γ.descendPoint r
  linkMap := Γ.descendOrientedLink r
  faceMap := Γ.descendFace r
end PeriodSublattice
structure SlabDecomposition where
  normal : AmbientSpace
  normal_mem : normal ∈ normalSet
  baseLevel : ℝ
  baseLevel_allowed : IsAllowedLevel 1 normal baseLevel
  width : ℤ
  two_le_width : 2 ≤ width
  count : ℕ
  one_le_count : 1 ≤ count
  period : PeriodSublattice 1
  splits : period.SplitsAlongWithHalfPeriod normal ((count : ℤ) * width)
namespace SlabDecomposition
variable (S : SlabDecomposition)
def halfPeriod : ℤ := (S.count : ℤ) * S.width
def level (k : ℤ) : ℝ := S.baseLevel + (k : ℝ) * (S.width : ℝ)
theorem level_allowed (k : ℤ) : IsAllowedLevel 1 S.normal (S.level k) := by
  have h := S.baseLevel_allowed.add_intCast (k * S.width)
  rw [Int.cast_mul] at h
  exact h
def levelPair (k : ℤ) : NormalLevelPair 1 := ⟨S.normal, S.normal_mem, S.level k, S.level_allowed k⟩
def mirrorLocus (k : ℤ) : Set S.period.QuotientTorus :=
  {s | S.period.HasHeight S.normal S.halfPeriod s (S.level k)}
def slabAt (k : ℤ) : Set S.period.QuotientTorus :=
  S.period.slab S.normal S.halfPeriod (S.level k) (S.level (k + 1))
theorem level_add_two_mul_mul (k m : ℤ) :
    S.level (k + 2 * (S.count : ℤ) * m) =
      S.level k + 2 * (S.halfPeriod : ℝ) * (m : ℝ) := by
  simp only [level, halfPeriod]
  push_cast
  ring
theorem slabAt_add_two_mul_mul (k m : ℤ) : S.slabAt (k + 2 * (S.count : ℤ) * m) = S.slabAt k := by
  have h : k + 2 * (S.count : ℤ) * m + 1 = (k + 1) + 2 * (S.count : ℤ) * m := by ring
  rw [slabAt, h, level_add_two_mul_mul, level_add_two_mul_mul]
  exact S.period.slab_add_two_mul_mul _ _ _ _ _
def reflectSym (k : ℤ) : LatticeSymmetry 1 := (S.levelPair k).reflectSymmetry
def torusReflection (k : ℤ) : S.period.TorusMap := S.period.descendedTorusMap (S.reflectSym k)
def reflectPullback (k : ℤ) (U : S.period.QuotientField) : S.period.QuotientField :=
  S.period.pullbackField (S.reflectSym k) U
def reflectAct {E : Type*} (k : ℤ) (F : S.period.QuotientField → E) :
    S.period.QuotientField → E :=
  S.period.compPullback (S.reflectSym k) F
def conjReflectAt (k : ℤ) (F : S.period.QuotientField → ℂ) :
    S.period.QuotientField → ℂ :=
  S.period.conjReflect (S.levelPair k) F
def slabAlgebra (k : ℤ) : Subalgebra ℂ (S.period.QuotientField → ℂ) :=
  S.period.boundedAlgebra (S.period.linksInside (S.slabAt k))
theorem slabAlgebra_add_two_mul_mul (k m : ℤ) :
    S.slabAlgebra (k + 2 * (S.count : ℤ) * m) = S.slabAlgebra k := by
  rw [slabAlgebra, slabAt_add_two_mul_mul, slabAlgebra]
def stepVec (j : ℤ) : LatticePoint 1 :=
  ⟨(2 * (j : ℝ) * (S.width : ℝ)) • dualVector S.normal, by
    have h := zsmul_mem (two_smul_dualVector_mem S.normal_mem) (j * S.width)
    have e : (j * S.width) • ((2 : ℝ) • dualVector S.normal) =
        (2 * (j : ℝ) * (S.width : ℝ)) • dualVector S.normal := by
      rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul]
      push_cast
      ring_nf
    rw [e] at h
    exact h⟩
def IsGroupTranslation (g : S.period.TorusMap) : Prop :=
  ∃ j : ℤ, g = S.period.descendedTorusMap (shift (S.stepVec j))
def IsGroupReflection (g : S.period.TorusMap) : Prop :=
  ∃ s : ℤ, g = S.torusReflection s
def generatedMaps : Set S.period.TorusMap :=
  {g | S.IsGroupTranslation g ∨ S.IsGroupReflection g}
instance neZero_two_mul_count : NeZero (2 * S.count) :=
  ⟨by have := S.one_le_count; omega⟩
def slabOfClass (j : ZMod (2 * S.count)) : Set S.period.QuotientTorus := S.slabAt (j.val : ℤ)
def slabAlgebraOfClass (j : ZMod (2 * S.count)) :
    Subalgebra ℂ (S.period.QuotientField → ℂ) :=
  S.slabAlgebra (j.val : ℤ)
def torusReflectionOfClass {m : ℕ} (j : ZMod m) : S.period.TorusMap :=
  S.torusReflection (j.val : ℤ)
def conjReflectOfClass {m : ℕ} (j : ZMod m) (F : S.period.QuotientField → ℂ) :
    S.period.QuotientField → ℂ :=
  S.conjReflectAt (j.val : ℤ) F
theorem exists_val_eq_add_two_mul_mul (k : ℤ) :
    ∃ m : ℤ, (((k : ZMod (2 * S.count)).val : ℕ) : ℤ) = k + 2 * (S.count : ℤ) * m := by
  have h : ((((k : ZMod (2 * S.count)).val : ℕ) : ℤ) : ZMod (2 * S.count)) =
      (k : ZMod (2 * S.count)) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h
  refine ⟨-m, ?_⟩
  push_cast at hm
  linarith
theorem slabOfClass_intCast (k : ℤ) : S.slabOfClass (k : ZMod (2 * S.count)) = S.slabAt k := by
  obtain ⟨m, hm⟩ := S.exists_val_eq_add_two_mul_mul k
  rw [slabOfClass, hm, slabAt_add_two_mul_mul]
theorem slabAlgebraOfClass_intCast (k : ℤ) :
    S.slabAlgebraOfClass (k : ZMod (2 * S.count)) = S.slabAlgebra k := by
  obtain ⟨m, hm⟩ := S.exists_val_eq_add_two_mul_mul k
  rw [slabAlgebraOfClass, hm, slabAlgebra_add_two_mul_mul]
def ValModEqTwo (j k : ZMod (2 * S.count)) : Prop :=
  ((j.val : ℤ)) ≡ (k.val : ℤ) [ZMOD 2]
end SlabDecomposition
end InfiniteLattice
end YangMills.Construction
