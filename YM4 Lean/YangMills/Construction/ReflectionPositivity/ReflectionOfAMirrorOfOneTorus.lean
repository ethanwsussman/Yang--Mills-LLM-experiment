import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOnOneTorusIsometriesAndSymmetricFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.TorusMirrors
namespace AxisLevel
variable (s : YangMills.Construction.Conventions.StandingParameters) (M : AxisLevel)
def affineReflect (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  y + (2 * (M.level - y M.axis)) • YangMills.Construction.PeriodicLattice.coordVec M.axis
theorem reflect_proj (y : Fin 4 → ℝ) :
    M.reflect s (TorusCutoffs.proj s y) =
      TorusCutoffs.proj s (reflectVec s M.axis M.level y) :=
  congrFun ((unitCouplingData s M.axis).induces_reflect M.level) y
theorem reflectVec_reflectVec (y : Fin 4 → ℝ) :
    reflectVec s M.axis M.level (reflectVec s M.axis M.level y) = y := by
  have hdir : (unitCouplingData s M.axis).dir = M.axis := rfl
  simp only [reflectVec, CutoffMirrors.MirrorData.reflectVec_eq_sub, hdir]
  funext ν
  by_cases h : ν = M.axis
  · subst h
    simp [YangMills.Construction.PeriodicLattice.coordVec]
    ring
  · simp [YangMills.Construction.PeriodicLattice.coordVec, Pi.single_eq_of_ne h]
theorem reflect_involutive : Function.Involutive (M.reflect s) := by
  intro x
  obtain ⟨y, rfl⟩ := TorusCutoffs.exists_proj_eq s x
  rw [M.reflect_proj s, M.reflect_proj s, M.reflectVec_reflectVec s]
def reflectPerm : s.Torus ≃ s.Torus :=
  (M.reflect_involutive s).toPerm
end AxisLevel
namespace AxisReflection
variable (s : YangMills.Construction.Conventions.StandingParameters) (M : AxisLevel)
def TorusProperties : Prop :=
  (∀ y y', TorusCutoffs.proj s y = TorusCutoffs.proj s y' →
    TorusCutoffs.proj s (M.affineReflect y) = TorusCutoffs.proj s (M.affineReflect y')) ∧
  (∀ y, M.reflect s (TorusCutoffs.proj s y) = TorusCutoffs.proj s (M.affineReflect y)) ∧
  TorusTuples.IsTorusIsometry s (M.reflect s) ∧
  M.reflect s ∘ M.reflect s = id ∧
  ∀ (E : Type) (h : s.Torus → E),
    TorusTuples.transport (M.reflectPerm s) h = h ∘ M.reflect s
def SlabProperties : Prop :=
  M.openSlab s .neg = TorusCutoffs.proj s '' {y | M.level - s.side / 2 < y M.axis ∧ y M.axis < M.level} ∧
  M.reflect s '' M.openSlab s .pos = M.openSlab s .neg ∧
  M.reflect s '' M.openSlab s .neg = M.openSlab s .pos ∧
  M.openSlab s .pos ∩ M.openSlab s .neg = ∅
def AxisReflectionProperties : Prop :=
  ∀ (s : YangMills.Construction.Conventions.StandingParameters) (M : AxisLevel),
    TorusProperties s M ∧ SlabProperties s M
end AxisReflection
end YangMills.Construction.ReflectionPositivity.TorusMirrors
end
