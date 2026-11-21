import YangMills.Construction.ReflectionPositivity.SimpleTransitivityOnTheSlabs
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open NormalFamilies
instance nonempty_latticeSymmetry_one : Nonempty (LatticeSymmetry 1) := ⟨shift 0⟩
namespace SlabDecomposition
variable (S : SlabDecomposition)
def InducesTorusMap (g : S.period.TorusMap) (r : LatticeSymmetry 1) : Prop :=
  IsClassIsometry S.normal r.toFun ∧ S.period.descendedTorusMap r = g
def inducingSymmetry (g : S.period.TorusMap) : LatticeSymmetry 1 :=
  Classical.epsilon (S.InducesTorusMap g)
def groupPullback (g : S.period.TorusMap) (U : S.period.QuotientField) :
    S.period.QuotientField :=
  S.period.pullbackField (S.inducingSymmetry g) U
def groupAct (g : S.period.TorusMap) (f : S.period.QuotientField → ℂ) :
    S.period.QuotientField → ℂ :=
  fun U => f (S.groupPullback g U)
def slabCopy (j k : ZMod (2 * S.count)) (f : S.period.QuotientField → ℂ) :
    S.period.QuotientField → ℂ :=
  open Classical in
  if S.IsGroupTranslation (S.slabTransporter j k) then
    S.groupAct (S.slabTransporter j k) f
  else
    fun U => conj (S.groupAct (S.slabTransporter j k) f U)
def fold (β : ℝ) (j : ZMod (2 * S.count)) (f : S.period.QuotientField → ℂ) : ℂ :=
  ∫ U, (∏ k : ZMod (2 * S.count), S.slabCopy j k f U) * (S.period.boltzmannWeight β U : ℂ)
    ∂S.period.quotientHaar
end SlabDecomposition
end YangMills.Construction.InfiniteLattice
