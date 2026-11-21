import YangMills.Construction.InfiniteLattice.ImagesOfBondsAndInvariantMeasuresOnATorus
import YangMills.Construction.InfiniteLattice.SignsAndWeakConvergenceAtSpacingOne
import YangMills.Construction.InfiniteLattice.ToriOfAnyShapeArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace PeriodSublattice
variable (Γ : PeriodSublattice 1)
def OrthogonalPartPreserves (r : LatticeSymmetry 1) : Prop :=
  r.orthogonalPart.mulVec '' (Subtype.val '' (Γ.periods : Set (LatticePoint 1))) =
    Subtype.val '' (Γ.periods : Set (LatticePoint 1))
def IsDescendedMap (r : LatticeSymmetry 1) (f : Γ.QuotientTorus → Γ.QuotientTorus) : Prop :=
  ∀ x : LatticePoint 1, f (Γ.quotientMap x) = Γ.quotientMap (r.pointMap x)
def descendedMap (r : LatticeSymmetry 1) : Γ.QuotientTorus → Γ.QuotientTorus :=
  Classical.epsilon (Γ.IsDescendedMap r)
def IsDescendedPullback (r : LatticeSymmetry 1)
    (h : Γ.QuotientField ≃ₜ Γ.QuotientField) : Prop :=
  ∀ U, Γ.lift (h U) = r.pullbackField (Γ.lift U)
def descendedPullback (r : LatticeSymmetry 1) :
    Γ.QuotientField ≃ₜ Γ.QuotientField :=
  @Classical.epsilon _ ⟨Homeomorph.refl _⟩ (Γ.IsDescendedPullback r)
end PeriodSublattice
def LatticeSymmetriesDescendToQuotient : Prop :=
  ∀ β : ℝ, 0 < β → ∀ Γ : PeriodSublattice 1,
    (∀ r : LatticeSymmetry 1, Γ.OrthogonalPartPreserves r →
      (∃! f : Γ.QuotientTorus → Γ.QuotientTorus, Γ.IsDescendedMap r f) ∧
      Γ.IsDescendedMap r (Γ.descendedMap r) ∧
      Function.Bijective (Γ.descendedMap r) ∧
      (∀ U : Γ.QuotientField, ∃! V : Γ.QuotientField,
        Γ.lift V = r.pullbackField (Γ.lift U)) ∧
      Γ.IsDescendedPullback r (Γ.descendedPullback r) ∧
      ∀ F ∈ continuousLocalFunctions 1,
        Γ.periodize (r.actOn F) = Γ.periodize F ∘ Γ.descendedPullback r) ∧
    ∀ 𝔸 : LocalObservableArray, 𝔸.FitsPeriods Γ → ∀ (t : ℝ) (v : LatticePoint 1), v ∈ 𝔸.sublattice →
      (shift v).orthogonalPart = 1 ∧
      PeriodSublattice.IsHomeomorphInvariant (𝔸.tiltedMeasure Γ β t)
        (Γ.descendedPullback (shift v))
end YangMills.Construction.InfiniteLattice
