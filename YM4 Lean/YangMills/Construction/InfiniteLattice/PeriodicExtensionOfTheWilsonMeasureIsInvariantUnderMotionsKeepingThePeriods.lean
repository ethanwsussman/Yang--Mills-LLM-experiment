import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.PeriodLatticesToriAndTheirWilsonMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def PeriodicGibbsSymmetricUnderPeriodPreservingMotions : Prop :=
  ∀ (a β : ℝ), 0 < a → 0 < β → ∀ Γ : PeriodSublattice a,
    ∀ (r : LatticeSymmetry a), ∀ R ∈ hyperoctahedralLinearGroup, ∀ v : LatticePoint a,
      (∀ x, r.toFun x = R x + (v : AmbientSpace)) →
      R '' (Subtype.val '' (Γ.periods : Set (LatticePoint a))) =
          Subtype.val '' (Γ.periods : Set (LatticePoint a)) →
        IsSymmetricUnder (Γ.liftedGibbsMeasure β) r
end InfiniteLattice
end YangMills.Construction
