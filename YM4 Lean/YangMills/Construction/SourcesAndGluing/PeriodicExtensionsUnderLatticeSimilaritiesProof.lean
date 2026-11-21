import YangMills.Construction.InfiniteLattice.PeriodGroupsAndCumulantsInAState
import YangMills.Construction.SourcesAndGluing.PeriodicExtensionsUnderLatticeSimilaritiesForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.ScaledMotionLift
variable {D : GluingSetup} {e : ScaleExponent D} (Φ : ScaledLatticeMotion e)
theorem pullTorusField_mem {V : e.target.PeriodicLink → Matrices.ComplexMatrix2}
    (hV : V ∈ e.target.gaugeFields) :
    Φ.pullTorusField V ∈
      PeriodicLattice.compactGaugeFields D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) :=
  ⟨fun b _ => hV.1 (Φ.onTorusLink b) (Set.mem_univ _),
    fun b _ => hV.2 (Φ.onTorusLink b) (Set.mem_univ _)⟩
theorem projectLink_onLink (b : InfiniteLattice.Link D.mesh) :
    InfiniteLattice.projectLink e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ) (Φ.onLink b) =
      Φ.onTorusLink (InfiniteLattice.projectLink D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) b) :=
  PeriodicLattice.Bond.ext (Subtype.ext (Φ.onTorus_torusProj b.initial).symm)
    (Subtype.ext (Φ.onTorus_torusProj b.terminal).symm)
theorem claim_holds : ScaledMotionLiftClaim := by
  intro D e Φ V hV
  have hV' : V ∈ PeriodicLattice.compactGaugeFields e.target.L (e.target.m : ℕ)
      ((e.target.K : ℕ) : ℤ) :=
    hV
  refine Subtype.ext (funext fun b => Subtype.ext ?_)
  have hleft := InfiniteLattice.liftField_apply e.target.L (e.target.m : ℕ)
    ((e.target.K : ℕ) : ℤ) hV' (Φ.onLink b)
  have hright := InfiniteLattice.liftField_apply D.L (D.m : ℕ) ((D.K : ℕ) : ℤ)
    (pullTorusField_mem Φ hV) b
  exact hleft.trans ((congrArg V (projectLink_onLink Φ b)).trans hright.symm)
end YangMills.Construction.SourcesAndGluing.ScaledMotionLift
end
