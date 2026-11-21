import YangMills.Construction.SourcesAndGluing.ConfigurationsUnderLatticeSimilaritiesOfTori
import YangMills.Construction.SourcesAndGluing.ObservablesUnderLatticeSimilaritiesOfToriForm
import YangMills.Construction.SourcesAndGluing.PlaquettesUnderLatticeSimilaritiesOfToriForm
import YangMills.Construction.SourcesAndGluing.ScalingOfLatticeSimilaritiesOfTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.ScaledMotionObservables
theorem pullsObservablesOfTori_of_module {D : GluingSetup} {e : ScaleExponent D}
    (Φ : ScaledLatticeMotion e)
    (hdil : Φ.IsDilatingBijectionOfTori) (hplaq : Φ.MapsPlaquettesOfTori)
    (hfield : Φ.PullsFieldsOfTori) (E : Type) [AddCommMonoid E] [Module ℝ E] :
    Φ.PullsObservablesOfTori E := by
  intro f V hV
  obtain ⟨hinj, -⟩ := hdil.1
  obtain ⟨-, hbij, -, hbar⟩ := hplaq
  obtain ⟨-, -, -, -, -, hcost⟩ := hfield
  have hsummand : ∀ p : D.PeriodicPlaquette,
      PeriodicLattice.plaquetteCost (Φ.pullTorusField V) p • f p.barycenter =
        PeriodicLattice.plaquetteCost V (Φ.onTorusPlaquette p) •
          (f ∘ Function.invFun Φ.onTorus) (Φ.onTorusPlaquette p).barycenter := by
    intro p
    rw [hcost p V hV, hbar p, Function.comp_apply,
      Function.leftInverse_invFun hinj p.barycenter]
  change (∑ᶠ p : D.PeriodicPlaquette,
      PeriodicLattice.plaquetteCost (Φ.pullTorusField V) p • f p.barycenter) =
    ∑ᶠ q : e.target.PeriodicPlaquette,
      PeriodicLattice.plaquetteCost V q • (f ∘ Function.invFun Φ.onTorus) q.barycenter
  rw [finsum_congr hsummand]
  exact finsum_comp
    (g := fun q : e.target.PeriodicPlaquette =>
      PeriodicLattice.plaquetteCost V q • (f ∘ Function.invFun Φ.onTorus) q.barycenter)
    Φ.onTorusPlaquette hbij
theorem claim_holds (hdil : TorusDilationOfScaledMotions.Statement)
    (hplaq : ScaledMotionPlaquettesOfToriClaim)
    (hfield : FieldsUnderScaledMotionsOfTori.Statement) : ScaledMotionObservablesOfToriClaim := by
  intro D e Φ
  exact ⟨pullsObservablesOfTori_of_module Φ (hdil D e Φ) (hplaq D e Φ) (hfield D e Φ) ℝ,
    pullsObservablesOfTori_of_module Φ (hdil D e Φ) (hplaq D e Φ) (hfield D e Φ) ℂ⟩
end YangMills.Construction.SourcesAndGluing.ScaledMotionObservables
end
