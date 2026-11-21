import YangMills.Construction.SourcesAndGluing.ConfigurationsUnderLatticeSimilaritiesOfFourSpace
import YangMills.Construction.SourcesAndGluing.ObservablesUnderLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.SourcesAndGluing.PlaquettesUnderLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.SourcesAndGluing.ScalingOfLatticeSimilaritiesOfFourSpaceForm
import Mathlib
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.ScaledMotionObservables
theorem pullsObservables {D : GluingSetup} {e : ScaleExponent D} {Φ : ScaledLatticeMotion e}
    (hs : Φ.IsDilatingBijectionOfSpace) (hp : Φ.MapsPlaquettesOfSpace)
    (hc : Φ.PullsFieldsOfSpace) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] : Φ.PullsObservablesOfSpace E := by
  intro f _ U'
  obtain ⟨hbij, -⟩ := hs
  obtain ⟨-, hpbij, -, hcenter⟩ := hp
  obtain ⟨-, -, -, -, hact⟩ := hc
  have hinv : Function.LeftInverse (Function.invFun Φ.onSpace) Φ.onSpace :=
    Function.leftInverse_invFun hbij.1
  unfold InfiniteLattice.smearedEnergy
  refine Eq.trans (finsum_congr fun p => ?_) (finsum_comp Φ.onPlaquette hpbij)
  rw [hcenter p, Function.comp_apply, hinv]
  exact congrArg (· • f p.center) (hact p U')
theorem scaledMotionObservablesOfSpace_holds (hs : ScaledMotionDilationOfSpaceClaim)
    (hp : ScaledMotionPlaquettesOfSpaceClaim)
    (hc : FieldsUnderScaledMotionsOfSpace.Statement) : ScaledMotionObservablesOfSpaceClaim :=
  fun D e Φ => ⟨pullsObservables (hs D e Φ) (hp D e Φ) (hc D e Φ) ℝ,
    pullsObservables (hs D e Φ) (hp D e Φ) (hc D e Φ) ℂ⟩
end YangMills.Construction.SourcesAndGluing.ScaledMotionObservables
end
