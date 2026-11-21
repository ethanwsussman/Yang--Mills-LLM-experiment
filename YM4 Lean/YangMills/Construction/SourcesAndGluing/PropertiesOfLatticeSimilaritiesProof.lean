import YangMills.Construction.SourcesAndGluing.CompositeOfLatticeSimilarities
import YangMills.Construction.SourcesAndGluing.ConfigurationsUnderLatticeSimilaritiesOfFourSpace
import YangMills.Construction.SourcesAndGluing.ConfigurationsUnderLatticeSimilaritiesOfTori
import YangMills.Construction.SourcesAndGluing.InverseOfALatticeSimilarityForm
import YangMills.Construction.SourcesAndGluing.LatticeSimilarityDeterminesItsLinearPartForm
import YangMills.Construction.SourcesAndGluing.LinksUnderLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.SourcesAndGluing.LinksUnderLatticeSimilaritiesOfToriForm
import YangMills.Construction.SourcesAndGluing.MeasuresUnderLatticeSimilaritiesForm
import YangMills.Construction.SourcesAndGluing.ObservablesUnderLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.SourcesAndGluing.ObservablesUnderLatticeSimilaritiesOfToriForm
import YangMills.Construction.SourcesAndGluing.PeriodicExtensionsUnderLatticeSimilaritiesForm
import YangMills.Construction.SourcesAndGluing.PlaquettesUnderLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.SourcesAndGluing.PlaquettesUnderLatticeSimilaritiesOfToriForm
import YangMills.Construction.SourcesAndGluing.PropertiesOfLatticeSimilaritiesForm
import YangMills.Construction.SourcesAndGluing.ScalingOfLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.SourcesAndGluing.ScalingOfLatticeSimilaritiesOfTori
import YangMills.Construction.SourcesAndGluing.WilsonActionUnderLatticeSimilarities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
theorem scaledMotionProperties
    (h1 : ScaledMotionDilationOfSpaceClaim)
    (h2 : TorusDilationOfScaledMotions.Statement)
    (h3 : ScaledMotionRotationClaim)
    (h4 : ScaledMotionInverseClaim)
    (h5 : CompositionOfScaledMotions.Statement)
    (h6 : ScaledMotionLinksOfSpaceClaim)
    (h7 : ScaledMotionLinksOfToriClaim)
    (h8 : ScaledMotionPlaquettesOfSpaceClaim)
    (h9 : ScaledMotionPlaquettesOfToriClaim)
    (h10 : FieldsUnderScaledMotionsOfSpace.Statement)
    (h11 : FieldsUnderScaledMotionsOfTori.Statement)
    (h12 : ScaledMotionObservablesOfSpaceClaim)
    (h13 : ScaledMotionObservablesOfToriClaim)
    (h14 : ActionUnderScaledMotions.Statement)
    (h15 : ScaledMotionMeasuresClaim)
    (h16 : ScaledMotionLiftClaim) :
    ScaledMotionPropertiesClaim :=
  fun D e Φ => ⟨h1 D e Φ, h2 D e Φ, h3 D e Φ, h4 D e Φ, h5 D e Φ, h6 D e Φ,
    h7 D e Φ, h8 D e Φ, h9 D e Φ, h10 D e Φ, h11 D e Φ, (h12 D e Φ).1,
    (h12 D e Φ).2, (h13 D e Φ).1, (h13 D e Φ).2, h14 D e Φ, h15 D e Φ, h16 D e Φ⟩
end YangMills.Construction.SourcesAndGluing
end
