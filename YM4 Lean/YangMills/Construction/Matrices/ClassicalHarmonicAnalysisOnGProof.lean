import YangMills.Construction.Matrices.CharactersOfG
import YangMills.Construction.Matrices.ClassFunctionsAsKernelsOnG
import YangMills.Construction.Matrices.ClassicalHarmonicAnalysisOnG
import YangMills.Construction.Matrices.ClebschGordanRuleOnG
import YangMills.Construction.Matrices.FieldsOnCoefficientSpacesOfG
import YangMills.Construction.Matrices.OrthogonalityRelationsAndPeterWeylOnG
import YangMills.Construction.Matrices.ProjectionsOntoCoefficientSpacesOfG
import YangMills.Construction.Matrices.RepresentationsOfGAreUnitaryAndIrreducible
import YangMills.Construction.Matrices.WeylIntegrationOnG
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SpinHarmonics
theorem harmonicAnalysisFacts_of_components
    (hReps : SpinRepsUnitaryIrreducible.Statement)
    (hOrth : PeterWeylOrthogonality.Statement)
    (hChar : AllCharacterFacts)
    (hWeyl : WeylIntegration.statement)
    (hProj : CoeffProjections.Statement)
    (hCG : AllClebschGordan)
    (hFields : AllRightFieldFacts)
    (hKer : AllConjInvariantKernels) :
    HarmonicAnalysisFacts :=
  fun a b => ⟨hReps a b, hOrth a b, hChar a, hWeyl, hProj a b,
    hCG a, hFields a, hKer a⟩
end YangMills.Construction.SpinHarmonics
