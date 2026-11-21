import YangMills.Construction.Towers.AbelianOperatorsAreLocalAndSelfAdjoint
import YangMills.Construction.Towers.CovariantShiftsOfAnAbelianField
import YangMills.Construction.Towers.DerivativeOfTheActionAtAnAbelianField
import YangMills.Construction.Towers.EntriesOfTheAbelianKernels
import YangMills.Construction.Towers.FactsOfAbelianFields
import YangMills.Construction.Towers.LowerBoundsOfTheAbelianOperators
import YangMills.Construction.Towers.PlaquetteAnglesOfTheLinearAbelianField
import YangMills.Construction.Towers.PlaquettesOfAnAbelianField
import YangMills.Construction.Towers.QuadraticFormOfTheAbelianMassiveOperator
import YangMills.Construction.Towers.SymmetriesOfTheAbelianOperators
import YangMills.Construction.Towers.TheAlgebraOfTheCharges
import YangMills.Construction.Towers.TrigonometricPolynomialsDetermineTheirCoefficients
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower.AbelianFieldFacts
theorem allFacts_holds
    (hCoeffs : FourierCoeffsDetermined)
    (hCharges : ChargeAlgebraAndForms)
    (hFaces : AbelianFieldPlaquettes.Claim)
    (hSymm : AbelianOperatorSymmetries)
    (hShift : CovariantShiftsUnitary)
    (hOps : AbelianOperatorsLocalSelfAdjoint)
    (hEntries : AbelianKernelEntries.EntriesAreTrigPolynomials)
    (hQuad : MassiveOperatorQuadraticForm)
    (hLower : AbelianOperatorBounds.LowerBoundsHold)
    (hGrad : AbelianActionGradient.Statement)
    (hAngles : LinearFieldPlaquetteAngles.Claim) :
    AllFacts :=
  ⟨hCoeffs, hCharges.1, fun L hL _ _ =>
    ⟨hCharges.2 L hL, hEntries L hL, hAngles L hL, fun θ =>
      ⟨hOps L hL θ, hSymm L hL θ, hShift L hL θ, hFaces L hL θ,
        hQuad L hL θ, hLower L hL θ, hGrad L hL θ⟩⟩⟩
end YangMills.Construction.Tower.AbelianFieldFacts
