import Reconstruction.DomainFacts
import Reconstruction.LimitWitnesses
import YangMills.Construction.ClusterExpansionOfAStep.ParametersExist
import YangMills.Construction.InfiniteLattice.TorusStatesAreTheVolumeLimitPoints
import YangMills.Construction.ParameterData.ScaleSequenceData
import YangMills.Construction.QuaternionicWilsonModel.ARoomFunctionExists
import YangMills.Construction.QuaternionicWilsonModel.SomeFunctionalHasSchwingerFunctions
import YangMills.Construction.QuaternionicWilsonModel.TheArgumentsLieInTheirDomains
import YangMills.Construction.QuaternionicWilsonModel.TheDefaultCasesAreUnused
import YangMills.Construction.QuaternionicWilsonModel.TheFlowRepresentsTheMixedMoment
import YangMills.Construction.QuaternionicWilsonModel.TheKernelAndTheArraysOfTheTop
import YangMills.Construction.QuaternionicWilsonModel.TheLimitsOfTheTopAreRealAndNotZero
import YangMills.Construction.QuaternionicWilsonModel.TheQuaternionModelIsSUTwoWithWilsonsWeight
import YangMills.Construction.QuaternionicWilsonModel.TheSeamsOfTheModel
import YangMills.Construction.QuaternionicWilsonModel.TheTopOfTheTrajectoryWithTheFlow
import YangMills.Construction.QuaternionicWilsonModel.TheTorusStatesHaveAMember
import YangMills.Construction.QuaternionicWilsonModel.WhatTheTopGivesAtEveryCoupling
import Mathlib
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.TopAux
structure NonvacuityParts : Prop where
  argumentsInDomains : ConditionDomains.Statement
  schwingerSequenceExists : TopAux.SchwingerSequenceExists.Statement
  fallbacksUnread : ConditionDefaults.NonvacuityStatement
  roomFunctionExists : QuaternionicWilsonModel.RoomFunctionExists.SuccIsSubexpGrowth
  testClassesNonempty : TopAux.NonemptyTestClasses.Statement
  torusLimitsAreVolumeLimits : InfiniteLattice.TorusLimitsAreInfiniteVolumeLimits
  torusLimitSetNonempty : QuaternionicWilsonModel.TorusLimitSetNonempty.NonemptyStatement
  quaternionModelIsWilsonSU2 : QuaternionModel.quaternionModelIsWilsonSU2Statement
  flowReadsMixedMoment : TopAux.flowReadsMixedMomentStatement
  modelSeams : ModelSeams.seamsStatement
  kernelAndFunctionals : TopAux.kernelAndFunctionalsStatement
  everyCoupling : ModelSeams.everyCouplingStatement
  limitsRealAndNonzero : QuaternionicWilsonModel.TopLimitsRealNonzero.MainStatement
  trajectoryData : TrajectoryData.trajectoryDataStatement
  topWithFlowBound : TopAux.TopWithFlowBound.Statement
  parametersCanBeChosen : ClusterExpansionOfAStep.ParametersCanBeChosen
def nonvacuityStatement : Prop :=
  NonvacuityParts
end YangMills.Construction.TopAux
end

noncomputable section
namespace YangMills.Construction.TopAux
theorem nonvacuity_of_parts
    (hDomains : YangMills.Construction.ConditionDomains.Statement)
    (hSchwinger : YangMills.Construction.TopAux.SchwingerSequenceExists.Statement)
    (hFallbacks : YangMills.Construction.ConditionDefaults.NonvacuityStatement)
    (hRoom : YangMills.Construction.QuaternionicWilsonModel.RoomFunctionExists.SuccIsSubexpGrowth)
    (hClasses : YangMills.Construction.TopAux.NonemptyTestClasses.Statement)
    (hLimits : YangMills.Construction.InfiniteLattice.TorusLimitsAreInfiniteVolumeLimits)
    (hNonempty : YangMills.Construction.QuaternionicWilsonModel.TorusLimitSetNonempty.NonemptyStatement)
    (hModel : YangMills.Construction.QuaternionModel.quaternionModelIsWilsonSU2Statement)
    (hMoment : YangMills.Construction.TopAux.flowReadsMixedMomentStatement)
    (hSeams : YangMills.Construction.ModelSeams.seamsStatement)
    (hKernel : YangMills.Construction.TopAux.kernelAndFunctionalsStatement)
    (hCoupling : YangMills.Construction.ModelSeams.everyCouplingStatement)
    (hRealNonzero : YangMills.Construction.QuaternionicWilsonModel.TopLimitsRealNonzero.MainStatement)
    (hFlowData : YangMills.Construction.TrajectoryData.trajectoryDataStatement)
    (hTop : YangMills.Construction.TopAux.TopWithFlowBound.Statement)
    (hParams : YangMills.Construction.ClusterExpansionOfAStep.ParametersCanBeChosen) :
    YangMills.Construction.TopAux.nonvacuityStatement :=
  (⟨hDomains, hSchwinger, hFallbacks, hRoom, hClasses, hLimits, hNonempty, hModel, hMoment, hSeams,
    hKernel, hCoupling, hRealNonzero, hFlowData, hTop, hParams⟩ : YangMills.Construction.TopAux.NonvacuityParts)
end YangMills.Construction.TopAux
end
