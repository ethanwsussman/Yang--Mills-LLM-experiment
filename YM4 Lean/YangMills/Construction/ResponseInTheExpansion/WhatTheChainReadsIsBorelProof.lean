import YangMills.Construction.CellOfTheFlow.LongClassesAtAllLevelsProof
import YangMills.Construction.ClusterExpansionOfAStep.ChartCoordinateIsBorelProof
import YangMills.Construction.ResponseInTheExpansion.TheDrawBelowHasItsLaw
import YangMills.Construction.ResponseInTheExpansion.WhatTheChainReadsIsBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open ClusterExpansionOfAStep BlockAverages LumpContours TorusLumps TorusFields StepSettings WeightedResponses
namespace ChainMeasurability
private theorem measurableQuaternion_minimalLog :
    MeasurableQuaternion fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]) := by apply _root_.YangMills.Construction.StepCosts.measurableQuaternion_minimalLog <;> assumption
private theorem measurableSet_hotCoreSites_eq (R : StepSetup) (n : ℕ) [NeZero n]
    (a : Finset (TorusSite n)) :
    MeasurableSet {V : TorusField n | hotCoreSites R V = a} := by apply _root_.YangMills.SharedProofs.p5873 <;> assumption
end ChainMeasurability
open ChainMeasurability in
theorem chainMeasurabilityStatement_of_forgetLastStep (hD : forgetLastStepStatement) :
    chainMeasurabilityStatement :=
  ⟨fun R n _ a => measurableSet_hotCoreSites_eq R n a, measurableQuaternion_minimalLog,
    fun ℓ hf hfl T hcut hcoin β s n _ =>
      ⟨(hD ℓ hf hfl T hcut hcoin β s n).1, (hD ℓ hf hfl T hcut hcoin β s n).2.map_eq⟩⟩
end YangMills.Construction.ResponseInTheExpansion
end
