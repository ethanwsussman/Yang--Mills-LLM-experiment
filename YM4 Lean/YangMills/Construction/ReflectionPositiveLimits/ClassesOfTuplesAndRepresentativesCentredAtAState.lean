import YangMills.Construction.InfiniteLattice.SeparatedTuplesOfFourSpaceAsSymbols
import YangMills.Construction.ReflectionPositiveLimits.LatticeApproximationsRepresentativesAndLimits
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb)
def asSymbolTuple (s : YangMills.Construction.Conventions.StandingParameters) (X : Tuple) :
    YangMills.Construction.FourSpaceSymbols.SymTuple s :=
  ⟨X.len, fun i => X.1.get i⟩
def IsAdmissibleAt (s : YangMills.Construction.Conventions.StandingParameters) (d R : ℝ)
    (X : Tuple) : Prop :=
  YangMills.Construction.FourSpaceSymbols.TupleAdmissible d R (asSymbolTuple s X)
def admissibleClass (s : YangMills.Construction.Conventions.StandingParameters) (w d R : ℝ) :
    Set Tuple :=
  {X | IsAdmissibleAt s d R X ∧ X ∈ tuplesSupportedIn (centredCube (w - d / 2))}
def centeredProductLinear (L K : ℕ)
    (m : BorelProb (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ))) :
    TupleComb →ₗ[ℂ] (GaugeFieldsAtLevel L K → ℂ) :=
  Finsupp.linearCombination ℂ fun X U => ((centeredProduct L K m X U : ℝ) : ℂ)
end YangMills.Construction.ReflectionPositivity
