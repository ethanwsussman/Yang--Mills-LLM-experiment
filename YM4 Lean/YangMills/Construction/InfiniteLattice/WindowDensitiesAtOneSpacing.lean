import YangMills.Construction.InfiniteLattice.LatticeOfACutoffAndTheVariablesOfASetOfBonds
import YangMills.Construction.InfiniteLattice.WindowDensityAtACutoff
import YangMills.Construction.InfiniteLattice.WindowsKernelOperatorAndDensitiesAtOneSpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
open PeriodicExtensions
namespace LinkWindow
section Properties
variable {a : ℝ} (W : LinkWindow a)
def KernelDensityBounds (ha : 0 < a) (β : ℝ) : Prop :=
  Continuous (fun p : W.Assignments × LinkVariables W.rim =>
      W.rimKernel ha β p.1 p.2) ∧
    (∀ (U : W.Assignments) (ξ : LinkVariables W.rim),
      Real.exp (-(2 * β * W.faceCount)) ≤ W.rimKernel ha β U ξ ∧
        W.rimKernel ha β U ξ ≤ Real.exp (2 * β * W.faceCount)) ∧
    (∀ (ω : RealWeakState a) (U : W.Assignments),
      Real.exp (-(2 * β * W.faceCount)) ≤ W.stateDensity ha β ω U ∧
        W.stateDensity ha β ω U ≤ Real.exp (2 * β * W.faceCount)) ∧
    ∀ ρ ω : RealWeakState a, W.stateDistance ha β ρ ω ≤
      ENNReal.ofReal (Real.exp (2 * β * W.faceCount) *
        TestFunctions.uniformNorm fun U : W.Assignments =>
          W.stateDensity ha β ω U - W.stateDensity ha β ρ U)
def IsInvariantState (ha : 0 < a) (β : ℝ) (ω : RealWeakState a) : Prop :=
  ∀ f : C(GaugeField a, ℝ), CutoffLattice.DependsOnlyOn f (W.links : Set (Link a)) →
    ω.value (W.realOperator ha β f) = ω.value f
def MarginalHasStateDensity (ha : 0 < a) (β : ℝ) : Prop :=
  ∀ ω : RealWeakState a, W.IsInvariantState ha β ω →
    CutoffLinks.marginalOn (W.links : Set (Link a)) ω.measure =
      haarWithDensity (W.links : Set (Link a)) fun U => W.stateDensity ha β ω U
def GibbsStatesInvariant (ha : 0 < a) (β : ℝ) : Prop :=
  ∀ ω : RealWeakState a, IsGibbs β ω.measure → W.IsInvariantState ha β ω
def InvariantStatesComparable (ha : 0 < a) (β : ℝ) : Prop :=
  ∀ ρ ω : RealWeakState a,
    W.IsInvariantState ha β ρ →
    W.IsInvariantState ha β ω →
    ∀ f : LinkVariables (W.links : Set (Link a)) → ℝ, Measurable f → (∃ C : ℝ, ∀ U, |f U| ≤ C) →
      ENNReal.ofReal |ρ.value (CutoffLinks.liftToFields f) -
          ω.value (CutoffLinks.liftToFields f)| ≤
        W.stateDistance ha β ρ ω *
          ENNReal.ofReal (ρ.value (CutoffLinks.liftToFields fun U => |f U|))
def StateDensityContinuous (ha : 0 < a) (β : ℝ) : Prop :=
  ∀ (ω : ℕ → RealWeakState a) (ω₀ : RealWeakState a), RealWeakState.TendstoWeakly ω ω₀ →
    Tendsto (fun n => TestFunctions.uniformNorm fun U : W.Assignments =>
      W.stateDensity ha β (ω n) U - W.stateDensity ha β ω₀ U) atTop (𝓝 0)
end Properties
section TorusSides
variable {L K : ℕ} (W : LinkWindow (PeriodicLattice.meshSize L (K : ℤ)))
def LiftedWilsonInvariant (ha : 0 < PeriodicLattice.meshSize L (K : ℤ)) (β : ℝ) (m : ℕ) : Prop :=
  W.leastTorusSide ≤ ((PeriodicLattice.torusSide L m : ℝ) : EReal) →
    ∃ ρ : RealWeakState (PeriodicLattice.meshSize L (K : ℤ)),
      ρ.measure = liftedWilsonMeasure L m K β ∧
        W.IsInvariantState ha β ρ
def admissibleSides (ha : 0 < PeriodicLattice.meshSize L (K : ℤ)) (β ε : ℝ) : Set ℝ :=
  {s | ∃ n : ℕ, 0 < n ∧ s = PeriodicLattice.torusSide L n ∧
    ∀ m : ℕ, 0 < m → s ≤ PeriodicLattice.torusSide L m →
      ∃ ρ : RealWeakState (PeriodicLattice.meshSize L (K : ℤ)),
        ρ.measure = liftedWilsonMeasure L m K β ∧
          W.infStateDistance ha β ρ (limitsOfLiftedMeasures L K β) ≤ ENNReal.ofReal ε}
def leastAdmissibleSide (ha : 0 < PeriodicLattice.meshSize L (K : ℤ)) (β ε : ℝ) : ℝ :=
  sInf (W.admissibleSides ha β ε)
end TorusSides
end LinkWindow
end InfiniteLattice
namespace WindowDensities
open InfiniteLattice
def Statement : Prop :=
  ∀ (L K : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L), 0 < K → ∀ β : ℝ, 0 < β →
    ∀ W : LinkWindow (PeriodicLattice.meshSize L (K : ℤ)),
      have ha : 0 < PeriodicLattice.meshSize L (K : ℤ) :=
        meshSize_natCast_pos (lt_of_lt_of_le (by norm_num) hL.2) K
      W.KernelDensityBounds ha β ∧
        W.MarginalHasStateDensity ha β ∧
        W.GibbsStatesInvariant ha β ∧
        (∀ m : ℕ, 0 < m → W.LiftedWilsonInvariant ha β m) ∧
        W.InvariantStatesComparable ha β ∧
        W.StateDensityContinuous ha β ∧
        ∀ ε : ℝ, 0 < ε → IsLeast (W.admissibleSides ha β ε) (W.leastAdmissibleSide ha β ε)
end WindowDensities
end YangMills.Construction
