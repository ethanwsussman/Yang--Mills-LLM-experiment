import YangMills.Construction.InfiniteLattice.WeakLimitPointsAreLimitsOfSequences
import YangMills.Construction.InfiniteLattice.WindowDensityAtACutoff
import YangMills.Construction.InfiniteLattice.WindowsKernelOperatorAndDensitiesAtOneSpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.WeakConvergence
open PeriodicExtensions
section Sequences
variable {a : ℝ}
def FrequentlyClose (μ : ℕ → RealWeakState a) (ν : RealWeakState a) : Prop :=
  ∀ (s : Finset C(GaugeField a, ℝ)) (ε : ℝ), 0 < ε →
    {i : ℕ | ∀ f ∈ s, |(μ i).value f - ν.value f| < ε}.Infinite
def HasSubseqTendsto (μ : ℕ → RealWeakState a) (ν : RealWeakState a) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ RealWeakState.TendstoWeakly (μ ∘ φ) ν
end Sequences
def IsLiftedAlongSides (L K : ℕ) (β : ℝ) (ℓ : ℕ → ℝ)
    (ρ : ℕ → RealWeakState (PeriodicLattice.meshSize L (K : ℤ))) : Prop :=
  ∀ i, 1 ≤ i → IsLiftedMeasureAtSide L K β (ℓ i) (ρ i)
def LiftedLimitsCharacterization (L K : ℕ) (β : ℝ) : Prop :=
  (∃ ρ, IsLiftedAlongSides L K β (fun i => PeriodicLattice.torusSide L i) ρ) ∧
    (∀ ρ, IsLiftedAlongSides L K β (fun i => PeriodicLattice.torusSide L i) ρ →
      ∀ ν, (ν ∈ limitsOfLiftedMeasures L K β ↔ FrequentlyClose ρ ν) ∧
        (ν ∈ limitsOfLiftedMeasures L K β ↔ HasSubseqTendsto ρ ν)) ∧
    ∀ μ : Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ))),
      IsInfiniteVolumeLimit L K β μ ↔ ∃ ν ∈ limitsOfLiftedMeasures L K β, ν.measure = μ
def LiftedMeasuresHaveLimitPoints (L K : ℕ) (β : ℝ) : Prop :=
  (limitsOfLiftedMeasures L K β).Nonempty ∧
    ∀ ℓ : ℕ → ℝ, SidesTendToInfinity L ℓ →
      (∃ ρ, IsLiftedAlongSides L K β ℓ ρ) ∧
        ∀ ρ, IsLiftedAlongSides L K β ℓ ρ →
          ∃ ν ∈ limitsOfLiftedMeasures L K β, HasSubseqTendsto ρ ν
section Window
variable {a : ℝ} (W : LinkWindow a)
def KernelAndDensitiesBounded (ha : 0 < a) (β : ℝ) : Prop :=
  W.faces.Finite ∧ W.rim.Finite ∧
    Continuous (fun x : W.Assignments × LinkVariables W.rim =>
      W.rimKernel ha β x.1 x.2) ∧
    (∀ (V : W.Assignments) (η : LinkVariables W.rim),
      Real.exp (-(2 * β * W.faceCount)) ≤ W.rimKernel ha β V η ∧
        W.rimKernel ha β V η ≤ Real.exp (2 * β * W.faceCount)) ∧
    (∀ η : LinkVariables W.rim, ∫ V, W.rimKernel ha β V η ∂W.haarProd = 1) ∧
    (∀ ν : RealWeakState a, Continuous (W.stateDensity ha β ν) ∧
      ∀ V : W.Assignments, Real.exp (-(2 * β * W.faceCount)) ≤ W.stateDensity ha β ν V ∧
        W.stateDensity ha β ν V ≤ Real.exp (2 * β * W.faceCount)) ∧
    ∀ μ ν : RealWeakState a, W.stateDistance ha β μ ν < ⊤
def DensitiesTendstoAlongWeakLimits (ha : 0 < a) (β : ℝ) : Prop :=
  ∀ (μ : ℕ → RealWeakState a) (ν : RealWeakState a), RealWeakState.TendstoWeakly μ ν →
    Tendsto (fun i => TestFunctions.uniformNorm fun V : W.Assignments =>
      W.stateDensity ha β (μ i) V - W.stateDensity ha β ν V) atTop (𝓝 0) ∧
    Tendsto (fun i => W.stateDistance ha β (μ i) ν) atTop (𝓝 0)
end Window
def WeakConvergenceWindowStatement : Prop :=
  ∀ (L K : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L), 0 < K → ∀ β : ℝ, 0 < β →
    have ha : 0 < PeriodicLattice.meshSize L (K : ℤ) :=
      meshSize_natCast_pos (lt_of_lt_of_le (by norm_num) hL.2) K
    (∀ (μ : ℕ → RealWeakState (PeriodicLattice.meshSize L (K : ℤ)))
        (ν : RealWeakState (PeriodicLattice.meshSize L (K : ℤ))),
      FrequentlyClose μ ν ↔ HasSubseqTendsto μ ν) ∧
    LiftedLimitsCharacterization L K β ∧
    (∀ μ : ℕ → RealWeakState (PeriodicLattice.meshSize L (K : ℤ)),
      ∃ ν, HasSubseqTendsto μ ν) ∧
    LiftedMeasuresHaveLimitPoints L K β ∧
    ∀ W : LinkWindow (PeriodicLattice.meshSize L (K : ℤ)),
      KernelAndDensitiesBounded W ha β ∧
        DensitiesTendstoAlongWeakLimits W ha β
end YangMills.Construction.InfiniteLattice.WeakConvergence
