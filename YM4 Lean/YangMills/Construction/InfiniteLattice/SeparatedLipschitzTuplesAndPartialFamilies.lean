import YangMills.Construction.InfiniteLattice.ConnectedCorrelations
import YangMills.Construction.InfiniteLattice.CutoffLattice
import Mathlib
set_option autoImplicit false
open Filter Set MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction
namespace SeparatedFamilies
open YangMills.Construction.InfiniteLattice YangMills.Construction.CutoffLattice
abbrev euclidLength (x : AmbientSpace) : ℝ := TorusMetric.euclidNormVec x
def torusSupport {L m : ℕ} (g : PeriodicLattice.FourTorus L m → ℝ) :
    Set (PeriodicLattice.FourTorus L m) :=
  {x | ∀ ε : ℝ, 0 < ε → ∃ y, g y ≠ 0 ∧ TorusMetric.torusEuclidNorm (x - y) < ε}
def originBall (r : ℝ≥0∞) : Set AmbientSpace := {x | ENNReal.ofReal (euclidLength x) < r}
theorem originBall_top : originBall ⊤ = univ := by
  ext x
  simp [originBall]
theorem originBall_ofReal {r : ℝ} (hr : 0 < r) :
    originBall (ENNReal.ofReal r) = {x | euclidLength x < r} := by
  ext x
  simp [originBall, ENNReal.ofReal_lt_ofReal_iff hr]
def IsEuclidLipschitz (g : AmbientSpace → ℝ) : Prop :=
  ∃ C : ℝ, ∀ x y, |g x - g y| ≤ C * euclidLength (x - y)
structure IsSeparatedLipschitzFamily {n : ℕ} (X : Fin n → AmbientSpace → ℝ) : Prop where
  pos_arity : 1 ≤ n
  lipschitz : ∀ i, IsEuclidLipschitz (X i)
  hasCompactSupport : ∀ i, HasCompactSupport (X i)
  pairwise_disjoint : Pairwise fun i j => Disjoint (tsupport (X i)) (tsupport (X j))
def separatedLipschitzSet (n : ℕ) : Set (Fin n → AmbientSpace → ℝ) :=
  {X | IsSeparatedLipschitzFamily X}
def boundedCompactlySupported : Set (AmbientSpace → ℝ) :=
  {g | (∃ C : ℝ, ∀ x, |g x| ≤ C) ∧ HasCompactSupport g}
def smearedObservable (L K : ℕ) (g : AmbientSpace → ℝ) (U : FieldsAt L K) : ℝ :=
  ∑ᶠ p ∈ {p : ElementaryPlaquette (spacingAt L K) | g p.center ≠ 0},
    g p.center * faceEnergy U p
theorem smearedObservable_eq_smearedEnergy (L K : ℕ) (g : AmbientSpace → ℝ) (U : FieldsAt L K) :
    smearedObservable L K g U = smearedEnergy g U := by
  unfold smearedObservable smearedEnergy
  refine finsum_congr fun p => ?_
  by_cases h : g p.center = 0
  · simp [h]
  · simp [h, mul_comm]
def torusC1 (L m : ℕ) : Set (PeriodicLattice.FourTorus L m → ℝ) :=
  {g | ContDiff ℝ 1 (g ∘ TorusMetric.torusProj (PeriodicLattice.torusSide L m))}
def fieldProbabilityMeasures (L K : ℕ) : Set (Measure (FieldsAt L K)) :=
  {μ | IsProbabilityMeasure μ}
def truncatedCorrelation {L K : ℕ} (μ : Measure (FieldsAt L K)) {n : ℕ}
    (g : Fin n → AmbientSpace → ℝ) : ℂ :=
  Cumulants.mixedCumulant μ fun i => smearedObservable L K (g i)
theorem truncatedCorrelation_eq_ursellFunction {L K : ℕ}
    (μ : Measure (FieldsAt L K)) {n : ℕ} (g : Fin n → AmbientSpace → ℝ) :
    truncatedCorrelation μ g = ursellFunction μ n g := by
  unfold truncatedCorrelation ursellFunction
  congr 1
  funext i U
  exact smearedObservable_eq_smearedEnergy L K (g i) U
theorem IsEuclidLipschitz.continuous {g : AmbientSpace → ℝ} (hg : IsEuclidLipschitz g) :
    Continuous g := by
  obtain ⟨C, hC⟩ := hg
  have hv : Continuous fun v : AmbientSpace => euclidLength v :=
    Real.continuous_sqrt.comp (by fun_prop)
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h0 : Tendsto (fun y => C * euclidLength (y - x)) (𝓝 x) (𝓝 0) := by
    have hc : Continuous fun y : AmbientSpace => C * euclidLength (y - x) :=
      continuous_const.mul (hv.comp (continuous_id.sub continuous_const))
    simpa [TorusMetric.euclidNormVec] using hc.tendsto x
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun y => ?_) h0)
  simpa using hC y x
theorem apply_mem_boundedCompactlySupported {n : ℕ} {X : Fin n → AmbientSpace → ℝ}
    (hX : X ∈ separatedLipschitzSet n) (i : Fin n) :
    X i ∈ boundedCompactlySupported := by
  have hc : HasCompactSupport (X i) := hX.hasCompactSupport i
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous (hX.lipschitz i).continuous
  exact ⟨⟨C, fun x => by simpa using hC x⟩, hc⟩
def separatedTruncatedCorrelation {L K : ℕ} (μ : Measure (FieldsAt L K)) (n : ℕ)
    (X : separatedLipschitzSet n) : ℂ :=
  truncatedCorrelation μ X.1
def truncatedCorrelationFamily {L K : ℕ} (μ : Measure (FieldsAt L K)) (n : ℕ) (_hn : 2 ≤ n) :
    separatedLipschitzSet n → ℂ :=
  separatedTruncatedCorrelation μ n
def IsPermutationInvariantOn {n : ℕ} {S : Set (Fin n → AmbientSpace → ℝ)} (Φ : S → ℝ) : Prop :=
  ∃ hS : ∀ g ∈ S, ∀ σ : Equiv.Perm (Fin n), g ∘ σ ∈ S,
    ∀ (g : S) (σ : Equiv.Perm (Fin n)), Φ ⟨g.1 ∘ σ, hS g.1 g.2 σ⟩ = Φ g
def IsSlotwiseLinearOn {n : ℕ} {S : Set (Fin n → AmbientSpace → ℝ)} (Φ : S → ℝ) : Prop :=
  ∀ (k : Fin n) (a b : ℝ) (g g' : S), (∀ i, i ≠ k → g.1 i = g'.1 i) →
    ∀ hmem : Function.update g.1 k (a • g.1 k + b • g'.1 k) ∈ S,
      Φ ⟨_, hmem⟩ = a * Φ g + b * Φ g'
def separatedLipschitzSetIn (n : ℕ) (r : ℝ≥0∞) : Set (Fin n → AmbientSpace → ℝ) :=
  {X | X ∈ separatedLipschitzSet n ∧ ∀ i, tsupport (X i) ⊆ originBall r}
structure RadialFunctionalFamily (r : ℝ≥0∞) where
  radius_pos : 0 < r
  eval : (n : ℕ) → 2 ≤ n → separatedLipschitzSetIn n r → ℝ
  perm_invariant : ∀ (n : ℕ) (hn : 2 ≤ n), IsPermutationInvariantOn (eval n hn)
  slot_linear : ∀ (n : ℕ) (hn : 2 ≤ n), IsSlotwiseLinearOn (eval n hn)
end SeparatedFamilies
end YangMills.Construction
