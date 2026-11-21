import YangMills.Construction.FreeEnergiesOfTheFlow.MomentsOfTheFlow
import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import YangMills.Construction.ResponseInTheExpansion.CumulantsOfQuadraticForms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages RenormalizationStepParameters TorusLumps WeightedResponses ColdStepAtMirrorFrames
open Classical
open MeasureTheory
structure IsLocalQuadraticObservable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {I : Type} [Fintype I] {q : ℕ}
    (F : Fin (q + 1) → Ω → ℝ) (G : Ω → I → imaginaryQuaternions) (A B : Set Ω) (κ : Fin (q + 1) → Matrix I I ℝ)
    (Tc : Matrix I I ℝ) (c : Fin (q + 1) → ℝ) (x n C P : ℝ) (Cr xr : ℕ → ℝ) : Prop where
  measurableSet_good : MeasurableSet A
  aestronglyMeasurable_comp : ∀ (a : I) (e : Fin 3),
    AEStronglyMeasurable (Set.indicator A fun ω => imaginaryComponent e (G ω a)) μ
  comp_bounded : ∃ M : ℝ, ∀ᵐ ω ∂μ, ω ∈ A → ∀ (a : I) (e : Fin 3), |imaginaryComponent e (G ω a)| ≤ M
  gaussian_moments : ∀ (r : ℕ) (a : Fin r → I) (e : Fin r → Fin 3), r ≤ 16 →
    Integrable (Set.indicator A fun ω => ∏ i, imaginaryComponent (e i) (G ω (a i))) μ ∧
    |∫ ω, Set.indicator A (fun ω => ∏ i, imaginaryComponent (e i) (G ω (a i))) ω ∂μ -
      x ^ (-(r : ℝ) / 2) * wickPairingSum fun i i' => if e i = e i' then Tc (a i) (a i') else 0| ≤
      C * x ^ (-((r : ℝ) + 1) / 2 + 2 / 1000)
  covariance_symm : Tc.IsSymm
  covariance_bounded : ∀ a b, |Tc a b| ≤ C
  kernel_symm : ∀ i, (κ i).IsSymm
  kernel_mass : ∀ i, ∑ a, ∑ b, |κ i a b| ≤ C * n ^ 4 * Real.log x ^ 24
  quadratic_approx : ∀ (i : Fin (q + 1)) (r : ℕ), 1 ≤ r → xr r ≤ x →
    ∫⁻ ω, ENNReal.ofReal (Set.indicator (A ∩ B)
        (fun ω => |F i ω - c i - quadraticForm (κ i) (G ω)| ^ (2 * r)) ω) ∂μ ≤
      ENNReal.ofReal ((Cr r * n ^ 4 * x ^ (-(3 / 2 : ℝ) + 6 / 1000)) ^ (2 * r))
  bad_small : μ.real Aᶜ ≤ C * x ^ (-P)
  bad_within_small : μ.real (A ∩ Bᶜ) ≤ C * x ^ (-P)
def localQuadraticEstimateAt (Tb : ParameterAssignment) (y : ℝ) : Prop :=
  ∀ Kr : ResponseParameters, Kr.Admissible (Tb.stepParameters y) → ∀ v : ℝ, 0 < v → v ≤ 1 → ∀ P : ℝ,
    ∃ (Cr xr : ℕ → ℝ) (C x₀ : ℝ),
    ∀ (q : ℕ) (β : ℝ) (k m : ℕ) (n : ℝ) (al : ℕ → ℝ) (T : StageTower (Tb.stepParameters y))
      (S : FreeEnergies.ScoredStageTower T) (top : ℕ),
      1 ≤ q → q ≤ 3 → InScaleWindow (Tb.stepParameters y) β k m n x₀ →
      IsChainResponseCoeff (Tb.stepParameters y) Kr β k al → |al k| ≤ 2 →
      k ≤ top → S.params = Kr → S.FollowsFlow β top → S.coeffs = al →
      IsTowerAtParameters Tb y T β (k + 2 * chainDepth (couplingFlow (Tb.stepParameters y) β k).1) →
      IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn → T.MarksMeasurable →
      ∀ f : Fin (q + 1) → PeriodicLattice.FourTorus (Tb.stepParameters y).side m → ℝ,
        IsSeparatedTestTuple (Tb.stepParameters y) m n v f →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
          (Φ : Ω → MarkedSample (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ m)) (I : Type)
          (_ : Fintype I) (G : Ω → I → imaginaryQuaternions) (A B : Set Ω)
          (κ : Fin (q + 1) → Matrix I I ℝ) (Tc : Matrix I I ℝ) (c : Fin (q + 1) → ℝ),
          Measurable Φ ∧ Measure.map Φ μ = markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m) ∧
          IsLocalQuadraticObservable μ
            (fun i ω => WeightedResponses.response T β al k (2 * (Tb.stepParameters y).side ^ m)
              (testWeight (Tb.stepParameters y).side k m (f i)) (Φ ω))
            G A B κ Tc c (couplingFlow (Tb.stepParameters y) β k).1 n C P Cr xr ∧
          |cyclicTraceSum κ Tc - al k ^ (q + 1) *
              gaussianCumulantLimit (PeriodicLattice.torusSide (Tb.stepParameters y).side m) f| ≤
            C * ((couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2 : ℝ)) + 1 / n)
def localQuadraticEstimateStatement : Prop := HoldsOnParameterFamilies localQuadraticEstimateAt
end YangMills.Construction.ResponseInTheExpansion
end
