import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import YangMills.Construction.ResponseInTheExpansion.CumulantsOfQuadraticForms
import YangMills.Construction.ResponseInTheExpansion.LocalChainAboveALevel
import YangMills.Construction.ResponseInTheExpansion.SeveralSupportsInOneStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open Classical
open MeasureTheory
def responseKernel {N : ℕ} [NeZero N] (A : Finset (YangMills.Construction.TorusFields.TorusSite N))
    (mean : YangMills.Construction.TorusFields.TorusSite N → ℝ) (coeff : ℝ)
    (ka kr : YangMills.Construction.TorusFields.TorusSite N →
      YangMills.Construction.TorusFields.TorusPlaquette N →
      YangMills.Construction.TorusFields.TorusPlaquette N → ℝ) :
    Matrix (YangMills.Construction.WeightedResponses.OrientedPlaquette N)
      (YangMills.Construction.WeightedResponses.OrientedPlaquette N) ℝ :=
  fun p p' => ∑ z ∈ A, (mean z * coeff * ka z p.1 p'.1 + kr z p.1 p'.1)
def responseKernelTracesAt (P : YangMills.Construction.TorusLumps.StepParameters) : Prop :=
  ∀ vt del c₀ C₀ : ℝ, 0 < vt → vt ≤ 1 → 0 < del → 0 < c₀ → ∃ C x₀ : ℝ,
    ∀ (q k m : ℕ) (x nn coeff : ℝ)
      (f : Fin (q + 1) → YangMills.Construction.PeriodicLattice.FourTorus P.side m → ℝ)
      (ka : YangMills.Construction.TorusFields.TorusSite (2 * P.side ^ m) →
        YangMills.Construction.TorusFields.TorusPlaquette (2 * P.side ^ m) →
        YangMills.Construction.TorusFields.TorusPlaquette (2 * P.side ^ m) → ℝ)
      (kr : Fin (q + 1) → YangMills.Construction.TorusFields.TorusSite (2 * P.side ^ m) →
        YangMills.Construction.TorusFields.TorusPlaquette (2 * P.side ^ m) →
        YangMills.Construction.TorusFields.TorusPlaquette (2 * P.side ^ m) → ℝ)
      (Tc : Matrix (YangMills.Construction.WeightedResponses.OrientedPlaquette (2 * P.side ^ m))
        (YangMills.Construction.WeightedResponses.OrientedPlaquette (2 * P.side ^ m)) ℝ),
      1 ≤ q → q ≤ 3 → x₀ ≤ x →
      2 ^ 12 * (P.side : ℝ) * (YangMills.Construction.TorusLumps.clusterRange x : ℝ) ≤ nn →
      nn ≤ x ^ ((1 : ℝ) / 90) →
      Real.exp (Real.log x ^ 3) ≤ 2 * (P.side : ℝ) ^ m → |coeff| ≤ 2 → IsSeparatedTestTuple P m nn vt f →
      IsLocalKernel (logCubeScale x) del C₀ ka →
      IsNormalizedShareForm (Real.exp (-(c₀ * logCubeScale x))) ka →
      (∀ i, IsLocalKernel (logCubeScale x) del (C₀ * (x ^ (-(1 / 2 : ℝ)) + 1 / (vt * nn))) (kr i)) →
      (∀ p p' : YangMills.Construction.WeightedResponses.OrientedPlaquette (2 * P.side ^ m),
        1 ≤ YangMills.Construction.LinearResponse.sqNorm
          (YangMills.Construction.LinearResponse.plaquetteCentreDisplacement p.1 p'.1) →
        YangMills.Construction.LinearResponse.sqNorm
          (YangMills.Construction.LinearResponse.plaquetteCentreDisplacement p.1 p'.1) ≤
          ((2 * (P.side : ℝ) ^ m) / 8) ^ 2 →
        |Tc p p' - YangMills.Construction.LinearResponse.continuumCurvatureKernel
            (YangMills.Construction.LinearResponse.plaquetteCentreDisplacement p.1 p'.1)
            p.1.2.1 p.1.2.2 p'.1.2.1 p'.1.2.2| ≤
          C₀ * (YangMills.Construction.LinearResponse.sqNorm
              (YangMills.Construction.LinearResponse.plaquetteCentreDisplacement p.1 p'.1) ^ (-(5 / 2 : ℝ)) +
            (2 * (P.side : ℝ) ^ m) ^ (-(4 : ℤ))) + x ^ (-(50 : ℝ))) →
      |cyclicTraceSum (fun i => responseKernel
            (weightSupportSites P.side k (2 * P.side ^ m)
              (YangMills.Construction.WeightedResponses.testWeight P.side k m (f i)))
            (fun z => YangMills.Construction.WeightedResponses.blockMean P.side k (2 * P.side ^ m) z
              (YangMills.Construction.WeightedResponses.testWeight P.side k m (f i))) coeff ka (kr i)) Tc -
          coeff ^ (q + 1) * gaussianCumulantLimit
            (YangMills.Construction.PeriodicLattice.torusSide P.side m) f| ≤
        C * (x ^ (-(1 / 2 : ℝ)) + 1 / nn)
def responseKernelTracesStatement : Prop :=
  HoldsOnParameterFamilies fun Tb y => responseKernelTracesAt (Tb.stepParameters y)
end YangMills.Construction.ResponseInTheExpansion
end
