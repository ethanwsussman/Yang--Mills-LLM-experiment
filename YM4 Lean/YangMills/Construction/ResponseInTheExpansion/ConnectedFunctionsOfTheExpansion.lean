import YangMills.Construction.ResponseInTheExpansion.KernelOfTheCurvature
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters
abbrev OrderedPlane : Type := {e : Fin 4 × Fin 4 // e.1 < e.2}
def planeKernelMatrix (z : Fin 4 → ℝ) : Matrix OrderedPlane OrderedPlane ℝ := fun P P' =>
  LinearResponse.continuumCurvatureKernel z P.1.1 P.1.2 P'.1.1 P'.1.2
def periodicDisplacement (s : ℝ) (x y : Fin 4 → ℝ) : Fin 4 → ℝ := fun i => LinearResponse.circleSub s (y i) (x i)
def traceAlongCycle (side : ℝ) {q : ℕ} (u : Fin (q + 1) → Fin 4 → ℝ) (σ : Equiv.Perm (Fin (q + 1))) : ℝ :=
  Matrix.trace (List.ofFn fun i : Fin (q + 1) =>
    planeKernelMatrix (periodicDisplacement side (u (σ (finRotate (q + 1) i))) (u (σ i)))).prod
open Classical in
def gaussianCumulantLimit (side : ℝ) {q : ℕ} (f : Fin (q + 1) → TorusMetric.Torus4 side → ℝ) : ℝ :=
  (3 / 2) * ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (q + 1)))).filter (fun σ => σ 0 = 0),
    ∫ u in Set.pi Set.univ (fun _ : Fin (q + 1) => Set.pi Set.univ fun _ : Fin 4 => Set.Ico (0 : ℝ) side),
      (∏ i, f i (TorusMetric.torusProj side (u i))) * traceAlongCycle side u σ
structure IsSeparatedTestTuple (ℓ : StepParameters) (m : ℕ) (n θ : ℝ) {p : ℕ} (f : Fin p → PeriodicLattice.FourTorus ℓ.side m → ℝ) : Prop where
  uniformNorm_eq : ∀ i, TestFunctions.uniformNorm (f i) = 1
  lipschitz : ∀ i, TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus (f i)
  lipConst_le : ∀ i, TestFunctions.lipConstTorus (f i) ≤ 1 / (θ * n)
  separated : TestFunctions.HasSeparatedSupportsTorus f n
  dist_le : ∀ i j, ∀ x ∈ tsupport (f i), ∀ z ∈ tsupport (f j), TestFunctions.euclidDistTorus x z ≤ 10 * n
def connectedFunctionsStatement : Prop :=
  HoldsOnParameterFamilies fun Tb y => ∀ R : ResponseParameters, R.Admissible (Tb.stepParameters y) → ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ∃ C x₀ : ℝ,
    ∀ (q : ℕ) (β : ℝ) (k m : ℕ) (n : ℝ) (α : ℕ → ℝ), 1 ≤ q → q ≤ 3 → InScaleWindow (Tb.stepParameters y) β k m n x₀ →
      IsChainResponseCoeff (Tb.stepParameters y) R β k α →
      ∀ f : Fin (q + 1) → PeriodicLattice.FourTorus (Tb.stepParameters y).side m → ℝ, IsSeparatedTestTuple (Tb.stepParameters y) m n θ f →
        ‖((((couplingFlow (Tb.stepParameters y) β k).1 ^ (q + 1) : ℝ)) : ℂ) *
              connectedCurvature β (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ m))
                (fun i => testWeight (Tb.stepParameters y).side k m (f i)) -
            ((α k ^ (q + 1) * gaussianCumulantLimit (PeriodicLattice.torusSide (Tb.stepParameters y).side m) f : ℝ) : ℂ)‖ ≤
          C * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 100 : ℝ))
end YangMills.Construction.ResponseInTheExpansion
end
