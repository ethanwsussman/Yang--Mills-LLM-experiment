import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FourPointCondition
def kernelCycleSum {n : ℕ} [NeZero n] {q : ℕ} (h : Fin (q + 1) → WeightedResponses.PlaquetteWeight n)
    (Tt : TorusFields.TorusPlaquette n → TorusFields.TorusPlaquette n → ℝ) : ℝ :=
  open Classical in
  ∑ s ∈ (Finset.univ : Finset (Equiv.Perm (Fin (q + 1)))).filter (fun s => s 0 = 0),
    ∑ p ∈ Fintype.piFinset (fun _ : Fin (q + 1) =>
        TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite n))),
      (∏ i, h i (p i)) * ∏ i, Tt (p (s i)) (p (s (finRotate (q + 1) i)))
def fineTraceRiemannSumStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (vt A : ℝ), ℓ.Admissible → 0 < vt → vt ≤ 1 → 0 ≤ A → ∃ C : ℝ,
    ∀ (m q : ℕ) (n ε : ℝ)
      (Tt : TorusFields.TorusPlaquette (WeightedResponses.fineSide ℓ.side 0 (2 * ℓ.side ^ m)) →
        TorusFields.TorusPlaquette (WeightedResponses.fineSide ℓ.side 0 (2 * ℓ.side ^ m)) → ℝ),
      (q = 1 ∨ q = 3) → 1 ≤ n → 80 * n ≤ PeriodicLattice.torusSide ℓ.side m → 0 ≤ ε → ε ≤ n ^ (-(4 : ℤ)) →
      (∀ p ∈ TorusFields.plaquettesIn Finset.univ, ∀ p' ∈ TorusFields.plaquettesIn Finset.univ,
        1 ≤ LinearResponse.sqNorm (LinearResponse.plaquetteCentreDisplacement p p') →
        LinearResponse.sqNorm (LinearResponse.plaquetteCentreDisplacement p p') ≤
          (PeriodicLattice.torusSide ℓ.side m / 8) ^ 2 →
        |Tt p p' - LinearResponse.continuumCurvatureKernel (LinearResponse.plaquetteCentreDisplacement p p')
            p.2.1 p.2.2 p'.2.1 p'.2.2| ≤
          A * (LinearResponse.sqNorm (LinearResponse.plaquetteCentreDisplacement p p') ^ (-(5 / 2 : ℝ)) + ε)) →
      ∀ f : Fin (q + 1) → PeriodicLattice.FourTorus ℓ.side m → ℝ, ResponseInTheExpansion.IsSeparatedTestTuple ℓ m n vt f →
        |3 / 2 * kernelCycleSum (fun i => WeightedResponses.testWeight ℓ.side 0 m (f i)) Tt -
            ResponseInTheExpansion.gaussianCumulantLimit (PeriodicLattice.torusSide ℓ.side m) f| ≤
          C * (1 / n + n ^ 4 * ε)
end YangMills.Construction.FourPointCondition
end
