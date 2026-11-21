import YangMills.Construction.ResponseInTheExpansion.LevelsBelowATuple
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory ProbabilityTheory
namespace YangMills.BranchHot
open Construction RenormalizationStepParameters WeightedResponses ResponseInTheExpansion
open FreeEnergies TorusLumps

def StageDecayAt (Tb : ParameterAssignment) (Kr : ResponseParameters) (y : ℝ) : Prop :=
  let p := Tb.stepParameters y
  ∀ (ell A vt : ℝ), 8 ≤ ell → 1 ≤ A → 0 < vt → ∀ ε > (0:ℝ),
    ∀ᶠ q : ℕ in atTop, ∀ (T : StageTower p) (S : ScoredStageTower T) (β : ℝ) (k m : ℕ),
      S.params = Kr → S.FollowsFlow β k → CouplingsAboveFloor p β k →
      ((2*p.side^m:ℕ):ℝ) = ell*q → 2*p.side ∣ 2*p.side^m →
      (q:ℝ)^92 ≤ flowCouplings p β k → flowCouplings p β k ≤ A*(q:ℝ)^92 →
      ∀ f : Fin 2 → PeriodicLattice.FourTorus p.side m → ℝ,
      IsSeparatedTestTuple p m ((6/5:ℝ)*q) vt f →
      |cov[curvatureObservable (testWeight p.side k m (f 0)),
           curvatureObservable (testWeight p.side k m (f 1));
           wilsonLaw β (fineSide p.side k (2*p.side^m))]| ≤ ε

end YangMills.BranchHot
end
