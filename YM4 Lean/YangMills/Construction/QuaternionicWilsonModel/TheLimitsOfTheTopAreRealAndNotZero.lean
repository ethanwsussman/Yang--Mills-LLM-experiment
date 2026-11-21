import YangMills.Construction.QuaternionicWilsonModel.TheClassesHaveMembersAtEveryScale
import YangMills.Construction.TotalDensitiesGiveASystem.ConditionsOfTheMainStatement
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.QuaternionicWilsonModel.TopLimitsRealNonzero
def OneTorusValuesReal (p : TorusLumps.StepParameters) (Bs g : ℝ) : Prop :=
  ∀ (m : ℕ+) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ), (∀ j, TotalDensitySystem.IsFirstPassagePair p Bs g (K j) (β j)) →
    Tendsto K atTop atTop →
    ∀ n, 2 ≤ n → ∀ X : Fin n → PeriodicLattice.FourTorus p.side m → ℝ,
      (∀ i, TestFunctions.IsC1Torus (X i)) → (∃ d : ℝ, 0 < d ∧ TestFunctions.HasSeparatedSupportsTorus X d) →
        ∀ z : ℂ,
          Tendsto (fun j => PeriodicLattice.torusUrsellFunction p.side m (K j) (β j) X) atTop (𝓝 z) → z.im = 0
def GrowingToriValuesReal (p : TorusLumps.StepParameters) (Bs g : ℝ) : Prop :=
  ∀ (K m : ℕ+ → ℕ+) (β : ℕ+ → ℝ), (∀ j, TotalDensitySystem.IsFirstPassagePair p Bs g (K j) (β j)) →
    Tendsto K atTop atTop → Tendsto m atTop atTop →
    ∀ n, 2 ≤ n → ∀ (X : TestSpaces.SepTupleOfCard n) (z : ℂ),
      Tendsto (fun j => PeriodicLattice.torusUrsellFunction p.side (m j) (K j) (β j)
        (fun i => TestFunctions.periodize (PeriodicLattice.torusSide p.side (m j)) (X.1 i))) atTop (𝓝 z) →
        z.im = 0
def ExistsSubseqFamilyOnTorus (p : TorusLumps.StepParameters) (Bs g : ℝ) : Prop :=
  ∀ s : Conventions.StandingParameters, s.L = p.side →
    ∀ (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ), (∀ j, TotalDensitySystem.IsFirstPassagePair p Bs g (K j) (β j)) →
      Tendsto K atTop atTop →
      ∃ (φ : ℕ+ → ℕ+) (S : AmbientPoints.TupleMapFamily s .torus), StrictMono φ ∧
        TotalDensitySystem.IsTorusLimit p Bs g s S ∧
        ∀ (n : ℕ) (hn : 2 ≤ n) (X : AmbientPoints.separatedTuples s .torus n),
          Tendsto (fun j => SchwingerFunctions.connectedSchwinger s.L s.m (K (φ j)) (β (φ j)) X.1) atTop
            (𝓝 ((S n hn X : ℝ) : ℂ))
def ExistsSubseqFamilyAlongTori (p : TorusLumps.StepParameters) (Bs g : ℝ) : Prop :=
  ∀ (K m : ℕ+ → ℕ+) (β : ℕ+ → ℝ), (∀ j, TotalDensitySystem.IsFirstPassagePair p Bs g (K j) (β j)) →
    Tendsto K atTop atTop → Tendsto m atTop atTop →
    ∃ (φ : ℕ+ → ℕ+) (S : LimitTheorem.CumulantFamily), StrictMono φ ∧
      TotalDensitySystem.IsGrowingTorusLimit p Bs g S ∧
      ∀ (n : ℕ) (hn : 2 ≤ n) (X : TestSpaces.SepTupleOfCard n),
        Tendsto (fun j => PeriodicLattice.torusUrsellFunction p.side (m (φ j)) (K (φ j)) (β (φ j))
          (fun i => TestFunctions.periodize (PeriodicLattice.torusSide p.side (m (φ j))) (X.1 i))) atTop
          (𝓝 ((S n hn X : ℝ) : ℂ))
structure LimitsRealAt (p : TorusLumps.StepParameters) (Bs g : ℝ) : Prop where
  real_onTorus : OneTorusValuesReal p Bs g
  real_alongTori : GrowingToriValuesReal p Bs g
  family_onTorus : ExistsSubseqFamilyOnTorus p Bs g
  family_alongTori : ExistsSubseqFamilyAlongTori p Bs g
  exists_params : ∀ m : ℕ+, ∃ s : Conventions.StandingParameters, s.L = p.side ∧ s.m = m
  exists_torusLimit : ∀ s : Conventions.StandingParameters, s.L = p.side →
    ∃ S, TotalDensitySystem.IsTorusLimit p Bs g s S
  exists_growingTorusLimit : ∃ S, TotalDensitySystem.IsGrowingTorusLimit p Bs g S
  exists_volumeFirstLimit : ∃ (Q : SystemsWithFiveBounds.PairSequence p.side
      (TotalDensitySystem.IsFirstPassagePair p Bs g)) (S : LimitTheorem.CumulantFamily), Q.Defines S
  volumeFirst_isGrowingTorusLimit : ∀ (Q : SystemsWithFiveBounds.PairSequence p.side
      (TotalDensitySystem.IsFirstPassagePair p Bs g)) (S : LimitTheorem.CumulantFamily),
    Q.Defines S → TotalDensitySystem.IsGrowingTorusLimit p Bs g S
  exists_continuumLimit : ∃ S, TotalDensitySystem.IsContinuumLimit p Bs g S
structure ValuesPositiveAt (p : TorusLumps.StepParameters) (Bs g ϑ d : ℝ) : Prop where
  nonempty_space : TopAux.NonemptyTestClasses.NonemptyOnEuclideanSpace d ϑ
  nonempty_torus : ∀ s : Conventions.StandingParameters, s.L = p.side →
    TopAux.NonemptyTestClasses.NonemptyOnTorus s d ϑ
  pair_pos_space : ∀ S : LimitTheorem.CumulantFamily, TotalDensitySystem.IsContinuumLimit p Bs g S →
    ∀ X : TestSpaces.SepTupleOfCard 2,
      (X.1 0, X.1 1) ∈ TestFunctions.separatedPairsR4 d ϑ → 0 < S 2 le_rfl X
  quad_pos_space : ∀ S : LimitTheorem.CumulantFamily, TotalDensitySystem.IsContinuumLimit p Bs g S →
    ∀ X : TestSpaces.SepTupleOfCard 4,
      X.1 ∈ QuadrupleClasses.collinearQuadsR4 d ϑ → 0 < S 4 (by norm_num) X
  pair_pos_torus : ∀ (s : Conventions.StandingParameters) (S : AmbientPoints.TupleMapFamily s .torus),
    s.L = p.side → TotalDensitySystem.IsTorusLimit p Bs g s S →
    ∀ X : AmbientPoints.separatedTuples s .torus 2,
      (X.1 0, X.1 1) ∈ TestFunctions.separatedPairsFourTorus s.L s.m d ϑ → 0 < S 2 le_rfl X
  quad_pos_torus : ∀ (s : Conventions.StandingParameters) (S : AmbientPoints.TupleMapFamily s .torus),
    s.L = p.side → TotalDensitySystem.IsTorusLimit p Bs g s S →
    ∀ X : AmbientPoints.separatedTuples s .torus 4,
      X.1 ∈ QuadrupleClasses.collinearQuadsTorus s d ϑ → 0 < S 4 (by norm_num) X
def MainStatement : Prop :=
  ∃ ϑ₀ ∈ Ioc (0 : ℝ) 1, ∃ J Lstar : ℕ, 1 ≤ J ∧ ∀ L : ℕ, Odd L → Lstar ≤ L →
    ∃ (p : TorusLumps.StepParameters) (Bs c₅ γ : ℝ) (Nw : ℕ) (CT : ℝ),
      p.side = L ∧ p.baseDepth = J ∧ TotalDensitySystem.IsUnitMeshStepParameters p ∧ 2 ≤ Bs ∧ 0 ≤ c₅ ∧
        γ ∈ Ioo (0 : ℝ) 1 ∧ 0 < CT ∧ 1 ≤ Nw ∧
        ∀ g ∈ Ioc 0 γ,
          TotalDensitySystem.CouplingConditions p Bs c₅ (3 / 4 * TotalDensitySystem.oneLoopShift L) Nw CT g ∧
            LimitsRealAt p Bs g ∧
            ∀ ϑ ∈ Ioc (0 : ℝ) ϑ₀, ∃ d₁ ∈ Ioc (0 : ℝ) (1 / 40), ∀ d ∈ Ioc (0 : ℝ) d₁,
              ValuesPositiveAt p Bs g ϑ d
end YangMills.Construction.QuaternionicWilsonModel.TopLimitsRealNonzero
end
