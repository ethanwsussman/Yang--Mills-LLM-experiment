import YangMills.Construction.FourPointCondition.ConditionInTheLimits
import YangMills.Construction.LawByMomentsOfTheFlow.CyclicFormulaOfTheLaw
import YangMills.Construction.TotalDensitiesGiveASystem.TopStatementDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
def SatisfiesTwoPointLawWithError (main : ℝ) (ηBar εBar : ℝ → ℝ) (d value : ℝ) : Prop :=
  ∃ η : ℝ, value = main * (1 + η) ∧ (1 - εBar d) * (1 - ηBar d) ^ 4 ≤ 1 + η ∧
    1 + η ≤ (1 + εBar d) * (1 + ηBar d) ^ 4
def twoPointMainTermTorus {side : ℝ} (d : ℝ) (f h : TorusMetric.Torus4 side → ℝ) : ℝ :=
  SystemsWithFiveBounds.twoPointPrefactor * TestFunctions.inverseEighthKernelTorus f h / Real.log (1 / d) ^ 2
structure TwoPointLawAtShape (p : TorusLumps.StepParameters) (Bs c₅ lam g vt : ℝ) (room : ℕ → ℝ) (d₀ : ℝ)
    (ηBar εBar : ℝ → ℝ) (ζ : ℕ+ → ℝ → ℝ → ℝ) (K₀ : ℝ → ℕ) : Prop where
  cutoff_mem : d₀ ∈ Ioc (0 : ℝ) (1 / 40)
  depth_bound : c₅ + 1 ≤ lam * RoomFunctions.scaleDepth p.side room d₀
  sharp_on_tori : FourPointCondition.SharpEvaluationLaws (TotalDensitySystem.totalFlowValue p g Bs room ζ) p.side vt d₀ 1 ηBar
    fun _ => εBar
  coupling_envelope : ∀ (K : ℕ+) (β : ℝ), TotalDensitySystem.IsFirstPassagePair p Bs g K β → ∀ d ∈ Ioc (0 : ℝ) d₀,
    (TotalDensitySystem.totalFlowValue p g Bs room ζ).IsDeepEnough p.side K 1 d →
      g ^ (-2 : ℤ) + lam * RoomFunctions.scaleDepth p.side room d - c₅ ≤
          TotalDensityFlow.coupling p β ((K : ℕ) - RoomFunctions.scaleDepth p.side room d) ∧
        TotalDensityFlow.coupling p β ((K : ℕ) - RoomFunctions.scaleDepth p.side room d) ≤
          g ^ (-2 : ℤ) + Bs * ((RoomFunctions.scaleDepth p.side room d : ℝ) + 1)
  torus_states : ∀ (K : ℕ+) (β : ℝ), TotalDensitySystem.IsFirstPassagePair p Bs g K β →
    ∀ ν ∈ InfiniteLattice.torusLimitSet p.side K β,
    ∀ d ∈ Ioc (0 : ℝ) d₀, (TotalDensitySystem.totalFlowValue p g Bs room ζ).IsDeepEnough p.side K 1 d →
      ∀ f h : InfiniteLattice.AmbientSpace → ℝ, (f, h) ∈ TestFunctions.separatedPairsR4 d vt →
        ∃ ε : ℝ, |ε| ≤ εBar d ∧
        InfiniteLattice.smearedEnergyCumulant ν ![f, h] =
          ((ζ K β d ^ 2 * TwoPointFunction.amplitudeConstant *
            (TotalDensitySystem.totalFlowValue p g Bs room ζ).coupling K β d ^ 4 *
            TestFunctions.inverseEighthKernel f h * (1 + ε) : ℝ) : ℂ)
  periodic_states : ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ (K : ℕ+) (β : ℝ), TotalDensitySystem.IsFirstPassagePair p Bs g K β →
    K₀ d ≤ (K : ℕ) →
    ∀ ν ∈ InfiniteLattice.periodicGibbsSet p.side K β, ∀ f h : InfiniteLattice.AmbientSpace → ℝ,
      (f, h) ∈ TestFunctions.separatedPairsR4 d vt →
      ∃ t : ℝ, InfiniteLattice.smearedEnergyCumulant ν ![f, h] = (t : ℂ) ∧
        SystemsWithFiveBounds.SatisfiesTwoPointLaw ηBar d t f h
structure TwoPointLawInLimits (p : TorusLumps.StepParameters) (Bs g vt d₀ : ℝ) (ηBar εBar : ℝ → ℝ) : Prop where
  on_torus : ∀ (s : Conventions.StandingParameters) (S : AmbientPoints.TupleMapFamily s .torus), s.L = p.side →
    TotalDensitySystem.IsTorusLimit p Bs g s S → ∀ d ∈ Ioc (0 : ℝ) d₀,
    ∀ X : AmbientPoints.separatedTuples s .torus 2,
      (X.1 0, X.1 1) ∈ TestFunctions.separatedPairsFourTorus s.L s.m d vt →
        SatisfiesTwoPointLawWithError (twoPointMainTermTorus d (X.1 0) (X.1 1)) ηBar εBar d (S 2 le_rfl X)
  on_space : ∀ S : LimitTheorem.CumulantFamily, TotalDensitySystem.IsContinuumLimit p Bs g S →
    ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ X : TestSpaces.SepTupleOfCard 2,
    (X.1 0, X.1 1) ∈ TestFunctions.separatedPairsR4 d vt →
      SatisfiesTwoPointLawWithError (SystemsWithFiveBounds.twoPointMainTerm d (X.1 0) (X.1 1)) ηBar εBar d
        (S 2 le_rfl X)
structure FourPointLawInLimits (p : TorusLumps.StepParameters) (Bs g vt d₄ : ℝ) : Prop where
  on_torus : ∀ (s : Conventions.StandingParameters) (S : AmbientPoints.TupleMapFamily s .torus), s.L = p.side →
    TotalDensitySystem.IsTorusLimit p Bs g s S → ∀ d ∈ Ioc (0 : ℝ) d₄,
    ∀ X : AmbientPoints.separatedTuples s .torus 4,
      X.1 ∈ QuadrupleClasses.collinearQuadsTorus s d vt →
        FourPointCondition.IsInLimitInterval vt d X.1 (S 4 (by norm_num) X)
  on_space : ∀ S : LimitTheorem.CumulantFamily, TotalDensitySystem.IsContinuumLimit p Bs g S →
    ∀ d ∈ Ioc (0 : ℝ) d₄, ∀ X : TestSpaces.SepTupleOfCard 4,
    X.1 ∈ QuadrupleClasses.collinearQuadsR4 d vt →
      FourPointCondition.IsInLimitInterval vt d X.1 (S 4 (by norm_num) X)
def dyadicRescale {n : ℕ} (i : ℕ) (f : Fin n → (Fin 4 → ℝ) → ℝ) : Fin n → (Fin 4 → ℝ) → ℝ :=
  fun k x => f k ((2 : ℝ) ^ i • x)
def shortDistanceLimit {n : ℕ} [NeZero n] (f : Fin n → (Fin 4 → ℝ) → ℝ) : ℝ :=
  CyclicFormula.cyclicMomentFormula n fun k x => f k (WithLp.ofLp x)
structure ShortDistanceAsymptotics (S : LimitTheorem.CumulantFamily) : Prop where
  at_limit : ∀ (n : ℕ) [NeZero n] (hn : 2 ≤ n), n ≤ 8 →
    ∀ (X : TestSpaces.SepTupleOfCard n) (Y : ℕ → TestSpaces.SepTupleOfCard n),
    (∀ i, (Y i).1 = dyadicRescale i X.1) →
      Tendsto (fun i : ℕ => (Real.log ((2 : ℝ) ^ i) / FourPointCondition.oneLoopCoeff) ^ n * S n hn (Y i)) atTop
        (𝓝 (shortDistanceLimit X.1))
  ae_components : ∀ A : SeparatedTuples.DecompositionData, A.IsCanonical (LimitTheorem.centredOf S) →
    ∀ (n : ℕ) [NeZero n], 2 ≤ n → n ≤ 8 →
    ∀ (X : TestSpaces.SepTupleOfCard n) (Y : ℕ → TestSpaces.SepTupleOfCard n),
      (∀ i, (Y i).1 = dyadicRescale i X.1) → ∀ᵐ ξ ∂A.law,
        Tendsto (fun i : ℕ => (Real.log ((2 : ℝ) ^ i) / FourPointCondition.oneLoopCoeff) ^ n *
          LimitTheorem.connectedFn (A.comp ξ) (Y i)) atTop (𝓝 (shortDistanceLimit X.1))
  gaussian_components_small : ∀ A : SeparatedTuples.DecompositionData, A.IsCanonical (LimitTheorem.centredOf S) →
    IsClosed {ξ : A.space | ∀ (n : ℕ), 3 ≤ n → ∀ X : TestSpaces.SepTupleOfCard n,
        LimitTheorem.connectedFn (A.comp ξ) X = 0} ∧
      A.law {ξ : A.space | ∀ (n : ℕ), 3 ≤ n → ∀ X : TestSpaces.SepTupleOfCard n,
        LimitTheorem.connectedFn (A.comp ξ) X = 0} = 0 ∧
      interior {ξ : A.space | ∀ (n : ℕ), 3 ≤ n → ∀ X : TestSpaces.SepTupleOfCard n,
        LimitTheorem.connectedFn (A.comp ξ) X = 0} = ∅
structure ShortDistanceLimitNonGaussian (vt : ℝ) : Prop where
  odd_vanish : ∀ (n : ℕ) [NeZero n], 2 ≤ n → Odd n → n ≤ 8 → ∀ X : TestSpaces.SepTupleOfCard n,
    shortDistanceLimit X.1 = 0
  four_pos : ∀ X : TestSpaces.SepTupleOfCard 4, X.1 ∈ QuadrupleClasses.collinearQuadsR4 1 vt →
    0 < shortDistanceLimit X.1
end YangMills.Construction.TotalDensities
end
