import YangMills.Construction.FamiliesOfLimits.TheTwoListsOfProperties
import YangMills.Construction.FourPointCondition.FourPointFunctionDefs
import YangMills.Construction.ParameterData.ShapesOfAPair
import YangMills.Construction.SystemsWithFiveBounds.TheoremOverASystemWithFiveBounds
import YangMills.Construction.WindowOfTheParameters.FlowOfTheTotalDensities
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensitySystem
structure IsUnitMeshStepParameters (ℓ : TorusLumps.StepParameters) : Prop where
  coupling_eq_one : ℓ.coupling = 1
  side_odd : Odd ℓ.side
  side_ge : 2 ^ 40 ≤ ℓ.side
  one_le_baseDepth : 1 ≤ ℓ.baseDepth
  side_gt : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side
  threshold_mem : ℓ.threshold ∈ Ioo (0 : ℝ) 1
def oneLoopShift (L : ℕ) : ℝ := SystemsWithFiveBounds.asymptoticFreedomSlope * Real.log L
def IsFirstPassageDatum (ℓ : TorusLumps.StepParameters) (Bs g : ℝ) (K : ℕ) (β : ℝ) : Prop :=
  β ∈ SequencePassage.definedPassageWindow (TotalDensityFlow.IsDefinedUpTo ℓ) Bs g (TotalDensityFlow.coupling ℓ) K
def IsFirstPassagePair (ℓ : TorusLumps.StepParameters) (Bs g : ℝ) (K : ℕ+) (β : ℝ) : Prop :=
  IsFirstPassageDatum ℓ Bs g K β
def totalFlowValue (ℓ : TorusLumps.StepParameters) (g Bs : ℝ) (room : ℕ → ℝ) (ζ : ℕ+ → ℝ → ℝ → ℝ) :
    FourPointCondition.CouplingEvaluation where
  IsFirstPassage := IsFirstPassagePair ℓ Bs g
  sides := PeriodicLattice.torusSides ℓ.side
  room := room
  coupling K β d := TotalDensityFlow.coupling ℓ β ((K : ℕ) - RoomFunctions.scaleDepth ℓ.side room d) ^ (-(1 / 2) : ℝ)
  fieldNorm := ζ
structure FlowPassage (ℓ : TorusLumps.StepParameters) (Bs c₅ lam : ℝ) (Nw : ℕ) (g : ℝ) : Prop where
  passes : ∀ β : ℝ, SequencePassage.passageThreshold Bs g ≤ β → ∃ K : ℕ, IsFirstPassageDatum ℓ Bs g K β ∧
    (β - g ^ (-2 : ℤ)) / Bs - 1 ≤ K ∧ (K : ℝ) ≤ 1 + (β - g ^ (-2 : ℤ) - Bs + c₅) / lam ∧
      g ^ (-2 : ℤ) < TotalDensityFlow.coupling ℓ β K
  asymptotically_free : ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ (K : ℕ) (β : ℝ), 1 ≤ K →
    IsFirstPassageDatum ℓ Bs g K β →
    |β / Real.log (1 / PeriodicLattice.meshSize ℓ.side (K : ℤ)) - SystemsWithFiveBounds.asymptoticFreedomSlope| ≤ δ K
  windows_recur : ∀ K' : ℕ, ∃ K : ℕ, K' < K ∧ K ≤ K' + Nw ∧ ∃ β, IsFirstPassageDatum ℓ Bs g K β
def CouplingTie (ℓ : TorusLumps.StepParameters) (Bs CT g : ℝ) : Prop :=
  ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePair ℓ Bs g K β → ∀ m : ℕ+,
    Real.exp (Real.log (SequencePassage.passageThreshold Bs g) ^ 3) ≤ PeriodicLattice.torusSide ℓ.side m →
      ∃ s : ℝ, 0 < s ∧
        PeriodicLattice.torusUrsellFunction ℓ.side m K β
            ![TrajectoryData.firstBump ℓ.side m (SequencePassage.passageThreshold Bs g ^ ((1 : ℝ) / 95)) 0,
              TrajectoryData.translatedBump ℓ.side m (SequencePassage.passageThreshold Bs g ^ ((1 : ℝ) / 95)) 0] = s ∧
        |(TwoPointFunction.amplitudeConstant *
              TestFunctions.inverseEighthKernelTorus
                (TrajectoryData.firstBump ℓ.side m (SequencePassage.passageThreshold Bs g ^ ((1 : ℝ) / 95)) 0)
                (TrajectoryData.translatedBump ℓ.side m (SequencePassage.passageThreshold Bs g ^ ((1 : ℝ) / 95)) 0) / s) ^
                ((1 : ℝ) / 2) /
              TotalDensityFlow.coupling ℓ β K - 1| ≤ CT * TotalDensityFlow.coupling ℓ β K ^ (-(1 / 100 : ℝ)) ∧
        g ^ (-2 : ℤ) < TotalDensityFlow.coupling ℓ β K ∧ TotalDensityFlow.coupling ℓ β K ≤ g ^ (-2 : ℤ) + Bs
def HasTorusSubsequenceLimits (ℓ : TorusLumps.StepParameters) (Bs g : ℝ) : Prop :=
  ∀ (m : ℕ+) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ), (∀ j, IsFirstPassagePair ℓ Bs g (K j) (β j)) → Tendsto K atTop atTop →
    ∃ φ : ℕ+ → ℕ+, StrictMono φ ∧ ∀ n, 2 ≤ n → ∀ X : Fin n → PeriodicLattice.FourTorus ℓ.side m → ℝ,
      (∀ i, TestFunctions.IsC1Torus (X i)) → (∃ d : ℝ, 0 < d ∧ TestFunctions.HasSeparatedSupportsTorus X d) →
        ∃ s : ℂ, Tendsto (fun j => PeriodicLattice.torusUrsellFunction ℓ.side m (K (φ j)) (β (φ j)) X) atTop (𝓝 s)
def HasGrowingTorusSubsequenceLimits (ℓ : TorusLumps.StepParameters) (Bs g : ℝ) : Prop :=
  ∀ (K m : ℕ+ → ℕ+) (β : ℕ+ → ℝ), (∀ j, IsFirstPassagePair ℓ Bs g (K j) (β j)) → Tendsto K atTop atTop →
    Tendsto m atTop atTop →
    ∃ φ : ℕ+ → ℕ+, StrictMono φ ∧ ∀ n, 2 ≤ n → ∀ X : TestSpaces.SepTupleOfCard n, ∃ s : ℂ,
      Tendsto (fun j => PeriodicLattice.torusUrsellFunction ℓ.side (m (φ j)) (K (φ j)) (β (φ j))
        (fun i => TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side (m (φ j))) (X.1 i))) atTop (𝓝 s)
def HasVolumeFirstLimits (ℓ : TorusLumps.StepParameters) (Bs g : ℝ) : Prop :=
  (∃ (Q : SystemsWithFiveBounds.PairSequence ℓ.side (IsFirstPassagePair ℓ Bs g))
      (S : LimitTheorem.CumulantFamily), Q.Defines S) ∧
    ∀ Q : SystemsWithFiveBounds.PairSequence ℓ.side (IsFirstPassagePair ℓ Bs g),
      ∃ (φ : ℕ+ → ℕ+) (hφ : Tendsto φ atTop atTop) (S : LimitTheorem.CumulantFamily), (Q.subseq φ hφ).Defines S
def IsTorusLimit (ℓ : TorusLumps.StepParameters) (Bs g : ℝ) (s : Conventions.StandingParameters)
    (S : AmbientPoints.TupleMapFamily s .torus) : Prop :=
  ∃ (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ), (∀ j, IsFirstPassagePair ℓ Bs g (K j) (β j)) ∧ Tendsto K atTop atTop ∧
    ∀ (n : ℕ) (hn : 2 ≤ n) (X : AmbientPoints.separatedTuples s .torus n),
      Tendsto (fun j => SchwingerFunctions.connectedSchwinger s.L s.m (K j) (β j) X.1) atTop
        (𝓝 ((S n hn X : ℝ) : ℂ))
def IsGrowingTorusLimit (ℓ : TorusLumps.StepParameters) (Bs g : ℝ) (S : LimitTheorem.CumulantFamily) : Prop :=
  ∃ (K m : ℕ+ → ℕ+) (β : ℕ+ → ℝ), (∀ j, IsFirstPassagePair ℓ Bs g (K j) (β j)) ∧ Tendsto K atTop atTop ∧
    Tendsto m atTop atTop ∧ ∀ (n : ℕ) (hn : 2 ≤ n) (X : TestSpaces.SepTupleOfCard n),
      Tendsto (fun j => PeriodicLattice.torusUrsellFunction ℓ.side (m j) (K j) (β j)
        (fun i => TestFunctions.periodize (PeriodicLattice.torusSide ℓ.side (m j)) (X.1 i))) atTop
          (𝓝 ((S n hn X : ℝ) : ℂ))
def IsContinuumLimit (ℓ : TorusLumps.StepParameters) (Bs g : ℝ) (S : LimitTheorem.CumulantFamily) : Prop :=
  IsGrowingTorusLimit ℓ Bs g S ∨
    ∃ Q : SystemsWithFiveBounds.PairSequence ℓ.side (IsFirstPassagePair ℓ Bs g), Q.Defines S
def TorusCumulantBound (ℓ : TorusLumps.StepParameters) (Bs g cV : ℝ) (Cn : ℕ → ℝ → ℝ) : Prop :=
  ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePair ℓ Bs g K β → ∀ m : ℕ+, ∀ n : ℕ, 2 ≤ n → ∀ d : ℝ, 0 < d →
    ∀ f : Fin n → PeriodicLattice.FourTorus ℓ.side m → ℝ,
      (∀ i, TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus (f i)) →
      TestFunctions.HasSeparatedSupportsTorus f d →
        ‖PeriodicLattice.torusUrsellFunction ℓ.side m K β f‖ ≤
          Cn n d * Real.exp (n * cV * PeriodicLattice.torusSide ℓ.side m ^ 4) *
            ∏ i, TestFunctions.sharpNormTorus 1 (f i)
structure LocalCumulantBounds (ℓ : TorusLumps.StepParameters) (Bs g : ℝ)
    (C : SystemsWithFiveBounds.LimitConstants) : Prop where
  onTori : ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePair ℓ Bs g K β → ∀ m : ℕ+, ∀ n : ℕ, 2 ≤ n → ∀ R d : ℝ,
    0 < R → 0 < d → ∀ f : Fin n → PeriodicLattice.FourTorus ℓ.side m → ℝ,
      (∀ i, TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus (f i)) →
      (∀ i, ∃ x, tsupport (f i) ⊆ TestFunctions.closedBallTorus x R) →
      TestFunctions.HasSeparatedSupportsTorus f d →
        ‖PeriodicLattice.torusUrsellFunction ℓ.side m K β f‖ ≤
            C.localBound n d R * ∏ i, TestFunctions.sharpNormTorus 1 (f i) ∧
        ‖PeriodicLattice.torusUrsellFunction ℓ.side m K β f‖ ≤
          C.globalPrefactor d R * C.globalBase R ^ n * (n.factorial : ℝ) ^ C.globalExp *
            ∏ i, TestFunctions.sharpNormTorus 1 (f i)
  inGibbsStates : ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePair ℓ Bs g K β →
    ∀ ν ∈ InfiniteLattice.periodicGibbsSet ℓ.side K β, ∀ n : ℕ, 2 ≤ n →
    ∀ R d : ℝ, 0 < R → 0 < d → ∀ f : Fin n → InfiniteLattice.AmbientSpace → ℝ,
      (∀ i, TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 (f i)) →
      (∀ i, ∃ x, tsupport (f i) ⊆ TestFunctions.closedBallR4 x R) → TestFunctions.HasSeparatedSupportsR4 f d →
        ‖InfiniteLattice.smearedEnergyCumulant ν f‖ ≤ C.localBound n d R * ∏ i, TestFunctions.sharpNormR4 1 (f i) ∧
        ‖InfiniteLattice.smearedEnergyCumulant ν f‖ ≤
          C.globalPrefactor d R * C.globalBase R ^ n * (n.factorial : ℝ) ^ C.globalExp *
            ∏ i, TestFunctions.sharpNormR4 1 (f i)
structure IsTorusLimitFamily (s : Conventions.StandingParameters) (cV : ℝ) (Cn : ℕ → ℝ → ℝ)
    (C : SystemsWithFiveBounds.LimitConstants) (S : AmbientPoints.TupleMapFamily s .torus) : Prop where
  multilinear : ∀ (n : ℕ) (hn : 2 ≤ n), AmbientPoints.IsTupleMultilinear (S n hn)
  symmetric : ∀ (n : ℕ) (hn : 2 ≤ n), AmbientPoints.IsTupleSymmetric (S n hn)
  invariant : FamiliesOfLimits.IsTranslationHypercubicInvariant S
  reflectionPositive : FamiliesOfLimits.TorusReflectionPositive S
  regular : ∀ (n : ℕ) (hn : 2 ≤ n),
    ∃! u : AmbientPoints.testFns (AmbientPoints.pairwiseDistinctTuples s .torus n) → ℂ,
      AmbientPoints.IsDistrib u ∧ FamiliesOfLimits.AgreesOnTensorProducts u (S n hn)
  torusBound : ∀ (n : ℕ) (hn : 2 ≤ n) (d : ℝ), 0 < d → ∀ X : AmbientPoints.separatedTuples s .torus n,
    ENNReal.ofReal d ≤ AmbientPoints.supportGap X.1 →
      |S n hn X| ≤ Cn n d * Real.exp (n * cV * PeriodicLattice.torusSide s.L s.m ^ 4) *
        ∏ i, TestFunctions.sharpNormTorus 1 (X.1 i)
  localBounds : ∀ (n : ℕ) (hn : 2 ≤ n) (R d : ℝ), 0 < R → 0 < d → ∀ X : AmbientPoints.separatedTuples s .torus n,
    (∀ i, ∃ x, tsupport (X.1 i) ⊆ TestFunctions.closedBallTorus x R) →
    ENNReal.ofReal d ≤ AmbientPoints.supportGap X.1 →
      |S n hn X| ≤ C.localBound n d R * ∏ i, TestFunctions.sharpNormTorus 1 (X.1 i) ∧
      |S n hn X| ≤ C.globalPrefactor d R * C.globalBase R ^ n * (n.factorial : ℝ) ^ C.globalExp *
        ∏ i, TestFunctions.sharpNormTorus 1 (X.1 i)
end YangMills.Construction.TotalDensitySystem
end
