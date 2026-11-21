import YangMills.Construction.InfiniteLattice.GeneratingFunctionsAndConnectedFunctionsOfAMeasureAndOfATorus
import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import YangMills.Construction.RoomFunctions.WitnessDepth
import YangMills.Construction.Torus.LiftsShapeConditionAndCollinearQuadruples
import YangMills.Construction.Parameters.ConstructionParameters
import Mathlib
import YangMills.Construction.WindowOfTheParameters.FirstPassageOfASequenceForm
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction
namespace TwoPointFunction
open YangMills.Construction.ParameterChoice
def amplitudeConstant : ℝ := 3 * ((colorNumber : ℝ) ^ 2 - 1) / Real.pi ^ 4
end TwoPointFunction
end YangMills.Construction
end

noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
def levelMesh (L K k : ℕ) : ℝ := PeriodicLattice.meshSize L ((K : ℤ) - (k : ℤ))
def IsLevelWindow (P : TorusLumps.StepParameters) (x : ℝ) (k : ℕ) (n e : ℝ) : Prop :=
  (2 ^ 12 * (P.side : ℝ) * (TorusLumps.clusterRange x : ℝ) ≤ n ∧ n ≤ x ^ ((1 : ℝ) / 90) ∧ e = 0) ∨
    (k = 0 ∧ 1 ≤ n ∧ n ≤ x ^ ((1 : ℝ) / 90) ∧ e = 1 / n)
def CumulantLawsOnTorus (P : TorusLumps.StepParameters) (vt C x al e β : ℝ) (K m : ℕ) (d : ℝ) : Prop :=
  ∀ q : ℕ, (q = 1 ∨ q = 3) → ∀ f : Fin (q + 1) → PeriodicLattice.FourTorus P.side m → ℝ,
    ResponseInTheExpansion.IsSeparatedTestTuple P m d vt f →
    ‖(((x ^ (q + 1) : ℝ)) : ℂ) * PeriodicLattice.torusUrsellFunction P.side m K β f -
        ((al ^ (q + 1) * ResponseInTheExpansion.gaussianCumulantLimit (PeriodicLattice.torusSide P.side m) f : ℝ) : ℂ)‖ ≤
      C * (x ^ (-(1 / 100 : ℝ)) + e)
def rescale (d : ℝ) (φ : (Fin 4 → ℝ) → ℝ) : (Fin 4 → ℝ) → ℝ := fun x => φ (d⁻¹ • x)
def twoPointPeriodized (L K : ℕ) (β : ℝ) (f h : (Fin 4 → ℝ) → ℝ) (m : ℕ) : ℂ :=
  PeriodicLattice.torusUrsellFunction L m K β
    ![TestFunctions.periodize (PeriodicLattice.torusSide L m) f,
      TestFunctions.periodize (PeriodicLattice.torusSide L m) h]
def twoPointLimsupAtScale (L K : ℕ) (β : ℝ) (sides : Set ℝ) (φ ψ : (Fin 4 → ℝ) → ℝ) (d : ℝ) : EReal :=
  limsup (fun m : ℕ => (((twoPointPeriodized L K β (rescale d φ) (rescale d ψ) m).re : ℝ) : EReal))
    (atTop ⊓ 𝓟 {m : ℕ | PeriodicLattice.torusSide L m ∈ sides})
def gaugeGroupDim : ℝ := (ParameterChoice.colorNumber : ℝ) ^ 2 - 1
def oneLoopCoeff : ℝ := 12 * Real.pi ^ 2 / (11 * (ParameterChoice.colorNumber : ℝ) ^ 2)
def fourPointLowerConst (ϑ : ℝ) : ℝ :=
  32 / 225 * Real.pi ^ (-8 : ℤ) * (25 / 4 : ℝ) ^ (-16 : ℤ) *
    min ϑ (TorusMeasure.omega4 * (16 : ℝ) ^ (-4 : ℤ)) ^ 4
def fourPointUpperConst : ℝ := 64 / 3 * (16 : ℝ) ^ (-16 : ℤ)
structure CouplingEvaluation where
  IsFirstPassage : ℕ+ → ℝ → Prop
  sides : Set ℝ
  room : ℕ → ℝ
  coupling : ℕ+ → ℝ → ℝ → ℝ
  fieldNorm : ℕ+ → ℝ → ℝ → ℝ
namespace CouplingEvaluation
variable (R : CouplingEvaluation) (L : ℕ)
def depthAt (d : ℝ) : ℕ := RoomFunctions.scaleDepth L R.room d
def IsDeepEnough (K : ℕ+) (n : ℕ) (d : ℝ) : Prop := (n : ℤ) ≤ ((K : ℕ) : ℤ) - (R.depthAt L d : ℤ)
end CouplingEvaluation
structure EvaluationLaws (R : CouplingEvaluation) (L : ℕ) (ϑ lam Ca d₀ : ℝ) (n₀ : ℕ) : Prop where
  room : RoomFunctions.IsSubexpGrowth R.room
  sides_unbounded : ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧ PeriodicLattice.torusSide L m ∈ R.sides
  lam_pos : 0 < lam
  d₀_mem : d₀ ∈ Ioo (0 : ℝ) 1
  one_le_n₀ : 1 ≤ n₀
  cutoff_le : ∀ (K : ℕ+) (β : ℝ), R.IsFirstPassage K β → ((K : ℕ) : ℝ) ≤ (β + Ca) / lam
  coupling_pos : ∀ (K : ℕ+) (β : ℝ), R.IsFirstPassage K β → ∀ d ∈ Ioc (0 : ℝ) d₀, R.IsDeepEnough L K n₀ d →
    0 < R.coupling K β d
  fieldNorm_mem : ∀ (K : ℕ+) (β : ℝ), R.IsFirstPassage K β → ∀ d ∈ Ioc (0 : ℝ) d₀, R.IsDeepEnough L K n₀ d →
    R.fieldNorm K β d ∈ Icc (2 / 3 : ℝ) (4 / 3)
  twoPoint : ∀ (K : ℕ+) (β : ℝ), R.IsFirstPassage K β → ∀ m : ℕ, PeriodicLattice.torusSide L m ∈ R.sides →
    ∀ d ∈ Ioc (0 : ℝ) d₀, R.IsDeepEnough L K n₀ d →
      ∀ f h : PeriodicLattice.FourTorus L m → ℝ, (f, h) ∈ TestFunctions.separatedPairsFourTorus L m d ϑ →
        ∃ ε : ℝ, |ε| ≤ 1 / 2 ∧
        PeriodicLattice.torusUrsellFunction L m K β ![f, h] =
          ((R.fieldNorm K β d ^ 2 * TwoPointFunction.amplitudeConstant * R.coupling K β d ^ 4 *
            TestFunctions.inverseEighthKernelTorus (ℓ := PeriodicLattice.torusSide L m) f h * (1 + ε) : ℝ) : ℂ)
  log_mem : ∀ (K : ℕ+) (β : ℝ), R.IsFirstPassage K β → ∀ d ∈ Ioc (0 : ℝ) d₀, R.IsDeepEnough L K n₀ d →
    R.coupling K β d ^ 2 * Real.log (1 / d) ∈ Icc (2 / 3 * oneLoopCoeff) (4 / 3 * oneLoopCoeff)
structure SharpEvaluationLaws (R : CouplingEvaluation) (L : ℕ) (ϑ d₀ : ℝ) (n₀ : ℕ) (ηBar : ℝ → ℝ)
    (εBar : ℕ → ℝ → ℝ) : Prop where
  ηBar_mono : MonotoneOn ηBar (Ioc 0 d₀)
  εBar_mono : ∀ m, MonotoneOn (εBar m) (Ioc 0 d₀)
  ηBar_mem : ∀ d ∈ Ioc (0 : ℝ) d₀, ηBar d ∈ Icc (0 : ℝ) (1 / 3)
  εBar_mem : ∀ m, ∀ d ∈ Ioc (0 : ℝ) d₀, εBar m d ∈ Icc (0 : ℝ) (1 / 2)
  ηBar_tendsto : Tendsto ηBar (nhdsWithin 0 (Ioi 0)) (nhds 0)
  εBar_tendsto : ∀ m, Tendsto (εBar m) (nhdsWithin 0 (Ioi 0)) (nhds 0)
  twoPoint : ∀ (K : ℕ+) (β : ℝ), R.IsFirstPassage K β → ∀ m : ℕ, PeriodicLattice.torusSide L m ∈ R.sides →
    ∀ d ∈ Ioc (0 : ℝ) d₀, R.IsDeepEnough L K n₀ d →
      ∀ f h : PeriodicLattice.FourTorus L m → ℝ, (f, h) ∈ TestFunctions.separatedPairsFourTorus L m d ϑ →
        ∃ ε : ℝ, |ε| ≤ εBar m d ∧
        PeriodicLattice.torusUrsellFunction L m K β ![f, h] =
          ((R.fieldNorm K β d ^ 2 * TwoPointFunction.amplitudeConstant * R.coupling K β d ^ 4 *
            TestFunctions.inverseEighthKernelTorus (ℓ := PeriodicLattice.torusSide L m) f h * (1 + ε) : ℝ) : ℂ)
  fieldNorm_le : ∀ (K : ℕ+) (β : ℝ), R.IsFirstPassage K β → ∀ d ∈ Ioc (0 : ℝ) d₀, R.IsDeepEnough L K n₀ d →
    |R.fieldNorm K β d - 1| ≤ ηBar d
  log_le : ∀ (K : ℕ+) (β : ℝ), R.IsFirstPassage K β → ∀ d ∈ Ioc (0 : ℝ) d₀, R.IsDeepEnough L K n₀ d →
    |R.coupling K β d ^ 2 * Real.log (1 / d) / oneLoopCoeff - 1| ≤ ηBar d
def flowProfile (P : TorusLumps.StepParameters) (g Bs : ℝ) (room : ℕ → ℝ) (al : ℝ → ℕ → ℝ) :
    CouplingEvaluation where
  IsFirstPassage K β := β ∈ SequencePassage.passageWindow Bs g (fun b k => (TorusLumps.couplingFlow P b k).1) K
  sides := PeriodicLattice.torusSides P.side
  room := room
  coupling K β d :=
    (TorusLumps.couplingFlow P β ((K : ℕ) - RoomFunctions.scaleDepth P.side room d)).1 ^ (-(1 / 2) : ℝ)
  fieldNorm K β d := al β ((K : ℕ) - RoomFunctions.scaleDepth P.side room d)
def FourPointBounds {Y : Type*} (c C g : ℝ) (f : Fin 4 → Y → ℝ) (r : ℝ) : Prop :=
  c * gaugeGroupDim * g ^ 8 * ∏ i, TestFunctions.uniformNorm (f i) ≤ r ∧
    r ≤ C * gaugeGroupDim * g ^ 8 * ∏ i, TestFunctions.uniformNorm (f i)
def FourPointConditionHolds (R : CouplingEvaluation) (L : ℕ) (ϑ d₄ : ℝ) (n₄ : ℕ) : Prop :=
  ∀ (s : Conventions.StandingParameters) (β : ℝ), s.L = L → R.IsFirstPassage s.K β →
    ∀ d ∈ Ioc (0 : ℝ) d₄, R.IsDeepEnough L s.K n₄ d →
    ∀ f ∈ QuadrupleClasses.collinearQuadsTorus s d ϑ, ∃ r : ℝ,
      PeriodicLattice.torusUrsellFunction s.L s.m s.K β f = r ∧ 0 < r ∧
      FourPointBounds (fourPointLowerConst ϑ) fourPointUpperConst (R.coupling s.K β d) f r
end YangMills.Construction.FourPointCondition
end
