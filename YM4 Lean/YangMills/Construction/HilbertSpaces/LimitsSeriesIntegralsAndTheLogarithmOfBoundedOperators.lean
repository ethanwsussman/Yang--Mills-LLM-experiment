import YangMills.Construction.Conventions.OneLoopLawDefs
import YangMills.Construction.Towers.SquareSummableFunctionsOnTheUnitLattice
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.OneLoopNotation YangMills.Construction.Tower.UnitLatticeL2
noncomputable section
namespace YangMills.Construction.OperatorCalculus
section Definitions
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def addScalar (T : BddOp H) (s : ℝ) : BddOp H := T + scalarOp (s : ℂ)
def inverseOp (X : BddOp H) : BddOp H :=
  Classical.epsilon fun B => IsTwoSidedInverse X B
def IsRiemannSumWithMeshLE (T : ℝ → BddOp H) (a b δ : ℝ) (R : BddOp H) :
    Prop :=
  ∃ P : MarkedPartition a b, 1 ≤ P.card ∧ StrictMono P.node ∧
    (∀ i : Fin P.card, P.node i.succ - P.node i.castSucc ≤ δ) ∧ R = P.sum T
def RiemannSumsTendsto (T : ℝ → BddOp H) (a b : ℝ) (X : BddOp H) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ R, IsRiemannSumWithMeshLE T a b δ R → ‖R - X‖ ≤ ε
def NormContinuousOn (T : ℝ → BddOp H) (a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ t' ∈ Icc a b, |t - t'| ≤ δ → ‖T t - T t'‖ ≤ ε
def UniformlyNormContinuousOn (T : ℝ → BddOp H) (a b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ t ∈ Icc a b, ∀ t' ∈ Icc a b, |t - t'| ≤ δ → ‖T t - T t'‖ ≤ ε
def opIntegral (T : ℝ → BddOp H) (a b : ℝ) : BddOp H :=
  Classical.epsilon fun X => RiemannSumsTendsto T a b X
def resolventDiff (S : BddOp H) (t : ℝ) : BddOp H :=
  scalarOp (((1 + t)⁻¹ : ℝ) : ℂ) - inverseOp (addScalar S t)
def IsLogOf (S X : BddOp H) : Prop :=
  TendstoInOpNorm atTop (fun b : ℝ => opIntegral (resolventDiff S) 0 b) X
def opLog (S : BddOp H) : BddOp H :=
  Classical.epsilon fun X => IsLogOf S X
end Definitions
def IntegrableOnHalfLine (g : ℝ → ℝ) : Prop :=
  ∃ l : ℝ, Tendsto (fun x : ℝ => ∫ t in (0 : ℝ)..x, |g t|) atTop (nhds l)
section Claims
variable (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
def AddScalarClaim : Prop :=
  ∀ T : BddOp H, IsSelfAdjointOp T → ∀ s s' : ℝ,
    IsSelfAdjointOp (addScalar T s) ∧ (IsBoundedBelowBy T s' → IsBoundedBelowBy (addScalar T s) (s' + s))
def OpCompleteness : Prop :=
  ∀ (𝒳 : ℕ → Set (BddOpBetween H H')) (ε : ℕ → ℝ),
    (∀ n, 1 ≤ n → (𝒳 n).Nonempty ∧ 0 ≤ ε n ∧ 𝒳 (n + 1) ⊆ 𝒳 n ∧
      ∀ X ∈ 𝒳 n, ∀ X' ∈ 𝒳 n, ‖X - X'‖ ≤ ε n) →
    Tendsto ε atTop (nhds 0) →
    ∃! X : BddOpBetween H H', ∀ n, 1 ≤ n → ∀ X' ∈ 𝒳 n, ‖X - X'‖ ≤ ε n
def IsSeriesSum {N : Type} (Y : N → BddOpBetween H H')
    (X : BddOpBetween H H') : Prop :=
  ∀ F : Finset N, ‖X - ∑ ν ∈ F, Y ν‖ ≤ ∑' ν : {ν // ν ∉ F}, ‖Y ν‖
def AbsSummableSeries : Prop :=
  ∀ (N : Type) [Countable N] [Infinite N] (Y : N → BddOpBetween H H'),
    Summable (fun ν => ‖Y ν‖) →
    ∃ X : BddOpBetween H H', IsSeriesSum H H' Y X ∧
      (∀ X', IsSeriesSum H H' Y X' → X' = X) ∧
      ‖X‖ ≤ ∑' ν, ‖Y ν‖ ∧
      ∀ e : ℕ+ ≃ N, TendstoInOpNorm atTop
        (fun n : ℕ+ => ∑ l ∈ Finset.Icc 1 n, Y (e l)) X
def NeumannClaim : Prop :=
  ∀ (A : BddOp H) (q : ℝ), ‖A‖ ≤ q → q < 1 →
    ∃ B : BddOp H,
      TendstoInOpNorm atTop (fun n : ℕ => ∑ l ∈ Finset.range (n + 1), A ^ l) B ∧
      IsTwoSidedInverse (1 - A) B ∧ ‖B‖ ≤ (1 - q)⁻¹
def CompactIntervalIntegral : Prop :=
  ∀ (a b : ℝ) (T : ℝ → BddOp H), a < b → NormContinuousOn T a b →
    UniformlyNormContinuousOn T a b ∧
    (∃! X, RiemannSumsTendsto T a b X) ∧
    RiemannSumsTendsto T a b (opIntegral T a b) ∧
    ContinuousOn (fun t => ‖T t‖) (Icc a b) ∧
    ‖opIntegral T a b‖ ≤ ∫ t in a..b, ‖T t‖ ∧
    ∀ c : ℝ, a < c → c < b →
      opIntegral T a b = opIntegral T a c + opIntegral T c b
def HalfLineIntegral : Prop :=
  ∀ T : ℝ → BddOp H, (∀ b : ℝ, 0 < b → NormContinuousOn T 0 b) →
    IntegrableOnHalfLine (fun t => ‖T t‖) →
    ∃! X, TendstoInOpNorm atTop (fun b : ℝ => opIntegral T 0 b) X
def LogExists : Prop :=
  ∀ (S : BddOp H) (c : ℝ), IsSelfAdjointOp S → 0 < c → IsBoundedBelowBy S c →
    (∀ t : ℝ, 0 ≤ t → IsTwoSidedInverse (addScalar S t) (inverseOp (addScalar S t)) ∧
      ‖inverseOp (addScalar S t)‖ ≤ (c + t)⁻¹) ∧
    (∀ x : ℝ, 0 < x → NormContinuousOn (resolventDiff S) 0 x) ∧
    ContinuousOn (fun t => ‖resolventDiff S t‖) (Ici 0) ∧
    IntegrableOnHalfLine (fun t => ‖resolventDiff S t‖) ∧
    (∀ b : ℝ, 0 < b → ∃! X, RiemannSumsTendsto (resolventDiff S) 0 b X) ∧
    (∃! X, IsLogOf S X) ∧
    IsLogOf S (opLog S)
end Claims
def Calculus.Statement : Prop :=
  ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'],
    AddScalarClaim H ∧ OpCompleteness H H' ∧ AbsSummableSeries H H' ∧
    NeumannClaim H ∧ CompactIntervalIntegral H ∧ HalfLineIntegral H ∧
    LogExists H
end YangMills.Construction.OperatorCalculus
end
