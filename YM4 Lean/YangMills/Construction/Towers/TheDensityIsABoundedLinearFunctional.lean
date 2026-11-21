import YangMills.Construction.Towers.TheDensityOfAnAbelianField
import Mathlib
set_option autoImplicit false
open Filter Set YangMills.Construction.OneLoopNotation YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
section Functional
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def opIntegralIoi (T : ℝ → BddOp H) : BddOp H :=
  Classical.epsilon fun X =>
    TendstoInOpNorm atTop (fun m : ℝ => opIntegral T 0 m) X
def complexIntegralIoi (g : ℝ → ℂ) : ℂ :=
  Classical.epsilon fun c => Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y, g w) atTop (nhds c)
def IsBoundedLinearTrace (τ : BddOp H → ℂ) (n : ℕ) : Prop :=
  (∀ (T T' : BddOp H) (s : ℂ), τ (T + s • T') = τ T + s * τ T') ∧
  (∀ T : BddOp H, ‖τ T‖ ≤ (n : ℝ) * ‖T‖) ∧
  τ (ContinuousLinearMap.id ℂ H) = (n : ℂ)
def CommutesWithIntegral (τ : BddOp H → ℂ) (n : ℕ) : Prop :=
  ∀ T : ℝ → BddOp H, (∀ m : ℝ, 0 < m → NormContinuousOn T 0 m) →
    (∃ l : ℝ, Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y, ‖T w‖) atTop (nhds l)) →
    (∀ m : ℝ, 0 < m → RiemannSumsTendsto T 0 m (opIntegral T 0 m)) ∧
    TendstoInOpNorm atTop (fun m : ℝ => opIntegral T 0 m)
      (opIntegralIoi T) ∧
    ContinuousOn (fun w : ℝ => τ (T w)) (Ici 0) ∧
    (∀ w : ℝ, 0 ≤ w → ‖τ (T w)‖ ≤ (n : ℝ) * ‖T w‖) ∧
    Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y, τ (T w)) atTop
      (nhds (complexIntegralIoi fun w => τ (T w))) ∧
    τ (opIntegralIoi T) = complexIntegralIoi fun w => τ (T w)
end Functional
def TraceIsBoundedLinear : Prop :=
  ∀ (L : ℕ) (x : FullSpace.Vertex L 0 0),
    (IsBoundedLinearTrace
        (fun T : BddOp (L2Field (FullSpace.Vertex L 0 0)) =>
          traceAt (vertexPos L) T x) 3 ∧
      CommutesWithIntegral
        (fun T : BddOp (L2Field (FullSpace.Vertex L 0 0)) =>
          traceAt (vertexPos L) T x) 3) ∧
    (IsBoundedLinearTrace
        (fun T : BddOp (L2Field (PeriodicOperators.PosEdge L 0 0)) =>
          traceAt (edgePos L) T x) 12 ∧
      CommutesWithIntegral
        (fun T : BddOp (L2Field (PeriodicOperators.PosEdge L 0 0)) =>
          traceAt (edgePos L) T x) 12) ∧
    ∀ N' : ℕ, 1 ≤ N' →
      IsBoundedLinearTrace
          (fun T : BddOp (VectorL2 L N') => vecTraceAt T x) N' ∧
        CommutesWithIntegral
          (fun T : BddOp (VectorL2 L N') => vecTraceAt T x) N'
end YangMills.Construction.Tower.AbelianFieldDensity
end
