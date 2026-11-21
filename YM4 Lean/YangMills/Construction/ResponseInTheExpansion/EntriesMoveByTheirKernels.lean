import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace ChartResponse
def HessianEntryLipschitz : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : BlockFrame) (w u : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
        (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
        (Bt : Finset (F.Site F.depth × Fin 4)) (Bn : Finset (F.Site F.top × Fin 4))
        (p q : F.Site F.depth × Fin 4 × imaginaryQuaternions),
        IsBlockTorus L F → ‖p.2.2‖ = 1 → ‖q.2.2‖ = 1 →
        (∀ b, b ∉ Bt → u b.1 b.2 = 0) → (∀ b, b ∉ Bn → v b.1 b.2 = 0) →
        (∀ (θ : F.Site F.depth → Fin 4 → ℝ) (ϑ : F.Site F.top → Fin 4 → ℝ), (∀ z i, 0 ≤ θ z i ∧ θ z i ≤ 1) →
          (∀ y i, 0 ≤ ϑ y i ∧ ϑ y i ≤ 1) →
          IsAdmissibleChartPoint L c.σA (fun z i => w z i + θ z i • u z i)
            (leftTranslate (fun y i => ϑ y i • v y i) V)) →
        |chartMixedDeriv a (fun z i => w z i + u z i) (leftTranslate v V) ![Sum.inl p, Sum.inl q] -
            chartMixedDeriv a w V ![Sum.inl p, Sum.inl q]| ≤
          ∑ b ∈ Bt, C * Real.exp (-(c.δ₁ * (max (cellSupDist (enclosingCell p.1) (enclosingCell q.1))
              (cellSupDist (enclosingCell p.1) (enclosingCell b.1)) : ℕ))) * ‖u b.1 b.2‖ +
            ∑ b ∈ Bn, C * Real.exp (-(c.δ₁ * (max (cellSupDist (enclosingCell p.1) (enclosingCell q.1))
              (cellSupDist (enclosingCell p.1) b.1) : ℕ))) * ‖v b.1 b.2‖
end ChartResponse
end YangMills.Construction
end
