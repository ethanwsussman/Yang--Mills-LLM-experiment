import YangMills.Construction.LinearAlgebra.TraceOfSixFoldProduct
import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SixJetTrace
open JetQuad
open TraceBound (schattenThreeNorm)
open RealPower (rpowPos)
def Bound : Prop :=
  ∀ I : PeriodicData, IsPeriodic I → ∀ [Finite I.UnitQuot], Nonempty I.UnitQuot →
    ∀ (δ : ℝ) (p : Fin 4 → ℂ) (A : (Fin 4 → ℂ) → QuotHom I I) (γ : ℝ), 0 < δ → p ∈ imStrip δ →
      IsJet δ p (⟨A, 0, 0, 0⟩ : JetQuad I I) → 0 ≤ γ →
      (∀ θ ∈ ({0, p, -p} : Set (Fin 4 → ℂ)),
        Continuous (fun κ : InfiniteLattice.AmbientSpace =>
          rpowPos (schattenThreeNorm (wInner (I.quotWeight 1)) (A (toComplexVec κ + θ))) 3) ∧
        ((2 * Real.pi) ^ 4)⁻¹ * ∫ κ in Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi),
          rpowPos (schattenThreeNorm (wInner (I.quotWeight 1)) (A (toComplexVec κ + θ))) 3
          ≤ γ) →
      ∀ B₁ B₂ B₃ : JetQuad I I, IsJet δ p B₁ → IsJet δ p B₂ → IsJet δ p B₃ →
        ENNReal.ofReal ‖traceNumber (mul p ⟨A, 0, 0, 0⟩ (mul p B₁ (mul p ⟨A, 0, 0, 0⟩
          (mul p B₂ (mul p ⟨A, 0, 0, 0⟩ B₃)))))‖ ≤
          ENNReal.ofReal γ * jetNorm δ p B₁ * jetNorm δ p B₂ * jetNorm δ p B₃
end YangMills.Construction.PeriodicOperators.SixJetTrace
end
