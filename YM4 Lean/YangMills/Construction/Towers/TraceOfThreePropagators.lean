import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.ResolventTrace
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad
open YangMills.Construction.PeriodicOperators.StripSymbols (openStripInterior)
inductive IsBracketedProductOf {I : PeriodicData} (p : Fin 4 → ℂ) :
    List (JetQuad I I) → JetQuad I I → Prop
  | leaf (T : JetQuad I I) : IsBracketedProductOf p [T] T
  | node {l l' : List (JetQuad I I)} {T S : JetQuad I I}
      (hT : IsBracketedProductOf p l T) (hS : IsBracketedProductOf p l' S) :
      IsBracketedProductOf p (l ++ l') (mul p T S)
def sixfoldProduct {I : PeriodicData} (p : Fin 4 → ℂ) (G : I.Carrier → I.Carrier → ℂ)
    (B₁ B₂ B₃ : JetQuad I I) : JetQuad I I :=
  mul p (ofKernel I I G) (mul p B₁ (mul p (ofKernel I I G) (mul p B₂
    (mul p (ofKernel I I G) B₃))))
structure TraceBoundOn (γ : ℝ) (I : PeriodicData) (G : I.Carrier → I.Carrier → ℂ) : Prop where
  periodic : IsPeriodicKernel I I G
  symbol_holomorphic : SymbolSummableOn I I G (openStripInterior (1 / 8)) ∧
    QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior (1 / 8)) (symbolHom I I G)
  imStrip_subset : imStrip (2 * stripHalfWidth) ⊆ openStripInterior (1 / 8)
  isJet : ∀ p ∈ imStrip stripHalfWidth, IsJet stripHalfWidth p (ofKernel I I G)
  mul_isJet : ∀ p ∈ imStrip stripHalfWidth, ∀ B₁ B₂ B₃ : JetQuad I I,
    IsJet stripHalfWidth p B₁ → IsJet stripHalfWidth p B₂ → IsJet stripHalfWidth p B₃ →
      IsJet stripHalfWidth p (sixfoldProduct p G B₁ B₂ B₃)
  bracketing_eq : ∀ p ∈ imStrip stripHalfWidth, ∀ B₁ B₂ B₃ : JetQuad I I,
    IsJet stripHalfWidth p B₁ → IsJet stripHalfWidth p B₂ → IsJet stripHalfWidth p B₃ →
      ∀ X, IsBracketedProductOf p
          [ofKernel I I G, B₁, ofKernel I I G, B₂, ofKernel I I G, B₃] X →
        IsJet stripHalfWidth p X ∧ EqAsJet stripHalfWidth p X (sixfoldProduct p G B₁ B₂ B₃)
  trace_le : ∀ p ∈ imStrip stripHalfWidth, ∀ B₁ B₂ B₃ : JetQuad I I,
    IsJet stripHalfWidth p B₁ → IsJet stripHalfWidth p B₂ → IsJet stripHalfWidth p B₃ →
      ENNReal.ofReal ‖traceNumber (sixfoldProduct p G B₁ B₂ B₃)‖ ≤
        ENNReal.ofReal γ * jetNorm stripHalfWidth p B₁ * jetNorm stripHalfWidth p B₂ *
          jetNorm stripHalfWidth p B₃
def IsThreeResolventTraceBound (γ : ℝ) : Prop :=
  0 ≤ γ ∧ ∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
    ∀ k : ℕ, 1 ≤ k →
    TraceBoundOn γ (colourEdges L k 0) (YangMills.Construction.Tower.FreeResolvents.edgeResolvent L k) ∧
      TraceBoundOn γ (colourVertices L k 0)
        (YangMills.Construction.Tower.FreeResolvents.vertexResolvent L k)
def threeResolventTraceConst : ℝ := Classical.epsilon IsThreeResolventTraceBound
def ThreeResolventTraceBound : Prop := IsThreeResolventTraceBound threeResolventTraceConst
end YangMills.Construction.Tower.FullSpace.BackgroundJets.ResolventTrace
end
