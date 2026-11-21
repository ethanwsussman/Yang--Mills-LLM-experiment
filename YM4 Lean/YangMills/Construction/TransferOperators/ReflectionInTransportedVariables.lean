import YangMills.Construction.TransferOperators.ReflectionInALinkMirrorSymmetricStacksAndTheReversal
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.TransferOperators
variable (μ : Fin 4)
def ReflectedLinkVariablesAt (i : ℤ) (S : Stack) (U U' : GaugeField 1) (j : ℤ) : Prop :=
  (∀ b : SliceLink μ, spatialLinkVariable μ U' j b = spatialLinkVariable μ U (reflectedLevel i j) b) ∧
    (∀ y : SliceSite μ,
      temporalLinkVariable μ U' j y = (temporalLinkVariable μ U (reflectedLevel i j - 1) y)⁻¹) ∧
    (∀ y : SliceSite μ,
      S.parallelTransport μ U' j y =
        (S.parallelTransport μ U S.upper y)⁻¹ * S.parallelTransport μ U (reflectedLevel i j) y) ∧
    ∀ b : SliceLink μ,
      S.transportedLinkVariable μ U' j b =
        (S.parallelTransport μ U S.upper b.source)⁻¹ *
          S.transportedLinkVariable μ U (reflectedLevel i j) b *
          S.parallelTransport μ U S.upper b.target
variable {μ}
def ReflectionSwapsLevels (θ : LatticeSymmetry 1) (i k : ℤ) (hk : 1 ≤ k) : Prop :=
  ∀ (v : Set (SliceSite μ)) [Finite v]
    (Ψ : (centeredLinkPairs i k v → YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary) → ℂ)
    (X : GaugeField 1 → ℂ),
    (linksWithin v).Nonempty → Measurable Ψ → (∃ C : ℝ, ∀ u, ‖Ψ u‖ ≤ C) →
    IsDiagonalGaugeInvariant (snd_mem_linksWithin i k v) Ψ →
    (∀ U : GaugeField 1, X U = Ψ fun p =>
      (centeredStack i k hk).transportedLinkVariable μ U p.1.1 p.1.2) →
    ∀ U : GaugeField 1,
      θ.actOn X U = (Ψ fun p =>
        (centeredStack i k hk).transportedLinkVariable μ U (reflectedLevel i p.1.1) p.1.2) ∧
      (Ψ fun p => (centeredStack i k hk).transportedLinkVariable μ U (reflectedLevel i p.1.1) p.1.2) =
        levelReversal i k v Ψ fun p => (centeredStack i k hk).transportedLinkVariable μ U p.1.1 p.1.2
def ReflectionOnTransportedVariables : Prop :=
  ∀ (μ : Fin 4) (i k : ℤ) (hk : 1 ≤ k),
    ∃ θ : LatticeSymmetry 1, θ.toFun = linkMirrorReflection μ i ∧
      (∀ (U : GaugeField 1) (j : ℤ), i - k + 1 ≤ j → j ≤ i + k →
        ReflectedLinkVariablesAt μ i (centeredStack i k hk) U (θ.pullbackField U) j) ∧
      ReflectionSwapsLevels (μ := μ) θ i k hk
end YangMills.Construction.TransferOperators
end
