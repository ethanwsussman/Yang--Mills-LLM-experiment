import YangMills.Construction.Conventions.LatticeAndStateDefs
import YangMills.Construction.SpectralMeasures.ProjectionValuedMeasuresOnASigmaAlgebra
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology ComplexConjugate
open scoped InnerProductSpace ComplexOrder
noncomputable section
namespace YangMills.Construction.SpectralMeasures
open YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert YangMills.Construction.LatticeConventions
namespace BddCalculus
variable {Ω 𝓗 : Type} [MeasurableSpace Ω]
  [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
structure Laws (P : PVM Ω 𝓗) : Prop where
  diag_finite : ∀ v, IsFiniteMeasure (P.diagMeasure v)
  diag_real_eq : ∀ v (A : MeasSet Ω), (P.diagMeasure v).real A.1 = ‖P A v‖ ^ 2
  diag_real_univ : ∀ v, (P.diagMeasure v).real Set.univ = ‖v‖ ^ 2
  apply_empty : P ⟨∅, MeasurableSet.empty⟩ = 0
  existsUnique_bddIntegral : ∀ u : Ω → ℂ, IsBddMeasurable u →
    ∃! T : BddOp 𝓗, P.IsBddIntegral u T
  bddIntegral_add : ∀ u w : Ω → ℂ, IsBddMeasurable u → IsBddMeasurable w →
    P.bddIntegral (u + w) = P.bddIntegral u + P.bddIntegral w
  bddIntegral_smul : ∀ (c : ℂ) (u : Ω → ℂ), IsBddMeasurable u →
    P.bddIntegral (c • u) = c • P.bddIntegral u
  bddIntegral_mul : ∀ u w : Ω → ℂ, IsBddMeasurable u → IsBddMeasurable w →
    P.bddIntegral (u * w) = P.bddIntegral u * P.bddIntegral w
  bddIntegral_indicator : ∀ A : MeasSet Ω, P.bddIntegral (indicatorOne A.1) = P A
  bddIntegral_one : P.bddIntegral (fun _ => 1) = idOp 𝓗
  inner_bddIntegral : ∀ u : Ω → ℂ, IsBddMeasurable u → ∀ v w,
    ⟪v, P.bddIntegral u w⟫_ℂ = ⟪P.bddIntegral (fun x => conj (u x)) v, w⟫_ℂ
  norm_bddIntegral_sq : ∀ u : Ω → ℂ, IsBddMeasurable u → ∀ v,
    ‖P.bddIntegral u v‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂(P.diagMeasure v)
  integral_norm_sq_le : ∀ u : Ω → ℂ, IsBddMeasurable u → ∀ v,
    ∫ x, ‖u x‖ ^ 2 ∂(P.diagMeasure v) ≤ (⨆ x, ‖u x‖ ^ 2) * ‖v‖ ^ 2
  isSymmetricOp_bddIntegral : ∀ u : Ω → ℂ, IsBddMeasurable u → (∀ x, (u x).im = 0) →
    IsSymmetricOp (P.bddIntegral u)
  bddIntegral_nonneg : ∀ u : Ω → ℂ, IsBddMeasurable u → (∀ x, 0 ≤ u x) →
    OpGE (P.bddIntegral u) 0
  tendsto_bddIntegral : ∀ (U : ℕ → Ω → ℂ) (u : Ω → ℂ), (∀ n, IsBddMeasurable (U n)) →
    IsBddMeasurable u → (∀ x, Tendsto (fun n => U n x) atTop (𝓝 (u x))) →
    (∃ M : ℝ, ∀ n x, ‖U n x‖ ≤ M) →
    ∀ v, Tendsto (fun n => P.bddIntegral (U n) v) atTop (𝓝 (P.bddIntegral u v))
  bddIntegral_congr : ∀ u w : Ω → ℂ, IsBddMeasurable u → IsBddMeasurable w →
    ∀ N : MeasSet Ω, P N = 0 → (∀ x, x ∉ N.1 → u x = w x) →
    P.bddIntegral u = P.bddIntegral w
  diag_bddIntegral : ∀ u : Ω → ℂ, IsBddMeasurable u →
    ∀ (A : MeasSet Ω) (v : 𝓗),
    (P.diagMeasure (P.bddIntegral u v)).real A.1 = ∫ x in A.1, ‖u x‖ ^ 2 ∂(P.diagMeasure v)
  pushforward_laws : ∀ (Ω' : Type) [MeasurableSpace Ω'] (k : Ω → Ω') (hk : Measurable k),
    ∃ h : IsPVM (P.pushforward k hk),
      (∀ v, (PVM.mk (P.pushforward k hk) h).diagMeasure v =
        (P.diagMeasure v).map k) ∧
      ∀ u' : Ω' → ℂ, IsBddMeasurable u' →
        (PVM.mk (P.pushforward k hk) h).bddIntegral u' = P.bddIntegral (u' ∘ k)
  conj_laws : ∀ (𝓗' : Type) [NormedAddCommGroup 𝓗'] [InnerProductSpace ℂ 𝓗'] [CompleteSpace 𝓗']
    (U : 𝓗 →ₗ[ℂ] 𝓗') (hU : IsUnitaryMap U),
    ∃ h : IsPVM (P.conj hU),
      (∀ v, (PVM.mk (P.conj hU) h).diagMeasure (U v) =
        P.diagMeasure v) ∧
      ∀ u : Ω → ℂ, IsBddMeasurable u →
        (PVM.mk (P.conj hU) h).bddIntegral u =
          unitaryToBdd hU ∘L P.bddIntegral u ∘L unitaryInvToBdd hU
def Statement : Prop :=
  ∀ (Ω 𝓗 : Type) [MeasurableSpace Ω]
    [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
    (P : PVM Ω 𝓗), Laws P
end BddCalculus
end YangMills.Construction.SpectralMeasures
