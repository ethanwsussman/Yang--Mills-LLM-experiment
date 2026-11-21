import YangMills.Construction.TransferOperators.GaugeAverageAndExchangeOfLayers
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter YangMills.Construction.InfiniteLattice YangMills.Construction.SpinHarmonics YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.TransferOperators
variable {μ : Fin 4} {v : Set (SliceSite μ)} {I : Set (ℤ × SliceLink μ)}
def IsRealValuedSliceFunction (Ψ : (I → specialUnitary) → ℂ) : Prop := ∀ u, (Ψ u).im = 0
def SliceGaugeMeanInvariantContraction [Finite v] [Finite I]
    (hI : ∀ i ∈ I, i.2 ∈ linksWithin v) : Prop :=
  (∀ Ψ : C(I → specialUnitary, ℂ), Continuous (sliceGaugeMean hI Ψ) ∧
    IsDiagonalGaugeInvariant hI (sliceGaugeMean hI Ψ)) ∧
  (∀ Ψ Φ : C(I → specialUnitary, ℂ),
    sliceGaugeMean hI (Ψ + Φ) = sliceGaugeMean hI Ψ + sliceGaugeMean hI Φ) ∧
  (∀ (c : ℂ) (Ψ : C(I → specialUnitary, ℂ)),
    sliceGaugeMean hI (c • Ψ) = c • sliceGaugeMean hI Ψ) ∧
  (∀ (Ψ : C(I → specialUnitary, ℂ)) (u : I → specialUnitary), ‖sliceGaugeMean hI Ψ u‖ ≤ ‖Ψ‖) ∧
  (∀ Ψ : C(I → specialUnitary, ℂ), IsRealValuedSliceFunction (Ψ : (I → specialUnitary) → ℂ) →
    IsRealValuedSliceFunction (sliceGaugeMean hI Ψ)) ∧
  ∀ Ψ : C(I → specialUnitary, ℂ),
    IsDiagonalGaugeInvariant hI (Ψ : (I → specialUnitary) → ℂ) →
      sliceGaugeMean hI Ψ = Ψ
def SliceGaugeMeanPreservesPolynomials [Finite v] [Finite I]
    (hI : ∀ i ∈ I, i.2 ∈ linksWithin v) : Prop :=
  ∀ Ψ : C(I → specialUnitary, ℂ),
    (IsEntryPolynomial (Ψ : (I → specialUnitary) → ℂ) → IsEntryPolynomial (sliceGaugeMean hI Ψ)) ∧
    (IsRealEntryPolynomial (Ψ : (I → specialUnitary) → ℂ) →
      IsRealEntryPolynomial (sliceGaugeMean hI Ψ))
def InvariantRealApproxByInvariantPolynomials [Finite I]
    (hI : ∀ i ∈ I, i.2 ∈ linksWithin v) : Prop :=
  ∀ Ψ : C(I → specialUnitary, ℂ), IsRealValuedSliceFunction (Ψ : (I → specialUnitary) → ℂ) →
    IsDiagonalGaugeInvariant hI (Ψ : (I → specialUnitary) → ℂ) →
    ∃ P : ℕ → (I → specialUnitary) → ℂ,
      (∀ n, IsRealEntryPolynomial (P n) ∧ IsDiagonalGaugeInvariant hI (P n)) ∧
      TendstoUniformly P Ψ atTop
def SliceGaugeMeanCommutesLevelExchange [Finite v] [Finite I]
    (hI : ∀ i ∈ I, i.2 ∈ linksWithin v) : Prop :=
  ∀ s : Equiv.Perm I, IsLevelExchange s → ∀ Ψ : C(I → specialUnitary, ℂ),
    sliceGaugeMean hI (levelExchanged s Ψ) =
      permuteArgs s (sliceGaugeMean hI Ψ) ∧
    ‖levelExchanged s Ψ‖ = ‖Ψ‖ ∧
    (IsDiagonalGaugeInvariant hI (Ψ : (I → specialUnitary) → ℂ) →
      IsDiagonalGaugeInvariant hI
        (levelExchanged s Ψ : (I → specialUnitary) → ℂ)) ∧
    (IsRealEntryPolynomial (Ψ : (I → specialUnitary) → ℂ) →
      IsRealEntryPolynomial (levelExchanged s Ψ : (I → specialUnitary) → ℂ))
def Stack.transportedFamily (S : Stack) (J : Set (ℤ × SliceLink μ)) (U : GaugeField 1) :
    J → specialUnitary :=
  fun i => S.transportedLinkVariable μ U i.1.1 i.1.2
def SliceGaugeMeanPreservesExpectation [Finite v]
    (hI : ∀ i ∈ I, i.2 ∈ linksWithin v) (β : ℝ) : Prop :=
  ∀ S : Stack, (∀ i ∈ I, S.lower ≤ i.1 ∧ i.1 ≤ S.upper) →
    ∀ ν ∈ gibbsClass one_pos β, ∀ Ψ : C(I → specialUnitary, ℂ),
      ∫ U, sliceGaugeMean hI Ψ (S.transportedFamily I U) ∂ν =
        ∫ U, Ψ (S.transportedFamily I U) ∂ν
def SliceGaugeMeanProperties : Prop :=
  ∀ (μ : Fin 4) (β : ℝ), 0 < β →
    ∀ (v : Set (SliceSite μ)) (I : Set (ℤ × SliceLink μ)) [Finite v] [Finite I],
      v.Nonempty → I.Nonempty → ∀ hI : ∀ i ∈ I, i.2 ∈ linksWithin v,
        SliceGaugeMeanInvariantContraction hI ∧
        SliceGaugeMeanPreservesPolynomials hI ∧
        InvariantRealApproxByInvariantPolynomials hI ∧
        SliceGaugeMeanCommutesLevelExchange hI ∧
        SliceGaugeMeanPreservesExpectation hI β
end YangMills.Construction.TransferOperators
end
