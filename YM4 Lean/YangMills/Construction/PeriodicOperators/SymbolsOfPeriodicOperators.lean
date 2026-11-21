import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import Mathlib
open Set
open scoped ENNReal
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
open RiemannSums (DualClasses periodLattice)
structure SymbolProperties (P Q R : PeriodicData) (K : Q.Carrier → P.Carrier → ℂ)
    (L : P.Carrier → R.Carrier → ℂ) (δ : ℝ) : Prop where
  summable_on_strip : SymbolSummableOn P Q K (strictImStrip δ)
  summable_locallyUniformly : ∀ j i,
    SummableLocallyUniformlyOn (fun k κ => symbolSummand P Q K κ j i k) (strictImStrip δ)
  norm_summable_locallyUniformly : ∀ j i,
    SummableLocallyUniformlyOn (fun k κ => ‖symbolSummand P Q K κ j i k‖) (strictImStrip δ)
  isHolomorphicIn : ∀ j i, Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1)
    (strictImStrip δ) fun κ _ => fourierSymbol P Q K κ j i
  eq_of_mkQuot_eq : ∀ κ, SymbolSummableAt P Q K κ → ∀ j₁ j₂ i₁ i₂,
    Q.mkQuot 1 j₁ = Q.mkQuot 1 j₂ → P.mkQuot 1 i₁ = P.mkQuot 1 i₂ →
      fourierSymbol P Q K κ j₁ i₁ = fourierSymbol P Q K κ j₂ i₂
  applyKernel_blochWave : ∀ κ, SymbolSummableAt P Q K κ → ∀ (φ : P.UnitQuot → ℂ) j,
    ApplySummableAt K (blochWave P κ φ) j ∧
      applyKernel K (blochWave P κ φ) j =
        blochWave Q κ (applyKernel (quotSymbol P Q K κ) φ) j
  compKernel_isPeriodicKernel : (∀ j l, CompSummableAt K L j l) ∧
    IsPeriodicKernel R Q (compKernel K L)
  kernelTranspose_isPeriodicKernel : IsPeriodicKernel Q P (kernelTranspose P Q K)
  quotSymbol_compKernel : ∀ κ ∈ strictImStrip δ, SymbolSummableAt R Q (compKernel K L) κ ∧
    quotSymbol R Q (compKernel K L) κ =
      compKernel (quotSymbol P Q K κ) (quotSymbol R P L κ)
  quotSymbol_kernelTranspose : ∀ κ ∈ strictImStrip δ,
    SymbolSummableAt Q P (kernelTranspose P Q K) κ ∧
      quotSymbol Q P (kernelTranspose P Q K) κ =
        quotTranspose P Q (quotSymbol P Q K (-κ))
  wInner_quotTranspose : (∀ j i, (K j i).im = 0) → ∀ (κ : AmbientSpace) (f : P.UnitQuot → ℂ)
    (g : Q.UnitQuot → ℂ),
      wInner (P.quotWeight 1)
          (applyKernel (quotTranspose P Q (quotSymbol P Q K (-toComplexVec κ))) g) f =
        wInner (Q.quotWeight 1) g
          (applyKernel (quotSymbol P Q K (toComplexVec κ)) f)
  exp_phase_eq_of_mkQuot_eq : ∀ (e : Fin 4 → ℤ) i₁ i₂, P.mkQuot 1 i₁ = P.mkQuot 1 i₂ →
    Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (P.pos i₁))) =
      Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (P.pos i₂)))
  quotSymbol_addTwoPiInt : ∀ κ (e : Fin 4 → ℤ), SymbolSummableAt P Q K κ →
    SymbolSummableAt P Q K (addTwoPiInt κ e) ∧
      IsUnit (phaseMul Q e : Module.End ℂ (Q.UnitQuot → ℂ)) ∧
      ∀ f : P.UnitQuot → ℂ, applyKernel (quotSymbol P Q K (addTwoPiInt κ e)) f =
        Ring.inverse (phaseMul Q e : Module.End ℂ (Q.UnitQuot → ℂ))
          (applyKernel (quotSymbol P Q K κ) (phaseMul P e f))
  periodization_summable : ∀ s, 0 < s → ∀ j i, PeriodizationSummableAt P Q K s j i
  periodization_eq_of_mkQuot_eq : ∀ s, 0 < s → ∀ j₁ j₂ i₁ i₂,
    Q.mkQuot s j₁ = Q.mkQuot s j₂ → P.mkQuot s i₁ = P.mkQuot s i₂ →
      periodization P Q K s j₁ i₁ = periodization P Q K s j₂ i₂
  blochWaveSubspace_internal : ∀ s, 0 < s → ∀ r, IsDualSection s r →
    iSupIndep (fun q => blochWaveSubspace P s (r q)) ∧ ⨆ q, blochWaveSubspace P s (r q) = ⊤
  blochWaveSubspace_orthogonal : ∀ s, 0 < s → ∀ r, IsDualSection s r → ∀ q q', q ≠ q' →
    ∀ g ∈ blochWaveSubspace P s (r q), ∀ g' ∈ blochWaveSubspace P s (r q'),
      wInner (P.quotWeight s) g g' = 0
  periodicMatrix_blochWave : ∀ s, 0 < s → ∀ κ ∈ dualLattice s, ∀ (φ : P.UnitQuot → ℂ)
    (g : P.QuotMod s → ℂ), (∀ i, g (P.mkQuot s i) = blochWave P (toComplexVec κ) φ i) →
      ∀ j, applyKernel (periodicMatrix P Q K s) g (Q.mkQuot s j) =
        blochWave Q (toComplexVec κ)
          (applyKernel (quotSymbol P Q K (toComplexVec κ)) φ) j
  trace_eq_zero_of_shift : ∀ s, 0 < s → ∀ q ∈ dualLattice s, q ∉ periodLattice →
    ∀ A : (P.QuotMod s → ℂ) →ₗ[ℂ] (P.QuotMod s → ℂ),
      (∀ κ ∈ dualLattice s, ∀ g ∈ blochWaveSubspace P s κ, A g ∈ blochWaveSubspace P s (κ + q)) →
        LinearMap.trace ℂ (P.QuotMod s → ℂ) A = 0
  fourierSymbol_expConj : ∀ θ : AmbientSpace, euclidNormVec θ < δ →
    ∀ κ ∈ strictImStrip (δ - euclidNormVec θ),
      IsPeriodicKernel P Q (expConj P Q θ K) ∧
        SymbolSummableAt P Q (expConj P Q θ K) κ ∧
        fourierSymbol P Q (expConj P Q θ K) κ = fourierSymbol P Q K (addIVec κ θ)
  kernelOpNorm_lt_top :
    (∀ f ∈ normSummableSet P, ∀ j, ApplySummableAt K f j) ∧
      OpNormSummable P.weightOf Q.weightOf (normSummableSet P) (applyKernel K) ∧
      kernelOpNorm P Q K < ⊤
  quotOpNorm_le : ∀ κ : AmbientSpace,
    quotOpNorm P Q (quotSymbol P Q K (toComplexVec κ)) ≤ kernelOpNorm P Q K
structure SymbolPropertiesEndo (P : PeriodicData) (K : P.Carrier → P.Carrier → ℂ) : Prop where
  trace_addTwoPiInt : ∀ [Fintype P.UnitQuot] κ (e : Fin 4 → ℤ), SymbolSummableAt P P K κ →
    Matrix.trace (Matrix.of (quotSymbol P P K (addTwoPiInt κ e))) =
      Matrix.trace (Matrix.of (quotSymbol P P K κ))
  det_addTwoPiInt : ∀ [Fintype P.UnitQuot] [DecidableEq P.UnitQuot] κ (e : Fin 4 → ℤ),
    SymbolSummableAt P P K κ →
      Matrix.det (Matrix.of (quotSymbol P P K (addTwoPiInt κ e))) =
        Matrix.det (Matrix.of (quotSymbol P P K κ))
  trace_periodicMatrix : ∀ s, 0 < s → ∀ [Fintype P.UnitQuot] [Fintype (P.QuotMod s)]
    [Fintype (DualClasses s)] r, IsDualSection s r →
      Matrix.trace (Matrix.of (periodicMatrix P P K s)) =
        ∑ q, Matrix.trace (Matrix.of (quotSymbol P P K (toComplexVec (r q))))
  det_periodicMatrix : ∀ s, 0 < s → ∀ [Fintype P.UnitQuot] [DecidableEq P.UnitQuot]
    [Fintype (P.QuotMod s)] [DecidableEq (P.QuotMod s)] [Fintype (DualClasses s)] r,
      IsDualSection s r →
        Matrix.det (Matrix.of (periodicMatrix P P K s)) =
          ∏ q, Matrix.det (Matrix.of (quotSymbol P P K (toComplexVec (r q))))
namespace Symbols
def Claim : Prop :=
  (∀ (P Q R : PeriodicData), IsPeriodic P → IsPeriodic Q → IsPeriodic R →
    ∀ (K : Q.Carrier → P.Carrier → ℂ) (L : P.Carrier → R.Carrier → ℂ) (δ : ℝ),
      IsPeriodicKernel P Q K → IsDecayRate P Q K δ →
      IsPeriodicKernel R P L → IsDecayRate R P L δ →
        SymbolProperties P Q R K L δ) ∧
  (∀ P : PeriodicData, IsPeriodic P → ∀ (K : P.Carrier → P.Carrier → ℂ) (δ : ℝ),
    IsPeriodicKernel P P K → IsDecayRate P P K δ → SymbolPropertiesEndo P K)
end Symbols
end PeriodicOperators
end YangMills.Construction
end
