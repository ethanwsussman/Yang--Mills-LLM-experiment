import YangMills.Construction.Lattice.CovarianceOfTheAveragingMaps
import YangMills.Construction.Lattice.LandauGaugeRelativeToABackground
import YangMills.Construction.Lattice.RepresentativesInTheAxialGauge
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def siteSetImage {j : ℤ} (σ : FourTorus L m ≃ FourTorus L m) (Y : Set (Site L m j)) :
    Set (Site L m j) :=
  {y' | ∃ y ∈ Y, (y' : FourTorus L m) = σ y}
def IsResidualInvariant {E : Type} (ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2)
    (Φ : (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) → E) : Prop :=
  ∀ U ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω
      (activeBondSet K k Ω) V,
    ∀ W ∈ endpointFixingOrbit Ω (activeBondSet K k Ω) U, Φ W = Φ U
def PreservesOrbitFunctions (K : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ (ε : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2),
    0 < ε → IsDeterminingChainFrom K k i Ω → IsLinkDatum (activeBondSet K k Ω) V →
    (HasActiveCriticalOrbit ε K k Ω V ↔
        HasActiveCriticalOrbit ε K k (imageChain σ Ω) (datumImage σ V)) ∧
      (HasActiveCriticalOrbit ε K k Ω V →
        ∀ (E : Type) (Φ : (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) → E),
          IsResidualInvariant ε K k (imageChain σ Ω) (datumImage σ V) Φ →
          ∀ U' ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k
              (imageChain σ Ω) (activeBondSet K k (imageChain σ Ω)) (datumImage σ V),
            ∀ U ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω
                (activeBondSet K k Ω) V,
              Φ U' = Φ (transportGaugeField σ U))
def PreservesRegularFields (K : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ (α₀ : ℝ) (e r k : ℕ) (Ω : ℕ → Set (FourTorus L m)),
    0 < α₀ → IsDeterminingChainFrom K k i Ω → IsSeparatedChain K e r 0 k Ω →
    regularFieldsOnChain α₀ K k (imageChain σ Ω) =
      transportGaugeField σ '' regularFieldsOnChain α₀ K k Ω
def PreservesRegularData (K : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ (δ : ℝ) (e r k : ℕ) (Ω : ℕ → Set (FourTorus L m)),
    0 < δ → IsDeterminingChainFrom K k i Ω → IsSeparatedChain K e r 0 k Ω →
    (∀ V ∈ activeRegularRealFields δ K k Ω,
      datumImage σ V ∈ activeRegularRealFields δ K k (imageChain σ Ω)) ∧
    ∀ V' ∈ activeRegularRealFields δ K k (imageChain σ Ω),
      ∃ V ∈ activeRegularRealFields δ K k Ω, ∀ j ≤ k, datumImage σ V j = V' j
def PreservesFamilyBall (K : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ (ε δ ρ : ℝ) (e r k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2),
    0 < ε → 0 < δ → 0 < ρ → IsDeterminingChainFrom K k i Ω →
    IsSeparatedChain K e r 0 k Ω → V₀ ∈ activeRegularRealFields δ K k Ω →
    HasActiveCriticalOrbit ε K k Ω V₀ →
    complexFamilyBall (bondSetImage σ (activeBondSet K k Ω)) ρ =
      twistedFamily (B := activeBondSet K k Ω) σ V₀ '' complexFamilyBall (activeBondSet K k Ω) ρ
def IsCommonAverageRestriction (ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2)
    (Y : Set (SiteAtLevel L m K (k + 1)))
    (W : BondAtLevel L m K k → Matrices.ComplexMatrix2) : Prop :=
  ∀ U ∈ axialGaugeRepresentatives ε K k Ω V Y,
    ∀ c ∈ blockAndEndpointBonds (activeBondSet K (k + 1) Ω) Y, IsAverageFormedOnRegion (Ω 0) c →
      regionBlockField k (Ω 0) U c = W c
def PreservesAxialGaugeRepresentatives (K : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) :
    Prop :=
  ∀ (ε : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2)
    (Y : Set (SiteAtLevel L m K (k + 1))),
    0 < ε → IsChainFromIndex K (k + 1) i Ω → IsAxialGaugeSetting ε K k Ω V Y →
    IsAxialGaugeSetting ε K k (imageChain σ Ω) (datumImage σ V) (siteSetImage σ Y) ∧
    transportGaugeField σ '' axialGaugeRepresentatives ε K k Ω V Y =
      axialGaugeRepresentatives ε K k (imageChain σ Ω) (datumImage σ V) (siteSetImage σ Y) ∧
    ((∀ y ∈ Y, IsEndpointOf (activeBondSet K (k + 1) Ω) (y : FourTorus L m)) →
      ∀ W : BondAtLevel L m K k → Matrices.ComplexMatrix2, IsCommonAverageRestriction ε K k Ω V Y W →
        IsCommonAverageRestriction ε K k (imageChain σ Ω) (datumImage σ V)
          (siteSetImage σ Y) (transportGaugeField σ W))
def IsometryCovariantRegularSetsAndAxialGauge : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K →
  ∀ (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m), -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i →
    PreservesOrbitFunctions K i σ ∧ PreservesRegularFields K i σ ∧
      PreservesRegularData K i σ ∧ PreservesFamilyBall K i σ ∧
      PreservesAxialGaugeRepresentatives K i σ
end YangMills.Construction.PeriodicLattice
