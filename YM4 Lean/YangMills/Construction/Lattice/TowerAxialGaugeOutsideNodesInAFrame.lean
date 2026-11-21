import YangMills.Construction.Lattice.SetsOfBondsOfASequenceOfRegions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
variable {L m : ℕ} {j j' : ℤ}
def framedBlockComb (σ : SignedFrame) (z : Site L m j) (x : Site L m j') : List (Bond L m j') :=
  (combToBlockSite (σ.preimageSite z) (σ.preimageSite x)).map σ.mapBond
def framedTowerAxialGauge (σ : SignedFrame) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (𝔅 : Set (Σ j : ℕ, BondAtLevel L m K j)) (W₀ : BondAtLevel L m K 0 → ComplexMatrix2) :
    Set (BondAtLevel L m K 0 → ComplexMatrix2) :=
  {W | W ∈ gaugeFieldsInside K (Ω 0) ∧
    ∀ (n : ℕ) (z : SiteAtLevel L m K (n + 1)) (x : SiteAtLevel L m K n),
      IsChainTriple K k Ω n z x → ¬IsEndpointOf 𝔅 (x : FourTorus L m) →
        AndAveragesFormed (Ω 0) {b | b ∈ framedBlockComb σ z x}
          (pathHolonomy (regionBlockField n (Ω 0) W) (framedBlockComb σ z x) =
            pathHolonomy (regionBlockField n (Ω 0) W₀) (framedBlockComb σ z x))}
def HasFramedAxialRepresentative (ε : ℝ) (σ : SignedFrame) (K k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) (𝔅 : Set (Σ j : ℕ, BondAtLevel L m K j))
    (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) (W₀ : BondAtLevel L m K 0 → ComplexMatrix2) :
    Prop :=
  IsLinkDatum 𝔅 V ∧ HasFormedMinimalOrbit (Averaging.smoothingRadius L) ε K k Ω 𝔅 V ∧
    ∃! W, W ∈ formedRegularCriticalSet (Averaging.smoothingRadius L) ε K k Ω 𝔅 V ∧
      W ∈ framedTowerAxialGauge σ K k Ω 𝔅 W₀
def framedAxialRepresentative (ε : ℝ) (σ : SignedFrame) (K k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) (𝔅 : Set (Σ j : ℕ, BondAtLevel L m K j))
    (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) (W₀ : BondAtLevel L m K 0 → ComplexMatrix2) :
    BondAtLevel L m K 0 → ComplexMatrix2 :=
  Classical.epsilon fun W =>
    W ∈ formedRegularCriticalSet (Averaging.smoothingRadius L) ε K k Ω 𝔅 V ∧
      W ∈ framedTowerAxialGauge σ K k Ω 𝔅 W₀
def framedAxialRepresentativeAtOne (ε : ℝ) (σ : SignedFrame) (K k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) (𝔅 : Set (Σ j : ℕ, BondAtLevel L m K j))
    (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) : BondAtLevel L m K 0 → ComplexMatrix2 :=
  framedAxialRepresentative ε σ K k Ω 𝔅 V trivialGaugeField
end YangMills.Construction.PeriodicLattice
