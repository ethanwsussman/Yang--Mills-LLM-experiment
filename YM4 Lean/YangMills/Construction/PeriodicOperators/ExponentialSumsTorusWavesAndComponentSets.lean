import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetDomains
def fstMomentum (z : Coordinates.ComplexCoordinates (4 + 4)) : Fin 4 → ℂ := fun μ => z (Fin.castAdd 4 μ)
def sndMomentum (z : Coordinates.ComplexCoordinates (4 + 4)) : Fin 4 → ℂ := fun μ => z (Fin.natAdd 4 μ)
abbrev MomentumLinearForm : Type := ((Fin 4 → ℂ) × (Fin 4 → ℂ)) →ₗ[ℂ] ℂ
def expSum {n : ℕ} (a : Fin n → ℂ) (f : Fin n → MomentumLinearForm) (κ p : Fin 4 → ℂ) : ℂ :=
  ∑ j, a j * Complex.exp (f j (κ, p))
def IsLiftOf (J : PeriodicData) (s : ℕ) (g : J.QuotMod s → ℂ) (f : J.Carrier → ℂ) : Prop :=
  ∀ ι, g (J.mkQuot s ι) = f ι
section Functions
variable (F I I' : PeriodicData)
def WavesDescend (s : ℕ) (κ p : InfiniteLattice.AmbientSpace) (εPlus εMinus : F.UnitQuot → ℂ)
    (φ : I.UnitQuot → ℂ) : Prop :=
  (∃ ζ, IsLiftOf F s ζ (blochWave F (toComplexVec p) εPlus)) ∧
    (∃ ζ, IsLiftOf F s ζ (blochWave F (-toComplexVec p) εMinus)) ∧
    ∃ g, IsLiftOf I s g (blochWave I (toComplexVec κ) φ)
def JetRelationsDescend (T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (s : ℕ)
    (κ p : InfiniteLattice.AmbientSpace) (εPlus εMinus : F.UnitQuot → ℂ) (φ : I.UnitQuot → ℂ) : Prop :=
  ∀ (ζPlus ζMinus : F.QuotMod s → ℂ) (g : I.QuotMod s → ℂ),
    IsLiftOf F s ζPlus (blochWave F (toComplexVec p) εPlus) →
    IsLiftOf F s ζMinus (blochWave F (-toComplexVec p) εMinus) →
    IsLiftOf I s g (blochWave I (toComplexVec κ) φ) →
    ∀ ι' : I'.Carrier,
      applyKernel (descendMatrix I I' s (periodicCoeffOne F I I' T s ζPlus)) g
          (I'.mkQuot s ι') =
        blochWave I' (toComplexVec κ + toComplexVec p)
          ((jetAlong F I I' T (toComplexVec p) εPlus εMinus).f10 (toComplexVec κ) φ) ι' ∧
      applyKernel (descendMatrix I I' s (periodicCoeffOne F I I' T s ζMinus)) g
          (I'.mkQuot s ι') =
        blochWave I' (toComplexVec κ - toComplexVec p)
          ((jetAlong F I I' T (toComplexVec p) εPlus εMinus).f01 (toComplexVec κ) φ) ι' ∧
      applyKernel (descendMatrix I I' s (periodicCoeffTwo F I I' T s ζPlus ζMinus)) g
          (I'.mkQuot s ι') =
        blochWave I' (toComplexVec κ)
          ((jetAlong F I I' T (toComplexVec p) εPlus εMinus).f11 (toComplexVec κ) φ) ι'
end Functions
structure Domains where
  dom00 : Set (Fin 4 → ℂ)
  dom10 : Set (Fin 4 → ℂ)
  dom01 : Set (Fin 4 → ℂ)
  dom11 : Set (Fin 4 → ℂ)
structure AreNhds (δ : ℝ) (p : Fin 4 → ℂ) (O : Domains) : Prop where
  isOpen00 : IsOpen O.dom00
  isOpen10 : IsOpen O.dom10
  isOpen01 : IsOpen O.dom01
  isOpen11 : IsOpen O.dom11
  strip_subset : imStrip (2 * δ) ⊆ O.dom00
  addShift_subset : stripAddShift δ p ⊆ O.dom10
  subShift_subset : stripSubShift δ p ⊆ O.dom01
  real_subset : realDualPoints ⊆ O.dom11
def AddDefinedOn (O O' N : Domains) : Prop :=
  N.dom00 ⊆ O.dom00 ∩ O'.dom00 ∧ N.dom10 ⊆ O.dom10 ∩ O'.dom10 ∧ N.dom01 ⊆ O.dom01 ∩ O'.dom01 ∧
    N.dom11 ⊆ O.dom11 ∩ O'.dom11
def SMulDefinedOn (O N : Domains) : Prop :=
  N.dom00 ⊆ O.dom00 ∧ N.dom10 ⊆ O.dom10 ∧ N.dom01 ⊆ O.dom01 ∧ N.dom11 ⊆ O.dom11
def MulDefinedOn (p : Fin 4 → ℂ) (O O' N : Domains) : Prop :=
  (∀ κ ∈ N.dom00, κ ∈ O.dom00 ∧ κ ∈ O'.dom00) ∧
    (∀ κ ∈ N.dom10, κ ∈ O.dom10 ∧ κ ∈ O'.dom00 ∧ κ + p ∈ O.dom00 ∧ κ ∈ O'.dom10) ∧
    (∀ κ ∈ N.dom01, κ ∈ O.dom01 ∧ κ ∈ O'.dom00 ∧ κ - p ∈ O.dom00 ∧ κ ∈ O'.dom01) ∧
    ∀ κ ∈ N.dom11, κ ∈ O.dom11 ∧ κ ∈ O'.dom00 ∧ κ ∈ O.dom00 ∧ κ ∈ O'.dom11 ∧
      κ - p ∈ O.dom10 ∧ κ ∈ O'.dom01 ∧ κ + p ∈ O.dom01 ∧ κ ∈ O'.dom10
def TransposeDefinedOn (p : Fin 4 → ℂ) (O N : Domains) : Prop :=
  (∀ κ ∈ N.dom00, -κ ∈ O.dom00) ∧ (∀ κ ∈ N.dom10, -κ - p ∈ O.dom10) ∧
    (∀ κ ∈ N.dom01, -κ + p ∈ O.dom01) ∧ ∀ κ ∈ N.dom11, -κ ∈ O.dom11
section Jets
variable {I I' I'' : PeriodicData}
def EntriesHolomorphicOn (D : Set (Fin 4 → ℂ)) (A : (Fin 4 → ℂ) → QuotHom I I') : Prop :=
  ∀ c' c, Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) D fun κ _ => linearMapEntry (A κ) c' c
def HolomorphicOnDomains (O : Domains) (T : JetQuad I I') : Prop :=
  EntriesHolomorphicOn O.dom00 T.f00 ∧ EntriesHolomorphicOn O.dom10 T.f10 ∧
    EntriesHolomorphicOn O.dom01 T.f01 ∧ EntriesHolomorphicOn O.dom11 T.f11
def SupsFinite (δ : ℝ) (p : Fin 4 → ℂ) (T : JetQuad I I') : Prop :=
  (⨆ κ ∈ imStrip (2 * δ), quotHomNorm (T.f00 κ)) < ∞ ∧
    (⨆ κ ∈ stripAddShift δ p, quotHomNorm (T.f10 κ)) < ∞ ∧
    (⨆ κ ∈ stripSubShift δ p, quotHomNorm (T.f01 κ)) < ∞ ∧
    (⨆ κ ∈ realDualPoints, quotHomNorm (T.f11 κ)) < ∞
def SymbolHolomorphicNear (I I' : PeriodicData) (D : Set (Fin 4 → ℂ))
    (T : I'.Carrier → I.Carrier → ℂ) : Prop :=
  ∃ O : Set (Fin 4 → ℂ), IsOpen O ∧ D ⊆ O ∧ SymbolSummableOn I I' T O ∧
    EntriesHolomorphicOn O (symbolHom I I' T)
end Jets
end YangMills.Construction.PeriodicOperators.JetDomains
end
