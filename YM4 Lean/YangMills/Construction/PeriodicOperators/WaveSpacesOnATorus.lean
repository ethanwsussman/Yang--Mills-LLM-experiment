import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.BlochDecomposition
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open RiemannSums (DualClasses periodLattice)
structure Facts (I : PeriodicData) : Prop where
  dualClasses_finite : ∀ s, 0 < s → Finite (DualClasses s)
  blochWave_descends : ∀ s, 0 < s → ∀ κ ∈ dualLattice s, ∀ φ : I.UnitQuot → ℂ,
    ∃ g : I.QuotMod s → ℂ, ∀ i, g (I.mkQuot s i) = blochWave I (toComplexVec κ) φ i
  blochWave_injective : ∀ (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ),
    (∀ i, blochWave I κ φ i = 0) → φ = 0
  subspace_congr : ∀ s, 0 < s → ∀ κ ∈ dualLattice s, ∀ κ' ∈ dualLattice s, κ' - κ ∈ periodLattice →
    blochWaveSubspace I s κ = blochWaveSubspace I s κ'
  internal_sum : ∀ s, 0 < s → ∀ r, IsDualSection s r →
    iSupIndep (fun q => blochWaveSubspace I s (r q)) ∧ ⨆ q, blochWaveSubspace I s (r q) = ⊤
  orthogonal : ∀ s, 0 < s → ∀ r, IsDualSection s r → ∀ q q', q ≠ q' →
    ∀ g ∈ blochWaveSubspace I s (r q), ∀ g' ∈ blochWaveSubspace I s (r q'),
      wInner (I.quotWeight s) g g' = 0
def Claim : Prop :=
  ∀ I : PeriodicData, IsPeriodic I → Facts I
end YangMills.Construction.PeriodicOperators.BlochDecomposition
end
