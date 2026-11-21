import YangMills.Construction.Lattice.LandauGaugeRelativeToABackground
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
variable {L m K k : ℕ}
def fieldsAgreeingOffBox (Z Λ : Set (FourTorus L m)) (V : BondAtLevel L m K k → ComplexMatrix2) :
    Set (BondAtLevel L m K k → ComplexMatrix2) :=
  {W | IsGaugeField compactGaugeGroup (bondsMeeting Z) W ∧
    (∀ b ∉ (bondsMeeting Z : Set (BondAtLevel L m K k)), W b = 1) ∧
    ∀ b ∈ (bondsMeeting Z \ bondsMeeting Λ : Set (BondAtLevel L m K k)), W b = V b}
def IsCriticalFieldOverBox (Z Λ : Set (FourTorus L m)) (V : BondAtLevel L m K k → ComplexMatrix2)
    (IsFormed : (BondAtLevel L m K k → ComplexMatrix2) → Prop)
    (U : (BondAtLevel L m K k → ComplexMatrix2) → BondAtLevel L m K 0 → ComplexMatrix2)
    (W : BondAtLevel L m K k → ComplexMatrix2) : Prop :=
  W ∈ fieldsAgreeingOffBox Z Λ V ∧
    (∃ ρ : ℝ, 0 < ρ ∧ ∀ W' ∈ fieldsAgreeingOffBox Z Λ V,
      (∀ b ∈ (bondsMeeting Z : Set (BondAtLevel L m K k)),
        ComplexMatrix2.operatorNorm (W' b - W b) < ρ) → IsFormed W') ∧
    ∀ (δ : ℝ) (c : ℝ → BondAtLevel L m K k → ComplexMatrix2), 0 < δ →
      (∀ s ∈ Ioo (-δ) δ, c s ∈ fieldsAgreeingOffBox Z Λ V) →
      (∀ b i j, DifferentiableOn ℝ (fun s => c s b i j) (Ioo (-δ) δ)) → c 0 = W →
      HasDerivAt (fun s => actionInside K Z (U (c s))) 0 0
def IsGaugeEquivalentOverBox (Z Λ : Set (FourTorus L m)) (W W' : BondAtLevel L m K k → ComplexMatrix2) :
    Prop :=
  (∀ b ∉ (bondsMeeting Z : Set (BondAtLevel L m K k)), W' b = 1) ∧
    ∃ u : SiteAtLevel L m K k → ComplexMatrix2, IsGaugeTransformSupportedIn Λ u ∧
      ∀ b ∈ (bondsMeeting Z : Set (BondAtLevel L m K k)), W' b = gaugeTransform u W b
def IsInCriticalOrbitOverBox (Z Λ : Set (FourTorus L m)) (V : BondAtLevel L m K k → ComplexMatrix2)
    (IsFormed : (BondAtLevel L m K k → ComplexMatrix2) → Prop)
    (U : (BondAtLevel L m K k → ComplexMatrix2) → BondAtLevel L m K 0 → ComplexMatrix2)
    (W : BondAtLevel L m K k → ComplexMatrix2) : Prop :=
  IsCriticalFieldOverBox Z Λ V IsFormed U W ∧
    ∀ W', IsCriticalFieldOverBox Z Λ V IsFormed U W' ↔ IsGaugeEquivalentOverBox Z Λ W W'
end YangMills.Construction.PeriodicLattice
