import YangMills.Construction.Lattice.PeriodicLattices
import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
class OrientedEdgeEnds (P : outParam Type) (E : Type) where
  src : E → P
  tgt : E → P
  flip : E → E
  src_flip : ∀ b, src (flip b) = tgt b
  tgt_flip : ∀ b, tgt (flip b) = src b
  flip_flip : ∀ b, flip (flip b) = b
instance {L m K : ℕ} : OrientedEdgeEnds (FourTorus L m) (Σ k : ℕ, BondAtLevel L m K k) where
  src b := (b.2.source : FourTorus L m)
  tgt b := (b.2.target : FourTorus L m)
  flip b := ⟨b.1, b.2.opposite⟩
  src_flip _ := rfl
  tgt_flip _ := rfl
  flip_flip _ := rfl
namespace FaddeevPopov
open OrientedEdgeEnds
variable {P E : Type} [OrientedEdgeEnds P E] {Ξ : Type*} [MeasurableSpace Ξ]
abbrev SiteGaugeGroup (S : Finset P) : Type := S → ComplexMatrix2.specialUnitary
def extendByOne {S : Finset P} (u : SiteGaugeGroup S) (p : P) : ComplexMatrix2.specialUnitary :=
  open Classical in if h : p ∈ S then u ⟨p, h⟩ else 1
def movedField {S : Finset P} (v : E → ComplexMatrix2.specialUnitary) (u : SiteGaugeGroup S)
    (b : E) : ComplexMatrix2.specialUnitary :=
  extendByOne u (src b) * v b * (extendByOne u (tgt b))⁻¹
def edgeGraph (T : Finset E) : SimpleGraph P :=
  SimpleGraph.fromRel fun x y => ∃ b ∈ T, src b = x ∧ tgt b = y
def IsSimpleTreePath (T : Finset E) (p₀ p : P) (Γ : List E) : Prop :=
  (∀ b ∈ Γ, b ∈ T) ∧ Γ.IsChain (fun b b' => tgt b = src b') ∧
  (Γ = [] → p₀ = p) ∧ (∀ b ∈ Γ.head?, src b = p₀) ∧ (∀ b ∈ Γ.getLast?, tgt b = p) ∧
  (p₀ :: Γ.map tgt).Nodup
def simpleTreePath (T : Finset E) (p₀ p : P) : List E :=
  Classical.epsilon (IsSimpleTreePath T p₀ p)
end FaddeevPopov
end YangMills.Construction.PeriodicLattice
