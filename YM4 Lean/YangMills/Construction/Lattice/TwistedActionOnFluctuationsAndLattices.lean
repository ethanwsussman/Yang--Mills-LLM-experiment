import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegions
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices Conventions
variable {L m : ℕ} {j : ℤ}
def IsGaugeFieldWithForm (B : Set (Bond L m j)) (V₀ X : Bond L m j → ComplexMatrix2) : Prop :=
  (IsGaugeField compactGaugeGroup B V₀ ∧ X ∈ realFormsOn B) ∨
    (IsGaugeField complexGaugeGroup B V₀ ∧ X ∈ complexFormsOn B)
def PreservesLatticeAndPartition (σ : FourTorus L m ≃ FourTorus L m) (j : ℤ) : Prop :=
  σ '' (sublattice L m j : Set (FourTorus L m)) = sublattice L m j ∧
  (∀ b : Bond L m j, ((bondImage σ b).source : FourTorus L m) = σ b.source ∧
    ((bondImage σ b).target : FourTorus L m) = σ b.target) ∧
  (fun S => σ '' S) '' bondEdgeSets L m j = bondEdgeSets L m j ∧
  (∀ p : Plaquette L m j, (plaquetteImage σ p).face = σ '' p.face) ∧
  (fun S => σ '' S) '' plaquetteFaces L m j = plaquetteFaces L m j ∧
  (fun Q => σ '' Q) '' standardCubePartition L m j = standardCubePartition L m j
def TwistedTransportOfFluctuations : Prop :=
  ∀ (L m : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m), IsAdmissibleBlockingFactor L → 0 < m →
    -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i →
    (∀ j : ℤ, -(m : ℤ) < j → i ≤ j → ∀ B : Set (Bond L m j), IsReversalClosed B →
      ∀ V₀ X : Bond L m j → ComplexMatrix2, IsGaugeFieldWithForm B V₀ X →
        (∀ b' ∈ bondSetTransport σ B,
          transportGaugeField σ (expTwist X V₀) b' =
            expTwist (twistedTransportForm σ V₀ X) (transportGaugeField σ V₀) b') ∧
        ((IsTorusTranslation σ ∨ ∃ π : Equiv.Perm (Fin 4), HasLinearPart σ (π, 1)) →
          twistedTransportForm σ V₀ X = transportForm σ X)) ∧
    ∀ i' : ℤ, i ≤ i' → PreservesLatticeAndPartition σ i'
end YangMills.Construction.PeriodicLattice
