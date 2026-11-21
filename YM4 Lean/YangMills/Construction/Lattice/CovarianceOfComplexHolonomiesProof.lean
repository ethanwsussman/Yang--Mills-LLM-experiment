import YangMills.Construction.Lattice.CovarianceOfComplexContourVariablesProof
import YangMills.Construction.Lattice.CovarianceOfComplexHolonomies
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
namespace HolonomyTransport
variable {L m : ℕ} {j : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
theorem pathHolonomy_transport_pathImage (hσ : MapsCellsAndCubes σ j)
    (hσinv : MapsCellsAndCubes σ.symm j) (U : Bond L m j → ComplexMatrix2)
    (γ : List (Bond L m j)) :
    pathHolonomy (transportGaugeField σ U) (pathImage σ γ) = pathHolonomy U γ := by apply _root_.YangMills.Construction.PeriodicLattice.ContourCovariance.pathHolonomy_transport_pathImage <;> assumption
end HolonomyTransport
open HolonomyTransport in
theorem complexHolonomyCovariance_holds (hgroup : LatticeIsometryGroupActionStatement) :
    ComplexHolonomyCovariance := by
  intro L m i σ hL hm hi hσ j hj S _ γ _ hγ
  have hpos : 0 < L := by
    have := hL.2
    omega
  have hg := hgroup L m i hL hm hi
  have hσsymm : σ.symm ∈ latticeIsometries L m i := by
    obtain ⟨⟨H, hH⟩, -⟩ := hg.1
    have hmem : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := by rw [hH]; exact hσ
    have hinv := H.inv_mem hmem
    rw [← hH]
    exact hinv
  have hc := (hg.2.2.2.2 σ hσ j hj).1
  have hs := (hg.2.2.2.2 σ.symm hσsymm j hj).1
  have : Finite (Site L m j) := SeparatedSequences.BaseParameters.site_finite hpos m j
  have : Finite (Bond L m j) :=
    Finite.of_injective (fun b : Bond L m j => (b.source, b.target)) fun b b' hb =>
      Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  have : Fintype ↥S := Fintype.ofFinite _
  let F : (↥S → ComplexMatrix2) → ComplexMatrix2 := fun w => pathHolonomy (extendWithIdentity S w) γ
  have hF : ∀ w, AnalyticAt ℂ F w := fun w => analyticAt_pathHolonomy_extendByOne hγ w
  have hval : ∀ U, pathHolonomy U γ = F (restrictToBonds S U) := fun U =>
    (pathHolonomy_extendByOne U hγ).symm
  have hopen : ComplexMatrix2.IsRelativelyOpen (restrictToBonds S '' complexGaugeFields S)
      (restrictToBonds S '' (complexGaugeFields S ∩ complexGaugeFields S)) := by
    rw [inter_self]
    exact isRelativelyOpen_self _
  exact ⟨IsHolomorphicOnFields.of_analytic_formula F (fun _ hU => hU.1) hopen (fun _ _ => hF _)
      fun U _ => (pathHolonomy_transport_pathImage hc hs U γ).trans (hval U),
    IsHolomorphicOnFields.of_analytic_formula F (fun _ hU => hU.1) hopen (fun _ _ => hF _)
      fun U _ => hval U,
    fun U _ => pathHolonomy_transport_pathImage hc hs U γ, fun _ => rfl⟩
end YangMills.Construction.PeriodicLattice
