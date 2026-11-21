import YangMills.Construction.Lattice.CovarianceOfComplexActions
import YangMills.Construction.Lattice.CovarianceOfComplexPlaquetteVariables
import YangMills.Construction.Lattice.IsometryCovarianceOfHolonomiesAndActionsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace EnergyCovariance
variable {L m : ℕ} {j : ℤ}
section Sums
variable {σ : FourTorus L m ≃ FourTorus L m}
theorem plaquetteImage_symm_plaquetteImage (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    (h : MapsCellsAndCubes σ j) (h' : MapsCellsAndCubes σ.symm j)
    (p : Plaquette L m j) : plaquetteImage σ.symm (plaquetteImage σ p) = p := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.plaquetteImage_symm_plaquetteImage <;> assumption
theorem plaquetteImage_plaquetteImage_symm (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    (h : MapsCellsAndCubes σ j) (h' : MapsCellsAndCubes σ.symm j)
    (p : Plaquette L m j) : plaquetteImage σ (plaquetteImage σ.symm p) = p := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.plaquetteImage_plaquetteImage_symm <;> assumption
def plaquettePerm (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) : Plaquette L m j ≃ Plaquette L m j where
  toFun := plaquetteImage σ
  invFun := plaquetteImage σ.symm
  left_inv := plaquetteImage_symm_plaquetteImage hL hj h h'
  right_inv := plaquetteImage_plaquetteImage_symm hL hj h h'
theorem mem_plaquettesInside_iff (X : Set (FourTorus L m)) (p : Plaquette L m j) :
    p ∈ (plaquettesInside X : Set (Plaquette L m j)) ↔
      (fun x : Site L m j => (x : FourTorus L m)) '' p.vertices ⊆ X := by
  constructor
  · rintro h _ ⟨c, hc, rfl⟩
    exact h c hc
  · intro h c hc
    exact h ⟨c, hc, rfl⟩
theorem plaquetteImage_mem_plaquettesInside_iff
    (hvert : ∀ p : Plaquette L m j,
      (fun x : Site L m j => (x : FourTorus L m)) '' (plaquetteImage σ p).vertices =
        σ '' ((fun x : Site L m j => (x : FourTorus L m)) '' p.vertices))
    (X : Set (FourTorus L m)) (p : Plaquette L m j) :
    plaquetteImage σ p ∈ (plaquettesInside (σ '' X) : Set (Plaquette L m j)) ↔
      p ∈ (plaquettesInside X : Set (Plaquette L m j)) := by
  rw [mem_plaquettesInside_iff, mem_plaquettesInside_iff, hvert,
    Set.image_subset_image_iff σ.injective]
theorem finsum_plaquettesInside_image {M : Type*} [AddCommMonoid M] (hL : 0 < L)
    (hj : -(m : ℤ) ≤ j) (h : MapsCellsAndCubes σ j) (h' : MapsCellsAndCubes σ.symm j)
    (hvert : ∀ p : Plaquette L m j,
      (fun x : Site L m j => (x : FourTorus L m)) '' (plaquetteImage σ p).vertices =
        σ '' ((fun x : Site L m j => (x : FourTorus L m)) '' p.vertices))
    (X : Set (FourTorus L m)) (F G : Plaquette L m j → M)
    (hFG : ∀ p ∈ (plaquettesInside X : Set (Plaquette L m j)), G (plaquetteImage σ p) = F p) :
    ∑ᶠ p ∈ (plaquettesInside (σ '' X) : Set (Plaquette L m j)), G p =
      ∑ᶠ p ∈ (plaquettesInside X : Set (Plaquette L m j)), F p := by
  symm
  refine finsum_mem_eq_of_bijOn (plaquetteImage σ) ⟨?_, ?_, ?_⟩ fun p hp => (hFG p hp).symm
  · exact fun p hp => (plaquetteImage_mem_plaquettesInside_iff hvert X p).2 hp
  · exact fun p _ p' _ e => (plaquettePerm hL hj h h').injective e
  · intro p' hp'
    refine ⟨plaquetteImage σ.symm p', ?_, plaquetteImage_plaquetteImage_symm hL hj h h' p'⟩
    rw [← plaquetteImage_mem_plaquettesInside_iff hvert X,
      plaquetteImage_plaquetteImage_symm hL hj h h']
    exact hp'
end Sums
theorem boundaryBonds_mem_bondsInside {X : Set (FourTorus L m)} {p : Plaquette L m j}
    (hp : p ∈ (plaquettesInside X : Set (Plaquette L m j))) :
    ∀ b ∈ p.boundaryBonds, b ∈ (bondsInside X : Set (Bond L m j)) := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.boundaryBonds_mem_bondsInside <;> assumption
theorem analyticAt_plaquetteEnergy {B : Set (Bond L m j)} [Fintype ↥B] {p : Plaquette L m j}
    (hp : ∀ b ∈ p.boundaryBonds, b ∈ B) (w : ↥B → Matrices.ComplexMatrix2) :
    AnalyticAt ℂ
      (fun w : ↥B → Matrices.ComplexMatrix2 => plaquetteEnergy (extendWithIdentity B w) p) w := by
  have hhol := analyticAt_pathHolonomy_extendByOne hp w
  have htr : AnalyticAt ℂ (fun Z : Matrices.ComplexMatrix2 => Matrices.ComplexMatrix2.fullTrace Z)
      (pathHolonomy (extendWithIdentity B w) p.boundaryBonds) :=
    (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)).analyticAt _
  exact analyticAt_const.sub (analyticAt_const.mul (AnalyticAt.fun_comp htr hhol))
theorem isHolomorphicEquation_of_finsum [Finite (Bond L m j)] [Finite (Plaquette L m j)]
    (σ : FourTorus L m ≃ FourTorus L m) {B : Set (Bond L m j)} (S : Set (Plaquette L m j))
    (c : Plaquette L m j → ℂ) {f₁ f₂ : (Bond L m j → Matrices.ComplexMatrix2) → ℂ}
    (hS : ∀ p ∈ S, ∀ b ∈ p.boundaryBonds, b ∈ B)
    (hf : ∀ U, f₂ U = ∑ᶠ p ∈ S, c p * plaquetteEnergy U p)
    (h : ∀ U ∈ complexGaugeFields B, f₁ U = f₂ U) :
    IsHolomorphicEquationOnComplexFields σ B f₁ f₂ := by
  classical
  have : Fintype ↥B := Fintype.ofFinite _
  have hfin : S.Finite := S.toFinite
  let F : (↥B → Matrices.ComplexMatrix2) → ℂ := fun w =>
    ∑ p ∈ hfin.toFinset, c p * plaquetteEnergy (extendWithIdentity B w) p
  have hF : ∀ w, AnalyticAt ℂ F w := fun w =>
    Finset.analyticAt_fun_sum _ fun p hp =>
      analyticAt_const.mul (analyticAt_plaquetteEnergy (hS p (hfin.mem_toFinset.1 hp)) w)
  have hval : ∀ U, f₂ U = F (restrictToBonds B U) := fun U => by
    rw [hf, finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine Finset.sum_congr rfl fun p hp => ?_
    have e : plaquetteEnergy (extendWithIdentity B (restrictToBonds B U)) p =
        plaquetteEnergy U p := by
      unfold plaquetteEnergy plaquetteHolonomy
      rw [pathHolonomy_extendByOne U (hS p (hfin.mem_toFinset.1 hp))]
    rw [e]
  have hopen : Matrices.ComplexMatrix2.IsRelativelyOpen
      (restrictToBonds B '' complexGaugeFields B)
      (restrictToBonds B '' (complexGaugeFields B ∩ complexGaugeFields B)) := by
    rw [inter_self]
    exact isRelativelyOpen_self _
  exact ⟨IsHolomorphicOnFields.of_analytic_formula F (fun _ hU => hU.1) hopen (fun _ _ => hF _)
      fun U hU => (h U hU.1).trans (hval U),
    IsHolomorphicOnFields.of_analytic_formula F (fun _ hU => hU.1) hopen (fun _ _ => hF _)
      fun U _ => hval U,
    fun U hU => h U hU.1, fun _ => rfl⟩
end EnergyCovariance
open EnergyCovariance in
theorem complexEnergiesIsometryInvariant_holds (h₁ : LatticeIsometryGroupActionStatement)
    (h₂ : IsometriesPreserveCells)
    (h₃ : PlaquetteVariablesCovarianceStatement) :
    ComplexEnergiesIsometryInvariant := by
  obtain ⟨ε, h₃⟩ := h₃
  intro L m i σ hL hm hi hσ j hj
  have hpos : 0 < L := by
    have := hL.2
    omega
  have hgrp := h₁ L m i hL hm hi
  have hσinv : σ.symm ∈ latticeIsometries L m i := by
    obtain ⟨⟨H, hH⟩, -⟩ := hgrp.1
    have t : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := by rw [hH]; exact hσ
    have t' := H.inv_mem t
    rw [← hH]
    exact t'
  have hmap := (hgrp.2.2.2.2 σ hσ j hj).1
  have hmapInv := (hgrp.2.2.2.2 σ.symm hσinv j hj).1
  have hjm : -(m : ℤ) ≤ j := hi.trans hj
  have : Finite (Site L m j) := SeparatedSequences.BaseParameters.site_finite hpos m j
  have : Finite (Bond L m j) :=
    Finite.of_injective (fun b : Bond L m j => (b.source, b.target)) fun b b' hb =>
      Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  have : Finite (Plaquette L m j) :=
    Finite.of_injective (fun p : Plaquette L m j => (p.origin, p.firstAxis, p.secondAxis))
      fun p q h => by
        simp only [Prod.mk.injEq] at h
        exact Plaquette.ext h.1 h.2.1 h.2.2
  have hvert := (h₂ L m i j σ hL hm hi hσ hj).2.2.2.2.2.1
  have henergy : ∀ (B : Set (Bond L m j)), IsReversalClosed B → ∀ p : Plaquette L m j,
      (∀ b ∈ p.boundaryBonds, b ∈ B) → ∀ U ∈ complexGaugeFields B,
        plaquetteEnergy (transportGaugeField σ U) (plaquetteImage σ p) =
          plaquetteEnergy U p := by
    intro B hB p hp U hU
    obtain ⟨Γ, -, hΓ⟩ := h₃ L m i σ hL hm hi hσ j hj p
    exact (hΓ B hB hp).2.2.2.1 U ⟨hU, hU⟩
  have hall : IsReversalClosed (univ : Set (Bond L m j)) := fun _ _ => mem_univ _
  refine ⟨fun c Ω₀ _ _ => ?_, fun f => ?_, fun f => ?_⟩
  · have hcl : IsReversalClosed (bondsInside Ω₀ : Set (Bond L m j)) :=
      fun b hb => ⟨hb.2, hb.1⟩
    refine isHolomorphicEquation_of_finsum σ (plaquettesInside Ω₀) (fun _ => 1)
      (fun p hp => boundaryBonds_mem_bondsInside hp) (fun U => by simp [interiorEnergy])
      fun U hU => ?_
    exact finsum_plaquettesInside_image hpos hjm hmap hmapInv hvert Ω₀ _ _
      fun p hp => henergy _ hcl p (boundaryBonds_mem_bondsInside hp) U hU
  · refine isHolomorphicEquation_of_finsum σ univ f (fun _ _ _ _ => mem_univ _)
      (fun U => by simp [plaquetteWeightedEnergy]) fun U hU => ?_
    unfold plaquetteWeightedEnergy
    rw [← finsum_comp_equiv (plaquettePerm hpos hjm hmap hmapInv)]
    refine finsum_congr fun p => ?_
    change f (plaquetteImage σ.symm (plaquetteImage σ p)) *
      plaquetteEnergy (transportGaugeField σ U) (plaquetteImage σ p) = _
    rw [plaquetteImage_symm_plaquetteImage hpos hjm hmap hmapInv,
      henergy univ hall p (fun _ _ => mem_univ _) U hU]
  · refine isHolomorphicEquation_of_finsum σ univ (fun p => f p.barycenter)
      (fun _ _ _ _ => mem_univ _)
      (fun U => by simp [barycenterWeightedEnergy, plaquetteWeightedEnergy]) fun U hU => ?_
    unfold barycenterWeightedEnergy plaquetteWeightedEnergy
    rw [← finsum_comp_equiv (plaquettePerm hpos hjm hmap hmapInv)]
    refine finsum_congr fun p => ?_
    change f (σ.symm (plaquetteImage σ p).barycenter) *
      plaquetteEnergy (transportGaugeField σ U) (plaquetteImage σ p) = _
    rw [hmap.2.2.2.2.2.2.2.1, Equiv.symm_apply_apply,
      henergy univ hall p (fun _ _ => mem_univ _) U hU]
end YangMills.Construction.PeriodicLattice
