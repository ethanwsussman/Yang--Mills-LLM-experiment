import YangMills.Construction.Towers.DerivativesOnFiniteSetsOfPlaquettesOnASide
import YangMills.Construction.Towers.SecondDerivativeOfFormsWithNoCommonPlaquetteOnASide
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower.LeftChartAlgebra
namespace DisjointFaces
open FiniteFaceDerivatives (faceSetAction)
variable {L n k j : ℕ}
theorem expTwist_congr_edge {C C' U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (h : C b = C' b) (h' : C b.opposite = C' b.opposite) :
    PeriodicLattice.expTwist C U b = PeriodicLattice.expTwist C' U b ∧
      PeriodicLattice.expTwist C U b.opposite = PeriodicLattice.expTwist C' U b.opposite := by
  have hrr : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
  simp only [PeriodicLattice.expTwist, hrr, h, h', and_self]
theorem complexFaceTerm_congr {U C C' : Edge L n k j → ComplexMatrix2}
    (hC : C ∈ complexEdgeForms L n k j) (hC' : C' ∈ complexEdgeForms L n k j) (p : Face L n k j)
    (h : ∀ b ∈ faceEdges p, C b = C' b) :
    complexFaceTerm (PeriodicLattice.expTwist C U) p =
      complexFaceTerm (PeriodicLattice.expTwist C' U) p := by
  have hv : ∀ b ∈ faceEdges p,
      PeriodicLattice.expTwist C U b = PeriodicLattice.expTwist C' U b ∧
        PeriodicLattice.expTwist C U b.opposite = PeriodicLattice.expTwist C' U b.opposite := by
    intro b hb
    refine expTwist_congr_edge (h b hb) ?_
    rw [hC.2 b, hC'.2 b, h b hb]
  have h₁ := hv _ (show PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis ∈ faceEdges p by
    simp [faceEdges])
  have h₂ := hv _ (show PeriodicLattice.Bond.forwardFrom
    (p.origin + PeriodicLattice.unitStep L n _ p.firstAxis) p.secondAxis ∈ faceEdges p by
    simp [faceEdges])
  have h₃ := hv _ (show PeriodicLattice.Bond.forwardFrom
    (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis) p.firstAxis ∈ faceEdges p by
    simp [faceEdges])
  have h₄ := hv _ (show PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis ∈ faceEdges p by
    simp [faceEdges])
  simp only [complexFaceTerm, PeriodicLattice.plaquetteEnergy,
    PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds,
    List.map_cons, List.map_nil, h₁.1, h₂.1, h₃.2, h₄.2]
theorem hessianDisjointVanish_of_finite (hD : FiniteFaceDerivatives.HoldsOnTorus L n k j)
    (hF : FaceEdgeFinsets.HoldsOnTorus L n k j) :
    HessianDisjointVanish L n k j := by
  intro U B B' hU hB hB' hno
  have hfin : Finite (Face L n k j) := Set.finite_univ_iff.mp hF.2.2.2.1
  have hfty : Fintype (Face L n k j) := Fintype.ofFinite _
  have hne : (Finset.univ : Finset (Face L n k j)).Nonempty :=
    ⟨FaceEdgeFinsets.baseFace L n k j, Finset.mem_univ _⟩
  obtain ⟨-, hΦ⟩ := hD Finset.univ hne
  obtain ⟨Φ, -, -, h⟩ := hΦ U hU
  have hd := (h B hB B' hB' (fun p _ => by simp)).1.2
  let φ : (Edge L n k j → ComplexMatrix2) → ℂ := fun C =>
    faceSetAction Finset.univ (PeriodicLattice.expTwist C U)
  have hzero : (0 : Edge L n k j → ComplexMatrix2) ∈ complexEdgeForms L n k j :=
    (complexEdgeForms L n k j).zero_mem
  have hsB : ∀ s : ℂ, s • B ∈ complexEdgeForms L n k j :=
    fun s => (complexEdgeForms L n k j).smul_mem s hB
  have htB' : ∀ t : ℂ, t • B' ∈ complexEdgeForms L n k j :=
    fun t => (complexEdgeForms L n k j).smul_mem t hB'
  have hsum : ∀ s t : ℂ, s • B + t • B' ∈ complexEdgeForms L n k j :=
    fun s t => (complexEdgeForms L n k j).add_mem (hsB s) (htB' t)
  have hsplit : ∀ s t : ℂ, φ (s • B + t • B') = φ (s • B) + φ (t • B') - φ 0 := by
    intro s t
    simp only [φ, faceSetAction]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : ∃ b ∈ edgeSupport B, b ∈ faceEdges p
    · have hB'0 : ∀ b ∈ faceEdges p, B' b = 0 := by
        intro b hb
        by_contra hne'
        exact hno ⟨p, hp, b, ⟨hF.1.2 p b hb, hne'⟩, hb⟩
      rw [complexFaceTerm_congr (hsum s t) (hsB s) p (fun b hb => by simp [hB'0 b hb]),
        complexFaceTerm_congr (htB' t) hzero p (fun b hb => by simp [hB'0 b hb])]
      ring
    · have hB0 : ∀ b ∈ faceEdges p, B b = 0 := by
        intro b hb
        by_contra hne'
        exact hp ⟨b, ⟨hF.1.2 p b hb, hne'⟩, hb⟩
      rw [complexFaceTerm_congr (hsum s t) (htB' t) p (fun b hb => by simp [hB0 b hb]),
        complexFaceTerm_congr (hsB s) hzero p (fun b hb => by simp [hB0 b hb])]
      ring
  have hconst : (fun s : ℂ => deriv (fun t : ℂ => φ (s • B + t • B')) 0) =
      fun _ => deriv (fun t : ℂ => φ (t • B')) 0 := by
    funext s
    simp only [hsplit, add_sub_assoc]
    rw [deriv_const_add, deriv_sub_const]
  have hd' : HasDerivAt (fun _ : ℂ => deriv (fun t : ℂ => φ (t • B')) 0)
      (complexActionHessian U B B') 0 := hconst ▸ hd
  exact hd'.unique (hasDerivAt_const _ _)
end DisjointFaces
open DisjointFaces in
theorem hessianDisjointVanishFiniteSide_holds
    (hD : FiniteFaceDerivatives.ReadOnFiniteFaceSets)
    (hF : FaceEdgeFinsets.FacesAndEdgesFinite) : HessianDisjointVanishFiniteSide := by
  intro L n k j hL hn hj
  exact hessianDisjointVanish_of_finite (hD L n k j hL hn hj) ((hF L hL k j hj).1 n hn)
end Tower.LeftChartAlgebra
end YangMills.Construction
end
