import YangMills.Construction.Lattice.ElementaryBoundsOfOneStepProof
import YangMills.Construction.Lattice.SignAndGaugeInvarianceOfTheAction
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexOrder
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice.ActionSign
variable {L m : ℕ} {j : ℤ}
theorem inv_eq_star_of_mem_compactGaugeGroup {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    V⁻¹ = star V := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.inv_eq_star_of_mem <;> assumption
theorem inv_mul_self_of_mem_compactGaugeGroup {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    V⁻¹ * V = 1 := by apply _root_.YangMills.SharedProofs.p14555 <;> assumption
theorem fullTrace_im_eq_zero {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    (ComplexMatrix2.fullTrace V).im = 0 := by
  have hdet : V.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp hV).2
  have hadj : star V = V.adjugate := by
    rw [← inv_eq_star_of_mem_compactGaugeGroup hV, Matrix.inv_def, hdet, Ring.inverse_one,
      one_smul]
  have hdiag : star (V 0 0) = V 1 1 := by
    have := congrFun (congrFun hadj 0) 0
    simpa [Matrix.adjugate_fin_two, Matrix.star_apply] using this
  rw [ComplexMatrix2.fullTrace, Matrix.trace_fin_two, ← hdiag]
  simp
theorem abs_fullTrace_re_le_two {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    |(ComplexMatrix2.fullTrace V).re| ≤ 2 := by
  have hunit := Matrix.specialUnitaryGroup_le_unitaryGroup hV
  have hfirst := entry_norm_bound_of_unitary hunit 0 0
  have hsecond := entry_norm_bound_of_unitary hunit 1 1
  have hrefirst := Complex.abs_re_le_norm (V 0 0)
  have hresecond := Complex.abs_re_le_norm (V 1 1)
  rw [ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Complex.add_re]
  calc |(V 0 0).re + (V 1 1).re| ≤ |(V 0 0).re| + |(V 1 1).re| := abs_add_le _ _
    _ ≤ 2 := by linarith
theorem plaquetteHolonomy_mem {U : Bond L m j → ComplexMatrix2} {p : Plaquette L m j}
    (hU : ∀ b ∈ p.boundaryBonds, U b ∈ compactGaugeGroup) :
    plaquetteHolonomy U p ∈ compactGaugeGroup := by
  refine Submonoid.list_prod_mem _ ?_
  intro x hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact hU b hb
theorem plaquetteEnergy_nonneg {U : Bond L m j → ComplexMatrix2} {p : Plaquette L m j}
    (hU : ∀ b ∈ p.boundaryBonds, U b ∈ compactGaugeGroup) : 0 ≤ plaquetteCost U p := by
  have h := abs_le.mp (abs_fullTrace_re_le_two (plaquetteHolonomy_mem hU))
  unfold plaquetteCost
  linarith [h.2]
theorem complexPlaquetteEnergy_eq_ofReal {U : Bond L m j → ComplexMatrix2} {p : Plaquette L m j}
    (hU : ∀ b ∈ p.boundaryBonds, U b ∈ compactGaugeGroup) :
    plaquetteEnergy U p = (plaquetteCost U p : ℂ) := by
  have h := fullTrace_im_eq_zero (plaquetteHolonomy_mem hU)
  apply Complex.ext
  · simp [plaquetteEnergy, plaquetteCost]
  · simp [plaquetteEnergy, h]
theorem complexPlaquetteEnergy_nonneg {U : Bond L m j → ComplexMatrix2} {p : Plaquette L m j}
    (hU : ∀ b ∈ p.boundaryBonds, U b ∈ compactGaugeGroup) : 0 ≤ plaquetteEnergy U p := by
  rw [complexPlaquetteEnergy_eq_ofReal hU]
  exact Complex.zero_le_real.mpr (plaquetteEnergy_nonneg hU)
theorem plaquetteHolonomy_gaugeTransform {g : Site L m j → ComplexMatrix2} {p : Plaquette L m j}
    (hg : ∀ c ∈ p.vertices, g c ∈ compactGaugeGroup) (U : Bond L m j → ComplexMatrix2) :
    plaquetteHolonomy (gaugeTransform g U) p =
      g p.origin * plaquetteHolonomy U p * (g p.origin)⁻¹ := by
  have cancel : ∀ x ∈ p.vertices, ∀ X : ComplexMatrix2, (g x)⁻¹ * (g x * X) = X :=
    fun x hx X => by
      rw [← mul_assoc, inv_mul_self_of_mem_compactGaugeGroup (hg x hx), one_mul]
  have cancelOne := cancel (p.origin + unitStep L m j p.firstAxis) (by simp [Plaquette.vertices])
  have cancelTwo := cancel (p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis)
    (by simp [Plaquette.vertices])
  have cancelThree := cancel (p.origin + unitStep L m j p.secondAxis)
    (by simp [Plaquette.vertices])
  have hswap : p.origin + unitStep L m j p.secondAxis + unitStep L m j p.firstAxis =
      p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis := add_right_comm _ _ _
  simp only [plaquetteHolonomy, pathHolonomy, Plaquette.boundaryBonds, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, gaugeTransform, Bond.forwardFrom, Bond.opposite,
    mul_one, hswap, mul_assoc, cancelOne, cancelTwo, cancelThree]
theorem fullTrace_plaquetteHolonomy_gaugeTransform {g : Site L m j → ComplexMatrix2}
    {p : Plaquette L m j} (hg : ∀ c ∈ p.vertices, g c ∈ compactGaugeGroup)
    (U : Bond L m j → ComplexMatrix2) :
    ComplexMatrix2.fullTrace (plaquetteHolonomy (gaugeTransform g U) p) =
      ComplexMatrix2.fullTrace (plaquetteHolonomy U p) := by
  have horigin : g p.origin ∈ compactGaugeGroup := hg _ (by simp [Plaquette.vertices])
  rw [plaquetteHolonomy_gaugeTransform hg, ComplexMatrix2.fullTrace, Matrix.trace_mul_comm,
    ← mul_assoc, inv_mul_self_of_mem_compactGaugeGroup horigin, one_mul]
theorem plaquetteEnergy_gaugeTransform {g : Site L m j → ComplexMatrix2} {p : Plaquette L m j}
    (hg : ∀ c ∈ p.vertices, g c ∈ compactGaugeGroup) (U : Bond L m j → ComplexMatrix2) :
    plaquetteCost (gaugeTransform g U) p = plaquetteCost U p := by
  unfold plaquetteCost
  rw [fullTrace_plaquetteHolonomy_gaugeTransform hg]
theorem complexPlaquetteEnergy_gaugeTransform {g : Site L m j → ComplexMatrix2}
    {p : Plaquette L m j} (hg : ∀ c ∈ p.vertices, g c ∈ compactGaugeGroup)
    (U : Bond L m j → ComplexMatrix2) :
    plaquetteEnergy (gaugeTransform g U) p = plaquetteEnergy U p := by
  unfold plaquetteEnergy
  rw [fullTrace_plaquetteHolonomy_gaugeTransform hg]
theorem boundaryBonds_mem_bondsInside {X : Set (FourTorus L m)} {p : Plaquette L m j}
    (hp : p ∈ (plaquettesInside X : Set (Plaquette L m j))) :
    ∀ b ∈ p.boundaryBonds, b ∈ (bondsInside X : Set (Bond L m j)) := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.boundaryBonds_mem_bondsInside <;> assumption
theorem actionNonnegAndGaugeInvariant_holds : ActionNonnegAndGaugeInvariant := by
  intro L m K _ _ _ _
  refine ⟨fun Ω₀ U g _ hU hg => ?_, fun U g hU hg => ?_⟩
  · have hb : ∀ p ∈ (plaquettesInside Ω₀ : Set (PlaquetteAtLevel L m K 0)),
        ∀ b ∈ p.boundaryBonds, U b ∈ compactGaugeGroup := fun p hp b hb =>
      hU.1 b (boundaryBonds_mem_bondsInside hp b hb)
    have hc : ∀ p ∈ (plaquettesInside Ω₀ : Set (PlaquetteAtLevel L m K 0)),
        ∀ c ∈ p.vertices, g c ∈ compactGaugeGroup := fun p hp c hc => hg c (hp c hc)
    refine ⟨fun p hp => ⟨plaquetteEnergy_nonneg (hb p hp),
      plaquetteEnergy_gaugeTransform (hc p hp) U, complexPlaquetteEnergy_nonneg (hb p hp),
      complexPlaquetteEnergy_gaugeTransform (hc p hp) U⟩, ?_, ?_, ?_, ?_⟩
    · exact finsum_nonneg fun p => finsum_nonneg fun hp => plaquetteEnergy_nonneg (hb p hp)
    · exact finsum_mem_congr rfl fun p hp => plaquetteEnergy_gaugeTransform (hc p hp) U
    · exact finsum_nonneg fun p => finsum_nonneg fun hp =>
        complexPlaquetteEnergy_nonneg (hb p hp)
    · exact finsum_mem_congr rfl fun p hp => complexPlaquetteEnergy_gaugeTransform (hc p hp) U
  · have hb : ∀ p : PlaquetteAtLevel L m K 0, ∀ b ∈ p.boundaryBonds, U b ∈ compactGaugeGroup :=
      fun _ b _ => hU.1 b (mem_univ b)
    exact ⟨finsum_nonneg fun p => plaquetteEnergy_nonneg (hb p),
      finsum_congr fun p => plaquetteEnergy_gaugeTransform (fun c _ => hg c) U⟩
end PeriodicLattice.ActionSign
end YangMills.Construction
