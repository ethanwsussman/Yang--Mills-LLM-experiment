import YangMills.Construction.Lattice.WeightedWilsonActions
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Matrices
namespace ComplexMatrix2
theorem fullTrace_im_eq_zero_of_mem_specialUnitary {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    (fullTrace W).im = 0 := by
  have hdet : W.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp hW).2
  have huni : W ∈ Matrix.unitaryGroup (Fin 2) ℂ := (Matrix.mem_specialUnitaryGroup_iff.mp hW).1
  have hstar : star W * W = 1 := Matrix.mem_unitaryGroup_iff'.mp huni
  have hadj : star W = Matrix.adjugate W := by
    have h := congrArg (· * Matrix.adjugate W) hstar
    simp only [Matrix.mul_assoc, Matrix.mul_adjugate, hdet, one_smul, mul_one, one_mul] at h
    exact h
  have h00 := congrFun (congrFun hadj 0) 0
  simp [Matrix.adjugate_fin_two, Matrix.star_apply] at h00
  have h := congrArg Complex.im h00
  simp [Matrix.trace_fin_two] at h ⊢
  linarith
end ComplexMatrix2
end Matrices
namespace PeriodicLattice
variable {L m : ℕ} {k : ℤ}
theorem plaquetteHolonomy_mem_specialUnitary {U : Bond L m k → Matrices.ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m k) (p : Plaquette L m k) :
    plaquetteHolonomy U p ∈ Matrices.ComplexMatrix2.specialUnitary := by
  refine Submonoid.list_prod_mem _ ?_
  intro x hx
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
  exact hU.1 v (Set.mem_univ v)
theorem complexEnergy_eq_realEnergy {U : Bond L m k → Matrices.ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m k) (p : Plaquette L m k) :
    plaquetteEnergy U p = (plaquetteCost U p : ℂ) := by
  have him := Matrices.ComplexMatrix2.fullTrace_im_eq_zero_of_mem_specialUnitary
    (plaquetteHolonomy_mem_specialUnitary hU p)
  apply Complex.ext <;> simp [plaquetteEnergy, plaquetteCost, him]
end PeriodicLattice
end YangMills.Construction
end
