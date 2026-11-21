import YangMills.Construction.InfiniteLattice.AllLatticeIsometriesAndTheMeanOfThePlaquetteFunctionProof
import YangMills.Construction.InfiniteLattice.AllMirrorsOfPeriodicGibbsStates
import YangMills.Construction.InfiniteLattice.OneMeanPlaquetteEnergy
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Matrix
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace MeanFaceEnergy
variable {a : ℝ}
theorem exists_perm_zero_one {μ l : Fin 4} (hne : μ ≠ l) :
    ∃ w : Equiv.Perm (Fin 4), w 0 = μ ∧ w 1 = l := by
  have hsw : Equiv.swap 0 μ l ≠ 0 := by
    intro hsw
    apply hne
    have := congrArg (Equiv.swap 0 μ) hsw
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact this.symm
  refine ⟨Equiv.swap 0 μ * Equiv.swap 1 (Equiv.swap 0 μ l), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hsw.symm,
      Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]
def coordPerm (w : Equiv.Perm (Fin 4)) : AmbientSpace →ₗ[ℝ] AmbientSpace :=
  LinearMap.funLeft ℝ ℝ w.symm
theorem coordPerm_mem_hypercubicGroup (w : Equiv.Perm (Fin 4)) :
    coordPerm w ∈ hypercubicGroup :=
  ⟨w, fun κ => Or.inl (by
    funext ν
    simp [coordPerm, LinearMap.funLeft_apply, basisVector, Pi.single_apply,
      Equiv.symm_apply_eq])⟩
def permMotion (w : Equiv.Perm (Fin 4)) (x : LatticePoint a) : latticeMotions a :=
  ⟨fun y => coordPerm w y + x,
    coordPerm w, coordPerm_mem_hypercubicGroup w, x, x.2, fun _ => rfl⟩
theorem permMotion_pointMap_zero (w : Equiv.Perm (Fin 4)) (x : LatticePoint a) :
    (latticeMotionSymmetry (permMotion w x)).pointMap 0 = x := by
  refine Subtype.ext (funext fun κ => ?_)
  change (0 : AmbientSpace) (w.symm κ) + (x : AmbientSpace) κ = (x : AmbientSpace) κ
  simp
theorem permMotion_pointMap_add_axisStep (w : Equiv.Perm (Fin 4)) (x y : LatticePoint a)
    (μ : Fin 4) :
    (latticeMotionSymmetry (permMotion w x)).pointMap (y + axisStep a μ) =
      (latticeMotionSymmetry (permMotion w x)).pointMap y + axisStep a (w μ) := by
  refine Subtype.ext (funext fun κ => ?_)
  change (y : AmbientSpace) (w.symm κ) + (Pi.single μ a : AmbientSpace) (w.symm κ) +
      (x : AmbientSpace) κ =
    (y : AmbientSpace) (w.symm κ) + (x : AmbientSpace) κ + (Pi.single (w μ) a : AmbientSpace) κ
  have hs : (Pi.single μ a : AmbientSpace) (w.symm κ) = (Pi.single (w μ) a : AmbientSpace) κ := by
    simp only [Pi.single_apply, Equiv.symm_apply_eq]
  rw [hs]
  ring
theorem permMotion_linkMap_forwardFrom (w : Equiv.Perm (Fin 4)) (x y : LatticePoint a)
    (μ : Fin 4) :
    (latticeMotionSymmetry (permMotion w x)).linkMap (Link.forwardFrom y μ) =
      Link.forwardFrom ((latticeMotionSymmetry (permMotion w x)).pointMap y) (w μ) :=
  Link.ext rfl (permMotion_pointMap_add_axisStep w x y μ)
def basePlaquette (a : ℝ) : ElementaryPlaquette a := ⟨0, 0, 1, by decide⟩
theorem faceHolonomy_pullbackField_permMotion (w : Equiv.Perm (Fin 4))
    (p : ElementaryPlaquette a) (h0 : w 0 = p.lowAxis) (h1 : w 1 = p.highAxis)
    (U : GaugeField a) :
    faceHolonomy ((latticeMotionSymmetry (permMotion w p.corner)).pullbackField U)
      (basePlaquette a) = faceHolonomy U p := by
  change U ((latticeMotionSymmetry (permMotion w p.corner)).linkMap _) *
      U ((latticeMotionSymmetry (permMotion w p.corner)).linkMap _) *
      (U ((latticeMotionSymmetry (permMotion w p.corner)).linkMap _))⁻¹ *
      (U ((latticeMotionSymmetry (permMotion w p.corner)).linkMap _))⁻¹ = _
  simp only [basePlaquette, permMotion_linkMap_forwardFrom, permMotion_pointMap_add_axisStep,
    permMotion_pointMap_zero, h0, h1]
  rfl
theorem isBoundedObservable_faceEnergy (p : ElementaryPlaquette a) :
    IsBoundedObservable fun U : GaugeField a => ((faceEnergy U p : ℝ) : ℂ) := by apply _root_.YangMills.Construction.LatticeConventions.SymmetryGeneration.isBoundedObservable_faceEnergy <;> assumption
theorem stateEval_faceEnergy_eq_base {ν : Measure (GaugeField a)}
    (hν : ∀ r : latticeMotions a, IsSymmetricUnder ν (latticeMotionSymmetry r))
    (p : ElementaryPlaquette a) :
    stateEval ν (fun U : GaugeField a => faceEnergy U p) =
      stateEval ν (fun U : GaugeField a => faceEnergy U (basePlaquette a)) := by
  have hlt : p.lowAxis < p.highAxis := by
    cases p
    assumption
  obtain ⟨w, h0, h1⟩ := exists_perm_zero_one hlt.ne
  have hsym := hν (permMotion w p.corner) _ (isBoundedObservable_faceEnergy (basePlaquette a))
  have hpull : (fun U : GaugeField a =>
      (latticeMotionSymmetry (permMotion w p.corner)).actOn
        (fun U : GaugeField a => ((faceEnergy U (basePlaquette a) : ℝ) : ℂ)) U) =
      fun U : GaugeField a => ((faceEnergy U p : ℝ) : ℂ) := by
    funext U
    change ((1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (faceHolonomy
      ((latticeMotionSymmetry (permMotion w p.corner)).pullbackField U)
        (basePlaquette a) : Matrices.ComplexMatrix2)).re : ℝ) : ℂ) = _
    rw [faceHolonomy_pullbackField_permMotion w p h0 h1]
    rfl
  have hreal : ∀ q : ElementaryPlaquette a,
      ∫ U : GaugeField a, ((faceEnergy U q : ℝ) : ℂ) ∂ν =
        ((∫ U : GaugeField a, faceEnergy U q ∂ν : ℝ) : ℂ) :=
    fun q => integral_complex_ofReal
      (f := fun U : GaugeField a => faceEnergy U q)
  rw [hpull, hreal, hreal] at hsym
  exact Complex.ofReal_injective hsym
end MeanFaceEnergy
theorem meanFaceEnergyIsUniform_of_periodicGibbsSymmetries
    (hAll : PeriodicGibbsSymmetries.Statement) :
    MeanFaceEnergyIsUniform := by
  intro a ha β hβ ν hν p p'
  have hinv := ((hAll a ha β hβ).1 ν hν).1
  rw [MeanFaceEnergy.stateEval_faceEnergy_eq_base hinv p,
    MeanFaceEnergy.stateEval_faceEnergy_eq_base hinv p']
end YangMills.Construction.InfiniteLattice
end
