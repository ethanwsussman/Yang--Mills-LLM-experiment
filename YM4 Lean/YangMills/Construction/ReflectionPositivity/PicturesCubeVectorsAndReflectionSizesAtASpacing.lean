import YangMills.Construction.InfiniteLattice.DictionaryBetweenSpacings
import YangMills.Construction.ReflectionPositivity.ReflectionGroupAndCubeReflectionSize
import YangMills.Construction.ReflectionPositivity.SpectralVariablesOfTheTwoPictures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField LatticeSymmetry LatticePoint latticeSubgroup
  axisStep shift pullToUnit pushToUnit trivialField)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
open YangMills.Construction.JointSpectrum (SpectralDomain)
open YangMills.Construction.FormHilbert
def diracUnitField : unitPositiveClass :=
  haveI : T2Space (GaugeField (1 : ℝ)) :=
    inferInstanceAs (T2Space {U : YangMills.Construction.InfiniteLattice.Link (1 : ℝ) →
      YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary // _})
  ⟨Measure.dirac (trivialField 1), inferInstance, fun v A _ => by
      rw [integral_dirac, integral_dirac]
      rfl,
    fun P => ⟨inferInstance, fun H _ F _ _ _ => by
      rw [integral_dirac]
      change 0 ≤ conj (F (trivialField 1)) * F (trivialField 1)
      rw [mul_comm, Complex.mul_conj]
      exact_mod_cast Complex.normSq_nonneg _⟩⟩
variable {a : ℝ}
def unitRepresentative (m : Measure (GaugeField a)) : unitPositiveClass :=
  open Classical in
  if h : pushToUnit m ∈ unitPositiveClass then ⟨pushToUnit m, h⟩
  else diracUnitField
theorem coe_unitRepresentative {m : Measure (GaugeField a)}
    (h : pushToUnit m ∈ unitPositiveClass) :
    (unitRepresentative m : Measure (GaugeField (1 : ℝ))) = pushToUnit m := by
  rw [unitRepresentative, dif_pos h]
theorem axisReflectionGroup_mem_latticeSubgroup
    {g : Equiv.Perm YangMills.Construction.InfiniteLattice.AmbientSpace}
    (hg : g ∈ axisReflectionGroup) {x : YangMills.Construction.InfiniteLattice.AmbientSpace}
    (hx : x ∈ latticeSubgroup a) :
    g x ∈ latticeSubgroup a := by
  obtain ⟨s, hs⟩ := exists_signs_of_mem_axisReflectionGroup hg
  obtain ⟨k, hk⟩ := hx
  refine ⟨fun i => (s i : ℤ) * k i, fun i => ?_⟩
  rw [hs, hk]
  push_cast
  ring
def axisReflectionGroup.toLatticeSymmetry (a : ℝ) (γ : axisReflectionGroup) :
    LatticeSymmetry a where
  toFun := γ.1
  preservesDist := (axisReflectionGroup_isometry γ.2).1
  image_eq := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact axisReflectionGroup_mem_latticeSubgroup γ.2 hy
    · intro hx
      exact ⟨γ.1⁻¹ x, axisReflectionGroup_mem_latticeSubgroup (inv_mem γ.2) hx, by simp⟩
namespace ScaledPair
variable (m : Measure (GaugeField a)) (μ : Fin 4)
abbrev Hilb : Type := ReflectionPair.site.Hilb (unitRepresentative m) μ
def transferOp : Hilb m μ →L[ℂ] Hilb m μ :=
  ReflectionPair.site.transferOp (unitRepresentative m) μ
def shiftOp (l : TransverseAxis μ) : Hilb m μ →L[ℂ] Hilb m μ :=
  ReflectionPair.site.shiftOp (unitRepresentative m) μ l
def shiftMonomial (w : Fin 4 → ℤ) : Hilb m μ →L[ℂ] Hilb m μ :=
  ReflectionPair.site.shiftMonomial (unitRepresentative m) μ w
def jointPVM : BorelPVM (TransverseAxis μ) (Hilb m μ) :=
  ReflectionPair.site.jointPVM (unitRepresentative m) μ
def spectralMeasureOf (ψ : Hilb m μ) : Measure (SpectralDomain (TransverseAxis μ)) :=
  DirectionPictures.spectralMeasureOf μ ReflectionPair.site (unitRepresentative m) ψ
def groundProjection : Hilb m μ →L[ℂ] Hilb m μ :=
  DirectionPictures.groundProjection μ ReflectionPair.site (unitRepresentative m)
def obsClass (ha : 0 < a) (F : GaugeField a → ℂ) : Hilb m μ :=
  ReflectionPair.site.obsClass (unitRepresentative m) μ (pullToUnit ha F)
def cubeVector (ha : 0 < a) (r : ℕ+) (A : GaugeField a → ℂ) : Hilb m μ :=
  obsClass m μ ha ((shift ((r : ℕ) • axisStep a μ)).actOn A)
end ScaledPair
def scaledCubeVectorNormsSq (ha : 0 < a) (m : Measure (GaugeField a)) (r : ℕ+)
    (A : GaugeField a → ℂ) : Set ℝ :=
  Set.range fun p : Fin 4 × axisReflectionGroup =>
    ‖ScaledPair.cubeVector m p.1 ha r
      ((axisReflectionGroup.toLatticeSymmetry a p.2).actOn A)‖ ^ 2
def scaledCubeReflectionSize (ha : 0 < a) (m : Measure (GaugeField a)) (r : ℕ+)
    (A : GaugeField a → ℂ) : ℝ :=
  sSup (scaledCubeVectorNormsSq ha m r A)
theorem isGreatest_scaledCubeReflectionSize (ha : 0 < a) (m : Measure (GaugeField a)) (r : ℕ+)
    (A : GaugeField a → ℂ) :
    IsGreatest (scaledCubeVectorNormsSq ha m r A) (scaledCubeReflectionSize ha m r A) := by
  have hf : (scaledCubeVectorNormsSq ha m r A).Finite := Set.finite_range _
  exact ⟨(Set.range_nonempty _).csSup_mem hf, fun _ hs => le_csSup hf.bddAbove hs⟩
end YangMills.Construction.ReflectionPositivity.DirectionPictures
