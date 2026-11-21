import YangMills.Construction.Lattice.Cochains
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace Gaussian
section Measures
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
def basisImageMeasure {n : ℕ} (v : Fin n → V) : Measure V :=
  (volume : Measure (Fin n → ℝ)).map fun t => ∑ i, t i • v i
variable (V) in
def lebesgueVolume : Measure V := basisImageMeasure (stdOrthonormalBasis ℝ V)
variable (V) in
def gaussianConstant : ℝ := ∫ ω, Real.exp (-‖ω‖ ^ 2 / 2) ∂lebesgueVolume V
variable (V) in
def stdGaussian : Measure V :=
  (lebesgueVolume V).withDensity fun ω =>
    ENNReal.ofReal (Real.exp (-‖ω‖ ^ 2 / 2) / gaussianConstant V)
end Measures
end Gaussian
namespace PeriodicLattice
open YangMills.Construction.Gaussian
variable {L m : ℕ} {j : ℤ}
instance [Finite (Site L m j)] : Finite (Plaquette L m j) :=
  Finite.of_injective (fun p : Plaquette L m j => (p.origin, p.firstAxis, p.secondAxis))
    fun p q h => by
      simp only [Prod.mk.injEq] at h
      exact Plaquette.ext h.1 h.2.1 h.2.2
def ExactPlaquetteCochain (L m : ℕ) (j : ℤ) : Type := ↥(exactPlaquetteCochains L m j)
namespace ExactPlaquetteCochain
instance : AddCommGroup (ExactPlaquetteCochain L m j) :=
  inferInstanceAs (AddCommGroup ↥(exactPlaquetteCochains L m j))
instance : Module ℝ (ExactPlaquetteCochain L m j) :=
  inferInstanceAs (Module ℝ ↥(exactPlaquetteCochains L m j))
def toCochain : ExactPlaquetteCochain L m j →ₗ[ℝ] PlaquetteCochain L m j :=
  (exactPlaquetteCochains L m j).subtype
instance : CoeFun (ExactPlaquetteCochain L m j) fun _ => Plaquette L m j → ℝ :=
  ⟨fun ω => toCochain ω⟩
theorem toCochain_injective : Function.Injective (toCochain : ExactPlaquetteCochain L m j → _) :=
  Subtype.val_injective
variable [Finite (Plaquette L m j)]
@[instance_reducible]
def innerProductCore : InnerProductSpace.Core ℝ (ExactPlaquetteCochain L m j) where
  inner ω ω' := plaquetteInner (toCochain ω) (toCochain ω')
  conj_inner_symm ω ω' := by
    have := Fintype.ofFinite (Plaquette L m j)
    simp only [conj_trivial, plaquetteInner, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  re_inner_nonneg ω := by
    have := Fintype.ofFinite (Plaquette L m j)
    simp only [RCLike.re_to_real, plaquetteInner, finsum_eq_sum_of_fintype]
    exact Finset.sum_nonneg fun p _ => mul_self_nonneg _
  add_left ω ω' ω'' := by
    have := Fintype.ofFinite (Plaquette L m j)
    simp only [map_add, plaquetteInner, finsum_eq_sum_of_fintype, Pi.add_apply, add_mul,
      Finset.sum_add_distrib]
  smul_left ω ω' c := by
    have := Fintype.ofFinite (Plaquette L m j)
    simp only [map_smul, plaquetteInner, finsum_eq_sum_of_fintype, Pi.smul_apply, smul_eq_mul,
      conj_trivial, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  definite ω h := by
    have := Fintype.ofFinite (Plaquette L m j)
    simp only [plaquetteInner, finsum_eq_sum_of_fintype] at h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun p _ => mul_self_nonneg _).mp h
    refine toCochain_injective (funext fun p => ?_)
    simpa using hz p (Finset.mem_univ p)
instance : NormedAddCommGroup (ExactPlaquetteCochain L m j) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (ExactPlaquetteCochain L m j) _ _ _
    innerProductCore
instance : InnerProductSpace ℝ (ExactPlaquetteCochain L m j) :=
  InnerProductSpace.ofCore innerProductCore.toCore
instance : FiniteDimensional ℝ (ExactPlaquetteCochain L m j) :=
  inferInstanceAs (FiniteDimensional ℝ ↥(exactPlaquetteCochains L m j))
instance : MeasurableSpace (ExactPlaquetteCochain L m j) := borel _
end ExactPlaquetteCochain
section FreeField
variable [Finite (Plaquette L m j)]
variable (L m j) in
def freeCurvatureLaw : Measure (ExactPlaquetteCochain L m j) :=
  stdGaussian (ExactPlaquetteCochain L m j)
def IsBorelObservable (f : ExactPlaquetteCochain L m j → ℝ) : Prop := Measurable f
def freeMean (f : ExactPlaquetteCochain L m j → ℝ) : ℝ := ∫ ω, f ω ∂freeCurvatureLaw L m j
def freeLMean (f : ExactPlaquetteCochain L m j → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, f ω ∂freeCurvatureLaw L m j
def freeCurvatureMap : ExactPlaquetteCochain L m j → ExactPlaquetteCochain L m j := id
def freeCurvatureAtPlaquette (p : Plaquette L m j) (ω : ExactPlaquetteCochain L m j) : ℝ :=
  freeCurvatureMap ω p
def freeGaugePotential (ω : ExactPlaquetteCochain L m j) : bondCochains L m j :=
  Function.invFunOn bondDifferential (closedBondCochainsOrth L m j)
    (ExactPlaquetteCochain.toCochain (freeCurvatureMap ω))
end FreeField
end PeriodicLattice
end YangMills.Construction
