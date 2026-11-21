import YangMills.Construction.InfiniteLattice.AllLatticeIsometriesAndTheMeanOfThePlaquetteFunctionProof
import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import YangMills.Construction.ReflectionPositivity.CovarianceAlgebraAndLocalisationOfTheRepresentativesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
structure OrientedLinkSet (a : ℝ) where
  links : Finset (Link a)
  noOpposites : GibbsAtFixedSpacing.HasNoOppositePairs (links : Set (Link a))
theorem continuous_gaugeField_eval (b : Link a) :
    Continuous fun U : GaugeField a => U b := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.continuous_eval_link <;> assumption
theorem continuous_faceEnergy (p : ElementaryPlaquette a) :
    Continuous fun U : GaugeField a => faceEnergy U p := by apply _root_.YangMills.Construction.LatticeConventions.SymmetryGeneration.continuous_faceEnergy <;> assumption
namespace OrientedLinkSet
variable (W : OrientedLinkSet a)
def faces : Set (ElementaryPlaquette a) :=
  {p | ∃ b ∈ p.edges, b ∈ W.links ∨ b.opposite ∈ W.links}
theorem faces_finite : W.faces.Finite := by
  classical
  refine (WilsonOperator.facesTouching_finite (W.links ∪ W.links.image Link.opposite)).subset ?_
  rintro p ⟨b, hb, h⟩
  refine ⟨b, hb, ?_⟩
  rcases h with h | h
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b.opposite, h, Link.opposite_opposite b⟩)
def faceCount : ℕ := W.faces.ncard
def energy (U : GaugeField a) : ℝ :=
  ∑ p ∈ W.faces_finite.toFinset, faceEnergy U p
theorem continuous_energy : Continuous W.energy := by
  unfold energy
  exact continuous_finsetSum _ fun p _ => continuous_faceEnergy p
abbrev Resample : Type := LinkVariables (W.links : Set (Link a))
def resampleHaar : Measure W.Resample := LinkVariables.haarMeasure (W.links : Set (Link a))
def glue (V : W.Resample) (U : GaugeField a) : GaugeField a :=
  GibbsAtFixedSpacing.overwriteLinks W.noOpposites V U
theorem continuous_glue (U : GaugeField a) : Continuous fun V : W.Resample => W.glue V U := by
  have hpi : Continuous fun V : W.Resample =>
      ((W.glue V U : GaugeField a) : Link a → Matrices.ComplexMatrix2.specialUnitary) := by
    refine continuous_pi fun b => ?_
    by_cases hb : b ∈ (W.links : Set (Link a))
    · have e : ∀ V : W.Resample, W.glue V U b = V ⟨b, hb⟩ := fun V => dif_pos hb
      simp only [e]
      exact continuous_apply _
    · by_cases hr : b.opposite ∈ (W.links : Set (Link a))
      · have e : ∀ V : W.Resample, W.glue V U b = (V ⟨b.opposite, hr⟩)⁻¹ := fun V =>
          (dif_neg hb).trans (dif_pos hr)
        simp only [e]
        exact (continuous_apply _).inv
      · have e : ∀ V : W.Resample, W.glue V U b = U b := fun V =>
          (dif_neg hb).trans (dif_neg hr)
        simp only [e]
        exact continuous_const
  exact Continuous.subtype_mk hpi _
def boltzmannDensity (β' : ℝ) (U : GaugeField a) (V : W.Resample) : ℝ :=
  Real.exp (-β' * W.energy (W.glue V U)) /
    ∫ V' : W.Resample, Real.exp (-β' * W.energy (W.glue V' U)) ∂W.resampleHaar
def heatBath (β' : ℝ) (F : GaugeField a → ℂ) (U : GaugeField a) : ℂ :=
  ∫ V : W.Resample, F (W.glue V U) * (W.boltzmannDensity β' U V : ℂ) ∂W.resampleHaar
end OrientedLinkSet
end InfiniteLattice
end YangMills.Construction
