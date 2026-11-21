import YangMills.Construction.InfiniteLattice.PeriodLatticesToriAndTheirWilsonMeasures
import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
namespace PeriodSublattice
variable {a : ℝ} (Γ : PeriodSublattice a)
abbrev QuotientTorus : Type := LatticePoint a ⧸ Γ.periods
def quotientMap : LatticePoint a →+ Γ.QuotientTorus := QuotientAddGroup.mk' Γ.periods
def faceClass (p : ElementaryPlaquette a) : Γ.QuotientPlaquette := ⟨Γ.plaquetteOrbit p, p, rfl⟩
theorem quotientLink_nonempty (c : Γ.QuotientLink) : (c : Set (PositiveLink a)).Nonempty := by
  obtain ⟨_, b, rfl⟩ := c
  exact ⟨_, 0, zero_mem _, rfl⟩
def linkRep (c : Γ.QuotientLink) : PositiveLink a := (Γ.quotientLink_nonempty c).some
def plaquetteRep (p : Γ.QuotientPlaquette) : ElementaryPlaquette a :=
  (Γ.quotientPlaquette_nonempty p).some
def linkEndpoints (c : Γ.QuotientLink) : Set Γ.QuotientTorus :=
  {Γ.quotientMap (Γ.linkRep c).1.initial, Γ.quotientMap (Γ.linkRep c).1.terminal}
def plaquetteVertices (p : Γ.QuotientPlaquette) : Set Γ.QuotientTorus :=
  Γ.quotientMap '' (Γ.plaquetteRep p).cornerSet
def plaquetteLinks (p : Γ.QuotientPlaquette) : Set Γ.QuotientLink :=
  {c | ∃ b : PositiveLink a, b.1 ∈ (Γ.plaquetteRep p).linkSet ∧ c = Γ.linkClass b}
end PeriodSublattice
structure LocalObservableArray where
  sublattice : AddSubgroup (LatticePoint 1)
  sublattice_finiteIndex : sublattice.FiniteIndex
  size : ℕ
  one_le_size : 1 ≤ size
  gen : Fin size → GaugeField 1 → ℂ
  gen_mem : ∀ ι, gen ι ∈ continuousLocalFunctions 1
  gen_im : ∀ ι U, (gen ι U).im = 0
namespace LocalObservableArray
variable (𝔸 : LocalObservableArray)
abbrev Label : Type := 𝔸.sublattice × Fin 𝔸.size
def translate (i : 𝔸.Label) : GaugeField 1 → ℂ :=
  (shift (i.1 : LatticePoint 1)).actOn (𝔸.gen i.2)
def labelsTouching (W : LinkWindow 1) : Set 𝔸.Label :=
  {i | (observableSupport (𝔸.translate i) ∩ (W.links : Set (Link 1))).Nonempty}
def windowEnergy (β t : ℝ) (W : LinkWindow 1) (U : GaugeField 1) : ℝ :=
  β * ∑ᶠ p ∈ facesMeeting (W.links : Set (Link 1)), faceEnergy U p -
    t * ∑ᶠ i ∈ 𝔸.labelsTouching W, (𝔸.translate i U).re
def windowPartition (β t : ℝ) (W : LinkWindow 1) (U : GaugeField 1) : ℝ :=
  ∫ V, Real.exp (-𝔸.windowEnergy β t W (W.glue one_pos V U)) ∂W.haarProd
def tiltedKernel (β t : ℝ) (W : LinkWindow 1) (F : GaugeField 1 → ℂ)
    (U : GaugeField 1) : ℂ :=
  (∫ V, F (W.glue one_pos V U) *
      (Real.exp (-𝔸.windowEnergy β t W (W.glue one_pos V U)) : ℂ) ∂W.haarProd) /
    (𝔸.windowPartition β t W U : ℂ)
def tiltedGibbsClass (β t : ℝ) : Set (Measure (GaugeField 1)) :=
  {ν | IsProbabilityMeasure ν ∧ ∀ W : LinkWindow 1, ∀ F ∈ continuousLocalFunctions 1,
    ∫ U, 𝔸.tiltedKernel β t W F U ∂ν = ∫ U, F U ∂ν}
variable (Γ : PeriodSublattice 1)
def FitsPeriods : Prop := Γ.periods ≤ 𝔸.sublattice
abbrev Cosets : Type := 𝔸.sublattice ⧸ Γ.periods.addSubgroupOf 𝔸.sublattice
def cosetRep (c : 𝔸.Cosets Γ) : 𝔸.sublattice := Quotient.out c
def periodicSum (U : Γ.QuotientField) : ℝ :=
  ∑ᶠ i : 𝔸.Cosets Γ × Fin 𝔸.size,
    (Γ.periodize (𝔸.translate (𝔸.cosetRep Γ i.1, i.2)) U).re
def tiltedWeight (β t : ℝ) (U : Γ.QuotientField) : ℝ :=
  Real.exp (t * 𝔸.periodicSum Γ U - β * ∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p)
def tiltedPartition (β t : ℝ) : ℝ := ∫ U, 𝔸.tiltedWeight Γ β t U ∂Γ.quotientHaar
def tiltedMeasure (β t : ℝ) : Measure Γ.QuotientField :=
  (ENNReal.ofReal (𝔸.tiltedPartition Γ β t))⁻¹ •
    Γ.quotientHaar.withDensity fun U => ENNReal.ofReal (𝔸.tiltedWeight Γ β t U)
def tiltedLiftMeasure (β t : ℝ) : Measure (GaugeField 1) :=
  (𝔸.tiltedMeasure Γ β t).map Γ.lift
end LocalObservableArray
end InfiniteLattice
end YangMills.Construction
