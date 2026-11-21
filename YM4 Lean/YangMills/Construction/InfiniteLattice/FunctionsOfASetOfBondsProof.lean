import YangMills.Construction.InfiniteLattice.FactsOfTheBondsConfigurationsAndMotionsAtOneSpacing
import YangMills.Construction.InfiniteLattice.FunctionsOfASetOfBonds
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice.LinkSetFunctions
open YangMills.Construction.FixedSpacing (Params IsBorelMeasurableFn)
open YangMills.Construction.InfiniteLattice.OneSpacing
  (FieldBorelGenerated TorusFieldBorelGenerated FieldSplitting TorusFieldSplitting)
section ConfigurationSpace
variable {C B : Type}
@[reducible] def linkSigma (link : C → B → Matrices.ComplexMatrix2.specialUnitary) (S : Set B) :
    MeasurableSpace C :=
  ⨆ b ∈ S, MeasurableSpace.comap (fun U => link U b) inferInstance
def restrictLinks (link : C → B → Matrices.ComplexMatrix2.specialUnitary) (S : Set B) (U : C) :
    S → Matrices.ComplexMatrix2.specialUnitary :=
  fun b => link U b
theorem linkSigma_le_comap (link : C → B → Matrices.ComplexMatrix2.specialUnitary) (S : Set B) :
    linkSigma link S ≤
      MeasurableSpace.comap (restrictLinks link S) MeasurableSpace.pi := by
  refine iSup₂_le fun b hb => ?_
  have hlink : (fun U => link U b) =
      (fun W : S → Matrices.ComplexMatrix2.specialUnitary => W ⟨b, hb⟩) ∘ restrictLinks link S := rfl
  rw [hlink, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply (⟨b, hb⟩ : S)).comap_le
theorem eq_of_measurable_linkSigma (link : C → B → Matrices.ComplexMatrix2.specialUnitary)
    (S : Set B) {F : C → ℂ}
    (hF : Measurable[linkSigma link S] F) {U U' : C}
    (hUU' : restrictLinks link S U = restrictLinks link S U') : F U = F U' := by
  have hmeas : MeasurableSet[linkSigma link S] (F ⁻¹' {F U}) := hF (measurableSet_singleton (F U))
  obtain ⟨A, -, hA⟩ := linkSigma_le_comap link S _ hmeas
  have hU : restrictLinks link S U ∈ A := by
    exact show U ∈ restrictLinks link S ⁻¹' A from by
      rw [hA]
      exact Set.mem_singleton (F U)
  have hU' : U' ∈ restrictLinks link S ⁻¹' A := by
    show restrictLinks link S U' ∈ A
    rw [← hUU']
    exact hU
  rw [hA] at hU'
  have h : F U' ∈ ({F U} : Set ℂ) := hU'
  exact (Set.mem_singleton_iff.mp h).symm
theorem measurable_restrictLinks (link : C → B → Matrices.ComplexMatrix2.specialUnitary)
    (S : Set B) :
    @Measurable _ _ (linkSigma link S) MeasurableSpace.pi (restrictLinks link S) := by
  let _ : MeasurableSpace C := linkSigma link S
  refine measurable_pi_iff.mpr fun b => ?_
  exact measurable_iff_comap_le.mpr (le_iSup₂_of_le b.1 b.2 le_rfl)
theorem continuous_measurable_borel {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) : Measurable[borel X, borel Y] f := by
  borelize X Y
  exact hf.measurable
theorem factor_through_restriction [TopologicalSpace C]
    (link : C → B → Matrices.ComplexMatrix2.specialUnitary) (S : Set B)
    (ext : (S → Matrices.ComplexMatrix2.specialUnitary) → C) (hext : Continuous ext)
    (hright : ∀ W, restrictLinks link S (ext W) = W)
    (hpi : borel (S → Matrices.ComplexMatrix2.specialUnitary) =
      @MeasurableSpace.pi S (fun _ => Matrices.ComplexMatrix2.specialUnitary)
        (fun _ => borel Matrices.ComplexMatrix2.specialUnitary))
    {F : C → ℂ} (hF : IsBoundedBorel F) :
    (Measurable[linkSigma link S] F ↔
        ∀ U U', restrictLinks link S U = restrictLinks link S U' → F U = F U') ∧
      ((∀ U U', restrictLinks link S U = restrictLinks link S U' → F U = F U') →
        (∀ U, F U = F (ext (restrictLinks link S U))) ∧
          IsBoundedBorel (fun W => F (ext W)) ∧
            (Continuous F → Continuous fun W => F (ext W))) := by
  obtain ⟨hFm, c, hc⟩ := hF
  have hfactor : (∀ U U', restrictLinks link S U = restrictLinks link S U' → F U = F U') →
      ∀ U, F U = F (ext (restrictLinks link S U)) := fun h U => h _ _ (hright _).symm
  have hF' : Measurable[borel C, borel ℂ] F := hFm
  have hext' : Measurable[borel (S → Matrices.ComplexMatrix2.specialUnitary), borel C] ext :=
    continuous_measurable_borel hext
  have hΦ : Measurable[borel (S → Matrices.ComplexMatrix2.specialUnitary), borel ℂ]
      (fun W => F (ext W)) := hF'.comp hext'
  have hΦ' : @Measurable _ ℂ
      (@MeasurableSpace.pi S (fun _ => Matrices.ComplexMatrix2.specialUnitary)
        (fun _ => borel Matrices.ComplexMatrix2.specialUnitary)) (borel ℂ)
      (fun W => F (ext W)) := by
    rw [← hpi]
    exact hΦ
  refine ⟨⟨fun h U U' hU => eq_of_measurable_linkSigma link S h hU, fun h => ?_⟩,
    fun h => ⟨hfactor h, ⟨hΦ, c, fun W => hc _⟩, fun hFc => hFc.comp hext⟩⟩
  have hkey : Measurable[linkSigma link S] ((fun W => F (ext W)) ∘ restrictLinks link S) :=
    hΦ'.comp (measurable_restrictLinks link S)
  have hcomp : ((fun W => F (ext W)) ∘ restrictLinks link S) = F := (funext (hfactor h)).symm
  rw [hcomp] at hkey
  exact hkey
end ConfigurationSpace
theorem infiniteCase_holds (hfacts : OneSpacing.AllFacts) (D : Params) : InfiniteCase D := by
  have h := hfacts D.toStandingParameters
  have hsplit : FieldSplitting (mesh_pos D) := h.2.2.1
  have hborel : FieldBorelGenerated D.mesh := h.2.1
  intro S hS F hF
  have hq := (hsplit S hS).2.2.1
  have hp : Continuous fun W : LinkVariables S => (W, trivialField D.mesh) :=
    continuous_id.prodMk continuous_const
  have hcont : Continuous fun W : LinkVariables S =>
      gluedField (mesh_pos D) hS W (trivialField D.mesh) := hq.comp hp
  have hright : ∀ W : LinkVariables S,
      restrictLinks (fun (U : GaugeField D.mesh) b => U b) S
        (gluedField (mesh_pos D) hS W (trivialField D.mesh)) = W :=
    fun W => (hsplit S hS).2.2.2.2 W _
  have hbounded : IsBoundedBorel F := ⟨hF.1, hF.2⟩
  exact factor_through_restriction (fun (U : GaugeField D.mesh) b => U b) S
    (fun W => gluedField (mesh_pos D) hS W (trivialField D.mesh)) hcont hright
    (hborel.1 S hS).1 hbounded
theorem periodicCase_holds (hfacts : OneSpacing.AllFacts) (D : Params) : PeriodicCase D := by
  have h := hfacts D.toStandingParameters
  have hsplit : TorusFieldSplitting (two_le_L D) (neg_m_lt_K D) := h.2.2.2.2.2.2.2.2.1
  have hborel : TorusFieldBorelGenerated D.L D.m (D.K : ℕ) := h.2.2.2.2.2.2.2.1
  intro S hS F hF
  have hq := (hsplit S hS).2.2.1
  have hp : Continuous fun W : LinkVariables S =>
      (W, PeriodicLattice.CompactGaugeField.identity D.L D.m (D.K : ℕ)) :=
    continuous_id.prodMk continuous_const
  have hcont : Continuous fun W : LinkVariables S =>
      PeriodicLattice.CompactGaugeField.glue (two_le_L D) (neg_m_lt_K D) hS W
        (PeriodicLattice.CompactGaugeField.identity D.L D.m (D.K : ℕ)) := hq.comp hp
  have hright : ∀ W : LinkVariables S,
      restrictLinks
        (fun (U : PeriodicLattice.CompactGaugeField D.L D.m (D.K : ℕ)) b => U.linkValue b) S
        (PeriodicLattice.CompactGaugeField.glue (two_le_L D) (neg_m_lt_K D) hS W
          (PeriodicLattice.CompactGaugeField.identity D.L D.m (D.K : ℕ))) = W :=
    fun W => (hsplit S hS).2.2.2.2 W _
  exact factor_through_restriction
    (fun (U : PeriodicLattice.CompactGaugeField D.L D.m (D.K : ℕ)) b => U.linkValue b) S
    (fun W => PeriodicLattice.CompactGaugeField.glue (two_le_L D) (neg_m_lt_K D) hS W
      (PeriodicLattice.CompactGaugeField.identity D.L D.m (D.K : ℕ))) hcont hright
    (hborel.1 S hS).1 hF
theorem claim_holds (hfacts : OneSpacing.AllFacts) : Claim :=
  fun D => ⟨infiniteCase_holds hfacts D, periodicCase_holds hfacts D⟩
end YangMills.Construction.InfiniteLattice.LinkSetFunctions
