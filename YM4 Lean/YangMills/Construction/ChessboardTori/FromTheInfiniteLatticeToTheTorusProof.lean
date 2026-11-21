import YangMills.Construction.ChessboardTori.CellFunctionFamiliesInTheTransferPictureProof
import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivityProof
import YangMills.Construction.ChessboardTori.ChessboardNumberAcrossBoxesProof
import YangMills.Construction.ChessboardTori.FromTheInfiniteLatticeToTheTorus
import YangMills.Construction.Lattice.SiteAndPlaquetteCounts
import Mathlib
set_option autoImplicit false
open Set MeasureTheory Function
noncomputable section
namespace YangMills.Construction.ChessboardTori.TorusReduction
open InfiniteLattice (AmbientSpace)
open TestFunctions (latticeTranslate)
section Measure
variable (D : ChessboardSetup)
theorem ae_mem_compactGaugeFields_haar (hCount : PeriodicLattice.SiteAndPlaquetteCounts) :
    ∀ᵐ U ∂(PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)),
      U ∈ D.compactFields := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hL1 : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  have hL : 0 < D.L := by omega
  have hm : -((D.m : ℕ) : ℤ) ≤ ((D.K : ℕ) : ℤ) := by omega
  have hm' : 0 < ((D.m : ℕ) : ℤ) + ((D.K : ℕ) : ℤ) := by
    have h1 := D.m.pos
    have h2 := D.K.pos
    omega
  obtain ⟨-, -, -, -, -, h⟩ := hCount D.L D.m ((D.K : ℕ) : ℤ) hL hm
  obtain ⟨-, -, hrange, -, -⟩ := h hL1 hm'
  have hclosed : MeasurableSet (PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)) :=
    (PeriodicLattice.isClosed_compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)).measurableSet
  have hmeas : Measurable (PeriodicLattice.gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond D.L D.m ((D.K : ℕ) : ℤ) →
          Matrices.ComplexMatrix2.specialUnitary) →
        PeriodicLattice.Bond D.L D.m ((D.K : ℕ) : ℤ) → Matrices.ComplexMatrix2) := by
    have hval : Measurable fun g : Matrices.ComplexMatrix2.specialUnitary =>
        (g : Matrices.ComplexMatrix2) := continuous_subtype_val.measurable
    have hinv : Measurable fun g : Matrices.ComplexMatrix2.specialUnitary =>
        (g : Matrices.ComplexMatrix2)⁻¹ := by
      have e : (fun g : Matrices.ComplexMatrix2.specialUnitary => (g : Matrices.ComplexMatrix2)⁻¹) =
          fun g => ((g⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) :=
        funext fun g => (InfiniteLattice.specialUnitary_coe_inv g).symm
      rw [e]
      exact (continuous_subtype_val.comp continuous_inv).measurable
    refine measurable_pi_iff.2 fun b => ?_
    unfold PeriodicLattice.gaugeFieldOfPositive
    by_cases hpos : b.IsPositivelyOriented
    · simp only [dif_pos hpos]
      exact hval.comp (measurable_pi_apply _)
    · by_cases hpos' : b.opposite.IsPositivelyOriented
      · simp only [dif_neg hpos, dif_pos hpos']
        exact hinv.comp (measurable_pi_apply _)
      · simp only [dif_neg hpos, dif_neg hpos']
        exact measurable_const
  unfold PeriodicLattice.productHaarMeasure
  refine (ae_map_iff
    (p := fun U => U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ))
    hmeas.aemeasurable hclosed).2 (ae_of_all _ fun g => ?_)
  rw [← hrange]
  exact mem_range_self g
theorem ae_mem_compactFields (hCount : PeriodicLattice.SiteAndPlaquetteCounts) :
    ∀ᵐ U ∂(PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β), U ∈ D.compactFields := by
  have hac : PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β ≪
      PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ) := by
    unfold PeriodicLattice.wilsonGibbsMeasure
    exact (withDensity_absolutelyContinuous _ _).smul_left _
  exact hac.ae_le (ae_mem_compactGaugeFields_haar D hCount)
theorem periodicExpectation_congr (hCount : PeriodicLattice.SiteAndPlaquetteCounts)
    {F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} (h : D.AgreeOnCompactFields F F') :
    D.periodicExpectation F = D.periodicExpectation F' :=
  integral_congr_ae ((ae_mem_compactFields D hCount).mono fun U hU => h U hU)
theorem liftedExpectation_eq {H : D.GaugeField → ℂ} (hH : Measurable H) :
    D.liftedExpectation H = D.periodicExpectation (D.liftedObservable H) :=
  integral_map
    (InfiniteLattice.measurable_liftField D.L D.m ((D.K : ℕ) : ℤ)).aemeasurable
    hH.aestronglyMeasurable
end Measure
section Links
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def translateSite (D : ChessboardSetup) (k : Fin 4 → ℤ) : InfiniteLattice.LatticePoint D.mesh :=
  ⟨latticeTranslate D.torusPeriod k, fun μ => 2 * (D.L : ℤ) ^ ((D.m : ℕ) + (D.K : ℕ)) * k μ,
    fun μ => by
    have hL : 0 < D.L := by
      have := D.isAdmissible.2
      omega
    have h := SourcesAndGluing.torusSide_eq_intCast_mul_meshSize hL D.m D.K
    have h' : D.torusPeriod = ((2 * (D.L : ℤ) ^ ((D.m : ℕ) + (D.K : ℕ)) : ℤ) : ℝ) * D.mesh := h
    simp only [latticeTranslate]
    rw [h']
    push_cast
    ring⟩
theorem cellSide_pos : 0 < g.cellSide := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.cellSide_pos <;> assumption
theorem two_mul_mesh_le_cellSide : 2 * D.mesh ≤ g.cellSide := by
  rw [g.cellSide_eq]
  have h : (2 : ℝ) ≤ g.cellRatio := by exact_mod_cast g.two_le_cellRatio
  have hmesh := D.mesh_pos
  nlinarith
theorem cell_subset_block (hside : 2 * g.cellSide ≤ D.torusPeriod) (k : Fin 4 → ℤ) :
    g.cell k ⊆ g.block k := by
  have := cellSide_pos g
  intro x hx μ
  exact ⟨(hx μ).1, (hx μ).2.trans (by change g.cellSide ≤ D.torusPeriod; linarith)⟩
theorem torusCellInterior_image (hsame : g.SameTorusImageCriterion) {S : Set AmbientSpace}
    (hS : S ∈ g.cellSet) : g.torusCellInterior (D.proj '' S) = D.proj '' interior S := by
  obtain ⟨h1, h2⟩ := Classical.epsilon_spec
    (p := fun S' : Set AmbientSpace => S' ∈ g.cellSet ∧ D.proj '' S' = D.proj '' S)
    ⟨S, hS, rfl⟩
  change D.proj '' interior (g.liftCell (D.proj '' S)) = _
  change g.liftCell (D.proj '' S) ∈ g.cellSet at h1
  change D.proj '' g.liftCell (D.proj '' S) = _ at h2
  obtain ⟨k, rfl⟩ := hS
  obtain ⟨k', hk'⟩ := h1
  rw [← hk'] at h2 ⊢
  exact ((hsame k k').2.2 h2.symm).symm ▸ rfl
theorem bijOn_projLink (hsurj : Surjective D.projLink) (hsame : g.SameTorusImageCriterion)
    (hinj : ∀ B ∈ g.blocks, InjOn D.proj (interior B)) (hside : 2 * g.cellSide ≤ D.torusPeriod)
    {S : Set AmbientSpace} (hS : S ∈ g.cellSet) :
    BijOn D.projLink (ReflectionGrid.interiorLinks (D := D) S)
      (g.torusCellLinks (D.proj '' S)) := by
  have hopen := torusCellInterior_image g hsame hS
  refine ⟨fun b hb => ?_, fun b hb b' hb' h => ?_, fun b hb => ?_⟩
  · change ((D.projLink b).source : D.Torus) ∈ _ ∧ ((D.projLink b).target : D.Torus) ∈ _
    rw [hopen]
    exact ⟨⟨_, hb.1, rfl⟩, ⟨_, hb.2, rfl⟩⟩
  · obtain ⟨k, rfl⟩ := hS
    have hI : InjOn D.proj (interior (g.cell k)) :=
      (hinj _ ⟨k, rfl⟩).mono (interior_mono (cell_subset_block g hside k))
    have ht : D.proj (b.initial : AmbientSpace) = D.proj (b'.initial : AmbientSpace) :=
      congrArg (fun c : D.PeriodicLink => (c.source : D.Torus)) h
    have hh : D.proj (b.terminal : AmbientSpace) = D.proj (b'.terminal : AmbientSpace) :=
      congrArg (fun c : D.PeriodicLink => (c.target : D.Torus)) h
    exact InfiniteLattice.Link.ext (Subtype.ext (hI hb.1 hb'.1 ht))
      (Subtype.ext (hI hb.2 hb'.2 hh))
  · obtain ⟨b₀, rfl⟩ := hsurj b
    have hb1 : ((D.projLink b₀).source : D.Torus) ∈ D.proj '' interior S := hopen ▸ hb.1
    have hb2 : ((D.projLink b₀).target : D.Torus) ∈ D.proj '' interior S := hopen ▸ hb.2
    obtain ⟨x, hx, hxe⟩ := hb1
    obtain ⟨y, hy, hye⟩ := hb2
    obtain ⟨c, hc⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq
      (show TorusMetric.torusProj D.torusPeriod x =
        TorusMetric.torusProj D.torusPeriod (b₀.initial : AmbientSpace) from hxe)
    obtain ⟨c', hc'⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq
      (show TorusMetric.torusProj D.torusPeriod y =
        TorusMetric.torusProj D.torusPeriod (b₀.terminal : AmbientSpace) from hye)
    have hcell : ∀ ν, |y ν - x ν| ≤ g.cellSide := by
      obtain ⟨k, rfl⟩ := hS
      intro ν
      have h1 := (interior_subset hx) ν
      have h2 := (interior_subset hy) ν
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hstep : ∀ ν, |(b₀.terminal : AmbientSpace) ν - (b₀.initial : AmbientSpace) ν| ≤ D.mesh := by
      intro ν
      have hmesh := D.mesh_pos
      obtain ⟨μ, h | h⟩ := b₀.isAdjacent
      · have h' : (b₀.terminal : AmbientSpace) ν - (b₀.initial : AmbientSpace) ν =
            ((InfiniteLattice.axisStep D.mesh μ : InfiniteLattice.LatticePoint D.mesh) :
              AmbientSpace) ν :=
          congrFun (congrArg Subtype.val h) ν
        rw [h']
        by_cases hν : ν = μ
        · subst hν
          simp [InfiniteLattice.axisStep, abs_of_pos hmesh]
        · simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne hν, hmesh.le]
      · have h' : (b₀.terminal : AmbientSpace) ν - (b₀.initial : AmbientSpace) ν =
            -((InfiniteLattice.axisStep D.mesh μ : InfiniteLattice.LatticePoint D.mesh) :
              AmbientSpace) ν :=
          congrFun (congrArg Subtype.val h) ν
        rw [h']
        by_cases hν : ν = μ
        · subst hν
          simp [InfiniteLattice.axisStep, abs_of_pos hmesh]
        · simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne hν, hmesh.le]
    have hcc : c' = c := by
      funext ν
      by_contra hne
      have hj : (1 : ℝ) ≤ |((c' ν - c ν : ℤ) : ℝ)| := by
        have h0 : c' ν - c ν ≠ 0 := sub_ne_zero.mpr hne
        exact_mod_cast Int.one_le_abs h0
      have hy' : y ν = (b₀.terminal : AmbientSpace) ν + D.torusPeriod * (c' ν : ℝ) :=
        congrFun hc' ν
      have hx' : x ν = (b₀.initial : AmbientSpace) ν + D.torusPeriod * (c ν : ℝ) :=
        congrFun hc ν
      have hd : D.torusPeriod * ((c' ν - c ν : ℤ) : ℝ) =
          (y ν - x ν) - ((b₀.terminal : AmbientSpace) ν - (b₀.initial : AmbientSpace) ν) := by
        push_cast
        rw [hy', hx']
        ring
      have hper : 0 < D.torusPeriod := by linarith [cellSide_pos g]
      have h1 : D.torusPeriod ≤ |D.torusPeriod * ((c' ν - c ν : ℤ) : ℝ)| := by
        rw [abs_mul, abs_of_pos hper]
        nlinarith
      have h2 := abs_sub (y ν - x ν)
        ((b₀.terminal : AmbientSpace) ν - (b₀.initial : AmbientSpace) ν)
      rw [← hd] at h2
      have := hcell ν
      have := hstep ν
      have := two_mul_mesh_le_cellSide g
      have := cellSide_pos g
      have := D.mesh_pos
      linarith
    subst hcc
    have hsrc : ((b₀.initial + translateSite D c' : InfiniteLattice.LatticePoint D.mesh) :
        AmbientSpace) = x := hc.symm
    have htgt : ((b₀.terminal + translateSite D c' : InfiniteLattice.LatticePoint D.mesh) :
        AmbientSpace) = y := hc'.symm
    refine ⟨⟨b₀.initial + translateSite D c', b₀.terminal + translateSite D c', ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · simpa only [add_sub_add_right_eq_sub] using b₀.isAdjacent
    · change ((b₀.initial + translateSite D c' : InfiniteLattice.LatticePoint D.mesh) :
        AmbientSpace) ∈ interior S
      rw [hsrc]
      exact hx
    · change ((b₀.terminal + translateSite D c' : InfiniteLattice.LatticePoint D.mesh) :
        AmbientSpace) ∈ interior S
      rw [htgt]
      exact hy
    · refine PeriodicLattice.Bond.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · change D.proj ((b₀.initial + translateSite D c' : InfiniteLattice.LatticePoint D.mesh) :
          AmbientSpace) = _
        rw [hsrc]
        exact hxe
      · change D.proj ((b₀.terminal + translateSite D c' : InfiniteLattice.LatticePoint D.mesh) :
          AmbientSpace) = _
        rw [htgt]
        exact hye
end Links
section EvaluationMaps
variable {D : ChessboardSetup} (g : ReflectionGrid D)
structure GridFacts : Prop where
  period_ge : 2 * g.cellSide ≤ D.torusPeriod
  counts : PeriodicLattice.SiteAndPlaquetteCounts
  projSurjective : Surjective D.projLink
  sameImage : g.SameTorusImageCriterion
  injOn : ∀ B ∈ g.blocks, InjOn D.proj (interior B)
  free : ∀ S ∈ g.cellSet, ∀ S' ∈ g.cellSet, ∃! r : g.reflectionGroup, r.1 '' S = S'
  induced : ∀ r ∈ g.reflectionGroup, ∃ r' : D.Torus → D.Torus,
    D.proj ∘ r = r' ∘ D.proj ∧ D.IsTorusDistPreserving r'
  sign : ∀ r ∈ g.reflectionGroup, ∀ s ∈ g.reflectionGroup, ∀ r' : D.Torus → D.Torus,
    D.proj ∘ r = r' ∘ D.proj → D.proj ∘ s = r' ∘ D.proj →
      orientationSign r = orientationSign s
  torusFree : ∀ C ∈ g.torusCellSet, ∀ C' ∈ g.torusCellSet,
    ∃! r', r' ∈ g.inducedTorusMaps ∧ r' '' C = C'
  respects : ∀ (r : D.LatticeSym) (r' : D.Torus → D.Torus),
    D.proj ∘ r.toFun = r' ∘ D.proj → D.InducedMapRespectsFields r r'
  rules : g.TransportRules
  blockCells : ∀ B ∈ g.blocks, g.BlockCellsRepresent B
  elements : ∀ B ∈ g.blocks, ∀ S ∈ g.cellSet, g.BlockElementsRepresent B S
  finite : ∀ B ∈ g.blocks, (g.cellsWithin B).Finite
variable {g}
theorem liftField_apply {U : D.PeriodicLink → Matrices.ComplexMatrix2}
    (hU : U ∈ D.compactFields) (b : D.Link) :
    (((D.liftField U) b : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      U (D.projLink b) := by
  change ((InfiniteLattice.liftField D.L D.m ((D.K : ℕ) : ℤ) U) b : Matrices.ComplexMatrix2) = _
  rw [InfiniteLattice.liftField_of_mem hU]
  rfl
theorem liftedObservable_mem {S : Set AmbientSpace}
    (hb : BijOn D.projLink (ReflectionGrid.interiorLinks (D := D) S)
      (g.torusCellLinks (D.proj '' S)))
    {F : D.GaugeField → ℂ} (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    D.liftedObservable F ∈ g.torusCellObservables (D.proj '' S) := by
  obtain ⟨f, hf, ⟨C, hC⟩, rfl⟩ := hF
  refine ⟨fun u => f fun b => u (hb.equiv D.projLink b),
    hf.comp (measurable_pi_lambda _ fun b => measurable_pi_apply _), ⟨C, fun u => hC _⟩,
    fun U => ?_⟩
  change f (ReflectionGrid.restrictField S (D.liftField U.1)) = f _
  congr 1
  funext b
  exact Subtype.ext (liftField_apply U.2 b.1)
theorem exists_liftedObservable {S : Set AmbientSpace}
    (hb : BijOn D.projLink (ReflectionGrid.interiorLinks (D := D) S)
      (g.torusCellLinks (D.proj '' S)))
    {F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF' : F' ∈ g.torusCellObservables (D.proj '' S)) :
    ∃ F ∈ ReflectionGrid.cellObservables (D := D) S,
      D.AgreeOnCompactFields (D.liftedObservable F) F' := by
  obtain ⟨f', hf', ⟨C, hC⟩, hF⟩ := hF'
  refine ⟨(fun u => f' fun b => u ((hb.equiv D.projLink).symm b)) ∘ ReflectionGrid.restrictField S,
    ⟨_, hf'.comp (measurable_pi_lambda _ fun b => measurable_pi_apply _), ⟨C, fun u => hC _⟩, rfl⟩,
    fun U hU => ?_⟩
  rw [hF ⟨U, hU⟩]
  change f' _ = f' _
  congr 1
  funext b
  refine Subtype.ext ((liftField_apply hU _).trans ?_)
  have h : D.projLink ((hb.equiv D.projLink).symm b).1 = b.1 :=
    congrArg Subtype.val ((hb.equiv D.projLink).apply_symm_apply b)
  rw [h]
  rfl
theorem descendToTorus_eq {r : AmbientSpace → AmbientSpace} {r' : D.Torus → D.Torus}
    (h : D.proj ∘ r = r' ∘ D.proj) : ReflectionGrid.descendToTorus (D := D) r = r' := by
  funext u
  have h1 := congrFun h (TestFunctions.liftPoint (ℓ := PeriodicLattice.torusSide D.L D.m) u)
  have h2 : D.proj (TestFunctions.liftPoint (ℓ := PeriodicLattice.torusSide D.L D.m) u) = u :=
    TestFunctions.torusProj_liftPoint u
  have h3 : r' (D.proj (TestFunctions.liftPoint (ℓ := PeriodicLattice.torusSide D.L D.m) u)) =
      r' u := by
    rw [h2]
  exact h1.trans h3
theorem image_proj_image {r : AmbientSpace → AmbientSpace} {r' : D.Torus → D.Torus}
    (h : D.proj ∘ r = r' ∘ D.proj) (S : Set AmbientSpace) :
    r' '' (D.proj '' S) = D.proj '' (r '' S) := by
  rw [← image_comp, ← image_comp, h]
theorem mover_eq (h : GridFacts g) {S S' : Set AmbientSpace} (hS : S ∈ g.cellSet)
    (hS' : S' ∈ g.cellSet) (r : g.reflectionGroup) (hr : r.1 '' S = S') : g.mover S S' = r :=
  (h.free S hS S' hS').unique
    (Classical.epsilon_spec (p := fun r : g.reflectionGroup => r.1 '' S = S') ⟨r, hr⟩) hr
theorem torusCarrier_spec (h : GridFacts g) {C C' : Set D.Torus} (hC : C ∈ g.torusCellSet)
    (hC' : C' ∈ g.torusCellSet) :
    g.torusCarrier C C' ∈ g.inducedTorusMaps ∧ g.torusCarrier C C' '' C = C' :=
  Classical.epsilon_spec
    (p := fun r' : D.Torus → D.Torus => r' ∈ g.inducedTorusMaps ∧ r' '' C = C')
    (h.torusFree C hC C' hC').exists
theorem torusCarrier_eq (h : GridFacts g) {C C' : Set D.Torus} (hC : C ∈ g.torusCellSet)
    (hC' : C' ∈ g.torusCellSet) {r' : D.Torus → D.Torus}
    (hr' : r' ∈ g.inducedTorusMaps ∧ r' '' C = C') : g.torusCarrier C C' = r' :=
  (h.torusFree C hC C' hC').unique (torusCarrier_spec h hC hC') hr'
theorem transport_liftedObservable (h : GridFacts g) (r : g.reflectionGroup)
    {r' : D.Torus → D.Torus} (hr : D.proj ∘ r.1 = r' ∘ D.proj)
    {U : D.PeriodicLink → Matrices.ComplexMatrix2} (hU : U ∈ D.compactFields)
    (F : D.GaugeField → ℂ) :
    g.transport r F (D.liftField U) = g.torusTransport r' (D.liftedObservable F) U := by
  have hs : g.torusSign r' = orientationSign r.1 := by
    have hi := Classical.epsilon_spec
      (p := fun s : g.reflectionGroup => D.proj ∘ s.1 = r' ∘ D.proj) ⟨r, hr⟩
    exact h.sign _ (g.inducingElement r').2 _ r.2 r' hi hr
  have hc := ((h.respects (g.toLatticeSym r) r' hr).2 U hU).1
  change Conventions.signedConj (orientationSign r.1)
      (F ((g.toLatticeSym r).pullbackField (D.liftField U))) =
    Conventions.signedConj (g.torusSign r') (F (D.liftField (D.pullbackField r' U)))
  rw [hs, hc]
theorem transportTo_liftedObservable (h : GridFacts g) {S S' : Set AmbientSpace}
    (hS : S ∈ g.cellSet) (hS' : S' ∈ g.cellSet)
    {U : D.PeriodicLink → Matrices.ComplexMatrix2} (hU : U ∈ D.compactFields)
    (F : D.GaugeField → ℂ) :
    g.transportTo S S' F (D.liftField U) =
      g.torusTransportTo (D.proj '' S) (D.proj '' S') (D.liftedObservable F) U := by
  obtain ⟨r, hr⟩ := (h.free S hS S' hS').exists
  obtain ⟨r', hr', -⟩ := h.induced r.1 r.2
  have hmem : r' ∈ g.inducedTorusMaps := ⟨r.1, r.2, hr'⟩
  have himg : r' '' (D.proj '' S) = D.proj '' S' := by
    rw [image_proj_image hr', hr]
  unfold ReflectionGrid.transportTo ReflectionGrid.torusTransportTo
  rw [mover_eq h hS hS' r hr, torusCarrier_eq h ⟨_, hS, rfl⟩ ⟨_, hS', rfl⟩ ⟨hmem, himg⟩]
  exact transport_liftedObservable h r hr' hU F
theorem productOfTransports_liftedObservable (h : GridFacts g) {B S : Set AmbientSpace}
    (hB : B ∈ g.blocks) (hS : S ∈ g.cellSet) (F : D.GaugeField → ℂ)
    {U : D.PeriodicLink → Matrices.ComplexMatrix2} (hU : U ∈ D.compactFields) :
    g.productOfTransports S B F (D.liftField U) = g.torusProduct (D.liftedObservable F) U := by
  have hE := (h.elements B hB S hS).2.2
  have hC : BijOn (fun r₀ : Equiv.Perm AmbientSpace => r₀ '' S) (g.elementsIntoBlock B S)
      (g.cellsWithin B) := by
    refine ⟨fun r hr => hr.2, fun r hr s hs hrs => ?_, fun S' hS' => ?_⟩
    · have hu := (h.free S hS _ hr.2.1).unique (y₁ := ⟨r, hr.1⟩) (y₂ := ⟨s, hs.1⟩) rfl hrs.symm
      exact congrArg Subtype.val hu
    · obtain ⟨r, hr⟩ := (h.free S hS S' hS'.1).exists
      exact ⟨r.1, ⟨r.2, by rw [hr]; exact hS'⟩, hr⟩
  change (∏ᶠ S' ∈ g.cellsWithin B, g.transportTo S S' F (D.liftField U)) =
    ∏ᶠ r' ∈ g.inducedTorusMaps, g.torusTransport r' (D.liftedObservable F) U
  refine (finprod_mem_eq_of_bijOn
    (f := fun r₀ : Equiv.Perm AmbientSpace => g.transportTo S (r₀ '' S) F (D.liftField U))
    (g := fun S' => g.transportTo S S' F (D.liftField U)) _ hC fun _ _ => rfl).symm.trans ?_
  refine finprod_mem_eq_of_bijOn _ hE fun r hr => ?_
  obtain ⟨r', hr', -⟩ := h.induced r hr.1
  have ht : ReflectionGrid.descendToTorus (D := D) r = r' := descendToTorus_eq hr'
  have hc : g.mover S (r '' S) = ⟨r, hr.1⟩ := mover_eq h hS hr.2.1 ⟨r, hr.1⟩ rfl
  change g.transport (g.mover S (r '' S)) F (D.liftField U) =
    g.torusTransport (ReflectionGrid.descendToTorus (D := D) r) (D.liftedObservable F) U
  rw [hc, ht]
  exact transport_liftedObservable h ⟨r, hr.1⟩ hr' hU F
theorem pullbackField_mem (h : GridFacts g) {r' : D.Torus → D.Torus}
    (hr' : r' ∈ g.inducedTorusMaps) {U : D.PeriodicLink → Matrices.ComplexMatrix2}
    (hU : U ∈ D.compactFields) : D.pullbackField r' U ∈ D.compactFields := by
  obtain ⟨r, hr, hc⟩ := hr'
  have hb := ((h.respects (g.toLatticeSym ⟨r, hr⟩) r' hc).2 U hU).2
  have hspec : ∀ b : D.PeriodicLink, ((D.imageLink r' b).source : D.Torus) = r' b.source ∧
      ((D.imageLink r' b).target : D.Torus) = r' b.target := fun b => by
    obtain ⟨b', h1, h2, -⟩ := hb b
    exact Classical.epsilon_spec (p := fun b' : D.PeriodicLink =>
      (b'.source : D.Torus) = r' b.source ∧ (b'.target : D.Torus) = r' b.target) ⟨b', h1, h2⟩
  refine ⟨fun b _ => hU.1 _ (mem_univ _), fun b _ => ?_⟩
  have hrev : D.imageLink r' b.opposite = (D.imageLink r' b).opposite :=
    PeriodicLattice.Bond.ext (Subtype.ext ((hspec _).1.trans (hspec b).2.symm))
      (Subtype.ext ((hspec _).2.trans (hspec b).1.symm))
  change U (D.imageLink r' b.opposite) = (U (D.imageLink r' b))⁻¹
  rw [hrev]
  exact hU.2 _ (mem_univ _)
theorem torusTransport_congr (h : GridFacts g) {r' : D.Torus → D.Torus}
    (hr' : r' ∈ g.inducedTorusMaps) {F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : D.AgreeOnCompactFields F F') :
    D.AgreeOnCompactFields (g.torusTransport r' F) (g.torusTransport r' F') := fun U hU => by
  change Conventions.signedConj _ (F (D.pullbackField r' U)) =
    Conventions.signedConj _ (F' (D.pullbackField r' U))
  rw [hF _ (pullbackField_mem h hr' hU)]
theorem torusProduct_congr (h : GridFacts g)
    {F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} (hF : D.AgreeOnCompactFields F F') :
    D.AgreeOnCompactFields (g.torusProduct F) (g.torusProduct F') := fun U hU => by
  unfold ReflectionGrid.torusProduct
  exact finprod_mem_congr rfl fun r' hr' => torusTransport_congr h hr' hF U hU
theorem torusChessboardNorm_congr (h : GridFacts g)
    {F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} (hF : D.AgreeOnCompactFields F F') :
    g.torusChessboardNorm F = g.torusChessboardNorm F' := by
  unfold ReflectionGrid.torusChessboardNorm
  rw [periodicExpectation_congr D h.counts (torusProduct_congr h hF)]
theorem measurable_of_mem_cellObservables {S : Set AmbientSpace} {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) : Measurable F := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardBlockInvariance.measurable_of_mem_cellObservables <;> assumption
theorem measurable_finprod_cells {T : Set (Set AmbientSpace)} (hT : T.Finite)
    {F : Set AmbientSpace → D.GaugeField → ℂ} (hF : ∀ S ∈ T, Measurable (F S)) :
    Measurable fun U => ∏ᶠ S ∈ T, F S U := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardBlockInvariance.measurable_finprod_cells <;> assumption
theorem periodicExpectation_torusProduct (h : GridFacts g) {B S : Set AmbientSpace}
    (hB : B ∈ g.blocks) (hS : S ∈ g.cellSet) {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    D.periodicExpectation (g.torusProduct (D.liftedObservable F)) =
      g.chessboardExpectation S B F := by
  have hm : Measurable (g.productOfTransports S B F) := by
    refine measurable_finprod_cells (h.finite B hB) fun S' hS' => ?_
    obtain ⟨r, hr⟩ := (h.free S hS S' hS'.1).exists
    exact measurable_of_mem_cellObservables
      (h.rules S hS S' hS'.1 S' hS'.1 r hr F hF F hF 0).1
  unfold ReflectionGrid.chessboardExpectation
  rw [liftedExpectation_eq D hm]
  exact periodicExpectation_congr D h.counts fun U hU =>
    (productOfTransports_liftedObservable h hB hS F hU).symm
theorem norm_eq_re_of_im_eq_zero {z : ℂ} (him : z.im = 0) (hre : 0 ≤ z.re) : ‖z‖ = z.re := by apply _root_.YangMills.Construction.ChessboardTori.TransferSetupCellFamilies.norm_eq_re_of_im_eq_zero <;> assumption
theorem chessboardNorm_eq (h : GridFacts g) {S : Set AmbientSpace} (hS : S ∈ g.cellSet)
    {F : D.GaugeField → ℂ} (hF : F ∈ ReflectionGrid.cellObservables (D := D) S)
    (him : (g.chessboardExpectation S (g.block 0) F).im = 0)
    (hre : 0 ≤ (g.chessboardExpectation S (g.block 0) F).re) :
    g.chessboardNorm S F = g.torusChessboardNorm (D.liftedObservable F) := by
  unfold ReflectionGrid.chessboardNorm ReflectionGrid.torusChessboardNorm
  rw [periodicExpectation_torusProduct h ⟨0, rfl⟩ hS hF, norm_eq_re_of_im_eq_zero him hre]
end EvaluationMaps
theorem proof (hArith : ReflectionGridArithmetic.Statement)
    (hSigns : CellsBlocksAndSigns.Statement) (hLift : LiftingRules.Statement)
    (hGrid : GridBasicProperties.Statement) (hChess : ChessboardInequality.Statement)
    (hCount : PeriodicLattice.SiteAndPlaquetteCounts) : Statement := by
  intro D g hside
  obtain ⟨-, -, -, hcoord, hrules, -, hrest⟩ := hGrid D g
  obtain ⟨hind, hgrp, hcov⟩ := hrest hside
  obtain ⟨hsame, hblocks⟩ := (hSigns D g).2 hside
  obtain ⟨-, -, -, harith⟩ := hArith D
  have hfree := hcoord.2.2.2.2.2.2.1
  have hfin : ∀ B ∈ g.blocks, (g.cellsWithin B).Finite := by
    rintro _ ⟨k, rfl⟩
    rw [((harith g).2 hside).2 k |>.2.1]
    exact ((Set.finite_Icc k (fun μ => k μ + g.cellsPerTorusSide - 1)).subset
      fun j hj => ⟨fun μ => (hj μ).1, fun μ => (hj μ).2⟩).image _
  have h : GridFacts g :=
    { period_ge := hside
      counts := hCount
      projSurjective := (hLift D).1.2.1
      sameImage := hsame
      injOn := hcov.1
      free := hfree
      induced := hind.2.2.1
      sign := hgrp.2.2.2.1
      torusFree := hgrp.2.2.2.2.2.2.1
      respects := (hLift D).2.2.2
      rules := hrules
      blockCells := fun B hB => (hblocks B hB).1
      elements := fun B hB S hS => ((hblocks B hB).2 S hS).1
      finite := hfin }
  obtain ⟨hc1, hc2, hc3, -⟩ := hChess D g hside
  have hB0 : g.block 0 ∈ g.blocks := ⟨0, rfl⟩
  have hlinks : ∀ S ∈ g.cellSet, BijOn D.projLink (ReflectionGrid.interiorLinks (D := D) S)
      (g.torusCellLinks (D.proj '' S)) := fun S hS =>
    bijOn_projLink g h.projSurjective hsame h.injOn hside hS
  have hnorm : ∀ S ∈ g.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
      g.chessboardNorm S F = g.torusChessboardNorm (D.liftedObservable F) := fun S hS F hF =>
    chessboardNorm_eq h hS hF (hc1 _ hB0 S hS F hF).1 (hc1 _ hB0 S hS F hF).2.1
  refine ⟨fun S hS => ⟨hlinks S hS, fun F hF => liftedObservable_mem (hlinks S hS) hF,
      fun F _ F' _ c => ⟨rfl, rfl, rfl, rfl⟩, rfl,
      fun F' hF' => exists_liftedObservable (hlinks S hS) hF'⟩,
    fun S hS S' hS' F _ U hU => transportTo_liftedObservable h hS hS' hU F,
    fun H hH => liftedExpectation_eq D hH.1,
    fun B hB S hS F _ U hU => productOfTransports_liftedObservable h hB hS F hU,
    fun S hS F hF => ?_, fun C hC F hF => ?_, fun F hF => ?_⟩
  · rw [periodicExpectation_torusProduct h hB0 hS hF]
    exact ⟨(hc1 _ hB0 S hS F hF).1, (hc1 _ hB0 S hS F hF).2.1, hnorm S hS F hF⟩
  · obtain ⟨S, hS, rfl⟩ := hC
    obtain ⟨F₀, hF₀, hagree⟩ := exists_liftedObservable (hlinks S hS) hF
    have hprod := periodicExpectation_congr D hCount (torusProduct_congr h hagree)
    have hexp := periodicExpectation_torusProduct h hB0 hS hF₀
    refine ⟨?_, ?_, fun C' hC' => ?_, ?_⟩
    · rw [← hprod, hexp]
      exact (hc1 _ hB0 S hS F₀ hF₀).1
    · rw [← hprod, hexp]
      exact (hc1 _ hB0 S hS F₀ hF₀).2.1
    · obtain ⟨S', hS', rfl⟩ := hC'
      obtain ⟨r, hr⟩ := (hfree S hS S' hS').exists
      have hmem := (hrules S hS S' hS' S' hS' r hr F₀ hF₀ F₀ hF₀ 0).1
      have hcarr := (torusCarrier_spec h (C := D.proj '' S) (C' := D.proj '' S')
        ⟨_, hS, rfl⟩ ⟨_, hS', rfl⟩).1
      have e1 : g.torusChessboardNorm
            (g.torusTransportTo (D.proj '' S) (D.proj '' S') F) =
          g.torusChessboardNorm (D.liftedObservable (g.transportTo S S' F₀)) :=
        torusChessboardNorm_congr h fun U hU =>
          ((torusTransport_congr h hcarr hagree U hU).symm).trans
            (transportTo_liftedObservable h hS hS' hU F₀).symm
      rw [e1, ← hnorm S' hS' _ hmem, ((hc3 S hS).1 F₀ hF₀).1 S' hS', hnorm S hS F₀ hF₀]
      exact torusChessboardNorm_congr h hagree
    · have hconj : (fun U => starRingEnd ℂ (F₀ U)) ∈ ReflectionGrid.cellObservables (D := D) S := by
        obtain ⟨f, hf, ⟨c, hc⟩, rfl⟩ := hF₀
        exact ⟨fun u => starRingEnd ℂ (f u), Complex.continuous_conj.measurable.comp hf,
          ⟨c, fun u => by simpa using hc u⟩, rfl⟩
      have e2 : g.torusChessboardNorm (fun U => starRingEnd ℂ (F U)) =
          g.torusChessboardNorm (D.liftedObservable fun U => starRingEnd ℂ (F₀ U)) :=
        torusChessboardNorm_congr h fun U hU => by
          change starRingEnd ℂ (F U) = starRingEnd ℂ (D.liftedObservable F₀ U)
          rw [hagree U hU]
      rw [e2, ← hnorm S hS _ hconj, ← ((hc3 S hS).1 F₀ hF₀).2.1, hnorm S hS F₀ hF₀]
      exact (torusChessboardNorm_congr h hagree).symm
  · have hbij := ((hblocks _ hB0).1).2
    have hex : ∀ S ∈ g.cellsWithin (g.block 0), ∃ F₀ : D.GaugeField → ℂ,
        F₀ ∈ ReflectionGrid.cellObservables (D := D) S ∧
          D.AgreeOnCompactFields (D.liftedObservable F₀) (F (D.proj '' S)) := fun S hS => by
      obtain ⟨F₀, h1, h2⟩ := exists_liftedObservable (hlinks S hS.1) (hF _ ⟨S, hS.1, rfl⟩)
      exact ⟨F₀, h1, h2⟩
    choose! Fam hFam using hex
    have hbound := hc2 _ hB0 Fam fun S hS => (hFam S hS).1
    have hm : Measurable fun U => ∏ᶠ S ∈ g.cellsWithin (g.block 0), Fam S U :=
      measurable_finprod_cells (hfin _ hB0) fun S hS =>
        measurable_of_mem_cellObservables (hFam S hS).1
    have e1 : D.liftedExpectation (fun U => ∏ᶠ S ∈ g.cellsWithin (g.block 0), Fam S U) =
        D.periodicExpectation fun U => ∏ᶠ C ∈ g.torusCellSet, F C U := by
      rw [liftedExpectation_eq D hm]
      exact periodicExpectation_congr D hCount fun U hU =>
        finprod_mem_eq_of_bijOn _ hbij fun S hS => (hFam S hS).2 U hU
    have e2 : (∏ᶠ S ∈ g.cellsWithin (g.block 0), g.chessboardNorm S (Fam S)) =
        ∏ᶠ C ∈ g.torusCellSet, g.torusChessboardNorm (F C) :=
      finprod_mem_eq_of_bijOn _ hbij fun S hS =>
        (hnorm S hS.1 _ (hFam S hS).1).trans (torusChessboardNorm_congr h (hFam S hS).2)
    rw [← e1, ← e2]
    exact hbound
end YangMills.Construction.ChessboardTori.TorusReduction
end
