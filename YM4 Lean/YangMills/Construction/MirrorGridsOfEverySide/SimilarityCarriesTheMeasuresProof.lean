import YangMills.Construction.Lattice.IsometryCovarianceOfHolonomiesAndActionsProof
import YangMills.Construction.Lattice.LatticeIsometriesAsMapsOfPairsProof
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesTheInfiniteLatticeProof
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesTheMeasures
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesTheTorus
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
open YangMills.Construction.InfiniteLattice (AmbientSpace)
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides.ScalingMeasures
variable {D : GridSetup} (S : ScalingMap D)
theorem pointOnAxis_eq_torusProj_single (L m : ℕ) (μ : Fin 4) (t : ℝ) :
    PeriodicLattice.pointOnAxis L m μ t =
      TorusMetric.torusProj (PeriodicLattice.torusSide L m) (Pi.single μ t) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.pointOnAxis_eq_toFourTorus <;> assumption
theorem torusProj_add_vec (s : ℝ) (x w : AmbientSpace) :
    TorusMetric.torusProj s (x + w) = TorusMetric.torusProj s x + TorusMetric.torusProj s w := by apply _root_.YangMills.Construction.AffineTorusIsometries.torusProj_add' <;> assumption
theorem toFun_add_single (x : AmbientSpace) (μ : Fin 4) :
    S.toFun (x + Pi.single μ D.mesh) = S.toFun x + Pi.single μ S.image.mesh := by
  funext ν
  rw [S.image_mesh]
  by_cases hνμ : ν = μ
  · subst hνμ
    simp [ScalingMap.toFun]
    ring
  · simp [ScalingMap.toFun, Pi.single_eq_of_ne hνμ]
variable {S}
theorem torusMap_add_pointOnAxis (hT : S.PreservesTorus) (y : D.Torus) (μ : Fin 4) :
    S.torusMap (y + PeriodicLattice.pointOnAxis D.L D.m μ D.mesh) =
      S.torusMap y + PeriodicLattice.pointOnAxis S.image.L S.image.m μ S.image.mesh := by
  have hmap : ∀ x : AmbientSpace, S.torusMap (D.proj x) = S.image.proj (S.toFun x) :=
    fun x => congrFun hT.2.1 x
  obtain ⟨x, rfl⟩ : ∃ x, D.proj x = y :=
    ⟨TestFunctions.liftPoint (ℓ := PeriodicLattice.torusSide D.L D.m) y,
      TestFunctions.torusProj_liftPoint y⟩
  have hstep : D.proj x + PeriodicLattice.pointOnAxis D.L D.m μ D.mesh =
      D.proj (x + Pi.single μ D.mesh) := by
    rw [pointOnAxis_eq_torusProj_single]
    exact (torusProj_add_vec _ _ _).symm
  rw [hstep, hmap, hmap, toFun_add_single, pointOnAxis_eq_torusProj_single]
  exact torusProj_add_vec _ _ _
theorem torusLinkMap_forwardFrom (hT : S.PreservesTorus) (x : D.TorusPoint)
    (x' : S.image.TorusPoint) (hx : (x' : S.image.Torus) = S.torusMap x) (μ : Fin 4) :
    S.torusLinkMap (PeriodicLattice.Bond.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom x' μ := by
  obtain ⟨hs, ht⟩ := hT.2.2.2.2.2.1 (PeriodicLattice.Bond.forwardFrom x μ)
  refine PeriodicLattice.Bond.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · exact hs.trans hx.symm
  · refine ht.trans ?_
    change S.torusMap ((x : D.Torus) + PeriodicLattice.pointOnAxis D.L D.m μ D.mesh) =
      (x' : S.image.Torus) + PeriodicLattice.pointOnAxis S.image.L S.image.m μ S.image.mesh
    rw [torusMap_add_pointOnAxis hT, hx]
theorem torusLinkMap_opposite (hT : S.PreservesTorus) (b : D.PeriodicLink) :
    S.torusLinkMap b.opposite = (S.torusLinkMap b).opposite := by
  obtain ⟨hs, ht⟩ := hT.2.2.2.2.2.1 b
  obtain ⟨hs', ht'⟩ := hT.2.2.2.2.2.1 b.opposite
  exact PeriodicLattice.Bond.ext (Subtype.ext (hs'.trans ht.symm)) (Subtype.ext (ht'.trans hs.symm))
theorem map_torusLinkMap_boundaryBonds (hT : S.PreservesTorus) (p : D.TorusFace) :
    p.boundaryBonds.map S.torusLinkMap = (S.torusFaceMap p).boundaryBonds := by
  obtain ⟨hf, hs, hb⟩ := hT.2.2.2.2.2.2.2.2.1 p
  have hstep : ∀ μ : Fin 4,
      (((S.torusFaceMap p).origin + PeriodicLattice.unitStep _ _ _ μ : S.image.TorusPoint) :
        S.image.Torus) =
      S.torusMap ((p.origin + PeriodicLattice.unitStep _ _ _ μ : D.TorusPoint) : D.Torus) := by
    intro μ
    change ((S.torusFaceMap p).origin : S.image.Torus) +
        PeriodicLattice.pointOnAxis S.image.L S.image.m μ S.image.mesh =
      S.torusMap ((p.origin : D.Torus) + PeriodicLattice.pointOnAxis D.L D.m μ D.mesh)
    rw [torusMap_add_pointOnAxis hT, hb]
  simp only [PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil,
    torusLinkMap_opposite hT, hf, hs]
  rw [torusLinkMap_forwardFrom hT _ _ hb, torusLinkMap_forwardFrom hT _ _ (hstep _),
    torusLinkMap_forwardFrom hT _ _ (hstep _), torusLinkMap_forwardFrom hT _ _ hb]
theorem plaquetteHolonomy_torusPullback (hT : S.PreservesTorus)
    (U' : S.image.PeriodicLink → Matrices.ComplexMatrix2) (p : D.TorusFace) :
    PeriodicLattice.plaquetteHolonomy (S.torusPullback U') p =
      PeriodicLattice.plaquetteHolonomy U' (S.torusFaceMap p) := by
  simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    ← map_torusLinkMap_boundaryBonds hT p, List.map_map]
  rfl
theorem plaquetteEnergy_torusPullback (hT : S.PreservesTorus)
    (U' : S.image.PeriodicLink → Matrices.ComplexMatrix2) (p : D.TorusFace) :
    PeriodicLattice.plaquetteCost (S.torusPullback U') p =
      PeriodicLattice.plaquetteCost U' (S.torusFaceMap p) := by
  simp only [PeriodicLattice.plaquetteCost, plaquetteHolonomy_torusPullback hT]
def torusFaceEquiv (hT : S.PreservesTorus) : D.TorusFace ≃ S.image.TorusFace :=
  Equiv.ofBijective S.torusFaceMap hT.2.2.2.2.2.2.2.2.2.2.1
def torusLinkEquiv (hT : S.PreservesTorus) : D.PeriodicLink ≃ S.image.PeriodicLink :=
  Equiv.ofBijective S.torusLinkMap hT.2.2.2.2.2.2.1
theorem wilsonAction_torusPullback (hT : S.PreservesTorus)
    (U' : S.image.PeriodicLink → Matrices.ComplexMatrix2) :
    PeriodicLattice.wilsonAction (S.torusPullback U') = PeriodicLattice.wilsonAction U' := by
  simp only [PeriodicLattice.wilsonAction, plaquetteEnergy_torusPullback hT]
  exact finsum_comp_equiv (torusFaceEquiv hT) (f := fun p => PeriodicLattice.plaquetteCost U' p)
def torusPushforward (hT : S.PreservesTorus) (U : D.PeriodicLink → Matrices.ComplexMatrix2) :
    S.image.PeriodicLink → Matrices.ComplexMatrix2 :=
  fun b' => U ((torusLinkEquiv hT).symm b')
theorem torusPullback_mem (hT : S.PreservesTorus) {U' : S.image.PeriodicLink → Matrices.ComplexMatrix2}
    (hU : U' ∈ S.image.torusFields) : S.torusPullback U' ∈ D.torusFields := by
  refine ⟨fun b _ => hU.1 _ (mem_univ _), fun b _ => ?_⟩
  change U' (S.torusLinkMap b.opposite) = (U' (S.torusLinkMap b))⁻¹
  rw [torusLinkMap_opposite hT]
  exact hU.2 _ (mem_univ _)
theorem torusLinkEquiv_symm_opposite (hT : S.PreservesTorus) (b' : S.image.PeriodicLink) :
    (torusLinkEquiv hT).symm b'.opposite = ((torusLinkEquiv hT).symm b').opposite := by
  apply (torusLinkEquiv hT).injective
  rw [Equiv.apply_symm_apply]
  change b'.opposite = S.torusLinkMap ((torusLinkEquiv hT).symm b').opposite
  rw [torusLinkMap_opposite hT]
  congr 1
  exact ((torusLinkEquiv hT).apply_symm_apply b').symm
theorem torusPushforward_mem (hT : S.PreservesTorus) {U : D.PeriodicLink → Matrices.ComplexMatrix2}
    (hU : U ∈ D.torusFields) : torusPushforward hT U ∈ S.image.torusFields := by
  refine ⟨fun b _ => hU.1 _ (mem_univ _), fun b _ => ?_⟩
  change U ((torusLinkEquiv hT).symm b.opposite) = (U ((torusLinkEquiv hT).symm b))⁻¹
  rw [torusLinkEquiv_symm_opposite hT]
  exact hU.2 _ (mem_univ _)
theorem torusPushforward_torusPullback (hT : S.PreservesTorus)
    (U' : S.image.PeriodicLink → Matrices.ComplexMatrix2) :
    torusPushforward hT (S.torusPullback U') = U' :=
  funext fun b' => congrArg U' ((torusLinkEquiv hT).apply_symm_apply b')
theorem torusPullback_torusPushforward (hT : S.PreservesTorus)
    (U : D.PeriodicLink → Matrices.ComplexMatrix2) :
    S.torusPullback (torusPushforward hT U) = U :=
  funext fun b => congrArg U ((torusLinkEquiv hT).symm_apply_apply b)
theorem continuous_torusPullback : Continuous S.torusPullback :=
  continuous_pi fun b => continuous_apply (S.torusLinkMap b)
theorem continuous_torusPushforward (hT : S.PreservesTorus) :
    Continuous (torusPushforward hT) :=
  continuous_pi fun b' => continuous_apply ((torusLinkEquiv hT).symm b')
def torusFieldsHomeomorph (hT : S.PreservesTorus) :
    S.image.torusFields ≃ₜ D.torusFields where
  toFun U' := ⟨S.torusPullback U'.1, torusPullback_mem hT U'.2⟩
  invFun U := ⟨torusPushforward hT U.1, torusPushforward_mem hT U.2⟩
  left_inv U' := Subtype.ext (torusPushforward_torusPullback hT U'.1)
  right_inv U := Subtype.ext (torusPullback_torusPushforward hT U.1)
  continuous_toFun := Continuous.subtype_mk
    (continuous_torusPullback.comp continuous_subtype_val) fun U' => torusPullback_mem hT U'.2
  continuous_invFun := Continuous.subtype_mk
    ((continuous_torusPushforward hT).comp continuous_subtype_val)
    fun U => torusPushforward_mem hT U.2
variable (S) in
theorem continuous_pullback : Continuous S.pullback := by
  have hc : Continuous (fun U' :
      {U : InfiniteLattice.Link S.image.mesh → Matrices.ComplexMatrix2.specialUnitary //
        ∀ b, U b.opposite = (U b)⁻¹} =>
      (fun b => U'.1 (S.linkMap b) : D.Link → Matrices.ComplexMatrix2.specialUnitary)) :=
    continuous_pi fun b => (continuous_apply (S.linkMap b)).comp continuous_subtype_val
  exact hc.subtype_mk fun U' => (S.pullback U').2
def latticeFieldsHomeomorph (hI : Function.Bijective S.linkMap) :
    S.image.GaugeField ≃ₜ D.GaugeField where
  toFun := S.pullback
  invFun U := ⟨fun b' => U ((Equiv.ofBijective _ hI).symm b'), fun b' => by
    have hb : (Equiv.ofBijective _ hI).symm b'.opposite =
        ((Equiv.ofBijective _ hI).symm b').opposite := by
      apply (Equiv.ofBijective _ hI).injective
      rw [Equiv.apply_symm_apply]
      change b'.opposite = S.linkMap ((Equiv.ofBijective _ hI).symm b').opposite
      rw [S.linkMap_opposite]
      congr 1
      exact ((Equiv.ofBijective _ hI).apply_symm_apply b').symm
    change U.1 _ = (U.1 _)⁻¹
    rw [hb]
    exact U.2 _⟩
  left_inv U' := Subtype.ext (funext fun b' =>
    congrArg U'.1 ((Equiv.ofBijective _ hI).apply_symm_apply b'))
  right_inv U := Subtype.ext (funext fun b =>
    congrArg U.1 ((Equiv.ofBijective _ hI).symm_apply_apply b))
  continuous_toFun := continuous_pullback S
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_pi fun b' => ?_) _
    exact (continuous_apply ((Equiv.ofBijective _ hI).symm b')).comp
      (continuous_subtype_val : Continuous (Subtype.val :
        {U : InfiniteLattice.Link D.mesh → Matrices.ComplexMatrix2.specialUnitary //
          ∀ b, U b.opposite = (U b)⁻¹} → _))
theorem pointMap_add_axisStep (x : InfiniteLattice.LatticePoint D.mesh) (μ : Fin 4) :
    S.pointMap (x + InfiniteLattice.axisStep D.mesh μ) =
      S.pointMap x + InfiniteLattice.axisStep S.image.mesh μ := by apply _root_.YangMills.Construction.MirrorGridsAllSides.ScalingOnGrid.pointMap_add_axisStep <;> assumption
theorem linkMap_forwardFrom (x : InfiniteLattice.LatticePoint D.mesh) (μ : Fin 4) :
    S.linkMap (InfiniteLattice.Link.forwardFrom x μ) =
      InfiniteLattice.Link.forwardFrom (S.pointMap x) μ := by
  refine InfiniteLattice.Link.ext rfl ?_
  exact pointMap_add_axisStep x μ
theorem faceEnergy_pullback (U' : S.image.GaugeField) (p : D.Plaquette) :
    InfiniteLattice.faceEnergy (S.pullback U') p =
      InfiniteLattice.faceEnergy U' (S.faceMap p) := by
  have hv : InfiniteLattice.faceHolonomy (S.pullback U') p =
      InfiniteLattice.faceHolonomy U' (S.faceMap p) := by
    change U' (S.linkMap _) * U' (S.linkMap _) * (U' (S.linkMap _))⁻¹ * (U' (S.linkMap _))⁻¹ = _
    rw [linkMap_forwardFrom, linkMap_forwardFrom, linkMap_forwardFrom, linkMap_forwardFrom,
      pointMap_add_axisStep, pointMap_add_axisStep]
    rfl
  simp only [InfiniteLattice.faceEnergy, hv]
def linkFunctionsEquiv (hT : S.PreservesTorus) :
    (S.image.PeriodicLink → Matrices.ComplexMatrix2) ≃ᵐ (D.PeriodicLink → Matrices.ComplexMatrix2) where
  toFun := S.torusPullback
  invFun := torusPushforward hT
  left_inv := torusPushforward_torusPullback hT
  right_inv := torusPullback_torusPushforward hT
  measurable_toFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
theorem measurable_gaugeFieldOfPositive (L m : ℕ) (j : ℤ) :
    Measurable (PeriodicLattice.gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) →
        PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.measurable_gaugeFieldOfPositive <;> assumption
def positiveBondEquiv (hT : S.PreservesTorus) :
    PeriodicLattice.PositivelyOrientedBond D.L D.m ((D.K : ℕ) : ℤ) ≃
      PeriodicLattice.PositivelyOrientedBond S.image.L S.image.m ((S.image.K : ℕ) : ℤ) :=
  (torusLinkEquiv hT).subtypeEquiv fun b => hT.2.2.2.2.2.2.2.1 b
def positiveRelabel (hT : S.PreservesTorus) :
    (PeriodicLattice.PositivelyOrientedBond S.image.L S.image.m ((S.image.K : ℕ) : ℤ) →
        Matrices.ComplexMatrix2.specialUnitary) ≃ᵐ
      (PeriodicLattice.PositivelyOrientedBond D.L D.m ((D.K : ℕ) : ℤ) →
        Matrices.ComplexMatrix2.specialUnitary) :=
  MeasurableEquiv.piCongrLeft (fun _ => Matrices.ComplexMatrix2.specialUnitary)
    (positiveBondEquiv hT).symm
theorem positiveRelabel_apply (hT : S.PreservesTorus)
    (v : PeriodicLattice.PositivelyOrientedBond S.image.L S.image.m ((S.image.K : ℕ) : ℤ) →
      Matrices.ComplexMatrix2.specialUnitary)
    (c : PeriodicLattice.PositivelyOrientedBond D.L D.m ((D.K : ℕ) : ℤ)) :
    positiveRelabel hT v c = v (positiveBondEquiv hT c) := by
  have hc := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ => Matrices.ComplexMatrix2.specialUnitary)
    (positiveBondEquiv hT).symm v (positiveBondEquiv hT c)
  rw [Equiv.symm_apply_apply] at hc
  exact hc
theorem map_positiveRelabel (hT : S.PreservesTorus) :
    (PeriodicLattice.gaugeFieldHaar S.image.L S.image.m ((S.image.K : ℕ) : ℤ)).map
        (positiveRelabel hT) =
      PeriodicLattice.gaugeFieldHaar D.L D.m ((D.K : ℕ) : ℤ) :=
  Measure.infinitePi_map_piCongrLeft (fun _ => Matrices.ComplexMatrix2.haarProb)
    (positiveBondEquiv hT).symm
theorem torusPullback_gaugeFieldOfPositive (hT : S.PreservesTorus)
    (v : PeriodicLattice.PositivelyOrientedBond S.image.L S.image.m ((S.image.K : ℕ) : ℤ) →
      Matrices.ComplexMatrix2.specialUnitary) :
    S.torusPullback (PeriodicLattice.gaugeFieldOfPositive v) =
      PeriodicLattice.gaugeFieldOfPositive (positiveRelabel hT v) := by
  have hpos := hT.2.2.2.2.2.2.2.1
  funext b
  change PeriodicLattice.gaugeFieldOfPositive v (S.torusLinkMap b) = _
  by_cases hb : b.IsPositivelyOriented
  · have h₁ : (S.torusLinkMap b).IsPositivelyOriented := (hpos b).1 hb
    rw [PeriodicLattice.gaugeFieldOfPositive, dif_pos h₁, PeriodicLattice.gaugeFieldOfPositive,
      dif_pos hb, positiveRelabel_apply]
    rfl
  · have h₁ : ¬ (S.torusLinkMap b).IsPositivelyOriented := fun h₂ => hb ((hpos b).2 h₂)
    by_cases hr : b.opposite.IsPositivelyOriented
    · have h₂ : (S.torusLinkMap b).opposite.IsPositivelyOriented := by
        rw [← torusLinkMap_opposite hT]
        exact (hpos _).1 hr
      rw [PeriodicLattice.gaugeFieldOfPositive, dif_neg h₁, dif_pos h₂,
        PeriodicLattice.gaugeFieldOfPositive, dif_neg hb, dif_pos hr, positiveRelabel_apply]
      congr 3
      exact Subtype.ext (torusLinkMap_opposite hT b).symm
    · have h₂ : ¬ (S.torusLinkMap b).opposite.IsPositivelyOriented := fun h₃ => hr ((hpos _).2 (by
        rw [torusLinkMap_opposite hT]
        exact h₃))
      rw [PeriodicLattice.gaugeFieldOfPositive, dif_neg h₁, dif_neg h₂,
        PeriodicLattice.gaugeFieldOfPositive, dif_neg hb, dif_neg hr]
theorem map_productHaarMeasure (hT : S.PreservesTorus) :
    (PeriodicLattice.productHaarMeasure S.image.L S.image.m ((S.image.K : ℕ) : ℤ)).map
        (linkFunctionsEquiv hT) =
      PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ) := by
  simp only [PeriodicLattice.productHaarMeasure]
  rw [Measure.map_map (linkFunctionsEquiv hT).measurable (measurable_gaugeFieldOfPositive _ _ _),
    ← map_positiveRelabel hT,
    Measure.map_map (measurable_gaugeFieldOfPositive _ _ _) (positiveRelabel hT).measurable]
  congr 1
  exact funext fun v => torusPullback_gaugeFieldOfPositive hT v
theorem boltzmannWeight_torusPullback (hT : S.PreservesTorus)
    (U' : S.image.PeriodicLink → Matrices.ComplexMatrix2) :
    PeriodicLattice.boltzmannWeight D.β (S.torusPullback U') =
      PeriodicLattice.boltzmannWeight D.β U' := by
  simp only [PeriodicLattice.boltzmannWeight, wilsonAction_torusPullback hT]
theorem partition_eq (hT : S.PreservesTorus) :
    D.partition = S.image.partition := by
  change ∫ U, PeriodicLattice.boltzmannWeight D.β U ∂PeriodicLattice.productHaarMeasure D.L D.m _ =
    ∫ U, PeriodicLattice.boltzmannWeight D.β U ∂PeriodicLattice.productHaarMeasure _ _ _
  rw [← map_productHaarMeasure hT, integral_map_equiv]
  exact integral_congr_ae (Filter.Eventually.of_forall fun U' => boltzmannWeight_torusPullback hT U')
theorem map_gibbs (hT : S.PreservesTorus) :
    S.image.gibbs.map (linkFunctionsEquiv hT) = D.gibbs := by
  have hw : ((PeriodicLattice.productHaarMeasure S.image.L S.image.m
        ((S.image.K : ℕ) : ℤ)).withDensity
        fun U => ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β U)).map (linkFunctionsEquiv hT) =
      (PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)).withDensity
        fun U => ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β U) := by
    ext s hs
    rw [Measure.map_apply (linkFunctionsEquiv hT).measurable hs,
      withDensity_apply _ ((linkFunctionsEquiv hT).measurable hs), withDensity_apply _ hs]
    have hp : MeasurePreserving (linkFunctionsEquiv hT)
        (PeriodicLattice.productHaarMeasure S.image.L S.image.m ((S.image.K : ℕ) : ℤ))
        (PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)) :=
      ⟨(linkFunctionsEquiv hT).measurable, map_productHaarMeasure hT⟩
    rw [← hp.setLIntegral_comp_preimage_emb (linkFunctionsEquiv hT).measurableEmbedding]
    refine lintegral_congr fun U' => ?_
    exact congrArg ENNReal.ofReal (boltzmannWeight_torusPullback hT U').symm
  have hZ : PeriodicLattice.partitionFunction D.L D.m D.K D.β =
      PeriodicLattice.partitionFunction S.image.L S.image.m S.image.K D.β :=
    partition_eq hT
  change ((ENNReal.ofReal (PeriodicLattice.partitionFunction S.image.L S.image.m S.image.K D.β))⁻¹ •
      (PeriodicLattice.productHaarMeasure S.image.L S.image.m
        ((S.image.K : ℕ) : ℤ)).withDensity
        fun U => ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β U)).map (linkFunctionsEquiv hT) =
    (ENNReal.ofReal (PeriodicLattice.partitionFunction D.L D.m D.K D.β))⁻¹ •
      (PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)).withDensity
        fun U => ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β U)
  rw [Measure.map_smul, hw, hZ]
theorem expect_eq (hT : S.PreservesTorus) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → E) :
    D.expect F = S.image.expect (F ∘ S.torusPullback) := by
  change ∫ U, F U ∂D.gibbs = ∫ U', F (S.torusPullback U') ∂S.image.gibbs
  rw [← map_gibbs hT, integral_map_equiv]
  rfl
theorem torusInv_torusMap (hT : S.PreservesTorus) (x : D.Torus) :
    S.torusInv (S.torusMap x) = x :=
  Function.leftInverse_invFun hT.2.2.1.1 x
theorem torusMap_torusInv (hT : S.PreservesTorus) (y : S.image.Torus) :
    S.torusMap (S.torusInv y) = y :=
  Function.rightInverse_invFun hT.2.2.1.2 y
theorem preservesObservables (hT : S.PreservesTorus) (E : Type*) [AddCommMonoid E] [Module ℝ E] :
    S.PreservesObservables E := by
  intro f U' _
  simp only [PeriodicLattice.smearedObservable]
  rw [← finsum_comp_equiv (torusFaceEquiv hT)]
  refine finsum_congr fun p => ?_
  change PeriodicLattice.plaquetteCost (S.torusPullback U') p • f p.barycenter =
    PeriodicLattice.plaquetteCost U' (S.torusFaceMap p) •
      f (S.torusInv (S.torusFaceMap p).barycenter)
  rw [plaquetteEnergy_torusPullback hT, hT.2.2.2.2.2.2.2.2.2.2.2 p, torusInv_torusMap hT]
theorem torusEuclidNorm_nonneg' {s : ℝ} (x : TorusMetric.Torus4 s) :
    0 ≤ TorusMetric.torusEuclidNorm x := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_nonneg <;> assumption
theorem sharpNormNonincreasing (hT : S.PreservesTorus) (E : Type*) [NormedAddCommGroup E]
    (f : D.Torus → E) : S.SharpNormNonincreasing E f := by
  intro hf M hM
  have hscale : 1 ≤ S.scale := one_le_pow₀ D.one_lt_factor.le
  have hsup : TestFunctions.uniformNorm (f ∘ S.torusInv) = TestFunctions.uniformNorm f := by
    simp only [TestFunctions.uniformNorm]
    exact (Function.Surjective.iSup_comp (g := fun x => ‖f x‖)
      (fun x => ⟨S.torusMap x, torusInv_torusMap hT x⟩))
  have hlip : TestFunctions.lipConstTorus (f ∘ S.torusInv) ≤ TestFunctions.lipConstTorus f := by
    refine csInf_le_csInf ⟨0, fun C hC => hC.1⟩ ?_ ?_
    · obtain ⟨C, hC, hCf⟩ := hf
      exact ⟨C, hC, hCf⟩
    · rintro C ⟨hC, hCf⟩
      refine ⟨hC, fun x y => (hCf _ _).trans ?_⟩
      refine mul_le_mul_of_nonneg_left ?_ hC
      have hd : TestFunctions.euclidDistTorus x y =
          S.scale * TestFunctions.euclidDistTorus (S.torusInv x) (S.torusInv y) := by
        have hxy := hT.2.2.2.1 (S.torusInv x) (S.torusInv y)
        rw [torusMap_torusInv hT, torusMap_torusInv hT] at hxy
        exact hxy
      rw [hd]
      exact le_mul_of_one_le_left (torusEuclidNorm_nonneg' _) hscale
  have h40 : (0 : ℝ) ≤ 40 * M := by linarith
  exact max_le_max hsup.le (mul_le_mul_of_nonneg_left hlip h40)
theorem preservesMeasures (hI : S.PreservesGridPoints) (hT : S.PreservesTorus) :
    S.PreservesMeasures :=
  ⟨⟨torusFieldsHomeomorph hT, fun _ => rfl⟩, (latticeFieldsHomeomorph hI.2.1).isHomeomorph,
    faceEnergy_pullback, fun U' _ p => plaquetteEnergy_torusPullback hT U' p,
    fun F _ => expect_eq hT F, fun F _ => expect_eq hT F,
    preservesObservables hT ℝ, preservesObservables hT ℂ,
    fun f => sharpNormNonincreasing hT ℝ f,
    fun f _ => sharpNormNonincreasing hT ℂ f,
    partition_eq hT⟩
theorem scalingPreservesMeasures_holds (hI : ScalingPreservesGridPoints)
    (hT : ScalingPreservesTorus) : ScalingPreservesMeasures :=
  fun D S => preservesMeasures (hI D S) (hT D S)
end YangMills.Construction.MirrorGridsAllSides.ScalingMeasures
end
