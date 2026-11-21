import YangMills.Construction.InfiniteLattice.InvarianceOfTheTorusMeasuresUnderLatticeIsometries
import YangMills.Construction.InfiniteLattice.PlaquetteFunctionAndActionOfTheIsometries
import YangMills.Construction.InfiniteLattice.PullBackOfAConfigurationByAnInducedIsometry
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Function
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TorusMeasureSymmetry
open FixedSpacing (Params)
open LatticeCovering (descend spacingIndex mesh)
open InfiniteLattice (IsBoundedObservable latticeMotions latticeMotionField latticeMotionAct
  liftField liftCompactField liftedWilsonMeasure)
open InducedPullback (PreservesIntegrals productHaarOnFields)
section Paths
open PeriodicLattice
variable {L m K : ℕ}
theorem boundaryBonds_isLoop (q : Plaquette L m (K : ℤ)) :
    IsLoopAroundPlaquette q q.boundaryBonds := by
  refine ⟨rfl, ⟨q.origin, ?_, by simp [Plaquette.boundaryBonds], ?_, ?_⟩, ?_⟩
  · simp [IsBondPath, Plaquette.boundaryBonds, Bond.forwardFrom, Bond.opposite, add_right_comm]
  · simp [Plaquette.boundaryBonds, Bond.forwardFrom]
  · simp [Plaquette.boundaryBonds, Bond.forwardFrom, Bond.opposite]
  · ext x
    simp only [Plaquette.boundaryBonds, Plaquette.vertices, Bond.forwardFrom, Bond.opposite,
      List.mem_cons, List.not_mem_nil, or_false, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff,
      exists_eq_or_imp, exists_eq_left]
    rw [add_right_comm q.origin (unitStep L m (K : ℤ) q.secondAxis)]
    tauto
theorem isLoop_map_bondMap (s : TorusLatticeSymmetry L m K)
    (hs : ∀ b, s.IsBondImage b (s.bondMap b)) {p q : Plaquette L m (K : ℤ)}
    (hq : q.vertices = s.pointMap '' p.vertices) {γ : List (Bond L m (K : ℤ))}
    (hγ : IsLoopAroundPlaquette p γ) : IsLoopAroundPlaquette q (γ.map s.bondMap) := by
  have hsrc : ∀ b, (s.bondMap b).source = s.pointMap b.source :=
    fun b => congrArg Prod.fst (hs b)
  have htgt : ∀ b, (s.bondMap b).target = s.pointMap b.target :=
    fun b => congrArg Prod.snd (hs b)
  obtain ⟨hlen, ⟨x, hpath, -, hfirst, hlast⟩, hverts⟩ := hγ
  refine ⟨by simpa using hlen, ⟨s.pointMap x, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact List.isChain_map_of_isChain _ (fun a b h => by rw [htgt, hsrc, h]) hpath
  · intro h
    have h0 : γ = [] := by simpa using h
    simp [h0] at hlen
  · intro b hb
    rw [List.head?_map] at hb
    obtain ⟨c, hc, rfl⟩ := Option.mem_map.1 hb
    rw [hsrc, hfirst c hc]
  · intro b hb
    rw [List.getLast?_map] at hb
    obtain ⟨c, hc, rfl⟩ := Option.mem_map.1 hb
    rw [htgt, hlast c hc]
  · rw [hq, ← hverts]
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
      exact ⟨c.source, ⟨c, hc, rfl⟩, (hsrc c).symm⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨s.bondMap c, List.mem_map.2 ⟨c, hc, rfl⟩, hsrc c⟩
theorem plaquetteEnergy_pullback
    (hF : InfiniteLattice.PeriodicFaceEnergyProperties L m (K : ℤ))
    (s : TorusLatticeSymmetry L m K) (hs : ∀ b, s.IsBondImage b (s.bondMap b))
    {p q : Plaquette L m (K : ℤ)} (hq : q.vertices = s.pointMap '' p.vertices)
    (U : CompactGaugeField L m (K : ℤ)) :
    plaquetteCost (s.pullback U).1 p = plaquetteCost U.1 q := by
  have h := (hF q).1 U (p.boundaryBonds.map s.bondMap) q.boundaryBonds
    (isLoop_map_bondMap s hs hq (boundaryBonds_isLoop p)) (boundaryBonds_isLoop q)
  have e : pathHolonomy (s.pullback U).1 p.boundaryBonds =
      pathHolonomy U.1 (p.boundaryBonds.map s.bondMap) := by
    simp only [pathHolonomy, List.map_map]
    rfl
  unfold plaquetteCost plaquetteHolonomy
  rw [e, h]
end Paths
section Embedding
open PeriodicLattice
variable {L m : ℕ} {j : ℤ}
theorem isEmbedding_coe :
    Topology.IsEmbedding (fun U : CompactGaugeField L m j => U.1) := by
  refine ⟨⟨?_⟩, Subtype.val_injective⟩
  change (⨅ b : Bond L m j, TopologicalSpace.induced
      (fun U : CompactGaugeField L m j => CompactGaugeField.linkValue U b) inferInstance) = _
  simp only [Pi.topologicalSpace, induced_iInf, induced_compose]
  refine iInf_congr fun b => ?_
  change TopologicalSpace.induced _ (TopologicalSpace.induced Subtype.val _) = _
  rw [induced_compose]
  rfl
theorem measurableEmbedding_coe :
    MeasurableEmbedding (fun U : CompactGaugeField L m j => U.1) := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  refine Topology.IsClosedEmbedding.measurableEmbedding ⟨isEmbedding_coe, ?_⟩
  have : range (fun U : CompactGaugeField L m j => U.1) = compactGaugeFields L m j :=
    Subtype.range_val
  rw [this]
  exact isClosed_compactGaugeFields L m j
end Embedding
section Expectation
variable (D : Params)
theorem one_lt_L : 1 < D.L := by
  have := D.isAdmissible.2
  omega
theorem wilsonMean_eq_integral (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (Ψ : GaugeConfig D → ℂ) :
    wilsonMean D Ψ = (PeriodicLattice.partitionFunction D.L D.m D.K D.β)⁻¹ •
      ∫ U : GaugeConfig D, PeriodicLattice.boltzmannWeight D.β U.1 • Ψ U
        ∂productHaarOnFields D.L D.m (spacingIndex D) := by
  classical
  obtain ⟨-, -, hpos, hint, hZ, -, hnull, -⟩ :=
    hW D.L D.m D.K D.β (one_lt_L D) D.m.pos D.K.pos
  have hd : AEMeasurable (fun U => ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β U))
      (PeriodicLattice.productHaarMeasure D.L D.m (spacingIndex D)) :=
    hint.aemeasurable.ennreal_ofReal
  have hR : ∀ᵐ U ∂PeriodicLattice.productHaarMeasure D.L D.m (spacingIndex D),
      U ∈ PeriodicLattice.compactGaugeFields D.L D.m (spacingIndex D) := by
    rw [ae_iff]
    exact hnull
  have hemb := measurableEmbedding_coe (L := D.L) (m := D.m) (j := spacingIndex D)
  have hμ : PeriodicLattice.productHaarMeasure D.L D.m (spacingIndex D) =
      (productHaarOnFields D.L D.m (spacingIndex D)).map
        (fun U : PeriodicLattice.CompactGaugeField D.L D.m (spacingIndex D) => U.1) := by
    unfold productHaarOnFields
    rw [hemb.map_comap]
    have : range (fun U : PeriodicLattice.CompactGaugeField D.L D.m (spacingIndex D) => U.1) =
        PeriodicLattice.compactGaugeFields D.L D.m (spacingIndex D) := Subtype.range_val
    rw [this]
    exact (Measure.restrict_eq_self_of_ae_mem hR).symm
  unfold wilsonMean PeriodicLattice.gibbsExpectation PeriodicLattice.wilsonGibbsMeasure
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul₀ hd
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le]
  congr 1
  have hstep := hemb.integral_map (μ := productHaarOnFields D.L D.m (spacingIndex D))
    (fun U => (ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β U)).toReal •
      (if h : U ∈ PeriodicLattice.compactGaugeFields D.L D.m (spacingIndex D)
        then Ψ ⟨U, h⟩ else 0))
  rw [← hμ] at hstep
  rw [hstep]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  have hU : U.1 ∈ PeriodicLattice.compactGaugeFields D.L D.m (spacingIndex D) := U.2
  simp only [dif_pos hU]
  rw [ENNReal.toReal_ofReal (hpos U.1 U.2).le]
  rfl
end Expectation
variable {D : Params}
theorem preservesWilson_of_mapsPlaquettes
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) {s : TorusSymmetry D}
    (hpl : MapsPlaquettes s)
    (hν : PreservesIntegrals s (productHaarOnFields D.L D.m (spacingIndex D))) :
    PreservesWilson s := by
  rintro Φ ⟨hΦb, C, hC⟩
  obtain ⟨hbound, hcont, hpos, -⟩ :=
    hW D.L D.m D.K D.β (one_lt_L D) D.m.pos D.K.pos
  have hΦ : Measurable Φ := by
    have h : Measurable[borel (GaugeConfig D), borel ℂ] Φ := hΦb
    rwa [← (BorelSpace.measurable_eq : (inferInstance : MeasurableSpace ℂ) = borel ℂ)] at h
  have hdc : Continuous fun U : GaugeConfig D => PeriodicLattice.boltzmannWeight D.β U.1 :=
    hcont.comp_continuous isEmbedding_coe.continuous fun U => U.2
  have hd1 : ∀ U : GaugeConfig D, PeriodicLattice.boltzmannWeight D.β U.1 ≤ 1 := fun U => by
    have hA : 0 ≤ PeriodicLattice.wilsonAction U.1 :=
      finsum_nonneg fun p => (hbound U.1 U.2 p).1.1
    have := mul_nonneg D.β_pos.le hA
    unfold PeriodicLattice.boltzmannWeight
    exact Real.exp_le_one_iff.2 (by linarith)
  have hA : ∀ U : GaugeConfig D, PeriodicLattice.wilsonAction (s.pullback U).1 =
      PeriodicLattice.wilsonAction U.1 := fun U => by
    unfold PeriodicLattice.wilsonAction
    simp only [hpl.2.2 U]
    exact finsum_comp_equiv (Equiv.ofBijective _ hpl.2.1)
  have hinv := hν (fun U => PeriodicLattice.boltzmannWeight D.β U.1 • Φ U)
    (hdc.measurable.smul hΦ) ⟨C, fun U => by
      rw [norm_smul, Real.norm_of_nonneg (hpos U.1 U.2).le]
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC U)
      calc _ ≤ 1 * C := mul_le_mul (hd1 U) (hC U) (norm_nonneg _) zero_le_one
        _ = C := one_mul C⟩
  rw [wilsonMean_eq_integral D hW, wilsonMean_eq_integral D hW, ← hinv]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  change PeriodicLattice.boltzmannWeight D.β U.1 • Φ (s.pullback U) =
    PeriodicLattice.boltzmannWeight D.β (s.pullback U).1 • Φ (s.pullback U)
  unfold PeriodicLattice.boltzmannWeight
  rw [hA U]
theorem preservesLifted_of_preservesWilson
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hC : LatticeCovering.CoveringStatement) (r : latticeMotions (mesh D))
    {s : TorusSymmetry D} (hsr : s.toFun = descend D r.1) (hpr : PreservesWilson s) :
    PreservesLifted r := by
  classical
  intro F hF
  obtain ⟨-, -, ⟨hcont, -, -, hint, hbor, -⟩, hmot, -⟩ := hC D
  obtain ⟨-, -, -, -, -, -, -, -, hnull, -⟩ :=
    hW D.L D.m D.K D.β (one_lt_L D) D.m.pos D.K.pos
  have key : ∀ G : InfiniteLattice.GaugeField (mesh D) → ℂ, IsBoundedObservable G →
      ∫ V, G V ∂liftedWilsonMeasure D.L D.m (D.K : ℕ) D.β =
        wilsonMean D (G ∘ liftCompactField) := by
    intro G hG
    rw [hint G hG]
    unfold PeriodicLattice.gibbsExpectation wilsonMean PeriodicLattice.gibbsExpectation
    refine integral_congr_ae ?_
    have hR : ∀ᵐ U ∂PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β,
        U ∈ PeriodicLattice.compactGaugeFields D.L D.m (spacingIndex D) := by
      rw [ae_iff]
      exact hnull
    filter_upwards [hR] with U hU
    simp only [dif_pos hU]
    rfl
  rw [key _ (hF.latticeMotionAct r), key F hF]
  have hΦ : InfiniteLattice.LinkSetFunctions.IsBoundedBorel
      (F ∘ liftCompactField :
        PeriodicLattice.CompactGaugeField D.L D.m (spacingIndex D) → ℂ) := by
    obtain ⟨hm, c, hc⟩ := hF
    refine ⟨?_, c, fun U => hc _⟩
    have h : Measurable (F ∘ liftCompactField :
        PeriodicLattice.CompactGaugeField D.L D.m (spacingIndex D) → ℂ) := hm.comp hbor
    change Measurable[borel _, borel ℂ] _
    rwa [← (BorelSpace.measurable_eq : (inferInstance : MeasurableSpace ℂ) = borel ℂ)]
  have e : (latticeMotionAct r F ∘ liftCompactField :
      PeriodicLattice.CompactGaugeField D.L D.m (spacingIndex D) → ℂ) =
      fun U => (F ∘ liftCompactField) (s.pullback U) := by
    funext U
    have h := (hmot r).2.2.2.2.2.2.2 s hsr U
    change F (latticeMotionField r (liftCompactField U)) = F (liftCompactField _)
    rw [h]
  rw [e]
  exact hpr _ hΦ
theorem invarianceStatement_holds (hPull : InducedPullback.Statement)
    (hCov : LatticeCovering.CoveringStatement)
    (hWil : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hMaps : PeriodicLattice.SymmetriesPreserveBondsAndPlaquettes)
    (hAct : InfiniteLattice.FaceEnergyAndMotionStatement) : InvarianceStatement := by
  intro D r
  obtain ⟨w, hw, v, hv, hrv⟩ := r.2
  obtain ⟨⟨⟨ε, ι⟩, hει, -⟩, ⟨s, hs⟩, hall⟩ := hPull D r w hw v hv hrv
  obtain ⟨-, -, hPres⟩ := hall ε ι hει
  obtain ⟨-, -, hν⟩ := (hPres s hs).2.2
  obtain ⟨t, ht, -, -, hleft, hright⟩ := ((hCov D).2.2.2.1 r).2.2.2.2.2.1
  obtain ⟨w', hw', v', hv', htv⟩ := ht
  obtain ⟨-, ⟨s', hs'⟩, -⟩ :=
    hPull D ⟨t, w', hw', v', hv', htv⟩ w' hw' v' hv' htv
  have hmaps := (hMaps D.toStandingParameters).1
  have hreads : ∀ s₀ : TorusSymmetry D, ReadsBondImages s₀ := fun s₀ b => by
    classical
    have h : ∃ b', s₀.IsBondImage b b' := (hmaps s₀).1 b
    have e : s₀.bondMap b = h.choose := dif_pos h
    rw [e]
    exact h.choose_spec
  have hcorn : ∀ (s₀ : TorusSymmetry D) (p : PeriodicLattice.Plaquette D.L D.m (spacingIndex D)),
      (s₀.plaquetteMap p).vertices = s₀.pointMap '' p.vertices := fun s₀ p => by
    classical
    have h : ∃ p' : PeriodicLattice.Plaquette D.L D.m (spacingIndex D),
        p'.vertices = s₀.pointMap '' p.vertices := ((hmaps s₀).2.2 p).exists
    have e : s₀.plaquetteMap p = h.choose := dif_pos h
    rw [e]
    exact h.choose_spec
  have hinvolve : ∀ (s₁ s₂ : TorusSymmetry D), LeftInverse s₂.toFun s₁.toFun →
      ∀ p : PeriodicLattice.Plaquette D.L D.m (spacingIndex D),
        s₂.plaquetteMap (s₁.plaquetteMap p) = p := fun s₁ s₂ h p => by
    refine ((hmaps s₂).2.2 (s₁.plaquetteMap p)).unique (hcorn s₂ _) ?_
    rw [hcorn s₁, image_image]
    have : ∀ x, s₂.pointMap (s₁.pointMap x) = x := fun x => Subtype.ext (h x)
    simp [this]
  have hbij : Bijective s.plaquetteMap :=
    bijective_iff_has_inverse.2 ⟨s'.plaquetteMap,
      hinvolve s s' (by rw [hs, hs']; exact hleft),
      hinvolve s' s (by rw [hs, hs']; exact hright)⟩
  have hpl : MapsPlaquettes s := ⟨hcorn s, hbij, fun U p =>
    plaquetteEnergy_pullback (hAct D).2.1 s (hreads s) (hcorn s p) U⟩
  have hpr := preservesWilson_of_mapsPlaquettes hWil hpl hν
  exact ⟨⟨s, hs, hreads s, hpl, hpr⟩, preservesLifted_of_preservesWilson hWil hCov r hs hpr⟩
end YangMills.Construction.TorusMeasureSymmetry
end
