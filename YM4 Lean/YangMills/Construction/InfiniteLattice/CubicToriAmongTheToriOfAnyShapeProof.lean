import YangMills.Construction.InfiniteLattice.FunctionsOfASetOfBonds
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.InfiniteLattice.ContinuousLocalFunctionsAreDenseAndTestMeasuresProof
import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLattice
import YangMills.Construction.InfiniteLattice.CumulantsArePolynomialsInTheMomentsAndWeakLimits
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.LawInAState.TheLeastTorusLawUnderLatticeIsometriesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Function
noncomputable section
namespace YangMills.Construction.InfiniteLattice.CubicTorusAsQuotient
section
open PeriodicLattice (meshSize torusSide)
variable {L m K : ℕ}
theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem torusSide_pos (hL : 0 < L) (m : ℕ) : 0 < torusSide L m := by apply _root_.YangMills.SharedProofs.p34445 <;> assumption
open GibbsAtFixedSpacing TestFunctions
theorem meshSize_le_one (hL : 0 < L) (K : ℕ) : meshSize L (K : ℤ) ≤ 1 := by
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  simp only [meshSize, zpow_neg, zpow_natCast]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)
theorem torusSide_eq_mul (hL : 0 < L) (m K : ℕ) :
    torusSide L m = ((2 * (L : ℤ) ^ (m + K) : ℤ) : ℝ) * meshSize L (K : ℤ) := by apply _root_.YangMills.Construction.SourcesAndGluing.torusSide_eq_intCast_mul_meshSize <;> assumption
theorem three_mul_meshSize_lt_torusSide (hL : 13 ≤ L) (hm : 0 < m) (K : ℕ) :
    3 * meshSize L (K : ℤ) < torusSide L m := by
  have h0 : 0 < L := by omega
  have h1 := meshSize_le_one h0 K
  have h2 : (13 : ℝ) ≤ L := by exact_mod_cast hL
  have h3 : (L : ℝ) ≤ (L : ℝ) ^ m :=
    le_self_pow₀ (by linarith) hm.ne'
  unfold torusSide
  linarith
def periodPoint (hL : 0 < L) (m K : ℕ) (k : Fin 4 → ℤ) : LatticePoint (meshSize L (K : ℤ)) :=
  ⟨latticeTranslate (torusSide L m) k, fun μ => 2 * (L : ℤ) ^ (m + K) * k μ, fun μ => by
    simp only [latticeTranslate]
    rw [torusSide_eq_mul hL m K]
    push_cast
    ring⟩
theorem le_norm_latticeTranslate {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    ℓ ≤ ‖(latticeTranslate ℓ k : AmbientSpace)‖ := by apply _root_.YangMills.SharedProofs.p106002 <;> assumption
def cubicPeriodSublattice (hL : 13 ≤ L) (hm : 0 < m) (K : ℕ) :
    PeriodSublattice (meshSize L (K : ℤ)) where
  periods :=
    { carrier := {x | ∃ k, latticeTranslate (torusSide L m) k = (x : AmbientSpace)}
      add_mem' := by
        rintro x y ⟨k, hk⟩ ⟨k', hk'⟩
        exact ⟨k + k', by rw [latticeTranslate_add, hk, hk']; rfl⟩
      zero_mem' := ⟨0, by funext μ; simp [latticeTranslate]⟩
      neg_mem' := by
        rintro x ⟨k, hk⟩
        refine ⟨-k, ?_⟩
        funext μ
        have := congrFun hk μ
        simp only [latticeTranslate, Pi.neg_apply, Int.cast_neg, mul_neg] at this ⊢
        rw [this]
        rfl }
  exists_linearIndependent := by
    have h0 : 0 < L := by omega
    refine ⟨fun i => periodPoint h0 m K (Pi.single i 1), fun i => ⟨_, rfl⟩, ?_⟩
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrFun hg i
    simp only [periodPoint, latticeTranslate, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at h
    rw [Finset.sum_eq_single i] at h
    · have := (torusSide_pos h0 m).ne'
      simpa [this] using h
    · intro ν _ hν
      simp [Pi.single_eq_of_ne hν.symm]
    · simp
  le_norm_of_ne_zero := by
    rintro γ ⟨k, hk⟩ hγ
    have h0 : 0 < L := by omega
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hγ
      apply Subtype.ext
      rw [← hk]
      funext μ
      simp [latticeTranslate]
    have := le_norm_latticeTranslate (torusSide_pos h0 m) hk0
    have h3 := three_mul_meshSize_lt_torusSide hL hm K
    rw [hk] at this
    unfold minimalPeriodRatio
    linarith
theorem hasCubicPeriods_cubicPeriodSublattice (hL : 13 ≤ L) (hm : 0 < m) (K : ℕ) :
    (cubicPeriodSublattice hL hm K).HasCubicPeriods (torusSide L m) := by
  have h0 : 0 < L := by omega
  ext x
  constructor
  · rintro ⟨γ, ⟨k, hk⟩, rfl⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩
    exact ⟨periodPoint h0 m K k, ⟨k, rfl⟩, rfl⟩
section Cubic
variable {Γ : PeriodSublattice (meshSize L (K : ℤ))}
theorem projectPoint_eq_iff (h : Γ.HasCubicPeriods (torusSide L m))
    (x y : LatticePoint (meshSize L (K : ℤ))) :
    projectPoint L m (K : ℤ) x = projectPoint L m (K : ℤ) y ↔ x - y ∈ Γ.periods := by apply _root_.YangMills.SharedProofs.p44398 <;> assumption
theorem cubicPeriodSublatticeProperties (hL : 0 < L) (h : Γ.HasCubicPeriods (torusSide L m)) :
    CubicPeriodSublatticeProperties Γ (torusSide L m) := by apply _root_.YangMills.SharedProofs.p73080 <;> assumption
end Cubic
end
section
open PeriodicLattice (meshSize torusSide)
variable {L m K : ℕ}
section Cubic
variable {Γ : PeriodSublattice (meshSize L (K : ℤ))}
theorem isPositivelyOriented_projectLink_iff (hL : 0 < L) (h : Γ.HasCubicPeriods (torusSide L m))
    (b : Link (meshSize L (K : ℤ))) :
    (projectLink L m (K : ℤ) b).IsPositivelyOriented ↔ b.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7324 <;> assumption
theorem orbitLink_linkClass (h : Γ.HasCubicPeriods (torusSide L m))
    (b : PositiveLink (meshSize L (K : ℤ))) :
    Γ.orbitLink m (Γ.linkClass b) = projectLink L m (K : ℤ) b.1 := by apply _root_.YangMills.SharedProofs.p27953 <;> assumption
theorem isPositivelyOriented_orbitLink (hL : 0 < L) (h : Γ.HasCubicPeriods (torusSide L m))
    (ω : Γ.QuotientLink) : (Γ.orbitLink m ω).IsPositivelyOriented :=
  (isPositivelyOriented_projectLink_iff hL h _).2 (mem_range.1 ω.2).choose.2
theorem bijOn_orbitLink (hL : 0 < L) (h : Γ.HasCubicPeriods (torusSide L m)) :
    BijOn (Γ.orbitLink m) univ (PeriodicLattice.forwardBonds L m (K : ℤ)) := by apply _root_.YangMills.SharedProofs.p56004 <;> assumption
def orbitLinkEquiv (hL : 0 < L) (h : Γ.HasCubicPeriods (torusSide L m)) :
    Γ.QuotientLink ≃ PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) :=
  Equiv.ofBijective (fun ω => ⟨Γ.orbitLink m ω, isPositivelyOriented_orbitLink hL h ω⟩) (by
    constructor
    · intro ω ω' e
      exact (bijOn_orbitLink hL h).injOn (mem_univ _) (mem_univ _) (congrArg Subtype.val e)
    · rintro ⟨c, hc⟩
      obtain ⟨ω, -, e⟩ := (bijOn_orbitLink hL h).surjOn
        (PeriodicLattice.mem_positiveBonds_iff.2 hc)
      exact ⟨ω, Subtype.ext e⟩)
@[simp] theorem coe_orbitLinkEquiv (hL : 0 < L) (h : Γ.HasCubicPeriods (torusSide L m))
    (ω : Γ.QuotientLink) : (orbitLinkEquiv hL h ω).1 = Γ.orbitLink m ω := rfl
theorem lift_pullbackField (h : Γ.HasCubicPeriods (torusSide L m))
    (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)) :
    Γ.lift (Γ.pullbackConfig m U) = liftCompactField U := by apply _root_.YangMills.SharedProofs.p44760 <;> assumption
theorem gaugeFieldOfPositive_mem (hL : 2 ≤ L) (hm : 0 < m)
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → Matrices.ComplexMatrix2.specialUnitary) :
    PeriodicLattice.gaugeFieldOfPositive v ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ) := by
  have hj : -(m : ℤ) < (K : ℤ) := by omega
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · unfold PeriodicLattice.gaugeFieldOfPositive
    rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL hj b with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [dif_pos h1]
      exact (v _).2
    · rw [dif_neg h2, dif_pos h1, ← specialUnitary_coe_inv]
      exact (_ : Matrices.ComplexMatrix2.specialUnitary).2
  · unfold PeriodicLattice.gaugeFieldOfPositive
    rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL hj b with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h3 : b.opposite.opposite.IsPositivelyOriented := h1
      rw [dif_neg h2, dif_pos h3, dif_pos h1]
      rfl
    · rw [dif_pos h1, dif_neg h2, dif_pos h1, ← specialUnitary_coe_inv, ← specialUnitary_coe_inv,
        inv_inv]
theorem gaugeFieldOfPositive_linkValue (hL : 2 ≤ L) (hm : 0 < m)
    (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)) :
    PeriodicLattice.gaugeFieldOfPositive
      (fun c : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) => U.linkValue c.1) = U.1 := by
  have hj : -(m : ℤ) < (K : ℤ) := by omega
  funext b
  unfold PeriodicLattice.gaugeFieldOfPositive
  rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL hj b with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [dif_pos h1]
    rfl
  · rw [dif_neg h2, dif_pos h1]
    have := U.2.2 b.opposite (mem_univ _)
    have e : b.opposite.opposite = b := rfl
    rw [e] at this
    rw [this]
    rfl
def compactFieldOfQuotientField (hL : 13 ≤ L) (hm : 0 < m) (h : Γ.HasCubicPeriods (torusSide L m))
    (V : Γ.QuotientField) : PeriodicLattice.CompactGaugeField L m (K : ℤ) :=
  ⟨PeriodicLattice.gaugeFieldOfPositive fun c => V ((orbitLinkEquiv (by omega) h).symm c),
    gaugeFieldOfPositive_mem (by omega) hm _⟩
theorem linkValue_compactFieldOfQuotientField_of_pos (hL : 13 ≤ L) (hm : 0 < m)
    (h : Γ.HasCubicPeriods (torusSide L m)) (V : Γ.QuotientField)
    {b : PeriodicLattice.Bond L m (K : ℤ)} (hb : b.IsPositivelyOriented) :
    (compactFieldOfQuotientField hL hm h V).linkValue b =
      V ((orbitLinkEquiv (by omega) h).symm ⟨b, hb⟩) :=
  Subtype.ext (dif_pos hb)
theorem linkValue_compactFieldOfQuotientField_of_not_pos (hL : 13 ≤ L) (hm : 0 < m)
    (h : Γ.HasCubicPeriods (torusSide L m)) (V : Γ.QuotientField)
    {b : PeriodicLattice.Bond L m (K : ℤ)} (hb : ¬b.IsPositivelyOriented)
    (hr : b.opposite.IsPositivelyOriented) :
    (compactFieldOfQuotientField hL hm h V).linkValue b =
      (V ((orbitLinkEquiv (by omega) h).symm ⟨b.opposite, hr⟩))⁻¹ :=
  Subtype.ext (((dif_neg hb).trans (dif_pos hr)).trans (specialUnitary_coe_inv _).symm)
theorem isHomeomorph_pullbackField (hL : 13 ≤ L) (hm : 0 < m)
    (h : Γ.HasCubicPeriods (torusSide L m)) :
    IsHomeomorph (Γ.pullbackConfig m (j := (K : ℤ))) := by
  have h0 : 0 < L := by omega
  have hj : -(m : ℤ) < (K : ℤ) := by omega
  rw [isHomeomorph_iff_exists_inverse]
  refine ⟨continuous_pi fun ω => continuous_iInf_dom continuous_induced_dom,
    compactFieldOfQuotientField hL hm h, ?_, ?_, ?_⟩
  · intro U
    apply Subtype.ext
    have e : (fun c => Γ.pullbackConfig m U ((orbitLinkEquiv h0 h).symm c)) =
        fun c => U.linkValue c.1 := by
      funext c
      change U.linkValue (Γ.orbitLink m ((orbitLinkEquiv h0 h).symm c)) = U.linkValue c.1
      rw [← coe_orbitLinkEquiv h0 h, Equiv.apply_symm_apply]
    exact (congrArg PeriodicLattice.gaugeFieldOfPositive e).trans
      (gaugeFieldOfPositive_linkValue (by omega) hm U)
  · intro V
    funext ω
    have e := linkValue_compactFieldOfQuotientField_of_pos hL hm h V
      (isPositivelyOriented_orbitLink h0 h ω)
    exact e.trans (congrArg V ((orbitLinkEquiv h0 h).symm_apply_apply ω))
  · refine continuous_iInf_rng.2 fun b => continuous_induced_rng.2 ?_
    rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite (by omega : 2 ≤ L) hj b
      with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e : (fun V => (compactFieldOfQuotientField hL hm h V).linkValue b) =
          fun V : Γ.QuotientField => V ((orbitLinkEquiv h0 h).symm ⟨b, h1⟩) :=
        funext fun V => linkValue_compactFieldOfQuotientField_of_pos hL hm h V h1
      exact (continuous_apply ((orbitLinkEquiv h0 h).symm ⟨b, h1⟩)).congr
        (fun V => (congrFun e V).symm)
    · have e : (fun V => (compactFieldOfQuotientField hL hm h V).linkValue b) =
          fun V : Γ.QuotientField => (V ((orbitLinkEquiv h0 h).symm ⟨b.opposite, h1⟩))⁻¹ :=
        funext fun V => linkValue_compactFieldOfQuotientField_of_not_pos hL hm h V h2 h1
      exact (continuous_apply ((orbitLinkEquiv h0 h).symm ⟨b.opposite, h1⟩)).inv.congr
        (fun V => (congrFun e V).symm)
theorem measurable_pullbackFun : Measurable (Γ.pullbackFun m) := by apply _root_.YangMills.SharedProofs.p17634 <;> assumption
theorem measurable_gaugeFieldOfPositive (hL : 2 ≤ L) (hm : 0 < m) :
    Measurable (PeriodicLattice.gaugeFieldOfPositive (L := L) (m := m) (j := (K : ℤ))) := by
  have hs : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hs' : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hj : -(m : ℤ) < (K : ℤ) := by omega
  refine measurable_pi_iff.2 fun b => Continuous.measurable ?_
  unfold PeriodicLattice.gaugeFieldOfPositive
  rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL hj b with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [dif_pos h1]
    exact continuous_subtype_val.comp (continuous_apply _)
  · simp only [dif_neg h2, dif_pos h1, ← specialUnitary_coe_inv]
    exact continuous_subtype_val.comp (continuous_apply _).inv
theorem map_productHaarMeasure (hL : 13 ≤ L) (hm : 0 < m)
    (h : Γ.HasCubicPeriods (torusSide L m)) [Finite Γ.QuotientLink]
    (hR : ReflectionPositivity.CutoffMirrors.RelabelInvertMeasurePreserving) :
    (PeriodicLattice.productHaarMeasure L m (K : ℤ)).map (Γ.pullbackFun m) = Γ.quotientHaar := by
  have h0 : 0 < L := by omega
  have hf : Finite (PeriodicLattice.PositivelyOrientedBond L m (K : ℤ)) :=
    Finite.of_equiv _ (orbitLinkEquiv h0 h)
  unfold PeriodicLattice.productHaarMeasure PeriodicLattice.gaugeFieldHaar
  rw [Measure.map_map measurable_pullbackFun (measurable_gaugeFieldOfPositive (by omega) hm)]
  have e : Γ.pullbackFun m ∘ PeriodicLattice.gaugeFieldOfPositive =
      ReflectionPositivity.CutoffMirrors.relabelInvert (orbitLinkEquiv h0 h) (fun _ => 1) := by
    funext v ω
    apply Subtype.ext
    have hv := gaugeFieldOfPositive_mem (K := K) (by omega) hm v
    simp only [comp_apply, PeriodSublattice.pullbackFun, dif_pos hv]
    change PeriodicLattice.gaugeFieldOfPositive v (Γ.orbitLink m ω) = _
    unfold PeriodicLattice.gaugeFieldOfPositive ReflectionPositivity.CutoffMirrors.relabelInvert
    rw [dif_pos (isPositivelyOriented_orbitLink h0 h ω)]
    simp
    rfl
  rw [e]
  exact (hR _ _ (orbitLinkEquiv h0 h) (fun _ => 1)).2.1
section Plaquettes
variable {a : ℝ}
def plaquetteShift (p : ElementaryPlaquette a) (γ : LatticePoint a) : ElementaryPlaquette a :=
  ⟨p.corner + γ, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
theorem cornerSet_plaquetteShift (p : ElementaryPlaquette a) (γ : LatticePoint a) :
    (plaquetteShift p γ).cornerSet = (shift γ).pointMap '' p.cornerSet := by apply _root_.YangMills.DeltaSharedProofs.p501596 <;> assumption
theorem plaquetteMap_shift (hmv : GibbsAtFixedSpacing.SymmetriesTransportPlaquettes a) (p : ElementaryPlaquette a)
    (γ : LatticePoint a) : (shift γ).plaquetteMap p = plaquetteShift p γ :=
  ((hmv (shift γ)).1 p).1.unique ((hmv (shift γ)).1 p).2
    (cornerSet_plaquetteShift p γ)
end Plaquettes
theorem projectPlaquette_plaquetteShift (h : Γ.HasCubicPeriods (torusSide L m))
    (p : ElementaryPlaquette (meshSize L (K : ℤ))) {γ : LatticePoint (meshSize L (K : ℤ))}
    (hγ : γ ∈ Γ.periods) :
    TorusLifts.projectPlaquette L m (K : ℤ) (plaquetteShift p γ) =
      TorusLifts.projectPlaquette L m (K : ℤ) p :=
  PeriodicLattice.Plaquette.ext
    ((projectPoint_eq_iff h _ _).2 (by simpa [plaquetteShift] using hγ)) rfl rfl
theorem orbitPlaquette_class (h : Γ.HasCubicPeriods (torusSide L m))
    (hmv : GibbsAtFixedSpacing.SymmetriesTransportPlaquettes (meshSize L (K : ℤ)))
    (p : ElementaryPlaquette (meshSize L (K : ℤ))) :
    Γ.orbitPlaquette m ⟨Γ.plaquetteOrbit p, p, rfl⟩ =
      TorusLifts.projectPlaquette L m (K : ℤ) p := by
  unfold PeriodSublattice.orbitPlaquette
  obtain ⟨γ, hγ, e⟩ := (Γ.quotientPlaquette_nonempty ⟨Γ.plaquetteOrbit p, p, rfl⟩).some_mem
  rw [e, plaquetteMap_shift hmv, projectPlaquette_plaquetteShift h p hγ]
theorem bijective_orbitPlaquette (h : Γ.HasCubicPeriods (torusSide L m))
    (hmv : GibbsAtFixedSpacing.SymmetriesTransportPlaquettes (meshSize L (K : ℤ))) :
    Bijective (Γ.orbitPlaquette m) := by apply _root_.YangMills.SharedProofs.p33208 <;> assumption
end Cubic
end
section
open PeriodicLattice (meshSize torusSide)
open GibbsAtFixedSpacing TestFunctions
open GibbsAtFixedSpacing TestFunctions
open TorusMetric (euclidNormVec torusProj)
theorem norm_le_euclidNormVec (v : AmbientSpace) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.InfiniteLattice.ContinuousLocalDensity.norm_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul_norm (v : AmbientSpace) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.SharedProofs.p8643 <;> assumption
theorem continuous_of_isLipschitzFor {f : AmbientSpace → ℝ}
    (hf : IsLipschitzFor InfiniteLattice.euclidDist f) : Continuous f := by apply _root_.YangMills.Construction.TestPairs.continuous_of_isLipschitzFor_r4 <;> assumption
theorem isBounded_of_hasDiameterLE {A : Set AmbientSpace} {D : ℝ} (hA : HasDiameterLE A D) :
    Bornology.IsBounded A := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact Bornology.isBounded_empty
  · refine (Metric.isBounded_closedBall (x := x₀) (r := D)).subset fun x hx => ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (norm_le_euclidNormVec _).trans (hA x hx x₀ hx₀)
theorem eq_zero_of_add_latticeTranslate {E : Type*} [Zero E] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {A : Set AmbientSpace} {f : AmbientSpace → E} (hA : HasDiameterLE A (ℓ / 2))
    (hs : Function.support f ⊆ A) {x : AmbientSpace} (hx : f x ≠ 0) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    f (x + latticeTranslate ℓ k) = 0 := by
  by_contra h
  have h1 := hA _ (hs h) _ (hs hx)
  have h2 : x + latticeTranslate ℓ k - x = latticeTranslate ℓ k := by abel
  rw [h2] at h1
  have h3 := (le_norm_latticeTranslate hℓ hk).trans (norm_le_euclidNormVec _)
  linarith
theorem periodicSum_eq_self {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [T2Space E] {ℓ : ℝ}
    (hℓ : 0 < ℓ) {A : Set AmbientSpace} {f : AmbientSpace → E} (hA : HasDiameterLE A (ℓ / 2))
    (hs : Function.support f ⊆ A) {x : AmbientSpace} (hx : f x ≠ 0) :
    periodicSum ℓ f x = f x := by
  unfold periodicSum
  rw [tsum_eq_single 0 fun k hk => eq_zero_of_add_latticeTranslate hℓ hA hs hx hk]
  congr 1
  funext μ
  simp [latticeTranslate]
section Data
open LatticeCovering (spacingIndex)
variable (D : ReflectionPositivity.AxisMirror.MirrorData)
def periodTranslatePlaquette (p : ElementaryPlaquette (meshSize D.L (spacingIndex D)))
    (k : Fin 4 → ℤ) : ElementaryPlaquette (meshSize D.L (spacingIndex D)) :=
  ⟨p.corner + periodPoint (by have := D.isAdmissible.2; omega) D.m D.K k, p.lowAxis,
    p.highAxis, p.lowAxis_lt_highAxis⟩
theorem center_periodTranslatePlaquette (p : ElementaryPlaquette (meshSize D.L (spacingIndex D)))
    (k : Fin 4 → ℤ) :
    (periodTranslatePlaquette D p k).center = p.center + latticeTranslate (torusSide D.L D.m) k := by
  funext μ
  simp only [periodTranslatePlaquette, ElementaryPlaquette.center, periodPoint, Pi.add_apply]
  change (p.corner : AmbientSpace) μ + latticeTranslate (torusSide D.L D.m) k μ + _ + _ = _
  ring
theorem projectPlaquette_periodTranslatePlaquette
    (p : ElementaryPlaquette (meshSize D.L (spacingIndex D))) (k : Fin 4 → ℤ) :
    TorusLifts.projectPlaquette D.L D.m (spacingIndex D) (periodTranslatePlaquette D p k) =
      TorusLifts.projectPlaquette D.L D.m (spacingIndex D) p := by
  refine PeriodicLattice.Plaquette.ext ?_ rfl rfl
  apply Subtype.ext
  change torusProj _ ((p.corner : AmbientSpace) + latticeTranslate (torusSide D.L D.m) k) =
    torusProj _ (p.corner : AmbientSpace)
  exact torusProj_add_latticeTranslate _ _ _
theorem finsum_plaquettes_eq_smearedObservable (hcov : LatticeCovering.CoveringStatement)
    {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
    {A : Set AmbientSpace} {f : AmbientSpace → E} (hA : HasDiameterLE A (torusSide D.L D.m / 2))
    (hs : Function.support f ⊆ A)
    (U : PeriodicLattice.CompactGaugeField D.L D.m (spacingIndex D))
    (hfin : {p : ElementaryPlaquette (meshSize D.L (spacingIndex D)) |
      faceEnergy (liftCompactField U) p • f p.center ≠ 0}.Finite) :
    ∑ᶠ p : ElementaryPlaquette (meshSize D.L (spacingIndex D)),
        faceEnergy (liftCompactField U) p • f p.center =
      PeriodicLattice.smearedObservable (periodize (torusSide D.L D.m) f) U.1 := by
  classical
  have h0 : 0 < D.L := by have := D.isAdmissible.2; omega
  have hℓ := torusSide_pos h0 D.m
  obtain ⟨hfib, hbond, hpe, -⟩ := hcov D
  obtain ⟨-, -, -, -, hsurj, -, hbary⟩ := hbond
  obtain ⟨-, -, hact, -⟩ := hpe
  set C := TorusLifts.projectPlaquette D.L D.m (spacingIndex D) with hC
  set S := hfin.toFinset with hS
  have hmemS : ∀ p, p ∈ S ↔ faceEnergy (liftCompactField U) p • f p.center ≠ 0 :=
    fun p => by simp [hS]
  have hne : ∀ p ∈ S, f p.center ≠ 0 := fun p hp h => by
    apply (hmemS p).1 hp
    rw [h, smul_zero]
  have hinj : Set.InjOn C (S : Set _) := by
    intro p hp q hq hpq
    have hbase : torusProj (torusSide D.L D.m) (p.corner : AmbientSpace) =
        torusProj (torusSide D.L D.m) (q.corner : AmbientSpace) :=
      congrArg (fun c : PeriodicLattice.Plaquette D.L D.m (spacingIndex D) =>
        (c.origin : PeriodicLattice.FourTorus D.L D.m)) hpq
    have h1 : p.lowAxis = q.lowAxis := congrArg PeriodicLattice.Plaquette.firstAxis hpq
    have h2 : p.highAxis = q.highAxis := congrArg PeriodicLattice.Plaquette.secondAxis hpq
    obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq hbase
    have hb : p.center = q.center + latticeTranslate (torusSide D.L D.m) k := by
      simp only [ElementaryPlaquette.center, hk, h1, h2]
      abel
    by_cases hk0 : k = 0
    · subst hk0
      refine ElementaryPlaquette.ext (Subtype.ext ?_) h1 h2
      rw [hk]
      funext μ
      simp [latticeTranslate]
    · exact absurd (by rw [hb]; exact eq_zero_of_add_latticeTranslate hℓ hA hs (hne q hq) hk0)
        (hne p hp)
  have hval : ∀ p, f p.center ≠ 0 →
      periodize (torusSide D.L D.m) f (C p).barycenter = f p.center := fun p hp => by
    rw [hbary p, periodize_torusProj, periodicSum_eq_self hℓ hA hs hp]
  have hL : ∑ᶠ p : ElementaryPlaquette (meshSize D.L (spacingIndex D)),
        faceEnergy (liftCompactField U) p • f p.center =
      ∑ p ∈ S, faceEnergy (liftCompactField U) p • f p.center :=
    finsum_eq_sum_of_support_subset _ fun p hp => by simpa [hS] using hp
  have hR : PeriodicLattice.smearedObservable (periodize (torusSide D.L D.m) f) U.1 =
      ∑ c ∈ S.image C, PeriodicLattice.plaquetteCost U.1 c •
        periodize (torusSide D.L D.m) f c.barycenter := by
    refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
    obtain ⟨p, rfl⟩ := hsurj c
    have hc' : PeriodicLattice.plaquetteCost U.1 (C p) •
        periodize (torusSide D.L D.m) f (C p).barycenter ≠ 0 := hc
    have ht : periodize (torusSide D.L D.m) f (C p).barycenter ≠ 0 := fun h =>
      hc' (by rw [h, smul_zero])
    rw [hbary p, periodize_torusProj] at ht
    obtain ⟨k, hk⟩ : ∃ k, f (p.center + latticeTranslate (torusSide D.L D.m) k) ≠ 0 := by
      by_contra hcon
      simp only [ne_eq, not_exists, not_not] at hcon
      apply ht
      unfold periodicSum
      simp [hcon]
    have hq : f (periodTranslatePlaquette D p k).center ≠ 0 := by
      rwa [center_periodTranslatePlaquette]
    have hCq : C (periodTranslatePlaquette D p k) = C p :=
      projectPlaquette_periodTranslatePlaquette D p k
    have hmem : periodTranslatePlaquette D p k ∈ S := by
      rw [hmemS, hact, ← hval _ hq, hCq]
      exact hc'
    rw [Finset.coe_image]
    exact ⟨_, hmem, hCq⟩
  rw [hL, hR, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [hact, hval p (hne p hp)]
theorem meshSize_pos_of_mirrorData : 0 < meshSize D.L (spacingIndex D) := by apply _root_.YangMills.Construction.InfiniteLattice.LinkSetFunctions.mesh_pos <;> assumption
theorem finite_support_complex (hcum : CumulantsPolynomialInMomentsAndWeakLimits)
    {f : AmbientSpace → ℂ} (hb : IsBoundedFun f) {A : Set AmbientSpace} {d : ℝ}
    (hA : HasDiameterLE A d) (hs : Function.support f ⊆ A)
    (U : GaugeField (meshSize D.L (spacingIndex D))) :
    {p : ElementaryPlaquette (meshSize D.L (spacingIndex D)) |
      faceEnergy U p • f p.center ≠ 0}.Finite := by
  refine (((hcum.2.1 _ (meshSize_pos_of_mirrorData D)).1 f
    ⟨hb, (isBounded_of_hasDiameterLE hA).subset hs⟩).1).subset fun p hp h => hp ?_
  have := congrFun h U
  simp only [Pi.zero_apply] at this
  rw [Complex.real_smul, mul_comm]
  exact this
theorem finite_support_real (hcum : CumulantsPolynomialInMomentsAndWeakLimits)
    {f : AmbientSpace → ℝ} (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) {A : Set AmbientSpace} {d : ℝ}
    (hA : HasDiameterLE A d) (hs : Function.support f ⊆ A)
    (U : GaugeField (meshSize D.L (spacingIndex D))) :
    {p : ElementaryPlaquette (meshSize D.L (spacingIndex D)) |
      faceEnergy U p • f p.center ≠ 0}.Finite := by
  obtain ⟨C, hC⟩ := hb
  have hs' : Function.support (fun x => (f x : ℂ)) ⊆ A := fun x hx =>
    hs fun h => hx (by simp [h])
  refine (finite_support_complex D hcum (f := fun x => (f x : ℂ)) ⟨C, fun x => ?_⟩ hA hs' U).subset
    fun p hp h => hp ?_
  · simpa using hC x
  · have h' : ((faceEnergy U p • f p.center : ℝ) : ℂ) = 0 := by
      rw [← h, Complex.real_smul, smul_eq_mul]
      push_cast
      rfl
    exact_mod_cast h'
theorem mixedCumulant_congr_ae {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {n : ℕ}
    {X Y : Fin n → Ω → ℝ} (h : ∀ᵐ ω ∂ν, ∀ i, X i ω = Y i ω) :
    Cumulants.mixedCumulant ν X = Cumulants.mixedCumulant ν Y := by
  have hg : Cumulants.momentGeneratingFunction ν X = Cumulants.momentGeneratingFunction ν Y :=
    funext fun t => integral_congr_ae (h.mono fun ω hω => by simp only [hω])
  unfold Cumulants.mixedCumulant
  simp only [hg]
theorem wilsonGibbsMeasure_facts (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    IsProbabilityMeasure (PeriodicLattice.wilsonGibbsMeasure D.L D.m (D.K : ℕ) D.β) ∧
      ∀ᵐ U ∂PeriodicLattice.wilsonGibbsMeasure D.L D.m (D.K : ℕ) D.β,
        U ∈ PeriodicLattice.compactGaugeFields D.L D.m (spacingIndex D) := by
  obtain ⟨-, -, -, -, -, -, -, hp, hn, -⟩ := hW D.L D.m (D.K : ℕ) D.β
    (by have := D.isAdmissible.2; omega) D.m.pos D.K.pos
  exact ⟨hp, hn⟩
theorem plaquetteSmearingUnderProjection (hcum : CumulantsPolynomialInMomentsAndWeakLimits)
    (hcov : LatticeCovering.CoveringStatement)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    PlaquetteSmearingUnderProjection D.L D.m D.K D.β := by
  obtain ⟨hprob, hae⟩ := wilsonGibbsMeasure_facts D hW
  have hpoint : ∀ (f : AmbientSpace → ℂ), IsBoundedFun f →
      (∃ A : Set AmbientSpace, IsPeriodizable (torusSide D.L D.m) A f) →
      ∀ U : PeriodicLattice.CompactGaugeField D.L D.m (spacingIndex D),
        plaquetteSmearing f (liftCompactField U) =
          PeriodicLattice.smearedObservable (periodize (torusSide D.L D.m) f) U.1 := by
    rintro f hb ⟨A, hA, hs⟩ U
    rw [plaquetteSmearing_eq_smearedEnergy]
    exact finsum_plaquettes_eq_smearedObservable D hcov hA hs U
      (finite_support_complex D hcum hb hA hs _)
  refine ⟨hpoint, ?_, ?_⟩
  · rintro f hb ⟨A, hA, hs⟩
    have hmem := ((hcum.2.1 _ (meshSize_pos_of_mirrorData D)).1 f
      ⟨hb, (isBounded_of_hasDiameterLE hA).subset hs⟩).2.1
    have hm : Measurable (plaquetteSmearing f :
        GaugeField (meshSize D.L (spacingIndex D)) → ℂ) := hmem.2.1.1
    unfold liftedWilsonMeasure PeriodicLattice.gibbsExpectation
    rw [integral_map (measurable_liftField _ _ _).aemeasurable hm.aestronglyMeasurable]
    refine integral_congr_ae (hae.mono fun U hU => ?_)
    exact hpoint f hb ⟨A, hA, hs⟩ ⟨U, hU⟩
  · rintro n f ⟨hn, hlip, hcomp, -, A, hA, hsub⟩
    have hbd : ∀ i, IsBoundedBorelCompactlySupported (f i) := fun i =>
      isBoundedBorelCompactlySupported_of_continuous (continuous_of_isLipschitzFor (hlip i))
        (hcomp i)
    have hs : ∀ i, Function.support (f i) ⊆ A := fun i => (subset_tsupport _).trans (hsub i)
    have hX : ∀ j, Probability.IsBoundedRealRV
        (fun U : GaugeField (meshSize D.L (spacingIndex D)) => smearedEnergy (f j) U) := by
      intro j
      obtain ⟨C, hC⟩ := (hbd j).2.1
      have hs' : Function.support (fun x => (f j x : ℂ)) ⊆ A := fun x hx =>
        hs j fun h => hx (by simp [h])
      have hmem := ((hcum.2.1 _ (meshSize_pos_of_mirrorData D)).1 (fun x => (f j x : ℂ))
        ⟨⟨C, fun x => by simpa using hC x⟩, (isBounded_of_hasDiameterLE hA).subset hs'⟩).2.1
      have hre : (fun U : GaugeField (meshSize D.L (spacingIndex D)) => smearedEnergy (f j) U) =
          fun U => (plaquetteSmearing (fun x => (f j x : ℂ)) U).re := by
        funext U
        rw [plaquetteSmearing_ofReal, Complex.ofReal_re]
      rw [hre]
      obtain ⟨C', hC'⟩ := hmem.2.1.2
      exact ⟨Complex.measurable_re.comp hmem.2.1.1, C', fun U =>
        (Complex.abs_re_le_norm _).trans (hC' U)⟩
    change Cumulants.mixedCumulant (liftedWilsonMeasure D.L D.m (D.K : ℕ) D.β)
        (fun i U => smearedEnergy (f i) U) =
      Cumulants.mixedCumulant (PeriodicLattice.wilsonGibbsMeasure D.L D.m (D.K : ℕ) D.β)
        (fun i U => PeriodicLattice.smearedObservable (periodize (torusSide D.L D.m) (f i)) U)
    refine (hcum.2.2.2 _ _ (liftedWilsonMeasure D.L D.m (D.K : ℕ) D.β)
      (PeriodicLattice.wilsonGibbsMeasure D.L D.m (D.K : ℕ) D.β)
      (liftField D.L D.m (spacingIndex D)) (measurable_liftField _ _ _) rfl n _
      (by omega) hX).trans (mixedCumulant_congr_ae (hae.mono fun U hU i => ?_))
    exact finsum_plaquettes_eq_smearedObservable D hcov hA (hs i) ⟨U, hU⟩
      (finite_support_real D hcum (hbd i).2.1 hA (hs i) _)
theorem liftedWilsonMeasureIntegral (hcov : LatticeCovering.CoveringStatement) :
    LiftedWilsonMeasureIntegral D.L D.m D.K D.β := by
  obtain ⟨-, -, hpe, -⟩ := hcov D
  exact hpe.2.2.2.1
end Data
end
section
open PeriodicLattice (meshSize torusSide)
variable {L m K : ℕ}
open GibbsAtFixedSpacing TestFunctions
theorem map_withDensity_comp_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {f : X → Y} (hf : Measurable f) {g : Y → ENNReal} (hg : Measurable g) :
    (μ.withDensity (g ∘ f)).map f = (μ.map f).withDensity g := by apply _root_.YangMills.SharedProofs.p22819 <;> assumption
section Cubic
variable {Γ : PeriodSublattice (meshSize L (K : ℤ))}
theorem continuous_boltzmannWeight [Finite Γ.QuotientPlaquette]
    (hper : ∀ F : GaugeField (meshSize L (K : ℤ)) → ℝ, Continuous F → Continuous (Γ.periodize F))
    (β : ℝ) : Continuous (Γ.boltzmannWeight β) := by apply _root_.YangMills.SharedProofs.p17687 <;> assumption
theorem periodicBoltzmannWeight_eq (h : Γ.HasCubicPeriods (torusSide L m))
    (hmv : GibbsAtFixedSpacing.SymmetriesTransportPlaquettes (meshSize L (K : ℤ)))
    (hpl : ∀ (U : PeriodicLattice.CompactGaugeField L m (K : ℤ))
      (p : ElementaryPlaquette (meshSize L (K : ℤ))), faceEnergy (liftCompactField U) p =
        PeriodicLattice.plaquetteCost U.1 (TorusLifts.projectPlaquette L m (K : ℤ) p))
    (β : ℝ) {U : PeriodicLattice.Bond L m (K : ℤ) → Matrices.ComplexMatrix2}
    (hU : U ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ)) :
    PeriodicLattice.boltzmannWeight β U = Γ.boltzmannWeight β (Γ.pullbackFun m U) := by apply _root_.YangMills.SharedProofs.p63838 <;> assumption
theorem lift_comp_pullbackFun (h : Γ.HasCubicPeriods (torusSide L m)) :
    Γ.lift ∘ Γ.pullbackFun m = liftField L m (K : ℤ) := by apply _root_.YangMills.SharedProofs.p23053 <;> assumption
theorem quotientByCubicPeriods (hL : 13 ≤ L) (hm : 0 < m) (hK : 0 < K) (β : ℝ)
    (ho : PeriodSublatticeQuotientFacts)
    (hmv : GibbsAtFixedSpacing.SymmetriesTransportPlaquettes (meshSize L (K : ℤ)))
    (hR : ReflectionPositivity.CutoffMirrors.RelabelInvertMeasurePreserving)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hpl : ∀ (U : PeriodicLattice.CompactGaugeField L m (K : ℤ))
      (p : ElementaryPlaquette (meshSize L (K : ℤ))), faceEnergy (liftCompactField U) p =
        PeriodicLattice.plaquetteCost U.1 (TorusLifts.projectPlaquette L m (K : ℤ) p))
    (h : Γ.HasCubicPeriods (torusSide L m)) :
    QuotientByCubicPeriodsIsPeriodicLattice L m K β Γ := by
  have h0 : 0 < L := by omega
  have ha := meshSize_pos h0 (K : ℤ)
  obtain ⟨⟨-, -, hFB, hFP, -⟩, ⟨hcont, -, -⟩, ⟨-, -, hper⟩⟩ := ho _ ha Γ
  have := hFB
  have := hFP
  obtain ⟨-, -, -, -, -, -, hreal, -, -, -⟩ := hW L m K β (by omega) hm hK
  have hae : ∀ᵐ U ∂PeriodicLattice.productHaarMeasure L m (K : ℤ),
      U ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ) := mem_ae_iff.2 hreal
  have hmeas : Measurable (Γ.pullbackFun m) := measurable_pullbackFun
  have hmap := map_productHaarMeasure hL hm h hR
  have hwc := continuous_boltzmannWeight (fun F hF => hper ℝ F hF) β
  have hs : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hs' : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hwm : Measurable (Γ.boltzmannWeight β) := hwc.measurable
  have hZ : PeriodicLattice.partitionFunction L m K β = Γ.partitionFunction β := by
    have e : Γ.partitionFunction β = ∫ V, Γ.boltzmannWeight β V
        ∂(PeriodicLattice.productHaarMeasure L m (K : ℤ)).map (Γ.pullbackFun m) := by
      rw [hmap]
      rfl
    rw [e, integral_map hmeas.aemeasurable hwm.aestronglyMeasurable]
    exact integral_congr_ae (hae.mono fun U hU => periodicBoltzmannWeight_eq h hmv hpl β hU)
  have hdens : (PeriodicLattice.productHaarMeasure L m (K : ℤ)).withDensity
      (fun U => ENNReal.ofReal (PeriodicLattice.boltzmannWeight β U)) =
      (PeriodicLattice.productHaarMeasure L m (K : ℤ)).withDensity
        ((fun V => ENNReal.ofReal (Γ.boltzmannWeight β V)) ∘ Γ.pullbackFun m) :=
    withDensity_congr_ae (hae.mono fun U hU => by
      simp only [comp_apply]
      rw [periodicBoltzmannWeight_eq h hmv hpl β hU])
  have hWm : Γ.gibbsMeasure β =
      (PeriodicLattice.wilsonGibbsMeasure L m K β).map (Γ.pullbackFun m) := by
    unfold PeriodicLattice.wilsonGibbsMeasure PeriodSublattice.gibbsMeasure
    rw [Measure.map_smul, hdens, map_withDensity_comp_eq _ hmeas hwm.ennreal_ofReal, hmap, hZ]
  refine ⟨isPositivelyOriented_projectLink_iff h0 h, orbitLink_linkClass h, bijOn_orbitLink h0 h,
    isHomeomorph_pullbackField hL hm h, hmap, lift_pullbackField h,
    continuous_liftCompactField, orbitPlaquette_class h hmv,
    bijective_orbitPlaquette h hmv, hpl, hWm, ?_⟩
  unfold PeriodSublattice.liftedGibbsMeasure liftedWilsonMeasure
  rw [hWm, Measure.map_map hcont.measurable hmeas, lift_comp_pullbackFun h]
end Cubic
theorem statement_holds (h₁ : SymmetriesTransportLinksSupportsAndPlaquettes)
    (h₂ : PeriodSublatticeQuotientFacts)
    (h₃ : CumulantsPolynomialInMomentsAndWeakLimits)
    (h₄ : LatticeCovering.CoveringStatement)
    (h₅ : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (h₆ : ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies.Statement) :
    Statement := by
  intro s β hβ
  have hL : 13 ≤ s.L := s.isAdmissible.2
  have h0 : 0 < s.L := by omega
  have hm : 0 < (s.m : ℕ) := s.m.pos
  have hK : 0 < (s.K : ℕ) := s.K.pos
  let D : ReflectionPositivity.AxisMirror.MirrorData := ⟨s, β, hβ⟩
  let D' : ReflectionPositivity.CutoffMirrors.MirrorData := ⟨s, β, hβ, 0⟩
  have ha := meshSize_pos h0 ((s.K : ℕ) : ℤ)
  have hmv : GibbsAtFixedSpacing.SymmetriesTransportPlaquettes (meshSize s.L ((s.K : ℕ) : ℤ)) := (h₁ _ ha).2.2
  have hR : ReflectionPositivity.CutoffMirrors.RelabelInvertMeasurePreserving := (h₆ D').2.1
  have hpl := ((h₄ D).2.2.1).2.2.1
  exact ⟨⟨cubicPeriodSublattice hL hm _, hasCubicPeriods_cubicPeriodSublattice hL hm _⟩,
    fun Γ h => ⟨cubicPeriodSublatticeProperties h0 h,
      quotientByCubicPeriods hL hm hK β h₂ hmv hR h₅ hpl h⟩,
    liftedWilsonMeasureIntegral D h₄, plaquetteSmearingUnderProjection D h₃ h₄ h₅⟩
end
end YangMills.Construction.InfiniteLattice.CubicTorusAsQuotient
