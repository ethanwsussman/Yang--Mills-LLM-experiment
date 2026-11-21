import YangMills.Construction.EuclideanFunctionals.BracketOfTheParametrixProof
import YangMills.Construction.EuclideanFunctionals.SmearingOfTheMoments
import YangMills.Construction.EuclideanFunctionals.VectorsOfPlatesAndTheProductFormula
import YangMills.Construction.ForwardTube.ShiftedTubesInLightConeCoordinates
import YangMills.Construction.RotationInvariance.DeterminationOfHolomorphicFunctionsOfTheDifferences
import YangMills.Construction.RotationInvariance.RadialBumpsExistAndMollifyInC1
import YangMills.Construction.RotationInvariance.RulesOfTheTranslationsAndMotionsOfPlates
import YangMills.Construction.RotationInvariance.SmearingOfPlatesByRadialBumps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.PlateSmearing
open RealPlane ForwardTube MeasureTheory
open scoped Pointwise
theorem planeComponent_add_embedFour (x : R4) (y : RealPlane) :
    planeComponent (x + embedFour y) = planeComponent x + y := by
  ext i
  fin_cases i <;>
    simp [planeComponent, embedFour, PeriodicLattice.coordVec]
theorem planeComponent_sub_embedFour (x : R4) (y : RealPlane) :
    planeComponent (x - embedFour y) = planeComponent x - y := by
  ext i
  fin_cases i <;>
    simp [planeComponent, embedFour, PeriodicLattice.coordVec]
theorem orthogonalComponent_add_embedFour (x : R4) (y : RealPlane) :
    orthogonalComponent (x + embedFour y) = orthogonalComponent x := by
  ext i
  fin_cases i <;>
    simp [orthogonalComponent, embedFour, PeriodicLattice.coordVec]
theorem orthogonalComponent_sub_embedFour (x : R4) (y : RealPlane) :
    orthogonalComponent (x - embedFour y) = orthogonalComponent x := by
  ext i
  fin_cases i <;>
    simp [orthogonalComponent, embedFour, PeriodicLattice.coordVec]
theorem planeComponent_embedFour (y : RealPlane) : planeComponent (embedFour y) = y := by
  rw [embedFour_eq_ofComponents, planeComponent_ofComponents]
theorem planeComponent_apply_zero (x : R4) : planeComponent x 0 = x 3 := by
  simp [planeComponent]
theorem abs_apply_three_le_euclidNorm (x : R4) :
    |x 3| ≤ Euclidean.euclidNorm x := by apply _root_.YangMills.Construction.EuclideanFunctionals.ParametrixBracket.abs_apply_three_le <;> assumption
def embedFourLinear : RealPlane →ₗ[ℝ] R4 where
  toFun := embedFour
  map_add' y y' := by
    funext i
    fin_cases i <;> simp [embedFour, PeriodicLattice.coordVec]
  map_smul' c y := by
    funext i
    fin_cases i <;> simp [embedFour, PeriodicLattice.coordVec]
theorem embedFourLinear_injective : Function.Injective embedFourLinear := by
  intro y y' h
  have h' : embedFour y = embedFour y' := h
  rw [← planeComponent_embedFour y, h', planeComponent_embedFour]
def timeSpacePlane : Submodule ℝ R4 := LinearMap.range embedFourLinear
def timeSpacePlaneLinearEquiv : RealPlane ≃ₗ[ℝ] timeSpacePlane :=
  LinearEquiv.ofInjective embedFourLinear embedFourLinear_injective
def timeSpacePlaneCLE : RealPlane ≃L[ℝ] timeSpacePlane :=
  timeSpacePlaneLinearEquiv.toContinuousLinearEquiv
def timeSpacePlaneMeasEquiv : RealPlane ≃ᵐ timeSpacePlane :=
  timeSpacePlaneCLE.toHomeomorph.toMeasurableEquiv
theorem timeSpacePlaneMeasEquiv_coe (y : RealPlane) :
    ((timeSpacePlaneMeasEquiv y : timeSpacePlane) : R4) = embedFour y :=
  rfl
def timeSpacePlaneMeasure : Measure timeSpacePlane := Measure.map timeSpacePlaneMeasEquiv volume
theorem exists_normPreserving_param (κ : ℕ) (hκ : κ = 2) :
    ∃ T : (Fin κ → ℝ) →ₗ[ℝ] timeSpacePlane, Function.Surjective T ∧
      (∀ y, EuclideanFunctions.euclideanNorm (T y : R4) =
        EuclideanFunctions.euclideanNorm y) ∧
      timeSpacePlaneMeasure = Measure.map T volume := by
  subst hκ
  let L : (Fin 2 → ℝ) ≃ₗ[ℝ] RealPlane := (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm
  refine ⟨(L.trans timeSpacePlaneLinearEquiv).toLinearMap,
    (L.trans timeSpacePlaneLinearEquiv).surjective, ?_, ?_⟩
  · intro y
    have hT : (((L.trans timeSpacePlaneLinearEquiv).toLinearMap y : timeSpacePlane) : R4) =
        embedFour (L y) := rfl
    rw [hT]
    simp only [EuclideanFunctions.euclideanNorm, Fin.sum_univ_four, Fin.sum_univ_two]
    congr 1
    simp [embedFour, PeriodicLattice.coordVec, L]
    ring
  · have hv : (volume : Measure RealPlane) = Measure.map L volume :=
      (PiLp.volume_preserving_toLp (Fin 2)).map_eq.symm
    have hL : Measurable L := (PiLp.volume_preserving_toLp (Fin 2)).measurable
    rw [timeSpacePlaneMeasure, hv, Measure.map_map timeSpacePlaneMeasEquiv.measurable hL]
    rfl
theorem timeSpacePlaneMeasure_isLebesgueOn :
    Smearing.IsLebesgueOn timeSpacePlane timeSpacePlaneMeasure := by
  have hfin : Module.finrank ℝ timeSpacePlane = 2 := by
    rw [← LinearEquiv.finrank_eq timeSpacePlaneLinearEquiv]
    simp
  obtain ⟨T, hs, hn, hm⟩ := exists_normPreserving_param _ hfin
  exact Or.inr ⟨by omega, T, ⟨hs, hn⟩, hm⟩
theorem integral_pi_timeSpacePlaneMeasure (n : ℕ) (F : (Fin n → timeSpacePlane) → ℂ) :
    ∫ z, F z ∂(Measure.pi fun _ : Fin n => timeSpacePlaneMeasure) =
      ∫ y : Fin n → RealPlane, F fun i => timeSpacePlaneMeasEquiv (y i) := by
  have : SigmaFinite timeSpacePlaneMeasure := timeSpacePlaneMeasEquiv.sigmaFinite_map
  have hmp : MeasurePreserving
      (MeasurableEquiv.piCongrRight fun _ : Fin n => timeSpacePlaneMeasEquiv)
      (volume : Measure (Fin n → RealPlane)) (Measure.pi fun _ => timeSpacePlaneMeasure) := by
    rw [volume_pi]
    exact measurePreserving_pi (fun _ => volume) (fun _ => timeSpacePlaneMeasure)
      fun _ => ⟨timeSpacePlaneMeasEquiv.measurable, rfl⟩
  exact (hmp.integral_comp' F).symm
theorem conv_productFunction (b α : RealPlane → ℂ) (φ : RealPlane → ℝ) (x : R4) :
    Smearing.conv timeSpacePlaneMeasure (fun z => b (timeSpacePlaneMeasEquiv.symm z))
      (productFunction α φ) x = productFunction (convolve b α) φ x := by
  unfold Smearing.conv timeSpacePlaneMeasure
  rw [integral_map_equiv]
  simp only [MeasurableEquiv.symm_apply_apply, timeSpacePlaneMeasEquiv_coe, productFunction,
    planeComponent_sub_embedFour, orthogonalComponent_sub_embedFour, convolve]
  rw [← integral_mul_const]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp [mul_assoc])
theorem lt_sub_of_lt_consecutive_gaps {q : ℕ} {η : ℝ} (hη : 0 ≤ η) {s : Fin (q + 1) → ℝ}
    (h : ∀ i : Fin q, η < s i.succ - s i.castSucc) {k l : Fin (q + 1)} (hkl : k < l) :
    η < s l - s k := by
  have hmono : StrictMono s := Fin.strictMono_iff_lt_succ.2 fun i => by
    have := h i
    linarith
  obtain ⟨l', rfl⟩ := Fin.exists_succ_eq.2 (Fin.ne_zero_of_lt hkl)
  have hk : k ≤ l'.castSucc := Fin.le_castSucc_iff.2 hkl
  have := hmono.monotone hk
  have := h l'
  linarith
def envelope (r : ℝ) (b : RealPlane → ℂ) (φ : RealPlane → ℝ) : Set R4 :=
  {x | planeComponent x ∈ tsupport b + closedDiscAt 0 r ∧ orthogonalComponent x ∈ tsupport φ}
theorem isCompact_closedDiscAt (r : ℝ) : IsCompact (closedDiscAt (0 : RealPlane) r) := by
  have : closedDiscAt (0 : RealPlane) r = Metric.closedBall 0 r := by
    ext y
    simp [closedDiscAt]
  rw [this]
  exact isCompact_closedBall 0 r
theorem isCompact_envelope (r : ℝ) {b : RealPlane → ℂ} {φ : RealPlane → ℝ}
    (hb : HasCompactSupport b) (hφ : HasCompactSupport φ) :
    IsCompact (envelope r b φ) := by
  have hc : Continuous fun p : RealPlane × RealPlane => ofComponents p.1 p.2 := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp [ofComponents] <;> fun_prop
  have himage : envelope r b φ =
      (fun p : RealPlane × RealPlane => ofComponents p.1 p.2) ''
        ((tsupport b + closedDiscAt 0 r) ×ˢ tsupport φ) := by
    ext x
    constructor
    · intro hx
      exact ⟨(planeComponent x, orthogonalComponent x), ⟨hx.1, hx.2⟩,
        ofComponents_planeComponent_orthogonalComponent x⟩
    · rintro ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa [planeComponent_ofComponents] using hy
      · simpa [orthogonalComponent_ofComponents] using hz
  rw [himage]
  exact ((IsCompact.add hb (isCompact_closedDiscAt r)).prod hφ).image hc
theorem exists_near_time_of_mem_envelope {r : ℝ} {b : RealPlane → ℂ} {φ : RealPlane → ℝ}
    {x : R4} (hx : x ∈ envelope r b φ) :
    ∃ y ∈ tsupport b, |x 3 - y 0| ≤ r := by
  obtain ⟨y, hy, w, hw, hyw⟩ := Set.mem_add.1 hx.1
  refine ⟨y, hy, ?_⟩
  have hw' : ‖w‖ ≤ r := by simpa [closedDiscAt] using hw
  have h0 : x 3 - y 0 = w 0 := by
    rw [← planeComponent_apply_zero x, ← hyw]
    simp
  rw [h0]
  exact le_trans (PiLp.norm_apply_le w 0) hw'
theorem plateSmearingStatement_of_lemmas
    (hmoll : RadialMollifiers.ExistAndConvergeC1)
    (hmot : TranslationRules.TranslationAndMotionFacts)
    (hsm : Smearing.Holds)
    (hprod : PlateVectorsProduct.Holds)
    (huniq : HolomorphicDifferences.determinedByProductIntegrals)
    (htub : ShiftedTubeCoords.Holds) : PlateSmearingStatement := by
  intro m S d q hq φ hφ η hη0 hη1 δ hδ b hb hg
  obtain ⟨hc0, hc1⟩ := d.base.frac_mem
  obtain ⟨-, hmotions, hplates, -⟩ := hmot
  have hm := (hmoll m S d η ⟨hη0, hη1⟩).2 δ hδ
  have hconv : ∀ (j : ℕ+) (i : Fin (q + 1)), mollifiedProfile (b i) δ j ∈ complexProfiles ∧
      tsupport (mollifiedProfile (b i) δ j) ⊆
        tsupport (b i) + closedDiscAt 0 (d.base.frac * η) :=
    fun j i => (hm (b i) (hb i) (φ i) (hφ i)).1 j
  have hgap : ∀ y : Fin (q + 1) → RealPlane, (∀ i, y i ∈ tsupport (b i)) →
      ∀ i : Fin q, η < y i.succ 0 - y i.castSucc 0 := by
    intro y hy i
    have h : η < (y i.succ - y i.castSucc) 0 :=
      (huniq (q + 1) (by omega) η hη0.le).1 b hg y hy i
    rwa [PiLp.sub_apply] at h
  have hne : ∀ i, (tsupport (b i)).Nonempty := by
    intro i
    obtain ⟨y, hy⟩ : ∃ y, b i y ≠ 0 := by
      by_contra hcon
      exact hg.2.2.1 i (funext fun y => by_contra fun h => hcon ⟨y, h⟩)
    exact ⟨y, subset_tsupport _ hy⟩
  choose y₀ hy₀ using hne
  have hsep : ∀ {k l : Fin (q + 1)}, k < l → ∀ y ∈ tsupport (b k), ∀ y' ∈ tsupport (b l),
      η < y' 0 - y 0 := by
    intro k l hkl y hy y' hy'
    classical
    have hkl' : k ≠ l := hkl.ne
    let t : Fin (q + 1) → RealPlane := Function.update (Function.update y₀ k y) l y'
    have htl : t l = y' := by simp [t]
    have htk : t k = y := by simp [t, hkl']
    have ht : ∀ i, t i ∈ tsupport (b i) := by
      intro i
      by_cases h1 : i = l
      · subst h1
        rwa [htl]
      · by_cases h2 : i = k
        · subst h2
          rwa [htk]
        · simpa [t, h1, h2] using hy₀ i
    have h := lt_sub_of_lt_consecutive_gaps hη0.le (s := fun i => t i 0) (hgap t ht) hkl
    simpa only [htl, htk] using h
  let A : Fin (q + 1) → Set R4 :=
    fun i => envelope (d.base.frac * η) (b i) (φ i)
  have hfar : ∀ {k l : Fin (q + 1)}, k < l → ∀ x ∈ A k, ∀ x' ∈ A l, η / 2 < x' 3 - x 3 := by
    intro k l hkl x hx x' hx'
    obtain ⟨y, hy, h1⟩ := exists_near_time_of_mem_envelope hx
    obtain ⟨y', hy', h2⟩ := exists_near_time_of_mem_envelope hx'
    have h3 := hsep hkl y hy y' hy'
    have h4 := abs_le.1 h1
    have h5 := abs_le.1 h2
    have h6 : d.base.frac * η < η / 4 := by nlinarith
    linarith [h4.1, h4.2, h5.1, h5.2]
  have hdist : ∀ {k l : Fin (q + 1)}, k ≠ l → ∀ x ∈ A k, ∀ x' ∈ A l,
      η / 2 < Euclidean.euclidNorm (x - x') := by
    intro k l hkl x hx x' hx'
    have ha := abs_apply_three_le_euclidNorm (x - x')
    have he : (x - x') 3 = x 3 - x' 3 := rfl
    rw [he] at ha
    rcases lt_or_gt_of_ne hkl with h | h
    · have h1 := hfar h x hx x' hx'
      have h2 := neg_abs_le (x 3 - x' 3)
      linarith
    · have h1 := hfar h x' hx' x hx
      have h2 := le_abs_self (x 3 - x' 3)
      linarith
  have hdisj : ∀ {k l : Fin (q + 1)}, k ≠ l → Disjoint (A k) (A l) := by
    intro k l hkl
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    have h := hdist hkl x hx x hx'
    have h0 : Euclidean.euclidNorm (x - x) = 0 := by
      simp [Euclidean.euclidNorm]
    rw [h0] at h
    linarith
  have hsupp : ∀ α ∈ complexProfiles, ∀ i, tsupport α ⊆
      tsupport (b i) + closedDiscAt 0 (d.base.frac * η) →
        supp (productFunction α (φ i)) ⊆ A i := by
    intro α hα i hs x hx
    have h := (hplates α hα (φ i) (hφ i)).2 hx
    exact ⟨hs h.1, h.2⟩
  have hself : ∀ i, tsupport (b i) ⊆
      tsupport (b i) + closedDiscAt 0 (d.base.frac * η) := by
    intro i y hy
    refine Set.mem_add.2 ⟨y, hy, 0, ?_, add_zero y⟩
    simpa [closedDiscAt] using (mul_pos hc0 hη0).le
  have hsets : IsSeparatedEnvelope η A b δ φ := by
    unfold IsSeparatedEnvelope
    refine ⟨fun i => isCompact_envelope _ (hb i).2 (hφ i).2, fun k l hkl => ?_,
      fun i => ⟨hsupp _ (hb i) i (hself i), fun j => hsupp _ (hconv j i).1 i (hconv j i).2⟩⟩
    unfold Euclidean.euclidSetDist
    exact le_iInf₂ fun x hx => le_iInf₂ fun x' hx' =>
      ENNReal.ofReal_le_ofReal (hdist hkl x hx x' hx').le
  refine ⟨⟨A, hsets⟩, fun j => ?_⟩
  unfold MollifiedIdentityAt
  refine ⟨fun i => (hconv j i).1, fun k l hkl => ?_, fun y hy => ?_, ?_⟩
  · exact (hdisj hkl).mono ((hsets.2.2 k).2 j) ((hsets.2.2 l).2 j)
  · have hreal := (htub q hq η hη0 hη1).2.2.1.1
    have hmem : embedPlaneTuple (fun i : Fin q => y i.succ - y i.castSucc) ∈
        realLocus (shiftedForwardTubePow q η) := by
      rw [hreal]
      refine ⟨_, fun i => ?_, rfl⟩
      have h1 := hgap y hy i
      show (y i.succ - y i.castSucc) 0 > η / 2
      rw [PiLp.sub_apply]
      linarith
    exact hmem.1
  · have hδp := hδ.ofRealFun_mem hη0 j
    let bE : Fin (q + 1) → timeSpacePlane → ℂ := fun l z => b l (timeSpacePlaneMeasEquiv.symm z)
    let h : Fin (q + 1) → R4 → ℂ := fun l => productFunction (ofRealFun (δ j)) (φ l)
    have hdata : Smearing.Data A h bE :=
      { compact := hsets.1
        pairwise_disjoint := fun k l hkl => hdisj hkl
        mem_C1c := fun l => (hplates _ hδp.1 _ (hφ l)).1
        cont := fun l => (hb l).1.continuous.comp timeSpacePlaneCLE.symm.continuous
        compactSupport := fun l =>
          (hb l).2.comp_homeomorph timeSpacePlaneCLE.symm.toHomeomorph
        conv_supp := by
          intro l hl
          rintro _ ⟨x, hx, _, ⟨z, hz, rfl⟩, rfl⟩
          have hpl := (hplates _ hδp.1 _ (hφ l)).2 hx
          have hz' : timeSpacePlaneMeasEquiv.symm z ∈ tsupport (b l) := by
            have hc : tsupport (bE l) =
                timeSpacePlaneCLE.symm.toHomeomorph ⁻¹' tsupport (b l) :=
              tsupport_comp_eq_preimage (b l) timeSpacePlaneCLE.symm.toHomeomorph
            have hz2 : z ∈ tsupport (bE l) := hz
            rw [hc] at hz2
            exact hz2
          have hzc : (z : R4) = embedFour (timeSpacePlaneMeasEquiv.symm z) := by
            have h1 := timeSpacePlaneMeasEquiv_coe (timeSpacePlaneMeasEquiv.symm z)
            rwa [MeasurableEquiv.apply_symm_apply] at h1
          rw [hzc]
          refine ⟨?_, ?_⟩
          · rw [planeComponent_add_embedFour, add_comm (planeComponent x)]
            refine Set.mem_add.2 ⟨_, hz', _, ?_, rfl⟩
            have h1 : ‖planeComponent x - 0‖ < d.base.frac * η := hδp.2 hpl.1
            exact h1.le
          · rw [orthogonalComponent_add_embedFour]
            exact hpl.2
        rest_supp := fun l hl => absurd l.is_lt hl }
    have hform := (hsm.2 m S d.base.sigma (q + 1) (q + 1) (by omega) (by omega) le_rfl
      timeSpacePlane timeSpacePlaneMeasure timeSpacePlaneMeasure_isLebesgueOn A h bE hdata).2.2.1
    have hL : Smearing.convEntries timeSpacePlaneMeasure bE h =
        mollifiedProducts b δ φ j := by
      funext l x
      simp only [Smearing.convEntries]
      rw [dif_pos l.is_lt]
      exact conv_productFunction (b l) (ofRealFun (δ j)) (φ l) x
    rw [hL, integral_pi_timeSpacePlaneMeasure] at hform
    refine hform.trans ?_
    unfold profileIntegral
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show Smearing.integrand S bE h (fun i => timeSpacePlaneMeasEquiv (y i)) =
      profileIntegrand b
        (fun y => d.mollifiedKernel η δ φ j (complexDifferences y)) y
    unfold profileIntegrand Smearing.integrand
    by_cases hy : y ∈ Set.univ.pi fun i => tsupport (b i)
    · rw [Set.indicator_of_mem hy]
      have hyi : ∀ i, y i ∈ tsupport (b i) := fun i => hy i (Set.mem_univ i)
      have hprodb : ∏ l, bE l (timeSpacePlaneMeasEquiv (y l)) = ∏ i, b i (y i) :=
        Finset.prod_congr rfl fun l _ => by simp [bE]
      rw [hprodb]
      congr 1
      have htr : Smearing.shiftSmearingTuple (fun i => timeSpacePlaneMeasEquiv (y i)) h =
          PlateVectorsProduct.productsOfShiftedProfiles y
            (fun _ => ofRealFun (δ j)) φ := by
        funext l
        simp only [Smearing.shiftSmearingTuple]
        rw [dif_pos l.is_lt]
        exact (hmotions _ hδp.1 _ (hφ l) (y l) 0).1
      let C : (RealPlane → ℝ) → ℝ := fun ψ =>
        open Classical in if hψ : ψ ∈ realLabels then d.base.labelConst ⟨ψ, hψ⟩ else 0
      have hC : ∀ ψ ∈ realLabels, ProductBoundWith d.base.sigma
          d.base.expo_pos d.base.frac_mem ψ (C ψ) := by
        intro ψ hψ
        simp only [C, dif_pos hψ]
        exact d.base.boundWith_labelConst ⟨ψ, hψ⟩
      have hPF := (hprod m S d.base.sigma d.base.expo d.base.frac
        d.base.expo_pos d.base.frac_mem C d.base.productBoundWithExponent hC
        d.base.cone η hη0 hη1).2 q (fun _ => ofRealFun (δ j)) φ
        (fun a => ⟨hφ a, hδp.1, hδp.2⟩)
      have hhalf : ∀ i, η / 2 ≤
          PlateVectorsProduct.successiveDiffs y i 0 := by
        intro i
        have h1 := hgap y hyi i
        show η / 2 ≤ (y i.succ - y i.castSucc) 0
        rw [PiLp.sub_apply]
        linarith
      have hval := (hPF.2.2 y hhalf).2
      unfold Smearing.valueAt
      rw [htr]
      exact hval
    · rw [Set.indicator_of_notMem hy]
      obtain ⟨i, hi⟩ : ∃ i, y i ∉ tsupport (b i) := by
        simpa [Set.mem_pi] using hy
      have hz : bE i (timeSpacePlaneMeasEquiv (y i)) = 0 := by
        simpa [bE] using image_eq_zero_of_notMem_tsupport hi
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, zero_mul]
end YangMills.Construction.EuclideanFunctionals.PlateSmearing
end
