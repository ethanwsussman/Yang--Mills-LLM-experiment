import YangMills.Construction.Towers.CurvesReadInTheChartAtOneProof
import YangMills.Construction.Lattice.MatrixValuedFormOperators
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMaps
import YangMills.Construction.Towers.ChartAtOneOnTheConfigurationsProof
import YangMills.Construction.Towers.MapsReadBackFromTheChartAtOne
import YangMills.Construction.Towers.RealAnalyticMapsAreReadInTheChartAtOne
import YangMills.Construction.Towers.RealAnalyticMapsOfConfigurationsAreDifferentiableProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus YangMills.Construction.IdentityExpChart
open scoped Matrix.Norms.L2Operator Topology NNReal ENNReal
noncomputable section
namespace YangMills.Construction.Tower.IdentityChartPullback
section Series
variable {N : ℕ}
abbrev LetterWord (N : ℕ) : Type := Σ n : ℕ, (Fin n → Fin N)
def letterMultiplicity (x : LetterWord N) : Fin N → ℕ :=
  fun j => (Finset.univ.filter fun i => x.2 i = j).card
theorem sum_letterMultiplicity (x : LetterWord N) : ∑ j, letterMultiplicity x j = x.1 := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin x.1)))
    (t := (Finset.univ : Finset (Fin N))) (f := x.2) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  simpa [letterMultiplicity] using h.symm
theorem finite_words_of_multiplicity (m : Fin N → ℕ) :
    Finite {x : LetterWord N // letterMultiplicity x = m} := by
  have hs : ({x : LetterWord N | letterMultiplicity x = m}).Finite := by
    refine (Set.finite_range fun w : Fin (∑ j, m j) → Fin N => (⟨_, w⟩ : LetterWord N)).subset ?_
    rintro ⟨n, w⟩ hx
    have hn : n = ∑ j, m j := by
      rw [← (show letterMultiplicity (⟨n, w⟩ : LetterWord N) = m from hx)]
      exact (sum_letterMultiplicity ⟨n, w⟩).symm
    subst hn
    exact ⟨w, rfl⟩
  exact hs.to_subtype
theorem prod_apply_word (h : Fin N → ℝ) (x : LetterWord N) :
    ∏ i, h (x.2 i) = ∏ j, h j ^ letterMultiplicity x j := by
  rw [← Finset.prod_fiberwise Finset.univ x.2 (fun i => h (x.2 i))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.prod_const]
  rfl
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem multilinear_diag_eq_sum_basis {n : ℕ}
    (q : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin N → ℝ) F) (h : Fin N → ℝ) :
    q (fun _ => h) = ∑ w : Fin n → Fin N,
      (∏ i, h (w i)) • q (fun i => Pi.single (w i) (1 : ℝ)) := by
  have hh : h = ∑ j, h j • (Pi.single j (1 : ℝ) : Fin N → ℝ) := by
    funext l
    simp [Finset.sum_apply, Pi.single_apply]
  calc q (fun _ => h) = q (fun _ => ∑ j, h j • (Pi.single j (1 : ℝ) : Fin N → ℝ)) := by rw [← hh]
    _ = ∑ w : Fin n → Fin N, q (fun i => h (w i) • (Pi.single (w i) (1 : ℝ) : Fin N → ℝ)) :=
      q.toMultilinearMap.map_sum fun _ j => h j • (Pi.single j (1 : ℝ) : Fin N → ℝ)
    _ = _ := Finset.sum_congr rfl fun w _ => q.map_smul_univ _ _
theorem exists_hasSum_monomials_of_analyticAt [CompleteSpace F] {G : (Fin N → ℝ) → F}
    {a : Fin N → ℝ} (hG : AnalyticAt ℝ G a) :
    ∃ c : (Fin N → ℕ) → F, ∀ᶠ u in 𝓝 a,
      HasSum (fun m : Fin N → ℕ => (∏ j, (u j - a j) ^ m j) • c m) (G u) := by
  classical
  obtain ⟨p, r, hp⟩ := hG
  obtain ⟨ρ, hρ0, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  have hρ : (0 : ℝ) < ρ := by exact_mod_cast hρ0
  have hsum : Summable fun n => ‖p n‖ * (ρ : ℝ) ^ n :=
    p.summable_norm_mul_pow (hρr.trans_le hp.r_le)
  let P : LetterWord N → F := fun x => p x.1 fun i => Pi.single (x.2 i) (1 : ℝ)
  let c : (Fin N → ℕ) → F := fun m => ∑' x : {x : LetterWord N // letterMultiplicity x = m}, P x
  refine ⟨c, ?_⟩
  have hnear : ∀ᶠ u in 𝓝 a, ∑ j, |u j - a j| < ρ := by
    have hc : Continuous fun u : Fin N → ℝ => ∑ j, |u j - a j| := by fun_prop
    have h0 : (∑ j, |a j - a j|) < ρ := by simpa using hρ
    exact (hc.tendsto a).eventually_lt_const h0
  filter_upwards [hnear] with u hu
  let h : Fin N → ℝ := fun j => u j - a j
  have hnorm : ‖h‖ < ρ := by
    refine (pi_norm_lt_iff hρ).2 fun i => lt_of_le_of_lt ?_ hu
    exact Finset.single_le_sum (f := fun j => |u j - a j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)
  have hball : h ∈ Metric.eball (0 : Fin N → ℝ) r := by
    refine Metric.mem_eball.2 (lt_trans ?_ hρr)
    rw [edist_nndist]
    refine ENNReal.coe_lt_coe.2 ?_
    rw [← NNReal.coe_lt_coe, coe_nndist, dist_zero_right]
    exact hnorm
  have hser := hp.hasSum hball
  have hau : a + h = u := by
    funext j
    simp [h]
  rw [hau] at hser
  let T : LetterWord N → F := fun x => (∏ i, h (x.2 i)) • P x
  have hTn : ∀ x, ‖T x‖ ≤ (∏ i, |h (x.2 i)|) * ‖p x.1‖ := by
    intro x
    have hP : ‖P x‖ ≤ ‖p x.1‖ := by
      refine ((p x.1).le_opNorm _).trans ?_
      have hone : ∏ i, ‖(Pi.single (x.2 i) (1 : ℝ) : Fin N → ℝ)‖ ≤ 1 := by
        refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => ?_
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun l => ?_
        rw [Pi.single_apply]
        split_ifs <;> simp
      exact mul_le_of_le_one_right (norm_nonneg _) hone
    rw [norm_smul, norm_prod]
    exact mul_le_mul_of_nonneg_left hP (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have hTsum : Summable T := by
    refine Summable.of_norm ?_
    rw [summable_sigma_of_nonneg fun _ => norm_nonneg _]
    refine ⟨fun n => (hasSum_fintype _).summable, ?_⟩
    refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun _ => norm_nonneg _) (fun n => ?_) hsum
    rw [tsum_fintype]
    calc ∑ w : Fin n → Fin N, ‖T ⟨n, w⟩‖
        ≤ ∑ w : Fin n → Fin N, (∏ i, |h (w i)|) * ‖p n‖ :=
          Finset.sum_le_sum fun w _ => hTn ⟨n, w⟩
      _ = (∑ j, |h j|) ^ n * ‖p n‖ := by
          rw [← Finset.sum_mul, Fintype.sum_pow]
      _ ≤ (ρ : ℝ) ^ n * ‖p n‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) hu.le n
      _ = ‖p n‖ * (ρ : ℝ) ^ n := mul_comm _ _
  have hTS : HasSum T (G u) := by
    have h1 : HasSum T (∑' x, T x) := hTsum.hasSum
    have h2 : HasSum (fun n => p n fun _ => h) (∑' x, T x) := by
      refine h1.sigma fun n => ?_
      rw [multilinear_diag_eq_sum_basis (p n) h]
      exact hasSum_fintype _
    rw [h2.unique hser] at h1
    exact h1
  have h3 : HasSum (T ∘ Equiv.sigmaFiberEquiv (letterMultiplicity (N := N))) (G u) :=
    (Equiv.sigmaFiberEquiv (letterMultiplicity (N := N))).hasSum_iff.2 hTS
  refine h3.sigma fun m => ?_
  have := finite_words_of_multiplicity m
  let _ := Fintype.ofFinite {x : LetterWord N // letterMultiplicity x = m}
  have h4 : HasSum (fun x : {x : LetterWord N // letterMultiplicity x = m} => P x) (c m) :=
    (hasSum_fintype _).summable.hasSum
  have h5 := h4.const_smul (∏ j, (u j - a j) ^ m j)
  convert h5 using 2 with x
  show (∏ i, h (x.1.2 i)) • P x.1 = _
  rw [prod_apply_word h x.1, x.2]
theorem isRelativelyOpen_realEmbed_image {D : Set (Fin N → ℝ)} (hD : IsOpen D) :
    ComplexMatrix2.IsRelativelyOpen (Coordinates.ComplexCoordinates.realLocus N)
      (PowerSeries.RealSeries.realEmbed '' D) := by
  refine ⟨{z | (fun i => (z i).re) ∈ D}, ?_, ?_⟩
  · exact hD.preimage (continuous_pi fun i => Complex.continuous_re.comp (continuous_apply i))
  · ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨?_, fun j => ?_⟩
      · simpa [PowerSeries.RealSeries.realEmbed] using hu
      · simp [PowerSeries.RealSeries.realEmbed]
    · rintro ⟨hz, hr⟩
      refine ⟨_, hz, ?_⟩
      funext i
      apply Complex.ext
      · simp [PowerSeries.RealSeries.realEmbed]
      · simpa [PowerSeries.RealSeries.realEmbed] using (hr i).symm
theorem isRealAnalyticIn_of_analyticOnNhd {M : ℕ} {D : Set (Fin N → ℝ)} (hD : IsOpen D)
    {G : (Fin N → ℝ) → Coordinates.ComplexCoordinates M} (hG : AnalyticOnNhd ℝ G D) :
    Coordinates.ComplexCoordinates.IsRealAnalyticIn (PowerSeries.RealSeries.realEmbed '' D)
      fun z => G fun i => (z i).re := by
  refine ⟨isRelativelyOpen_realEmbed_image hD, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨c, hc⟩ := exists_hasSum_monomials_of_analyticAt (hG a ha)
  refine ⟨c, ?_⟩
  have hcont : Continuous fun z : Coordinates.ComplexCoordinates N => fun i => (z i).re :=
    continuous_pi fun i => Complex.continuous_re.comp (continuous_apply i)
  have hre : Tendsto (fun z : Coordinates.ComplexCoordinates N => fun i => (z i).re)
      (𝓝[Coordinates.ComplexCoordinates.realLocus N] PowerSeries.RealSeries.realEmbed a)
      (𝓝 a) := by
    have h := hcont.tendsto (PowerSeries.RealSeries.realEmbed a)
    have e : (fun i => (PowerSeries.RealSeries.realEmbed a i).re) = a := by
      funext i
      simp [PowerSeries.RealSeries.realEmbed]
    rw [e] at h
    exact h.mono_left nhdsWithin_le_nhds
  filter_upwards [hre.eventually hc, self_mem_nhdsWithin] with z hz hzr
  have hfun : (fun m : Fin N → ℕ =>
      (∏ j, (z j - PowerSeries.RealSeries.realEmbed a j) ^ m j) • c m) =
      fun m => (∏ j, ((z j).re - a j) ^ m j) • c m := by
    funext m
    have e : (∏ j, (z j - PowerSeries.RealSeries.realEmbed a j) ^ m j) =
        ((∏ j, ((z j).re - a j) ^ m j : ℝ) : ℂ) := by
      push_cast
      refine Finset.prod_congr rfl fun j _ => ?_
      have hzj : z j = ((z j).re : ℂ) := Complex.ext rfl (by simpa using hzr j)
      rw [hzj]
      simp [PowerSeries.RealSeries.realEmbed]
    rw [e]
    funext i
    simp [Complex.real_smul]
  rw [hfun]
  exact hz
theorem isRealAnalyticToRealSpace_of_analyticOnNhd {V W : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {D : Set V} (hD : IsOpen D) {g : V → W}
    (hg : AnalyticOnNhd ℝ g D) : IsRealAnalyticToRealSpace D g := by
  intro M y
  refine ⟨hD, fun K x => ?_⟩
  let xL : V ≃L[ℝ] (Fin K → ℝ) := x.toContinuousLinearEquiv
  let yL : W ≃L[ℝ] (Fin M → ℝ) := y.toContinuousLinearEquiv
  let R : (Fin M → ℝ) →L[ℝ] Coordinates.ComplexCoordinates M :=
    ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)
  have hopen : IsOpen (x '' D) := xL.toHomeomorph.isOpenMap _ hD
  let G : (Fin K → ℝ) → Coordinates.ComplexCoordinates M :=
    fun u => PowerSeries.RealSeries.realEmbed (y (g (x.symm u)))
  have hG : AnalyticOnNhd ℝ G (x '' D) := by
    rintro _ ⟨v, hv, rfl⟩
    have h1 : AnalyticAt ℝ g ((xL.symm : (Fin K → ℝ) →L[ℝ] V) (x v)) := by
      have e : (xL.symm : (Fin K → ℝ) →L[ℝ] V) (x v) = v := x.symm_apply_apply v
      rw [e]
      exact hg v hv
    have h2 : AnalyticAt ℝ (g ∘ (xL.symm : (Fin K → ℝ) →L[ℝ] V)) (x v) :=
      AnalyticAt.comp h1 ((xL.symm : (Fin K → ℝ) →L[ℝ] V).analyticAt _)
    exact show AnalyticAt ℝ
        ((R.comp (yL : W →L[ℝ] (Fin M → ℝ))) ∘ (g ∘ (xL.symm : (Fin K → ℝ) →L[ℝ] V))) (x v) from
      AnalyticAt.comp ((R.comp (yL : W →L[ℝ] (Fin M → ℝ))).analyticAt _) h2
  exact isRealAnalyticIn_of_analyticOnNhd hopen hG
end Series
section Forms
variable {L n k j : ℕ}
def toMatrixCLM : ComplexMatrix2.LieElement →L[ℝ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := ComplexMatrix2.LieElement.toMatrix, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }
abbrev UniqueOrientation (L n k j : ℕ) : Prop :=
  ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
theorem uniqueOrientation (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) : UniqueOrientation L n k j := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.uniqueOrientation <;> assumption
theorem nonempty_positiveEdge : Nonempty (PositiveEdge L n k j) := by apply _root_.YangMills.Construction.Tower.IdentityChart.nonempty_positiveEdge <;> assumption
theorem extendOddly_of_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) : extendOddly f b = f b := if_pos h
theorem extendOddly_of_not_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : ¬b.IsPositivelyOriented) : extendOddly f b = -f b.opposite := if_neg h
theorem extendOddly_of_mem {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j) :
    extendOddly B = B := by
  funext b
  by_cases h : b.IsPositivelyOriented
  · exact extendOddly_of_pos B h
  · rw [extendOddly_of_not_pos B h, hB.2 b, neg_neg]
theorem extendOddly_congr (hx : UniqueOrientation L n k j) {f g : Edge L n k j → ComplexMatrix2}
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b = g b) :
    extendOddly f = extendOddly g := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_congr <;> assumption
theorem edgeForm_ext (hx : UniqueOrientation L n k j) {A B : Edge L n k j → ComplexMatrix2}
    (hA : A ∈ edgeFormSpace L n k j) (hB : B ∈ edgeFormSpace L n k j)
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → A b = B b) : A = B := by
  rw [← extendOddly_of_mem hA, ← extendOddly_of_mem hB]
  exact extendOddly_congr hx h
theorem ofValues_of_pos (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) : ofValues y b = (y ⟨b, h⟩).toMatrix := by apply _root_.YangMills.Construction.Tower.IdentityChart.ofValues_of_positive <;> assumption
theorem ofValues_smul (hx : UniqueOrientation L n k j)
    (hform : ∀ y : PositiveEdge L n k j → ComplexMatrix2.LieElement,
      ofValues y ∈ edgeFormSpace L n k j)
    (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) (t : ℝ) :
    ofValues (t • y) = algebraMap ℝ ℂ t • ofValues y := by
  rw [algebraMap_smul]
  refine edgeForm_ext hx (hform _) ((edgeFormSpace L n k j).smul_mem t (hform y)) fun b hb => ?_
  simp only [Pi.smul_apply, ofValues_of_pos _ hb]
  rfl
theorem expTwist_of_not_pos (A U : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : ¬b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := if_neg h
theorem expForm_ofValues_of_pos (y : PositiveEdge L n k j → ComplexMatrix2.LieElement)
    {b : Edge L n k j} (h : b.IsPositivelyOriented) :
    expForm (ofValues y) b = expFamily y ⟨b, h⟩ := by apply _root_.YangMills.Construction.Tower.IdentityChart.identityChartPoint_of_positive <;> assumption
theorem fieldOfPositiveValues_expFamily (hx : UniqueOrientation L n k j)
    (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    fieldOfPositiveValues (expFamily y) = identityChartPoint y := by
  funext b
  rcases hx b with ⟨hb, -⟩ | ⟨hr, hb⟩
  · show _ = expForm (ofValues y) b
    rw [expForm_ofValues_of_pos y hb]
    simp only [fieldOfPositiveValues, dif_pos hb]
  · show _ = expForm (ofValues y) b
    simp only [fieldOfPositiveValues, dif_neg hb, dif_pos hr, expForm, expTwist_of_not_pos _ _ hb,
      ofValues_of_pos y hr, expFamily, Pi.one_apply, mul_one]
theorem fieldOfPositiveValues_restrict (hx : UniqueOrientation L n k j)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j) :
    fieldOfPositiveValues (restrictToPositiveEdges V) = V := by
  funext b
  have hrr : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
  rcases hx b with ⟨h, -⟩ | ⟨h', h⟩
  · simp [fieldOfPositiveValues, h, restrictToPositiveEdges]
  · have hinv := hV.2 b.opposite (mem_univ _)
    simp only [fieldOfPositiveValues, dif_neg h, dif_pos h', restrictToPositiveEdges]
    rw [← hinv, hrr]
theorem restrict_fieldOfPositiveValues (w : PositiveEdge L n k j → ComplexMatrix2) :
    restrictToPositiveEdges (fieldOfPositiveValues w) = w := by apply _root_.YangMills.SharedProofs.p777 <;> assumption
theorem restrict_identityChartPoint (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    restrictToPositiveEdges (identityChartPoint y) = expFamily y := by apply _root_.YangMills.Construction.Tower.IdentityChart.restrictToPositiveEdges_identityChartPoint <;> assumption
theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
def tracelessBasis : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
  Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
end Forms
section ReadBack
variable {L n k j j' : ℕ}
theorem pullback_isAnalyticFieldMap [inst : Fintype (PositiveEdge L n k j)]
    [inst' : Fintype (PositiveEdge L n k j')] (hx' : UniqueOrientation L n k j')
    (hC' : ExpChartAtOne (PositiveEdge L n k j')) (hC : ExpChartAtOne (PositiveEdge L n k j))
    (hR : RealAnalyticIffInExpChart (PositiveEdge L n k j') (PositiveEdge L n k j) tracelessBasis)
    (hP : GroupPowerAnalyticity (PositiveEdge L n k j') (PositiveEdge L n k j))
    (hlog : ∀ y ∈ lieBall (PositiveEdge L n k j') (1 / 2),
      identityChartLog (identityChartPoint y) = y)
    (hconf : ∀ y ∈ lieBall (PositiveEdge L n k j) (1 / 2),
      identityChartPoint y ∈ fieldSpace L n k j)
    {s : (PositiveEdge L n k j' → ComplexMatrix2.LieElement) →
      PositiveEdge L n k j → ComplexMatrix2.LieElement}
    {A : Set (PositiveEdge L n k j' → ComplexMatrix2.LieElement)} (hA : IsOpen A)
    (hAs : A ⊆ lieBall (PositiveEdge L n k j') (1 / 2)) (hs : AnalyticOnNhd ℝ s A)
    (hmap : MapsTo s A (lieBall (PositiveEdge L n k j) (1 / 2)))
    (hopen : IsOpenFieldSet PeriodicLattice.compactGaugeGroup (identityChartPoint '' A)) :
    IsAnalyticFieldMap (identityChartPoint '' A)
      fun W => identityChartPoint (s (identityChartLog W)) := by
  let m : (Edge L n k j' → ComplexMatrix2) → Edge L n k j → ComplexMatrix2 :=
    fun W => identityChartPoint (s (identityChartLog W))
  have hmS : ∀ y ∈ A, m (identityChartPoint y) = identityChartPoint (s y) := fun y hy => by
    show identityChartPoint (s (identityChartLog (identityChartPoint y))) = _
    rw [hlog y (hAs hy)]
  have hmaps : MapsTo m (identityChartPoint '' A) (fieldSpace L n k j) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hmS y hy]
    exact hconf _ (hmap hy)
  refine ⟨hopen, hmaps, inst', inst, ?_⟩
  let 𝒲 : Set (PositiveEdge L n k j' ⊕ Empty → ComplexMatrix2) :=
    {q | fieldOfPositiveValues (groupComponent q) ∈ identityChartPoint '' A}
  let f : (PositiveEdge L n k j' → ComplexMatrix2) → PositiveEdge L n k j → ComplexMatrix2 :=
    fun w => restrictToPositiveEdges (m (fieldOfPositiveValues w))
  have hW : IsOpenInSubspaceTimesGroup (hermitianTracelessFunctions Empty) 𝒲 := by
    obtain ⟨O₀, hO₀, e⟩ := hopen.2
    refine ⟨le_refl _, (fun q => groupComponent q) ⁻¹' O₀,
      hO₀.preimage (continuous_pi fun r => continuous_apply _), ?_⟩
    ext q
    constructor
    · intro hq
      have h : groupComponent q ∈ restrictToPositiveEdges '' (identityChartPoint '' A) :=
        ⟨_, hq, restrict_fieldOfPositiveValues _⟩
      rw [e] at h
      refine ⟨h.1, ?_, h.2⟩
      rw [Subsingleton.elim (algebraComponent q) 0]
      exact Submodule.zero_mem _
    · rintro ⟨h1, -, h2⟩
      have h : groupComponent q ∈ restrictToPositiveEdges '' (identityChartPoint '' A) := by
        rw [e]
        exact ⟨h1, h2⟩
      obtain ⟨U, hU, hUq⟩ := h
      show fieldOfPositiveValues (groupComponent q) ∈ identityChartPoint '' A
      rw [← hUq, fieldOfPositiveValues_restrict hx' (hopen.1 hU)]
      exact hU
  obtain ⟨hOpenO, hb⟩ := hP 𝒲 hW
  have hOmem : ∀ {w}, w ∈ asGroupFactors ⁻¹' 𝒲 → ∃ y ∈ A, w = expFamily y := by
    intro w hw
    obtain ⟨y, hy, e⟩ : fieldOfPositiveValues w ∈ identityChartPoint '' A := hw
    refine ⟨y, hy, ?_⟩
    rw [← restrict_identityChartPoint y, e, restrict_fieldOfPositiveValues]
  have hsub : asGroupFactors ⁻¹' 𝒲 ⊆ expImage (PositiveEdge L n k j') := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := hOmem hw
    exact ⟨y, hAs hy, rfl⟩
  have hfchart : ∀ y ∈ A, f (expFamily y) = expFamily (s y) := fun y hy => by
    show restrictToPositiveEdges (m (fieldOfPositiveValues (expFamily y))) = _
    rw [fieldOfPositiveValues_expFamily hx', hmS y hy, restrict_identityChartPoint]
  have hinto : MapsTo f (asGroupFactors ⁻¹' 𝒲) (specialUnitaryPower (PositiveEdge L n k j)) := by
    intro w hw
    have h := hmaps (show fieldOfPositiveValues w ∈ identityChartPoint '' A from hw)
    exact fun c => h.1 c (mem_univ _)
  have hinto' : MapsTo f (asGroupFactors ⁻¹' 𝒲) (expImage (PositiveEdge L n k j)) := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := hOmem hw
    rw [hfchart y hy]
    exact ⟨s y, hmap hy, rfl⟩
  have hdom : pullbackDomain (asGroupFactors ⁻¹' 𝒲) = A := by
    ext y
    constructor
    · rintro ⟨hys, hyO⟩
      obtain ⟨y', hy', e⟩ := hOmem hyO
      rw [hC'.1 hys (hAs hy') e]
      exact hy'
    · intro hy
      refine ⟨hAs hy, ?_⟩
      show fieldOfPositiveValues (expFamily y) ∈ identityChartPoint '' A
      rw [fieldOfPositiveValues_expFamily hx']
      exact ⟨y, hy, rfl⟩
  have hreal : IsRealAnalyticToRealSpace (pullbackDomain (asGroupFactors ⁻¹' 𝒲))
      (logChart ∘ f ∘ expFamily) := by
    rw [hdom]
    refine isRealAnalyticToRealSpace_of_analyticOnNhd hA (hs.congr hA fun y hy => ?_)
    show s y = logChart (f (expFamily y))
    rw [hfchart y hy, hC.2.2.1 _ (hmap hy)]
  have hrest := (((hR _ hOpenO hsub).2.2 f hinto).2 hinto').2 hreal
  have hfin := ((hb tracelessBasis).2.2 f hinto).2 hrest
  have e : (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) = hermitianTracelessFunctions Empty := by
    ext x
    constructor
    · intro hx
      rw [(Submodule.mem_bot ℝ).1 hx]
      exact Submodule.zero_mem _
    · intro _
      exact (Submodule.mem_bot ℝ).2 (Subsingleton.elim _ _)
  rw [e]
  exact hfin
theorem hasDerivAt_comp_smul_line {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {ψ : E → W} (h : DifferentiableAt ℝ ψ 0) (u : E) :
    HasDerivAt (fun t : ℝ => ψ (t • u)) (fderiv ℝ ψ 0 u) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have h2 : HasFDerivAt ψ (fderiv ℝ ψ 0) ((0 : ℝ) • u) := by
    simpa using h.hasFDerivAt
  exact h2.comp_hasDerivAt (0 : ℝ) h1
theorem pullback_leftDifferential [Fintype (PositiveEdge L n k j)]
    [Fintype (PositiveEdge L n k j')] (hx : UniqueOrientation L n k j)
    (hx' : UniqueOrientation L n k j') (hC : ExpChartAtOne (PositiveEdge L n k j))
    (hopen' : IsOpen (lieBall (PositiveEdge L n k j') (1 / 2)))
    (hopen : IsOpen (lieBall (PositiveEdge L n k j) (1 / 2)))
    (h0' : (0 : PositiveEdge L n k j' → ComplexMatrix2.LieElement) ∈
      lieBall (PositiveEdge L n k j') (1 / 2))
    (h0m : (0 : PositiveEdge L n k j → ComplexMatrix2.LieElement) ∈
      lieBall (PositiveEdge L n k j) (1 / 2))
    (hpt' : identityChartPoint (0 : PositiveEdge L n k j' → ComplexMatrix2.LieElement) =
      trivialField L n k j')
    (hpt : identityChartPoint (0 : PositiveEdge L n k j → ComplexMatrix2.LieElement) =
      trivialField L n k j)
    (hlog : ∀ y ∈ lieBall (PositiveEdge L n k j') (1 / 2),
      identityChartLog (identityChartPoint y) = y)
    (hform : ∀ y : PositiveEdge L n k j' → ComplexMatrix2.LieElement,
      ofValues y ∈ edgeFormSpace L n k j')
    (hback : ∀ B ∈ edgeFormSpace L n k j', ofValues (formValues B) = B)
    {s : (PositiveEdge L n k j' → ComplexMatrix2.LieElement) →
      PositiveEdge L n k j → ComplexMatrix2.LieElement}
    (hs0 : s 0 = 0) (hd : DifferentiableAt ℝ s 0) {B : Edge L n k j' → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j') :
    leftDifferential
        (fun W : Edge L n k j' → ComplexMatrix2 => identityChartPoint (s (identityChartLog W)))
        (trivialField L n k j') B =
      ofValues (fderiv ℝ s 0 (formValues B)) := by
  let m : (Edge L n k j' → ComplexMatrix2) → Edge L n k j → ComplexMatrix2 :=
    fun W => identityChartPoint (s (identityChartLog W))
  let y := formValues B
  have hBy : ofValues y = B := hback B hB
  have hm1 : m (trivialField L n k j') = trivialField L n k j := by
    show identityChartPoint (s (identityChartLog (trivialField L n k j'))) = _
    rw [← hpt', hlog 0 h0', hs0, hpt]
  rw [leftDifferential, ofValues]
  refine extendOddly_congr hx fun c hc => ?_
  rw [dif_pos hc]
  let cc : PositiveEdge L n k j := ⟨c, hc⟩
  have hl : HasDerivAt (fun t : ℝ => s (t • y)) (fderiv ℝ s 0 y) 0 :=
    hasDerivAt_comp_smul_line hd y
  let P : (PositiveEdge L n k j → ComplexMatrix2.LieElement) →L[ℝ] ComplexMatrix2 :=
    toMatrixCLM.comp (ContinuousLinearMap.proj cc)
  have hp : HasDerivAt (fun t : ℝ => (s (t • y) cc).toMatrix)
      ((fderiv ℝ s 0 y cc).toMatrix) 0 :=
    P.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
  let φ : ℝ → ComplexMatrix2 := fun t => ComplexMatrix2.logSeries (m (PeriodicLattice.expTwist
    (algebraMap ℝ ℂ t • B) (trivialField L n k j')) c)
  have hline : Tendsto (fun t : ℝ => t • y) (𝓝 0) (𝓝 0) := by
    have h : Continuous fun t : ℝ => t • y := by fun_prop
    simpa using h.tendsto 0
  have hsline : Tendsto (fun t : ℝ => s (t • y)) (𝓝 0) (𝓝 0) := by
    have h := hl.continuousAt.tendsto
    simpa [hs0] using h
  have hev : (fun t : ℝ => (s (t • y) cc).toMatrix) =ᶠ[𝓝 0]
      fun t => (1 / Complex.I) • φ t := by
    filter_upwards [hline.eventually (hopen'.mem_nhds h0'),
      hsline.eventually (hopen.mem_nhds h0m)] with t ht ht'
    have e₁ : PeriodicLattice.expTwist (algebraMap ℝ ℂ t • B) (trivialField L n k j') =
        identityChartPoint (t • y) := by
      show _ = expForm (ofValues (t • y))
      rw [ofValues_smul hx' hform, hBy]
      rfl
    have e₂ : m (identityChartPoint (t • y)) = identityChartPoint (s (t • y)) := by
      show identityChartPoint (s (identityChartLog (identityChartPoint (t • y)))) = _
      rw [hlog _ ht]
    have e₃ : identityChartPoint (s (t • y)) c = expFamily (s (t • y)) cc :=
      congrFun (restrict_identityChartPoint (s (t • y))) cc
    have e₄ := congrFun (hC.2.2.2.1 _ ⟨s (t • y), ht', rfl⟩) cc
    rw [hC.2.2.1 _ ht'] at e₄
    show (s (t • y) cc).toMatrix = (1 / Complex.I) • ComplexMatrix2.logSeries
      (m (PeriodicLattice.expTwist (algebraMap ℝ ℂ t • B) (trivialField L n k j')) c)
    rw [e₁, e₂, e₃]
    exact e₄
  have hφ : HasDerivAt φ (Complex.I • (fderiv ℝ s 0 y cc).toMatrix) 0 := by
    have h₁ := (hp.congr_of_eventuallyEq hev.symm).const_smul Complex.I
    have e : (Complex.I • fun t => (1 / Complex.I) • φ t) = φ := by
      funext t
      rw [Pi.smul_apply, smul_smul, mul_one_div_cancel Complex.I_ne_zero, one_smul]
    rw [e] at h₁
    exact h₁
  have hW : m (trivialField L n k j') c = 1 := by rw [hm1]
  have hi : (1 : ComplexMatrix2)⁻¹ = 1 := by simp
  show Complex.I⁻¹ • deriv (fun t : ℝ => ComplexMatrix2.logSeries (m (PeriodicLattice.expTwist
    (algebraMap ℝ ℂ t • B) (trivialField L n k j')) c *
      (m (trivialField L n k j') c)⁻¹)) 0 = _
  simp only [hW, hi, mul_one]
  show Complex.I⁻¹ • deriv φ 0 = _
  rw [hφ.deriv, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
end ReadBack
theorem statement_holds
    (hOn : IdentityChartOnFields)
    (hInv : ChartAndBallImages.Statement)
    (hRead : AnalyticReadInExpChartStatement)
    (hLin : AnalyticCalculusStatement) :
    Statement := by
  intro L n k j j' hL hn hj hj' _ _ s
  have hx : UniqueOrientation L n k j := uniqueOrientation hL hn hj
  have hx' : UniqueOrientation L n k j' := uniqueOrientation hL hn hj'
  have : Nonempty (PositiveEdge L n k j) := nonempty_positiveEdge
  have : Nonempty (PositiveEdge L n k j') := nonempty_positiveEdge
  obtain ⟨ho, h0m, hpt, hsm, hop, -, -, -, -, -, -⟩ := hOn L n k j hL hn hj
  obtain ⟨ho', h0', hpt', hsm', hop', -, -, -, -, hform', hback'⟩ := hOn L n k j' hL hn hj'
  have hC := (hInv (PositiveEdge L n k j)).1
  have hC' := (hInv (PositiveEdge L n k j')).1
  refine ⟨fun A hA hAs hs hmap => ?_, fun hs0 hd B hB => ?_⟩
  · exact pullback_isAnalyticFieldMap hx' hC' hC (hRead _ _ tracelessBasis)
      ((hLin Empty _ Empty _).2.2.1) (fun y hy => (hsm' y hy).2) (fun y hy => (hsm y hy).1) hA hAs
      hs hmap (hop' A hA hAs)
  · exact pullback_leftDifferential hx hx' hC ho' ho h0' h0m hpt' hpt (fun y hy => (hsm' y hy).2)
      (fun y => (hform' y).1) hback' hs0 hd hB
end YangMills.Construction.Tower.IdentityChartPullback
end
