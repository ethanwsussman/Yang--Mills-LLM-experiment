import YangMills.Construction.RunningCouplingSlope.LimitOfTheKernelOfTheDifferenceProof
import YangMills.Construction.RunningCouplingSlope.TheDifferenceKernelIsCarriedByTranslations
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.DifferenceKernelTranslationInvarianceProof
open Matrices Tower PeriodicOperators
open Tower.CriticalBranchResponse
open Tower.ResponseOperators (ClassFnEqForm)
open Tower.BackgroundFieldResponse (responseKernel)
open LocalKernels (projPositiveEdge)
open LocalKernels.Periodisation
open SummableFields (periodize)
open SlopeCoefficient (secondAxis)
variable {L k : ℕ}
private theorem pauliCoeff_pauliFamily (a b : Fin 3) :
    pauliCoeff a (ComplexMatrix2.pauliFamily b) = if a = b then 1 else 0 := by apply _root_.YangMills.Construction.Tower.CrossingSmoothingContraction.pauliCoeff_pauliFamily <;> assumption
private theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
private theorem real_smul_eq_complex_smul (x : ℝ) (Y : ComplexMatrix2) : x • Y = (x : ℂ) • Y := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
private theorem pauliCoeff_real_smul (x : ℝ) {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (x • Y) = (x : ℂ) * pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.FullSpace.HolomorphicRescaledKernels.pauliCoeff_real_smul <;> assumption
private theorem mem_traceless_of_mem_hermitianTraceless {Y : ComplexMatrix2}
    (h : Y ∈ ComplexMatrix2.hermitianTraceless) : Y ∈ ComplexMatrix2.traceless := h.2
private theorem pauliCoeff_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
private theorem translate_neg_translate {F : PeriodicData} (hF : IsPeriodic F) (n : Fin 4 → ℤ)
    (ι : F.Carrier) : F.translate (-n) (F.translate n ι) = ι := by
  rw [← hF.translate_add, add_neg_cancel, hF.translate_zero]
private theorem mkQuot_eq_iff {F : PeriodicData} (hF : IsPeriodic F) (s : ℕ)
    (ι ι' : F.Carrier) :
    F.mkQuot s ι = F.mkQuot s ι' ↔ ∃ n : Fin 4 → ℤ, ι' = F.translate (s • n) ι := by apply _root_.YangMills.Construction.PeriodicOperators.QuotOrbits.mkQuot_eq_iff <;> assumption
private theorem tsum_quotClass {F : PeriodicData} (hF : IsPeriodic F) {s : ℕ} (hs : 0 < s)
    (g : F.Carrier → ℂ) (ι : F.Carrier) :
    (∑' κ : {κ : F.Carrier // F.mkQuot s κ = F.mkQuot s ι}, g κ) =
      ∑' n : Fin 4 → ℤ, g (F.translate (s • n) ι) := by apply _root_.YangMills.SharedProofs.p39301 <;> assumption
private def gridVertex (L k : ℕ) (z : Fin 4 → ℤ) : FullSpace.Vertex L k k :=
  ∑ μ, z μ • InfiniteLattice.axisStep (meshAt L k k) μ
private def gridEdge (L k : ℕ) (z : Fin 4 → ℤ) : PosEdge L k k :=
  ⟨InfiniteLattice.Link.forwardFrom (gridVertex L k z) secondAxis, secondAxis, by
    simp [InfiniteLattice.Link.forwardFrom]⟩
private def unitCell (L k : ℕ) (z : Fin 4 → ℤ) : (colourEdges L k k).Carrier := (2, gridEdge L k z)
private def responseColumn (L k : ℕ) (z : Fin 4 → ℤ) : (colourEdges L k 0).Carrier → ℂ :=
  fun ι => (finestMesh L k : ℂ) * responseKernel L k ι (unitCell L k z)
private theorem gridVertex_apply (L k : ℕ) (z : Fin 4 → ℤ) (μ : Fin 4) :
    ((gridVertex L k z : FullSpace.Vertex L k k) : InfiniteLattice.AmbientSpace) μ =
      (z μ : ℝ) * meshAt L k k := by apply _root_.YangMills.DeltaSharedProofs.p500957 <;> assumption
private theorem projVertex_add_axisStep (L n k : ℕ) (x : FullSpace.Vertex L k k) (μ : Fin 4) :
    FullSpace.projVertex L n k k (x + InfiniteLattice.axisStep (meshAt L k k) μ) =
      FullSpace.projVertex L n k k x +
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ := by apply _root_.YangMills.SharedProofs.p27769 <;> assumption
private theorem projPositiveEdge_gridEdge {L n k : ℕ} (hB : ProjEdgesCompatible L n k k)
    (z : Fin 4 → ℤ) :
    (projPositiveEdge L n k k (gridEdge L k z)).1 =
      PeriodicLattice.Bond.forwardFrom (PeriodicLattice.offsetSite 0 z) secondAxis := by apply _root_.YangMills.DeltaSharedProofs.p502410 <;> assumption
open Classical in
private theorem coeffsOnEdges_pauliUnitForm (hIdx : IsPeriodic (colourEdges L k k)) {n : ℕ}
    (hC : ProjCellsClassified L n k k) (hB : ProjEdgesCompatible L n k k) (z : Fin 4 → ℤ)
    (ι : (colourEdges L k k).Carrier) :
    PeriodicForm.coeffsOnEdges L n k k (pauliUnitForm L n k z) ι =
      if (colourEdges L k k).mkQuot (periodSide L n) ι =
          (colourEdges L k k).mkQuot (periodSide L n) (unitCell L k z) then 1 else 0 := by
  have hval : PeriodicForm.coeffsOnEdges L n k k (pauliUnitForm L n k z) ι =
      pauliCoeff ι.1 (if (projPositiveEdge L n k k ι.2).1 =
        PeriodicLattice.Bond.forwardFrom (PeriodicLattice.offsetSite 0 z) secondAxis then
          ComplexMatrix2.pauliFamily 2 else 0) := by
    simp only [PeriodicForm.coeffsOnEdges, toPauliCoeffs, restrictToPositiveEdges, pauliUnitForm,
      extendOddly]
    rw [if_pos (projPositiveEdge L n k k ι.2).2]
  rw [hval]
  have hcell := (hC .edge).2
  by_cases hq : (projPositiveEdge L n k k ι.2).1 =
      PeriodicLattice.Bond.forwardFrom (PeriodicLattice.offsetSite 0 z) secondAxis
  · rw [if_pos hq, pauliCoeff_pauliFamily]
    have hq' : projPositiveEdge L n k k ι.2 = projPositiveEdge L n k k (gridEdge L k z) :=
      Subtype.ext (hq.trans (projPositiveEdge_gridEdge hB z).symm)
    obtain ⟨m, hm⟩ := (hcell ι.2 (gridEdge L k z)).1 hq'
    by_cases hcol : ι.1 = 2
    · rw [if_pos hcol, if_pos]
      refine (mkQuot_eq_iff hIdx _ _ _).2 ⟨m, ?_⟩
      exact Prod.ext hcol.symm hm
    · rw [if_neg hcol, if_neg]
      intro hcl
      obtain ⟨t, ht⟩ := (mkQuot_eq_iff hIdx _ _ _).1 hcl
      exact hcol (congrArg Prod.fst ht).symm
  · rw [if_neg hq, pauliCoeff_zero, if_neg]
    intro hcl
    obtain ⟨t, ht⟩ := (mkQuot_eq_iff hIdx _ _ _).1 hcl
    apply hq
    have h4 := (hcell ι.2 (gridEdge L k z)).2 ⟨t, congrArg Prod.snd ht⟩
    exact (congrArg Subtype.val h4).trans (projPositiveEdge_gridEdge hB z)
private theorem pauliUnitForm_mem (h₉ : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {n : ℕ} (hn : 0 < n) (hk : 0 < k)
    (z : Fin 4 → ℤ) : pauliUnitForm L n k z ∈ edgeFormSpace L n k k := by apply _root_.YangMills.SharedProofs.p32844 <;> assumption
private theorem classFnEqForm_responseColumn
    (hP0 : IsPeriodic (colourEdges L k 0)) (hPk : IsPeriodic (colourEdges L k k))
    (hcov : IsShiftInvariant (colourEdges L k k) (colourEdges L k 0) (responseKernel L k)) {n : ℕ}
    (hs : 0 < periodSide L n) (hC : ProjCellsClassified L n k k) (hB : ProjEdgesCompatible L n k k)
    (z : Fin 4 → ℤ) (hmem : pauliUnitForm L n k z ∈ edgeFormSpace L n k k)
    (hAt : ResponseImagesFullSide.AtForm L n k ⟨_, hmem⟩) :
    ClassFnEqForm L n k 0
      (restrictToPositiveEdges (meshScaledResponse L n k (pauliUnitForm L n k z) :
        Edge L n k 0 → ComplexMatrix2))
      (periodize (colourEdges L k 0) (periodSide L n) (responseColumn L k z)) := by
  classical
  intro ι
  set s := periodSide L n with hsdef
  set u := unitCell L k z with hu
  have hRHS : toPauliCoeffs (restrictToPositiveEdges
        (meshScaledResponse L n k (pauliUnitForm L n k z) : Edge L n k 0 → ComplexMatrix2))
        (ι.1, projPositiveEdge L n k 0 ι.2) =
      (finestMesh L k : ℂ) * PeriodicForm.coeffsOnEdges L n k 0
        (periodicResponse L n k (pauliUnitForm L n k z) : Edge L n k 0 → ComplexMatrix2) ι := by
    have hb := (projPositiveEdge L n k 0 ι.2).2
    have hmem' := (periodicResponse L n k (pauliUnitForm L n k z)).2.1 _ hb
    simp only [toPauliCoeffs, PeriodicForm.coeffsOnEdges, restrictToPositiveEdges,
      meshScaledResponse]
    exact pauliCoeff_real_smul _ (mem_traceless_of_mem_hermitianTraceless hmem') _
  rw [hRHS]
  have hread := congrFun hAt.resp_coeffs ι
  simp only at hread
  rw [hread]
  have hsum : applyKernel (responseKernel L k) (PeriodicForm.coeffsOnEdges L n k k
        (pauliUnitForm L n k z)) ι =
      ∑' m : Fin 4 → ℤ, responseKernel L k ι ((colourEdges L k k).translate (s • m) u) := by
    rw [← tsum_quotClass hPk hs (responseKernel L k ι) u]
    simp only [applyKernel]
    refine Eq.trans ?_ (tsum_subtype
      {κ | (colourEdges L k k).mkQuot s κ = (colourEdges L k k).mkQuot s u}
      (responseKernel L k ι)).symm
    refine tsum_congr fun κ => ?_
    rw [coeffsOnEdges_pauliUnitForm hPk hC hB z κ]
    by_cases h : (colourEdges L k k).mkQuot s κ = (colourEdges L k k).mkQuot s u
    · rw [if_pos h, mul_one, Set.indicator_of_mem (by exact h)]
    · rw [if_neg h, mul_zero, Set.indicator_of_notMem (by exact h)]
  rw [hsum, periodize, tsum_quotClass hP0 hs, ← tsum_mul_left,
    ← (Equiv.neg (Fin 4 → ℤ)).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [responseColumn, Equiv.neg_apply, smul_neg]
  congr 1
  have h1 := hcov (-(s • m)) ι ((colourEdges L k k).translate (s • m) u)
  rw [translate_neg_translate hPk] at h1
  exact h1
private theorem summable_responseColumn (hSums : ExponentialSums.Bounds)
    (hP0 : IsPeriodic (colourEdges L k 0))
    (hPer : IsPeriodicKernel (colourEdges L k k) (colourEdges L k 0) (responseKernel L k))
    (z : Fin 4 → ℤ) : Summable (responseColumn L k z) := by
  obtain ⟨-, C, δ, hC, hδ, hb⟩ := hPer
  have h1 := ((hSums δ hδ).2.2 _ hP0 ((colourEdges L k k).pos (unitCell L k z))).1
  have h2 : Summable fun ι : (colourEdges L k 0).Carrier => ‖(finestMesh L k : ℂ)‖ * (C *
      Real.exp (-δ * TorusMetric.euclidNormVec ((colourEdges L k 0).pos ι -
        (colourEdges L k k).pos (unitCell L k z)))) := (h1.mul_left _).mul_left _
  refine Summable.of_norm_bounded h2 fun ι => ?_
  rw [responseColumn, norm_mul]
  exact mul_le_mul_of_nonneg_left (hb _ _) (norm_nonneg _)
private theorem im_periodize {F : PeriodicData} {f : F.Carrier → ℂ} (hf : Summable f)
    (hr : ∀ κ, (f κ).im = 0) (s : ℕ) (c : F.QuotMod s) : (periodize F s f c).im = 0 := by
  have hs' : Summable fun κ : {κ : F.Carrier // F.mkQuot s κ = c} => f κ := hf.subtype _
  rw [periodize, Complex.im_tsum hs']
  simp [hr]
section Entries
variable {J : Type} [Finite J]
private theorem linearMapEntry_linearMapOfEntries (K : J → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by
  classical
  cases nonempty_fintype J
  have hex : ∃ M : (J → ℂ) →ₗ[ℂ] (J → ℂ), linearMapEntry M = K := by
    refine ⟨{ toFun := fun φ c' => ∑ c, K c' c * φ c, map_add' := ?_, map_smul' := ?_ }, ?_⟩
    · intro φ ψ
      funext c'
      simp [mul_add, Finset.sum_add_distrib]
    · intro w φ
      funext c'
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    · funext c' c
      simp [linearMapEntry, Pi.single_apply]
  exact Classical.epsilon_spec hex
private theorem linearMapOfEntries_eq {K : J → J → ℂ} {G : (J → ℂ) →ₗ[ℂ] (J → ℂ)}
    (h : linearMapEntry G = K) : linearMapOfEntries K = G := by
  classical
  have e := linearMapEntry_linearMapOfEntries K
  refine LinearMap.pi_ext fun i x => ?_
  have hs : (Pi.single i x : J → ℂ) = x • Pi.single i 1 := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [hs, map_smul, map_smul]
  congr 1
  funext c'
  have e1 := congrFun (congrFun e c') i
  have e2 := congrFun (congrFun h c') i
  simp only [linearMapEntry] at e1 e2
  convert e1.trans e2.symm
private theorem det_linearMapOfEntries_perm (σ : J ≃ J) {M M' : J → J → ℂ}
    (h : ∀ c' c, M' c' c = M (σ c') (σ c)) :
    LinearMap.det (linearMapOfEntries M' : (J → ℂ) →ₗ[ℂ] (J → ℂ)) =
      LinearMap.det (linearMapOfEntries M : (J → ℂ) →ₗ[ℂ] (J → ℂ)) := by
  classical
  let E : (J → ℂ) ≃ₗ[ℂ] (J → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ σ
  have hE : ∀ (f : J → ℂ) (d : J), E f d = f (σ d) := fun f d => rfl
  have hsymm : ∀ c : J, E.symm (Pi.single c 1) = Pi.single (σ c) 1 := by
    intro c
    rw [LinearEquiv.symm_apply_eq]
    funext d
    rw [hE]
    by_cases hd : d = c
    · subst hd
      simp
    · have : σ d ≠ σ c := fun e => hd (σ.injective e)
      simp [hd, this]
  have key : (linearMapOfEntries M' : (J → ℂ) →ₗ[ℂ] (J → ℂ)) =
      (E : (J → ℂ) →ₗ[ℂ] (J → ℂ)) ∘ₗ linearMapOfEntries M ∘ₗ
        (E.symm : (J → ℂ) →ₗ[ℂ] (J → ℂ)) := by
    refine linearMapOfEntries_eq ?_
    funext c' c
    have e1 := congrFun (congrFun (linearMapEntry_linearMapOfEntries M) (σ c')) (σ c)
    simp only [linearMapEntry] at e1 ⊢
    rw [h]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hE]
    have e2 : linearMapOfEntries M (E.symm (Pi.single c 1)) (σ c') = M (σ c') (σ c) := by
      rw [hsymm c]
      convert e1
    convert e2
  rw [key, LinearMap.det_conj]
end Entries
section Classes
variable {F I : PeriodicData}
private theorem translate_comm (hF : IsPeriodic F) (m n : Fin 4 → ℤ) (ι : F.Carrier) :
    F.translate m (F.translate n ι) = F.translate n (F.translate m ι) := by
  rw [← hF.translate_add, ← hF.translate_add, add_comm]
private def quotShift (hF : IsPeriodic F) (s : ℕ) (w : Fin 4 → ℤ) :
    F.QuotMod s → F.QuotMod s :=
  Quot.lift (fun ι => F.mkQuot s (F.translate w ι)) (by
    rintro ι _ ⟨n, rfl⟩
    exact Quot.sound ⟨n, translate_comm hF w _ ι⟩)
private theorem quotShift_quotShift_neg (hF : IsPeriodic F) (s : ℕ) (w : Fin 4 → ℤ)
    (c : F.QuotMod s) : quotShift hF s w (quotShift hF s (-w) c) = c := by
  induction c using Quot.ind with
  | mk ι =>
    show F.mkQuot s (F.translate w (F.translate (-w) ι)) = F.mkQuot s ι
    rw [← hF.translate_add, neg_add_cancel, hF.translate_zero]
private def quotShiftEquiv (hF : IsPeriodic F) (s : ℕ) (w : Fin 4 → ℤ) :
    F.QuotMod s ≃ F.QuotMod s where
  toFun := quotShift hF s (-w)
  invFun := quotShift hF s w
  left_inv := quotShift_quotShift_neg hF s w
  right_inv := fun c => by
    have := quotShift_quotShift_neg hF s (-w) c
    rwa [neg_neg] at this
private theorem quotShift_add_period (hF : IsPeriodic F) (s : ℕ) (v m : Fin 4 → ℤ) :
    quotShift hF s (v + s • m) = quotShift hF s v := by
  funext c
  induction c using Quot.ind with
  | mk ι =>
    show F.mkQuot s (F.translate (v + s • m) ι) = F.mkQuot s (F.translate v ι)
    rw [hF.translate_add]
    exact (Quot.sound ⟨m, rfl⟩ : F.mkQuot s (F.translate v ι) = _).symm
private theorem descendMatrix_mkQuot {s : ℕ} {K : I.Carrier → I.Carrier → ℂ}
    (hK : ∀ ι' ι κ' κ, I.mkQuot s ι' = I.mkQuot s κ' → I.mkQuot s ι = I.mkQuot s κ →
      K ι' ι = K κ' κ) (ι' ι : I.Carrier) :
    descendMatrix I I s K (I.mkQuot s ι') (I.mkQuot s ι) = K ι' ι := by
  have spec := Classical.epsilon_spec (p := fun w => ∀ a b, I.mkQuot s a = I.mkQuot s ι' →
    I.mkQuot s b = I.mkQuot s ι → K a b = w) ⟨K ι' ι, fun a b ha hb => hK _ _ _ _ ha hb⟩
  exact (spec ι' ι rfl rfl).symm
private theorem periodization_translate (hI : IsPeriodic I) {Y Y' : I.Carrier → I.Carrier → ℂ}
    (s : ℕ) (u : Fin 4 → ℤ) (h : ∀ ι' ι, Y' (I.translate u ι') (I.translate u ι) = Y ι' ι)
    (ι' ι : I.Carrier) :
    periodization I I Y' s (I.translate u ι') (I.translate u ι) = periodization I I Y s ι' ι := by
  simp only [periodization]
  refine tsum_congr fun n => ?_
  rw [translate_comm hI (s • n) u ι, h]
private theorem periodization_translate_period (hI : IsPeriodic I)
    (Y : I.Carrier → I.Carrier → ℂ) (s : ℕ) (m : Fin 4 → ℤ) (ι' ι : I.Carrier) :
    periodization I I Y s ι' (I.translate (s • m) ι) = periodization I I Y s ι' ι := by
  simp only [periodization]
  have e := (Equiv.addLeft m).tsum_eq (fun n : Fin 4 → ℤ => Y ι' (I.translate (s • n) ι))
  rw [← e]
  refine tsum_congr fun n => ?_
  simp only [Equiv.coe_addLeft]
  rw [← hI.translate_add, smul_add]
private theorem periodization_congr_quot (hI : IsPeriodic I) {Y : I.Carrier → I.Carrier → ℂ}
    {s : ℕ}
    (hY : ∀ (m : Fin 4 → ℤ) ι' ι, Y (I.translate (s • m) ι') (I.translate (s • m) ι) = Y ι' ι)
    (ι' ι κ' κ : I.Carrier) (h' : I.mkQuot s ι' = I.mkQuot s κ')
    (h : I.mkQuot s ι = I.mkQuot s κ) :
    periodization I I Y s ι' ι = periodization I I Y s κ' κ := by
  obtain ⟨m', rfl⟩ := (mkQuot_eq_iff hI s _ _).1 h'
  obtain ⟨m, rfl⟩ := (mkQuot_eq_iff hI s _ _).1 h
  rw [periodization_translate_period hI Y s m]
  have e : I.translate (s • m') (I.translate (s • (-m')) ι) = ι := by
    rw [← hI.translate_add, smul_neg, neg_add_cancel, hI.translate_zero]
  have h2 := periodization_translate hI (Y := Y) (Y' := Y) s (s • m') (hY m') ι'
    (I.translate (s • (-m')) ι)
  rw [e, periodization_translate_period hI Y s] at h2
  exact h2.symm
private theorem shiftField_period (hF : IsPeriodic F) (s : ℕ) (ζ : F.QuotMod s → ℂ)
    (m : Fin 4 → ℤ) :
    shiftField F (s • m) (liftQuotField F s ζ) = liftQuotField F s ζ := by apply _root_.YangMills.Construction.PeriodicOperators.LocalTorusMatrices.shiftField_liftQuotField <;> assumption
private theorem op_translate_period (hF : IsPeriodic F)
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
    {ρ R : ℝ} (hT : IsLocalWith F I I T ρ R) {s : ℕ} {ζ : F.QuotMod s → ℂ}
    (hζ : IsSupBelow F (liftQuotField F s ζ) ρ) (m : Fin 4 → ℤ) (ι' ι : I.Carrier) :
    T (liftQuotField F s ζ) (I.translate (s • m) ι') (I.translate (s • m) ι) =
      T (liftQuotField F s ζ) ι' ι := by
  have h := hT.shift_covariant _ hζ (s • m) ι' ι
  rwa [shiftField_period hF] at h
private theorem det_quotOperator_quotShift (hF : IsPeriodic F) (hI : IsPeriodic I)
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} {ρ R : ℝ} (hT : IsLocalWith F I I T ρ R)
    {s : ℕ} [Finite (I.QuotMod s)] (ζ : F.QuotMod s → ℂ)
    (hζ : IsSupBelow F (liftQuotField F s ζ) ρ) (w : Fin 4 → ℤ) :
    LinearMap.det (LogDetSecondDerivs.quotOperator F I T s (ζ ∘ quotShift hF s (-w))) =
      LinearMap.det (LogDetSecondDerivs.quotOperator F I T s ζ) := by
  have hfield : liftQuotField F s (ζ ∘ quotShift hF s (-w)) =
      shiftField F w (liftQuotField F s ζ) := rfl
  have hζ' : IsSupBelow F (liftQuotField F s (ζ ∘ quotShift hF s (-w))) ρ := by
    obtain ⟨r, hr, hb⟩ := hζ
    exact ⟨r, hr, fun κ => by rw [hfield]; exact hb _⟩
  have hK : ∀ ι' ι κ' κ, I.mkQuot s ι' = I.mkQuot s κ' → I.mkQuot s ι = I.mkQuot s κ →
      periodicValue F I I T s ζ ι' ι = periodicValue F I I T s ζ κ' κ :=
    periodization_congr_quot hI (op_translate_period hF hT hζ)
  have hK' : ∀ ι' ι κ' κ, I.mkQuot s ι' = I.mkQuot s κ' → I.mkQuot s ι = I.mkQuot s κ →
      periodicValue F I I T s (ζ ∘ quotShift hF s (-w)) ι' ι =
        periodicValue F I I T s (ζ ∘ quotShift hF s (-w)) κ' κ :=
    periodization_congr_quot hI (op_translate_period hF hT hζ')
  refine det_linearMapOfEntries_perm (quotShiftEquiv hI s w) fun c' c => ?_
  induction c' using Quot.ind with
  | mk ι' =>
    induction c using Quot.ind with
    | mk ι =>
      have e1 := descendMatrix_mkQuot hK' ι' ι
      have e2 := descendMatrix_mkQuot hK (I.translate (-w) ι') (I.translate (-w) ι)
      have hcov : ∀ a b, T (liftQuotField F s (ζ ∘ quotShift hF s (-w))) (I.translate w a)
          (I.translate w b) = T (liftQuotField F s ζ) a b := fun a b => by
        rw [hfield]
        exact hT.shift_covariant _ hζ w a b
      have e3 := periodization_translate hI s w hcov (I.translate (-w) ι') (I.translate (-w) ι)
      have e4 : ∀ a, I.translate w (I.translate (-w) a) = a := fun a => by
        rw [← hI.translate_add, neg_add_cancel, hI.translate_zero]
      rw [e4, e4] at e3
      exact e1.trans (e3.trans e2.symm)
end Classes
section Columns
private theorem translate_unitCell (hTr : TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (z w : Fin 4 → ℤ) :
    (colourEdges L k k).translate w (unitCell L k z) = unitCell L k (z + w) := by
  obtain ⟨-, hsite, -, hbond, -⟩ := hTr L hL k k hk le_rfl w
  have hb := hbond 2 (gridEdge L k z) secondAxis (by
    show gridVertex L k z + InfiniteLattice.axisStep _ secondAxis - gridVertex L k z = _
    abel)
  have hs : FullSpace.vertexImage (intShift w) (gridVertex L k z) = gridVertex L k (z + w) := by
    apply Subtype.ext
    rw [(hsite (gridVertex L k z)).1]
    funext μ
    rw [Pi.add_apply, gridVertex_apply, gridVertex_apply]
    simp [castVec, meshAt]
  refine hb.trans ?_
  show ((2 : Fin 3), TowerTranslations.posEdgeForward
      (FullSpace.vertexImage (intShift w) (gridVertex L k z)) secondAxis) =
    ((2 : Fin 3), TowerTranslations.posEdgeForward (gridVertex L k (z + w)) secondAxis)
  rw [hs]
private theorem responseColumn_add (hPk : IsPeriodic (colourEdges L k k))
    (hcov : IsShiftInvariant (colourEdges L k k) (colourEdges L k 0) (responseKernel L k))
    (hsh : ∀ z w : Fin 4 → ℤ,
      (colourEdges L k k).translate w (unitCell L k z) = unitCell L k (z + w))
    (z w : Fin 4 → ℤ) (ι : (colourEdges L k 0).Carrier) :
    responseColumn L k (z + w) ι =
      responseColumn L k z ((colourEdges L k 0).translate (-w) ι) := by
  simp only [responseColumn]
  congr 1
  have h1 := hcov (-w) ι (unitCell L k (z + w))
  rw [← hsh z w, translate_neg_translate hPk] at h1
  rw [← hsh z w]
  exact h1.symm
private theorem periodize_translate {F : PeriodicData} (hF : IsPeriodic F) {s : ℕ} (hs : 0 < s)
    (f : F.Carrier → ℂ) (w : Fin 4 → ℤ) (c : F.QuotMod s) :
    periodize F s (fun κ => f (F.translate (-w) κ)) c =
      periodize F s f (quotShift hF s (-w) c) := by
  induction c using Quot.ind with
  | mk ι =>
    show periodize F s _ (F.mkQuot s ι) =
      periodize F s f (F.mkQuot s (F.translate (-w) ι))
    rw [periodize, periodize, tsum_quotClass hF hs (fun κ => f (F.translate (-w) κ)) ι,
      tsum_quotClass hF hs f]
    exact tsum_congr fun n => congrArg f (translate_comm hF _ _ _)
private theorem exists_centredCoords_period {s : ℕ} (x y : TorusFields.TorusSite s) :
    ∃ m : Fin 4 → ℤ, centredCoords x =
      centredCoords (x - y) + (centredCoords y + s • m) := by
  have h : ∀ μ, (s : ℤ) ∣
      centredCoords x μ - centredCoords (x - y) μ - centredCoords y μ := by
    intro μ
    rw [← CharP.intCast_eq_zero_iff (ZMod s) s]
    push_cast
    simp only [centredCoords, ZMod.coe_valMinAbs, Pi.sub_apply]
    ring
  choose m hm using h
  refine ⟨m, ?_⟩
  funext μ
  have h1 := hm μ
  have h2 : (s • m) μ = (s : ℤ) * m μ := by simp
  rw [Pi.add_apply, Pi.add_apply, h2]
  linarith
private theorem eval_quotShift {D : LocalLogDetTerm L k} (hF : IsPeriodic (colourEdges L k 0))
    (hI : IsPeriodic D.idx) {ρ R : ℝ}
    (hT : IsLocalWith (colourEdges L k 0) D.idx D.idx D.op ρ R) {s : ℕ}
    [Finite (D.idx.QuotMod s)] (g : (colourEdges L k 0).QuotMod s → ℝ)
    (hg : ∀ x, |g x| < ρ / 2) (w : Fin 4 → ℤ) :
    D.eval s (g ∘ quotShift hF s (-w)) = D.eval s g := by
  have hb : IsSupBelow (colourEdges L k 0) (liftQuotField (colourEdges L k 0) s
      fun c => (g c : ℂ)) ρ :=
    ⟨ρ / 2, by linarith [hT.radius_pos], fun κ => by
      simpa [liftQuotField] using (hg _).le⟩
  have h := det_quotOperator_quotShift hF hI hT (fun c => (g c : ℂ)) hb w
  simp only [LocalLogDetTerm.eval]
  congr 3
end Columns
set_option maxHeartbeats 1600000 in
theorem differenceKernelTranslationInvariant
    (hB : DifferenceIsLocalLogDetSum)
    (hImg : ResponseImagesFullSide.ResponseImagesHold)
    (hResp : ResponseOperators.Claim)
    (hSums : ExponentialSums.Bounds)
    (hCells : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (hIdx : TowerIndexSets.Claim)
    (hQuot : Quotients.QuotientTransposeNorm)
    (h₉ : PeriodicLattice.LevelBondOrientationDichotomy)
    (hTr : TowerTranslations.Claim) :
    DifferenceKernelTranslationInvariant := by
  classical
  intro a ha L hL k hk
  have hP0 := (hIdx L hL k 0 (Nat.zero_le k)).2.1
  have hPk := (hIdx L hL k k le_rfl).2.1
  obtain ⟨δ₀, -, hAll⟩ := hResp
  have hAt := hAll L hL k hk
  have hPer := hAt.resp_periodic
  have hcov := hPer.1
  obtain ⟨Ds, hDs, hev⟩ := hB a ha L hL k hk
  have hLpos : 0 < L := by have := hL.2; omega
  have hs : ∀ n, 0 < periodSide L n := fun n => by
    have := pow_pos hLpos n
    simp only [periodSide]
    omega
  have hsh := translate_unitCell hTr hL hk
  have hreal : ∀ z' ι, (responseColumn L k z' ι).im = 0 := by
    intro z' ι
    have := hAt.resp_real.1 ι (unitCell L k z')
    simp [responseColumn, Complex.mul_im, this]
  filter_upwards [hev, eventually_gt_atTop 0] with n hn1 hn
  obtain ⟨c, ε, hε, hform⟩ := hn1
  intro y x
  have hfin : Finite ((colourEdges L k 0).QuotMod (periodSide L n)) :=
    (hQuot _ _ hP0 hP0 _ (hs n)).1.2.1
  obtain ⟨hC, hBd⟩ := (hCells L hL k n hn).1 k le_rfl
  have hmem : ∀ z', pauliUnitForm L n k z' ∈ edgeFormSpace L n k k := fun z' =>
    pauliUnitForm_mem h₉ hL hn hk z'
  let P : (Fin 4 → ℤ) → (colourEdges L k 0).QuotMod (periodSide L n) → ℂ :=
    fun z' => periodize (colourEdges L k 0) (periodSide L n) (responseColumn L k z')
  let g : (Fin 4 → ℤ) → (colourEdges L k 0).QuotMod (periodSide L n) → ℝ :=
    fun z' x => (P z' x).re
  have read : ∀ z', ClassFnEqForm L n k 0
      (restrictToPositiveEdges (meshScaledResponse L n k (pauliUnitForm L n k z') :
        Edge L n k 0 → ComplexMatrix2))
      (P z') := fun z' =>
    classFnEqForm_responseColumn hP0 hPk hcov (hs n) hC hBd z' (hmem z')
      (hImg L hL k hk n hn ⟨_, hmem z'⟩)
  have hc : ∀ z' x, ((g z' x : ℝ) : ℂ) = P z' x := fun z' x =>
    Complex.ext (by simp [g])
      (by simpa using (im_periodize (summable_responseColumn hSums hP0 hPer z') (hreal z') _ x).symm)
  have near : ∀ z₀ z₁ : Fin 4 → ℤ, ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)),
      chainMinusBackground a (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ p.1 • (meshScaledResponse L n k (pauliUnitForm L n k z₀) :
          Edge L n k 0 → ComplexMatrix2) +
          algebraMap ℝ ℂ p.2 •
            (meshScaledResponse L n k (pauliUnitForm L n k z₁) : Edge L n k 0 → ComplexMatrix2))
        (trivialField L n k 0)) =
      (Ds.map fun D => D.eval (periodSide L n) fun x => p.1 * g z₀ x + p.2 * g z₁ x).sum + c := by
    intro z₀ z₁
    set r₀ := meshScaledResponse L n k (pauliUnitForm L n k z₀) with hr₀
    set r₁ := meshScaledResponse L n k (pauliUnitForm L n k z₁) with hr₁
    have hsmall : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)),
        ∀ x, |p.1 * g z₀ x + p.2 * g z₁ x| < ε := by
      refine eventually_all.2 fun x => ?_
      have hcont : Continuous fun p : ℝ × ℝ => |p.1 * g z₀ x + p.2 * g z₁ x| := by fun_prop
      have h0 := hcont.tendsto ((0 : ℝ), (0 : ℝ))
      simp only [zero_mul, add_zero, abs_zero] at h0
      exact h0.eventually_lt_const hε
    filter_upwards [hsmall] with p hp
    have hcoe : ((p.1 • r₀ + p.2 • r₁ : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) =
        algebraMap ℝ ℂ p.1 • (r₀ : Edge L n k 0 → ComplexMatrix2) +
          algebraMap ℝ ℂ p.2 • (r₁ : Edge L n k 0 → ComplexMatrix2) := by
      funext b
      simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply,
        Complex.coe_algebraMap]
      rw [real_smul_eq_complex_smul, real_smul_eq_complex_smul]
    have hreadp : ClassFnEqForm L n k 0
        (restrictToPositiveEdges ((p.1 • r₀ + p.2 • r₁ : edgeFormSpace L n k 0) :
          Edge L n k 0 → ComplexMatrix2))
        (fun x => ((p.1 * g z₀ x + p.2 * g z₁ x : ℝ) : ℂ)) := by
      intro ι
      have e₀ := read z₀ ι
      have e₁ := read z₁ ι
      have hb := (projPositiveEdge L n k 0 ι.2).2
      have m₀ := mem_traceless_of_mem_hermitianTraceless (r₀.2.1 _ hb)
      have m₁ := mem_traceless_of_mem_hermitianTraceless (r₁.2.1 _ hb)
      simp only [toPauliCoeffs, restrictToPositiveEdges] at e₀ e₁ ⊢
      simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply]
      rw [pauliCoeff_add (by rw [real_smul_eq_complex_smul]; exact Submodule.smul_mem _ _ m₀)
        (by rw [real_smul_eq_complex_smul]; exact Submodule.smul_mem _ _ m₁),
        pauliCoeff_real_smul _ m₀, pauliCoeff_real_smul _ m₁, ← e₀, ← e₁, ← hc, ← hc]
      push_cast
      ring
    have hval := hform (p.1 • r₀ + p.2 • r₁) _ hreadp hp
    rw [hcoe] at hval
    exact hval
  have hPshift : ∀ z' w : Fin 4 → ℤ,
      P (z' + w) = P z' ∘ quotShift hP0 (periodSide L n) (-w) := by
    intro z' w
    funext c'
    have hcol : responseColumn L k (z' + w) =
        fun κ => responseColumn L k z' ((colourEdges L k 0).translate (-w) κ) :=
      funext (responseColumn_add hPk hcov hsh z' w)
    simp only [P, hcol, Function.comp_apply]
    exact periodize_translate hP0 (hs n) _ w c'
  obtain ⟨m, hm⟩ := exists_centredCoords_period x y
  set y' := centredCoords y with hy'
  set x' := centredCoords x with hx'
  set z := centredCoords (x - y) with hz
  set S := quotShift hP0 (periodSide L n) (-y') with hS
  have hSm : quotShift hP0 (periodSide L n) (-(y' + (periodSide L n) • m)) = S := by
    have e : -(y' + (periodSide L n) • m) = -y' + (periodSide L n) • (-m) := by
      rw [smul_neg, neg_add]
    rw [e, quotShift_add_period]
  have hPy : P y' = P 0 ∘ S := by
    have := hPshift 0 y'
    rwa [zero_add] at this
  have hPx : P x' = P z ∘ S := by
    have := hPshift z (y' + (periodSide L n) • m)
    rw [hSm] at this
    rw [hm]
    exact this
  have hgy : ∀ c', g y' c' = g 0 (S c') := fun c' => by simp only [g, hPy, Function.comp_apply]
  have hgx : ∀ c', g x' c' = g z (S c') := fun c' => by simp only [g, hPx, Function.comp_apply]
  have hinv : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), ∀ D ∈ {D | D ∈ Ds},
      D.eval (periodSide L n) (fun x => p.1 * g y' x + p.2 * g x' x) =
        D.eval (periodSide L n) (fun x => p.1 * g 0 x + p.2 * g z x) := by
    refine (Filter.eventually_all_finite (List.finite_toSet Ds)).2 fun D hD => ?_
    have hA := hDs D hD
    obtain ⟨ρ, R, hT⟩ := hA.local_op
    have hρ := hT.radius_pos
    have : Finite (D.idx.QuotMod (periodSide L n)) :=
      (hQuot _ _ hA.periodic hA.periodic _ (hs n)).1.2.1
    have hsmall : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)),
        ∀ x, |p.1 * g 0 x + p.2 * g z x| < ρ / 2 := by
      refine eventually_all.2 fun x => ?_
      have hcont : Continuous fun p : ℝ × ℝ => |p.1 * g 0 x + p.2 * g z x| := by fun_prop
      have h0 := hcont.tendsto ((0 : ℝ), (0 : ℝ))
      simp only [zero_mul, add_zero, abs_zero] at h0
      exact h0.eventually_lt_const (by linarith)
    filter_upwards [hsmall] with p hp
    have e : (fun x => p.1 * g y' x + p.2 * g x' x) =
        (fun x => p.1 * g 0 x + p.2 * g z x) ∘ S := by
      funext c'
      simp only [Function.comp_apply, hgy, hgx]
    rw [e]
    exact eval_quotShift hP0 hA.periodic hT _ hp y'
  have hnear : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)),
      chainMinusBackground a (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ p.1 • (meshScaledResponse L n k (pauliUnitForm L n k y') :
          Edge L n k 0 → ComplexMatrix2) +
          algebraMap ℝ ℂ p.2 •
            (meshScaledResponse L n k (pauliUnitForm L n k x') : Edge L n k 0 → ComplexMatrix2))
        (trivialField L n k 0)) =
      chainMinusBackground a (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ p.1 • (meshScaledResponse L n k (pauliUnitForm L n k 0) :
          Edge L n k 0 → ComplexMatrix2) +
          algebraMap ℝ ℂ p.2 •
            (meshScaledResponse L n k (pauliUnitForm L n k z) : Edge L n k 0 → ComplexMatrix2))
        (trivialField L n k 0)) := by
    filter_upwards [near y' x', near 0 z, hinv] with p h1 h2 h3
    rw [h1, h2]
    congr 1
    exact congrArg List.sum (List.map_congr_left fun D hD => h3 D hD)
  have hcurry := hnear.curry_nhds
  have hmid : (fun σ : ℝ => deriv (fun τ : ℝ => chainMinusBackground a (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ σ • (meshScaledResponse L n k (pauliUnitForm L n k y') :
          Edge L n k 0 → ComplexMatrix2) +
          algebraMap ℝ ℂ τ •
            (meshScaledResponse L n k (pauliUnitForm L n k x') : Edge L n k 0 → ComplexMatrix2))
        (trivialField L n k 0))) 0) =ᶠ[𝓝 0]
      fun σ => deriv (fun τ : ℝ => chainMinusBackground a (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ σ • (meshScaledResponse L n k (pauliUnitForm L n k 0) :
          Edge L n k 0 → ComplexMatrix2) +
          algebraMap ℝ ℂ τ •
            (meshScaledResponse L n k (pauliUnitForm L n k z) : Edge L n k 0 → ComplexMatrix2))
        (trivialField L n k 0))) 0 := by
    filter_upwards [hcurry] with σ hσ
    exact Filter.EventuallyEq.deriv_eq hσ
  exact hmid.deriv_eq
end YangMills.Construction.RunningCouplingSlope.DifferenceKernelTranslationInvarianceProof
end
