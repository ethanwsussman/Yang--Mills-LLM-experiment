import YangMills.Construction.Matrices.CalculusOfHolomorphicMapsProof
import YangMills.Construction.RotationInvariance.DensityOfThePlateFunctionsAtDistinctPointsProof
import YangMills.Construction.ComplexAnalysis.RealLocusIdentity
import YangMills.Construction.RotationInvariance.CovarianceOfTheHarmonicsBetweenOrderedPositionsProof
import YangMills.Construction.RotationInvariance.DeterminationOfHolomorphicFunctionsOfTheDifferences
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.ForwardTube.ProductIntegralDetermination
open YangMills.Construction.RealPlane
open YangMills.Construction.Coordinates
def timeSeparatedTuples (n : ℕ) (η : ℝ) : Set (Fin n → RealPlane) :=
  successiveDifferences ⁻¹' realTuplesTimeAbove (n - 1) η
theorem continuous_planeTime : Continuous fun y : RealPlane => y 0 :=
  (EuclideanSpace.proj (0 : Fin 2) : RealPlane →L[ℝ] ℝ).continuous
theorem continuous_embedPlane : Continuous embedPlane :=
  (Complex.continuous_ofReal.comp continuous_planeTime).prodMk
    (Complex.continuous_ofReal.comp
      (EuclideanSpace.proj (1 : Fin 2) : RealPlane →L[ℝ] ℝ).continuous)
theorem continuous_complexifyRealTuple (p : ℕ) :
    Continuous (complexifyRealTuple (p := p)) := by apply _root_.YangMills.Construction.EuclideanFunctionals.HarmonicDensity.continuous_embedPlaneTuple <;> assumption
theorem continuous_successiveDifferences (n : ℕ) :
    Continuous (successiveDifferences (n := n)) :=
  continuous_pi fun _ => (continuous_apply _).sub (continuous_apply _)
theorem continuous_pairTupleEquiv (p : ℕ) : Continuous (pairTupleEquiv p) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency.continuous_pairTupleEquiv <;> assumption
theorem isOpen_realTuplesTimeAbove (p : ℕ) (η : ℝ) : IsOpen (realTuplesTimeAbove p η) := by
  have h : realTuplesTimeAbove p η = ⋂ i, {v | η < v i 0} := by
    ext v
    simp [realTuplesTimeAbove]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (continuous_planeTime.comp (continuous_apply i))
theorem isOpen_timeSeparatedTuples (n : ℕ) (η : ℝ) : IsOpen (timeSeparatedTuples n η) :=
  (isOpen_realTuplesTimeAbove _ η).preimage (continuous_successiveDifferences n)
theorem exists_successiveDifferences_eq {n : ℕ} (v : Fin (n - 1) → RealPlane) :
    ∃ y : Fin n → RealPlane, successiveDifferences y = v := by
  let w : ℕ → RealPlane := fun k => if h : k < n - 1 then v ⟨k, h⟩ else 0
  refine ⟨fun i => ∑ k ∈ Finset.range i, w k, ?_⟩
  funext i
  simp [successiveDifferences, Finset.sum_range_succ, w]
theorem successiveDifferences_mem_of_timeSeparated {n : ℕ} {η : ℝ}
    {b : Fin n → RealPlane → ℂ} (hb : TimeSeparated η b) {y : Fin n → RealPlane}
    (hy : ∀ i, y i ∈ tsupport (b i)) :
    successiveDifferences y ∈ realTuplesTimeAbove (n - 1) η := by
  intro i
  have hi : (i : ℕ) + 1 < n := by
    have := i.2
    omega
  have hgap := hb.2.2.2 i hi
  have hlow : minTime (tsupport (b ⟨i + 1, hi⟩)) ≤ y ⟨i + 1, hi⟩ 0 :=
    csInf_le ((hb.2.1 _).isCompact.image continuous_planeTime).bddBelow
      (mem_image_of_mem _ (hy _))
  have hup : y ⟨i, Nat.lt_of_succ_lt hi⟩ 0 ≤
      maxTime (tsupport (b ⟨i, Nat.lt_of_succ_lt hi⟩)) :=
    le_csSup ((hb.2.1 _).isCompact.image continuous_planeTime).bddAbove
      (mem_image_of_mem _ (hy _))
  show η < (y ⟨i + 1, hi⟩ - y ⟨i, Nat.lt_of_succ_lt hi⟩) 0
  rw [PiLp.sub_apply]
  linarith
theorem tsupport_complexifyProfiles {n : ℕ} (b : Fin n → RealPlane → ℝ) (i : Fin n) :
    tsupport (complexifyProfiles b i) = tsupport (b i) := by
  unfold tsupport
  congr 1
  ext y
  simp [Function.mem_support, complexifyProfiles]
theorem smoothTimeSeparated_of_testFamily {n : ℕ} {η : ℝ} {α : Fin n → RealPlane → ℝ}
    (hα : IsSmoothTestFamilyIn (timeSeparatedTuples n η) α)
    (hne : ∀ i, α i ≠ 0) : SmoothTimeSeparated η α := by
  have hcompact : ∀ i, IsCompact (tsupport (α i)) := fun i => (hα.2.1 i).isCompact
  have hnonempty : ∀ i, (tsupport (α i)).Nonempty := by
    intro i
    obtain ⟨x, hx⟩ := Function.ne_iff.1 (hne i)
    exact ⟨x, subset_tsupport _ hx⟩
  refine ⟨hα.1, fun i => ?_, fun i => ?_, fun i => ?_, fun i hi => ?_⟩
  · exact Complex.continuous_ofReal.comp (hα.1 i).continuous
  · show IsCompact _
    rw [tsupport_complexifyProfiles]
    exact hcompact i
  · intro h
    apply hne i
    funext x
    have := congrFun h x
    simpa [complexifyProfiles] using this
  · rw [tsupport_complexifyProfiles, tsupport_complexifyProfiles]
    have hi' : i < n := Nat.lt_of_succ_lt hi
    obtain ⟨a, ha, hamax⟩ := (hcompact ⟨i, hi'⟩).exists_isMaxOn (hnonempty _)
      continuous_planeTime.continuousOn
    obtain ⟨c, hc, hcmin⟩ := (hcompact ⟨i + 1, hi⟩).exists_isMinOn (hnonempty _)
      continuous_planeTime.continuousOn
    choose w hw using hnonempty
    have hne' : (⟨i, hi'⟩ : Fin n) ≠ ⟨i + 1, hi⟩ := by simp [Fin.ext_iff]
    let y : Fin n → RealPlane :=
      Function.update (Function.update w ⟨i, hi'⟩ a) ⟨i + 1, hi⟩ c
    have hy1 : y ⟨i + 1, hi⟩ = c := Function.update_self _ _ _
    have hy0 : y ⟨i, hi'⟩ = a := by
      simp only [y]
      rw [Function.update_of_ne hne', Function.update_self]
    have hy : y ∈ Set.univ.pi fun j => tsupport (α j) := by
      intro j _
      by_cases h1 : j = ⟨i + 1, hi⟩
      · subst h1
        rw [hy1]
        exact hc
      by_cases h0 : j = ⟨i, hi'⟩
      · subst h0
        rw [hy0]
        exact ha
      simp only [y]
      rw [Function.update_of_ne h1, Function.update_of_ne h0]
      exact hw j
    have hO := hα.2.2 hy ⟨i, by omega⟩
    have hO' : η < (y ⟨i + 1, hi⟩ - y ⟨i, hi'⟩) 0 := hO
    rw [hy1, hy0, PiLp.sub_apply] at hO'
    have e1 : minTime (tsupport (α ⟨i + 1, hi⟩)) = c 0 :=
      IsLeast.csInf_eq ⟨mem_image_of_mem _ hc, by
        rintro _ ⟨x, hx, rfl⟩
        exact isMinOn_iff.1 hcmin x hx⟩
    have e2 : maxTime (tsupport (α ⟨i, hi'⟩)) = a 0 :=
      IsGreatest.csSup_eq ⟨mem_image_of_mem _ ha, by
        rintro _ ⟨x, hx, rfl⟩
        exact isMaxOn_iff.1 hamax x hx⟩
    rw [e1, e2]
    exact hO'
theorem productWeightedIntegral_eq_differencesIntegral {n : ℕ} {η : ℝ}
    (f : (Fin (n - 1) → ℂ × ℂ) → ℂ) {α : Fin n → RealPlane → ℝ}
    (hα : IsSmoothTestFamilyIn (timeSeparatedTuples n η) α) :
    productWeightedIntegral (timeSeparatedTuples n η) α
        (fun y => f (complexifyRealTuple (successiveDifferences y))) =
      differencesIntegral α f := by
  unfold productWeightedIntegral differencesIntegral profileIntegral
  congr 1
  funext y
  unfold profileIntegrand
  have hset : (Set.univ.pi fun i => tsupport (complexifyProfiles α i)) =
      Set.univ.pi fun i => tsupport (α i) := by
    simp only [tsupport_complexifyProfiles]
  rw [hset]
  by_cases hy : y ∈ Set.univ.pi fun i => tsupport (α i)
  · rw [indicator_of_mem (hα.2.2 hy), indicator_of_mem hy]
    rfl
  · rw [indicator_of_notMem hy]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hy
    obtain ⟨i, hi⟩ := hy
    have hp : ∏ a, ((α a (y a) : ℝ) : ℂ) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [image_eq_zero_of_notMem_tsupport hi])
    refine indicator_apply_eq_zero.2 fun _ => ?_
    show (∏ a, ((α a (y a) : ℝ) : ℂ)) * _ = 0
    rw [hp, zero_mul]
theorem productWeightedIntegral_eq_zero_of_eq_zero {n : ℕ} (O : Set (Fin n → RealPlane))
    (α : Fin n → RealPlane → ℝ) (g : (Fin n → RealPlane) → ℂ) {i : Fin n}
    (hi : α i = 0) : productWeightedIntegral O α g = 0 := by
  have h : ∀ y, O.indicator (fun y => (∏ a, ((α a (y a) : ℝ) : ℂ)) * g y) y = 0 := fun y =>
    indicator_apply_eq_zero.2 fun _ => by
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), zero_mul]
  simp only [productWeightedIntegral, h, integral_zero]
theorem prop_productWeightedIntegral_of_testFamily {n : ℕ} {η : ℝ}
    (f : (Fin (n - 1) → ℂ × ℂ) → ℂ) {P : ℂ → Prop}
    (h0 : P 0) (h : ∀ b, SmoothTimeSeparated η b → P (differencesIntegral b f))
    (α : Fin n → RealPlane → ℝ)
    (hα : IsSmoothTestFamilyIn (timeSeparatedTuples n η) α) :
    P (productWeightedIntegral (timeSeparatedTuples n η) α
      (fun y => f (complexifyRealTuple (successiveDifferences y)))) := by
  by_cases hne : ∀ i, α i ≠ 0
  · rw [productWeightedIntegral_eq_differencesIntegral f hα]
    exact h α (smoothTimeSeparated_of_testFamily hα hne)
  · simp only [not_forall, not_not] at hne
    obtain ⟨i, hi⟩ := hne
    rw [productWeightedIntegral_eq_zero_of_eq_zero _ α _ hi]
    exact h0
theorem scalarEquiv_apply (x : ℂ) (j : Fin 1) :
    Matrices.GroupLieProduct.Subspaces.AnalyticCalculus.scalarEquiv x j = x := by apply _root_.YangMills.DeltaSharedProofs.p23888 <;> assumption
theorem continuousOn_of_holomorphicOnTuples {p : ℕ} {D : Set (Fin p → ℂ × ℂ)}
    {f : (Fin p → ℂ × ℂ) → ℂ} (hf : HolomorphicOnTuples D f) : ContinuousOn f D := by apply _root_.YangMills.Construction.EuclideanFunctionals.HarmonicRotationCovariance.continuousOn_of_holomorphicOnTuples <;> assumption
theorem pairTupleEquiv_complexifyRealTuple {p : ℕ} (v : Fin p → RealPlane) (i : Fin p)
    (k : Fin 2) :
    pairTupleEquiv p (complexifyRealTuple v) (finProdFinEquiv (i, k)) = (v i k : ℂ) := by
  have h : ∀ k : Fin 2, pairTupleEquiv p (complexifyRealTuple v) (finProdFinEquiv (i, k)) =
      (v i k : ℂ) :=
    Fin.forall_fin_two.2
      ⟨by rw [pairTupleEquiv_apply_fst]; rfl, by rw [pairTupleEquiv_apply_snd]; rfl⟩
  exact h k
theorem eq_zero_of_eq_zero_on_realTuplesTimeAbove
    (hid : ComplexAnalysis.IdentityTheoremOnRealLocus) {p : ℕ} (hp : 1 ≤ p) {η : ℝ}
    {D : Set (Fin p → ℂ × ℂ)} {f : (Fin p → ℂ × ℂ) → ℂ} (hDc : IsConnected D)
    (hUD : ∀ v ∈ realTuplesTimeAbove p η, complexifyRealTuple v ∈ D)
    (hf : HolomorphicOnTuples D f)
    (hU : ∀ v ∈ realTuplesTimeAbove p η, f (complexifyRealTuple v) = 0) :
    ∀ z ∈ D, f z = 0 := by
  let e := pairTupleEquiv p
  have hconn : IsConnected (e '' D) :=
    hDc.image e (continuous_pairTupleEquiv p).continuousOn
  have hhol : ComplexCoordinates.IsHolomorphicIn (N' := 1) (e '' D)
      (fun z _ => (f ∘ e.symm) z) := by
    have heq : (fun (z : ComplexCoordinates (p * 2)) (_ : Fin 1) => (f ∘ e.symm) z) =
        Matrices.GroupLieProduct.Subspaces.AnalyticCalculus.scalarEquiv ∘ f ∘ e.symm := by
      funext z j
      exact (scalarEquiv_apply _ j).symm
    rw [heq]
    exact hf
  let O' : Set (ComplexCoordinates (p * 2)) :=
    ⋂ i : Fin p, {z | η < (z (finProdFinEquiv (i, 0))).re}
  have hO' : IsOpen O' := isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply _))
  have hrep : ∀ z ∈ O' ∩ ComplexCoordinates.realLocus (p * 2),
      ∃ v ∈ realTuplesTimeAbove p η, z = e (complexifyRealTuple v) := by
    rintro z ⟨hz, hr⟩
    let v : Fin p → RealPlane := fun i =>
      !₂[(z (finProdFinEquiv (i, 0))).re, (z (finProdFinEquiv (i, 1))).re]
    have hv : ∀ i k, ((v i k : ℝ) : ℂ) = z (finProdFinEquiv (i, k)) := by
      intro i
      refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
      · apply Complex.ext
        · simp [v]
        · simpa [v] using (hr _).symm
      · apply Complex.ext
        · simp [v]
        · simpa [v] using (hr _).symm
    refine ⟨v, fun i => ?_, ?_⟩
    · have := mem_iInter.1 hz i
      simpa [v] using this
    · funext j
      obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective j
      rw [pairTupleEquiv_complexifyRealTuple, hv]
  have hmem : ∀ v ∈ realTuplesTimeAbove p η,
      e (complexifyRealTuple v) ∈ O' ∩ ComplexCoordinates.realLocus (p * 2) := by
    intro v hv
    refine ⟨mem_iInter.2 fun i => ?_, fun j => ?_⟩
    · show η < (pairTupleEquiv p (complexifyRealTuple v) (finProdFinEquiv (i, 0))).re
      rw [pairTupleEquiv_complexifyRealTuple]
      simpa using hv i
    · obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective j
      show (pairTupleEquiv p (complexifyRealTuple v) (finProdFinEquiv (i, k))).im = 0
      rw [pairTupleEquiv_complexifyRealTuple]
      simp
  have hnonempty : (O' ∩ ComplexCoordinates.realLocus (p * 2)).Nonempty := by
    refine ⟨_, hmem (fun _ => !₂[η + 1, 0]) fun i => ?_⟩
    simp
  have hsub : O' ∩ ComplexCoordinates.realLocus (p * 2) ⊆
      e '' D ∩ ComplexCoordinates.realLocus (p * 2) := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hrep z hz
    exact ⟨mem_image_of_mem _ (hUD v hv), hz.2⟩
  have hzero : ∀ z ∈ O' ∩ ComplexCoordinates.realLocus (p * 2), (f ∘ e.symm) z = 0 := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hrep z hz
    simpa using hU v hv
  have hall := hid.1 (p * 2) (by omega) (e '' D) (f ∘ e.symm) hhol.1 hconn hhol
    (O' ∩ ComplexCoordinates.realLocus (p * 2)) hnonempty hsub ⟨O', hO', rfl⟩ hzero
  intro z hz
  simpa using hall (e z) (mem_image_of_mem _ hz)
theorem determinedByProductIntegrals_holds (hdensity : DensityUniqueness.Claim)
    (hidentity : ComplexAnalysis.IdentityTheoremOnRealLocus) :
    HolomorphicDifferences.determinedByProductIntegrals := by
  intro n hn η _
  refine ⟨fun b hb y hy => successiveDifferences_mem_of_timeSeparated hb hy, ?_⟩
  intro D f _ hDc hUD hf
  have hg : ContinuousOn (fun y => f (complexifyRealTuple (successiveDifferences y)))
      (timeSeparatedTuples n η) :=
    (continuousOn_of_holomorphicOnTuples hf).comp
      ((continuous_complexifyRealTuple _).comp (continuous_successiveDifferences n)).continuousOn
      fun y hy => hUD _ hy
  obtain ⟨h1, h2⟩ := hdensity n (by omega) _ (isOpen_timeSeparatedTuples n η) _ hg
  refine ⟨fun h => ?_, fun h v hv => ?_⟩
  · refine eq_zero_of_eq_zero_on_realTuplesTimeAbove hidentity (by omega) hDc hUD hf
      fun v hv => ?_
    obtain ⟨y, rfl⟩ := exists_successiveDifferences_eq v
    exact h1 (prop_productWeightedIntegral_of_testFamily f (P := fun c => c = 0) rfl h) y hv
  · obtain ⟨y, rfl⟩ := exists_successiveDifferences_eq v
    exact h2 (prop_productWeightedIntegral_of_testFamily f (P := fun c => c.im = 0) rfl h) y hv
end YangMills.Construction.ForwardTube.ProductIntegralDetermination
end
