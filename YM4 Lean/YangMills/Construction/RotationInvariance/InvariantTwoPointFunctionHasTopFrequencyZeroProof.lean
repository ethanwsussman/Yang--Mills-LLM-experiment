import YangMills.Construction.TwoPoints.GrowthBoundsTheNumberOfHarmonicsProof
import YangMills.Construction.RealPlane.ContinuousDensityUniqueness
import YangMills.Construction.RotationInvariance.InvariantTwoPointFunctionHasTopFrequencyZero
import YangMills.Construction.RotationInvariance.MomentsAndConnectedFunctionsUnderAnOrthogonalMap
import YangMills.Construction.RotationInvariance.MotionsOfPlatesAndQuarterRotations
import YangMills.Construction.RotationInvariance.PlaneDataAreDataOfTheTwoSettings
import Mathlib
set_option autoImplicit false
open Complex (I)
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror RealPlane ForwardTube
open Matrices.GroupLieProduct.Subspaces.AnalyticCalculus (scalarEquiv)
namespace EuclideanFunctionals.TwoPointTopFrequency
open MomentSymmetry
theorem rotate_neg_rotate (t : ℝ) (y : RealPlane) :
    RealPlane.rotate (-t) (RealPlane.rotate t y) = y := by
  have hst := Real.sin_sq_add_cos_sq t
  ext i
  fin_cases i
  · simp [RealPlane.rotate]
    linear_combination (y 0) * hst
  · simp [RealPlane.rotate]
    linear_combination (y 1) * hst
theorem rotate_rotate_neg (t : ℝ) (y : RealPlane) :
    RealPlane.rotate t (RealPlane.rotate (-t) y) = y := by
  simpa using rotate_neg_rotate (-t) y
def rotateLinearIsometryEquiv (t : ℝ) : RealPlane ≃ₗᵢ[ℝ] RealPlane where
  toFun := RealPlane.rotate t
  invFun := RealPlane.rotate (-t)
  left_inv := rotate_neg_rotate t
  right_inv := rotate_rotate_neg t
  map_add' x y := by
    ext i
    fin_cases i <;> simp [RealPlane.rotate] <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [RealPlane.rotate] <;> ring
  norm_map' y := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    have hst := Real.sin_sq_add_cos_sq t
    simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    simp [RealPlane.rotate]
    linear_combination (y 0 ^ 2 + y 1 ^ 2) * hst
theorem continuous_rotate (t : ℝ) : Continuous (RealPlane.rotate t) :=
  (rotateLinearIsometryEquiv t).continuous
theorem continuous_coord (i : Fin 2) : Continuous fun y : RealPlane => y i :=
  (EuclideanSpace.proj i : RealPlane →L[ℝ] ℝ).continuous
theorem mem_tsupport_comp_rotate (β : RealPlane → ℂ) (t : ℝ) (y : RealPlane) :
    y ∈ tsupport (β ∘ RealPlane.rotate (-t)) ↔
      RealPlane.rotate (-t) y ∈ tsupport β := by
  have hpre := tsupport_comp_eq_preimage β (rotateLinearIsometryEquiv (-t)).toHomeomorph
  have hpre' : tsupport (β ∘ RealPlane.rotate (-t)) =
      RealPlane.rotate (-t) ⁻¹' tsupport β := hpre
  rw [hpre']
  rfl
def rotationOrderedPairs (t : ℝ) : Set (Fin 2 → RealPlane) :=
  {y | y 0 0 < y 1 0 ∧ RealPlane.rotate t (y 0) 0 < RealPlane.rotate t (y 1) 0}
theorem isOpen_rotationOrderedPairs (t : ℝ) : IsOpen (rotationOrderedPairs t) := by
  have c : ∀ i : Fin 2, Continuous fun y : Fin 2 → RealPlane => y i 0 := fun i =>
    (continuous_coord 0).comp (continuous_apply i)
  have c' : ∀ i : Fin 2, Continuous fun y : Fin 2 → RealPlane =>
      RealPlane.rotate t (y i) 0 := fun i =>
    (continuous_coord 0).comp ((continuous_rotate t).comp (continuous_apply i))
  exact (isOpen_lt (c 0) (c 1)).inter (isOpen_lt (c' 0) (c' 1))
abbrev pairDiff (y : Fin 2 → RealPlane) : Fin 1 → ℂ × ℂ :=
  embedPlaneTuple (successiveDifferences y)
theorem continuous_pairDiff : Continuous pairDiff := by
  refine continuous_pi fun i => ?_
  have hcd : Continuous fun y : Fin 2 → RealPlane => embedPlane (y 1 - y 0) := by
    have hc : Continuous embedPlane :=
      (Complex.continuous_ofReal.comp (continuous_coord 0)).prodMk
        (Complex.continuous_ofReal.comp (continuous_coord 1))
    exact hc.comp ((continuous_apply 1).sub (continuous_apply 0))
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  exact hcd
theorem pairDiff_mem_forwardTubePow {y : Fin 2 → RealPlane} (hlt : y 0 0 < y 1 0) :
    pairDiff y ∈ forwardTubePow 1 := by
  intro i _
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  show embedPlane (y 1 - y 0) ∈ forwardTube
  constructor <;> simpa [lightConePlus, lightConeMinus, embedPlane] using hlt
theorem continuous_pairTupleEquiv (q : ℕ) : Continuous (pairTupleEquiv q) := by
  refine continuous_pi fun k => ?_
  obtain ⟨⟨i, c⟩, rfl⟩ := finProdFinEquiv.surjective k
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · simp only [pairTupleEquiv_apply_fst]
    fun_prop
  · simp only [pairTupleEquiv_apply_snd]
    fun_prop
theorem continuousOn_of_holomorphicOnTuples {q : ℕ} {K : (Fin q → ℂ × ℂ) → ℂ}
    (hK : HolomorphicOnTuples (forwardTubePow q) K) : ContinuousOn K (forwardTubePow q) := by
  have hK' : Coordinates.ComplexCoordinates.IsHolomorphicIn (pairTupleEquiv q '' forwardTubePow q)
      (scalarEquiv ∘ K ∘ (pairTupleEquiv q).symm) := hK
  have h1 := hK'.2.1
  have h2 : ContinuousOn (fun v => (scalarEquiv ∘ K ∘
      (pairTupleEquiv q).symm) (pairTupleEquiv q v) 0) (forwardTubePow q) :=
    ((continuous_apply 0).comp_continuousOn
      (h1.comp (continuous_pairTupleEquiv q).continuousOn fun v hv => ⟨v, hv, rfl⟩))
  refine h2.congr fun v _ => ?_
  simp [scalarEquiv]
theorem funsTimeSeparated_of_tsupport {γ : Fin 2 → RealPlane → ℂ}
    (hc : ∀ i, HasCompactSupport (γ i)) (hne : ∀ i, γ i ≠ 0)
    (hlt : ∀ a ∈ tsupport (γ 0), ∀ b ∈ tsupport (γ 1), a 0 < b 0) :
    FunsTimeSeparated γ := by
  have hn : ∀ i, (tsupport (γ i)).Nonempty := fun i => by
    obtain ⟨x, hx⟩ := Function.ne_iff.1 (hne i)
    exact ⟨x, subset_tsupport _ hx⟩
  refine ⟨hc, hne, fun i => hc i, hn, fun i hi => ?_⟩
  have hi0 : i = 0 := by omega
  subst hi0
  obtain ⟨⟨a, ha, hae⟩, -⟩ := isGreatest_supInner (rotatedDirection rightAngleZero) (hc 0) (hn 0)
  obtain ⟨⟨b, hb, hbe⟩, -⟩ := isLeast_infInner (rotatedDirection rightAngleZero) (hc 1) (hn 1)
  have hin : ∀ z : RealPlane, inner ℝ (rotatedDirection rightAngleZero) z = z 0 := fun z => by
    rw [rotatedDirection_rightAngleZero, inner_eq_coord_sum]
    simp [RealPlane.unitX]
  have hab := hlt a ha b hb
  simp only [hin] at hae hbe
  show supInner _ (tsupport (γ 0)) < infInner _ (tsupport (γ 1))
  rw [← hae, ← hbe]
  exact hab
theorem productFunctions_mem_disjointComplexTuples (hMotions : ProductMotions.MotionFacts)
    {γ : Fin 2 → RealPlane → ℂ} (hγ : ∀ i, γ i ∈ complexProfiles)
    (φ : Fin 2 → realLabels)
    (hlt : ∀ a ∈ tsupport (γ 0), ∀ b ∈ tsupport (γ 1), a 0 < b 0) :
    (fun i => productFunction (γ i) (φ i)) ∈ disjointComplexTuples 2 := by
  have hp := hMotions.2.2.1
  have hd : Disjoint (supp (productFunction (γ 0) (φ 0))) (supp (productFunction (γ 1) (φ 1))) := by
    refine Set.disjoint_left.2 fun x h0 h1 => ?_
    have a0 := ((hp _ (hγ 0) _ (φ 0).2).2 h0).1
    have a1 := ((hp _ (hγ 1) _ (φ 1).2).2 h1).1
    exact lt_irrefl _ (hlt _ a0 _ a1)
  refine ⟨fun l => (hp _ (hγ l) _ (φ l).2).1, ?_⟩
  intro k l hkl
  fin_cases k <;> fin_cases l
  · exact absurd rfl hkl
  · exact hd
  · exact hd.symm
  · exact absurd rfl hkl
theorem list_ofFn_two (f : Fin 2 → R4 → ℝ) : List.ofFn f = [f 0, f 1] := by
  simp [List.ofFn_succ]
theorem centeredFnFree_real_pair {m : SharpScale} {S : ConnFamily} (d : ProductPlaneData m S)
    (hMoments : OrthogonalInvariance.OrthogonalMapStatement) {h : Fin 2 → R4 → ℂ}
    (hh : h ∈ disjointComplexTuples 2) (hreal : ∀ l, IsRealValued (h l)) :
    centeredFnFree S (complexTuple h) =
      ((Ambient.evalOrZero (S.fn 2 le_rfl) [fun x => (h 0 x).re, fun x => (h 1 x).re] : ℝ) : ℂ) := by
  obtain ⟨⟨hrec, -, hempty, -⟩, -, -, -, -, hagree, -⟩ := hMoments m S d.fnl 1
  have hX := ofFn_re_mem_sepN hh hreal
  have h1 := hagree 2 (by norm_num) _ hX
  rw [complexTuple_complexify] at h1
  rw [complexTuple, if_pos hreal, ← h1, hrec 2 le_rfl _ hX, hempty]
  simp only [Ambient.ConnectedFamily.evalAt]
  simp
  exact congrArg _ (list_ofFn_two _)
theorem profileIntegral_comp_rotate (t : ℝ) (β : Fin 2 → RealPlane → ℂ)
    (G : (Fin 2 → RealPlane) → ℂ) :
    profileIntegral (fun i => β i ∘ RealPlane.rotate (-t)) G =
      profileIntegral β fun y => G (mapPoints (RealPlane.rotate t) y) := by
  have hmp : MeasurePreserving
      (MeasurableEquiv.piCongrRight fun _ : Fin 2 =>
        (rotateLinearIsometryEquiv t).toHomeomorph.toMeasurableEquiv)
      (volume : Measure (Fin 2 → RealPlane)) volume := by
    rw [volume_pi]
    exact measurePreserving_pi (fun _ => volume) (fun _ => volume)
      fun _ => (rotateLinearIsometryEquiv t).measurePreserving
  unfold profileIntegral
  rw [← hmp.integral_comp']
  congr 1
  funext y
  have hT : (MeasurableEquiv.piCongrRight (fun _ : Fin 2 =>
      (rotateLinearIsometryEquiv t).toHomeomorph.toMeasurableEquiv) y) =
      mapPoints (RealPlane.rotate t) y := rfl
  rw [hT]
  unfold profileIntegrand
  have hiff : mapPoints (RealPlane.rotate t) y ∈
      (Set.univ.pi fun i => tsupport (β i ∘ RealPlane.rotate (-t))) ↔
        y ∈ Set.univ.pi fun i => tsupport (β i) := by
    simp only [Set.mem_univ_pi, mem_tsupport_comp_rotate, mapPoints, rotate_neg_rotate]
  by_cases hy : y ∈ Set.univ.pi fun i => tsupport (β i)
  · rw [Set.indicator_of_mem (hiff.2 hy), Set.indicator_of_mem hy]
    simp [mapPoints, rotate_neg_rotate]
  · rw [Set.indicator_of_notMem (mt hiff.1 hy), Set.indicator_of_notMem hy]
theorem integrable_profileIntegrand {α : Fin 2 → RealPlane → ℂ}
    (hα : ∀ i, Continuous (α i)) (hc : ∀ i, HasCompactSupport (α i))
    {f : (Fin 2 → RealPlane) → ℂ}
    (hf : ContinuousOn f (Set.univ.pi fun i => tsupport (α i))) :
    Integrable (profileIntegrand α f) := by
  have hP : IsCompact (Set.univ.pi fun i => tsupport (α i)) := isCompact_univ_pi fun i => hc i
  unfold profileIntegrand
  rw [integrable_indicator_iff hP.measurableSet]
  refine ContinuousOn.integrableOn_compact hP ?_
  refine ContinuousOn.mul ?_ hf
  exact (continuous_finsetProd _ fun i _ => (hα i).comp (continuous_apply i)).continuousOn
theorem kernel_rotate_invariant {m : SharpScale} {S : ConnFamily} (d : ProductPlaneData m S)
    (hMoments : OrthogonalInvariance.OrthogonalMapStatement) (hMotions : ProductMotions.MotionFacts)
    (hDensity : RealPlane.DensityUniqueness.Claim) {φ : Fin 2 → realLabels}
    {K : (Fin 1 → ℂ × ℂ) → ℂ} (hK : IsPlaneKernel S φ K) {t : ℝ}
    (hinv : TwoPointInvariant S (rotateMotion t))
    {y : Fin 2 → RealPlane} (hy : y ∈ rotationOrderedPairs t) :
    K (pairDiff (mapPoints (RealPlane.rotate t) y)) = K (pairDiff y) := by
  let O := rotationOrderedPairs t
  let G : (Fin 2 → RealPlane) → ℂ := fun z => K (pairDiff z)
  let G' : (Fin 2 → RealPlane) → ℂ := fun z => G (mapPoints (RealPlane.rotate t) z)
  have hKc := continuousOn_of_holomorphicOnTuples hK.holomorphic
  have hGc : ContinuousOn G O :=
    hKc.comp continuous_pairDiff.continuousOn fun z hz => pairDiff_mem_forwardTubePow hz.1
  have hT : Continuous fun z : Fin 2 → RealPlane => mapPoints (RealPlane.rotate t) z :=
    continuous_pi fun i => (continuous_rotate t).comp (continuous_apply i)
  have hG'c : ContinuousOn G' O :=
    hKc.comp (continuous_pairDiff.comp hT).continuousOn
      fun z hz => pairDiff_mem_forwardTubePow hz.2
  have hvan : ∀ α, IsSmoothTestFamilyIn O α →
      productWeightedIntegral O α (fun z => G' z - G z) = 0 := by
    rintro α ⟨hsm, hcs, hsub⟩
    by_cases h0 : ∃ i, α i = 0
    · obtain ⟨i, hi⟩ := h0
      have hz : ∀ z : Fin 2 → RealPlane, (∏ a, ((α a (z a) : ℝ) : ℂ)) = 0 :=
        fun z => Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      simp [productWeightedIntegral, Set.indicator, hz]
    have hαne : ∀ i, α i ≠ 0 := fun i hi => h0 ⟨i, hi⟩
    let β : Fin 2 → RealPlane → ℂ := fun i z => (α i z : ℂ)
    let β' : Fin 2 → RealPlane → ℂ := fun i => β i ∘ RealPlane.rotate (-t)
    have hβc : ∀ i, ContDiff ℝ 1 (β i) := fun i =>
      Complex.ofRealCLM.contDiff.comp ((hsm i).of_le (by exact_mod_cast le_top))
    have hβ : ∀ i, β i ∈ complexProfiles := fun i =>
      ⟨hβc i, (hcs i).comp_left Complex.ofReal_zero⟩
    have hts : ∀ i, tsupport (β i) = tsupport (α i) := fun i => by
      have e : Function.support (β i) = Function.support (α i) := by
        ext z
        simp [β]
      unfold tsupport
      rw [e]
    have hβ' : ∀ i, β' i ∈ complexProfiles := fun i =>
      (hMotions.2.2.2.2 (β i) (hβ i) (φ i) (φ i).2 0 t).2.1
    have hβne : ∀ i, β i ≠ 0 := fun i hb => hαne i (by
      funext z
      have := congrFun hb z
      simpa [β] using this)
    have hβ'ne : ∀ i, β' i ≠ 0 := fun i hb => hβne i (by
      funext z
      have := congrFun hb (RealPlane.rotate t z)
      simpa [β', rotate_neg_rotate] using this)
    have hC : (Set.univ.pi fun i => tsupport (β i)) ⊆ O := by
      simpa only [hts] using hsub
    have hord : ∀ a ∈ tsupport (β 0), ∀ b ∈ tsupport (β 1),
        a 0 < b 0 ∧ RealPlane.rotate t a 0 < RealPlane.rotate t b 0 := by
      intro a ha b hb
      exact show (![a, b] : Fin 2 → RealPlane) ∈ O from hC (by
        intro i _
        fin_cases i
        · exact ha
        · exact hb)
    have hord' : ∀ a ∈ tsupport (β' 0), ∀ b ∈ tsupport (β' 1), a 0 < b 0 := by
      intro a ha b hb
      have hr := (hord _ ((mem_tsupport_comp_rotate _ _ _).1 ha) _
        ((mem_tsupport_comp_rotate _ _ _).1 hb)).2
      rwa [rotate_rotate_neg, rotate_rotate_neg] at hr
    have hT0 : FunsTimeSeparated β := funsTimeSeparated_of_tsupport (fun i => (hβ i).2) hβne
      fun a ha b hb => (hord a ha b hb).1
    have hT1 : FunsTimeSeparated β' :=
      funsTimeSeparated_of_tsupport (fun i => (hβ' i).2) hβ'ne hord'
    have hreal : ∀ i, IsRealValued (productFunction (β i) (φ i)) := fun i x => by
      simp [productFunction, β]
    have hreal' : ∀ i, IsRealValued (productFunction (β' i) (φ i)) := fun i x => by
      simp [productFunction, β', β]
    have hmem := productFunctions_mem_disjointComplexTuples hMotions hβ φ
      fun a ha b hb => (hord a ha b hb).1
    have hmem' := productFunctions_mem_disjointComplexTuples hMotions hβ' φ hord'
    have hval : centeredFnFree S (complexTuple fun i => productFunction (β i) (φ i)) =
        ((Ambient.evalOrZero (S.fn 2 le_rfl) [fun x => (productFunction (β 0) (φ 0) x).re,
          fun x => (productFunction (β 1) (φ 1) x).re] : ℝ) : ℂ) :=
      centeredFnFree_real_pair d hMoments hmem hreal
    have hval' : centeredFnFree S (complexTuple fun i => productFunction (β' i) (φ i)) =
        ((Ambient.evalOrZero (S.fn 2 le_rfl) [fun x => (productFunction (β' 0) (φ 0) x).re,
          fun x => (productFunction (β' 1) (φ 1) x).re] : ℝ) : ℂ) :=
      centeredFnFree_real_pair d hMoments hmem' hreal'
    have hturn : ∀ i, (rotateMotion t).actFn (fun x => (productFunction (β i) (φ i) x).re) =
        fun x => (productFunction (β' i) (φ i) x).re := fun i => by
      have hon := (hMotions.2.2.2.1 (β i) (hβ i) (φ i) (φ i).2 0 t).2.1
      funext x
      exact congrArg Complex.re (congrFun hon x)
    have hsep : [fun x => (productFunction (β 0) (φ 0) x).re,
        fun x => (productFunction (β 1) (φ 1) x).re] ∈ sepN 2 := by
      have hs := ofFn_re_mem_sepN hmem hreal
      rwa [list_ofFn_two] at hs
    have hσ : centeredFnAtProducts S β' φ = centeredFnAtProducts S β φ := by
      unfold centeredFnAtProducts
      have e : [fun x => (productFunction (β' 0) (φ 0) x).re,
          fun x => (productFunction (β' 1) (φ 1) x).re] =
          [(rotateMotion t).actFn fun x => (productFunction (β 0) (φ 0) x).re,
            (rotateMotion t).actFn fun x => (productFunction (β 1) (φ 1) x).re] := by
        rw [hturn 0, hturn 1]
      rw [hval, hval']
      exact congrArg (fun r : ℝ => (r : ℂ)) ((congrArg _ e).trans (hinv _ _ hsep))
    have hint : productWeightedIntegral O α (fun z => G' z - G z) =
        profileIntegral β G' - profileIntegral β G := by
      have hβcont : ∀ i, Continuous (β i) := fun i => (hβc i).continuous
      have hcs' : ∀ i, HasCompactSupport (β i) := fun i => (hβ i).2
      unfold productWeightedIntegral profileIntegral
      rw [← integral_sub (integrable_profileIntegrand hβcont hcs' (hG'c.mono hC))
        (integrable_profileIntegrand hβcont hcs' (hGc.mono hC))]
      congr 1
      funext z
      unfold profileIntegrand
      by_cases hz : z ∈ Set.univ.pi fun i => tsupport (β i)
      · rw [Set.indicator_of_mem (hC hz), Set.indicator_of_mem hz, Set.indicator_of_mem hz,
          mul_sub]
      · have hzero : (∏ a, ((α a (z a) : ℝ) : ℂ)) = 0 := by
          obtain ⟨i, hi⟩ : ∃ i, z i ∉ tsupport (β i) := by
            by_contra hall
            exact hz fun i _ => not_not.1 (not_exists.1 hall i)
          have hbi : β i (z i) = 0 := image_eq_zero_of_notMem_tsupport hi
          exact Finset.prod_eq_zero (Finset.mem_univ i) hbi
        rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, sub_zero]
        simp [Set.indicator, hzero]
    have e1 : profileIntegral β G = centeredFnAtProducts S β φ :=
      (hK.integral_eq β hβ hT0).symm
    have e2 : profileIntegral β G' = centeredFnAtProducts S β' φ := by
      rw [hK.integral_eq β' hβ' hT1]
      exact (profileIntegral_comp_rotate t β G).symm
    rw [hint, e1, e2, hσ, sub_self]
  have h0 := (hDensity 2 (by norm_num) O (isOpen_rotationOrderedPairs t) _
    (hG'c.sub hGc)).1 hvan y hy
  exact sub_eq_zero.1 h0
theorem mem_rotationOrderedPairs_of_mem_pencilSet {φ₀ : openingAngles} {y : Fin 2 → RealPlane}
    (hy : y ∈ pencilSet φ₀ 2) {t : ℝ} (ht : |t| < Real.pi / 2 - (φ₀ : ℝ)) :
    y ∈ rotationOrderedPairs t := by
  obtain ⟨hv, harg⟩ : y 1 - y 0 ∈ coneSector φ₀ := hy 0
  set v := y 1 - y 0 with hvdef
  set w := lightConePlus (embedPlane v) with hwdef
  have hre : w.re = v 0 := by simp [hwdef, lightConePlus, embedPlane]
  have him : w.im = v 1 := by simp [hwdef, lightConePlus, embedPlane]
  have hw : w ≠ 0 := fun h0 => hv (by
    ext i
    fin_cases i
    · simpa [h0] using hre.symm
    · simpa [h0] using him.symm)
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hc := Complex.norm_mul_cos_arg w
  have hs := Complex.norm_mul_sin_arg w
  have hφ := φ₀.2
  obtain ⟨a1, a2⟩ := abs_lt.1 harg
  obtain ⟨b1, b2⟩ := abs_lt.1 ht
  have hφ1 : (φ₀ : ℝ) < Real.pi / 4 := hφ.2
  have p1 : 0 < Real.cos (Complex.arg w) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have p2 : 0 < Real.cos (Complex.arg w + t) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hv0 : 0 < v 0 := by
    rw [← hre, ← hc]
    exact mul_pos hn p1
  have hrot : 0 < v 0 * Real.cos t - v 1 * Real.sin t := by
    rw [← hre, ← him, ← hc, ← hs]
    have : ‖w‖ * Real.cos (Complex.arg w) * Real.cos t -
        ‖w‖ * Real.sin (Complex.arg w) * Real.sin t = ‖w‖ * Real.cos (Complex.arg w + t) := by
      rw [Real.cos_add]
      ring
    rw [this]
    exact mul_pos hn p2
  have e0 : v 0 = y 1 0 - y 0 0 := by simp [hvdef]
  have e1 : v 1 = y 1 1 - y 0 1 := by simp [hvdef]
  refine ⟨by linarith, ?_⟩
  simp only [RealPlane.rotate]
  rw [e0, e1] at hrot
  simp
  nlinarith [hrot]
theorem differentiable_of_entire {a : ℂ → ℂ} (ha : ForwardTube.Entire a) : Differentiable ℂ a := by apply _root_.YangMills.Construction.TwoPoints.HarmonicCountFromGrowth.differentiable_of_isHolomorphicVia <;> assumption
theorem eq_const_of_eq_near_zero {a : ℂ → ℂ} (ha : Differentiable ℂ a) {r : ℝ} (hr : 0 < r)
    (h : ∀ t : ℝ, |t| < r → a (t : ℂ) = a 0) (z : ℂ) : a z = a 0 := by
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), a w = (fun _ : ℂ => a 0) w := by
    have ht : Tendsto (fun n : ℕ => (((r / 2 * (1 / ((n : ℝ) + 1)) : ℝ)) : ℂ)) atTop
        (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h' := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (r / 2)
        rw [mul_zero] at h'
        have := (Complex.continuous_ofReal.tendsto 0).comp h'
        simpa [Function.comp_def] using this
      · have : (0 : ℝ) < r / 2 * (1 / ((n : ℝ) + 1)) := by positivity
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact_mod_cast this.ne'
    refine ht.frequently (Frequently.of_forall fun n => h _ ?_)
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [abs_of_pos (by positivity)]
    nlinarith
  have hU := (ha.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_frequently_eq
    ((differentiable_const (a 0)).differentiableOn.analyticOnNhd isOpen_univ)
    isPreconnected_univ (Set.mem_univ 0) hfreq
  exact hU (Set.mem_univ z)
theorem harmonic_eq_zero_of_const {a : ℂ → ℂ} {c : ℂ} (h : ∀ t : ℝ, a (t : ℂ) = c) {ν : ℤ}
    (hν : ν ≠ 0) :
    ((2 / Real.pi : ℝ) : ℂ) * ∫ t : ℝ in (0 : ℝ)..(Real.pi / 2),
      a (t : ℂ) * Complex.exp (-(4 * I * (ν : ℂ) * (t : ℂ))) = 0 := by
  have hk : -(4 * I * (ν : ℂ)) ≠ 0 := by
    simp [hν, Complex.I_ne_zero]
  have he : Complex.exp (-(4 * I * (ν : ℂ)) * ((Real.pi / 2 : ℝ) : ℂ)) = 1 := by
    have e : -(4 * I * (ν : ℂ)) * ((Real.pi / 2 : ℝ) : ℂ) =
        ((-ν : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast
      ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
  have hi : ∫ t : ℝ in (0 : ℝ)..(Real.pi / 2),
      a (t : ℂ) * Complex.exp (-(4 * I * (ν : ℂ) * (t : ℂ))) =
      c * ∫ t : ℝ in (0 : ℝ)..(Real.pi / 2), Complex.exp (-(4 * I * (ν : ℂ)) * (t : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    rw [h t]
    congr 2
    ring
  rw [hi, integral_exp_mul_complex hk, he]
  simp
theorem holds (hSetting : PlaneDataAsStandingData.ExistsStandingAndApertureData)
    (hAngle : AngleFunctionOnPencil.Holds)
    (hKernels : PlaneKernelProps.Holds)
    (hMoments : OrthogonalInvariance.OrthogonalMapStatement)
    (hMotions : ProductMotions.MotionFacts)
    (hDensity : RealPlane.DensityUniqueness.Claim) : TwoPointTopFrequency.Holds := by
  intro m S data φ₀ hnear
  obtain ⟨t₀, ht₀, hinv⟩ := hnear
  obtain ⟨e, -, rfl⟩ := (hSetting m S data).2 φ₀
  have hharm : ∀ y ∈ pencilSet e.angle (1 + 1), ∀ (φ : Fin (1 + 1) → realLabels) (ν : ℤ),
      ν ≠ 0 → angleHarmonic S e.angle y φ ν = 0 := by
    intro y hy φ ν hν
    have hKer := (hKernels m S e 1 le_rfl φ).1
    obtain ⟨-, hfun, -, hvals, -, -⟩ := hAngle m S e 1 le_rfl y hy φ
    have hd := differentiable_of_entire hfun.entire
    have hφ : (e.angle : ℝ) < Real.pi / 4 := e.angle.2.2
    have hpos : 0 < Real.pi / 2 - (e.angle : ℝ) := by
      have := Real.pi_pos
      linarith
    have hr : 0 < min t₀ (Real.pi / 2 - (e.angle : ℝ)) := lt_min ht₀ hpos
    have hzero : mapPoints (RealPlane.rotate 0) y = y := by
      funext i
      ext j
      fin_cases j <;> simp [mapPoints, RealPlane.rotate]
    have hconst : ∀ t : ℝ, |t| < min t₀ (Real.pi / 2 - (e.angle : ℝ)) →
        angleFunction S e.angle y φ (t : ℂ) = angleFunction S e.angle y φ 0 := by
      intro t ht
      have ht1 := lt_of_lt_of_le ht (min_le_left _ _)
      have ht2 := lt_of_lt_of_le ht (min_le_right _ _)
      have h1 := (hvals.1 t ht2).1
      have h2 := (hvals.1 0 (by simpa using hpos)).1
      have hk := kernel_rotate_invariant data hMoments hMotions hDensity hKer (hinv t ht1)
        (mem_rotationOrderedPairs_of_mem_pencilSet hy ht2)
      rw [hzero] at h2
      rw [Complex.ofReal_zero] at h2
      rw [h1, h2]
      exact hk
    exact harmonic_eq_zero_of_const (fun t => eq_const_of_eq_near_zero hd hr hconst _) hν
  show (if 1 ≤ 1 then sSup (harmonicFrequencies S e.angle 1) else 0) = 0
  rw [if_pos le_rfl]
  have hset : harmonicFrequencies S e.angle 1 = {0} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨Or.inl rfl, ?_⟩
    rintro k (hk | ⟨ν, rfl, y, hy, φ, hne⟩)
    · exact hk
    · by_contra hc
      have hν : ν ≠ 0 := by
        rintro rfl
        simp at hc
      exact hne (hharm y hy φ ν hν)
  rw [hset, csSup_singleton]
end EuclideanFunctionals.TwoPointTopFrequency
end YangMills.Construction
end
