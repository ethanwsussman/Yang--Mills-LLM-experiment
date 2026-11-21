import YangMills.Construction.HilbertSpaces.CalculusOfAProjectionValuedMeasureWithBoundedFunctionsProof
import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusTheorem
import YangMills.Construction.SpectralTheory.MeasuresOnRealSpaceOfTheEarlierSettings
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction.SettingsComparison
open YangMills.Construction.BorelSpectral
open YangMills.Construction.SpectralTheorem (IsSpectralIntegralOf spectralIntegralOp)
open YangMills.Construction.BorelCalculus (IsBoundedFn)
open YangMills.Construction.SelfAdjointFunctions (FullSpace)
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {n : ℕ}
def coordsToEuclid (y : FullSpace n) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 y.1
theorem measurable_coordsToEuclid : Measurable (coordsToEuclid (n := n)) :=
  (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.comp measurable_subtype_coe
def euclidToCoords (x : EuclideanSpace ℝ (Fin n)) : FullSpace n := ⟨WithLp.ofLp x, mem_univ _⟩
theorem measurable_euclidToCoords : Measurable (euclidToCoords (n := n)) :=
  (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurable.subtype_mk
theorem euclidToCoords_coordsToEuclid (y : FullSpace n) :
    euclidToCoords (coordsToEuclid y) = y :=
  Subtype.ext rfl
def borelToEuclid (Δ : BorelSubsets (FullSpace n)) : EuclideanSpectral.BorelSubset n :=
  ⟨euclidToCoords ⁻¹' Δ.1, measurable_euclidToCoords Δ.2⟩
theorem euclideanToCoords_borelToEuclid (Δ : BorelSubsets (FullSpace n)) :
    euclideanToCoords (borelToEuclid Δ) = Δ := by
  refine Subtype.ext (Set.ext fun y => ?_)
  change euclidToCoords (coordsToEuclid y) ∈ Δ.1 ↔ y ∈ Δ.1
  rw [euclidToCoords_coordsToEuclid]
theorem inner_orthProj_self {p : K →ₗ[ℂ] K}
    (h : EuclideanSpectral.IsOrthProj p) (ψ : K) :
    ⟪ψ, p ψ⟫_ℂ = ((‖p ψ‖ ^ 2 : ℝ) : ℂ) := by
  have hi : p (p ψ) = p ψ := LinearMap.congr_fun h.idem ψ
  have h₁ : ⟪ψ, p ψ⟫_ℂ = ⟪p ψ, p ψ⟫_ℂ := by
    rw [h.symm, hi]
  rw [h₁, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
theorem norm_orthProj_apply_le {p : K →ₗ[ℂ] K}
    (h : EuclideanSpectral.IsOrthProj p) (ψ : K) : ‖p ψ‖ ≤ ‖ψ‖ := by apply _root_.YangMills.Construction.PVMCalculus.norm_orthProj_apply_le <;> assumption
theorem isProjFn_of_isOrthProj {p : K →ₗ[ℂ] K}
    (h : EuclideanSpectral.IsOrthProj p) : IsProjFn (⇑p) := by
  refine ⟨p.mkContinuous 1 fun ψ => by simpa using norm_orthProj_apply_le h ψ, rfl, ?_⟩
  change OperatorTransport.IsSelfAdjointCLM _ ∧ _
  refine ⟨fun φ ψ => (h.symm φ ψ).symm, ?_⟩
  ext ψ
  exact LinearMap.congr_fun h.idem ψ
variable [NeZero n]
theorem exists_projMeasure_of_isProjValued {E : BorelSubsets (FullSpace n) → K → K}
    (hE : IsProjValuedBorelMeasure E) :
    ∃ G : EuclideanSpectral.ProjMeasure K n,
      ∀ B, ⇑(G B) = E (euclideanToCoords B) := by
  have hex : ∀ B : EuclideanSpectral.BorelSubset n, ∃ T : K →L[ℂ] K,
      ⇑T = E (euclideanToCoords B) ∧ OperatorTransport.IsProjectionCLM T :=
    fun B => hE.proj _
  choose T hT hP using hex
  have hproj : ∀ B, EuclideanSpectral.IsOrthProj (T B : K →ₗ[ℂ] K) := fun B =>
    { idem := by
        ext ψ
        exact congrArg (fun S : K →L[ℂ] K => S ψ) (hP B).2
      symm := fun φ ψ => ((hP B).1 φ ψ).symm }
  refine ⟨{ toFun := fun B => (T B : K →ₗ[ℂ] K)
            isOrthProj := hproj
            univ_eq_id := ?_
            hasSum_diag := ?_ }, fun B => hT B⟩
  · have hw : euclideanToCoords (EuclideanSpectral.BorelSubset.univ n) =
        ⟨univ, MeasurableSet.univ⟩ := Subtype.ext (Set.ext fun y => by
          simp [euclideanToCoords, EuclideanSpectral.BorelSubset.univ])
    ext ψ
    have h₁ := congrFun (hT (EuclideanSpectral.BorelSubset.univ n)) ψ
    rw [hw, hE.apply_univ] at h₁
    exact h₁
  · intro ψ B hd
    have hU : SetFunctions.iUnionSets (fun k => euclideanToCoords (B k)) =
        euclideanToCoords (EuclideanSpectral.BorelSubset.unionSeq B) :=
      Subtype.ext (Set.ext fun y => by
        simp [euclideanToCoords, SetFunctions.iUnionSets,
          EuclideanSpectral.BorelSubset.unionSeq])
    have hd' : SetFunctions.PairwiseDisjointSeq (fun k => euclideanToCoords (B k)) :=
      fun k l hkl => (hd hkl).preimage coordsToEuclid
    have ht := hE.diag_countablyAdditive ψ (fun k => euclideanToCoords (B k)) hd'
    have hterm : ∀ C, ⟪ψ, E (euclideanToCoords C) ψ⟫_ℂ = ((‖T C ψ‖ ^ 2 : ℝ) : ℂ) := fun C => by
      rw [← hT C]
      exact inner_orthProj_self (hproj C) ψ
    simp only [hU, hterm] at ht
    have ht' : Tendsto (fun N => ∑ k ∈ Finset.range N, ‖T (B k) ψ‖ ^ 2) atTop
        (𝓝 (‖T (EuclideanSpectral.BorelSubset.unionSeq B) ψ‖ ^ 2)) := by
      have h₂ := (Complex.continuous_re.tendsto _).comp ht
      simpa [Function.comp_def, ← Complex.ofReal_pow] using h₂
    have hs := (hasSum_iff_tendsto_nat_of_nonneg (fun _ => by positivity) _).2 ht'
    have hc := Complex.hasSum_ofReal.mpr hs
    have he : ∀ C, EuclideanSpectral.diagValue
        (fun B => (T B : K →ₗ[ℂ] K)) ψ C = ((‖T C ψ‖ ^ 2 : ℝ) : ℂ) :=
      fun C => inner_orthProj_self (hproj C) ψ
    simp only [he]
    exact hc
theorem isProjValued_of_projMeasure
    (hFacts : EuclideanSpectral.ProjMeasureBasicFacts)
    {E : BorelSubsets (FullSpace n) → K → K}
    (G : EuclideanSpectral.ProjMeasure K n)
    (hG : ∀ B, ⇑(G B) = E (euclideanToCoords B)) : IsProjValuedBorelMeasure E := by
  have hE : ∀ Δ, E Δ = ⇑(G (borelToEuclid Δ)) := fun Δ => by
    rw [hG, euclideanToCoords_borelToEuclid]
  obtain ⟨-, -, -, -, ⟨-, -, hinter⟩, -, -⟩ := hFacts K n G
  refine ⟨fun Δ => ?_, ?_, fun Δ Δ' => ?_, fun ψ => ?_⟩
  · rw [hE]
    exact isProjFn_of_isOrthProj (G.isOrthProj _)
  · have hw : borelToEuclid (⟨univ, MeasurableSet.univ⟩ : BorelSubsets (FullSpace n)) =
        EuclideanSpectral.BorelSubset.univ n := Subtype.ext rfl
    rw [hE, hw]
    change ⇑(G.toFun _) = id
    rw [G.univ_eq_id]
    rfl
  · have he : borelToEuclid ⟨Δ.1 ∩ Δ'.1, Δ.2.inter Δ'.2⟩ =
        ⟨(borelToEuclid Δ).1 ∩ (borelToEuclid Δ').1,
          (borelToEuclid Δ).2.inter (borelToEuclid Δ').2⟩ :=
      Subtype.ext rfl
    rw [hE, hE Δ, hE Δ', he, ← hinter]
    rfl
  · intro A hA
    have hU : borelToEuclid (SetFunctions.iUnionSets A) =
        EuclideanSpectral.BorelSubset.unionSeq fun k => borelToEuclid (A k) :=
      Subtype.ext (by
        simp [borelToEuclid, SetFunctions.iUnionSets,
          EuclideanSpectral.BorelSubset.unionSeq])
    have h₁ := (G.hasSum_diag ψ (fun k => borelToEuclid (A k))
      fun k l hkl => (hA hkl).preimage euclidToCoords).tendsto_sum_nat
    simp only [hE, hU]
    exact h₁
section SameMeasure
variable {F : SpectralMeasure (FullSpace n) K}
  {G : EuclideanSpectral.ProjMeasure K n}
theorem diag_eq_measureReal (h : IsSameMeasure F G) (ψ : K)
    (B : EuclideanSpectral.BorelSubset n) :
    G.diag ψ B = (((F.diagMeasure ψ).real (euclideanToCoords B).1 : ℝ) : ℂ) := by
  have h₁ : G.diag ψ B = ⟪ψ, F (euclideanToCoords B) ψ⟫_ℂ :=
    congrArg (fun x => ⟪ψ, x⟫_ℂ) (congrFun (h B) ψ)
  rw [h₁, F.inner_apply_self_eq_diagMeasure]
theorem diagMeasure_eq_map
    (hFacts : EuclideanSpectral.ProjMeasureBasicFacts)
    (h : IsSameMeasure F G) (ψ : K) :
    G.diagMeasure ψ = (F.diagMeasure ψ).map coordsToEuclid := by
  obtain ⟨-, -, hm, -⟩ := hFacts K n G
  obtain ⟨⟨hfin, hval⟩, -, -⟩ := hm ψ
  refine Measure.ext fun S hS => ?_
  have h₁ := hval ⟨S, hS⟩
  rw [diag_eq_measureReal h] at h₁
  have h₂ : (F.diagMeasure ψ).real (coordsToEuclid ⁻¹' S) = (G.diagMeasure ψ).real S :=
    Complex.ofReal_injective h₁
  rw [Measure.map_apply measurable_coordsToEuclid hS]
  exact ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h₂).symm
theorem integralOp_eq_boundedIntegral
    (hFacts : EuclideanSpectral.ProjMeasureBasicFacts)
    (hCal : BorelCalculus.BorelCalculusTheorem)
    (h : IsSameMeasure F G) {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Measurable f)
    (hb : IsBoundedFn f) :
    (F.integralOp (liftToCoords f) : K →ₗ[ℂ] K) = G.boundedIntegral f := by
  obtain ⟨hB, -⟩ := (hCal K n).1 _ F
  have hg : Measurable (liftToCoords f) := hf.comp measurable_coordsToEuclid
  have hgb : IsBoundedFn (liftToCoords f) := by
    obtain ⟨c, hc⟩ := hb
    exact ⟨c, fun y => hc _⟩
  have hdiag : F.IsDiagonalIntegral (liftToCoords f) (F.integralOp (liftToCoords f)) :=
    Classical.epsilon_spec (hB.existsUnique_op _ hg hgb).exists
  obtain ⟨-, -, -, -, -, -, hint⟩ := hFacts K n G
  obtain ⟨⟨A, hA, huniq⟩, -⟩ := hint f hf hb
  have hGI : G.IsWeakIntegralOp f (G.boundedIntegral f) := Classical.epsilon_spec ⟨A, hA⟩
  have hw : G.IsWeakIntegralOp f (F.integralOp (liftToCoords f) : K →ₗ[ℂ] K) := fun ψ => by
    rw [diagMeasure_eq_map hFacts h ψ,
      integral_map measurable_coordsToEuclid.aemeasurable hf.aestronglyMeasurable]
    exact hdiag ψ
  exact (huniq _ hw).trans (huniq _ hGI).symm
end SameMeasure
omit [NeZero n] in
theorem spectralIntegralOp_eq_of {F : SpectralMeasure (FullSpace n) K} {g : FullSpace n → ℂ}
    {A : HilbertSpaceBasics.UnboundedOp K} (hA : IsSpectralIntegralOf A F g) :
    spectralIntegralOp F g = A := by
  have hs : IsSpectralIntegralOf (spectralIntegralOp F g) F g :=
    Classical.epsilon_spec (p := fun B => IsSpectralIntegralOf B F g) ⟨A, hA⟩
  refine LinearPMap.ext (Submodule.ext fun ψ => (hs.1 ψ).trans (hA.1 ψ).symm) fun x hx hy => ?_
  rw [hs.2 ⟨x, hx⟩, hA.2 ⟨x, hy⟩]
omit [NeZero n] in
theorem isSpectralIntegralOf_totalOp {F : SpectralMeasure (FullSpace n) K}
    {g : FullSpace n → ℂ} (hb : IsBoundedFn g) :
    IsSpectralIntegralOf (totalOp (F.integralOp g : K →ₗ[ℂ] K)) F g := by
  obtain ⟨c, hc⟩ := hb
  refine ⟨fun ψ => ?_, fun ψ => ?_⟩
  · rw [F.integralDom_eq_univ hc]
    simp [totalOp]
  · rw [F.integralApply_eq_integralOp hc]
    rfl
theorem mem_fnDomainSet_iff
    (hFacts : EuclideanSpectral.ProjMeasureBasicFacts)
    {F : SpectralMeasure (FullSpace n) K}
    {G : EuclideanSpectral.ProjMeasure K n} (h : IsSameMeasure F G)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Measurable f) (ψ : K) :
    ψ ∈ G.fnDomainSet f ↔ ψ ∈ F.integralDom (liftToCoords f) := by
  change ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(G.diagMeasure ψ) < ⊤ ↔
    ∫⁻ y, ‖liftToCoords f y‖ₑ ^ 2 ∂F.diagMeasure ψ < ∞
  rw [diagMeasure_eq_map hFacts h ψ,
    lintegral_map (hf.enorm.pow_const 2) measurable_coordsToEuclid]
  rfl
theorem isSpectralIntegralOf_borelFnOp
    (hFacts : EuclideanSpectral.ProjMeasureBasicFacts)
    (hEuclidean : EuclideanSpectral.ProjMeasureBoundedCalculus)
    (hCal : BorelCalculus.BorelCalculusTheorem)
    {F : SpectralMeasure (FullSpace n) K}
    {G : EuclideanSpectral.ProjMeasure K n} (h : IsSameMeasure F G)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Measurable f) :
    IsSpectralIntegralOf
      (⟨G.fnDomain f, G.borelFnOp f⟩ : HilbertSpaceBasics.UnboundedOp K)
      F (liftToCoords f) := by
  obtain ⟨-, -, -, -, -, -, hfun⟩ := hEuclidean K n G
  obtain ⟨hdom, hlim, -, -⟩ := hfun f hf
  obtain ⟨-, -, -, hU, -⟩ := (hCal K n).1 _ F
  have hg : Measurable (liftToCoords f) := hf.comp measurable_coordsToEuclid
  have hmem : ∀ ψ, ψ ∈ G.fnDomain f ↔ ψ ∈ F.integralDom (liftToCoords f) := fun ψ => by
    rw [← mem_fnDomainSet_iff hFacts h hf, ← hdom]
    rfl
  refine ⟨hmem, fun ψ => ?_⟩
  have h₁ := hU.tendsto_truncate _ hg ψ.1 ((hmem ψ.1).1 ψ.2)
  have h₂ := hlim ψ
  have hk : ∀ k : ℕ, F.integralOp (BorelSpectral.truncate (liftToCoords f) k) ψ.1 =
      G.truncIntegral f k ψ.1 := fun k => by
    have hm : Measurable ({x | ‖f x‖ ≤ (k : ℝ)}.indicator f) :=
      hf.indicator (measurableSet_le hf.norm measurable_const)
    have hb : IsBoundedFn ({x | ‖f x‖ ≤ (k : ℝ)}.indicator f) := by
      refine ⟨k, fun x => ?_⟩
      by_cases hx : x ∈ {x | ‖f x‖ ≤ (k : ℝ)}
      · rw [indicator_of_mem hx]
        exact hx
      · rw [indicator_of_notMem hx, norm_zero]
        exact Nat.cast_nonneg k
    have he : BorelSpectral.truncate (liftToCoords f) k =
        liftToCoords ({x | ‖f x‖ ≤ (k : ℝ)}.indicator f) := by
      funext y
      rfl
    rw [he]
    exact LinearMap.congr_fun (integralOp_eq_boundedIntegral hFacts hCal h hm hb) ψ.1
  simp only [hk] at h₁
  exact tendsto_nhds_unique h₂ ((tendsto_add_atTop_iff_nat 1).2 h₁)
theorem fullSpaceMeasuresAgreeForAllSpaces_holds
    (hFacts : EuclideanSpectral.ProjMeasureBasicFacts)
    (hEuclidean : EuclideanSpectral.ProjMeasureBoundedCalculus)
    (hCal : BorelCalculus.BorelCalculusTheorem) : FullSpaceMeasuresAgreeForAllSpaces := by
  intro K _ _ _ n _
  refine
    { isProjValued_iff := fun E => ⟨exists_projMeasure_of_isProjValued,
        fun ⟨G, hG⟩ => isProjValued_of_projMeasure hFacts G hG⟩
      diag_eq := fun F G h ψ B => diag_eq_measureReal h ψ B
      diagMeasure_eq := fun F G h ψ B => ?_
      supports_iff := fun F G h B => ?_
      integralOp_eq := fun F G h f hf hb => funext fun ψ =>
        LinearMap.congr_fun (integralOp_eq_boundedIntegral hFacts hCal h hf hb) ψ
      setIntegralOp_eq := fun F G h C f hf hc => ?_
      spectralIntegralOp_eq := fun F G h f hf =>
        spectralIntegralOp_eq_of (isSpectralIntegralOf_borelFnOp hFacts hEuclidean hCal h hf) }
  · rw [diagMeasure_eq_map hFacts h ψ, Measure.map_apply measurable_coordsToEuclid B.2]
    rfl
  · have hc : (⟨(euclideanToCoords B).1ᶜ, (euclideanToCoords B).2.compl⟩ :
          BorelSubsets (FullSpace n)) =
        euclideanToCoords B.compl := Subtype.ext (Set.ext fun y => by
          simp [euclideanToCoords, EuclideanSpectral.BorelSubset.compl])
    have h₁ := h B.compl
    constructor
    · intro h₀
      change G B.compl = 0 at h₀
      change F _ = 0
      rw [hc]
      ext ψ
      have h₂ := congrFun h₁ ψ
      rw [h₀] at h₂
      simpa using h₂.symm
    · intro h₀
      change F _ = 0 at h₀
      rw [hc] at h₀
      change G B.compl = 0
      ext ψ
      have h₂ := congrFun h₁ ψ
      rw [h₀] at h₂
      simpa using h₂
  · obtain ⟨c, hc⟩ := hc
    have hm : Measurable (C.1.indicator f) := hf.indicator C.2
    have hb : IsBoundedFn (C.1.indicator f) := by
      refine ⟨max c 0, fun x => ?_⟩
      by_cases hx : x ∈ C.1
      · rw [indicator_of_mem hx]
        exact (hc x hx).trans (le_max_left _ _)
      · rw [indicator_of_notMem hx, norm_zero]
        exact le_max_right _ _
    have hb' : IsBoundedFn (liftToCoords (C.1.indicator f)) := by
      obtain ⟨c', hc'⟩ := hb
      exact ⟨c', fun y => hc' _⟩
    have he : BorelSpectral.zeroExtend (euclideanToCoords C).1
        (fun y => liftToCoords f y.1) = liftToCoords (C.1.indicator f) := by
      funext y
      by_cases hy : y ∈ (euclideanToCoords C).1
      · simp only [BorelSpectral.zeroExtend, dif_pos hy]
        exact (indicator_of_mem (show coordsToEuclid y ∈ C.1 from hy) f).symm
      · simp only [BorelSpectral.zeroExtend, dif_neg hy]
        exact (indicator_of_notMem (show coordsToEuclid y ∉ C.1 from hy) f).symm
    change spectralIntegralOp F
      (BorelSpectral.zeroExtend (euclideanToCoords C).1 fun y => liftToCoords f y.1) = _
    rw [he, spectralIntegralOp_eq_of (isSpectralIntegralOf_totalOp hb'),
      integralOp_eq_boundedIntegral hFacts hCal h hm hb]
    rfl
end YangMills.Construction.SettingsComparison
