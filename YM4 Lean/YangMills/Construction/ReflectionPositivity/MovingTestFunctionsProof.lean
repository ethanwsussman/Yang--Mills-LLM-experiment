import YangMills.Construction.ReflectionPositiveLimits.MovingTestFunctionsProof
import YangMills.Construction.QuaternionicWilsonModel.TheDefaultCasesAreUnusedProof
import YangMills.Construction.ReflectionPositivity.ContinuityOfTheLimitOfABoundedLatticeApproximationProof
import Mathlib
set_option autoImplicit false
open Filter Function Metric Set Topology
open scoped Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.MovingTests
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Mirrors (ReflectingHyperplane)
open YangMills.Construction.TestFunctions (partialDerivR4 c1NormR4 uniformNorm IsC1R4)
open YangMills.Construction.SeparatedTuples
private def translateFn (u : AmbientSpace) (g : RealValued) : RealValued := fun x => g (x - u)
private theorem translateFn_zero (g : RealValued) : translateFn 0 g = g := by
  funext x
  simp [translateFn]
private theorem translateFn_translateFn (a b : AmbientSpace) (g : RealValued) :
    translateFn a g = translateFn (a - b) (translateFn b g) := by apply _root_.YangMills.DeltaSharedProofs.p501722 <;> assumption
private theorem tsupport_translateFn_subset {u : AmbientSpace} {δ : ℝ} (g : RealValued)
    (hu : ‖u‖ ≤ δ) : tsupport (translateFn u g) ⊆ cthickening δ (tsupport g) := by apply _root_.YangMills.DeltaSharedProofs.p502471 <;> assumption
private theorem hasDerivAt_line {g : RealValued} (hg : IsC1R4 g) (μ : Fin 4) (x : AmbientSpace) :
    HasDerivAt (fun t : ℝ => g (x + t • (Pi.single μ (1 : ℝ) : AmbientSpace)))
      (fderiv ℝ g x (Pi.single μ 1)) 0 := by apply _root_.YangMills.SharedProofs.p48546 <;> assumption
private theorem partialDerivR4_translateFn_sub {g : RealValued} (hg : IsC1R4 g) (μ : Fin 4)
    (u x : AmbientSpace) :
    partialDerivR4 μ (translateFn u g - g) x =
      fderiv ℝ g (x - u) (Pi.single μ 1) - fderiv ℝ g x (Pi.single μ 1) := by apply _root_.YangMills.DeltaSharedProofs.p502281 <;> assumption
private theorem tendsto_c1NormR4 {g : RealValued} (hg : IsC1R4 g)
    (hs : HasCompactSupport g) :
    Tendsto (fun u : AmbientSpace => c1NormR4 (translateFn u g - g)) (𝓝 0) (𝓝 0) := by apply _root_.YangMills.DeltaSharedProofs.p502201 <;> assumption
private theorem tendstoAdmissibly_of_translates (G : SepTuple) (s : ℕ → SepTuple)
    (u : ℕ → ℕ → AmbientSpace)
    (hu : ∀ i, Tendsto (u i) atTop (𝓝 0)) (r₂ : ℕ) (hr₂ : 1 ≤ r₂)
    (hlen : ∀ r, r₂ ≤ r → (s r).size = G.size)
    (hs : ∀ r, r₂ ≤ r → ∀ i, i < G.size → (s r).componentAt i = translateFn (u i r) (G.componentAt i)) :
    ∃ r₀, r₂ ≤ r₀ ∧ TendstoAdmissibly r₀ s G := by
  have hget : ∀ i : Fin G.size, G.componentAt i = G.1[(i : ℕ)]'i.2 := fun i =>
    List.getD_eq_getElem _ _ i.2
  have hC : ∀ i : Fin G.size, IsC1c (G.componentAt i) := fun i => by
    rw [hget i]
    exact G.2.1 _ (List.getElem_mem i.2)
  have hlt : ∀ i j : Fin G.size, i < j →
      Disjoint (tsupport (G.componentAt i)) (tsupport (G.componentAt j)) := fun i j hij => by
    rw [hget i, hget j]
    exact List.pairwise_iff_getElem.1 G.2.2 i j i.2 j.2 hij
  have hdisj : ∀ i j : Fin G.size, i ≠ j →
      Disjoint (tsupport (G.componentAt i)) (tsupport (G.componentAt j)) := fun i j hij => by
    rcases lt_or_gt_of_ne hij with h | h
    · exact hlt i j h
    · exact (hlt j i h).symm
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i j : Fin G.size, i ≠ j →
      Disjoint (cthickening δ (tsupport (G.componentAt i))) (cthickening δ (tsupport (G.componentAt j))) := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    · obtain ⟨d, hd, H⟩ := (hdisj i j hij).exists_cthickenings (hC i).2.isCompact
        (isClosed_tsupport _)
      filter_upwards [Ioo_mem_nhdsGT hd] with δ hδ _
      exact H.mono (cthickening_mono hδ.2.le _) (cthickening_mono hδ.2.le _)
  obtain ⟨δ, hδ, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hsmall : ∀ᶠ r in atTop, ∀ i : Fin G.size, ‖u i r‖ ≤ δ :=
    eventually_all.2 fun i => (hu i).eventually
      (Metric.eventually_nhds_iff.2 ⟨δ, hδ0, fun {y} hy => by
        have : ‖y‖ < δ := by simpa using hy
        exact this.le⟩)
  obtain ⟨R, hR⟩ := eventually_atTop.1 hsmall
  refine ⟨max r₂ R, le_max_left _ _, hr₂.trans (le_max_left _ _),
    fun r hr => hlen r ((le_max_left _ _).trans hr),
    fun i => cthickening δ (tsupport (G.componentAt i)), fun i => (hC i).2.isCompact.cthickening,
    fun i j hij => hδ i j hij, fun r hr i => ?_, fun i => ?_⟩
  · rw [hs r ((le_max_left _ _).trans hr) i i.2]
    exact union_subset (tsupport_translateFn_subset _ (hR r ((le_max_right _ _).trans hr) i))
      (self_subset_cthickening _)
  · refine ((tendsto_c1NormR4 (hC i).1 (hC i).2).comp (hu i)).congr' ?_
    filter_upwards [eventually_ge_atTop r₂] with r hr
    simp only [comp_apply]
    rw [hs r hr i i.2]
private theorem getD_map_translateFn (L : List RealValued) (a : AmbientSpace) (i : ℕ) :
    (L.map (translateFn a)).getD i 0 = translateFn a (L.getD i 0) := by apply _root_.YangMills.DeltaSharedProofs.p502215 <;> assumption
private theorem getD_append_map_translateFn (Y L : List RealValued) (a b : AmbientSpace) (i : ℕ) :
    (Y ++ L.map (translateFn a)).getD i 0 =
      translateFn (if i < Y.length then 0 else a - b) ((Y ++ L.map (translateFn b)).getD i 0) := by apply _root_.YangMills.DeltaSharedProofs.p502597 <;> assumption
private theorem getD_map_translateFn_append (Y L : List RealValued) (a b : AmbientSpace) (i : ℕ) :
    (L.map (translateFn a) ++ Y).getD i 0 =
      translateFn (if i < L.length then a - b else 0) ((L.map (translateFn b) ++ Y).getD i 0) := by apply _root_.YangMills.DeltaSharedProofs.p97 <;> assumption
private theorem push_translate_val (hF : BasicFacts.MainFacts) (v : AmbientSpace) (X : SepTuple) :
    (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v) X).1 = X.1.map (translateFn v) := by
  have h := (hF.1 (_root_.YangMills.Construction.SeparatedTuples.translate v) (isEuclidIsometry_translate v) X X).1
  unfold _root_.YangMills.Construction.SeparatedTuples.push
  rw [dif_pos h]
  exact pushList_translate v X.1
private theorem composable_symm {X Y : SepTuple} (h : SepTuple.Composable X Y) :
    SepTuple.Composable Y X :=
  fun f hf g hg => (h g hg f hf).symm
private theorem eventually_composable (hF : BasicFacts.MainFacts) (X Y : SepTuple)
    {w : ℕ → AmbientSpace} {v : AmbientSpace}
    (hw : Tendsto (fun r => w r - v) atTop (𝓝 0))
    (hY : SepTuple.Composable Y (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v) X)) :
    ∀ᶠ r in atTop, SepTuple.Composable Y (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate (w r)) X) := by
  have hall : ∀ᶠ r in atTop, ∀ f ∈ {f | f ∈ Y.1}, ∀ h ∈ {h | h ∈ X.1},
      Disjoint (tsupport f) (tsupport (translateFn (w r) h)) := by
    refine (eventually_all_finite (List.finite_toSet Y.1)).2 fun f hf =>
      (eventually_all_finite (List.finite_toSet X.1)).2 fun h hh => ?_
    have hd : Disjoint (tsupport (translateFn v h)) (tsupport f) := by
      refine (hY f hf (translateFn v h) ?_).symm
      rw [push_translate_val hF]
      exact List.mem_map_of_mem hh
    have hk : IsCompact (tsupport (translateFn v h)) := by
      have : translateFn v h ∈ (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v) X).1 := by
        rw [push_translate_val hF]
        exact List.mem_map_of_mem hh
      exact ((_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v) X).2.1 _ this).2.isCompact
    obtain ⟨d, hd0, H⟩ := hd.exists_cthickenings hk (isClosed_tsupport _)
    have hsmall : ∀ᶠ r in atTop, ‖w r - v‖ ≤ d := hw.eventually
      (Metric.eventually_nhds_iff.2 ⟨d, hd0, fun {y} hy => by
        have : ‖y‖ < d := by simpa using hy
        exact this.le⟩)
    filter_upwards [hsmall] with r hr
    rw [translateFn_translateFn (w r) v h]
    exact (H.mono (tsupport_translateFn_subset _ hr) (self_subset_cthickening _)).symm
  filter_upwards [hall] with r hr f hf g hg
  rw [push_translate_val hF] at hg
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hg
  exact hr f hf h hh
private theorem tendstoAdmissibly_mono {r₀ r' : ℕ} {s : ℕ → SepTuple} {X : SepTuple}
    (hr : r₀ ≤ r') (h : TendstoAdmissibly r₀ s X) : TendstoAdmissibly r' s X := by
  obtain ⟨h1, hlen, A, hA, hd, hsup, hn⟩ := h
  exact ⟨h1.trans hr, fun r hr' => hlen r (hr.trans hr'), A, hA, hd,
    fun r hr' => hsup r (hr.trans hr'), hn⟩
private theorem tendsto_ite_zero_then {w : ℕ → AmbientSpace} (hw : Tendsto w atTop (𝓝 0))
    (p : Prop) [Decidable p] : Tendsto (fun r => if p then 0 else w r) atTop (𝓝 0) := by apply _root_.YangMills.DeltaSharedProofs.p500968 <;> assumption
private theorem tendsto_ite_zero_else {w : ℕ → AmbientSpace} (hw : Tendsto w atTop (𝓝 0))
    (p : Prop) [Decidable p] : Tendsto (fun r => if p then w r else 0) atTop (𝓝 0) := by apply _root_.YangMills.DeltaSharedProofs.p502399 <;> assumption
private theorem translates_tendsto (hF : BasicFacts.MainFacts) : TranslatesTendsto := by
  intro r₁ hr₁ X w v hw
  have hu : Tendsto (fun r => w r - v) atTop (𝓝 0) := by simpa using hw.sub_const v
  refine ⟨?_, fun Y hY => ?_⟩
  · exact tendstoAdmissibly_of_translates (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v) X)
      (fun r => _root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate (w r)) X) (fun _ r => w r - v) (fun _ => hu) r₁ hr₁
      (fun r _ => by simp [SepTuple.size, push_translate_val hF])
      (fun r _ i _ => by
        simp only [SepTuple.componentAt]
        rw [push_translate_val hF, push_translate_val hF, getD_map_translateFn,
          getD_map_translateFn, ← translateFn_translateFn])
  · obtain ⟨R, hR⟩ := eventually_atTop.1 (eventually_composable hF X Y hu hY)
    have hYs := composable_symm hY
    have hr₂ : 1 ≤ max r₁ R := hr₁.trans (le_max_left _ _)
    have hd1 : ∀ r, max r₁ R ≤ r → SepTuple.Composable Y (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate (w r)) X) :=
      fun r hr => hR r ((le_max_right _ _).trans hr)
    have hd2 : ∀ r, max r₁ R ≤ r → SepTuple.Composable (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate (w r)) X) Y :=
      fun r hr => composable_symm (hd1 r hr)
    have hv1 : ∀ r, max r₁ R ≤ r → (SepTuple.juxt Y (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate (w r)) X)).1 =
        Y.1 ++ X.1.map (translateFn (w r)) := fun r hr => by
      rw [SepTuple.juxt_val (hd1 r hr), push_translate_val hF]
    have hv2 : ∀ r, max r₁ R ≤ r → (SepTuple.juxt (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate (w r)) X) Y).1 =
        X.1.map (translateFn (w r)) ++ Y.1 := fun r hr => by
      rw [SepTuple.juxt_val (hd2 r hr), push_translate_val hF]
    have hg1 : (SepTuple.juxt Y (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v) X)).1 = Y.1 ++ X.1.map (translateFn v) := by
      rw [SepTuple.juxt_val hY, push_translate_val hF]
    have hg2 : (SepTuple.juxt (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v) X) Y).1 = X.1.map (translateFn v) ++ Y.1 := by
      rw [SepTuple.juxt_val hYs, push_translate_val hF]
    obtain ⟨ra, hra, ca⟩ := tendstoAdmissibly_of_translates (SepTuple.juxt Y (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v) X))
      (fun r => SepTuple.juxt Y (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate (w r)) X))
      (fun i r => if i < Y.1.length then 0 else w r - v) (fun i => tendsto_ite_zero_then hu _)
      (max r₁ R) hr₂
      (fun r hr => by simp [SepTuple.size, hv1 r hr, hg1])
      (fun r hr i _ => by
        simp only [SepTuple.componentAt]
        rw [hv1 r hr, hg1]
        exact getD_append_map_translateFn _ _ _ _ _)
    obtain ⟨rb, hrb, cb⟩ := tendstoAdmissibly_of_translates (SepTuple.juxt (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate v) X) Y)
      (fun r => SepTuple.juxt (_root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate (w r)) X) Y)
      (fun i r => if i < X.1.length then w r - v else 0) (fun i => tendsto_ite_zero_else hu _)
      (max r₁ R) hr₂
      (fun r hr => by simp [SepTuple.size, hv2 r hr, hg2])
      (fun r hr i _ => by
        simp only [SepTuple.componentAt]
        rw [hv2 r hr, hg2]
        exact getD_map_translateFn_append _ _ _ _ _)
    exact ⟨max ra rb, (le_max_left _ _).trans (hra.trans (le_max_left _ _)),
      fun r hr => hd1 r (hra.trans ((le_max_left _ _).trans hr)),
      tendstoAdmissibly_mono (le_max_left _ _) ca,
      fun r hr => hd2 r (hra.trans ((le_max_left _ _).trans hr)),
      tendstoAdmissibly_mono (le_max_right _ _) cb⟩
private theorem isEuclidIsometry_reflect (hm : Mirrors.UnitNormalAndLattice.Statement)
    (P : ReflectingHyperplane) : IsEuclidIsometry P.reflect := by apply _root_.YangMills.Construction.ConditionDefaults.isEuclidIsometry_reflect <;> assumption
private theorem reflect_reflect (hm : Mirrors.UnitNormalAndLattice.Statement)
    (P : ReflectingHyperplane) (x : AmbientSpace) : P.reflect (P.reflect x) = x := by
  obtain ⟨-, -, -, ⟨-, hinv, -, -⟩, -⟩ := hm P 1 one_pos
  exact congrFun hinv x
private theorem invMap_reflect (hm : Mirrors.UnitNormalAndLattice.Statement)
    (P : ReflectingHyperplane) : invMap P.reflect = P.reflect := by
  have hinj : Injective P.reflect :=
    LeftInverse.injective (g := P.reflect) (reflect_reflect hm P)
  funext y
  calc invMap P.reflect y
      = invMap P.reflect (P.reflect (P.reflect y)) := by
        rw [reflect_reflect hm P y]
    _ = P.reflect y := leftInverse_invFun hinj _
private theorem push_reflect_val (hF : BasicFacts.MainFacts)
    (hm : Mirrors.UnitNormalAndLattice.Statement) (P : ReflectingHyperplane) (X : SepTuple) :
    (_root_.YangMills.Construction.SeparatedTuples.push P.reflect X).1 = X.1.map fun f => f ∘ P.reflect := by
  have h := (hF.1 P.reflect (isEuclidIsometry_reflect hm P) X X).1
  unfold _root_.YangMills.Construction.SeparatedTuples.push
  rw [dif_pos h]
  simp only [pushList, invMap_reflect hm P]
private theorem continuous_reflect (P : ReflectingHyperplane) : Continuous P.reflect := by
  unfold ReflectingHyperplane.reflect
  fun_prop
private theorem push_parallelHyperplane_reflect (hF : BasicFacts.MainFacts)
    (hm : Mirrors.UnitNormalAndLattice.Statement) (M : ReflectingHyperplane) (c' : ℝ)
    (X : SepTuple) :
    _root_.YangMills.Construction.SeparatedTuples.push (parallelHyperplane M c').reflect X =
      _root_.YangMills.Construction.SeparatedTuples.push (_root_.YangMills.Construction.SeparatedTuples.translate ((2 * (c' - M.offset) * (M.normalNorm ^ 2)⁻¹) • M.normalVec))
        (_root_.YangMills.Construction.SeparatedTuples.push M.reflect X) := by
  set P := parallelHyperplane M c' with hP
  set b : AmbientSpace := (2 * (c' - M.offset) * (M.normalNorm ^ 2)⁻¹) • M.normalVec with hb
  have hform : ∀ y, P.reflect y = M.reflect y + b := by
    obtain ⟨-, -, -, -, he⟩ := hm P 1 one_pos
    exact fun y => he M.offset y
  have hpt : ∀ x, M.reflect (x - b) = P.reflect x := fun x => by
    have h1 := hform (P.reflect x)
    rw [reflect_reflect hm P x] at h1
    rw [sub_eq_of_eq_add h1, reflect_reflect hm M]
  refine Subtype.ext ?_
  rw [push_reflect_val hF hm, push_translate_val hF, push_reflect_val hF hm, List.map_map]
  refine List.map_congr_left fun f _ => ?_
  funext x
  simp only [comp_apply, translateFn, hpt]
private theorem reflections_tendsto (hF : BasicFacts.MainFacts)
    (hm : Mirrors.UnitNormalAndLattice.Statement) : ReflectionsTendsto := by
  intro r₁ hr₁ M X₁ X₂ h₁ h₂ c hc hlim
  have hb : Tendsto (fun r => (2 * (c r - M.offset) * (M.normalNorm ^ 2)⁻¹) • M.normalVec) atTop
      (𝓝 0) := by
    have h : Tendsto (fun r => 2 * (c r - M.offset) * (M.normalNorm ^ 2)⁻¹) atTop (𝓝 0) := by
      simpa using ((hlim.sub_const M.offset).const_mul 2).mul_const (M.normalNorm ^ 2)⁻¹
    simpa using h.smul_const M.normalVec
  have hθ := (hF.2.2.1 M X₁ X₂ h₁ h₂).2
  have hZ0 : _root_.YangMills.Construction.SeparatedTuples.push (SeparatedTuples.translate 0) (_root_.YangMills.Construction.SeparatedTuples.push M.reflect X₁) = _root_.YangMills.Construction.SeparatedTuples.push M.reflect X₁ := by
    refine Subtype.ext ?_
    rw [push_translate_val hF]
    simp [show translateFn 0 = id from funext translateFn_zero]
  refine ⟨fun r hr f hf h hh => ?_, ?_⟩
  · rw [push_reflect_val hF hm] at hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    rw [Set.disjoint_left]
    intro x hx hxh
    have hx' : (parallelHyperplane M (c r)).reflect x ∈ tsupport g :=
      tsupport_comp_subset_preimage g (continuous_reflect _) hx
    have a1 : M.normalVec ⬝ᵥ (parallelHyperplane M (c r)).reflect x > M.offset := h₁ g hg hx'
    have a2 : M.normalVec ⬝ᵥ x > M.offset := h₂ h hh hxh
    obtain ⟨-, -, -, ⟨hd, -, -, -⟩, -⟩ := hm (parallelHyperplane M (c r)) 1 one_pos
    have a3 : M.normalVec ⬝ᵥ (parallelHyperplane M (c r)).reflect x - c r =
        -(M.normalVec ⬝ᵥ x - c r) :=
      hd x
    have a4 := hc r hr
    linarith
  · obtain ⟨r₀, h0, -, -, -, hcv⟩ := (translates_tendsto hF r₁ hr₁ (_root_.YangMills.Construction.SeparatedTuples.push M.reflect X₁) _ 0 hb).2 X₂
      (by rw [hZ0]; exact composable_symm hθ)
    refine ⟨r₀, h0, ?_⟩
    simp only [push_parallelHyperplane_reflect hF hm]
    rw [hZ0] at hcv
    exact hcv
theorem statement_holds (hF : BasicFacts.MainFacts)
    (hm : Mirrors.UnitNormalAndLattice.Statement) : Statement :=
  ⟨translates_tendsto hF, reflections_tendsto hF hm⟩
end YangMills.Construction.ReflectionPositivity.MovingTests
