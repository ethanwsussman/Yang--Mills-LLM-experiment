import YangMills.Construction.ReflectionPositivity.FactsOnSeparatedTuplesOfFourSpaceProof
import YangMills.Construction.ReflectionPositivity.SeparatedTuples
import YangMills.Construction.ReflectionPositiveLimits.LimitsOfLatticeStatesProof
import Mathlib
set_option autoImplicit false
open Filter Function Metric Set Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.MovingTestFunctions
open YangMills.Construction.ReflectionPositivity.EuclidIsometry
open YangMills.Construction.TestFunctions (partialDerivR4 c1NormR4 uniformNorm IsC1R4)
open YangMills.Construction.TorusMetric (euclidNormVec)
private theorem euclidIsometry_ext {r r' : EuclidIsometry} (h : r.toFun = r'.toFun) : r = r' := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeLimits.euclidIsometry_ext <;> assumption
private theorem symm_comp_apply (r r' : EuclidIsometry) (x : Space) :
    (r.comp r').symm.toFun x = r'.symm.toFun (r.symm.toFun x) := by
  apply (r.comp r').bijective_toFun.1
  rw [toFun_symm]
  change x = r.toFun (r'.toFun (r'.symm.toFun (r.symm.toFun x)))
  rw [toFun_symm, toFun_symm]
private theorem push_comp (r r' : EuclidIsometry) (X : Tuple) :
    push (r.comp r') X = push r (push r' X) := by
  refine Subtype.ext ?_
  change X.1.map (pushFn (r.comp r')) = (X.1.map (pushFn r')).map (pushFn r)
  rw [List.map_map]
  refine List.map_congr_left fun f _ => ?_
  funext x
  simp only [pushFn, comp_apply, symm_comp_apply]
private theorem tsupport_pushFn_eq_image (r : EuclidIsometry) (f : ScalarField) :
    tsupport (pushFn r f) = r.toFun '' tsupport f := by
  rw [tsupport_pushFn]
  ext y
  constructor
  · intro h
    exact ⟨r.symm.toFun y, h, toFun_symm r y⟩
  · rintro ⟨x, hx, rfl⟩
    change r.symm.toFun (r.toFun x) ∈ tsupport f
    rw [symm_toFun]
    exact hx
private theorem concatenable_push (r : EuclidIsometry) {X Y : Tuple}
    (h : Concatenable X Y) : Concatenable (push r X) (push r Y) := by
  intro g hg g' hg'
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  obtain ⟨f', hf', rfl⟩ := List.mem_map.1 hg'
  rw [tsupport_pushFn, tsupport_pushFn]
  exact (h f hf f' hf').preimage _
private theorem isometryActsOnTuples_holds : IsometryActsOnTuples := by
  intro X Y r r'
  refine ⟨push_comp r r' X, ?_, fun h => ⟨concatenable_push r h, ?_⟩⟩
  · change (X.1.map (pushFn r)).map tsupport = _
    rw [List.map_map]
    exact List.map_congr_left fun f _ => tsupport_pushFn_eq_image r f
  · refine Subtype.ext ?_
    simp only [concat, push, List.map_append]
private def translateFn (u : Space) (g : ScalarField) : ScalarField := fun x => g (x - u)
private theorem translateFn_zero (g : ScalarField) : translateFn 0 g = g := by
  funext x
  simp [translateFn]
private theorem translateFn_split (a b : Space) (g : ScalarField) :
    translateFn a g = translateFn (a - b) (translateFn b g) := by
  funext x
  simp only [translateFn]
  congr 1
  abel
abbrev _root_.YangMills.DeltaSharedProofs.p501722 := @translateFn_split
private theorem tsupport_translateFn_subset {u : Space} {δ : ℝ} (g : ScalarField) (hu : ‖u‖ ≤ δ) :
    tsupport (translateFn u g) ⊆ cthickening δ (tsupport g) := by
  refine closure_minimal (fun x hx => ?_) isClosed_cthickening
  refine mem_cthickening_of_dist_le x (x - u) δ _ (subset_tsupport g hx) ?_
  simpa [dist_eq_norm] using hu
abbrev _root_.YangMills.DeltaSharedProofs.p502471 := @tsupport_translateFn_subset
private theorem eventually_sub_translate_le {h : Space → ℝ} (hc : Continuous h)
    (hs : HasCompactSupport h) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : Space in 𝓝 0, ∀ x, |h (x - u) - h x| ≤ ε := by
  obtain ⟨δ, hδ, H⟩ := Metric.uniformContinuous_iff.1 (hs.uniformContinuous_of_continuous hc) ε hε
  refine Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun {u} hu x => ?_⟩
  have hd : dist (x - u) x < δ := by simpa [dist_eq_norm] using hu
  have := H hd
  rw [Real.dist_eq] at this
  exact this.le
abbrev _root_.YangMills.DeltaSharedProofs.p502456 := @eventually_sub_translate_le
private theorem hasDerivAt_along_axis {g : ScalarField} (hg : IsC1R4 g) (μ : Fin 4) (x : Space) :
    HasDerivAt (fun t : ℝ => g (x + t • (Pi.single μ (1 : ℝ) : Space)))
      (fderiv ℝ g x (Pi.single μ 1)) 0 := by apply _root_.YangMills.Construction.SeparatedTuples.BasicFacts.hasDerivAt_coordLine_of_contDiff <;> assumption
private theorem partialDerivR4_translateFn_sub {g : ScalarField} (hg : IsC1R4 g) (μ : Fin 4)
    (u x : Space) :
    partialDerivR4 μ (translateFn u g - g) x =
      fderiv ℝ g (x - u) (Pi.single μ 1) - fderiv ℝ g x (Pi.single μ 1) := by
  have h := (hasDerivAt_along_axis hg μ (x - u)).sub (hasDerivAt_along_axis hg μ x)
  have he : (fun t : ℝ => (translateFn u g - g) (x + t • (Pi.single μ (1 : ℝ) : Space))) =
      (fun t : ℝ => g (x - u + t • (Pi.single μ (1 : ℝ) : Space))) -
        fun t : ℝ => g (x + t • (Pi.single μ (1 : ℝ) : Space)) := by
    funext t
    simp only [translateFn, Pi.sub_apply]
    congr 2
    abel
  unfold partialDerivR4
  rw [he]
  exact h.deriv
abbrev _root_.YangMills.DeltaSharedProofs.p502281 := @partialDerivR4_translateFn_sub
private theorem eventually_c1NormR4_translateFn_sub_le {g : ScalarField} (hg : IsC1R4 g)
    (hs : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : Space in 𝓝 0, c1NormR4 (translateFn u g - g) ≤ ε := by
  have h0 := eventually_sub_translate_le hg.continuous hs hε
  have h1 : ∀ᶠ u : Space in 𝓝 0, ∀ (μ : Fin 4) (x : Space),
      |fderiv ℝ g (x - u) (Pi.single μ 1) - fderiv ℝ g x (Pi.single μ 1)| ≤ ε :=
    eventually_all.2 fun μ => eventually_sub_translate_le
      ((ContDiff.continuous_fderiv hg (by norm_num)).clm_apply continuous_const)
      (hs.fderiv_apply ℝ _) hε
  filter_upwards [h0, h1] with u hu0 hu1
  refine max_le (ciSup_le fun x => ?_) (ciSup_le fun μ => ciSup_le fun x => ?_)
  · exact hu0 x
  · rw [partialDerivR4_translateFn_sub hg]
    exact hu1 μ x
abbrev _root_.YangMills.DeltaSharedProofs.p502314 := @eventually_c1NormR4_translateFn_sub_le
private theorem tendsto_c1NormR4_translateFn_sub {g : ScalarField} (hg : IsC1R4 g)
    (hs : HasCompactSupport g) :
    Tendsto (fun u : Space => c1NormR4 (translateFn u g - g)) (𝓝 0) (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun u => ?_, fun a ha => ?_⟩
  · exact ha.trans_le (le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _))
  · filter_upwards [eventually_c1NormR4_translateFn_sub_le hg hs (half_pos ha)] with u hu
    linarith
abbrev _root_.YangMills.DeltaSharedProofs.p502201 := @tendsto_c1NormR4_translateFn_sub
private theorem tendsto_int_toNat : Tendsto Int.toNat atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨(b : ℤ), fun a ha => by omega⟩
private theorem admissiblyTendsto_of_translates (G : Tuple) (s : ℕ → Tuple)
    (u : ℕ → ℕ → Space) (hu : ∀ i, Tendsto (u i) atTop (𝓝 0)) (r₂ : ℕ)
    (hlen : ∀ r, r₂ ≤ r → (s r).len = G.len)
    (hs : ∀ r, r₂ ≤ r → ∀ i, i < G.len → componentAt (s r) i = translateFn (u i r) (componentAt G i)) :
    ∃ r₀ : ℕ, r₂ ≤ r₀ ∧ AdmissiblyTendsto (r₀ : ℤ) (fun n => s n.toNat) G := by
  have hget : ∀ i : Fin G.len, componentAt G i = G.1[(i : ℕ)]'i.2 := fun i =>
    List.getD_eq_getElem _ _ i.2
  have hC : ∀ i : Fin G.len, componentAt G i ∈ c1Compact univ := fun i => by
    rw [hget i]
    exact G.2.1 _ (List.getElem_mem i.2)
  have hlt : ∀ i j : Fin G.len, i < j →
      Disjoint (tsupport (componentAt G i)) (tsupport (componentAt G j)) := fun i j hij => by
    rw [hget i, hget j]
    exact List.pairwise_iff_getElem.1 G.2.2 i j i.2 j.2 hij
  have hdisj : ∀ i j : Fin G.len, i ≠ j →
      Disjoint (tsupport (componentAt G i)) (tsupport (componentAt G j)) := fun i j hij => by
    rcases lt_or_gt_of_ne hij with h | h
    · exact hlt i j h
    · exact (hlt j i h).symm
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i j : Fin G.len, i ≠ j →
      Disjoint (cthickening δ (tsupport (componentAt G i))) (cthickening δ (tsupport (componentAt G j))) := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    · obtain ⟨d, hd, H⟩ := (hdisj i j hij).exists_cthickenings (hC i).2.1 (isClosed_tsupport _)
      filter_upwards [Ioo_mem_nhdsGT hd] with δ hδ _
      exact H.mono (cthickening_mono hδ.2.le _) (cthickening_mono hδ.2.le _)
  obtain ⟨δ, hδ, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hsmall : ∀ᶠ r in atTop, ∀ i : Fin G.len, ‖u i r‖ ≤ δ :=
    eventually_all.2 fun i => (hu i).eventually
      (Metric.eventually_nhds_iff.2 ⟨δ, hδ0, fun {y} hy => by
        have : ‖y‖ < δ := by simpa using hy
        exact this.le⟩)
  obtain ⟨R, hR⟩ := eventually_atTop.1 hsmall
  have hnat : ∀ n : ℤ, ((max r₂ R : ℕ) : ℤ) ≤ n → max r₂ R ≤ n.toNat := fun n hn => by omega
  refine ⟨max r₂ R, le_max_left _ _,
    fun n hn => hlen _ ((le_max_left _ _).trans (hnat n hn)),
    fun i => cthickening δ (tsupport (componentAt G i)), fun i => (hC i).2.1.cthickening,
    fun i j hij => hδ i j hij, fun n hn i => ?_, fun i => ?_⟩
  · simp only []
    rw [hs _ ((le_max_left _ _).trans (hnat n hn)) i i.2]
    exact union_subset (tsupport_translateFn_subset _ (hR _ ((le_max_right _ _).trans (hnat n hn)) i))
      (self_subset_cthickening _)
  · refine (((tendsto_c1NormR4_translateFn_sub (hC i).1 (hC i).2.1).comp (hu i)).comp
      tendsto_int_toNat).congr' ?_
    filter_upwards [eventually_ge_atTop (r₂ : ℤ)] with n hn
    simp only [comp_apply]
    rw [hs n.toNat (by omega) i i.2]
private theorem getD_map_translateFn (L : List ScalarField) (a : Space) (i : ℕ) :
    (L.map (translateFn a)).getD i 0 = translateFn a (L.getD i 0) := by
  induction L generalizing i with
  | nil => funext x; simp [translateFn]
  | cons f L ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i
abbrev _root_.YangMills.DeltaSharedProofs.p502215 := @getD_map_translateFn
private theorem getD_append_map_translateFn_right (Y L : List ScalarField) (a b : Space) (i : ℕ) :
    (Y ++ L.map (translateFn a)).getD i 0 =
      translateFn (if i < Y.length then 0 else a - b) ((Y ++ L.map (translateFn b)).getD i 0) := by
  by_cases hi : i < Y.length
  · rw [if_pos hi, translateFn_zero, List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hi]
  · have hle : Y.length ≤ i := not_lt.1 hi
    rw [if_neg hi, List.getD_append_right _ _ _ _ hle, List.getD_append_right _ _ _ _ hle,
      getD_map_translateFn, getD_map_translateFn, ← translateFn_split]
abbrev _root_.YangMills.DeltaSharedProofs.p502597 := @getD_append_map_translateFn_right
private theorem getD_map_translateFn_append_left (Y L : List ScalarField) (a b : Space) (i : ℕ) :
    (L.map (translateFn a) ++ Y).getD i 0 =
      translateFn (if i < L.length then a - b else 0) ((L.map (translateFn b) ++ Y).getD i 0) := by
  by_cases hi : i < L.length
  · have h1 : i < (L.map (translateFn a)).length := by simpa using hi
    have h2 : i < (L.map (translateFn b)).length := by simpa using hi
    rw [if_pos hi, List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2,
      getD_map_translateFn, getD_map_translateFn, ← translateFn_split]
  · have hle : L.length ≤ i := not_lt.1 hi
    have h1 : (L.map (translateFn a)).length ≤ i := by simpa using hle
    have h2 : (L.map (translateFn b)).length ≤ i := by simpa using hle
    rw [if_neg hi, translateFn_zero, List.getD_append_right _ _ _ _ h1,
      List.getD_append_right _ _ _ _ h2]
    simp
abbrev _root_.YangMills.DeltaSharedProofs.p97 := @getD_map_translateFn_append_left
private theorem push_translate_val (v : Space) (X : Tuple) :
    (push (translate v) X).1 = X.1.map (translateFn v) := by apply _root_.YangMills.Construction.ReflectionPositivity.push_translate <;> assumption
private theorem concatOrNil_val {X Y : Tuple} (h : Concatenable X Y) :
    (concatOrNil X Y).1 = X.1 ++ Y.1 := by
  rw [concatOrNil, dif_pos h]
  rfl
private theorem concat_congr_left {X X' Y : Tuple} (e : X = X')
    (h : Concatenable X Y) (h' : Concatenable X' Y) :
    concat X Y h = concat X' Y h' := by
  subst e
  rfl
private theorem eventually_concatenable_translate (X Y : Tuple) {w : ℕ → Space} {v : Space}
    (hw : Tendsto (fun r => w r - v) atTop (𝓝 0))
    (hY : Concatenable Y (push (translate v) X)) :
    ∀ᶠ r in atTop, Concatenable Y (push (translate (w r)) X) := by
  have hall : ∀ᶠ r in atTop, ∀ f ∈ {f | f ∈ Y.1}, ∀ h ∈ {h | h ∈ X.1},
      Disjoint (tsupport f) (tsupport (translateFn (w r) h)) := by
    refine (eventually_all_finite (List.finite_toSet Y.1)).2 fun f hf =>
      (eventually_all_finite (List.finite_toSet X.1)).2 fun h hh => ?_
    have hm : translateFn v h ∈ (push (translate v) X).1 := by
      rw [push_translate_val]
      exact List.mem_map_of_mem hh
    have hd : Disjoint (tsupport (translateFn v h)) (tsupport f) := (hY f hf (translateFn v h) hm).symm
    have hk : IsCompact (tsupport (translateFn v h)) := ((push (translate v) X).2.1 _ hm).2.1
    obtain ⟨d, hd0, H⟩ := hd.exists_cthickenings hk (isClosed_tsupport _)
    have hsmall : ∀ᶠ r in atTop, ‖w r - v‖ ≤ d := hw.eventually
      (Metric.eventually_nhds_iff.2 ⟨d, hd0, fun {y} hy => by
        have : ‖y‖ < d := by simpa using hy
        exact this.le⟩)
    filter_upwards [hsmall] with r hr
    rw [translateFn_split (w r) v h]
    exact (H.mono (tsupport_translateFn_subset _ hr) (self_subset_cthickening _)).symm
  filter_upwards [hall] with r hr f hf g hg
  rw [push_translate_val] at hg
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hg
  exact hr f hf h hh
private theorem admissiblyTendsto_mono {r₀ r' : ℤ} {s : ℤ → Tuple} {X : Tuple}
    (hr : r₀ ≤ r') (h : AdmissiblyTendsto r₀ s X) : AdmissiblyTendsto r' s X := by
  obtain ⟨hlen, A, hA, hd, hsup, hn⟩ := h
  exact ⟨fun r hr' => hlen r (hr.trans hr'), A, hA, hd, fun r hr' => hsup r (hr.trans hr'), hn⟩
private theorem tendsto_ite_zero_left {w : ℕ → Space} (hw : Tendsto w atTop (𝓝 0)) (p : Prop)
    [Decidable p] : Tendsto (fun r => if p then 0 else w r) atTop (𝓝 0) := by
  by_cases h : p
  · simp [h]
  · simpa [h] using hw
abbrev _root_.YangMills.DeltaSharedProofs.p500968 := @tendsto_ite_zero_left
private theorem tendsto_ite_zero_right {w : ℕ → Space} (hw : Tendsto w atTop (𝓝 0)) (p : Prop)
    [Decidable p] : Tendsto (fun r => if p then w r else 0) atTop (𝓝 0) := by
  by_cases h : p
  · simpa [h] using hw
  · simp [h]
abbrev _root_.YangMills.DeltaSharedProofs.p502399 := @tendsto_ite_zero_right
private theorem translateTendsto_holds : TranslateTendsto := by
  intro X w v hw
  have hu : Tendsto (fun r => w r - v) atTop (𝓝 0) := by simpa using hw.sub_const v
  obtain ⟨r₀, h0, c⟩ := admissiblyTendsto_of_translates (push (translate v) X)
    (fun r => push (translate (w r)) X) (fun _ r => w r - v) (fun _ => hu) 1
    (fun r _ => by simp [Tuple.len, push_translate_val])
    (fun r _ i _ => by
      simp only [componentAt]
      rw [push_translate_val, push_translate_val, getD_map_translateFn, getD_map_translateFn,
        ← translateFn_split])
  exact ⟨r₀, h0, c⟩
private theorem translateConcatTendsto_holds : TranslateConcatTendsto := by
  intro X Y w v hw hY
  have hu : Tendsto (fun r => w r - v) atTop (𝓝 0) := by simpa using hw.sub_const v
  obtain ⟨R, hR⟩ := eventually_atTop.1 (eventually_concatenable_translate X Y hu hY)
  have hd1 : ∀ r, max 1 R ≤ r → Concatenable Y (push (translate (w r)) X) :=
    fun r hr => hR r ((le_max_right _ _).trans hr)
  have hd2 : ∀ r, max 1 R ≤ r → Concatenable (push (translate (w r)) X) Y :=
    fun r hr => (hd1 r hr).symm
  have hv1 : ∀ r, max 1 R ≤ r → (concatOrNil Y (push (translate (w r)) X)).1 =
      Y.1 ++ X.1.map (translateFn (w r)) := fun r hr => by
    rw [concatOrNil_val (hd1 r hr), push_translate_val]
  have hv2 : ∀ r, max 1 R ≤ r → (concatOrNil (push (translate (w r)) X) Y).1 =
      X.1.map (translateFn (w r)) ++ Y.1 := fun r hr => by
    rw [concatOrNil_val (hd2 r hr), push_translate_val]
  have hg1 : (concat Y (push (translate v) X) hY).1 = Y.1 ++ X.1.map (translateFn v) := by
    change Y.1 ++ (push (translate v) X).1 = _
    rw [push_translate_val]
  have hg2 : (concat (push (translate v) X) Y hY.symm).1 =
      X.1.map (translateFn v) ++ Y.1 := by
    change (push (translate v) X).1 ++ Y.1 = _
    rw [push_translate_val]
  obtain ⟨ra, hra, ca⟩ := admissiblyTendsto_of_translates (concat Y (push (translate v) X) hY)
    (fun r => concatOrNil Y (push (translate (w r)) X))
    (fun i r => if i < Y.1.length then 0 else w r - v) (fun i => tendsto_ite_zero_left hu _)
    (max 1 R)
    (fun r hr => by simp [Tuple.len, hv1 r hr, hg1])
    (fun r hr i _ => by
      simp only [componentAt]
      rw [hv1 r hr, hg1]
      exact getD_append_map_translateFn_right _ _ _ _ _)
  obtain ⟨rb, hrb, cb⟩ := admissiblyTendsto_of_translates
    (concat (push (translate v) X) Y hY.symm)
    (fun r => concatOrNil (push (translate (w r)) X) Y)
    (fun i r => if i < X.1.length then w r - v else 0) (fun i => tendsto_ite_zero_right hu _)
    (max 1 R)
    (fun r hr => by simp [Tuple.len, hv2 r hr, hg2])
    (fun r hr i _ => by
      simp only [componentAt]
      rw [hv2 r hr, hg2]
      exact getD_map_translateFn_append_left _ _ _ _ _)
  have hm : max 1 R ≤ max ra rb := hra.trans (le_max_left _ _)
  exact ⟨max ra rb, (le_max_left _ _).trans hm,
    fun n hn => ⟨hd1 n (hm.trans hn), hd2 n (hm.trans hn)⟩,
    admissiblyTendsto_mono (Int.ofNat_le.2 (le_max_left _ _)) ca,
    admissiblyTendsto_mono (Int.ofNat_le.2 (le_max_right _ _)) cb⟩
private theorem reflectIso_atOffset_toFun (M : NormalMirror) (c' : ℝ) :
    (M.atOffset c').reflectIso.toFun =
      (EuclidIsometry.translate (M.shiftVec c')).toFun ∘ M.reflectIso.toFun := by
  funext x μ
  simp only [NormalMirror.reflectIso, NormalMirror.atOffset, NormalMirror.reflectPt,
    EuclidIsometry.translate, NormalMirror.shiftVec, comp_apply, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring
private theorem push_reflectIso_atOffset (M : NormalMirror) (c' : ℝ) (X : Tuple) :
    push (M.atOffset c').reflectIso X =
      push (translate (M.shiftVec c')) (push M.reflectIso X) := by
  have e : (M.atOffset c').reflectIso =
      (EuclidIsometry.translate (M.shiftVec c')).comp M.reflectIso :=
    euclidIsometry_ext (reflectIso_atOffset_toFun M c')
  rw [e, push_comp]
private theorem push_reflectIso_atOffset_mem {M : NormalMirror} {X : Tuple} (c' : ℝ)
    (hX : X ∈ tuplesSupportedIn M.posSide) :
    push (M.atOffset c').reflectIso X ∈
      tuplesSupportedIn {x | euclidInner M.normal x < 2 * c' - M.offset} := by
  intro g hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  rw [tsupport_pushFn]
  intro y hy
  have hz : M.offset <
      euclidInner M.normal ((M.atOffset c').reflectIso.symm.toFun y) := hX f hf hy
  have e := (M.atOffset c').euclidInner_reflectPt
    ((M.atOffset c').reflectIso.symm.toFun y)
  have e' : (M.atOffset c').reflectPt ((M.atOffset c').reflectIso.symm.toFun y) = y :=
    (M.atOffset c').reflectIso.toFun_symm y
  rw [e'] at e
  change euclidInner M.normal y - c' =
    -(euclidInner M.normal ((M.atOffset c').reflectIso.symm.toFun y) - c') at e
  change euclidInner M.normal y < 2 * c' - M.offset
  linarith
private theorem reflectConcatTendsto_holds : ReflectConcatTendsto := by
  intro M X₁ X₂ h₁ h₂ c hc hlim
  have hb : Tendsto (fun n => M.shiftVec (c n)) atTop (𝓝 0) := by
    have h : Tendsto (fun n => 2 * (c n - M.offset) / euclidNormVec M.normal ^ 2) atTop (𝓝 0) := by
      simpa using ((hlim.sub_const M.offset).const_mul 2).div_const (euclidNormVec M.normal ^ 2)
    simpa [NormalMirror.shiftVec] using h.smul_const M.normal
  have hθ := NormalMirror.concatenable_reflectIso h₁ h₂
  have hZ0 : push (translate 0) (push M.reflectIso X₁) = push M.reflectIso X₁ := by
    refine Subtype.ext ?_
    rw [push_translate_val]
    simp [show translateFn 0 = id from funext translateFn_zero]
  refine ⟨fun n _ => reflectIso_atOffset_toFun M (c n), hb, fun n hn => ?_, ?_⟩
  · have hmem := push_reflectIso_atOffset_mem (c n) h₁
    have hle := hc n hn
    refine ⟨hmem, fun x hx => ?_, concatenable_of_disjoint ?_ hmem h₂⟩
    · have hx' : euclidInner M.normal x < 2 * c n - M.offset := hx
      change euclidInner M.normal x < M.offset
      linarith
    · refine Set.disjoint_left.2 fun x hx hx' => ?_
      have a1 : euclidInner M.normal x < 2 * c n - M.offset := hx
      have a2 : M.offset < euclidInner M.normal x := hx'
      linarith
  · obtain ⟨n₀, h0, -, -, hcv⟩ := translateConcatTendsto_holds (push M.reflectIso X₁) X₂
      (fun n => M.shiftVec (c n)) 0 hb (by rw [hZ0]; exact hθ.symm)
    refine ⟨n₀, h0, ?_⟩
    have e1 : (fun n : ℤ =>
        concatOrNil (push (M.atOffset (c n.toNat)).reflectIso X₁) X₂) =
        fun n : ℤ => concatOrNil
          (push (translate (M.shiftVec (c n.toNat))) (push M.reflectIso X₁)) X₂ := by
      funext n
      rw [push_reflectIso_atOffset]
    rw [e1]
    rwa [concat_congr_left hZ0 _ hθ] at hcv
theorem statement_holds : statement :=
  ⟨isometryActsOnTuples_holds, translateConcatTendsto_holds, translateTendsto_holds,
    reflectConcatTendsto_holds⟩
end YangMills.Construction.ReflectionPositivity.MovingTestFunctions
