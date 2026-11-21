import YangMills.Construction.Continuum.NeighbourhoodsAdmissibleFamiliesAndMembersOfTheClasses
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevelProof
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TorusTransport.SupportFacts
open TorusMetric TestFunctions
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_add_le (v w : Fin 4 → ℝ) :
    euclidNormVec (v + w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem setDistR4_le_of_mem {A B : Set (Fin 4 → ℝ)} {a b : Fin 4 → ℝ} (ha : a ∈ A) (hb : b ∈ B) :
    setDistR4 A B ≤ ENNReal.ofReal (euclidNormVec (a - b)) :=
  iInf₂_le_of_le a ha (iInf₂_le b hb)
theorem le_setDistR4 {A B : Set (Fin 4 → ℝ)} {c : ℝ≥0∞}
    (h : ∀ a ∈ A, ∀ b ∈ B, c ≤ ENNReal.ofReal (euclidNormVec (a - b))) :
    c ≤ setDistR4 A B :=
  le_iInf₂ fun a ha => le_iInf₂ fun b hb => h a ha b hb
theorem setDist_anti (D : TransportData) {A B A' B' : Set (Fin 4 → ℝ)} (h : A ⊆ B)
    (h' : A' ⊆ B') :
    Domain.euclidean.setDist D B B' ≤ Domain.euclidean.setDist D A A' :=
  le_setDistR4 fun _ ha _ hb => setDistR4_le_of_mem (h ha) (h' hb)
theorem disjoint_of_setDist_pos (D : TransportData) {S S' : Set (Fin 4 → ℝ)}
    (h : 0 < Domain.euclidean.setDist D S S') : Disjoint S S' := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h₁ := setDistR4_le_of_mem hx hx'
  have e : euclidNormVec (x - x) = 0 := by simp [euclidNormVec]
  rw [e, ENNReal.ofReal_zero] at h₁
  exact absurd h (not_lt.mpr h₁)
theorem setDist_pos_of_disjoint (D : TransportData) {S S' : Set (Fin 4 → ℝ)} (hS : IsCompact S)
    (hS' : IsCompact S') (h : Disjoint S S') : 0 < Domain.euclidean.setDist D S S' := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [Domain.setDist_empty_left]
    exact ENNReal.zero_lt_top
  rcases S'.eq_empty_or_nonempty with rfl | hne'
  · rw [Domain.setDist_empty_right]
    exact ENNReal.zero_lt_top
  have hc : Continuous fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => euclidNormVec (p.1 - p.2) :=
    continuous_euclidNormVec.comp (continuous_fst.sub continuous_snd)
  obtain ⟨⟨s, s'⟩, hp, hmin⟩ := (hS.prod hS').exists_isMinOn (hne.prod hne') hc.continuousOn
  have hpos : 0 < euclidNormVec (s - s') :=
    euclidNormVec_pos (sub_ne_zero.mpr fun e =>
      Set.disjoint_left.mp h hp.1 (by rw [e]; exact hp.2))
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hpos) ?_
  exact le_setDistR4 fun a ha b hb =>
    ENNReal.ofReal_le_ofReal (isMinOn_iff.mp hmin (a, b) ⟨ha, hb⟩)
theorem disjointIffPosDist_holds (D : TransportData) : DisjointIffPosDist D :=
  ⟨fun _ _ hS hS' h => setDist_pos_of_disjoint D hS hS' h, fun _ _ h => disjoint_of_setDist_pos D h⟩
theorem closedNbhd_empty (η : ℝ) : closedNbhd ∅ η = ∅ := by
  ext x
  simp [closedNbhd, setDistR4]
theorem exists_mem_euclidNormVec_sub_le {S : Set (Fin 4 → ℝ)} (hS : IsCompact S)
    (hne : S.Nonempty) {x : Fin 4 → ℝ} {η : ℝ} (hη : 0 ≤ η) (hx : x ∈ closedNbhd S η) :
    ∃ s ∈ S, euclidNormVec (x - s) ≤ η := by
  have hc : Continuous fun s => euclidNormVec (x - s) :=
    continuous_euclidNormVec.comp (continuous_const.sub continuous_id)
  obtain ⟨s, hs, hmin⟩ := hS.exists_isMinOn hne hc.continuousOn
  refine ⟨s, hs, ?_⟩
  have h₁ : ENNReal.ofReal (euclidNormVec (x - s)) ≤ setDistR4 {x} S := by
    refine le_setDistR4 fun a ha b hb => ?_
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact ENNReal.ofReal_le_ofReal (isMinOn_iff.mp hmin b hb)
  exact (ENNReal.ofReal_le_ofReal_iff hη).mp (h₁.trans hx)
theorem nbhdDistLowerBound_holds (D : TransportData) : NbhdDistLowerBound D := by
  intro S S' η η' hS hS' hη hη'
  have hempty : S = ∅ ∨ S' = ∅ →
      Domain.euclidean.setDist D (closedNbhd S η) (closedNbhd S' η') = ∞ ∧
        Domain.euclidean.setDist D S S' = ∞ := by
    rintro (rfl | rfl)
    · rw [closedNbhd_empty]
      exact ⟨Domain.setDist_empty_left D _ _, Domain.setDist_empty_left D _ _⟩
    · rw [closedNbhd_empty]
      exact ⟨Domain.setDist_empty_right D _ _, Domain.setDist_empty_right D _ _⟩
  refine ⟨?_, fun h => ⟨(hempty h).1, ?_⟩⟩
  · by_cases h : S = ∅ ∨ S' = ∅
    · rw [(hempty h).1]
      exact le_top
    · rw [not_or] at h
      have hne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr h.1
      have hne' : S'.Nonempty := Set.nonempty_iff_ne_empty.mpr h.2
      refine le_setDistR4 fun x hx x' hx' => ?_
      obtain ⟨s, hs, hxs⟩ := exists_mem_euclidNormVec_sub_le hS hne hη.le hx
      obtain ⟨s', hs', hxs'⟩ := exists_mem_euclidNormVec_sub_le hS' hne' hη'.le hx'
      rw [tsub_le_iff_right, tsub_le_iff_right,
        ← ENNReal.ofReal_add (euclidNormVec_nonneg _) hη'.le,
        ← ENNReal.ofReal_add (add_nonneg (euclidNormVec_nonneg _) hη'.le) hη.le]
      refine le_trans (setDistR4_le_of_mem hs hs') (ENNReal.ofReal_le_ofReal ?_)
      have e : s - s' = -(x - s) + ((x - x') + (x' - s')) := by abel
      have h₁ := euclidNormVec_add_le (-(x - s)) ((x - x') + (x' - s'))
      have h₂ := euclidNormVec_add_le (x - x') (x' - s')
      rw [euclidNormVec_neg] at h₁
      rw [e]
      linarith
  · rw [(hempty h).2, ENNReal.sub_eq_top_iff, ENNReal.sub_eq_top_iff]
    exact ⟨⟨rfl, ENNReal.ofReal_ne_top⟩, ENNReal.ofReal_ne_top⟩
theorem subfamilyIsAdmissible_holds (D : TransportData) : SubfamilyIsAdmissible D := by
  intro q d R hd hR A hA J hJ
  refine ⟨fun l => hA.1 _, fun l k hlk => hA.2 _ _ fun e => hlk ?_⟩
  exact (J.orderEmbOfFin (k := subfamilyLength J hJ) rfl).injective e
theorem admissibleProductMembers_holds (D : TransportData) : AdmissibleProductMembers D := by
  intro q d R hd hR A hA h hh
  have hsub : ∀ l, Domain.euclidean.fnSupport D (h l) ⊆ A l := fun l => (hh l).2.2
  have hpair : ∀ l k, l ≠ k → ENNReal.ofReal d ≤
      Domain.euclidean.setDist D (Domain.euclidean.fnSupport D (h l))
        (Domain.euclidean.fnSupport D (h k)) := fun l k hlk =>
    (hA.2 l k hlk).trans (setDist_anti D (hsub l) (hsub k))
  have hlip : ∀ l, Domain.euclidean.LipschitzOn D (h l) := fun l => (hh l).1
  have hrad : Domain.euclidean.IsBallSupported D R hR h := fun l => by
    obtain ⟨x, hx⟩ := hA.1 l
    exact ⟨x, (hsub l).trans hx⟩
  have hsep : Domain.euclidean.IsSepLipschitz D h :=
    ⟨hlip, fun l => (hh l).2.1, fun l k hlk =>
      disjoint_of_setDist_pos D (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hd) (hpair l k hlk))⟩
  exact ⟨hsep, hrad, hpair, ⟨hlip, hrad, hpair⟩, fun hq hs =>
    (Domain.le_supportGap_iff D Domain.euclidean hq hs).mpr hpair⟩
theorem isCompact_closedBallR4 (x : Fin 4 → ℝ) (R : ℝ) : IsCompact (closedBallR4 x R) := by apply _root_.YangMills.SharedProofs.p20989 <;> assumption
theorem lipFamilyIsSepLipschitz_holds (D : TransportData) : LipFamilyIsSepLipschitz D := by
  intro n d R hd hR f hf
  obtain ⟨hlip, hrad, hpair⟩ := hf
  refine ⟨hlip, fun i => ?_, fun i k hik =>
    disjoint_of_setDist_pos D (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hd) (hpair i k hik))⟩
  obtain ⟨u, hu⟩ := hrad i
  exact (isCompact_closedBallR4 u R).of_isClosed_subset (isClosed_tsupport _) hu
section C1Bounds
variable {f : (Fin 4 → ℝ) → ℝ}
theorem hasDerivAt_comp_line (hf : ContDiff ℝ 1 f) (y v : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => f (y + t • v)) (fderiv ℝ f (y + t • v) v) t := by
  have h₁ : HasDerivAt (fun t : ℝ => y + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add y
  exact ((hf.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t h₁
theorem partialDerivR4_eq_fderiv (hf : ContDiff ℝ 1 f) (μ : Fin 4) (u : Fin 4 → ℝ) :
    partialDerivR4 μ f u = fderiv ℝ f u (Pi.single μ 1) := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.partialDerivR4_eq_fderiv <;> assumption
theorem gradNorm_eq_sqrt_fderiv (D : TransportData) (hf : ContDiff ℝ 1 f) (u : Fin 4 → ℝ) :
    Domain.euclidean.gradNorm D f u =
      Real.sqrt (∑ μ, fderiv ℝ f u (Pi.single μ 1) ^ 2) := by
  have h : ∀ μ, ‖Domain.euclidean.partialDeriv D μ f u‖ ^ 2 =
      fderiv ℝ f u (Pi.single μ 1) ^ 2 := fun μ => by
    change ‖partialDerivR4 μ f u‖ ^ 2 = _
    rw [partialDerivR4_eq_fderiv hf, Real.norm_eq_abs, sq_abs]
  simp only [Domain.gradNorm, h]
theorem abs_fderiv_apply_le (u v : Fin 4 → ℝ) :
    |fderiv ℝ f u v| ≤
      Real.sqrt (∑ μ, fderiv ℝ f u (Pi.single μ 1) ^ 2) * euclidNormVec v := by
  have hv : v = ∑ μ, v μ • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) := by
    ext ν
    simp [Finset.sum_apply, Pi.single_apply]
  have e : fderiv ℝ f u v = fderiv ℝ f u (∑ μ, v μ • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)) :=
    congrArg _ hv
  rw [map_sum] at e
  simp only [map_smul, smul_eq_mul] at e
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun μ => fderiv ℝ f u (Pi.single μ 1)) v
  have h := Real.abs_le_sqrt cs
  rw [Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
  have e' : fderiv ℝ f u v = ∑ μ, fderiv ℝ f u (Pi.single μ 1) * v μ := by
    rw [e]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [e']
  exact h
theorem exists_bound_sqrt_fderiv (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ C, ∀ u, ‖Real.sqrt (∑ μ, fderiv ℝ f u (Pi.single μ 1) ^ 2)‖ ≤ C := by
  have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hp : ∀ μ : Fin 4, Continuous fun u => fderiv ℝ f u (Pi.single μ 1) := fun μ =>
    hd.clm_apply continuous_const
  have hG : Continuous fun u => Real.sqrt (∑ μ, fderiv ℝ f u (Pi.single μ 1) ^ 2) :=
    Real.continuous_sqrt.comp (continuous_finsetSum _ fun μ _ => (hp μ).pow 2)
  let g : ((Fin 4 → ℝ) →L[ℝ] ℝ) → ℝ := fun L => Real.sqrt (∑ μ, L (Pi.single μ 1) ^ 2)
  have hS : HasCompactSupport fun u => Real.sqrt (∑ μ, fderiv ℝ f u (Pi.single μ 1) ^ 2) :=
    (hc.fderiv (𝕜 := ℝ)).comp_left (g := g) (by simp [g])
  exact hG.bounded_above_of_compact_support hS
theorem gradSupNorm_bounds_of_hasCompactSupport (D : TransportData) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    Domain.euclidean.gradSupNorm D f < ∞ ∧
      (∀ x y : Fin 4 → ℝ,
        |f x - f y| ≤ (Domain.euclidean.gradSupNorm D f).toReal * euclidNorm (x - y)) ∧
      Domain.euclidean.lipConst D f ≤ Domain.euclidean.gradSupNorm D f := by
  obtain ⟨C, hC⟩ := exists_bound_sqrt_fderiv hf hc
  have hfin : Domain.euclidean.gradSupNorm D f < ∞ := by
    refine lt_of_le_of_lt (iSup_le fun u => ENNReal.ofReal_le_ofReal ?_)
      (ENNReal.ofReal_lt_top (r := C))
    rw [gradNorm_eq_sqrt_fderiv D hf]
    exact hC u
  have hle : ∀ u, Real.sqrt (∑ μ, fderiv ℝ f u (Pi.single μ 1) ^ 2) ≤
      (Domain.euclidean.gradSupNorm D f).toReal := fun u => by
    have h₁ : ENNReal.ofReal ‖Domain.euclidean.gradNorm D f u‖ ≤
        Domain.euclidean.gradSupNorm D f :=
      le_iSup (fun u => ENNReal.ofReal ‖Domain.euclidean.gradNorm D f u‖) u
    have h₂ := (ENNReal.ofReal_le_iff_le_toReal hfin.ne).mp h₁
    rw [gradNorm_eq_sqrt_fderiv D hf, Real.norm_eq_abs] at h₂
    exact (le_abs_self _).trans h₂
  have hlip : ∀ x y : Fin 4 → ℝ,
      |f x - f y| ≤ (Domain.euclidean.gradSupNorm D f).toReal * euclidNorm (x - y) := by
    intro x y
    have hcont : Continuous fun t : ℝ => f (y + t • (x - y)) :=
      hf.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
    obtain ⟨t, -, ht⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => f (y + t • (x - y)))
      (fun t => fderiv ℝ f (y + t • (x - y)) (x - y)) zero_lt_one hcont.continuousOn
      (fun t _ => hasDerivAt_comp_line hf y (x - y) t)
    have e : f x - f y = fderiv ℝ f (y + t • (x - y)) (x - y) := by
      rw [ht]
      simp
    rw [e]
    exact (abs_fderiv_apply_le _ _).trans
      (mul_le_mul_of_nonneg_right (hle _) (Real.sqrt_nonneg _))
  refine ⟨hfin, hlip, ?_⟩
  have h₃ : Domain.euclidean.lipConst D f ≤
      ENNReal.ofReal (Domain.euclidean.gradSupNorm D f).toReal :=
    (ennLipConst_le_ofReal_iff (fun _ _ h => Domain.euclidean.pointDist_pos D h)
      (Domain.euclidean.pointDist_self_nonneg D) ENNReal.toReal_nonneg).mpr fun u v => hlip u v
  rwa [ENNReal.ofReal_toReal hfin.ne] at h₃
end C1Bounds
theorem contDiff_hasCompactSupport_of_toComplex_mem {f : RealFun (Fin 4 → ℝ)}
    (h : RealFun.toComplex f ∈ c1CompactSupport) :
    ContDiff ℝ 1 f ∧ HasCompactSupport f := by
  obtain ⟨h₁, h₂⟩ := h
  have h₁' : ContDiff ℝ 1 (RealFun.toComplex f) := h₁
  have hc : ContDiff ℝ 1 f := by
    have h₃ := Complex.reCLM.contDiff.comp h₁'
    simpa [Function.comp_def, RealFun.toComplex] using h₃
  refine ⟨hc, ?_⟩
  have e : Function.support (RealFun.toComplex f) = Function.support f := by
    ext x
    simp [RealFun.toComplex]
  have e' : tsupport (RealFun.toComplex f) = tsupport f := by
    simp only [tsupport, e]
  rw [e'] at h₂
  exact h₂
theorem c1CompactIsLipschitz_holds (D : TransportData) : C1CompactIsLipschitz D := fun _ hf =>
  gradSupNorm_bounds_of_hasCompactSupport D (contDiff_hasCompactSupport_of_toComplex_mem hf).1
    (contDiff_hasCompactSupport_of_toComplex_mem hf).2
theorem disjointC1FamilyIsSeparated_holds (D : TransportData) :
    DisjointC1FamilyIsSeparated D := by
  intro n f hf hdisj
  have hc := fun i => contDiff_hasCompactSupport_of_toComplex_mem (hf i)
  have hs : Domain.euclidean.IsSepLipschitz D f :=
    ⟨fun i => lt_of_le_of_lt (gradSupNorm_bounds_of_hasCompactSupport D (hc i).1 (hc i).2).2.2
        (gradSupNorm_bounds_of_hasCompactSupport D (hc i).1 (hc i).2).1,
      fun i => (hc i).2, hdisj⟩
  exact ⟨hs, hs, fun i => (hc i).1⟩
section SupportedSpaces
variable {A : Set (Fin 4 → ℝ)}
theorem hasCompactSupportIn_zero : HasCompactSupportIn (0 : RealFun (Fin 4 → ℝ)) A := by
  have e : tsupport (0 : RealFun (Fin 4 → ℝ)) = ∅ := by
    simp [tsupport]
  exact ⟨by rw [e]; exact isCompact_empty, by rw [e]; exact Set.empty_subset _⟩
theorem hasCompactSupportIn_add {f g : RealFun (Fin 4 → ℝ)} (hf : HasCompactSupportIn f A)
    (hg : HasCompactSupportIn g A) : HasCompactSupportIn (f + g) A := by
  have sub : tsupport (f + g) ⊆ tsupport f ∪ tsupport g := by
    refine closure_minimal (fun x hx => ?_) ((isClosed_tsupport f).union (isClosed_tsupport g))
    by_contra hn
    rw [Set.mem_union, not_or] at hn
    have hf₀ : f x = 0 := image_eq_zero_of_notMem_tsupport hn.1
    have hg₀ : g x = 0 := image_eq_zero_of_notMem_tsupport hn.2
    exact hx (by simp [hf₀, hg₀])
  exact ⟨(hf.1.union hg.1).of_isClosed_subset (isClosed_tsupport _) sub,
    sub.trans (Set.union_subset hf.2 hg.2)⟩
theorem hasCompactSupportIn_smul {f : RealFun (Fin 4 → ℝ)} (c : ℝ)
    (hf : HasCompactSupportIn f A) : HasCompactSupportIn (c • f) A := by
  have sub : tsupport (c • f) ⊆ tsupport f :=
    closure_mono fun x hx h₀ => hx (by simp [show f x = 0 from h₀])
  exact ⟨hf.1.of_isClosed_subset (isClosed_tsupport _) sub, sub.trans hf.2⟩
theorem lipConstFinite_iff_isLipschitzFor_euclid {h : RealFun (Fin 4 → ℝ)} :
    LipConstFinite euclidDistR4 h ↔ TestFunctions.IsLipschitzFor euclidDistR4 h :=
  lipConstFinite_iff_isLipschitzFor (fun _ _ huv => euclidNormVec_pos (sub_ne_zero.mpr huv))
    (fun _ => Real.sqrt_nonneg _)
def lipschitzSupportedInSubmodule (A : Set (Fin 4 → ℝ)) :
    Submodule ℝ (RealFun (Fin 4 → ℝ)) where
  carrier := lipschitzSupportedIn A
  add_mem' := by
    intro f g hf hg
    obtain ⟨C, hC, H⟩ := lipConstFinite_iff_isLipschitzFor_euclid.mp hf.1
    obtain ⟨C', hC', H'⟩ := lipConstFinite_iff_isLipschitzFor_euclid.mp hg.1
    refine ⟨lipConstFinite_iff_isLipschitzFor_euclid.mpr
      ⟨C + C', add_nonneg hC hC', fun x y => ?_⟩, hasCompactSupportIn_add hf.2 hg.2⟩
    have e : (f + g) x - (f + g) y = (f x - f y) + (g x - g y) := by
      simp only [Pi.add_apply]
      ring
    rw [e, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (H x y) (H' x y))
  zero_mem' :=
    ⟨lipConstFinite_iff_isLipschitzFor_euclid.mpr ⟨0, le_rfl, fun x y => by simp⟩,
      hasCompactSupportIn_zero⟩
  smul_mem' := by
    intro c f hf
    obtain ⟨C, hC, H⟩ := lipConstFinite_iff_isLipschitzFor_euclid.mp hf.1
    refine ⟨lipConstFinite_iff_isLipschitzFor_euclid.mpr
      ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, fun x y => ?_⟩, hasCompactSupportIn_smul c hf.2⟩
    have e : (c • f) x - (c • f) y = c • (f x - f y) := by
      simp only [Pi.smul_apply, smul_sub]
    rw [e, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (H x y) (norm_nonneg _)
def c1SupportedInSubmodule (A : Set (Fin 4 → ℝ)) : Submodule ℝ (RealFun (Fin 4 → ℝ)) where
  carrier := c1SupportedIn A
  add_mem' := by
    intro f g hf hg
    exact ⟨ContDiff.add hf.1 hg.1, hasCompactSupportIn_add hf.2 hg.2⟩
  zero_mem' := ⟨contDiff_const, hasCompactSupportIn_zero⟩
  smul_mem' := by
    intro c f hf
    exact ⟨ContDiff.const_smul c hf.1, hasCompactSupportIn_smul c hf.2⟩
end SupportedSpaces
theorem supportedFnSubmodules_holds (D : TransportData) : SupportedFnSubmodules := by
  intro A
  refine ⟨⟨lipschitzSupportedInSubmodule A, rfl⟩, ⟨c1SupportedInSubmodule A, rfl⟩,
    fun h hh => ⟨?_, hh.2⟩⟩
  have h₁ := gradSupNorm_bounds_of_hasCompactSupport D hh.1 hh.2.1
  exact lt_of_le_of_lt h₁.2.2 h₁.1
theorem allSupportFacts_holds : AllSupportFacts := fun D =>
  ⟨nbhdDistLowerBound_holds D, subfamilyIsAdmissible_holds D, admissibleProductMembers_holds D,
    lipFamilyIsSepLipschitz_holds D, c1CompactIsLipschitz_holds D,
    disjointC1FamilyIsSeparated_holds D, supportedFnSubmodules_holds D,
    disjointIffPosDist_holds D⟩
end YangMills.Construction.TorusTransport.SupportFacts
end
