import YangMills.Construction.Continuum.MomentsOfComponentsThatFactoriseFarAway
import YangMills.Construction.Lattice.DoubleBlockContourPaths
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
noncomputable section
namespace YangMills.Construction.ClusterMoments
open TupleLists CanonicalDecomposition
theorem exists_finEquiv_get_eq_of_perm {α : Type*} {A B : List α} (h : A.Perm B) :
    ∃ e : Fin A.length ≃ Fin B.length, ∀ i, A.get i = B.get (e i) := by apply _root_.YangMills.Construction.PeriodicLattice.DoubleBlock.Contours.exists_equiv_get_of_perm <;> assumption
theorem eq_of_perm_of_isPermutationInvariant {σ : TestSpaces.SepTuple → ℝ}
    (hσ : WightmanReconstruction.IsPermutationInvariant σ)
    {A B : SeparatedTuples.SepTuple} (h : A.1.Perm B.1) : σ (ofList A) = σ (ofList B) := by
  obtain ⟨e, he⟩ := exists_finEquiv_get_eq_of_perm h.symm
  have hlen : A.1.length = B.1.length := h.length_eq
  rcases Nat.eq_zero_or_pos A.1.length with h0 | hpos
  · have hA : A = B := Subtype.ext (by
      have a0 := List.eq_nil_of_length_eq_zero h0
      have b0 := List.eq_nil_of_length_eq_zero (hlen ▸ h0)
      rw [a0, b0])
    rw [hA]
  · have key := hσ A.1.length hpos (ofList A).2 ((finCongr hlen).trans e)
    have hB : (⟨A.1.length, WightmanReconstruction.permuteComponents (ofList A).2
        ((finCongr hlen).trans e)⟩ : TestSpaces.SepTuple) = ofList B := by
      refine TestSpaces.sepTuple_ext _ _ hlen ?_
      intro k
      exact (he (Fin.cast hlen k)).symm
    rw [← hB]
    exact key.symm
section Moments
variable {Ξ : Type} [TopologicalSpace Ξ] [CompactSpace Ξ] [TopologicalSpace.MetrizableSpace Ξ]
  [MeasurableSpace Ξ] [BorelSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
  {σ : Ξ → TestSpaces.SepTuple → ℝ} {s : TestSpaces.SepTuple → ℝ}
def prefixProd (σ : Ξ → TestSpaces.SepTuple → ℝ) (Y : List TestSpaces.SepTuple) (k : ℕ)
    (ξ : Ξ) : ℝ :=
  ((Y.take k).map fun Z => σ ξ Z).prod
theorem continuous_prefixProd (hc : ∀ X, Continuous fun ξ => σ ξ X)
    (Y : List TestSpaces.SepTuple) (k : ℕ) : Continuous (prefixProd σ Y k) :=
  continuous_list_prod (Y.take k) fun Z _ => hc Z
theorem integrable_of_continuous_on_compact {f : Ξ → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
theorem prefixProd_succ (Y : List TestSpaces.SepTuple) {k : ℕ} (hk : k < Y.length) (ξ : Ξ) :
    prefixProd σ Y (k + 1) ξ = prefixProd σ Y k ξ * σ ξ Y[k] := by
  have h : Y.take (k + 1) = Y.take k ++ [Y[k]] := (List.take_append_getElem hk).symm
  simp only [prefixProd, h, List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
variable (hc : ∀ X, Continuous fun ξ => σ ξ X)
  (hsym : ∀ ξ, WightmanReconstruction.IsPermutationInvariant (σ ξ))
  (hmean : ∀ X, s X = ∫ ξ, σ ξ X ∂μ) (hfac : ClusterFactorises σ)
  (X : TestSpaces.SepTuple) (Y : List TestSpaces.SepTuple)
include hc hsym hfac in
theorem tendsto_partialLimit_cons {k : ℕ} (hk : k < Y.length)
    {vs : List InfiniteLattice.AmbientSpace}
    (hvs : IsAdmissibleShifts X Y (k + 1) vs)
    (ih : ∀ vs', IsAdmissibleShifts X Y k vs' → partialLimit X Y s k vs' =
      ∫ ξ, σ ξ (shiftedGlue X Y k vs') * prefixProd σ Y k ξ ∂μ) :
    Tendsto (fun v => partialLimit X Y s k (v :: vs)) SeparatedTuples.atInfinity
      (𝓝 (∫ ξ, σ ξ (shiftedGlue X Y (k + 1) vs) * prefixProd σ Y (k + 1) ξ ∂μ)) := by
  have hk' : k < (Y.map toList).length := by simpa using hk
  set W : SeparatedTuples.SepTuple := ⟨_, hvs.2.2⟩ with hWdef
  set T : SeparatedTuples.SepTuple := (Y.map toList)[k] with hTdef
  have hW : shiftedGlue X Y (k + 1) vs = ofList W := by
    have : SeparatedTuples.shiftedJuxt (toList X) (((Y.map toList).drop (k + 1)).zip vs) = W :=
      Subtype.ext (SeparatedTuples.shiftedJuxt_val hvs.2.2)
    simp only [shiftedGlue, this]
  have hT : ofList T = Y[k] := by simp [hTdef, ofList_toList]
  obtain ⟨b, hb, hbound⟩ := hfac W T
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_prefixProd hc Y k).continuousOn
  have hadm : ∀ᶠ v in SeparatedTuples.atInfinity, IsAdmissibleShifts X Y k (v :: vs) := by
    have := SeparatedTuples.eventually_cons_mem_iterLimitDomain (toList X) (Y.map toList)
      Set.univ hk' hvs
    rwa [SeparatedTuples.atInfinityWithin_univ] at this
  have hdef := SeparatedTuples.eventually_composable W T
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    ?_ (by simpa using hb.mul_const C))
  filter_upwards [hadm, hdef, hbound] with v hv hd hbv
  have hperm : ∀ ξ, σ ξ (shiftedGlue X Y k (v :: vs)) =
      σ ξ (ofList (SeparatedTuples.SepTuple.juxt W
        (SeparatedTuples.push (SeparatedTuples.translate v) T))) := fun ξ => by
    unfold shiftedGlue
    refine eq_of_perm_of_isPermutationInvariant (hsym ξ) ?_
    rw [SeparatedTuples.shiftedJuxt_val hv.2.2, SeparatedTuples.SepTuple.juxt_val hd]
    rw [List.drop_eq_getElem_cons hk', List.zip_cons_cons]
    simp only [SeparatedTuples.shiftedComponents, hWdef, List.flatMap_cons, List.append_assoc,
      ← hTdef]
    exact List.Perm.append_left _ List.perm_append_comm
  have i₁ : Integrable (fun ξ => σ ξ (shiftedGlue X Y k (v :: vs)) *
      prefixProd σ Y k ξ) μ :=
    integrable_of_continuous_on_compact ((hc _).mul (continuous_prefixProd hc Y k))
  have i₂ : Integrable (fun ξ => σ ξ (shiftedGlue X Y (k + 1) vs) *
      prefixProd σ Y (k + 1) ξ) μ :=
    integrable_of_continuous_on_compact ((hc _).mul (continuous_prefixProd hc Y (k + 1)))
  rw [ih _ hv, Real.dist_eq, ← integral_sub i₁ i₂]
  have hpt : ∀ ξ, ‖σ ξ (shiftedGlue X Y k (v :: vs)) * prefixProd σ Y k ξ -
      σ ξ (shiftedGlue X Y (k + 1) vs) * prefixProd σ Y (k + 1) ξ‖ ≤ b v * C := by
    intro ξ
    have he : σ ξ (shiftedGlue X Y k (v :: vs)) * prefixProd σ Y k ξ -
        σ ξ (shiftedGlue X Y (k + 1) vs) * prefixProd σ Y (k + 1) ξ =
        (σ ξ (ofList (SeparatedTuples.SepTuple.juxt W
          (SeparatedTuples.push (SeparatedTuples.translate v) T))) -
          σ ξ (ofList W) * σ ξ (ofList T)) * prefixProd σ Y k ξ := by
      rw [hperm, hW, prefixProd_succ Y hk, hT]
      ring
    rw [he, norm_mul]
    exact mul_le_mul (hbv ξ) (hC ξ (Set.mem_univ _)) (norm_nonneg _)
      ((abs_nonneg _).trans (hbv ξ))
  have := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hpt)
  simpa using this
include hc hsym hmean hfac in
theorem partialLimit_eq_integral {k : ℕ} (hk : k ≤ Y.length) :
    ∀ vs, IsAdmissibleShifts X Y k vs →
    partialLimit X Y s k vs =
      ∫ ξ, σ ξ (shiftedGlue X Y k vs) * prefixProd σ Y k ξ ∂μ := by
  induction k with
  | zero =>
    intro vs _
    rw [partialLimit_zero, hmean]
    simp [prefixProd]
  | succ k ih =>
    intro vs hvs
    have hlt : k < Y.length := hk
    have ht := tendsto_partialLimit_cons hc hsym hfac X Y hlt hvs (ih hlt.le)
    have : partialLimit X Y s (k + 1) vs =
        limUnder SeparatedTuples.atInfinity fun v => partialLimit X Y s k (v :: vs) := by
      simp only [partialLimit, SeparatedTuples.iterLimitValue,
        SeparatedTuples.atInfinityWithin_univ]
    rw [this]
    exact ht.limUnder_eq
include hc hsym hmean hfac in
theorem iteratedLimitsExist_of_cluster : IteratedLimitsExist X Y s := by
  intro k hk vs hvs
  have hk' : k < (Y.map toList).length := by simpa using hk
  have hadm := SeparatedTuples.eventually_cons_mem_iterLimitDomain (toList X) (Y.map toList)
    Set.univ hk' hvs
  rw [SeparatedTuples.atInfinityWithin_univ] at hadm
  obtain ⟨t, ht, hsub⟩ := mem_comap.1 hadm
  obtain ⟨a, ha⟩ := mem_atTop_sets.1 ht
  exact ⟨⟨a, fun v hv => hsub (ha _ hv)⟩, _, tendsto_partialLimit_cons hc hsym hfac X Y hk hvs
    (partialLimit_eq_integral hc hsym hmean hfac X Y hk.le)⟩
include hc hsym hmean hfac in
theorem integral_mul_prod_eq_iterLimit :
    ∫ ξ, σ ξ X * (Y.map fun Z => σ ξ Z).prod ∂μ = iterLimit X Y s := by
  have h := partialLimit_eq_integral hc hsym hmean hfac X Y le_rfl []
    ((isAdmissibleShifts_length_iff X Y []).2 rfl)
  rw [iterLimit, h, shiftedGlue_length]
  simp [prefixProd]
end Moments
theorem iteratedLimitIsMoment_holds : IteratedLimitIsMoment :=
  fun _ _ _ _ _ _ _ _ _ _ hc hsym hmean hfac X Y =>
  ⟨iteratedLimitsExist_of_cluster hc hsym hmean hfac X Y,
    integral_mul_prod_eq_iterLimit hc hsym hmean hfac X Y⟩
end YangMills.Construction.ClusterMoments
end
