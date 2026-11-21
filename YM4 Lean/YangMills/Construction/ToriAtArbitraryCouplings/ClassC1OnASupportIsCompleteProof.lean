import YangMills.Construction.Continuum.ExistenceOfAStableChoiceProof
import YangMills.Construction.PassageToTheLimit.SpacesOfFunctionsOfClassC1AreBanachSpacesProof
import YangMills.Construction.TestFunctions.RationalBoxFamilies
import YangMills.Construction.ToriAtArbitraryCouplings.ClassC1OnASupportIsComplete
import YangMills.Construction.Torus.CollinearQuadruplesProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace C1SupportComplete
private abbrev basisVec (i : Fin 4) : Fin 4 → ℝ := Pi.single i (1 : ℝ)
private def coordForm (c : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ∑ i, c i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i
private theorem coordForm_apply (c v : Fin 4 → ℝ) : coordForm c v = ∑ i, c i * v i := by
  simp [coordForm]
private theorem eq_coordForm (T : (Fin 4 → ℝ) →L[ℝ] ℝ) : T = coordForm fun i => T (basisVec i) := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = ∑ i, v i • basisVec i := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [coordForm_apply]
  conv_lhs => rw [hv]
  simp [map_sum, mul_comm]
private theorem norm_coordForm_sub_le {c d : Fin 4 → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i, |c i - d i| ≤ r) : ‖coordForm c - coordForm d‖ ≤ 4 * r := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hsum : (coordForm c - coordForm d) v = ∑ i, (c i - d i) * v i := by
    simp [coordForm_apply, sub_mul, Finset.sum_sub_distrib]
  rw [hsum]
  calc ‖∑ i, (c i - d i) * v i‖ ≤ ∑ i, ‖(c i - d i) * v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, r * ‖v‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]
        exact mul_le_mul (h i) (norm_le_pi_norm v i) (norm_nonneg _) hr
    _ = 4 * r * ‖v‖ := by simp; ring
private theorem partialDerivR4_eq_fderiv {φ : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ}
    (hφ : DifferentiableAt ℝ φ x) (i : Fin 4) :
    TestFunctions.partialDerivR4 i φ x = fderiv ℝ φ x (basisVec i) := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.C1Banach.partialDerivR4_eq_fderiv <;> assumption
private theorem continuous_partialDerivR4 {φ : (Fin 4 → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (i : Fin 4) :
    Continuous (TestFunctions.partialDerivR4 i φ) := by apply _root_.YangMills.Construction.DisjointTuples.StableChoice.continuous_partialDerivR4 <;> assumption
abbrev _root_.YangMills.SharedProofs.p32205 := @continuous_partialDerivR4
private theorem exists_unif_limit {X : Type*} (v : ℕ → X → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n → ∀ x, |v m x - v n x| < ε) :
    ∃ w : X → ℝ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ x, |v n x - w x| ≤ ε := by
  have hc : ∀ x, CauchySeq fun n => v n x := fun x => by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun m hm n hn => by simpa [Real.dist_eq] using hN m n hm hn x⟩
  choose w hw using fun x => cauchySeq_tendsto_of_complete (hc x)
  refine ⟨w, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn x => ?_⟩
  have ht : Tendsto (fun m => |v n x - v m x|) atTop (𝓝 |v n x - w x|) :=
    (tendsto_const_nhds.sub (hw x)).abs
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop N] with m hm
  exact (hN n m hn hm x).le
private theorem tendstoUniformly_of_eps {X : Type*} {v : ℕ → X → ℝ} {w : X → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ x, |v n x - w x| ≤ ε) :
    TendstoUniformly v w atTop := by
  refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop N] with n hn x
  have := hN n hn x
  rw [Real.dist_eq, abs_sub_comm]
  linarith
private theorem contDiff_of_unif_limit (F : ℕ → (Fin 4 → ℝ) → ℝ) (hF : ∀ n, ContDiff ℝ 1 (F n))
    (Φ : (Fin 4 → ℝ) → ℝ) (D : Fin 4 → (Fin 4 → ℝ) → ℝ)
    (hΦ : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ x, |F n x - Φ x| ≤ ε)
    (hD : ∀ i, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ x,
      |TestFunctions.partialDerivR4 i (F n) x - D i x| ≤ ε) :
    ContDiff ℝ 1 Φ ∧ ∀ i, TestFunctions.partialDerivR4 i Φ = D i := by
  have hd : ∀ n, Differentiable ℝ (F n) := fun n => (hF n).differentiable (by norm_num)
  have hform : ∀ n x, fderiv ℝ (F n) x =
      coordForm fun i => TestFunctions.partialDerivR4 i (F n) x := fun n x => by
    rw [eq_coordForm (fderiv ℝ (F n) x)]
    congr 1
    funext i
    rw [partialDerivR4_eq_fderiv (hd n x) i]
  have hDc : ∀ i, Continuous (D i) := fun i =>
    (tendstoUniformly_of_eps (hD i)).continuous
      (Frequently.of_forall fun n => continuous_partialDerivR4 (hF n) i)
  have hU : TendstoUniformly (fun n x => fderiv ℝ (F n) x) (fun x => coordForm fun i => D i x)
      atTop := by
    refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
    have hN : ∀ i, ∃ N : ℕ, ∀ n, N ≤ n → ∀ x,
        |TestFunctions.partialDerivR4 i (F n) x - D i x| ≤ ε / 8 := fun i =>
      hD i (ε / 8) (by positivity)
    choose N hN using hN
    filter_upwards [eventually_ge_atTop (∑ i, N i)] with n hn x
    have hb := norm_coordForm_sub_le (c := fun i => TestFunctions.partialDerivR4 i (F n) x)
      (d := fun i => D i x) (r := ε / 8) (by positivity) fun i =>
        hN i n ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hn) x
    rw [dist_comm, dist_eq_norm, hform n x]
    linarith
  have hpt : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (Φ x)) := fun x =>
    (tendstoUniformly_of_eps hΦ).tendsto_at x
  have hder : ∀ x, HasFDerivAt Φ (coordForm fun i => D i x) x :=
    hasFDerivAt_of_tendstoUniformly hU (fun n x => (hd n x).hasFDerivAt) hpt
  have hfd : fderiv ℝ Φ = fun x => coordForm fun i => D i x := funext fun x => (hder x).fderiv
  refine ⟨contDiff_one_iff_fderiv.2 ⟨fun x => (hder x).differentiableAt, ?_⟩, fun i => ?_⟩
  · rw [hfd]
    exact continuous_finsetSum _ fun i _ => (hDc i).smul continuous_const
  · funext x
    rw [partialDerivR4_eq_fderiv (hder x).differentiableAt, (hder x).fderiv, coordForm_apply]
    simp [Pi.single_apply]
variable {s : TorusSide} {E : Ambient}
private theorem nonempty_torusPoint : Nonempty (s.Point E) := ⟨s.ambientProj E 0⟩
private theorem pullback_contDiff {f : s.Point E → ℝ} (hf : f ∈ s.c1Set E) :
    ContDiff ℝ 1 (s.pullback f) := by
  cases E
  · exact hf
  · exact hf
private theorem mem_c1Set_of_pullback {f : s.Point E → ℝ} (hf : ContDiff ℝ 1 (s.pullback f)) :
    f ∈ s.c1Set E := by
  cases E
  · exact hf
  · exact hf
private theorem partialD_sub {f g : s.Point E → ℝ} (hf : f ∈ s.c1Set E)
    (hg : g ∈ s.c1Set E) (i : Fin 4) :
    s.partialD i E (f - g) =
      s.partialD i E f - s.partialD i E g := by
  symm
  refine s.eq_partialD_of_pullback i E _ _ ?_
  have hdf : Differentiable ℝ (s.pullback f) := (pullback_contDiff hf).differentiable (by norm_num)
  have hdg : Differentiable ℝ (s.pullback g) := (pullback_contDiff hg).differentiable (by norm_num)
  have hl : s.pullback (f - g) = s.pullback f - s.pullback g := rfl
  have hl' : s.pullback (s.partialD i E f - s.partialD i E g) =
      s.pullback (s.partialD i E f) - s.pullback (s.partialD i E g) := rfl
  rw [hl', s.pullback_partialD, s.pullback_partialD, hl]
  funext x
  rw [Pi.sub_apply, partialDerivR4_eq_fderiv (hdf x), partialDerivR4_eq_fderiv (hdg x),
    partialDerivR4_eq_fderiv ((hdf x).sub (hdg x)), fderiv_sub (hdf x) (hdg x)]
  rfl
private theorem isBoundedFun_on_torus (φ : s.Point .torus → ℝ) (hc : Continuous (s.pullback φ)) :
    TestFunctions.IsBoundedFun φ := by
  have hpos : 0 < s.length := by
    have hL : 0 < s.L := by
      have := s.admissible.2
      omega
    simp only [TorusSide.length, PeriodicLattice.torusSide]
    positivity
  have : Fact (0 < s.length) := ⟨hpos⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Fin 4 → ℝ)) (b := fun _ => s.length)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨C, fun p => ?_⟩
  have hex : ∀ i, ∃ t ∈ Set.Ico (0 : ℝ) (0 + s.length), (t : AddCircle s.length) = p i := fun i => by
    have himg := AddCircle.coe_image_Ico_eq s.length (0 : ℝ)
    have hp : p i ∈ (Set.univ : Set (AddCircle s.length)) := Set.mem_univ _
    rw [← himg] at hp
    obtain ⟨t, ht, hpt⟩ := hp
    exact ⟨t, ht, hpt⟩
  choose y hy hyp using hex
  have hproj : s.ambientProj .torus y = p := funext hyp
  have hin : y ∈ Set.Icc (0 : Fin 4 → ℝ) (fun _ => s.length) :=
    ⟨fun i => (hy i).1, fun i => by simpa using (hy i).2.le⟩
  have := hC y hin
  simpa [TorusSide.pullback, hproj] using this
private theorem isBoundedFun_of_compact {S : Set (Fin 4 → ℝ)} (hS : IsCompact S)
    {φ : (Fin 4 → ℝ) → ℝ} (hc : Continuous φ) (h0 : ∀ x, x ∉ S → φ x = 0) :
    TestFunctions.IsBoundedFun φ := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ S
  · exact (hC x hx).trans (le_max_left _ _)
  · simp [h0 x hx]
private theorem partialDerivR4_eq_zero_outside {S : Set (Fin 4 → ℝ)} (hS : IsClosed S)
    {φ : (Fin 4 → ℝ) → ℝ} (hd : Differentiable ℝ φ) (h0 : ∀ x, x ∉ S → φ x = 0) (i : Fin 4)
    (x : Fin 4 → ℝ) (hx : x ∉ S) : TestFunctions.partialDerivR4 i φ x = 0 := by
  have hev : φ =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hS.isOpen_compl.mem_nhds hx] with y hy
    exact h0 y hy
  rw [partialDerivR4_eq_fderiv (hd x), hev.fderiv_eq]
  simp
private theorem isCompact_of_mem_euclidSupportFamily {S : Set (Fin 4 → ℝ)}
    (hS : S ∈ euclidSupportFamily) : IsCompact S := by apply _root_.YangMills.Construction.TestFunctions.isCompact_of_mem_ratBoxUnions <;> assumption
abbrev _root_.YangMills.SharedProofs.p23763 := @isCompact_of_mem_euclidSupportFamily
private theorem isBoundedFun_and_partials {S : Set (Fin 4 → ℝ)} (hS : IsCompact S)
    {φ : (Fin 4 → ℝ) → ℝ} (hc : ContDiff ℝ 1 φ) (h0 : ∀ x, x ∉ S → φ x = 0) :
    TestFunctions.IsBoundedFun φ ∧ ∀ i, TestFunctions.IsBoundedFun (TestFunctions.partialDerivR4 i φ) :=
  ⟨isBoundedFun_of_compact hS hc.continuous h0, fun i =>
    isBoundedFun_of_compact hS (continuous_partialDerivR4 hc i)
      (partialDerivR4_eq_zero_outside hS.isClosed (hc.differentiable (by norm_num)) h0 i)⟩
private theorem isBoundedFun_of_mem {S : Set (s.Point E)} (hS : S ∈ s.supportFamily E)
    {φ : s.Point E → ℝ} (hφ : φ ∈ s.c1VanishingOutside E S) :
    TestFunctions.IsBoundedFun φ ∧ ∀ i, TestFunctions.IsBoundedFun (s.partialD i E φ) := by
  have hc := pullback_contDiff hφ.1
  cases E
  · refine ⟨isBoundedFun_on_torus φ hc.continuous, fun i => isBoundedFun_on_torus _ ?_⟩
    rw [s.pullback_partialD]
    exact continuous_partialDerivR4 hc i
  · exact isBoundedFun_and_partials (isCompact_of_mem_euclidSupportFamily hS) hc hφ.2
private theorem abs_le_uniformNorm {X : Type*} {w : X → ℝ} (hw : TestFunctions.IsBoundedFun w) (x : X) :
    |w x| ≤ TestFunctions.uniformNorm w := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.abs_le_uniformNorm <;> assumption
private theorem uniformNorm_le {X : Type*} [Nonempty X] {w : X → ℝ} {C : ℝ} (h : ∀ x, |w x| ≤ C) :
    TestFunctions.uniformNorm w ≤ C :=
  ciSup_le h
private theorem isBoundedFun_sub {X : Type*} {a b : X → ℝ} (ha : TestFunctions.IsBoundedFun a)
    (hb : TestFunctions.IsBoundedFun b) : TestFunctions.IsBoundedFun (a - b) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  exact ⟨A + B, fun x => (norm_sub_le _ _).trans (add_le_add (hA x) (hB x))⟩
theorem statement_holds : Statement := by
  intro s E S hS u hu hC
  have : Nonempty (s.Point E) := nonempty_torusPoint
  have hsub : ∀ m n i, s.partialD i E (u m - u n) =
      s.partialD i E (u m) - s.partialD i E (u n) := fun m n i =>
    partialD_sub (hu m).1 (hu n).1 i
  have hval : ∀ m n x, |u m x - u n x| ≤ s.c1NormOn E (u m - u n) := fun m n x => by
    rw [s.c1NormOn_eq_max]
    exact le_max_of_le_left (abs_le_uniformNorm
      (isBoundedFun_sub (isBoundedFun_of_mem hS (hu m)).1 (isBoundedFun_of_mem hS (hu n)).1) x)
  have hpar : ∀ i m n x, |s.partialD i E (u m) x - s.partialD i E (u n) x| ≤
      s.c1NormOn E (u m - u n) := fun i m n x => by
    rw [s.c1NormOn_eq_max]
    refine le_max_of_le_right (le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove i))
    rw [hsub m n i]
    exact abs_le_uniformNorm
      (isBoundedFun_sub ((isBoundedFun_of_mem hS (hu m)).2 i) ((isBoundedFun_of_mem hS (hu n)).2 i)) x
  obtain ⟨f, hf⟩ := exists_unif_limit u fun ε hε => by
    obtain ⟨N, hN⟩ := hC ε hε
    exact ⟨N, fun m n hm hn x => (hval m n x).trans_lt (hN m n hm hn)⟩
  have hgex : ∀ i, ∃ g : s.Point E → ℝ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ x,
      |s.partialD i E (u n) x - g x| ≤ ε := fun i =>
    exists_unif_limit (fun n => s.partialD i E (u n)) fun ε hε => by
      obtain ⟨N, hN⟩ := hC ε hε
      exact ⟨N, fun m n hm hn x => (hpar i m n x).trans_lt (hN m n hm hn)⟩
  choose g hg using hgex
  have hlim := contDiff_of_unif_limit (fun n => s.pullback (u n)) (fun n => pullback_contDiff (hu n).1)
    (s.pullback f) (fun i => s.pullback (g i))
    (fun ε hε => by
      obtain ⟨N, hN⟩ := hf ε hε
      exact ⟨N, fun n hn x => hN n hn _⟩)
    (fun i ε hε => by
      obtain ⟨N, hN⟩ := hg i ε hε
      refine ⟨N, fun n hn x => ?_⟩
      rw [← s.pullback_partialD]
      exact hN n hn _)
  have hfC : f ∈ s.c1Set E := mem_c1Set_of_pullback hlim.1
  have hfS : ∀ x, x ∉ S → f x = 0 := fun x hx => by
    by_contra hne
    obtain ⟨N, hN⟩ := hf (|f x| / 2) (by have := abs_pos.2 hne; positivity)
    have h := hN N le_rfl x
    rw [(hu N).2 x hx, zero_sub, abs_neg] at h
    have := abs_pos.2 hne
    linarith
  have hgf : ∀ i, g i = s.partialD i E f := fun i =>
    s.eq_partialD_of_pullback i E f (g i) (hlim.2 i).symm
  refine ⟨f, ⟨hfC, hfS⟩, fun ε hε => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hf (ε / 2) (by positivity)
  have hNi : ∀ i, ∃ N : ℕ, ∀ n, N ≤ n → ∀ x,
      |s.partialD i E (u n) x - g i x| ≤ ε / 2 := fun i => hg i _ (by positivity)
  choose N hN using hNi
  refine ⟨N₀ + ∑ i, N i, fun n hn => ?_⟩
  have hbound : s.c1NormOn E (u n - f) ≤ ε / 2 := by
    rw [s.c1NormOn_eq_max]
    refine max_le (uniformNorm_le fun x => hN₀ n (by omega) x) (ciSup_le fun i => ?_)
    rw [partialD_sub (hu n).1 hfC i, ← hgf i]
    refine uniformNorm_le fun x => hN i n ?_ x
    have := Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  linarith
end C1SupportComplete
end YangMills.Construction.ToriAtArbitraryCouplings
end
