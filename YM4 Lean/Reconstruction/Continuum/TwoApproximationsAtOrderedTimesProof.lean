import YangMills.Construction.Continuum.CutoffNearTheComplementOfAnOpenSet
import YangMills.Construction.Continuum.RulesOfThePartialDerivatives
import YangMills.Construction.Continuum.TensorsOfBumpsInTheNormProof
import YangMills.Construction.Continuum.TruncationOfSchwartzFunctionsAtInfinity
import Reconstruction.Continuum.TwoApproximationsAtOrderedTimes
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces.OrderedApprox
open BumpApprox Elementary WightmanReconstruction TestSpaceFacts
variable {q : ℕ}
theorem exists_seq_tendsto_of_forall_approx {P : (PointTuple q → ℂ) → Prop} {k : ℕ}
    {f : PointTuple q → ℂ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ g, P g ∧ weightedSeminorm k (f - g) ≤ ENNReal.ofReal ε) :
    ∃ fs : ℕ → PointTuple q → ℂ, (∀ n, P (fs n)) ∧
      Tendsto (fun n => weightedSeminorm k (f - fs n)) atTop (𝓝 0) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose fs hP hn using fun n : ℕ => h _ (hpos n)
  refine ⟨fs, hP, ?_⟩
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h0 := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hn
def timeUnitVec (j : Fin q) : PointTuple q := Pi.single j (Pi.single 3 1)
theorem timeCoord_sub_smul_timeUnitVec (x : PointTuple q) (j l : Fin q) (s : ℝ) :
    timeCoord (x - s • timeUnitVec j) l = timeCoord x l - (if l = j then s else 0) := by
  by_cases h : l = j
  · subst h
    simp [timeCoord, timeUnitVec]
  · simp [timeCoord, timeUnitVec, h]
theorem mem_closure_of_forall_time_shift {U : Set (PointTuple q)} (x : PointTuple q) (j : Fin q)
    (h : ∀ s : ℝ, 0 < s → x - s • timeUnitVec j ∈ U) : x ∈ closure U := by
  have hc : Continuous fun s : ℝ => x - s • timeUnitVec j :=
    continuous_const.sub (continuous_id.smul continuous_const)
  have ht : Tendsto (fun s : ℝ => x - s • timeUnitVec j) (𝓝[>] 0) (𝓝 x) := by
    have h0 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using h0
  exact mem_closure_of_tendsto ht
    (by filter_upwards [self_mem_nhdsWithin] with s hs using h s hs)
theorem mem_closure_interior_compl {x : PointTuple q} (hx : x ∉ increasingPositiveTimes q) :
    x ∈ closure (interior (increasingPositiveTimes q)ᶜ) := by
  by_cases hs : StrictMono (timeCoord x)
  · have hex : ∃ h : 0 < q, timeCoord x ⟨0, h⟩ ≤ 0 := by
      by_contra hne
      refine hx ⟨hs, fun h => ?_⟩
      by_contra h0
      exact hne ⟨h, not_lt.1 h0⟩
    obtain ⟨h, h0⟩ := hex
    have hU : IsOpen {y : PointTuple q | timeCoord y ⟨0, h⟩ < 0} :=
      isOpen_lt (continuous_timeCoord_apply _) continuous_const
    have hsub : {y : PointTuple q | timeCoord y ⟨0, h⟩ < 0} ⊆
        interior (increasingPositiveTimes q)ᶜ :=
      interior_maximal (fun y hy hyV => absurd (hyV.2 h) (not_lt.2 (le_of_lt hy))) hU
    refine closure_mono hsub (mem_closure_of_forall_time_shift x ⟨0, h⟩ fun s hs' => ?_)
    show timeCoord (x - s • timeUnitVec ⟨0, h⟩) ⟨0, h⟩ < 0
    rw [timeCoord_sub_smul_timeUnitVec]
    simp only [if_true]
    linarith
  · have hex : ∃ i j : Fin q, i < j ∧ timeCoord x j ≤ timeCoord x i := by
      by_contra hne
      refine hs fun i j hij => ?_
      by_contra h0
      exact hne ⟨i, j, hij, not_lt.1 h0⟩
    obtain ⟨i, j, hij, h0⟩ := hex
    have hU : IsOpen {y : PointTuple q | timeCoord y j < timeCoord y i} :=
      isOpen_lt (continuous_timeCoord_apply _) (continuous_timeCoord_apply _)
    have hsub : {y : PointTuple q | timeCoord y j < timeCoord y i} ⊆
        interior (increasingPositiveTimes q)ᶜ :=
      interior_maximal (fun y hy hyV => absurd (hyV.1 hij) (not_lt.2 (le_of_lt hy))) hU
    refine closure_mono hsub (mem_closure_of_forall_time_shift x j fun s hs' => ?_)
    show timeCoord (x - s • timeUnitVec j) j < timeCoord (x - s • timeUnitVec j) i
    rw [timeCoord_sub_smul_timeUnitVec, timeCoord_sub_smul_timeUnitVec]
    simp only [if_true, if_neg hij.ne]
    linarith
theorem vanishesToInfiniteOrderOff_of_mem (hR : DerivRules.Combined) {f : PointTuple q → ℂ}
    (hf : f ∈ schwartzOnIncreasingPositiveTimes q) :
    VanishesToInfiniteOrderOff f (increasingPositiveTimes q) := by
  obtain ⟨⟨hs, -⟩, hv⟩ := hf
  obtain ⟨-, hRc, -, -⟩ := hR
  have hrules := hRc q f hs
  refine ⟨hs, isOpen_increasingPositiveTimes q, fun x hx => ⟨hs, hv x hx, fun α => ?_⟩⟩
  have hzero := hrules.2.2.2.2.2.2.2 _ isOpen_interior
    (fun y hy => hv y (interior_subset hy)) α
  have hcont : Continuous (multiDeriv α f) := (hrules.2.2.1 α).continuous
  exact closure_minimal (t := {y | multiDeriv α f y = 0}) hzero
    (isClosed_eq hcont continuous_const) (mem_closure_interior_compl hx)
theorem compactlySupportedApprox_holds (hF : Elementary.BasicProperties)
    (hR : DerivRules.Combined)
    (htr : SchwartzTruncationApprox)
    (hcut : approxByCompactSuppInOpen) {k : ℕ} (hq : 0 < q) (hk : 0 < k) :
    CompactlySupportedApprox q k := by
  intro f hf
  obtain ⟨hO, -, hC, -, -⟩ := hF q hq
  have hflat := vanishesToInfiniteOrderOff_of_mem hR hf
  have hs := hf.1
  refine exists_seq_tendsto_of_forall_approx fun ε hε => ?_
  have ε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨f₁, hs₁, hc₁, hf₁, hn₁, -⟩ := htr q k hq hk _ f hs hflat _ ε2
  obtain ⟨f₂, hm₂, hn₂, -⟩ := hcut q k hq hk _ f₁ hc₁ hf₁ _ ε2
  refine ⟨f₂, hm₂, ?_⟩
  have hf₁' : f₁ ∈ schwartzSet q :=
    (hC Set.univ isOpen_univ f₁ ⟨hs₁, hc₁, Set.subset_univ _⟩).1
  have hf₂' : f₂ ∈ schwartzSet q := (hC _ (isOpen_increasingPositiveTimes q) f₂ hm₂).1
  have hsub : ∀ {a b : PointTuple q → ℂ}, a ∈ schwartzSet q → b ∈ schwartzSet q →
      a - b ∈ schwartzSet q := by
    intro a b ha hb
    have h := (hO.1 a ha b hb 1 (-1)).1.1
    have e : linComb 1 a (-1) b = a - b := by
      funext x
      simp [linComb, sub_eq_add_neg]
    rwa [e] at h
  have ha := hsub hs hf₁'
  have hb := hsub hf₁' hf₂'
  have htri := ((hO.1 _ ha _ hb 1 1).2.1 k k hk le_rfl).2.1
  have e : linComb 1 (f - f₁) 1 (f₁ - f₂) = f - f₂ := by
    funext x
    simp [linComb]
  rw [e] at htri
  simp only [norm_one, ENNReal.ofReal_one, one_mul] at htri
  calc weightedSeminorm k (f - f₂)
        ≤ weightedSeminorm k (f - f₁) + weightedSeminorm k (f₁ - f₂) := htri
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hn₁ hn₂
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add ε2.le ε2.le]
        congr 1
        ring
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem dist_le_of_forall_euclidNormVec_le {x z : PointTuple q} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i, TorusMetric.euclidNormVec (x i - z i) ≤ r) : dist x z ≤ r := by apply _root_.YangMills.Construction.TestSpaces.TensorApprox.dist_le_of_forall_euclidNormVec_le <;> assumption
theorem exists_isStandardBumpR4 (hB : BumpLemma) :
    ∃ b : (Fin 4 → ℝ) → ℝ, IsStandardBumpR4 b := by apply _root_.YangMills.Construction.TestSpaces.OffDiagonal.exists_standardBumpR4 <;> assumption
theorem timeCoord_add_two_mul_lt {V : Set (PointTuple q)} (hV : ∀ x ∈ V, StrictMono (timeCoord x))
    {z : PointTuple q} {δ : ℝ} (hδ : 0 < δ) (hz : ∀ x : PointTuple q, dist x z ≤ δ → x ∈ V)
    {i j : Fin q} (hij : i < j) :
    timeCoord z i + 2 * δ < timeCoord z j := by
  let s : Fin q → ℝ := fun l => if l = i then δ else if l = j then -δ else 0
  have hs : ∀ l, |s l| ≤ δ := by
    intro l
    simp only [s]
    split_ifs
    · rw [abs_of_pos hδ]
    · rw [abs_neg, abs_of_pos hδ]
    · simpa using hδ.le
  let x : PointTuple q := fun l μ => z l μ + (if μ = 3 then s l else 0)
  have hx : x ∈ V := hz x (by
    refine (dist_pi_le_iff hδ.le).2 fun l => (dist_pi_le_iff hδ.le).2 fun μ => ?_
    rw [Real.dist_eq]
    by_cases h : μ = 3
    · simpa [x, h] using hs l
    · simpa [x, h] using hδ.le)
  have hlt := hV x hx hij
  have e1 : timeCoord x i = timeCoord z i + δ := by simp [x, s, timeCoord]
  have e2 : timeCoord x j = timeCoord z j - δ := by
    simp [x, s, timeCoord, hij.ne', sub_eq_add_neg]
  rw [e1, e2] at hlt
  linarith
theorem isTimeOrdered_of_time_separation {X : Fin q → (Fin 4 → ℝ) → ℝ}
    (hX : X ∈ disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) q) {z : PointTuple q}
    {δ r : ℝ} (hq : 0 < q) (hδ : 0 < δ) (hrδ : r < δ)
    (hgap : ∀ i j : Fin q, i < j → timeCoord z i + 2 * δ < timeCoord z j)
    (hsupp : ∀ i, tsupport (X i) ⊆ {u | |u 3 - z i 3| ≤ r}) : IsTimeOrdered X := by
  let c : Fin (q + 1) → ℝ := fun l =>
    if h : l.val < q then timeCoord z ⟨l.val, h⟩ - δ else timeCoord z ⟨q - 1, by omega⟩ + δ
  have hcast : ∀ i : Fin q, c i.castSucc = timeCoord z i - δ := by
    intro i
    simp [c]
  have hsucc : ∀ i : Fin q, timeCoord z i + δ ≤ c i.succ := by
    intro i
    by_cases h : i.val + 1 < q
    · have e1 : c i.succ = timeCoord z ⟨i.val + 1, h⟩ - δ := by simp [c, h]
      have e2 := hgap i ⟨i.val + 1, h⟩ (by simp [Fin.lt_def])
      rw [e1]
      linarith
    · have hi : (⟨q - 1, by omega⟩ : Fin q) = i := Fin.ext (by simp; omega)
      have e1 : c i.succ = timeCoord z ⟨q - 1, by omega⟩ + δ := by simp [c, h]
      rw [e1, hi]
  refine ⟨hX, c, Fin.strictMono_iff_lt_succ.2 fun i => ?_, fun i u hu => ?_⟩
  · rw [hcast]
    linarith [hsucc i]
  · have hu' : |u 3 - z i 3| ≤ r := hsupp i hu
    have hb := abs_le.1 hu'
    have h1 := hcast i
    have h2 := hsucc i
    have ht : timeCoord z i = z i 3 := rfl
    refine ⟨?_, ?_⟩
    · rw [h1, ht]
      linarith [hb.1]
    · rw [ht] at h2
      linarith [hb.2]
theorem rescaledBumps_mem_smoothDisjointTuples {V : Set (PointTuple q)} {O : Set (Fin 4 → ℝ)}
    (hV : ∀ x ∈ V, (∀ i, x i ∈ O) ∧ StrictMono (timeCoord x))
    {b : (Fin 4 → ℝ) → ℝ} {r : ℝ} {z : PointTuple q} (hr : 0 ≤ r)
    (hz : ∀ x : PointTuple q, (∀ i, TorusMetric.euclidNormVec (x i - z i) ≤ r) → x ∈ V)
    (hs : ∀ v, rescaledBump b r v ∈ (smoothCompactSupp Set.univ : Set ((Fin 4 → ℝ) → ℝ)) ∧
      tsupport (rescaledBump b r v) ⊆ {u | TorusMetric.euclidNormVec (u - v) ≤ r}) :
    (fun i => rescaledBump b r (z i)) ∈ smoothDisjointTuples O q := by
  have hself : ∀ i, TorusMetric.euclidNormVec (z i - z i) ≤ r := by
    intro i
    simpa [TorusMetric.euclidNormVec] using hr
  have hO : ∀ i, tsupport (rescaledBump b r (z i)) ⊆ O := by
    intro i u hu
    have hu' : TorusMetric.euclidNormVec (u - z i) ≤ r := (hs (z i)).2 hu
    have hx : Function.update z i u ∈ V := by
      apply hz
      intro l
      by_cases h : l = i
      · subst h
        simpa using hu'
      · simpa [Function.update_of_ne h] using hself l
    simpa using (hV _ hx).1 i
  have hsm : ∀ i, rescaledBump b r (z i) ∈
      (smoothCompactSupp O : Set ((Fin 4 → ℝ) → ℝ)) :=
    fun i => ⟨(hs (z i)).1.1, (hs (z i)).1.2.1, hO i⟩
  refine ⟨⟨fun i => ⟨(hsm i).1.of_le ?_, (hsm i).2.1, hO i⟩, ?_⟩, hsm⟩
  · exact_mod_cast le_top
  · intro i i' hne
    rw [Set.disjoint_left]
    intro u hu hu'
    have hu1 : TorusMetric.euclidNormVec (u - z i) ≤ r := (hs (z i)).2 hu
    have hu2 : TorusMetric.euclidNormVec (u - z i') ≤ r := (hs (z i')).2 hu'
    have hx : Function.update (Function.update z i u) i' u ∈ V := by
      apply hz
      intro l
      by_cases h' : l = i'
      · subst h'
        simpa using hu2
      · by_cases h : l = i
        · subst h
          simpa [Function.update_of_ne h'] using hu1
        · simpa [Function.update_of_ne h', Function.update_of_ne h] using hself l
    have hinj : Function.Injective (timeCoord (Function.update (Function.update z i u) i' u)) :=
      (hV _ hx).2.injective
    exact hne (hinj (by simp [timeCoord, Function.update_of_ne hne]))
theorem tensorApprox_of_forall_mem (hF : Elementary.BasicProperties)
    (hB : BumpLemma) {k : ℕ} (hq : 0 < q) (hk : 0 < k)
    {V : Set (PointTuple q)} {O : Set (Fin 4 → ℝ)} (hVo : IsOpen V) (hOo : IsOpen O)
    (hV : ∀ x ∈ V, (∀ i, x i ∈ O) ∧ StrictMono (timeCoord x)) : TensorApprox V O k := by
  intro f hf
  obtain ⟨hfs, hfc, hfV⟩ := hf
  obtain ⟨-, -, hCS, hST, -⟩ := hF q hq
  obtain ⟨-, -, hbump, happ⟩ := hB q hq
  obtain ⟨b, hb⟩ := exists_isStandardBumpR4 hB
  have hKc : IsCompact (tsupport f) := hfc
  obtain ⟨δ, hδ, hδV⟩ := hKc.exists_cthickening_subset_open hVo hfV
  have hCc : IsCompact (Metric.cthickening δ (tsupport f)) := hKc.cthickening
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧
      ∀ x ∈ Metric.cthickening δ (tsupport f), tupleNorm x ≤ R := by
    have hc : Continuous (tupleNorm : PointTuple q → ℝ) := by
      unfold tupleNorm
      fun_prop
    obtain ⟨B, hB'⟩ := (hCc.image hc).bddAbove
    exact ⟨max B 0, le_max_right _ _,
      fun x hx => (hB' ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩
  have hW : 0 < (1 + R ^ 2) ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨Metric.cthickening δ (tsupport f), hCc, hδV, ?_⟩
  refine exists_seq_tendsto_of_forall_approx
    (P := fun g => tsupport g ⊆ Metric.cthickening δ (tsupport f) ∧
      IsOrderedTensorCombination O g) fun ε hε => ?_
  obtain ⟨ε₁, hε₁, hap⟩ := happ f ⟨hfs, hfc, Set.subset_univ _⟩ k
    (ε / (1 + R ^ 2) ^ ((k : ℝ) / 2)) (div_pos hε hW)
  obtain ⟨r, hr, hr₁, hrδ⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ ε₁ ∧ r < δ :=
    ⟨min ε₁ (δ / 2), lt_min hε₁ (half_pos hδ), min_le_left _ _,
      (min_le_right _ _).trans_lt (half_lt_self hδ)⟩
  obtain ⟨a, -, hfin, hnear⟩ := hap b hb r hr hr₁
  have hs := fun v => hbump b hb r v hr
  have hsum : ∀ x, gridApprox b f r a x = ∑ z ∈ hfin.toFinset, gridSummand b f r a z x := by
    intro x
    have h0 : gridApprox b f r a = ∑ z ∈ hfin.toFinset, gridSummand b f r a z :=
      finsum_mem_eq_sum _ hfin
    rw [h0, Finset.sum_apply]
  have hTK : ∀ z ∈ hfin.toFinset, z ∈ tsupport f := by
    intro z hz
    have hz' : z ∈ latticeGrid q a ∧ gridSummand b f r a z ≠ 0 := hfin.mem_toFinset.1 hz
    refine subset_tsupport _ ?_
    intro h0
    apply hz'.2
    funext x
    simp [gridSummand, h0]
  have hball : ∀ z ∈ hfin.toFinset, ∀ x : PointTuple q, dist x z ≤ δ → x ∈ V := fun z hz x hx =>
    hδV (Metric.mem_cthickening_of_dist_le x z δ _ (hTK z hz) hx)
  have hsep : ∀ z ∈ hfin.toFinset,
      (fun i => rescaledBump b r (z i)) ∈ smoothDisjointTuples O q := fun z hz =>
    rescaledBumps_mem_smoothDisjointTuples hV hr.le
      (fun x hx => hball z hz x ((dist_le_of_forall_euclidNormVec_le hr.le hx).trans hrδ.le)) hs
  have hord : ∀ z ∈ hfin.toFinset, IsTimeOrdered fun i => rescaledBump b r (z i) := by
    intro z hz
    refine isTimeOrdered_of_time_separation (z := z) (δ := δ) (r := r)
      ⟨fun i => ⟨((hsep z hz).1.1 i).1, ((hsep z hz).1.1 i).2.1, Set.subset_univ _⟩,
        (hsep z hz).1.2⟩ hq hδ hrδ
      (fun i j hij => timeCoord_add_two_mul_lt (fun x hx => (hV x hx).2) hδ (hball z hz) hij)
      fun i u hu => ?_
    exact (abs_apply_le_euclidNormVec (u - z i) 3).trans ((hs (z i)).2 hu)
  have hterm : ∀ z ∈ hfin.toFinset, ContDiff ℝ ∞ (gridSummand b f r a z) := by
    intro z hz
    have hc : ContDiff ℝ ∞ (tensorProdComplex fun i => rescaledBump b r (z i)) :=
      (((hST O hOo _ (hsep z hz).1).2 (hsep z hz).2).2.1).1.1
    exact contDiff_const.mul hc
  have hsmooth : ContDiff ℝ ∞ (gridApprox b f r a) := by
    have he' : gridApprox b f r a = fun x => ∑ z ∈ hfin.toFinset, gridSummand b f r a z x :=
      funext hsum
    rw [he']
    exact ContDiff.sum hterm
  have hRx : ∀ x, x ∉ Metric.cthickening δ (tsupport f) → gridApprox b f r a x = 0 := by
    intro x hx
    rw [hsum]
    refine Finset.sum_eq_zero fun z hz => ?_
    have hex : ∃ i, ¬ TorusMetric.euclidNormVec (x i - z i) ≤ r := by
      by_contra hall
      exact hx (Metric.mem_cthickening_of_dist_le x z δ _ (hTK z hz)
        ((dist_le_of_forall_euclidNormVec_le hr.le
          fun i => by_contra fun hi => hall ⟨i, hi⟩).trans hrδ.le))
    obtain ⟨i, hi⟩ := hex
    have hzero : rescaledBump b r (z i) (x i) = 0 :=
      image_eq_zero_of_notMem_tsupport fun hm => hi ((hs (z i)).2 hm)
    have ht : tensorProd (fun i => rescaledBump b r (z i)) x = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hzero
    simp [gridSummand, ht]
  have hvan : ∀ x, x ∉ Metric.cthickening δ (tsupport f) → (f - gridApprox b f r a) x = 0 := by
    intro x hx
    have hfx : f x = 0 :=
      image_eq_zero_of_notMem_tsupport fun hm => hx (Metric.self_subset_cthickening _ hm)
    simp [hfx, hRx x hx]
  have hD : f - gridApprox b f r a ∈
      (smoothCompactSupp Set.univ : Set (PointTuple q → ℂ)) :=
    ⟨hfs.sub hsmooth, HasCompactSupport.intro hCc hvan, Set.subset_univ _⟩
  have hnorm : weightedSeminorm k (f - gridApprox b f r a) ≤ ENNReal.ofReal ε := by
    have hbd := (hCS Set.univ isOpen_univ _ hD).2.2.2 R hR0
      (fun x hx => hvan x fun hm => hx (hR x hm)) k hk
    calc weightedSeminorm k (f - gridApprox b f r a)
        ≤ ENNReal.ofReal ((1 + R ^ 2) ^ ((k : ℝ) / 2)) *
            derivSupNorm k (f - gridApprox b f r a) := hbd
      _ ≤ ENNReal.ofReal ((1 + R ^ 2) ^ ((k : ℝ) / 2)) *
            ENNReal.ofReal (ε / (1 + R ^ 2) ^ ((k : ℝ) / 2)) := by gcongr
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_mul hW.le, mul_div_cancel₀ _ hW.ne']
  let pt : Fin hfin.toFinset.card → PointTuple q := fun i => (hfin.toFinset.equivFin.symm i).1
  have hpt : ∀ i, pt i ∈ hfin.toFinset := fun i => (hfin.toFinset.equivFin.symm i).2
  let c : Fin hfin.toFinset.card → ℂ := fun i => ((a ^ (4 * q) : ℝ) : ℂ) * f (pt i)
  let X : Fin hfin.toFinset.card → Fin q → (Fin 4 → ℝ) → ℝ :=
    fun i l => rescaledBump b r (pt i l)
  have hcomb : gridApprox b f r a = tensorCombination c X := by
    funext x
    rw [hsum]
    show _ = ∑ ι, c ι * ((tensorProd (X ι) x : ℝ) : ℂ)
    rw [← Finset.sum_coe_sort hfin.toFinset fun z => gridSummand b f r a z x,
      ← Equiv.sum_comp hfin.toFinset.equivFin.symm]
    rfl
  refine ⟨gridApprox b f r a, ⟨?_, hfin.toFinset.card, c, X,
    fun ι => ⟨hsep _ (hpt ι), hord _ (hpt ι)⟩, hcomb⟩, hnorm⟩
  refine closure_minimal (fun x hx => ?_) Metric.isClosed_cthickening
  by_contra hC
  exact hx (hRx x hC)
theorem statement_of_ingredients (hF : Elementary.BasicProperties) (hR : DerivRules.Combined)
    (hB : BumpLemma)
    (htr : SchwartzTruncationApprox)
    (hcut : approxByCompactSuppInOpen) :
    OrderedApprox.Statement := by
  intro q k hq hk
  exact ⟨compactlySupportedApprox_holds hF hR htr hcut hq hk,
    tensorApprox_of_forall_mem hF hB hq hk (isOpen_increasingTimes q) isOpen_univ
      fun x hx => ⟨fun _ => trivial, hx⟩,
    tensorApprox_of_forall_mem hF hB hq hk (isOpen_increasingPositiveTimes q)
      (isOpen_lt continuous_const (continuous_apply 3))
      fun x hx => ⟨fun i => (increasingPositiveTimes_subset_positiveTimeLocus q hx).2 i, hx.1⟩⟩
end YangMills.Construction.TestSpaces.OrderedApprox
end
