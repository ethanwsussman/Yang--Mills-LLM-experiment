import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumps
import YangMills.Construction.Continuum.DistributionsOffTheDiagonalsAndTranslationsInSpace
import YangMills.Construction.Continuum.FirstFactsOnTheTestSpaces
import YangMills.Construction.Continuum.TensorBoundsIntegrationBoundsAndDensity
import YangMills.Construction.Continuum.TensorsOfTuplesAreTestFunctionsOffTheDiagonals
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces.OffDiagonal
open BumpApprox
variable {n : ℕ}
theorem derivSupNorm_mono {p p' : ℕ} (hpp : p ≤ p') (f : PointTuple n → ℂ) :
    derivSupNorm p f ≤ derivSupNorm p' f := by
  unfold derivSupNorm
  refine iSup_mono fun x => iSup_mono fun α => ?_
  exact iSup_le fun hα => le_iSup_of_le (hα.trans hpp) le_rfl
theorem smoothCompactSupp_mono {U V : Set (PointTuple n)} (hUV : U ⊆ V) {f : PointTuple n → ℂ}
    (hf : f ∈ (smoothCompactSupp U : Set (PointTuple n → ℂ))) :
    f ∈ (smoothCompactSupp V : Set (PointTuple n → ℂ)) :=
  ⟨hf.1, hf.2.1, hf.2.2.trans hUV⟩
theorem smoothCompactSupp_linComb_mem {U : Set (PointTuple n)} {f g : PointTuple n → ℂ}
    (hf : f ∈ (smoothCompactSupp U : Set (PointTuple n → ℂ)))
    (hg : g ∈ (smoothCompactSupp U : Set (PointTuple n → ℂ))) (a b : ℂ) :
    a • f + b • g ∈ (smoothCompactSupp U : Set (PointTuple n → ℂ)) := by
  obtain ⟨f1, f2, f3⟩ := hf
  obtain ⟨g1, g2, g3⟩ := hg
  refine ⟨(f1.const_smul a).add (g1.const_smul b), (f2.smul_left).add (g2.smul_left), ?_⟩
  have hsub : Function.support (a • f + b • g) ⊆ tsupport f ∪ tsupport g := by
    intro x hx
    by_contra hc
    rw [Set.mem_union, not_or] at hc
    apply hx
    simp [image_eq_zero_of_notMem_tsupport hc.1, image_eq_zero_of_notMem_tsupport hc.2]
  exact (closure_minimal hsub ((isClosed_tsupport f).union (isClosed_tsupport g))).trans
    (Set.union_subset f3 g3)
theorem smoothCompactSupp_zero_mem (U : Set (PointTuple n)) :
    (0 : PointTuple n → ℂ) ∈ (smoothCompactSupp U : Set (PointTuple n → ℂ)) := by
  refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
  rw [tsupport_zero]
  exact Set.empty_subset _
theorem linear_vanishes_on_finset_sum {V U : Set (PointTuple n)} (hUV : U ⊆ V)
    {L : TestFnOn V → ℂ} (hL : IsTestFnLinear L)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (e : ι → PointTuple n → ℂ)
    (he : ∀ i ∈ s, e i ∈ (smoothCompactSupp U : Set (PointTuple n → ℂ)))
    (hz : ∀ i ∈ s, ∀ hm : e i ∈ (smoothCompactSupp V : Set (PointTuple n → ℂ)), L ⟨e i, hm⟩ = 0) :
    (∑ i ∈ s, c i • e i) ∈ (smoothCompactSupp U : Set (PointTuple n → ℂ)) ∧
      ∀ hm : (∑ i ∈ s, c i • e i) ∈ (smoothCompactSupp V : Set (PointTuple n → ℂ)),
        L ⟨_, hm⟩ = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using smoothCompactSupp_zero_mem U, fun hm => ?_⟩
    have := hL 0 0 ⟨_, hm⟩ ⟨_, hm⟩ ⟨_, hm⟩ (by simp)
    simpa using this
  | insert i s hi ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun l hl => he l (Finset.mem_insert_of_mem hl))
      (fun l hl => hz l (Finset.mem_insert_of_mem hl))
    have hei := he i (Finset.mem_insert_self i s)
    have heq : (∑ l ∈ insert i s, c l • e l) = c i • e i + (1 : ℂ) • ∑ l ∈ s, c l • e l := by
      rw [Finset.sum_insert hi, one_smul]
    refine ⟨by rw [heq]; exact smoothCompactSupp_linComb_mem hei ih1 _ _, fun hm => ?_⟩
    have hei' := smoothCompactSupp_mono hUV hei
    have hs' := smoothCompactSupp_mono hUV ih1
    rw [hL (c i) 1 ⟨_, hei'⟩ ⟨_, hs'⟩ ⟨_, hm⟩ heq, hz i (Finset.mem_insert_self i s) hei', ih2 hs']
    simp
theorem dist_le_of_euclidNormVec_le {u v : Fin 4 → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (huv : TorusMetric.euclidNormVec (u - v) ≤ r) : dist u v ≤ r := by
  refine (dist_pi_le_iff hr).2 fun μ => ?_
  rw [Real.dist_eq]
  refine le_trans ?_ huv
  unfold TorusMetric.euclidNormVec
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun μ => (u - v) μ ^ 2) (fun μ _ => sq_nonneg _)
    (Finset.mem_univ μ)
theorem exists_standardBumpR4 (hB : BumpLemma) :
    ∃ b : (Fin 4 → ℝ) → ℝ, IsStandardBumpR4 b := by
  obtain ⟨j, hj⟩ := (hB 1 one_pos).1
  refine ⟨fun u => j fun _ => u, ?_⟩
  have hsame : (fun x : PointTuple 1 => j fun _ => x 0) = j := by
    funext x
    congr 1
    funext i
    rw [Subsingleton.elim i 0]
  show IsStandardBump (fun x : PointTuple 1 => j fun _ => x 0)
  rw [hsame]
  exact hj
theorem exists_small_remainder_of_tensor_vanishing (hF : Elementary.BasicProperties)
    (hB : BumpLemma) (hn : 0 < n) (f : PointTuple n → ℂ)
    (hf : f ∈ (smoothCompactSupp (distinctLocus n) : Set (PointTuple n → ℂ))) :
    ∃ K : Set (PointTuple n), IsCompact K ∧ K ⊆ distinctLocus n ∧
      ∀ (p : ℕ) (ϵ : ℝ), 0 < ϵ → ∀ L : TestFnOn (distinctLocus n) → ℂ,
        IsTestFnLinear L →
        (∀ X : SepTupleOfCard n, HasSmoothComponents Set.univ X.1 →
          ∀ hm : tensorProdComplex X.1 ∈
            (smoothCompactSupp (distinctLocus n) : Set (PointTuple n → ℂ)),
            L ⟨_, hm⟩ = 0) →
        ∃ g : TestFnOn (distinctLocus n), tsupport g.1 ⊆ K ∧
          derivSupNorm p g.1 ≤ ENNReal.ofReal ϵ ∧ L ⟨f, hf⟩ = L g := by
  obtain ⟨-, hopen, -, hST, -⟩ := hF n hn
  obtain ⟨-, -, hbump, happ⟩ := hB n hn
  obtain ⟨b, hb⟩ := exists_standardBumpR4 hB
  have hVo : IsOpen (distinctLocus n) := hopen.1
  obtain ⟨hfs, hfc, hfV⟩ := id hf
  have hK : IsCompact (tsupport f) := hfc
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hVo hfV
  refine ⟨Metric.cthickening δ (tsupport f), hK.cthickening, hδV, ?_⟩
  intro p ϵ hϵ L hL hL0
  obtain ⟨ε₁, hε₁, hap⟩ := happ f ⟨hfs, hfc, Set.subset_univ _⟩ p ϵ hϵ
  obtain ⟨ε, hε, hεε₁, hεδ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₁ ∧ ε ≤ δ / 3 :=
    ⟨min ε₁ (δ / 3), lt_min hε₁ (by positivity), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨h, -, hfin, hnear⟩ := hap b hb ε hε hεε₁
  have hsep : ∀ z ∈ tsupport f, ∀ i i', i ≠ i' → δ < dist (z i) (z i') := by
    intro z hz i i' hne
    by_contra hc
    rw [not_lt] at hc
    have hy : dist (Function.update z i (z i')) z ≤ δ := by
      refine (dist_pi_le_iff hδ.le).2 fun l => ?_
      by_cases hl : l = i
      · subst hl
        simpa [dist_comm] using hc
      · simp [Function.update_of_ne hl, hδ.le]
    have hmem : Function.update z i (z i') ∈ distinctLocus n :=
      hδV (Metric.closedBall_subset_cthickening hz δ (Metric.mem_closedBall.2 hy))
    have hinj : Function.Injective (Function.update z i (z i')) := hmem
    exact hne (hinj (by simp [Function.update_of_ne hne.symm]))
  have hbz : ∀ v, rescaledBump b ε v ∈ (smoothCompactSupp Set.univ : Set ((Fin 4 → ℝ) → ℝ)) ∧
      tsupport (rescaledBump b ε v) ⊆ {u | TorusMetric.euclidNormVec (u - v) ≤ ε} :=
    fun v => hbump b hb ε v hε
  have hnear' : ∀ v u, u ∈ tsupport (rescaledBump b ε v) → dist u v ≤ ε := fun v u hu =>
    dist_le_of_euclidNormVec_le hε.le ((hbz v).2 hu)
  have hsmooth : ∀ z : PointTuple n, HasSmoothComponents Set.univ fun i => rescaledBump b ε (z i) :=
    fun z i => (hbz (z i)).1
  have htuple : ∀ z ∈ tsupport f,
      (fun i => rescaledBump b ε (z i)) ∈ disjointSupportTuples Set.univ n := by
    intro z hz
    refine ⟨fun i => ⟨(hbz (z i)).1.1.of_le ?_, (hbz (z i)).1.2.1, Set.subset_univ _⟩, ?_⟩
    · exact_mod_cast le_top
    · intro i i' hne
      rw [Set.disjoint_left]
      intro u hu hu'
      have h1 := hnear' _ _ hu
      have h2 := hnear' _ _ hu'
      have h3 := hsep z hz i i' hne
      have h4 := dist_triangle_left (z i) (z i') u
      linarith
  let c : PointTuple n → ℂ := fun z => ((h ^ (4 * n) : ℝ) : ℂ) * f z
  let e : PointTuple n → PointTuple n → ℂ := fun z x =>
    ((tensorProd (fun i => rescaledBump b ε (z i)) x : ℝ) : ℂ)
  have hterm : ∀ z, gridSummand b f ε h z = c z • e z := fun z => rfl
  have hsum : gridApprox b f ε h = ∑ z ∈ hfin.toFinset, c z • e z := by
    unfold gridApprox
    rw [finsum_mem_eq_sum _ hfin]
    exact Finset.sum_congr rfl fun z _ => hterm z
  have hzK : ∀ z ∈ hfin.toFinset, z ∈ tsupport f := by
    intro z hz
    have hz' : gridSummand b f ε h z ≠ 0 := ((Set.Finite.mem_toFinset hfin).1 hz).2
    apply subset_tsupport
    intro h0
    apply hz'
    rw [hterm]
    simp [c, h0]
  have hemem : ∀ z ∈ tsupport f, e z ∈
      (smoothCompactSupp (Metric.cthickening δ (tsupport f)) : Set (PointTuple n → ℂ)) := by
    intro z hz
    obtain ⟨hc, hcs, -⟩ := ((hST Set.univ isOpen_univ _ (htuple z hz)).2 (hsmooth z)).1
    refine ⟨Complex.ofRealCLM.contDiff.comp hc,
      hcs.comp_left (g := Complex.ofRealCLM) (by simp), ?_⟩
    have hsub : Function.support (e z) ⊆ Metric.closedBall z ε := by
      intro x hx
      have hx' : tensorProd (fun i => rescaledBump b ε (z i)) x ≠ 0 := by
        intro h0
        apply hx
        simp [e, h0]
      have hprod := Finset.prod_ne_zero_iff.1 hx'
      refine Metric.mem_closedBall.2 ((dist_pi_le_iff hε.le).2 fun i => ?_)
      exact hnear' _ _ (subset_tsupport _ (hprod i (Finset.mem_univ i)))
    refine (closure_minimal hsub Metric.isClosed_closedBall).trans ?_
    refine (Metric.closedBall_subset_closedBall ?_).trans
      (Metric.closedBall_subset_cthickening hz δ)
    linarith
  have hL0' : ∀ z ∈ hfin.toFinset, ∀ hz : e z ∈
      (smoothCompactSupp (distinctLocus n) : Set (PointTuple n → ℂ)), L ⟨e z, hz⟩ = 0 :=
    fun z hz hm => hL0 ⟨_, htuple z (hzK z hz)⟩ (hsmooth z) hm
  obtain ⟨hSU, hS0⟩ := linear_vanishes_on_finset_sum hδV hL hfin.toFinset c e
    (fun z hz => hemem z (hzK z hz)) hL0'
  have hfU : f ∈ (smoothCompactSupp (Metric.cthickening δ (tsupport f)) :
      Set (PointTuple n → ℂ)) :=
    ⟨hfs, hfc, Metric.self_subset_cthickening _⟩
  set S : PointTuple n → ℂ := ∑ z ∈ hfin.toFinset, c z • e z with hSdef
  have hdiff : f - S = (1 : ℂ) • f + (-1 : ℂ) • S := by
    simp [sub_eq_add_neg]
  have hgU : f - S ∈ (smoothCompactSupp (Metric.cthickening δ (tsupport f)) :
      Set (PointTuple n → ℂ)) := by
    rw [hdiff]
    exact smoothCompactSupp_linComb_mem hfU hSU _ _
  have hgV := smoothCompactSupp_mono hδV hgU
  have hSV := smoothCompactSupp_mono hδV hSU
  refine ⟨⟨_, hgV⟩, hgU.2.2, ?_, ?_⟩
  · rw [hsum] at hnear
    exact hnear
  · have heq : f = (1 : ℂ) • (f - S) + (1 : ℂ) • S := by simp
    rw [hL 1 1 ⟨_, hgV⟩ ⟨_, hSV⟩ ⟨f, hf⟩ heq, hS0 hSV]
    simp
theorem distribDeterminedByTensors (hF : Elementary.BasicProperties)
    (hB : BumpLemma) (hn : 0 < n) : DistribDeterminedByTensors n := by
  intro u₁ u₂ hu₁ hu₂ hval
  let L : TestFnOn (distinctLocus n) → ℂ := fun χ => u₁ χ - u₂ χ
  have hL : IsTestFnLinear L := by
    intro a b f g χ hχ
    simp only [L]
    rw [hu₁.1 a b f g χ hχ, hu₂.1 a b f g χ hχ]
    ring
  have hL0 : ∀ X : SepTupleOfCard n, HasSmoothComponents Set.univ X.1 →
      ∀ hm : tensorProdComplex X.1 ∈
        (smoothCompactSupp (distinctLocus n) : Set (PointTuple n → ℂ)), L ⟨_, hm⟩ = 0 :=
    fun X hX hm => sub_eq_zero.2 (hval X hX hm)
  funext χ
  obtain ⟨f, hf⟩ := χ
  obtain ⟨K, hK, hKV, hnear⟩ := exists_small_remainder_of_tensor_vanishing hF hB hn f hf
  obtain ⟨p₁, c₁, hc₁, hb₁⟩ := hu₁.2 K hK hKV
  obtain ⟨p₂, c₂, hc₂, hb₂⟩ := hu₂.2 K hK hKV
  have key : ∀ ϵ : ℝ, 0 < ϵ → ‖L ⟨f, hf⟩‖ ≤ (c₁ + c₂) * ϵ := by
    intro ϵ hϵ
    obtain ⟨g, hgK, hgn, hg⟩ := hnear (max p₁ p₂) ϵ hϵ L hL hL0
    rw [hg]
    have e1 : ‖u₁ g‖ ≤ c₁ * ϵ := by
      have hle := (hb₁ g hgK).trans (mul_le_mul_right
        ((derivSupNorm_mono (le_max_left _ _) _).trans hgn) _)
      rw [← ENNReal.ofReal_mul hc₁] at hle
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle
    have e2 : ‖u₂ g‖ ≤ c₂ * ϵ := by
      have hle := (hb₂ g hgK).trans (mul_le_mul_right
        ((derivSupNorm_mono (le_max_right _ _) _).trans hgn) _)
      rw [← ENNReal.ofReal_mul hc₂] at hle
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle
    have e3 : ‖L g‖ ≤ ‖u₁ g‖ + ‖u₂ g‖ := norm_sub_le _ _
    linarith
  have hzero : ‖L ⟨f, hf⟩‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hpos : 0 < c₁ + c₂ + 1 := by linarith
    have h1 := key (η / (c₁ + c₂ + 1)) (div_pos hη hpos)
    have h2 : (c₁ + c₂) * (η / (c₁ + c₂ + 1)) ≤ (c₁ + c₂ + 1) * (η / (c₁ + c₂ + 1)) := by
      have : 0 < η / (c₁ + c₂ + 1) := div_pos hη hpos
      nlinarith
    have h3 : (c₁ + c₂ + 1) * (η / (c₁ + c₂ + 1)) = η := by
      field_simp
    linarith
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hzero)
theorem boundedFunctionalRestrictsToDistrib (hF : Elementary.BasicProperties) (hn : 0 < n) :
    BoundedFunctionalRestrictsToDistrib n := by
  intro T k c hT hk hc hb
  obtain ⟨-, hopen, hCS, -, -⟩ := hF n hn
  have hsub : (smoothCompactSupp (distinctLocus n) : Set (PointTuple n → ℂ)) ⊆
      flatSchwartzSet n := by
    intro f hf
    obtain ⟨h1, h2, -⟩ := hCS _ hopen.1 f hf
    rw [hopen.2.2.2.2.2.2.1]
    exact ⟨h1, h2⟩
  refine ⟨hsub, fun a b f g χ hχ => hT a b _ _ _ hχ, fun K hK hKV => ?_⟩
  obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ x ∈ K, tupleNorm x ≤ ρ := by
    have hcont : Continuous (tupleNorm : PointTuple n → ℝ) := by
      unfold tupleNorm
      fun_prop
    obtain ⟨B, hB'⟩ := (hK.image hcont).bddAbove
    exact ⟨max B 0, le_max_right _ _, fun x hx => (hB' ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩
  have hW : 0 ≤ (1 + ρ ^ 2) ^ ((k : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  refine ⟨k, c * (1 + ρ ^ 2) ^ ((k : ℝ) / 2), mul_nonneg hc hW, fun f hf => ?_⟩
  have hzero : ∀ x, x ∉ {x : PointTuple n | tupleNorm x ≤ ρ} → f.1 x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hxs => hx (hρ x (hf hxs))
  have hle := (hCS _ hopen.1 f.1 f.2).2.2.2 ρ hρ0 hzero k hk
  calc ENNReal.ofReal ‖restrictToCompactSupp hsub T f‖
      ≤ ENNReal.ofReal c * weightedSeminorm k f.1 := hb ⟨f.1, hsub f.2⟩
    _ ≤ ENNReal.ofReal c *
        (ENNReal.ofReal ((1 + ρ ^ 2) ^ ((k : ℝ) / 2)) * derivSupNorm k f.1) :=
        mul_le_mul_right hle _
    _ = ENNReal.ofReal (c * (1 + ρ ^ 2) ^ ((k : ℝ) / 2)) * derivSupNorm k f.1 := by
        rw [ENNReal.ofReal_mul hc, mul_assoc]
theorem schwingerFamilyImpliesRegular (hF : Elementary.BasicProperties)
    (hB : BumpLemma) (hE : OffDiagonalTensors.Statement) (hn : 0 < n) :
    SchwingerFamilyImpliesRegular n := by
  intro σ T hσ hS
  have hbase : ∀ m : ℕ, 0 < m → ∃ hm : (smoothCompactSupp (distinctLocus m) :
      Set (PointTuple m → ℂ)) ⊆ flatSchwartzSet m,
      IsDistribOn (restrictToCompactSupp hm (T m)) ∧
        AgreesOnTensors σ (restrictToCompactSupp hm (T m)) := by
    intro m hm
    obtain ⟨hl, ⟨k, c, hk, hc, hb⟩, hv⟩ := hS.1 m hm
    obtain ⟨hsub, hd⟩ := boundedFunctionalRestrictsToDistrib hF hm (T m) k c hl hk hc hb
    exact ⟨hsub, hd, fun X hX =>
      ⟨(hE m hm).1 X hX, hv X hX (hsub ((hE m hm).1 X hX))⟩⟩
  refine ⟨⟨hσ, fun m hm => ?_⟩, ?_⟩
  · obtain ⟨hsub, hd, hv⟩ := hbase m hm
    exact ⟨_, hd, hv⟩
  · obtain ⟨hsub, hd, hv⟩ := hbase n hn
    refine ⟨hsub, hd, hv, fun u hu huv => distribDeterminedByTensors hF hB hn u _ hu hd ?_⟩
    intro X hX hmem
    obtain ⟨_, e₁⟩ := huv X hX
    obtain ⟨_, e₂⟩ := hv X hX
    exact e₁.trans e₂.symm
theorem coordDeriv_comp_sub (a : PointTuple n) (i : Fin n) (μ : Fin 4) (g : PointTuple n → ℂ) :
    coordDeriv i μ (g ∘ fun y => y - a) = coordDeriv i μ g ∘ fun y => y - a := by
  funext x
  simp only [coordDeriv, Function.comp, lineDeriv]
  congr 1
  funext s
  congr 1
  abel
theorem iterate_comp_of_commute (s : PointTuple n → PointTuple n)
    (D : (PointTuple n → ℂ) → PointTuple n → ℂ)
    (hD : ∀ g, D (g ∘ s) = D g ∘ s) (m : ℕ) (g : PointTuple n → ℂ) :
    D^[m] (g ∘ s) = D^[m] g ∘ s := by
  induction m generalizing g with
  | zero => rfl
  | succ m ih =>
    simp only [Function.iterate_succ, Function.comp_apply]
    rw [hD, ih]
theorem foldr_comp_of_commute {β : Type*} (s : PointTuple n → PointTuple n) (l : List β)
    (D : β → (PointTuple n → ℂ) → PointTuple n → ℂ) (hD : ∀ b g, D b (g ∘ s) = D b g ∘ s)
    (g : PointTuple n → ℂ) : l.foldr D (g ∘ s) = l.foldr D g ∘ s := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldr_cons]
    rw [ih, hD]
theorem multiDeriv_comp_sub (a : PointTuple n) (α : MultiIdx4 n) (g : PointTuple n → ℂ) :
    multiDeriv α (g ∘ fun y => y - a) = multiDeriv α g ∘ fun y => y - a := by
  unfold multiDeriv
  refine foldr_comp_of_commute _ _ _ (fun i k => ?_) g
  refine foldr_comp_of_commute _ _ _ (fun μ k' => ?_) k
  exact iterate_comp_of_commute _ _ (coordDeriv_comp_sub a i μ) _ k'
theorem spatialShiftPreservesPositiveTime (hO : TestFunctionOps.OperationsStatement)
    (hn : 0 < n) : SpatialShiftPreservesPositiveTime n := by
  intro v hv g hg
  obtain ⟨hgs, hgf⟩ := hg
  have hs : SmoothSeparatedTuples.translateFun v g ∈ schwartzSet n :=
    ((hO.1 n 1 hn one_pos (Equiv.refl _)
      (SmoothSeparatedTuples.pureTranslation v)).2.1 g hgs).1.2.1
  refine ⟨hs, hs.1, hgf.2.1, fun x hx => ?_⟩
  let a : PointTuple n := fun _ => v
  have hfun : SmoothSeparatedTuples.translateFun v g = g ∘ fun y => y - a := by
    funext y
    rw [SmoothSeparatedTuples.translateFun_apply]
    rfl
  have hv3 : v 3 = 0 := hv
  have hx' : x - a ∈ (positiveTimeLocus n)ᶜ := by
    intro hmem
    apply hx
    obtain ⟨hinj, htime⟩ := hmem
    refine ⟨fun i i' hii => hinj ?_, fun i => ?_⟩
    · show x i - v = x i' - v
      rw [hii]
    · have := htime i
      simpa [timeCoord, a, hv3] using this
  have hflat := hgf.2.2 _ hx'
  refine ⟨hs.1, ?_, fun α => ?_⟩
  · rw [hfun]
    exact hflat.2.1
  · rw [hfun, multiDeriv_comp_sub]
    exact hflat.2.2 α
theorem reflectConjTensorFlat (hT : TestSpaceFacts.Statement)
    (hO : TestFunctionOps.OperationsStatement) : ReflectConjTensorFlat := by
  intro q q' hq hq' f hf g hg
  have hr := (hO.1 q 1 hq one_pos (Equiv.refl _)
    (SmoothSeparatedTuples.pureTranslation 0)).2.1 f hf.1
  have hneg : VanishesToInfiniteOrderOff (Motions.reflectConj f) (negativeTimeLocus q) :=
    hr.2.2.1 hf.2
  have hmem : Motions.reflectConj f ∈ schwartzSet q := hr.1.2.2.1
  exact ⟨⟨hmem, hneg⟩, (hT.1 q q' 1 hq hq' one_pos _ hmem g hg.1).2.2 hneg hg.2⟩
theorem offDiagonalFacts_holds (hF : Elementary.BasicProperties) (hB : BumpLemma)
    (hT : TestSpaceFacts.Statement) (hO : TestFunctionOps.OperationsStatement)
    (hE : OffDiagonalTensors.Statement) : OffDiagonalFacts :=
  fun _ hn => ⟨distribDeterminedByTensors hF hB hn, boundedFunctionalRestrictsToDistrib hF hn,
    schwingerFamilyImpliesRegular hF hB hE hn, spatialShiftPreservesPositiveTime hO hn,
    reflectConjTensorFlat hT hO⟩
end YangMills.Construction.TestSpaces.OffDiagonal
end
