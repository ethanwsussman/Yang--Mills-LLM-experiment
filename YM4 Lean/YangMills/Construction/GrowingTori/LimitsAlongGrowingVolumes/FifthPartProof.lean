import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes.FirstPartProofForm
import YangMills.Construction.GrowingTori.TorusFunctionalsReadOnTuplesOfFourSpaceProof
import YangMills.Construction.TorusOrFourSpace.OpenSetsAndBallsOfSeveralPointsProof
import YangMills.Construction.Continuum.FormsFormedFromAFamilyOfDistributionsAreDistributions
import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes.FourthPartProof
import YangMills.Construction.TorusOrFourSpace.BallsTuplesInABallAndAdmissibleTuplesOfFourSpace
import YangMills.Construction.TorusOrFourSpace.ContinuousPartialsAreContinuousDifferentiability
import YangMills.Construction.TorusOrFourSpace.DerivativesOfFunctionsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.DistanceAndLiftsOfSeveralPoints
import Mathlib
set_option autoImplicit false
open Set
open scoped NNReal ENNReal ComplexConjugate
section
open TopologicalSpace YangMills.Construction.ReflectionSpaces YangMills.Construction.PeriodicSpace YangMills.Construction.PeriodicSpace.Kind
open YangMills.Construction.CoordinateRepresentation (IsCoordinateImageOfSet)
open scoped ContDiff ENNReal NNReal Topology
noncomputable section
namespace YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading
variable {p : ℕ+}
def euclidLength (x x' : Coords p) : ℝ := Real.sqrt (∑ j, (x - x') j ^ 2)
theorem eq_zero_of_mem_periodSet (D : Params) {k : Coords p}
    (hk : k ∈ Tuple.periodSet D euclidean p) : k = 0 := by
  funext j
  have hj : (j : ℕ) / 4 < (p : ℕ) := Nat.div_lt_of_lt_mul j.2
  have h0 : Coords.block k ⟨(j : ℕ) / 4, hj⟩ = 0 := hk ⟨(j : ℕ) / 4, hj⟩
  have h1 := congrFun h0 ⟨(j : ℕ) % 4, Nat.mod_lt _ (by norm_num)⟩
  have h2 : (⟨4 * ((j : ℕ) / 4) + (j : ℕ) % 4, by have := j.2; omega⟩ : Fin (4 * (p : ℕ))) = j :=
    Fin.ext (Nat.div_add_mod _ 4)
  simpa [Coords.block, h2] using h1
section EvaluationMaps
variable (hD : TupleMetric.QuotientDistanceAndLifts) (D : Params)
include hD
theorem tupleDist_proj (x x' : Coords p) :
    Tuple.tupleDist D euclidean (Tuple.proj D euclidean x)
      (Tuple.proj D euclidean x') = euclidLength x x' := by
  obtain ⟨_, h, _⟩ := hD D euclidean p
  obtain ⟨⟨k, hk, hr⟩, _⟩ := (h x x').1
  rw [hr, eq_zero_of_mem_periodSet D hk, sub_zero]
  rfl
theorem proj_bijective :
    Function.Bijective (Tuple.proj D euclidean (p := p)) :=
  ⟨fun x x' h => sub_eq_zero.1
      (eq_zero_of_mem_periodSet D (((hD D euclidean p).1.2 x x').1 h)),
    (hD D euclidean p).1.1⟩
omit hD in
theorem euclidLength_lt_mem_nhds (x : Coords p) {r : ℝ} (hr : 0 < r) :
    {x' | euclidLength x x' < r} ∈ 𝓝 x := by
  have hc : Continuous fun x' : Coords p => euclidLength x x' := by
    unfold euclidLength
    simp only [Pi.sub_apply]
    fun_prop
  have h0 : euclidLength x x = 0 := by simp [euclidLength]
  exact (isOpen_lt hc continuous_const).mem_nhds (by simpa [h0] using hr)
omit hD in
theorem dist_le_euclidLength (x x' : Coords p) : dist x x' ≤ euclidLength x x' := by apply _root_.YangMills.Construction.PeriodicSpace.TupleTopology.dist_le_euclidDist <;> assumption
theorem isOpenT_iff (S : Set (euclidean.Tuple D p)) :
    Tuple.IsOpenT D euclidean S ↔
      IsOpen (Tuple.proj D euclidean ⁻¹' S) := by
  have hs := (proj_bijective (p := p) hD D).2
  constructor
  · intro h
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨r, hr, hS⟩ := h _ hx
    exact Filter.mem_of_superset (euclidLength_lt_mem_nhds x hr) fun x' hx' =>
      hS _ (by rw [tupleDist_proj hD]; exact hx')
  · intro h y hy
    obtain ⟨x, rfl⟩ := hs y
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 h x hy
    refine ⟨ε, hε, fun y' hy' => ?_⟩
    obtain ⟨x', rfl⟩ := hs y'
    rw [tupleDist_proj hD] at hy'
    exact hb (by rw [Metric.mem_ball, dist_comm]; exact (dist_le_euclidLength x x').trans_lt hy')
theorem preimage_closureT (S : Set (euclidean.Tuple D p)) :
    Tuple.proj D euclidean ⁻¹' Tuple.closureT D euclidean S =
      closure (Tuple.proj D euclidean ⁻¹' S) := by
  have hs := (proj_bijective (p := p) hD D).2
  ext x
  constructor
  · intro h
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 ht
    obtain ⟨y, hy, hd⟩ := h ε hε
    obtain ⟨x', rfl⟩ := hs y
    rw [tupleDist_proj hD] at hd
    exact ⟨x', hb (by rw [Metric.mem_ball, dist_comm]; exact (dist_le_euclidLength x x').trans_lt hd), hy⟩
  · intro h r hr
    obtain ⟨x', hx', hS⟩ := mem_closure_iff_nhds.1 h _ (euclidLength_lt_mem_nhds x hr)
    exact ⟨_, hS, by rw [tupleDist_proj hD]; exact hx'⟩
theorem isCompactT_iff (S : Set (euclidean.Tuple D p)) :
    Tuple.IsCompactT D euclidean S ↔
      IsCompact (Tuple.proj D euclidean ⁻¹' S) := by
  classical
  have hb := proj_bijective (p := p) hD D
  set π := Tuple.proj D euclidean (p := p) with hπ
  constructor
  · intro h
    refine isCompact_of_finite_subcover fun {ι} U hU hcov => ?_
    have hpre : ∀ i, π ⁻¹' (π '' U i) = U i := fun i => Set.preimage_image_eq _ hb.1
    obtain ⟨𝒰, hsub, hfin, hcov'⟩ := h (Set.range fun i => π '' U i)
      (by
        rintro _ ⟨i, rfl⟩
        exact (isOpenT_iff hD D _).2 (by rw [← hπ, hpre]; exact hU i))
      (by
        intro y hy
        obtain ⟨x, rfl⟩ := hb.2 y
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hy)
        exact ⟨_, ⟨i, rfl⟩, x, hi, rfl⟩)
    have hsub' : ((hfin.toFinset : Finset _) : Set _) ⊆ (fun i => π '' U i) '' Set.univ := by
      simpa [Set.image_univ] using hsub
    obtain ⟨t, -, ht⟩ := Finset.subset_set_image_iff.1 hsub'
    refine ⟨t, fun x hx => ?_⟩
    obtain ⟨u, hu, hxu⟩ := hcov' hx
    have hu' : u ∈ t.image fun i => π '' U i := by rw [ht]; simpa using hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hu'
    obtain ⟨x', hx', he⟩ := hxu
    exact Set.mem_biUnion hi (hb.1 he ▸ hx')
  · intro h 𝒰 hopen hcov
    obtain ⟨𝒰', hsub, hfin, hcov'⟩ := h.elim_finite_subcover_image (b := 𝒰)
      (c := fun u => π ⁻¹' u) (fun u hu => (isOpenT_iff hD D u).1 (hopen u hu))
      (by
        intro x hx
        obtain ⟨u, hu, hxu⟩ := hcov hx
        exact Set.mem_biUnion hu hxu)
    refine ⟨𝒰', hsub, hfin, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ := hb.2 y
    obtain ⟨u, hu, hxu⟩ := Set.mem_iUnion₂.1 (hcov' hy)
    exact ⟨u, hu, hxu⟩
theorem tsupport_comp_proj (F : euclidean.Tuple D p → ℂ) :
    tsupport (F ∘ Tuple.proj D euclidean) =
      Tuple.proj D euclidean ⁻¹' Tuple.supportT D euclidean F := by
  rw [Tuple.supportT, preimage_closureT hD]
  rfl
theorem mem_testFns_iff (hC : ContPartialsIffContDiff)
    {Ω : Set (euclidean.Tuple D p)} {W : Opens (Euclidean.Coord (4 * (p : ℕ)))}
    (hW : IsCoordinateImageOfSet Ω W) (F : euclidean.Tuple D p → ℂ) :
    F ∈ Tuple.testFns D euclidean Ω ↔
      F ∘ Tuple.proj D euclidean ∈ Euclidean.testFunctionSpace W := by
  have hs := (proj_bijective (p := p) hD D).2
  have h1 : Tuple.IsSmoothT D euclidean F ↔
      ContDiff ℝ ∞ (F ∘ Tuple.proj D euclidean) := by
    rw [contDiff_infty]
    exact forall_congr' fun ν => hC p ν _
  have h2 : Tuple.IsCompactT D euclidean (Tuple.supportT D euclidean F) ↔
      HasCompactSupport (F ∘ Tuple.proj D euclidean) := by
    rw [isCompactT_iff hD, HasCompactSupport, tsupport_comp_proj hD]
  have h3 : Tuple.supportT D euclidean F ⊆ Ω ↔
      tsupport (F ∘ Tuple.proj D euclidean) ⊆ W := by
    rw [tsupport_comp_proj hD, show (W : Set (Euclidean.Coord (4 * (p : ℕ)))) = _ from hW]
    exact (Set.preimage_subset_preimage_iff (by rw [hs.range_eq]; exact Set.subset_univ _)).symm
  show _ ∧ _ ∧ _ ↔ _ ∧ _ ∧ _
  rw [h1, h2, h3]
end EvaluationMaps
section Norms
variable {n : ℕ}
def IsPartialDerivOfOrder (G : Euclidean.Coord n → ℂ) (k : ℕ)
    (H : Euclidean.Coord n → ℂ) : Prop :=
  ∃ c : Fin k → Fin n, H = Euclidean.partialDeriv c G
theorem isPartialDerivOfOrder_zero (G : Euclidean.Coord n → ℂ) : IsPartialDerivOfOrder G 0 G :=
  ⟨Fin.elim0, by funext x; simp [Euclidean.partialDeriv]⟩
theorem IsPartialDerivOfOrder.lineDeriv_single {G : Euclidean.Coord n → ℂ} (hG : ContDiff ℝ ∞ G)
    {k : ℕ} {H : Euclidean.Coord n → ℂ} (h : IsPartialDerivOfOrder G k H) (j : Fin n) :
    IsPartialDerivOfOrder G (k + 1) fun x => lineDeriv ℝ H x (Pi.single j 1) := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨Fin.cons j c, ?_⟩
  funext x
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k G) x :=
    (hG.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast WithTop.coe_lt_top _)) x
  have hf := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euclidean.Coord n) ℂ
    (fun i => Pi.single (c i) 1)).hasFDerivAt.comp x hd.hasFDerivAt)
  have hl := (hf.hasLineDerivAt (Pi.single j 1)).lineDeriv
  refine hl.trans ?_
  simp only [Euclidean.partialDeriv, iteratedFDeriv_succ_apply_left]
  rfl
theorem norm_partialDeriv_le_cNorm {G : Euclidean.Coord n → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) {ν k : ℕ} (hk : k ≤ ν) (c : Fin k → Fin n)
    (x : Euclidean.Coord n) :
    ‖Euclidean.partialDeriv c G x‖ ≤ Euclidean.cNorm ν G := by
  have h0 : Continuous (iteratedFDeriv ℝ k G) :=
    hG.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)
  have hcont : Continuous (Euclidean.partialDeriv c G) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euclidean.Coord n) ℂ
      (fun i => Pi.single (c i) 1)).continuous.comp h0
  have hcs : HasCompactSupport (Euclidean.partialDeriv c G) :=
    (hc.iteratedFDeriv (𝕜 := ℝ) k).comp_left
      (g := fun A : ContinuousMultilinearMap ℝ (fun _ : Fin k => Euclidean.Coord n) ℂ =>
        A fun i => Pi.single (c i) 1) rfl
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs
  have hbdd : BddAbove (Set.range fun x => ‖Euclidean.partialDeriv c G x‖) :=
    ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  calc ‖Euclidean.partialDeriv c G x‖
      ≤ TestFunctions.uniformNorm (Euclidean.partialDeriv c G) := le_ciSup hbdd x
    _ ≤ Euclidean.cNorm ν G :=
      le_ciSup (f := fun q : Euclidean.DerivIndex n ν =>
          TestFunctions.uniformNorm (Euclidean.partialDeriv q.2 G))
        (Set.finite_range _).bddAbove ⟨⟨k, by omega⟩, c⟩
theorem cNorm_nonneg (ν : ℕ) (G : Euclidean.Coord n → ℂ) :
    0 ≤ Euclidean.cNorm ν G :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
end Norms
theorem IsPartialDerivOfOrder.iterate_partialAlong {G : Coords p → ℂ} (hG : ContDiff ℝ ∞ G) {k : ℕ}
    {H : Coords p → ℂ} (h : IsPartialDerivOfOrder G k H) (j : Fin (4 * (p : ℕ))) (m : ℕ) :
    IsPartialDerivOfOrder G (k + m) ((Coords.partialAlong j)^[m] H) := by
  induction m with
  | zero => exact h
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact ih.lineDeriv_single hG j
theorem isPartialDerivOfOrder_iterPartial {G : Coords p → ℂ} (hG : ContDiff ℝ ∞ G)
    (α : CoordIndex p) : IsPartialDerivOfOrder G α.degree (Coords.iterPartial α G) := by
  have hL : ∀ L : List (Fin (4 * (p : ℕ))), IsPartialDerivOfOrder G (L.map α).sum
      (L.foldr (fun j H => (Coords.partialAlong j)^[α j] H) G) := by
    intro L
    induction L with
    | nil => exact isPartialDerivOfOrder_zero G
    | cons j L ih =>
      rw [List.map_cons, List.sum_cons, add_comm, List.foldr_cons]
      exact ih.iterate_partialAlong hG j (α j)
  have h := hL (List.finRange _)
  rwa [← Fin.sum_univ_def] at h
theorem tupleCNorm_le_ofReal_cNorm (hD : TupleMetric.QuotientDistanceAndLifts)
    (hDer : TupleDerivatives.Statement) (D : Params)
    {F : euclidean.Tuple D p → ℂ} (hF : Tuple.IsSmoothT D euclidean F)
    (hG : ContDiff ℝ ∞ (F ∘ Tuple.proj D euclidean))
    (hc : HasCompactSupport (F ∘ Tuple.proj D euclidean)) (ν : ℕ) :
    Tuple.cNorm D euclidean ν F ≤
      ENNReal.ofReal (Euclidean.cNorm ν (F ∘ Tuple.proj D euclidean)) := by
  refine iSup_le fun α => iSup_le fun hα => iSup_le fun y => ?_
  obtain ⟨x, rfl⟩ := (proj_bijective (p := p) hD D).2 y
  have h := ((hDer D euclidean p).1 ν F (hF ν) α hα).2.1
  have hx := congrFun h x
  obtain ⟨c, hc'⟩ := isPartialDerivOfOrder_iterPartial hG α
  rw [Function.comp_apply] at hx
  rw [hx, hc']
  exact ENNReal.ofReal_le_ofReal (norm_partialDeriv_le_cNorm hG hc hα c x)
end YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading
end
end
section
open Filter TopologicalSpace YangMills.Construction.ReflectionSpaces YangMills.Construction.PeriodicSpace YangMills.Construction.PeriodicSpace.Kind
open YangMills.Construction.CoordinateRepresentation (IsCoordinateImageOfSet)
open scoped ContDiff ENNReal NNReal Topology
noncomputable section
namespace YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading
variable {p : ℕ+}
theorem foldr_iterate_eq_self (α : CoordIndex p) (G : Coords p → ℂ)
    (L : List (Fin (4 * (p : ℕ)))) (hL : ∀ j ∈ L, α j = 0) :
    L.foldr (fun j H => (Coords.partialAlong j)^[α j] H) G = G := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    rw [List.foldr_cons, ih fun j hj => hL j (List.mem_cons_of_mem _ hj), hL i List.mem_cons_self]
    rfl
theorem iterPartial_zero (G : Coords p → ℂ) : Coords.iterPartial 0 G = G :=
  foldr_iterate_eq_self 0 G _ fun _ _ => rfl
theorem iterPartial_single (j : Fin (4 * (p : ℕ))) (G : Coords p → ℂ) :
    Coords.iterPartial (Pi.single j 1 : CoordIndex p) G =
      Coords.partialAlong j G := by
  have hL : ∀ L : List (Fin (4 * (p : ℕ))), L.Nodup → j ∈ L →
      L.foldr (fun i H => (Coords.partialAlong i)^[
        (Pi.single j 1 : CoordIndex p) i] H) G = Coords.partialAlong j G := by
    intro L
    induction L with
    | nil => intro _ h; simp at h
    | cons i L ih =>
      intro hn hj
      rw [List.foldr_cons]
      by_cases hij : i = j
      · subst hij
        rw [foldr_iterate_eq_self (Pi.single i 1) G L fun k hk => ?_]
        · simp
        · exact Pi.single_eq_of_ne (fun e => (List.nodup_cons.1 hn).1 (by rw [← e]; exact hk)) _
      · have hjL : j ∈ L := by
          rcases List.mem_cons.1 hj with h | h
          · exact absurd h.symm hij
          · exact h
        rw [ih (List.nodup_cons.1 hn).2 hjL, Pi.single_eq_of_ne hij]
        rfl
  exact hL _ (List.nodup_finRange _) (List.mem_finRange j)
theorem lineDeriv_partialDeriv_eq_cons {n : ℕ} {G : Euclidean.Coord n → ℂ}
    (hG : ContDiff ℝ ∞ G) {k : ℕ} (c : Fin k → Fin n) (j : Fin n) :
    (fun x => lineDeriv ℝ (Euclidean.partialDeriv c G) x (Pi.single j 1)) =
      Euclidean.partialDeriv (Fin.cons j c : Fin (k + 1) → Fin n) G := by
  funext x
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k G) x :=
    (hG.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast WithTop.coe_lt_top _)) x
  have hf := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euclidean.Coord n) ℂ
    (fun i => Pi.single (c i) 1)).hasFDerivAt.comp x hd.hasFDerivAt)
  have hl := (hf.hasLineDerivAt (Pi.single j 1)).lineDeriv
  refine hl.trans ?_
  simp only [Euclidean.partialDeriv, iteratedFDeriv_succ_apply_left]
  rfl
theorem exists_partialDeriv_eq_comp
    (hDer : TupleDerivatives.Statement) (D : Params)
    {F : euclidean.Tuple D p → ℂ} (hF : Tuple.IsSmoothT D euclidean F)
    (hG : ContDiff ℝ ∞ (F ∘ Tuple.proj D euclidean)) :
    ∀ (k : ℕ) (c : Fin k → Fin (4 * (p : ℕ))), ∃ α : CoordIndex p, α.degree = k ∧
      Euclidean.partialDeriv c (F ∘ Tuple.proj D euclidean) =
        Tuple.partialDeriv D euclidean α F ∘ Tuple.proj D euclidean := by
  intro k
  induction k with
  | zero =>
    intro c
    refine ⟨0, by simp [CoordIndex.degree], ?_⟩
    have h := ((hDer D euclidean p).1 0 F (hF 0) 0 (by simp [CoordIndex.degree])).2.1
    rw [h, iterPartial_zero]
    funext x
    simp [Euclidean.partialDeriv]
  | succ k ih =>
    intro c
    obtain ⟨α, hα, he⟩ := ih (Fin.tail c)
    set j := c 0 with hj
    have hβ : CoordIndex.degree (p := p) (Pi.single j 1) = 1 := by
      simp [CoordIndex.degree, Pi.single_apply]
    obtain ⟨-, -, -, hclass, hadd, -⟩ :=
      (hDer D euclidean p).1 (k + 1) F (hF _) α (by omega)
    have hclass' : Tuple.IsClassC D euclidean 1 (Tuple.partialDeriv D euclidean α F) := by
      have h1 : k + 1 - α.degree = 1 := by omega
      rwa [h1] at hclass
    have hcomp := ((hDer D euclidean p).1 1 _ hclass' (Pi.single j 1) hβ.le).2.1
    refine ⟨α + Pi.single j 1, ?_, ?_⟩
    · have : CoordIndex.degree (p := p) (α + Pi.single j 1) = α.degree +
          CoordIndex.degree (p := p) (Pi.single j 1) := by
        simp [CoordIndex.degree, Finset.sum_add_distrib]
      omega
    · rw [← hadd _ (by omega), hcomp, iterPartial_single, ← he]
      have hc : c = (Fin.cons j (Fin.tail c) : Fin (k + 1) → Fin (4 * (p : ℕ))) :=
        (Fin.cons_self_tail c).symm
      rw [hc, ← lineDeriv_partialDeriv_eq_cons hG]
      rw [← hc]
      rfl
theorem cNorm_comp_le_toReal (hDer : TupleDerivatives.Statement) (D : Params)
    {F : euclidean.Tuple D p → ℂ} (hF : Tuple.IsSmoothT D euclidean F)
    (hG : ContDiff ℝ ∞ (F ∘ Tuple.proj D euclidean))
    (hc : Tuple.IsCompactT D euclidean (Tuple.supportT D euclidean F)) (ν : ℕ) :
    Euclidean.cNorm ν (F ∘ Tuple.proj D euclidean) ≤
      (Tuple.cNorm D euclidean ν F).toReal := by
  have hfin := (hDer D euclidean p).2 ν F (hF ν) hc
  have h0 : (Nonempty (Euclidean.DerivIndex (4 * (p : ℕ)) ν)) :=
    ⟨⟨⟨0, Nat.succ_pos _⟩, Fin.elim0⟩⟩
  refine ciSup_le fun q => ciSup_le fun x => ?_
  obtain ⟨α, hα, he⟩ := exists_partialDeriv_eq_comp hDer D hF hG q.1 q.2
  rw [he, Function.comp_apply]
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin.ne]
  have hle : α.degree ≤ ν := by have := q.1.2; omega
  exact le_iSup_of_le α (le_iSup_of_le hle
    (le_iSup (fun y => ENNReal.ofReal ‖Tuple.partialDeriv D euclidean α F y‖) _))
theorem tendstoInTest_of_tendstoInTestFns (hD : TupleMetric.QuotientDistanceAndLifts)
    (hDer : TupleDerivatives.Statement)
    (hC : ContPartialsIffContDiff) (D : Params)
    {Ω : Set (euclidean.Tuple D p)} {W : Opens (Euclidean.Coord (4 * (p : ℕ)))}
    (hW : IsCoordinateImageOfSet Ω W) (Fs : ℕ+ → Tuple.testFns D euclidean Ω)
    (F : Tuple.testFns D euclidean Ω)
    (h : Tuple.TendstoInTestFns Fs F)
    (hs : ∀ t, (Fs t).1 ∘ Tuple.proj D euclidean ∈ Euclidean.testFunctionSpace W)
    (h0 : F.1 ∘ Tuple.proj D euclidean ∈ Euclidean.testFunctionSpace W) :
    Euclidean.TendstoInTest (fun t => ⟨_, hs t⟩) ⟨_, h0⟩ := by
  obtain ⟨⟨K, hK, hKΩ, hFK, hFsK⟩, hν⟩ := h
  refine ⟨⟨Tuple.proj D euclidean ⁻¹' K, (isCompactT_iff hD D K).1 hK, ?_, ?_,
    fun t => ?_⟩, fun ν => ?_⟩
  · intro x hx
    show x ∈ (W : Set _)
    rw [show (W : Set (Euclidean.Coord (4 * (p : ℕ)))) = _ from hW]
    exact hKΩ hx
  · show tsupport (F.1 ∘ _) ⊆ _
    rw [tsupport_comp_proj hD]
    exact Set.preimage_mono hFK
  · show tsupport ((Fs t).1 ∘ _) ⊆ _
    rw [tsupport_comp_proj hD]
    exact Set.preimage_mono (hFsK t)
  · have hsub : ∀ t, ((Fs t).1 - F.1) ∈ Tuple.testFns D euclidean Ω := fun t => by
      refine (mem_testFns_iff hD D hC hW _).2 ?_
      exact (Euclidean.testFunctionSpace W).sub_mem (hs t) h0
    have hb : ∀ t, Euclidean.cNorm ν
        (((Fs t).1 ∘ Tuple.proj D euclidean) -
          (F.1 ∘ Tuple.proj D euclidean)) ≤
        (Tuple.cNorm D euclidean ν ((Fs t).1 - F.1)).toReal := fun t =>
      cNorm_comp_le_toReal hDer D (hsub t).1
        ((mem_testFns_iff hD D hC hW _).1 (hsub t)).1 (hsub t).2.1 ν
    have hlim : Tendsto (fun t => (Tuple.cNorm D euclidean ν ((Fs t).1 - F.1)).toReal)
        atTop (𝓝 0) := by
      simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hν ν)
    exact squeeze_zero (fun t => cNorm_nonneg ν _) hb hlim
theorem tendstoInTestFns_of_tendstoInTest (hD : TupleMetric.QuotientDistanceAndLifts)
    (hDer : TupleDerivatives.Statement)
    (hC : ContPartialsIffContDiff) (D : Params)
    {Ω : Set (euclidean.Tuple D p)} {W : Opens (Euclidean.Coord (4 * (p : ℕ)))}
    (hW : IsCoordinateImageOfSet Ω W) (Fs : ℕ+ → Tuple.testFns D euclidean Ω)
    (F : Tuple.testFns D euclidean Ω)
    (hs : ∀ t, (Fs t).1 ∘ Tuple.proj D euclidean ∈ Euclidean.testFunctionSpace W)
    (h0 : F.1 ∘ Tuple.proj D euclidean ∈ Euclidean.testFunctionSpace W)
    (h : Euclidean.TendstoInTest (fun t => ⟨_, hs t⟩) ⟨_, h0⟩) :
    Tuple.TendstoInTestFns Fs F := by
  obtain ⟨⟨K, hK, hKW, hFK, hFsK⟩, hν⟩ := h
  have hb := proj_bijective (p := p) hD D
  have himg : ∀ {G : euclidean.Tuple D p → ℂ},
      tsupport (G ∘ Tuple.proj D euclidean) ⊆ K →
      Tuple.supportT D euclidean G ⊆ Tuple.proj D euclidean '' K := by
    intro G hG y hy
    obtain ⟨x, rfl⟩ := hb.2 y
    refine ⟨x, hG ?_, rfl⟩
    rw [tsupport_comp_proj hD]
    exact hy
  refine ⟨⟨Tuple.proj D euclidean '' K, ?_, ?_, himg hFK, fun t => himg (hFsK t)⟩,
    fun ν => ?_⟩
  · refine (isCompactT_iff hD D _).2 ?_
    rw [Set.preimage_image_eq _ hb.1]
    exact hK
  · rintro _ ⟨x, hx, rfl⟩
    have hxW : x ∈ (W : Set (Euclidean.Coord (4 * (p : ℕ)))) := hKW hx
    rw [show (W : Set (Euclidean.Coord (4 * (p : ℕ)))) = _ from hW] at hxW
    exact hxW
  · have hsub : ∀ t, ((Fs t).1 - F.1) ∈ Tuple.testFns D euclidean Ω := fun t => by
      refine (mem_testFns_iff hD D hC hW _).2 ?_
      exact (Euclidean.testFunctionSpace W).sub_mem (hs t) h0
    have hbd : ∀ t, Tuple.cNorm D euclidean ν ((Fs t).1 - F.1) ≤
        ENNReal.ofReal (Euclidean.cNorm ν
          (((Fs t).1 ∘ Tuple.proj D euclidean) -
            (F.1 ∘ Tuple.proj D euclidean))) := fun t => by
      have hm := (mem_testFns_iff hD D hC hW _).1 (hsub t)
      exact tupleCNorm_le_ofReal_cNorm hD hDer D (hsub t).1 hm.1 hm.2.1 ν
    have hlim : Tendsto (fun t => ENNReal.ofReal (Euclidean.cNorm ν
          (((Fs t).1 ∘ Tuple.proj D euclidean) -
            (F.1 ∘ Tuple.proj D euclidean)))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal (hν ν)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) hbd
end YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading
end
end
section
open Filter TopologicalSpace YangMills.Construction.ReflectionSpaces YangMills.Construction.PeriodicSpace YangMills.Construction.PeriodicSpace.Kind
open YangMills.Construction.TorusTransport.TestFunctionOrders
open YangMills.Construction.CoordinateRepresentation (IsCoordinateImageOfSet)
open scoped ContDiff ENNReal NNReal Topology ComplexConjugate
noncomputable section
namespace YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading
section Sets
variable (Y : Params) {n : ℕ+}
theorem proj_eq_pointAt (x : Coords n) :
    Tuple.proj Y euclidean x =
      Continuum.BlockProducts.pointAt (n := (n : ℕ)) x := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.ExistencePart.proj_euclidean_eq_pointAt <;> assumption
theorem mem_injTuplesIn {O : Set (Fin 4 → ℝ)} {m : ℕ} {y : Fin m → Fin 4 → ℝ} :
    y ∈ Euclid.injTuplesIn O m ↔ (∀ i, y i ∈ O) ∧ Function.Injective y := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨fun i => (z i).2, fun a b h => hz (Subtype.ext h)⟩
  · rintro ⟨hO, hi⟩
    exact ⟨fun i => ⟨y i, hO i⟩, fun a b h => hi (congrArg Subtype.val h), rfl⟩
theorem continuous_proj :
    @Continuous (Coords n) (Fin (n : ℕ) → Fin 4 → ℝ) _ _
      (Tuple.proj Y euclidean) := by
  have h : Continuous fun (x : Coords n) (i : Fin (n : ℕ)) (μ : Fin 4) =>
      x ⟨4 * (i : ℕ) + (μ : ℕ), by have := i.2; have := μ.2; omega⟩ :=
    continuous_pi fun _ => continuous_pi fun _ => continuous_apply _
  exact h
theorem isOpen_injTuplesIn {O : Set (Fin 4 → ℝ)} (hO : IsOpen O) (m : ℕ) :
    IsOpen (Euclid.injTuplesIn O m) := by
  have h : Euclid.injTuplesIn O m =
      Set.univ.pi (fun _ => O) ∩ TestFunctions.injectiveTuples (Fin 4 → ℝ) m := by
    ext y
    rw [mem_injTuplesIn]
    simp [TestFunctions.injectiveTuples, Set.mem_pi]
  rw [h]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => hO).inter
    (Distributions.isOpen_injectiveTuples m)
def injTuplesOpens {O : Set (Fin 4 → ℝ)} (hO : IsOpen O) (n : ℕ+) :
    Opens (Euclidean.Coord (4 * (n : ℕ))) where
  carrier := Tuple.proj Y euclidean ⁻¹' Euclid.injTuplesIn O (n : ℕ)
  is_open' := (isOpen_injTuplesIn hO _).preimage (continuous_proj Y)
theorem isCoordinateReadingOfSet_injTuplesOpens {O : Set (Fin 4 → ℝ)} (hO : IsOpen O) (n : ℕ+) :
    IsCoordinateImageOfSet (D := Y) (Euclid.injTuplesIn O (n : ℕ)) (injTuplesOpens Y hO n) :=
  rfl
def projHomeomorph (n : ℕ+) : Coords n ≃ₜ (Fin (n : ℕ) → Fin 4 → ℝ) where
  toFun := Tuple.proj Y euclidean
  invFun y := fun j => y ⟨(j : ℕ) / 4, Nat.div_lt_of_lt_mul j.2⟩ ⟨(j : ℕ) % 4, Nat.mod_lt _ (by omega)⟩
  left_inv x := by
    funext j
    show x ⟨4 * ((j : ℕ) / 4) + (j : ℕ) % 4, _⟩ = x j
    congr 1
    exact Fin.ext (Nat.div_add_mod _ 4)
  right_inv y := by
    funext i μ
    have h₁ : (4 * (i : ℕ) + (μ : ℕ)) / 4 = i := by have := μ.2; omega
    have h₂ : (4 * (i : ℕ) + (μ : ℕ)) % 4 = μ := by have := μ.2; omega
    show y ⟨(4 * (i : ℕ) + (μ : ℕ)) / 4, _⟩ ⟨(4 * (i : ℕ) + (μ : ℕ)) % 4, _⟩ = y i μ
    simp only [h₁, h₂]
  continuous_toFun := continuous_proj Y
  continuous_invFun := continuous_pi fun _ => (continuous_apply _).comp (continuous_apply _)
end Sets
section Reflection
abbrev reflectionPerm (μ : Fin 4) (c : ℝ) : Equiv.Perm (Fin 4 → ℝ) :=
  (BallPeriodization.hyperplaneReflection μ c : Equiv.Perm (Fin 4 → ℝ))
theorem reflectionPerm_reflectionPerm (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    reflectionPerm μ c (reflectionPerm μ c x) = x := by apply _root_.YangMills.Construction.CentredTensorMoments.TorusFunctionals.axisRefl_axisRefl <;> assumption
theorem continuous_reflectionPerm (μ : Fin 4) (c : ℝ) : Continuous (reflectionPerm μ c) := by apply _root_.YangMills.Construction.CentredTensorMoments.TorusFunctionals.continuous_axisRefl <;> assumption
def conjReflected (μ : Fin 4) (c : ℝ) {m : ℕ} (F : (Fin m → Fin 4 → ℝ) → ℂ) :
    (Fin m → Fin 4 → ℝ) → ℂ :=
  fun x => conj (F fun i => reflectionPerm μ c (x i))
variable (μ : Fin 4) (c : ℝ) (n : ℕ+)
def reflectionSign (j : Fin (4 * (n : ℕ))) : ℝ := if (j : ℕ) % 4 = (μ : ℕ) then -1 else 1
def reflectionShift (j : Fin (4 * (n : ℕ))) : ℝ := if (j : ℕ) % 4 = (μ : ℕ) then 2 * c else 0
abbrev reflectionMatrix : Matrix (Fin (4 * (n : ℕ))) (Fin (4 * (n : ℕ))) ℝ :=
  Matrix.diagonal (reflectionSign μ n)
theorem isSignedPermMatrix_reflectionMatrix :
    DistributionBasics.IsSignedPermMatrix (reflectionMatrix μ n) := by
  refine ⟨1, reflectionSign μ n, fun j => ?_, fun i j => ?_⟩
  · unfold reflectionSign
    split_ifs <;> simp
  · by_cases h : i = j
    · subst h
      simp
    · simp [h]
abbrev reflectionMap : Coords n → Coords n :=
  DistributionBasics.signedAffine (reflectionMatrix μ n) (reflectionShift μ c n)
theorem reflectionMap_apply (x : Coords n) (j : Fin (4 * (n : ℕ))) :
    reflectionMap μ c n x j = reflectionSign μ n j * x j + reflectionShift μ c n j := by
  simp [DistributionBasics.signedAffine, Matrix.mulVec_diagonal]
theorem reflectionMap_reflectionMap (x : Coords n) :
    reflectionMap μ c n (reflectionMap μ c n x) = x := by
  funext j
  rw [reflectionMap_apply, reflectionMap_apply]
  unfold reflectionSign reflectionShift
  split_ifs <;> ring
variable {n}
theorem proj_reflectionMap (Y : Params) (x : Coords n) :
    Tuple.proj Y euclidean (reflectionMap μ c n x) =
      fun i => reflectionPerm μ c (Tuple.proj Y euclidean x i) := by
  funext i ν
  have hν : (4 * (i : ℕ) + (ν : ℕ)) % 4 = ν := by have := ν.2; omega
  have hμ : (4 * (i : ℕ) + (μ : ℕ)) < 4 * (n : ℕ) := by have := i.2; have := μ.2; omega
  show reflectionMap μ c n x ⟨4 * (i : ℕ) + (ν : ℕ), _⟩ =
    (reflectionPerm μ c) (fun ν' => x ⟨4 * (i : ℕ) + (ν' : ℕ), _⟩) ν
  rw [reflectionMap_apply, BallPeriodization.hyperplaneReflection_apply]
  by_cases h : ν = μ
  · subst h
    simp [reflectionSign, reflectionShift, hν, PeriodicLattice.coordVec]
    ring
  · have h' : (ν : ℕ) ≠ μ := fun e => h (Fin.ext e)
    simp [reflectionSign, reflectionShift, hν, h', PeriodicLattice.coordVec, Pi.single_eq_of_ne h]
end Reflection
end YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading
end
end
section
open Filter TopologicalSpace YangMills.Construction.ReflectionSpaces YangMills.Construction.PeriodicSpace YangMills.Construction.PeriodicSpace.Kind
open YangMills.Construction.TorusTransport.TestFunctionOrders
open YangMills.Construction.CoordinateRepresentation (IsCoordinateImageOfSet)
open scoped ContDiff ENNReal NNReal Topology ComplexConjugate
noncomputable section
namespace YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep
open FlatReading MirrorFamilies
section Convergence
variable (h : CitedFacts) (hD : TupleMetric.QuotientDistanceAndLifts)
  (hDer : TupleDerivatives.Statement)
  (hC : ContPartialsIffContDiff)
  (hForms : Continuum.BlockProducts.AssembledFormsAreDistributions)
  (Y : Params)
omit h hD hDer hC hForms in
theorem isOpenQ_euclidean_of_isOpen {O : Set (Fin 4 → ℝ)} (hO : IsOpen O) :
    Kind.IsOpenQ Y Kind.euclidean O :=
  (SeparatedTuplesR4.isOpenWrt_euclid_iff (EuclideanCase.quotDist_euclidean_eq Y) O).2 hO
include h hD hDer hC
theorem convergesOn_conjReflected (μ : Fin 4) (c : ℝ) {O : Set (Fin 4 → ℝ)} (hO : IsOpen O) {n : ℕ+}
    {Fs : ℕ+ → Kind.euclidean.Tuple Y n → ℂ}
    {F : Kind.euclidean.Tuple Y n → ℂ} (hc : TendstoInInjTestFns Y O Fs F) :
    TendstoInInjTestFns Y (reflectionPerm μ c ⁻¹' O) (fun t => conjReflected μ c (Fs t))
      (conjReflected μ c F) := by
  obtain ⟨hs, h0, hconv⟩ := hc
  have hO' : IsOpen (reflectionPerm μ c ⁻¹' O) := hO.preimage (continuous_reflectionPerm μ c)
  have hWr := isCoordinateReadingOfSet_injTuplesOpens Y hO n
  have hWr' := isCoordinateReadingOfSet_injTuplesOpens Y hO' n
  have himg : ((injTuplesOpens Y hO n : Opens _) : Set (Euclidean.Coord (4 * (n : ℕ)))) =
      DistributionBasics.signedAffine (reflectionMatrix μ n) (reflectionShift μ c n) ''
        ((injTuplesOpens Y hO' n : Opens _) : Set (Euclidean.Coord (4 * (n : ℕ)))) := by
    ext x
    constructor
    · intro hx
      have hx' : Tuple.proj Y euclidean x ∈
          Euclid.injTuplesIn O (n : ℕ) := hx
      obtain ⟨h₁, h₂⟩ := mem_injTuplesIn.1 hx'
      refine ⟨reflectionMap μ c n x, ?_, reflectionMap_reflectionMap μ c n x⟩
      show Tuple.proj Y euclidean (reflectionMap μ c n x) ∈
        Euclid.injTuplesIn (reflectionPerm μ c ⁻¹' O) (n : ℕ)
      rw [proj_reflectionMap]
      refine mem_injTuplesIn.2 ⟨fun i => ?_, fun a b hab => h₂ ((reflectionPerm μ c).injective hab)⟩
      exact Eq.mpr (congrArg (· ∈ O)
        (reflectionPerm_reflectionPerm μ c (Tuple.proj Y euclidean x i))) (h₁ i)
    · rintro ⟨y, hy, rfl⟩
      have hy' : Tuple.proj Y euclidean y ∈
          Euclid.injTuplesIn (reflectionPerm μ c ⁻¹' O) (n : ℕ) := hy
      obtain ⟨h₁, h₂⟩ := mem_injTuplesIn.1 hy'
      show Tuple.proj Y euclidean (reflectionMap μ c n y) ∈
        Euclid.injTuplesIn O (n : ℕ)
      rw [proj_reflectionMap]
      exact mem_injTuplesIn.2 ⟨fun i => h₁ i, fun a b hab => h₂ ((reflectionPerm μ c).injective hab)⟩
  obtain ⟨-, -, hEl⟩ := h.elementary (4 * (n : ℕ)) (by have := n.pos; omega) (injTuplesOpens Y hO' n)
  obtain ⟨⟨-, Φ, hΦ, -, -, -, hlim⟩, -⟩ :=
    (hEl (reflectionMatrix μ n) (isSignedPermMatrix_reflectionMatrix μ n) (reflectionShift μ c n)).2
      (injTuplesOpens Y hO n) himg
  have hmem : ∀ G, G ∈ injTestFns Y O n →
      G ∘ Tuple.proj Y euclidean ∈
        Euclidean.testFunctionSpace (injTuplesOpens Y hO n) := fun G hG =>
    (FlatReading.mem_testFns_iff hD Y hC hWr G).1 hG
  have key : ∀ (G : Kind.euclidean.Tuple Y n → ℂ)
      (hG : G ∘ Tuple.proj Y euclidean ∈
        Euclidean.testFunctionSpace (injTuplesOpens Y hO n)),
      ((Φ ⟨_, hG⟩ : Euclidean.testFunctionSpace (injTuplesOpens Y hO' n)) :
          Euclidean.Coord (4 * (n : ℕ)) → ℂ) =
        conjReflected μ c G ∘ Tuple.proj Y euclidean := by
    intro G hG
    funext x
    rw [hΦ]
    show conj (G (Tuple.proj Y euclidean (reflectionMap μ c n x))) = _
    rw [proj_reflectionMap]
    rfl
  have hpull : ∀ (G : Kind.euclidean.Tuple Y n → ℂ)
      (hG : G ∘ Tuple.proj Y euclidean ∈
        Euclidean.testFunctionSpace (injTuplesOpens Y hO n)),
      conjReflected μ c G ∘ Tuple.proj Y euclidean ∈
        Euclidean.testFunctionSpace (injTuplesOpens Y hO' n) := fun G hG =>
    Eq.mp (congrArg (· ∈ Euclidean.testFunctionSpace (injTuplesOpens Y hO' n)) (key G hG))
      (Φ ⟨_, hG⟩).2
  have hback : ∀ G, G ∈ injTestFns Y O n →
      conjReflected μ c G ∈ injTestFns Y (reflectionPerm μ c ⁻¹' O) n :=
    fun G hG => (FlatReading.mem_testFns_iff hD Y hC hWr' _).2 (hpull G (hmem G hG))
  have hT := tendstoInTest_of_tendstoInTestFns hD hDer hC Y hWr (fun t => ⟨Fs t, hs t⟩) ⟨F, h0⟩ hconv
    (fun t => hmem _ (hs t)) (hmem _ h0)
  have hT' := hlim _ _ hT
  refine ⟨fun t => hback _ (hs t), hback _ h0, ?_⟩
  have hs' : ∀ t, conjReflected μ c (Fs t) ∘ Tuple.proj Y euclidean ∈
      Euclidean.testFunctionSpace (injTuplesOpens Y hO' n) := fun t => hpull _ (hmem _ (hs t))
  have h0' : conjReflected μ c F ∘ Tuple.proj Y euclidean ∈
      Euclidean.testFunctionSpace (injTuplesOpens Y hO' n) := hpull _ (hmem _ h0)
  refine tendstoInTestFns_of_tendstoInTest hD hDer hC Y hWr' _ _ hs' h0' ?_
  have e₁ : (fun t => Φ ⟨_, hmem _ (hs t)⟩) = fun t => ⟨_, hs' t⟩ :=
    funext fun t => Subtype.ext (key _ _)
  have e₂ : Φ ⟨_, hmem _ h0⟩ = ⟨_, h0'⟩ := Subtype.ext (key _ _)
  exact show Euclidean.TendstoInTest (fun t => ⟨_, hs' t⟩) ⟨_, h0'⟩ from by
    rw [← e₁, ← e₂]
    exact hT'
omit h hD hDer hC in
theorem convergesOn_pairwiseDistinct {O : Set (Fin 4 → ℝ)} {n : ℕ+}
    {Fs : ℕ+ → Kind.euclidean.Tuple Y n → ℂ}
    {F : Kind.euclidean.Tuple Y n → ℂ} (hc : TendstoInInjTestFns Y O Fs F) :
    ∃ (hs : ∀ t, Fs t ∈ Tuple.testFns Y euclidean
          (Kind.pairwiseDistinct Y Kind.euclidean n))
      (h0 : F ∈ Tuple.testFns Y euclidean
          (Kind.pairwiseDistinct Y Kind.euclidean n)),
      Tuple.TendstoInTestFns (fun t => ⟨Fs t, hs t⟩) ⟨F, h0⟩ := by
  obtain ⟨hs, h0, ⟨K, hK, hKΩ, hFK, hFsK⟩, hν⟩ := hc
  have hsub : Euclid.injTuplesIn O (n : ℕ) ⊆ Kind.pairwiseDistinct Y Kind.euclidean n :=
    fun y hy => (mem_injTuplesIn.1 hy).2
  exact ⟨fun t => ⟨(hs t).1, (hs t).2.1, (hs t).2.2.trans hsub⟩,
    ⟨h0.1, h0.2.1, h0.2.2.trans hsub⟩, ⟨K, hK, hKΩ.trans hsub, hFK, hFsK⟩, hν⟩
end Convergence
section FormedDistributions
variable (u : Continuum.BlockProducts.DistribFamily)
theorem assembledDistributionAt_of_isOffDiagonalTest {Q : ℕ} {G : OrderedTestFun (Q + 1)}
    (hG : IsOffDiagonalTest ⟨Q + 1, G⟩) :
    assembledDistributionAt u ⟨Q + 1, G⟩ =
      Continuum.BlockProducts.assembledForm (Q + 1) u ⟨_, hG⟩ :=
  dif_pos hG
theorem isOffDiagonalTest_const_mul {Q : ℕ} {G : OrderedTestFun (Q + 1)} (a : ℂ)
    (hG : IsOffDiagonalTest ⟨Q + 1, G⟩) :
    IsOffDiagonalTest ⟨Q + 1, fun x => a * G x⟩ :=
  (Euclidean.testFunctionSpace _).smul_mem a hG
theorem assembledDistributionAt_const_mul {Q : ℕ} {G : OrderedTestFun (Q + 1)} (a : ℂ)
    (hG : IsOffDiagonalTest ⟨Q + 1, G⟩) :
    assembledDistributionAt u ⟨Q + 1, fun x => a * G x⟩ = a * assembledDistributionAt u ⟨Q + 1, G⟩ := by
  have e : (⟨_, isOffDiagonalTest_const_mul a hG⟩ : Euclidean.testFunctionSpace
        (Continuum.BlockProducts.configSpace (Q + 1))) = a • ⟨_, hG⟩ :=
    Subtype.ext rfl
  refine (assembledDistributionAt_of_isOffDiagonalTest u (isOffDiagonalTest_const_mul a hG)).trans ?_
  rw [assembledDistributionAt_of_isOffDiagonalTest u hG]
  exact (congrArg _ e).trans ((map_smul _ a _).trans (smul_eq_mul a _))
theorem isOffDiagonalTest_zero (z : ℂ) : IsOffDiagonalTest ⟨0, z⟩ := by
  have he : IsEmpty (Fin (4 * 0)) := ⟨fun a => by have := a.2; omega⟩
  have hu : Unique (Fin (4 * 0) → ℝ) := Pi.uniqueOfIsEmpty _
  refine ⟨contDiff_const, ?_, ?_⟩
  · exact @HasCompactSupport.of_compactSpace (Fin (4 * 0) → ℝ) ℂ _ _ _ _
  · intro x _
    exact (fun a => Fin.elim0 a :
      Function.Injective (Continuum.BlockProducts.pointAt (n := 0) x))
variable (h : CitedFacts) (hD : TupleMetric.QuotientDistanceAndLifts)
  (hC : ContPartialsIffContDiff)
  (hDer : TupleDerivatives.Statement)
  (hForms : Continuum.BlockProducts.AssembledFormsAreDistributions)
  (Y : Params)
omit hD hC hDer hForms h in
theorem isCoordinateReadingOfSet_configSpace (Q : ℕ) :
    IsCoordinateImageOfSet (D := Y) (p := Q.succPNat)
      (Kind.pairwiseDistinct Y Kind.euclidean Q.succPNat)
      (Continuum.BlockProducts.configSpace (Q + 1)) := by
  refine Set.ext fun x => ?_
  exact Eq.to_iff (congrArg (· ∈ TestFunctions.injectiveTuples (Fin 4 → ℝ) (Q + 1))
    (proj_eq_pointAt Y (n := Q.succPNat) x).symm)
omit hD hC hDer hForms h in
theorem flatCoordinates_eq_comp_proj {Q : ℕ} (G : OrderedTestFun (Q + 1)) :
    flatCoordinates ⟨Q + 1, G⟩ =
      (show Kind.euclidean.Tuple Y Q.succPNat → ℂ from G) ∘
        Tuple.proj Y euclidean (p := Q.succPNat) := by
  funext x
  exact congrArg G (proj_eq_pointAt Y (n := Q.succPNat) x).symm
include h hD hDer hC hForms
theorem tendsto_assembledDistributionAt {Q : ℕ} {Fs : ℕ+ → OrderedTestFun (Q + 1)}
    {F : OrderedTestFun (Q + 1)}
    (hs : ∀ t, (show Kind.euclidean.Tuple Y Q.succPNat → ℂ from Fs t) ∈
      Tuple.testFns Y euclidean (Kind.pairwiseDistinct Y Kind.euclidean Q.succPNat))
    (h0 : (show Kind.euclidean.Tuple Y Q.succPNat → ℂ from F) ∈
      Tuple.testFns Y euclidean (Kind.pairwiseDistinct Y Kind.euclidean Q.succPNat))
    (hc : Tuple.TendstoInTestFns (fun t => ⟨_, hs t⟩) ⟨_, h0⟩) :
    IsOffDiagonalTest ⟨Q + 1, F⟩ ∧
      (∀ t, IsOffDiagonalTest ⟨Q + 1, Fs t⟩) ∧
      Tendsto (fun t => assembledDistributionAt u ⟨Q + 1, Fs t⟩) atTop
        (𝓝 (assembledDistributionAt u ⟨Q + 1, F⟩)) := by
  have hW := isCoordinateReadingOfSet_configSpace Y Q
  have hmem : ∀ G : OrderedTestFun (Q + 1),
      (show Kind.euclidean.Tuple Y Q.succPNat → ℂ from G) ∈
        Tuple.testFns Y euclidean
          (Kind.pairwiseDistinct Y Kind.euclidean Q.succPNat) →
      IsOffDiagonalTest ⟨Q + 1, G⟩ := fun G hG => by
    show flatCoordinates ⟨Q + 1, G⟩ ∈ _
    rw [flatCoordinates_eq_comp_proj Y G]
    exact (FlatReading.mem_testFns_iff hD Y hC hW _).1 hG
  have hF := hmem F h0
  have hFs := fun t => hmem (Fs t) (hs t)
  refine ⟨hF, hFs, ?_⟩
  obtain ⟨T, hT⟩ := (hForms u).2 (Q + 1) (by omega)
  have hcont := ((h.elementary (4 * (Q + 1)) (by omega)
    (Continuum.BlockProducts.configSpace (Q + 1))).2.1 T).1
  have hread : ∀ G : OrderedTestFun (Q + 1), IsOffDiagonalTest ⟨Q + 1, G⟩ →
      (show Kind.euclidean.Tuple Y Q.succPNat → ℂ from G) ∘
        Tuple.proj Y euclidean (p := Q.succPNat) ∈
        Euclidean.testFunctionSpace (Continuum.BlockProducts.configSpace (Q + 1)) :=
    fun G hG => Eq.mp (congrArg
      (· ∈ Euclidean.testFunctionSpace (Continuum.BlockProducts.configSpace (Q + 1)))
      (flatCoordinates_eq_comp_proj Y G)) hG
  have hT' := tendstoInTest_of_tendstoInTestFns hD hDer hC Y hW _ _ hc
    (fun t => hread _ (hFs t)) (hread _ hF)
  have hlim := hcont _ _ hT'
  have e : ∀ (G : OrderedTestFun (Q + 1)) (hG : IsOffDiagonalTest ⟨Q + 1, G⟩)
      (hG' : (show Kind.euclidean.Tuple Y Q.succPNat → ℂ from G) ∘
        Tuple.proj Y euclidean (p := Q.succPNat) ∈
        Euclidean.testFunctionSpace (Continuum.BlockProducts.configSpace (Q + 1))),
      assembledDistributionAt u ⟨Q + 1, G⟩ = T.form ⟨_, hG'⟩ := fun G hG hG' => by
    rw [assembledDistributionAt_of_isOffDiagonalTest u hG, hT]
    exact congrArg _ (Subtype.ext (flatCoordinates_eq_comp_proj Y G))
  have e₁ : (fun t => assembledDistributionAt u ⟨Q + 1, Fs t⟩) =
      fun t => T.form ⟨_, hread _ (hFs t)⟩ :=
    funext fun t => e _ (hFs t) _
  rw [e₁, e _ hF (hread _ hF)]
  exact hlim
end FormedDistributions
end YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep
end
end
section
open Filter TopologicalSpace YangMills.Construction.ReflectionSpaces YangMills.Construction.PeriodicSpace YangMills.Construction.PeriodicSpace.Kind
open YangMills.Construction.TorusTransport.TestFunctionOrders
open scoped ContDiff ENNReal NNReal Topology ComplexConjugate
noncomputable section
namespace YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep
variable (h : CitedFacts) (hD : TupleMetric.QuotientDistanceAndLifts)
  (hDer : TupleDerivatives.Statement)
  (hC : ContPartialsIffContDiff)
  (hForms : Continuum.BlockProducts.AssembledFormsAreDistributions)
  (Y : Params)
open FlatReading MirrorFamilies
include h hD hC in
theorem exists_smoothTensor_approximants (μ : Fin 4) (c : ℝ) (q : ℕ) (F : OrderedTestFun (q + 1))
    (hF : F ∈ Distributions.testFunctionSpace
      (Distributions.offDiagonalPower (openHalfSpace μ c) (q + 1))) :
    ∃ Fs : ℕ+ → OrderedTestFun (q + 1),
      (∀ t, Fs t ∈ smoothSepTensors Y (openHalfSpace μ c : Set (Fin 4 → ℝ)) (q + 1)) ∧
      TendstoInInjTestFns Y (openHalfSpace μ c : Set (Fin 4 → ℝ)) (n := q.succPNat) Fs F := by
  have hO : IsOpen (openHalfSpace μ c : Set (Fin 4 → ℝ)) := (openHalfSpace μ c).isOpen
  have hW := isCoordinateReadingOfSet_injTuplesOpens Y hO q.succPNat
  obtain ⟨h₁, h₂, h₃⟩ := hF
  have hπ : ContDiff ℝ ∞ fun (x : Coords q.succPNat) (i : Fin (q + 1)) (ν : Fin 4) =>
      x ⟨4 * (i : ℕ) + (ν : ℕ), by have := i.2; have := ν.2; simp; omega⟩ :=
    contDiff_pi.2 fun _ => contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ _
  have hmem : F ∈ injTestFns Y (openHalfSpace μ c : Set (Fin 4 → ℝ)) q.succPNat := by
    refine (FlatReading.mem_testFns_iff hD Y hC hW F).2
      ⟨h₁.comp hπ, h₂.comp_homeomorph (projHomeomorph Y q.succPNat), ?_⟩
    have hts := tsupport_comp_eq_preimage F (projHomeomorph Y q.succPNat)
    intro x hx
    have hx' : projHomeomorph Y q.succPNat x ∈ tsupport F := hts.subset hx
    obtain ⟨hp, hi⟩ := h₃ hx'
    exact mem_injTuplesIn.2 ⟨fun i => hp i trivial, hi⟩
  obtain ⟨-, hdense, -⟩ := h.density Y q.succPNat (openHalfSpace μ c : Set (Fin 4 → ℝ))
    (isOpenQ_euclidean_of_isOpen Y hO)
  obtain ⟨Fs, hsm, hc⟩ := hdense ⟨F, hmem⟩
  exact ⟨fun t => (Fs t).1, hsm, fun t => (Fs t).2, hmem, hc⟩
include h hD hDer hC hForms in
theorem tendsto_assembledDistributionAt_reflectedTensor
    (u : Continuum.BlockProducts.DistribFamily) (μ : Fin 4)
    (c : ℝ) (q₀ : ℕ) (F : TestFamily) (Ft : ℕ+ → TestFamily) (h0 : ∀ t, Ft t 0 = F 0)
    (hconv : ∀ q, q + 1 ≤ q₀ → TendstoInInjTestFns Y (openHalfSpace μ c : Set (Fin 4 → ℝ)) (n := q.succPNat)
      (fun t => Ft t (q + 1)) (F (q + 1))) :
    (∀ q q', q ≤ q₀ → q' ≤ q₀ → IsOffDiagonalTest (reflectedTensor μ c F F q q')) ∧
    ∀ q q', q ≤ q₀ → q' ≤ q₀ →
      Tendsto (fun t => assembledDistributionAt u (reflectedTensor μ c (Ft t) (Ft t) q q')) atTop
        (𝓝 (assembledDistributionAt u (reflectedTensor μ c F F q q'))) := by
  have hO : IsOpen (openHalfSpace μ c : Set (Fin 4 → ℝ)) := (openHalfSpace μ c).isOpen
  have hO' : IsOpen (reflectionPerm μ c ⁻¹' (openHalfSpace μ c : Set (Fin 4 → ℝ))) :=
    hO.preimage (continuous_reflectionPerm μ c)
  have hdisj : reflectionPerm μ c ⁻¹' (openHalfSpace μ c : Set (Fin 4 → ℝ)) ∩
      (openHalfSpace μ c : Set (Fin 4 → ℝ)) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    have h₁ : c < reflectionPerm μ c x μ := hx.1
    have h₂ : c < x μ := hx.2
    rw [BallPeriodization.hyperplaneReflection_apply] at h₁
    simp [PeriodicLattice.coordVec] at h₁
    linarith
  have hA : ∀ q, q + 1 ≤ q₀ → IsOffDiagonalTest ⟨q + 1, F (q + 1)⟩ ∧
      (∀ t, IsOffDiagonalTest ⟨q + 1, Ft t (q + 1)⟩) ∧
      Tendsto (fun t => assembledDistributionAt u ⟨q + 1, Ft t (q + 1)⟩) atTop
        (𝓝 (assembledDistributionAt u ⟨q + 1, F (q + 1)⟩)) := fun q hq => by
    obtain ⟨hs, h₀, hc⟩ := convergesOn_pairwiseDistinct Y (hconv q hq)
    exact tendsto_assembledDistributionAt u h hD hC hDer hForms Y hs h₀ hc
  have hB : ∀ q, q + 1 ≤ q₀ →
      IsOffDiagonalTest ⟨q + 1, conjReflected μ c (F (q + 1))⟩ ∧
      (∀ t, IsOffDiagonalTest ⟨q + 1, conjReflected μ c (Ft t (q + 1))⟩) ∧
      Tendsto (fun t => assembledDistributionAt u ⟨q + 1, conjReflected μ c (Ft t (q + 1))⟩) atTop
        (𝓝 (assembledDistributionAt u ⟨q + 1, conjReflected μ c (F (q + 1))⟩)) := fun q hq => by
    obtain ⟨hs, h₀, hc⟩ := convergesOn_pairwiseDistinct Y
      (convergesOn_conjReflected h hD hDer hC Y μ c hO (hconv q hq))
    exact tendsto_assembledDistributionAt u h hD hC hDer hForms Y hs h₀ hc
  have key : ∀ q q', q ≤ q₀ → q' ≤ q₀ →
      IsOffDiagonalTest (reflectedTensor μ c F F q q') ∧
      Tendsto (fun t => assembledDistributionAt u (reflectedTensor μ c (Ft t) (Ft t) q q')) atTop
        (𝓝 (assembledDistributionAt u (reflectedTensor μ c F F q q'))) := by
    intro q q' hq hq'
    rcases q with _ | q <;> rcases q' with _ | q'
    · have e : ∀ t, assembledDistributionAt u (reflectedTensor μ c (Ft t) (Ft t) 0 0) =
          assembledDistributionAt u (reflectedTensor μ c F F 0 0) := fun t => by
        show assembledDistributionAt u ⟨0, conj (Ft t 0 : ℂ) * (Ft t 0 : ℂ)⟩ =
          assembledDistributionAt u ⟨0, conj (F 0 : ℂ) * (F 0 : ℂ)⟩
        rw [h0]
      exact ⟨isOffDiagonalTest_zero _, by simp only [e]; exact tendsto_const_nhds⟩
    · obtain ⟨hT, hTs, hL⟩ := hA q' hq'
      have e : ∀ t, assembledDistributionAt u (reflectedTensor μ c (Ft t) (Ft t) 0 (q' + 1)) =
          conj (F 0 : ℂ) * assembledDistributionAt u ⟨q' + 1, Ft t (q' + 1)⟩ := fun t => by
        show assembledDistributionAt u ⟨q' + 1, fun x => conj (Ft t 0 : ℂ) * Ft t (q' + 1) x⟩ = _
        rw [h0]
        exact assembledDistributionAt_const_mul u _ (hTs t)
      have e₀ : assembledDistributionAt u (reflectedTensor μ c F F 0 (q' + 1)) =
          conj (F 0 : ℂ) * assembledDistributionAt u ⟨q' + 1, F (q' + 1)⟩ :=
        assembledDistributionAt_const_mul u _ hT
      refine ⟨isOffDiagonalTest_const_mul _ hT, ?_⟩
      simp only [e, e₀]
      exact hL.const_mul _
    · obtain ⟨hT, hTs, hL⟩ := hB q hq
      have e : ∀ t, assembledDistributionAt u (reflectedTensor μ c (Ft t) (Ft t) (q + 1) 0) =
          (F 0 : ℂ) * assembledDistributionAt u ⟨q + 1, conjReflected μ c (Ft t (q + 1))⟩ :=
          fun t => by
        show assembledDistributionAt u
          ⟨q + 1, fun x => (Ft t 0 : ℂ) * conjReflected μ c (Ft t (q + 1)) x⟩ = _
        rw [h0]
        exact assembledDistributionAt_const_mul u _ (hTs t)
      have e₀ : assembledDistributionAt u (reflectedTensor μ c F F (q + 1) 0) =
          (F 0 : ℂ) * assembledDistributionAt u ⟨q + 1, conjReflected μ c (F (q + 1))⟩ :=
        assembledDistributionAt_const_mul u _ hT
      refine ⟨isOffDiagonalTest_const_mul _ hT, ?_⟩
      simp only [e, e₀]
      exact hL.const_mul _
    · obtain ⟨hs₁, h₁, c₁⟩ := convergesOn_conjReflected h hD hDer hC Y μ c hO (hconv q hq)
      obtain ⟨hs₂, h₂, c₂⟩ := hconv q' hq'
      obtain ⟨hs, h₀, cc⟩ := (h.density Y q.succPNat _ (isOpenQ_euclidean_of_isOpen Y hO')).2.2.2
        q'.succPNat _ (isOpenQ_euclidean_of_isOpen Y hO) hdisj _ _ _ _ c₁ c₂
      obtain ⟨hT, -, hL⟩ := tendsto_assembledDistributionAt u h hD hC hDer hForms Y (Q := q + 1 + q')
        (Fs := fun t => YangMills.Construction.TorusTransport.TestFunctionOrders.tensor
          (p := q + 1) (q := q' + 1) (conjReflected μ c (Ft t (q + 1))) (Ft t (q' + 1)))
        (F := YangMills.Construction.TorusTransport.TestFunctionOrders.tensor
          (p := q + 1) (q := q' + 1) (conjReflected μ c (F (q + 1))) (F (q' + 1)))
        hs h₀ cc
      exact ⟨hT, hL⟩
  exact ⟨fun q q' hq hq' => (key q q' hq hq').1, fun q q' hq hq' => (key q q' hq hq').2⟩
end YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep
end
end
section
open Set Filter Topology
open scoped NNReal ENNReal ComplexConjugate ContDiff
noncomputable section
namespace YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep
open YangMills.Construction.PeriodicSpace YangMills.Construction.TorusTransport.TestFunctionOrders
open YangMills.Construction.Continuum.BlockProducts YangMills.Construction.SetPartition
  YangMills.Construction.AmbientPoints MirrorFamilies
def flatTensor {n : ℕ} (X : Fin n → (Fin 4 → ℝ) → ℝ) :
    ReflectionSpaces.Euclidean.Coord (4 * n) → ℂ :=
  fun x => ∏ i, ((X i (pointAt x i) : ℝ) : ℂ)
def flattenPoints {n : ℕ} (y : Fin n → Fin 4 → ℝ) :
    ReflectionSpaces.Euclidean.Coord (4 * n) :=
  fun k => y ((pointCoordEquiv n).symm k).1 ((pointCoordEquiv n).symm k).2
theorem flattenPoints_pointAt {n : ℕ} (x : ReflectionSpaces.Euclidean.Coord (4 * n)) :
    flattenPoints (fun i => pointAt x i) = x := by
  funext k
  simp [flattenPoints, pointAt]
theorem flatTensor_mem {n : ℕ} {X : Fin n → (Fin 4 → ℝ) → ℝ}
    (hs : ∀ i, ContDiff ℝ ∞ (X i)) (hc : ∀ i, HasCompactSupport (X i))
    (hd : ∀ i k, i ≠ k → Disjoint (tsupport (X i)) (tsupport (X k))) :
    flatTensor X ∈
      ReflectionSpaces.Euclidean.testFunctionSpace (configSpace n) := by
  set K : Set (ReflectionSpaces.Euclidean.Coord (4 * n)) :=
    {x | ∀ i, pointAt x i ∈ tsupport (X i)} with hK
  have hKc : IsClosed K := by
    rw [hK, Set.ofPred_forall]
    exact isClosed_iInter fun i =>
      (isClosed_tsupport (X i)).preimage (continuous_pointAt i)
  have hKcomp : IsCompact K := by
    have h₁ : IsCompact (Set.univ.pi fun i => tsupport (X i)) :=
      isCompact_univ_pi fun i => hc i
    have hg : Continuous (flattenPoints (n := n)) :=
      continuous_pi fun k => (continuous_apply _).comp (continuous_apply _)
    refine (h₁.image hg).of_isClosed_subset hKc fun x hx => ?_
    exact ⟨fun i => pointAt x i, fun i _ => hx i,
      flattenPoints_pointAt x⟩
  have hsub : Function.support (flatTensor X) ⊆ K := by
    intro x hx i
    have hne : flatTensor X x ≠ 0 := hx
    have : ((X i (pointAt x i) : ℝ) : ℂ) ≠ 0 :=
      fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ i) h0)
    exact subset_tsupport _ (fun h0 => this (by rw [h0]; simp))
  have hts : tsupport (flatTensor X) ⊆ K := closure_minimal hsub hKc
  refine ⟨?_, hKcomp.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans ?_⟩
  · unfold flatTensor
    refine contDiff_prod fun i _ => ?_
    refine Complex.ofRealCLM.contDiff.comp ((hs i).comp ?_)
    exact contDiff_pi.2 fun μ => contDiff_apply ℝ ℝ _
  · intro x hx i k hik
    by_contra hne
    exact Set.disjoint_left.1 (hd i k hne) (hx i) (hik ▸ hx k)
variable {D : Setup}
theorem flatTensor_mem_of_sepDomain {n : ℕ} {X : Fin n → (Fin 4 → ℝ) → ℝ}
    (hX : X ∈ D.sepDomain n) (hs : ∀ i, ContDiff ℝ ∞ (X i)) :
    flatTensor X ∈
      ReflectionSpaces.Euclidean.testFunctionSpace (configSpace n) := by
  obtain ⟨-, hk, hd⟩ := (BallTuples.mem_sepC1Tuples_euclidean_iff X).1 hX
  exact flatTensor_mem hs hk hd
theorem member_value_flatTensor {Ξ : D.LimitHierarchy} (hMem : MembersAreDistribs Ξ)
    {u : DistribFamily} (hu : IsMemberFamily Ξ u) {n : ℕ} (hn : 2 ≤ n)
    (X : D.sepDomain n) (hs : ∀ i, ContDiff ℝ ∞ (X.1 i))
    (h : flatTensor X.1 ∈
      ReflectionSpaces.Euclidean.testFunctionSpace (configSpace n)) :
    (u n hn).form ⟨_, h⟩ = ((Ξ.func n hn X : ℝ) : ℂ) := by
  let n' : ℕ+ := ⟨n, by omega⟩
  obtain ⟨T, hT, -⟩ := (hMem n' hn).1
  have hread := hu n' hn T hT
  obtain ⟨hφ, hF, hval⟩ := hT.2 X.1 X.2 (fun i => hs i)
  have := hread _ hF h
  exact this.trans hval
theorem flatTensor_comp_regroup_symm {Q : ℕ} (π : PartitionsFin Q)
    (X : Fin Q → (Fin 4 → ℝ) → ℝ) :
    flatTensor X ∘ (regroup π).symm =
      Continuum.TensorProduct.tensorFn (fun i => 4 * orderedBlockCard π i)
        fun i => flatTensor fun a => X (blockMemberIndex π ⟨i, a⟩) := by
  funext y
  obtain ⟨x, rfl⟩ := (regroup π).surjective y
  simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
  simp only [Continuum.TensorProduct.tensorFn, flatTensor]
  simp only [pointAt_blockComponent_regroup]
  rw [Finset.prod_sigma', Finset.univ_sigma_univ]
  exact (Fintype.prod_bijective _ (blockMemberIndex_bijective π) _ _ fun _ => rfl).symm
theorem partitionForm_flatTensor (h : CitedFacts) {Ξ : D.LimitHierarchy} (hMem : MembersAreDistribs Ξ)
    {u : DistribFamily} (hu : IsMemberFamily Ξ u) {Q : ℕ} (hQ : 1 ≤ Q)
    {π : PartitionsFin Q} (hπ : π ∈ nonSingletonPartitions Q) (X : D.sepDomain Q)
    (hs : ∀ i, ContDiff ℝ ∞ (X.1 i))
    (hX : flatTensor X.1 ∈
      ReflectionSpaces.Euclidean.testFunctionSpace (distinctWithinBlocks π)) :
    partitionForm u hπ ⟨_, hX⟩ =
      ∏ i, ((Ξ.func (orderedBlockCard π i) (two_le_orderedBlockCard hπ i)
        ⟨Kind.restrictTuple _ _ X.1 (orderedBlock π i),
          Kind.restrictTuple_mem_sepC1Tuples _ _ X.2 _⟩ : ℝ) : ℂ) := by
  have hr : 1 ≤ blockCount π := by
    have hne : π.parts.Nonempty := by
      have h0 : (⟨0, hQ⟩ : Fin Q) ∈ (Finset.univ : Finset (Fin Q)) := Finset.mem_univ _
      exact ⟨_, π.part_mem.2 h0⟩
    exact Finset.card_pos.2 hne
  have key := (h.product (blockCount π) hr (fun i => 4 * orderedBlockCard π i)
    (fun i => by have := two_le_orderedBlockCard hπ i; omega)
    (fun i => configSpace (orderedBlockCard π i))
    (fun i => u _ (two_le_orderedBlockCard hπ i))).1
  let X' : ∀ i, Fin (orderedBlockCard π i) → (Fin 4 → ℝ) → ℝ :=
    fun i a => X.1 (blockMemberIndex π ⟨i, a⟩)
  have hsub : ∀ i, X' i ∈ D.sepDomain (orderedBlockCard π i) := fun i =>
    Kind.restrictTuple_mem_sepC1Tuples _ _ X.2 (orderedBlock π i)
  have hss : ∀ i a, ContDiff ℝ ∞ (X' i a) := fun i a => hs _
  let φ : ∀ i, ReflectionSpaces.Euclidean.testFunctionSpace
      (configSpace (orderedBlockCard π i)) := fun i =>
    ⟨_, flatTensor_mem_of_sepDomain (hsub i) (hss i)⟩
  obtain ⟨hφ, hval⟩ := key φ
  have hfun : regroupTest π ⟨_, hX⟩ = ⟨_, hφ⟩ :=
    Subtype.ext (flatTensor_comp_regroup_symm π X.1)
  show (Continuum.TensorProduct.tensorDist _).form (regroupTest π ⟨_, hX⟩) = _
  rw [hfun, hval]
  exact Finset.prod_congr rfl fun i _ =>
    member_value_flatTensor hMem hu (two_le_orderedBlockCard hπ i) ⟨_, hsub i⟩ (hss i) _
theorem nonSingletonPartitions_eq_partitionsNoSingletons (Q : ℕ) :
    nonSingletonPartitions Q = PeriodicSpace.partitionsNoSingletons Q := by
  ext π
  simp only [nonSingletonPartitions, PeriodicSpace.partitionsNoSingletons,
    Finset.mem_filter, Finset.mem_univ, true_and]
  refine forall₂_congr fun J hJ => ?_
  have h0 : 0 < J.card := Finset.card_pos.2 (π.nonempty_of_mem_parts hJ)
  omega
theorem assembledForm_flatTensor (h : CitedFacts) {Ξ : D.LimitHierarchy} (hMem : MembersAreDistribs Ξ)
    {u : DistribFamily} (hu : IsMemberFamily Ξ u) {Q : ℕ} (hQ : 1 ≤ Q)
    (X : D.sepDomain Q) (hs : ∀ i, ContDiff ℝ ∞ (X.1 i))
    (hX : flatTensor X.1 ∈
      ReflectionSpaces.Euclidean.testFunctionSpace (configSpace Q)) :
    assembledForm Q u ⟨_, hX⟩ = ((Ξ.partitionMoment X : ℝ) : ℂ) := by
  rw [assembledForm, LinearMap.sum_apply]
  unfold Kind.Hierarchy.partitionMoment
  push_cast
  refine Finset.sum_bij (fun π _ => ⟨π.1, nonSingletonPartitions_eq_partitionsNoSingletons Q ▸ π.2⟩)
    (fun _ _ => Finset.mem_attach _ _) (fun π _ π' _ e => Subtype.ext (Subtype.mk_eq_mk.1 e))
    (fun π _ => ⟨⟨π.1, (nonSingletonPartitions_eq_partitionsNoSingletons Q).symm ▸ π.2⟩,
      Finset.mem_attach _ _, rfl⟩)
    fun π _ => ?_
  refine (partitionForm_flatTensor h hMem hu hQ π.2 X hs _).trans ?_
  refine Finset.prod_bij (fun i _ => ⟨orderedBlock π.1 i, orderedBlock_mem π.1 i⟩)
    (fun _ _ => Finset.mem_attach _ _)
    (fun i _ i' _ e => orderedBlock_injective π.1 (congrArg Subtype.val e))
    (fun J _ => ?_) fun i _ => rfl
  obtain ⟨i, hi⟩ := exists_orderedBlock_eq π.1 J.2
  exact ⟨i, Finset.mem_univ _, Subtype.ext hi⟩
theorem assembledForm_eq_momentExtensionAt_of_mem_smoothTensors (h : CitedFacts) {Ξ : D.LimitHierarchy}
    (hMem : MembersAreDistribs Ξ) {u : DistribFamily} (hu : IsMemberFamily Ξ u)
    (hE : MomentLinearExtension Ξ) (q : ℕ) (A : OrderedTestFun (q + 1))
    (hA : A ∈ smoothSepTensors D.euclidParams Set.univ (q + 1)) :
    ∃ hT : IsOffDiagonalTest ⟨q + 1, A⟩,
      A ∈ sepTensorSubmodule D.euclidParams Set.univ (q + 1) ∧
        assembledForm (q + 1) u ⟨_, hT⟩ = momentExtensionAt Ξ ⟨q + 1, A⟩ := by
  refine Submodule.span_induction (p := fun A _ => ∃ hT : IsOffDiagonalTest ⟨q + 1, A⟩,
      A ∈ sepTensorSubmodule D.euclidParams Set.univ (q + 1) ∧
        assembledForm (q + 1) u ⟨_, hT⟩ = momentExtensionAt Ξ ⟨q + 1, A⟩) ?_ ?_ ?_ ?_ hA
  · rintro _ ⟨f₀, hf₀, hs, -, rfl⟩
    let f : Fin (q + 1) → (Fin 4 → ℝ) → ℝ := f₀
    have hf : f ∈ D.sepDomain (q + 1) := hf₀
    have hs' : ∀ i, ContDiff ℝ ∞ (f i) := hs
    have hX : flatTensor f ∈
        ReflectionSpaces.Euclidean.testFunctionSpace (configSpace (q + 1)) :=
      flatTensor_mem_of_sepDomain (D := D) hf hs'
    refine ⟨hX, realTensor_mem_sepTensorSpanOn D.euclidParams ⟨f, hf⟩, ?_⟩
    exact (assembledForm_flatTensor h hMem hu (Nat.succ_pos q) ⟨f, hf⟩ hs' hX).trans
      (hE.at_tensor q ⟨f, hf⟩).symm
  · have hT : IsOffDiagonalTest ⟨q + 1, 0⟩ :=
      Submodule.zero_mem (ReflectionSpaces.Euclidean.testFunctionSpace _)
    have h0 : (0 : OrderedTestFun (q + 1)) ∈
        sepTensorSubmodule D.euclidParams Set.univ (q + 1) := Submodule.zero_mem _
    refine ⟨hT, h0, ?_⟩
    have e₁ : (⟨_, hT⟩ : ReflectionSpaces.Euclidean.testFunctionSpace
        (configSpace (q + 1))) = 0 := rfl
    have hl := hE.is_linear (q + 1) 0 0 0 0 h0 h0
    simp only [zero_smul, add_zero, zero_mul] at hl
    rw [e₁, map_zero, hl]
  · rintro x y _ _ ⟨hx, mx, ex⟩ ⟨hy, my, ey⟩
    have hT : IsOffDiagonalTest ⟨q + 1, x + y⟩ :=
      Submodule.add_mem (ReflectionSpaces.Euclidean.testFunctionSpace _) hx hy
    refine ⟨hT, Submodule.add_mem _ mx my, ?_⟩
    have e₁ : (⟨_, hT⟩ : ReflectionSpaces.Euclidean.testFunctionSpace
        (configSpace (q + 1))) = ⟨_, hx⟩ + ⟨_, hy⟩ := rfl
    have hl := hE.is_linear (q + 1) x y 1 1 mx my
    simp only [one_smul, one_mul] at hl
    rw [e₁, map_add, ex, ey]
    exact hl.symm
  · rintro a x _ ⟨hx, mx, ex⟩
    have hT : IsOffDiagonalTest ⟨q + 1, a • x⟩ :=
      Submodule.smul_mem (ReflectionSpaces.Euclidean.testFunctionSpace _) a hx
    refine ⟨hT, Submodule.smul_mem _ a mx, ?_⟩
    have e₁ : (⟨_, hT⟩ : ReflectionSpaces.Euclidean.testFunctionSpace
        (configSpace (q + 1))) = a • ⟨_, hx⟩ := rfl
    have hl := hE.is_linear (q + 1) x 0 a 0 mx (Submodule.zero_mem _)
    simp only [zero_smul, add_zero, zero_mul] at hl
    refine (congrArg (assembledForm (q + 1) u) e₁).trans ((map_smul _ a _).trans ?_)
    rw [ex, smul_eq_mul]
    exact hl.symm
theorem assembledDistributionAt_eq_momentExtensionAt (h : CitedFacts) {Ξ : D.LimitHierarchy}
    (hMem : MembersAreDistribs Ξ) (u : DistribFamily) (hu : IsMemberFamily Ξ u)
    (hE : MomentLinearExtension Ξ) (Q : ℕ) (A : OrderedTestFun Q)
    (hA : A ∈ smoothSepTensors D.euclidParams Set.univ Q) :
    assembledDistributionAt u ⟨Q, A⟩ = momentExtensionAt Ξ ⟨Q, A⟩ := by
  cases Q with
  | zero => exact (hE.at_zero A).symm
  | succ q =>
    obtain ⟨hT, -, he⟩ := assembledForm_eq_momentExtensionAt_of_mem_smoothTensors h hMem hu hE q A hA
    rw [assembledDistributionAt, dif_pos hT]
    exact he
end YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep
end
end
