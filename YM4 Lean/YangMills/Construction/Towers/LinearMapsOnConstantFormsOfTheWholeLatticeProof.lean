import YangMills.Construction.Towers.BlocksOfATowerProof
import YangMills.Construction.Towers.DilationCarriesValuesAtAStepOfTheWholeSpaceProof
import YangMills.Construction.Towers.LinearMapsOnConstantFormsOfTheWholeLattice
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace Tower.FullSpace.ConstantForms
section SingleSpacing
variable {a' : ℝ} {B : InfiniteLattice.Link a' → Matrices.ComplexMatrix2}
  {v : Fin 4 → Matrices.ComplexMatrix2}
theorem backwardLink_eq_neg (hr : ∀ b : InfiniteLattice.Link a', B b.opposite = -B b)
    (hc : ∀ (x : InfiniteLattice.LatticePoint a') (μ : Fin 4),
      B (InfiniteLattice.Link.forwardFrom x μ) = v μ)
    (x : InfiniteLattice.LatticePoint a') (μ : Fin 4) : B (FullSpace.backwardLink x μ) = -v μ := by
  have h : FullSpace.backwardLink x μ =
      (InfiniteLattice.Link.forwardFrom (x - InfiniteLattice.axisStep a' μ) μ).opposite := by
    apply InfiniteLattice.Link.ext
    · simp [FullSpace.backwardLink, InfiniteLattice.Link.opposite, InfiniteLattice.Link.forwardFrom]
    · simp [FullSpace.backwardLink, InfiniteLattice.Link.opposite, InfiniteLattice.Link.forwardFrom]
  rw [h, hr, hc]
theorem sumAlong_forwardSteps
    (hc : ∀ (x : InfiniteLattice.LatticePoint a') (μ : Fin 4),
      B (InfiniteLattice.Link.forwardFrom x μ) = v μ)
    (μ : Fin 4) (n : ℕ) (x : InfiniteLattice.LatticePoint a') :
    FullSpace.sumAlong B (FullSpace.forwardSteps x μ n) = n • v μ := by
  induction n generalizing x with
  | zero => simp [FullSpace.forwardSteps, FullSpace.sumAlong]
  | succ n ih =>
    have h := ih (x + InfiniteLattice.axisStep a' μ)
    rw [FullSpace.sumAlong] at h
    rw [FullSpace.forwardSteps, FullSpace.sumAlong, List.map_cons, List.sum_cons, hc, h,
      succ_nsmul, add_comm]
theorem sumAlong_backwardSteps (hr : ∀ b : InfiniteLattice.Link a', B b.opposite = -B b)
    (hc : ∀ (x : InfiniteLattice.LatticePoint a') (μ : Fin 4),
      B (InfiniteLattice.Link.forwardFrom x μ) = v μ)
    (μ : Fin 4) (n : ℕ) (x : InfiniteLattice.LatticePoint a') :
    FullSpace.sumAlong B (FullSpace.backwardSteps x μ n) = -(n • v μ) := by
  induction n generalizing x with
  | zero => simp [FullSpace.backwardSteps, FullSpace.sumAlong]
  | succ n ih =>
    have h := ih (x - InfiniteLattice.axisStep a' μ)
    rw [FullSpace.sumAlong] at h
    rw [FullSpace.backwardSteps, FullSpace.sumAlong, List.map_cons, List.sum_cons,
      backwardLink_eq_neg hr hc, h, succ_nsmul]
    abel
theorem sumAlong_signedSteps (hr : ∀ b : InfiniteLattice.Link a', B b.opposite = -B b)
    (hc : ∀ (x : InfiniteLattice.LatticePoint a') (μ : Fin 4),
      B (InfiniteLattice.Link.forwardFrom x μ) = v μ)
    (μ : Fin 4) (n : ℤ) (x : InfiniteLattice.LatticePoint a') :
    FullSpace.sumAlong B (FullSpace.signedSteps x μ n) = n • v μ := by
  unfold FullSpace.signedSteps
  split_ifs with h
  · rw [sumAlong_forwardSteps hc, ← natCast_zsmul, Int.toNat_of_nonneg h]
  · rw [sumAlong_backwardSteps hr hc, ← natCast_zsmul, Int.toNat_of_nonneg (by omega), neg_smul,
      neg_neg]
theorem sumAlong_stepsInOrder (hr : ∀ b : InfiniteLattice.Link a', B b.opposite = -B b)
    (hc : ∀ (x : InfiniteLattice.LatticePoint a') (μ : Fin 4),
      B (InfiniteLattice.Link.forwardFrom x μ) = v μ)
    (ν : Fin 4 → ℤ) (l : List (Fin 4)) (x : InfiniteLattice.LatticePoint a') :
    FullSpace.sumAlong B (FullSpace.stepsInOrder ν x l) = (l.map fun μ => ν μ • v μ).sum := by
  induction l generalizing x with
  | nil => simp [FullSpace.stepsInOrder, FullSpace.sumAlong]
  | cons μ l ih =>
    have h := ih (x + ν μ • InfiniteLattice.axisStep a' μ)
    have h' := sumAlong_signedSteps hr hc μ (ν μ) x
    rw [FullSpace.sumAlong] at h h'
    rw [FullSpace.stepsInOrder, FullSpace.sumAlong, List.map_append, List.sum_append, h, h',
      List.map_cons, List.sum_cons]
theorem coe_zsmul_axisStep (n : ℤ) (μ : Fin 4) :
    ((n • InfiniteLattice.axisStep a' μ : InfiniteLattice.LatticePoint a') : AmbientSpace) =
      Pi.single μ ((n : ℝ) * a') := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.coe_zsmul_axisStep <;> assumption
theorem sumAlong_axisPath (ha : a' ≠ 0) (hr : ∀ b : InfiniteLattice.Link a', B b.opposite = -B b)
    (hc : ∀ (x : InfiniteLattice.LatticePoint a') (μ : Fin 4),
      B (InfiniteLattice.Link.forwardFrom x μ) = v μ)
    {x x' : InfiniteLattice.LatticePoint a'} {μ : Fin 4} {n : ℤ} (hn : n ≠ 0)
    (hx : x' - x = n • InfiniteLattice.axisStep a' μ) :
    FullSpace.sumAlong B (FullSpace.axisPath x x') = n • v μ := by
  have hex : ∃ q : Fin 4 × ℤ, FullSpace.IsAxisDisplacement x x' q.1 q.2 := ⟨(μ, n), hx⟩
  have hq : hex.choose = (μ, n) := by
    have hs : x' - x = hex.choose.2 • InfiniteLattice.axisStep a' hex.choose.1 := hex.choose_spec
    generalize hex.choose = q at hs ⊢
    obtain ⟨μ', n'⟩ := q
    replace hs : x' - x = n' • InfiniteLattice.axisStep a' μ' := hs
    have hco : (Pi.single μ' ((n' : ℝ) * a') : AmbientSpace) = Pi.single μ ((n : ℝ) * a') := by
      rw [← coe_zsmul_axisStep, ← coe_zsmul_axisStep]
      exact congrArg _ (hs.symm.trans hx)
    have hnr : (n : ℝ) * a' ≠ 0 := mul_ne_zero (by exact_mod_cast hn) ha
    have hμ : μ' = μ := by
      by_contra hne
      have h1 := congrFun hco μ
      rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at h1
      exact hnr h1.symm
    subst hμ
    have h1 := congrFun hco μ'
    rw [Pi.single_eq_same, Pi.single_eq_same] at h1
    have h2 : (n' : ℝ) = n := mul_right_cancel₀ ha h1
    have h3 : n' = n := by exact_mod_cast h2
    rw [h3]
  unfold FullSpace.axisPath
  rw [dif_pos hex, hq]
  exact sumAlong_signedSteps hr hc μ n x
end SingleSpacing
section Cubes
variable {L : ℕ} {a a' : ℝ} {B : InfiniteLattice.Link a' → Matrices.ComplexMatrix2}
  {v : Fin 4 → Matrices.ComplexMatrix2}
theorem isCubeOffset_unique (ha : a' ≠ 0) {y : InfiniteLattice.LatticePoint a}
    {x : InfiniteLattice.LatticePoint a'} {ν ν' : Fin 4 → ℤ} (h : FullSpace.IsCubeOffset L y x ν)
    (h' : FullSpace.IsCubeOffset L y x ν') : ν = ν' := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingOfValues.cubeOffset_unique <;> assumption
theorem mem_cubeVertices_iff {y : InfiniteLattice.LatticePoint a}
    {x : InfiniteLattice.LatticePoint a'} :
    x ∈ FullSpace.cubeVertices L a' y ↔ ∃ ν, FullSpace.IsCubeOffset L y x ν := by
  constructor
  · rintro ⟨ν, hb, hx⟩
    exact ⟨ν, by rw [hx]; simp, fun μ => by simpa using hb μ⟩
  · rintro ⟨ν, hx, hb⟩
    exact ⟨ν, fun μ => by simpa using hb μ, by rw [← hx]; simp⟩
theorem contourAverage_eq_sum (ha : a' ≠ 0)
    (hr : ∀ b : InfiniteLattice.Link a', B b.opposite = -B b)
    (hc : ∀ (x : InfiniteLattice.LatticePoint a') (μ : Fin 4),
      B (InfiniteLattice.Link.forwardFrom x μ) = v μ)
    {y : InfiniteLattice.LatticePoint a} {x : InfiniteLattice.LatticePoint a'} {ν : Fin 4 → ℤ}
    (h : FullSpace.IsCubeOffset L y x ν) :
    FullSpace.contourAverage L B y x = ∑ μ, ν μ • v μ := by
  have hν : FullSpace.cubeOffset L y x = ν :=
    isCubeOffset_unique ha
      (Classical.epsilon_spec (⟨ν, h⟩ : ∃ ν, FullSpace.IsCubeOffset L y x ν)) h
  have hσ : ∀ σ : FullSpace.ContourOrder L y x, FullSpace.sumAlong B (FullSpace.contour L y x σ) =
      ∑ μ, FullSpace.cubeOffset L y x μ • v μ := by
    intro σ
    rw [FullSpace.contour, sumAlong_stepsInOrder hr hc, List.map_map, ← Fin.sum_univ_def]
    calc ∑ i, ((fun μ => FullSpace.cubeOffset L y x μ • v μ) ∘
            fun i => ((σ i : FullSpace.offsetSupport L y x) : Fin 4)) i
        = ∑ s : FullSpace.offsetSupport L y x,
            FullSpace.cubeOffset L y x (s : Fin 4) • v (s : Fin 4) :=
          Equiv.sum_comp σ fun s : FullSpace.offsetSupport L y x =>
            FullSpace.cubeOffset L y x (s : Fin 4) • v (s : Fin 4)
      _ = ∑ μ ∈ FullSpace.offsetSupport L y x, FullSpace.cubeOffset L y x μ • v μ :=
          Finset.sum_coe_sort (FullSpace.offsetSupport L y x)
            fun μ => FullSpace.cubeOffset L y x μ • v μ
      _ = ∑ μ, FullSpace.cubeOffset L y x μ • v μ := by
          refine Finset.sum_subset (Finset.subset_univ _) fun μ _ hμ => ?_
          have h0 : FullSpace.cubeOffset L y x μ = 0 := by
            by_contra hne
            exact hμ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
          rw [h0, zero_smul]
  have hne : Nonempty (FullSpace.ContourOrder L y x) :=
    ⟨(FullSpace.offsetSupport L y x).equivFin.symm⟩
  have hcard : (Fintype.card (FullSpace.ContourOrder L y x) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold FullSpace.contourAverage
  simp_rw [hσ]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hν]
  have h1 : ((((Fintype.card (FullSpace.ContourOrder L y x) : ℝ)⁻¹ : ℝ) : ℂ)) *
      (Fintype.card (FullSpace.ContourOrder L y x) : ℂ) = 1 := by
    push_cast
    exact inv_mul_cancel₀ hcard
  rw [h1, one_smul]
theorem finsum_contourAverage_eq_zero (ha : a' ≠ 0)
    (hr : ∀ b : InfiniteLattice.Link a', B b.opposite = -B b)
    (hc : ∀ (x : InfiniteLattice.LatticePoint a') (μ : Fin 4),
      B (InfiniteLattice.Link.forwardFrom x μ) = v μ)
    (y : InfiniteLattice.LatticePoint a) (y' : InfiniteLattice.LatticePoint a')
    (hy : (y' : AmbientSpace) = y) :
    ∑ᶠ x ∈ FullSpace.cubeVertices L a' y, FullSpace.contourAverage L B y x = 0 := by
  have hrefl : ∀ {x : InfiniteLattice.LatticePoint a'} {ν : Fin 4 → ℤ},
      FullSpace.IsCubeOffset L y x ν → FullSpace.IsCubeOffset L y (y' + y' - x) (-ν) := by
    intro x ν h
    refine ⟨?_, fun μ => by simpa using h.2 μ⟩
    have h1 := h.1
    rw [Finset.univ_sum_single] at h1 ⊢
    funext μ
    have h2 := congrFun h1 μ
    simp only [Pi.sub_apply] at h2
    simp only [AddSubgroup.coe_sub, AddSubgroup.coe_add, hy, Pi.sub_apply, Pi.add_apply,
      Pi.neg_apply, Int.cast_neg, neg_mul]
    linarith
  have hmaps : MapsTo (fun x : InfiniteLattice.LatticePoint a' => y' + y' - x)
      (FullSpace.cubeVertices L a' y) (FullSpace.cubeVertices L a' y) := by
    intro x hx
    obtain ⟨ν, h⟩ := mem_cubeVertices_iff.mp hx
    exact mem_cubeVertices_iff.mpr ⟨-ν, hrefl h⟩
  have hinv : ∀ x : InfiniteLattice.LatticePoint a', y' + y' - (y' + y' - x) = x :=
    fun x => by abel
  have hb : BijOn (fun x : InfiniteLattice.LatticePoint a' => y' + y' - x)
      (FullSpace.cubeVertices L a' y) (FullSpace.cubeVertices L a' y) :=
    ⟨hmaps, fun p _ q _ hpq => by
        have := congrArg (fun x => y' + y' - x) hpq
        simpa [hinv] using this,
      fun z hz => ⟨y' + y' - z, hmaps hz, hinv z⟩⟩
  have hsum : ∑ᶠ x ∈ FullSpace.cubeVertices L a' y, -FullSpace.contourAverage L B y x =
      ∑ᶠ x ∈ FullSpace.cubeVertices L a' y, FullSpace.contourAverage L B y x := by
    refine finsum_mem_eq_of_bijOn _ hb fun x hx => ?_
    obtain ⟨ν, h⟩ := mem_cubeVertices_iff.mp hx
    rw [contourAverage_eq_sum ha hr hc h, contourAverage_eq_sum ha hr hc (hrefl h)]
    simp [Finset.sum_neg_distrib]
  simp only [finsum_neg_distrib] at hsum
  have h2 : (2 : ℂ) • ∑ᶠ x ∈ FullSpace.cubeVertices L a' y, FullSpace.contourAverage L B y x = 0 := by
    rw [two_smul]
    nth_rw 1 [← hsum]
    simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
theorem coe_toFiner {s : InfiniteLattice.LatticePoint a}
    (hs : (s : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a') :
    ((FullSpace.toFiner a' s : InfiniteLattice.LatticePoint a') : AmbientSpace) = s := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.coe_toFiner <;> assumption
theorem mem_latticeSubgroup_of_coarser (haL : a = (L : ℝ) * a') {s : AmbientSpace}
    (hs : s ∈ InfiniteLattice.latticeSubgroup a) : s ∈ InfiniteLattice.latticeSubgroup a' := by
  obtain ⟨n, hn⟩ := hs
  refine ⟨fun μ => n μ * L, fun μ => ?_⟩
  rw [hn, haL]
  push_cast
  ring
theorem isCubeOffset_shifted (haL : a = (L : ℝ) * a') (c : InfiniteLattice.Link a)
    {x : InfiniteLattice.LatticePoint a'} {ν : Fin 4 → ℤ}
    (h : FullSpace.IsCubeOffset L c.initial x ν) :
    FullSpace.IsCubeOffset L c.terminal (FullSpace.shifted c x) ν := by
  refine ⟨?_, h.2⟩
  rw [← h.1, FullSpace.shifted, AddSubgroup.coe_add,
    coe_toFiner (mem_latticeSubgroup_of_coarser haL (c.terminal - c.initial).2)]
  simp only [AddSubgroup.coe_sub]
  abel
theorem pathSum_crossingPath (ha : a' ≠ 0) (haL : a = (L : ℝ) * a') (hL : L ≠ 0)
    (hr : ∀ b : InfiniteLattice.Link a', B b.opposite = -B b)
    (hc : ∀ (x : InfiniteLattice.LatticePoint a') (μ : Fin 4),
      B (InfiniteLattice.Link.forwardFrom x μ) = v μ)
    (c : InfiniteLattice.Link a) {μ : Fin 4} {ε : ℤ} (hε : ε ≠ 0)
    (hd : c.terminal - c.initial = ε • InfiniteLattice.axisStep a μ)
    (x : InfiniteLattice.LatticePoint a') :
    FullSpace.edgeFormPathSum B (FullSpace.crossingPath c x) = (ε * (L : ℤ)) • v μ := by
  refine sumAlong_axisPath ha hr hc (mul_ne_zero hε (by exact_mod_cast hL)) ?_
  apply Subtype.ext
  rw [FullSpace.shifted, add_sub_cancel_left,
    coe_toFiner (mem_latticeSubgroup_of_coarser haL (c.terminal - c.initial).2),
    hd, coe_zsmul_axisStep, coe_zsmul_axisStep, haL]
  push_cast
  congr 1
  ring
theorem weight_smul_finsum_const (hL : L ≠ 0)
    (hcard : ∀ y : InfiniteLattice.LatticePoint a, (FullSpace.cube L a' y).ncard = L ^ 4)
    (hsub : ∀ y : InfiniteLattice.LatticePoint a,
      FullSpace.cube L a' y ⊆ (InfiniteLattice.latticeSubgroup a' : Set AmbientSpace))
    (y : InfiniteLattice.LatticePoint a) (w : Matrices.ComplexMatrix2) :
    PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ _x ∈ FullSpace.cubeVertices L a' y, w = w := by
  have himg : (fun x : InfiniteLattice.LatticePoint a' => (x : AmbientSpace)) ''
      FullSpace.cubeVertices L a' y = FullSpace.cube L a' y := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      exact ⟨⟨p, hsub y hp⟩, hp, rfl⟩
  have hinj : Function.Injective fun x : InfiniteLattice.LatticePoint a' => (x : AmbientSpace) :=
    Subtype.val_injective
  have hn : (FullSpace.cubeVertices L a' y).ncard = L ^ 4 := by
    rw [← hcard y, ← himg, Set.ncard_image_of_injective _ hinj]
  have hfin : (FullSpace.cubeVertices L a' y).Finite := by
    apply Set.finite_of_ncard_ne_zero
    rw [hn]
    exact pow_ne_zero 4 hL
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const,
    ← Set.ncard_eq_toFinset_card _ hfin, hn, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hw : PeriodicLattice.inverseFourthPowerWeight L * ((L ^ 4 : ℕ) : ℂ) = 1 := by
    have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
    unfold PeriodicLattice.inverseFourthPowerWeight
    push_cast
    rw [zpow_neg]
    simp only [zpow_ofNat]
    exact inv_mul_cancel₀ (pow_ne_zero 4 hLc)
  rw [hw, one_smul]
end Cubes
theorem meshAt_succ {L : ℕ} (hL : L ≠ 0) (k j : ℕ) :
    Tower.meshAt L k (j + 1) = (L : ℝ) * Tower.meshAt L k j := by
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  unfold Tower.meshAt
  rw [show ((j + 1 : ℕ) : ℤ) - (k : ℤ) = 1 + ((j : ℤ) - (k : ℤ)) by push_cast; ring,
    zpow_add₀ hLr, zpow_one]
theorem constantFormsStatement_holds (hZ : Tower.BlockStructure) :
    FullSpace.LinearizationFacts.constantFormsStatement := by
  intro L hL k j hj B hB v hv
  have hL0 : L ≠ 0 := by
    have := hL.2
    omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL0
  have ha : Tower.meshAt L k j ≠ 0 := (zpow_pos hLr _).ne'
  have haL := meshAt_succ hL0 k j
  have hr : ∀ b : InfiniteLattice.Link (Tower.meshAt L k j), B b.opposite = -B b := hB.2
  obtain ⟨-, hblocks, -, -, -⟩ := hZ L k (j + 1) hL (by omega) (by omega) (by omega)
  have hcard : ∀ y : FullSpace.Vertex L k (j + 1),
      (FullSpace.cube L (Tower.meshAt L k j) y).ncard = L ^ 4 :=
    fun y => (hblocks y).2.2.1
  have hsub : ∀ y : FullSpace.Vertex L k (j + 1), FullSpace.cube L (Tower.meshAt L k j) y ⊆
      (InfiniteLattice.latticeSubgroup (Tower.meshAt L k j) : Set AmbientSpace) :=
    fun y => (hblocks y).2.2.2
  have hn : FullSpace.cubeContourAverage (a := Tower.meshAt L k (j + 1)) L B = 0 := by
    funext y
    have hy : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup (Tower.meshAt L k j) :=
      mem_latticeSubgroup_of_coarser haL y.2
    have h0 := finsum_contourAverage_eq_zero (L := L) ha hr hv y ⟨y, hy⟩ rfl
    simp only [FullSpace.cubeContourAverage, h0, smul_zero, Pi.zero_apply]
  have hval : ∀ (c : FullSpace.Edge L k (j + 1)) (μ : Fin 4) (ε : ℤ), ε ≠ 0 →
      c.terminal - c.initial = ε • InfiniteLattice.axisStep (Tower.meshAt L k (j + 1)) μ →
      FullSpace.crossingSmoothing (a := Tower.meshAt L k (j + 1)) L B c =
        (ε * (L : ℤ)) • v μ := by
    intro c μ ε hε hd
    unfold FullSpace.crossingSmoothing
    rw [finsum_mem_congr rfl fun x _ => pathSum_crossingPath ha haL hL0 hr hv c hε hd x]
    exact weight_smul_finsum_const hL0 hcard hsub c.initial _
  have hfwd : ∀ (x : FullSpace.Vertex L k (j + 1)) (μ : Fin 4),
      FullSpace.crossingSmoothing (a := Tower.meshAt L k (j + 1)) L B
          (InfiniteLattice.Link.forwardFrom x μ) = (L : ℂ) • v μ := by
    intro x μ
    rw [hval (InfiniteLattice.Link.forwardFrom x μ) μ 1 one_ne_zero
        (by simp [InfiniteLattice.Link.forwardFrom]), one_mul, natCast_zsmul,
      Nat.cast_smul_eq_nsmul]
  have hdir : ∀ c : FullSpace.Edge L k (j + 1), ∃ (μ : Fin 4) (ε : ℤ), ε ≠ 0 ∧
      (ε = 1 ∨ ε = -1) ∧
        c.terminal - c.initial = ε • InfiniteLattice.axisStep (Tower.meshAt L k (j + 1)) μ := by
    intro c
    obtain ⟨μ, h | h⟩ := c.isAdjacent
    · exact ⟨μ, 1, one_ne_zero, Or.inl rfl, by simpa using h⟩
    · exact ⟨μ, -1, by norm_num, Or.inr rfl, by simpa using h⟩
  refine ⟨?_, hn, ?_, ⟨?_, ?_⟩, hfwd⟩
  · intro y x ν _ hd
    exact contourAverage_eq_sum ha hr hv hd
  · funext c
    unfold FullSpace.linearSmoothing FullSpace.crossingSmoothing
    congr 1
    refine finsum_mem_congr rfl fun x hx => ?_
    obtain ⟨ν, h⟩ := mem_cubeVertices_iff.mp hx
    rw [contourAverage_eq_sum ha hr hv h,
      contourAverage_eq_sum ha hr hv (isCubeOffset_shifted haL c h)]
    simp [FullSpace.edgeFormPathSum]
  · rintro b ⟨μ, hb⟩
    have h1 := hval b μ 1 one_ne_zero (by simpa using hb)
    rw [h1, one_mul, natCast_zsmul]
    have hmem : v μ ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
      rw [← hv 0 μ]
      exact hB.1 _ ⟨μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    exact (Matrices.ComplexMatrix2.hermitianTraceless).smul_mem _ hmem
  · intro b
    obtain ⟨μ, ε, hε, -, hd⟩ := hdir b
    have hd' : b.opposite.terminal - b.opposite.initial =
        (-ε) • InfiniteLattice.axisStep (Tower.meshAt L k (j + 1)) μ := by
      rw [neg_smul, ← hd]
      simp [InfiniteLattice.Link.opposite]
    rw [hval b μ ε hε hd, hval b.opposite μ (-ε) (neg_ne_zero.mpr hε) hd', neg_mul, neg_smul]
end Tower.FullSpace.ConstantForms
end YangMills.Construction
end
