import YangMills.Construction.RunningCouplingSlope.DeterminantSandwichAndNeighborhood
import YangMills.Construction.RunningCouplingSlope.TheFourFamiliesAreLocal
import YangMills.Construction.RunningCouplingSlope.TheKernelOfTheDifferenceIsSmallOnASideForm
import YangMills.Construction.RunningCouplingSlope.TheKernelOfTheHessianOfTheWholeChainDecaysProof
import YangMills.Construction.RunningCouplingSlope.TwoFunctionalsDifferByDeterminants
import YangMills.Construction.Towers.TheCrossingAverageReadAtTheSideInfinityProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.DifferenceKernelDecay
open YangMills.Construction.Tower
open YangMills.Construction.Tower.CriticalBranchResponse
def mixedPartial (f : ℝ → ℝ → ℝ) : ℝ := deriv (fun s => deriv (fun t => f s t) 0) 0
section
theorem mixedPartial_add {f g : ℝ × ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0) :
    mixedPartial (fun s t => f (s, t) + g (s, t)) = mixedPartial (fun s t => f (s, t)) +
      mixedPartial (fun s t => g (s, t)) := by apply _root_.YangMills.DeltaSharedProofs.p502252 <;> assumption
theorem mixedPartial_const_mul (c : ℝ) {f : ℝ × ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    mixedPartial (fun s t => c * f (s, t)) = c * mixedPartial (fun s t => f (s, t)) := by apply _root_.YangMills.DeltaSharedProofs.p500943 <;> assumption
theorem mixedPartial_const (c : ℝ) : mixedPartial (fun _ _ => c) = 0 := by
  simp [mixedPartial]
theorem mixedPartial_congr {f g : ℝ → ℝ → ℝ}
    (h : ∀ᶠ w in 𝓝 ((0 : ℝ), (0 : ℝ)), f w.1 w.2 = g w.1 w.2) :
    mixedPartial f = mixedPartial g := by apply _root_.YangMills.DeltaSharedProofs.p501748 <;> assumption
end
section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem contDiffAt_log_norm_det {T : ℝ → ℝ → Matrix ι ι ℂ}
    (hT : ∀ p q, ContDiffAt ℝ 2 (fun w : ℝ × ℝ => T w.1 w.2 p q) 0)
    (h0 : IsUnit (Matrix.det (T 0 0))) :
    ContDiffAt ℝ 2 (fun w : ℝ × ℝ => Real.log ‖Matrix.det (T w.1 w.2)‖) 0 := by apply _root_.YangMills.SharedProofs.p41557 <;> assumption
end
section
theorem card_fiber_le_of_injOn {ι β Y : Type} [Fintype ι] [Fintype β] (c : ι → Y) (y : Y)
    [DecidablePred fun p => c p = y] (f : ι → β)
    (hf : ∀ p q, c p = y → c q = y → f p = f q → p = q) :
    (Finset.univ.filter fun p => c p = y).card ≤ Fintype.card β := by
  classical
  refine (Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_).trans
    (le_of_eq Finset.card_univ)
  intro p hp q hq h
  exact hf p q (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 h
variable {L n k : ℕ}
def edgeAxis (b : PositiveEdge L n k k) : Fin 4 := b.2.choose
theorem eq_of_source_eq_of_edgeAxis_eq (p q : PositiveEdge L n k k) (ht : p.1.source = q.1.source)
    (hd : edgeAxis p = edgeAxis q) : p = q := by
  apply Subtype.ext
  have h1 := p.2.choose_spec
  have h2 := q.2.choose_spec
  have h3 : p.1.target = q.1.target := by
    have e1 : p.1.target = p.1.source + PeriodicLattice.unitStep L n _ (edgeAxis p) := by
      rw [← sub_eq_iff_eq_add']; exact h1
    have e2 : q.1.target = q.1.source + PeriodicLattice.unitStep L n _ (edgeAxis q) := by
      rw [← sub_eq_iff_eq_add']; exact h2
    rw [e1, e2, ht, hd]
  exact PeriodicLattice.Bond.ext ht h3
end
section
theorem matExp_inv (Z : Matrices.ComplexMatrix2) :
    (Matrices.ComplexMatrix2.matExp Z)⁻¹ = Matrices.ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
variable {L n k : ℕ}
theorem one_mem_fieldSpace :
    (fun _ : Edge L n k 0 => (1 : Matrices.ComplexMatrix2)) ∈ fieldSpace L n k 0 := by apply _root_.YangMills.Construction.Tower.CrossingSmoothingAtInfinity.const_one_mem_fieldSpace <;> assumption
theorem twoSource_mem_edgeFormSpace (s t : ℝ) (z : Fin 4 → ℤ) :
    (((s : ℂ) • (meshScaledResponse L n k (pauliUnitForm L n k 0) :
        Edge L n k 0 → Matrices.ComplexMatrix2)) +
      ((t : ℂ) • (meshScaledResponse L n k (pauliUnitForm L n k z) :
        Edge L n k 0 → Matrices.ComplexMatrix2))) ∈
      edgeFormSpace L n k 0 := by
  have h1 := (meshScaledResponse L n k (pauliUnitForm L n k 0)).2
  have h2 := (meshScaledResponse L n k (pauliUnitForm L n k z)).2
  have e : ∀ (r : ℝ) (B : Edge L n k 0 → Matrices.ComplexMatrix2), (r : ℂ) • B = r • B :=
    fun r B => by
      funext b
      simp
  rw [e, e]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)
end
set_option maxHeartbeats 1600000 in
theorem differenceKernelDecaysOnLargeTori_holds (hfour : FourFamiliesLocal)
    (hmix : MixedDerivLogDetDecays)
    (hdiff : FunctionalDifferenceIsTopDeterminants)
    (hval : Tower.SmoothingNearTrivialField)
    (hlat : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hel : Matrices.ComplexMatrix2.ExpLogEstimates) :
    DifferenceKernelDecaysOnLargeTori := by
  classical
  intro a ha L hL
  obtain ⟨M, θ, hM, hθ, H⟩ := hfour a ha L hL
  obtain ⟨C, θ', hC, hθ', Hm⟩ := hmix M θ 24 hM hθ
  refine ⟨θ', 3 * C, hθ', by positivity, fun k hk => ?_⟩
  obtain ⟨n₀, Hn⟩ := H k hk
  refine ⟨n₀, fun n hn₀ hn z => ?_⟩
  have fin0 := (hlat L hL n 0 k hn (Nat.zero_le k)).2.1
  have finK := (hlat L hL n k k hn le_rfl).2.1
  haveI : Finite (Vertex L n k 0) := fin0.2.2.2.2.2.2.2.2.2.2.1
  haveI : Finite (Vertex L n k k) := finK.2.2.2.2.2.2.2.2.2.2.1
  haveI : Finite (Edge L n k 0) := fin0.2.2.2.2.2.2.2.2.2.2.2.1
  haveI : Finite (Edge L n k k) := finK.2.2.2.2.2.2.2.2.2.2.2.1
  letI : Fintype (Fin 3 × PositiveEdge L n k 0) := Fintype.ofFinite _
  letI : Fintype (Fin 3 × PositiveEdge L n k k) := Fintype.ofFinite _
  letI : Fintype (Fin 3 × Vertex L n k 0) := Fintype.ofFinite _
  letI : Fintype (Fin 3 × Vertex L n k k) := Fintype.ofFinite _
  obtain ⟨hN, hCv, hRu, hR⟩ := Hn n hn₀ hn z
  obtain ⟨c, hc⟩ := hdiff a ha L hL k n hk hn
  have hbgD : ∀ s t : ℝ, twoSourceBackground L n k z s t ∈ fieldSpace L n k 0 := fun s t =>
    (hval L n k hL hn hk).2 0 (Nat.zero_le k) _ (twoSource_mem_edgeFormSpace s t z) _
      one_mem_fieldSpace
  have hinv1 : (1 : Matrices.ComplexMatrix2)⁻¹ = 1 := Matrix.inv_eq_right_inv (mul_one 1)
  have hbgcont : Tendsto (fun w : ℝ × ℝ => twoSourceBackground L n k z w.1 w.2)
      (𝓝 ((0 : ℝ), (0 : ℝ))) (𝓝 fun _ => (1 : Matrices.ComplexMatrix2)) := by
    refine tendsto_pi_nhds.mpr fun b => ?_
    set B₁ := (meshScaledResponse L n k (pauliUnitForm L n k 0) :
      Edge L n k 0 → Matrices.ComplexMatrix2) with hB₁
    set B₂ := (meshScaledResponse L n k (pauliUnitForm L n k z) :
      Edge L n k 0 → Matrices.ComplexMatrix2) with hB₂
    have hval : ∀ w : ℝ × ℝ, twoSourceBackground L n k z w.1 w.2 b =
        Matrices.ComplexMatrix2.matExp
          (Complex.I • ((w.1 : ℂ) • B₁ b + (w.2 : ℂ) • B₂ b)) := by
      intro w
      have hf := (twoSource_mem_edgeFormSpace (L := L) (n := n) (k := k) w.1 w.2 z).2
      have hf' : ∀ b', ((w.1 : ℂ) • B₁ + (w.2 : ℂ) • B₂) b'.opposite =
          -((w.1 : ℂ) • B₁ + (w.2 : ℂ) • B₂) b' := hf
      simp only [twoSourceBackground, PeriodicLattice.expTwist, mul_one]
      split_ifs with h
      · rfl
      · rw [matExp_inv, hf']
        congr 1
        simp
    have hZ : Tendsto (fun w : ℝ × ℝ => ‖Complex.I • ((w.1 : ℂ) • B₁ b + (w.2 : ℂ) • B₂ b)‖)
        (𝓝 ((0 : ℝ), (0 : ℝ))) (𝓝 0) := by
      have hc : Continuous fun w : ℝ × ℝ =>
          ‖Complex.I • ((w.1 : ℂ) • B₁ b + (w.2 : ℂ) • B₂ b)‖ := by fun_prop
      have := hc.tendsto ((0 : ℝ), (0 : ℝ))
      simpa using this
    have hE : Tendsto (fun w : ℝ × ℝ =>
        Real.exp ‖Complex.I • ((w.1 : ℂ) • B₁ b + (w.2 : ℂ) • B₂ b)‖ - 1)
        (𝓝 ((0 : ℝ), (0 : ℝ))) (𝓝 0) := by
      have := (Real.continuous_exp.tendsto 0).comp hZ
      simpa using this.sub_const 1
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun w => ?_) hE
    rw [hval w]
    exact (hel.1 _).2
  have hnonzero :=
    (DirectDeterminants.eventually_det_ne_zero
      (T := fun s t => noiseBlockMatrix a (twoSourceBackground L n k z s t))
      hN.contDiffAt hN.isUnit_det).and
      ((DirectDeterminants.eventually_det_ne_zero
        (T := fun s t => topCovariance (twoSourceBackground L n k z s t))
        hCv.contDiffAt hCv.isUnit_det).and
        ((DirectDeterminants.eventually_det_ne_zero
          (T := fun s t => Matrix.of (meanKernelR L n k (twoSourceBackground L n k z s t)) *
            yInv (twoSourceBackground L n k z s t) *
            Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).Rt)
          hRu.contDiffAt hRu.isUnit_det).and
          (DirectDeterminants.eventually_det_ne_zero
            (T := fun s t => Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).R *
              yInv (twoSourceBackground L n k z s t) *
              Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).Rt)
            hR.contDiffAt hR.isUnit_det)))
  have hev : ∀ᶠ w in 𝓝 ((0 : ℝ), (0 : ℝ)),
      chainMinusBackground a (twoSourceBackground L n k z w.1 w.2) =
        topLogDeterminants a (twoSourceBackground L n k z w.1 w.2) + c :=
    (((tendsto_nhdsWithin_iff.mpr
      ⟨hbgcont, Eventually.of_forall fun w => hbgD w.1 w.2⟩).eventually hc).and hnonzero).mono
        fun _ h => h.1 h.2
  set l₁ : ℝ × ℝ → ℝ := fun w =>
    Real.log ‖Matrix.det (noiseBlockMatrix a (twoSourceBackground L n k z w.1 w.2))‖
  set l₂ : ℝ × ℝ → ℝ := fun w =>
    Real.log ‖Matrix.det (topCovariance (twoSourceBackground L n k z w.1 w.2))‖
  set l₃ : ℝ × ℝ → ℝ := fun w => Real.log ‖Matrix.det
    (Matrix.of (meanKernelR L n k (twoSourceBackground L n k z w.1 w.2)) *
      yInv (twoSourceBackground L n k z w.1 w.2) *
      Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z w.1 w.2)).Rt)‖
  set l₄ : ℝ × ℝ → ℝ := fun w => Real.log ‖Matrix.det
    (Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z w.1 w.2)).R *
      yInv (twoSourceBackground L n k z w.1 w.2) *
      Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z w.1 w.2)).Rt)‖
  have c₁ : ContDiffAt ℝ 2 l₁ 0 := contDiffAt_log_norm_det
    (T := fun s t => noiseBlockMatrix a (twoSourceBackground L n k z s t))
    hN.contDiffAt hN.isUnit_det
  have c₂ : ContDiffAt ℝ 2 l₂ 0 := contDiffAt_log_norm_det
    (T := fun s t => topCovariance (twoSourceBackground L n k z s t))
    hCv.contDiffAt hCv.isUnit_det
  have c₃ : ContDiffAt ℝ 2 l₃ 0 := contDiffAt_log_norm_det
    (T := fun s t => Matrix.of (meanKernelR L n k (twoSourceBackground L n k z s t)) *
      yInv (twoSourceBackground L n k z s t) *
      Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).Rt)
    hRu.contDiffAt hRu.isUnit_det
  have c₄ : ContDiffAt ℝ 2 l₄ 0 := contDiffAt_log_norm_det
    (T := fun s t => Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).R *
      yInv (twoSourceBackground L n k z s t) *
      Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).Rt)
    hR.contDiffAt hR.isUnit_det
  have hk1 : differenceKernelFinite a L n k z =
      mixedPartial fun s t => chainMinusBackground a (twoSourceBackground L n k z s t) := rfl
  have hk2 : mixedPartial (fun s t => chainMinusBackground a (twoSourceBackground L n k z s t)) =
      mixedPartial fun s t => (-(1 / 2) * l₁ (s, t) + 1 / 2 * l₂ (s, t)) +
        (l₃ (s, t) + ((-1) * l₄ (s, t) + c)) := by
    refine mixedPartial_congr (hev.mono fun w hw => ?_)
    simp only [hw, topLogDeterminants, l₁, l₂, l₃, l₄]
    ring
  have d₁ : ContDiffAt ℝ 2 (fun w : ℝ × ℝ => -(1 / 2) * l₁ w) 0 := contDiffAt_const.mul c₁
  have d₂ : ContDiffAt ℝ 2 (fun w : ℝ × ℝ => 1 / 2 * l₂ w) 0 := contDiffAt_const.mul c₂
  have d₄ : ContDiffAt ℝ 2 (fun w : ℝ × ℝ => (-1) * l₄ w) 0 := contDiffAt_const.mul c₄
  have dc : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => c) 0 := contDiffAt_const
  have hk3 : mixedPartial (fun s t => (-(1 / 2) * l₁ (s, t) + 1 / 2 * l₂ (s, t)) +
        (l₃ (s, t) + ((-1) * l₄ (s, t) + c))) =
      -(1 / 2) * mixedPartial (fun s t => l₁ (s, t)) +
        1 / 2 * mixedPartial (fun s t => l₂ (s, t)) +
        (mixedPartial (fun s t => l₃ (s, t)) + (-1) * mixedPartial (fun s t => l₄ (s, t))) := by
    have e1 := mixedPartial_add (f := fun w => -(1 / 2) * l₁ w + 1 / 2 * l₂ w)
      (g := fun w => l₃ w + ((-1) * l₄ w + c)) (d₁.add d₂) (c₃.add (d₄.add dc))
    have e2 := mixedPartial_add (f := fun w => -(1 / 2) * l₁ w) (g := fun w => 1 / 2 * l₂ w) d₁ d₂
    have e3 := mixedPartial_add (f := l₃) (g := fun w => (-1) * l₄ w + c) c₃ (d₄.add dc)
    have e4 := mixedPartial_add (f := fun w => (-1) * l₄ w) (g := fun _ => c) d₄ dc
    beta_reduce at e1 e2 e3 e4
    rw [e1, e2, e3, e4, mixedPartial_const_mul _ c₁, mixedPartial_const_mul _ c₂,
      mixedPartial_const_mul _ c₄, mixedPartial_const]
    ring
  have hb12 : ∀ y : Vertex L n k k,
      (Finset.univ.filter fun p : Fin 3 × PositiveEdge L n k k => edgeCell p = y).card ≤ 24 := by
    intro y
    have h := card_fiber_le_of_injOn (β := Fin 3 × Fin 4) edgeCell y
      (fun p => (p.1, edgeAxis p.2)) (fun p q hp hq h => by
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact Prod.ext h1 (eq_of_source_eq_of_edgeAxis_eq _ _ (hp.trans hq.symm) h2))
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    omega
  have h2c : ∀ y : Vertex L n k k, (Finset.univ.filter fun p :
      Fin 3 × PositiveEdge L n k k ⊕ Fin 3 × PositiveEdge L n k k =>
        doubledEdgeCell p = y).card ≤ 24 := by
    intro y
    have h := card_fiber_le_of_injOn (β := Bool × Fin 3 × Fin 4) doubledEdgeCell y
      (fun p => Sum.elim (fun p => (true, p.1, edgeAxis p.2))
        (fun p => (false, p.1, edgeAxis p.2)) p) (fun p q hp hq h => by
        rcases p with p | p <;> rcases q with q | q
        · simp only [Sum.elim_inl, Prod.mk.injEq, true_and] at h
          congr 1
          exact Prod.ext h.1 (eq_of_source_eq_of_edgeAxis_eq _ _ (hp.trans hq.symm) h.2)
        · simp at h
        · simp at h
        · simp only [Sum.elim_inr, Prod.mk.injEq, true_and] at h
          congr 1
          exact Prod.ext h.1 (eq_of_source_eq_of_edgeAxis_eq _ _ (hp.trans hq.symm) h.2))
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h
    omega
  have hs3 : ∀ y : Vertex L n k k,
      (Finset.univ.filter fun p : Fin 3 × Vertex L n k k => vertexCell p = y).card ≤ 24 := by
    intro y
    have h := card_fiber_le_of_injOn (β := Fin 3) vertexCell y (fun p => p.1)
      (fun p q hp hq h => Prod.ext h (hp.trans hq.symm))
    simp only [Fintype.card_fin] at h
    omega
  have m₁ := Hm L n k _ doubledEdgeCell _ z hL hn h2c hN
  have m₂ := Hm L n k _ edgeCell _ z hL hn hb12 hCv
  have m₃ := Hm L n k _ vertexCell _ z hL hn hs3 hRu
  have m₄ := Hm L n k _ vertexCell _ z hL hn hs3 hR
  change |mixedPartial (fun s t => l₁ (s, t))| ≤ _ at m₁
  change |mixedPartial (fun s t => l₂ (s, t))| ≤ _ at m₂
  change |mixedPartial (fun s t => l₃ (s, t))| ≤ _ at m₃
  change |mixedPartial (fun s t => l₄ (s, t))| ≤ _ at m₄
  rw [hk1, hk2, hk3]
  set E := C * Real.exp (-(θ' * cellDist (cellOfCoords L n k 0) (cellOfCoords L n k z))) with hEdef
  have hfinal : 3 * C * Real.exp (-(θ' * cellDist (cellOfCoords L n k 0) (cellOfCoords L n k z))) =
      3 * E := by rw [hEdef]; ring
  rw [hfinal]
  rw [abs_le] at m₁ m₂ m₃ m₄ ⊢
  constructor <;> linarith [m₁.1, m₁.2, m₂.1, m₂.2, m₃.1, m₃.2, m₄.1, m₄.2]
end YangMills.Construction.RunningCouplingSlope.DifferenceKernelDecay
end
