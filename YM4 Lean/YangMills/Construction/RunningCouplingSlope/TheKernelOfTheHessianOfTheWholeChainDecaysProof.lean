import YangMills.Construction.RunningCouplingSlope.BoundedInversesOfLocalMatricesAreLocal
import YangMills.Construction.RunningCouplingSlope.ColourCoordinatesOfATower
import YangMills.Construction.RunningCouplingSlope.MixedDerivativeByCellsProof
import YangMills.Construction.RunningCouplingSlope.SaddleDeterminantInCoordinates
import YangMills.Construction.RunningCouplingSlope.TheGhostOfTheWholeChainHasABoundedInverseAtOne
import YangMills.Construction.RunningCouplingSlope.TheGhostOfTheWholeChainIsALocalFamily
import YangMills.Construction.RunningCouplingSlope.TheHessianOfTheSoftActionReadsNearCellsProof
import YangMills.Construction.RunningCouplingSlope.TheKernelOfTheHessianOfTheWholeChainDecays
import YangMills.Construction.RunningCouplingSlope.TheLengthsOfTheWholeChainAreALocalFamily
import YangMills.Construction.RunningCouplingSlope.TheSaddleOfTheWholeChainHasABoundedInverseAtOne
import YangMills.Construction.RunningCouplingSlope.TheSaddleOfTheWholeChainIsALocalFamily
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter YangMills.Construction.Tower
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.KernelDecayArgument
variable {L n k : ℕ}
private def mixedPartial (f : ℝ → ℝ → ℝ) : ℝ := deriv (fun s => deriv (fun t => f s t) 0) 0
section Calculus
private theorem partials_differentiable {f : ℝ × ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    (∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun t => f (s, t)) 0) ∧
      DifferentiableAt ℝ (fun s => deriv (fun t => f (s, t)) 0) 0 := by
  have hfd : ∀ᶠ w in 𝓝 (0 : ℝ × ℝ), DifferentiableAt ℝ f w :=
    (hf.eventually (by simp)).mono fun w hw => hw.differentiableAt (by norm_num)
  have hcurve : Tendsto (fun s : ℝ => ((s, 0) : ℝ × ℝ)) (𝓝 0) (𝓝 0) := by
    have : Continuous fun s : ℝ => ((s, 0) : ℝ × ℝ) := by fun_prop
    exact this.tendsto' 0 0 rfl
  have hline : ∀ s : ℝ, HasDerivAt (fun t : ℝ => ((s, t) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) 0 := by
    intro s
    exact (hasDerivAt_const _ s).prodMk (hasDerivAt_id _)
  have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (s, 0) := hcurve.eventually hfd
  constructor
  · refine h1.mono fun s hs => ?_
    exact (hs.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hline s)).differentiableAt
  · have hfd1 : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
    have hval : ∀ᶠ s in 𝓝 (0 : ℝ), deriv (fun t => f (s, t)) 0 = fderiv ℝ f (s, 0) (0, 1) := by
      refine h1.mono fun s hs => ?_
      exact (hs.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hline s)).deriv
    have h3 : DifferentiableAt ℝ (fun s : ℝ => fderiv ℝ f (s, 0) (0, 1)) 0 := by
      have hd : DifferentiableAt ℝ (fderiv ℝ f) ((0 : ℝ), (0 : ℝ)) :=
        hfd1.differentiableAt (by norm_num)
      have hc : DifferentiableAt ℝ (fun s : ℝ => ((s, 0) : ℝ × ℝ)) 0 := by fun_prop
      have h4 : DifferentiableAt ℝ (fun s : ℝ => fderiv ℝ f (s, 0)) 0 :=
        DifferentiableAt.comp (f := fun s : ℝ => ((s, 0) : ℝ × ℝ)) (g := fderiv ℝ f) (0 : ℝ) hd hc
      exact h4.clm_apply (differentiableAt_const _)
    exact h3.congr_of_eventuallyEq hval
abbrev _root_.YangMills.SharedProofs.p82379 := @partials_differentiable
private theorem mixedPartial_add {f g : ℝ × ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0) :
    mixedPartial (fun s t => f (s, t) + g (s, t)) = mixedPartial (fun s t => f (s, t)) +
      mixedPartial (fun s t => g (s, t)) := by
  obtain ⟨f1, f2⟩ := partials_differentiable hf
  obtain ⟨g1, g2⟩ := partials_differentiable hg
  have e : (fun s => deriv (fun t => f (s, t) + g (s, t)) 0) =ᶠ[𝓝 0]
      fun s => deriv (fun t => f (s, t)) 0 + deriv (fun t => g (s, t)) 0 := by
    filter_upwards [f1, g1] with s h1 h2
    exact deriv_fun_add h1 h2
  simp only [mixedPartial]
  rw [e.deriv_eq, deriv_fun_add f2 g2]
abbrev _root_.YangMills.DeltaSharedProofs.p502252 := @mixedPartial_add
private theorem mixedPartial_const_mul (c : ℝ) {f : ℝ × ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    mixedPartial (fun s t => c * f (s, t)) = c * mixedPartial (fun s t => f (s, t)) := by
  obtain ⟨f1, f2⟩ := partials_differentiable hf
  have e : (fun s => deriv (fun t => c * f (s, t)) 0) =ᶠ[𝓝 0]
      fun s => c * deriv (fun t => f (s, t)) 0 := by
    filter_upwards [f1] with s h1
    exact deriv_const_mul _ h1
  simp only [mixedPartial]
  rw [e.deriv_eq, deriv_const_mul _ f2]
abbrev _root_.YangMills.DeltaSharedProofs.p500943 := @mixedPartial_const_mul
private theorem mixedPartial_congr {f g : ℝ → ℝ → ℝ}
    (h : ∀ᶠ w in 𝓝 ((0 : ℝ), (0 : ℝ)), f w.1 w.2 = g w.1 w.2) : mixedPartial f = mixedPartial g := by
  have h1 := h.curry_nhds
  have e : (fun s => deriv (fun t => f s t) 0) =ᶠ[𝓝 0] fun s => deriv (fun t => g s t) 0 := by
    refine h1.mono fun s hs => ?_
    exact Filter.EventuallyEq.deriv_eq hs
  simp only [mixedPartial]
  exact e.deriv_eq
abbrev _root_.YangMills.DeltaSharedProofs.p501748 := @mixedPartial_congr
end Calculus
section LogDet
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem contDiffAt_det_entries {T : ℝ → ℝ → Matrix ι ι ℂ}
    (hT : ∀ p q, ContDiffAt ℝ 2 (fun w : ℝ × ℝ => T w.1 w.2 p q) 0) :
    ContDiffAt ℝ 2 (fun w : ℝ × ℝ => Matrix.det (T w.1 w.2)) 0 := by
  simp only [Matrix.det_apply]
  refine ContDiffAt.sum fun σ _ => ?_
  refine ContDiffAt.const_smul _ ?_
  exact contDiffAt_prod fun i _ => hT _ _
private theorem contDiffAt_log_norm_det {T : ℝ → ℝ → Matrix ι ι ℂ}
    (hT : ∀ p q, ContDiffAt ℝ 2 (fun w : ℝ × ℝ => T w.1 w.2 p q) 0)
    (h0 : IsUnit (Matrix.det (T 0 0))) :
    ContDiffAt ℝ 2 (fun w : ℝ × ℝ => Real.log ‖Matrix.det (T w.1 w.2)‖) 0 := by
  have hne : Matrix.det (T 0 0) ≠ 0 := h0.ne_zero
  have hn : ContDiffAt ℝ 2 (fun w : ℝ × ℝ => ‖Matrix.det (T w.1 w.2)‖) 0 :=
    (contDiffAt_det_entries hT).norm ℝ hne
  exact hn.log (by simpa using hne)
abbrev _root_.YangMills.SharedProofs.p41557 := @contDiffAt_log_norm_det
end LogDet
section Cells
private theorem cellDist_nonneg (u v : Vertex L n k k) : 0 ≤ cellDist u v := by apply _root_.YangMills.SharedProofs.p2231 <;> assumption
private theorem cellDist_add_add (u v y : Vertex L n k k) :
    cellDist (u + y) (v + y) = cellDist u v := by
  unfold cellDist
  congr 1
  push_cast
  abel
private theorem cellDist_add_left (u y y' : Vertex L n k k) :
    cellDist (u + y) y' = cellDist u (y' - y) := by
  unfold cellDist
  congr 1
  push_cast
  abel
private theorem cellOfCoords_zero : cellOfCoords L n k 0 = 0 := by
  simp [cellOfCoords, PeriodicLattice.offsetSite]
variable {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
private def recentred {ι : Type} (y : Vertex L n k k) (c : ι → Vertex L n k k) : ι → Vertex L n k k :=
  fun p => c p - y
private theorem blockBetween_recentred (y : Vertex L n k k) (c : ι → Vertex L n k k)
    (c' : ι' → Vertex L n k k) (T : Matrix ι' ι ℂ) (u' u : Vertex L n k k) :
    blockBetween (recentred y c) (recentred y c') T u' u = blockBetween c c' T (u' + y) (u + y) := by
  funext p q
  simp only [blockBetween, recentred, sub_eq_iff_eq_add]
  congr
private theorem isLocalOnCells_recentred {y : Vertex L n k k} {c : ι → Vertex L n k k}
    {c' : ι' → Vertex L n k k} {T : Matrix ι' ι ℂ} {M θ : ℝ} {m m' : Vertex L n k k → ℝ}
    (h : IsLocalOnCells c c' T M θ m) (hm : ∀ u, m (u + y) = m' u) :
    IsLocalOnCells (recentred y c) (recentred y c') T M θ m' := by
  intro u' u
  rw [blockBetween_recentred]
  have := h (u' + y) (u + y)
  rwa [cellDist_add_add, hm] at this
private theorem isLocalOnCells_mono {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k}
    {T : Matrix ι' ι ℂ} {M M' θ θ' : ℝ} {m m' : Vertex L n k k → ℝ}
    (h : IsLocalOnCells c c' T M θ m) (hM : 0 ≤ M) (hMM : M ≤ M') (hθ : θ' ≤ θ)
    (hm0 : ∀ u, 0 ≤ m u) (hm : ∀ u, m u ≤ m' u) : IsLocalOnCells c c' T M' θ' m' := by
  intro u' u
  refine (h u' u).trans ?_
  have hd := cellDist_nonneg u' u
  have he : Real.exp (-(θ * cellDist u' u)) ≤ Real.exp (-(θ' * cellDist u' u)) := by
    apply Real.exp_le_exp.2
    nlinarith
  have h1 : M * Real.exp (-(θ * cellDist u' u)) ≤ M' * Real.exp (-(θ' * cellDist u' u)) :=
    mul_le_mul hMM he (Real.exp_pos _).le (hM.trans hMM)
  exact mul_le_mul h1 (hm u') (hm0 u') (mul_nonneg (hM.trans hMM) (Real.exp_pos _).le)
private theorem cellDecayWeight_anti {θ θ' : ℝ} (h : θ' ≤ θ) (y u : Vertex L n k k) :
    cellDecayWeight θ y u ≤ cellDecayWeight θ' y u := by
  have hd := cellDist_nonneg u y
  apply Real.exp_le_exp.2
  nlinarith
private theorem cellDecayWeight_nonneg (θ : ℝ) (y u : Vertex L n k k) : 0 ≤ cellDecayWeight θ y u :=
  (Real.exp_pos _).le
private theorem cellDecayWeight_shift_origin (θ : ℝ) (y u : Vertex L n k k) :
    cellDecayWeight θ y (u + y) = cellDecayWeight θ (cellOfCoords L n k 0) u := by
  unfold cellDecayWeight
  rw [cellDist_add_left, sub_self, cellOfCoords_zero]
private theorem cellDecayWeight_shift_offset {θ : ℝ} {y y' : Vertex L n k k} {z : Fin 4 → ℤ}
    (hz : cellOfCoords L n k z = y' - y) (u : Vertex L n k k) :
    cellDecayWeight θ y' (u + y) = cellDecayWeight θ (cellOfCoords L n k z) u := by
  unfold cellDecayWeight
  rw [cellDist_add_left, hz]
private theorem isLocalFamily_of_alongCellPair {c : ι → Vertex L n k k} {T : ℝ → ℝ → Matrix ι ι ℂ}
    {y y' : Vertex L n k k} {z : Fin 4 → ℤ} {M₀ θ₀ M θ : ℝ}
    (h : IsLocalAlongCellPair c T y y' M₀ θ₀) (hz : cellOfCoords L n k z = y' - y)
    (hM₀ : 0 ≤ M₀) (hMM : M₀ ≤ M) (hθθ : θ ≤ θ₀)
    (hu : IsUnit (Matrix.det (T 0 0)))
    (hi : IsLocalOnCells (recentred y c) (recentred y c) (T 0 0)⁻¹ M θ fun _ => 1) :
    IsLocalFamily (recentred y c) T z M θ := by
  refine ⟨h.contDiffAt_entry, hu, hi, ?_, ?_, ?_⟩
  · exact isLocalOnCells_mono (isLocalOnCells_recentred h.derivFirst_local
      (cellDecayWeight_shift_origin θ₀ y)) hM₀ hMM hθθ
      (cellDecayWeight_nonneg _ _) (cellDecayWeight_anti hθθ _)
  · exact isLocalOnCells_mono (isLocalOnCells_recentred h.derivSecond_local
      (cellDecayWeight_shift_offset hz)) hM₀ hMM hθθ
      (cellDecayWeight_nonneg _ _) (cellDecayWeight_anti hθθ _)
  · refine isLocalOnCells_mono (isLocalOnCells_recentred h.derivMixed_local (m' := fun u =>
      cellDecayWeight θ₀ (cellOfCoords L n k 0) u * cellDecayWeight θ₀ (cellOfCoords L n k z) u)
      fun u => ?_) hM₀ hMM hθθ
      (fun u => mul_nonneg (cellDecayWeight_nonneg _ _ _) (cellDecayWeight_nonneg _ _ _)) fun u => ?_
    · simp only [cellDecayWeight_shift_origin, cellDecayWeight_shift_offset hz]
    · exact mul_le_mul (cellDecayWeight_anti hθθ _ _) (cellDecayWeight_anti hθθ _ _)
        (cellDecayWeight_nonneg _ _ _) (cellDecayWeight_nonneg _ _ _)
end Cells
section Count
private def edgeAxis {j : ℕ} (b : PositiveEdge L n k j) : Fin 4 := b.2.choose
private theorem eq_of_source_eq_of_axis_eq {j : ℕ} (p q : PositiveEdge L n k j)
    (ht : p.1.source = q.1.source) (hd : edgeAxis p = edgeAxis q) : p = q := by
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
private theorem edge_eq_of_torus {j : ℕ} (p q : PositiveEdge L n k j)
    (ht : (p.1.source : PeriodicLattice.FourTorus L n) = q.1.source) (hd : edgeAxis p = edgeAxis q) :
    p = q :=
  eq_of_source_eq_of_axis_eq p q (Subtype.ext ht) hd
private theorem card_fibre_le {ι κ Y P : Type} [Fintype ι] [Fintype κ] (c : ι → Y) (y : Y)
    [DecidablePred fun p => c p = y] (pt : ι → P) (lab : ι → κ) (B : Set P) (hB : B.Finite)
    (hmem : ∀ p, c p = y → pt p ∈ B)
    (hinj : ∀ p q, c p = y → c q = y → lab p = lab q → pt p = pt q → p = q) :
    (Finset.univ.filter fun p => c p = y).card ≤ Fintype.card κ * B.ncard := by apply _root_.YangMills.SharedProofs.p5765 <;> assumption
private abbrev IndexTag (k : ℕ) : Type := Fin (k + 2) × Fin 3 × Fin 4
private def formIndexPoint : LevelFormIndex L n k → PeriodicLattice.FourTorus L n
  | .inl p => p.2.1.source
  | .inr p => p.2.2.1.source
private def formIndexTag : LevelFormIndex L n k → IndexTag k
  | .inl p => (0, p.1, edgeAxis p.2)
  | .inr p => (⟨p.1 + 1, by have := p.1.2; omega⟩, p.2.1, edgeAxis p.2.2)
private theorem formIndexTag_inj (p q : LevelFormIndex L n k) (hl : formIndexTag p = formIndexTag q)
    (hp : formIndexPoint p = formIndexPoint q) : p = q := by
  rcases p with ⟨c, b⟩ | ⟨i, c, b⟩ <;> rcases q with ⟨c', b'⟩ | ⟨i', c', b'⟩
  · simp only [formIndexTag, Prod.mk.injEq, true_and] at hl
    simp only [formIndexPoint] at hp
    obtain rfl := hl.1
    rw [edge_eq_of_torus b b' hp hl.2]
  · simp only [formIndexTag, Prod.mk.injEq] at hl
    have := congrArg Fin.val hl.1
    simp at this
  · simp only [formIndexTag, Prod.mk.injEq] at hl
    have := congrArg Fin.val hl.1
    simp at this
  · simp only [formIndexTag, Prod.mk.injEq] at hl
    have h1 := congrArg Fin.val hl.1
    simp only [Nat.add_right_cancel_iff] at h1
    obtain rfl : i = i' := Fin.ext h1
    simp only [formIndexPoint] at hp
    obtain rfl := hl.2.1
    rw [edge_eq_of_torus b b' hp hl.2.2]
private def saddleIndexPoint : SaddlePointIndex L n k → PeriodicLattice.FourTorus L n
  | .inl p => formIndexPoint p
  | .inr p => p.2.1.source
private def saddleIndexTag : SaddlePointIndex L n k → IndexTag k
  | .inl p => formIndexTag p
  | .inr p => (Fin.last _, p.1, edgeAxis p.2)
private theorem formIndexTag_fst_ne_last (p : LevelFormIndex L n k) :
    (formIndexTag p).1 ≠ Fin.last _ := by
  rcases p with ⟨c, b⟩ | ⟨i, c, b⟩
  · simp [formIndexTag, Fin.ext_iff]
  · have := i.2
    simp only [formIndexTag, ne_eq, Fin.ext_iff, Fin.val_last]
    omega
private theorem saddleIndexTag_inj (p q : SaddlePointIndex L n k)
    (hl : saddleIndexTag p = saddleIndexTag q)
    (hp : saddleIndexPoint p = saddleIndexPoint q) : p = q := by
  rcases p with p | ⟨c, b⟩ <;> rcases q with q | ⟨c', b'⟩
  · rw [formIndexTag_inj p q hl hp]
  · exact absurd (congrArg Prod.fst hl) (formIndexTag_fst_ne_last p)
  · exact absurd (congrArg Prod.fst hl).symm (formIndexTag_fst_ne_last q)
  · simp only [saddleIndexTag, Prod.mk.injEq, true_and] at hl
    simp only [saddleIndexPoint] at hp
    obtain rfl := hl.1
    rw [edge_eq_of_torus b b' hp hl.2]
private def ghostIndexPoint : GhostCoordIndex L n k → PeriodicLattice.FourTorus L n
  | .inl p => p.2
  | .inr p => p.2
private def ghostIndexTag : GhostCoordIndex L n k → IndexTag k
  | .inl p => (0, p.1, 0)
  | .inr p => (Fin.last _, p.1, 0)
private theorem ghostIndexTag_inj (p q : GhostCoordIndex L n k)
    (hl : ghostIndexTag p = ghostIndexTag q)
    (hp : ghostIndexPoint p = ghostIndexPoint q) : p = q := by
  rcases p with ⟨c, x⟩ | ⟨c, x⟩ <;> rcases q with ⟨c', x'⟩ | ⟨c', x'⟩
  · simp only [ghostIndexTag, Prod.mk.injEq, and_true, true_and] at hl
    simp only [ghostIndexPoint] at hp
    rw [hl, Subtype.ext hp]
  · have := congrArg (fun l : IndexTag k => (l.1 : ℕ)) hl
    simp [ghostIndexTag] at this
  · have := congrArg (fun l : IndexTag k => (l.1 : ℕ)) hl
    simp [ghostIndexTag] at this
  · simp only [ghostIndexTag, Prod.mk.injEq, and_true, true_and] at hl
    simp only [ghostIndexPoint] at hp
    rw [hl, Subtype.ext hp]
private def noiseIndexPoint (p : NoiseIndex L n k) : PeriodicLattice.FourTorus L n := p.2.1.source
private def noiseIndexTag (p : NoiseIndex L n k) : IndexTag k :=
  (⟨p.1, by have := p.1.2; omega⟩, 0, edgeAxis p.2)
private theorem noiseIndexTag_inj (p q : NoiseIndex L n k) (hl : noiseIndexTag p = noiseIndexTag q)
    (hp : noiseIndexPoint p = noiseIndexPoint q) : p = q := by
  obtain ⟨i, b⟩ := p
  obtain ⟨i', b'⟩ := q
  simp only [noiseIndexTag, Prod.mk.injEq, true_and] at hl
  have h1 := congrArg Fin.val hl.1
  simp only at h1
  obtain rfl : i = i' := Fin.ext h1
  simp only [noiseIndexPoint] at hp
  rw [edge_eq_of_torus b b' hp hl.2]
private theorem refinedBlock_of_cell (hLat : PeriodicLattice.CoordinateDescription)
    (hCell : NeighbouringFineVertexCells) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (y : Vertex L n k k) :
    (PeriodicLattice.refinedBlock k y).Finite ∧
      (PeriodicLattice.refinedBlock k y).ncard = L ^ (4 * k) ∧
      ∀ {j : ℕ} (_ : j ≤ k) (x : Vertex L n k j), levelVertexCell x = y →
        (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k y := by apply _root_.YangMills.SharedProofs.p41695 <;> assumption
private def indicesPerCell (L k : ℕ) : ℕ := Fintype.card (IndexTag k) * L ^ (4 * k)
end Count
section Coordinates
private def levelFormsEquiv [Fintype (Fin 3 × PositiveEdge L n k 0)]
    [∀ i : Fin k, Fintype (Fin 3 × PositiveEdge L n k (i + 1))]
    (Ψ₀ : edgeFormSpace L n k 0 ≃ₗ[ℝ] (Fin 3 × PositiveEdge L n k 0 → ℝ))
    (Ψ : ∀ i : Fin k,
      edgeFormSpace L n k (i + 1) ≃ₗ[ℝ] (Fin 3 × PositiveEdge L n k (i + 1) → ℝ)) :
    LevelForms L n k ≃ₗ[ℝ] (LevelFormIndex L n k → ℝ) where
  toFun ξ := Sum.elim (Ψ₀ ξ.1) fun p => Ψ p.1 (ξ.2 p.1) p.2
  map_add' ξ ξ' := by
    funext p
    rcases p with p | ⟨i, p⟩ <;> simp
  map_smul' r ξ := by
    funext p
    rcases p with p | ⟨i, p⟩ <;> simp
  invFun f := (Ψ₀.symm fun ι => f (.inl ι), fun i => (Ψ i).symm fun ι => f (.inr ⟨i, ι⟩))
  left_inv ξ := by
    refine Prod.ext ?_ (funext fun i => ?_)
    · show Ψ₀.symm (fun ι => Ψ₀ ξ.1 ι) = ξ.1
      simp
    · show (Ψ i).symm (fun ι => Ψ i (ξ.2 i) ι) = ξ.2 i
      simp
  right_inv f := by
    funext p
    rcases p with p | ⟨i, p⟩ <;> simp
private def ghostPairEquiv [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
    (Ψ₀ : vertexFunctionSpace L n k 0 ≃ₗ[ℝ] (Fin 3 × Vertex L n k 0 → ℝ))
    (Ψk : vertexFunctionSpace L n k k ≃ₗ[ℝ] (Fin 3 × Vertex L n k k → ℝ)) :
    (vertexFunctionSpace L n k 0 × vertexFunctionSpace L n k k) ≃ₗ[ℝ]
      (GhostCoordIndex L n k → ℝ) where
  toFun g := Sum.elim (Ψ₀ g.1) (Ψk g.2)
  map_add' g g' := by
    funext p
    rcases p with p | p <;> simp
  map_smul' r g := by
    funext p
    rcases p with p | p <;> simp
  invFun f := (Ψ₀.symm fun ι => f (.inl ι), Ψk.symm fun ι => f (.inr ι))
  left_inv g := by
    refine Prod.ext ?_ ?_
    · show Ψ₀.symm (fun ι => Ψ₀ g.1 ι) = g.1
      simp
    · show Ψk.symm (fun ι => Ψk g.2 ι) = g.2
      simp
  right_inv f := by
    funext p
    rcases p with p | p <;> simp
private theorem nonempty_pauliCoordinates (hC : PauliCoordsOrthonormal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    [Fintype (Fin 3 × PositiveEdge L n k 0)]
    [∀ i : Fin k, Fintype (Fin 3 × PositiveEdge L n k (i + 1))]
    [Fintype (Fin 3 × PositiveEdge L n k k)] [Fintype (Fin 3 × Vertex L n k 0)]
    [Fintype (Fin 3 × Vertex L n k k)] : Nonempty (PauliCoordinates L n k) := by
  obtain ⟨Ψ₀, c₀, p₀⟩ := (hC L n k 0 hL hn (Nat.zero_le k)).1
  have hlev : ∀ i : Fin k, ∃ Ψ : edgeFormSpace L n k (i + 1) ≃ₗ[ℝ]
      (Fin 3 × PositiveEdge L n k (i + 1) → ℝ),
      (∀ (f : edgeFormSpace L n k (i + 1)) ι,
        toPauliCoeffs (restrictToPositiveEdges
          (f : Edge L n k (i + 1) → Matrices.ComplexMatrix2)) ι = ((Ψ f ι : ℝ) : ℂ)) ∧
      ∀ f g : edgeFormSpace L n k (i + 1),
        edgeFormPairing (f : Edge L n k (i + 1) → Matrices.ComplexMatrix2)
            (g : Edge L n k (i + 1) → Matrices.ComplexMatrix2) =
          ((∑ ι, Ψ f ι * Ψ g ι : ℝ) : ℂ) := fun i => (hC L n k (i + 1) hL hn i.2).1
  choose Ψ c p using hlev
  obtain ⟨Ψk, ck, pk⟩ := (hC L n k k hL hn le_rfl).1
  obtain ⟨Γ₀, d₀, q₀⟩ := (hC L n k 0 hL hn (Nat.zero_le k)).2
  obtain ⟨Γk, dk, qk⟩ := (hC L n k k hL hn le_rfl).2
  refine ⟨⟨levelFormsEquiv Ψ₀ Ψ, Ψk, ghostPairEquiv Γ₀ Γk, fun ξ ι => c₀ ξ.1 ι,
    fun ξ i ι => c i (ξ.2 i) ι, ck, fun g ι => d₀ g.1 ι, fun g ι => dk g.2 ι,
    fun ξ ξ' => ?_, fun μ μ' => ?_, fun g g' => ?_⟩⟩
  · unfold levelPairing formValues
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    simp only [p₀, p, Complex.ofReal_re]
    rfl
  · rw [pk, Complex.ofReal_re]
  · rw [Fintype.sum_sum_type, q₀, qk, Complex.ofReal_re, Complex.ofReal_re]
    rfl
abbrev _root_.YangMills.SharedProofs.p4012 := @nonempty_pauliCoordinates
private theorem levelFormsEuclidean_of (hF : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) : LevelFormsEuclidean L n k := by
  have h₀ := hF L n k 0 hL hn (Nat.zero_le k)
  have hi : ∀ i : Fin k, _ := fun i : Fin k => hF L n k (i + 1) hL hn i.2
  haveI := h₀.2.1
  haveI : ∀ i : Fin k, FiniteDimensional ℝ (edgeFormSpace L n k (i + 1)) := fun i => (hi i).2.1
  obtain ⟨c₀, hc₀⟩ := h₀.2.2.2
  choose c hc using fun i => (hi i).2.2.2
  refine ⟨inferInstance, ⟨⟨⟨fun ξ ξ' => c₀.inner ξ.1 ξ'.1 + ∑ i, (c i).inner (ξ.2 i) (ξ'.2 i)⟩,
    ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro ξ ξ'
    simp only [conj_trivial]
    rw [← c₀.conj_inner_symm ξ'.1 ξ.1]
    simp only [conj_trivial]
    refine congrArg₂ _ rfl (Finset.sum_congr rfl fun i _ => ?_)
    simpa using (c i).conj_inner_symm (ξ.2 i) (ξ'.2 i)
  · intro ξ
    simp only [RCLike.re_to_real]
    have h1 := c₀.re_inner_nonneg ξ.1
    simp only [RCLike.re_to_real] at h1
    refine add_nonneg h1 (Finset.sum_nonneg fun i _ => ?_)
    simpa using (c i).re_inner_nonneg (ξ.2 i)
  · intro ξ ξ' ζ
    have h1 := c₀.add_left ξ.1 ξ'.1 ζ.1
    show c₀.inner (ξ.1 + ξ'.1) ζ.1 + ∑ i, (c i).inner (ξ.2 i + ξ'.2 i) (ζ.2 i) =
      (c₀.inner ξ.1 ζ.1 + ∑ i, (c i).inner (ξ.2 i) (ζ.2 i)) +
        (c₀.inner ξ'.1 ζ.1 + ∑ i, (c i).inner (ξ'.2 i) (ζ.2 i))
    rw [h1, Finset.sum_congr rfl fun i _ => (c i).add_left (ξ.2 i) (ξ'.2 i) (ζ.2 i),
      Finset.sum_add_distrib]
    ring
  · intro ξ ξ' r
    have h1 := c₀.smul_left ξ.1 ξ'.1 r
    show c₀.inner (r • ξ.1) ξ'.1 + ∑ i, (c i).inner (r • ξ.2 i) (ξ'.2 i) =
      r * (c₀.inner ξ.1 ξ'.1 + ∑ i, (c i).inner (ξ.2 i) (ξ'.2 i))
    rw [h1, Finset.sum_congr rfl fun i _ => (c i).smul_left (ξ.2 i) (ξ'.2 i) r]
    simp only [conj_trivial, ← Finset.mul_sum]
    ring
  · intro ξ h
    have h1 : 0 ≤ c₀.inner ξ.1 ξ.1 := by simpa using c₀.re_inner_nonneg ξ.1
    have h2 : ∀ i, 0 ≤ (c i).inner (ξ.2 i) (ξ.2 i) := fun i => by
      simpa using (c i).re_inner_nonneg (ξ.2 i)
    have hs : 0 ≤ ∑ i, (c i).inner (ξ.2 i) (ξ.2 i) := Finset.sum_nonneg fun i _ => h2 i
    have h3 : c₀.inner ξ.1 ξ.1 + ∑ i, (c i).inner (ξ.2 i) (ξ.2 i) = 0 := h
    have h4 : c₀.inner ξ.1 ξ.1 = 0 := by linarith
    have h5 : ∑ i, (c i).inner (ξ.2 i) (ξ.2 i) = 0 := by linarith
    have h6 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => h2 i).mp h5
    exact Prod.ext (c₀.definite _ h4) (funext fun i => (c i).definite _ (h6 i (Finset.mem_univ i)))
  · intro ξ ξ'
    show c₀.inner ξ.1 ξ'.1 + ∑ i, (c i).inner (ξ.2 i) (ξ'.2 i) = _
    unfold levelPairing formValues
    simp only [hc₀, hc, Complex.ofReal_re]
abbrev _root_.YangMills.SharedProofs.p14283 := @levelFormsEuclidean_of
private theorem edgeFormsEuclidean_of (hF : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) : EdgeFormsEuclidean L n k k := by
  have h := hF L n k k hL hn le_rfl
  obtain ⟨c, hc⟩ := h.2.2.2
  exact ⟨h.2.1, c, fun B B' => by rw [hc, Complex.ofReal_re]⟩
section Determinants
variable {V V' I T : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']
  [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
private theorem coords_apply_eq_sum (Φ : V ≃ₗ[ℝ] (I → ℝ)) (Φ' : V' ≃ₗ[ℝ] (T → ℝ))
    (f : V →ₗ[ℝ] V') (x : V) (t : T) :
    ((Φ' (f x) t : ℝ) : ℂ) = ∑ j, complexMatrixOfLinearMap Φ Φ' f t j * ((Φ x j : ℝ) : ℂ) := by
  have h : Φ' (f x) =
      (LinearMap.toMatrix' (Φ'.toLinearMap ∘ₗ f ∘ₗ Φ.symm.toLinearMap)).mulVec (Φ x) := by
    rw [LinearMap.toMatrix'_mulVec]
    simp
  rw [h]
  simp only [Matrix.mulVec, dotProduct, complexMatrixOfLinearMap, Matrix.map_apply]
  push_cast
  rfl
private theorem abs_det_eq_norm_det (Φ : V ≃ₗ[ℝ] (I → ℝ)) (f : V →ₗ[ℝ] V) :
    |LinearMap.det f| = ‖Matrix.det (complexMatrixOfLinearMap Φ Φ f)‖ := by
  have h1 : Matrix.det (LinearMap.toMatrix' (Φ.toLinearMap ∘ₗ f ∘ₗ Φ.symm.toLinearMap)) =
      LinearMap.det f := by
    rw [LinearMap.det_toMatrix']
    exact LinearMap.det_conj f Φ
  have h2 : Matrix.det (complexMatrixOfLinearMap Φ Φ f) = ((LinearMap.det f : ℝ) : ℂ) := by
    have := Complex.ofRealHom.map_det
      (LinearMap.toMatrix' (Φ.toLinearMap ∘ₗ f ∘ₗ Φ.symm.toLinearMap))
    rw [h1] at this
    exact this.symm
  rw [h2, Complex.norm_real, Real.norm_eq_abs]
end Determinants
section OnTheChain
variable [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
  [Fintype (Fin 3 × PositiveEdge L n k k)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
  [Fintype (GhostCoordIndex L n k)] [DecidableEq (GhostCoordIndex L n k)]
  [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
private theorem abs_saddleDet_eq (hS : SaddleDetInOrthonormalCoords)
    (hA : LevelFormsEuclidean L n k) (hC : EdgeFormsEuclidean L n k k)
    (P : PauliCoordinates L n k) (X : LevelForms L n k →ₗ[ℝ] LevelForms L n k)
    (Q : LevelForms L n k →ₗ[ℝ] edgeFormSpace L n k k) :
    |levelSaddleDet X Q| = ‖Matrix.det (Matrix.fromBlocks
      (complexMatrixOfLinearMap P.formCoords P.formCoords X)
      (complexMatrixOfLinearMap P.formCoords P.topFormCoords Q).transpose
      (complexMatrixOfLinearMap P.formCoords P.topFormCoords Q) 0)‖ := by
  unfold levelSaddleDet
  rw [dif_pos ⟨hA, hC⟩]
  haveI := hA.1
  haveI := hC.1
  refine hS _ _ _ _ hA.2.choose hC.2.choose P.formCoords P.topFormCoords (fun x y => ?_)
    (fun x y => ?_) X Q _ _
    (coords_apply_eq_sum P.formCoords P.formCoords X)
    (coords_apply_eq_sum P.formCoords P.topFormCoords Q)
  · rw [hA.2.choose_spec x y, P.formCoords_pairing]
  · rw [hC.2.choose_spec x y, P.topFormCoords_pairing]
end OnTheChain
end Coordinates
section Function
private theorem logRadiusSum_eq [∀ i : Fin k, Fintype (PositiveEdge L n k (i + 1))]
    [DecidableEq (NoiseIndex L n k)] (τ : LevelTriple L n k)
    (h : ∀ p : NoiseIndex L n k,
      (meanRadius (levelField (expMove τ.1 (unitPoint L n k)) p.1) p.2.1).re ≠ 0) :
    logRadiusSum (expMove τ.1 (unitPoint L n k)) =
      Real.log ‖Matrix.det (noiseRadiusMatrix τ)‖ := by
  unfold logRadiusSum noiseRadiusMatrix
  rw [Matrix.det_diagonal, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [Real.log_prod (fun p _ => abs_ne_zero.2 (h p)), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun c _ => (Real.log_abs _).symm
private theorem eventually_meanRadius_re_ne [Fintype (NoiseIndex L n k)]
    [DecidableEq (NoiseIndex L n k)] {τ τ' : LevelTriple L n k}
    (hs : ∀ p q, ContDiffAt ℝ 2
      (fun w : ℝ × ℝ => noiseRadiusMatrix (w.1 • τ + w.2 • τ') p q) 0)
    (hu : IsUnit (Matrix.det (noiseRadiusMatrix (0 : LevelTriple L n k)))) :
    ∀ᶠ w in 𝓝 ((0 : ℝ), (0 : ℝ)), ∀ p : NoiseIndex L n k,
      (meanRadius (levelField (expMove (w.1 • τ + w.2 • τ').1 (unitPoint L n k)) p.1)
        p.2.1).re ≠ 0 := by
  have hd := contDiffAt_det_entries (T := fun s t => noiseRadiusMatrix (s • τ + t • τ')) hs
  have hz : Matrix.det (noiseRadiusMatrix ((((0 : ℝ), (0 : ℝ)) : ℝ × ℝ).1 • τ +
      (((0 : ℝ), (0 : ℝ)) : ℝ × ℝ).2 • τ')) ≠ 0 := by
    simpa using hu.ne_zero
  have hc : ContinuousAt (fun w : ℝ × ℝ => Matrix.det (noiseRadiusMatrix (w.1 • τ + w.2 • τ')))
      ((0 : ℝ), (0 : ℝ)) := hd.continuousAt
  filter_upwards [hc.eventually_ne hz] with w hw p
  unfold noiseRadiusMatrix at hw
  rw [Matrix.det_diagonal] at hw
  have := Finset.prod_ne_zero_iff.1 hw p (Finset.mem_univ p)
  exact_mod_cast this
variable [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
  [Fintype (Fin 3 × PositiveEdge L n k k)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
  [Fintype (GhostCoordIndex L n k)] [DecidableEq (GhostCoordIndex L n k)]
  [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
private theorem tripleFreeEnergy_eq [∀ i : Fin k, Fintype (PositiveEdge L n k (i + 1))]
    [DecidableEq (NoiseIndex L n k)] (hS : SaddleDetInOrthonormalCoords)
    (hA : LevelFormsEuclidean L n k) (hC : EdgeFormsEuclidean L n k k)
    (P : PauliCoordinates L n k) (a : ℝ) (τ : LevelTriple L n k)
    (h : ∀ p : NoiseIndex L n k,
      (meanRadius (levelField (expMove τ.1 (unitPoint L n k)) p.1) p.2.1).re ≠ 0) :
    tripleFreeEnergy a τ = -(1 / 2) * Real.log ‖Matrix.det (saddlePointMatrix P a τ)‖ +
      3 / 2 * Real.log ‖Matrix.det (noiseRadiusMatrix τ)‖ +
      Real.log ‖Matrix.det (ghostOperatorMatrix P τ)‖ := by
  unfold tripleFreeEnergy chainFreeEnergy
  rw [abs_saddleDet_eq hS hA hC P, abs_det_eq_norm_det P.ghostCoords, logRadiusSum_eq τ h]
  rfl
end Function
section Scaling
private theorem formSupported_smul {j : ℕ} {y : Vertex L n k k} (c : ℝ)
    {B : Edge L n k j → Matrices.ComplexMatrix2}
    (h : FormSupportedInCell y B) : FormSupportedInCell y (c • B) := fun b hb => by
  rw [Pi.smul_apply, h b hb, smul_zero]
private theorem levelFormsSupported_smul {y : Vertex L n k k} (c : ℝ) {ξ : LevelForms L n k}
    (h : LevelFormsSupportedInCell y ξ) : LevelFormsSupportedInCell y (c • ξ) :=
  ⟨formSupported_smul c h.1, fun i => formSupported_smul c (h.2 i)⟩
private theorem tripleSupported_smul {y : Vertex L n k k} (c : ℝ) {τ : LevelTriple L n k}
    (h : TripleSupportedInCell y τ) : TripleSupportedInCell y (c • τ) :=
  ⟨levelFormsSupported_smul c h.1, levelFormsSupported_smul c h.2.1, formSupported_smul c h.2.2⟩
private theorem hessianOfFreeEnergy_smul (a c d : ℝ) (τ τ' : LevelTriple L n k) :
    hessianOfFreeEnergy a (c • τ) (d • τ') = c * d * hessianOfFreeEnergy a τ τ' := by
  unfold hessianOfFreeEnergy
  have e : ∀ s u : ℝ, s • c • τ + u • d • τ' = (c * s) • τ + (d * u) • τ' := by
    intro s u
    rw [smul_smul, smul_smul, mul_comm s, mul_comm u]
  simp only [e]
  have h1 : ∀ s : ℝ, deriv (fun u : ℝ => tripleFreeEnergy a ((c * s) • τ + (d * u) • τ')) 0 =
      d * deriv (fun u : ℝ => tripleFreeEnergy a ((c * s) • τ + u • τ')) 0 := fun s => by
    have := deriv_comp_mul_left d (fun u : ℝ => tripleFreeEnergy a ((c * s) • τ + u • τ')) 0
    simpa using this
  simp only [h1]
  rw [deriv_const_mul_field]
  have := deriv_comp_mul_left c
    (fun s : ℝ => deriv (fun u : ℝ => tripleFreeEnergy a (s • τ + u • τ')) 0) 0
  simp only [mul_zero, smul_eq_mul] at this
  rw [this]
  ring
private theorem bound_of_unit_bound {E : Type} {sm : ℝ → E → E} {sq : E → ℝ} {H : E → E → ℝ}
    {Y₁ Y₂ : E → Prop} {K : ℝ} (h0 : ∀ τ, 0 ≤ sq τ)
    (hs : ∀ (c : ℝ) τ, sq (sm c τ) = c ^ 2 * sq τ)
    (hH : ∀ (c d : ℝ) τ τ', H (sm c τ) (sm d τ') = c * d * H τ τ')
    (hY₁ : ∀ (c : ℝ) τ, Y₁ τ → Y₁ (sm c τ)) (hY₂ : ∀ (c : ℝ) τ, Y₂ τ → Y₂ (sm c τ))
    (hunit : ∀ τ τ', Y₁ τ → Y₂ τ' → sq τ ≤ 1 → sq τ' ≤ 1 → |H τ τ'| ≤ K)
    {τ τ' : E} (h₁ : Y₁ τ) (h₂ : Y₂ τ') :
    |H τ τ'| ≤ K * Real.sqrt (sq τ) * Real.sqrt (sq τ') := by
  set A := Real.sqrt (sq τ) with hA
  set A' := Real.sqrt (sq τ') with hA'
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hA'0 : 0 ≤ A' := Real.sqrt_nonneg _
  have key : ∀ ε : ℝ, 0 < ε → |H τ τ'| ≤ K * (A + ε) * (A' + ε) := by
    intro ε hε
    have hr : 0 < A + ε := by positivity
    have hr' : 0 < A' + ε := by positivity
    have e1 : sq (sm (A + ε)⁻¹ τ) ≤ 1 := by
      rw [hs, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one, ← Real.sq_sqrt (h0 τ)]
      exact pow_le_pow_left₀ hA0 (by linarith) 2
    have e2 : sq (sm (A' + ε)⁻¹ τ') ≤ 1 := by
      rw [hs, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one, ← Real.sq_sqrt (h0 τ')]
      exact pow_le_pow_left₀ hA'0 (by linarith) 2
    have h3 := hunit _ _ (hY₁ (A + ε)⁻¹ τ h₁) (hY₂ (A' + ε)⁻¹ τ' h₂) e1 e2
    rw [hH, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hr), abs_of_pos (inv_pos.2 hr')] at h3
    have e3 : |H τ τ'| = (A + ε) * (A' + ε) * ((A + ε)⁻¹ * (A' + ε)⁻¹ * |H τ τ'|) := by
      field_simp
    rw [e3]
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ (A + ε) * (A' + ε))
    linarith
  have hc : Continuous fun ε : ℝ => K * (A + ε) * (A' + ε) := by fun_prop
  have ht : Tendsto (fun ε : ℝ => K * (A + ε) * (A' + ε)) (𝓝[>] 0) (𝓝 (K * A * A')) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  refine ge_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε using key ε hε
end Scaling
section Family
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem cellDist_origin_offset {y y' : Vertex L n k k} {z : Fin 4 → ℤ}
    (hz : cellOfCoords L n k z = y' - y) :
    cellDist (cellOfCoords L n k 0) (cellOfCoords L n k z) = cellDist y y' := by
  rw [cellOfCoords_zero, hz]
  unfold cellDist
  congr 1
  push_cast
  abel
private theorem mixed_logDet_bound {c : ι → Vertex L n k k} {T : ℝ → ℝ → Matrix ι ι ℂ}
    {y y' : Vertex L n k k} {z : Fin 4 → ℤ} {M₀ θ₀ M₁ θ₁ M θ C θ' : ℝ} {D : ℕ}
    (Hm : ∀ (c : ι → Vertex L n k k) (T : ℝ → ℝ → Matrix ι ι ℂ) (z : Fin 4 → ℤ),
      (∀ y, (Finset.univ.filter fun p => c p = y).card ≤ D) → IsLocalFamily c T z M θ →
        |deriv (fun s => deriv (fun t => Real.log ‖Matrix.det (T s t)‖) 0) 0| ≤
          C * Real.exp (-(θ' * cellDist (cellOfCoords L n k 0) (cellOfCoords L n k z))))
    (h : IsLocalAlongCellPair c T y y' M₀ θ₀) (hz : cellOfCoords L n k z = y' - y)
    (hM₀ : 0 ≤ M₀) (hMM : M₀ ≤ M) (hθθ : θ ≤ θ₀) (hM₁ : 0 ≤ M₁) (hM₁M : M₁ ≤ M) (hθ₁ : θ ≤ θ₁)
    (hu : IsUnit (Matrix.det (T 0 0)))
    (hinv : ∀ c' : ι → Vertex L n k k, IsLocalOnCells c' c' (T 0 0) M₀ θ₀ (fun _ => 1) →
      IsLocalOnCells c' c' (T 0 0)⁻¹ M₁ θ₁ fun _ => 1)
    (hc : ∀ u, (Finset.univ.filter fun p => c p = u).card ≤ D) :
    |deriv (fun s => deriv (fun t => Real.log ‖Matrix.det (T s t)‖) 0) 0| ≤
      C * Real.exp (-(θ' * cellDist y y')) := by
  have hv := isLocalOnCells_recentred (y := y) h.value_local (m' := fun _ => 1) fun _ => rfl
  have hi := isLocalOnCells_mono (hinv _ hv) hM₁ hM₁M hθ₁ (fun _ => zero_le_one) fun _ => le_rfl
  have fam := isLocalFamily_of_alongCellPair h hz hM₀ hMM hθθ hu hi
  have hcs : ∀ u, (Finset.univ.filter fun p => recentred y c p = u).card ≤ D := by
    intro u
    refine le_trans (le_of_eq ?_) (hc (u + y))
    congr 1
    ext p
    simp [recentred, sub_eq_iff_eq_add]
  have := Hm _ T z hcs fam
  rwa [cellDist_origin_offset hz] at this
end Family
section Combined
variable [∀ i : Fin k, Fintype (PositiveEdge L n k (i + 1))] [DecidableEq (NoiseIndex L n k)]
  [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
  [Fintype (Fin 3 × PositiveEdge L n k k)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
  [Fintype (GhostCoordIndex L n k)] [DecidableEq (GhostCoordIndex L n k)]
  [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
private theorem hessian_le_three_mul (hSad : SaddleDetInOrthonormalCoords)
    (hA : LevelFormsEuclidean L n k) (hF : EdgeFormsEuclidean L n k k)
    (P : PauliCoordinates L n k) {a E : ℝ} {τ τ' : LevelTriple L n k}
    (sS : ∀ p q, ContDiffAt ℝ 2
      (fun w : ℝ × ℝ => saddlePointMatrix P a (w.1 • τ + w.2 • τ') p q) 0)
    (sL : ∀ p q, ContDiffAt ℝ 2
      (fun w : ℝ × ℝ => noiseRadiusMatrix (w.1 • τ + w.2 • τ') p q) 0)
    (sG : ∀ p q, ContDiffAt ℝ 2
      (fun w : ℝ × ℝ => ghostOperatorMatrix P (w.1 • τ + w.2 • τ') p q) 0)
    (uS : IsUnit (Matrix.det (saddlePointMatrix P a ((0 : ℝ) • τ + (0 : ℝ) • τ'))))
    (uL : IsUnit (Matrix.det (noiseRadiusMatrix (0 : LevelTriple L n k))))
    (uG : IsUnit (Matrix.det (ghostOperatorMatrix P ((0 : ℝ) • τ + (0 : ℝ) • τ'))))
    (bS : |deriv (fun s : ℝ => deriv (fun t : ℝ =>
      Real.log ‖Matrix.det (saddlePointMatrix P a (s • τ + t • τ'))‖) 0) 0| ≤ E)
    (bL : |deriv (fun s : ℝ => deriv (fun t : ℝ =>
      Real.log ‖Matrix.det (noiseRadiusMatrix (s • τ + t • τ'))‖) 0) 0| ≤ E)
    (bG : |deriv (fun s : ℝ => deriv (fun t : ℝ =>
      Real.log ‖Matrix.det (ghostOperatorMatrix P (s • τ + t • τ'))‖) 0) 0| ≤ E) :
    |hessianOfFreeEnergy a τ τ'| ≤ 3 * E := by
  have z0 : (0 : ℝ) • τ + (0 : ℝ) • τ' = 0 := by simp
  have cA : ContDiffAt ℝ 2 (fun w : ℝ × ℝ =>
      Real.log ‖Matrix.det (saddlePointMatrix P a (w.1 • τ + w.2 • τ'))‖) 0 :=
    contDiffAt_log_norm_det (T := fun s t => saddlePointMatrix P a (s • τ + t • τ')) sS uS
  have cB : ContDiffAt ℝ 2 (fun w : ℝ × ℝ =>
      Real.log ‖Matrix.det (noiseRadiusMatrix (w.1 • τ + w.2 • τ'))‖) 0 :=
    contDiffAt_log_norm_det (T := fun s t => noiseRadiusMatrix (s • τ + t • τ')) sL
      (by simpa only [z0] using uL)
  have cC : ContDiffAt ℝ 2 (fun w : ℝ × ℝ =>
      Real.log ‖Matrix.det (ghostOperatorMatrix P (w.1 • τ + w.2 • τ'))‖) 0 :=
    contDiffAt_log_norm_det (T := fun s t => ghostOperatorMatrix P (s • τ + t • τ')) sG uG
  obtain ⟨A, hAe⟩ : ∃ A : ℝ × ℝ → ℝ, A = fun w : ℝ × ℝ =>
      Real.log ‖Matrix.det (saddlePointMatrix P a (w.1 • τ + w.2 • τ'))‖ := ⟨_, rfl⟩
  obtain ⟨Bn, hBe⟩ : ∃ B : ℝ × ℝ → ℝ, B = fun w : ℝ × ℝ =>
      Real.log ‖Matrix.det (noiseRadiusMatrix (w.1 • τ + w.2 • τ'))‖ := ⟨_, rfl⟩
  obtain ⟨G, hGe⟩ : ∃ G : ℝ × ℝ → ℝ, G = fun w : ℝ × ℝ =>
      Real.log ‖Matrix.det (ghostOperatorMatrix P (w.1 • τ + w.2 • τ'))‖ := ⟨_, rfl⟩
  rw [← hAe] at cA
  rw [← hBe] at cB
  rw [← hGe] at cC
  have bs' : |mixedPartial fun s t => A (s, t)| ≤ E := by
    rw [hAe]
    exact bS
  have bl' : |mixedPartial fun s t => Bn (s, t)| ≤ E := by
    rw [hBe]
    exact bL
  have bg' : |mixedPartial fun s t => G (s, t)| ≤ E := by
    rw [hGe]
    exact bG
  have hne := eventually_meanRadius_re_ne (τ := τ) (τ' := τ') sL uL
  have e1 : hessianOfFreeEnergy a τ τ' = mixedPartial fun s t =>
      (-(1 / 2) * A (s, t) + 3 / 2 * Bn (s, t)) + G (s, t) := by
    refine mixedPartial_congr (f := fun s t => tripleFreeEnergy a (s • τ + t • τ')) ?_
    filter_upwards [hne] with w hw
    rw [hAe, hBe, hGe]
    exact tripleFreeEnergy_eq hSad hA hF P a _ hw
  have c1 : ContDiffAt ℝ 2 (fun w : ℝ × ℝ => -(1 / 2) * A w) 0 := contDiffAt_const.mul cA
  have c2 : ContDiffAt ℝ 2 (fun w : ℝ × ℝ => 3 / 2 * Bn w) 0 := contDiffAt_const.mul cB
  have e2 := mixedPartial_add (c1.add c2) cC
  have e3 := mixedPartial_add c1 c2
  have e4 := mixedPartial_const_mul (-(1 / 2)) cA
  have e5 := mixedPartial_const_mul (3 / 2) cB
  rw [e1]
  refine (congrArg abs e2).le.trans ?_
  rw [e3, e4, e5]
  rw [abs_le] at bs' bl' bg' ⊢
  constructor <;> linarith [bs'.1, bs'.2, bl'.1, bl'.2, bg'.1, bg'.2]
end Combined
private def InverseLocality (M θ K M' θ' : ℝ) : Prop :=
  ∀ (L n k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (c : ι → Vertex L n k k)
    (T : Matrix ι ι ℂ), Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    IsLocalOnCells c c T M θ (fun _ => 1) → IsUnit (Matrix.det T) → ‖T⁻¹‖ ≤ K →
    IsLocalOnCells c c T⁻¹ M' θ' fun _ => 1
private def MixedDecay (M θ : ℝ) (D : ℕ) (C θ' : ℝ) : Prop :=
  ∀ (L n k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (c : ι → Vertex L n k k)
    (T : ℝ → ℝ → Matrix ι ι ℂ) (z : Fin 4 → ℤ), Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    (∀ y, (Finset.univ.filter fun p => c p = y).card ≤ D) →
    IsLocalFamily c T z M θ →
      |deriv (fun s => deriv (fun t => Real.log ‖Matrix.det (T s t)‖) 0) 0| ≤
        C * Real.exp (-(θ' * cellDist (cellOfCoords L n k 0) (cellOfCoords L n k z)))
private def CellBlocks (L n k : ℕ) : Prop :=
  ∀ y : Vertex L n k k, (PeriodicLattice.refinedBlock k y).Finite ∧
    (PeriodicLattice.refinedBlock k y).ncard = L ^ (4 * k) ∧
      ∀ {j : ℕ} (_ : j ≤ k) (x : Vertex L n k j), levelVertexCell x = y →
        (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k y
section Counts
private theorem card_saddle_fibre_le [Fintype (LevelFormIndex L n k)]
    [Fintype (Fin 3 × PositiveEdge L n k k)] (hb : CellBlocks L n k) (u : Vertex L n k k) :
    (Finset.univ.filter fun p : SaddlePointIndex L n k => saddlePointIndexCell p = u).card ≤
      indicesPerCell L k := by
  have h := card_fibre_le saddlePointIndexCell u saddleIndexPoint saddleIndexTag _ (hb u).1 ?_
    fun p q _ _ => saddleIndexTag_inj p q
  · rwa [(hb u).2.1] at h
  · rintro ((p | p) | p) hp
    · exact (hb u).2.2 (Nat.zero_le k) _ hp
    · exact (hb u).2.2 p.1.2 _ hp
    · exact (hb u).2.2 le_rfl _ hp
private theorem card_ghost_fibre_le [Fintype (GhostCoordIndex L n k)]
    (hb : CellBlocks L n k) (u : Vertex L n k k) :
    (Finset.univ.filter fun p : GhostCoordIndex L n k => ghostCoordIndexCell p = u).card ≤
      indicesPerCell L k := by
  have h := card_fibre_le ghostCoordIndexCell u ghostIndexPoint ghostIndexTag _ (hb u).1 ?_
    fun p q _ _ => ghostIndexTag_inj p q
  · rwa [(hb u).2.1] at h
  · rintro (p | p) hp
    · exact (hb u).2.2 (Nat.zero_le k) _ hp
    · exact (hb u).2.2 le_rfl _ hp
private theorem card_noise_fibre_le [Fintype (NoiseIndex L n k)]
    (hb : CellBlocks L n k) (u : Vertex L n k k) :
    (Finset.univ.filter fun p : NoiseIndex L n k => noiseIndexCell p = u).card ≤
      indicesPerCell L k := by
  have h := card_fibre_le noiseIndexCell u noiseIndexPoint noiseIndexTag _ (hb u).1 ?_
    fun p q _ _ => noiseIndexTag_inj p q
  · rwa [(hb u).2.1] at h
  · rintro p hp
    exact (hb u).2.2 p.1.2 _ hp
end Counts
section Side
variable [∀ i : Fin k, Fintype (PositiveEdge L n k (i + 1))] [DecidableEq (NoiseIndex L n k)]
  [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
  [Fintype (Fin 3 × PositiveEdge L n k k)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
  [Fintype (GhostCoordIndex L n k)] [DecidableEq (GhostCoordIndex L n k)]
  [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
private theorem unit_bound_at_side (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hSad : SaddleDetInOrthonormalCoords)
    (hA : LevelFormsEuclidean L n k) (hF : EdgeFormsEuclidean L n k k)
    (hb : CellBlocks L n k) (P : PauliCoordinates L n k) {a M θ C θ' : ℝ}
    {Ms θs Mg θg Ml θl Ks Kg Ms' θs' Mg' θg' Ml' θl' : ℝ}
    (hMix : MixedDecay M θ (indicesPerCell L k) C θ')
    (Bs : InverseLocality Ms θs Ks Ms' θs') (Bg : InverseLocality Mg θg Kg Mg' θg')
    (Bl : InverseLocality Ml θl Ml Ml' θl')
    (hMs : 0 ≤ Ms) (hMg : 0 ≤ Mg) (hMl : 0 ≤ Ml) (hMs' : 0 ≤ Ms') (hMg' : 0 ≤ Mg') (hMl' : 0 ≤ Ml')
    (hMa : Ms ≤ M) (hMb : Mg ≤ M) (hMc : Ml ≤ M) (hMd : Ms' ≤ M) (hMe : Mg' ≤ M) (hMf : Ml' ≤ M)
    (hta : θ ≤ θs) (htb : θ ≤ θg) (htc : θ ≤ θl) (htd : θ ≤ θs') (hte : θ ≤ θg') (htf : θ ≤ θl')
    (us : IsUnit (Matrix.det (saddlePointMatrix P a 0)) ∧ ‖(saddlePointMatrix P a 0)⁻¹‖ ≤ Ks)
    (ug : IsUnit (Matrix.det (ghostOperatorMatrix P 0)) ∧ ‖(ghostOperatorMatrix P 0)⁻¹‖ ≤ Kg)
    (ul : IsUnit (Matrix.det (noiseRadiusMatrix (0 : LevelTriple L n k))))
    (nl : ‖(noiseRadiusMatrix (0 : LevelTriple L n k))⁻¹‖ ≤ Ml)
    {y y' : Vertex L n k k} {z : Fin 4 → ℤ} {τ τ' : LevelTriple L n k}
    (hz : cellOfCoords L n k z = y' - y)
    (ls : IsLocalAlongCellPair saddlePointIndexCell
      (fun s t => saddlePointMatrix P a (s • τ + t • τ')) y y' Ms θs)
    (lg : IsLocalAlongCellPair ghostCoordIndexCell
      (fun s t => ghostOperatorMatrix P (s • τ + t • τ')) y y' Mg θg)
    (ll : IsLocalAlongCellPair noiseIndexCell
      (fun s t => noiseRadiusMatrix (s • τ + t • τ')) y y' Ml θl) :
    |hessianOfFreeEnergy a τ τ'| ≤ 3 * (C * Real.exp (-(θ' * cellDist y y'))) := by
  have z0 : (0 : ℝ) • τ + (0 : ℝ) • τ' = 0 := by simp
  have bs := mixed_logDet_bound (Hm := fun c T z hc hf => hMix L n k _ c T z hL hn hc hf) ls hz
    hMs hMa hta hMs' hMd htd (by simpa only [z0] using us.1)
    (fun c' hv => by
      simp only [z0] at hv ⊢
      exact Bs L n k _ c' _ hL hn hv us.1 us.2) (card_saddle_fibre_le hb)
  have bg := mixed_logDet_bound (Hm := fun c T z hc hf => hMix L n k _ c T z hL hn hc hf) lg hz
    hMg hMb htb hMg' hMe hte (by simpa only [z0] using ug.1)
    (fun c' hv => by
      simp only [z0] at hv ⊢
      exact Bg L n k _ c' _ hL hn hv ug.1 ug.2) (card_ghost_fibre_le hb)
  have bl := mixed_logDet_bound (Hm := fun c T z hc hf => hMix L n k _ c T z hL hn hc hf) ll hz
    hMl hMc htc hMl' hMf htf (by simpa only [z0] using ul)
    (fun c' hv => by
      simp only [z0] at hv ⊢
      exact Bl L n k _ c' _ hL hn hv ul nl) (card_noise_fibre_le hb)
  exact hessian_le_three_mul hSad hA hF P ls.contDiffAt_entry ll.contDiffAt_entry
    lg.contDiffAt_entry (by simpa only [z0] using us.1) ul (by simpa only [z0] using ug.1) bs bl bg
private theorem tripleNormSq_eq (P : PauliCoordinates L n k) (τ : LevelTriple L n k) :
    tripleNormSq τ =
      ∑ ι, (P.formCoords τ.1 ι) ^ 2 + ∑ ι, (P.formCoords τ.2.1 ι) ^ 2 +
        ∑ ι, (P.topFormCoords τ.2.2 ι) ^ 2 := by
  unfold tripleNormSq levelFormsNormSq topFormNormSq
  rw [P.formCoords_pairing, P.formCoords_pairing, P.topFormCoords_pairing]
  simp only [sq]
private theorem tripleNormSq_nonneg (P : PauliCoordinates L n k) (τ : LevelTriple L n k) :
    0 ≤ tripleNormSq τ := by
  rw [tripleNormSq_eq P]
  positivity
private theorem tripleNormSq_smul (P : PauliCoordinates L n k) (c : ℝ) (τ : LevelTriple L n k) :
    tripleNormSq (c • τ) = c ^ 2 * tripleNormSq τ := by
  rw [tripleNormSq_eq P, tripleNormSq_eq P]
  have e1 : (c • τ).1 = c • τ.1 := rfl
  have e2 : (c • τ).2.1 = c • τ.2.1 := rfl
  have e3 : (c • τ).2.2 = c • τ.2.2 := rfl
  rw [e1, e2, e3, map_smul, map_smul, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  ring
private theorem bound_at_side {a : ℝ} (P : PauliCoordinates L n k)
    {E : Vertex L n k k → Vertex L n k k → ℝ}
    (hunit : ∀ (y y' : Vertex L n k k) (τ τ' : LevelTriple L n k),
      TripleSupportedInCell y τ → TripleSupportedInCell y' τ' → tripleNormSq τ ≤ 1 →
        tripleNormSq τ' ≤ 1 → |hessianOfFreeEnergy a τ τ'| ≤ E y y')
    (y y' : Vertex L n k k) (τ τ' : LevelTriple L n k) (h1 : TripleSupportedInCell y τ)
    (h2 : TripleSupportedInCell y' τ') :
    |hessianOfFreeEnergy a τ τ'| ≤
      E y y' * Real.sqrt (tripleNormSq τ) * Real.sqrt (tripleNormSq τ') :=
  bound_of_unit_bound (sm := fun c τ => c • τ) (sq := tripleNormSq) (H := hessianOfFreeEnergy a)
    (Y₁ := TripleSupportedInCell y) (Y₂ := TripleSupportedInCell y')
    (K := E y y') (tripleNormSq_nonneg P) (tripleNormSq_smul P) (hessianOfFreeEnergy_smul a)
    (fun c _ h => tripleSupported_smul c h) (fun c _ h => tripleSupported_smul c h)
    (fun τ τ' a b c d => hunit y y' τ τ' a b c d) h1 h2
end Side
theorem hessianKernelDecays_holds (hSL : SaddlePointMatrixIsLocal)
    (hGL : GhostOperatorMatrixIsLocal)
    (hLL : NoiseRadiusMatrixIsLocal)
    (hSI : SaddlePointMatrixInverseBounded)
    (hGI : GhostOperatorMatrixInverseBounded)
    (hmix : MixedDerivLogDetDecays)
    (hB : LocalMatricesBoundedAndInverseLocal)
    (hSad : SaddleDetInOrthonormalCoords)
    (hCol : PauliCoordsOrthonormal)
    (hCell : NeighbouringFineVertexCells)
    (hSp : FiniteSideFormSpaces)
    (hConf : BondSetFields.ProductStructureHolds)
    (hLat : PeriodicLattice.CoordinateDescription) :
    HessianKernelDecays := by
  intro a ha L hL k hk
  obtain ⟨Ms, θs, hMs, hθs, Hs⟩ := hSL a ha L hL k hk
  obtain ⟨Mg, θg, hMg, hθg, Hg⟩ := hGL L hL k hk
  obtain ⟨Ml, θl, hMl, hθl, Hl⟩ := hLL L hL k hk
  obtain ⟨Ks, hKs, Is⟩ := hSI a ha L hL k hk
  obtain ⟨Kg, hKg, Ig⟩ := hGI L hL k hk
  obtain ⟨Ms', θs', hMs', hθs', Bs⟩ := hB.2 Ms θs Ks hMs hθs hKs
  obtain ⟨Mg', θg', hMg', hθg', Bg⟩ := hB.2 Mg θg Kg hMg hθg hKg
  obtain ⟨Ml', θl', hMl', hθl', Bl⟩ := hB.2 Ml θl Ml hMl hθl hMl
  obtain ⟨M, hM, hMa, hMb, hMc, hMd, hMe, hMf⟩ : ∃ M : ℝ, 0 < M ∧ Ms ≤ M ∧ Mg ≤ M ∧ Ml ≤ M ∧
      Ms' ≤ M ∧ Mg' ≤ M ∧ Ml' ≤ M :=
    ⟨Ms + Mg + Ml + Ms' + Mg' + Ml', by positivity, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith⟩
  obtain ⟨θ, hθ, hta, htb, htc, htd, hte, htf⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ θs ∧ θ ≤ θg ∧ θ ≤ θl ∧
      θ ≤ θs' ∧ θ ≤ θg' ∧ θ ≤ θl' := by
    refine ⟨min θs (min θg (min θl (min θs' (min θg' θl')))), by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp
  obtain ⟨C, θ', hC, hθ', Hm⟩ := hmix M θ (indicesPerCell L k) hM hθ
  refine ⟨3 * C, θ', by positivity, hθ', ?_⟩
  filter_upwards [Hs, Hg, Hl, Is, Ig, eventually_gt_atTop 0] with n Hs Hg Hl Is Ig hn
  have hbond : ∀ j ≤ k, Finite (Edge L n k j) := fun j hj =>
    Set.finite_univ_iff.1 ((hConf L hL k j hj).1 n hn).2.1
  have fb : ∀ j ≤ k, Finite (PositiveEdge L n k j) := fun j hj => by
    haveI := hbond j hj
    exact Subtype.finite
  have fs : ∀ j ≤ k, Finite (Vertex L n k j) := fun j hj => by
    haveI := hbond j hj
    exact Finite.of_injective (fun y : Vertex L n k j => PeriodicLattice.Bond.forwardFrom y 0)
      fun y y' e => congrArg PeriodicLattice.Bond.source e
  letI f0 : Fintype (PositiveEdge L n k 0) :=
    @Fintype.ofFinite _ (fb 0 (Nat.zero_le k))
  letI fi : ∀ i : Fin k, Fintype (PositiveEdge L n k (i + 1)) := fun i =>
    @Fintype.ofFinite _ (fb _ i.2)
  letI fk : Fintype (PositiveEdge L n k k) := @Fintype.ofFinite _ (fb k le_rfl)
  letI s0 : Fintype (Vertex L n k 0) := @Fintype.ofFinite _ (fs 0 (Nat.zero_le k))
  letI sk : Fintype (Vertex L n k k) := @Fintype.ofFinite _ (fs k le_rfl)
  letI dC : DecidableEq (LevelFormIndex L n k) := Classical.decEq _
  letI dT : DecidableEq (Fin 3 × PositiveEdge L n k k) := Classical.decEq _
  letI dG : DecidableEq (GhostCoordIndex L n k) := Classical.decEq _
  letI dL : DecidableEq (NoiseIndex L n k) := Classical.decEq _
  obtain ⟨P⟩ := nonempty_pauliCoordinates (k := k) hCol hL hn
  have hA : LevelFormsEuclidean L n k := levelFormsEuclidean_of hSp hL hn
  have hF : EdgeFormsEuclidean L n k k := edgeFormsEuclidean_of hSp hL hn
  have hb : CellBlocks L n k := fun y => refinedBlock_of_cell hLat hCell hL hn y
  obtain ⟨ul, nl, Hl⟩ := Hl
  have us := Is P
  have ug := Ig P
  have hj : -(n : ℤ) ≤ PeriodicLattice.levelDepth k k := by
    simp only [PeriodicLattice.levelDepth]
    omega
  have hcoord := ((hLat L n hL.1 hL.2 hn).1 _ hj).2.2.2.1
  intro y y' τ τ' h1 h2
  rw [mul_assoc 3 C]
  refine bound_at_side (E := fun y y' => 3 * (C * Real.exp (-(θ' * cellDist y y')))) P
    (fun y y' τ τ' h1 h2 h3 h4 => ?_) y y' τ τ' h1 h2
  obtain ⟨z, hz⟩ := hcoord 0 (y' - y)
  exact unit_bound_at_side hL hn hSad hA hF hb P (C := C) (θ' := θ') Hm Bs Bg Bl
    hMs.le hMg.le hMl.le hMs'.le hMg'.le hMl'.le hMa hMb hMc hMd hMe hMf
    hta htb htc htd hte htf us ug ul nl hz.symm
    (Hs P y y' τ τ' h1 h2 h3 h4) (Hg P y y' τ τ' h1 h2 h3 h4) (Hl y y' τ τ' h1 h2 h3 h4)
end YangMills.Construction.RunningCouplingSlope.KernelDecayArgument
end
