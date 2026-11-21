import YangMills.Construction.InequalityOnMirroredCopies.ObservableOffTheFacesIsInTheCell
import YangMills.Construction.InfiniteLattice.FunctionsOfSomeOfTheBondsAndClassesStableUnderBoundedLimits
import YangMills.Construction.ReflectionsAndOneInsertion.ReflectionsObservablesAndCellData
import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open Filter MeasureTheory Set TestFunctions
open ChessboardTori
open InfiniteLattice (AmbientSpace ElementaryPlaquette)
open ReflectionsAndOneInsertion (complexSmeared)
namespace CellSupport
variable {D : ChessboardSetup}
private theorem mesh_pos (D : ChessboardSetup) : 0 < D.mesh := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardSetup.mesh_pos <;> assumption
private theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem continuous_of_isLipschitzFor {f : AmbientSpace → ℝ}
    (hf : IsLipschitzFor euclidDistR4 f) : Continuous f := by apply _root_.YangMills.SharedProofs.p29528 <;> assumption
private theorem isBoundedFun_of_isLipschitzFor {f : AmbientSpace → ℝ} {y : AmbientSpace} {r : ℝ}
    (hf : IsLipschitzFor euclidDistR4 f) (hv : ∀ x, x ∉ closedBallR4 y r → f x = 0) :
    TestFunctions.IsBoundedFun f := by
  obtain ⟨C, hC0, hC⟩ := hf
  refine ⟨‖f y‖ + C * |r|, fun x => ?_⟩
  by_cases hx : x ∈ closedBallR4 y r
  · have hd : euclidDistR4 x y ≤ r := hx
    have h₁ : ‖f x‖ ≤ ‖f y‖ + ‖f x - f y‖ := norm_le_norm_add_norm_sub' _ _
    have h₂ : C * euclidDistR4 x y ≤ C * |r| :=
      mul_le_mul_of_nonneg_left (hd.trans (le_abs_self r)) hC0
    have h₃ := hC x y
    linarith
  · rw [hv x hx, norm_zero]
    exact add_nonneg (norm_nonneg _) (mul_nonneg hC0 (abs_nonneg _))
abbrev _root_.YangMills.SharedProofs.p118540 := @isBoundedFun_of_isLipschitzFor
private theorem isBounded_closedBallR4 (c : AmbientSpace) {r : ℝ} (hr : 0 ≤ r) :
    Bornology.IsBounded (closedBallR4 c r) := by
  refine (Metric.isBounded_closedBall (x := c) (r := r)).subset fun x hx => ?_
  refine Metric.mem_closedBall.2 ((dist_pi_le_iff hr).2 fun μ => ?_)
  rw [Real.dist_eq]
  exact (abs_apply_le_euclidNormVec (x - c) μ).trans hx
abbrev _root_.YangMills.SharedProofs.p53483 := @isBounded_closedBallR4
private theorem ofReal_smearedEnergy {a : ℝ} (f : AmbientSpace → ℝ)
    (U : InfiniteLattice.GaugeField a)
    (hfin : (Function.support fun p : ElementaryPlaquette a =>
      InfiniteLattice.faceEnergy U p • f p.center).Finite) :
    ((InfiniteLattice.smearedEnergy f U : ℝ) : ℂ) =
      InfiniteLattice.smearedEnergy (fun x => (f x : ℂ)) U := by
  unfold InfiniteLattice.smearedEnergy
  refine (AddMonoidHom.map_finsum Complex.ofRealHom.toAddMonoidHom hfin).trans
    (finsum_congr fun p => ?_)
  simp
abbrev _root_.YangMills.SharedProofs.p21788 := @ofReal_smearedEnergy
private theorem vertex_near_center (p : ElementaryPlaquette D.mesh)
    {y : InfiniteLattice.LatticePoint D.mesh}
    (hy : y ∈ p.cornerSet) (μ : Fin 4) : |(y : AmbientSpace) μ - p.center μ| ≤ D.mesh / 2 := by
  have hne : ¬(μ = p.lowAxis ∧ μ = p.highAxis) := fun h =>
    p.lowAxis_lt_highAxis.ne (h.1.symm.trans h.2)
  have ha := mesh_pos D
  have hs : ∀ ν, ((InfiniteLattice.axisStep D.mesh ν : InfiniteLattice.LatticePoint D.mesh) :
      AmbientSpace) μ = if μ = ν then D.mesh else 0 := fun ν => by
    simp [InfiniteLattice.axisStep, Pi.single_apply]
  have hb : p.center μ = (p.corner : AmbientSpace) μ + (if μ = p.lowAxis then D.mesh / 2 else 0) +
      (if μ = p.highAxis then D.mesh / 2 else 0) := by
    simp [ElementaryPlaquette.center, Pi.single_apply]
  simp only [InfiniteLattice.ElementaryPlaquette.cornerSet, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl <;>
    simp only [AddSubgroup.coe_add, Pi.add_apply, hs, hb] <;> split_ifs <;>
    first
    | exact absurd ⟨by assumption, by assumption⟩ hne
    | (rw [abs_le]; constructor <;> linarith)
private theorem center_apply_eq_int_mul (p : ElementaryPlaquette D.mesh) (μ : Fin 4) :
    ∃ t : ℤ, p.center μ = (t : ℝ) * (D.mesh / 2) := by
  have hne : ¬(μ = p.lowAxis ∧ μ = p.highAxis) := fun h =>
    p.lowAxis_lt_highAxis.ne (h.1.symm.trans h.2)
  have hb : p.center μ = (p.corner : AmbientSpace) μ + (if μ = p.lowAxis then D.mesh / 2 else 0) +
      (if μ = p.highAxis then D.mesh / 2 else 0) := by
    simp [ElementaryPlaquette.center, Pi.single_apply]
  obtain ⟨m, hm⟩ := p.corner.2
  rw [hb, hm μ]
  split_ifs with h1 h2 h2
  · exact absurd ⟨h1, h2⟩ hne
  · exact ⟨2 * m μ + 1, by push_cast; ring⟩
  · exact ⟨2 * m μ + 1, by push_cast; ring⟩
  · exact ⟨2 * m μ, by push_cast; ring⟩
private theorem even_strictly_between {e : ℝ} (he : 0 < e) {I J t u : ℤ}
    (h1 : ((2 * I + 1 : ℤ) : ℝ) * e ≤ (t : ℝ) * e) (h2 : (t : ℝ) * e ≤ ((2 * J + 1 : ℤ) : ℝ) * e)
    (n1 : t ≠ 2 * I + 1) (n2 : t ≠ 2 * J + 1)
    (h : |((2 * u : ℤ) : ℝ) * e - (t : ℝ) * e| ≤ e) :
    ((2 * I + 1 : ℤ) : ℝ) * e < ((2 * u : ℤ) : ℝ) * e ∧
      ((2 * u : ℤ) : ℝ) * e < ((2 * J + 1 : ℤ) : ℝ) * e := by
  have a1 : 2 * I + 1 ≤ t := by exact_mod_cast le_of_mul_le_mul_right h1 he
  have a2 : t ≤ 2 * J + 1 := by exact_mod_cast le_of_mul_le_mul_right h2 he
  obtain ⟨h3, h4⟩ := abs_le.mp h
  have a3 : 2 * u ≤ t + 1 := by
    have : ((2 * u : ℤ) : ℝ) * e ≤ ((t + 1 : ℤ) : ℝ) * e := by
      push_cast at h4 ⊢
      linarith
    exact_mod_cast le_of_mul_le_mul_right this he
  have a4 : t - 1 ≤ 2 * u := by
    have : ((t - 1 : ℤ) : ℝ) * e ≤ ((2 * u : ℤ) : ℝ) * e := by
      push_cast at h3 ⊢
      linarith
    exact_mod_cast le_of_mul_le_mul_right this he
  have b1 : 2 * I + 1 < 2 * u := by omega
  have b2 : 2 * u < 2 * J + 1 := by omega
  exact ⟨mul_lt_mul_of_pos_right (by exact_mod_cast b1) he,
    mul_lt_mul_of_pos_right (by exact_mod_cast b2) he⟩
private theorem vertex_strictly_between_walls (g : ReflectionGrid D) (k : Fin 4 → ℤ)
    (p : ElementaryPlaquette D.mesh)
    (hin : p.center ∈ g.cell k) (hoff : p.center ∉ g.walls)
    {y : InfiniteLattice.LatticePoint D.mesh} (hy : y ∈ p.cornerSet) (μ : Fin 4) :
    g.origin μ + g.cellSide * k μ < (y : AmbientSpace) μ ∧
      (y : AmbientSpace) μ < g.origin μ + g.cellSide * k μ + g.cellSide := by
  have ha := mesh_pos D
  obtain ⟨m, hm⟩ := y.2
  obtain ⟨t, ht⟩ := center_apply_eq_int_mul p μ
  obtain ⟨i, hi⟩ := g.origin_mem μ
  have hr := g.cellSide_eq
  have hwall : ∀ z : ℤ, p.center μ ≠ g.origin μ + (z : ℝ) * g.cellSide := fun z hz =>
    hoff (Set.mem_iUnion.2 ⟨μ, Set.mem_iUnion.2 ⟨z, hz⟩⟩)
  set e := D.mesh / 2 with he
  have he0 : 0 < e := by positivity
  have hf : ∀ z : ℤ, g.origin μ + (z : ℝ) * g.cellSide =
      ((2 * (i + g.cellRatio * z) + 1 : ℤ) : ℝ) * e := fun z => by
    rw [hi, hr, he]
    push_cast
    ring
  have hcell := hin μ
  have n1 : t ≠ 2 * (i + g.cellRatio * k μ) + 1 := fun h => hwall (k μ) (by rw [ht, hf, h])
  have n2 : t ≠ 2 * (i + g.cellRatio * (k μ + 1)) + 1 := fun h =>
    hwall (k μ + 1) (by rw [ht, hf, h])
  have e1 := hf (k μ)
  have e2 := hf (k μ + 1)
  have hnear := vertex_near_center p hy μ
  have hyu : (y : AmbientSpace) μ = ((2 * m μ : ℤ) : ℝ) * e := by
    rw [hm μ, he]
    push_cast
    ring
  rw [← he, ht, hyu] at hnear
  have hpush : ((k μ + 1 : ℤ) : ℝ) = (k μ : ℝ) + 1 := by push_cast; ring
  rw [hpush] at e2
  obtain ⟨b1, b2⟩ := even_strictly_between he0 (I := i + g.cellRatio * k μ)
    (J := i + g.cellRatio * (k μ + 1))
    (t := t) (u := m μ) (by rw [← e1, ← ht]; linarith [hcell.1])
    (by rw [← e2, ← ht]; linarith [hcell.2]) n1 n2 hnear
  rw [← e1, ← hyu] at b1
  rw [← e2, ← hyu] at b2
  constructor <;> linarith
end CellSupport
theorem smearedMemCellObservables_of_linkFunctions
    (hB : FieldsAtSpacing.LinkFunctionsStatement)
    (hmaps : ReflectionsAndOneInsertion.ReflectionsObservablesCells.Statement) :
    SmearedMemCellObservables := by
  intro D c ϱ f hf
  have hr0 : 0 ≤ ϱ := hf.radius_pos.le
  have hcont := CellSupport.continuous_of_isLipschitzFor hf.lipschitz
  obtain ⟨y₀, hy₀⟩ := hf.support_in_ball
  have hv : ∀ x, x ∉ closedBallR4 y₀ ϱ → f x = 0 := fun x hx =>
    by_contra fun hne => hx (hy₀ x hne)
  have hbd := CellSupport.isBoundedFun_of_isLipschitzFor hf.lipschitz hv
  obtain ⟨-, hfinB, hsum, -, -⟩ :=
    (hB D.mesh (CellSupport.mesh_pos D) ∅ (Set.empty_subset _)).2.2.2.2.2
  have hv' : InfiniteLattice.IsBoundedBorelCompactlySupported (fun x => (f x : ℂ)) := by
    refine ⟨Complex.measurable_ofReal.comp hcont.measurable, ?_, ?_⟩
    · obtain ⟨C, hC⟩ := hbd
      exact ⟨C, fun x => by simpa using hC x⟩
    · refine HasCompactSupport.intro (isCompact_closedBall y₀ ϱ) fun x hx => ?_
      have hx' : x ∉ closedBallR4 y₀ ϱ := fun hb' => hx <| by
        refine Metric.mem_closedBall.2 ((dist_pi_le_iff hr0).2 fun μ => ?_)
        rw [Real.dist_eq]
        exact (CellSupport.abs_apply_le_euclidNormVec (x - y₀) μ).trans hb'
      simp [hv x hx']
  have hopen : {x : AmbientSpace | ∀ μ, c.grid.origin μ + c.grid.cellSide * c.index μ < x μ ∧
      x μ < c.grid.origin μ + c.grid.cellSide * c.index μ + c.grid.cellSide} ⊆
        interior c.cell := by
    refine interior_maximal (fun x hx μ => ?_) ?_
    · have := hx μ
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    · have : {x : AmbientSpace | ∀ μ, c.grid.origin μ + c.grid.cellSide * c.index μ < x μ ∧
          x μ < c.grid.origin μ + c.grid.cellSide * c.index μ + c.grid.cellSide} =
          ⋂ μ, {x : AmbientSpace | c.grid.origin μ + c.grid.cellSide * c.index μ < x μ ∧
            x μ < c.grid.origin μ + c.grid.cellSide * c.index μ + c.grid.cellSide} := by
        ext x
        simp
      rw [this]
      refine isOpen_iInter_of_finite fun μ => ?_
      exact (isOpen_lt continuous_const (continuous_apply μ)).inter
        (isOpen_lt (continuous_apply μ) continuous_const)
  have hcorners : ∀ p : ElementaryPlaquette D.mesh, (fun x => (f x : ℂ)) p.center ≠ 0 →
      FieldsAtSpacing.ContainsCorners (interior c.cell) p := by
    intro p hp y hy
    have hne : f p.center ≠ 0 := fun h0 => hp (by simp [h0])
    have hoff : p.center ∉ c.grid.walls := fun hz => by
      have := hf.far_from_walls _ hne _ hz
      have h0 : TorusMetric.euclidNormVec (p.center - p.center) = 0 := by
        simp [TorusMetric.euclidNormVec]
      rw [h0] at this
      exact absurd this (not_le.mpr hf.radius_pos)
    exact hopen fun μ => CellSupport.vertex_strictly_between_walls c.grid c.index p
      (hf.support_in_cell _ hne) hoff hy μ
  have hc := ((hsum _ hv').2.2.2 (interior c.cell) hcorners).1
  have e : complexSmeared D f = InfiniteLattice.smearedEnergy (fun x => (f x : ℂ)) := by
    funext U
    refine CellSupport.ofReal_smearedEnergy f U
      ((hfinB _ (CellSupport.isBounded_closedBallR4 y₀ hr0)).subset ?_)
    intro p hp
    exact by_contra fun hn => hp (by simp [hv _ hn])
  obtain ⟨-, -, -, hW, -, -⟩ := hmaps D
  rw [hW.2.2.2 c.grid c.hasAdmissibleSide c.cell c.cell_mem_cellSet, e]
  exact hc
end YangMills.Construction.ReflectedCopies
end
