import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Lattice.PeriodicLattices
import YangMills.Construction.FormOnAFibre.SiteFormsAtAFiniteSideAreEuclidean
import YangMills.Construction.Lattice.AmbientSpaceOfTheRealPairsOnADomain
import YangMills.Construction.Lattice.MatricesBlocksAndGaugeTransformations
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometriesProof
import YangMills.Construction.RunningCouplingSlope.BackgroundMapsOfAFamilyThroughOne
import YangMills.Construction.RunningCouplingSlope.EntriesOfTheFunctionOfTheWholeChain
import YangMills.Construction.RunningCouplingSlope.FieldsOfAFamilyThroughOne
import YangMills.Construction.RunningCouplingSlope.TheGaugeShiftReadsNearCellsProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Filter Matrices Tower
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace RunningCouplingSlope.ChainEntries
section Calculus
variable {E Z Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
private def fderivSnd {Y' : Type} [NormedAddCommGroup Y'] [NormedSpace ℝ Y'] (Φ : E × Z → Y') (q : E × Z) : Z →L[ℝ] Y' :=
  (fderiv ℝ Φ q).comp (ContinuousLinearMap.inr ℝ E Z)
private theorem analyticAt_fderivSnd {Y' : Type} [NormedAddCommGroup Y'] [NormedSpace ℝ Y'] [CompleteSpace Y']
    {Φ : E × Z → Y'} {q : E × Z} (h : AnalyticAt ℝ Φ q) : AnalyticAt ℝ (fderivSnd Φ) q := by
  have hd : AnalyticAt ℝ (fderiv ℝ Φ) q := h.fderiv
  exact ((ContinuousLinearMap.compL ℝ Z (E × Z) Y').flip
    (ContinuousLinearMap.inr ℝ E Z)).analyticAt _ |>.comp hd
private theorem hasDerivAt_line_snd {Y' : Type} [NormedAddCommGroup Y'] [NormedSpace ℝ Y']
    {Φ : E × Z → Y'} {w : E} {x b : Z} (h : DifferentiableAt ℝ Φ (w, x)) :
    HasDerivAt (fun t : ℝ => Φ (w, x + t • b)) (fderivSnd Φ (w, x) b) 0 := by
  have hc : HasDerivAt (fun t : ℝ => ((w, x + t • b) : E × Z)) ((0 : E), b) 0 := by
    have hl : HasDerivAt (fun t : ℝ => x + t • b) b 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add x
    exact (hasDerivAt_const (0 : ℝ) w).prodMk hl
  have hz : ((w, x + (0 : ℝ) • b) : E × Z) = (w, x) := by simp
  have hΦ : HasFDerivAt Φ (fderiv ℝ Φ (w, x)) ((w, x + (0 : ℝ) • b) : E × Z) := by
    rw [hz]
    exact h.hasFDerivAt
  have := hΦ.comp_hasDerivAt (0 : ℝ) hc
  simpa [fderivSnd, Function.comp_def] using this
private theorem exists_analytic_mixedDeriv [CompleteSpace Y] {Φ : E × Z → Y} {p₀ : E}
    (hΦ : AnalyticAt ℝ Φ (p₀, 0)) :
    ∃ Bf : E → Z →L[ℝ] Z →L[ℝ] Y, AnalyticAt ℝ Bf p₀ ∧ ∀ᶠ w in 𝓝 p₀, ∀ a b : Z,
      deriv (fun s : ℝ => deriv (fun t : ℝ => Φ (w, s • a + t • b)) 0) 0 = Bf w a b := by
  set D₁ : E × Z → Z →L[ℝ] Y := fderivSnd Φ with hD₁
  set D₂ : E × Z → Z →L[ℝ] Z →L[ℝ] Y := fderivSnd D₁ with hD₂
  have hD₁a : AnalyticAt ℝ D₁ (p₀, 0) := analyticAt_fderivSnd hΦ
  have hD₂a : AnalyticAt ℝ D₂ (p₀, 0) := analyticAt_fderivSnd hD₁a
  have hemb : AnalyticAt ℝ (fun w : E => ((w, 0) : E × Z)) p₀ :=
    analyticAt_id.prod analyticAt_const
  refine ⟨fun w => D₂ (w, 0), AnalyticAt.comp (g := D₂) (f := fun w : E => ((w, 0) : E × Z)) hD₂a hemb, ?_⟩
  have hev : ∀ᶠ q in 𝓝 ((p₀, 0) : E × Z), AnalyticAt ℝ Φ q ∧ AnalyticAt ℝ D₁ q :=
    hΦ.eventually_analyticAt.and hD₁a.eventually_analyticAt
  have hev' : ∀ᶠ w in 𝓝 p₀, ∀ᶠ x in 𝓝 (0 : Z), AnalyticAt ℝ Φ (w, x) ∧ AnalyticAt ℝ D₁ (w, x) :=
    hev.curry_nhds
  filter_upwards [hev'] with w hw a b
  have hs : ∀ᶠ s : ℝ in 𝓝 0, AnalyticAt ℝ Φ (w, s • a) := by
    have ht : Tendsto (fun s : ℝ => s • a) (𝓝 0) (𝓝 (0 : Z)) := by
      have : Continuous fun s : ℝ => s • a := by fun_prop
      simpa using this.tendsto 0
    exact (ht.eventually hw).mono fun s h => h.1
  have hinner : (fun s : ℝ => deriv (fun t : ℝ => Φ (w, s • a + t • b)) 0) =ᶠ[𝓝 0]
      fun s => D₁ (w, s • a) b := by
    filter_upwards [hs] with s h
    exact (hasDerivAt_line_snd h.differentiableAt).deriv
  rw [hinner.deriv_eq]
  have hdiff : DifferentiableAt ℝ D₁ (w, (0 : Z)) := hw.self_of_nhds.2.differentiableAt
  have hline := hasDerivAt_line_snd (b := a) hdiff
  have happ : HasDerivAt (fun s : ℝ => D₁ (w, s • a) b) (D₂ (w, 0) a b) 0 := by
    have hcomp := (ContinuousLinearMap.apply ℝ Y b).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (by simpa using hline)
    simpa [Function.comp_def] using hcomp
  exact happ.deriv
end Calculus
section Tools
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p₀ : E}
private theorem analyticAt_matInv {f : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀) (hu : (f p₀).det ≠ 0) :
    AnalyticAt ℝ (fun y => (f y)⁻¹) p₀ := by apply _root_.YangMills.SharedProofs.p24898 <;> assumption
private theorem analyticAt_complexSmul (c : ℂ) {f : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀) :
    AnalyticAt ℝ (fun p => c • f p) p₀ := by apply _root_.YangMills.SharedProofs.p44577 <;> assumption
private theorem analyticAt_matExp {f : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀) :
    AnalyticAt ℝ (fun p => ComplexMatrix2.matExp (f p)) p₀ :=
  AnalyticAt.comp (g := ComplexMatrix2.matExp) (NormedSpace.exp_analytic (𝕂 := ℝ) _) hf
private theorem analyticAt_conjugateBy {f g : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀) (hg : AnalyticAt ℝ g p₀)
    (hu : (f p₀).det ≠ 0) : AnalyticAt ℝ (fun p => ComplexMatrix2.conjugateBy (f p) (g p)) p₀ :=
  (hf.mul hg).mul (analyticAt_matInv hf hu)
private theorem analyticAt_halfTrace {f : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀) :
    AnalyticAt ℝ (fun p => ComplexMatrix2.halfTrace (f p)) p₀ := by
  have h : AnalyticAt ℝ (fun p => Matrix.trace (f p)) p₀ :=
    (LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).restrictScalars ℝ)).analyticAt _ |>.comp hf
  exact analyticAt_const.mul h
private theorem analyticAt_re {z : E → ℂ} (hz : AnalyticAt ℝ z p₀) :
    AnalyticAt ℝ (fun p => (z p).re) p₀ :=
  (Complex.reCLM.analyticAt _).comp hz
private theorem analyticAt_traceFinsumPairing {ι : Type} [Finite ι] {f g : E → ι → ComplexMatrix2}
    (hf : ∀ i, AnalyticAt ℝ (fun p => f p i) p₀) (hg : ∀ i, AnalyticAt ℝ (fun p => g p i) p₀) :
    AnalyticAt ℝ (fun p => traceFinsumPairing (f p) (g p)) p₀ := by
  have := Fintype.ofFinite ι
  have e : (fun p => traceFinsumPairing (f p) (g p)) =
      fun p => ∑ i, ComplexMatrix2.halfTrace (f p i * g p i) := by
    funext p
    exact finsum_eq_sum_of_fintype _
  rw [e]
  exact Finset.analyticAt_fun_sum _ fun i _ => analyticAt_halfTrace ((hf i).mul (hg i))
end Tools
section Lattice
variable {L n k j : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p₀ : E}
private theorem expTwist_of_pos {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_positive <;> assumption
private theorem expTwist_of_not_pos {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_not_positive <;> assumption
private theorem matExp_I_smul_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • X) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
private theorem compact_mul_mem {g g' : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hg' : g' ∈ PeriodicLattice.compactGaugeGroup) : g * g' ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.mul_mem_of_mem <;> assumption
private theorem expTwist_mem_fieldSpace
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {A U : Edge L n k j → ComplexMatrix2} (hA : A ∈ edgeFormSpace L n k j) (hU : U ∈ fieldSpace L n k j) :
    PeriodicLattice.expTwist A U ∈ fieldSpace L n k j := by apply _root_.YangMills.SharedProofs.p8814 <;> assumption
private theorem analyticAt_pathHolonomy {V : E → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, AnalyticAt ℝ (fun p => V p b) p₀) (l : List (Edge L n k j)) :
    AnalyticAt ℝ (fun p => PeriodicLattice.pathHolonomy (V p) l) p₀ := by
  induction l with
  | nil =>
    simpa [PeriodicLattice.pathHolonomy] using analyticAt_const
  | cons b l ih =>
    have h : AnalyticAt ℝ (fun p => V p b * PeriodicLattice.pathHolonomy (V p) l) p₀ := (hV b).mul ih
    exact h.congr (Eventually.of_forall fun p => by simp [PeriodicLattice.pathHolonomy])
private theorem analyticAt_extendOddly {f : E → Edge L n k j → ComplexMatrix2}
    (hf : ∀ c : Edge L n k j, c.IsPositivelyOriented → AnalyticAt ℝ (fun p => f p c) p₀)
    (hr : ∀ c : Edge L n k j, c.IsPositivelyOriented ∨ c.opposite.IsPositivelyOriented) (c : Edge L n k j) :
    AnalyticAt ℝ (fun p => extendOddly (f p) c) p₀ := by
  classical
  by_cases hc : c.IsPositivelyOriented
  · refine (hf c hc).congr (Eventually.of_forall fun p => ?_)
    simp [extendOddly, hc]
  · have hop := (hr c).resolve_left hc
    refine (hf _ hop).neg.congr (Eventually.of_forall fun p => ?_)
    simp [extendOddly, hc]
end Lattice
section Chain
variable {L n k : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p₀ : E}
private structure TowerFacts (L n k : ℕ) : Prop where
  edges_finite : ∀ j, Finite (Edge L n k j)
  vertices_finite : ∀ j, Finite (Vertex L n k j)
  orientation : ∀ j ≤ k, ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
private theorem towerFacts (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) : TowerFacts L n k := by
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have : NeZero L := ⟨by omega⟩
  have hb : ∀ j, Finite (Edge L n k j) := fun j => PeriodicLattice.instFiniteBond _
  have hs : ∀ j, Finite (Vertex L n k j) := fun j =>
    SeparatedSequences.BaseParameters.site_finite (by omega) n _
  exact ⟨hb, hs, fun j hj b =>
    PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b⟩
private theorem expMove_zero_unitPoint :
    expMove (0 : LevelForms L n k) (unitPoint L n k) = unitPoint L n k := by apply _root_.YangMills.SharedProofs.p5970 <;> assumption
private theorem isAnalyticFamily_expMove (F : TowerFacts L n k) {X : E → ChainPoint L n k}
    (hX : IsAnalyticFamilyThroughUnit X p₀) {g : E → LevelForms L n k} (hg₀ : g p₀ = 0)
    (hg₁ : ∀ b, AnalyticAt ℝ (fun p => ((g p).1 : Edge L n k 0 → ComplexMatrix2) b) p₀)
    (hg₂ : ∀ (i : Fin k) (c : Edge L n k (i + 1)),
      AnalyticAt ℝ (fun p => ((g p).2 i : Edge L n k (i + 1) → ComplexMatrix2) c) p₀) :
    IsAnalyticFamilyThroughUnit (fun p => expMove (g p) (X p)) p₀ := by
  have hval : ∀ b : Edge L n k 0, AnalyticAt ℝ (fun p => ComplexMatrix2.matExp
      (Complex.I • ((g p).1 : Edge L n k 0 → ComplexMatrix2) b) * (X p).fine b) p₀ := fun b =>
    (analyticAt_matExp (analyticAt_complexSmul _ (hg₁ b))).mul (hX.analyticAt_fine b)
  refine ⟨?_, fun b => ?_, fun i c => ?_, ?_⟩
  · show expMove (g p₀) (X p₀) = _
    rw [hg₀, hX.eq_unit, expMove_zero_unitPoint]
  · by_cases hb : b.IsPositivelyOriented
    · exact (hval b).congr (Eventually.of_forall fun p => (expTwist_of_pos hb).symm)
    · refine (analyticAt_matInv (hval b.opposite) ?_).congr
        (Eventually.of_forall fun p => (expTwist_of_not_pos hb).symm)
      have hzero : ((g p₀).1 : Edge L n k 0 → ComplexMatrix2) b.opposite = 0 := by
        rw [hg₀]
        rfl
      have hone : (X p₀).fine b.opposite = 1 := by
        rw [hX.eq_unit]
        rfl
      simp [hzero, hone, ComplexMatrix2.matExp, NormedSpace.exp_zero]
  · exact (analyticAt_matExp (analyticAt_complexSmul _ (hg₂ i c.1))).mul (hX.analyticAt_noise i c)
  · filter_upwards [hX.eventually_compact] with p h
    exact ⟨expTwist_mem_fieldSpace (F.orientation 0 (Nat.zero_le k)) (g p).1.2 h.1, fun i c =>
      compact_mul_mem (matExp_I_smul_mem (((g p).2 i).2.1 c.1 c.2)) (h.2 i c)⟩
private theorem fine_det_ne_zero {X : E → ChainPoint L n k} (hX : IsAnalyticFamilyThroughUnit X p₀)
    (b : Edge L n k 0) : ((X p₀).fine b).det ≠ 0 := by
  rw [hX.eq_unit]
  simp [unitPoint]
private theorem noise_det_ne_zero {X : E → ChainPoint L n k} (hX : IsAnalyticFamilyThroughUnit X p₀)
    (i : Fin k) (c : PositiveEdge L n k (i + 1)) : ((X p₀).noise i c).det ≠ 0 := by
  rw [hX.eq_unit]
  simp [unitPoint]
private def AnalyticValues (f : E → LevelValues L n k) (p₀ : E) : Prop :=
  (∀ b, AnalyticAt ℝ (fun p => (f p).1 b) p₀) ∧
    ∀ (i : Fin k) b, AnalyticAt ℝ (fun p => (f p).2 i b) p₀
private theorem TowerFacts.positive_finite (F : TowerFacts L n k) (j : ℕ) : Finite (PositiveEdge L n k j) := by
  have := F.edges_finite j
  exact Subtype.finite
private theorem analyticAt_edgeFormPairing (F : TowerFacts L n k) {j : ℕ} {B B' : E → Edge L n k j → ComplexMatrix2}
    (hB : ∀ b, AnalyticAt ℝ (fun p => B p b) p₀) (hB' : ∀ b, AnalyticAt ℝ (fun p => B' p b) p₀) :
    AnalyticAt ℝ (fun p => edgeFormPairing (B p) (B' p)) p₀ := by
  have := F.positive_finite j
  exact analyticAt_traceFinsumPairing (f := fun p => restrictToPositiveEdges (B p))
    (g := fun p => restrictToPositiveEdges (B' p)) (fun b => hB b.1) fun b => hB' b.1
private theorem analyticAt_levelPairing (F : TowerFacts L n k) {f g : E → LevelValues L n k}
    (hf : AnalyticValues f p₀) (hg : AnalyticValues g p₀) :
    AnalyticAt ℝ (fun p => levelPairing (f p) (g p)) p₀ := by
  have h₁ := analyticAt_re (analyticAt_edgeFormPairing F hf.1 hg.1)
  have h₂ : AnalyticAt ℝ (fun p => ∑ i : Fin k, (edgeFormPairing ((f p).2 i) ((g p).2 i)).re) p₀ :=
    Finset.analyticAt_fun_sum _ fun i _ => analyticAt_re (analyticAt_edgeFormPairing F (hf.2 i) (hg.2 i))
  exact h₁.add h₂
private theorem analyticAt_covDiff (F : TowerFacts L n k) {j : ℕ} (hj : j ≤ k)
    {U : E → Edge L n k j → ComplexMatrix2} {l : E → Vertex L n k j → ComplexMatrix2}
    (hU : ∀ b, AnalyticAt ℝ (fun p => U p b) p₀) (hl : ∀ x, AnalyticAt ℝ (fun p => l p x) p₀)
    (hd : ∀ b, (U p₀ b).det ≠ 0) (b : Edge L n k j) :
    AnalyticAt ℝ (fun p => covDiff (U p) (l p) b) p₀ :=
  analyticAt_extendOddly (fun c _ => (analyticAt_conjugateBy (hU c) (hl _) (hd c)).sub (hl _))
    (fun c => (F.orientation j hj c).elim (fun h => Or.inl h.1) fun h => Or.inr h.1) b
private theorem analyticAt_lie {f g : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀) (hg : AnalyticAt ℝ g p₀) :
    AnalyticAt ℝ (fun p => ⁅f p, g p⁆) p₀ := by
  have h : AnalyticAt ℝ (fun p => f p * g p - g p * f p) p₀ := (hf.mul hg).sub (hg.mul hf)
  exact h.congr (Eventually.of_forall fun p => (Ring.lie_def _ _).symm)
private theorem analyticValues_chainBracket (F : TowerFacts L n k) {X : E → ChainPoint L n k}
    (hX : IsAnalyticFamilyThroughUnit X p₀) {l : E → Vertex L n k 0 → ComplexMatrix2}
    (hl : ∀ x, AnalyticAt ℝ (fun p => l p x) p₀) {v : E → LevelValues L n k} (hv : AnalyticValues v p₀) :
    AnalyticValues (fun p => chainBracket (X p) (l p) (v p)) p₀ := by
  have hr : ∀ (j : ℕ), j ≤ k → ∀ c : Edge L n k j, c.IsPositivelyOriented ∨ c.opposite.IsPositivelyOriented :=
    fun j hj c => (F.orientation j hj c).elim (fun h => Or.inl h.1) fun h => Or.inr h.1
  refine ⟨fun b => ?_, fun i b => ?_⟩
  · exact analyticAt_extendOddly (fun c _ => analyticAt_complexSmul _ (analyticAt_lie ((hl _).add
      (analyticAt_conjugateBy (hX.analyticAt_fine c) (hl _) (fine_det_ne_zero hX c))) (hv.1 c)))
      (hr 0 (Nat.zero_le k)) b
  · refine analyticAt_extendOddly (f := fun p c => (open Classical in
      if hc : c.IsPositivelyOriented then (Complex.I / 2) • ⁅restrictVertexFunction (i + 1) (l p) c.source +
          ComplexMatrix2.conjugateBy ((X p).noise i ⟨c, hc⟩) (restrictVertexFunction (i + 1) (l p) c.source),
          (v p).2 i c⁆
      else 0)) (fun c hc => ?_) (hr _ i.2) b
    simp only [dif_pos hc]
    exact analyticAt_complexSmul _ (analyticAt_lie ((hl _).add
      (analyticAt_conjugateBy (hX.analyticAt_noise i ⟨c, hc⟩) (hl _) (noise_det_ne_zero hX i _)))
      (hv.2 i c))
private theorem analyticValues_gaugeOrbitValues (F : TowerFacts L n k) {X : E → ChainPoint L n k}
    (hX : IsAnalyticFamilyThroughUnit X p₀) {l : E → Vertex L n k 0 → ComplexMatrix2}
    (hl : ∀ x, AnalyticAt ℝ (fun p => l p x) p₀) :
    AnalyticValues (fun p => gaugeOrbitValues (X p) (l p)) p₀ := by
  have hr : ∀ (j : ℕ), j ≤ k → ∀ c : Edge L n k j, c.IsPositivelyOriented ∨ c.opposite.IsPositivelyOriented :=
    fun j hj c => (F.orientation j hj c).elim (fun h => Or.inl h.1) fun h => Or.inr h.1
  refine ⟨fun b => analyticAt_covDiff F (Nat.zero_le k) hX.analyticAt_fine hl (fine_det_ne_zero hX) b,
    fun i b => ?_⟩
  refine analyticAt_extendOddly (f := fun p c => (open Classical in
      if hc : c.IsPositivelyOriented then
        ComplexMatrix2.conjugateBy ((X p).noise i ⟨c, hc⟩) (restrictVertexFunction (i + 1) (l p) c.source) -
          restrictVertexFunction (i + 1) (l p) c.source else 0)) (fun c hc => ?_) (hr _ i.2) b
  simp only [dif_pos hc]
  exact (analyticAt_conjugateBy (hX.analyticAt_noise i ⟨c, hc⟩) (hl _) (noise_det_ne_zero hX i _)).sub (hl _)
end Chain
section Linear
variable {L n k : ℕ}
private def IsQuadraticFn {V : Type} [AddCommGroup V] [Module ℝ V] (f : V → ℝ) : Prop :=
  ∃ q : QuadraticForm ℝ V, ∀ ξ, q ξ = f ξ
private theorem IsQuadraticFn.add {V : Type} [AddCommGroup V] [Module ℝ V] {f g : V → ℝ}
    (hf : IsQuadraticFn f) (hg : IsQuadraticFn g) : IsQuadraticFn fun ξ => f ξ + g ξ := by
  obtain ⟨q, hq⟩ := hf
  obtain ⟨q', hq'⟩ := hg
  exact ⟨q + q', fun ξ => by simp [hq, hq']⟩
private theorem IsQuadraticFn.sub {V : Type} [AddCommGroup V] [Module ℝ V] {f g : V → ℝ}
    (hf : IsQuadraticFn f) (hg : IsQuadraticFn g) : IsQuadraticFn fun ξ => f ξ - g ξ := by
  obtain ⟨q, hq⟩ := hf
  obtain ⟨q', hq'⟩ := hg
  exact ⟨q - q', fun ξ => by simp [hq, hq']⟩
private theorem isQuadraticFn_of_bilin {V : Type} [AddCommGroup V] [Module ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {f : V → ℝ} (h : ∀ ξ, f ξ = β ξ ξ) : IsQuadraticFn f :=
  ⟨LinearMap.BilinMap.toQuadraticMap β, fun ξ => by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, h]⟩
private theorem extendOddly_add {j : ℕ} {f g h : Edge L n k j → ComplexMatrix2} (e : ∀ c, f c = g c + h c) :
    extendOddly f = extendOddly g + extendOddly h := by
  classical
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp [extendOddly, hb, e]
  · simp [extendOddly, hb, e, add_comm]
private theorem extendOddly_smul {j : ℕ} (r : ℝ) {f g : Edge L n k j → ComplexMatrix2}
    (e : ∀ c, f c = r • g c) : extendOddly f = r • extendOddly g := by
  classical
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp [extendOddly, hb, e]
  · simp [extendOddly, hb, e]
private def bracketTerm (g a b v : ComplexMatrix2) : ComplexMatrix2 :=
  (Complex.I / 2) • ⁅a + ComplexMatrix2.conjugateBy g b, v⁆
private theorem bracketTerm_add_left (g a a' b b' v : ComplexMatrix2) :
    bracketTerm g (a + a') (b + b') v = bracketTerm g a b v + bracketTerm g a' b' v := by
  simp only [bracketTerm, ComplexMatrix2.conjugateBy, Ring.lie_def, mul_add, add_mul, ← smul_add]
  congr 1
  abel
private theorem bracketTerm_smul_left (r : ℝ) (g a b v : ComplexMatrix2) :
    bracketTerm g (r • a) (r • b) v = r • bracketTerm g a b v := by
  simp only [bracketTerm, ComplexMatrix2.conjugateBy, Ring.lie_def, mul_add, add_mul, mul_smul_comm,
    smul_mul_assoc, smul_add, smul_sub]
  rw [smul_comm r (Complex.I / 2), smul_comm r (Complex.I / 2), smul_comm r (Complex.I / 2),
    smul_comm r (Complex.I / 2)]
private theorem bracketTerm_add_right (g a b v v' : ComplexMatrix2) :
    bracketTerm g a b (v + v') = bracketTerm g a b v + bracketTerm g a b v' := by
  simp only [bracketTerm, Ring.lie_def, mul_add, add_mul, ← smul_add]
  congr 1
  abel
private theorem bracketTerm_smul_right (r : ℝ) (g a b v : ComplexMatrix2) :
    bracketTerm g a b (r • v) = r • bracketTerm g a b v := by
  simp only [bracketTerm, Ring.lie_def, mul_smul_comm, smul_mul_assoc, ← smul_sub]
  rw [smul_comm]
private theorem chainBracket_fst (X : ChainPoint L n k) (l : Vertex L n k 0 → ComplexMatrix2)
    (v : LevelValues L n k) : (chainBracket X l v).1 =
      extendOddly fun b => bracketTerm (X.fine b) (l b.source) (l b.target) (v.1 b) := rfl
private theorem chainBracket_snd (X : ChainPoint L n k) (l : Vertex L n k 0 → ComplexMatrix2)
    (v : LevelValues L n k) (i : Fin k) : (chainBracket X l v).2 i =
      extendOddly fun c => (open Classical in
          if hc : c.IsPositivelyOriented then
            bracketTerm (X.noise i ⟨c, hc⟩) (restrictVertexFunction (i + 1) l c.source)
              (restrictVertexFunction (i + 1) l c.source) (v.2 i c)
          else 0) := rfl
private theorem restrictVertexFunction_add {j : ℕ} (i : ℕ) (l l' : Vertex L n k j → ComplexMatrix2) :
    restrictVertexFunction i (l + l') = restrictVertexFunction i l + restrictVertexFunction i l' := rfl
private theorem restrictVertexFunction_smul {j : ℕ} (i : ℕ) (r : ℝ) (l : Vertex L n k j → ComplexMatrix2) :
    restrictVertexFunction i (r • l) = r • restrictVertexFunction i l := rfl
private theorem chainBracket_add_left (X : ChainPoint L n k) (l l' : Vertex L n k 0 → ComplexMatrix2)
    (v : LevelValues L n k) :
    chainBracket X (l + l') v = chainBracket X l v + chainBracket X l' v := by
  classical
  apply Prod.ext
  · rw [Prod.fst_add, chainBracket_fst, chainBracket_fst, chainBracket_fst]
    exact extendOddly_add fun c => bracketTerm_add_left (X.fine c) (l c.source) (l' c.source) (l c.target)
      (l' c.target) (v.1 c)
  · funext i
    rw [Prod.snd_add, Pi.add_apply, chainBracket_snd, chainBracket_snd, chainBracket_snd]
    refine extendOddly_add fun c => ?_
    by_cases hc : c.IsPositivelyOriented
    · simp only [dif_pos hc, restrictVertexFunction_add]
      exact bracketTerm_add_left _ (restrictVertexFunction (i + 1) l c.source)
        (restrictVertexFunction (i + 1) l' c.source) (restrictVertexFunction (i + 1) l c.source)
        (restrictVertexFunction (i + 1) l' c.source) _
    · simp [dif_neg hc]
private theorem chainBracket_smul_left (X : ChainPoint L n k) (r : ℝ) (l : Vertex L n k 0 → ComplexMatrix2)
    (v : LevelValues L n k) : chainBracket X (r • l) v = r • chainBracket X l v := by
  classical
  apply Prod.ext
  · rw [Prod.smul_fst, chainBracket_fst, chainBracket_fst]
    exact extendOddly_smul r fun c => bracketTerm_smul_left r (X.fine c) (l c.source) (l c.target) (v.1 c)
  · funext i
    rw [Prod.smul_snd, Pi.smul_apply, chainBracket_snd, chainBracket_snd]
    refine extendOddly_smul r fun c => ?_
    by_cases hc : c.IsPositivelyOriented
    · simp only [dif_pos hc, restrictVertexFunction_smul]
      exact bracketTerm_smul_left r _ (restrictVertexFunction (i + 1) l c.source)
        (restrictVertexFunction (i + 1) l c.source) _
    · simp [dif_neg hc]
private theorem chainBracket_add_right (X : ChainPoint L n k) (l : Vertex L n k 0 → ComplexMatrix2)
    (v v' : LevelValues L n k) :
    chainBracket X l (v + v') = chainBracket X l v + chainBracket X l v' := by
  classical
  apply Prod.ext
  · rw [Prod.fst_add, chainBracket_fst, chainBracket_fst, chainBracket_fst]
    exact extendOddly_add fun c => bracketTerm_add_right (X.fine c) (l c.source) (l c.target) (v.1 c)
      (v'.1 c)
  · funext i
    rw [Prod.snd_add, Pi.add_apply, chainBracket_snd, chainBracket_snd, chainBracket_snd]
    refine extendOddly_add fun c => ?_
    by_cases hc : c.IsPositivelyOriented
    · simp only [dif_pos hc]
      exact bracketTerm_add_right _ _ _ (v.2 i c) (v'.2 i c)
    · simp [dif_neg hc]
private theorem chainBracket_smul_right (X : ChainPoint L n k) (r : ℝ) (l : Vertex L n k 0 → ComplexMatrix2)
    (v : LevelValues L n k) : chainBracket X l (r • v) = r • chainBracket X l v := by
  classical
  apply Prod.ext
  · rw [Prod.smul_fst, chainBracket_fst, chainBracket_fst]
    exact extendOddly_smul r fun c => bracketTerm_smul_right r (X.fine c) (l c.source) (l c.target) (v.1 c)
  · funext i
    rw [Prod.smul_snd, Pi.smul_apply, chainBracket_snd, chainBracket_snd]
    refine extendOddly_smul r fun c => ?_
    by_cases hc : c.IsPositivelyOriented
    · simp only [dif_pos hc]
      exact bracketTerm_smul_right r _ _ _ (v.2 i c)
    · simp [dif_neg hc]
private theorem halfTrace_add (A B : ComplexMatrix2) : ComplexMatrix2.halfTrace (A + B) =
    ComplexMatrix2.halfTrace A + ComplexMatrix2.halfTrace B := by
  simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_add, mul_add]
private theorem halfTrace_real_smul_re (r : ℝ) (A : ComplexMatrix2) : (ComplexMatrix2.halfTrace (r • A)).re =
    r * (ComplexMatrix2.halfTrace A).re := by
  have h : ComplexMatrix2.halfTrace (r • A) = (r : ℂ) * ComplexMatrix2.halfTrace A := by
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_smul, Complex.real_smul]
    ring
  rw [h, Complex.re_ofReal_mul]
private def rePairingLinear {ι : Type} [Finite ι] (f : ι → ComplexMatrix2) : (ι → ComplexMatrix2) →ₗ[ℝ] ℝ where
  toFun g := (traceFinsumPairing f g).re
  map_add' g g' := by
    have := Fintype.ofFinite ι
    simp only [traceFinsumPairing, finsum_eq_sum_of_fintype, Pi.add_apply, mul_add, halfTrace_add,
      Complex.re_sum, Complex.add_re, Finset.sum_add_distrib]
  map_smul' r g := by
    have := Fintype.ofFinite ι
    simp only [traceFinsumPairing, finsum_eq_sum_of_fintype, Pi.smul_apply, RingHom.id_apply, smul_eq_mul,
      Complex.re_sum, Finset.mul_sum, mul_smul_comm, halfTrace_real_smul_re]
private def levelPairingLinear (F : ∀ j, Finite (PositiveEdge L n k j)) (u : LevelValues L n k) :
    LevelValues L n k →ₗ[ℝ] ℝ where
  toFun v := levelPairing u v
  map_add' v v' := by
    have h₀ := (@rePairingLinear _ (F 0) (restrictToPositiveEdges u.1)).map_add (restrictToPositiveEdges v.1)
      (restrictToPositiveEdges v'.1)
    have h₁ : ∀ i : Fin k, _ := fun i : Fin k => (@rePairingLinear _ (F (i + 1))
      (restrictToPositiveEdges (u.2 i))).map_add (restrictToPositiveEdges (v.2 i))
        (restrictToPositiveEdges (v'.2 i))
    show (edgeFormPairing u.1 (v.1 + v'.1)).re + ∑ i, (edgeFormPairing (u.2 i) (v.2 i + v'.2 i)).re =
      ((edgeFormPairing u.1 v.1).re + ∑ i, (edgeFormPairing (u.2 i) (v.2 i)).re) +
        ((edgeFormPairing u.1 v'.1).re + ∑ i, (edgeFormPairing (u.2 i) (v'.2 i)).re)
    have e₀ : (edgeFormPairing u.1 (v.1 + v'.1)).re = (edgeFormPairing u.1 v.1).re +
        (edgeFormPairing u.1 v'.1).re := h₀
    have e₁ : ∀ i : Fin k, (edgeFormPairing (u.2 i) (v.2 i + v'.2 i)).re =
        (edgeFormPairing (u.2 i) (v.2 i)).re + (edgeFormPairing (u.2 i) (v'.2 i)).re := h₁
    rw [e₀, Finset.sum_congr rfl fun i _ => e₁ i, Finset.sum_add_distrib]
    ring
  map_smul' r v := by
    have h₀ := (@rePairingLinear _ (F 0) (restrictToPositiveEdges u.1)).map_smul r (restrictToPositiveEdges v.1)
    have h₁ : ∀ i : Fin k, _ := fun i : Fin k => (@rePairingLinear _ (F (i + 1))
      (restrictToPositiveEdges (u.2 i))).map_smul r (restrictToPositiveEdges (v.2 i))
    show (edgeFormPairing u.1 (r • v.1)).re + ∑ i, (edgeFormPairing (u.2 i) (r • v.2 i)).re =
      r • ((edgeFormPairing u.1 v.1).re + ∑ i, (edgeFormPairing (u.2 i) (v.2 i)).re)
    have e₀ : (edgeFormPairing u.1 (r • v.1)).re = r * (edgeFormPairing u.1 v.1).re := h₀
    have e₁ : ∀ i : Fin k, (edgeFormPairing (u.2 i) (r • v.2 i)).re =
        r * (edgeFormPairing (u.2 i) (v.2 i)).re := h₁
    rw [e₀, Finset.sum_congr rfl fun i _ => e₁ i, ← Finset.mul_sum, smul_eq_mul]
    ring
private def bracketBilin (F : ∀ j, Finite (PositiveEdge L n k j)) (X : ChainPoint L n k)
    (u : LevelValues L n k) : (Vertex L n k 0 → ComplexMatrix2) →ₗ[ℝ] LevelValues L n k →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun l v => levelPairingLinear F u (chainBracket X l v))
    (fun l l' v => by rw [chainBracket_add_left, map_add])
    (fun r l v => by rw [chainBracket_smul_left, map_smul])
    (fun l v v' => by rw [chainBracket_add_right, map_add])
    (fun r l v => by rw [chainBracket_smul_right, map_smul])
private def formValuesLinear (L n k : ℕ) : LevelForms L n k →ₗ[ℝ] LevelValues L n k where
  toFun := formValues
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private theorem formValuesLinear_injective : Function.Injective (formValuesLinear L n k) := by
  intro ξ ξ' h
  have h₁ : (ξ.1 : Edge L n k 0 → ComplexMatrix2) = ξ'.1 := congrArg Prod.fst h
  have h₂ : ∀ i : Fin k, (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) = ξ'.2 i := fun i =>
    congrFun (congrArg Prod.snd h) i
  exact Prod.ext (Subtype.ext h₁) (funext fun i => Subtype.ext (h₂ i))
private theorem isQuadraticFn_gaugeSliceResidual_sq (c : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0))
    (hc : IsVertexPairingCore c) (U : Edge L n k 0 → ComplexMatrix2) :
    IsQuadraticFn fun ξ : LevelForms L n k =>
      traceFinsumNorm (gaugeSliceResidual U ξ.1 : Vertex L n k 0 → ComplexMatrix2) ^ 2 := by
  let _ := c.toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore c.toCore
  set G : LevelForms L n k →ₗ[ℝ] vertexFunctionSpace L n k 0 :=
    (covDiffRealTranspose L n k U -
      ((L : ℝ) ^ (4 * k)) • (iterAverageRealTranspose L n k U ∘ₗ
        iterAverageLinear L n k U ∘ₗ covDiffRealTranspose L n k U)) ∘ₗ
      LinearMap.fst ℝ _ _ with hG
  refine ⟨normSqForm G, fun ξ => ?_⟩
  have h₁ : G ξ = gaugeSliceResidual U ξ.1 := rfl
  have h₂ : normSqForm G ξ = c.inner (G ξ) (G ξ) := rfl
  have h₃ := hc (G ξ) (G ξ)
  have h₄ : 0 ≤ c.inner (G ξ) (G ξ) := by
    simp
  have h₅ : traceFinsumNorm (gaugeSliceResidual U ξ.1 : Vertex L n k 0 → ComplexMatrix2) ^ 2 =
      (traceFinsumPairing (G ξ : Vertex L n k 0 → ComplexMatrix2) (G ξ : Vertex L n k 0 → ComplexMatrix2)).re :=
    Real.sq_sqrt (by rw [← h₁, ← h₃]; exact h₄)
  show normSqForm G ξ = traceFinsumNorm (gaugeSliceResidual U ξ.1 : Vertex L n k 0 → ComplexMatrix2) ^ 2
  rw [h₅, h₂, h₃]
end Linear
section Analysis
variable {L n k : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p₀ : E}
private theorem analyticAt_fullTrace {f : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀) :
    AnalyticAt ℝ (fun p => ComplexMatrix2.fullTrace (f p)) p₀ :=
  (LinearMap.toContinuousLinearMap
    ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).restrictScalars ℝ)).analyticAt _ |>.comp hf
private theorem analyticAt_plaquetteAction (F : TowerFacts L n k) {U : E → Edge L n k 0 → ComplexMatrix2}
    (hU : ∀ b, AnalyticAt ℝ (fun p => U p b) p₀) :
    AnalyticAt ℝ (fun p => plaquetteAction L n k (U p)) p₀ := by
  have := F.vertices_finite 0
  have := Fintype.ofFinite (Face L n k 0)
  have e : (fun p => plaquetteAction L n k (U p)) =
      fun p => ∑ P : Face L n k 0, PeriodicLattice.plaquetteCost (U p) P := by
    funext p
    exact finsum_eq_sum_of_fintype _
  rw [e]
  refine Finset.analyticAt_fun_sum _ fun P _ => ?_
  exact analyticAt_const.sub (analyticAt_const.mul (analyticAt_re (analyticAt_fullTrace (analyticAt_pathHolonomy hU _))))
private theorem analyticAt_chainAction (F : TowerFacts L n k) {X : E → ChainPoint L n k}
    (hX : IsAnalyticFamilyThroughUnit X p₀)
    (hl : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      AnalyticAt ℝ (fun p => meanRadius (levelField (X p) i) c.1) p₀) (a : ℝ) :
    AnalyticAt ℝ (fun p => chainAction a (X p)) p₀ := by
  have h₂ : AnalyticAt ℝ (fun p => ∑ i : Fin k, ∑ᶠ c : PositiveEdge L n k (i + 1),
      (meanRadius (levelField (X p) i) c.1).re * traceDefect ((X p).noise i c)) p₀ := by
    refine Finset.analyticAt_fun_sum _ fun i _ => ?_
    have := F.positive_finite (i + 1)
    have := Fintype.ofFinite (PositiveEdge L n k (i + 1))
    have e : (fun p => ∑ᶠ c : PositiveEdge L n k (i + 1),
        (meanRadius (levelField (X p) i) c.1).re * traceDefect ((X p).noise i c)) =
        fun p => ∑ c : PositiveEdge L n k (i + 1),
          (meanRadius (levelField (X p) i) c.1).re * traceDefect ((X p).noise i c) := by
      funext p
      exact finsum_eq_sum_of_fintype _
    rw [e]
    refine Finset.analyticAt_fun_sum _ fun c _ => (analyticAt_re (hl i c)).mul ?_
    exact analyticAt_const.sub (analyticAt_re (analyticAt_halfTrace (hX.analyticAt_noise i c)))
  exact (analyticAt_plaquetteAction F hX.analyticAt_fine).add (analyticAt_const.mul h₂)
private theorem isAnalyticFamily_const_unitPoint (_F : TowerFacts L n k) (p₀ : E) :
    IsAnalyticFamilyThroughUnit (fun _ : E => unitPoint L n k) p₀ := by
  refine ⟨rfl, fun _ => analyticAt_const, fun _ _ => analyticAt_const, ?_⟩
  refine Eventually.of_forall fun _ => ⟨⟨fun b _ => ?_, fun b _ => ?_⟩, fun _ _ => ?_⟩
  · exact Submonoid.one_mem _
  · simp [unitPoint]
  · exact Submonoid.one_mem _
private theorem isAnalyticFamily_expMove_linear (F : TowerFacts L n k) [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] LevelForms L n k) {X : E → ChainPoint L n k}
    (hX : IsAnalyticFamilyThroughUnit X 0) :
    IsAnalyticFamilyThroughUnit (fun p => expMove (A p) (X p)) 0 := by
  refine isAnalyticFamily_expMove F hX (map_zero A) (fun b => ?_) fun i c => ?_
  · let T : LevelForms L n k →ₗ[ℝ] ComplexMatrix2 :=
      { toFun := fun ξ => (ξ.1 : Edge L n k 0 → ComplexMatrix2) b
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap (T ∘ₗ A)).analyticAt _
  · let T : LevelForms L n k →ₗ[ℝ] ComplexMatrix2 :=
      { toFun := fun ξ => (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap (T ∘ₗ A)).analyticAt _
private theorem analyticAt_extendByZero {l : E → Vertex L n k k → ComplexMatrix2}
    (hl : ∀ y, AnalyticAt ℝ (fun p => l p y) p₀) (x : Vertex L n k 0) :
    AnalyticAt ℝ (fun p => extendByZero (l p) x) p₀ := by
  classical
  by_cases h : ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = x
  · refine (hl h.choose).congr (Eventually.of_forall fun p => ?_)
    simp [extendByZero, h]
  · refine analyticAt_const (v := (0 : ComplexMatrix2)) |>.congr (Eventually.of_forall fun p => ?_)
    simp [extendByZero, h]
end Analysis
section Forms
variable {L n k : ℕ}
variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
private abbrev BoundedBilin (Z Y : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] : Type := Z →L[ℝ] Z →L[ℝ] Y
private theorem exists_bilin_leftSecondDeriv (a : ℝ) (g : Z →ₗ[ℝ] LevelForms L n k)
    (ι : LevelForms L n k →ₗ[ℝ] Z) (hι : ∀ ξ, g (ι ξ) = ξ) {X : Z → ChainPoint L n k}
    (hA : AnalyticAt ℝ (fun q : Z × Z => chainAction a (expMove (g q.2) (X q.1))) (0, 0)) :
    ∃ B : Z → Z →L[ℝ] Z →L[ℝ] ℝ, AnalyticAt ℝ B 0 ∧ ∀ᶠ w in 𝓝 (0 : Z), ∀ ξ ξ',
      leftSecondDeriv (chainAction a) (X w) ξ ξ' = B w (ι ξ) (ι ξ') := by
  obtain ⟨B, hB, ev⟩ := exists_analytic_mixedDeriv hA
  refine ⟨B, hB, ?_⟩
  filter_upwards [ev] with w hw ξ ξ'
  rw [← hw]
  have e : ∀ s t : ℝ, g (s • ι ξ + t • ι ξ') = s • ξ + t • ξ' := fun s t => by
    simp only [map_add, map_smul, hι]
  simp only [leftSecondDeriv, e]
private theorem exists_bilin_topSecondVariation (g : Z →ₗ[ℝ] LevelForms L n k)
    (ι : LevelForms L n k →ₗ[ℝ] Z) (hι : ∀ ξ, g (ι ξ) = ξ) {X : Z → ChainPoint L n k}
    (c : PositiveEdge L n k k) (hlog : AnalyticAt ℝ ComplexMatrix2.logSeries 1)
    (h₁ : AnalyticAt ℝ (fun q : Z × Z => levelField (expMove (g q.2) (X q.1)) k c.1) (0, 0))
    (h₂ : AnalyticAt ℝ (fun q : Z × Z => levelField (X q.1) k c.1) (0, 0))
    (v₁ : levelField (expMove (g 0) (X 0)) k c.1 = 1) (v₂ : levelField (X 0) k c.1 = 1) :
    ∃ B : Z → BoundedBilin Z ComplexMatrix2, AnalyticAt ℝ B 0 ∧ ∀ᶠ w in 𝓝 (0 : Z), ∀ ξ ξ',
      topSecondVariation (X w) ξ ξ' c = B w (ι ξ) (ι ξ') := by
  have h₃ : AnalyticAt ℝ (fun q : Z × Z => levelField (expMove (g q.2) (X q.1)) k c.1 *
      (levelField (X q.1) k c.1)⁻¹) (0, 0) :=
    h₁.mul (analyticAt_matInv h₂ (by simp [v₂]))
  have h₀ : levelField (expMove (g ((0, 0) : Z × Z).2) (X ((0, 0) : Z × Z).1)) k c.1 *
      (levelField (X ((0, 0) : Z × Z).1) k c.1)⁻¹ = 1 := by
    show levelField (expMove (g 0) (X 0)) k c.1 * (levelField (X 0) k c.1)⁻¹ = 1
    rw [v₁, v₂]
    simp
  have h₄ : AnalyticAt ℝ (fun q : Z × Z => Complex.I⁻¹ • ComplexMatrix2.logSeries
      (levelField (expMove (g q.2) (X q.1)) k c.1 * (levelField (X q.1) k c.1)⁻¹)) (0, 0) :=
    analyticAt_complexSmul _ (AnalyticAt.comp (g := ComplexMatrix2.logSeries) (by simp only [h₀]; exact hlog) h₃)
  obtain ⟨B, hB, ev⟩ := exists_analytic_mixedDeriv h₄
  refine ⟨B, hB, ?_⟩
  filter_upwards [ev] with w hw ξ ξ'
  rw [← hw]
  have e : ∀ s t : ℝ, g (s • ι ξ + t • ι ξ') = s • ξ + t • ξ' := fun s t => by
    simp only [map_add, map_smul, hι]
  simp only [topSecondVariation, topLog, e]
private theorem analyticAt_coords [FiniteDimensional ℝ Z] (F : TowerFacts L n k)
    (ι : LevelForms L n k →ₗ[ℝ] Z) {f : Z → LevelForms L n k} {v : Z → LevelValues L n k}
    (hv : AnalyticValues v 0) (ev : ∀ᶠ w in 𝓝 (0 : Z), formValues (f w) = v w) :
    AnalyticAt ℝ (fun w => ι (f w)) 0 := by
  classical
  let _ : ∀ j, Fintype (Edge L n k j) := fun j => @Fintype.ofFinite _ (F.edges_finite j)
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (formValuesLinear L n k)
    (LinearMap.ker_eq_bot.2 formValuesLinear_injective)
  have hva : AnalyticAt ℝ v 0 := by
    have h₁ : AnalyticAt ℝ (fun w => (v w).1) 0 := analyticAt_pi_iff.2 hv.1
    have h₂ : AnalyticAt ℝ (fun w => (v w).2) 0 :=
      analyticAt_pi_iff.2 fun i => analyticAt_pi_iff.2 (hv.2 i)
    exact h₁.prod h₂
  have h₃ : AnalyticAt ℝ (fun w => (ι ∘ₗ r) (v w)) 0 :=
    ((LinearMap.toContinuousLinearMap (ι ∘ₗ r)).analyticAt _).comp hva
  refine h₃.congr (ev.mono fun w h => ?_)
  have h₄ : r (formValuesLinear L n k (f w)) = f w := LinearMap.congr_fun hr (f w)
  have h₅ : formValuesLinear L n k (f w) = v w := h
  show ι (r (v w)) = ι (f w)
  rw [← h₅, h₄]
private theorem analyticValues_formValues_linear [FiniteDimensional ℝ Z] (A : Z →ₗ[ℝ] LevelForms L n k) :
    AnalyticValues (fun w => formValues (A w)) (0 : Z) := by
  refine ⟨fun b => ?_, fun i b => ?_⟩
  · let T : LevelForms L n k →ₗ[ℝ] ComplexMatrix2 :=
      { toFun := fun ξ => (ξ.1 : Edge L n k 0 → ComplexMatrix2) b
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap (T ∘ₗ A)).analyticAt _
  · let T : LevelForms L n k →ₗ[ℝ] ComplexMatrix2 :=
      { toFun := fun ξ => (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) b
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap (T ∘ₗ A)).analyticAt _
private def pullbackBilin {V : Type} [AddCommGroup V] [Module ℝ V] (B : Z →L[ℝ] Z →L[ℝ] ℝ)
    (ι : V →ₗ[ℝ] Z) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun ξ ξ' => B (ι ξ) (ι ξ'))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
private def pairedPullbackBilin {V : Type} [AddCommGroup V] [Module ℝ V] {σ : Type} [Finite σ]
    (f : σ → ComplexMatrix2) (B : σ → BoundedBilin Z ComplexMatrix2) (ι : V →ₗ[ℝ] Z) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun ξ ξ' => rePairingLinear f fun c => B c (ι ξ) (ι ξ'))
    (fun x y z => by
      rw [← map_add]
      congr 1
      funext c
      simp)
    (fun r x z => by
      rw [smul_eq_mul, ← smul_eq_mul, ← map_smul]
      congr 1
      funext c
      simp)
    (fun x y z => by
      rw [← map_add]
      congr 1
      funext c
      simp)
    (fun r x z => by
      rw [smul_eq_mul, ← smul_eq_mul, ← map_smul]
      congr 1
      funext c
      simp)
end Forms
section Main
variable {L n k : ℕ}
variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
private theorem analyticAt_clm_apply [FiniteDimensional ℝ Z] {E Y : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {p₀ : E} {T : E → Z →L[ℝ] Y}
    {x : E → Z} (hT : AnalyticAt ℝ T p₀) (hx : AnalyticAt ℝ x p₀) :
    AnalyticAt ℝ (fun p => T p (x p)) p₀ := by
  let b := Module.finBasis ℝ Z
  have e : (fun p => T p (x p)) = fun p => ∑ i, b.repr (x p) i • T p (b i) := by
    funext p
    have h := congrArg (T p) (b.sum_repr (x p))
    rw [map_sum] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [e]
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  have h₁ : AnalyticAt ℝ (fun p => b.repr (x p) i) p₀ :=
    ((LinearMap.toContinuousLinearMap (b.coord i)).analyticAt _).comp hx
  have h₂ : AnalyticAt ℝ (fun p => T p (b i)) p₀ :=
    ((ContinuousLinearMap.apply ℝ Y (b i)).analyticAt _).comp hT
  exact h₁.smul h₂
private theorem exists_quadraticForm_gaugedRightValue (a : ℝ) (P : ∀ j, Finite (PositiveEdge L n k j))
    (ι : LevelForms L n k →ₗ[ℝ] Z) (X : ChainPoint L n k) (J : LevelForms L n k)
    (μ : edgeFormSpace L n k k) (c₀ : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0))
    (hc₀ : IsVertexPairingCore c₀) (B₁ : BoundedBilin Z ℝ) (Bc : PositiveEdge L n k k → BoundedBilin Z ComplexMatrix2)
    (h₁ : ∀ ξ ξ', leftSecondDeriv (chainAction a) X ξ ξ' = B₁ (ι ξ) (ι ξ'))
    (h₄ : ∀ (c : PositiveEdge L n k k) ξ ξ', topSecondVariation X ξ ξ' c = Bc c (ι ξ) (ι ξ'))
    (hτ : IsGaugeTransform X (gaugeTransform X)) (S : LevelForms L n k →ₗ[ℝ] vertexFunctionSpace L n k 0)
    (hS : ∀ ξ, (S ξ : Vertex L n k 0 → ComplexMatrix2) = gaugeCorrection X ξ) :
    ∃ q : QuadraticForm ℝ (LevelForms L n k), ∀ ξ, q ξ = gaugedRightValue a X J μ ξ := by
  have := P k
  have Q₁ : IsQuadraticFn fun ξ => leftSecondDeriv (chainAction a) X ξ ξ :=
    isQuadraticFn_of_bilin (pullbackBilin B₁ ι) fun ξ => h₁ ξ ξ
  let Sc : LevelForms L n k →ₗ[ℝ] (Vertex L n k 0 → ComplexMatrix2) := (vertexFunctionSpace L n k 0).subtype ∘ₗ S
  have hSc : ∀ ξ, gaugeCorrection X ξ = Sc ξ := fun ξ => (hS ξ).symm
  have Q₂ : IsQuadraticFn fun ξ => 2 * levelPairing (formValues J)
      (chainBracket X (gaugeCorrection X ξ) (formValues ξ)) :=
    isQuadraticFn_of_bilin ((2 : ℝ) • (bracketBilin P X (formValues J)).compl₁₂ Sc (formValuesLinear L n k))
      fun ξ => by
        rw [hSc]
        rfl
  have Q₃ : IsQuadraticFn fun ξ => levelPairing (formValues J)
      (chainBracket X (gaugeCorrection X ξ) (gaugeOrbitValues X (gaugeCorrection X ξ))) :=
    isQuadraticFn_of_bilin ((bracketBilin P X (formValues J)).compl₁₂ Sc
        (formValuesLinear L n k ∘ₗ gaugeTransform X - formValuesLinear L n k))
      fun ξ => by
        have h' : gaugeOrbitValues X (Sc ξ) =
            (formValuesLinear L n k ∘ₗ gaugeTransform X - formValuesLinear L n k) ξ := by
          have h₅ := hτ ξ
          rw [hSc] at h₅
          show _ = formValues (gaugeTransform X ξ) - formValues ξ
          rw [h₅]
          abel
        rw [hSc, h']
        rfl
  have Q₄ : IsQuadraticFn fun ξ => (traceFinsumPairing (restrictToPositiveEdges (μ : Edge L n k k → ComplexMatrix2))
      (topSecondVariation X (gaugeTransform X ξ) (gaugeTransform X ξ))).re :=
    isQuadraticFn_of_bilin (pairedPullbackBilin (restrictToPositiveEdges (μ : Edge L n k k → ComplexMatrix2)) Bc
        (ι ∘ₗ gaugeTransform X))
      fun ξ => by
        have h : topSecondVariation X (gaugeTransform X ξ) (gaugeTransform X ξ) =
            fun c => Bc c (ι (gaugeTransform X ξ)) (ι (gaugeTransform X ξ)) :=
          funext fun c => h₄ c _ _
        rw [h]
        rfl
  have Q₅ := isQuadraticFn_gaugeSliceResidual_sq (L := L) (n := n) (k := k) c₀ hc₀ X.fine
  exact (((Q₁.add Q₂).add Q₃).sub Q₄).add Q₅
private theorem analyticAt_gaugedRightValue [FiniteDimensional ℝ Z] (a : ℝ) (F : TowerFacts L n k)
    (ι : LevelForms L n k →ₗ[ℝ] Z) {X : Z → ChainPoint L n k} (hX : IsAnalyticFamilyThroughUnit X 0)
    {J : Z → LevelForms L n k} (hJ : AnalyticValues (fun w => formValues (J w)) 0)
    {M : Z → edgeFormSpace L n k k}
    (hμ : ∀ b, AnalyticAt ℝ (fun w => (M w : Edge L n k k → ComplexMatrix2) b) 0)
    (c₀ : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0)) (hc₀ : IsVertexPairingCore c₀)
    {B₁ : Z → BoundedBilin Z ℝ} (hB₁ : AnalyticAt ℝ B₁ 0)
    {Bc : PositiveEdge L n k k → Z → BoundedBilin Z ComplexMatrix2}
    (hBc : ∀ c, AnalyticAt ℝ (Bc c) 0)
    (S₁ : ∀ᶠ w in 𝓝 (0 : Z), ∀ ξ ξ',
      leftSecondDeriv (chainAction a) (X w) ξ ξ' = B₁ w (ι ξ) (ι ξ'))
    (S₄ : ∀ᶠ w in 𝓝 (0 : Z), ∀ (c : PositiveEdge L n k k) ξ ξ',
      topSecondVariation (X w) ξ ξ' c = Bc c w (ι ξ) (ι ξ'))
    (hτ : ∀ᶠ w in 𝓝 (0 : Z), IsGaugeTransform (X w) (gaugeTransform (X w)))
    (ξ : LevelForms L n k)
    (hσ : ∀ x, AnalyticAt ℝ (fun w => gaugeCorrection (X w) ξ x) 0)
    (bT : ∀ (B : edgeFormSpace L n k 0) (x : Vertex L n k 0), AnalyticAt ℝ
        (fun w => (gaugeSliceResidual (X w).fine B : Vertex L n k 0 → ComplexMatrix2) x) 0) :
    AnalyticAt ℝ (fun w => gaugedRightValue a (X w) (J w) (M w) ξ) 0 := by
  have hPk := F.positive_finite k
  have hξv : AnalyticValues (fun _ : Z => formValues ξ) 0 :=
    ⟨fun _ => analyticAt_const, fun _ _ => analyticAt_const⟩
  have t₁ : AnalyticAt ℝ (fun w => leftSecondDeriv (chainAction a) (X w) ξ ξ) 0 :=
    (analyticAt_clm_apply (analyticAt_clm_apply hB₁ analyticAt_const) analyticAt_const).congr
      (S₁.mono fun w h => (h ξ ξ).symm)
  have t₂ : AnalyticAt ℝ (fun w => 2 * levelPairing (formValues (J w))
      (chainBracket (X w) (gaugeCorrection (X w) ξ) (formValues ξ))) 0 :=
    analyticAt_const.mul (analyticAt_levelPairing F hJ (analyticValues_chainBracket F hX hσ hξv))
  have t₃ : AnalyticAt ℝ (fun w => levelPairing (formValues (J w))
      (chainBracket (X w) (gaugeCorrection (X w) ξ) (gaugeOrbitValues (X w) (gaugeCorrection (X w) ξ)))) 0 :=
    analyticAt_levelPairing F hJ (analyticValues_chainBracket F hX hσ (analyticValues_gaugeOrbitValues F hX hσ))
  have hτa : AnalyticAt ℝ (fun w => ι (gaugeTransform (X w) ξ)) 0 := by
    have hv : AnalyticValues (fun w => formValues ξ + gaugeOrbitValues (X w) (gaugeCorrection (X w) ξ)) (0 : Z) := by
      have ho := analyticValues_gaugeOrbitValues F hX hσ
      exact ⟨fun b => analyticAt_const.add (ho.1 b),
        fun i b => analyticAt_const.add (ho.2 i b)⟩
    exact analyticAt_coords F ι hv (hτ.mono fun w h => h ξ)
  have t₄ : AnalyticAt ℝ (fun w => (traceFinsumPairing (restrictToPositiveEdges (M w : Edge L n k k → ComplexMatrix2))
      (topSecondVariation (X w) (gaugeTransform (X w) ξ) (gaugeTransform (X w) ξ))).re) 0 := by
    have h : AnalyticAt ℝ (fun w => (traceFinsumPairing (restrictToPositiveEdges (M w : Edge L n k k → ComplexMatrix2))
        (fun c => Bc c w (ι (gaugeTransform (X w) ξ)) (ι (gaugeTransform (X w) ξ)))).re) 0 :=
      analyticAt_re (analyticAt_traceFinsumPairing
        (f := fun w => restrictToPositiveEdges (M w : Edge L n k k → ComplexMatrix2))
        (fun c => hμ c.1) fun c => analyticAt_clm_apply (analyticAt_clm_apply (hBc c) hτa) hτa)
    refine h.congr (S₄.mono fun w hw => ?_)
    have h' : topSecondVariation (X w) (gaugeTransform (X w) ξ) (gaugeTransform (X w) ξ) =
        fun c => Bc c w (ι (gaugeTransform (X w) ξ)) (ι (gaugeTransform (X w) ξ)) :=
      funext fun c => hw c _ _
    simp only [h']
  have t₅ : AnalyticAt ℝ (fun w => traceFinsumNorm
      (gaugeSliceResidual (X w).fine ξ.1 : Vertex L n k 0 → ComplexMatrix2) ^ 2) 0 := by
    have := F.vertices_finite 0
    have h : AnalyticAt ℝ (fun w =>
        (traceFinsumPairing (gaugeSliceResidual (X w).fine ξ.1 : Vertex L n k 0 → ComplexMatrix2)
          (gaugeSliceResidual (X w).fine ξ.1 : Vertex L n k 0 → ComplexMatrix2)).re) 0 :=
      analyticAt_re (analyticAt_traceFinsumPairing (bT ξ.1) (bT ξ.1))
    refine h.congr (Eventually.of_forall fun w => ?_)
    have h₃ := hc₀ (gaugeSliceResidual (X w).fine ξ.1) (gaugeSliceResidual (X w).fine ξ.1)
    have h₄ : 0 ≤ c₀.inner (gaugeSliceResidual (X w).fine ξ.1)
        (gaugeSliceResidual (X w).fine ξ.1) := by
      simpa using c₀.re_inner_nonneg (gaugeSliceResidual (X w).fine ξ.1)
    have h₅ : 0 ≤ (traceFinsumPairing (gaugeSliceResidual (X w).fine ξ.1 : Vertex L n k 0 → ComplexMatrix2)
        (gaugeSliceResidual (X w).fine ξ.1 : Vertex L n k 0 → ComplexMatrix2)).re := by
      rw [← h₃]
      exact h₄
    exact (Real.sq_sqrt h₅).symm
  exact (((t₁.add t₂).add t₃).sub t₄).add t₅
private theorem analyticAt_logRadiusSum (F : TowerFacts L n k) {X : Z → ChainPoint L n k}
    (fL : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      AnalyticAt ℝ (fun p => meanRadius (levelField (X p) i) c.1) 0 ∧
        meanRadius (levelField (X 0) i) c.1 = 1) :
    AnalyticAt ℝ (fun w => logRadiusSum (X w)) 0 := by
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  have := F.positive_finite (i + 1)
  have := Fintype.ofFinite (PositiveEdge L n k (i + 1))
  have e' : (fun w => ∑ᶠ c : PositiveEdge L n k (i + 1),
      Real.log (meanRadius (levelField (X w) i) c.1).re) =
      fun w => ∑ c : PositiveEdge L n k (i + 1),
        Real.log (meanRadius (levelField (X w) i) c.1).re := by
    funext w
    exact finsum_eq_sum_of_fintype _
  refine AnalyticAt.congr ?_ (Eventually.of_forall fun w => (congrFun e' w).symm)
  refine Finset.analyticAt_fun_sum _ fun c _ => ?_
  refine AnalyticAt.comp (g := Real.log) ?_ (analyticAt_re (fL i c).1)
  rw [(fL i c).2]
  exact analyticAt_log (by simp)
private theorem analyticAt_shiftedGaugeMap_pairing (F : TowerFacts L n k) {X : Z → ChainPoint L n k}
    {ξ : LevelForms L n k} (C : edgeFormSpace L n k k)
    (fW : ∀ b : Edge L n k k, AnalyticAt ℝ (fun p => levelField (X p) k b) 0 ∧
      levelField (X 0) k b = 1)
    (mA : (∀ b : Edge L n k k, AnalyticAt ℝ (fun p => tangentTransport (X p) ξ k b) 0) ∧
      ∀ y : Vertex L n k k, AnalyticAt ℝ (fun p => chainDrift (X p) ξ k y) 0)
    (hO : ∀ᶠ w in 𝓝 (0 : Z), IsShiftedGaugeMap (X w) (shiftedGaugeMap (X w))) :
    AnalyticAt ℝ (fun w => (edgeFormPairing (C : Edge L n k k → ComplexMatrix2)
      (shiftedGaugeMap (X w) ξ : Edge L n k k → ComplexMatrix2)).re) 0 := by
  have h : AnalyticAt ℝ (fun w => (edgeFormPairing (C : Edge L n k k → ComplexMatrix2)
      (shiftedGaugeValues (X w) ξ)).re) 0 := by
    refine analyticAt_re (analyticAt_edgeFormPairing F (fun _ => analyticAt_const) fun b => ?_)
    refine (mA.1 b).add ?_
    refine analyticAt_covDiff F le_rfl (fun b => (fW b).1) mA.2 (fun b => ?_) b
    simp [(fW b).2]
  refine h.congr (hO.mono fun w hw => ?_)
  have h' : (shiftedGaugeMap (X w) ξ : Edge L n k k → ComplexMatrix2) = shiftedGaugeValues (X w) ξ := hw ξ
  simp only [h']
private theorem analyticAt_ghostBlockOperator_pairing (F : TowerFacts L n k) {X : Z → ChainPoint L n k}
    (x y : vertexFunctionSpace L n k 0 × vertexFunctionSpace L n k k)
    (h₁ : ∀ s : Vertex L n k 0, AnalyticAt ℝ
      (fun w => ((ghostBlockOperator (X w) y).1 : Vertex L n k 0 → ComplexMatrix2) s) 0)
    (h₂ : ∀ s : Vertex L n k k, AnalyticAt ℝ
      (fun w => ((ghostBlockOperator (X w) y).2 : Vertex L n k k → ComplexMatrix2) s) 0) :
    AnalyticAt ℝ (fun w => (traceFinsumPairing (x.1 : Vertex L n k 0 → ComplexMatrix2)
        ((ghostBlockOperator (X w) y).1 : Vertex L n k 0 → ComplexMatrix2)).re +
      (traceFinsumPairing (x.2 : Vertex L n k k → ComplexMatrix2)
        ((ghostBlockOperator (X w) y).2 : Vertex L n k k → ComplexMatrix2)).re) 0 := by
  have := F.vertices_finite 0
  have := F.vertices_finite k
  have a₁ : AnalyticAt ℝ (fun w => traceFinsumPairing (x.1 : Vertex L n k 0 → ComplexMatrix2)
      ((ghostBlockOperator (X w) y).1 : Vertex L n k 0 → ComplexMatrix2)) 0 :=
    analyticAt_traceFinsumPairing (f := fun _ => (x.1 : Vertex L n k 0 → ComplexMatrix2))
      (g := fun w => ((ghostBlockOperator (X w) y).1 : Vertex L n k 0 → ComplexMatrix2))
      (fun _ => analyticAt_const) h₁
  have a₂ : AnalyticAt ℝ (fun w => traceFinsumPairing (x.2 : Vertex L n k k → ComplexMatrix2)
      ((ghostBlockOperator (X w) y).2 : Vertex L n k k → ComplexMatrix2)) 0 :=
    analyticAt_traceFinsumPairing (f := fun _ => (x.2 : Vertex L n k k → ComplexMatrix2))
      (g := fun w => ((ghostBlockOperator (X w) y).2 : Vertex L n k k → ComplexMatrix2))
      (fun _ => analyticAt_const) h₂
  exact (analyticAt_re a₁).add (analyticAt_re a₂)
private theorem isAnalyticFamily_linearChart (F : TowerFacts L n k) [FiniteDimensional ℝ Z]
    (g : Z →ₗ[ℝ] LevelForms L n k) :
    IsAnalyticFamilyThroughUnit (fun w : Z => expMove (g w) (unitPoint L n k)) 0 :=
  isAnalyticFamily_expMove_linear F g (isAnalyticFamily_const_unitPoint F 0)
private theorem isAnalyticFamily_linearChart_fst (F : TowerFacts L n k) [FiniteDimensional ℝ Z]
    (g : Z →ₗ[ℝ] LevelForms L n k) :
    IsAnalyticFamilyThroughUnit (fun q : Z × Z => expMove (g q.1) (unitPoint L n k)) 0 :=
  isAnalyticFamily_expMove_linear (E := Z × Z) F (g ∘ₗ LinearMap.fst ℝ Z Z)
    (isAnalyticFamily_const_unitPoint F 0)
private theorem isAnalyticFamily_linearChart_iterate (F : TowerFacts L n k) [FiniteDimensional ℝ Z]
    (g : Z →ₗ[ℝ] LevelForms L n k) :
    IsAnalyticFamilyThroughUnit
      (fun q : Z × Z => expMove (g q.2) (expMove (g q.1) (unitPoint L n k))) 0 :=
  isAnalyticFamily_expMove_linear (E := Z × Z) F (g ∘ₗ LinearMap.snd ℝ Z Z)
    (isAnalyticFamily_linearChart_fst F g)
private theorem chainEntries_of_linearChart [FiniteDimensional ℝ Z] (a : ℝ)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hn : 0 < n)
    (hFields : LevelFieldsAnalyticAlongFamily) (hMaps : AnalyticFamilyTransportAndGauge)
    (hBack : GaugeMapsAnalyticAlongFamily) (hlog : AnalyticAt ℝ ComplexMatrix2.logSeries 1)
    (c₀ : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0)) (hc₀ : IsVertexPairingCore c₀)
    (g : Z →ₗ[ℝ] LevelForms L n k) (ι : LevelForms L n k →ₗ[ℝ] Z) (hι : ∀ ξ, g (ι ξ) = ξ)
    (J : Z →ₗ[ℝ] LevelForms L n k) (M : Z →ₗ[ℝ] edgeFormSpace L n k k) :
    (∀ᶠ w in 𝓝 (0 : Z), ∃ q : QuadraticForm ℝ (LevelForms L n k), ∀ ξ,
      q ξ = gaugedRightValue a (expMove (g w) (unitPoint L n k)) (J w) (M w) ξ) ∧
    (∀ ξ : LevelForms L n k, AnalyticAt ℝ (fun w =>
      gaugedRightValue a (expMove (g w) (unitPoint L n k)) (J w) (M w) ξ) 0) ∧
    (∀ (ξ : LevelForms L n k) (C : edgeFormSpace L n k k), AnalyticAt ℝ (fun w =>
      (edgeFormPairing (C : Edge L n k k → ComplexMatrix2)
        (shiftedGaugeMap (expMove (g w) (unitPoint L n k)) ξ : Edge L n k k → ComplexMatrix2)).re) 0) ∧
    (∀ x y : vertexFunctionSpace L n k 0 × vertexFunctionSpace L n k k, AnalyticAt ℝ (fun w =>
      (traceFinsumPairing (x.1 : Vertex L n k 0 → ComplexMatrix2)
        ((ghostBlockOperator (expMove (g w) (unitPoint L n k)) y).1 : Vertex L n k 0 → ComplexMatrix2)).re +
      (traceFinsumPairing (x.2 : Vertex L n k k → ComplexMatrix2)
        ((ghostBlockOperator (expMove (g w) (unitPoint L n k)) y).2 : Vertex L n k k → ComplexMatrix2)).re) 0) ∧
    AnalyticAt ℝ (fun w => logRadiusSum (expMove (g w) (unitPoint L n k))) 0 := by
  have F : TowerFacts L n k := towerFacts hL hn
  have hX := isAnalyticFamily_linearChart F g
  have hX' := isAnalyticFamily_linearChart_fst F g
  have hY := isAnalyticFamily_linearChart_iterate F g
  obtain ⟨fW, fL, -⟩ := hFields L hL k n hk hn Z _ 0 hX
  obtain ⟨fW', -, -⟩ := hFields L hL k n hk hn (Z × Z) _ 0 hX'
  obtain ⟨fWY, fLY, -⟩ := hFields L hL k n hk hn (Z × Z) _ 0 hY
  obtain ⟨mA, mE⟩ := hMaps L hL k n hk hn Z _ 0 hX
  obtain ⟨bT, bG⟩ := hBack L hL k n hk hn Z _ 0 hX
  obtain ⟨B₁, hB₁, S₁⟩ := exists_bilin_leftSecondDeriv a g ι hι
    (X := fun w => expMove (g w) (unitPoint L n k))
    (analyticAt_chainAction F hY (fun i c => (fLY i c).1) a)
  have hTop := fun c : PositiveEdge L n k k => exists_bilin_topSecondVariation g ι hι
    (X := fun w => expMove (g w) (unitPoint L n k)) c hlog (fWY k le_rfl c.1).1 (fW' k le_rfl c.1).1
    (fWY k le_rfl c.1).2 (fW k le_rfl c.1).2
  choose Bc hBc S₄ using hTop
  have hPk := F.positive_finite k
  have S₄' : ∀ᶠ w in 𝓝 (0 : Z), ∀ (c : PositiveEdge L n k k) ξ ξ',
      topSecondVariation (expMove (g w) (unitPoint L n k)) ξ ξ' c = Bc c w (ι ξ) (ι ξ') :=
    eventually_all.2 S₄
  have hσ : ∀ (ξ : LevelForms L n k) (x : Vertex L n k 0), AnalyticAt ℝ
      (fun w => gaugeCorrection (expMove (g w) (unitPoint L n k)) ξ x) (0 : Z) := fun ξ x =>
    analyticAt_extendByZero (mA ξ k le_rfl).2 x
  have hμ : ∀ b : Edge L n k k, AnalyticAt ℝ (fun w => (M w : Edge L n k k → ComplexMatrix2) b) (0 : Z) :=
    fun b => by
      let T : edgeFormSpace L n k k →ₗ[ℝ] ComplexMatrix2 :=
        { toFun := fun t => (t : Edge L n k k → ComplexMatrix2) b
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      exact (LinearMap.toContinuousLinearMap (T ∘ₗ M)).analyticAt _
  refine ⟨?_, fun ξ => ?_, fun ξ C => ?_, fun x y => ?_, ?_⟩
  · filter_upwards [mE, S₁, S₄'] with w hm h₁ h₄
    obtain ⟨-, hτ, S, hS⟩ := hm
    exact exists_quadraticForm_gaugedRightValue a F.positive_finite ι _ (J w) (M w) c₀ hc₀ (B₁ w)
      (fun c => Bc c w) h₁ h₄ hτ S hS
  · exact analyticAt_gaugedRightValue a F ι hX (analyticValues_formValues_linear J) hμ c₀ hc₀ hB₁ hBc S₁ S₄'
      (mE.mono fun w h => h.2.1) ξ (hσ ξ) bT
  · exact analyticAt_shiftedGaugeMap_pairing F C (fW k le_rfl) (mA ξ k le_rfl) (mE.mono fun w h => h.1)
  · exact analyticAt_ghostBlockOperator_pairing F x y (bG y).1 (bG y).2
  · exact analyticAt_logRadiusSum F fL
end Main
theorem chainFunctionEntriesAnalytic_holds (hFields : LevelFieldsAnalyticAlongFamily)
    (hMaps : AnalyticFamilyTransportAndGauge)
    (hBack : GaugeMapsAnalyticAlongFamily)
    (hMB : PeriodicLattice.ElementaryStepFacts)
    (hSite : FormOnAFibre.VertexFunctionsAreEuclidean.Statement) :
    ChainFunctionEntriesAnalytic := by
  intro a _ L hL k n hk hn N e
  have hlog : AnalyticAt ℝ ComplexMatrix2.logSeries 1 :=
    (((hMB L n 1 0 hL hn one_pos).2.2.1).1 1 (by simp [ComplexMatrix2.logBall])).restrictScalars
  obtain ⟨-, c₀, hc₀⟩ := hSite L n k 0 hL hn (Nat.zero_le k)
  exact chainEntries_of_linearChart a hL hk hn hFields hMaps hBack hlog c₀ hc₀
    (LinearMap.fst ℝ _ _ ∘ₗ e.toLinearMap) (e.symm.toLinearMap ∘ₗ LinearMap.inl ℝ _ _)
    (fun ξ => by simp)
    ((LinearMap.fst ℝ _ _ ∘ₗ LinearMap.snd ℝ _ _) ∘ₗ e.toLinearMap)
    ((LinearMap.snd ℝ _ _ ∘ₗ LinearMap.snd ℝ _ _) ∘ₗ e.toLinearMap)
end RunningCouplingSlope.ChainEntries
end
end YangMills.Construction
