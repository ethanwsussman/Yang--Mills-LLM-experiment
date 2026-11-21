import YangMills.Construction.Towers.ChainOfTheComplexIteratesAtTheSideInfinity
import YangMills.Construction.Towers.CovariantAveragesAsDifferentials
import YangMills.Construction.Towers.GaugeCovarianceOfTheCovariantAveragesAtTheSideInfinity
import YangMills.Construction.Towers.GaugeCovarianceOfTheCovariantAveragesOnTheSidesProof
import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOnTheWholeLatticeProof
import YangMills.Construction.Towers.RelationsOfTheCovariantIteratesOfTheWholeLattice
import YangMills.Construction.Towers.TranslationsAndIsometriesOfATowerProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.CovarianceProof
open YangMills.Construction.Tower.FullSpace.AsDifferentials
open YangMills.Construction.Matrices
section Conjugation
theorem inv_inv_of_det_eq_one {V : ComplexMatrix2} (h : V.det = 1) : V⁻¹⁻¹ = V :=
  Matrix.nonsing_inv_nonsing_inv V (by rw [h]; exact isUnit_one)
theorem det_eq_one_of_mem_compact {V : ComplexMatrix2}
    (h : V ∈ PeriodicLattice.compactGaugeGroup) : V.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
theorem conjugateBy_add (g X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (X + Y) =
      ComplexMatrix2.conjugateBy g X + ComplexMatrix2.conjugateBy g Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_sub (g X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (X - Y) =
      ComplexMatrix2.conjugateBy g X - ComplexMatrix2.conjugateBy g Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_sub, sub_mul]
theorem conjugateBy_smul (g : ComplexMatrix2) (c : ℂ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (c • X) = c • ComplexMatrix2.conjugateBy g X := by apply _root_.YangMills.Construction.LieInnerProductProof.conjugateBy_smul <;> assumption
theorem conjugateBy_zero (g : ComplexMatrix2) : ComplexMatrix2.conjugateBy g 0 = 0 := by
  simp only [ComplexMatrix2.conjugateBy, mul_zero, zero_mul]
theorem conj_mem_traceless {g X : ComplexMatrix2} (hg : g.det = 1)
    (hX : X ∈ ComplexMatrix2.traceless) : ComplexMatrix2.conjugateBy g X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.conjugateBy_mem_traceless_of_det <;> assumption
theorem conjugateBy_twist {g h : ComplexMatrix2} (X A : ComplexMatrix2) (hh : h.det = 1) :
    ComplexMatrix2.conjugateBy (g * X * h⁻¹) (ComplexMatrix2.conjugateBy h A) =
      ComplexMatrix2.conjugateBy g (ComplexMatrix2.conjugateBy X A) := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.conjugateBy_conjugateBy_gauge <;> assumption
theorem conjugateBy_finsum_mem {ι : Type*} {g : ComplexMatrix2} (hg : g.det = 1) (S : Set ι)
    (f : ι → ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (∑ᶠ x ∈ S, f x) = ∑ᶠ x ∈ S, ComplexMatrix2.conjugateBy g (f x) := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.conjugateBy_finsum_mem <;> assumption
theorem logSeries_conj {g : ComplexMatrix2} (hg : g.det = 1) (X : ComplexMatrix2) :
    ComplexMatrix2.logSeries (g * X * g⁻¹) =
      ComplexMatrix2.conjugateBy g (ComplexMatrix2.logSeries X) := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.logSeries_conj <;> assumption
theorem ratio_conj {g h W W₀ : ComplexMatrix2} (hh : h.det = 1) :
    (g * W * h⁻¹) * (g * W₀ * h⁻¹)⁻¹ = g * (W * W₀⁻¹) * g⁻¹ := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.mul_inv_gauge_conj <;> assumption
theorem deriv_log_conj {g : ComplexMatrix2} {p p' : ℂ → ComplexMatrix2} {D D' : ComplexMatrix2}
    (hg : g.det = 1)
    (h : ∀ᶠ t in 𝓝 (0 : ℂ), p' t = g * p t * g⁻¹)
    (hD : HasDerivAt (fun t => Complex.I⁻¹ • ComplexMatrix2.logSeries (p t)) D 0)
    (hD' : HasDerivAt (fun t => Complex.I⁻¹ • ComplexMatrix2.logSeries (p' t)) D' 0) :
    D' = ComplexMatrix2.conjugateBy g D := by
  have h1 : HasDerivAt (fun t => g * (Complex.I⁻¹ • ComplexMatrix2.logSeries (p t)) * g⁻¹)
      (g * D * g⁻¹) 0 :=
    (hD.const_mul g).mul_const g⁻¹
  have h2 : (fun t => Complex.I⁻¹ • ComplexMatrix2.logSeries (p' t)) =ᶠ[𝓝 0]
      fun t => g * (Complex.I⁻¹ • ComplexMatrix2.logSeries (p t)) * g⁻¹ := by
    filter_upwards [h] with t ht
    rw [ht, logSeries_conj hg]
    simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
  exact hD'.unique (h1.congr_of_eventuallyEq h2)
end Conjugation
section SingleLattice
variable {a : ℝ}
theorem isPositivelyOriented_or_opposite (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem not_opposite_isPositivelyOriented (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
theorem extendOddly_of_pos (f : InfiniteLattice.Link a → ComplexMatrix2) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.FullSpace.Translations.extendOddly_of_pos <;> assumption
theorem extendOddly_of_not_pos (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : ¬ b.IsPositivelyOriented) :
    extendOddly f b = -f b.opposite := by
  unfold extendOddly
  exact if_neg hb
theorem extendOddly_opposite (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : ¬ b.IsPositivelyOriented) :
    extendOddly f b = -extendOddly f b.opposite := by
  rw [extendOddly_of_not_pos f hb,
    extendOddly_of_pos f ((isPositivelyOriented_or_opposite b).resolve_left hb)]
theorem extendOddly_congr {f f' : InfiniteLattice.Link a → ComplexMatrix2}
    (h : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → extendOddly f b = extendOddly f' b) :
    extendOddly f = extendOddly f' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact h b hb
  · rw [extendOddly_opposite f hb, extendOddly_opposite f' hb,
      h _ ((isPositivelyOriented_or_opposite b).resolve_left hb)]
theorem eq_of_eq_on_positive {X Y : InfiniteLattice.Link a → ComplexMatrix2}
    (hX : ∀ b : InfiniteLattice.Link a, ¬ b.IsPositivelyOriented → X b = -X b.opposite)
    (hY : ∀ b : InfiniteLattice.Link a, ¬ b.IsPositivelyOriented → Y b = -Y b.opposite)
    (h : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → X b = Y b) : X = Y := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact h b hb
  · rw [hX b hb, hY b hb, h _ ((isPositivelyOriented_or_opposite b).resolve_left hb)]
theorem adjointForm_of_pos (u : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B : InfiniteLattice.Link a → ComplexMatrix2) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) :
    adjointForm u B b = ComplexMatrix2.conjugateBy (u b.initial) (B b) :=
  extendOddly_of_pos _ hb
theorem adjointForm_add (u : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B B' : InfiniteLattice.Link a → ComplexMatrix2) :
    adjointForm u (B + B') = adjointForm u B + adjointForm u B' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [Pi.add_apply, adjointForm_of_pos _ _ hb, conjugateBy_add]
  · have e : ∀ C : InfiniteLattice.Link a → ComplexMatrix2,
        adjointForm u C b = -ComplexMatrix2.conjugateBy (u b.opposite.initial) (C b.opposite) :=
      fun C => extendOddly_of_not_pos _ hb
    simp only [Pi.add_apply, e, conjugateBy_add, neg_add]
theorem smul_adjointForm (u : InfiniteLattice.LatticePoint a → ComplexMatrix2) (t : ℂ)
    (B : InfiniteLattice.Link a → ComplexMatrix2) :
    t • adjointForm u B = adjointForm u (t • B) := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [Pi.smul_apply, adjointForm_of_pos _ _ hb, conjugateBy_smul]
  · have e : ∀ C : InfiniteLattice.Link a → ComplexMatrix2,
        adjointForm u C b = -ComplexMatrix2.conjugateBy (u b.opposite.initial) (C b.opposite) :=
      fun C => extendOddly_of_not_pos _ hb
    simp only [Pi.smul_apply, e, conjugateBy_smul, smul_neg]
theorem adjointForm_mem (ha : 0 < a) {u : InfiniteLattice.LatticePoint a → ComplexMatrix2}
    (hu : ∀ x, (u x).det = 1) {B : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms a) : adjointForm u B ∈ complexEdgeForms a := by
  obtain ⟨hv, -⟩ := hB
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [adjointForm_of_pos _ _ hb]
    exact conj_mem_traceless (hu _) (hv b hb)
  · unfold adjointForm
    by_cases hb : b.IsPositivelyOriented
    · rw [extendOddly_of_not_pos _ (not_opposite_isPositivelyOriented ha hb), extendOddly_of_pos _ hb]
      rfl
    · rw [extendOddly_opposite _ hb, neg_neg]
theorem adjointVertexFn_add (u l l' : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    adjointVertexFn u (l + l') = adjointVertexFn u l + adjointVertexFn u l' :=
  funext fun _ => conjugateBy_add _ _ _
theorem covDiff_gaugeAct {u : InfiniteLattice.LatticePoint a → ComplexMatrix2}
    (hu : ∀ x, (u x).det = 1) (U : InfiniteLattice.Link a → ComplexMatrix2)
    (l : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    covDiff (gaugeAct u U) (adjointVertexFn u l) = adjointForm u (covDiff U l) := by
  refine extendOddly_congr fun b hb => ?_
  rw [extendOddly_of_pos _ hb, extendOddly_of_pos _ hb]
  have hD : covDiff U l b =
      ComplexMatrix2.conjugateBy (U b) (l b.terminal) - l b.initial := extendOddly_of_pos _ hb
  change ComplexMatrix2.conjugateBy (u b.initial * U b * (u b.terminal)⁻¹)
      (ComplexMatrix2.conjugateBy (u b.terminal) (l b.terminal)) -
    ComplexMatrix2.conjugateBy (u b.initial) (l b.initial) = _
  rw [hD, conjugateBy_twist _ _ (hu _), conjugateBy_sub]
theorem eventually_defined_smul {IsDefined : (InfiniteLattice.Link a → ComplexMatrix2) → Prop}
    {p v : (InfiniteLattice.Link a → ComplexMatrix2) → ComplexMatrix2}
    (h : _root_.YangMills.Construction.Tower.AsDifferentials.IsLocallyHolomorphicLog
      (fun b : InfiniteLattice.Link a => b.IsPositivelyOriented) (complexEdgeForms a) IsDefined p v)
    {B : InfiniteLattice.Link a → ComplexMatrix2} (hB : B ∈ complexEdgeForms a) :
    ∀ᶠ t : ℂ in 𝓝 0, IsDefined (t • B) := by
  obtain ⟨F, O, f, -, hpos, h0, hf, -, hv⟩ := h
  obtain ⟨s, hs, hball⟩ := (hf OneLoop.pauliBasis).1.2 0 h0
  have hsmall : ∀ b : F, ∀ᶠ t : ℂ in 𝓝 0, ‖t • B b‖ < s := fun b => by
    have hc : Filter.Tendsto (fun t : ℂ => ‖t • B b‖) (𝓝 0) (𝓝 0) := by
      have := ((continuous_id.smul continuous_const :
        Continuous fun t : ℂ => t • B b).norm).tendsto 0
      simpa using this
    exact hc.eventually_lt_const hs
  filter_upwards [eventually_all.2 hsmall] with t ht
  have hmem : t • B ∈ complexEdgeForms a := (complexEdgeForms a).smul_mem t hB
  refine (hv (t • B) hmem (hball _ ?_ ?_)).1
  · exact fun b => hmem.1 b (hpos b b.2)
  · rcases isEmpty_or_nonempty F with he | he
    · simpa [GroupLieProduct.supNorm, Real.iSup_of_isEmpty] using hs
    · obtain ⟨b, hb⟩ := exists_eq_ciSup_of_finite
        (f := fun b : F => ComplexMatrix2.operatorNorm (((fun c : F => (t • B) c) - 0) b))
      rw [GroupLieProduct.supNorm, ← hb]
      simpa using ht b
end SingleLattice
section SingleStep
variable {L k i : ℕ}
structure StepHyps (L k i : ℕ) (U : Edge L k 0 → ComplexMatrix2) : Prop where
  admissible : ∀ c : Edge L k (i + 1), c.IsPositivelyOriented →
    PolydiscIsAdmissible L k i (Tower.polydiscRadius L) c
  mem_polydisc : ∀ c : Edge L k (i + 1), c.IsPositivelyOriented →
    ∀ V ∈ smallComplexFields L k i, V ∈ nearIdentityPolydisc L k i (Tower.polydiscRadius L) c
  equivariance : LeftChartFacts.GaugeEquivarianceForms L k i
  clauses : ∀ V ∈ smallComplexFields L k i, StepConditions i V U
  mesh_pos : 0 < Tower.meshAt L k i
variable {U V : Edge L k 0 → ComplexMatrix2}
theorem inv_twist {g h X : ComplexMatrix2} (hh : h.det = 1) :
    (g * X * h⁻¹)⁻¹ = h * X⁻¹ * g⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_inv_of_det_eq_one hh, mul_assoc]
theorem complexSmoothing_opposite (L : ℕ) {a a' : ℝ} (V : InfiniteLattice.Link a' → ComplexMatrix2)
    {c : InfiniteLattice.Link a} (hc : ¬ c.IsPositivelyOriented) :
    complexSmoothing L V c = (complexSmoothing L V c.opposite)⁻¹ := by
  have hr := (isPositivelyOriented_or_opposite c).resolve_left hc
  unfold complexSmoothing
  rw [if_neg hc, if_pos hr]
end SingleStep
section StepMaps
variable {L k i : ℕ} {U : Edge L k 0 → ComplexMatrix2} {V : Edge L k i → ComplexMatrix2}
  {u : Vertex L k i → ComplexMatrix2}
theorem expTwist_gaugeAct (hD : StepHyps L k i U) (hV : V ∈ smallComplexFields L k i)
    (hu : u ∈ gaugeGroupAt L k i) {B : Edge L k i → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (Tower.meshAt L k i)) (t : ℂ) :
    expTwist (t • adjointForm u B) (gaugeAct u V) = gaugeAct u (expTwist (t • B) V) := by
  rw [smul_adjointForm]
  exact (hD.equivariance u (fun x => det_eq_one_of_mem_compact (hu x))).1 V hV.1 (t • B)
    ((complexEdgeForms _).smul_mem t hB)
theorem smoothingMap_gaugeAct (hD : StepHyps L k i U) (hV : V ∈ smallComplexFields L k i)
    (hu : u ∈ gaugeGroupAt L k i) :
    smoothingMap L k i (gaugeAct u V) =
      gaugeAct (restrictVertexFunction (Tower.meshAt L k (i + 1)) u) (smoothingMap L k i V) := by
  have hr : ∀ x, (restrictVertexFunction (Tower.meshAt L k (i + 1)) u x).det = 1 :=
    fun x => det_eq_one_of_mem_compact (hu _)
  have hpos : ∀ c : Edge L k (i + 1), c.IsPositivelyOriented →
      complexSmoothing L (gaugeAct u V) c =
        gaugeAct (restrictVertexFunction (Tower.meshAt L k (i + 1)) u) (complexSmoothing L V) c :=
    fun c hc => ((hD.admissible c hc).gauge_covariant V (hD.mem_polydisc c hc V hV) u hu).2.1
  funext c
  by_cases hc : c.IsPositivelyOriented
  · exact hpos c hc
  · have hp := (isPositivelyOriented_or_opposite c).resolve_left hc
    show complexSmoothing L (gaugeAct u V) c =
      restrictVertexFunction (Tower.meshAt L k (i + 1)) u c.initial * complexSmoothing L V c *
        (restrictVertexFunction (Tower.meshAt L k (i + 1)) u c.terminal)⁻¹
    rw [complexSmoothing_opposite L _ hc, hpos _ hp, complexSmoothing_opposite L V hc]
    exact inv_twist (hr _)
theorem complexContourMean_gaugeAct (hD : StepHyps L k i U) (hV : V ∈ smallComplexFields L k i)
    (hu : u ∈ gaugeGroupAt L k i) (y : Vertex L k (i + 1)) {x : Vertex L k i}
    (hx : x ∈ cubeVertices L (Tower.meshAt L k i) y) :
    complexContourMean L (gaugeAct u V) y x =
      u (toFiner (Tower.meshAt L k i) y) * complexContourMean L V y x * (u x)⁻¹ := by
  have hc : (InfiniteLattice.Link.forwardFrom y 0).IsPositivelyOriented :=
    ⟨0, by simp [InfiniteLattice.Link.forwardFrom]⟩
  exact ((hD.admissible _ hc).gauge_covariant V (hD.mem_polydisc _ hc V hV) u hu).2.2 y
    (Or.inl rfl) x hx
theorem adjointCubeAverage_gaugeAct (hD : StepHyps L k i U) (hV : V ∈ smallComplexFields L k i)
    (hu : u ∈ gaugeGroupAt L k i) (l : Vertex L k i → ComplexMatrix2) :
    adjointCubeAverage (gaugeAct u V) (adjointVertexFn u l) =
      adjointVertexFn (restrictVertexFunction (Tower.meshAt L k (i + 1)) u)
        (adjointCubeAverage V l) := by
  funext y
  have hg : (u (toFiner (Tower.meshAt L k i) y)).det = 1 := det_eq_one_of_mem_compact (hu _)
  change PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ cubeVertices L (Tower.meshAt L k i) y,
      ComplexMatrix2.conjugateBy (complexContourMean L (gaugeAct u V) y x)
        (ComplexMatrix2.conjugateBy (u x) (l x)) =
    ComplexMatrix2.conjugateBy (u (toFiner (Tower.meshAt L k i) y))
      (PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ cubeVertices L (Tower.meshAt L k i) y,
        ComplexMatrix2.conjugateBy (complexContourMean L V y x) (l x))
  rw [conjugateBy_smul, conjugateBy_finsum_mem hg]
  congr 1
  refine finsum_mem_congr rfl fun x hx => ?_
  rw [complexContourMean_gaugeAct hD hV hu y hx,
    conjugateBy_twist _ _ (det_eq_one_of_mem_compact (hu x))]
theorem logDirectionalDeriv_gaugeAct (hD : StepHyps L k i U) (hV : V ∈ smallComplexFields L k i)
    (hV' : gaugeAct u V ∈ smallComplexFields L k i)
    (hu : u ∈ gaugeGroupAt L k i) (y : Vertex L k (i + 1)) {x : Vertex L k i}
    (hx : x ∈ cubeVertices L (Tower.meshAt L k i) y) {B : Edge L k i → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (Tower.meshAt L k i)) :
    Tower.logDirectionalDeriv ℂ
        (fun X => complexContourMean L (expTwist X (gaugeAct u V)) y x)
        (complexContourMean L (gaugeAct u V) y x) (adjointForm u B) =
      ComplexMatrix2.conjugateBy (u (toFiner (Tower.meshAt L k i) y))
        (Tower.logDirectionalDeriv ℂ (fun X => complexContourMean L (expTwist X V) y x)
          (complexContourMean L V y x) B) := by
  have hB' := adjointForm_mem hD.mesh_pos (fun x => det_eq_one_of_mem_compact (hu x)) hB
  refine deriv_log_conj (p := fun t => contourRatio V y x (t • B))
    (p' := fun t => contourRatio (gaugeAct u V) y x (t • adjointForm u B))
    (det_eq_one_of_mem_compact (hu _)) ?_ ((hD.clauses V hV).deriv_contour y x hx B hB)
    ((hD.clauses _ hV').deriv_contour y x hx _ hB')
  filter_upwards [eventually_defined_smul ((hD.clauses V hV).local_contour y x hx) hB] with t ht
  obtain ⟨c, hc, hy, hp⟩ := ht
  have hcov := ((hD.admissible c hc).gauge_covariant _ hp u hu).2.2 y hy x hx
  have hcov0 :=
    ((hD.admissible c hc).gauge_covariant V (hD.mem_polydisc c hc V hV) u hu).2.2 y hy x hx
  change complexContourMean L (expTwist (t • adjointForm u B) (gaugeAct u V)) y x *
      (complexContourMean L (gaugeAct u V) y x)⁻¹ =
    _ * (complexContourMean L (expTwist (t • B) V) y x *
      (complexContourMean L V y x)⁻¹) * _
  rw [expTwist_gaugeAct hD hV hu hB t, hcov, hcov0]
  exact ratio_conj (det_eq_one_of_mem_compact (hu x))
theorem contourLogDrift_gaugeAct (hD : StepHyps L k i U) (hV : V ∈ smallComplexFields L k i)
    (hV' : gaugeAct u V ∈ smallComplexFields L k i)
    (hu : u ∈ gaugeGroupAt L k i) {B : Edge L k i → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (Tower.meshAt L k i)) :
    contourLogDrift (gaugeAct u V) (adjointForm u B) =
      adjointVertexFn (restrictVertexFunction (Tower.meshAt L k (i + 1)) u)
        (contourLogDrift V B) := by
  funext y
  have hg : (u (toFiner (Tower.meshAt L k i) y)).det = 1 := det_eq_one_of_mem_compact (hu _)
  change PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ cubeVertices L (Tower.meshAt L k i) y,
      Tower.logDirectionalDeriv ℂ
        (fun X => complexContourMean L (expTwist X (gaugeAct u V)) y x)
        (complexContourMean L (gaugeAct u V) y x) (adjointForm u B) =
    ComplexMatrix2.conjugateBy (u (toFiner (Tower.meshAt L k i) y))
      (PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ cubeVertices L (Tower.meshAt L k i) y,
        Tower.logDirectionalDeriv ℂ (fun X => complexContourMean L (expTwist X V) y x)
          (complexContourMean L V y x) B)
  rw [conjugateBy_smul, conjugateBy_finsum_mem hg]
  congr 1
  exact finsum_mem_congr rfl fun x hx => logDirectionalDeriv_gaugeAct hD hV hV' hu y hx hB
theorem complexSmoothingDeriv_gaugeAct (hD : StepHyps L k i U) (hV : V ∈ smallComplexFields L k i)
    (hV' : gaugeAct u V ∈ smallComplexFields L k i)
    (hu : u ∈ gaugeGroupAt L k i) {B : Edge L k i → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (Tower.meshAt L k i)) :
    complexSmoothingDeriv (gaugeAct u V) (adjointForm u B) =
      adjointForm (restrictVertexFunction (Tower.meshAt L k (i + 1)) u)
        (complexSmoothingDeriv V B) := by
  have hB' := adjointForm_mem hD.mesh_pos (fun x => det_eq_one_of_mem_compact (hu x)) hB
  refine eq_of_eq_on_positive (fun b hb => ?_) (fun b hb => ?_) fun c hc => ?_
  · unfold complexSmoothingDeriv holLeftDifferential
    exact extendOddly_opposite _ hb
  · unfold adjointForm
    exact extendOddly_opposite _ hb
  rw [adjointForm_of_pos _ _ hc]
  refine deriv_log_conj (p := fun t => meanRatio V c (t • B))
    (p' := fun t => meanRatio (gaugeAct u V) c (t • adjointForm u B))
    (det_eq_one_of_mem_compact (hu _)) ?_ ((hD.clauses V hV).deriv_mean c hc B hB)
    ((hD.clauses _ hV').deriv_mean c hc _ hB')
  filter_upwards [eventually_defined_smul ((hD.clauses V hV).local_mean c hc) hB] with t hp
  have hcov := ((hD.admissible c hc).gauge_covariant _ hp u hu).2.1
  have hcov0 := ((hD.admissible c hc).gauge_covariant V (hD.mem_polydisc c hc V hV) u hu).2.1
  change complexSmoothing L (expTwist (t • adjointForm u B) (gaugeAct u V)) c *
      (complexSmoothing L (gaugeAct u V) c)⁻¹ =
    _ * (complexSmoothing L (expTwist (t • B) V) c * (complexSmoothing L V c)⁻¹) * _
  rw [expTwist_gaugeAct hD hV hu hB t, hcov, hcov0]
  exact ratio_conj (det_eq_one_of_mem_compact (hu _))
end StepMaps
section ByLevel
variable {L k : ℕ}
theorem latticeSubgroup_succ_subset (L k j : ℕ) (hL : L ≠ 0) :
    (InfiniteLattice.latticeSubgroup (Tower.meshAt L k (j + 1)) : Set InfiniteLattice.AmbientSpace) ⊆
      InfiniteLattice.latticeSubgroup (Tower.meshAt L k j) := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.latticeSubgroup_meshAt_succ_subset <;> assumption
theorem latticeSubgroup_subset_of_le (L k i j : ℕ) (hL : L ≠ 0) (hij : i ≤ j) :
    (InfiniteLattice.latticeSubgroup (Tower.meshAt L k j) : Set InfiniteLattice.AmbientSpace) ⊆
      InfiniteLattice.latticeSubgroup (Tower.meshAt L k i) := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.latticeSubgroup_meshAt_subset_of_le <;> assumption
theorem restrictVertexFunction_self {a : ℝ} (l : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    restrictVertexFunction a l = l := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.restrict_self <;> assumption
theorem restrictVertexFunction_restrictVertexFunction {a a' a'' : ℝ}
    (h₁ : (InfiniteLattice.latticeSubgroup a'' : Set InfiniteLattice.AmbientSpace) ⊆
      InfiniteLattice.latticeSubgroup a')
    (h₂ : (InfiniteLattice.latticeSubgroup a' : Set InfiniteLattice.AmbientSpace) ⊆
      InfiniteLattice.latticeSubgroup a)
    (l : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    restrictVertexFunction a'' (restrictVertexFunction a' l) = restrictVertexFunction a'' l := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.restrict_restrict <;> assumption
variable {U : Edge L k 0 → ComplexMatrix2} {u : Vertex L k 0 → ComplexMatrix2}
theorem restrictVertexFunction_succ (hL : L ≠ 0) (i : ℕ) (u : Vertex L k 0 → ComplexMatrix2) :
    restrictVertexFunction (Tower.meshAt L k (i + 1))
        (restrictVertexFunction (Tower.meshAt L k i) u) =
      restrictVertexFunction (Tower.meshAt L k (i + 1)) u :=
  restrictVertexFunction_restrictVertexFunction (latticeSubgroup_succ_subset L k i hL)
    (latticeSubgroup_subset_of_le L k 0 i hL (Nat.zero_le i)) u
theorem restrictVertexFunction_mem (hu : u ∈ gaugeGroupAt L k 0) (i : ℕ) :
    restrictVertexFunction (Tower.meshAt L k i) u ∈ gaugeGroupAt L k i :=
  fun _ => hu _
theorem complexIter_gaugeAct (hL : L ≠ 0) (hD : ∀ i < k, StepHyps L k i U)
    (hU : U ∈ smallIterateFields L k) (hu : u ∈ gaugeGroupAt L k 0) :
    ∀ i ≤ k, complexIter L k i (gaugeAct u U) =
      gaugeAct (restrictVertexFunction (Tower.meshAt L k i) u) (complexIter L k i U) := by
  intro i
  induction i with
  | zero =>
    intro _
    show gaugeAct u U = gaugeAct (restrictVertexFunction (Tower.meshAt L k 0) u) U
    rw [restrictVertexFunction_self]
  | succ i ih =>
    intro h
    have hi : i < k := h
    show smoothingMap L k i (complexIter L k i (gaugeAct u U)) =
      gaugeAct (restrictVertexFunction (Tower.meshAt L k (i + 1)) u)
        (smoothingMap L k i (complexIter L k i U))
    rw [ih hi.le, smoothingMap_gaugeAct (hD i hi) (hU.2 i hi) (restrictVertexFunction_mem hu i),
      restrictVertexFunction_succ hL]
theorem iterAdjointCubeAverage_gaugeAct (hL : L ≠ 0) (hD : ∀ i < k, StepHyps L k i U)
    (hU : U ∈ smallIterateFields L k) (hu : u ∈ gaugeGroupAt L k 0)
    (l : Vertex L k 0 → ComplexMatrix2) :
    ∀ i ≤ k, iterAdjointCubeAverage L k (gaugeAct u U) i (adjointVertexFn u l) =
      adjointVertexFn (restrictVertexFunction (Tower.meshAt L k i) u)
        (iterAdjointCubeAverage L k U i l) := by
  intro i
  induction i with
  | zero =>
    intro _
    show adjointVertexFn u l = adjointVertexFn (restrictVertexFunction (Tower.meshAt L k 0) u) l
    rw [restrictVertexFunction_self]
  | succ i ih =>
    intro h
    have hi : i < k := h
    show adjointCubeAverage (complexIter L k i (gaugeAct u U))
        (iterAdjointCubeAverage L k (gaugeAct u U) i (adjointVertexFn u l)) =
      adjointVertexFn (restrictVertexFunction (Tower.meshAt L k (i + 1)) u)
        (adjointCubeAverage (complexIter L k i U) (iterAdjointCubeAverage L k U i l))
    rw [ih hi.le, complexIter_gaugeAct hL hD hU hu i hi.le,
      adjointCubeAverage_gaugeAct (hD i hi) (hU.2 i hi) (restrictVertexFunction_mem hu i),
      restrictVertexFunction_succ hL]
theorem gaugeAct_complexIter_mem (hL : L ≠ 0) (hD : ∀ i < k, StepHyps L k i U)
    (hU : U ∈ smallIterateFields L k) (hu : u ∈ gaugeGroupAt L k 0)
    (hW : gaugeAct u U ∈ smallIterateFields L k) {i : ℕ} (hi : i < k) :
    gaugeAct (restrictVertexFunction (Tower.meshAt L k i) u) (complexIter L k i U) ∈
      smallComplexFields L k i := by
  rw [← complexIter_gaugeAct hL hD hU hu i hi.le]
  exact hW.2 i hi
abbrev IterChainAt (L k : ℕ) : Prop :=
  ∀ U ∈ smallIterateFields L k, ∀ B ∈ complexEdgeForms (Tower.meshAt L k 0),
    complexIterDeriv L k 0 U B = B ∧
    (∀ j < k, complexIterDeriv L k (j + 1) U B =
      complexSmoothingDeriv (complexIter L k j U) (complexIterDeriv L k j U B)) ∧
    ∀ j ≤ k, complexIterDeriv L k j U B ∈ complexEdgeForms (Tower.meshAt L k j)
theorem complexIterDeriv_gaugeAct (hL : L ≠ 0) (hD : ∀ i < k, StepHyps L k i U)
    (hI : IterChainAt L k) (hU : U ∈ smallIterateFields L k) (hu : u ∈ gaugeGroupAt L k 0)
    (hW : gaugeAct u U ∈ smallIterateFields L k) {B : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (Tower.meshAt L k 0))
    (hB' : adjointForm u B ∈ complexEdgeForms (Tower.meshAt L k 0)) :
    ∀ i ≤ k, complexIterDeriv L k i (gaugeAct u U) (adjointForm u B) =
      adjointForm (restrictVertexFunction (Tower.meshAt L k i) u)
        (complexIterDeriv L k i U B) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [(hI _ hW _ hB').1, (hI U hU B hB).1, restrictVertexFunction_self]
  | succ i ih =>
    intro h
    have hi : i < k := h
    rw [(hI _ hW _ hB').2.1 i hi, (hI U hU B hB).2.1 i hi, ih hi.le,
      complexIter_gaugeAct hL hD hU hu i hi.le,
      complexSmoothingDeriv_gaugeAct (hD i hi) (hU.2 i hi)
        (gaugeAct_complexIter_mem hL hD hU hu hW hi) (restrictVertexFunction_mem hu i)
        ((hI U hU B hB).2.2 i hi.le), restrictVertexFunction_succ hL]
theorem iterContourLogDrift_gaugeAct (hL : L ≠ 0) (hD : ∀ i < k, StepHyps L k i U)
    (hI : IterChainAt L k) (hU : U ∈ smallIterateFields L k) (hu : u ∈ gaugeGroupAt L k 0)
    (hW : gaugeAct u U ∈ smallIterateFields L k) {B : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (Tower.meshAt L k 0))
    (hB' : adjointForm u B ∈ complexEdgeForms (Tower.meshAt L k 0)) :
    ∀ i ≤ k, iterContourLogDrift L k (gaugeAct u U) i (adjointForm u B) =
      adjointVertexFn (restrictVertexFunction (Tower.meshAt L k i) u)
        (iterContourLogDrift L k U i B) := by
  intro i
  induction i with
  | zero =>
    intro _
    funext x
    exact (conjugateBy_zero _).symm
  | succ i ih =>
    intro h
    have hi : i < k := h
    show adjointCubeAverage (complexIter L k i (gaugeAct u U))
          (iterContourLogDrift L k (gaugeAct u U) i (adjointForm u B)) +
        contourLogDrift (complexIter L k i (gaugeAct u U))
          (complexIterDeriv L k i (gaugeAct u U) (adjointForm u B)) =
      adjointVertexFn (restrictVertexFunction (Tower.meshAt L k (i + 1)) u)
        (adjointCubeAverage (complexIter L k i U) (iterContourLogDrift L k U i B) +
          contourLogDrift (complexIter L k i U) (complexIterDeriv L k i U B))
    rw [ih hi.le, complexIterDeriv_gaugeAct hL hD hI hU hu hW hB hB' i hi.le,
      complexIter_gaugeAct hL hD hU hu i hi.le,
      adjointCubeAverage_gaugeAct (hD i hi) (hU.2 i hi) (restrictVertexFunction_mem hu i),
      contourLogDrift_gaugeAct (hD i hi) (hU.2 i hi) (gaugeAct_complexIter_mem hL hD hU hu hW hi)
        (restrictVertexFunction_mem hu i) ((hI U hU B hB).2.2 i hi.le),
      restrictVertexFunction_succ hL, adjointVertexFn_add]
theorem meshAt_pos (hL : L ≠ 0) (i : ℕ) : 0 < Tower.meshAt L k i :=
  zpow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hL)) _
end ByLevel
theorem averagesGaugeCovariant_holds (hA : Tower.SmoothingNearIdentity)
    (hG : Tower.GaugeEquivarianceFormsAllSides)
    (hP : Tower.MeanStableFields.MeanStableFieldsHold)
    (hC : _root_.YangMills.Construction.Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (hI : ComplexIterChain)
    (hR : CovariantIterRelations) : AveragesGaugeCovariant := by
  intro L hL k j hj U hU u hu hW
  have hL0 : L ≠ 0 := by
    have := hL.2
    omega
  have hD : ∀ i < k, StepHyps L k i U := fun i hi =>
    have hk : 1 ≤ k := by omega
    { admissible := fun c hc => (hA.1 L hL).2.2.fullSpace k i hi c hc
      mem_polydisc := fun c hc V hV => (hP L hL k hk).2.mem_polydisc i hi c hc V hV
      equivariance := (hG L k i hL hi.le).2
      clauses := fun V hV => (hC L hL k hk).2.1 i hi V hV U hU
      mesh_pos := meshAt_pos hL0 i }
  have hI' : IterChainAt L k := fun W hW' B hB => hI L hL k W hW' B hB
  have hd : ∀ x, (u x).det = 1 := fun x => det_eq_one_of_mem_compact (hu x)
  refine ⟨fun l _ => ⟨covDiff_gaugeAct hd U l,
    iterAdjointCubeAverage_gaugeAct hL0 hD hU hu l j hj⟩, fun B hB => ?_⟩
  have hB' := adjointForm_mem (meshAt_pos hL0 0) hd hB
  have hq := complexIterDeriv_gaugeAct hL0 hD hI' hU hu hW hB hB' j hj
  have hn := iterContourLogDrift_gaugeAct hL0 hD hI' hU hu hW hB hB' j hj
  refine ⟨hq, ?_, hn⟩
  rw [(hR L hL k j hj _ hW).1 _ hB', (hR L hL k j hj U hU).1 B hB, hq, hn,
    complexIter_gaugeAct hL0 hD hU hu j hj,
    covDiff_gaugeAct (fun x => det_eq_one_of_mem_compact (restrictVertexFunction_mem hu j x)),
    adjointForm_add]
end YangMills.Construction.Tower.FullSpace.CovarianceProof
end
