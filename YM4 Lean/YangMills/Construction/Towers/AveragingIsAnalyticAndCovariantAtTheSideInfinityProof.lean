import YangMills.Construction.Lattice.HolonomyUnderReorderingProof
import YangMills.Construction.Averaging.EverySmallRadiusServesProof
import YangMills.Construction.Towers.AveragingIsAnalyticAndCovariantAtTheSideInfinity
import YangMills.Construction.Towers.AveragingPolydiscRadiusExists
import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.SmoothingAnalyticCovariantProof
open Matrices
theorem inv_inv_of_det_eq_one {X : ComplexMatrix2} (h : X.det = 1) : X⁻¹⁻¹ = X :=
  Matrix.nonsing_inv_nonsing_inv X (by rw [h]; exact isUnit_one)
theorem su_det_eq_one {g : ComplexMatrix2}
    (hg : g ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) : g.det = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hg).2
theorem su_inv_mem {g : ComplexMatrix2}
    (hg : g ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    g⁻¹ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by apply _root_.YangMills.SharedProofs.p33390 <;> assumption
theorem su_norm_inv_sub_one {g : ComplexMatrix2}
    (hg : g ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) : ‖g⁻¹ - 1‖ = ‖g - 1‖ := by apply _root_.YangMills.Construction.PeriodicLattice.HolonomyUnderReordering.norm_inv_sub_one_of_mem <;> assumption
section Holomorphic
variable {ι ι' κ : Type} [Fintype ι] [Fintype ι'] [Fintype κ]
def reindexCLM (e : ι ≃ ι') : (ι → ComplexMatrix2) →L[ℂ] (ι' → ComplexMatrix2) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (e.symm i)
omit [Fintype ι] [Fintype ι'] in
theorem reindexCLM_apply (e : ι ≃ ι') (w : ι → ComplexMatrix2) : reindexCLM e w = w ∘ e.symm := rfl
theorem isHolomorphicBetween_reindex (e : ι ≃ ι') (t : κ → ComplexMatrix2.FactorKind)
    {W : Set (ι' → ComplexMatrix2)} {h : (ι' → ComplexMatrix2) → κ → ComplexMatrix2}
    (hh : ComplexMatrix2.IsHolomorphicBetween (fun _ : ι' => ComplexMatrix2.FactorKind.group) t W h) :
    ComplexMatrix2.IsHolomorphicBetween (fun _ : ι => ComplexMatrix2.FactorKind.group) t
      (reindexCLM e ⁻¹' W) fun w => h (reindexCLM e w) := by
  obtain ⟨⟨O, hO, rfl⟩, hm, ha⟩ := hh
  refine ⟨⟨reindexCLM e ⁻¹' O, hO.preimage (reindexCLM e).continuous, ?_⟩, fun w hw => hm hw, ?_⟩
  · ext w
    show (w ∘ e.symm ∈ O ∧ _) ↔ (w ∘ e.symm ∈ O ∧ _)
    refine and_congr_right fun _ => ⟨fun h i => ?_, fun h i => h _⟩
    simpa [reindexCLM_apply] using h (e i)
  · intro x hx
    obtain ⟨F, hF, hev⟩ := ha _ hx
    refine ⟨fun w => F (reindexCLM e w), hF.comp ((reindexCLM e).analyticAt x), ?_⟩
    have ht : Filter.Tendsto (reindexCLM e)
        (𝓝[reindexCLM e ⁻¹' (O ∩ ComplexMatrix2.complexifiedProduct fun _ => ComplexMatrix2.FactorKind.group)] x)
        (𝓝[O ∩ ComplexMatrix2.complexifiedProduct fun _ => ComplexMatrix2.FactorKind.group] (reindexCLM e x)) :=
      (reindexCLM e).continuous.continuousWithinAt.tendsto_nhdsWithin (mapsTo_preimage _ _)
    exact ht.eventually hev
def adjugateLinearMap : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 where
  toFun X := X.adjugate
  map_add' X Y := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [Matrix.adjugate_fin_two] <;> ring
  map_smul' c X := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [Matrix.adjugate_fin_two]
def adjugateAtUnit : (Unit → ComplexMatrix2) →L[ℂ] (Unit → ComplexMatrix2) :=
  ContinuousLinearMap.pi fun _ =>
    (LinearMap.toContinuousLinearMap adjugateLinearMap).comp (ContinuousLinearMap.proj ())
theorem isHolomorphicBetween_adjugate {s : ι → ComplexMatrix2.FactorKind} {W : Set (ι → ComplexMatrix2)}
    {h : (ι → ComplexMatrix2) → Unit → ComplexMatrix2}
    (hh : ComplexMatrix2.IsHolomorphicBetween s (fun _ : Unit => ComplexMatrix2.FactorKind.group) W h) :
    ComplexMatrix2.IsHolomorphicBetween s (fun _ : Unit => ComplexMatrix2.FactorKind.group) W
      fun w _ => (h w ()).adjugate := by
  refine ⟨hh.1, fun w hw i => ?_, fun x hx => ?_⟩
  · have h1 : (h w ()).det = 1 := hh.2.1 hw ()
    show (h w ()).adjugate.det = 1
    rw [Matrix.det_adjugate, h1, one_pow]
  · obtain ⟨F, hF, hev⟩ := hh.2.2 x hx
    refine ⟨fun w => adjugateAtUnit (F w), (adjugateAtUnit.analyticAt _).comp hF, ?_⟩
    filter_upwards [hev] with y hy
    funext _
    rw [hy]
    rfl
end Holomorphic
section OneLattice
variable {a : ℝ}
theorem opposite_opposite (b : InfiniteLattice.Link a) : b.opposite.opposite = b := rfl
theorem opposite_isPositivelyOriented {b : InfiniteLattice.Link a} (h : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem not_opposite_isPositivelyOriented (ha : 0 < a) {b : InfiniteLattice.Link a}
    (h : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
variable {ℬ : Set (InfiniteLattice.Link a)}
theorem extendFromPositive_of_positive (v : PositiveEdgeOf ℬ → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (h : b ∈ ℬ ∧ b.IsPositivelyOriented) :
    extendFromPositive ℬ v b = v ⟨b, h⟩ := dif_pos h
theorem extendFromPositive_of_not_positive (v : PositiveEdgeOf ℬ → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (h : ¬ b.IsPositivelyOriented) (h' : b.opposite ∈ ℬ) :
    extendFromPositive ℬ v b = (extendFromPositive ℬ v b.opposite)⁻¹ := by
  have hr := opposite_isPositivelyOriented h
  rw [extendFromPositive_of_positive v ⟨h', hr⟩]
  unfold extendFromPositive
  rw [dif_neg (fun x => h x.2), dif_pos ⟨h', hr⟩]
theorem restrictPositive_extendFromPositive (v : PositiveEdgeOf ℬ → ComplexMatrix2) :
    restrictPositive ℬ (extendFromPositive ℬ v) = v := by
  funext p
  exact extendFromPositive_of_positive v p.2
theorem extendFromPositive_restrictPositive (hsym : ∀ b ∈ ℬ, b.opposite ∈ ℬ)
    {V : InfiniteLattice.Link a → ComplexMatrix2}
    (hV : IsFieldOn PeriodicLattice.complexGaugeGroup ℬ V)
    {b : InfiniteLattice.Link a} (hb : b ∈ ℬ) :
    extendFromPositive ℬ (restrictPositive ℬ V) b = V b := by
  by_cases h : b.IsPositivelyOriented
  · exact extendFromPositive_of_positive _ ⟨hb, h⟩
  · have hr := opposite_isPositivelyOriented h
    rw [extendFromPositive_of_not_positive _ h (hsym b hb),
      extendFromPositive_of_positive _ ⟨hsym b hb, hr⟩]
    show (V b.opposite)⁻¹ = V b
    rw [hV.2 b hb]
    exact inv_inv_of_det_eq_one (hV.1 b hb)
theorem extendFromPositive_mem_polydisc (ha : 0 < a) (hsym : ∀ b ∈ ℬ, b.opposite ∈ ℬ) {ρ : ℝ}
    {v : PositiveEdgeOf ℬ → ComplexMatrix2}
    (hv : ∀ p, v p ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2))
    (hn : ∀ p, ‖v p - 1‖ < ρ) :
    IsFieldOn PeriodicLattice.complexGaugeGroup ℬ (extendFromPositive ℬ v) ∧
      ∀ b ∈ ℬ, ComplexMatrix2.operatorNorm (extendFromPositive ℬ v b - 1) < ρ := by
  have key : ∀ b ∈ ℬ, extendFromPositive ℬ v b ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) ∧
      ‖extendFromPositive ℬ v b - 1‖ < ρ := by
    intro b hb
    by_cases h : b.IsPositivelyOriented
    · rw [extendFromPositive_of_positive v ⟨hb, h⟩]
      exact ⟨hv _, hn _⟩
    · have hr := opposite_isPositivelyOriented h
      rw [extendFromPositive_of_not_positive v h (hsym b hb),
        extendFromPositive_of_positive v ⟨hsym b hb, hr⟩]
      exact ⟨su_inv_mem (hv _), by rw [su_norm_inv_sub_one (hv _)]; exact hn _⟩
  refine ⟨⟨fun b hb => su_det_eq_one (key b hb).1, fun b hb => ?_⟩, fun b hb => (key b hb).2⟩
  by_cases h : b.IsPositivelyOriented
  · have hn' := not_opposite_isPositivelyOriented ha h
    rw [extendFromPositive_of_not_positive v hn' (by simpa [opposite_opposite] using hb),
      opposite_opposite]
  · rw [extendFromPositive_of_not_positive v h (hsym b hb)]
    exact (inv_inv_of_det_eq_one (su_det_eq_one (key _ (hsym b hb)).1)).symm
theorem analyticInFinitelyManyLinks_of_polydisc (ha : 0 < a) (hsym : ∀ b ∈ ℬ, b.opposite ∈ ℬ)
    {ρ : ℝ} {P : Set (InfiniteLattice.Link a → ComplexMatrix2)}
    (hP : ∀ V, V ∈ P ↔ IsFieldOn PeriodicLattice.complexGaugeGroup ℬ V ∧
      ∀ b ∈ ℬ, ComplexMatrix2.operatorNorm (V b - 1) < ρ)
    {Φ : (InfiniteLattice.Link a → ComplexMatrix2) → ComplexMatrix2}
    (hol : ∃ _ : Fintype (PositiveEdgeOf ℬ),
      ComplexMatrix2.IsHolomorphicBetween (fun _ : PositiveEdgeOf ℬ => ComplexMatrix2.FactorKind.group)
        (fun _ : Unit => ComplexMatrix2.FactorKind.group) (restrictPositive ℬ '' P)
        fun v _ => Φ (extendFromPositive ℬ v))
    (hloc : ∀ V ∈ P, ∀ V' ∈ P, (∀ b ∈ ℬ, V b = V' b) → Φ V = Φ V')
    {D : Set (InfiniteLattice.Link a → ComplexMatrix2)} (hDP : D ⊆ P)
    (hDG : ∀ V ∈ D, ∀ b, V b ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    IsAnalyticInFinitelyManyLinks D Φ := by
  classical
  obtain ⟨inst, hh⟩ := hol
  let F : Finset (InfiniteLattice.Link a) :=
    Finset.univ.image (Subtype.val : PositiveEdgeOf ℬ → _)
  have hF : ∀ b, b ∈ F ↔ b ∈ ℬ ∧ b.IsPositivelyOriented := by
    intro b
    constructor
    · intro hb
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hb
      exact p.2
    · intro hb
      exact Finset.mem_image.2 ⟨⟨b, hb⟩, Finset.mem_univ _, rfl⟩
  let e : F ≃ PositiveEdgeOf ℬ := Equiv.subtypeEquivRight hF
  refine ⟨F, {w | (∀ b, w b ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) ∧ ∀ b, ‖w b - 1‖ < ρ},
    fun w _ => Φ (extendFromPositive ℬ (reindexCLM e w)), ⟨?_, ?_⟩, ?_⟩
  · refine ⟨{w | ∀ b, ‖w b - 1‖ < ρ}, ?_, ?_⟩
    · have h : {w : F → ComplexMatrix2 | ∀ b, ‖w b - 1‖ < ρ} = ⋂ b, {w | ‖w b - 1‖ < ρ} := by
        ext w
        simp
      rw [h]
      exact isOpen_iInter_of_finite fun b =>
        isOpen_lt (continuous_norm.comp ((continuous_apply b).sub continuous_const))
          continuous_const
    · ext w
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  · intro x hx
    have hc := extendFromPositive_mem_polydisc (v := reindexCLM e x) ha hsym (fun p => hx.1 _)
      (fun p => hx.2 _)
    exact ⟨reindexCLM e ⁻¹' (restrictPositive ℬ '' P),
      fun w _ => Φ (extendFromPositive ℬ (reindexCLM e w)),
      ⟨_, (hP _).2 hc, restrictPositive_extendFromPositive _⟩, isHolomorphicBetween_reindex e _ hh,
      Filter.Eventually.of_forall fun _ => rfl⟩
  · intro V hV
    have hVP := (hP V).1 (hDP hV)
    have hbF : ∀ b : F, (b : InfiniteLattice.Link a) ∈ ℬ := fun b => ((hF b).1 b.2).1
    refine ⟨⟨fun b => hDG V hV b, fun b => hVP.2 b (hbF b)⟩, ?_⟩
    have hr : reindexCLM e (fun b : F => V b) = restrictPositive ℬ V := rfl
    show Φ V = Φ (extendFromPositive ℬ (reindexCLM e fun b : F => V b))
    rw [hr]
    refine hloc V (hDP hV) _ ((hP _).2 ?_) fun b hb =>
      (extendFromPositive_restrictPositive hsym hVP.1 hb).symm
    exact extendFromPositive_mem_polydisc ha hsym (fun p => hDG V hV _) (fun p => hVP.2 _ p.2.1)
theorem analyticInFinitelyManyLinks_inv {D : Set (InfiniteLattice.Link a → ComplexMatrix2)}
    {f : (InfiniteLattice.Link a → ComplexMatrix2) → ComplexMatrix2}
    (hf : IsAnalyticInFinitelyManyLinks D f) (hdet : ∀ V ∈ D, (f V).det = 1) :
    IsAnalyticInFinitelyManyLinks D fun V => (f V)⁻¹ := by
  obtain ⟨F, O, g, hg, hv⟩ := hf
  refine ⟨F, O, fun w _ => (g w ()).adjugate, ⟨hg.1, fun x hx => ?_⟩,
    fun V hV => ⟨(hv V hV).1, ?_⟩⟩
  · obtain ⟨W, h, hxW, hh, hev⟩ := hg.2 x hx
    refine ⟨W, fun w _ => (h w ()).adjugate, hxW, isHolomorphicBetween_adjugate hh, ?_⟩
    filter_upwards [hev] with y hy
    rw [hy]
  · show (f V)⁻¹ = (g (fun b : F => V b) ()).adjugate
    rw [← (hv V hV).2, Matrix.inv_def, hdet V hV]
    simp
end OneLattice
theorem projField_congr {L n k i : ℕ} (ℬ : Set (Edge L k i)) {V V' : Edge L k i → ComplexMatrix2}
    (h : ∀ b ∈ ℬ, V b = V' b) :
    projField L n k i ℬ V = projField L n k i ℬ V' := by
  funext c
  unfold projField
  by_cases hc : ∃ b ∈ ℬ, projEdge L n k i b = c
  · rw [dif_pos hc, dif_pos hc]
    exact h _ hc.choose_spec.1
  · rw [dif_neg hc, dif_neg hc]
theorem forwardFrom_zero_isPositivelyOriented {a : ℝ} (y : InfiniteLattice.LatticePoint a) :
    (InfiniteLattice.Link.forwardFrom y 0).IsPositivelyOriented :=
  ⟨0, by
    show y + InfiniteLattice.axisStep a 0 - y = _
    abel⟩
section Average
variable {L : ℕ} {a a' : ℝ}
theorem complexSmoothing_of_positive (V : InfiniteLattice.Link a' → ComplexMatrix2)
    {c : InfiniteLattice.Link a} (hc : c.IsPositivelyOriented) :
    complexSmoothing L V c = complexSmoothingPositive L V c := by
  unfold complexSmoothing
  exact if_pos hc
theorem complexSmoothing_of_not_positive (V : InfiniteLattice.Link a' → ComplexMatrix2)
    {c : InfiniteLattice.Link a} (hc : ¬ c.IsPositivelyOriented) :
    complexSmoothing L V c = (complexSmoothingPositive L V c.opposite)⁻¹ := by
  unfold complexSmoothing
  exact if_neg hc
end Average
theorem smoothingAnalyticCovariant_of_lt (hR : AdmissiblePolydiscRadiusExists)
    (hF : SublatticesSymmetriesScalingsAndProjections.Statement)
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {k j : ℕ} (hjk : j < k) :
    SmoothingAnalyticCovariant L k j := by
  obtain ⟨ρ, hρ⟩ := hR L hL
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have ha : 0 < meshAt L k j := by
    unfold meshAt
    exact zpow_pos (by exact_mod_cast hL0) _
  have hk : 1 ≤ k := by omega
  have Q : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented → ProjPreservesStructures L 1 k j c :=
    fun c hc => ((hF L hL0 hL k).2.2.2.2.2.2 hk 1 one_pos).2 j hjk c hc
  have S : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented → PolydiscIsAdmissible L k j ρ c :=
    fun c hc => hρ.fullSpace k j hjk c hc
  have hsym : ∀ c : Edge L k (j + 1), ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
      b.opposite ∈ doubleCubeLinks L (meshAt L k j) c :=
    fun c b hb => ⟨hb.2, hb.1⟩
  have hnorm : ∀ V : Edge L k j → ComplexMatrix2, supDistOne V < ENNReal.ofReal ρ →
      ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ := fun V hd b => by
    have h : ENNReal.ofReal (ComplexMatrix2.operatorNorm (V b - 1)) < ENNReal.ofReal ρ :=
      lt_of_le_of_lt (le_iSup (fun b => ENNReal.ofReal (ComplexMatrix2.operatorNorm (V b - 1))) b) hd
    exact (ENNReal.ofReal_lt_ofReal_iff hρ.pos).1 h
  have hpoly : ∀ V ∈ smoothingDomain L k j, supDistOne V < ENNReal.ofReal ρ →
      ∀ c : Edge L k (j + 1), V ∈ nearIdentityPolydisc L k j ρ c :=
    fun V hV hd c => ⟨⟨fun b _ => su_det_eq_one (hV.1.1 b), fun b _ => hV.1.2 b⟩,
      fun b _ => hnorm V hd b⟩
  have hDP : ∀ c : Edge L k (j + 1),
      smoothingBall L k j ρ ⊆ nearIdentityPolydisc L k j ρ c :=
    fun c V hV => hpoly V hV.1 hV.2 c
  have hDG : ∀ V ∈ smoothingBall L k j ρ, ∀ b,
      V b ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) :=
    fun V hV b => hV.1.1.1 b
  have smoothingAnalytic : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
      IsAnalyticInFinitelyManyLinks (smoothingBall L k j ρ)
        fun V => complexSmoothing L V c := fun c hc =>
    analyticInFinitelyManyLinks_of_polydisc (P := nearIdentityPolydisc L k j ρ c)
      (Φ := fun V => complexSmoothing L V c) ha (hsym c) (fun _ => Iff.rfl)
      (S c hc).holomorphic_smoothing.1
      (fun V hV V' hV' h => by
        rw [(Q c hc).complexSmoothing_eq V ((S c hc).subset_complexDomain hV),
          (Q c hc).complexSmoothing_eq V' ((S c hc).subset_complexDomain hV'),
          projField_congr _ h])
      (hDP c) hDG
  have mainContour : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented → ∀ y : Vertex L k (j + 1),
      y = c.initial → ∀ x : Vertex L k j, x ∈ cubeVertices L (meshAt L k j) y →
      IsAnalyticInFinitelyManyLinks (smoothingBall L k j ρ)
        fun V => complexContourMean L V y x := fun c hc y hy x hx =>
    analyticInFinitelyManyLinks_of_polydisc (P := nearIdentityPolydisc L k j ρ c)
      (Φ := fun V => complexContourMean L V y x) ha (hsym c) (fun _ => Iff.rfl)
      ((S c hc).holomorphic_contourMean y (Or.inl hy) x hx).1
      (fun V hV V' hV' h => by
        rw [(Q c hc).complexContourMean_eq V ((S c hc).subset_complexDomain hV) y (Or.inl hy) x hx,
          (Q c hc).complexContourMean_eq V' ((S c hc).subset_complexDomain hV') y (Or.inl hy) x hx,
          projField_congr _ h])
      (hDP c) hDG
  refine ⟨⟨ρ, hρ.pos, ?_, ?_⟩, ρ, hρ.pos, ?_⟩
  · intro b
    by_cases hb : b.IsPositivelyOriented
    · exact smoothingAnalytic b hb
    · have hr := opposite_isPositivelyOriented hb
      have heq : (fun V => smoothingMap L k j V b) =
          fun V => (complexSmoothing L V b.opposite)⁻¹ := by
        funext V
        show complexSmoothing L V b = _
        rw [complexSmoothing_of_not_positive V hb, complexSmoothing_of_positive V hr]
      show IsAnalyticInFinitelyManyLinks _ fun V => smoothingMap L k j V b
      rw [heq]
      refine analyticInFinitelyManyLinks_inv (smoothingAnalytic _ hr) fun V hV => ?_
      rw [complexSmoothing_of_positive V hr]
      exact su_det_eq_one (hV.1.2 _ hr).2
  · rintro ⟨y, x⟩
    exact mainContour (InfiniteLattice.Link.forwardFrom y 0)
      (forwardFrom_zero_isPositivelyOriented y) y rfl x.1 x.2
  · intro V hV hd u hu
    have hpV := hpoly V hV hd
    have hu' : ∀ x, restrictVertexFunction (meshAt L k (j + 1)) u x ∈
        (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) :=
      fun x => hu _
    have cov := fun (c : Edge L k (j + 1)) (hc : c.IsPositivelyOriented) =>
      (S c hc).gauge_covariant V (hpV c) u hu
    refine ⟨⟨⟨fun b => ?_, fun b => ?_⟩, fun c hc => ⟨(cov c hc).1, ?_⟩⟩, ?_, ?_⟩
    · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hu _) (hV.1.1 b)) (su_inv_mem (hu _))
    · show u b.terminal * V b.opposite * (u b.initial)⁻¹ = (u b.initial * V b * (u b.terminal)⁻¹)⁻¹
      rw [hV.1.2 b, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        inv_inv_of_det_eq_one (su_det_eq_one (hu _)), mul_assoc]
    · rw [← complexSmoothing_of_positive _ hc, (cov c hc).2.1]
      show restrictVertexFunction (meshAt L k (j + 1)) u c.initial * complexSmoothing L V c *
        (restrictVertexFunction (meshAt L k (j + 1)) u c.terminal)⁻¹ ∈ _
      rw [complexSmoothing_of_positive V hc]
      exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hu' _) (hV.2 c hc).2) (su_inv_mem (hu' _))
    · funext b
      by_cases hb : b.IsPositivelyOriented
      · exact (cov b hb).2.1
      · have hr := opposite_isPositivelyOriented hb
        show complexSmoothing L (gaugeAct u V) b =
          restrictVertexFunction (meshAt L k (j + 1)) u b.initial * complexSmoothing L V b *
            (restrictVertexFunction (meshAt L k (j + 1)) u b.terminal)⁻¹
        rw [complexSmoothing_of_not_positive _ hb, complexSmoothing_of_not_positive V hb,
          ← complexSmoothing_of_positive _ hr, (cov _ hr).2.1]
        show (restrictVertexFunction (meshAt L k (j + 1)) u b.terminal *
            complexSmoothing L V b.opposite *
            (restrictVertexFunction (meshAt L k (j + 1)) u b.initial)⁻¹)⁻¹ = _
        rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_inv_of_det_eq_one (su_det_eq_one (hu' _)),
          complexSmoothing_of_positive V hr, mul_assoc]
    · intro y x hx
      exact (cov _ (forwardFrom_zero_isPositivelyOriented y)).2.2 y (Or.inl rfl) x hx
theorem allStepsSmoothingAnalyticCovariant (hR : AdmissiblePolydiscRadiusExists)
    (hF : SublatticesSymmetriesScalingsAndProjections.Statement) :
    AllStepsSmoothingAnalyticCovariant := by apply _root_.YangMills.Construction.Tower.FullSpace.SmoothingAnalyticCovariantProof.smoothingAnalyticCovariant_of_lt <;> assumption
end YangMills.Construction.Tower.FullSpace.SmoothingAnalyticCovariantProof
end
