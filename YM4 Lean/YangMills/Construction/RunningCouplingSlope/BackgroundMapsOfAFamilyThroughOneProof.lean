import YangMills.Construction.FormOnAFibre.SiteFormsAtAFiniteSideAreEuclidean
import YangMills.Construction.Lattice.LatticeFieldOperations
import YangMills.Construction.RunningCouplingSlope.BackgroundMapsOfAFamilyThroughOne
import YangMills.Construction.RunningCouplingSlope.FieldsOfAFamilyThroughOne
import YangMills.Construction.RunningCouplingSlope.PlainIteratesAreHolomorphicAtARadiusProof
import YangMills.Construction.RunningCouplingSlope.TheGaugeShiftReadsNearCellsProof
import YangMills.Construction.Towers.EntriesOfTheBackgroundDeterminantsAreRealAnalyticProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Set Filter
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.AnalyticGaugeMaps
open YangMills.Construction.Matrices
section AnalyticFunctions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p₀ : E}
private theorem analyticAt_clm {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (T : X →L[ℂ] Y) {g : E → X}
    (h : AnalyticAt ℝ g p₀) : AnalyticAt ℝ (fun p => T (g p)) p₀ :=
  ((T.restrictScalars ℝ).analyticAt (g p₀)).comp h
private theorem analyticAt_finset_sum {α X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (s : Finset α) {f : α → E → X} (h : ∀ a ∈ s, AnalyticAt ℝ (f a) p₀) :
    AnalyticAt ℝ (fun p => ∑ a ∈ s, f a p) p₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using analyticAt_const
  | insert a s ha ih =>
    have h₁ := (h a (Finset.mem_insert_self a s)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
    refine h₁.congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply, Finset.sum_insert ha]
private def entryCLM (r s : Fin 2) : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ r s)
private theorem analyticAt_inv {g : E → ComplexMatrix2} (h : AnalyticAt ℝ g p₀)
    (h0 : (g p₀).det ≠ 0) : AnalyticAt ℝ (fun p => (g p)⁻¹) p₀ := by apply _root_.YangMills.SharedProofs.p24898 <;> assumption
private theorem analyticAt_conjugateBy {g g' : E → ComplexMatrix2} (h : AnalyticAt ℝ g p₀)
    (h' : AnalyticAt ℝ g' p₀) (h0 : (g p₀).det ≠ 0) :
    AnalyticAt ℝ (fun p => ComplexMatrix2.conjugateBy (g p) (g' p)) p₀ :=
  (h.mul h').mul (analyticAt_inv h h0)
private theorem analyticAt_comp_family {τ Y : Type} [Fintype τ] [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] {Ψ : E → τ → ComplexMatrix2}
    (hΨ : ∀ i, AnalyticAt ℝ (fun p => Ψ p i) p₀) {D : Set (τ → ComplexMatrix2)}
    (hD : ∀ᶠ p in 𝓝 p₀, Ψ p ∈ D) {φ G : (τ → ComplexMatrix2) → Y}
    (hG : AnalyticAt ℂ G (Ψ p₀)) (hGev : ∀ᶠ y in 𝓝[D] (Ψ p₀), φ y = G y) :
    AnalyticAt ℝ (fun p => φ (Ψ p)) p₀ := by
  have hvec : AnalyticAt ℝ Ψ p₀ := AnalyticAt.pi hΨ
  have htend : Tendsto Ψ (𝓝 p₀) (𝓝[D] (Ψ p₀)) :=
    tendsto_nhdsWithin_iff.2 ⟨hvec.continuousAt.tendsto, hD⟩
  refine ((hG.restrictScalars (𝕜 := ℝ)).comp hvec).congr ?_
  filter_upwards [htend.eventually hGev] with p h using h.symm
private def halfTraceCLM : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := ComplexMatrix2.halfTrace
      map_add' := fun X Y => by
        simp [ComplexMatrix2.halfTrace, Finset.sum_add_distrib, mul_add]
      map_smul' := fun c X => by
        simp [ComplexMatrix2.halfTrace, Finset.mul_sum]
        ring }
private theorem analyticAt_re_pairing {ι : Type} [Finite ι] {f g : E → ι → ComplexMatrix2}
    (hf : ∀ i, AnalyticAt ℝ (fun p => f p i) p₀) (hg : ∀ i, AnalyticAt ℝ (fun p => g p i) p₀) :
    AnalyticAt ℝ (fun p => (Tower.traceFinsumPairing (f p) (g p)).re) p₀ := by
  letI := Fintype.ofFinite ι
  have h₁ : AnalyticAt ℝ
      (fun p => ∑ i, (ComplexMatrix2.halfTrace (f p i * g p i)).re) p₀ :=
    analyticAt_finset_sum Finset.univ fun i _ =>
      (Complex.reCLM.analyticAt _).comp (analyticAt_clm halfTraceCLM ((hf i).mul (hg i)))
  refine h₁.congr (Eventually.of_forall fun p => ?_)
  show _ = (∑ᶠ i, ComplexMatrix2.halfTrace (f p i * g p i)).re
  rw [finsum_eq_sum_of_fintype, Complex.re_sum]
end AnalyticFunctions
private theorem exists_orthonormal_expansion {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (c : InnerProductSpace.Core ℝ V) :
    ∃ (d : ℕ) (e : Fin d → V), ∀ x : V, x = ∑ a, c.inner (e a) x • e a := by
  letI := c.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c.toCore
  exact ⟨_, stdOrthonormalBasis ℝ V, fun x => ((stdOrthonormalBasis ℝ V).sum_repr' x).symm⟩
private theorem core_inner_comm {V : Type} [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V) (x y : V) : c.inner x y = c.inner y x := by
  simpa using c.conj_inner_symm y x
private theorem coe_orthonormal_expansion {α : Type} {p : Submodule ℝ (α → ComplexMatrix2)}
    {d : ℕ} (c : InnerProductSpace.Core ℝ p) {e : Fin d → p}
    (h : ∀ x : p, x = ∑ a, c.inner (e a) x • e a) (x : p) :
    (x : α → ComplexMatrix2) = ∑ a, c.inner (e a) x • (e a : α → ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.BackgroundDeterminants.coe_eq_sum_inner_smul <;> assumption
section StepOfTower
variable {L n k j : ℕ}
private structure StepData (L n k j : ℕ) : Prop where
  finite_edges : Finite (Tower.Edge L n k j)
  finite_upper : Finite (Tower.Edge L n k (j + 1))
  finite_vertices : Finite (Tower.Vertex L n k j)
  xor_opposite : ∀ b : Tower.Edge L n k (j + 1),
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  admissible : ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
    Tower.PolydiscIsAdmissible (Tower.polydiscRadius L) c
  contour_local : ∀ (y : Tower.Vertex L n k (j + 1)),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
    ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
    y ∈ ({c.source, c.target} : Set (Tower.Vertex L n k (j + 1))) →
    ∀ W : Tower.Edge L n k j → ComplexMatrix2,
    PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ W →
    (∀ b, ComplexMatrix2.operatorNorm (W b - 1) < Tower.polydiscRadius L) →
    ∀ W' : Tower.Edge L n k j → ComplexMatrix2,
      (∀ b ∈ Tower.DoubleBlockPolydisc.doubleBlockBonds c, W' b = W b) →
        PeriodicLattice.complexMeanContourHolonomy W' y x =
          PeriodicLattice.complexMeanContourHolonomy W y x
  average_local : ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
    ∀ W W' : Tower.Edge L n k j → ComplexMatrix2,
    (∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Tower.Edge L n k j)), W' b = W b) →
      PeriodicLattice.complexBlockAverage W' c = PeriodicLattice.complexBlockAverage W c
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p₀ : E}
private structure IsAdmissibleFamily (V : E → Tower.Edge L n k j → ComplexMatrix2) (p₀ : E) :
    Prop where
  analytic : ∀ b, AnalyticAt ℝ (fun p => V p b) p₀
  near_one : ∀ b, ComplexMatrix2.operatorNorm (V p₀ b - 1) < Tower.polydiscRadius L
  mem_fields : ∀ᶠ p in 𝓝 p₀, V p ∈ Tower.fieldsIn L n k j PeriodicLattice.complexGaugeGroup
variable {V : E → Tower.Edge L n k j → ComplexMatrix2}
private theorem IsAdmissibleFamily.eventually_near_one (T : StepData L n k j)
    (hV : IsAdmissibleFamily V p₀) :
    ∀ᶠ p in 𝓝 p₀, ∀ b, ComplexMatrix2.operatorNorm (V p b - 1) < Tower.polydiscRadius L := by
  have := T.finite_edges
  refine eventually_all.2 fun b => ?_
  have h₁ : Tendsto (fun p => ‖V p b - 1‖) (𝓝 p₀) (𝓝 ‖V p₀ b - 1‖) :=
    ((hV.analytic b).continuousAt.tendsto.sub_const 1).norm
  exact h₁.eventually_lt_const (hV.near_one b)
private theorem extendFromPositive_restrict {ℬ : Set (Tower.Edge L n k j)}
    (hℬ : ∀ b ∈ ℬ, b.opposite ∈ ℬ) {W : Tower.Edge L n k j → ComplexMatrix2}
    (hW : ∀ b : Tower.Edge L n k j, W b.opposite = (W b)⁻¹) (b : Tower.Edge L n k j)
    (hb : b ∈ ℬ) :
    PeriodicLattice.extendFromPositive ℬ (PeriodicLattice.restrictToPositive ℬ W) b = W b := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.extendFromPositive_restrict_eq <;> assumption
private theorem IsAdmissibleFamily.analyticAt_of_local (T : StepData L n k j)
    (hV : IsAdmissibleFamily V p₀)
    {c : Tower.Edge L n k (j + 1)} {Φ : (Tower.Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : PeriodicLattice.IsHolomorphicOnFields
      (PeriodicLattice.bondsInDoubleBlock c : Set (Tower.Edge L n k j))
      (Tower.nearIdentityPolydisc (Tower.polydiscRadius L) c) Φ)
    (hread : ∀ W : Tower.Edge L n k j → ComplexMatrix2,
      PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ W →
      (∀ b, ComplexMatrix2.operatorNorm (W b - 1) < Tower.polydiscRadius L) →
      ∀ W' : Tower.Edge L n k j → ComplexMatrix2,
        (∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Tower.Edge L n k j)), W' b = W b) →
          Φ W' = Φ W) :
    AnalyticAt ℝ (fun p => Φ (V p)) p₀ ∧
      ∀ᶠ p in 𝓝 p₀, Φ (V p) ∈ PeriodicLattice.complexGaugeGroup := by
  classical
  obtain ⟨inst, hol⟩ := hΦ.1
  have hclosed : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Tower.Edge L n k j)),
      b.opposite ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Tower.Edge L n k j)) :=
    fun b hb => ⟨hb.2, hb.1⟩
  have hpoly : ∀ W ∈ Tower.fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ b, ComplexMatrix2.operatorNorm (W b - 1) < Tower.polydiscRadius L) →
        W ∈ Tower.nearIdentityPolydisc (Tower.polydiscRadius L) c := by
    intro W hW hn
    have hW' : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ W := hW
    exact ⟨⟨fun b _ => hW'.1 b (mem_univ b), fun b _ => hW'.2 b (mem_univ b)⟩, fun b _ => hn b⟩
  have hD : ∀ᶠ p in 𝓝 p₀, PeriodicLattice.restrictToPositive
      (PeriodicLattice.bondsInDoubleBlock c : Set (Tower.Edge L n k j)) (V p) ∈
      PeriodicLattice.restrictToPositive
        (PeriodicLattice.bondsInDoubleBlock c : Set (Tower.Edge L n k j)) ''
        Tower.nearIdentityPolydisc (Tower.polydiscRadius L) c := by
    filter_upwards [hV.mem_fields, hV.eventually_near_one T] with p h₁ h₂
    exact ⟨_, hpoly _ h₁ h₂, rfl⟩
  have h0 := hD.self_of_nhds
  obtain ⟨G, hG, hGev⟩ := hol.2.2 _ h0
  have hfam := analyticAt_comp_family (p₀ := p₀)
    (Ψ := fun p => PeriodicLattice.restrictToPositive
      (PeriodicLattice.bondsInDoubleBlock c : Set (Tower.Edge L n k j)) (V p))
    (fun i => hV.analytic i.1) hD hG hGev
  have hone := analyticAt_clm
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Unit => ComplexMatrix2) ()) hfam
  have hread' : ∀ᶠ p in 𝓝 p₀, Φ (PeriodicLattice.extendFromPositive
        (PeriodicLattice.bondsInDoubleBlock c : Set (Tower.Edge L n k j))
        (PeriodicLattice.restrictToPositive
          (PeriodicLattice.bondsInDoubleBlock c : Set (Tower.Edge L n k j)) (V p))) =
        Φ (V p) := by
    filter_upwards [hV.mem_fields, hV.eventually_near_one T] with p h₁ h₂
    have h₁' : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ (V p) := h₁
    exact hread _ h₁' h₂ _
      fun b hb => extendFromPositive_restrict hclosed (fun b => h₁'.2 b (mem_univ b)) b hb
  refine ⟨hone.congr hread', ?_⟩
  filter_upwards [hD, hread'] with p h₁ h₂
  have h := hol.2.1 h₁ ()
  rw [← h₂]
  exact h
private theorem IsAdmissibleFamily.analyticAt_contour (T : StepData L n k j)
    (hV : IsAdmissibleFamily V p₀) (y : Tower.Vertex L n k (j + 1)) {x : Tower.Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    AnalyticAt ℝ (fun p => PeriodicLattice.complexMeanContourHolonomy (V p) y x) p₀ ∧
      ∀ᶠ p in 𝓝 p₀, PeriodicLattice.complexMeanContourHolonomy (V p) y x ∈
        PeriodicLattice.complexGaugeGroup := by
  have hc : (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented :=
    ⟨0, add_sub_cancel_left _ _⟩
  have hy : y ∈ ({(PeriodicLattice.Bond.forwardFrom y 0).source,
      (PeriodicLattice.Bond.forwardFrom y 0).target} : Set (Tower.Vertex L n k (j + 1))) :=
    Or.inl rfl
  exact hV.analyticAt_of_local T ((T.admissible _ hc).holomorphic_contourMean y hy x hx)
    fun W hW hn W' he => T.contour_local y x hx _ hc hy W hW hn W' he
private theorem IsAdmissibleFamily.analyticAt_average (T : StepData L n k j)
    (hV : IsAdmissibleFamily V p₀) {c : Tower.Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    AnalyticAt ℝ (fun p => PeriodicLattice.complexBlockAverage (V p) c) p₀ ∧
      ∀ᶠ p in 𝓝 p₀, PeriodicLattice.complexBlockAverage (V p) c ∈
        PeriodicLattice.complexGaugeGroup :=
  hV.analyticAt_of_local T (T.admissible c hc).holomorphic_smoothing
    fun W _ _ W' he => T.average_local c hc W W' he
private theorem inv_mem_unitDeterminant {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.unitDeterminant) : g⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
private theorem inv_inv_of_mem_unitDeterminant {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.unitDeterminant) : (g⁻¹)⁻¹ = g := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
private theorem det_of_mem_complexGaugeGroup {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.complexGaugeGroup) : g.det = 1 := hg
private theorem complexBlockAverage_of_positive {W : Tower.Edge L n k j → ComplexMatrix2}
    {c : Tower.Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverage W c =
      PeriodicLattice.complexBlockAverageOnPositive W c :=
  if_pos hc
private theorem complexBlockAverage_of_not_positive {W : Tower.Edge L n k j → ComplexMatrix2}
    {c : Tower.Edge L n k (j + 1)} (hc : ¬ c.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverage W c =
      (PeriodicLattice.complexBlockAverageOnPositive W c.opposite)⁻¹ :=
  if_neg hc
private theorem IsAdmissibleFamily.next (T : StepData L n k j) (hV : IsAdmissibleFamily V p₀)
    (hnear : ∀ b : Tower.Edge L n k (j + 1),
      ComplexMatrix2.operatorNorm (PeriodicLattice.complexBlockAverage (V p₀) b - 1) <
        Tower.polydiscRadius L) :
    IsAdmissibleFamily
      (fun p => (PeriodicLattice.complexBlockAverage (V p) :
        Tower.Edge L n k (j + 1) → ComplexMatrix2)) p₀ := by
  refine ⟨fun c => ?_, hnear, ?_⟩
  · by_cases hc : c.IsPositivelyOriented
    · exact (hV.analyticAt_average T hc).1
    · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive c).resolve_left hc
      obtain ⟨h₁, h₂⟩ := hV.analyticAt_average T hr
      refine (analyticAt_inv h₁ ?_).congr (Eventually.of_forall fun p => ?_)
      · rw [det_of_mem_complexGaugeGroup h₂.self_of_nhds]
        exact one_ne_zero
      · show (PeriodicLattice.complexBlockAverage (V p) c.opposite)⁻¹ =
          PeriodicLattice.complexBlockAverage (V p) c
        rw [complexBlockAverage_of_positive hr, complexBlockAverage_of_not_positive hc]
  · have := T.finite_upper
    have hall : ∀ᶠ p in 𝓝 p₀, ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
        PeriodicLattice.complexBlockAverage (V p) c ∈ PeriodicLattice.complexGaugeGroup :=
      eventually_all.2 fun c => by
        by_cases hc : c.IsPositivelyOriented
        · filter_upwards [(hV.analyticAt_average T hc).2] with p h _ using h
        · exact Eventually.of_forall fun p h => absurd h hc
    filter_upwards [hall] with p h
    refine ⟨fun c _ => ?_, fun c _ => ?_⟩
    · by_cases hc : c.IsPositivelyOriented
      · exact h c hc
      · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive c).resolve_left hc
        have h₂ := h _ hr
        rw [complexBlockAverage_of_positive hr] at h₂
        rw [complexBlockAverage_of_not_positive hc]
        exact inv_mem_unitDeterminant h₂
    · by_cases hc : c.IsPositivelyOriented
      · have hnr : ¬ c.opposite.IsPositivelyOriented := fun hr => ((T.xor_opposite c).elim
          (fun q => q.2 hr) (fun q => q.2 hc))
        rw [complexBlockAverage_of_not_positive hnr, PeriodicLattice.Bond.opposite_opposite,
          complexBlockAverage_of_positive hc]
      · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive c).resolve_left hc
        have h₂ := h _ hr
        rw [complexBlockAverage_of_positive hr] at h₂
        rw [complexBlockAverage_of_positive hr, complexBlockAverage_of_not_positive hc,
          inv_inv_of_mem_unitDeterminant h₂]
private theorem IsAdmissibleFamily.analyticAt_adjointCubeAverage (T : StepData L n k j)
    (hV : IsAdmissibleFamily V p₀) {l : E → Tower.Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, AnalyticAt ℝ (fun p => l p x) p₀) (y : Tower.Vertex L n k (j + 1)) :
    AnalyticAt ℝ (fun p => Tower.adjointCubeAverage (V p) (l p) y) p₀ := by
  have := T.finite_vertices
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Tower.Vertex L n k j)).Finite := Set.toFinite _
  unfold Tower.adjointCubeAverage
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hs : AnalyticAt ℝ (fun p => ∑ x ∈ hfin.toFinset,
      ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy (V p) y x)
        (l p x)) p₀ := by
    refine analyticAt_finset_sum _ fun x hx => ?_
    obtain ⟨h₁, h₂⟩ := hV.analyticAt_contour T y (hfin.mem_toFinset.1 hx)
    refine analyticAt_conjugateBy h₁ (hl x) ?_
    rw [det_of_mem_complexGaugeGroup h₂.self_of_nhds]
    exact one_ne_zero
  have hw : AnalyticAt ℝ
      (fun _ : E => (PeriodicLattice.inverseFourthPowerWeight L : ℂ)) p₀ := analyticAt_const
  exact hw.smul hs
end StepOfTower
section ChainsOfAverages
variable {L n k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p₀ : E}
private theorem admissible_iterates (F : ∀ j < k, StepData L n k j)
    {U : E → Tower.Edge L n k 0 → ComplexMatrix2} (hU : IsAdmissibleFamily U p₀)
    (hnear : ∀ j ≤ k, ∀ b : Tower.Edge L n k j,
      ComplexMatrix2.operatorNorm (PeriodicLattice.complexBlockFieldAtLevel j (U p₀) b - 1) <
        Tower.polydiscRadius L) :
    ∀ j ≤ k, IsAdmissibleFamily
      (fun p => (PeriodicLattice.complexBlockFieldAtLevel j (U p) :
        Tower.Edge L n k j → ComplexMatrix2)) p₀ := by
  intro j
  induction j with
  | zero => exact fun _ => hU
  | succ j ih =>
    intro hj
    exact (ih (by omega)).next (F j (by omega)) (hnear (j + 1) hj)
private theorem analyticAt_iterAdjointCubeAverage (F : ∀ j < k, StepData L n k j)
    {U : E → Tower.Edge L n k 0 → ComplexMatrix2}
    (hg : ∀ j ≤ k, IsAdmissibleFamily
      (fun p => (PeriodicLattice.complexBlockFieldAtLevel j (U p) :
        Tower.Edge L n k j → ComplexMatrix2)) p₀)
    {l : E → Tower.Vertex L n k 0 → ComplexMatrix2}
    (hl : ∀ x, AnalyticAt ℝ (fun p => l p x) p₀) :
    ∀ j ≤ k, ∀ y : Tower.Vertex L n k j,
      AnalyticAt ℝ (fun p => Tower.iterAdjointCubeAverage L n k (U p) j (l p) y) p₀ := by
  intro j
  induction j with
  | zero => exact fun _ y => hl y
  | succ j ih =>
    intro hj y
    exact (hg j (by omega)).analyticAt_adjointCubeAverage (F j (by omega)) (ih (by omega)) y
private theorem analyticAt_composedCubeAverage (F : ∀ j < k, StepData L n k j)
    {X : E → RunningCouplingSlope.ChainPoint L n k}
    (hg : ∀ j ≤ k, IsAdmissibleFamily (fun p => RunningCouplingSlope.levelField (X p) j) p₀)
    (l : Tower.Vertex L n k 0 → ComplexMatrix2) :
    ∀ j ≤ k, ∀ y : Tower.Vertex L n k j,
      AnalyticAt ℝ (fun p => RunningCouplingSlope.composedCubeAverage (X p) j l y) p₀ := by
  intro j
  induction j with
  | zero => exact fun _ y => analyticAt_const
  | succ j ih =>
    intro hj y
    exact (hg j (by omega)).analyticAt_adjointCubeAverage (F j (by omega)) (ih (by omega)) y
private theorem analyticAt_covDiff {j : ℕ} {U : E → Tower.Edge L n k j → ComplexMatrix2}
    (hU : ∀ b, AnalyticAt ℝ (fun p => U p b) p₀) (hdet : ∀ b, (U p₀ b).det ≠ 0)
    (l : Tower.Vertex L n k j → ComplexMatrix2) (b : Tower.Edge L n k j) :
    AnalyticAt ℝ (fun p => Tower.covDiff (U p) l b) p₀ := by
  classical
  have h : ∀ b : Tower.Edge L n k j, AnalyticAt ℝ
      (fun p => ComplexMatrix2.conjugateBy (U p b) (l b.target) - l b.source) p₀ := fun b =>
    (analyticAt_conjugateBy (hU b) analyticAt_const (hdet b)).sub analyticAt_const
  by_cases hb : b.IsPositivelyOriented
  · refine (h b).congr (Eventually.of_forall fun p => ?_)
    simp [Tower.covDiff, Tower.extendOddly, if_pos hb]
  · refine (h b.opposite).neg.congr (Eventually.of_forall fun p => ?_)
    simp [Tower.covDiff, Tower.extendOddly, if_neg hb]
private theorem tendsto_nhdsWithin_one {ι : Type} {V : E → ι → ComplexMatrix2}
    (hV : ∀ b, ContinuousAt (fun p => V p b) p₀) (h1 : ∀ b, V p₀ b = 1)
    {D : Set (ι → ComplexMatrix2)} (hD : ∀ᶠ p in 𝓝 p₀, V p ∈ D) :
    Tendsto V (𝓝 p₀) (𝓝[D] fun _ => (1 : ComplexMatrix2)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun b => ?_, hD⟩
  have h := (hV b).tendsto
  rwa [h1 b] at h
private theorem composedCubeAverage_linear
    (hY : ∀ i < k, Tower.RealLinearMaps.StepLinearity L n k i)
    {X : E → RunningCouplingSlope.ChainPoint L n k}
    (hW : ∀ j < k, Tendsto (fun p => RunningCouplingSlope.levelField (X p) j) (𝓝 p₀)
      (𝓝[Tower.fieldSpace L n k j] fun _ => (1 : ComplexMatrix2))) :
    ∀ j ≤ k, ∀ᶠ p in 𝓝 p₀,
      ∃ T : Tower.vertexFunctionSpace L n k 0 →ₗ[ℝ] Tower.vertexFunctionSpace L n k j,
      ∀ l : Tower.vertexFunctionSpace L n k 0, (T l : Tower.Vertex L n k j → ComplexMatrix2) =
        RunningCouplingSlope.composedCubeAverage (X p) j (l : Tower.Vertex L n k 0 → ComplexMatrix2) := by
  intro j
  induction j with
  | zero => exact fun _ => Eventually.of_forall fun p => ⟨LinearMap.id, fun l => rfl⟩
  | succ j ih =>
    intro hj
    have h₁ := (hW j (by omega)).eventually (hY j (by omega)).adjointCubeAverage_isLinear
    filter_upwards [ih (by omega), h₁] with p h₂ h₃
    obtain ⟨T, hT⟩ := h₂
    obtain ⟨T', hT'⟩ := h₃
    refine ⟨T' ∘ₗ T, fun l => ?_⟩
    show (T' (T l) : Tower.Vertex L n k (j + 1) → ComplexMatrix2) =
      Tower.adjointCubeAverage (RunningCouplingSlope.levelField (X p) j)
        (RunningCouplingSlope.composedCubeAverage (X p) j l)
    rw [hT', hT]
private theorem iterAdjointCubeAverage_linear (hY : Tower.RealLinearMaps.RealLinearMapsStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    Tower.EventuallyNearIdentity (Tower.fieldSpace L n k 0) fun U =>
      ∃ T : Tower.vertexFunctionSpace L n k 0 →ₗ[ℝ] Tower.vertexFunctionSpace L n k k,
      ∀ l : Tower.vertexFunctionSpace L n k 0,
        (T l : Tower.Vertex L n k k → ComplexMatrix2) =
          Tower.iterAdjointCubeAverage L n k U k (l : Tower.Vertex L n k 0 → ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.BackgroundDeterminants.iterAverage_eventually_linear <;> assumption
private theorem linearMapWithValues_apply {α β : Type*} {p : Submodule ℝ (α → ComplexMatrix2)}
    {p' : Submodule ℝ (β → ComplexMatrix2)} {f : (α → ComplexMatrix2) → β → ComplexMatrix2}
    (h : ∃ T : p →ₗ[ℝ] p', ∀ x : p, (T x : β → ComplexMatrix2) = f x) (x : p) :
    (Tower.linearMapWithValues p p' f x : β → ComplexMatrix2) = f x := by apply _root_.YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide.linearMapWithValues_apply <;> assumption
private theorem remainderGaugeField_zero :
    Tower.remainderGaugeField (0 : Tower.Edge L n k 0 → ComplexMatrix2) = fun _ => 1 := by
  funext b
  simp only [Tower.remainderGaugeField, IdentityExpChart.expForm,
    Tower.scaledRemainderForm, smul_zero]
  unfold PeriodicLattice.expTwist
  split_ifs <;> simp [ComplexMatrix2.matExp]
private theorem operatorNorm_one_sub_one :
    ComplexMatrix2.operatorNorm ((1 : ComplexMatrix2) - 1) = 0 := by
  rw [sub_self]
  exact norm_zero (E := ComplexMatrix2)
private theorem complexBlockFieldAtLevel_one_near
    (hIt : Tower.IteratedSmallFieldMeans.IteratedMeansClaim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    (hr : 0 < Tower.polydiscRadius L) (j : ℕ) (hj : j ≤ k) (b : Tower.Edge L n k j) :
    ComplexMatrix2.operatorNorm
      (PeriodicLattice.complexBlockFieldAtLevel j (fun _ => (1 : ComplexMatrix2)) b - 1) <
      Tower.polydiscRadius L := by
  obtain ⟨hρ, -, -, hall⟩ := hIt.1 L hL
  have h0 : (0 : Tower.Edge L n k 0 → ComplexMatrix2) ∈
      Tower.IteratedSmallFieldMeans.smallFormBall L n k
        (Tower.IteratedSmallFieldMeans.smallRadius L) := by
    refine ⟨(Tower.complexEdgeForms L n k 0).zero_mem, ?_⟩
    refine iSup_le fun b => ?_
    have h : ComplexMatrix2.operatorNorm ((0 : Tower.Edge L n k 0 → ComplexMatrix2) b) = 0 :=
      norm_zero (E := ComplexMatrix2)
    rw [h, ENNReal.ofReal_zero]
    exact zero_le
  have h := (((hall k hk).1 n hn).pointwise 0 h0).norm_sub_one_lt_half j hj b
  unfold Tower.IteratedSmallFieldMeans.meanIterate at h
  rw [remainderGaugeField_zero] at h
  linarith
end ChainsOfAverages
theorem gaugeMapsAnalyticAlongFamily_holds
    (hFields : RunningCouplingSlope.LevelFieldsAnalyticAlongFamily)
    (hAvg : Tower.SmoothingNearIdentity)
    (hCont : Tower.PairContourIndependence.Statement)
    (hR : PeriodicLattice.ComplexAverageIsLocal)
    (hIt : Tower.IteratedSmallFieldMeans.IteratedMeansClaim)
    (hY : Tower.RealLinearMaps.RealLinearMapsStatement)
    (hQ : Tower.RealQuadraticTransposes.Statement)
    (hSite : FormOnAFibre.VertexFunctionsAreEuclidean.Statement)
    (hO : PeriodicLattice.BondEndpointsOrientation.Statement) :
    RunningCouplingSlope.GaugeMapsAnalyticAlongFamily := by
  classical
  intro L hL k n hk hn E _ _ X p₀ hX
  have hrad := (hAvg.1 L hL).2.2
  have hr : 0 < Tower.polydiscRadius L := hrad.pos
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL.2
  have hsites : ∀ j, Finite (Tower.Vertex L n k j) := fun j =>
    SeparatedSequences.BaseParameters.site_finite hLpos n _
  have hbonds : ∀ j, Finite (Tower.Edge L n k j) := fun j =>
    have := hsites j
    Finite.of_injective (fun b : Tower.Edge L n k j => (b.source, b.target)) fun b b' hb =>
      PeriodicLattice.Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  have hxor : ∀ j ≤ k, ∀ b : Tower.Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun j hj b =>
    ((hO ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj).2.2.2 b).2.2.2.2.2
  have F : ∀ j < k, StepData L n k j := fun j hj =>
    { finite_edges := hbonds j
      finite_upper := hbonds (j + 1)
      finite_vertices := hsites j
      xor_opposite := hxor (j + 1) hj
      admissible := fun c hc => hrad.periodic n k j hn hj c hc
      contour_local := fun y x hx c hc hy W hW hWn W' hr' =>
        ((hCont L hL k j hj).1 n hn y x hx c c hc hc hy hy W hW (fun b _ => hWn b)
          (fun b _ => hWn b) W' W hr' (fun _ _ => rfl)).2.2
      average_local := fun c hc W W' he => by
        rw [complexBlockAverage_of_positive hc, complexBlockAverage_of_positive hc]
        exact (hR L n k j hL.1 hL.2 hn hj c hc).average_eq _ _ he }
  obtain ⟨hF₁, -, hF₃⟩ := hFields L hL k n hk hn E X p₀ hX
  have hone : (X p₀).fine = fun _ => 1 := by rw [hX.eq_unit]; rfl
  have hconf : ∀ {j : ℕ} {W : Tower.Edge L n k j → ComplexMatrix2},
      W ∈ Tower.fieldSpace L n k j →
      W ∈ Tower.fieldsIn L n k j PeriodicLattice.complexGaugeGroup := fun {j W} h =>
    ⟨fun b hb => EquivariantMaps.compactGaugeGroup_subset_complexGaugeGroup (h.1 b hb), h.2⟩
  have hgood₀ : ∀ j ≤ k, IsAdmissibleFamily (fun p => RunningCouplingSlope.levelField (X p) j) p₀ :=
    fun j hj =>
    ⟨fun b => (hF₁ j hj b).1, fun b => by rw [(hF₁ j hj b).2, operatorNorm_one_sub_one]; exact hr,
      by filter_upwards [hF₃] with p h using hconf (h.2 j hj)⟩
  have hU : IsAdmissibleFamily (fun p => (X p).fine) p₀ := hgood₀ 0 (Nat.zero_le k)
  have hgood := admissible_iterates F hU fun j hj b => by
    rw [hone]
    exact complexBlockFieldAtLevel_one_near hIt hL hn hk hr j hj b
  have hdet : ∀ b, ((X p₀).fine b).det ≠ 0 := fun b => by
    rw [hone]
    simp
  obtain ⟨hfd, s₀, hs₀⟩ := hSite L n k 0 hL hn (Nat.zero_le k)
  haveI := hfd
  obtain ⟨d, e, he⟩ := exists_orthonormal_expansion s₀
  have hcoord : ∀ z : E → Tower.vertexFunctionSpace L n k 0,
      (∀ a, AnalyticAt ℝ (fun p =>
        (Tower.traceFinsumPairing (z p : Tower.Vertex L n k 0 → ComplexMatrix2)
          (e a : Tower.Vertex L n k 0 → ComplexMatrix2)).re) p₀) →
      ∀ x, AnalyticAt ℝ (fun p => (z p : Tower.Vertex L n k 0 → ComplexMatrix2) x) p₀ := by
    intro z hz x
    have h₁ : AnalyticAt ℝ (fun p => ∑ a,
        (Tower.traceFinsumPairing (z p : Tower.Vertex L n k 0 → ComplexMatrix2)
          (e a : Tower.Vertex L n k 0 → ComplexMatrix2)).re •
            (e a : Tower.Vertex L n k 0 → ComplexMatrix2) x) p₀ :=
      analyticAt_finset_sum Finset.univ fun a _ => (hz a).smul analyticAt_const
    refine h₁.congr (Eventually.of_forall fun p => ?_)
    have h₂ := congrFun (coe_orthonormal_expansion s₀ he (z p)) x
    simp only [Finset.sum_apply, Pi.smul_apply] at h₂
    show _ = (z p : Tower.Vertex L n k 0 → ComplexMatrix2) x
    rw [h₂]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [core_inner_comm, hs₀]
  have hUt : Tendsto (fun p => (X p).fine) (𝓝 p₀)
      (𝓝[Tower.fieldSpace L n k 0] fun _ => (1 : ComplexMatrix2)) :=
    tendsto_nhdsWithin_one (fun b => (hX.analyticAt_fine b).continuousAt)
      (fun b => congrFun hone b) (hX.eventually_compact.mono fun p h => h.1)
  have hconf₀ : ∀ᶠ p in 𝓝 p₀, (X p).fine ∈ Tower.fieldSpace L n k 0 :=
    hX.eventually_compact.mono fun p h => h.1
  have hTower := (hY L n k hL hn hk).2
  have hDlin : ∀ᶠ p in 𝓝 p₀, ∀ l : Tower.vertexFunctionSpace L n k 0,
      (Tower.covDiffLinear L n k (X p).fine l : Tower.Edge L n k 0 → ComplexMatrix2) =
        Tower.covDiff (X p).fine (l : Tower.Vertex L n k 0 → ComplexMatrix2) := by
    filter_upwards [hconf₀] with p h l
    exact linearMapWithValues_apply (hTower.covDiff_isLinear 0 (Nat.zero_le k) _ h) l
  have hDTr : ∀ᶠ p in 𝓝 p₀, ∀ (x : Tower.edgeFormSpace L n k 0)
      (l : Tower.vertexFunctionSpace L n k 0),
      Tower.traceFinsumPairing
          (Tower.covDiffRealTranspose L n k (X p).fine x : Tower.Vertex L n k 0 → ComplexMatrix2)
          (l : Tower.Vertex L n k 0 → ComplexMatrix2) =
        Tower.edgeFormPairing (x : Tower.Edge L n k 0 → ComplexMatrix2)
          (Tower.covDiffLinear L n k (X p).fine l : Tower.Edge L n k 0 → ComplexMatrix2) := by
    filter_upwards [hconf₀] with p h x l
    obtain ⟨T, -, -, -, h'⟩ := (hQ L n k hL hn hk).1 0 (Nat.zero_le k) _ h
    exact h' x l
  have hAlin : ∀ᶠ p in 𝓝 p₀, ∀ l : Tower.vertexFunctionSpace L n k 0,
      (Tower.iterAverageLinear L n k (X p).fine l : Tower.Vertex L n k k → ComplexMatrix2) =
        Tower.iterAdjointCubeAverage L n k (X p).fine k
          (l : Tower.Vertex L n k 0 → ComplexMatrix2) := by
    filter_upwards [hUt.eventually (iterAdjointCubeAverage_linear hY hL hn hk)] with p h l
    exact linearMapWithValues_apply h l
  have hATr : ∀ᶠ p in 𝓝 p₀, ∀ (x : Tower.vertexFunctionSpace L n k k)
      (l : Tower.vertexFunctionSpace L n k 0),
      Tower.traceFinsumPairing
          (Tower.iterAverageRealTranspose L n k (X p).fine x :
            Tower.Vertex L n k 0 → ComplexMatrix2)
          (l : Tower.Vertex L n k 0 → ComplexMatrix2) =
        Tower.traceFinsumPairing (x : Tower.Vertex L n k k → ComplexMatrix2)
          (Tower.iterAverageLinear L n k (X p).fine l : Tower.Vertex L n k k → ComplexMatrix2) := by
    filter_upwards [hUt.eventually (hQ L n k hL hn hk).2] with p h x l
    obtain ⟨T, -, -, -, h'⟩ := h.2.1.average_transpose
    exact h' x l
  have hWt : ∀ j < k, Tendsto (fun p => RunningCouplingSlope.levelField (X p) j) (𝓝 p₀)
      (𝓝[Tower.fieldSpace L n k j] fun _ => (1 : ComplexMatrix2)) := fun j hj =>
    tendsto_nhdsWithin_one (fun b => (hF₁ j hj.le b).1.continuousAt)
      (fun b => (hF₁ j hj.le b).2) (hF₃.mono fun p h => h.2 j hj.le)
  have hSlin : ∀ᶠ p in 𝓝 p₀, ∀ l : Tower.vertexFunctionSpace L n k 0,
      (RunningCouplingSlope.composedCubeAverageLinear (X p) l : Tower.Vertex L n k k → ComplexMatrix2) =
        RunningCouplingSlope.composedCubeAverage (X p) k (l : Tower.Vertex L n k 0 → ComplexMatrix2) := by
    filter_upwards [composedCubeAverage_linear (fun i hi => (hY L n k hL hn hk).1 i hi) hWt k
      le_rfl] with p h l
    exact linearMapWithValues_apply h l
  have hsk := hsites k
  have hpos₀ : Finite (Tower.PositiveEdge L n k 0) := by
    have := hbonds 0
    exact Subtype.finite
  have hDan : ∀ (l : Tower.vertexFunctionSpace L n k 0) (c : Tower.PositiveEdge L n k 0),
      AnalyticAt ℝ (fun p => Tower.restrictToPositiveEdges
        (Tower.covDiff (X p).fine (l : Tower.Vertex L n k 0 → ComplexMatrix2)) c) p₀ :=
    fun l c => analyticAt_covDiff hX.analyticAt_fine hdet _ c.1
  have hAan : ∀ (l : Tower.vertexFunctionSpace L n k 0) (y : Tower.Vertex L n k k), AnalyticAt ℝ
      (fun p => Tower.iterAdjointCubeAverage L n k (X p).fine k
        (l : Tower.Vertex L n k 0 → ComplexMatrix2) y) p₀ :=
    fun l y => analyticAt_iterAdjointCubeAverage F hgood
      (l := fun _ => (l : Tower.Vertex L n k 0 → ComplexMatrix2))
      (fun _ => analyticAt_const) k le_rfl y
  have hz : ∀ (B : Tower.edgeFormSpace L n k 0) (x : Tower.Vertex L n k 0), AnalyticAt ℝ
      (fun p => (Tower.covDiffRealTranspose L n k (X p).fine B :
        Tower.Vertex L n k 0 → ComplexMatrix2) x) p₀ := by
    intro B
    refine hcoord _ fun a => ?_
    refine (analyticAt_re_pairing
      (f := fun _ => Tower.restrictToPositiveEdges (B : Tower.Edge L n k 0 → ComplexMatrix2))
      (fun _ => analyticAt_const) (hDan (e a))).congr ?_
    filter_upwards [hDTr, hDlin] with p h₁ h₂
    rw [h₁, h₂]
    rfl
  have hdd : ∀ (l : Tower.vertexFunctionSpace L n k 0) (x : Tower.Vertex L n k 0), AnalyticAt ℝ
      (fun p => (Tower.covDiffRealTranspose L n k (X p).fine
        (Tower.covDiffLinear L n k (X p).fine l) : Tower.Vertex L n k 0 → ComplexMatrix2) x)
        p₀ := by
    intro l
    refine hcoord _ fun a => ?_
    refine (analyticAt_re_pairing (hDan l) (hDan (e a))).congr ?_
    filter_upwards [hDTr, hDlin] with p h₁ h₂
    rw [h₁, h₂, h₂]
    rfl
  have hAt : ∀ g : E → Tower.vertexFunctionSpace L n k k,
      (∀ y, AnalyticAt ℝ (fun p => (g p : Tower.Vertex L n k k → ComplexMatrix2) y) p₀) →
      ∀ x, AnalyticAt ℝ (fun p =>
        (Tower.iterAverageRealTranspose L n k (X p).fine (g p) :
          Tower.Vertex L n k 0 → ComplexMatrix2) x) p₀ := by
    intro g hg
    refine hcoord _ fun a => ?_
    refine (analyticAt_re_pairing hg (hAan (e a))).congr ?_
    filter_upwards [hATr, hAlin] with p h₁ h₂
    rw [h₁, h₂]
  refine ⟨fun B x => ?_, fun y => ⟨fun x => ?_, fun x => ?_⟩⟩
  · have hg : ∀ y, AnalyticAt ℝ (fun p => (Tower.iterAverageLinear L n k (X p).fine
        (Tower.covDiffRealTranspose L n k (X p).fine B) :
          Tower.Vertex L n k k → ComplexMatrix2) y) p₀ := by
      intro y
      refine (analyticAt_iterAdjointCubeAverage F hgood (hz B) k le_rfl y).congr ?_
      filter_upwards [hAlin] with p h
      rw [h]
    exact ((hz B x).sub (analyticAt_const.smul (hAt _ hg x))).congr
      (Eventually.of_forall fun p => rfl)
  · exact ((hdd y.1 x).add (hAt (fun _ => y.2) (fun _ => analyticAt_const) x)).congr
      (Eventually.of_forall fun p => rfl)
  · refine (analyticAt_composedCubeAverage F hgood₀
      (y.1 : Tower.Vertex L n k 0 → ComplexMatrix2) k le_rfl x).congr ?_
    filter_upwards [hSlin] with p h
    exact (congrFun (h y.1) x).symm
end YangMills.Construction.RunningCouplingSlope.AnalyticGaugeMaps
end
