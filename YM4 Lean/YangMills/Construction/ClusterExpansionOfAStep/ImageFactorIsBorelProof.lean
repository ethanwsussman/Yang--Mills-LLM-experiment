import YangMills.Construction.ClusterExpansionOfAStep.GasDensityOfAGroundIsBorelProof
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsBorelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TopLevelSites TorusFields TorusLumps StepSettings StepCosts
  StateMeasurability StepFrames RenormalizationStepParameters StepGas ColdChain
namespace CoarseFactorMeasurability
section GaugeFields
variable {F : BlockFrame} {j : ℕ}
theorem measurable_pathHolonomy (l : List PathStep) (x : F.Site j) :
    Measurable fun U : F.GaugeField j => pathHolonomy U x l := by apply _root_.YangMills.Construction.BlockTrees.measurable_pathHolonomy <;> assumption
theorem measurable_plaquetteDefect (p : F.Site j × Fin 4 × Fin 4) :
    Measurable fun U : F.GaugeField j => plaquetteDefect U p := by
  unfold plaquetteDefect plaquetteHolonomy
  have hc : Continuous fun g : UnitQuaternion => ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1‖ :=
    (continuous_subtype_val.sub continuous_const).norm
  exact hc.measurable.comp (measurable_pathHolonomy _ _)
theorem measurable_readAtLevel {m : ℕ} (j : ℕ) : Measurable (readAtLevel (n := m) F j) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.measurable_readAtLevel <;> assumption
theorem measurableSet_comp_eq {β γ δ : Type*} [MeasurableSpace β] [Countable γ] (h : β → γ)
    (hs : ∀ v, MeasurableSet {b | h b = v}) (G : γ → δ) (d : δ) : MeasurableSet {b | G (h b) = d} := by apply _root_.YangMills.Construction.KernelMeasurability.measurableSet_fibre_comp <;> assumption
open Classical in
theorem measurableSet_hotLumps_eq {L : ℕ} (g : LumpGrid L) (s : ℝ) (X : Finset (F.Site j)) {β : Type*}
    [MeasurableSpace β] {f : β → F.GaugeField j} (hf : Measurable f) (H : Finset (Finset (F.Site j))) :
    MeasurableSet {b | hotLumps g s X (f b) = H} := by
  let Pf : β → Finset (F.Site j × Fin 4 × Fin 4) := fun b =>
    (cutPlaquettes X).filter fun p => s ≤ plaquetteDefect (f b) p
  have hP : ∀ A, MeasurableSet {b | Pf b = A} := by
    intro A
    by_cases hA : A ⊆ cutPlaquettes X
    · have e : {b | Pf b = A} = ⋂ p ∈ cutPlaquettes X, {b | s ≤ plaquetteDefect (f b) p ↔ p ∈ A} := by
        ext b
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Pf]
        constructor
        · intro h p hp
          rw [← h]
          simp [hp]
        · intro h
          ext p
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨h1, h2⟩
            exact (h p h1).mp h2
          · intro hp
            exact ⟨hA hp, (h p (hA hp)).mpr hp⟩
      rw [e]
      refine Finset.measurableSet_biInter _ fun p _ => ?_
      have hm : Measurable fun b => plaquetteDefect (f b) p := (measurable_plaquetteDefect p).comp hf
      by_cases hp : p ∈ A
      · simp only [hp, iff_true]
        exact measurableSet_le measurable_const hm
      · simp only [hp, iff_false, not_le]
        exact measurableSet_lt hm measurable_const
    · have e : {b | Pf b = A} = ∅ := by
        ext b
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hA (h ▸ Finset.filter_subset _ _)
      rw [e]
      exact MeasurableSet.empty
  have e : {b | hotLumps g s X (f b) = H} = ⋃ A ∈ (cutPlaquettes X).powerset.filter
      (fun A => A.biUnion (fun p => (plaquetteCorners p).image (lumpOf g)) = H), {b | Pf b = A} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset, exists_prop]
    constructor
    · intro h
      exact ⟨Pf b, ⟨Finset.filter_subset _ _, h⟩, rfl⟩
    · rintro ⟨A, ⟨_, h1⟩, h2⟩
      rw [← h2] at h1
      exact h1
  rw [e]
  exact Finset.measurableSet_biUnion _ fun A _ => hP A
end GaugeFields
section HotLumps
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {n : ℕ} [NeZero n]
open Classical in
theorem torusLumpOf_mem_hotLumpsOn (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) {X : Finset (TorusSite n)}
    {V : TorusField n} {x : TorusSite n} {μ ν : Fin 4}
    (hlt : μ < ν) (hs : ℓ.threshold ≤ curvature V x μ ν) (hc : ∀ z ∈ plaquetteVertices x μ ν, z ∈ X)
    {z : TorusSite n} (hz : z ∈ plaquetteVertices x μ ν) : torusLumpOf ℓ z ∈ hotLumpsOn ℓ X V := by
  have hp : ∀ i, (stepBlockFrame ℓ.side (n / ℓ.side)).period 0 i = n := period_stepBlockFrame hLn
  obtain ⟨x₀, rfl⟩ := toTorusSite_surjective (ℓ := ℓ) hLn x
  obtain ⟨z₀, hz₀, rfl⟩ := (mem_plaquetteVertices_iff hLn x₀ μ ν _).mp hz
  unfold hotLumpsOn hotLumps
  refine Finset.mem_image.mpr ⟨lumpOf ℓ.grid z₀, Finset.mem_biUnion.mpr ⟨(x₀, μ, ν), ?_, ?_⟩,
    image_lumpOf hfit hLn z₀⟩
  · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · unfold cutPlaquettes
      have hall : ∀ y ∈ plaquetteCorners ((x₀, μ, ν) : (stepBlockFrame ℓ.side (n / ℓ.side)).Site 0 × Fin 4 × Fin 4),
          y ∈ X.image (torusSiteInFrame (stepBlockFrame ℓ.side (n / ℓ.side)) 0) := by
        intro y hy
        refine Finset.mem_image.mpr ⟨toTorusSite n y,
          hc _ ((mem_plaquetteVertices_iff hLn x₀ μ ν _).mpr ⟨y, hy, rfl⟩), ?_⟩
        exact torusSiteInFrame_toTorusSite hp y
      refine Finset.mem_filter.mpr ⟨?_, hlt, hall⟩
      have hx₀ : x₀ ∈ plaquetteCorners ((x₀, μ, ν) : (stepBlockFrame ℓ.side (n / ℓ.side)).Site 0 × Fin 4 × Fin 4) := by
        simp [plaquetteCorners]
      simp [hall x₀ hx₀]
    · rw [plaquetteDefect_readAtLevel_eq hp]
      exact hs
  · exact Finset.mem_image.mpr ⟨z₀, hz₀, rfl⟩
end HotLumps
section Marks
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem measurable_norm_sub_of_measurableQuaternion {α : Type} [MeasurableSpace α] {f g : α → ℍ[ℝ]}
    (hf : MeasurableQuaternion f) (hg : MeasurableQuaternion g) : Measurable fun a => ‖f a - g a‖ := by apply _root_.YangMills.Construction.CoarseMeasurability.measurable_norm_sub_of_quaternion <;> assumption
theorem measurable_cutoffFactor {ρ : ℝ} {p : ℝ → ℝ} (hp : ContinuousOn p (Set.Ico 0 ρ)) {α : Type}
    [MeasurableSpace α] {u : α → ℝ} (hu : Measurable u) (h0 : ∀ a, 0 ≤ u a) :
    Measurable fun a => cutoffFactor ρ p (u a) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GroundDensityMeasurability.measurable_cutoffFactor_comp <;> assumption
theorem measurableQuaternion_comp₂ {β₁ β₂ α : Type} [MeasurableSpace β₁] [MeasurableSpace β₂] [MeasurableSpace α]
    (C : β₁ → β₂ → ℍ[ℝ]) (hC : MeasurableQuaternion fun p : β₁ × β₂ => C p.1 p.2) {v : α → β₁} {w : α → β₂}
    (hv : Measurable v) (hw : Measurable w) : MeasurableQuaternion fun a => C (v a) (w a) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GroundDensityMeasurability.measurableQuaternion_comp_pair <;> assumption
theorem measurableQuaternion_of_continuousOn {β α : Type} [TopologicalSpace β] [MeasurableSpace β]
    [OpensMeasurableSpace β] [MeasurableSpace α] {U : Set β} {f : β → ℍ[ℝ]} (hU : ContinuousOn f U)
    {v : α → β} (hv : Measurable v) (hmem : ∀ a, v a ∈ U) : MeasurableQuaternion fun a => f (v a) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GroundDensityMeasurability.measurableQuaternion_of_continuousOn <;> assumption
theorem measurable_bondMark (hFC : continuousOn_frameCoord_of_cold) (hCC : ChartCoordMeasurable)
    {δ lam σA cg : ℝ} {N : ℕ → ℝ} (hfit : R.params.Admissible)
    (hch : ColdChainConstants R.params.coupling δ R.params.side lam R.anchorRadius σA cg N)
    (hσ : R.params.threshold ≤ σA) (hcut : IsCutoff R.ballRadius R.barrierFn) (hm : 16 ≤ R.frameReach)
    (hn : 64 ≤ n) {b : TorusBond (n * R.params.side)} (hb : b ∈ chartBonds R.params.side n)
    {α : Type} [MeasurableSpace α] {v : α → TorusField n} {w : α → TorusField (n * R.params.side)}
    (hv : Measurable v) (hw : Measurable w)
    (h1 : 4 * R.frameReach + 5 < n →
      ∀ a, ColdNearSite R.params.threshold R.frameReach (parentBlock R.params.side b.1) (v a))
    (h2 : ¬ 4 * R.frameReach + 5 < n → ∀ a, IsCold R.params.threshold (v a)) :
    Measurable fun a => bondMark R (v a) (w a) b := by
  haveI : NeZero (n * R.params.side) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne R.params.side)⟩
  obtain ⟨c1, c2⟩ := hFC R.params δ lam R.anchorRadius σA cg N hfit hch hσ R.depth R.frameReach n hm hn b hb
  have hframe : MeasurableQuaternion fun a =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v a) b : imaginaryQuaternions) : ℍ[ℝ]) := by
    by_cases hbig : 4 * R.frameReach + 5 < n
    · exact measurableQuaternion_of_continuousOn (β := TorusField n)
        (U := {V | ColdNearSite R.params.threshold R.frameReach (parentBlock R.params.side b.1) V})
        (f := fun V : TorusField n =>
          ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ]))
        (c1 hbig) hv (h1 hbig)
    · exact measurableQuaternion_of_continuousOn (β := TorusField n) (U := {V | IsCold R.params.threshold V})
        (f := fun V : TorusField n =>
          ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ]))
        (c2 hbig) hv (h2 hbig)
  have hchart : MeasurableQuaternion fun a =>
      ((chartCoord R.params (v a) (w a) b : imaginaryQuaternions) : ℍ[ℝ]) := by
    exact measurableQuaternion_comp₂ (fun V W => ((chartCoord R.params V W b : imaginaryQuaternions) : ℍ[ℝ]))
      (hCC R.params n b) hv hw
  unfold bondMark
  exact measurable_cutoffFactor hcut.smooth.continuousOn
    (measurable_norm_sub_of_measurableQuaternion hchart hframe) fun _ => norm_nonneg _
end Marks
section Records
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem isAdmissibleOn_of_shapeEquivalent {p p' : CoarseState R n} (h : ShapeEquivalent p p')
    {C X : Finset (TorusSite n)}
    (hhot : frameHotLumps R.params (sitesInBlocks R.params.side p.markedZone) p.storedField =
      frameHotLumps R.params (sitesInBlocks R.params.side p'.markedZone) p'.storedField)
    (ha : p.IsAdmissibleCoarseState C X) : p'.IsAdmissibleCoarseState C X := by
  have hz := markedZone_eq h
  have hb := storedBadBonds_eq h
  have hf := storedFieldBonds_eq h
  have hl := labelSet_eq h
  have hc : frameHotLumpSites R.params (sitesInBlocks R.params.side p'.markedZone) p'.storedField =
      frameHotLumpSites R.params (sitesInBlocks R.params.side p.markedZone) p.storedField := by
    unfold frameHotLumpSites
    rw [hhot]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hz]
    exact ha.eq_thickening
  · intro y s hs
    rcases markAt_shape h y with ⟨h1, h2⟩ | ⟨s₀, s₁, h1, h2, h3, _⟩
    · rw [h2] at hs
      exact absurd hs (by simp)
    · rw [h2] at hs
      obtain rfl := Option.some.inj hs
      rw [← h3]
      exact ha.isCore_eq y s₀ h1
  · rw [← hz]
    exact ha.subset_dataZone
  · rw [← hb]
    exact ha.badBonds_subset
  · rw [← hf, ← hz]
    exact ha.fieldBonds_eq
  · rw [← hb, ← hl]
    exact ha.attached_eq
  · rw [← hb, ← hl, ← hz]
    exact ha.storedBlocks_eq
  · rw [hc, ← hl]
    exact ha.hotHull_subset
  · rw [hc, ← hl]
    exact ha.component_meets
theorem mem_hotNeighbourhoodOn (hfit : R.params.Admissible) (hLn : R.params.side ∣ n) {X : Finset (TorusSite n)}
    {V : TorusField n} {x : TorusSite n} {μ ν : Fin 4}
    (hlt : μ < ν) (hs : R.params.threshold ≤ curvature V x μ ν) (hc : ∀ z ∈ plaquetteVertices x μ ν, z ∈ X)
    {y : TorusSite n} (hy : supDist y x ≤ 2 * R.nextRange) : y ∈ hotNeighbourhoodOn R X V := by
  classical
  have hx : x ∈ plaquetteVertices x μ ν := base_mem_plaquetteVertices x μ ν
  refine (mem_thickening _ _ _).mpr ⟨x, ?_, hy⟩
  exact Finset.mem_biUnion.mpr ⟨torusLumpOf R.params x, torusLumpOf_mem_hotLumpsOn hfit hLn hlt hs hc hx,
    mem_torusLumpOf_self x⟩
theorem coldNearSite_of_not_mem (hfit : R.params.Admissible) (hLn : R.params.side ∣ n)
    {X Zo : Finset (TorusSite n)} {V : TorusField n} {y : TorusSite n}
    (hX : X = thickening (R.nextRange / 2) Zo) (hy : y ∈ Zo) (hC : y ∉ hotNeighbourhoodOn R X V)
    (hm : R.frameReach ≤ R.nextRange / 2) :
    ColdNearSite R.params.threshold R.frameReach y V := by
  intro a μ ν hlt hcorn
  by_contra hcon
  have hs : R.params.threshold ≤ curvature V (y + siteOfInt a) μ ν := not_lt.mp hcon
  have hbox : ∀ d ∈ plaquetteOffsets μ ν, supDist y (y + siteOfInt (a + d)) ≤ R.frameReach := by
    intro d hd
    refine supDist_add_siteOfInt_le _ _ _ fun i => ?_
    have := hcorn d hd i
    have h2 := abs_le.mp this
    omega
  have hc : ∀ z ∈ plaquetteVertices (y + siteOfInt a) μ ν, z ∈ X := by
    intro z hz
    have h1 : ∃ d ∈ plaquetteOffsets μ ν, z = y + siteOfInt (a + d) := by
      simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact ⟨0, by simp [plaquetteOffsets], by simp⟩
      · exact ⟨Pi.single μ 1, by simp [plaquetteOffsets],
          by rw [siteOfInt_add, unitStep_eq_siteOfInt, add_assoc]⟩
      · exact ⟨Pi.single ν 1, by simp [plaquetteOffsets],
          by rw [siteOfInt_add, unitStep_eq_siteOfInt, add_assoc]⟩
      · exact ⟨Pi.single μ 1 + Pi.single ν 1, by simp [plaquetteOffsets], by
          rw [siteOfInt_add, siteOfInt_add, unitStep_eq_siteOfInt, unitStep_eq_siteOfInt]
          abel⟩
    obtain ⟨d, hd, rfl⟩ := h1
    rw [hX]
    refine (mem_thickening _ _ _).mpr ⟨y, hy, ?_⟩
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
    exact (hbox d hd).trans hm
  refine hC (mem_hotNeighbourhoodOn hfit hLn hlt hs hc ?_)
  have h0 := hbox 0 (by simp [plaquetteOffsets])
  rw [add_zero] at h0
  omega
theorem supDist_le_half (x z : TorusSite n) : supDist x z ≤ n / 2 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.supDist_le_half_card <;> assumption
theorem isCold_of_not_mem (hfit : R.params.Admissible) (hLn : R.params.side ∣ n) {X Zo : Finset (TorusSite n)}
    {V : TorusField n} {y : TorusSite n}
    (hX : X = thickening (R.nextRange / 2) Zo) (hy : y ∈ Zo) (hC : y ∉ hotNeighbourhoodOn R X V)
    (hn : n / 2 ≤ R.nextRange / 2) :
    IsCold R.params.threshold V := by
  intro x μ ν hlt
  by_contra hcon
  have hs : R.params.threshold ≤ curvature V x μ ν := not_lt.mp hcon
  have hc : ∀ z ∈ plaquetteVertices x μ ν, z ∈ X := by
    intro z _
    rw [hX]
    exact (mem_thickening _ _ _).mpr ⟨y, hy, (supDist_le_half z y).trans hn⟩
  refine hC (mem_hotNeighbourhoodOn hfit hLn hlt hs hc ?_)
  have := supDist_le_half y x
  omega
open Classical in
theorem labelAt_eq_inr_labeling (q : CoarseState R n) (z : q.labelSet) :
    q.labelAt z = Sum.inr (q.labeling z) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.labelAt_eq_inr_labeling <;> assumption
theorem prod_chainComponents_congr {Ω : Type} {m : ℕ} [NeZero m]
    (Φ : TorusField m → (Y : Finset (TorusSite m)) → (Y → Ω) → Finset (TorusSite m) → ℝ) (r : ℕ)
    (W : TorusField m) {B A : Finset (TorusSite m)} (hB : B = A) (l : B → Ω) :
    ∏ Xc ∈ chainComponents r B, Φ W B l Xc =
      ∏ Xc ∈ chainComponents r A, Φ W A (fun z => l ⟨z, hB ▸ z.2⟩) Xc := by
  subst hB
  rfl
end Records
def neighbourhoodOfLumps (R : StepSetup) {n : ℕ} [NeZero n]
    (H : Finset (Finset ((stepBlockFrame R.params.side (n / R.params.side)).Site 0))) : Finset (TorusSite n) :=
  open Classical in thickening (2 * R.nextRange) ((H.image fun l => l.image (toTorusSite n)).biUnion id)
theorem hotNeighbourhoodOn_eq (R : StepSetup) {n : ℕ} [NeZero n] (X : Finset (TorusSite n)) (V : TorusField n) :
    hotNeighbourhoodOn R X V = neighbourhoodOfLumps R (n := n) (open Classical in
      hotLumps R.params.grid R.params.threshold
      (X.image (torusSiteInFrame (stepBlockFrame R.params.side (n / R.params.side)) 0))
      (readAtLevel (stepBlockFrame R.params.side (n / R.params.side)) 0 V)) := rfl
theorem measurableSet_hotNeighbourhoodOn_eq {R : StepSetup} {n : ℕ} [NeZero n] (hLn : R.params.side ∣ n)
    (X : Finset (TorusSite n)) {β : Type} [MeasurableSpace β] {f : β → TorusField n} (hf : Measurable f)
    (C : Finset (TorusSite n)) : MeasurableSet {b | hotNeighbourhoodOn R X (f b) = C} := by
  classical
  haveI hnd : NeZero (n / R.params.side) := neZero_div_side hLn
  simp only [hotNeighbourhoodOn_eq]
  exact measurableSet_comp_eq _
    (fun H => measurableSet_hotLumps_eq _ _ _ ((measurable_readAtLevel 0).comp hf) H)
    (neighbourhoodOfLumps R) C
def storedBaseWeight {R : StepSetup} {n : ℕ} [NeZero n] (p : CoarseState R n) : ℝ :=
  ∏ y ∈ p.markedZone, match p.markAt y with
    | some s => blockBaseWeight R.params
        (frameHotLumps R.params (sitesInBlocks R.params.side p.markedZone) p.storedField)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 0 (blockSite y s.basePoint))
    | none => 1
theorem storedBaseWeight_congr {R : StepSetup} {n : ℕ} [NeZero n] {p p' : CoarseState R n}
    (h : ShapeEquivalent p p')
    (hhot : frameHotLumps R.params (sitesInBlocks R.params.side p.markedZone) p.storedField =
      frameHotLumps R.params (sitesInBlocks R.params.side p'.markedZone) p'.storedField) :
    storedBaseWeight p = storedBaseWeight p' := by
  unfold storedBaseWeight
  rw [hhot, markedZone_eq h]
  refine Finset.prod_congr rfl fun y _ => ?_
  rcases markAt_shape h y with ⟨h1, h2⟩ | ⟨s, s', h1, h2, _, _, _, h3, _⟩
  · rw [h1, h2]
  · rw [h1, h2]
    simp only [h3]
theorem baseFactorProduct_congr {R : StepSetup} {n : ℕ} [NeZero n] {q q' : CoarseState R n}
    {X : Finset (TorusSite n)} (h : ShapeEquivalent (q.restrict X) (q'.restrict X))
    (hhot : frameHotLumps R.params (sitesInBlocks R.params.side (q.restrict X).markedZone)
        (q.restrict X).storedField =
      frameHotLumps R.params (sitesInBlocks R.params.side (q'.restrict X).markedZone)
        (q'.restrict X).storedField) :
    baseFactorProduct q X = baseFactorProduct q' X :=
  storedBaseWeight_congr h hhot
theorem shapeEquivalent_of_labelShape_eq {R : StepSetup} {n : ℕ} [NeZero n] {Z : Finset (TorusSite n)}
    {ω ω' : Z → CoarseLabel R.labels.Ω R.params.side} (e : ∀ y, markShape (ω y) = markShape (ω' y)) :
    ShapeEquivalent (⟨Z, ω⟩ : CoarseState R n) ⟨Z, ω'⟩ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.shapeEquivalent_of <;> assumption
end CoarseFactorMeasurability
set_option maxHeartbeats 1600000 in
open CoarseFactorMeasurability in
theorem CoarseFactorMeasurability.coarseFactorExpansionMeasurable_holds (hFC : continuousOn_frameCoord_of_cold)
    (hCC : ChartCoordMeasurable) : CoarseFactorExpansionMeasurable := by
  intro T hT
  refine ⟨0, fun y _ R htab hform n _ hB Y X => ?_⟩
  classical
  have hfit := hform.admissible
  have hLn : R.params.side ∣ n := hB.1
  have hLpos : 0 < R.params.side := hfit.L_odd.pos
  haveI hnz : NeZero (n * R.params.side) := ⟨mul_ne_zero (NeZero.ne n) hLpos.ne'⟩
  haveI hnd : NeZero (n / R.params.side) := neZero_div_side hLn
  have hl := htab.params_eq
  have hch : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    have e1 : R.params.coupling = T.coupling := by rw [hl]; rfl
    have e2 : R.params.side = T.side := by rw [hl]; rfl
    rw [e1, e2, htab.anchorRadius_eq]
    exact hT.chain
  have hσ : R.params.threshold ≤ T.σA := by
    have e1 : R.params.threshold = T.threshold := by rw [hl]; rfl
    have h1 := hT.σ_le
    have h2 := hT.σ_pos
    rw [e1]
    linarith
  have hcut := hform.isCutoff
  have hrb : 2 ^ 40 * R.params.side ≤ R.range := hform.range_ge_side
  have hra : R.range ≤ R.nextRange + 1 := hform.range_le
  have hm : 16 ≤ R.frameReach := by
    show 16 ≤ R.range / 2 ^ 11
    have : 2 ^ 40 ≤ R.range := le_trans (Nat.le_mul_of_pos_right _ hLpos) hrb
    omega
  have hn64 : 64 ≤ n := by
    have h1 : R.params.side * R.params.n₀ ≤ n := hB.2
    have h2 : 4096 ≤ R.params.n₀ := hfit.n₀_ge
    have h3 : R.params.n₀ ≤ R.params.side * R.params.n₀ := Nat.le_mul_of_pos_left _ hLpos
    omega
  have hm2 : R.frameReach ≤ R.nextRange / 2 := by
    show R.range / 2 ^ 11 ≤ R.nextRange / 2
    omega
  have hsm : ¬ 4 * R.frameReach + 5 < n → n / 2 ≤ R.nextRange / 2 := by
    intro h
    have h1 : R.frameReach = R.range / 2 ^ 11 := rfl
    omega
  have hrow := hform.hasExpansions.2
  have hblock : IsBlockTorusSide R.params (n * R.params.side) := by
    refine ⟨Dvd.intro_left _ rfl, ?_⟩
    have h1 : R.params.side * R.params.n₀ ≤ n := hB.2
    have h2 : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hLpos) h1
    rw [mul_comm n]
    exact Nat.mul_le_mul_left _ h2
  let Z : Finset (TorusSite n) := Y ∩ X
  let rs : (Y → CoarseLabel R.labels.Ω R.params.side) → (Z → CoarseLabel R.labels.Ω R.params.side) :=
    fun ω y => ω ⟨y, (Finset.mem_inter.mp y.2).1⟩
  have hrs : Measurable rs := measurable_pi_iff.mpr fun y => measurable_pi_apply _
  let Q : (Y → CoarseLabel R.labels.Ω R.params.side) → CoarseState R n := fun ω => ⟨Z, rs ω⟩
  let τ : (Y → CoarseLabel R.labels.Ω R.params.side) → Z → CoarseStateShape R.params.side :=
    fun ω y => markShape (rs ω y)
  let Hv : (Y → CoarseLabel R.labels.Ω R.params.side) →
      Finset (Finset ((stepBlockFrame R.params.side n).Site 0)) := fun ω =>
    frameHotLumps R.params (sitesInBlocks R.params.side (Q ω).markedZone) (Q ω).storedField
  have hsame : ∀ ω ω', τ ω = τ ω' → ShapeEquivalent (Q ω) (Q ω') := fun ω ω' e =>
    shapeEquivalent_of_labelShape_eq fun y => congrFun e y
  have hτ : ∀ t, MeasurableSet {ω | τ ω = t} := by
    intro t
    have e : {ω | τ ω = t} = ⋂ y, {ω | markShape (rs ω y) = t y} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact funext_iff
    rw [e]
    refine MeasurableSet.iInter fun y => ?_
    have hm : Measurable fun ω : Y → CoarseLabel R.labels.Ω R.params.side => rs ω y :=
      measurable_pi_apply (⟨y, (Finset.mem_inter.mp y.2).1⟩ : Y)
    exact hm (measurableSet_configShape (t y))
  have hstored : Measurable fun ω => (Q ω).storedField := (measurable_storedField Z).comp hrs
  have hH : ∀ t H, MeasurableSet ({ω | τ ω = t} ∩ {ω | Hv ω = H}) := by
    intro t H
    by_cases hex : ∃ ω₀, τ ω₀ = t
    · obtain ⟨ω₀, h₀⟩ := hex
      have e : {ω | τ ω = t} ∩ {ω | Hv ω = H} = {ω | τ ω = t} ∩
          {ω | frameHotLumps R.params (sitesInBlocks R.params.side (Q ω₀).markedZone) (Q ω).storedField = H} := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        refine and_congr_right fun h => ?_
        have hz := markedZone_eq (hsame ω ω₀ (h.trans h₀.symm))
        show frameHotLumps R.params (sitesInBlocks R.params.side (Q ω).markedZone) (Q ω).storedField = H ↔ _
        rw [hz]
      rw [e]
      refine (hτ t).inter ?_
      exact measurableSet_hotLumps_eq _ _ _ ((measurable_readAtLevel 0).comp hstored) H
    · have e : {ω | τ ω = t} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hex ⟨ω, h⟩
      rw [e]
      simp
  have hC : ∀ C, MeasurableSet
      {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | hotNeighbourhoodOn R X p.1 = C} := by
    intro C
    exact measurableSet_hotNeighbourhoodOn_eq hLn X measurable_fst C
  let S : ((Z → CoarseStateShape R.params.side) × Finset (TorusSite n) ×
      Finset (Finset ((stepBlockFrame R.params.side n).Site 0))) →
      Set (TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side)) := fun i =>
    (Prod.snd ⁻¹' ({ω | τ ω = i.1} ∩ {ω | Hv ω = i.2.2})) ∩ {p | hotNeighbourhoodOn R X p.1 = i.2.1}
  refine measurable_of_countable_cover S (fun i => (measurable_snd (hH _ _)).inter (hC _))
    (fun p => ⟨(τ p.2, hotNeighbourhoodOn R X p.1, Hv p.2), ⟨rfl, rfl⟩, rfl⟩) ?_
  rintro ⟨t, C, H⟩
  rcases isEmpty_or_nonempty (S (t, C, H)) with he | ⟨⟨p₀, ⟨h₁, h₂⟩, h₃⟩⟩
  · exact measurable_of_empty _
  have hsh : ∀ x : S (t, C, H), ShapeEquivalent (Q p₀.2) (Q x.1.2) := fun x =>
    hsame _ _ (h₁.trans x.2.1.1.symm)
  have hHx : ∀ x : S (t, C, H), Hv p₀.2 = Hv x.1.2 := fun x => h₂.trans x.2.1.2.symm
  have hCx : ∀ x : S (t, C, H), hotNeighbourhoodOn R X x.1.1 = C := fun x => x.2.2
  have hsh' : ∀ x : S (t, C, H), ShapeEquivalent (Q x.1.2) (Q p₀.2) := fun x =>
    hsame _ _ (x.2.1.1.trans h₁.symm)
  have hval : ∀ x : S (t, C, H), coarseFactorExpansion R n x.1.1 Y x.1.2 X =
      coarseFactor x.1.1 (⟨Y, x.1.2⟩ : CoarseState R n) X := fun x => dif_neg (NeZero.ne n)
  have hx1 : Measurable fun x : S (t, C, H) => x.1.1 := measurable_fst.comp measurable_subtype_coe
  have hx2 : Measurable fun x : S (t, C, H) => x.1.2 := measurable_snd.comp measurable_subtype_coe
  by_cases adm : (Q p₀.2).IsAdmissibleCoarseState C X
  swap
  · have e : (fun x : S (t, C, H) => coarseFactorExpansion R n x.1.1 Y x.1.2 X) = fun _ => 0 := by
      funext x
      rw [hval]
      have hna : ¬ (Q x.1.2).IsAdmissibleCoarseState C X := fun h =>
        adm (isAdmissibleOn_of_shapeEquivalent (hsh' x) (hHx x).symm h)
      have ht : admissibilityIndicator x.1.1 (⟨Y, x.1.2⟩ : CoarseState R n) X = 0 := by
        show (if (Q x.1.2).IsAdmissibleCoarseState (hotNeighbourhoodOn R X x.1.1) X then (1 : ℝ) else 0) = 0
        rw [hCx x, if_neg hna]
      simp only [coarseFactor, ht, zero_mul]
    show Measurable fun x : S (t, C, H) => coarseFactorExpansion R n x.1.1 Y x.1.2 X
    rw [e]
    exact measurable_const
  have hadm : ∀ x : S (t, C, H), (Q x.1.2).IsAdmissibleCoarseState C X := fun x =>
    isAdmissibleOn_of_shapeEquivalent (hsh x) (hHx x) adm
  let A : Finset (TorusSite (n * R.params.side)) := (Q p₀.2).labelSet
  have hA : ∀ x : S (t, C, H), (Q x.1.2).labelSet = A := fun x => labelSet_eq (hsh' x)
  let g : S (t, C, H) → A → R.labels.Ω := fun x z => (Q x.1.2).labeling ⟨z, (hA x).ge z.2⟩
  have hgm : Measurable g := by
    refine measurable_pi_iff.mpr fun z => ?_
    have hz : ∀ x : S (t, C, H), (Q x.1.2).labelAt z = Sum.inr (g x z) := fun x =>
      labelAt_eq_inr_labeling (Q x.1.2) ⟨z, (hA x).ge z.2⟩
    have hm1 : Measurable fun x : S (t, C, H) => (Q x.1.2).labelAt z :=
      ((measurable_labelAt (R := R) Z z.1).comp hrs).comp hx2
    have hm3 : Measurable fun x : S (t, C, H) => (Sum.inr (g x z) : WithNone R.labels.Ω) := by
      have e : (fun x : S (t, C, H) => (Sum.inr (g x z) : WithNone R.labels.Ω)) =
          fun x => (Q x.1.2).labelAt z := funext fun x => (hz x).symm
      rw [e]
      exact hm1
    intro s hs
    have h4 := hm3 (hs.inr_image (α := Unit))
    have e : (fun x : S (t, C, H) => g x z) ⁻¹' s =
        (fun x : S (t, C, H) => (Sum.inr (g x z) : WithNone R.labels.Ω)) ⁻¹' (Sum.inr '' s) := by
      ext x
      simp
    rw [e]
    exact h4
  have hst : Measurable fun x : S (t, C, H) => (Q x.1.2).storedField := hstored.comp hx2
  have hlev : Measurable fun x : S (t, C, H) =>
      ∏ Xc ∈ chainComponents R.range A, R.clusterFactor (n * R.params.side) (Q x.1.2).storedField A (g x) Xc := by
    refine Finset.measurable_fun_prod _ fun Xc _ => ?_
    have h1 := (hrow.borel (n * R.params.side) hblock A).2.1 Xc
    exact h1.comp (hst.prodMk hgm)
  have hlev' : ∀ x : S (t, C, H), clusterFactorProduct (⟨Y, x.1.2⟩ : CoarseState R n) X =
      ∏ Xc ∈ chainComponents R.range A, R.clusterFactor (n * R.params.side) (Q x.1.2).storedField A (g x) Xc :=
    fun x => prod_chainComponents_congr (fun W B l Xc => R.clusterFactor (n * R.params.side) W B l Xc)
      R.range _ (hA x) _
  let Mb : Finset (TorusBond (n * R.params.side)) :=
    markedBonds R C ∩ bondsOverBlocks R.params.side (Q p₀.2).markedZone
  let Bd : Finset (TorusBond (n * R.params.side)) := (Q p₀.2).storedBadBonds
  have hmk : ∀ b ∈ Mb, Measurable fun x : S (t, C, H) => bondMark R x.1.1 (Q x.1.2).storedField b := by
    intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_inter.mp hb
    have hbc : b ∈ chartBonds R.params.side n := (Finset.mem_filter.mp hb1).1
    have hbC : parentBlock R.params.side b.1 ∉ C := (Finset.mem_filter.mp hb1).2
    have hbz : parentBlock R.params.side b.1 ∈ (Q p₀.2).markedZone := (Finset.mem_filter.mp hb2).2.1
    refine measurable_bondMark hFC hCC hfit hch hσ hcut hm hn64 hbc hx1 hst ?_ ?_
    · intro _ x
      refine coldNearSite_of_not_mem hfit hLn (hadm x).eq_thickening ?_ (by rw [hCx x]; exact hbC) hm2
      rw [markedZone_eq (hsh' x)]
      exact hbz
    · intro hbig x
      refine isCold_of_not_mem hfit hLn (hadm x).eq_thickening ?_ (by rw [hCx x]; exact hbC) (hsm hbig)
      rw [markedZone_eq (hsh' x)]
      exact hbz
  have hmark : Measurable fun x : S (t, C, H) => ∏ b ∈ Mb,
      if b ∈ Bd then 1 - bondMark R x.1.1 (Q x.1.2).storedField b
      else bondMark R x.1.1 (Q x.1.2).storedField b := by
    refine Finset.measurable_fun_prod _ fun b hb => ?_
    by_cases hbd : b ∈ Bd
    · simp only [hbd, if_true]
      exact measurable_const.sub (hmk b hb)
    · simp only [hbd, if_false]
      exact hmk b hb
  have hmark' : ∀ x : S (t, C, H), markFactorProduct x.1.1 (⟨Y, x.1.2⟩ : CoarseState R n) X = ∏ b ∈ Mb,
      if b ∈ Bd then 1 - bondMark R x.1.1 (Q x.1.2).storedField b
      else bondMark R x.1.1 (Q x.1.2).storedField b := by
    intro x
    show (∏ b ∈ markedBonds R (hotNeighbourhoodOn R X x.1.1) ∩
        bondsOverBlocks R.params.side (Q x.1.2).markedZone,
      if b ∈ (Q x.1.2).storedBadBonds then 1 - bondMark R x.1.1 (Q x.1.2).storedField b
      else bondMark R x.1.1 (Q x.1.2).storedField b) = _
    rw [hCx x, markedZone_eq (hsh' x), storedBadBonds_eq (hsh' x)]
  have hbase : ∀ x : S (t, C, H), baseFactorProduct (⟨Y, x.1.2⟩ : CoarseState R n) X =
      baseFactorProduct (⟨Y, p₀.2⟩ : CoarseState R n) X := fun x =>
    baseFactorProduct_congr (hsh' x) (hHx x).symm
  have e : (fun x : S (t, C, H) => coarseFactorExpansion R n x.1.1 Y x.1.2 X) = fun x =>
      1 * (∏ Xc ∈ chainComponents R.range A,
        R.clusterFactor (n * R.params.side) (Q x.1.2).storedField A (g x) Xc) * (∏ b ∈ Mb,
        if b ∈ Bd then 1 - bondMark R x.1.1 (Q x.1.2).storedField b
        else bondMark R x.1.1 (Q x.1.2).storedField b) *
      baseFactorProduct (⟨Y, p₀.2⟩ : CoarseState R n) X := by
    funext x
    rw [hval]
    have ht : admissibilityIndicator x.1.1 (⟨Y, x.1.2⟩ : CoarseState R n) X = 1 := by
      show (if (Q x.1.2).IsAdmissibleCoarseState (hotNeighbourhoodOn R X x.1.1) X then (1 : ℝ) else 0) = 1
      rw [hCx x, if_pos (hadm x)]
    simp only [coarseFactor]
    rw [ht, hlev' x, hmark' x, hbase x]
  show Measurable fun x : S (t, C, H) => coarseFactorExpansion R n x.1.1 Y x.1.2 X
  rw [e]
  exact ((measurable_const.mul hlev).mul hmark).mul measurable_const
end YangMills.Construction
end
