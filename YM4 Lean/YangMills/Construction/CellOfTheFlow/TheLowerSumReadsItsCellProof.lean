import YangMills.Construction.CellOfTheFlow.BlocksOfACellAreACell
import YangMills.Construction.CellOfTheFlow.MomentsOfTheClassesNearABoxProof
import YangMills.Construction.CellOfTheFlow.TheChainReadsItsCellProof
import YangMills.Construction.CellOfTheFlow.TheDrawOfTheNoiseIsBorel
import YangMills.Construction.CellOfTheFlow.TheLowerSumReadsItsCell
import YangMills.Construction.ResponseInTheExpansion.LawOfTheDrawsBelowProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses BlockAverages LumpContours
namespace LowerScoreSumLocality
section LowerRule
variable {ℓ : StepParameters}
private theorem mem_interiorAtDepth_of_le {n : ℕ} [NeZero n] {a b : ℕ} (h : a ≤ b) {c : Finset (TorusSite n)}
    {v : TorusSite n} (hv : v ∈ interiorAtDepth b c) : v ∈ interiorAtDepth a c := by apply _root_.YangMills.SharedProofs.p110460 <;> assumption
private theorem mem_sitesInBlocks_iff {n : ℕ} [NeZero n] {L : ℕ} [NeZero L] {S : Finset (TorusSite n)}
    {x : TorusSite (n * L)} : x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.Construction.CongruentBoxes.mem_sitesInBlocks <;> assumption
private theorem lowerZone_congr (T : StageTower ℓ) (k s : ℕ) {n : ℕ} [NeZero n] {C C' : Finset (TorusSite n)}
    {bad bad' : Finset (TorusBond (n * ℓ.side))} (Y : Finset (TorusSite (n * ℓ.side))) (c : Finset (TorusSite n))
    (hC : ∀ z ∈ interiorAtDepth (blockDepth T k s) c, (z ∈ C ↔ z ∈ C'))
    (hb : ∀ b : TorusBond (n * ℓ.side), b.1 ∈ sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) c) →
      (b ∈ bad ↔ b ∈ bad')) :
    lowerZone T k s C bad Y c = lowerZone T k s C' bad' Y c := by
  classical
  set D := interiorAtDepth (blockDepth T k s) c with hD
  set Rw := sitesInBlocks ℓ.side D with hRw
  have hX : windowSeeds ℓ.side bad Y C Rw = windowSeeds ℓ.side bad' Y C' Rw := by
    ext x
    unfold windowSeeds
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_image]
    refine and_congr_left fun hx => ?_
    have hblk : parentBlock ℓ.side x ∈ D := mem_sitesInBlocks_iff.mp hx
    have e1 : (∃ b ∈ bad, b.1 = x) ↔ ∃ b ∈ bad', b.1 = x := by
      constructor
      · rintro ⟨b, hb1, rfl⟩
        exact ⟨b, (hb b hx).mp hb1, rfl⟩
      · rintro ⟨b, hb1, rfl⟩
        exact ⟨b, (hb b hx).mpr hb1, rfl⟩
    have e2 : x ∈ sitesInBlocks ℓ.side C ↔ x ∈ sitesInBlocks ℓ.side C' := by
      rw [mem_sitesInBlocks_iff, mem_sitesInBlocks_iff]
      exact hC _ hblk
    rw [e1, e2]
  have hA : lowerAttached ℓ.side (stageRange T s) (windowSeeds ℓ.side bad Y C Rw) (sitesInBlocks ℓ.side C) =
      lowerAttached ℓ.side (stageRange T s) (windowSeeds ℓ.side bad' Y C' Rw) (sitesInBlocks ℓ.side C') := by
    rw [← hX]
    unfold lowerAttached
    congr 1
    refine Finset.filter_congr fun K hK => ?_
    have hsub : K ⊆ windowSeeds ℓ.side bad Y C Rw := by
      unfold chainComponents at hK
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hK
      exact Finset.filter_subset _ _
    have hR : ∀ x ∈ K, parentBlock ℓ.side x ∈ D := fun x hx =>
      mem_sitesInBlocks_iff.mp (Finset.mem_inter.mp (hsub hx)).2
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hx
      exact ⟨x, Finset.mem_inter.mpr ⟨h1,
        mem_sitesInBlocks_iff.mpr ((hC _ (hR x h1)).mp (mem_sitesInBlocks_iff.mp h2))⟩⟩
    · rintro ⟨x, hx⟩
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hx
      exact ⟨x, Finset.mem_inter.mpr ⟨h1,
        mem_sitesInBlocks_iff.mpr ((hC _ (hR x h1)).mpr (mem_sitesInBlocks_iff.mp h2))⟩⟩
  unfold lowerZone windowZone
  rw [← hD, ← hRw, hA]
  ext y
  simp only [Finset.mem_inter, Finset.mem_union]
  refine and_congr_left fun hy => ?_
  rw [hC y hy]
private def EvaluationsAgree (T : StageTower ℓ) (k : ℕ) : (s n : ℕ) → [NeZero n] → Finset (TorusSite n) →
    MarkedSample ℓ s n → MarkedSample ℓ s n → Prop
  | 0, n, _, c, W, W' => lowerHull T k 0 n W c = lowerHull T k 0 n W' c
  | s + 1, n, _, c, u, u' =>
      EvaluationsAgree T k s (n * ℓ.side) (sitesInBlocks ℓ.side c) u.1 u'.1 ∧
      (∀ z ∈ interiorAtDepth (4 * stageRange T (s + 1)) c,
        (z ∈ hotCoreSites (T.stage s).toStepSetup u.2.2.1 ↔ z ∈ hotCoreSites (T.stage s).toStepSetup u'.2.2.1)) ∧
      ∀ b : TorusBond (n * ℓ.side), b.1 ∈ sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) c) →
        (b ∈ (show Finset (TorusBond (n * ℓ.side)) from u.2.2.2) ↔
          b ∈ (show Finset (TorusBond (n * ℓ.side)) from u'.2.2.2))
private theorem lowerZone_eq_of_agree (T : StageTower ℓ) (k s : ℕ) {n : ℕ} [NeZero n] {c : Finset (TorusSite n)}
    {u u' : MarkedSample ℓ (s + 1) n}
    (hY : lowerHull T k s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c) =
      lowerHull T k s (n * ℓ.side) u'.1 (sitesInBlocks ℓ.side c))
    (hC : ∀ z ∈ interiorAtDepth (4 * stageRange T (s + 1)) c,
        (z ∈ hotCoreSites (T.stage s).toStepSetup u.2.2.1 ↔ z ∈ hotCoreSites (T.stage s).toStepSetup u'.2.2.1))
    (hb : ∀ b : TorusBond (n * ℓ.side), b.1 ∈ sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) c) →
        (b ∈ (show Finset (TorusBond (n * ℓ.side)) from u.2.2.2) ↔
          b ∈ (show Finset (TorusBond (n * ℓ.side)) from u'.2.2.2))) :
    lowerZone T k s (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.2
        (lowerHull T k s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c)) c =
      lowerZone T k s (hotCoreSites (T.stage s).toStepSetup u'.2.2.1) u'.2.2.2
        (lowerHull T k s (n * ℓ.side) u'.1 (sitesInBlocks ℓ.side c)) c := by
  rw [hY]
  exact lowerZone_congr T k s _ c
    (fun z hz => hC z (mem_interiorAtDepth_of_le (le_max_left _ _) hz)) hb
private theorem lowerHull_lowerScore_eq_of_agree (T : StageTower ℓ) (k : ℕ) (s₀ s₁ : ℝ) : ∀ (s n : ℕ) [NeZero n]
    (c : Finset (TorusSite n)) (u u' : MarkedSample ℓ s n), EvaluationsAgree T k s n c u u' →
    lowerHull T k s n u c = lowerHull T k s n u' c ∧
      ∀ y, lowerScore T k s₀ s₁ s n u c y = lowerScore T k s₀ s₁ s n u' c y := by
  intro s
  induction s with
  | zero =>
    intro n _ c u u' h
    have h' : lowerHull T k 0 n u c = lowerHull T k 0 n u' c := h
    refine ⟨h', fun y => ?_⟩
    simp only [lowerScore, h']
  | succ s ih =>
    intro n _ c u u' h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨hY, hS⟩ := ih (n * ℓ.side) (sitesInBlocks ℓ.side c) u.1 u'.1 h1
    have hZ := lowerZone_eq_of_agree T k s hY h2 h3
    have hH : lowerHull T k (s + 1) n u c = lowerHull T k (s + 1) n u' c := by
      simp only [lowerHull]
      rw [hZ]
    refine ⟨hH, fun y => ?_⟩
    simp only [lowerScore]
    rw [hH, hZ]
    simp only [hS]
end LowerRule
section Measurability
variable {X : Type} [MeasurableSpace X]
private theorem measurableSet_comp_fibre {A D : Type} [Countable A] {f : X → A}
    (hf : ∀ a, MeasurableSet {x | f x = a}) (F : A → D) (d : D) : MeasurableSet {x | F (f x) = d} := by apply _root_.YangMills.SharedProofs.p22983 <;> assumption
private theorem measurableSet_prod_fibre {A B : Type} {f : X → A} {g : X → B}
    (hf : ∀ a, MeasurableSet {x | f x = a}) (hg : ∀ b, MeasurableSet {x | g x = b}) (p : A × B) :
    MeasurableSet {x | (f x, g x) = p} := by
  have e : {x | (f x, g x) = p} = {x | f x = p.1} ∩ {x | g x = p.2} := by
    ext x
    simp [Prod.ext_iff]
  rw [e]
  exact (hf _).inter (hg _)
abbrev _root_.YangMills.SharedProofs.p66564 := @measurableSet_prod_fibre
private theorem measurable_of_measurableSet_fibres {D Z : Type} [Countable D] [MeasurableSpace Z] (f : X → D)
    (hf : ∀ d, MeasurableSet {x | f x = d}) (G : D → X → Z) (hG : ∀ d, Measurable (G d)) :
    Measurable fun x => G (f x) x := by apply _root_.YangMills.SharedProofs.p23008 <;> assumption
private theorem measurableSet_mem_of_fibres {S : Type} {f : X → Finset S} [Countable (Finset S)]
    (hf : ∀ a, MeasurableSet {x | f x = a}) (y : S) : MeasurableSet {x | y ∈ f x} := by
  have e : {x | y ∈ f x} = ⋃ a ∈ {a : Finset S | y ∈ a}, {x | f x = a} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨a, h, h'⟩ => by rw [h']; exact h⟩
  rw [e]
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ => hf a
variable {ℓ : StepParameters}
private theorem measurable_lowerPart (s n : ℕ) : Measurable fun u : MarkedSample ℓ (s + 1) n => u.1 := by apply _root_.YangMills.SharedProofs.p1941 <;> assumption
private theorem measurable_upperField (s n : ℕ) : Measurable fun u : MarkedSample ℓ (s + 1) n => u.2.2.1 :=
  letI := markedSampleMeasurableSpace ℓ s (n * ℓ.side)
  ((measurable_fst.comp (measurable_snd.comp measurable_snd)) :
    Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.2.2.1)
private theorem measurableSet_badBonds_fibre (s n : ℕ) (a : Finset (TorusBond (n * ℓ.side))) :
    MeasurableSet {u : MarkedSample ℓ (s + 1) n | (show Finset (TorusBond (n * ℓ.side)) from u.2.2.2) = a} :=
  letI := markedSampleMeasurableSpace ℓ s (n * ℓ.side)
  have hm : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  hm (show MeasurableSet ({a} : Set (BondSet (n * ℓ.side))) from trivial)
private theorem measurableSet_torusHotSites_fibre (hfit : ℓ.Admissible) {n : ℕ} [NeZero n] (hL : ℓ.side ∣ n)
    (A : Finset (TorusSite n)) : MeasurableSet {W : TorusField n | torusHotSites ℓ W = A} :=
  measurableSet_comp_fibre (f := fun W : TorusField n => torusHotLumps ℓ W)
    (fun H => measurableSet_torusHotLumps_eq hfit hL H) (fun H => H.biUnion id) A
private theorem measurableSet_hotCoreSites_fibre (R : StepSetup) (hfit : R.params.Admissible) {n : ℕ} [NeZero n]
    (hL : R.params.side ∣ n) (A : Finset (TorusSite n)) : MeasurableSet {V : TorusField n | hotCoreSites R V = A} :=
  measurableSet_comp_fibre (f := fun V : TorusField n => torusHotSites R.params V)
    (measurableSet_torusHotSites_fibre hfit hL) (fun H => thickening (2 * R.nextRange) H) A
variable (T : StageTower ℓ) (k : ℕ)
private theorem measurableSet_lowerZone_fibre (hfit : ℓ.Admissible) {s n : ℕ} [NeZero n] (hL : ℓ.side ∣ n)
    {c : Finset (TorusSite n)} {f : MarkedSample ℓ s (n * ℓ.side) → Finset (TorusSite (n * ℓ.side))}
    (hf : ∀ a, MeasurableSet {u | f u = a}) (A : Finset (TorusSite n)) :
    MeasurableSet {u : MarkedSample ℓ (s + 1) n |
      lowerZone T k s (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.2 (f u.1) c = A} := by
  have h1 : ∀ a, MeasurableSet {u : MarkedSample ℓ (s + 1) n |
      hotCoreSites (T.stage s).toStepSetup u.2.2.1 = a} := fun a =>
    measurable_upperField s n (measurableSet_hotCoreSites_fibre (T.stage s).toStepSetup hfit hL a)
  have h2 : ∀ a, MeasurableSet {u : MarkedSample ℓ (s + 1) n | f u.1 = a} := fun a =>
    measurable_lowerPart s n (hf a)
  exact measurableSet_comp_fibre
    (f := fun u : MarkedSample ℓ (s + 1) n => (hotCoreSites (T.stage s).toStepSetup u.2.2.1,
      ((show Finset (TorusBond (n * ℓ.side)) from u.2.2.2), f u.1)))
    (measurableSet_prod_fibre h1 (measurableSet_prod_fibre (measurableSet_badBonds_fibre s n) h2))
    (fun p => lowerZone T k s p.1 p.2.1 p.2.2 c) A
private theorem measurableSet_lowerHull_fibre (hfit : ℓ.Admissible) : ∀ (s n : ℕ) [NeZero n], ℓ.side ∣ n →
    ∀ (c A : Finset (TorusSite n)), MeasurableSet {u : MarkedSample ℓ s n | lowerHull T k s n u c = A} := by
  intro s
  induction s with
  | zero =>
    intro n _ hL c A
    exact measurableSet_comp_fibre (f := fun W : TorusField n => torusHotSites ℓ W)
      (measurableSet_torusHotSites_fibre hfit hL)
      (fun H => thickening (2 * clusterRange T.base.coupling) H ∩ interiorAtDepth (windowDepth T k 0) c) A
  | succ s ih =>
    intro n _ hL c A
    have hz := measurableSet_lowerZone_fibre T k hfit hL (s := s) (c := c)
      (ih (n * ℓ.side) (Dvd.intro_left n rfl) (sitesInBlocks ℓ.side c))
    exact measurableSet_comp_fibre (f := fun u : MarkedSample ℓ (s + 1) n =>
      lowerZone T k s (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.2
        (lowerHull T k s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c)) c) hz
      (fun Z => thickening (stageRange T (s + 1) / 2) Z) A
private theorem measurable_lowerScore (hfit : ℓ.Admissible) (s₀ s₁ : ℝ) : ∀ (s n : ℕ) [NeZero n], ℓ.side ∣ n →
    ∀ (c : Finset (TorusSite n)) (y : TorusSite n),
      Measurable fun u : MarkedSample ℓ s n => lowerScore T k s₀ s₁ s n u c y := by
  classical
  intro s
  induction s with
  | zero =>
    intro n _ hL c y
    simp only [lowerScore]
    exact Measurable.ite (measurableSet_mem_of_fibres (measurableSet_lowerHull_fibre T k hfit 0 n hL c) y)
      measurable_const measurable_const
  | succ s ih =>
    intro n _ hL c y
    have hL' : ℓ.side ∣ n * ℓ.side := Dvd.intro_left n rfl
    have hz := measurableSet_lowerZone_fibre T k hfit hL (s := s) (c := c)
      (measurableSet_lowerHull_fibre T k hfit s (n * ℓ.side) hL' (sitesInBlocks ℓ.side c))
    simp only [lowerScore]
    refine Measurable.ite (measurableSet_mem_of_fibres (measurableSet_lowerHull_fibre T k hfit (s + 1) n hL c) y)
      (measurable_const.add (Measurable.ite (measurableSet_mem_of_fibres hz y) ?_ measurable_const))
      measurable_const
    exact Finset.measurable_sum _ fun z _ =>
      (ih (n * ℓ.side) hL' (sitesInBlocks ℓ.side c) z).comp (measurable_lowerPart s n)
private theorem measurable_lowerScoreSum (hfit : ℓ.Admissible) (s₀ s₁ : ℝ) (s n : ℕ) [NeZero n]
    (hL : ℓ.side ∣ n) (c : Finset (TorusSite n)) :
    Measurable fun u : MarkedSample ℓ s n => lowerScoreSum T k s₀ s₁ s n u c := by
  classical
  unfold lowerScoreSum
  exact measurable_of_measurableSet_fibres (fun u : MarkedSample ℓ s n => lowerHull T k s n u c)
    (measurableSet_lowerHull_fibre T k hfit s n hL c) (fun A u => ∑ y ∈ A, lowerScore T k s₀ s₁ s n u c y)
    fun A => Finset.measurable_sum _ fun y _ => measurable_lowerScore T k hfit s₀ s₁ s n hL c y
abbrev _root_.YangMills.SharedProofs.p15189 := @measurable_lowerScoreSum
end Measurability
section ChainInCoordinates
variable {ℓ : StepParameters} {T : StageTower ℓ} {S : ChainSampler T} {k : ℕ}
private theorem valuesAgree_of_local (hb : cellBlocksEqRefinedCellStatement)
    (c2 : ∀ (m : ℕ) [NeZero m] (G : CellGrid) (κ : Fin 4 → ℤ), G.Compatible m → ∀ (U U' : TorusField m),
      FieldsAgreeOn (G.cell m κ) U U' → ∀ z ∈ interiorAtDepth (windowDepth T k 0) (G.cell m κ),
        (z ∈ stageHull T 0 m U ↔ z ∈ stageHull T 0 m U'))
    (c3 : ∀ (s : ℕ), s < k → ∀ (m : ℕ) [NeZero m] (G : CellGrid) (κ : Fin 4 → ℤ), G.Compatible m →
      ∀ (U U' : TorusField (fineSide ℓ.side (s + 1) m)) (ξ ξ' : ChainNoise ℓ (s + 1) m),
        FieldsAgreeOn (cellBelow ℓ.side (s + 1) m (G.cell m κ)) U U' →
        NoiseAgreesOn ℓ (s + 1) m (G.cell m κ) ξ ξ' →
        (∀ z ∈ interiorAtDepth (4 * stageRange T (s + 1)) (G.cell m κ),
          (z ∈ hotCoreSites (T.stage s).toStepSetup (sampleChain T S (s + 1) m U ξ).2.2.1 ↔
            z ∈ hotCoreSites (T.stage s).toStepSetup (sampleChain T S (s + 1) m U' ξ').2.2.1)) ∧
        ∀ b : TorusBond (m * ℓ.side),
          b.1 ∈ sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) (G.cell m κ)) →
          (b ∈ (show Finset (TorusBond (m * ℓ.side)) from (sampleChain T S (s + 1) m U ξ).2.2.2) ↔
            b ∈ (show Finset (TorusBond (m * ℓ.side)) from (sampleChain T S (s + 1) m U' ξ').2.2.2))) :
    ∀ (s : ℕ), s ≤ k → ∀ (m : ℕ) [NeZero m] (G : CellGrid) (κ : Fin 4 → ℤ), G.Compatible m →
      ∀ (U U' : TorusField (fineSide ℓ.side s m)) (ξ ξ' : ChainNoise ℓ s m),
        FieldsAgreeOn (cellBelow ℓ.side s m (G.cell m κ)) U U' → NoiseAgreesOn ℓ s m (G.cell m κ) ξ ξ' →
        EvaluationsAgree T k s m (G.cell m κ) (sampleChain T S s m U ξ) (sampleChain T S s m U' ξ') := by
  intro s
  induction s with
  | zero =>
    intro _ m _ G κ hG U U' ξ ξ' hF _
    show lowerHull T k 0 m U (G.cell m κ) = lowerHull T k 0 m U' (G.cell m κ)
    ext z
    simp only [lowerHull, Finset.mem_inter]
    exact and_congr_left fun hz => c2 m G κ hG U U' hF z hz
  | succ s ih =>
    intro hs m _ G κ hG U U' ξ ξ' hF hN
    have e := hb ℓ.side G m κ
    have hG' : (G.refine ℓ.side).Compatible (m * ℓ.side) := by
      refine ⟨Nat.mul_pos hG.side_pos (Nat.pos_of_ne_zero (NeZero.ne ℓ.side)), ?_⟩
      obtain ⟨w, hw⟩ := hG.two_mul_side_dvd
      show 2 * (G.side * ℓ.side) ∣ m * ℓ.side
      exact ⟨w, by rw [hw]; ring⟩
    have hc := c3 s (by omega) m G κ hG U U' ξ ξ' hF hN
    refine ⟨?_, hc.1, hc.2⟩
    have hF' : FieldsAgreeOn (cellBelow ℓ.side s (m * ℓ.side) (sitesInBlocks ℓ.side (G.cell m κ))) U U' := hF
    obtain ⟨hN', -⟩ := hN
    rw [e] at hF' hN'
    show EvaluationsAgree T k s (m * ℓ.side) (sitesInBlocks ℓ.side (G.cell m κ))
      (sampleChain T S s (m * ℓ.side) U ξ.1) (sampleChain T S s (m * ℓ.side) U' ξ'.1)
    rw [e]
    exact ih (by omega) (m * ℓ.side) (G.refine ℓ.side) κ hG' U U' ξ.1 ξ'.1 hF' hN'
end ChainInCoordinates
end LowerScoreSumLocality
open LowerScoreSumLocality in
theorem lowerScoreSum_isLocal (hchain : chainLocalityStatement)
    (hblocks : cellBlocksEqRefinedCellStatement) (hdraw : sampleChainMeasurableStatement) :
    lowerSumLocalStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, hpos, h⟩ := hchain a ha
  refine ⟨L₀, rt₀, hpos, fun L hodd hL Tb hTa hTL hD hrt => ?_⟩
  obtain ⟨y₀, hy⟩ := h L hodd hL Tb hTa hTL hD hrt
  refine ⟨max y₀ Tb.floorMin, fun y hyy hrow hhas => ?_⟩
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y (le_trans (le_max_right _ _) hyy)
  have hcl := hy y (le_trans (le_max_left _ _) hyy) hrow hhas
  intro T S β s₀ s₁ k hT hS m _ G κ hG hLm h64
  obtain ⟨-, c2, c3⟩ := hcl T S β k hT hS
  refine ⟨?_, fun U U' ξ ξ' hF hN => ?_⟩
  · exact (measurable_lowerScoreSum T k hfit s₀ s₁ k m hLm _).comp
      (hdraw _ hfit T S hT.measurable hS k m hLm h64)
  · obtain ⟨h1, h2⟩ := lowerHull_lowerScore_eq_of_agree T k s₀ s₁ k m _ _ _
      (valuesAgree_of_local hblocks c2 c3 k le_rfl m G κ hG U U' ξ ξ' hF hN)
    unfold lowerScoreSum
    rw [h1]
    exact Finset.sum_congr rfl fun y _ => h2 y
end YangMills.Construction.CellWindows
end
