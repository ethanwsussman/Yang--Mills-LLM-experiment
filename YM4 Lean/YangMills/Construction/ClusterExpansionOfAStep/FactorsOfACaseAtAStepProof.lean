import YangMills.Construction.ClusterExpansionOfAStep.FactorsAtACaseProof
import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfACaseAtAStep
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields TorusLumps StepSettings StepCosts BlockAverages LumpContours GaugeFixing TorusContours
  TopLevelSites TorusBlocks TorusBalls BlockPlaces BlockSites
namespace CaseFactors
section Components
variable {m : ℕ} [NeZero m]
theorem chainComponents_eq_biUnion {ι : Type} [DecidableEq (Finset (TorusSite m))] {r : ℕ}
    {S : Finset (TorusSite m)} (I : Finset ι)
    (P : ι → Finset (TorusSite m)) (hsub : ∀ i ∈ I, P i ⊆ S) (hcov : ∀ z ∈ S, ∃ i ∈ I, z ∈ P i)
    (hclosed : ∀ i ∈ I, ∀ u ∈ P i, ∀ v ∈ S, _root_.YangMills.Construction.TorusFields.supDist u v ≤ r → v ∈ P i) :
    chainComponents r S = I.biUnion fun i => chainComponents r (P i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.chainComponents_eq_biUnion <;> assumption
theorem chainComponents_eq_of_mem {r : ℕ} {Y X X' : Finset (TorusSite m)} (hX : X ∈ chainComponents r Y)
    (hX' : X' ∈ chainComponents r Y) {u : TorusSite m} (hu : u ∈ X) (hu' : u ∈ X') : X = X' :=
  eq_of_chainConnected_of_mem_chainComponents hX hX' hu hu' Relation.ReflTransGen.refl
theorem chainComponents_nonempty {r : ℕ} {Y X : Finset (TorusSite m)} (hX : X ∈ chainComponents r Y) :
    X.Nonempty := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.nonempty_of_mem_chainComponents <;> assumption
theorem mem_chainComponents_of_supDist_le {r : ℕ} {Y X : Finset (TorusSite m)} (hX : X ∈ chainComponents r Y)
    {y y' : TorusSite m} (hy : y ∈ X) (hy' : y' ∈ Y) (h : _root_.YangMills.Construction.TorusFields.supDist y y' ≤ r) : y' ∈ X := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.mem_of_mem_chainComponents_of_supDist_le <;> assumption
end Components
section Chart
variable {L n : ℕ} [NeZero L] [NeZero n]
theorem parentBlock_toTorusSite (hL : Odd L) (x : (stepBlockFrame L n).Site 0) :
    parentBlock L (toTorusSite (n * L) x) = toTorusSite n (enclosingCell x : (stepBlockFrame L n).Cell) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.parentBlock_toTorusSite <;> assumption
theorem chartCoord_congr (ℓ : StepParameters) (hodd : Odd ℓ.side) (S : Finset (TorusSite n))
    (V : TorusField n) (W W' : TorusField (n * ℓ.side))
    (h : ∀ x i, parentBlock ℓ.side x ∈ S →
      parentBlock ℓ.side (x + TorusFields.unitStep (n * ℓ.side) i) ∈ S → W x i = W' x i)
    (c : TorusBond (n * ℓ.side)) (h1 : parentBlock ℓ.side c.1 ∈ S)
    (h2 : parentBlock ℓ.side (c.1 + TorusFields.unitStep (n * ℓ.side) c.2) ∈ S) :
    chartCoord ℓ V W c = chartCoord ℓ V W' c := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.chartCoord_congr <;> assumption
end Chart
section Bases
theorem nearbyLumps_congr {F : BlockFrame} {h h' : Finset (Finset (F.Site F.depth))} {y : F.Cell}
    (H : ∀ l, l ⊆ cutBelow F.depth (cellBall y 2) → (l ∈ h ↔ l ∈ h')) :
    nearbyLumps h y = nearbyLumps h' y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.nearbyLumps_ext <;> assumption
theorem enclosingCell_of_subset_cutBelow {F : BlockFrame} (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {r : ℕ} {l : Finset (F.Site F.depth)} {y : F.Cell} (hU : l ⊆ cutBelow F.depth (cellBall y r))
    {z : F.Site F.depth} (hz : z ∈ l) :
    ∃ c : Fin 4 → ℤ, (∀ i, |c i| ≤ r) ∧ enclosingCell z = y + siteOfCoords F.top c :=
  mem_cellBall_iff.mp ((mem_cutBelow_iff hodd hs).mp (hU hz))
theorem blockBaseWeight_congr {n : ℕ} (ℓ : StepParameters)
    {h h' : Finset (Finset ((stepBlockFrame ℓ.side n).Site 0))}
    {y : (stepBlockFrame ℓ.side n).Cell} (z : (stepBlockFrame ℓ.side n).Site 0)
    (e : nearbyLumps (F := stepBlockFrame ℓ.side n) h y = nearbyLumps (F := stepBlockFrame ℓ.side n) h' y) :
    blockBaseWeight ℓ h y z = blockBaseWeight ℓ h' y z := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.blockBaseWeight_congr <;> assumption
variable {n : ℕ} [NeZero n]
open Classical in
theorem mem_frameHotLumps_iff (ℓ : StepParameters) (S : Finset (TorusSite (n * ℓ.side)))
    (W : TorusField (n * ℓ.side)) (l : Finset ((stepBlockFrame ℓ.side n).Site 0)) :
    l ∈ frameHotLumps ℓ S W ↔ l.image (toTorusSite (n * ℓ.side)) ∈ hotLumpsOn ℓ S W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.mem_frameHotLumps_iff <;> assumption
open Classical in
theorem mem_stepHotLumps_iff (ℓ : StepParameters) (W : TorusField (n * ℓ.side))
    (l : Finset ((stepBlockFrame ℓ.side n).Site 0)) :
    l ∈ stepHotLumps ℓ W ↔ l.image (toTorusSite (n * ℓ.side)) ∈ torusHotLumps ℓ W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.mem_stepHotLumps_iff <;> assumption
end Bases
section Case
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem fieldWithStoredLinks_restrict (q : CoarseState R n) (X : Finset (TorusSite n))
    (W : TorusField (n * R.params.side))
    (x : TorusSite (n * R.params.side)) (i : Fin 4) (hx : parentBlock R.params.side x ∈ X) :
    (q.restrict X).fieldWithStoredLinks W x i = q.fieldWithStoredLinks W x i := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentAdmission.fieldWithStoredLinks_restrict <;> assumption
theorem curvature_congr {m : ℕ} {W W' : TorusField m} {x : TorusSite m} {μ ν : Fin 4} (h1 : W x μ = W' x μ)
    (h2 : W (x + TorusFields.unitStep m μ) ν = W' (x + TorusFields.unitStep m μ) ν)
    (h3 : W (x + TorusFields.unitStep m ν) μ = W' (x + TorusFields.unitStep m ν) μ)
    (h4 : W x ν = W' x ν) : curvature W x μ ν = curvature W' x μ ν := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentAdmission.curvature_congr <;> assumption
theorem supDist_parentBlock_le_nextRange (hR : R.ReadsCaseTests) {u v : TorusSite (n * R.params.side)}
    (h : _root_.YangMills.Construction.TorusFields.supDist u v ≤ 10 * R.range) :
    _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side u) (parentBlock R.params.side v) ≤ R.nextRange := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentAdmission.supDist_parentBlock_le_nextRange <;> assumption
variable (hR : R.ReadsCaseTests) (V : TorusField n) (W : TorusField (n * R.params.side))
  (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
  (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
include hR in
theorem exists_near_attached_of_mem_storedBlocks (C : Finset (TorusSite n)) {y : TorusSite n}
    (hy : y ∈ storedBlocks R.params.side R.range bad Yt C) :
    ∃ v t, parentBlock R.params.side v = y ∧ t ∈ attachedSites R.params.side R.range bad Yt C ∧
      _root_.YangMills.Construction.TorusFields.supDist v t ≤ 4 * R.range := by
  classical
  rcases Finset.mem_union.mp hy with hC | hcore
  · have hb : parentBlock R.params.side (blockCentreSite R.params.side y) = y :=
      parentBlock_blockCentreSite hR.admissible.L_odd y
    refine ⟨blockCentreSite R.params.side y, blockCentreSite R.params.side y, hb,
      sitesInBlocks_subset_attachedSites R.range bad Yt C (mem_sitesInBlocks.mpr (hb.symm ▸ hC)), ?_⟩
    rw [_root_.YangMills.Construction.TorusFields.supDist_self]
    omega
  · obtain ⟨u, hu⟩ := (Finset.mem_filter.mp hcore).2
    obtain ⟨hu1, hu2⟩ := Finset.mem_inter.mp hu
    obtain ⟨t, ht, hut⟩ := (mem_thickening _ _ _).mp hu2
    exact ⟨u, t, Finset.mem_singleton.mp (mem_sitesInBlocks.mp hu1), ht, hut⟩
include hR in
theorem parentBlock_mem_storedBlocks_of_near_hot (C : Finset (TorusSite n))
    (hW : IsHullState R.params R.range W Yt) {y : TorusSite n}
    (hy : y ∈ storedBlocks R.params.side R.range bad Yt C) {z u : TorusSite (n * R.params.side)}
    (hz : z ∈ torusHotSites R.params W)
    (hd : _root_.YangMills.Construction.TorusFields.supDist y (parentBlock R.params.side z) ≤ 2) (hu : _root_.YangMills.Construction.TorusFields.supDist u z ≤ 4) :
    parentBlock R.params.side u ∈ storedBlocks R.params.side R.range bad Yt C ∧
      _root_.YangMills.Construction.TorusFields.supDist y (parentBlock R.params.side u) ≤ R.nextRange := by
  classical
  obtain ⟨v, t, hv, ht, hvt⟩ := exists_near_attached_of_mem_storedBlocks hR Yt bad C hy
  have hfar : _root_.YangMills.Construction.TorusFields.supDist v z ≤ 3 * R.params.side := by
    have h1 := _root_.YangMills.Construction.TorusBlocks.supDist_le_mul_supDist_parentBlock_add_one hR.admissible.L_odd v z
    rw [hv] at h1
    nlinarith
  have hblock := hR.range_ge_side
  have hLge := hR.admissible.L_ge
  have hvu : _root_.YangMills.Construction.TorusFields.supDist v u ≤ 3 * R.params.side + 4 := by
    have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle v z u
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm z u] at h1
    omega
  have htu : _root_.YangMills.Construction.TorusFields.supDist t u ≤ 10 * R.range := by
    have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle t v u
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm t v] at h1
    omega
  have huY : u ∈ Yt := hW.1 ((mem_thickening _ _ _).mpr ⟨z, hz, by omega⟩)
  have huθ := mem_attachedSites_of_supDist_le R.range bad Yt C ht
    (Finset.mem_union_left _ (Finset.mem_union_right _ huY)) htu
  refine ⟨parentBlock_mem_storedBlocks R.range bad Yt C huθ, ?_⟩
  have h2 := _root_.YangMills.Construction.ClusterExpansionOfAStep.CaseFactors.supDist_parentBlock_le_nextRange hR (u := v) (v := u) (by omega)
  rwa [hv] at h2
variable {q : CoarseState R n} {X : Finset (TorusSite n)}
include hR in
theorem storedField_restrict_eq (hq : coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = q)
    (x : TorusSite (n * R.params.side)) (i : Fin 4)
    (h1 : parentBlock R.params.side x ∈ (q.restrict X).markedZone)
    (h2 : parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) ∈ (q.restrict X).markedZone) :
    (q.restrict X).storedField x i = W x i := by
  subst hq
  have h1' := mem_controlRegion_restrict.mp h1
  have h2' := mem_controlRegion_restrict.mp h2
  rw [markedZone_coarseStateOf] at h1' h2'
  unfold CoarseState.storedField
  rw [fieldWithStoredLinks_restrict _ X _ x i h1'.2]
  exact fieldWithStoredLinks_coarseStateOf _ W Yt ωt bad b _ (x, i)
    ((mem_storedFieldBonds_coarseStateOf _ W Yt ωt bad b).mpr ⟨h1'.1, h2'.1⟩)
include hR in
theorem curvature_storedField_restrict (hq : coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = q)
    (x : TorusSite (n * R.params.side)) (μ ν : Fin 4)
    (h : ∀ z ∈ plaquetteVertices x μ ν, parentBlock R.params.side z ∈ (q.restrict X).markedZone) :
    curvature (q.restrict X).storedField x μ ν = curvature W x μ ν := by
  have c1 := h x (by simp [plaquetteVertices])
  have c2 := h (x + TorusFields.unitStep _ μ) (by simp [plaquetteVertices])
  have c3 := h (x + TorusFields.unitStep _ ν) (by simp [plaquetteVertices])
  have c4 := h (x + TorusFields.unitStep _ μ + TorusFields.unitStep _ ν) (by simp [plaquetteVertices])
  have c5 : parentBlock R.params.side (x + TorusFields.unitStep _ ν + TorusFields.unitStep _ μ) ∈
      (q.restrict X).markedZone := by
    rw [add_right_comm]
    exact c4
  have e := storedField_restrict_eq hR V W Yt ωt bad b (X := X) hq
  exact curvature_congr (e x μ c1 c2) (e _ ν c2 c4) (e _ μ c3 c5) (e x ν c1 c3)
include hR in
theorem nearbyLumps_frameHotLumps_restrict (hq : coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = q)
    (hW : IsHullState R.params R.range W Yt)
    (hX : X ∈ chainComponents R.nextRange q.1) {y : TorusSite n} (hy : y ∈ (q.restrict X).markedZone) :
    nearbyLumps (F := stepBlockFrame R.params.side n)
        (frameHotLumps R.params (sitesInBlocks R.params.side (q.restrict X).markedZone) (q.restrict X).storedField)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) =
      nearbyLumps (F := stepBlockFrame R.params.side n) (stepHotLumps R.params W)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) := by
  classical
  have hfit := hR.admissible
  have hodd := hfit.L_odd
  have hs : ∀ i, 0 < (stepBlockFrame R.params.side n).extent i := fun _ => Nat.pos_of_ne_zero (NeZero.ne n)
  have hp1 : ∀ i, (stepBlockFrame R.params.side n).period 1 i = n := fun i => stepBlockFrame_period_one i
  have hLn' : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
  have hyz := mem_controlRegion_restrict.mp hy
  have hZq : ∀ {w}, w ∈ storedBlocks R.params.side R.range bad Yt (hotCoreSites R V) → w ∈ q.1 := fun hw => by
    rw [← hq]
    exact storedBlocks_subset_coarseHull _ Yt bad hw
  have hzone : q.markedZone = storedBlocks R.params.side R.range bad Yt (hotCoreSites R V) := by
    rw [← hq]
    exact markedZone_coarseStateOf _ W Yt ωt bad b
  refine nearbyLumps_congr fun l hU => ?_
  refine (mem_frameHotLumps_iff _ _ _ l).trans (Iff.trans ?_ (mem_stepHotLumps_iff _ _ l).symm)
  constructor
  · intro hl
    obtain ⟨x, μ, ν, h1, h2, hS, z, hz, e⟩ := (mem_hotLumpsOn_iff R.params hfit hLn' _ _ _).mp hl
    refine (mem_torusHotLumps_iff R.params hfit hLn' W _).mpr ⟨x, μ, ν, h1, ?_, z, hz, e⟩
    rwa [curvature_storedField_restrict hR V W Yt ωt bad b hq x μ ν
      fun w hw => mem_sitesInBlocks.mp (hS w hw)] at h2
  · intro hl
    obtain ⟨x, μ, ν, h1, h2, z, hz, e⟩ := (mem_torusHotLumps_iff R.params hfit hLn' W _).mp hl
    have hzl : z ∈ l.image (toTorusSite (n * R.params.side)) := e ▸ mem_torusLumpOf_self z
    have hzhot : z ∈ torusHotSites R.params W := Finset.mem_biUnion.mpr ⟨_, hl, hzl⟩
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp hzl
    obtain ⟨h, hh, ehc⟩ := enclosingCell_of_subset_cutBelow (F := stepBlockFrame R.params.side n) hodd hs hU hz₀
    have hblock : parentBlock R.params.side (toTorusSite (n * R.params.side) z₀) = y + siteOfInt h := by
      have e1 : toTorusSite n ((torusSiteInFrame (stepBlockFrame R.params.side n) 1 y + siteOfCoords 1 h :
          (stepBlockFrame R.params.side n).Site 1)) = y + siteOfInt h := by
        rw [TopLevelSites.toTorusSite_add hp1, toTorusSite_torusSiteInFrame hp1, TopLevelSites.toTorusSite_siteOfCoords hp1]
      exact (parentBlock_toTorusSite hodd z₀).trans ((congrArg (toTorusSite n) ehc).trans e1)
    have hd : _root_.YangMills.Construction.TorusFields.supDist y (parentBlock R.params.side (toTorusSite (n * R.params.side) z₀)) ≤ 2 := by
      rw [hblock]
      refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => ?_
      have := hh i
      rw [abs_le] at this
      push_cast at this
      omega
    have hall : ∀ u ∈ plaquetteVertices x μ ν, parentBlock R.params.side u ∈ (q.restrict X).markedZone := by
      intro u hu
      obtain ⟨h3, h4⟩ := parentBlock_mem_storedBlocks_of_near_hot hR W Yt bad _ hW (hzone ▸ hyz.1) hzhot hd
        (_root_.YangMills.Construction.TorusLumps.supDist_le_four_of_mem_plaquetteVertices (x, μ, ν) hu hz)
      exact mem_controlRegion_restrict.mpr
        ⟨hzone ▸ h3, mem_chainComponents_of_supDist_le hX hyz.2 (hZq h3) h4⟩
    refine (mem_hotLumpsOn_iff R.params hfit hLn' _ _ _).mpr
      ⟨x, μ, ν, h1, ?_, fun u hu => mem_sitesInBlocks.mpr (hall u hu), _, hz, e⟩
    rw [curvature_storedField_restrict hR V W Yt ωt bad b hq x μ ν hall]
    exact h2
end Case
section Split
variable {R : StepSetup} {n : ℕ} [NeZero n]
variable (hR : R.ReadsCaseTests) (V : TorusField n) (W : TorusField (n * R.params.side))
  (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
  (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
variable {q : CoarseState R n}
theorem markedZone_subset (q : CoarseState R n) : q.markedZone ⊆ q.1 := Finset.filter_subset _ _
theorem markedZone_eq_biUnion (q : CoarseState R n) :
    q.markedZone = open Classical in
      (chainComponents R.nextRange q.1).biUnion fun X => (q.restrict X).markedZone := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.markedZone_eq_biUnion <;> assumption
theorem mem_labelSet_of_eq (hq : coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = q)
    {z : TorusSite (n * R.params.side)} :
    z ∈ q.labelSet ↔ z ∈ Yt ∧ parentBlock R.params.side z ∈ q.markedZone := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.mem_labelSet_of_eq <;> assumption
theorem mem_storedBadBonds_of_eq (hq : coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = q)
    {c : TorusBond (n * R.params.side)} :
    c ∈ q.storedBadBonds ↔ c ∈ bad ∧ parentBlock R.params.side c.1 ∈ q.markedZone := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.mem_storedBadBonds_of_eq <;> assumption
theorem labeling_restrict (hq : coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = q) {X : Finset (TorusSite n)}
    (z : TorusSite (n * R.params.side)) (hz : z ∈ (q.restrict X).labelSet) (hz' : z ∈ Yt) :
    (q.restrict X).labeling ⟨z, hz⟩ = ωt ⟨z, hz'⟩ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.labeling_restrict_of_eq <;> assumption
theorem mem_markedBonds_iff {C : Finset (TorusSite n)} {c : TorusBond (n * R.params.side)} :
    c ∈ markedBonds R C ↔ c ∈ chartBonds R.params.side n ∧ parentBlock R.params.side c.1 ∉ C := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.mem_markedBonds_iff <;> assumption
theorem mem_bondsOverBlocks_iff {L : ℕ} [NeZero L] {Z : Finset (TorusSite n)} {c : TorusBond (n * L)} :
    c ∈ bondsOverBlocks L Z ↔
      parentBlock L c.1 ∈ Z ∧ parentBlock L (c.1 + TorusFields.unitStep (n * L) c.2) ∈ Z := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.mem_bondsOverBlocks_iff <;> assumption
include hR in
theorem prod_clusterFactorProduct (hside : IsBlockTorusSide R.params n)
    (hq : coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = q) :
    ∏ X ∈ chainComponents R.nextRange q.1, clusterFactorProduct q X =
      ∏ Xc ∈ chainComponents R.range q.labelSet, R.clusterFactor (n * R.params.side) W Yt ωt Xc := by
  classical
  have hside' : IsBlockTorusSide R.params (n * R.params.side) := by
    refine ⟨Dvd.intro_left n rfl, hside.2.trans ?_⟩
    exact Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero (NeZero.ne R.params.side))
  have hcase := fun {z : TorusSite (n * R.params.side)} => mem_labelSet_of_eq V W Yt ωt bad b hq (z := z)
  have hcl : chainComponents R.range q.labelSet =
      (chainComponents R.nextRange q.1).biUnion fun X => chainComponents R.range (q.restrict X).labelSet := by
    refine chainComponents_eq_biUnion _ _ (fun X _ z hz => (mem_labelSet_restrict.mp hz).1) (fun z hz => ?_)
      (fun X hX u hu v hv hd => ?_)
    · obtain ⟨X, hX, hbX⟩ := exists_mem_chainComponents (r := R.nextRange) (markedZone_subset q (hcase.mp hz).2)
      exact ⟨X, hX, mem_labelSet_restrict.mpr ⟨hz, hbX⟩⟩
    · obtain ⟨h1, h2⟩ := mem_labelSet_restrict.mp hu
      have hd' := _root_.YangMills.Construction.ClusterExpansionOfAStep.CaseFactors.supDist_parentBlock_le_nextRange hR (u := u) (v := v) (by omega)
      exact mem_labelSet_restrict.mpr
        ⟨hv, mem_chainComponents_of_supDist_le hX h2 (markedZone_subset q (hcase.mp hv).2) hd'⟩
  have hdis : (↑(chainComponents R.nextRange q.1) : Set (Finset (TorusSite n))).PairwiseDisjoint
      fun X => chainComponents R.range (q.restrict X).labelSet := by
    intro X hX X' hX' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro A hA hA'
    obtain ⟨u, hu⟩ := chainComponents_nonempty hA
    exact hne (chainComponents_eq_of_mem hX hX'
      (mem_labelSet_restrict.mp (subset_of_mem_chainComponents hA hu)).2
      (mem_labelSet_restrict.mp (subset_of_mem_chainComponents hA' hu)).2)
  rw [hcl, Finset.prod_biUnion hdis]
  refine Finset.prod_congr rfl fun X hX => ?_
  unfold clusterFactorProduct
  refine Finset.prod_congr rfl fun Xc hXc => ?_
  have hsubX : Xc ⊆ (q.restrict X).labelSet := subset_of_mem_chainComponents hXc
  have hsubY : Xc ⊆ Yt := fun z hz => (hcase.mp (mem_labelSet_restrict.mp (hsubX hz)).1).1
  have hzoneOf : ∀ {u}, u ∈ Xc → parentBlock R.params.side u ∈ (q.restrict X).markedZone := fun hu =>
    mem_controlRegion_restrict.mpr
      ⟨(hcase.mp (mem_labelSet_restrict.mp (hsubX hu)).1).2, (mem_labelSet_restrict.mp (hsubX hu)).2⟩
  refine hR.hasExpansions.2.reads_class (n * R.params.side) hside' _ _ _ _ _ _ Xc hsubX hsubY (fun c h1 h2 => ?_)
    (fun z hz hz' _ => labeling_restrict V W Yt ωt bad b hq z hz hz')
  exact storedField_restrict_eq hR V W Yt ωt bad b hq c.1 c.2 (hzoneOf h1) (hzoneOf h2)
include hR in
theorem prod_markFactorProduct (hLn : R.params.side ∣ n)
    (hq : coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = q)
    (hv : IsHullState R.params R.nextRange V q.1) :
    open Classical in ∏ X ∈ chainComponents R.nextRange q.1, markFactorProduct V q X =
      ∏ c ∈ markedBonds R (hotCoreSites R V) ∩ bondsOverBlocks R.params.side q.markedZone,
        if c ∈ bad then 1 - bondMark R V W c else bondMark R V W c := by
  classical
  have hfit := hR.admissible
  have hr' := hR.nextRange_ge
  have hL2 : 2 ≤ R.params.side := by have := hfit.L_ge; omega
  have hCX : ∀ {X y}, X ∈ chainComponents R.nextRange q.1 → y ∈ X →
      (y ∈ hotNeighbourhoodOn R X V ↔ y ∈ hotCoreSites R V) :=
    fun hX hy => mem_hotNeighbourhoodOn_iff R hfit hLn hr' hv.1 hX hy
  have hsplit : markedBonds R (hotCoreSites R V) ∩ bondsOverBlocks R.params.side q.markedZone =
      (chainComponents R.nextRange q.1).biUnion fun X =>
        markedBonds R (hotNeighbourhoodOn R X V) ∩ bondsOverBlocks R.params.side (q.restrict X).markedZone := by
    ext c
    simp only [Finset.mem_inter, Finset.mem_biUnion, mem_bondsOverBlocks_iff, mem_markedBonds_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      obtain ⟨X, hX, hbX⟩ := exists_mem_chainComponents (r := R.nextRange) (markedZone_subset q h3)
      have hnear := _root_.YangMills.Construction.BlockPlaces.supDist_parentBlock_le_one hL2 c.1 (c.1 + TorusFields.unitStep (n * R.params.side) c.2)
        (_root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le _ _)
      have h5 := mem_chainComponents_of_supDist_le hX hbX (markedZone_subset q h4) (hnear.trans (by omega))
      exact ⟨X, hX, ⟨h1, fun h => h2 ((hCX hX hbX).mp h)⟩, mem_controlRegion_restrict.mpr ⟨h3, hbX⟩,
        mem_controlRegion_restrict.mpr ⟨h4, h5⟩⟩
    · rintro ⟨X, hX, ⟨h1, h2⟩, h3, h4⟩
      have h3' := mem_controlRegion_restrict.mp h3
      have h4' := mem_controlRegion_restrict.mp h4
      exact ⟨⟨h1, fun h => h2 ((hCX hX h3'.2).mpr h)⟩, h3'.1, h4'.1⟩
  have hdis : (↑(chainComponents R.nextRange q.1) : Set (Finset (TorusSite n))).PairwiseDisjoint
      fun X => markedBonds R (hotNeighbourhoodOn R X V) ∩ bondsOverBlocks R.params.side (q.restrict X).markedZone := by
    intro X hX X' hX' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro c hc hc'
    have h1 := (mem_bondsOverBlocks_iff.mp (Finset.mem_inter.mp hc).2).1
    have h2 := (mem_bondsOverBlocks_iff.mp (Finset.mem_inter.mp hc').2).1
    exact hne (chainComponents_eq_of_mem hX hX' (mem_controlRegion_restrict.mp h1).2 (mem_controlRegion_restrict.mp h2).2)
  rw [hsplit, Finset.prod_biUnion hdis]
  refine Finset.prod_congr rfl fun X hX => ?_
  unfold markFactorProduct
  refine Finset.prod_congr rfl fun c hc => ?_
  obtain ⟨h3, h4⟩ := mem_bondsOverBlocks_iff.mp (Finset.mem_inter.mp hc).2
  have h3' := mem_controlRegion_restrict.mp h3
  have hbad : c ∈ (q.restrict X).storedBadBonds ↔ c ∈ bad := by
    rw [mem_storedBadBonds_restrict, mem_storedBadBonds_of_eq V W Yt ωt bad b hq]
    exact ⟨fun h => h.1.1, fun h => ⟨⟨h, h3'.1⟩, h3'.2⟩⟩
  have hm : bondMark R V (q.restrict X).storedField c = bondMark R V W c := by
    unfold bondMark
    rw [chartCoord_congr R.params hfit.L_odd (q.restrict X).markedZone V _ W
      (fun x i h1 h2 => storedField_restrict_eq hR V W Yt ωt bad b hq x i h1 h2) c h3 h4]
  simp only [hbad, hm]
theorem exists_supportAt_of_eq (hq : coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = q) {y : TorusSite n}
    (hy : y ∈ q.markedZone) :
    ∃ s, q.markAt y = some s ∧ s.basePoint = baseOffset R b y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.exists_supportAt_of_eq <;> assumption
theorem torusSiteInFrame_blockSite_baseOffset (hodd : Odd R.params.side)
    (hB : IsBaseChoice R.params.baseDepth (stepHotLumps R.params W) b) (y : TorusSite n) :
    torusSiteInFrame (stepBlockFrame R.params.side n) 0 (blockSite y (baseOffset R b y)) =
      b (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.torusSiteInFrame_blockSite_baseOffset <;> assumption
include hR in
theorem prod_baseFactorProduct (hq : coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = q)
    (hW : IsHullState R.params R.range W Yt)
    (hB : IsBaseChoice R.params.baseDepth (stepHotLumps R.params W) b) :
    ∏ X ∈ chainComponents R.nextRange q.1, baseFactorProduct q X =
      ∏ y ∈ q.markedZone, blockBaseWeight R.params (stepHotLumps R.params W)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
        (b (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)) := by
  classical
  have hdis : (↑(chainComponents R.nextRange q.1) : Set (Finset (TorusSite n))).PairwiseDisjoint
      fun X => (q.restrict X).markedZone := by
    intro X hX X' hX' hne
    rw [Function.onFun, Finset.disjoint_left]
    exact fun y hy hy' => hne (chainComponents_eq_of_mem hX hX'
      (mem_controlRegion_restrict.mp hy).2 (mem_controlRegion_restrict.mp hy').2)
  conv_rhs => rw [markedZone_eq_biUnion q]
  rw [Finset.prod_biUnion hdis]
  refine Finset.prod_congr rfl fun X hX => ?_
  unfold baseFactorProduct
  refine Finset.prod_congr rfl fun y hy => ?_
  have hyz := mem_controlRegion_restrict.mp hy
  obtain ⟨s, hs, hbase⟩ := exists_supportAt_of_eq V W Yt ωt bad b hq hyz.1
  have hs' : (q.restrict X).markAt y = some s := by rw [markAt_restrict, if_pos hyz.2, hs]
  rw [hs']
  show blockBaseWeight R.params _ _
    (torusSiteInFrame (stepBlockFrame R.params.side n) 0 (blockSite y s.basePoint)) = _
  rw [hbase, torusSiteInFrame_blockSite_baseOffset W b hR.admissible.L_odd hB y]
  exact blockBaseWeight_congr R.params _ (nearbyLumps_frameHotLumps_restrict hR V W Yt ωt bad b hq hW hX hy)
end Split
end CaseFactors
open CaseFactors in
theorem caseFactorProduct (hA : AdmissionIffComponentTests) : CaseFactorProductStatement := by
  intro R hR n _ hside V q W Yt ωt bad b hq hbad hW hB hstate
  classical
  have hadm := ((hA R hR n hside V q hq W Yt ωt bad b hbad hW).mp hstate).1
  have h1 : ∀ X ∈ chainComponents R.nextRange q.1,
      coarseFactor V q X = clusterFactorProduct q X * markFactorProduct V q X * baseFactorProduct q X := by
    intro X hX
    unfold coarseFactor admissibilityIndicator
    rw [if_pos (hadm X hX), one_mul]
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    prod_clusterFactorProduct hR V W Yt ωt bad b hside hstate,
    prod_markFactorProduct hR V W Yt ωt bad b hside.1 hstate hq,
    prod_baseFactorProduct hR V W Yt ωt bad b hstate hW hB]
end YangMills.Construction.ClusterExpansionOfAStep
end
