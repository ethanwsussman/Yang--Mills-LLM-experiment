import YangMills.Construction.CellOfTheFlow.TheChainHasASampler
import YangMills.Construction.ClusterExpansionOfAStep.AZeroFactorKillsTheStateProof
import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ClusterExpansionOfAStep.BasesExist
import YangMills.Construction.ClusterExpansionOfAStep.EnergyNearAClassProof
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelOfABond
import Mathlib
set_option autoImplicit false
set_option linter.constructorNameAsVariable false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped unitInterval Quaternion
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps TorusContours StepSettings StepCosts TopLevelSites TorusBalls BlockAverages LumpContours
section Paths
variable {F : BlockFrame} {j : ℕ}
private def countAlong (k : Fin 4) (l : List PathStep) : ℕ := l.countP fun st => st.1 == k
private theorem countAlong_le_length (k : Fin 4) (l : List PathStep) : countAlong k l ≤ l.length :=
  List.countP_le_length
private theorem countAlong_append (k : Fin 4) (l l' : List PathStep) :
    countAlong k (l ++ l') = countAlong k l + countAlong k l' :=
  List.countP_append
private theorem countAlong_axisPath (k : Fin 4) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    countAlong k (axisPath h π) = (h k).natAbs := by
  obtain ⟨a, rfl⟩ := π.surjective k
  rw [axisPath_eq]
  simp only [countAlong, List.countP_append, List.countP_replicate]
  fin_cases a <;> simp [π.injective.eq_iff]
private theorem countAlong_reversePath (k : Fin 4) (l : List PathStep) :
    countAlong k (reversePath l) = countAlong k l := by
  simp [countAlong, reversePath, List.countP_map, List.countP_reverse, Function.comp_def]
private theorem natAbs_signedStep_le (k i : Fin 4) (b : Bool) :
    (((if b then Pi.single i (1 : ℤ) else -Pi.single i (1 : ℤ)) : Fin 4 → ℤ) k).natAbs ≤ if i == k then 1 else 0 := by
  by_cases hk : k = i
  · subst hk
    cases b <;> simp
  · have : (i == k) = false := by simpa using fun h : i = k => hk h.symm
    cases b <;> simp [this, Pi.single_eq_of_ne hk]
private theorem exists_offset_of_mem_pathSites : ∀ (l : List PathStep) (s x : F.Site j), x ∈ pathSites s l →
    ∃ d : Fin 4 → ℤ, x = s + BlockAverages.siteOfCoords j d ∧ ∀ k, (d k).natAbs ≤ countAlong k l
  | [], s, x, hx => by
    have hs : x = s := by simpa [pathSites] using hx
    exact ⟨0, by simp [hs, TorusContours.siteOfCoords_zero], by simp⟩
  | ⟨i, b⟩ :: r, s, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨0, by simp [TorusContours.siteOfCoords_zero], by simp⟩
    · obtain ⟨d, hd, hb⟩ := exists_offset_of_mem_pathSites r _ x hx
      refine ⟨(if b then Pi.single i (1 : ℤ) else -Pi.single i (1 : ℤ)) + d, ?_, fun k => ?_⟩
      · rw [hd]
        cases b <;> simp [stepDisplacement, BlockAverages.unitStep, TorusContours.siteOfCoords_add,
          TorusContours.siteOfCoords_neg, add_assoc]
      · have h1 := natAbs_signedStep_le k i b
        have h2 := hb k
        have h3 : countAlong k ((i, b) :: r) = countAlong k r + if i == k then 1 else 0 := by
          simp [countAlong, List.countP_cons]
        rw [h3, Pi.add_apply]
        exact (Int.natAbs_add_le _ _).trans (by omega)
private theorem pathHolonomy_congr {X X' : F.GaugeField j} (P : F.Site j → Prop)
    (hag : ∀ x i, P x → P (x + BlockAverages.unitStep j i) → X x i = X' x i) :
    ∀ (l : List PathStep) (x : F.Site j), (∀ s ∈ pathSites x l, P s) → pathHolonomy X x l = pathHolonomy X' x l
  | [], _, _ => rfl
  | ⟨i, b⟩ :: r, x, hp => by
    have h1 : P x := hp x (by simp [pathSites])
    have h2 : P (x + stepDisplacement j (i, b)) := hp _ (by
      cases r <;> simp [pathSites])
    simp only [pathHolonomy]
    rw [pathHolonomy_congr P hag r _ fun s hs => hp s (by simp [pathSites, hs])]
    congr 1
    cases b
    · have h3 : P (x - BlockAverages.unitStep j i) := by simpa [stepDisplacement, sub_eq_add_neg] using h2
      have h4 := hag (x - BlockAverages.unitStep j i) i h3 (by simpa using h1)
      simp [linkValue, h4]
    · have h4 := hag x i h1 (by simpa [stepDisplacement] using h2)
      simp [linkValue, h4]
end Paths
section Blocks
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem mem_sitesInBlocks_iff {S : Finset (TorusSite n)} {x : TorusSite (n * L)} :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by
  simp [sitesInBlocks]
private theorem mem_thickening_three_iff {X : Finset (TorusSite n)} {z : TorusSite n} :
    z ∈ thickening 3 X ↔ ∃ x ∈ X, _root_.YangMills.Construction.TorusFields.supDist z x ≤ 3 := by
  simp [thickening]
private theorem readAtLevel_congr {Z : Finset (TorusSite n)} {W W' : TorusField (n * L)}
    (h : FieldsAgreeOn (sitesInBlocks L Z) W W')
    (x : (stepBlockFrame L n).Site 0) (i : Fin 4) (hx : parentBlock L (toTorusSite (n * L) x) ∈ Z)
    (hx' : parentBlock L (toTorusSite (n * L) (x + BlockAverages.unitStep 0 i)) ∈ Z) :
    readAtLevel (stepBlockFrame L n) 0 W x i = readAtLevel (stepBlockFrame L n) 0 W' x i := by
  have e : toTorusSite (n * L) (x + BlockAverages.unitStep 0 i) =
      toTorusSite (n * L) x + TorusFields.unitStep (n * L) i := by
    rw [TopLevelSites.toTorusSite_add (fun k => stepBlockFrame_period_zero k),
      TopLevelSites.toTorusSite_unitStep (fun k => stepBlockFrame_period_zero k)]
  exact h (toTorusSite (n * L) x, i) (mem_sitesInBlocks_iff.mpr hx) (by
    show toTorusSite (n * L) x + TorusFields.unitStep (n * L) i ∈ _
    rw [← e]
    exact mem_sitesInBlocks_iff.mpr hx')
private theorem supDist_le_of_mem_pathSites {x s : (stepBlockFrame L n).Site 0} {l : List PathStep} {m : ℕ}
    (hs : s ∈ pathSites x l) (hm : ∀ k, countAlong k l ≤ m) :
    _root_.YangMills.Construction.TorusFields.supDist (toTorusSite (n * L) x) (toTorusSite (n * L) s) ≤ m := by
  obtain ⟨d, rfl, hd⟩ := exists_offset_of_mem_pathSites l x s hs
  rw [TopLevelSites.toTorusSite_add (fun k => stepBlockFrame_period_zero k),
    TopLevelSites.toTorusSite_siteOfCoords (fun k => stepBlockFrame_period_zero k)]
  exact _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ fun k => (hd k).trans (hm k)
end Blocks
section Filters
private theorem mem_of_mem_filter' {α : Type*} {p : α → Prop} {d : DecidablePred p} {s : Finset α} {x : α}
    (h : x ∈ @Finset.filter α p d s) : x ∈ s := (Finset.mem_filter.mp h).1
private theorem prop_of_mem_filter {α : Type*} {p : α → Prop} {d : DecidablePred p} {s : Finset α} {x : α}
    (h : x ∈ @Finset.filter α p d s) : p x := (Finset.mem_filter.mp h).2
end Filters
section Lumps
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
private theorem mem_cutBelow_cellBall_iff {F : BlockFrame} {y : F.Cell} {x : F.Site F.depth} :
    x ∈ cutBelow F.depth (cellBall y 2) ↔
      ∃ m : Fin 4 → ℤ, (∀ k, (m k).natAbs ≤ 2) ∧ x ∈ sitesBelow F.depth (y + BlockAverages.siteOfCoords F.top m) := by
  simp only [cutBelow, LumpContours.cellBall, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, hxY⟩
    refine ⟨m, fun k => ?_, hxY⟩
    have := _root_.YangMills.Construction.TorusContours.mem_centredCube_iff.mp hm k
    push_cast at this
    omega
  · rintro ⟨m, hm, hxY⟩
    refine ⟨_, ⟨m, _root_.YangMills.Construction.TorusContours.mem_centredCube_iff.mpr fun k => ?_, rfl⟩, hxY⟩
    have := hm k
    push_cast
    omega
private theorem mem_lumpOf_self (hfit : ℓ.Admissible) (z : (stepBlockFrame ℓ.side n).Site 0) :
    z ∈ lumpOf ℓ.grid z := by
  have hL : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne _)
  refine Finset.mem_image.mpr ⟨siteCoords z, ?_, TorusContours.siteOfCoords_siteCoords z⟩
  refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_
  have hb := ℓ.grid.mem_interval _ (offsetFromCentre_spec hL hfit.L_odd (siteCoords z i)).2
  constructor <;> linarith [hb.2.1, hb.2.2.1]
private theorem mem_fineHotLumps_of_agree (hfit : ℓ.Admissible) {W W' : TorusField (n * ℓ.side)}
    {y : TorusSite n} {Z : Finset (TorusSite n)}
    (hZ : thickening 3 {y} ⊆ Z) (hag : FieldsAgreeOn (sitesInBlocks ℓ.side Z) W W')
    {l : Finset ((stepBlockFrame ℓ.side n).Site 0)} (hl : l ∈ fineHotLumps ℓ (fineLevelField ℓ n W))
    (hsub : ∀ x ∈ l, ∃ m : Fin 4 → ℤ, (∀ k, (m k).natAbs ≤ 2) ∧
      x ∈ sitesBelow (stepBlockFrame ℓ.side n).depth
        ((torusSiteInFrame (stepBlockFrame ℓ.side n) 1 y : (stepBlockFrame ℓ.side n).Cell) +
          BlockAverages.siteOfCoords (stepBlockFrame ℓ.side n).top m)) :
    l ∈ fineHotLumps ℓ (fineLevelField ℓ n W') := by
  classical
  have hLge : 2 ^ 16 ≤ ℓ.side := hfit.L_ge
  simp only [fineHotLumps, hotLumps, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image] at hl ⊢
  obtain ⟨p, ⟨hp, hs⟩, z, hz, hlz⟩ := hl
  refine ⟨p, ⟨hp, ?_⟩, z, hz, hlz⟩
  have hzl : z ∈ l := by
    rw [← hlz]
    exact mem_lumpOf_self (ℓ := ℓ) (n := n) hfit z
  obtain ⟨h, hh, hzY⟩ := hsub z hzl
  obtain ⟨w, hw, hzw⟩ := (_root_.YangMills.Construction.TorusContours.mem_sitesBelow_iff _ z).mp hzY
  have hblock : parentBlock ℓ.side (toTorusSite (n * ℓ.side) z) = y + siteOfInt h := by
    have h1 : parentBlock ℓ.side (toTorusSite (n * ℓ.side) z) = toTorusSite n
        ((torusSiteInFrame (stepBlockFrame ℓ.side n) 1 y : (stepBlockFrame ℓ.side n).Cell) +
          BlockAverages.siteOfCoords (stepBlockFrame ℓ.side n).top h) := by
      rw [hzw]
      exact parentBlock_siteAtOffset _ hw
    have h2 := toTorusSite_add (F := stepBlockFrame ℓ.side n) (j := (stepBlockFrame ℓ.side n).top) (m := n)
      (fun k => stepBlockFrame_period_one k)
      (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 y) (BlockAverages.siteOfCoords (stepBlockFrame ℓ.side n).top h)
    have h3 := toTorusSite_siteOfCoords (F := stepBlockFrame ℓ.side n) (j := (stepBlockFrame ℓ.side n).top) (m := n)
      (fun k => stepBlockFrame_period_one k) h
    have h4 : toTorusSite (F := stepBlockFrame ℓ.side n) (j := (stepBlockFrame ℓ.side n).top) n
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 y) = y :=
      toTorusSite_torusSiteInFrame (fun k => stepBlockFrame_period_one k) y
    rw [h1]
    exact h2.trans (by rw [h3, h4])
  have hyz : _root_.YangMills.Construction.TorusFields.supDist (parentBlock ℓ.side (toTorusSite (n * ℓ.side) z)) y ≤ 2 := by
    rw [hblock, _root_.YangMills.Construction.TorusFields.supDist_comm]
    exact _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ hh
  have key : ∀ s : (stepBlockFrame ℓ.side n).Site 0,
      _root_.YangMills.Construction.TorusFields.supDist (toTorusSite (n * ℓ.side) s) (toTorusSite (n * ℓ.side) z) ≤ 8 →
      parentBlock ℓ.side (toTorusSite (n * ℓ.side) s) ∈ Z := by
    intro s hs
    refine hZ (mem_thickening_three_iff.mpr ⟨y, by simp, ?_⟩)
    have h1 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one ℓ.side (toTorusSite (n * ℓ.side) s) (toTorusSite (n * ℓ.side) z)
    have h2 : _root_.YangMills.Construction.TorusFields.supDist (toTorusSite (n * ℓ.side) s) (toTorusSite (n * ℓ.side) z) / ℓ.side = 0 :=
      Nat.div_eq_of_lt (by omega)
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock ℓ.side (toTorusSite (n * ℓ.side) s))
      (parentBlock ℓ.side (toTorusSite (n * ℓ.side) z)) y
    omega
  have hlen : ∀ k, countAlong k [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] ≤ 4 :=
    fun k => countAlong_le_length k _
  have hzp : z ∈ pathSites p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] := by
    simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [pathSites, stepDisplacement, if_true, Bool.false_eq_true, if_false, List.mem_cons,
      List.not_mem_nil, or_false]
    rcases hz with rfl | rfl | rfl | rfl
    · simp
    · simp
    · right; right; right; left
      abel
    · simp
  have hval : plaquetteHolonomy (fineLevelField ℓ n W) p = plaquetteHolonomy (fineLevelField ℓ n W') p := by
    refine pathHolonomy_congr (fun s => parentBlock ℓ.side (toTorusSite (n * ℓ.side) s) ∈ Z)
      (fun x i hx hx' => readAtLevel_congr hag x i hx hx') _ _ fun s hs => key s ?_
    have h1 := supDist_le_of_mem_pathSites hs hlen
    have h2 := supDist_le_of_mem_pathSites hzp hlen
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle (toTorusSite (n * ℓ.side) s) (toTorusSite (n * ℓ.side) p.1)
      (toTorusSite (n * ℓ.side) z)
    have h4 := _root_.YangMills.Construction.TorusFields.supDist_comm (toTorusSite (n * ℓ.side) s) (toTorusSite (n * ℓ.side) p.1)
    omega
  have hc : plaquetteDefect (fineLevelField ℓ n W') p = plaquetteDefect (fineLevelField ℓ n W) p := by
    unfold plaquetteDefect
    rw [hval]
  rw [hc]
  exact hs
private theorem nearbyLumps_congr {F : BlockFrame} {h h' : Finset (Finset (F.Site F.depth))} {y : F.Cell}
    (H : ∀ l ∈ h, (∀ x ∈ l, ∃ m : Fin 4 → ℤ, (∀ k, (m k).natAbs ≤ 2) ∧
      x ∈ sitesBelow F.depth (y + BlockAverages.siteOfCoords F.top m)) → l ∈ h')
    (H' : ∀ l ∈ h', (∀ x ∈ l, ∃ m : Fin 4 → ℤ, (∀ k, (m k).natAbs ≤ 2) ∧
      x ∈ sitesBelow F.depth (y + BlockAverages.siteOfCoords F.top m)) → l ∈ h) :
    nearbyLumps h y = nearbyLumps h' y := by
  classical
  ext l
  simp only [nearbyLumps, Finset.mem_filter, Finset.subset_iff, mem_cutBelow_cellBall_iff]
  exact ⟨fun a => ⟨H l a.1 a.2, a.2⟩, fun a => ⟨H' l a.1 a.2, a.2⟩⟩
private theorem nearbyLumps_eq_of_agree (hfit : ℓ.Admissible) {W W' : TorusField (n * ℓ.side)}
    {y : TorusSite n} {Z : Finset (TorusSite n)}
    (hZ : thickening 3 {y} ⊆ Z) (hag : FieldsAgreeOn (sitesInBlocks ℓ.side Z) W W') :
    nearbyLumps (fineHotLumps ℓ (fineLevelField ℓ n W)) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 y) =
      nearbyLumps (fineHotLumps ℓ (fineLevelField ℓ n W')) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 y) :=
  nearbyLumps_congr (fun _ a b => mem_fineHotLumps_of_agree hfit hZ hag a b)
    (fun _ a b => mem_fineHotLumps_of_agree hfit hZ (fun c u v => (hag c u v).symm) a b)
end Lumps
section Means
private theorem baseSitesAt_congr {F : BlockFrame} {J₀ : ℕ} {h h' : Finset (Finset (F.Site F.depth))} {y : F.Cell}
    (e : nearbyLumps h y = nearbyLumps h' y) : baseSitesAt J₀ h y = baseSitesAt J₀ h' y := by apply _root_.YangMills.Construction.InBoxTransfer.baseSitesAt_congr <;> assumption
private theorem usedContours_congr {F : BlockFrame} {J₀ : ℕ} {h h' : Finset (Finset (F.Site F.depth))}
    {b b' : F.Cell → F.Site F.depth} {c : F.Cell × Fin 4} (e₀ : nearbyLumps h c.1 = nearbyLumps h' c.1)
    (e₁ : nearbyLumps h (c.1 + BlockAverages.unitStep F.top c.2) = nearbyLumps h' (c.1 + BlockAverages.unitStep F.top c.2))
    (b₀ : b c.1 = b' c.1) (b₁ : b (c.1 + BlockAverages.unitStep F.top c.2) = b' (c.1 + BlockAverages.unitStep F.top c.2)) :
    usedContours J₀ h b c = usedContours J₀ h' b' c := by exact _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.usedContours_congr (F := F) (J₀ := J₀) (h := h) (h' := h') (b := b) (b' := b') (c := c) e₀ e₁ b₀ b₁
private theorem contourMean_congr {F : BlockFrame} {J₀ : ℕ} {h h' : Finset (Finset (F.Site F.depth))}
    {b b' : F.Cell → F.Site F.depth} {X X' : F.GaugeField F.depth} {c : F.Cell × Fin 4}
    (e₀ : nearbyLumps h c.1 = nearbyLumps h' c.1)
    (e₁ : nearbyLumps h (c.1 + BlockAverages.unitStep F.top c.2) = nearbyLumps h' (c.1 + BlockAverages.unitStep F.top c.2))
    (b₀ : b c.1 = b' c.1) (b₁ : b (c.1 + BlockAverages.unitStep F.top c.2) = b' (c.1 + BlockAverages.unitStep F.top c.2))
    (hX : ∀ e ∈ allContours F, pathHolonomy X (b c.1) (contourPath b c e.1 e.2) =
      pathHolonomy X' (b c.1) (contourPath b c e.1 e.2)) :
    contourMean J₀ h b X c = contourMean J₀ h' b' X' c := by
  classical
  have hu := usedContours_congr (J₀ := J₀) e₀ e₁ b₀ b₁
  have hs : ∀ ξ π, contourPath b c ξ π = contourPath b' c ξ π := fun ξ π => by simp only [contourPath, b₀, b₁]
  have hsub : usedContours J₀ h b c ⊆ allContours F := by
    unfold usedContours
    split_ifs
    · exact subset_rfl
    · exact Finset.filter_subset _ _
  unfold contourMean
  rw [← hu]
  congr 1
  refine Finset.sum_congr rfl fun e he => ?_
  rw [hX e (hsub he), hs, b₀]
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
private theorem parentBlock_mem_thickening_of_mem_contour {b : BaseChoice ℓ.side n}
    {y : (stepBlockFrame ℓ.side n).Cell} {i : Fin 4}
    {e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)} (hfit : ℓ.Admissible)
    (hb₀ : b y ∈ sitesBelow (stepBlockFrame ℓ.side n).depth y)
    (hb₁ : b (y + BlockAverages.unitStep (stepBlockFrame ℓ.side n).top i) ∈
      sitesBelow (stepBlockFrame ℓ.side n).depth (y + BlockAverages.unitStep (stepBlockFrame ℓ.side n).top i))
    (he : e ∈ allContours (stepBlockFrame ℓ.side n)) {s : (stepBlockFrame ℓ.side n).Site 0}
    (hs : s ∈ pathSites (b y) (contourPath b (y, i) e.1 e.2)) :
    parentBlock ℓ.side (toTorusSite (n * ℓ.side) s) ∈ thickening 3 {toTorusSite n y} := by
  have hLge : 2 ^ 16 ≤ ℓ.side := hfit.L_ge
  obtain ⟨z₀, hz₀, e₀⟩ := (_root_.YangMills.Construction.TorusContours.mem_sitesBelow_iff y _).mp hb₀
  obtain ⟨z₁, hz₁, e₁⟩ := (_root_.YangMills.Construction.TorusContours.mem_sitesBelow_iff _ _).mp hb₁
  have hξ : e.1 ∈ centredCube ℓ.side := (Finset.mem_product.mp he).1
  have hoff : ∀ (y₁ : (stepBlockFrame ℓ.side n).Cell) {z : Fin 4 → ℤ}, z ∈ centredCube ℓ.side → ∀ k,
      (minimalOffset (siteAtOffset y₁ z : (stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth)
        (cellCentre (stepBlockFrame ℓ.side n).depth y₁ +
          BlockAverages.siteOfCoords (stepBlockFrame ℓ.side n).depth e.1) k).natAbs ≤ ℓ.side - 1 := by
    intro y₁ z hz k
    have h1 := _root_.YangMills.Construction.TorusContours.mem_centredCube_iff.mp hz k
    have h2 := _root_.YangMills.Construction.TorusContours.mem_centredCube_iff.mp hξ k
    have h3 : ((cellCentre (stepBlockFrame ℓ.side n).depth y₁ +
        BlockAverages.siteOfCoords (stepBlockFrame ℓ.side n).depth e.1 -
        siteAtOffset y₁ z : (stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth)) k =
        ((e.1 k - z k : ℤ) : ZMod ((stepBlockFrame ℓ.side n).period (stepBlockFrame ℓ.side n).depth k)) := by
      simp [siteAtOffset, BlockAverages.siteOfCoords]
    simp only [minimalOffset]
    rw [h3]
    refine (_root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le _).trans ?_
    omega
  have hm : ∀ k, countAlong k (contourPath b (y, i) e.1 e.2) ≤ 3 * ℓ.side - 2 := by
    intro k
    have h1 := hoff y hz₀ k
    have h2 := hoff (y + BlockAverages.unitStep (stepBlockFrame ℓ.side n).top i) hz₁ k
    have h3 := countAlong_le_length k (List.replicate (stepBlockFrame ℓ.side n).blockSide (i, true))
    rw [List.length_replicate] at h3
    have h4 : (stepBlockFrame ℓ.side n).blockSide = ℓ.side := rfl
    simp only [contourPath, countAlong_append, countAlong_axisPath, countAlong_reversePath]
    rw [e₀, e₁]
    rw [h4] at h3 ⊢
    omega
  have h1 := supDist_le_of_mem_pathSites hs hm
  have hblock : parentBlock ℓ.side (toTorusSite (n * ℓ.side) (b y)) = toTorusSite n y := by
    rw [e₀]
    exact parentBlock_siteAtOffset y hz₀
  refine mem_thickening_three_iff.mpr ⟨toTorusSite n y, by simp, ?_⟩
  have h2 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one ℓ.side (toTorusSite (n * ℓ.side) s) (toTorusSite (n * ℓ.side) (b y))
  rw [hblock, _root_.YangMills.Construction.TorusFields.supDist_comm (toTorusSite (n * ℓ.side) s)] at h2
  have h3 : _root_.YangMills.Construction.TorusFields.supDist (toTorusSite (n * ℓ.side) (b y)) (toTorusSite (n * ℓ.side) s) / ℓ.side < 3 :=
    Nat.div_lt_of_lt_mul (by omega)
  omega
private theorem torusSiteInFrame_add_unitStep (x : TorusSite n) (i : Fin 4) :
    (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (x + TorusFields.unitStep n i) : (stepBlockFrame ℓ.side n).Cell) =
      (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x : (stepBlockFrame ℓ.side n).Cell) +
        BlockAverages.unitStep (stepBlockFrame ℓ.side n).top i := by
  have h := torusSiteInFrame_toTorusSite (F := stepBlockFrame ℓ.side n) (j := 1) (fun k => stepBlockFrame_period_one k)
    (BlockAverages.unitStep 1 i : (stepBlockFrame ℓ.side n).Site 1)
  rw [TopLevelSites.toTorusSite_unitStep (fun k => stepBlockFrame_period_one k)] at h
  rw [torusSiteInFrame_add (fun k => stepBlockFrame_period_one k), h]
  rfl
private theorem contourMean_eq_of_agree (hfit : ℓ.Admissible) {W W' : TorusField (n * ℓ.side)}
    {b b' : BaseChoice ℓ.side n} {c : TorusBond n}
    (hag : FieldsAgreeOn (sitesInBlocks ℓ.side (thickening 3 {c.1, c.1 + TorusFields.unitStep n c.2})) W W')
    (u₀ : b (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1) ∈
      sitesBelow 0 (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1))
    (u₁ : b (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (c.1 + TorusFields.unitStep n c.2)) ∈
      sitesBelow 0 (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (c.1 + TorusFields.unitStep n c.2)))
    (b₀ : b (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1) = b' (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1))
    (b₁ : b (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (c.1 + TorusFields.unitStep n c.2)) =
      b' (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (c.1 + TorusFields.unitStep n c.2))) :
    contourMean ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ n W)) b (fineLevelField ℓ n W)
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) =
      contourMean ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ n W')) b' (fineLevelField ℓ n W')
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) := by
  have hZ₀ : thickening 3 {c.1} ⊆ thickening 3 {c.1, c.1 + TorusFields.unitStep n c.2} := by
    intro z hz
    obtain ⟨x, hx, hd⟩ := mem_thickening_three_iff.mp hz
    exact mem_thickening_three_iff.mpr ⟨x, by simp [Finset.mem_singleton.mp hx], hd⟩
  have hZ₁ : thickening 3 {c.1 + TorusFields.unitStep n c.2} ⊆ thickening 3 {c.1, c.1 + TorusFields.unitStep n c.2} := by
    intro z hz
    obtain ⟨x, hx, hd⟩ := mem_thickening_three_iff.mp hz
    exact mem_thickening_three_iff.mpr ⟨x, by simp [Finset.mem_singleton.mp hx], hd⟩
  have e₀ := nearbyLumps_eq_of_agree hfit hZ₀ hag
  have e₁ := nearbyLumps_eq_of_agree hfit hZ₁ hag
  rw [torusSiteInFrame_add_unitStep (ℓ := ℓ) c.1 c.2] at e₁ b₁ u₁
  refine contourMean_congr e₀ e₁ b₀ b₁ fun e he => ?_
  refine pathHolonomy_congr
    (fun s => parentBlock ℓ.side (toTorusSite (n * ℓ.side) s) ∈ thickening 3 {c.1, c.1 + TorusFields.unitStep n c.2})
    (fun x i hx hx' => readAtLevel_congr hag x i hx hx') _ _ fun s hs => ?_
  have h := parentBlock_mem_thickening_of_mem_contour hfit u₀ u₁ he hs
  have hc : toTorusSite (F := stepBlockFrame ℓ.side n) (j := (stepBlockFrame ℓ.side n).top) n
      (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1) = c.1 :=
    toTorusSite_torusSiteInFrame (fun k => stepBlockFrame_period_one k) c.1
  rw [hc] at h
  exact hZ₀ h
end Means
section Bases
private theorem mem_baseSitesAt_of_isBaseChoice {F : BlockFrame} {J₀ : ℕ} {h : Finset (Finset (F.Site F.depth))}
    {b : F.Cell → F.Site F.depth} (hb : IsBaseChoice J₀ h b) (y : F.Cell) : b y ∈ baseSitesAt J₀ h y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseWeightZero.mem_baseSitesAt <;> assumption
private theorem mem_sitesBelow_of_mem_baseSitesAt {ℓ : StepParameters} {n : ℕ} [NeZero n]
    {h : Finset (Finset ((stepBlockFrame ℓ.side n).Site 0))}
    {y : (stepBlockFrame ℓ.side n).Cell} {z : (stepBlockFrame ℓ.side n).Site 0}
    (hz : z ∈ baseSitesAt ℓ.baseDepth h y) :
    z ∈ sitesBelow (stepBlockFrame ℓ.side n).depth y := by
  classical
  unfold baseSitesAt at hz
  split_ifs at hz with hc
  · rw [Finset.mem_singleton.mp hz]
    exact (_root_.YangMills.Construction.TorusContours.mem_sitesBelow_iff y _).mpr ⟨0, zero_mem_centredCube (Nat.pos_of_ne_zero (NeZero.ne ℓ.side)), by
      simp [siteAtOffset, TorusContours.siteOfCoords_zero]⟩
  · exact mem_of_mem_filter' hz
private theorem exists_uniformChoice (E : Type) [MeasurableSpace E] [Finite E] [MeasurableSingletonClass E]
    [Nonempty E] :
    ∃ f : Finset E → I → E, (∀ A, Measurable (f A)) ∧ ∀ A : Finset E, A.Nonempty → (∀ u, f A u ∈ A) ∧
      (∀ z ∈ A, (volume : Measure I) {u | f A u = z} = ENNReal.ofReal (1 / (A.card : ℝ))) ∧
      ∀ z, z ∉ A → (volume : Measure I) {u | f A u = z} = 0 := by
  classical
  have key : ∀ A : Finset E, ∃ g : I → E, Measurable g ∧ (A.Nonempty → (∀ u, g u ∈ A) ∧
      (∀ z ∈ A, (volume : Measure I) {u | g u = z} = ENNReal.ofReal (1 / (A.card : ℝ))) ∧
      ∀ z, z ∉ A → (volume : Measure I) {u | g u = z} = 0) := by
    intro A
    by_cases hA : A.Nonempty
    · have : Nonempty A := hA.to_subtype
      haveI : Fintype A := Finset.fintypeCoeSort A
      obtain ⟨g, hg, hgμ⟩ := Measure.exists_measurable_map_eq (PMF.uniformOfFintype A).toMeasure
      refine ⟨fun u => (g u : E), measurable_subtype_coe.comp hg,
        fun _ => ⟨fun u => (g u).2, fun z hz => ?_, fun z hz => ?_⟩⟩
      · have hset : {u | (g u : E) = z} = g ⁻¹' {⟨z, hz⟩} := by
          ext u
          simp [Subtype.ext_iff]
        have hc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
        rw [hset, ← Measure.map_apply hg (measurableSet_singleton _), hgμ,
          PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply,
          Fintype.card_coe, one_div, ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_natCast]
      · have hset : {u | (g u : E) = z} = ∅ := by
          ext u
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h => hz (h ▸ (g u).2)
        rw [hset, measure_empty]
    · exact ⟨fun _ => Classical.arbitrary E, measurable_const, fun h => absurd h hA⟩
  choose f hf using key
  exact ⟨f, fun A => (hf A).1, fun A hA => (hf A).2 hA⟩
private def uniformChoice (E : Type) [MeasurableSpace E] [Finite E] [MeasurableSingletonClass E] [Nonempty E] :
    Finset E → I → E := (exists_uniformChoice E).choose
private theorem uniformChoice_spec (E : Type) [MeasurableSpace E] [Finite E] [MeasurableSingletonClass E]
    [Nonempty E] :
    (∀ A, Measurable (uniformChoice E A)) ∧ ∀ A : Finset E, A.Nonempty → (∀ u, uniformChoice E A u ∈ A) ∧
      (∀ z ∈ A, (volume : Measure I) {u | uniformChoice E A u = z} = ENNReal.ofReal (1 / (A.card : ℝ))) ∧
      ∀ z, z ∉ A → (volume : Measure I) {u | uniformChoice E A u = z} = 0 := (exists_uniformChoice E).choose_spec
end Bases
section Bonds
private def quaternionOfCoords (p : Fin 4 → ℝ) : ℍ[ℝ] := ⟨p 0, p 1, p 2, p 3⟩
private def quaternionCoords (w : ℍ[ℝ]) : Fin 4 → ℝ := ![w.re, w.imI, w.imJ, w.imK]
private theorem quaternionOfCoords_coords (w : ℍ[ℝ]) : quaternionOfCoords (quaternionCoords w) = w := by
  ext <;> simp [quaternionOfCoords, quaternionCoords]
private theorem continuous_quaternionCoords (i : Fin 4) : Continuous fun w : ℍ[ℝ] => quaternionCoords w i := by
  fin_cases i
  · exact Quaternion.continuous_re
  · exact Quaternion.continuous_imI
  · exact Quaternion.continuous_imJ
  · exact Quaternion.continuous_imK
private theorem continuous_quaternionOfCoords : Continuous quaternionOfCoords := by
  have h : quaternionOfCoords = fun p => p 0 • (⟨1, 0, 0, 0⟩ : ℍ[ℝ]) + p 1 • (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) +
      p 2 • (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) + p 3 • (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) := by
    funext p
    ext <;> simp [quaternionOfCoords]
  rw [h]
  exact ((((continuous_apply 0).smul continuous_const).add ((continuous_apply 1).smul continuous_const)).add
    ((continuous_apply 2).smul continuous_const)).add ((continuous_apply 3).smul continuous_const)
private theorem measurable_partitionFn : Measurable partitionFn := by
  have h : Continuous fun a : ℝ × UnitQuaternion => Real.exp (a.1 * ((a.2 : UnitQuaternion) : ℍ[ℝ]).re) :=
    Real.continuous_exp.comp
      (continuous_fst.mul (Quaternion.continuous_re.comp (continuous_subtype_val.comp continuous_snd)))
  exact (StronglyMeasurable.integral_prod_right (ν := haarUnit)
    (f := fun (t : ℝ) (g : UnitQuaternion) => Real.exp (t * ((g : UnitQuaternion) : ℍ[ℝ]).re))
    h.stronglyMeasurable).measurable
private theorem measurable_meanKernel_density (s : ℝ) :
    Measurable (Function.uncurry fun (p : Fin 4 → ℝ) (g : UnitQuaternion) =>
      ENNReal.ofReal (meanKernel s (quaternionOfCoords p) g)) := by
  have hq : Continuous fun a : (Fin 4 → ℝ) × UnitQuaternion =>
      quaternionOfCoords a.1 * ((a.2⁻¹ : UnitQuaternion) : ℍ[ℝ]) :=
    (continuous_quaternionOfCoords.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd.inv)
  have hnum : Continuous fun a : (Fin 4 → ℝ) × UnitQuaternion =>
      Real.exp (s * (quaternionOfCoords a.1 * ((a.2⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) :=
    Real.continuous_exp.comp (continuous_const.mul (Quaternion.continuous_re.comp hq))
  have hden : Measurable fun a : (Fin 4 → ℝ) × UnitQuaternion => partitionFn (s * ‖quaternionOfCoords a.1‖) :=
    measurable_partitionFn.comp
      (continuous_const.mul (continuous_norm.comp (continuous_quaternionOfCoords.comp continuous_fst))).measurable
  exact ENNReal.measurable_ofReal.comp (hnum.measurable.div hden)
private theorem exists_link_sampler (s : ℝ) : ∃ f : (Fin 4 → ℝ) → I → UnitQuaternion,
    Measurable (Function.uncurry f) ∧
    ∀ p, ∫⁻ g, ENNReal.ofReal (meanKernel s (quaternionOfCoords p) g) ∂haarUnit = 1 →
      ∀ A : Set UnitQuaternion, MeasurableSet A →
      (volume : Measure I) {u | f p u ∈ A} =
        ∫⁻ g in A, ENNReal.ofReal (meanKernel s (quaternionOfCoords p) g) ∂haarUnit := by
  classical
  let dens : (Fin 4 → ℝ) → UnitQuaternion → ENNReal := fun p g =>
    ENNReal.ofReal (meanKernel s (quaternionOfCoords p) g)
  have hd : Measurable (Function.uncurry dens) := measurable_meanKernel_density s
  let κ₀ : Kernel (Fin 4 → ℝ) UnitQuaternion := Kernel.withDensity (Kernel.const _ haarUnit) dens
  have hκ₀ : ∀ p, κ₀ p = haarUnit.withDensity (dens p) := fun p => by
    simp only [κ₀, Kernel.withDensity_apply _ hd, Kernel.const_apply]
  have hG : MeasurableSet {p | κ₀ p Set.univ = 1} :=
    κ₀.measurable_coe MeasurableSet.univ (measurableSet_singleton 1)
  let κ : Kernel (Fin 4 → ℝ) UnitQuaternion := Kernel.piecewise hG κ₀ (Kernel.const _ (Measure.dirac 1))
  haveI : IsMarkovKernel κ := ⟨fun p => ⟨by
    by_cases hp : p ∈ {p | κ₀ p Set.univ = 1}
    · simp only [κ, Kernel.piecewise_apply, if_pos hp]
      exact hp
    · simp only [κ, Kernel.piecewise_apply, if_neg hp, Kernel.const_apply]
      exact measure_univ⟩⟩
  obtain ⟨f, hf, hfκ⟩ := Kernel.exists_measurable_map_eq_unitInterval κ
  refine ⟨f, hf, fun p hp A hA => ?_⟩
  have hmem : p ∈ {p | κ₀ p Set.univ = 1} := by
    show κ₀ p Set.univ = 1
    rw [hκ₀, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hp
  have h1 : Measurable (f p) := hf.of_uncurry_left
  have h2 : {u | f p u ∈ A} = f p ⁻¹' A := rfl
  rw [h2, ← Measure.map_apply h1 hA, hfκ]
  simp only [κ, Kernel.piecewise_apply, if_pos hmem]
  rw [hκ₀, withDensity_apply _ hA]
end Bonds
section Sampler
private theorem measurable_of_countable_partition {α C β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable C]
    (A : α → C) (hA : ∀ c, MeasurableSet (A ⁻¹' {c})) (G : C → I → β) (hG : ∀ c, Measurable (G c)) :
    Measurable fun p : α × I => G (A p.1) p.2 := by
  letI : MeasurableSpace C := ⊤
  have : MeasurableSingletonClass C := ⟨fun _ => trivial⟩
  have hA' : Measurable A := measurable_to_countable' hA
  have h : Measurable fun q : C × I => G q.1 q.2 := measurable_from_prod_countable_right hG
  exact h.comp ((hA'.comp measurable_fst).prodMk measurable_snd)
private def samplerOfStep (R : StepSetup) (Q : (Fin 4 → ℝ) → I → UnitQuaternion) : StepSampler R where
  sampleBase n _ W y := uniformChoice _
    (baseSitesAt R.params.baseDepth (fineHotLumps R.params (fineLevelField R.params n W))
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y))
  sampleLink n _ W b c := Q (quaternionCoords (contourMean R.params.baseDepth
    (fineHotLumps R.params (fineLevelField R.params n W)) b (fineLevelField R.params n W)
    (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2)))
private theorem baseSitesAt_nonempty (hB : BaseChoicesNonempty) {ℓ : StepParameters} (hfit : ℓ.Admissible) {n : ℕ}
    [NeZero n] (W : TorusField (n * ℓ.side)) (y : (stepBlockFrame ℓ.side n).Cell) :
    (baseSitesAt ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ n W)) y).Nonempty := by
  classical
  obtain ⟨b, hb⟩ := hB ℓ hfit hfit.depth_lt n (fineLevelField ℓ n W)
  exact ⟨b y, mem_baseSitesAt_of_isBaseChoice (prop_of_mem_filter hb) y⟩
private theorem lintegral_meanKernel_eq_one (hO : BondKernelProperties) (ℓ : StepParameters) (x : ℝ) (n : ℕ)
    (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) :
    ∫⁻ g, ENNReal.ofReal (meanKernel (ℓ.coupling * x)
      (contourMean ℓ.baseDepth (fineHotLumps ℓ W) b W c) g) ∂haarUnit = 1 := by
  set V : (stepBlockFrame ℓ.side n).GaugeField 1 := fun _ _ => 1
  have hform : ∀ g : UnitQuaternion, bondKernel ℓ x W (updateBond V c g) b c =
      meanKernel (ℓ.coupling * x) (contourMean ℓ.baseDepth (fineHotLumps ℓ W) b W c) g := fun g => by
    rw [bondKernel_eq_meanKernel]
    simp [updateBond]
  have hone := (hO.2 ℓ x n W V b c).2.2
  have hpos : ∀ g, 0 ≤ meanKernel (ℓ.coupling * x) (contourMean ℓ.baseDepth (fineHotLumps ℓ W) b W c) g :=
    fun g => by
      rw [← hform]
      exact (hO.2 ℓ x n W (updateBond V c g) b c).1.le
  simp only [hform] at hone
  have hint : Integrable
      (fun g => meanKernel (ℓ.coupling * x) (contourMean ℓ.baseDepth (fineHotLumps ℓ W) b W c) g) haarUnit := by
    by_contra h
    rw [integral_undef h] at hone
    exact zero_ne_one hone
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hpos), hone, ENNReal.ofReal_one]
private theorem exists_faithful_stepSampler (hB : BaseChoicesNonempty) (hK : BondKernelBorel)
    (hO : BondKernelProperties) (hM : MeasurableContourMeanStatement) (R : StepSetup)
    (hfit : R.params.Admissible) :
    ∃ S : StepSampler R, S.IsFaithful := by
  classical
  obtain ⟨Q, hQ, hlaw⟩ := exists_link_sampler (R.params.coupling * R.coupling)
  refine ⟨samplerOfStep R Q, ?_⟩
  constructor
  · intro n _ y
    exact measurable_of_countable_partition
      (fun W : TorusField (n * R.params.side) => fineHotLumps R.params (fineLevelField R.params n W))
      (fun H => (hK R.params R.coupling n).2.2.1 H)
      (fun H => uniformChoice ((stepBlockFrame R.params.side n).Site 0)
        (baseSitesAt R.params.baseDepth H (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)))
      (fun H => (uniformChoice_spec ((stepBlockFrame R.params.side n).Site 0)).1 _)
  · intro n _ c
    have hm : ∀ b : BaseChoice R.params.side n, Measurable fun W : TorusField (n * R.params.side) =>
        quaternionCoords (contourMean R.params.baseDepth (fineHotLumps R.params (fineLevelField R.params n W)) b
          (fineLevelField R.params n W) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2)) := fun b =>
      measurable_pi_iff.mpr fun i =>
        hM R.params n b _ (fun w => quaternionCoords w i) (continuous_quaternionCoords i)
    have hj : Measurable fun q : TorusField (n * R.params.side) × BaseChoice R.params.side n =>
        quaternionCoords (contourMean R.params.baseDepth (fineHotLumps R.params (fineLevelField R.params n q.1)) q.2
          (fineLevelField R.params n q.1) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2)) :=
      measurable_from_prod_countable_left hm
    exact hQ.comp ((hj.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd))
  · intro n _ W y z
    obtain ⟨-, h1, h2⟩ := (uniformChoice_spec ((stepBlockFrame R.params.side n).Site 0)).2 _
      (baseSitesAt_nonempty hB hfit W (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y))
    by_cases hz : z ∈ baseSitesAt R.params.baseDepth (fineHotLumps R.params (fineLevelField R.params n W))
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
    · have e := h1 z hz
      simp only [blockBaseWeight]
      rw [if_pos hz]
      exact e
    · have e := h2 z hz
      simp only [blockBaseWeight]
      rw [if_neg hz, ENNReal.ofReal_zero]
      exact e
  · intro n _ W b c A hA
    have h := hlaw _ (by
      rw [quaternionOfCoords_coords]
      exact lintegral_meanKernel_eq_one hO R.params R.coupling n (fineLevelField R.params n W) b
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2)) A hA
    rw [quaternionOfCoords_coords] at h
    exact h
  · intro n _ W y u
    exact mem_sitesBelow_of_mem_baseSitesAt (ℓ := R.params)
      (((uniformChoice_spec ((stepBlockFrame R.params.side n).Site 0)).2 _
        (baseSitesAt_nonempty hB hfit W (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y))).1 u)
  · intro n _ W W' y u hag
    show uniformChoice _ (baseSitesAt R.params.baseDepth _ _) u = uniformChoice _ (baseSitesAt R.params.baseDepth _ _) u
    rw [baseSitesAt_congr (nearbyLumps_eq_of_agree hfit subset_rfl hag)]
  · intro n _ W W' b b' c u hag u₀ u₁ b₀ b₁
    show Q (quaternionCoords _) u = Q (quaternionCoords _) u
    rw [contourMean_eq_of_agree hfit hag u₀ u₁ b₀ b₁]
end Sampler
theorem samplerExistsStatement_holds (hB : BaseChoicesNonempty) (hK : BondKernelBorel)
    (hO : BondKernelProperties) (hM : MeasurableContourMeanStatement) : samplerExistsStatement := by
  intro ℓ hfit T
  have h : ∀ s, ∃ S : StepSampler (T.stage s).toStepSetup, S.IsFaithful :=
    fun s => exists_faithful_stepSampler hB hK hO hM _ hfit
  choose S hS using h
  exact ⟨S, hS⟩
end YangMills.Construction.CellWindows
end
