import YangMills.Construction.ClusterExpansionOfAStep.CalculusOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.CostAtTheFramesIsTheShare
import YangMills.Construction.ClusterExpansionOfAStep.FieldOfASettingAtItsFrames
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.NearFieldsHaveNearShares
import YangMills.Construction.ClusterExpansionOfAStep.PlainFitsOfNearFields
import YangMills.Construction.ClusterExpansionOfAStep.PriceOfTheHotLumps
import YangMills.Construction.ClusterExpansionOfAStep.RegionsOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsPlainFarFromLumps
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.HoleBesideASecondHole.SitesOfBlocksAndCells
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames TopLevelSites TorusFields TorusLumps StepSettings StepCosts
  BlockOffsets TorusShares
namespace FrameCost
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem coordNorm_toImaginary (z : EuclideanSpace ℝ (Fin 3)) : coordNorm z = ‖z‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coordNorm_eq_norm <;> assumption
theorem supDist_fineSite_le (L : ℕ) [NeZero L] (Y Z : TorusSite n) :
    supDist (fineSite L Y 0 0 : TorusSite (n * L)) (fineSite L Z 0 0) ≤ L * supDist Y Z := by
  rw [supDist_le_iff]
  intro i
  set k : ℤ := (Y i - Z i).valMinAbs with hk
  have hk1 : k.natAbs ≤ supDist Y Z := (supDist_le_iff Y Z _).mp le_rfl i
  have hk2 : ((k : ℤ) : ZMod n) = Y i - Z i := ZMod.coe_valMinAbs _
  have hcast : (((((Y i).cast : ℤ) - ((Z i).cast : ℤ) - k) : ℤ) : ZMod n) = 0 := by
    push_cast
    rw [hk2]
    ring
  obtain ⟨e, he⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  have hdiff : (fineSite L Y 0 0 : TorusSite (n * L)) i - (fineSite L Z 0 0 : TorusSite (n * L)) i =
      (((L : ℤ) * k : ℤ) : ZMod (n * L)) := by
    simp only [fineSite, siteOfInt, Pi.zero_apply, add_zero]
    rw [← Int.cast_sub]
    have : (L : ℤ) * ((Y i).cast : ℤ) - (L : ℤ) * ((Z i).cast : ℤ) = (L : ℤ) * k + ((n * L : ℕ) : ℤ) * e := by
      have : ((Y i).cast : ℤ) - ((Z i).cast : ℤ) = k + (n : ℤ) * e := by linarith
      push_cast
      calc (L : ℤ) * ((Y i).cast : ℤ) - (L : ℤ) * ((Z i).cast : ℤ)
          = (L : ℤ) * (((Y i).cast : ℤ) - ((Z i).cast : ℤ)) := by ring
        _ = _ := by rw [this]; ring
    rw [this]
    have h0 : (n : ZMod (n * L)) * (L : ZMod (n * L)) = 0 := by
      exact_mod_cast ZMod.natCast_self (n * L)
    push_cast
    rw [h0]
    simp
  rw [hdiff]
  refine (natAbs_valMinAbs_intCast_le _).trans ?_
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ hk1
theorem mem_sitesInBlocks_parentBlock (L : ℕ) [NeZero L] (x : TorusSite (n * L)) :
    x ∈ sitesInBlocks L {parentBlock L x} := by
  classical
  simp [sitesInBlocks]
theorem parentBlock_eq_of_mem {L : ℕ} [NeZero L] {x : TorusSite (n * L)} {Y : TorusSite n}
    (h : x ∈ sitesInBlocks L {Y}) : parentBlock L x = Y := by
  classical
  simpa [sitesInBlocks] using h
variable (s : ChartSetting R n) (c : SettingCore R n)
theorem parentBlock_not_mem_storedBlockSet {Y : TorusSite n} (hoff : s.AwayFromCore c Y)
    {y q : TorusSite (n * R.params.side)} (hy : y ∈ sitesInBlocks R.params.side {Y})
    (hq : (supDist y q : ℝ) ≤ (R.range : ℝ) / 8) : parentBlock R.params.side q ∉ s.storedBlockSet c := by
  intro hZ
  have := hoff _ hZ y hy q (mem_sitesInBlocks_parentBlock _ q)
  linarith
theorem parentBlock_mem_storedBlockSet_of_hot (hs : s.IsAdmissible) (hz0 : s.InBalls 0)
    {z : TorusSite (n * R.params.side)}
    (hz : z ∈ torusHotSites R.params (s.field 0)) : parentBlock R.params.side z ∈ s.storedBlockSet c := by
  classical
  have h1 := (hs.isHull 0 hz0).1
  have hzY : z ∈ s.support :=
    h1 ((mem_thickening _ _ _).mpr ⟨z, hz, by rw [supDist_self]; exact Nat.zero_le _⟩)
  have hθ : z ∈ (s.storedComponents c).biUnion id := by
    refine Finset.mem_biUnion.mpr ?_
    have hU : z ∈ c.badBonds.image Prod.fst ∪ s.support ∪ sitesInBlocks R.params.side c.core :=
      Finset.mem_union_left _ (Finset.mem_union_right _ hzY)
    refine ⟨_, Finset.mem_image.mpr ⟨z, hU, rfl⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨hU, Relation.ReflTransGen.refl⟩
  refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
  exact ⟨z, Finset.mem_inter.mpr ⟨mem_sitesInBlocks_parentBlock _ z, (mem_thickening _ _ _).mpr ⟨z, hθ, by
    rw [supDist_self]; exact Nat.zero_le _⟩⟩⟩
theorem image_stepHotLumps (ℓ : StepParameters) (W : TorusField (n * ℓ.side)) :
    (stepHotLumps ℓ W).image (fun l => l.image (toTorusSite (n * ℓ.side))) = torusHotLumps ℓ W := by
  have hL : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
  have hq : n * ℓ.side / ℓ.side = n := Nat.mul_div_cancel _ hL
  unfold torusHotLumps stepHotLumps
  generalize n * ℓ.side / ℓ.side = k at hq ⊢
  subst hq
  rfl
theorem exists_hot_site_of_mem_stepHotLumps (ℓ : StepParameters) (hfit : ℓ.Admissible)
    (W : TorusField (n * ℓ.side)) {l : Finset ((stepBlockFrame ℓ.side n).Site 0)}
    (hlh : l ∈ stepHotLumps ℓ W) : ∃ x' ∈ l, toTorusSite (n * ℓ.side) x' ∈ torusHotSites ℓ W := by
  classical
  have hl' : l.image (toTorusSite (n * ℓ.side)) ∈ torusHotLumps ℓ W := by
    rw [← image_stepHotLumps]
    exact Finset.mem_image_of_mem _ hlh
  have hLn : ℓ.side ∣ n * ℓ.side := Dvd.intro_left _ rfl
  obtain ⟨x, μ, ν, hμν, hσ, z, hz, hlz⟩ := (mem_torusHotLumps_iff ℓ hfit hLn _ _).mp hl'
  have hzl : z ∈ l.image (toTorusSite (n * ℓ.side)) := by
    rw [hlz]
    exact mem_torusLumpOf_self z
  obtain ⟨x', hx'l, hx'z⟩ := Finset.mem_image.mp hzl
  refine ⟨x', hx'l, ?_⟩
  rw [hx'z]
  exact mem_torusHotSites_iff.mpr ⟨_, hl', hzl⟩
theorem supDist_parentBlock_le_of_mem_cutBelow {F : BlockFrame} [NeZero (n * F.blockSide)]
    (hn : ∀ i, F.extent i = n) (hodd : Odd F.blockSide) {Z : TorusSite n} {x' : F.Site F.depth} {r : ℕ}
    (hx : x' ∈ cutBelow F.depth (cellBall (torusSiteInFrame F F.top Z) r)) :
    supDist Z (parentBlock F.blockSide (toTorusSite (n * F.blockSide) x')) ≤ r := by
  classical
  rw [LumpContours.BlockLevels.cutBelow_eq_sitesOfCells] at hx
  have hv := LumpContours.BlockLevels.enclosingCell_mem_of_mem_sitesOfCells (F := F) (j := F.depth)
    (by simp [BlockFrame.top]) hodd hx
  obtain ⟨cc, hcc, hvy⟩ := BlockSites.mem_cellBall_iff.mp hv
  have hblk := enclosingCell_torusSiteInFrame (F := F) hn (toTorusSite (n * F.blockSide) x')
  have h3 : torusSiteInFrame F F.depth (toTorusSite (n * F.blockSide) x') = x' :=
    torusSiteInFrame_toTorusSite (period_depth_of_extent hn) x'
  rw [h3, hvy] at hblk
  have h4 := congrArg (toTorusSite n) hblk
  rw [toTorusSite_add (period_top_of_extent hn), toTorusSite_torusSiteInFrame (period_top_of_extent hn),
    toTorusSite_siteOfCoords (period_top_of_extent hn), toTorusSite_torusSiteInFrame (period_top_of_extent hn)] at h4
  rw [← h4]
  refine supDist_add_siteOfInt_le Z cc r fun i => ?_
  have h5 := hcc i
  rw [Int.abs_eq_natAbs] at h5
  exact_mod_cast h5
theorem parentBlock_of_mem_sitesBelow {F : BlockFrame} [NeZero (n * F.blockSide)] (hn : ∀ i, F.extent i = n)
    (hodd : Odd F.blockSide) {Z : TorusSite n} {x : F.Site F.depth}
    (hx : x ∈ sitesBelow F.depth (torusSiteInFrame F F.top Z)) :
    parentBlock F.blockSide (toTorusSite (n * F.blockSide) x) = Z := by
  have h1 := LumpContours.BlockLevels.enclosingCell_of_mem_sitesBelow (F := F) (i := F.depth) (j := F.top)
    (by simp [BlockFrame.top]) le_rfl hodd hx
  have h2 : enclosingCell x = torusSiteInFrame F F.top Z := by
    rw [h1]
    exact LumpContours.BlockLevels.enclosingCell_cell hodd.pos _
  have hblk := enclosingCell_torusSiteInFrame (F := F) hn (toTorusSite (n * F.blockSide) x)
  have h3 : torusSiteInFrame F F.depth (toTorusSite (n * F.blockSide) x) = x :=
    torusSiteInFrame_toTorusSite (period_depth_of_extent hn) x
  rw [h3, h2] at hblk
  have h4 := congrArg (toTorusSite n) hblk
  rw [toTorusSite_torusSiteInFrame (period_top_of_extent hn), toTorusSite_torusSiteInFrame (period_top_of_extent hn)] at h4
  exact h4.symm
theorem not_subset_cutBelow (ℓ : StepParameters) (hfit : ℓ.Admissible) (W : TorusField (n * ℓ.side))
    (St : Finset (TorusSite n)) (hW : ∀ z ∈ torusHotSites ℓ W, parentBlock ℓ.side z ∈ St) {Z : TorusSite n} {r : ℕ}
    (hZ : ∀ Z' : TorusSite n, supDist Z Z' ≤ r → Z' ∉ St) :
    ∀ l ∈ stepHotLumps ℓ W, ¬ l ⊆ cutBelow (F := stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth
      (cellBall (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 Z) r) := by
  intro l hlh hsub
  obtain ⟨x', hx'l, hx'h⟩ := exists_hot_site_of_mem_stepHotLumps ℓ hfit W hlh
  haveI : NeZero (n * (stepBlockFrame ℓ.side n).blockSide) := inferInstanceAs (NeZero (n * ℓ.side))
  exact hZ _ (supDist_parentBlock_le_of_mem_cutBelow (F := stepBlockFrame ℓ.side n) (fun _ => rfl) hfit.L_odd
    (hsub hx'l)) (hW _ hx'h)
theorem nearbyLumps_eq_empty (ℓ : StepParameters) (hfit : ℓ.Admissible) (W : TorusField (n * ℓ.side))
    (St : Finset (TorusSite n)) (hW : ∀ z ∈ torusHotSites ℓ W, parentBlock ℓ.side z ∈ St) {Z : TorusSite n}
    (hZ : ∀ Z' : TorusSite n, supDist Z Z' ≤ 2 → Z' ∉ St) :
    nearbyLumps (stepHotLumps ℓ W) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 Z) = ∅ := by
  classical
  unfold nearbyLumps
  exact Finset.filter_eq_empty_iff.mpr (not_subset_cutBelow ℓ hfit W St hW hZ)
theorem isColdOn_compl_thickening (ℓ : StepParameters) (hfit : ℓ.Admissible) (W : TorusField (n * ℓ.side)) :
    IsColdOn (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) ℓ.threshold W := by
  intro x μ ν hμν hcor
  by_contra hlt
  have hLn : ℓ.side ∣ n * ℓ.side := Dvd.intro_left _ rfl
  have h1 := mem_torusHotSites_of_mem_plaquetteVertices hfit hLn hμν (not_lt.mp hlt)
    (base_mem_plaquetteVertices x μ ν)
  have h2 := hcor x (base_mem_plaquetteVertices x μ ν)
  exact (Finset.mem_sdiff.mp h2).2 ((mem_thickening _ _ _).mpr ⟨x, h1, by rw [supDist_self]; exact Nat.zero_le _⟩)
theorem stepHotLumps_eq_of_torusHotLumps_eq (hfit : R.params.Admissible) (W W' : TorusField (n * R.params.side))
    (h : torusHotLumps R.params W = torusHotLumps R.params W') :
    stepHotLumps R.params W = stepHotLumps R.params W' := by
  classical
  have hp0 : ∀ i, (stepBlockFrame R.params.side n).period 0 i = n * R.params.side := period_zero
  have hinj : Function.Injective
      (fun l : Finset ((stepBlockFrame R.params.side n).Site 0) => l.image (toTorusSite (n * R.params.side))) :=
    Finset.image_injective fun x y e => toTorusSite_injective hp0 e
  have h2 := image_stepHotLumps R.params W
  have h3 := image_stepHotLumps R.params W'
  rw [h, ← h3] at h2
  exact (Finset.image_injective hinj) h2
theorem torusSiteInFrame_add_unitStep (L : ℕ) (Z : TorusSite n) (i : Fin 4) :
    torusSiteInFrame (stepBlockFrame L n) 1 Z + BlockAverages.unitStep 1 i =
      torusSiteInFrame (stepBlockFrame L n) 1 (Z + TorusFields.unitStep n i) := by
  have hp1 : ∀ i, (stepBlockFrame L n).period 1 i = n := period_one
  apply toTorusSite_injective hp1
  rw [toTorusSite_add hp1, toTorusSite_torusSiteInFrame hp1, toTorusSite_torusSiteInFrame hp1,
    toTorusSite_unitStep hp1]
theorem abs_bondFit_sub_blockFitAt_le (hKern : KernelPlainAwayFromLumps) (hPlain : PlainFitsOfNearFields)
    (hfit : R.params.Admissible) (h16 : 16 ≤ n) (W W' : TorusField (n * R.params.side)) (V : TorusField n)
    (b : BaseChoice R.params.side n)
    (hb : IsBaseChoice R.params.baseDepth (stepHotLumps R.params W) b) (St : Finset (TorusSite n))
    (hW : ∀ z ∈ torusHotSites R.params W, parentBlock R.params.side z ∈ St) {Z : TorusSite n} {i : Fin 4}
    (hZ : ∀ Z' : TorusSite n, supDist Z Z' ≤ 2 → Z' ∉ St)
    (hZ1 : ∀ Z' : TorusSite n, supDist (Z + TorusFields.unitStep n i) Z' ≤ 2 → Z' ∉ St)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ (q : TorusSite (n * R.params.side)) (k : Fin 4),
      (parentBlock R.params.side q = Z ∨ parentBlock R.params.side q = Z + TorusFields.unitStep n i) →
      (parentBlock R.params.side (q + TorusFields.unitStep (n * R.params.side) k) = Z ∨
        parentBlock R.params.side (q + TorusFields.unitStep (n * R.params.side) k) = Z + TorusFields.unitStep n i) →
      ‖(W q k : ℍ[ℝ]) - W' q k‖ ≤ ε) :
    |bondFit R.params W V b (Z, i) - blockFitAt R.params.side W' V (Z, i)| ≤ 18 * R.params.side * ε := by
  classical
  have hp0 : ∀ i, (stepBlockFrame R.params.side n).period 0 i = n * R.params.side := period_zero
  haveI : NeZero (n * (stepBlockFrame R.params.side n).blockSide) := inferInstanceAs (NeZero (n * R.params.side))
  set y := torusSiteInFrame (stepBlockFrame R.params.side n) 1 Z with hy
  have hodd := hfit.L_odd
  have h₀ := nearbyLumps_eq_empty R.params hfit W St hW hZ
  have h₁ := nearbyLumps_eq_empty R.params hfit W St hW hZ1
  rw [← torusSiteInFrame_add_unitStep, ← hy] at h₁
  obtain ⟨-, hk⟩ := hKern R.params hfit n (readAtLevel (stepBlockFrame R.params.side n) 0 W) y i h₀ h₁
  have hbm : b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
  obtain ⟨-, hf, -⟩ := hk 0 (readAtLevel (stepBlockFrame R.params.side n) 1 V) b hbm
  have e1 : bondFit R.params W V b (Z, i) = blockFit (readAtLevel (stepBlockFrame R.params.side n) 0 W)
      (readAtLevel (stepBlockFrame R.params.side n) 1 V) (y, i) := hf
  rw [e1]
  refine hPlain R.params.side n hodd h16 (readAtLevel (stepBlockFrame R.params.side n) 0 W)
    (readAtLevel (stepBlockFrame R.params.side n) 0 W') (readAtLevel (stepBlockFrame R.params.side n) 1 V) y i ε hε ?_
  intro x k hx hx'
  have hq : ∀ {x₁ : (stepBlockFrame R.params.side n).Site 0},
      (x₁ ∈ sitesBelow 0 y ∨ x₁ ∈ sitesBelow 0 (y + BlockAverages.unitStep 1 i)) →
      (parentBlock R.params.side (toTorusSite (n * R.params.side) x₁) = Z ∨
        parentBlock R.params.side (toTorusSite (n * R.params.side) x₁) = Z + TorusFields.unitStep n i) := by
    intro x₁ h
    rcases h with h | h
    · exact Or.inl (parentBlock_of_mem_sitesBelow (F := stepBlockFrame R.params.side n) (fun _ => rfl) hodd h)
    · rw [hy, torusSiteInFrame_add_unitStep] at h
      exact Or.inr (parentBlock_of_mem_sitesBelow (F := stepBlockFrame R.params.side n) (fun _ => rfl) hodd h)
  have h2 := hq hx'
  rw [toTorusSite_add hp0, toTorusSite_unitStep hp0] at h2
  exact hclose (toTorusSite (n * R.params.side) x) k (hq hx) h2
theorem card_sitesInBlocks_singleton (hfit : R.params.Admissible) (Y : TorusSite n) :
    ((sitesInBlocks R.params.side {Y}).card : ℝ) = (R.params.side : ℝ) ^ 4 := by
  have h1 := sum_sitesInBlocks (n := n) hfit.L_odd Y (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h1
  rw [h1, card_centredCube hfit.L_odd]
  push_cast
  rfl
set_option maxHeartbeats 1000000 in
theorem abs_blockCostAt_sub_levelShare_le (hKern : KernelPlainAwayFromLumps) (hPlain : PlainFitsOfNearFields)
    (hNear : ShareContinuity.ShareLipschitzInField) (hfit : R.params.Admissible) (h64 : 64 ≤ n)
    (hs : s.IsAdmissible) (hz0 : s.InBalls 0) {Y : TorusSite n} (hoff : s.AwayFromCore c Y)
    {A δ s₀ s₁ ε : ℝ} {ρ : ℕ}
    (hS : ShareLocality R.params.coupling R.params.side s₀ A δ) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (ha : 0 ≤ R.params.coupling) (hε : 0 ≤ ε)
    (hs₁ : 0 < s₁) (hσ : R.params.threshold ≤ s₁) (hs₀ : s₁ + 8 * ε ≤ s₀)
    (hρ : (ρ : ℝ) + 1 + (lumpRange : ℝ) ≤ (R.range : ℝ) / 8)
    (hX₀ : IsLocallyOrthantClosed (Finset.univ \ thickening lumpRange (torusHotSites R.params (s.field 0))) 1024)
    (hX₁ : IsLocallyOrthantClosed (sitesInBlocks R.params.side s.region) 1024)
    (hc₁ : IsColdOn (sitesInBlocks R.params.side s.region) s₁
      (minimizingField R.params.coupling R.anchorRadius R.params.side R.depth s.region s.coarse))
    (hclose : ∀ (x : TorusSite (n * R.params.side)) (i : Fin 4), parentBlock R.params.side x ∉ s.storedBlockSet c →
      parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) ∉ s.storedBlockSet c →
      ‖(s.field 0 x i : ℍ[ℝ]) -
        minimizingField R.params.coupling R.anchorRadius R.params.side R.depth s.region s.coarse x i‖ ≤ ε)
    (hY3 : ∀ Z : TorusSite n, supDist Y Z ≤ 3 → Z ∉ s.storedBlockSet c)
    (hYS : ∀ Z : TorusSite n, supDist Y Z ≤ 1 → Z ∈ s.region)
    (hqS : ∀ y ∈ sitesInBlocks R.params.side {Y}, ∀ q : TorusSite (n * R.params.side),
      (supDist y q : ℝ) ≤ (ρ : ℝ) + 1 → parentBlock R.params.side q ∈ s.region)
    (hsplit : levelShare R.params.coupling R.params.side (R.depth + 1) s.region Y s.coarse =
      ∑ y ∈ sitesInBlocks R.params.side {Y}, levelShare R.params.coupling R.params.side R.depth
          (sitesInBlocks R.params.side s.region) y
          (minimizingField R.params.coupling R.anchorRadius R.params.side R.depth s.region s.coarse) +
        R.params.coupling * halfBlockFits R.params.side s.region
          (minimizingField R.params.coupling R.anchorRadius R.params.side R.depth s.region s.coarse) s.coarse Y) :
    |s.blockCostAt Y 0 - levelShare R.params.coupling R.params.side (R.depth + 1) s.region Y s.coarse| ≤
      (R.params.side : ℝ) ^ 4 * (A * Real.exp (-(δ * ρ)) + A * (2 * ε) * (4 * (2 * (ρ : ℝ) + 2) ^ 4)) +
        72 * R.params.coupling * R.params.side * ε := by
  classical
  set W₀ := s.field 0 with hW₀
  set Wst := minimizingField R.params.coupling R.anchorRadius R.params.side R.depth s.region s.coarse with hWst
  set X₀ := Finset.univ \ thickening lumpRange (torusHotSites R.params W₀) with hX₀d
  set X₁ := sitesInBlocks R.params.side s.region with hX₁d
  set B : ℝ := A * Real.exp (-(δ * ρ)) + A * (2 * ε) * (4 * (2 * (ρ : ℝ) + 2) ^ 4) with hB
  have hc₀ : IsColdOn X₀ s₁ W₀ := by
    intro x μ ν hμν hcor
    exact (isColdOn_compl_thickening R.params hfit W₀ x μ ν hμν hcor).trans_le hσ
  have hmem₀ : ∀ y ∈ sitesInBlocks R.params.side {Y}, ∀ q : TorusSite (n * R.params.side),
      (supDist y q : ℝ) ≤ (ρ : ℝ) + 1 → q ∈ X₀ := by
    intro y hy q hq
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hw => ?_⟩
    obtain ⟨z, hz, hqz⟩ := (mem_thickening _ _ _).mp hw
    have h1 : (supDist y z : ℝ) ≤ (R.range : ℝ) / 8 := by
      have h2 := supDist_triangle y q z
      have h3 : (supDist y z : ℝ) ≤ (supDist y q : ℝ) + (supDist q z : ℝ) := by exact_mod_cast h2
      have h4 : (supDist q z : ℝ) ≤ (lumpRange : ℝ) := by exact_mod_cast hqz
      linarith
    exact parentBlock_not_mem_storedBlockSet s c hoff hy h1 (parentBlock_mem_storedBlockSet_of_hot s c hs hz0 hz)
  have hmem₁ : ∀ y ∈ sitesInBlocks R.params.side {Y}, ∀ q : TorusSite (n * R.params.side),
      (supDist y q : ℝ) ≤ (ρ : ℝ) + 1 → q ∈ X₁ := by
    intro y hy q hq
    have := hqS y hy q hq
    simpa [hX₁d, sitesInBlocks] using this
  have hrn : ∀ y ∈ sitesInBlocks R.params.side {Y}, ∀ q : TorusSite (n * R.params.side),
      (supDist y q : ℝ) ≤ (ρ : ℝ) + 1 → parentBlock R.params.side q ∉ s.storedBlockSet c := by
    intro y hy q hq
    refine parentBlock_not_mem_storedBlockSet s c hoff hy ?_
    have : (0 : ℝ) ≤ (lumpRange : ℝ) := Nat.cast_nonneg _
    linarith
  have hm64 : 64 ≤ n * R.params.side := by
    have h1 : 1 ≤ R.params.side := hfit.L_odd.pos
    nlinarith
  have hshare : ∀ y ∈ sitesInBlocks R.params.side {Y},
      |levelShare R.params.coupling R.params.side R.depth X₀ y W₀ -
        levelShare R.params.coupling R.params.side R.depth X₁ y Wst| ≤ B := by
    intro y hy
    have hn := hNear R.params.coupling R.params.side s₀ A δ hS hA hδ R.depth (n * R.params.side) X₀ X₁ W₀ Wst y ρ
      s₁ ε hm64 hs₁ hε hs₀ hX₀ hX₁ hc₀ hc₁
    have hAe : 0 ≤ A * (2 * ε) := by positivity
    by_cases hbig : 2 * ρ + 2 < n * R.params.side
    · have hin : ∀ h : Fin 4 → ℤ, OffsetInBox ρ h → (supDist y (y + siteOfInt h) : ℝ) ≤ (ρ : ℝ) + 1 := by
        intro h hh
        have h1 := supDist_add_siteOfInt_le y h ρ fun i => by
          have h2 := hh i
          rw [Int.abs_eq_natAbs] at h2
          exact_mod_cast h2
        have h3 : (supDist y (y + siteOfInt h) : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast h1
        linarith
      have h1 := hn.1 hbig (fun h hh => ⟨fun _ => hmem₁ y hy _ (hin h hh), fun _ => hmem₀ y hy _ (hin h hh)⟩)
        (fun b hb => ?_)
      · refine h1.trans ?_
        have h4 : (2 * (ρ : ℝ) + 1) ^ 4 ≤ (2 * (ρ : ℝ) + 2) ^ 4 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 4
        have h5 : A * (2 * ε) * (4 * (2 * (ρ : ℝ) + 1) ^ 4) ≤ A * (2 * ε) * (4 * (2 * (ρ : ℝ) + 2) ^ 4) :=
          mul_le_mul_of_nonneg_left (by linarith) hAe
        rw [hB]
        linarith
      · refine hclose _ _ (hrn y hy _ (hin _ hb.1)) ?_
        have e : (bondFrom y b).1 + TorusFields.unitStep (n * R.params.side) (bondFrom y b).2 =
            y + siteOfInt (b.1 + Pi.single b.2 1) := by
          show y + siteOfInt b.1 + TorusFields.unitStep (n * R.params.side) b.2 = _
          rw [siteOfInt_add, ← unitStep_eq_siteOfInt, add_assoc]
        rw [e]
        exact hrn y hy _ (hin _ hb.2)
    · have hall : ∀ q : TorusSite (n * R.params.side), (supDist y q : ℝ) ≤ (ρ : ℝ) + 1 := by
        intro q
        have h1 : supDist y q ≤ ρ + 1 := by
          rw [supDist_le_iff]
          intro i
          have := ZMod.natAbs_valMinAbs_le (y i - q i)
          omega
        exact_mod_cast h1
      have hXe : X₀ = X₁ := by
        ext q
        exact ⟨fun _ => hmem₁ y hy q (hall q), fun _ => hmem₀ y hy q (hall q)⟩
      have h1 := hn.2 hXe (fun x i => hclose x i (hrn y hy _ (hall _)) (hrn y hy _ (hall _)))
      refine h1.trans ?_
      have h2 : ((n * R.params.side : ℕ) : ℝ) ≤ 2 * (ρ : ℝ) + 2 := by
        have : n * R.params.side ≤ 2 * ρ + 2 := not_lt.mp hbig
        exact_mod_cast this
      have h4 : ((n * R.params.side : ℕ) : ℝ) ^ 4 ≤ (2 * (ρ : ℝ) + 2) ^ 4 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h2 4
      have h5 : A * (2 * ε) * (4 * ((n * R.params.side : ℕ) : ℝ) ^ 4) ≤
          A * (2 * ε) * (4 * (2 * (ρ : ℝ) + 2) ^ 4) :=
        mul_le_mul_of_nonneg_left (by linarith) hAe
      have h6 : 0 ≤ A * Real.exp (-(δ * ρ)) := by positivity
      rw [hB]
      linarith
  have h16 : 16 ≤ n := by omega
  have hbases : IsBaseChoice R.params.baseDepth (stepHotLumps R.params W₀) s.bases := by
    rw [stepHotLumps_eq_of_torusHotLumps_eq hfit W₀ s.fine (hs.hotLumps_eq 0 hz0)]
    exact hs.isBaseChoice
  have hW : ∀ z ∈ torusHotSites R.params W₀, parentBlock R.params.side z ∈ s.storedBlockSet c :=
    fun z hz => parentBlock_mem_storedBlockSet_of_hot s c hs hz0 hz
  have hstep : ∀ i : Fin 4, supDist Y (Y + TorusFields.unitStep n i) ≤ 1 := fun i => supDist_add_unitStep_le Y i
  have hstep' : ∀ i : Fin 4, supDist Y (Y - TorusFields.unitStep n i) ≤ 1 := by
    intro i
    have h1 := supDist_add_unitStep_le (Y - TorusFields.unitStep n i) i
    rw [sub_add_cancel, supDist_comm] at h1
    exact h1
  have hfar : ∀ (Z Z' : TorusSite n), supDist Y Z ≤ 1 → supDist Z Z' ≤ 2 → Z' ∉ s.storedBlockSet c := by
    intro Z Z' h1 h2
    refine hY3 Z' ?_
    have := supDist_triangle Y Z Z'
    omega
  have hclose' : ∀ {Z Z₁ : TorusSite n}, supDist Y Z ≤ 1 → supDist Y Z₁ ≤ 1 →
      ∀ (q : TorusSite (n * R.params.side)) (k : Fin 4),
      (parentBlock R.params.side q = Z ∨ parentBlock R.params.side q = Z₁) →
      (parentBlock R.params.side (q + TorusFields.unitStep (n * R.params.side) k) = Z ∨
        parentBlock R.params.side (q + TorusFields.unitStep (n * R.params.side) k) = Z₁) →
      ‖(W₀ q k : ℍ[ℝ]) - Wst q k‖ ≤ ε := by
    intro Z Z₁ h1 h2 q k e1 e2
    refine hclose q k ?_ ?_
    · rcases e1 with e | e <;> rw [e] <;> exact hY3 _ (by omega)
    · rcases e2 with e | e <;> rw [e] <;> exact hY3 _ (by omega)
  have hf₁ : ∀ i : Fin 4, |bondFit R.params W₀ s.coarse s.bases (Y, i) -
      blockFitAt R.params.side Wst s.coarse (Y, i)| ≤ 18 * R.params.side * ε := by
    intro i
    refine abs_bondFit_sub_blockFitAt_le hKern hPlain hfit h16 W₀ Wst s.coarse s.bases hbases (s.storedBlockSet c) hW
      (fun Z' h => hfar Y Z' (by rw [supDist_self]; omega) h) (fun Z' h => hfar _ Z' (hstep i) h) hε ?_
    exact hclose' (by rw [supDist_self]; omega) (hstep i)
  have hf₂ : ∀ i : Fin 4, |bondFit R.params W₀ s.coarse s.bases (Y - TorusFields.unitStep n i, i) -
      blockFitAt R.params.side Wst s.coarse (Y - TorusFields.unitStep n i, i)| ≤ 18 * R.params.side * ε := by
    intro i
    have e : Y - TorusFields.unitStep n i + TorusFields.unitStep n i = Y := sub_add_cancel _ _
    refine abs_bondFit_sub_blockFitAt_le hKern hPlain hfit h16 W₀ Wst s.coarse s.bases hbases (s.storedBlockSet c) hW
      (fun Z' h => hfar _ Z' (hstep' i) h)
      (fun Z' h => hfar Y Z' (by rw [supDist_self]; omega) (by rwa [e] at h)) hε ?_
    rw [e]
    exact hclose' (hstep' i) (by rw [supDist_self]; omega)
  have hhalf : halfBlockFits R.params.side s.region Wst s.coarse Y = (1 / 2 : ℝ) * ∑ i : Fin 4,
      (blockFitAt R.params.side Wst s.coarse (Y, i) +
        blockFitAt R.params.side Wst s.coarse (Y - TorusFields.unitStep n i, i)) := by
    unfold halfBlockFits
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_pos (hYS _ (hstep i)), if_pos (hYS _ (hstep' i))]
  have hcost : s.blockCostAt Y 0 = ∑ y ∈ sitesInBlocks R.params.side {Y},
      levelShare R.params.coupling R.params.side R.depth X₀ y W₀ +
      R.params.coupling / 2 * ∑ i : Fin 4, (bondFit R.params W₀ s.coarse s.bases (Y, i) +
        bondFit R.params W₀ s.coarse s.bases (Y - TorusFields.unitStep n i, i)) := rfl
  rw [hcost, hsplit, hhalf]
  have hsum1 : |∑ y ∈ sitesInBlocks R.params.side {Y}, (levelShare R.params.coupling R.params.side R.depth X₀ y W₀ -
      levelShare R.params.coupling R.params.side R.depth X₁ y Wst)| ≤ (R.params.side : ℝ) ^ 4 * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ hshare).trans (le_of_eq ?_)
    rw [nsmul_eq_mul, card_sitesInBlocks_singleton hfit]
  have hsum2 : |∑ i : Fin 4, ((bondFit R.params W₀ s.coarse s.bases (Y, i) -
      blockFitAt R.params.side Wst s.coarse (Y, i)) +
      (bondFit R.params W₀ s.coarse s.bases (Y - TorusFields.unitStep n i, i) -
        blockFitAt R.params.side Wst s.coarse (Y - TorusFields.unitStep n i, i)))| ≤
      4 * (2 * (18 * R.params.side * ε)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
        |(bondFit R.params W₀ s.coarse s.bases (Y, i) - blockFitAt R.params.side Wst s.coarse (Y, i)) +
          (bondFit R.params W₀ s.coarse s.bases (Y - TorusFields.unitStep n i, i) -
            blockFitAt R.params.side Wst s.coarse (Y - TorusFields.unitStep n i, i))| ≤
        2 * (18 * R.params.side * ε) := by
      intro i _
      have := abs_add_le (bondFit R.params W₀ s.coarse s.bases (Y, i) - blockFitAt R.params.side Wst s.coarse (Y, i))
        (bondFit R.params W₀ s.coarse s.bases (Y - TorusFields.unitStep n i, i) -
          blockFitAt R.params.side Wst s.coarse (Y - TorusFields.unitStep n i, i))
      linarith [hf₁ i, hf₂ i]
    refine (Finset.sum_le_card_nsmul _ _ _ h1).trans (le_of_eq ?_)
    simp
  have hid : (∑ y ∈ sitesInBlocks R.params.side {Y}, levelShare R.params.coupling R.params.side R.depth X₀ y W₀ +
      R.params.coupling / 2 * ∑ i : Fin 4, (bondFit R.params W₀ s.coarse s.bases (Y, i) +
        bondFit R.params W₀ s.coarse s.bases (Y - TorusFields.unitStep n i, i))) -
      (∑ y ∈ sitesInBlocks R.params.side {Y}, levelShare R.params.coupling R.params.side R.depth X₁ y Wst +
        R.params.coupling * ((1 / 2 : ℝ) * ∑ i : Fin 4,
          (blockFitAt R.params.side Wst s.coarse (Y, i) +
            blockFitAt R.params.side Wst s.coarse (Y - TorusFields.unitStep n i, i)))) =
      (∑ y ∈ sitesInBlocks R.params.side {Y}, (levelShare R.params.coupling R.params.side R.depth X₀ y W₀ -
        levelShare R.params.coupling R.params.side R.depth X₁ y Wst)) +
        R.params.coupling / 2 * ∑ i : Fin 4, ((bondFit R.params W₀ s.coarse s.bases (Y, i) -
          blockFitAt R.params.side Wst s.coarse (Y, i)) +
          (bondFit R.params W₀ s.coarse s.bases (Y - TorusFields.unitStep n i, i) -
            blockFitAt R.params.side Wst s.coarse (Y - TorusFields.unitStep n i, i))) := by
    rw [Finset.sum_sub_distrib]
    have e2 : ∀ i : Fin 4, (bondFit R.params W₀ s.coarse s.bases (Y, i) -
        blockFitAt R.params.side Wst s.coarse (Y, i)) +
        (bondFit R.params W₀ s.coarse s.bases (Y - TorusFields.unitStep n i, i) -
          blockFitAt R.params.side Wst s.coarse (Y - TorusFields.unitStep n i, i)) =
        (bondFit R.params W₀ s.coarse s.bases (Y, i) +
          bondFit R.params W₀ s.coarse s.bases (Y - TorusFields.unitStep n i, i)) -
        (blockFitAt R.params.side Wst s.coarse (Y, i) +
          blockFitAt R.params.side Wst s.coarse (Y - TorusFields.unitStep n i, i)) := fun i => by ring
    simp only [e2]
    rw [Finset.sum_sub_distrib]
    ring
  rw [hid]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ R.params.coupling / 2)]
  have h7 := mul_le_mul_of_nonneg_left hsum2 (by positivity : 0 ≤ R.params.coupling / 2)
  have h8 : R.params.coupling / 2 * (4 * (2 * (18 * R.params.side * ε))) =
      72 * R.params.coupling * R.params.side * ε := by ring
  rw [h8] at h7
  linarith
theorem supDist_le_side_of_mem_block (hodd : Odd R.params.side) {Y : TorusSite n}
    {y y' : TorusSite (n * R.params.side)}
    (hy : y ∈ sitesInBlocks R.params.side {Y}) (hy' : y' ∈ sitesInBlocks R.params.side {Y}) :
    supDist y y' ≤ R.params.side := by
  obtain ⟨o, ho, e⟩ := exists_fineSite_of_parentBlock hodd Y y (parentBlock_eq_of_mem hy)
  obtain ⟨o', ho', e'⟩ := exists_fineSite_of_parentBlock hodd Y y' (parentBlock_eq_of_mem hy')
  rw [e, e', supDist_le_iff]
  intro i
  have hc := (BlockOffsets.mem_centredCube_iff o).mp ho i
  have hc' := (BlockOffsets.mem_centredCube_iff o').mp ho' i
  have hd : (fineSite R.params.side Y 0 o : TorusSite (n * R.params.side)) i - fineSite R.params.side Y 0 o' i =
      (((o i - o' i : ℤ)) : ZMod (n * R.params.side)) := by
    simp only [fineSite, siteOfInt]
    push_cast
    ring
  rw [hd]
  refine (natAbs_valMinAbs_intCast_le _).trans ?_
  omega
theorem exists_chartBond_in_block (hodd : Odd R.params.side) (hn : 2 ≤ n) (Y : TorusSite n) :
    ∃ x ∈ sitesInBlocks R.params.side {Y}, (x, (0 : Fin 4)) ∈ chartBonds R.params.side n := by
  classical
  obtain ⟨H, hH⟩ := hodd
  have hL : ((R.params.side : ℤ) - 1) / 2 = (H : ℤ) := by rw [hH]; push_cast; omega
  set o : Fin 4 → ℤ := fun _ => (H : ℤ) with ho
  have hoc : o ∈ centredCube R.params.side := by
    rw [BlockOffsets.mem_centredCube_iff, hL]
    intro l
    simp [ho]
  have hodd' : Odd R.params.side := ⟨H, hH⟩
  refine ⟨fineSite R.params.side Y 0 o, ?_, ?_⟩
  · have h1 := parentBlock_fineSite hodd' Y 0 o hoc
    have h0 : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite n) = 0 := by
      funext k
      simp [siteOfInt]
    rw [h0, add_zero] at h1
    have h2 := mem_sitesInBlocks_parentBlock (n := n) R.params.side (fineSite R.params.side Y 0 o)
    rwa [h1] at h2
  · simp only [chartBonds, Finset.mem_filter, Finset.mem_univ, true_and]
    intro htree
    apply htree.1
    show IsCrossingBond (F := stepBlockFrame R.params.side n) (torusSiteInFrame (stepBlockFrame R.params.side n) 0
      (siteOfInt (blockPoint R.params.side (fun i => ((Y i).cast : ℤ) + (0 : Fin 4 → ℤ) i) o)), 0)
    rw [BlockOffsets.torusSiteInFrame_siteOfInt, isCrossingBond_blockPoint_iff hodd' hn _ o hoc 0]
    intro hc
    have := ((BlockOffsets.mem_centredCube_iff _).mp hc 0).2
    rw [hL] at this
    simp [ho] at this
theorem parentBlock_mem_region (hs : s.IsAdmissible) {b : TorusBond (n * R.params.side)} (hb : b ∈ s.free)
    {q : TorusSite (n * R.params.side)}
    (hq : supDist b.1 q + R.params.side + 1 < 4 * R.range) (hr : lumpRange ≤ 2 * clusterRange R.nextCoupling) :
    parentBlock R.params.side q ∈ s.region := by
  rcases hs.region_spec with ⟨htop, -⟩ | ⟨-, htop, hfar⟩
  · rw [htop]
    exact Finset.mem_univ _
  · rw [htop]
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hw => ?_⟩
    obtain ⟨z, hz, hd⟩ := (mem_thickening _ _ _).mp hw
    have h1 := hfar b hb q ((mem_thickening _ _ _).mpr ⟨z, hz, hd.trans hr⟩)
    omega
theorem clusterRange_le {x : ℝ} (hx : 4 ≤ x) : (clusterRange x : ℝ) ≤ x := by
  have h1 : ((clusterRange x : ℕ) : ℝ) < x ^ ((1 : ℝ) / 100) + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2 : x ^ ((1 : ℝ) / 100) ≤ x ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h3 : x ^ ((1 : ℝ) / 2) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
  have h4 : Real.sqrt x ≤ x / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  linarith
theorem tail_bound {x A a Lr Q D E q₁ ε P Lq : ℝ} (hx1 : 1 ≤ x) (hA : 0 ≤ A) (ha : 0 ≤ a) (hLr : 0 ≤ Lr)
    (hQ : 0 ≤ Q) (hLq : 0 ≤ Lq) (hD : 1 ≤ D) (hE : 0 < E) (hq₁ : q₁ ≤ D * E) (hε : ε ≤ Q * (D * E))
    (hε0 : 0 ≤ ε) (hP0 : 0 ≤ P) (hP : P ≤ x) (hK : D * (Lq * A + 8 * Lq * A * Q + 72 * a * Lr * Q) + 1 ≤ x) :
    Lq * (A * q₁ + A * (2 * ε) * (4 * P ^ 4)) + 72 * a * Lr * ε ≤ x ^ 6 * E := by
  have hP4 : P ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ hP0 hP 4
  have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx1
  have h1 : A * q₁ ≤ A * (D * E) * x ^ 4 := by
    calc A * q₁ ≤ A * (D * E) := mul_le_mul_of_nonneg_left hq₁ hA
      _ ≤ A * (D * E) * x ^ 4 := le_mul_of_one_le_right (by positivity) hx4
  have h2 : A * (2 * ε) * (4 * P ^ 4) ≤ 8 * A * Q * (D * E) * x ^ 4 := by
    have e1 : A * (2 * ε) * (4 * P ^ 4) = (8 * A) * ε * P ^ 4 := by ring
    rw [e1]
    calc (8 * A) * ε * P ^ 4 ≤ (8 * A) * (Q * (D * E)) * P ^ 4 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hε (by positivity)) (by positivity)
      _ ≤ (8 * A) * (Q * (D * E)) * x ^ 4 := mul_le_mul_of_nonneg_left hP4 (by positivity)
      _ = _ := by ring
  have h3 : 72 * a * Lr * ε ≤ 72 * a * Lr * Q * (D * E) * x ^ 4 := by
    calc 72 * a * Lr * ε ≤ 72 * a * Lr * (Q * (D * E)) := mul_le_mul_of_nonneg_left hε (by positivity)
      _ = 72 * a * Lr * Q * (D * E) := by ring
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hx4
  set K := D * (Lq * A + 8 * Lq * A * Q + 72 * a * Lr * Q) with hKd
  have h4 : Lq * (A * q₁ + A * (2 * ε) * (4 * P ^ 4)) + 72 * a * Lr * ε ≤ K * x ^ 4 * E := by
    have h5 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hLq
    calc _ ≤ Lq * (A * (D * E) * x ^ 4 + 8 * A * Q * (D * E) * x ^ 4) + 72 * a * Lr * Q * (D * E) * x ^ 4 :=
          add_le_add h5 h3
      _ = _ := by rw [hKd]; ring
  have hK0 : K ≤ x ^ 2 := by nlinarith
  have h6 : K * x ^ 4 * E ≤ x ^ 2 * x ^ 4 * E :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK0 (by positivity)) hE.le
  calc _ ≤ K * x ^ 4 * E := h4
    _ ≤ x ^ 2 * x ^ 4 * E := h6
    _ = x ^ 6 * E := by ring
theorem eight_mul_le_half {N σ D E Cf ε : ℝ} (hN : 0 ≤ N) (hσ : 0 ≤ σ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hCf : 32 * N * D ≤ Cf) (hCE : Cf * E ≤ 1) (hε : ε ≤ 2 * N * σ * (D * E)) : 8 * ε ≤ σ / 2 := by
  have h1 : 32 * N * D * E ≤ 1 := (mul_le_mul_of_nonneg_right hCf hE).trans hCE
  have h2 : 16 * (N * D * E) ≤ 1 / 2 := by nlinarith
  have h5 : σ * (16 * (N * D * E)) ≤ σ * (1 / 2) := mul_le_mul_of_nonneg_left h2 hσ
  linarith
theorem exp_neg_le_mul_exp {δ c r m : ℝ} (hδ : 0 < δ) (hc : c * r ≤ δ * (m + 1)) :
    Real.exp (-(δ * m)) ≤ Real.exp δ * Real.exp (-c * r) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  nlinarith
theorem mul_le_one_of_stretched {x Cf E : ℝ} (hx : 1 ≤ x) (hCf : 1 ≤ Cf) (hE : 0 ≤ E)
    (h : Cf * x ^ Cf * E ≤ Real.exp (-(x ^ (1 / 200 : ℝ)))) : Cf * E ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have h1 : 1 ≤ x ^ Cf := Real.one_le_rpow hx (by linarith)
  have h2 : Real.exp (-(x ^ (1 / 200 : ℝ))) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have := Real.rpow_nonneg hx0.le (1 / 200 : ℝ)
    linarith
  have h3 : Cf * E ≤ Cf * x ^ Cf * E := by
    have : 0 ≤ Cf * E := by positivity
    nlinarith
  linarith
end FrameCost
open FrameCost in
set_option maxHeartbeats 4000000 in
theorem frameCostNearLevelShare_of (hField : FrameFieldNearMinimizer)
    (hReg : SettingRegionsRegular) (hNear : ShareContinuity.ShareLipschitzInField)
    (hPlain : PlainFitsOfNearFields) (hKern : KernelPlainAwayFromLumps)
    (hSplit : LevelShareSplits) (hSh : ShareLocalityExists)
    (hFl : StepFloors.EventuallyFloorConditions) : FrameCostNearLevelShare := by
  intro T hT
  obtain ⟨y₁, hF₁⟩ := hField T hT
  obtain ⟨y₂, hF₂⟩ := hReg T hT
  have ha : 0 < T.coupling := by linarith [hT.a_ge]
  have hoddT : Odd T.side := hT.L_odd
  obtain ⟨A, hA, hS⟩ := hSh T.coupling T.δ₁ T.side T.lam T.ρA T.σA T.cg T.N ha hoddT hT.chain
  obtain ⟨hδ, -, -, -, -, -, -, hNp, -⟩ := hT.chain
  have hN0 : 0 < T.N 0 := hNp 0
  have hσ0 : 0 < T.threshold := hT.σ_pos
  set D : ℝ := Real.exp T.δ₁ with hD
  have hD1 : 1 ≤ D := Real.one_le_exp hδ.le
  set Q : ℝ := 2 * T.N 0 * T.threshold with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set Lq : ℝ := (T.side : ℝ) ^ 4 with hLq
  have hLq0 : 0 ≤ Lq := by positivity
  set K : ℝ := D * (Lq * A + 8 * Lq * A * Q + 72 * T.coupling * (T.side : ℝ) * Q) with hK
  have hK0 : 0 ≤ K := by positivity
  set c : ℝ := T.δ₁ / 2 ^ 12 with hc
  have hc0 : 0 < c := by positivity
  set Cf : ℝ := 2 ^ 18 + (T.side : ℝ) * 32 + 32 * T.N 0 * D with hCf
  have hCf1 : 1 ≤ Cf := by
    have : 0 ≤ (T.side : ℝ) * 32 + 32 * T.N 0 * D := by positivity
    rw [hCf]
    linarith
  obtain ⟨yf, hF⟩ := hFl T hT Cf c (by linarith) hc0
  refine ⟨6, c, max (max y₁ y₂) (max yf (max T.floorMin (max 4 (K + 1)))), by norm_num, hc0,
    fun y hy R hR n _ hn s hs c' Y hst hmk hoff => ?_⟩
  simp only [max_le_iff] at hy
  obtain ⟨⟨hy₁, hy₂⟩, hyf, hyT, hy4, hyK⟩ := hy
  have hxR : y ≤ R.coupling := hR.le_coupling
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hT.fits y hyT
  have hLe : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hLr : (R.params.side : ℝ) = (T.side : ℝ) := by rw [hLe]
  have haR : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
  have hσe : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hn₀e : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have hx4 : 4 ≤ R.coupling := hy4.trans hxR
  have hx1 : 1 ≤ R.coupling := by linarith
  have hFx := hF R.coupling (hyf.trans hxR)
  have hrC : Cf ≤ (R.range : ℝ) := hFx.range_ge
  have hr18 : 2 ^ 18 + (T.side : ℝ) * 32 ≤ (R.range : ℝ) := by
    have : 0 ≤ 32 * T.N 0 * D := by positivity
    rw [hCf] at hrC
    linarith
  have hrN : 2 ^ 18 + T.side * 32 ≤ R.range := by exact_mod_cast hr18
  have hodd : Odd R.params.side := hfit.L_odd
  have hn₀ := hfit.n₀_ge
  have h64 : 64 ≤ n := by omega
  have hρ0 : 0 ≤ R.ballRadius := by
    have h1 : R.ballRadius = R.params.threshold / 64 := rfl
    rw [h1, hσe]
    positivity
  have hz0 : s.InBalls (0 : FreeCoords s.free) := by
    intro b
    rw [coordNorm_toImaginary]
    simpa using hρ0
  obtain ⟨rS1, rS2, rS3, rS4, rS5⟩ := hF₂ y hy₂ R hR n hn s hs
  have hclose := hF₁ y hy₁ R hR n hn s hs c' hst hmk
  have hSR : ShareLocality R.params.coupling R.params.side T.σA A T.δ₁ := by
    rw [haR, hLe]
    exact hS
  have hchain : ColdChain.ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [haR, hLe, hR.anchorRadius_eq]
    exact hT.chain
  have hσA : 2 * T.threshold ≤ T.σA := hT.σ_le
  have hY3 : ∀ Z : TorusSite n, supDist Y Z ≤ 3 → Z ∉ s.storedBlockSet c' := by
    intro Z hZ
    have h0 : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite n) = 0 := by
      funext k
      simp [siteOfInt]
    have hz0c : (0 : Fin 4 → ℤ) ∈ centredCube R.params.side := by
      rw [BlockOffsets.mem_centredCube_iff]
      intro l
      have : (1 : ℤ) ≤ R.params.side := by exact_mod_cast hodd.pos
      simp only [Pi.zero_apply]
      omega
    have hb : ∀ Z' : TorusSite n,
        parentBlock R.params.side (fineSite R.params.side Z' 0 0 : TorusSite (n * R.params.side)) = Z' := by
      intro Z'
      rw [parentBlock_fineSite hodd Z' 0 0 hz0c, h0, add_zero]
    have hy0 : (fineSite R.params.side Y 0 0 : TorusSite (n * R.params.side)) ∈ sitesInBlocks R.params.side {Y} := by
      have := mem_sitesInBlocks_parentBlock (n := n) R.params.side (fineSite R.params.side Y 0 0)
      rwa [hb] at this
    have h1 := supDist_fineSite_le (n := n) R.params.side Y Z
    have h2 : supDist (fineSite R.params.side Y 0 0 : TorusSite (n * R.params.side)) (fineSite R.params.side Z 0 0) ≤
        R.params.side * 3 :=
      h1.trans (Nat.mul_le_mul_left _ hZ)
    have h3 : (supDist (fineSite R.params.side Y 0 0 : TorusSite (n * R.params.side))
        (fineSite R.params.side Z 0 0) : ℝ) ≤ (R.range : ℝ) / 8 := by
      have h4 : (supDist (fineSite R.params.side Y 0 0 : TorusSite (n * R.params.side))
          (fineSite R.params.side Z 0 0) : ℝ) ≤ (R.params.side : ℝ) * 3 := by
        exact_mod_cast h2
      rw [hLr] at h4
      have : (0 : ℝ) ≤ (T.side : ℝ) := Nat.cast_nonneg _
      linarith
    have := parentBlock_not_mem_storedBlockSet s c' hoff hy0 h3
    rwa [hb] at this
  have hYst : Y ∉ s.storedBlockSet c' := hY3 Y (by rw [supDist_self]; omega)
  obtain ⟨x₀, hx₀, hx₀c⟩ := exists_chartBond_in_block (R := R) hodd (by omega : 2 ≤ n) Y
  have hx₀b : parentBlock R.params.side x₀ = Y := parentBlock_eq_of_mem hx₀
  have hfree : (x₀, (0 : Fin 4)) ∈ s.free := by
    rw [hst.free_eq]
    refine Finset.mem_filter.mpr ⟨hx₀c, ?_, ?_⟩
    · show parentBlock R.params.side x₀ ∉ c'.core
      rw [hx₀b]
      exact fun h => hYst (Finset.mem_union_left _ h)
    · intro h
      have h1 : parentBlock R.params.side x₀ ∈ s.storedBlockSet c' := h.1
      rw [hx₀b] at h1
      exact hYst h1
  have hrr : lumpRange ≤ 2 * clusterRange R.nextCoupling := by
    have h1 : R.range ≤ clusterRange R.nextCoupling + 1 := hR.isStep.2.2
    have h2 : lumpRange = 2 ^ 12 := rfl
    omega
  have hLT : R.params.side = T.side := hLe
  have htop : ∀ q : TorusSite (n * R.params.side), supDist x₀ q + R.params.side + 1 < 4 * R.range →
      parentBlock R.params.side q ∈ s.region :=
    fun q hq => parentBlock_mem_region s hs hfree hq hrr
  set ρ : ℕ := R.range / 16 with hρd
  have hρN : 16 * ρ ≤ R.range := Nat.mul_div_le _ _
  have hρlow : R.range < 16 * (ρ + 1) := by
    have := Nat.lt_mul_div_succ R.range (by norm_num : 0 < 16)
    simpa [hρd] using this
  have hρ : (ρ : ℝ) + 1 + (lumpRange : ℝ) ≤ (R.range : ℝ) / 8 := by
    have h1 : (16 : ℝ) * ρ ≤ (R.range : ℝ) := by exact_mod_cast hρN
    have h2 : (lumpRange : ℝ) = 2 ^ 12 := by
      show ((2 ^ 12 : ℕ) : ℝ) = _
      norm_num
    rw [h2]
    have : (0 : ℝ) ≤ (T.side : ℝ) * 32 := by positivity
    linarith
  have hYS : ∀ Z : TorusSite n, supDist Y Z ≤ 1 → Z ∈ s.region := by
    intro Z hZ
    have h0 : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite n) = 0 := by
      funext k
      simp [siteOfInt]
    have hz0c : (0 : Fin 4 → ℤ) ∈ centredCube R.params.side := by
      rw [BlockOffsets.mem_centredCube_iff]
      intro l
      have : (1 : ℤ) ≤ R.params.side := by exact_mod_cast hodd.pos
      simp only [Pi.zero_apply]
      omega
    have hb : ∀ Z' : TorusSite n,
        parentBlock R.params.side (fineSite R.params.side Z' 0 0 : TorusSite (n * R.params.side)) = Z' := by
      intro Z'
      rw [parentBlock_fineSite hodd Z' 0 0 hz0c, h0, add_zero]
    have hy0 : (fineSite R.params.side Y 0 0 : TorusSite (n * R.params.side)) ∈ sitesInBlocks R.params.side {Y} := by
      have := mem_sitesInBlocks_parentBlock (n := n) R.params.side (fineSite R.params.side Y 0 0)
      rwa [hb] at this
    have h1 := supDist_fineSite_le (n := n) R.params.side Y Z
    have h2 : supDist (fineSite R.params.side Y 0 0 : TorusSite (n * R.params.side)) (fineSite R.params.side Z 0 0) ≤
        R.params.side * 1 :=
      h1.trans (Nat.mul_le_mul_left _ hZ)
    have h3 := supDist_le_side_of_mem_block hodd hx₀ hy0
    have h4 := supDist_triangle x₀ (fineSite R.params.side Y 0 0) (fineSite R.params.side Z 0 0)
    have := htop (fineSite R.params.side Z 0 0) (by omega)
    rwa [hb] at this
  have hqS : ∀ y' ∈ sitesInBlocks R.params.side {Y}, ∀ q : TorusSite (n * R.params.side),
      (supDist y' q : ℝ) ≤ (ρ : ℝ) + 1 → parentBlock R.params.side q ∈ s.region := by
    intro y' hy' q hq
    have h1 : supDist y' q ≤ ρ + 1 := by exact_mod_cast hq
    have h3 := supDist_le_side_of_mem_block hodd hx₀ hy'
    have h4 := supDist_triangle x₀ y' q
    exact htop q (by omega)
  have hs₁ : 0 < 9 / 8 * T.threshold := by positivity
  have hσ₁ : R.params.threshold ≤ 9 / 8 * T.threshold := by rw [hσe]; linarith
  have hsplit := hSplit R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N
    (by rw [haR]; exact ha) hodd hchain R.depth n s.region s.coarse
    (9 / 8 * T.threshold) Y h64 hs₁ (by linarith) rS1 rS2 (hYS Y (by rw [supDist_self]; omega))
  set E : ℝ := Real.exp (-c * (R.range : ℝ)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hcr : c * (R.range : ℝ) ≤ T.δ₁ * ((R.range : ℝ) / 2 ^ 12) := by
    rw [hc]
    apply le_of_eq
    ring
  have hrpos : (0 : ℝ) ≤ (R.range : ℝ) := Nat.cast_nonneg _
  have hm₀ : ((R.range : ℝ) / 2 ^ 12) ≤ (R.frameReach : ℝ) + 1 := by
    have h1 : R.range < 2 ^ 11 * (R.frameReach + 1) := by
      have := Nat.lt_mul_div_succ R.range (by norm_num : 0 < 2 ^ 11)
      exact this
    have h2 : (R.range : ℝ) < 2 ^ 11 * ((R.frameReach : ℝ) + 1) := by exact_mod_cast h1
    have h3 : (0 : ℝ) ≤ (R.frameReach : ℝ) := Nat.cast_nonneg _
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  have hρ12 : ((R.range : ℝ) / 2 ^ 12) ≤ (ρ : ℝ) + 1 := by
    have h2 : (R.range : ℝ) < 16 * ((ρ : ℝ) + 1) := by exact_mod_cast hρlow
    have h3 : (0 : ℝ) ≤ (ρ : ℝ) := Nat.cast_nonneg _
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  have hq₁ : Real.exp (-(T.δ₁ * (ρ : ℝ))) ≤ D * E :=
    exp_neg_le_mul_exp hδ (hcr.trans (mul_le_mul_of_nonneg_left hρ12 hδ.le))
  have hq₂ : Real.exp (-(T.δ₁ * (R.frameReach : ℝ))) ≤ D * E :=
    exp_neg_le_mul_exp hδ (hcr.trans (mul_le_mul_of_nonneg_left hm₀ hδ.le))
  set ε : ℝ := 2 * T.N 0 * T.threshold * Real.exp (-(T.δ₁ * (R.frameReach : ℝ))) with hεd
  have hε0 : 0 ≤ ε := by positivity
  have hεE : ε ≤ Q * (D * E) := mul_le_mul_of_nonneg_left hq₂ hQ0
  have hCE : Cf * E ≤ 1 := by
    have e : E = Real.exp (-(c * (clusterRange R.coupling : ℝ))) := by
      rw [hE, neg_mul]
      rfl
    rw [e]
    exact mul_le_one_of_stretched hx1 hCf1 (Real.exp_pos _).le hFx.stretched_tail.1
  have hε8 : 8 * ε ≤ T.threshold / 2 := by
    refine eight_mul_le_half hN0.le hσ0.le (by linarith) hE0.le ?_ hCE hεE
    have : 0 ≤ 2 ^ 18 + (T.side : ℝ) * 32 := by positivity
    rw [hCf]
    linarith
  have hs₀ : 9 / 8 * T.threshold + 8 * ε ≤ T.σA := by linarith
  have hb := abs_blockCostAt_sub_levelShare_le s c' hKern hPlain hNear hfit h64 hs hz0 hoff hSR hA.le hδ.le
    (by rw [haR]; exact ha.le) hε0 hs₁ hσ₁ hs₀ hρ (rS5 _) rS3 rS4 hclose hY3 hYS hqS hsplit
  refine hb.trans ?_
  rw [hLr, haR]
  have hr_x : (R.range : ℝ) ≤ R.coupling := clusterRange_le hx4
  have hP : 2 * (ρ : ℝ) + 2 ≤ R.coupling := by
    have h1 : (16 : ℝ) * ρ ≤ (R.range : ℝ) := by exact_mod_cast hρN
    have h2 : (2 : ℝ) ^ 18 ≤ (R.range : ℝ) := by
      have : (0 : ℝ) ≤ (T.side : ℝ) * 32 := by positivity
      linarith
    linarith
  have hfin := tail_bound (x := R.coupling) (A := A) (a := T.coupling) (Lr := (T.side : ℝ)) (Q := Q) (D := D)
    (E := E) (q₁ := Real.exp (-(T.δ₁ * (ρ : ℝ)))) (ε := ε) (P := 2 * (ρ : ℝ) + 2) (Lq := Lq) hx1 hA.le ha.le
    (by positivity) hQ0 hLq0 hD1 hE0 hq₁ hεE hε0 (by positivity) hP (hyK.trans hxR)
  have e6 : R.coupling ^ (6 : ℝ) = R.coupling ^ 6 := by
    have := Real.rpow_natCast R.coupling 6
    exact_mod_cast this
  rw [e6]
  exact hfin
end YangMills.Construction.ClusterExpansionOfAStep
end
