import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ClusterExpansionOfAStep.LumpsAreFibres
import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyAtTheLeastChartProof
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages TorusLumps StepCosts ColdStepAtMirrorFrames LumpContours
namespace TopLevelSites
section EvaluationOnTheTorus
variable {F : BlockFrame} {j N : ℕ} [NeZero N]
theorem period_neZero (hp : ∀ i, F.period j i = N) (i : Fin 4) : NeZero (F.period j i) :=
  ⟨by rw [hp]; exact NeZero.ne N⟩
theorem toTorusSite_add (hp : ∀ i, F.period j i = N) (x y : F.Site j) :
    toTorusSite N (x + y) = toTorusSite N x + toTorusSite N y := by
  funext k
  haveI := period_neZero hp k
  exact castInt_add (hp k) (x k) (y k)
theorem toTorusSite_neg (hp : ∀ i, F.period j i = N) (x : F.Site j) :
    toTorusSite N (-x) = - toTorusSite N x := by
  funext k
  haveI := period_neZero hp k
  exact castInt_neg (hp k) (x k)
theorem toTorusSite_siteOfCoords (hp : ∀ i, F.period j i = N) (c : Fin 4 → ℤ) :
    toTorusSite N (siteOfCoords j c : F.Site j) = TorusFields.siteOfInt c := by
  funext k
  haveI := period_neZero hp k
  exact castInt_intCast (hp k) (c k)
theorem toTorusSite_unitStep (hp : ∀ i, F.period j i = N) (i : Fin 4) :
    toTorusSite N (unitStep j i : F.Site j) = TorusFields.unitStep N i := by
  unfold unitStep
  rw [toTorusSite_siteOfCoords hp]
  funext k
  by_cases hk : k = i
  · subst hk
    simp [TorusFields.siteOfInt, TorusFields.unitStep]
  · simp [TorusFields.siteOfInt, TorusFields.unitStep, Pi.single_apply, hk]
theorem toTorusSite_torusSiteInFrame (hp : ∀ i, F.period j i = N) (x : TorusFields.TorusSite N) :
    toTorusSite N (torusSiteInFrame F j x) = x := by
  funext k
  haveI := period_neZero hp k
  simp only [toTorusSite, torusSiteInFrame, siteOfCoords, siteCoords]
  rw [castInt_intCast (hp k)]
  simp
theorem toTorusSite_injective (hp : ∀ i, F.period j i = N) {x y : F.Site j}
    (h : toTorusSite N x = toTorusSite N y) : x = y := by
  funext k
  haveI := period_neZero hp k
  exact castInt_injective (hp k) _ _ (congrFun h k)
theorem torusSiteInFrame_toTorusSite (hp : ∀ i, F.period j i = N) (x : F.Site j) :
    torusSiteInFrame F j (toTorusSite N x) = x :=
  toTorusSite_injective hp (toTorusSite_torusSiteInFrame hp _)
theorem torusSiteInFrame_add (hp : ∀ i, F.period j i = N) (x y : TorusFields.TorusSite N) :
    torusSiteInFrame F j (x + y) = torusSiteInFrame F j x + torusSiteInFrame F j y := by
  apply toTorusSite_injective hp
  rw [toTorusSite_add hp, toTorusSite_torusSiteInFrame hp, toTorusSite_torusSiteInFrame hp,
    toTorusSite_torusSiteInFrame hp]
theorem torusSiteInFrame_siteOfInt (hp : ∀ i, F.period j i = N) (c : Fin 4 → ℤ) :
    torusSiteInFrame F j (TorusFields.siteOfInt c : TorusFields.TorusSite N) = siteOfCoords j c := by
  apply toTorusSite_injective hp
  rw [toTorusSite_torusSiteInFrame hp, toTorusSite_siteOfCoords hp]
theorem readAtLevel_torusSiteInFrame (hp : ∀ i, F.period j i = N) (W : TorusFields.TorusField N)
    (x : TorusFields.TorusSite N) (i : Fin 4) :
    TorusFields.readAtLevel F j W (torusSiteInFrame F j x) i = W x i := by
  have : TorusFields.readAtLevel F j W (torusSiteInFrame F j x) i =
      W (toTorusSite N (torusSiteInFrame F j x)) i := rfl
  rw [this, toTorusSite_torusSiteInFrame hp]
theorem siteCoords_torusSiteInFrame (hp : ∀ i, F.period j i = N) (x : TorusFields.TorusSite N)
    (i : Fin 4) : siteCoords (torusSiteInFrame F j x) i = ((x i).cast : ℤ) := by
  haveI := period_neZero hp i
  have h0 : (0 : ℤ) ≤ ((x i).cast : ℤ) := by
    rw [ZMod.cast_eq_val]
    positivity
  have h1 : ((x i).cast : ℤ) < (N : ℤ) := by
    rw [ZMod.cast_eq_val]
    exact_mod_cast ZMod.val_lt (x i)
  simp only [siteCoords, torusSiteInFrame, siteOfCoords]
  rw [ZMod.coe_intCast, hp i]
  exact Int.emod_eq_of_lt h0 h1
theorem plaquetteDefect_readAtLevel_eq (hp : ∀ i, F.period j i = N) (W : TorusFields.TorusField N)
    (x : F.Site j) (μ ν : Fin 4) :
    plaquetteDefect (TorusFields.readAtLevel F j W) (x, μ, ν) =
      TorusFields.curvature W (toTorusSite N x) μ ν := by
  unfold plaquetteDefect TorusFields.curvature TorusFields.holonomy
  have hv : plaquetteHolonomy (TorusFields.readAtLevel F j W) (x, μ, ν) =
      W (toTorusSite N x) μ * W (toTorusSite N x + TorusFields.unitStep N μ) ν *
        (W (toTorusSite N x + TorusFields.unitStep N ν) μ)⁻¹ * (W (toTorusSite N x) ν)⁻¹ := by
    have a1 : x + unitStep j μ + unitStep j ν - unitStep j μ = x + unitStep j ν := by abel
    have a2 : x + unitStep j μ + unitStep j ν + -unitStep j μ - unitStep j ν = x := by abel
    have hr : ∀ (z : F.Site j) (i : Fin 4),
        TorusFields.readAtLevel F j W z i = W (toTorusSite N z) i := fun _ _ => rfl
    simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true,
      Bool.false_eq_true, if_false, mul_one, a1, a2, hr, toTorusSite_add hp,
      toTorusSite_unitStep hp, mul_assoc]
  rw [hv]
end EvaluationOnTheTorus
section BlockGeometry
variable {F : BlockFrame}
theorem top_sub_depth : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by simp [BlockFrame.period]
theorem period_depth (i : Fin 4) : F.period F.depth i = F.extent i * F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimizingChart.period_depth <;> assumption
theorem finite_cell (hs : ∀ i, 0 < F.extent i) : Finite F.Cell := by
  have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
    rw [period_top]
    exact (hs i).ne'⟩
  have : ∀ i, Finite (ZMod (F.period F.top i)) := fun i => by
    have := hne i
    exact inferInstance
  exact Pi.finite
theorem mem_finiteCells (hs : ∀ i, 0 < F.extent i) (z : F.Cell) : z ∈ finiteCells F := by apply _root_.YangMills.Construction.FrameTorusAction.mem_finiteCells <;> assumption
def halfWidth (L : ℕ) : ℤ := ((L : ℤ) - 1) / 2
theorem mem_centredCube_iff {L : ℕ} (c : Fin 4 → ℤ) :
    c ∈ centredCube L ↔ ∀ i, -halfWidth L ≤ c i ∧ c i ≤ halfWidth L := by apply _root_.YangMills.Construction.LatticePaths.mem_centredCube_iff <;> assumption
theorem siteCoords_centre_add (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (c : Fin 4 → ℤ) (hc : c ∈ centredCube F.blockSide) (i : Fin 4) :
    ∃ e : ℤ, siteCoords (cellCentre F.depth z + siteOfCoords F.depth c : F.Site F.depth) i =
      (F.blockSide : ℤ) * siteCoords z i + c i + (F.extent i : ℤ) * F.blockSide * e ∧
        (e = 0 ∨ e = 1) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.siteCoords_offset <;> assumption
theorem enclosingCell_centre_add (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (c : Fin 4 → ℤ) (hc : c ∈ centredCube F.blockSide) :
    enclosingCell (cellCentre F.depth z + siteOfCoords F.depth c : F.Site F.depth) = z := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.enclosingCell_offset <;> assumption
theorem cellOffset_centre_add (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (c : Fin 4 → ℤ) (hc : c ∈ centredCube F.blockSide) :
    cellOffset (cellCentre F.depth z + siteOfCoords F.depth c : F.Site F.depth) = c := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.cellOffset_offset <;> assumption
theorem unitStep_top_ne_zero (hs : ∀ i, 2 ≤ F.extent i) (i : Fin 4) :
    (unitStep F.top i : F.Cell) ≠ 0 := by apply _root_.YangMills.Construction.GaugeFixing.unitStep_top_ne_zero <;> assumption
theorem centre_add_add_unitStep (z : F.Cell) (c : Fin 4 → ℤ) (i : Fin 4) :
    (cellCentre F.depth z + siteOfCoords F.depth c + unitStep F.depth i : F.Site F.depth) =
      cellCentre F.depth z + siteOfCoords F.depth (c + Pi.single i 1) := by apply _root_.YangMills.Construction.GaugeFixing.cellCentre_add_siteOfCoords_add_unitStep <;> assumption
theorem cellCentre_add_unitStep (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (i : Fin 4) :
    (cellCentre F.depth (z + unitStep F.top i) : F.Site F.depth) =
      cellCentre F.depth z + siteOfCoords F.depth (Pi.single i (F.blockSide : ℤ)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.cellCentre_add_unitStep <;> assumption
theorem centre_add_add_unitStep_of_edge (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (z : F.Cell) (c : Fin 4 → ℤ) (hc : c ∈ centredCube F.blockSide) (i : Fin 4)
    (he : c i = halfWidth F.blockSide) :
    (c + Pi.single i (1 - (F.blockSide : ℤ))) ∈ centredCube F.blockSide ∧
      (cellCentre F.depth z + siteOfCoords F.depth c + unitStep F.depth i : F.Site F.depth) =
        cellCentre F.depth (z + unitStep F.top i) +
          siteOfCoords F.depth (c + Pi.single i (1 - (F.blockSide : ℤ))) := by
  have hcb := (mem_centredCube_iff c).mp hc
  set c' : Fin 4 → ℤ := c + Pi.single i (1 - (F.blockSide : ℤ)) with hc'
  obtain ⟨k, hk⟩ := hL
  have hLz : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have hk2 : halfWidth F.blockSide = k := by
    unfold halfWidth
    rw [hLz]
    omega
  refine ⟨?_, ?_⟩
  · rw [mem_centredCube_iff]
    intro l
    by_cases hl : l = i
    · subst hl
      simp only [hc', Pi.add_apply, Pi.single_eq_same, he]
      rw [hk2, hLz]
      constructor <;> linarith
    · simp only [hc', Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
      exact hcb l
  · rw [cellCentre_add_unitStep hs, centre_add_add_unitStep]
    have e2 : (siteOfCoords F.depth (c + Pi.single i 1) : F.Site F.depth) =
        siteOfCoords F.depth (Pi.single i (F.blockSide : ℤ)) + siteOfCoords F.depth c' := by
      funext l
      by_cases hl : l = i
      · subst hl
        simp [siteOfCoords, hc']
        ring
      · simp [siteOfCoords, hc', Pi.single_eq_of_ne hl]
    rw [e2, add_assoc]
theorem isCrossingBond_iff (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (c : Fin 4 → ℤ) (hc : c ∈ centredCube F.blockSide) (i : Fin 4) :
    IsCrossingBond ((cellCentre F.depth z + siteOfCoords F.depth c : F.Site F.depth), i) ↔
      c i = halfWidth F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.isCrossingBond_iff <;> assumption
def IsTreeOffset (L : ℕ) (b : (Fin 4 → ℤ) × Fin 4) : Prop :=
  b.1 b.2 ≠ halfWidth L ∧ ∀ l, b.2 < l → b.1 l = 0
theorem isAxialTreeBond_iff (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (c : Fin 4 → ℤ) (hc : c ∈ centredCube F.blockSide) (i : Fin 4) :
    IsAxialTreeBond ((cellCentre F.depth z + siteOfCoords F.depth c : F.Site F.depth), i) ↔
      IsTreeOffset F.blockSide (c, i) := by
  unfold IsAxialTreeBond IsTreeOffset
  simp only
  rw [isCrossingBond_iff hL hs z c hc i, cellOffset_centre_add hL hs z c hc]
theorem exists_centre_add (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) :
    ∃ (z : F.Cell) (h : Fin 4 → ℤ), h ∈ centredCube F.blockSide ∧
      x = cellCentre F.depth z + siteOfCoords F.depth h := by
  obtain ⟨k, hk⟩ := hL
  have hLpos : 0 < F.blockSide := by omega
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hne1 : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by rw [period_top]; exact (hpos i).ne'⟩
  have hne0 : ∀ i, NeZero (F.period F.depth i) := fun i =>
    ⟨by rw [period_depth]; exact (Nat.mul_pos (hpos i) hLpos).ne'⟩
  set c : Fin 4 → ℤ := siteCoords x with hc
  set q : Fin 4 → ℤ := fun i => (c i + k) / (F.blockSide : ℤ) with hq
  set h : Fin 4 → ℤ := fun i => c i - (F.blockSide : ℤ) * q i with hh
  have hLz : (0 : ℤ) < (F.blockSide : ℤ) := by exact_mod_cast hLpos
  have hLk : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  refine ⟨siteOfCoords F.top q, h, ?_, ?_⟩
  · rw [mem_centredCube_iff]
    intro i
    have e1 := Int.emod_add_mul_ediv (c i + k) (F.blockSide : ℤ)
    have e2 := Int.emod_nonneg (c i + k) hLz.ne'
    have e3 := Int.emod_lt_of_pos (c i + k) hLz
    have e4 : halfWidth F.blockSide = k := by
      unfold halfWidth
      rw [hLk]
      omega
    rw [e4]
    simp only [hh, hq]
    constructor <;> nlinarith
  · funext i
    have := hne1 i
    have := hne0 i
    simp only [cellCentre, siteOfCoords, siteCoords, top_sub_depth, pow_one, Pi.add_apply]
    have e1 : (((F.blockSide : ℤ) * ZMod.cast ((q i : ZMod (F.period F.top i)) :
        ZMod (F.period F.top i)) : ℤ) : ZMod (F.period F.depth i)) =
        (((F.blockSide : ℤ) * q i : ℤ) : ZMod (F.period F.depth i)) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      rw [ZMod.coe_intCast]
      have e2 := Int.emod_add_mul_ediv (q i) (F.period F.top i : ℤ)
      refine ⟨q i / (F.period F.top i : ℤ), ?_⟩
      rw [period_depth, period_top i] at *
      push_cast
      linear_combination (-(F.blockSide : ℤ)) * e2
    rw [e1, ← Int.cast_add]
    have e3 : (F.blockSide : ℤ) * q i + h i = c i := by
      simp only [hh]
      ring
    rw [e3]
    simp only [hc, siteCoords]
    exact (ZMod.intCast_zmod_cast (x i)).symm
theorem centre_cellOffset (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) :
    cellOffset x ∈ centredCube F.blockSide ∧
      cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth (cellOffset x) = x := by
  obtain ⟨z, h, hh, rfl⟩ := exists_centre_add hL hs x
  rw [cellOffset_centre_add hL hs z h hh, enclosingCell_centre_add hL hs z h hh]
  exact ⟨hh, rfl⟩
theorem enclosingCell_add_unitStep (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) (i : Fin 4) (hc : IsCrossingBond (x, i)) :
    enclosingCell (x + unitStep F.depth i) = enclosingCell x + unitStep F.top i := by
  obtain ⟨z, h, hh, rfl⟩ := exists_centre_add hL hs x
  rw [isCrossingBond_iff hL hs z h hh i] at hc
  obtain ⟨hin, e⟩ := centre_add_add_unitStep_of_edge hL hs z h hh i hc
  rw [e, enclosingCell_centre_add hL hs _ _ hin, enclosingCell_centre_add hL hs _ _ hh]
end BlockGeometry
end TopLevelSites
end YangMills.Construction
end
