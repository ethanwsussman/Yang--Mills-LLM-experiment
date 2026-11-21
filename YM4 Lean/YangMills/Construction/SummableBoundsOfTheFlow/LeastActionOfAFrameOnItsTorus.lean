import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps ColdStepAtMirrorFrames
namespace FrameTorusAction
theorem mem_sitesOfCells_of_forall_mem {F : BlockFrame} (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {S : Finset F.Cell} (hS : ∀ z : F.Cell, z ∈ S) {j : ℕ} (x : F.Site j) : x ∈ sitesOfCells S j := by
  set M : ℕ := F.blockSide ^ (F.top - j) with hM
  obtain ⟨k, hk⟩ := hodd.pow (n := F.top - j)
  have hMpos : 0 < M := by rw [hM, hk]; omega
  have hperTop : ∀ i, F.period F.top i = F.extent i := by
    intro i
    simp [BlockFrame.period]
  have hperLevel : ∀ i, F.period j i = F.extent i * M := fun i => rfl
  have hneTop : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by rw [hperTop]; exact (hs i).ne'⟩
  have hneLevel : ∀ i, NeZero (F.period j i) := fun i =>
    ⟨by rw [hperLevel]; exact (Nat.mul_pos (hs i) hMpos).ne'⟩
  set c : Fin 4 → ℤ := siteCoords x with hc
  set q : Fin 4 → ℤ := fun i => (c i + k) / (M : ℤ) with hq
  set r : Fin 4 → ℤ := fun i => c i - (M : ℤ) * q i with hr
  have hMz : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hMpos
  have hMk : (M : ℤ) = 2 * k + 1 := by
    rw [hM, hk]
    push_cast
    ring
  unfold sitesOfCells
  rw [Finset.mem_biUnion]
  refine ⟨siteOfCoords F.top q, hS _, ?_⟩
  rw [Finset.mem_image]
  refine ⟨r, ?_, ?_⟩
  · unfold centredCube
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have e1 := Int.emod_add_mul_ediv (c i + k) (M : ℤ)
    have e2 := Int.emod_nonneg (c i + k) hMz.ne'
    have e3 := Int.emod_lt_of_pos (c i + k) hMz
    have e4 : (((F.blockSide ^ (F.top - j) : ℕ) : ℤ) - 1) / 2 = k := by
      rw [← hM, hMk]
      omega
    have e5 : ((F.blockSide ^ (F.top - j) : ℕ) : ℤ) = (M : ℤ) := rfl
    rw [e5] at e4 ⊢
    rw [e4]
    simp only [hr, hq]
    constructor <;> nlinarith
  · funext i
    have := hneTop i
    have := hneLevel i
    simp only [cellCentre, siteOfCoords, siteCoords, Pi.add_apply]
    have e1 : (((F.blockSide : ℤ) ^ (F.top - j) *
        ZMod.cast ((q i : ZMod (F.period F.top i)) : ZMod (F.period F.top i)) : ℤ) :
        ZMod (F.period j i)) = (((M : ℤ) * q i : ℤ) : ZMod (F.period j i)) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      rw [ZMod.coe_intCast]
      have e2 := Int.emod_add_mul_ediv (q i) (F.period F.top i : ℤ)
      refine ⟨q i / (F.period F.top i : ℤ), ?_⟩
      rw [hperLevel, hperTop i] at *
      have e6 : (F.blockSide : ℤ) ^ (F.top - j) = (M : ℤ) := by
        rw [hM]
        push_cast
        rfl
      rw [e6]
      push_cast
      linear_combination (-(M : ℤ)) * e2
    rw [e1, ← Int.cast_add]
    have e3 : (M : ℤ) * q i + r i = c i := by
      simp only [hr]
      ring
    rw [e3]
    simp only [hc, siteCoords]
    exact ZMod.intCast_zmod_cast (x i)
section Casts
variable {a b c : ℕ}
theorem intCast_cast_self (u : ZMod a) : ((u.cast : ℤ) : ZMod a) = u := by
  simp
theorem intCast_cast_add (h : a = b) (u v : ZMod a) :
    (((u + v).cast : ℤ) : ZMod b) = ((u.cast : ℤ) : ZMod b) + ((v.cast : ℤ) : ZMod b) := by
  subst h
  simp only [intCast_cast_self]
theorem intCast_cast_neg (h : a = b) (u : ZMod a) :
    (((-u).cast : ℤ) : ZMod b) = -((u.cast : ℤ) : ZMod b) := by
  subst h
  simp only [intCast_cast_self]
theorem intCast_cast_intCast (h : a = b) (z : ℤ) : (((z : ZMod a).cast : ℤ) : ZMod b) = (z : ZMod b) := by
  subst h
  simp only [intCast_cast_self]
theorem intCast_cast_roundTrip (h : a = b) (u : ZMod b) :
    (((((u.cast : ℤ) : ZMod a)).cast : ℤ) : ZMod b) = u := by
  subst h
  simp only [intCast_cast_self]
theorem cast_intCast_cast (h : a = b) (u : ZMod a) :
    ((((u.cast : ℤ) : ZMod b)).cast : ℤ) = u.cast := by
  subst h
  simp only [intCast_cast_self]
theorem intCast_cast_threeWay (h : a = b) (h' : b = c) (u : ZMod a) :
    ((((((((u.cast : ℤ) : ZMod b)).cast : ℤ) : ZMod c).cast : ℤ)) : ZMod a) = u := by
  subst h
  subst h'
  simp only [intCast_cast_self]
end Casts
section TwoFrames
variable {F F' : BlockFrame}
def transferSite (j : ℕ) (x : F.Site j) : F'.Site j := siteOfCoords j (siteCoords x)
def transferField (F F' : BlockFrame) (j : ℕ) (W : F'.GaugeField j) : F.GaugeField j :=
  fun x i => W (transferSite j x) i
variable {j : ℕ}
theorem transferSite_transferSite (hp : ∀ i, F.period j i = F'.period j i) (x : F.Site j) :
    transferSite (F' := F) j (transferSite (F' := F') j x) = x :=
  funext fun k => intCast_cast_roundTrip (hp k).symm (x k)
theorem transferSite_transferSite' (hp : ∀ i, F.period j i = F'.period j i) (x : F'.Site j) :
    transferSite (F' := F') j (transferSite (F' := F) j x) = x :=
  funext fun k => intCast_cast_roundTrip (hp k) (x k)
theorem transferSite_add (hp : ∀ i, F.period j i = F'.period j i) (x y : F.Site j) :
    transferSite (F' := F') j (x + y) = transferSite j x + transferSite j y :=
  funext fun k => intCast_cast_add (hp k) (x k) (y k)
theorem transferSite_neg (hp : ∀ i, F.period j i = F'.period j i) (x : F.Site j) :
    transferSite (F' := F') j (-x) = -transferSite j x :=
  funext fun k => intCast_cast_neg (hp k) (x k)
theorem transferSite_sub (hp : ∀ i, F.period j i = F'.period j i) (x y : F.Site j) :
    transferSite (F' := F') j (x - y) = transferSite j x - transferSite j y := by
  rw [sub_eq_add_neg, transferSite_add hp, transferSite_neg hp, sub_eq_add_neg]
theorem transferSite_siteOfCoords (hp : ∀ i, F.period j i = F'.period j i) (z : Fin 4 → ℤ) :
    transferSite (F' := F') j (siteOfCoords (F := F) j z) = siteOfCoords j z :=
  funext fun k => intCast_cast_intCast (hp k) (z k)
theorem transferSite_unitStep (hp : ∀ i, F.period j i = F'.period j i) (i : Fin 4) :
    transferSite (F' := F') j (BlockAverages.unitStep (F := F) j i) = BlockAverages.unitStep j i := by
  rw [BlockAverages.unitStep, transferSite_siteOfCoords hp, BlockAverages.unitStep]
theorem siteCoords_transferSite (hp : ∀ i, F.period j i = F'.period j i) (x : F.Site j) :
    siteCoords (transferSite (F' := F') j x) = siteCoords x :=
  funext fun k => cast_intCast_cast (hp k) (x k)
theorem linkValue_transferField (hp : ∀ i, F.period j i = F'.period j i) (W : F'.GaugeField j) (x : F.Site j)
    (st : PathStep) : linkValue (transferField F F' j W) x st = linkValue W (transferSite j x) st := by
  unfold linkValue transferField
  split_ifs
  · rfl
  · rw [transferSite_sub hp, transferSite_unitStep hp]
theorem transferSite_stepDisplacement (hp : ∀ i, F.period j i = F'.period j i) (st : PathStep) :
    transferSite (F' := F') j (stepDisplacement (F := F) j st) = stepDisplacement j st := by
  unfold stepDisplacement
  split_ifs
  · exact transferSite_unitStep hp _
  · rw [transferSite_neg hp, transferSite_unitStep hp]
theorem pathHolonomy_transferField (hp : ∀ i, F.period j i = F'.period j i) (W : F'.GaugeField j)
    (l : List PathStep) (x : F.Site j) :
    pathHolonomy (transferField F F' j W) x l = pathHolonomy W (transferSite j x) l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    simp only [pathHolonomy]
    rw [linkValue_transferField hp, ih, transferSite_add hp, transferSite_stepDisplacement hp]
theorem contourAverage_transferField (hL : F'.blockSide = F.blockSide) (hp : ∀ i, F.period j i = F'.period j i)
    (hp1 : ∀ i, F.period (j + 1) i = F'.period (j + 1) i) (W : F'.GaugeField j) (c : F.Site (j + 1) × Fin 4) :
    contourAverage (transferField F F' j W) c = contourAverage W (transferSite (j + 1) c.1, c.2) := by
  have hd : transferSite (F' := F') j (refineSite c.1) = refineSite (transferSite (j + 1) c.1) := by
    unfold refineSite
    rw [transferSite_siteOfCoords hp, siteCoords_transferSite hp1, hL]
  unfold contourAverage
  simp only [hL, pathHolonomy_transferField hp, hd]
theorem blockFit_transferField (hL : F'.blockSide = F.blockSide) (hp : ∀ i, F.period j i = F'.period j i)
    (hp1 : ∀ i, F.period (j + 1) i = F'.period (j + 1) i) (W : F'.GaugeField j) (V : F'.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) :
    blockFit (transferField F F' j W) (transferField F F' (j + 1) V) c =
      blockFit W V (transferSite (j + 1) c.1, c.2) := by
  unfold blockFit
  rw [contourAverage_transferField hL hp hp1]
  rfl
def CoversLevels (F : BlockFrame) (S : Finset F.Cell) (J : ℕ) : Prop :=
  ∀ j ≤ J, ∀ x : F.Site j, x ∈ sitesOfCells S j
theorem mem_innerBonds_of_coversLevels {S : Finset F.Cell} {J : ℕ} (h : CoversLevels F S J) {j : ℕ}
    (hj : j ≤ J) (c : F.Site j × Fin 4) : c ∈ innerBonds S j := by
  unfold innerBonds
  rw [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨h j hj _, Finset.mem_univ _⟩, h j hj _⟩
theorem sum_innerBonds_transferSite {S : Finset F.Cell} {S' : Finset F'.Cell} {J : ℕ} (h : CoversLevels F S J)
    (h' : CoversLevels F' S' J) {j : ℕ} (hj : j ≤ J) (hp : ∀ i, F.period j i = F'.period j i)
    (g : F'.Site j × Fin 4 → ℝ) :
    ∑ c ∈ innerBonds S j, g (transferSite j c.1, c.2) = ∑ c ∈ innerBonds S' j, g c := by
  refine Finset.sum_nbij' (fun c => (transferSite j c.1, c.2)) (fun c => (transferSite (F' := F) j c.1, c.2))
    (fun c _ => mem_innerBonds_of_coversLevels h' hj _) (fun c _ => mem_innerBonds_of_coversLevels h hj _)
    ?_ ?_ (fun _ _ => rfl)
  · intro c _
    exact Prod.ext (transferSite_transferSite hp c.1) rfl
  · intro c _
    exact Prod.ext (transferSite_transferSite' hp c.1) rfl
theorem mem_innerPlaquettes_iff_of_coversLevels {S : Finset F.Cell} {J : ℕ} (h : CoversLevels F S J) {j : ℕ}
    (hj : j ≤ J) (p : F.Site j × Fin 4 × Fin 4) : p ∈ innerPlaquettes S j ↔ p.2.1 < p.2.2 := by
  unfold innerPlaquettes
  rw [Finset.mem_filter]
  constructor
  · exact fun hp => hp.2.1
  · intro hlt
    refine ⟨?_, hlt, fun x _ => h j hj x⟩
    simp [h j hj p.1]
theorem minimalAction_transferField {S : Finset F.Cell} {S' : Finset F'.Cell} {a : ℝ} {J : ℕ}
    (hL : F'.blockSide = F.blockSide) (h : CoversLevels F S J) (h' : CoversLevels F' S' J)
    (hper : ∀ j ≤ J, ∀ i, F.period j i = F'.period j i) :
    ∀ j ≤ J, ∀ W : F'.GaugeField j, minimalAction a S j (transferField F F' j W) = minimalAction a S' j W := by
  intro j
  induction j with
  | zero =>
    intro hj W
    have hp := hper 0 hj
    simp only [minimalAction, BlockAverages.wilsonAction]
    refine Finset.sum_nbij' (fun p => (transferSite 0 p.1, p.2)) (fun p => (transferSite (F' := F) 0 p.1, p.2))
      ?_ ?_ ?_ ?_ ?_
    · intro p hpm
      exact (mem_innerPlaquettes_iff_of_coversLevels h' hj _).mpr
        ((mem_innerPlaquettes_iff_of_coversLevels h hj _).mp hpm)
    · intro p hpm
      exact (mem_innerPlaquettes_iff_of_coversLevels h hj _).mpr
        ((mem_innerPlaquettes_iff_of_coversLevels h' hj _).mp hpm)
    · intro p _
      exact Prod.ext (transferSite_transferSite hp p.1) rfl
    · intro p _
      exact Prod.ext (transferSite_transferSite' hp p.1) rfl
    · intro p _
      unfold plaquetteHolonomy
      simp only
      rw [pathHolonomy_transferField hp]
  | succ j ih =>
    intro hj V
    have hp := hper j (by omega)
    have hp1 := hper (j + 1) hj
    simp only [minimalAction]
    let e : F'.GaugeField j ≃ F.GaugeField j :=
      { toFun := transferField F F' j
        invFun := transferField F' F j
        left_inv := fun W => by
          funext x i
          simp only [transferField]
          rw [transferSite_transferSite' hp]
        right_inv := fun W => by
          funext x i
          simp only [transferField]
          rw [transferSite_transferSite hp] }
    refine (Equiv.iInf_congr e fun W => ?_).symm
    show minimalAction a S j (transferField F F' j W) +
        a * ∑ c ∈ innerBonds S (j + 1), blockFit (transferField F F' j W) (transferField F F' (j + 1) V) c =
      minimalAction a S' j W + a * ∑ c ∈ innerBonds S' (j + 1), blockFit W V c
    rw [ih (by omega) W]
    simp only [blockFit_transferField hL hp hp1]
    rw [sum_innerBonds_transferSite h h' hj hp1 (fun c => blockFit W V c)]
end TwoFrames
section Torus
variable {F : BlockFrame} {m j : ℕ}
def siteOfTorusSite (j : ℕ) (x : TorusSite m) : F.Site j := siteOfCoords j fun k => ((x k).cast : ℤ)
theorem toTorusSite_siteOfTorusSite (hp : ∀ i, F.period j i = m) (x : TorusSite m) :
    toTorusSite m (siteOfTorusSite (F := F) j x) = x :=
  funext fun k => intCast_cast_roundTrip (hp k) (x k)
theorem siteOfTorusSite_toTorusSite (hp : ∀ i, F.period j i = m) (y : F.Site j) :
    siteOfTorusSite j (toTorusSite m y) = y :=
  funext fun k => intCast_cast_roundTrip (hp k).symm (y k)
theorem toTorusSite_add (hp : ∀ i, F.period j i = m) (x y : F.Site j) :
    toTorusSite m (x + y) = toTorusSite m x + toTorusSite m y :=
  funext fun k => intCast_cast_add (hp k) (x k) (y k)
theorem siteOfInt_single (i : Fin 4) : (siteOfInt (Pi.single i 1) : TorusSite m) = TorusFields.unitStep m i := by
  funext k
  simp only [siteOfInt, TorusFields.unitStep, Pi.single_apply]
  split_ifs <;> simp
theorem toTorusSite_unitStep (hp : ∀ i, F.period j i = m) (i : Fin 4) :
    toTorusSite m (BlockAverages.unitStep (F := F) j i) = TorusFields.unitStep m i := by
  have h : toTorusSite m (siteOfCoords (F := F) j (Pi.single i 1)) = siteOfInt (Pi.single i 1) :=
    funext fun k => intCast_cast_intCast (hp k) _
  rw [BlockAverages.unitStep, h, siteOfInt_single]
theorem restrictToTorus_toTorusSite (hp : ∀ i, F.period j i = m) (W : F.GaugeField j) (y : F.Site j)
    (i : Fin 4) : restrictToTorus m W (toTorusSite m y) i = W y i :=
  congrFun (congrArg W (siteOfTorusSite_toTorusSite hp y)) i
theorem plaquetteHolonomy_eq_holonomy (hp : ∀ i, F.period j i = m) (W : F.GaugeField j) (y : F.Site j)
    (μ ν : Fin 4) :
    plaquetteHolonomy W (y, μ, ν) = TorusFields.holonomy (restrictToTorus m W) (toTorusSite m y) μ ν := by
  have h1 : toTorusSite m y + TorusFields.unitStep m μ = toTorusSite m (y + BlockAverages.unitStep j μ) := by
    rw [toTorusSite_add hp, toTorusSite_unitStep hp]
  have h2 : toTorusSite m y + TorusFields.unitStep m ν = toTorusSite m (y + BlockAverages.unitStep j ν) := by
    rw [toTorusSite_add hp, toTorusSite_unitStep hp]
  have h3 : y + BlockAverages.unitStep j μ + BlockAverages.unitStep j ν - BlockAverages.unitStep j μ =
      y + BlockAverages.unitStep j ν := by abel
  have h4 : y + BlockAverages.unitStep j μ + BlockAverages.unitStep j ν + -BlockAverages.unitStep j μ -
      BlockAverages.unitStep j ν = y := by abel
  simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
    if_false, TorusFields.holonomy, h1, h2, restrictToTorus_toTorusSite hp, h3, h4, mul_one, mul_assoc]
theorem isCold_restrictToTorus (hp : ∀ i, F.period j i = m) {s : ℝ} {W : F.GaugeField j}
    (h : IsSmallCurvature s W) : IsCold s (restrictToTorus m W) := by
  intro x μ ν hμν
  have h1 := h (siteOfTorusSite j x, μ, ν) hμν
  unfold plaquetteDefect at h1
  rw [plaquetteHolonomy_eq_holonomy hp, toTorusSite_siteOfTorusSite hp] at h1
  exact h1
theorem mem_finiteCells (F : BlockFrame) (hs : ∀ i, 0 < F.extent i) (z : F.Cell) : z ∈ finiteCells F := by
  have hperTop : ∀ i, F.period F.top i = F.extent i := by
    intro i
    simp [BlockFrame.period]
  have hneTop : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by rw [hperTop]; exact (hs i).ne'⟩
  have hfin : Finite F.Cell := by
    have : ∀ i, Finite (ZMod (F.period F.top i)) := fun i => by
      have := hneTop i
      exact inferInstance
    exact Pi.finite
  unfold finiteCells
  rw [dif_pos hfin]
  exact @Finset.mem_univ _ (Fintype.ofFinite _) z
theorem minimalAction_eq_actionAtLevel {a : ℝ} {L n : ℕ} [NeZero m] (hL : F.blockSide = L) (hodd : Odd L)
    (hs : ∀ i, F.extent i = n) (hn : 0 < n) (hj : j = F.depth) (hp : ∀ i, F.period j i = m) (hmn : m = n * L)
    (W : F.GaugeField j) :
    minimalAction a (finiteCells F) j W = actionAtLevel a L j Finset.univ (restrictToTorus m W) := by
  have hpos : ∀ i, 0 < F.extent i := fun i => by rw [hs]; exact hn
  have hoddF : Odd F.blockSide := by rw [hL]; exact hodd
  have hcover : CoversLevels F (finiteCells F) j := fun j' _ x =>
    mem_sitesOfCells_of_forall_mem hoddF hpos (mem_finiteCells F hpos) x
  cases j with
  | zero =>
    simp only [minimalAction, BlockAverages.wilsonAction, actionAtLevel, TorusFields.wilsonAction,
      plaquetteEnergy]
    refine Finset.sum_nbij' (fun p => (toTorusSite m p.1, p.2)) (fun p => (siteOfTorusSite 0 p.1, p.2))
      ?_ ?_ ?_ ?_ ?_
    · intro p hpm
      have h1 := (mem_innerPlaquettes_iff_of_coversLevels hcover le_rfl _).mp hpm
      simp only [plaquettesIn, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h1, fun _ _ => Finset.mem_univ _⟩
    · intro p hpm
      simp only [plaquettesIn, Finset.mem_filter] at hpm
      exact (mem_innerPlaquettes_iff_of_coversLevels hcover le_rfl _).mpr hpm.2.1
    · intro p _
      exact Prod.ext (siteOfTorusSite_toTorusSite hp p.1) rfl
    · intro p _
      exact Prod.ext (toTorusSite_siteOfTorusSite hp p.1) rfl
    · intro p _
      obtain ⟨y, μ, ν⟩ := p
      simp only
      rw [plaquetteHolonomy_eq_holonomy hp]
  | succ j =>
    have hFtop : F.top = j + 2 := by
      simp only [BlockFrame.top]
      omega
    have hLpos : 0 < L := hodd.pos
    set F' : BlockFrame := torusFrame L j m with hF'
    have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    have hper : ∀ j' ≤ j + 1, ∀ i, F.period j' i = F'.period j' i := by
      intro j' hj' i
      have e1 : j + 2 - j' = (j + 1 - j') + 1 := by omega
      simp only [BlockFrame.period, hs, hL, hFtop, hF', torusFrame, BlockFrame.top]
      rw [hmn, e1, pow_succ]
      ring
    have hpos' : ∀ i, 0 < F'.extent i := fun _ => hm0
    have hoddF' : Odd F'.blockSide := hodd
    have hcell : ∀ z : F'.Cell, z ∈ cellsOfSites F' (Finset.univ : Finset (TorusSite m)) := by
      intro z
      have hz : ∀ k, F'.period F'.top k = m := by
        intro k
        simp [hF', torusFrame, BlockFrame.period, BlockFrame.top]
      unfold cellsOfSites
      rw [Finset.mem_image]
      exact ⟨fun k => ((siteCoords z k : ℤ) : ZMod m), Finset.mem_univ _,
        funext fun k => intCast_cast_roundTrip (hz k).symm (z k)⟩
    have hcover' : CoversLevels F' (cellsOfSites F' (Finset.univ : Finset (TorusSite m))) (j + 1) :=
      fun j' _ x => mem_sitesOfCells_of_forall_mem hoddF' hpos' hcell x
    have hL' : F'.blockSide = F.blockSide := by rw [hL]; rfl
    have h := minimalAction_transferField (a := a) hL' hcover hcover' hper (j + 1) le_rfl
      (readAtLevel F' (j + 1) (restrictToTorus m W))
    have htr : transferField F F' (j + 1) (readAtLevel F' (j + 1) (restrictToTorus m W)) = W := by
      funext y i
      show W (siteOfCoords (j + 1) fun k =>
        (((((siteCoords (transferSite (F' := F') (j + 1) y) k : ℤ) : ZMod m)).cast : ℤ))) i = W y i
      congr 1
      funext k
      exact intCast_cast_threeWay (hper (j + 1) le_rfl k) ((hper (j + 1) le_rfl k).symm.trans (hp k)) (y k)
    rw [htr] at h
    exact h
end Torus
end FrameTorusAction
end YangMills.Construction
end
