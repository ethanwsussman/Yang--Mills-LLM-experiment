import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import YangMills.Construction.RunningCouplingSlope.ContoursAtTheLeastFieldHaveKernelsProof
import YangMills.Construction.ClusterExpansionOfAStep.BlocksOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.MatchingClasses
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.RunningCouplingSlope.ContourKernelsAreLocal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FlatLinearization
open BlockAverages hiding unitStep stepDisplacement
open TorusBlocks hiding blockCentreSite
open FlatPairing LatticeFractionalIntegration TorusFields TorusLumps SlopeCoefficient
variable {m : ℕ}
private theorem natAbs_le_of_mem_centredCube {L : ℕ} {h : Fin 4 → ℤ} (hh : h ∈ centredCube L) (i : Fin 4) :
    (h i).natAbs ≤ (L - 1) / 2 := by
  have h1 := Fintype.mem_piFinset.mp hh i
  rw [Finset.mem_Icc] at h1
  obtain ⟨h2, h3⟩ := h1
  omega
private theorem axisPath_length (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    (axisPath h π).length =
      (h (π 0)).natAbs + (h (π 1)).natAbs + (h (π 2)).natAbs + (h (π 3)).natAbs := by apply _root_.YangMills.Construction.LatticePaths.length_axisPath <;> assumption
private theorem bondContour_length_le {L : ℕ} (hL : 1 ≤ L) {h : Fin 4 → ℤ} (hh : h ∈ centredCube L)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) : (bondContour L h π i).length ≤ 5 * L := by
  have h0 := natAbs_le_of_mem_centredCube hh (π 0)
  have h1 := natAbs_le_of_mem_centredCube hh (π 1)
  have h2 := natAbs_le_of_mem_centredCube hh (π 2)
  have h3 := natAbs_le_of_mem_centredCube hh (π 3)
  simp only [bondContour, reversePath, List.length_append, List.length_replicate, List.length_map,
    List.length_reverse, axisPath_length]
  omega
private theorem centredCube_card {L : ℕ} (hL : Odd L) : (centredCube L).card = L ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
private theorem abs_cubeAverage_le {L : ℕ} (hL : Odd L) (S : (Fin 4 → ℤ) → Equiv.Perm (Fin 4) → ℝ) {B : ℝ}
    (hS : ∀ h ∈ centredCube L, ∀ π, |S h π| ≤ B) :
    |(1 / (24 * (L : ℝ) ^ 4)) * ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), S h π| ≤ B := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL.pos
  have h1 : |∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), S h π| ≤ 24 * (L : ℝ) ^ 4 * B := by
    calc |∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), S h π|
        ≤ ∑ h ∈ centredCube L, |∑ π : Equiv.Perm (Fin 4), S h π| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _h ∈ centredCube L, 24 * B := by
          refine Finset.sum_le_sum fun h hh => ?_
          calc |∑ π : Equiv.Perm (Fin 4), S h π|
              ≤ ∑ π : Equiv.Perm (Fin 4), |S h π| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _π : Equiv.Perm (Fin 4), B := Finset.sum_le_sum fun π _ => hS h hh π
            _ = 24 * B := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
                simp [Nat.factorial]
      _ = 24 * (L : ℝ) ^ 4 * B := by
          rw [Finset.sum_const, centredCube_card hL]
          simp only [nsmul_eq_mul]
          push_cast
          ring
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (24 * (L : ℝ) ^ 4))]
  calc 1 / (24 * (L : ℝ) ^ 4) * |∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), S h π|
      ≤ 1 / (24 * (L : ℝ) ^ 4) * (24 * (L : ℝ) ^ 4 * B) := by gcongr
    _ = B := by field_simp
private theorem cubeAverage_eq_zero {L : ℕ} (S : (Fin 4 → ℤ) → Equiv.Perm (Fin 4) → ℝ)
    (hS : ∀ h ∈ centredCube L, ∀ π, S h π = 0) :
    (1 / (24 * (L : ℝ) ^ 4)) * ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), S h π = 0 := by
  rw [Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun π _ => hS h hh π, mul_zero]
private theorem pathIntegral_eq_sum_indicator [NeZero m] (ξ : RealOneForm m) (y : TorusSite m) (l : List PathStep) :
    pathIntegral ξ y l = ∑ b, pathIntegral (indicatorForm b) y l * ξ b := by
  induction l generalizing y with
  | nil => simp [pathIntegral]
  | cons st r ih =>
    obtain ⟨i, s⟩ := st
    simp only [pathIntegral, add_mul, Finset.sum_add_distrib]
    rw [← ih]
    congr 1
    cases s <;> simp [indicatorForm]
private theorem supDist_stepEndpoint_le [NeZero m] (y : TorusSite m) (st : PathStep) :
    supDist (stepEndpoint y st) y ≤ 1 := by
  obtain ⟨i, s⟩ := st
  cases s
  · have h := supDist_add_unitStep_le (y - unitStep m i) i
    rw [sub_add_cancel] at h
    simpa [stepEndpoint] using h
  · have h := supDist_add_unitStep_le y i
    rw [supDist_comm] at h
    simpa [stepEndpoint] using h
private theorem pathIntegral_indicator_of_far [NeZero m] (b : TorusBond m) (y : TorusSite m) (l : List PathStep)
    (hl : l.length < supDist b.1 y) : pathIntegral (indicatorForm b) y l = 0 := by
  induction l generalizing y with
  | nil => rfl
  | cons st r ih =>
    simp only [List.length_cons] at hl
    have h1 : r.length < supDist b.1 (stepEndpoint y st) := by
      have h2 := supDist_triangle b.1 (stepEndpoint y st) y
      have h3 := supDist_stepEndpoint_le y st
      omega
    obtain ⟨i, s⟩ := st
    have h4 : (if s then indicatorForm b (y, i) else - indicatorForm b (y - unitStep m i, i)) = 0 := by
      cases s
      · have h5 : (y - unitStep m i, i) ≠ b := by
          rintro rfl
          have h := supDist_add_unitStep_le (y - unitStep m i) i
          rw [sub_add_cancel] at h
          simp only at hl
          omega
        simp [indicatorForm, h5]
      · have h5 : (y, i) ≠ b := by
          rintro rfl
          simp only [supDist_self] at hl
          omega
        simp [indicatorForm, h5]
    rw [pathIntegral, h4, ih _ h1, add_zero]
private theorem abs_indicatorForm_le (b c : TorusBond m) : |indicatorForm b c| ≤ 1 := by
  unfold indicatorForm
  split_ifs <;> simp
private theorem abs_pathIntegral_indicator_le (b : TorusBond m) (y : TorusSite m) (l : List PathStep) :
    |pathIntegral (indicatorForm b) y l| ≤ l.length := by
  induction l generalizing y with
  | nil => simp [pathIntegral]
  | cons st r ih =>
    obtain ⟨i, s⟩ := st
    have h1 : |(if s then indicatorForm b (y, i) else - indicatorForm b (y - unitStep m i, i))| ≤ 1 := by
      cases s
      · simpa using abs_indicatorForm_le b _
      · simpa using abs_indicatorForm_le b _
    rw [pathIntegral]
    refine (abs_add_le _ _).trans ?_
    have h2 := ih (stepEndpoint y (i, s))
    simp only [List.length_cons]
    push_cast
    linarith
private theorem natAbs_le_offsetNorm (h : Fin 4 → ℤ) (i : Fin 4) : (h i).natAbs ≤ offsetNorm h := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
private theorem offsetNorm_le_of_forall {h : Fin 4 → ℤ} {N : ℕ} (hN : ∀ i, (h i).natAbs ≤ N) :
    offsetNorm h ≤ N := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.offsetNorm_le <;> assumption
private theorem natAbs_stepDisplacement_le (st : PathStep) (i : Fin 4) : (stepDisplacement st i).natAbs ≤ 1 := by
  obtain ⟨k, s⟩ := st
  by_cases hk : i = k
  · subst hk
    cases s <;> simp [stepDisplacement, basisVector]
  · cases s <;> simp [stepDisplacement, basisVector, hk]
private theorem natAbs_basisVector_le (k i : Fin 4) : (basisVector k i).natAbs ≤ 1 := by apply _root_.YangMills.DeltaSharedProofs.p500493 <;> assumption
private theorem offsetNorm_le_sub_stepDisplacement (a : Fin 4 → ℤ) (st : PathStep) :
    offsetNorm a ≤ offsetNorm (a - stepDisplacement st) + 1 := by
  refine offsetNorm_le_of_forall fun i => ?_
  have h1 := natAbs_le_offsetNorm (a - stepDisplacement st) i
  have h2 := natAbs_stepDisplacement_le st i
  simp only [Pi.sub_apply] at h1
  omega
private def latticeIndicator (b : LatticeBond) : LatticeOneForm := fun b' => if b' = b then 1 else 0
private theorem abs_latticeIndicator_le (b c : LatticeBond) : |latticeIndicator b c| ≤ 1 := by
  unfold latticeIndicator
  split_ifs <;> simp
private theorem latticeLineSum_indicator_of_far (b : LatticeBond) (z : Fin 4 → ℤ) (l : List PathStep)
    (hl : l.length < offsetNorm (b.1 - z)) : latticeLineSum (latticeIndicator b) z l = 0 := by
  induction l generalizing z with
  | nil => rfl
  | cons st r ih =>
    simp only [List.length_cons] at hl
    have h1 : r.length < offsetNorm (b.1 - (z + stepDisplacement st)) := by
      have h2 := offsetNorm_le_sub_stepDisplacement (b.1 - z) st
      rw [sub_sub] at h2
      omega
    obtain ⟨i, s⟩ := st
    have h4 : (if s then latticeIndicator b (z, i) else - latticeIndicator b (z - basisVector i, i)) = 0 := by
      cases s
      · have h5 : (z - basisVector i, i) ≠ b := by
          rintro rfl
          have h6 : offsetNorm (z - basisVector i - z) ≤ 1 := by
            refine offsetNorm_le_of_forall fun k => ?_
            have := natAbs_basisVector_le i k
            simpa using this
          simp only at hl
          omega
        simp [latticeIndicator, h5]
      · have h5 : (z, i) ≠ b := by
          rintro rfl
          have h6 : offsetNorm (z - z) = 0 := by
            simp [offsetNorm]
          simp only at hl
          omega
        simp [latticeIndicator, h5]
    rw [latticeLineSum, h4, ih _ h1, add_zero]
private theorem abs_latticeLineSum_indicator_le (b : LatticeBond) (z : Fin 4 → ℤ) (l : List PathStep) :
    |latticeLineSum (latticeIndicator b) z l| ≤ l.length := by
  induction l generalizing z with
  | nil => simp [latticeLineSum]
  | cons st r ih =>
    obtain ⟨i, s⟩ := st
    have h1 : |(if s then latticeIndicator b (z, i) else - latticeIndicator b (z - basisVector i, i))| ≤ 1 := by
      cases s
      · simpa using abs_latticeIndicator_le b _
      · simpa using abs_latticeIndicator_le b _
    rw [latticeLineSum]
    refine (abs_add_le _ _).trans ?_
    have h2 := ih (z + stepDisplacement (i, s))
    simp only [List.length_cons]
    push_cast
    linarith
private theorem latticeLineSum_congr_near {ξ ξ' : LatticeOneForm} (z : Fin 4 → ℤ) (l : List PathStep)
    (h : ∀ b' : LatticeBond, offsetNorm (b'.1 - z) ≤ l.length → ξ b' = ξ' b') :
    latticeLineSum ξ z l = latticeLineSum ξ' z l := by
  induction l generalizing z with
  | nil => rfl
  | cons st r ih =>
    simp only [List.length_cons] at h
    have h1 : latticeLineSum ξ (z + stepDisplacement st) r = latticeLineSum ξ' (z + stepDisplacement st) r := by
      refine ih _ fun b' hb' => h b' ?_
      have h2 := offsetNorm_le_sub_stepDisplacement (b'.1 - z) st
      rw [sub_sub] at h2
      omega
    obtain ⟨i, s⟩ := st
    rw [latticeLineSum, latticeLineSum, h1]
    congr 1
    cases s
    · have h2 : ξ (z - basisVector i, i) = ξ' (z - basisVector i, i) := by
        refine h _ ?_
        have h6 : offsetNorm (z - basisVector i - z) ≤ 1 := by
          refine offsetNorm_le_of_forall fun k => ?_
          have := natAbs_basisVector_le i k
          simpa using this
        simp only
        omega
      simp [h2]
    · have h2 : ξ (z, i) = ξ' (z, i) := by
        refine h _ ?_
        have h6 : offsetNorm (z - z) = 0 := by
          simp [offsetNorm]
        simp only
        omega
      simp [h2]
private theorem siteOfInt_add_stepDisplacement (z : Fin 4 → ℤ) (st : PathStep) :
    (siteOfInt (z + stepDisplacement st) : TorusSite m) = stepEndpoint (siteOfInt z) st := by
  obtain ⟨i, s⟩ := st
  funext k
  by_cases hk : k = i
  · subst hk
    cases s <;> simp [siteOfInt, stepDisplacement, basisVector, stepEndpoint, unitStep, sub_eq_add_neg]
  · cases s <;> simp [siteOfInt, stepDisplacement, basisVector, stepEndpoint, unitStep, hk]
private theorem siteOfInt_sub_basisVector (z : Fin 4 → ℤ) (i : Fin 4) :
    (siteOfInt (z - basisVector i) : TorusSite m) = siteOfInt z - unitStep m i := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [siteOfInt, basisVector, unitStep]
  · simp [siteOfInt, basisVector, unitStep, hk]
abbrev _root_.YangMills.DeltaSharedProofs.p500696 := @siteOfInt_sub_basisVector
private theorem pathIntegral_siteOfInt (ξ : RealOneForm m) (z : Fin 4 → ℤ) (l : List PathStep) :
    pathIntegral ξ (siteOfInt z) l = latticeLineSum (fun b' => ξ (siteOfInt b'.1, b'.2)) z l := by
  induction l generalizing z with
  | nil => rfl
  | cons st r ih =>
    rw [pathIntegral, latticeLineSum, ← siteOfInt_add_stepDisplacement, ih]
    obtain ⟨i, s⟩ := st
    cases s
    · simp [siteOfInt_sub_basisVector]
    · simp
private theorem blockCentreSite_siteOfInt (L n : ℕ) [NeZero n] (z : Fin 4 → ℤ) :
    blockCentreSite L (siteOfInt z : TorusSite n) = siteOfInt (blockCentreOnLattice L z) := by
  funext i
  show ((L * ((z i : ZMod n)).val : ℕ) : ZMod (n * L)) = (((L : ℤ) * z i : ℤ) : ZMod (n * L))
  have h1 : (((z i : ZMod n)).val : ℤ) = z i % (n : ℤ) := ZMod.val_intCast (z i)
  have h2 : ((L * ((z i : ZMod n)).val : ℕ) : ZMod (n * L)) =
      (((L : ℤ) * (((z i : ZMod n)).val : ℤ) : ℤ) : ZMod (n * L)) := by
    push_cast
    rfl
  rw [h2, h1, ZMod.intCast_eq_intCast_iff_dvd_sub, Int.emod_def]
  refine ⟨z i / (n : ℤ), ?_⟩
  push_cast
  ring
private theorem coarseSite_siteOfInt (L n : ℕ) [NeZero n] [NeZero L] (z : Fin 4 → ℤ) :
    coarseSite L (siteOfInt z : TorusSite (n * L)) = siteOfInt (latticeBlockOf L z) := by
  funext k
  exact TorusBlocks.parentBlock_siteOfInt z k
private theorem abs_lt_of_offsetNorm_lt {v : Fin 4 → ℤ} {N : ℕ} (h : offsetNorm v < N) (i : Fin 4) :
    |v i| < N := by
  have h1 := natAbs_le_offsetNorm v i
  rw [Int.abs_eq_natAbs]
  omega
private theorem contourWeight_bondFrom_zero_eventually (L : ℕ) (hL : 1 ≤ L) (c b : LatticeBond) :
    ∀ᶠ n : ℕ in Filter.atTop,
      contourWeight L (bondFrom 0 c : TorusBond n) (bondFrom 0 b : TorusBond (n * L)) =
        latticeContourWeight L c b := by
  filter_upwards [Filter.eventually_gt_atTop (5 * L + offsetNorm (b.1 - blockCentreOnLattice L c.1) + 1)] with n hn
  have : NeZero n := ⟨by omega⟩
  have : NeZero L := ⟨by omega⟩
  have hnL : n ≤ n * L := Nat.le_mul_of_pos_right n (by omega)
  have e0 : ((bondFrom 0 c : TorusBond n)).1 = siteOfInt c.1 := zero_add _
  have hc : blockCentreSite L ((bondFrom 0 c : TorusBond n)).1 = siteOfInt (blockCentreOnLattice L c.1) := by
    rw [e0, blockCentreSite_siteOfInt]
  show contourAverage L (indicatorForm (bondFrom 0 b : TorusBond (n * L))) (bondFrom 0 c) =
    latticeContourAverage L (latticeIndicator b) c
  unfold contourAverage latticeContourAverage
  rw [hc]
  congr 1
  refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => ?_
  rw [pathIntegral_siteOfInt]
  have hlen := bondContour_length_le hL hh π c.2
  refine latticeLineSum_congr_near _ _ fun b' hb' => ?_
  have hb'2 : offsetNorm (b'.1 - blockCentreOnLattice L c.1) ≤ 5 * L :=
    hb'.trans (by simpa [bondFrom] using hlen)
  show indicatorForm (bondFrom 0 b : TorusBond (n * L)) (siteOfInt b'.1, b'.2) = latticeIndicator b b'
  have hiff : ((siteOfInt b'.1, b'.2) : TorusBond (n * L)) = bondFrom 0 b ↔ b' = b := by
    constructor
    · intro he
      have h1 : (siteOfInt b'.1 : TorusSite (n * L)) = siteOfInt b.1 := by
        have := congrArg Prod.fst he
        simpa [bondFrom] using this
      have h2 : b'.2 = b.2 := (Prod.ext_iff.mp he).2
      have h3 : b'.1 = b.1 := by
        refine eq_of_siteOfInt_eq h1 fun i => ?_
        have h4 := natAbs_le_offsetNorm (b'.1 - blockCentreOnLattice L c.1) i
        have h5 := natAbs_le_offsetNorm (b.1 - blockCentreOnLattice L c.1) i
        simp only [Pi.sub_apply] at h4 h5
        have h6 : ((n * L : ℕ) : ℤ) ≥ n := by exact_mod_cast hnL
        have h7 : (n : ℤ) > 5 * L + offsetNorm (b.1 - blockCentreOnLattice L c.1) + 1 := by exact_mod_cast hn
        have h8 : ((offsetNorm (b'.1 - blockCentreOnLattice L c.1) : ℕ) : ℤ) ≤ 5 * L := by exact_mod_cast hb'2
        rw [Int.abs_eq_natAbs]
        omega
      exact Prod.ext h3 h2
    · rintro rfl
      simp [bondFrom]
  simp only [indicatorForm, latticeIndicator, hiff]
private theorem isBlockTreeBond_bondFrom_zero_eventually (L : ℕ) (hL : 1 ≤ L) (b : LatticeBond) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (IsBlockTreeBond L (bondFrom 0 b : TorusBond (n * L)) ↔ IsLatticeTreeBond L b) := by
  filter_upwards [Filter.eventually_gt_atTop
    (offsetNorm (latticeBlockOf L (b.1 + basisVector b.2) - latticeBlockOf L b.1) +
      offsetNorm (offsetInBlock L b.1) + 1)] with n hn
  have : NeZero n := ⟨by omega⟩
  have : NeZero L := ⟨by omega⟩
  have : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have hnL : n ≤ n * L := Nat.le_mul_of_pos_right n (by omega)
  have e0 : ((bondFrom 0 b : TorusBond (n * L))).1 = siteOfInt b.1 := zero_add _
  have e1 : ((bondFrom 0 b : TorusBond (n * L))).2 = b.2 := rfl
  have hcross : CrossesBlockBoundary L (bondFrom 0 b : TorusBond (n * L)) ↔
      latticeBlockOf L (b.1 + basisVector b.2) ≠ latticeBlockOf L b.1 := by
    have e2 : ((siteOfInt b.1 : TorusSite (n * L)) + unitStep (n * L) b.2) =
        siteOfInt (b.1 + basisVector b.2) := by
      have := siteOfInt_add_stepDisplacement (m := n * L) b.1 (b.2, true)
      simpa [stepDisplacement, stepEndpoint] using this.symm
    unfold CrossesBlockBoundary
    rw [e0, e1, e2, coarseSite_siteOfInt, coarseSite_siteOfInt, not_iff_not]
    constructor
    · intro he
      refine eq_of_siteOfInt_eq he fun i => ?_
      have h1 := abs_lt_of_offsetNorm_lt (N := n)
        (v := latticeBlockOf L (b.1 + basisVector b.2) - latticeBlockOf L b.1) (by omega) i
      simpa using h1
    · intro he
      rw [he]
  have hoff : ∀ l, offsetFromCentre L (bondFrom 0 b : TorusBond (n * L)).1 l = 0 ↔
      offsetInBlock L b.1 l = 0 := by
    intro l
    have e3 : (siteOfInt b.1 : TorusSite (n * L)) -
        blockCentreSite L (coarseSite L (siteOfInt b.1 : TorusSite (n * L))) =
        siteOfInt (offsetInBlock L b.1) := by
      rw [coarseSite_siteOfInt, blockCentreSite_siteOfInt]
      funext k
      simp [siteOfInt, offsetInBlock]
    unfold offsetFromCentre
    rw [e0, e3, ZMod.valMinAbs_eq_zero]
    show ((offsetInBlock L b.1 l : ℤ) : ZMod (n * L)) = 0 ↔ _
    constructor
    · intro he
      have h1 := abs_lt_of_offsetNorm_lt (N := n) (v := offsetInBlock L b.1) (by omega) l
      refine int_eq_of_zmod_cast_eq (n := n * L) (by simpa using he) ?_
      simp only [sub_zero]
      omega
    · intro he
      simp [he]
  unfold IsBlockTreeBond IsLatticeTreeBond
  rw [hcross, not_not, e1]
  simp only [hoff]
theorem contourWeightLocality : RunningCouplingSlope.ContourWeightLocality := by
  intro L hL
  have hodd : Odd L := hL.1
  have hone : 1 ≤ L := hodd.pos
  have hC : (0 : ℝ) < 5 * L := by
    have : (0 : ℝ) < L := by exact_mod_cast hone
    linarith
  refine ⟨5 * L, hC, ?_, ?_, contourWeight_bondFrom_zero_eventually L hone,
    isBlockTreeBond_bondFrom_zero_eventually L hone⟩
  · refine Filter.Eventually.of_forall fun n => ?_
    intro _ _
    refine ⟨fun ξ c => ?_, fun c b => ⟨?_, fun hfar => ?_⟩⟩
    · unfold contourWeight contourAverage
      simp_rw [mul_assoc, ← Finset.mul_sum]
      congr 1
      simp_rw [Finset.sum_mul]
      symm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro π _
      exact (pathIntegral_eq_sum_indicator ξ _ _).symm
    · refine abs_cubeAverage_le hodd _ fun h hh π => ?_
      refine (abs_pathIntegral_indicator_le b _ _).trans ?_
      exact_mod_cast bondContour_length_le hone hh π c.2
    · refine cubeAverage_eq_zero _ fun h hh π => ?_
      refine pathIntegral_indicator_of_far b _ _ ?_
      have := bondContour_length_le hone hh π c.2
      omega
  · intro c b
    refine ⟨?_, fun hfar => ?_⟩
    · refine abs_cubeAverage_le hodd _ fun h hh π => ?_
      refine (abs_latticeLineSum_indicator_le b _ _).trans ?_
      exact_mod_cast bondContour_length_le hone hh π c.2
    · refine cubeAverage_eq_zero _ fun h hh π => ?_
      refine latticeLineSum_indicator_of_far b _ _ ?_
      have := bondContour_length_le hone hh π c.2
      omega
end YangMills.Construction.FlatLinearization
end
