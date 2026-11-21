import YangMills.Construction.ResponseInTheExpansion.TheStepsAddUpToTheMaxwellCovarianceProof
import YangMills.Construction.LawByMomentsOfTheFlow.CanonicalGaussianInTheTreeGauge
import YangMills.Construction.LawByMomentsOfTheFlow.ChainHasACanonicalGaussian
import YangMills.Construction.LawByMomentsOfTheFlow.TheChainHasItsGaussianProof
import YangMills.Construction.RunningCouplingSlope.FloorOfFormsOffTheTreesProof
import YangMills.Construction.RunningCouplingSlope.LatticeFormsHaveATreeGaugeProof
import YangMills.Construction.SummableBoundsOfTheFlow.ContoursByOffsets
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
namespace TreeGaugeConstruction
open TorusFields TorusBlocks TorusLumps StepCosts TopLevelSites TorusContours TorusPaths WeightedResponses
  LatticeFractionalIntegration FlatPairing
open BlockAverages hiding unitStep stepDisplacement
section Lines
private def axisLineSum (ξ : (Fin 4 → ℤ) × Fin 4 → ℝ) (x : Fin 4 → ℤ) (μ : Fin 4) : ℤ → ℝ
  | Int.ofNat k => ∑ i ∈ Finset.range k, ξ (x + (i : ℤ) • basisVector μ, μ)
  | Int.negSucc k => - ∑ i ∈ Finset.range (k + 1), ξ (x + (-((i : ℤ) + 1)) • basisVector μ, μ)
private theorem axisLineSum_zero (ξ : (Fin 4 → ℤ) × Fin 4 → ℝ) (x : Fin 4 → ℤ) (μ : Fin 4) :
    axisLineSum ξ x μ 0 = 0 := by
  show axisLineSum ξ x μ (Int.ofNat 0) = 0
  simp [axisLineSum]
private theorem axisLineSum_succ_sub (ξ : (Fin 4 → ℤ) × Fin 4 → ℝ) (x : Fin 4 → ℤ) (μ : Fin 4) (k : ℤ) :
    axisLineSum ξ x μ (k + 1) - axisLineSum ξ x μ k = ξ (x + k • basisVector μ, μ) := by
  cases k with
  | ofNat n =>
    have h : (Int.ofNat n + 1 : ℤ) = Int.ofNat (n + 1) := rfl
    rw [h]
    simp only [axisLineSum, Finset.sum_range_succ]
    simp
  | negSucc n =>
    cases n with
    | zero =>
      have h : (Int.negSucc 0 + 1 : ℤ) = Int.ofNat 0 := rfl
      rw [h]
      simp [axisLineSum]
    | succ m =>
      have h : (Int.negSucc (m + 1) + 1 : ℤ) = Int.negSucc m := rfl
      have h2 : (Int.negSucc (m + 1) : ℤ) = -(((m + 1 : ℕ) : ℤ) + 1) := rfl
      rw [h]
      simp only [axisLineSum]
      rw [Finset.sum_range_succ _ (m + 1), h2]
      ring_nf
private def lowerCoords (o : Fin 4 → ℤ) (i : Fin 4) : Fin 4 → ℤ := fun j => if j < i then o j else 0
private def axialTreeSum (ξ : (Fin 4 → ℤ) × Fin 4 → ℝ) (o : Fin 4 → ℤ) : ℝ :=
  ∑ i, axisLineSum ξ (lowerCoords o i) i (o i)
private theorem axialTreeSum_zero (ξ : (Fin 4 → ℤ) × Fin 4 → ℝ) : axialTreeSum ξ 0 = 0 := by
  unfold axialTreeSum
  refine Finset.sum_eq_zero fun i _ => ?_
  exact axisLineSum_zero ξ _ i
private theorem axialTreeSum_add_basisVector_sub (ξ : (Fin 4 → ℤ) × Fin 4 → ℝ) (o : Fin 4 → ℤ) (μ : Fin 4)
    (ho : ∀ l, μ < l → o l = 0) :
    axialTreeSum ξ (o + basisVector μ) - axialTreeSum ξ o = ξ (o, μ) := by
  have hi : ∀ i j : Fin 4, i ≠ j → (basisVector i) j = 0 := by
    intro i j hij
    simp [basisVector, hij.symm]
  have hup : ∀ i, i ≤ μ → lowerCoords (o + basisVector μ) i = lowerCoords o i := by
    intro i hiμ
    funext j
    by_cases hj : j < i
    · have : μ ≠ j := (lt_of_lt_of_le hj hiμ).ne'
      simp [lowerCoords, hj, hi μ j this]
    · simp [lowerCoords, hj]
  unfold axialTreeSum
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single μ]
  · rw [hup μ le_rfl]
    have hone : (o + basisVector μ) μ = o μ + 1 := by
      simp [basisVector]
    rw [hone, axisLineSum_succ_sub]
    congr 2
    funext j
    rcases lt_trichotomy j μ with h | h | h
    · simp [lowerCoords, h, hi μ j h.ne']
    · subst h
      simp [lowerCoords, basisVector]
    · simp [lowerCoords, not_lt.2 h.le, hi μ j h.ne, ho j h]
  · intro i _ hne
    rcases lt_or_gt_of_ne hne with h | h
    · rw [hup i h.le]
      have : (o + basisVector μ) i = o i := by
        simp [hi μ i h.ne']
      rw [this, sub_self]
    · have h1 : o i = 0 := ho i h
      have h2 : (o + basisVector μ) i = 0 := by
        simp [hi μ i h.ne, h1]
      rw [h1, h2, axisLineSum_zero, axisLineSum_zero, sub_self]
  · intro h
    exact absurd (Finset.mem_univ μ) h
end Lines
section Torus
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem siteOfInt_basisVector {m : ℕ} (i : Fin 4) :
    (siteOfInt (basisVector i) : TorusSite m) = unitStep m i := by apply _root_.YangMills.SharedProofs.p5838 <;> assumption
private def blockOffsetVector (L : ℕ) {n : ℕ} (x : TorusSite (n * L)) : Fin 4 → ℤ :=
  fun l => LumpContours.offsetFromCentre L ((x l).cast : ℤ)
private theorem blockOffsetVector_centre_add (hL : Odd L) (Y : TorusSite n) (e : Fin 4 → ℤ)
    (he : ∀ i, |e i| ≤ ((L : ℤ) - 1) / 2) :
    blockOffsetVector L (blockCentreSite L Y + siteOfInt e) = e ∧
      parentBlock L (blockCentreSite L Y + siteOfInt e) = Y := by
  have hLpos : 0 < L := hL.pos
  constructor
  · funext l
    unfold blockOffsetVector
    have hw : (blockCentreSite L Y + siteOfInt e : TorusSite (n * L)) l =
        (((L : ℤ) * ((Y l).cast : ℤ) + e l : ℤ) : ZMod (n * L)) :=
      (blockCentreSite_apply_add Y l (e l)).symm
    rw [hw]
    have hc : ((((((L : ℤ) * ((Y l).cast : ℤ) + e l : ℤ) : ZMod (n * L))).cast : ℤ) : ZMod (n * L)) =
        (((L : ℤ) * ((Y l).cast : ℤ) + e l : ℤ) : ZMod (n * L)) := ZMod.intCast_zmod_cast _
    obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hc
    have e1 : ((((L : ℤ) * ((Y l).cast : ℤ) + e l : ℤ) : ZMod (n * L)).cast : ℤ) =
        ((L : ℤ) * ((Y l).cast : ℤ) - ((n * L : ℕ) : ℤ) * q) + e l := by linarith
    rw [e1]
    refine offsetFromCentre_add_of_dvd hLpos hL _ _ ?_ (he l)
    refine ⟨((Y l).cast : ℤ) - (n : ℤ) * q, ?_⟩
    push_cast
    ring
  · rw [parentBlock_blockCentreSite_add]
    have h0 : (fun i => (e i + ((L : ℤ) - 1) / 2) / (L : ℤ)) = 0 := by
      funext i
      obtain ⟨k, hk⟩ := hL
      have hh : ((L : ℤ) - 1) / 2 = k := by
        subst hk
        push_cast
        omega
      have h1 := he i
      rw [hh, abs_le] at h1
      rw [hh]
      apply Int.ediv_eq_zero_of_lt
      · omega
      · subst hk
        push_cast
        omega
    rw [h0]
    have : (siteOfInt 0 : TorusSite n) = 0 := by
      funext i
      simp [siteOfInt]
    rw [this, add_zero]
private theorem eq_blockCentreSite_add_offset (hL : Odd L) (x : TorusSite (n * L)) :
    x = blockCentreSite L (parentBlock L x) + siteOfInt (blockOffsetVector L x) := by
  obtain ⟨o, ho, hx⟩ := exists_eq_blockCentreSite_add hL x
  have hcube : ∀ i, |o i| ≤ ((L : ℤ) - 1) / 2 := by
    intro i
    obtain ⟨h1, h2⟩ := ho i
    obtain ⟨k, hk⟩ := hL
    have hh : ((L : ℤ) - 1) / 2 = k := by
      subst hk
      push_cast
      omega
    rw [hh] at h1 h2 ⊢
    rw [abs_le]
    subst hk
    push_cast at h2
    constructor <;> omega
  have h3 := (blockOffsetVector_centre_add hL (parentBlock L x) o hcube).1
  rw [← hx] at h3
  rw [h3]
  exact hx
private theorem exists_potential_of_axial (hL : Odd L) (h2 : 2 ≤ n) (A : TorusBond (n * L) → ℝ)
    (ψ : TorusSite n → ℝ) :
    ∃ ψ' : TorusSite (n * L) → ℝ, (∀ Y, ψ' (blockCentreSite L Y) = ψ Y) ∧
      ∀ b ∉ chartBonds L n, latticeGradient ψ' b = A b := by
  classical
  have hLpos : 0 < L := hL.pos
  let ξ : TorusSite n → (Fin 4 → ℤ) × Fin 4 → ℝ := fun Y b => A (blockCentreSite L Y + siteOfInt b.1, b.2)
  refine ⟨fun x => ψ (parentBlock L x) + axialTreeSum (ξ (parentBlock L x)) (blockOffsetVector L x),
    fun Y => ?_, ?_⟩
  · have hz : ∀ i, |(0 : Fin 4 → ℤ) i| ≤ ((L : ℤ) - 1) / 2 := by
      intro i
      simp only [Pi.zero_apply, abs_zero]
      obtain ⟨k, hk⟩ := hL
      subst hk
      push_cast
      omega
    obtain ⟨e1, e2⟩ := blockOffsetVector_centre_add hL Y 0 hz
    have e3 : (siteOfInt 0 : TorusSite (n * L)) = 0 := by
      funext i
      simp [siteOfInt]
    rw [e3, add_zero] at e1 e2
    show ψ (parentBlock L (blockCentreSite L Y)) +
      axialTreeSum (ξ (parentBlock L (blockCentreSite L Y))) (blockOffsetVector L (blockCentreSite L Y)) = _
    rw [e1, e2, axialTreeSum_zero, add_zero]
  · rintro ⟨x, μ⟩ hb
    have hn : NeZero (n * (stepBlockFrame L n).blockSide) := inferInstanceAs (NeZero (n * L))
    have htree : IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 x, μ) := by
      by_contra hnot
      apply hb
      unfold chartBonds
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hnot⟩
    have h3 := (isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame L n) (n := n) (fun _ => rfl) hL h2 x μ).1 htree
    obtain ⟨h4, h5⟩ := h3
    have h4' : blockOffsetVector L x μ ≠ halfWidth L := h4
    have h5' : ∀ l, μ < l → blockOffsetVector L x l = 0 := h5
    have hsp : ∀ i, |blockOffsetVector L x i| ≤ ((L : ℤ) - 1) / 2 :=
      fun i => (offsetFromCentre_spec hLpos hL _).2
    have hnext : ∀ i, |(blockOffsetVector L x + basisVector μ) i| ≤ ((L : ℤ) - 1) / 2 := by
      intro i
      by_cases hi : i = μ
      · subst hi
        have h6 := hsp i
        rw [abs_le] at h6 ⊢
        have h7 : (basisVector i) i = 1 := by simp [basisVector]
        rw [Pi.add_apply, h7]
        have h8 : blockOffsetVector L x i ≠ ((L : ℤ) - 1) / 2 := h4'
        omega
      · have h7 : (basisVector μ) i = 0 := by simp [basisVector, hi]
        rw [Pi.add_apply, h7, add_zero]
        exact hsp i
    have hxe : x + unitStep (n * L) μ =
        blockCentreSite L (parentBlock L x) + siteOfInt (blockOffsetVector L x + basisVector μ) := by
      rw [siteOfInt_add, siteOfInt_basisVector, ← add_assoc, ← eq_blockCentreSite_add_offset hL x]
    obtain ⟨e1, e2⟩ := blockOffsetVector_centre_add hL (parentBlock L x) (blockOffsetVector L x + basisVector μ) hnext
    rw [← hxe] at e1 e2
    show (ψ (parentBlock L (x + unitStep (n * L) μ)) +
      axialTreeSum (ξ (parentBlock L (x + unitStep (n * L) μ))) (blockOffsetVector L (x + unitStep (n * L) μ))) -
      (ψ (parentBlock L x) + axialTreeSum (ξ (parentBlock L x)) (blockOffsetVector L x)) = A (x, μ)
    rw [e1, e2]
    have h6 := axialTreeSum_add_basisVector_sub (ξ (parentBlock L x)) (blockOffsetVector L x) μ h5'
    have h7 : ξ (parentBlock L x) (blockOffsetVector L x, μ) = A (x, μ) := by
      show A (blockCentreSite L (parentBlock L x) + siteOfInt (blockOffsetVector L x), μ) = _
      rw [← eq_blockCentreSite_add_offset hL x]
    rw [h7] at h6
    linarith
abbrev _root_.YangMills.SharedProofs.p73176 := @exists_potential_of_axial
private theorem sumAlongWord_gradient_pathToWord {m : ℕ} [NeZero m] (f : TorusSite m → ℝ) (y : TorusSite m)
    (l : List PathStep) :
    sumAlongWord (latticeGradient f) (pathToWord y l) = f (y + siteOfInt (l.map stepDisplacement).sum) - f y := by
  induction l generalizing y with
  | nil =>
    have : (siteOfInt 0 : TorusSite m) = 0 := by
      funext i
      simp [siteOfInt]
    simp [pathToWord, sumAlongWord, this]
  | cons st r ih =>
    obtain ⟨i, s⟩ := st
    have hw : ∀ (e : TorusBond m × Bool) (w : BondWord m), sumAlongWord (latticeGradient f) (e :: w) =
        (if e.2 then latticeGradient f e.1 else - latticeGradient f e.1) + sumAlongWord (latticeGradient f) w :=
      fun _ _ => by
        simp [sumAlongWord]
    cases s with
    | true =>
      simp only [pathToWord, if_true, hw, ih, List.map_cons, List.sum_cons]
      have e1 : y + siteOfInt (stepDisplacement (i, true) + (r.map stepDisplacement).sum) =
          y + unitStep m i + siteOfInt (r.map stepDisplacement).sum := by
        rw [siteOfInt_add, ← add_assoc]
        congr 2
        simp [stepDisplacement, siteOfInt_basisVector]
      rw [e1]
      simp [latticeGradient]
    | false =>
      simp only [pathToWord, Bool.false_eq_true, if_false, hw, ih, List.map_cons, List.sum_cons]
      have e1 : y + siteOfInt (stepDisplacement (i, false) + (r.map stepDisplacement).sum) =
          y - unitStep m i + siteOfInt (r.map stepDisplacement).sum := by
        rw [siteOfInt_add, ← add_assoc, sub_eq_add_neg]
        congr 2
        rw [← siteOfInt_basisVector]
        funext k
        simp [stepDisplacement, siteOfInt]
      rw [e1]
      simp [latticeGradient]
private theorem sum_reversePath (l : List PathStep) :
    ((reversePath l).map stepDisplacement).sum = - (l.map stepDisplacement).sum := by apply _root_.YangMills.SharedProofs.p25873 <;> assumption
private theorem sum_bondContour (L : ℕ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    ((bondContour L h π i).map stepDisplacement).sum = fun k => (L : ℤ) * basisVector i k := by
  unfold bondContour
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append, sum_reversePath,
    List.map_replicate, List.sum_replicate]
  funext k
  simp [stepDisplacement]
private theorem contourAverage_gradient (hL : Odd L) (f : TorusSite (n * L) → ℝ) (c : TorusBond n) :
    contourAverage L (latticeGradient f) c =
      f (blockCentreSite L (c.1 + unitStep n c.2)) - f (blockCentreSite L c.1) := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have he : ∀ e ∈ contourIndex L, sumAlongWord (latticeGradient f) (contourWord L c.1 c.2 e) =
      f (blockCentreSite L (c.1 + unitStep n c.2)) - f (blockCentreSite L c.1) := by
    intro e _
    unfold contourWord
    rw [sumAlongWord_gradient_pathToWord, sum_bondContour, ← siteOfInt_basisVector,
      ContourMeans.blockCentreSite_add]
  unfold contourAverage
  rw [Finset.sum_congr rfl he, Finset.sum_const, contourIndex, Finset.card_product,
    LatticePaths.card_centredCube hL, Finset.card_univ, Fintype.card_perm, _root_.YangMills.Construction.TorusContours.contourWeight]
  simp [Nat.factorial]
  field_simp
abbrev _root_.YangMills.DeltaSharedProofs.p501243 := @contourAverage_gradient
abbrev _root_.YangMills.SharedProofs.p24879 := @contourAverage_gradient
end Torus
section Chains
variable {L : ℕ} [NeZero L]
@[reducible] private def levelBondFintype (L : ℕ) [NeZero L] : (s n : ℕ) → [NeZero n] → Fintype (LevelBond L s n)
  | 0, n, _ => inferInstanceAs (Fintype (TorusBond n))
  | s + 1, n, _ => by
    letI := levelBondFintype L s (n * L)
    exact inferInstanceAs (Fintype (LevelBond L s (n * L) ⊕ TorusBond n))
private instance (s n : ℕ) [NeZero n] : Fintype (LevelBond L s n) := levelBondFintype L s n
private theorem sumAlongWord_add {m : ℕ} (A B : TorusBond m → ℝ) (w : BondWord m) :
    sumAlongWord (A + B) w = sumAlongWord A w + sumAlongWord B w := by apply _root_.YangMills.SharedProofs.p21609 <;> assumption
variable {n : ℕ}
private theorem contourAverage_add [NeZero n] (A B : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    contourAverage L (A + B) c = contourAverage L A c + contourAverage L B c := by
  simp only [contourAverage, sumAlongWord_add, Finset.sum_add_distrib, mul_add]
private theorem contourAverage_smul [NeZero n] (r : ℝ) (A : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    contourAverage L (r • A) c = r * contourAverage L A c := by apply _root_.YangMills.SharedProofs.p14469 <;> assumption
private theorem chainTop_add : ∀ (s n : ℕ) (X Y : LevelChain L s n),
    chainTop s n (X + Y) = chainTop s n X + chainTop s n Y
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem chainTop_smul : ∀ (s n : ℕ) (r : ℝ) (X : LevelChain L s n),
    chainTop s n (r • X) = r • chainTop s n X
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem chainLower_add {s : ℕ} (X Y : LevelChain L (s + 1) n) :
    chainLower (X + Y) = chainLower X + chainLower Y := rfl
private theorem chainLower_smul {s : ℕ} (r : ℝ) (X : LevelChain L (s + 1) n) :
    chainLower (r • X) = r • chainLower X := rfl
private theorem chainDefect_add [NeZero n] {s : ℕ} (X Y : LevelChain L (s + 1) n) (e : Fin 3) (c : TorusBond n) :
    chainDefect (X + Y) e c = chainDefect X e c + chainDefect Y e c := by
  simp only [chainDefect, chainTop_add, chainLower_add, Pi.add_apply]
  rw [show (chainTop s (n * L) (chainLower X) e + chainTop s (n * L) (chainLower Y) e) =
    (chainTop s (n * L) (chainLower X) + chainTop s (n * L) (chainLower Y)) e from rfl,
    Pi.add_apply, contourAverage_add]
  ring
abbrev _root_.YangMills.SharedProofs.p32985 := @chainDefect_add
private theorem chainDefect_smul [NeZero n] {s : ℕ} (r : ℝ) (X : LevelChain L (s + 1) n) (e : Fin 3)
    (c : TorusBond n) :
    chainDefect (r • X) e c = r * chainDefect X e c := by
  simp only [chainDefect, chainTop_smul, chainLower_smul, Pi.smul_apply, smul_eq_mul]
  rw [contourAverage_smul]
  ring
abbrev _root_.YangMills.SharedProofs.p30900 := @chainDefect_smul
private theorem curl_add {m : ℕ} (A B : TorusBond m → ℝ) (p : TorusPlaquette m) :
    curl (A + B) p = curl A p + curl B p := by apply _root_.YangMills.SharedProofs.p35838 <;> assumption
private theorem curl_smul {m : ℕ} (r : ℝ) (A : TorusBond m → ℝ) (p : TorusPlaquette m) :
    curl (r • A) p = r * curl A p := by apply _root_.YangMills.SharedProofs.p39240 <;> assumption
private def IsFlatLevelChain : (s n : ℕ) → [NeZero n] → LevelChain L s n → Prop
  | 0, _, _, X => ∀ (e : Fin 3) (p : TorusPlaquette _), curl (chainTop 0 _ X e) p = 0
  | s + 1, n, _, X => IsFlatLevelChain s (n * L) (chainLower X) ∧ ∀ (e : Fin 3) (c : TorusBond n), chainDefect X e c = 0
private theorem isFlatLevelChain_add : ∀ (s n : ℕ) [NeZero n] (X Y : LevelChain L s n),
    IsFlatLevelChain s n X → IsFlatLevelChain s n Y → IsFlatLevelChain s n (X + Y)
  | 0, n, _, X, Y, h1, h2 => fun e p => by
    rw [chainTop_add]
    show curl (chainTop 0 n X e + chainTop 0 n Y e) p = 0
    rw [curl_add, h1 e p, h2 e p, add_zero]
  | s + 1, n, _, X, Y, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨isFlatLevelChain_add s (n * L) _ _ h1 h3, fun e c => by
      rw [chainDefect_add, h2 e c, h4 e c, add_zero]⟩
private theorem isFlatLevelChain_smul : ∀ (s n : ℕ) [NeZero n] (r : ℝ) (X : LevelChain L s n),
    IsFlatLevelChain s n X → IsFlatLevelChain s n (r • X)
  | 0, n, _, r, X, h => fun e p => by
    rw [chainTop_smul]
    show curl (r • chainTop 0 n X e) p = 0
    rw [curl_smul, h e p, mul_zero]
  | s + 1, n, _, r, X, ⟨h1, h2⟩ => ⟨isFlatLevelChain_smul s (n * L) r _ h1, fun e c => by
      rw [chainDefect_smul, h2 e c, mul_zero]⟩
private theorem isFlatLevelChain_zero : ∀ (s n : ℕ) [NeZero n], IsFlatLevelChain s n (0 : LevelChain L s n)
  | 0, n, _ => fun e p => by
    show curl (0 : TorusBond n → ℝ) p = 0
    simp [curl]
  | s + 1, n, _ => ⟨isFlatLevelChain_zero s (n * L), fun e c => by
      have h := chainDefect_smul (L := L) (s := s) (n := n) (0 : ℝ) 0 e c
      rwa [zero_smul, zero_mul] at h⟩
private theorem levelEnergy_eq_zero_of_flat (a : ℝ) : ∀ (s n : ℕ) [NeZero n] (X : LevelChain L s n),
    IsFlatLevelChain s n X → levelEnergy a s n X = 0
  | 0, n, _, X, h => by
    simp only [levelEnergy]
    refine Finset.sum_eq_zero fun p _ => ?_
    have : curlNorm (chainTop 0 n X) p = 0 := by
      unfold curlNorm
      rw [Finset.sum_eq_zero fun e _ => by rw [h e p]; simp]
      simp
    rw [this]
    simp
  | s + 1, n, _, X, ⟨h1, h2⟩ => by
    simp only [levelEnergy]
    rw [levelEnergy_eq_zero_of_flat a s (n * L) _ h1, zero_add]
    simp [h2]
private def flatSubmodule (s n : ℕ) [NeZero n] : Submodule ℝ (LevelChain L s n) where
  carrier := {X | IsFlatLevelChain s n X}
  add_mem' := fun {X Y} hX hY => isFlatLevelChain_add s n X Y hX hY
  zero_mem' := isFlatLevelChain_zero s n
  smul_mem' := fun r X hX => isFlatLevelChain_smul s n r X hX
private theorem isTreeGauge_add : ∀ (s n : ℕ) [NeZero n] (X Y : LevelChain L s n), IsTreeGauge s n X →
    IsTreeGauge s n Y → IsTreeGauge s n (X + Y)
  | 0, _, _, _, _, _, _ => trivial
  | s + 1, n, _, X, Y, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨fun e b hb => by
      rw [chainLower_add, chainTop_add, Pi.add_apply, Pi.add_apply, h1 e b hb, h3 e b hb, add_zero],
    isTreeGauge_add s (n * L) _ _ h2 h4⟩
private theorem isTreeGauge_smul : ∀ (s n : ℕ) [NeZero n] (r : ℝ) (X : LevelChain L s n), IsTreeGauge s n X →
    IsTreeGauge s n (r • X)
  | 0, _, _, _, _, _ => trivial
  | s + 1, n, _, r, X, ⟨h1, h2⟩ => ⟨fun e b hb => by
      rw [chainLower_smul, chainTop_smul, Pi.smul_apply, Pi.smul_apply, h1 e b hb, smul_zero],
    isTreeGauge_smul s (n * L) r _ h2⟩
private theorem isTreeGauge_zero : ∀ (s n : ℕ) [NeZero n], IsTreeGauge s n (0 : LevelChain L s n)
  | 0, _, _ => trivial
  | s + 1, n, _ => ⟨fun e b _ => by
      have h := chainTop_smul s (n * L) 0 (chainLower (0 : LevelChain L (s + 1) n))
      rw [zero_smul] at h
      have h' : chainLower (0 : LevelChain L (s + 1) n) = 0 := rfl
      rw [h', h]
      simp, isTreeGauge_zero s (n * L)⟩
private def treeGaugeSubmodule (s n : ℕ) [NeZero n] : Submodule ℝ (LevelChain L s n) where
  carrier := {X | IsTreeGauge s n X}
  add_mem' := fun {X Y} hX hY => isTreeGauge_add s n X Y hX hY
  zero_mem' := isTreeGauge_zero s n
  smul_mem' := fun r X hX => isTreeGauge_smul s n r X hX
private def consTop {s n : ℕ} (B : LevelChain L s (n * L)) (A : ColourForm n) : LevelChain L (s + 1) n := fun e =>
  (Sum.elim (B e) (A e) : LevelBond L s (n * L) ⊕ TorusBond n → ℝ)
private theorem curl_latticeGradient {m : ℕ} (f : TorusSite m → ℝ) (p : TorusPlaquette m) :
    curl (latticeGradient f) p = 0 := by apply _root_.YangMills.DeltaSharedProofs.p500719 <;> assumption
private theorem exists_flat_gauge (hL : Odd L) : ∀ (s n : ℕ) [NeZero n], 2 ≤ n → ∀ (X : LevelChain L s n)
    (ψ : Fin 3 → TorusSite n → ℝ), ∃ k : LevelChain L s n, IsFlatLevelChain s n k ∧
      chainTop s n k = (fun e => latticeGradient (ψ e)) ∧ IsTreeGauge s n (X - k)
  | 0, n, _, _, _, ψ => ⟨fun e => latticeGradient (ψ e), fun e p => curl_latticeGradient (ψ e) p, rfl, trivial⟩
  | s + 1, n, _, h2, X, ψ => by
    choose ψ' hc ht using fun e : Fin 3 =>
      exists_potential_of_axial hL h2 (chainTop s (n * L) (chainLower X) e) (ψ e)
    obtain ⟨k, hk, htop, htree⟩ := exists_flat_gauge hL s (n * L)
      (h2.trans (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero (NeZero.ne L)))) (chainLower X) ψ'
    refine ⟨consTop k fun e => latticeGradient (ψ e), ⟨hk, fun e c => ?_⟩, rfl, ⟨fun e b hb => ?_, htree⟩⟩
    · show latticeGradient (ψ e) c - contourAverage L (chainTop s (n * L) k e) c = 0
      rw [htop]
      show latticeGradient (ψ e) c - contourAverage L (latticeGradient (ψ' e)) c = 0
      rw [contourAverage_gradient hL, hc, hc]
      simp [latticeGradient]
    · show chainTop s (n * L) (chainLower X - k) e b = 0
      have e1 : chainLower X - k = chainLower X + (-1 : ℝ) • k := by
        rw [neg_one_smul, ← sub_eq_add_neg]
      rw [e1, chainTop_add, chainTop_smul, htop]
      show chainTop s (n * L) (chainLower X) e b + (-1 : ℝ) * latticeGradient (ψ' e) b = 0
      rw [ht e b hb]
      ring
end Chains
end TreeGaugeConstruction
open TreeGaugeConstruction TorusFields WeightedResponses
theorem canonicalGaussianTreeGauge_of_exists (hC : canonicalGaussianExistsStatement) :
    canonicalGaussianTreeGaugeStatement := by
  classical
  intro L _ a hL ha s n _ h2
  obtain ⟨μ₀, hμ₀⟩ := hC L a ha s n
  have := hμ₀.isProbabilityMeasure
  set K := flatSubmodule (L := L) s n with hK
  set T := treeGaugeSubmodule (L := L) s n with hT
  have hsurj : LinearMap.range (K.mkQ ∘ₗ T.subtype) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro q
    obtain ⟨X, rfl⟩ := K.mkQ_surjective q
    obtain ⟨k, hk, -, ht⟩ := exists_flat_gauge hL s n h2 X fun _ _ => 0
    refine ⟨⟨X - k, ht⟩, ?_⟩
    show K.mkQ (X - k) = K.mkQ X
    rw [map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero K).2 hk, sub_zero]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective _ hsurj
  let R : LevelChain L s n →ₗ[ℝ] LevelChain L s n := T.subtype ∘ₗ g ∘ₗ K.mkQ
  have hRT : ∀ x, IsTreeGauge s n (R x) := fun x => (g (K.mkQ x)).2
  have hRK : ∀ x, IsFlatLevelChain s n (R x - x) := by
    intro x
    have h1 : K.mkQ (R x) = K.mkQ x := LinearMap.congr_fun hg (K.mkQ x)
    have h3 : K.mkQ (R x - x) = 0 := by rw [map_sub, h1, sub_self]
    exact (Submodule.Quotient.mk_eq_zero K).1 h3
  have hRm : Measurable R := (LinearMap.continuous_of_finiteDimensional R).measurable
  refine ⟨μ₀.map R, ⟨Measure.isProbabilityMeasure_map hRm.aemeasurable, fun f hf => ?_⟩, ?_⟩
  · have hfm : Measurable f := (LinearMap.continuous_of_finiteDimensional f).measurable
    rw [Measure.map_map hfm hRm]
    have e : (⇑f ∘ ⇑R) = ⇑f := by
      funext x
      have h1 := hf _ (levelEnergy_eq_zero_of_flat a s n _ (hRK x))
      rw [map_sub, sub_eq_zero] at h1
      exact h1
    rw [e]
    exact hμ₀.map_eq f hf
  · have hset : MeasurableSet ((T : Submodule ℝ (LevelChain L s n)) : Set (LevelChain L s n)) :=
      (Submodule.closed_of_finiteDimensional T).measurableSet
    exact (ae_map_iff hRm.aemeasurable hset).2 (Filter.Eventually.of_forall hRT)
end YangMills.Construction.MomentLaw
end
