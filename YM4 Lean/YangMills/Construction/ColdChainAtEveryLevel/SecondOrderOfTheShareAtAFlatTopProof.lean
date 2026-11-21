import YangMills.Construction.ColdChainAtEveryLevel.LocalFormOfTheLinesProof
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.ResponsesNearAFlatTopProof
import YangMills.Construction.ColdChainAtEveryLevel.DifferencesAreNearlyFlat
import YangMills.Construction.ColdChainAtEveryLevel.EveryFormSplitsAlongTheSlice
import YangMills.Construction.ColdChainAtEveryLevel.ReferenceFormAtAFlatTopProof
import YangMills.Construction.ColdChainAtEveryLevel.SecondOrderOfAShareAtItsResponse
import YangMills.Construction.ColdChainAtEveryLevel.SecondOrderOfTheShareAtAFlatTop
import YangMills.Construction.ColdChainAtEveryLevel.TopAverageNearACell
import YangMills.Construction.ColdChainAtEveryLevel.WeightedEstimateOnTheSlice
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.QuadraticResponseAtFlat
open BlockLines LatticePaths
section Scalars
section Ramp
def cutoffRamp (b₁ b₂ t : ℝ) : ℝ := min 1 (max 0 ((b₂ - t) / (b₂ - b₁)))
theorem cutoffRamp_nonneg (b₁ b₂ t : ℝ) : 0 ≤ cutoffRamp b₁ b₂ t := le_min zero_le_one (le_max_left _ _)
theorem cutoffRamp_le_one (b₁ b₂ t : ℝ) : cutoffRamp b₁ b₂ t ≤ 1 := min_le_left _ _
theorem cutoffRamp_eq_one_of_le {b₁ b₂ t : ℝ} (h : b₁ < b₂) (ht : t ≤ b₁) : cutoffRamp b₁ b₂ t = 1 := by
  unfold cutoffRamp
  refine min_eq_left (le_max_of_le_right ?_)
  rw [le_div_iff₀ (by linarith)]
  linarith
theorem cutoffRamp_eq_zero_of_ge {b₁ b₂ t : ℝ} (h : b₁ < b₂) (ht : b₂ ≤ t) : cutoffRamp b₁ b₂ t = 0 := by
  unfold cutoffRamp
  have : (b₂ - t) / (b₂ - b₁) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  rw [max_eq_left this]
  simp
theorem abs_cutoffRamp_sub_le {b₁ b₂ : ℝ} (h : b₁ < b₂) (t t' : ℝ) :
    |cutoffRamp b₁ b₂ t - cutoffRamp b₁ b₂ t'| ≤ |t - t'| / (b₂ - b₁) := by
  have hp : 0 < b₂ - b₁ := by linarith
  unfold cutoffRamp
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le (by positivity) ?_
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le (by positivity) ?_
  rw [← sub_div, abs_div, abs_of_pos hp]
  have e : b₂ - t - (b₂ - t') = -(t - t') := by ring
  rw [e, abs_neg]
end Ramp
section LatticePoints
def supNorm (w : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun i => (w i).natAbs
theorem natAbs_le_supNorm (w : Fin 4 → ℤ) (i : Fin 4) : (w i).natAbs ≤ supNorm w := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
theorem abs_le_supNorm (w : Fin 4 → ℤ) (i : Fin 4) : |((w i : ℤ) : ℝ)| ≤ (supNorm w : ℝ) := by apply _root_.YangMills.Construction.BlockAverages.abs_coord_le_supNorm <;> assumption
theorem supNorm_add_single_le (w : Fin 4 → ℤ) (i : Fin 4) : supNorm (w + Pi.single i 1) ≤ supNorm w + 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearUniformTop.offsetSupNorm_add_single_le <;> assumption
theorem supNorm_le_add_single (w : Fin 4 → ℤ) (i : Fin 4) : supNorm w ≤ supNorm (w + Pi.single i 1) + 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearUniformTop.offsetSupNorm_le_add_single <;> assumption
def curvatureL1 (A : Fin 4 → Fin 4 → imaginaryQuaternions) : ℝ := ∑ ν, ∑ μ, ‖A ν μ‖
theorem curvatureL1_nonneg (A : Fin 4 → Fin 4 → imaginaryQuaternions) : 0 ≤ curvatureL1 A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
def gradedPotential (κ : ℝ) (A : Fin 4 → Fin 4 → imaginaryQuaternions) (w : Fin 4 → ℤ) (μ : Fin 4) :
    imaginaryQuaternions :=
  κ • ∑ ν, ((w ν : ℤ) : ℝ) • A ν μ
theorem norm_gradedPotential_le (κ : ℝ) (A : Fin 4 → Fin 4 → imaginaryQuaternions) (w : Fin 4 → ℤ) (μ : Fin 4) :
    ‖gradedPotential κ A w μ‖ ≤ |κ| * (supNorm w * curvatureL1 A) := by
  unfold gradedPotential
  rw [norm_smul, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  unfold curvatureL1
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ν _ => ?_
  rw [norm_smul, Real.norm_eq_abs]
  have h2 : ‖A ν μ‖ ≤ ∑ μ', ‖A ν μ'‖ :=
    Finset.single_le_sum (f := fun μ' => ‖A ν μ'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
  exact mul_le_mul (abs_le_supNorm w ν) h2 (norm_nonneg _) (by positivity)
theorem gradedPotential_add_single (κ : ℝ) (A : Fin 4 → Fin 4 → imaginaryQuaternions) (w : Fin 4 → ℤ)
    (i μ : Fin 4) :
    gradedPotential κ A (w + Pi.single i 1) μ = gradedPotential κ A w μ + κ • A i μ := by
  unfold gradedPotential
  rw [← smul_add]
  congr 1
  have e : ∀ ν, (((w + Pi.single i 1 : Fin 4 → ℤ) ν : ℤ) : ℝ) • A ν μ =
      ((w ν : ℤ) : ℝ) • A ν μ + (if ν = i then A ν μ else 0) := by
    intro ν
    by_cases h : ν = i
    · subst h
      simp [add_smul]
    · simp [h]
  simp only [e, Finset.sum_add_distrib]
  simp
theorem gradedPotential_curl (κ : ℝ) (A : Fin 4 → Fin 4 → imaginaryQuaternions) (hA : ∀ μ ν, A μ ν = - A ν μ)
    (w : Fin 4 → ℤ) (μ ν : Fin 4) :
    gradedPotential κ A w μ + gradedPotential κ A (w + Pi.single μ 1) ν -
        gradedPotential κ A (w + Pi.single ν 1) μ - gradedPotential κ A w ν =
      (2 * κ) • A μ ν := by
  rw [gradedPotential_add_single, gradedPotential_add_single, hA ν μ, two_mul, add_smul]
  simp only [smul_neg]
  abel
end LatticePoints
end Scalars
section Coordinates
variable {F : BlockFrame}
def intCoords {j : ℕ} (x : F.Site j) : Fin 4 → ℤ := fun i => (x i).valMinAbs
def ReadsBack (F : BlockFrame) (j ρ : ℕ) : Prop := ∀ i, F.period j i = 0 ∨ 2 * (ρ : ℤ) < F.period j i
theorem ReadsBack.mono {j ρ ρ' : ℕ} (h : ReadsBack F j ρ') (hρ : ρ ≤ ρ') : ReadsBack F j ρ := by
  intro i
  rcases h i with h1 | h1
  · exact Or.inl h1
  · right
    have : (ρ : ℤ) ≤ ρ' := by exact_mod_cast hρ
    linarith
theorem siteOfCoords_intCoords {j : ℕ} (x : F.Site j) : siteOfCoords j (intCoords x) = x := by
  funext i
  simp [siteOfCoords, intCoords, ZMod.coe_valMinAbs]
theorem intCoords_siteOfCoords {j ρ : ℕ} (hR : ReadsBack F j ρ) (w : Fin 4 → ℤ) (hw : supNorm w ≤ ρ) :
    intCoords (siteOfCoords j w : F.Site j) = w := by
  funext i
  refine valMinAbs_intCast_of_small ?_
  rcases hR i with h | h
  · exact Or.inl h
  · right
    have h1 : |w i| ≤ ρ := by
      have h2 := natAbs_le_supNorm w i
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h2.trans hw
    linarith
theorem supNorm_intCoords_add_le {j : ℕ} (x : F.Site j) (e : F.Site j)
    (he : ∀ i, ((e i).valMinAbs).natAbs ≤ 1) :
    supNorm (intCoords (x + e)) ≤ supNorm (intCoords x) + 1 := by
  refine Finset.sup_le fun k _ => ?_
  have h1 : ((x k + e k).valMinAbs).natAbs ≤ ((x k).valMinAbs).natAbs + ((e k).valMinAbs).natAbs :=
    (ZMod.natAbs_valMinAbs_add_le _ _).trans (Int.natAbs_add_le _ _)
  have h2 := natAbs_le_supNorm (intCoords x) k
  have h3 := he k
  simp only [intCoords] at h2 ⊢
  show (((x + e) k).valMinAbs).natAbs ≤ _
  simp only [Pi.add_apply]
  omega
theorem natAbs_valMinAbs_unitStep_le {j : ℕ} (hR : ReadsBack F j 1) (i k : Fin 4) :
    (((unitStep j i : F.Site j) k).valMinAbs).natAbs ≤ 1 := by
  have e : (unitStep j i : F.Site j) = siteOfCoords j (Pi.single i 1) := rfl
  have hs : supNorm (Pi.single i 1 : Fin 4 → ℤ) ≤ 1 := by
    refine Finset.sup_le fun l _ => ?_
    by_cases hl : l = i
    · subst hl
      simp
    · simp [hl]
  have := congrFun (intCoords_siteOfCoords (F := F) hR _ hs) k
  simp only [intCoords] at this
  rw [e, this]
  exact (natAbs_le_supNorm _ k).trans hs
theorem natAbs_valMinAbs_neg_unitStep_le {j : ℕ} (hR : ReadsBack F j 1) (i k : Fin 4) :
    (((-unitStep j i : F.Site j) k).valMinAbs).natAbs ≤ 1 := by
  show (((-(unitStep j i : F.Site j) k)).valMinAbs).natAbs ≤ 1
  rw [ZMod.natAbs_valMinAbs_neg]
  exact natAbs_valMinAbs_unitStep_le hR i k
theorem supNorm_intCoords_add_unitStep {j : ℕ} (hR : ReadsBack F j 1) (x : F.Site j) (i : Fin 4) :
    supNorm (intCoords (x + unitStep j i)) ≤ supNorm (intCoords x) + 1 :=
  supNorm_intCoords_add_le _ _ (natAbs_valMinAbs_unitStep_le hR i)
theorem supNorm_intCoords_sub_unitStep {j : ℕ} (hR : ReadsBack F j 1) (x : F.Site j) (i : Fin 4) :
    supNorm (intCoords (x - unitStep j i)) ≤ supNorm (intCoords x) + 1 := by
  rw [sub_eq_add_neg]
  exact supNorm_intCoords_add_le _ _ (natAbs_valMinAbs_neg_unitStep_le hR i)
theorem supNorm_intCoords_le_add_unitStep {j : ℕ} (hR : ReadsBack F j 1) (x : F.Site j) (i : Fin 4) :
    supNorm (intCoords x) ≤ supNorm (intCoords (x + unitStep j i)) + 1 := by
  have := supNorm_intCoords_sub_unitStep hR (x + unitStep j i) i
  simpa using this
theorem pathHolonomy_eq_one {j ρ : ℕ} (hR : ReadsBack F j 1) {X : F.GaugeField j}
    (h : ∀ x i, supNorm (intCoords x) ≤ ρ → X x i = 1) (x : F.Site j) (l : List PathStep)
    (hl : supNorm (intCoords x) + l.length ≤ ρ) : pathHolonomy X x l = 1 := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    obtain ⟨i, b⟩ := st
    simp only [List.length_cons] at hl
    have hstep : supNorm (intCoords (x + stepDisplacement j (i, b))) ≤ supNorm (intCoords x) + 1 := by
      unfold stepDisplacement
      cases b
      · simp only [Bool.false_eq_true, if_false]
        have := supNorm_intCoords_sub_unitStep hR x i
        rwa [sub_eq_add_neg] at this
      · simpa using supNorm_intCoords_add_unitStep hR x i
    have hv : linkValue X x (i, b) = 1 := by
      unfold linkValue
      cases b
      · simp only [Bool.false_eq_true, if_false]
        rw [h _ i (by have := supNorm_intCoords_sub_unitStep hR x i; omega)]
        simp
      · simp only [if_true]
        exact h x i (by omega)
    simp only [pathHolonomy, hv, one_mul]
    exact ih _ (by omega)
theorem abs_ediv_le_of_abs_le {w m M r : ℤ} (hM : 0 < M) (hm0 : 0 ≤ m) (hmM : m < M)
    (hw : |w| ≤ (r - 1) * M) :
    |(w + m) / M| ≤ r := by
  set q := (w + m) / M with hq
  have h1 : q * M ≤ w + m := Int.ediv_mul_le (w + m) hM.ne'
  have h2 : w + m < (q + 1) * M := Int.lt_ediv_add_one_mul_self (w + m) hM
  obtain ⟨w1, w2⟩ := abs_le.1 hw
  rw [abs_le]
  constructor
  · by_contra hc
    have hc' : q + 1 ≤ -r := by omega
    have : (q + 1) * M ≤ -r * M := mul_le_mul_of_nonneg_right hc' hM.le
    nlinarith
  · by_contra hc
    have hc' : r + 1 ≤ q := by omega
    have : (r + 1) * M ≤ q * M := mul_le_mul_of_nonneg_right hc' hM.le
    nlinarith
theorem enclosingCell_mem_of_coords {j r : ℕ} (hL : Odd F.blockSide) (hj : j ≤ F.top) {S : Finset F.Cell}
    (hbox : ∀ h, WithinRadius r h → siteOfCoords F.top h ∈ S) (w : Fin 4 → ℤ)
    (hw : ∀ i, |w i| ≤ ((r : ℤ) - 1) * (F.blockSide : ℤ) ^ (F.top - j)) :
    enclosingCell (siteOfCoords j w : F.Site j) ∈ S := by
  rw [LumpContours.BlockLevels.enclosingCell_siteOfCoords hj hL.pos]
  refine hbox _ fun i => ?_
  have hLz : (0 : ℤ) < F.blockSide := by exact_mod_cast hL.pos
  have hM : (0 : ℤ) < (F.blockSide : ℤ) ^ (F.top - j) := by positivity
  have hodd : Odd ((F.blockSide : ℤ) ^ (F.top - j)) := by
    have : Odd (F.blockSide : ℤ) := by exact_mod_cast hL
    exact this.pow
  obtain ⟨k, hk⟩ := hodd
  refine abs_ediv_le_of_abs_le hM ?_ ?_ (hw i)
  · rw [hk]
    omega
  · rw [hk]
    omega
theorem referenceFieldChain_eq_one (hRef : flatTopReferenceStatement) (hL : Odd F.blockSide)
    (hamb : IsAdmissibleAmbient F) {j r ρ : ℕ}
    (hj : j ≤ F.top) (hR : ReadsBack F j ρ) (hρ : 1 ≤ ρ) {S : Finset F.Cell}
    (hbox : ∀ h, WithinRadius r h → siteOfCoords F.top h ∈ S)
    (hsize : ((ρ : ℤ) + 1) ≤ ((r : ℤ) - 1) * (F.blockSide : ℤ) ^ (F.top - j))
    (x : F.Site j) (i : Fin 4) (hx : supNorm (intCoords x) ≤ ρ) :
    referenceFieldChain S flatTopField j x i = 1 := by
  have hR1 : ReadsBack F j 1 := hR.mono hρ
  have key : ∀ y : F.Site j, supNorm (intCoords y) ≤ ρ + 1 → enclosingCell y ∈ S := by
    intro y hy
    have := enclosingCell_mem_of_coords (j := j) hL hj hbox (intCoords y) (fun k => by
      have h1 := natAbs_le_supNorm (intCoords y) k
      linarith)
    rwa [siteOfCoords_intCoords] at this
  exact hRef F S j x i hL hamb hj (key x (by omega))
    (key _ (by have := supNorm_intCoords_add_unitStep hR1 x i; omega))
end Coordinates
section Averages
variable {F : BlockFrame}
theorem adjointAction_one_apply (w : ℍ[ℝ]) : _root_.YangMills.Construction.BlockAverages.adjointAction (1 : UnitQuaternion) w = w := by
  simp [_root_.YangMills.Construction.BlockAverages.adjointAction]
theorem eq_zero_of_eq_neg {W : Type*} [AddCommGroup W] [Module ℝ W] {x : W} (h : x = -x) : x = 0 := by
  have h2 : (2 : ℝ) • x = 0 := by
    rw [two_smul]
    nth_rw 1 [h]
    simp
  rcases smul_eq_zero.1 h2 with h3 | h3
  · norm_num at h3
  · exact h3
theorem diag_eq_zero_of_antisymm (A : Fin 4 → Fin 4 → imaginaryQuaternions) (hA : ∀ μ ν, A μ ν = - A ν μ)
    (μ : Fin 4) : A μ μ = 0 :=
  eq_zero_of_eq_neg (hA μ μ)
theorem sum_centredCube_gradedPotential (κ : ℝ) (A : Fin 4 → Fin 4 → imaginaryQuaternions) (M : ℕ) (μ : Fin 4) :
    ∑ h ∈ centredCube M, gradedPotential κ A h μ = 0 := by
  have hneg : ∀ h, gradedPotential κ A (-h) μ = - gradedPotential κ A h μ := by
    intro h
    unfold gradedPotential
    have e : ∑ ν, (((-h) ν : ℤ) : ℝ) • A ν μ = -∑ ν, ((h ν : ℤ) : ℝ) • A ν μ := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Pi.neg_apply]
      push_cast
      module
    rw [e, smul_neg]
  have hs : ∑ h ∈ centredCube M, gradedPotential κ A h μ = ∑ h ∈ centredCube M, gradedPotential κ A (-h) μ := by
    refine Finset.sum_nbij' (fun h => -h) (fun h => -h) ?_ ?_ ?_ ?_ ?_
    · intro h hh
      have := (mem_centredCube_iff M h).1 hh
      refine (mem_centredCube_iff M _).2 fun i => ?_
      have h1 := this i
      simp only [Pi.neg_apply]
      constructor <;> omega
    · intro h hh
      have := (mem_centredCube_iff M h).1 hh
      refine (mem_centredCube_iff M _).2 fun i => ?_
      have h1 := this i
      simp only [Pi.neg_apply]
      constructor <;> omega
    · intro h _
      simp
    · intro h _
      simp
    · intro h _
      simp
  simp only [hneg, Finset.sum_neg_distrib] at hs
  exact eq_zero_of_eq_neg hs
def blockLinePoint (L : ℕ) (w h : Fin 4 → ℤ) (μ : Fin 4) (r : ℕ) : Fin 4 → ℤ :=
  fun i => (L : ℤ) * w i + h i + (r : ℤ) * (Pi.single μ 1 : Fin 4 → ℤ) i
theorem gradedPotential_blockLinePoint (κ : ℝ) (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (hA : ∀ μ ν, A μ ν = - A ν μ) (L : ℕ)
    (w h : Fin 4 → ℤ) (μ : Fin 4) (r : ℕ) :
    gradedPotential κ A (blockLinePoint L w h μ r) μ = (L : ℝ) • gradedPotential κ A w μ + gradedPotential κ A h μ := by
  unfold gradedPotential blockLinePoint
  rw [smul_comm, ← smul_add]
  congr 1
  have e : ∀ ν, (((L : ℤ) * w ν + h ν + (r : ℤ) * (Pi.single μ 1 : Fin 4 → ℤ) ν : ℤ) : ℝ) • A ν μ =
      (L : ℝ) • (((w ν : ℤ) : ℝ) • A ν μ) + ((h ν : ℤ) : ℝ) • A ν μ := by
    intro ν
    by_cases hν : ν = μ
    · subst hν
      rw [diag_eq_zero_of_antisymm A hA]
      simp
    · have : (Pi.single μ 1 : Fin 4 → ℤ) ν = 0 := by simp [hν]
      rw [this]
      push_cast
      rw [mul_zero, add_zero, add_smul, mul_smul]
  simp only [e, Finset.sum_add_distrib, Finset.smul_sum]
theorem sum_gradedPotential_blockLinePoint (κ : ℝ) (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (hA : ∀ μ ν, A μ ν = - A ν μ) {L : ℕ} (hL : Odd L)
    (w : Fin 4 → ℤ) (μ : Fin 4) :
    ∑ h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range L,
        gradedPotential κ A (blockLinePoint L w h μ r) μ =
      (24 * (L : ℝ) ^ 6) • gradedPotential κ A w μ := by
  simp only [gradedPotential_blockLinePoint κ A hA]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, Finset.card_range]
  have hs := sum_centredCube_gradedPotential κ A L μ
  have e : ∀ x : Fin 4 → ℤ, Nat.factorial 4 • L • ((L : ℝ) • gradedPotential κ A w μ + gradedPotential κ A x μ) =
      (24 * (L : ℝ) ^ 2) • gradedPotential κ A w μ + (24 * (L : ℝ)) • gradedPotential κ A x μ := by
    intro x
    have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, hf]
    module
  simp only [e, Finset.sum_add_distrib, ← Finset.smul_sum, hs, smul_zero, add_zero, Finset.sum_const,
    card_centredCube hL]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  push_cast
  ring
section Transport
variable {R : F.FieldChain} {u : F.Site 0 → Fin 4 → imaginaryQuaternions}
theorem parallelAverage_eq_of_terms {j : ℕ} (Rj : F.GaugeField j) (f : F.Site j → Fin 4 → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) (g : (Fin 4 → ℤ) → ℕ → imaginaryQuaternions)
    (hterm : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4), ∀ r ∈ Finset.range F.blockSide,
      _root_.YangMills.Construction.BlockAverages.adjointAction (pathHolonomy Rj (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
        (f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2) = (g h r : ℍ[ℝ])) :
    parallelAverage Rj f c = (((1 / (24 * (F.blockSide : ℝ) ^ 4)) •
      ∑ h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide, g h r :
        imaginaryQuaternions) : ℍ[ℝ]) := by
  unfold parallelAverage
  rw [Submodule.coe_smul]
  congr 1
  simp only [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun r hr => ?_
  exact hterm h hh π r hr
theorem linearPart_eq_zero_of_vanishing (hL : Odd F.blockSide) (B : Finset F.Cell)
    (hz : ∀ b ∈ innerBonds B 0, u b.1 b.2 = 0) (j : ℕ)
    (hj : j ≤ F.top) : ∀ c ∈ innerBonds B j, linearPart R (baseOnlyChart u) j c.1 c.2 = 0 := by
  induction j with
  | zero =>
    intro c hc
    simp [linearPart, baseOnlyChart, hz c hc]
  | succ j ih =>
    intro c hc
    have hj' : j < F.top := by omega
    have ht : parallelAverage (R j) (linearPart R (baseOnlyChart u) j) c = 0 := by
      unfold parallelAverage
      refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun π _ =>
        Finset.sum_eq_zero fun r hr => ?_)
      have hb := lineBond_mem_innerBonds hj' hL c hc h hh r (Finset.mem_range.1 hr)
      have := ih (by omega) _ hb
      simp only [lineBond] at this
      simp only [this]
      simp [_root_.YangMills.Construction.BlockAverages.adjointAction]
    have hcc : linearPart R (baseOnlyChart u) (j + 1) c.1 c.2 =
        parallelAverage (R j) (linearPart R (baseOnlyChart u) j) (c.1, c.2) +
          if j + 1 < F.top then (((baseOnlyChart u).coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) else 0 := rfl
    rw [hcc, Prod.mk.eta, ht]
    simp [baseOnlyChart]
theorem norm_linearPart_le (hL : Odd F.blockSide) {M : ℝ} (hM : ∀ x i, ‖(u x i : ℍ[ℝ])‖ ≤ M) (j : ℕ) :
    ∀ y i, ‖linearPart R (baseOnlyChart u) j y i‖ ≤ (F.blockSide : ℝ) ^ j * M := by
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  induction j with
  | zero =>
    intro y i
    simpa [linearPart, baseOnlyChart] using hM y i
  | succ j ih =>
    intro y i
    have h1 := norm_parallelAverage_le hL (R j) (linearPart R (baseOnlyChart u) j) (y, i)
    have h2 : ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
        ‖linearPart R (baseOnlyChart u) j (lineBond (y, i) h r).1 (lineBond (y, i) h r).2‖ ≤
        ∑ _h ∈ centredCube F.blockSide, ∑ _r ∈ Finset.range F.blockSide, (F.blockSide : ℝ) ^ j * M :=
      Finset.sum_le_sum fun h _ => Finset.sum_le_sum fun r _ => ih _ _
    simp only [Finset.sum_const, Finset.card_range, card_centredCube hL, nsmul_eq_mul] at h2
    have hz : linearPart R (baseOnlyChart u) (j + 1) y i =
        parallelAverage (R j) (linearPart R (baseOnlyChart u) j) (y, i) := by
      simp only [linearPart, baseOnlyChart]
      simp
    rw [hz]
    refine h1.trans ?_
    calc 1 / (F.blockSide : ℝ) ^ 4 * _ ≤ 1 / (F.blockSide : ℝ) ^ 4 *
          (((F.blockSide ^ 4 : ℕ) : ℝ) * ((F.blockSide : ℝ) * ((F.blockSide : ℝ) ^ j * M))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by
        push_cast
        field_simp
        ring
end Transport
end Averages
section LinearZone
variable {F : BlockFrame}
theorem supNorm_blockLinePoint_add_two_le {L : ℕ} (hL : Odd L) (hL3 : 3 ≤ L) (w h : Fin 4 → ℤ)
    (hh : h ∈ centredCube L) (μ : Fin 4) {r : ℕ} (hr : r < L) :
    supNorm (blockLinePoint L w h μ r) + 2 ≤ L * (supNorm w + 2) := by
  obtain ⟨m, rfl⟩ := hL
  have hc := (mem_centredCube_iff _ h).1 hh
  have hhalf : ((((2 * m + 1 : ℕ) : ℤ) - 1) / 2) = m := by
    push_cast
    omega
  have hb : supNorm (blockLinePoint (2 * m + 1) w h μ r) ≤ (2 * m + 1) * supNorm w + m + 2 * m := by
    refine Finset.sup_le fun i _ => ?_
    have h1 := natAbs_le_supNorm w i
    have h2 := hc i
    rw [hhalf] at h2
    have h3 : ((h i).natAbs : ℤ) ≤ m := by
      rw [Int.natCast_natAbs, abs_le]
      exact h2
    have h5 : ((r : ℤ) * (Pi.single μ 1 : Fin 4 → ℤ) i).natAbs ≤ 2 * m := by
      by_cases hi : i = μ
      · subst hi
        simp
        omega
      · simp [hi]
    have h6 : (((2 * m + 1 : ℕ) : ℤ) * w i).natAbs ≤ (2 * m + 1) * supNorm w := by
      rw [Int.natAbs_mul]
      simp only [Int.natAbs_natCast]
      exact Nat.mul_le_mul_left _ h1
    unfold blockLinePoint
    calc _ ≤ (((2 * m + 1 : ℕ) : ℤ) * w i + h i).natAbs + ((r : ℤ) * (Pi.single μ 1 : Fin 4 → ℤ) i).natAbs :=
          Int.natAbs_add_le _ _
      _ ≤ (((2 * m + 1 : ℕ) : ℤ) * w i).natAbs + (h i).natAbs +
            ((r : ℤ) * (Pi.single μ 1 : Fin 4 → ℤ) i).natAbs :=
          Nat.add_le_add_right (Int.natAbs_add_le _ _) _
      _ ≤ _ := by omega
  nlinarith
theorem supNorm_smul_le (L : ℕ) (w : Fin 4 → ℤ) : supNorm (fun i => (L : ℤ) * w i) ≤ L * supNorm w := by
  refine Finset.sup_le fun i _ => ?_
  rw [Int.natAbs_mul]
  simp only [Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (natAbs_le_supNorm w i)
theorem length_axisPath_append_le {L : ℕ} (hL : Odd L) (h : Fin 4 → ℤ) (hh : h ∈ centredCube L)
    (π : Equiv.Perm (Fin 4)) (μ : Fin 4)
    {r : ℕ} (hr : r < L) : (axisPath h π ++ List.replicate r (μ, true)).length ≤ 3 * L := by
  obtain ⟨m, rfl⟩ := hL
  have hc := (mem_centredCube_iff _ h).1 hh
  have hhalf : ((((2 * m + 1 : ℕ) : ℤ) - 1) / 2) = m := by
    push_cast
    omega
  have hb : ∀ i, (h i).natAbs ≤ m := by
    intro i
    have h2 := hc i
    rw [hhalf] at h2
    have h3 : ((h i).natAbs : ℤ) ≤ m := by
      rw [Int.natCast_natAbs, abs_le]
      exact h2
    exact_mod_cast h3
  rw [List.length_append, length_axisPath, List.length_replicate]
  have := hb (π 0)
  have := hb (π 1)
  have := hb (π 2)
  have := hb (π 3)
  omega
theorem gradedPotential_mul (c κ : ℝ) (A : Fin 4 → Fin 4 → imaginaryQuaternions) (w : Fin 4 → ℤ) (μ : Fin 4) :
    gradedPotential (κ * c) A w μ = c • gradedPotential κ A w μ := by
  unfold gradedPotential
  rw [smul_smul, mul_comm]
theorem linearPart_eq_gradedPotential (hL : Odd F.blockSide) (hL3 : 3 ≤ F.blockSide) (R : F.FieldChain)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (A : Fin 4 → Fin 4 → imaginaryQuaternions) (hA : ∀ μ ν, A μ ν = - A ν μ) (κ : ℝ) (Bn : ℕ) (ρ ρ' : ℕ → ℕ)
    (hu : ∀ x μ, supNorm (intCoords x) + 2 ≤ Bn → u x μ = gradedPotential κ A (intCoords x) μ)
    (hroom : ∀ j, j ≤ F.top → ReadsBack F j (ρ j)) (hρ : ∀ j, j ≤ F.top → Bn ≤ ρ j * F.blockSide ^ j)
    (hρ1 : ∀ j, j ≤ F.top → 1 ≤ ρ j)
    (hR1 : ∀ j, j < F.top → ∀ x i, supNorm (intCoords x) ≤ ρ' j → R j x i = 1)
    (hρ' : ∀ j, j < F.top → ∀ t, (t + 2) * F.blockSide ^ (j + 1) ≤ Bn → (t + 3) * F.blockSide ≤ ρ' j) :
    ∀ j, j ≤ F.top → ∀ (y : F.Site j) (μ : Fin 4), (supNorm (intCoords y) + 2) * F.blockSide ^ j ≤ Bn →
      linearPart R (baseOnlyChart u) j y μ =
        ((gradedPotential (κ * ((F.blockSide : ℝ) ^ 2) ^ j) A (intCoords y) μ : imaginaryQuaternions) : ℍ[ℝ]) := by
  have hLp : 0 < F.blockSide := hL.pos
  intro j
  induction j with
  | zero =>
    intro _ y μ hy
    simp only [pow_zero, mul_one] at hy ⊢
    simp only [linearPart, baseOnlyChart]
    rw [hu y μ hy]
  | succ j ih =>
    intro hj y μ hy
    have hj' : j < F.top := by omega
    have hjj : j ≤ F.top := by omega
    set w := intCoords y with hw
    have hyw : siteOfCoords (j + 1) w = y := siteOfCoords_intCoords y
    have hdown : refineSite y = siteOfCoords j (fun i => (F.blockSide : ℤ) * w i) := by
      have := refineSite_siteOfCoords (F := F) (j := j) hj' w
      rwa [hyw] at this
    have hpow : 0 < F.blockSide ^ j := pow_pos hLp _
    have hterm : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4), ∀ r ∈ Finset.range F.blockSide,
        _root_.YangMills.Construction.BlockAverages.adjointAction (pathHolonomy (R j) (refineSite y) (axisPath h π ++ List.replicate r (μ, true)))
          (linearPart R (baseOnlyChart u) j (refineSite y + siteOfCoords j h + (r : ℤ) • unitStep j μ) μ) =
        ((gradedPotential (κ * ((F.blockSide : ℝ) ^ 2) ^ j) A (blockLinePoint F.blockSide w h μ r) μ :
          imaginaryQuaternions) : ℍ[ℝ]) := by
      intro h hh π r hr
      have hr' := Finset.mem_range.1 hr
      have hsite : refineSite y + siteOfCoords j h + (r : ℤ) • unitStep j μ =
          siteOfCoords j (blockLinePoint F.blockSide w h μ r) := by
        rw [hdown]
        funext i
        have e0 : (((r : ℤ) • unitStep j μ : F.Site j)) i = (r : ℤ) • ((unitStep j μ : F.Site j) i) := rfl
        simp only [Pi.add_apply]
        rw [e0, zsmul_eq_mul]
        simp only [siteOfCoords, unitStep, blockLinePoint]
        push_cast
        ring
      have hs := supNorm_blockLinePoint_add_two_le hL hL3 w h hh μ hr'
      have hs2 : (supNorm (blockLinePoint F.blockSide w h μ r) + 2) * F.blockSide ^ j ≤ Bn := by
        refine le_trans ?_ hy
        calc _ ≤ (F.blockSide * (supNorm w + 2)) * F.blockSide ^ j := Nat.mul_le_mul_right _ hs
          _ = _ := by ring
      have hs3 : supNorm (blockLinePoint F.blockSide w h μ r) + 2 ≤ ρ j := by
        have := hs2.trans (hρ j hjj)
        exact Nat.le_of_mul_le_mul_right this hpow
      have hbc : intCoords (siteOfCoords j (blockLinePoint F.blockSide w h μ r) : F.Site j) =
          blockLinePoint F.blockSide w h μ r :=
        intCoords_siteOfCoords (hroom j hjj) _ (by omega)
      have hih := ih hjj (siteOfCoords j (blockLinePoint F.blockSide w h μ r)) μ (by rw [hbc]; exact hs2)
      rw [hbc] at hih
      have hR1' : ReadsBack F j 1 := (hroom j hjj).mono (hρ1 j hjj)
      have hsw : supNorm (fun i => (F.blockSide : ℤ) * w i) + 2 ≤ F.blockSide * (supNorm w + 2) := by
        have := supNorm_smul_le F.blockSide w
        nlinarith
      have hsd : supNorm (fun i => (F.blockSide : ℤ) * w i) ≤ ρ j := by
        have h2 : (supNorm (fun i => (F.blockSide : ℤ) * w i) + 2) * F.blockSide ^ j ≤ Bn := by
          refine le_trans ?_ hy
          calc _ ≤ (F.blockSide * (supNorm w + 2)) * F.blockSide ^ j := Nat.mul_le_mul_right _ hsw
            _ = _ := by ring
        have := h2.trans (hρ j hjj)
        have := Nat.le_of_mul_le_mul_right this hpow
        omega
      have hbd : intCoords (refineSite y) = fun i => (F.blockSide : ℤ) * w i := by
        rw [hdown]
        exact intCoords_siteOfCoords (hroom j hjj) _ hsd
      have hhol : pathHolonomy (R j) (refineSite y) (axisPath h π ++ List.replicate r (μ, true)) = 1 := by
        refine pathHolonomy_eq_one hR1' (hR1 j hj') _ _ ?_
        rw [hbd]
        have h1 := length_axisPath_append_le hL h hh π μ hr'
        have h2 := hρ' j hj' (supNorm w) hy
        have h3 := supNorm_smul_le F.blockSide w
        nlinarith
      rw [hsite, hih, hhol, _root_.YangMills.Construction.BlockAverages.QuadraticResponseAtFlat.adjointAction_one_apply]
    have hexp := parallelAverage_eq_of_terms (R j) (linearPart R (baseOnlyChart u) j) (y, μ)
      (fun h r => gradedPotential (κ * ((F.blockSide : ℝ) ^ 2) ^ j) A (blockLinePoint F.blockSide w h μ r) μ) hterm
    have hcc : linearPart R (baseOnlyChart u) (j + 1) y μ =
        parallelAverage (R j) (linearPart R (baseOnlyChart u) j) (y, μ) +
          if j + 1 < F.top then (((baseOnlyChart u).coarse j y μ : imaginaryQuaternions) : ℍ[ℝ]) else 0 := rfl
    rw [hcc, hexp, sum_gradedPotential_blockLinePoint _ A hA hL]
    have hz : (if j + 1 < F.top then (((baseOnlyChart u).coarse j y μ : imaginaryQuaternions) : ℍ[ℝ]) else 0) = 0 := by
      simp [baseOnlyChart]
    rw [hz, add_zero]
    have e : κ * ((F.blockSide : ℝ) ^ 2) ^ (j + 1) = (κ * ((F.blockSide : ℝ) ^ 2) ^ j) * (F.blockSide : ℝ) ^ 2 := by
      rw [pow_succ]
      ring
    have hc : 1 / (24 * (F.blockSide : ℝ) ^ 4) * (24 * (F.blockSide : ℝ) ^ 6) = (F.blockSide : ℝ) ^ 2 := by
      field_simp
    have key : (1 / (24 * (F.blockSide : ℝ) ^ 4)) • (24 * (F.blockSide : ℝ) ^ 6) •
          gradedPotential (κ * ((F.blockSide : ℝ) ^ 2) ^ j) A w μ =
        gradedPotential (κ * ((F.blockSide : ℝ) ^ 2) ^ (j + 1)) A w μ := by
      rw [smul_smul, hc, e, gradedPotential_mul ((F.blockSide : ℝ) ^ 2) (κ * ((F.blockSide : ℝ) ^ 2) ^ j)]
    exact congrArg Subtype.val key
end LinearZone
section Norms
variable {F : BlockFrame}
theorem cellSupDist_triangle (a b c : F.Cell) : cellSupDist a c ≤ cellSupDist a b + cellSupDist b c := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
def unitWeights (F : BlockFrame) : F.SiteWeights := fun _ _ => 1
def linearDecay (del : ℝ) (y : F.Cell) : ℝ := -del * (cellSupDist y (0 : F.Cell) : ℝ)
theorem abs_linearDecay_sub_le {del : ℝ} (hdel : 0 ≤ del) (y y' : F.Cell) :
    |linearDecay del y - linearDecay del y'| ≤ del * cellSupDist y y' := by
  unfold linearDecay
  have h1 : (cellSupDist y (0 : F.Cell) : ℝ) ≤ cellSupDist y y' + cellSupDist y' 0 := by
    exact_mod_cast cellSupDist_triangle y y' 0
  have h2 : (cellSupDist y' (0 : F.Cell) : ℝ) ≤ cellSupDist y' y + cellSupDist y 0 := by
    exact_mod_cast cellSupDist_triangle y' y 0
  rw [cellSupDist_comm y' y] at h2
  rw [abs_le]
  constructor <;> nlinarith
theorem classWeight_zero_apply (del : ℝ) (p : F.Site 0) (j : ℕ) (x : F.Site j) :
    classWeight F (linearDecay del) 0 p j x = Real.exp (linearDecay del (enclosingCell x)) := by
  simp [classWeight]
theorem localNormSq_mul_le (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (W W' : F.SiteWeights)
    {c : ℝ} (hc : 0 ≤ c)
    (hW : ∀ (j : ℕ) (x : F.Site j), enclosingCell x ∈ B → 0 ≤ W j x ∧ c * W j x ≤ W' j x) :
    c ^ 2 * localNormSq S B R U W ≤ localNormSq S B R U W' := by
  classical
  unfold localNormSq
  have t1 : c ^ 2 * Real.sqrt (∑ b ∈ bondsOver S B 0, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) ≤
      Real.sqrt (∑ b ∈ bondsOver S B 0, (W' 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) := by
    have e : c ^ 2 = Real.sqrt (c ^ 4) := by
      rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [e, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    obtain ⟨h0, h1⟩ := hW 0 b.1 (Finset.mem_filter.1 hb).2
    have hn := norm_nonneg (U.fine b.1 b.2)
    have : c * (W 0 b.1 * ‖U.fine b.1 b.2‖) ≤ W' 0 b.1 * ‖U.fine b.1 b.2‖ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right h1 hn
    calc c ^ 4 * (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 = (c * (W 0 b.1 * ‖U.fine b.1 b.2‖)) ^ 4 := by ring
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hc (mul_nonneg h0 hn)) this 4
  have t2 : c ^ 2 * ∑ p ∈ plaquettesOver S B 0, (W 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 ≤
      ∑ p ∈ plaquettesOver S B 0, (W' 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨h0, h1⟩ := hW 0 p.1 (Finset.mem_filter.1 hp).2
    have hn := norm_nonneg (linearizedCurl (R 0) U.fine p)
    have : c * (W 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ≤ W' 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right h1 hn
    calc c ^ 2 * (W 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 =
          (c * (W 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖)) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hc (mul_nonneg h0 hn)) this 2
  have t3 : c ^ 2 * ∑ j ∈ Finset.range (F.top - 1), ∑ e ∈ bondsOver S B (j + 1),
        (W (j + 1) e.1 * ‖U.coarse j e.1 e.2‖) ^ 2 ≤
      ∑ j ∈ Finset.range (F.top - 1), ∑ e ∈ bondsOver S B (j + 1),
        (W' (j + 1) e.1 * ‖U.coarse j e.1 e.2‖) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e he => ?_
    obtain ⟨h0, h1⟩ := hW (j + 1) e.1 (Finset.mem_filter.1 he).2
    have hn := norm_nonneg (U.coarse j e.1 e.2)
    have : c * (W (j + 1) e.1 * ‖U.coarse j e.1 e.2‖) ≤ W' (j + 1) e.1 * ‖U.coarse j e.1 e.2‖ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right h1 hn
    calc c ^ 2 * (W (j + 1) e.1 * ‖U.coarse j e.1 e.2‖) ^ 2 =
          (c * (W (j + 1) e.1 * ‖U.coarse j e.1 e.2‖)) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hc (mul_nonneg h0 hn)) this 2
  rw [mul_add, mul_add]
  exact add_le_add (add_le_add t1 t2) t3
theorem localNormSq_nonneg (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (W : F.SiteWeights) :
    0 ≤ localNormSq S B R U W := by apply _root_.YangMills.Construction.CoordinateSeminorms.localNormSq_nonneg <;> assumption
theorem localNorm_mul_le (S : Finset F.Cell) (z : F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (W W' : F.SiteWeights)
    {c : ℝ} (hc : 0 ≤ c)
    (hW : ∀ (j : ℕ) (x : F.Site j), enclosingCell x ∈ cellBall S z 3 → 0 ≤ W j x ∧ c * W j x ≤ W' j x) :
    c * localNorm S R U W z ≤ localNorm S R U W' z := by
  unfold localNorm
  have e : c = Real.sqrt (c ^ 2) := (Real.sqrt_sq hc).symm
  rw [e, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt (localNormSq_mul_le S _ R U W W' hc hW)
theorem cellSupDist_le_of_mem_cellBall {S : Finset F.Cell} {z y : F.Cell} (h : y ∈ cellBall S z 3) :
    cellSupDist z y ≤ 3 := by
  classical
  exact (Finset.mem_filter.1 h).2
theorem localNorm_le_inverted (S : Finset F.Cell) (z : F.Cell) (R : F.FieldChain) (U : ChainChart F) {del : ℝ}
    (hdel : 0 ≤ del) (p : F.Site 0) :
    Real.exp (del * ((cellSupDist z (0 : F.Cell) : ℝ) - 3)) * localNorm S R U (unitWeights F) z ≤
      localNorm S R U (invertedWeights (classWeight F (linearDecay del) 0 p)) z := by
  refine localNorm_mul_le S z R U _ _ (Real.exp_pos _).le fun j x hx => ⟨zero_le_one, ?_⟩
  simp only [unitWeights, mul_one, invertedWeights, classWeight_zero_apply, linearDecay]
  rw [← Real.exp_neg]
  refine Real.exp_le_exp.2 ?_
  have h1 := cellSupDist_le_of_mem_cellBall hx
  have h2 : (cellSupDist z (0 : F.Cell) : ℝ) ≤ cellSupDist z (enclosingCell x) + cellSupDist (enclosingCell x) 0 := by
    exact_mod_cast cellSupDist_triangle z (enclosingCell x) 0
  have h3 : (cellSupDist z (enclosingCell x) : ℝ) ≤ 3 := by exact_mod_cast h1
  nlinarith
theorem localNorm_le_weighted (S : Finset F.Cell) (z : F.Cell) (R : F.FieldChain) (U : ChainChart F) {del : ℝ}
    (hdel : 0 ≤ del) (p : F.Site 0) :
    Real.exp (-del * ((cellSupDist z (0 : F.Cell) : ℝ) + 3)) * localNorm S R U (unitWeights F) z ≤
      localNorm S R U (classWeight F (linearDecay del) 0 p) z := by
  refine localNorm_mul_le S z R U _ _ (Real.exp_pos _).le fun j x hx => ⟨zero_le_one, ?_⟩
  simp only [unitWeights, mul_one, classWeight_zero_apply, linearDecay]
  refine Real.exp_le_exp.2 ?_
  have h1 := cellSupDist_le_of_mem_cellBall hx
  have h2 : (cellSupDist (enclosingCell x) (0 : F.Cell) : ℝ) ≤ cellSupDist (enclosingCell x) z + cellSupDist z 0 := by
    exact_mod_cast cellSupDist_triangle (enclosingCell x) z 0
  have h3 : (cellSupDist (enclosingCell x) z : ℝ) ≤ 3 := by
    rw [cellSupDist_comm]
    exact_mod_cast h1
  nlinarith
theorem localNorm_le_weightedNorm (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (W : F.SiteWeights)
    {z : F.Cell} (hz : z ∈ S) : localNorm S R U W z ≤ weightedNorm S R U W := by apply _root_.YangMills.Construction.BlockWeights.localNorm_le_weightedNorm <;> assumption
theorem sum_localNorm_le (S Sh : Finset F.Cell) (hSh : Sh ⊆ S) (R : F.FieldChain) (U : ChainChart F) {del : ℝ}
    (hdel : 0 ≤ del)
    (p : F.Site 0) {d₀ : ℝ} (hd : ∀ z ∈ Sh, d₀ ≤ cellSupDist z (0 : F.Cell)) :
    ∑ z ∈ Sh, localNorm S R U (unitWeights F) z ≤
      Real.exp (-del * (d₀ - 3)) * Real.sqrt (Sh.card) *
        _root_.YangMills.Construction.BlockAverages.weightedNorm S R U (invertedWeights (classWeight F (linearDecay del) 0 p)) := by
  set Wi := invertedWeights (classWeight F (linearDecay del) 0 p) with hWi
  have h1 : ∀ z ∈ Sh, localNorm S R U (unitWeights F) z ≤ Real.exp (-del * (d₀ - 3)) * localNorm S R U Wi z := by
    intro z hz
    have h2 := localNorm_le_inverted S z R U hdel p
    have h3 : Real.exp (del * (d₀ - 3)) ≤ Real.exp (del * ((cellSupDist z (0 : F.Cell) : ℝ) - 3)) :=
      Real.exp_le_exp.2 (by nlinarith [hd z hz])
    have hn : 0 ≤ localNorm S R U (unitWeights F) z := Real.sqrt_nonneg _
    have h4 : Real.exp (del * (d₀ - 3)) * localNorm S R U (unitWeights F) z ≤ localNorm S R U Wi z :=
      (mul_le_mul_of_nonneg_right h3 hn).trans h2
    have e : Real.exp (-del * (d₀ - 3)) * Real.exp (del * (d₀ - 3)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc localNorm S R U (unitWeights F) z
        = Real.exp (-del * (d₀ - 3)) * (Real.exp (del * (d₀ - 3)) * localNorm S R U (unitWeights F) z) := by
          rw [← mul_assoc, e, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have h5 : (∑ z ∈ Sh, localNorm S R U Wi z) ^ 2 ≤ (Sh.card : ℝ) * ∑ z ∈ Sh, localNorm S R U Wi z ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h6 : ∑ z ∈ Sh, localNorm S R U Wi z ^ 2 ≤ ∑ z ∈ S, localNorm S R U Wi z ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hSh fun _ _ _ => sq_nonneg _
  unfold _root_.YangMills.Construction.BlockAverages.weightedNorm
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.le_sqrt_of_sq_le (h5.trans ?_)
  exact mul_le_mul_of_nonneg_left h6 (by positivity)
end Norms
section Setup
variable {F : BlockFrame}
structure ComparisonSetup (S : Finset F.Cell) (r q : ℕ) : Prop where
  odd_blockSide : Odd F.blockSide
  three_le_blockSide : 3 ≤ F.blockSide
  ambient : IsAdmissibleAmbient F
  five_le_scale : 5 ≤ q
  scale_le_radius : 24 * q ≤ r
  box_mem : ∀ h, WithinRadius r h → siteOfCoords F.top h ∈ S
  extent_large : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i
abbrev cellSide (F : BlockFrame) : ℕ := F.blockSide ^ F.top
variable {S : Finset F.Cell} {r q : ℕ}
theorem ComparisonSetup.cellSide_pos (h : ComparisonSetup S r q) : 0 < cellSide F := pow_pos h.odd_blockSide.pos _
theorem ComparisonSetup.cellSide_pos_real (h : ComparisonSetup S r q) : (0 : ℝ) < cellSide F := by
  exact_mod_cast h.cellSide_pos
theorem ComparisonSetup.readsBack (h : ComparisonSetup S r q) (j : ℕ) :
    ReadsBack F j ((r + 1) * F.blockSide ^ (F.top - j)) := by
  intro i
  have hM : 0 < F.blockSide ^ (F.top - j) := pow_pos h.odd_blockSide.pos _
  rcases h.extent_large i with h1 | h1
  · left
    simp [BlockFrame.period, h1]
  · right
    simp only [BlockFrame.period]
    push_cast
    nlinarith
theorem ComparisonSetup.readsBack_one (h : ComparisonSetup S r q) (j : ℕ) : ReadsBack F j 1 :=
  (h.readsBack j).mono (by
    have : 0 < F.blockSide ^ (F.top - j) := pow_pos h.odd_blockSide.pos _
    nlinarith)
theorem ComparisonSetup.reference_eq_one (hRef : flatTopReferenceStatement) (h : ComparisonSetup S r q)
    {j : ℕ} (hj : j ≤ F.top)
    (x : F.Site j) (i : Fin 4) (hx : supNorm (intCoords x) ≤ (r - 3) * F.blockSide ^ (F.top - j)) :
    referenceFieldChain S flatTopField j x i = 1 := by
  have hM : 0 < F.blockSide ^ (F.top - j) := pow_pos h.odd_blockSide.pos _
  have hr : 120 ≤ r := by
    have := h.five_le_scale
    have := h.scale_le_radius
    omega
  refine referenceFieldChain_eq_one hRef h.odd_blockSide h.ambient hj (ρ := (r - 3) * F.blockSide ^ (F.top - j))
    ((h.readsBack j).mono ?_) ?_ h.box_mem ?_ x i hx
  · exact Nat.mul_le_mul_right _ (by omega)
  · exact Nat.mul_pos (by omega) hM
  · have hM' : (1 : ℤ) ≤ (F.blockSide : ℤ) ^ (F.top - j) := by exact_mod_cast hM
    have e : (((r - 3) * F.blockSide ^ (F.top - j) : ℕ) : ℤ) = ((r : ℤ) - 3) * (F.blockSide : ℤ) ^ (F.top - j) := by
      push_cast [Nat.cast_sub (show 3 ≤ r by omega)]
      ring
    rw [e]
    nlinarith
def candidateCutoff (q N : ℕ) (w : Fin 4 → ℤ) : ℝ := cutoffRamp (6 * q * N) (7 * q * N) (supNorm w)
def testCutoff (q N : ℕ) (w : Fin 4 → ℤ) : ℝ := cutoffRamp (4 * q * N) (5 * q * N) (supNorm w)
def candidateForm (F : BlockFrame) (q : ℕ) (A : Fin 4 → Fin 4 → imaginaryQuaternions) :
    F.Site 0 → Fin 4 → imaginaryQuaternions :=
  fun x μ => candidateCutoff q (cellSide F) (intCoords x) •
    gradedPotential (1 / (2 * (cellSide F : ℝ) ^ 2)) A (intCoords x) μ
theorem ComparisonSetup.candidate_gap (h : ComparisonSetup S r q) :
    (6 * q * cellSide F : ℝ) < 7 * q * cellSide F := by
  have h1 := h.cellSide_pos_real
  have h2 : (5 : ℝ) ≤ q := by exact_mod_cast h.five_le_scale
  nlinarith [mul_pos (by linarith : (0 : ℝ) < q) h1]
theorem ComparisonSetup.test_gap (h : ComparisonSetup S r q) : (4 * q * cellSide F : ℝ) < 5 * q * cellSide F := by
  have h1 := h.cellSide_pos_real
  have h2 : (5 : ℝ) ≤ q := by exact_mod_cast h.five_le_scale
  nlinarith [mul_pos (by linarith : (0 : ℝ) < q) h1]
theorem candidateForm_eq_of_inner (h : ComparisonSetup S r q) (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (x : F.Site 0) (μ : Fin 4)
    (hx : supNorm (intCoords x) ≤ 6 * q * cellSide F) :
    candidateForm F q A x μ = gradedPotential (1 / (2 * (cellSide F : ℝ) ^ 2)) A (intCoords x) μ := by
  unfold candidateForm candidateCutoff
  rw [cutoffRamp_eq_one_of_le h.candidate_gap (by exact_mod_cast hx), one_smul]
theorem candidateForm_eq_zero_of_outer (h : ComparisonSetup S r q) (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (x : F.Site 0) (μ : Fin 4)
    (hx : 7 * q * cellSide F ≤ supNorm (intCoords x)) : candidateForm F q A x μ = 0 := by
  unfold candidateForm candidateCutoff
  rw [cutoffRamp_eq_zero_of_ge h.candidate_gap (by exact_mod_cast hx), zero_smul]
theorem norm_candidateForm_le (h : ComparisonSetup S r q) (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (x : F.Site 0) (μ : Fin 4) :
    ‖candidateForm F q A x μ‖ ≤ 4 * q / cellSide F * curvatureL1 A := by
  have hN := h.cellSide_pos_real
  have hS := curvatureL1_nonneg A
  by_cases hx : 7 * q * cellSide F ≤ supNorm (intCoords x)
  · rw [candidateForm_eq_zero_of_outer h A x μ hx, norm_zero]
    positivity
  · have hx' : (supNorm (intCoords x) : ℝ) ≤ 7 * q * cellSide F := by
      have : supNorm (intCoords x) ≤ 7 * q * cellSide F := by omega
      exact_mod_cast this
    unfold candidateForm candidateCutoff
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoffRamp_nonneg _ _ _)]
    have h1 := cutoffRamp_le_one (6 * q * cellSide F) (7 * q * cellSide F) (supNorm (intCoords x))
    have h2 := norm_gradedPotential_le (1 / (2 * (cellSide F : ℝ) ^ 2)) A (intCoords x) μ
    have h3 : |1 / (2 * (cellSide F : ℝ) ^ 2)| = 1 / (2 * (cellSide F : ℝ) ^ 2) := abs_of_pos (by positivity)
    rw [h3] at h2
    have h4 : 1 / (2 * (cellSide F : ℝ) ^ 2) * ((supNorm (intCoords x) : ℝ) * curvatureL1 A) ≤
        1 / (2 * (cellSide F : ℝ) ^ 2) * ((7 * q * cellSide F) * curvatureL1 A) := by gcongr
    have h5 : 1 / (2 * (cellSide F : ℝ) ^ 2) * ((7 * q * cellSide F) * curvatureL1 A) ≤
        4 * q / cellSide F * curvatureL1 A := by
      have e : 1 / (2 * (cellSide F : ℝ) ^ 2) * ((7 * q * cellSide F) * curvatureL1 A) =
          (7 / 2) * q / cellSide F * curvatureL1 A := by
        field_simp
      rw [e]
      gcongr
      norm_num
    calc _ ≤ 1 * ‖gradedPotential (1 / (2 * (cellSide F : ℝ) ^ 2)) A (intCoords x) μ‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ _ := by
        rw [one_mul]
        exact h2.trans (h4.trans h5)
def candidateChart (F : BlockFrame) (q : ℕ) (A : Fin 4 → Fin 4 → imaginaryQuaternions) : ChainChart F :=
  baseOnlyChart (candidateForm F q A)
theorem linearPart_candidate_top (hRef : flatTopReferenceStatement) (h : ComparisonSetup S r q)
    (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (hA : ∀ μ ν, A μ ν = - A ν μ) (y : F.Cell) (μ : Fin 4) (hy : supNorm (intCoords y) + 2 ≤ 6 * q) :
    linearPart (referenceFieldChain S flatTopField) (candidateChart F q A) F.top y μ =
      constantCurvaturePotential A y μ := by
  have hN := h.cellSide_pos
  have hq := h.five_le_scale
  have hr := h.scale_le_radius
  have key := linearPart_eq_gradedPotential h.odd_blockSide h.three_le_blockSide
    (referenceFieldChain S flatTopField) (candidateForm F q A) A hA
    (1 / (2 * (cellSide F : ℝ) ^ 2)) (6 * q * cellSide F) (fun j => (r + 1) * F.blockSide ^ (F.top - j))
    (fun j => (r - 3) * F.blockSide ^ (F.top - j))
    (fun x μ hx => candidateForm_eq_of_inner h A x μ (by omega))
    (fun j _ => h.readsBack j)
    (fun j hj => by
      have e : F.blockSide ^ (F.top - j) * F.blockSide ^ j = cellSide F := by
        rw [← pow_add]
        congr 1
        omega
      calc 6 * q * cellSide F ≤ (r + 1) * cellSide F := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by rw [← e]; ring)
    (fun j _ => Nat.mul_pos (by omega) (pow_pos h.odd_blockSide.pos _) )
    (fun j hj x i hx => h.reference_eq_one hRef hj.le x i hx)
    (fun j hj t ht => by
      have e : F.blockSide ^ (F.top - j) * F.blockSide ^ j = cellSide F := by
        rw [← pow_add]
        congr 1
        omega
      have hM : F.blockSide ≤ F.blockSide ^ (F.top - j) := by
        calc F.blockSide = F.blockSide ^ 1 := (pow_one _).symm
          _ ≤ _ := Nat.pow_le_pow_right h.odd_blockSide.pos (by omega)
      have hp : 0 < F.blockSide ^ j := pow_pos h.odd_blockSide.pos _
      have h1 : ((t + 2) * F.blockSide) * F.blockSide ^ j ≤ (6 * q * F.blockSide ^ (F.top - j)) * F.blockSide ^ j := by
        calc ((t + 2) * F.blockSide) * F.blockSide ^ j = (t + 2) * F.blockSide ^ (j + 1) := by ring
          _ ≤ 6 * q * cellSide F := ht
          _ = _ := by rw [← e]; ring
      have h2 := Nat.le_of_mul_le_mul_right h1 hp
      have h3 : (6 * q + 1) * F.blockSide ^ (F.top - j) ≤ (r - 3) * F.blockSide ^ (F.top - j) :=
        Nat.mul_le_mul_right _ (by omega)
      nlinarith)
    F.top le_rfl y μ (by
      calc (supNorm (intCoords y) + 2) * F.blockSide ^ F.top ≤ (6 * q) * F.blockSide ^ F.top :=
            Nat.mul_le_mul_right _ hy
        _ = _ := rfl)
  show linearPart (referenceFieldChain S flatTopField) (baseOnlyChart (candidateForm F q A)) F.top y μ = _
  rw [key]
  have e : 1 / (2 * (cellSide F : ℝ) ^ 2) * (((F.blockSide : ℝ)) ^ 2) ^ F.top = 1 / 2 := by
    have e2 : (((F.blockSide : ℝ)) ^ 2) ^ F.top = (cellSide F : ℝ) ^ 2 := by
      push_cast [cellSide]
      ring
    rw [e2]
    field_simp
  rw [e]
  rfl
end Setup
section FarZone
variable {F : BlockFrame} {S : Finset F.Cell} {r q : ℕ}
theorem supNorm_enclosingCell_le (h : ComparisonSetup S r q) (x : F.Site 0) {t : ℕ} (ht : t ≤ r)
    (hx : supNorm (intCoords x) ≤ t * cellSide F) :
    supNorm (intCoords (enclosingCell x)) ≤ t + 1 := by
  have hN : (0 : ℤ) < (cellSide F : ℤ) := by exact_mod_cast h.cellSide_pos
  have hcell := LumpContours.BlockLevels.enclosingCell_siteOfCoords (F := F) (j := 0) (Nat.zero_le _)
    h.odd_blockSide.pos (intCoords x)
  rw [siteOfCoords_intCoords] at hcell
  set v : Fin 4 → ℤ := fun i => (intCoords x i + ((F.blockSide : ℤ) ^ (F.top - 0) - 1) / 2) /
    (F.blockSide : ℤ) ^ (F.top - 0) with hv
  have hpow : (F.blockSide : ℤ) ^ (F.top - 0) = (cellSide F : ℤ) := by
    simp [cellSide]
  have hb : ∀ i, |v i| ≤ (t : ℤ) + 1 := by
    intro i
    have hodd : Odd ((F.blockSide : ℤ) ^ (F.top - 0)) := by
      have : Odd (F.blockSide : ℤ) := by exact_mod_cast h.odd_blockSide
      exact this.pow
    obtain ⟨k, hk⟩ := hodd
    have hP : (0 : ℤ) < (F.blockSide : ℤ) ^ (F.top - 0) := by rw [hpow]; exact hN
    have hw : |intCoords x i| ≤ (((t : ℤ) + 1) - 1) * (F.blockSide : ℤ) ^ (F.top - 0) := by
      have h1 := natAbs_le_supNorm (intCoords x) i
      rw [Int.abs_eq_natAbs, hpow]
      have h2 : (intCoords x i).natAbs ≤ t * cellSide F := h1.trans hx
      have h3 : ((intCoords x i).natAbs : ℤ) ≤ (t : ℤ) * (cellSide F : ℤ) := by exact_mod_cast h2
      have e : ((t : ℤ) + 1 - 1) * (cellSide F : ℤ) = (t : ℤ) * (cellSide F : ℤ) := by ring
      rw [e]
      exact h3
    refine abs_ediv_le_of_abs_le hP ?_ ?_ hw
    · rw [hk]
      omega
    · rw [hk]
      omega
  have hsv : supNorm v ≤ t + 1 := by
    refine Finset.sup_le fun i _ => ?_
    have := hb i
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  have hroom : ReadsBack F F.top (t + 1) := (h.readsBack F.top).mono (by simp; omega)
  rw [hcell, intCoords_siteOfCoords hroom v hsv]
  exact hsv
theorem linearPart_candidate_far (h : ComparisonSetup S r q) (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (R : F.FieldChain) (y : F.Cell) (μ : Fin 4)
    (hy : 7 * q + 3 ≤ supNorm (intCoords y)) : linearPart R (candidateChart F q A) F.top y μ = 0 := by
  classical
  have hr := h.scale_le_radius
  have hmem : (y, μ) ∈ innerBonds ({y, y + unitStep F.top μ} : Finset F.Cell) F.top := by
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    refine ⟨mem_sitesOfCells_top.2 (Finset.mem_insert_self _ _), mem_sitesOfCells_top.2 (by simp)⟩
  have hz : ∀ b ∈ innerBonds ({y, y + unitStep F.top μ} : Finset F.Cell) 0, candidateForm F q A b.1 b.2 = 0 := by
    intro b hb
    have hb1 : b.1 ∈ sitesOfCells ({y, y + unitStep F.top μ} : Finset F.Cell) 0 := by
      simp only [innerBonds, Finset.mem_filter, Finset.mem_product] at hb
      exact hb.1.1
    have hc := LumpContours.BlockLevels.enclosingCell_mem_of_mem_sitesOfCells (Nat.zero_le _) h.odd_blockSide hb1
    refine candidateForm_eq_zero_of_outer h A b.1 b.2 ?_
    by_contra hlt
    have hs := supNorm_enclosingCell_le h b.1 (t := 7 * q) (by omega) (le_of_lt (not_le.1 hlt))
    rcases Finset.mem_insert.1 hc with h1 | h1
    · rw [h1] at hs
      omega
    · rw [Finset.mem_singleton.1 h1] at hs
      have := supNorm_intCoords_le_add_unitStep (h.readsBack_one F.top) y μ
      omega
  exact linearPart_eq_zero_of_vanishing (R := R) (u := candidateForm F q A) h.odd_blockSide _ hz F.top le_rfl
    (y, μ) hmem
theorem norm_linearPart_candidate_le (h : ComparisonSetup S r q) (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (R : F.FieldChain) (y : F.Cell) (μ : Fin 4) :
    ‖linearPart R (candidateChart F q A) F.top y μ‖ ≤ 4 * q * curvatureL1 A := by
  have hb := norm_linearPart_le (R := R) (u := candidateForm F q A) h.odd_blockSide
    (M := 4 * q / cellSide F * curvatureL1 A)
    (fun x i => norm_candidateForm_le h A x i) F.top y μ
  refine hb.trans (le_of_eq ?_)
  have hN := h.cellSide_pos_real
  have e : ((F.blockSide : ℝ)) ^ F.top = (cellSide F : ℝ) := by
    push_cast [cellSide]
    rfl
  rw [e]
  field_simp
def untransportedCurl (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (p : F.Site 0 × Fin 4 × Fin 4) :
    imaginaryQuaternions :=
  u p.1 p.2.1 + u (p.1 + unitStep 0 p.2.1) p.2.2 - u (p.1 + unitStep 0 p.2.2) p.2.1 - u p.1 p.2.2
theorem linearizedCurl_eq_untransported (hRef : flatTopReferenceStatement) (h : ComparisonSetup S r q)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S 0) :
    linearizedCurl (referenceFieldChain S flatTopField 0) u p = (untransportedCurl u p : ℍ[ℝ]) := by
  classical
  have hc : plaquetteCorners p ⊆ sitesOfCells S 0 := (Finset.mem_filter.1 hp).2.2
  have cell : ∀ x ∈ plaquetteCorners p, enclosingCell x ∈ S := fun x hx =>
    LumpContours.BlockLevels.enclosingCell_mem_of_mem_sitesOfCells (Nat.zero_le _) h.odd_blockSide (hc hx)
  have m0 : p.1 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have m1 : p.1 + unitStep 0 p.2.1 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have m2 : p.1 + unitStep 0 p.2.2 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have m3 : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have m3' : p.1 + unitStep 0 p.2.2 + unitStep 0 p.2.1 ∈ plaquetteCorners p := by
    rw [add_right_comm]
    exact m3
  have r1 := hRef F S 0 p.1 p.2.1 h.odd_blockSide h.ambient (Nat.zero_le _) (cell _ m0) (cell _ m1)
  have r2 := hRef F S 0 (p.1 + unitStep 0 p.2.1) p.2.2 h.odd_blockSide h.ambient (Nat.zero_le _) (cell _ m1)
    (cell _ m3)
  have r3 := hRef F S 0 (p.1 + unitStep 0 p.2.2) p.2.1 h.odd_blockSide h.ambient (Nat.zero_le _) (cell _ m2)
    (cell _ m3')
  have r4 := hRef F S 0 p.1 p.2.2 h.odd_blockSide h.ambient (Nat.zero_le _) (cell _ m0) (cell _ m2)
  unfold linearizedCurl untransportedCurl
  simp only [r1, r2, r3, r4, inv_one, mul_one, _root_.YangMills.Construction.BlockAverages.QuadraticResponseAtFlat.adjointAction_one_apply]
  rfl
theorem intCoords_add_unitStep (h : ComparisonSetup S r q) (x : F.Site 0) (μ : Fin 4)
    (hx : supNorm (intCoords x) + 1 ≤ (r + 1) * cellSide F) :
    intCoords (x + unitStep 0 μ) = intCoords x + Pi.single μ 1 := by
  have e : x + unitStep 0 μ = siteOfCoords 0 (intCoords x + Pi.single μ 1) := by
    rw [siteOfCoords_add]
    congr 1
    exact (siteOfCoords_intCoords x).symm
  rw [e]
  exact intCoords_siteOfCoords (h.readsBack 0) _ ((supNorm_add_single_le _ _).trans hx)
end FarZone
section CandidateCurl
variable {F : BlockFrame} {S : Finset F.Cell} {r q : ℕ}
theorem inner_zone_le (h : ComparisonSetup S r q) : 6 * q * cellSide F + 2 ≤ (r + 1) * cellSide F := by
  have hN := h.cellSide_pos
  have hq := h.five_le_scale
  have hr := h.scale_le_radius
  nlinarith
theorem outer_zone_le (h : ComparisonSetup S r q) : 7 * q * cellSide F + 3 ≤ (r + 1) * cellSide F := by
  have hN := h.cellSide_pos
  have hq := h.five_le_scale
  have hr := h.scale_le_radius
  nlinarith
theorem untransportedCurl_candidate_inner (h : ComparisonSetup S r q) (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (hA : ∀ μ ν, A μ ν = - A ν μ)
    (x : F.Site 0) (μ ν : Fin 4) (hx : supNorm (intCoords x) + 1 ≤ 6 * q * cellSide F) :
    untransportedCurl (candidateForm F q A) (x, μ, ν) = (1 / (cellSide F : ℝ) ^ 2) • A μ ν := by
  have h6 := inner_zone_le h
  have hm := intCoords_add_unitStep h x μ (by omega)
  have hn := intCoords_add_unitStep h x ν (by omega)
  have s1 : supNorm (intCoords (x + unitStep 0 μ)) ≤ 6 * q * cellSide F := by
    rw [hm]
    exact (supNorm_add_single_le _ _).trans hx
  have s2 : supNorm (intCoords (x + unitStep 0 ν)) ≤ 6 * q * cellSide F := by
    rw [hn]
    exact (supNorm_add_single_le _ _).trans hx
  have s0 : supNorm (intCoords x) ≤ 6 * q * cellSide F := by omega
  simp only [untransportedCurl]
  rw [candidateForm_eq_of_inner h A _ _ s0, candidateForm_eq_of_inner h A _ _ s1,
    candidateForm_eq_of_inner h A _ _ s2, candidateForm_eq_of_inner h A _ _ s0, hm, hn,
    gradedPotential_curl _ A hA]
  congr 1
  have hN := h.cellSide_pos_real
  field_simp
theorem untransportedCurl_candidate_far (h : ComparisonSetup S r q) (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (x : F.Site 0) (μ ν : Fin 4)
    (hx : 7 * q * cellSide F + 2 ≤ supNorm (intCoords x)) :
    untransportedCurl (candidateForm F q A) (x, μ, ν) = 0 := by
  have a1 := supNorm_intCoords_le_add_unitStep (h.readsBack_one 0) x μ
  have a2 := supNorm_intCoords_le_add_unitStep (h.readsBack_one 0) x ν
  simp only [untransportedCurl]
  rw [candidateForm_eq_zero_of_outer h A _ _ (by omega), candidateForm_eq_zero_of_outer h A _ _ (by omega),
    candidateForm_eq_zero_of_outer h A _ _ (by omega), candidateForm_eq_zero_of_outer h A _ _ (by omega)]
  simp
theorem norm_le_curvatureL1 (A : Fin 4 → Fin 4 → imaginaryQuaternions) (μ ν : Fin 4) : ‖A μ ν‖ ≤ curvatureL1 A := by
  unfold curvatureL1
  have h1 : ‖A μ ν‖ ≤ ∑ ν', ‖A μ ν'‖ :=
    Finset.single_le_sum (f := fun ν' => ‖A μ ν'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
  have h2 : ∑ ν', ‖A μ ν'‖ ≤ ∑ μ', ∑ ν', ‖A μ' ν'‖ :=
    Finset.single_le_sum (f := fun μ' => ∑ ν', ‖A μ' ν'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ _)
  exact h1.trans h2
theorem abs_supNorm_add_single_sub_le (w : Fin 4 → ℤ) (i : Fin 4) :
    |(supNorm (w + Pi.single i 1) : ℝ) - supNorm w| ≤ 1 := by
  have a1 : (supNorm (w + Pi.single i 1) : ℝ) ≤ supNorm w + 1 := by exact_mod_cast supNorm_add_single_le w i
  have a2 : (supNorm w : ℝ) ≤ supNorm (w + Pi.single i 1) + 1 := by exact_mod_cast supNorm_le_add_single w i
  rw [abs_le]
  constructor <;> linarith
theorem abs_candidateCutoff_step_le (h : ComparisonSetup S r q) (w : Fin 4 → ℤ) (i : Fin 4) :
    |candidateCutoff q (cellSide F) (w + Pi.single i 1) - candidateCutoff q (cellSide F) w| ≤
      1 / (q * cellSide F) := by
  unfold candidateCutoff
  refine (abs_cutoffRamp_sub_le h.candidate_gap _ _).trans ?_
  have hN := h.cellSide_pos_real
  have hq : (0 : ℝ) < q := by
    have := h.five_le_scale
    exact_mod_cast (by omega : 0 < q)
  have e : (7 * q * cellSide F : ℝ) - 6 * q * cellSide F = q * cellSide F := by ring
  rw [e]
  exact div_le_div_of_nonneg_right (abs_supNorm_add_single_sub_le w i) (by positivity)
theorem norm_untransportedCurl_candidate_le (h : ComparisonSetup S r q) (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (hA : ∀ μ ν, A μ ν = - A ν μ)
    (p : F.Site 0 × Fin 4 × Fin 4) :
    ‖untransportedCurl (candidateForm F q A) p‖ ≤ 9 / (cellSide F : ℝ) ^ 2 * curvatureL1 A := by
  obtain ⟨x, μ, ν⟩ := p
  have hNr := h.cellSide_pos_real
  have hS := curvatureL1_nonneg A
  by_cases hfar : 7 * q * cellSide F + 2 ≤ supNorm (intCoords x)
  · rw [untransportedCurl_candidate_far h A x μ ν hfar, norm_zero]
    positivity
  have h7 := outer_zone_le h
  have hx1 : supNorm (intCoords x) + 1 ≤ (r + 1) * cellSide F := by omega
  set w := intCoords x with hw
  have hm := intCoords_add_unitStep h x μ hx1
  have hn := intCoords_add_unitStep h x ν hx1
  set κ : ℝ := 1 / (2 * (cellSide F : ℝ) ^ 2) with hκ
  have hκ0 : 0 < κ := by positivity
  set c₀ := candidateCutoff q (cellSide F) w with hc0
  set c₁ := candidateCutoff q (cellSide F) (w + Pi.single μ 1) with hc1
  set c₂ := candidateCutoff q (cellSide F) (w + Pi.single ν 1) with hc2
  have e : untransportedCurl (candidateForm F q A) (x, μ, ν) =
      c₀ • ((2 * κ) • A μ ν) + (c₁ - c₀) • gradedPotential κ A (w + Pi.single μ 1) ν -
        (c₂ - c₀) • gradedPotential κ A (w + Pi.single ν 1) μ := by
    have hc := gradedPotential_curl κ A hA w μ ν
    rw [← hc]
    simp only [untransportedCurl, candidateForm, hm, hn]
    simp only [← hw, ← hκ, ← hc0, ← hc1, ← hc2]
    module
  rw [e]
  have hN1 : (1 : ℝ) ≤ cellSide F := by exact_mod_cast h.cellSide_pos
  have hq5 : (5 : ℝ) ≤ q := by exact_mod_cast h.five_le_scale
  have hsz : ∀ i, (supNorm (w + Pi.single i 1) : ℝ) ≤ 7 * q * cellSide F + 2 := by
    intro i
    have a1 := supNorm_add_single_le w i
    have a2 : supNorm (w + Pi.single i 1) ≤ 7 * q * cellSide F + 2 := by omega
    exact_mod_cast a2
  have b0 : ‖c₀ • ((2 * κ) • A μ ν)‖ ≤ 2 * κ * curvatureL1 A := by
    have hc00 : 0 ≤ c₀ := cutoffRamp_nonneg _ _ _
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc00,
      abs_of_pos (by positivity : 0 < 2 * κ)]
    have h1 : c₀ ≤ 1 := cutoffRamp_le_one _ _ _
    have h2 := norm_le_curvatureL1 A μ ν
    calc c₀ * (2 * κ * ‖A μ ν‖) ≤ 1 * (2 * κ * curvatureL1 A) := by
          refine mul_le_mul h1 ?_ (by positivity) zero_le_one
          gcongr
      _ = _ := one_mul _
  have bp : ∀ (c : ℝ) (i j : Fin 4), |c| ≤ 1 / (q * cellSide F) →
      ‖c • gradedPotential κ A (w + Pi.single i 1) j‖ ≤ 8 * κ * curvatureL1 A / 1 := by
    intro c i j hc
    rw [norm_smul, Real.norm_eq_abs]
    have h2 := norm_gradedPotential_le κ A (w + Pi.single i 1) j
    rw [abs_of_pos hκ0] at h2
    have h3 : κ * ((supNorm (w + Pi.single i 1) : ℝ) * curvatureL1 A) ≤
        κ * ((7 * q * cellSide F + 2) * curvatureL1 A) := by
      have := hsz i
      gcongr
    have hqN : (5 : ℝ) ≤ q * cellSide F := by nlinarith
    have h4 : 1 / (q * cellSide F) * (κ * ((7 * q * cellSide F + 2) * curvatureL1 A)) ≤ 8 * κ * curvatureL1 A := by
      have e2 : 1 / (q * cellSide F) * (κ * ((7 * q * cellSide F + 2) * curvatureL1 A)) =
          (7 + 2 / (q * cellSide F)) * (κ * curvatureL1 A) := by
        field_simp
      rw [e2]
      have h5 : 2 / ((q : ℝ) * cellSide F) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      have hk : 0 ≤ κ * curvatureL1 A := by positivity
      nlinarith
    rw [div_one]
    calc |c| * ‖gradedPotential κ A (w + Pi.single i 1) j‖ ≤
          1 / (q * cellSide F) * (κ * ((7 * q * cellSide F + 2) * curvatureL1 A)) := by
          refine mul_le_mul hc (h2.trans h3) (norm_nonneg _) (by positivity)
      _ ≤ _ := h4
  have d1 := bp (c₁ - c₀) μ ν (abs_candidateCutoff_step_le h w μ)
  have d2 := bp (c₂ - c₀) ν μ (abs_candidateCutoff_step_le h w ν)
  have hfin : 2 * κ * curvatureL1 A + 8 * κ * curvatureL1 A / 1 + 8 * κ * curvatureL1 A / 1 ≤
      9 / (cellSide F : ℝ) ^ 2 * curvatureL1 A := by
    have e3 : 9 / (cellSide F : ℝ) ^ 2 = 18 * κ := by
      rw [hκ]
      field_simp
      norm_num
    rw [e3]
    have hk : 0 ≤ κ * curvatureL1 A := by positivity
    nlinarith
  refine le_trans ?_ hfin
  refine (norm_sub_le _ _).trans ?_
  exact add_le_add ((norm_add_le _ _).trans (add_le_add b0 d1)) d2
end CandidateCurl
section TestCurl
variable {F : BlockFrame} {S : Finset F.Cell} {r q : ℕ}
open Classical in
def coordBall (F : BlockFrame) (ρ : ℕ) : Finset (F.Site 0) :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(ρ : ℤ)) ρ).image (siteOfCoords 0)
theorem mem_coordBall {ρ : ℕ} (hR : ReadsBack F 0 ρ) {x : F.Site 0} :
    x ∈ coordBall F ρ ↔ supNorm (intCoords x) ≤ ρ := by
  classical
  constructor
  · intro hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
    have hs : supNorm w ≤ ρ := by
      refine Finset.sup_le fun i _ => ?_
      have := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hw i)
      have h2 : |w i| ≤ ρ := abs_le.2 this
      rw [Int.abs_eq_natAbs] at h2
      exact_mod_cast h2
    rwa [intCoords_siteOfCoords hR w hs]
  · intro hx
    refine Finset.mem_image.2 ⟨intCoords x, Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ?_,
      siteOfCoords_intCoords x⟩
    have h1 := natAbs_le_supNorm (intCoords x) i
    have h2 : |intCoords x i| ≤ ρ := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h1.trans hx
    exact abs_le.1 h2
theorem sum_translate {M : Type*} [AddCommGroup M] (G : F.Site 0 → M) (e : F.Site 0) (X : Finset (F.Site 0))
    (h1 : ∀ x, G x ≠ 0 → x ∈ X) (h2 : ∀ x, G x ≠ 0 → x - e ∈ X) :
    ∑ x ∈ X, G (x + e) = ∑ x ∈ X, G x := by
  have a : ∑ x ∈ X, G x = ∑ᶠ x, G x :=
    (finsum_eq_sum_of_support_subset G (s := X) fun x hx => h1 x hx).symm
  have b : ∑ x ∈ X, G (x + e) = ∑ᶠ x, G (x + e) := by
    refine (finsum_eq_sum_of_support_subset (fun x => G (x + e)) (s := X) fun x hx => ?_).symm
    have := h2 (x + e) hx
    simpa using this
  have c : ∑ᶠ x, G (x + e) = ∑ᶠ x, G x := finsum_comp_equiv (Equiv.addRight e)
  rw [a, b, c]
theorem mem_sitesOfCells_of_supNorm (h : ComparisonSetup S r q) (y : F.Site 0)
    (hy : supNorm (intCoords y) ≤ (r - 1) * cellSide F) : y ∈ sitesOfCells S 0 := by
  have hr : 1 ≤ r := by
    have := h.five_le_scale
    have := h.scale_le_radius
    omega
  refine (LumpContours.BlockLevels.mem_sitesOfCells_iff (Nat.zero_le _) h.odd_blockSide).2 ?_
  have := enclosingCell_mem_of_coords (j := 0) h.odd_blockSide (Nat.zero_le _) h.box_mem (intCoords y) (fun i => by
    have h1 := natAbs_le_supNorm (intCoords y) i
    have h2 : (intCoords y i).natAbs ≤ (r - 1) * cellSide F := h1.trans hy
    rw [Int.abs_eq_natAbs]
    have h3 : ((intCoords y i).natAbs : ℤ) ≤ (((r - 1) * cellSide F : ℕ) : ℤ) := by exact_mod_cast h2
    have e : (((r - 1) * cellSide F : ℕ) : ℤ) = ((r : ℤ) - 1) * (F.blockSide : ℤ) ^ (F.top - 0) := by
      push_cast [Nat.cast_sub hr, cellSide]
      simp
    rw [e] at h3
    exact h3)
  rwa [siteOfCoords_intCoords] at this
def orderedPlanes : Finset (Fin 4 × Fin 4) := Finset.univ.filter fun π => π.1 < π.2
theorem mem_innerPlaquettes_of_supNorm (h : ComparisonSetup S r q) (x : F.Site 0) {π : Fin 4 × Fin 4}
    (hπ : π ∈ orderedPlanes)
    (hx : supNorm (intCoords x) + 2 ≤ (r - 1) * cellSide F) : (x, π) ∈ innerPlaquettes S 0 := by
  have h1 := supNorm_intCoords_add_unitStep (h.readsBack_one 0) x π.1
  have h2 := supNorm_intCoords_add_unitStep (h.readsBack_one 0) x π.2
  have h3 := supNorm_intCoords_add_unitStep (h.readsBack_one 0) (x + unitStep 0 π.1) π.2
  have hlt : π.1 < π.2 := (Finset.mem_filter.1 hπ).2
  simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  refine ⟨mem_sitesOfCells_of_supNorm h x (by omega), hlt, fun y hy => ?_⟩
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact mem_sitesOfCells_of_supNorm h _ (by omega)
  · exact mem_sitesOfCells_of_supNorm h _ (by omega)
  · exact mem_sitesOfCells_of_supNorm h _ (by omega)
  · exact mem_sitesOfCells_of_supNorm h _ (by omega)
theorem untransportedCurl_eq_zero (g : F.Site 0 → Fin 4 → imaginaryQuaternions) (p : F.Site 0 × Fin 4 × Fin 4)
    (h0 : ∀ i, g p.1 i = 0) (h1 : ∀ i, g (p.1 + unitStep 0 p.2.1) i = 0)
    (h2 : ∀ i, g (p.1 + unitStep 0 p.2.2) i = 0) : untransportedCurl g p = 0 := by
  simp [untransportedCurl, h0, h1, h2]
theorem sum_inner_candidate_curl_eq_zero (h : ComparisonSetup S r q) (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (hA : ∀ μ ν, A μ ν = - A ν μ)
    (g : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (hg : ∀ x i, g x i ≠ 0 → supNorm (intCoords x) ≤ 5 * q * cellSide F) :
    ∑ p ∈ innerPlaquettes S 0, inner ℝ (untransportedCurl (candidateForm F q A) p : ℍ[ℝ])
      (untransportedCurl g p : ℍ[ℝ]) = 0 := by
  classical
  have hN := h.cellSide_pos
  have hq := h.five_le_scale
  have hr := h.scale_le_radius
  set ρ := 5 * q * cellSide F + 2 with hρ
  have h7 := outer_zone_le h
  have hroom : ReadsBack F 0 ρ := (h.readsBack 0).mono (by
    have e : F.blockSide ^ (F.top - 0) = cellSide F := by simp [cellSide]
    rw [e]
    have : 5 * q * cellSide F ≤ 7 * q * cellSide F := Nat.mul_le_mul_right _ (by omega)
    omega)
  have hfar : ∀ p : F.Site 0 × Fin 4 × Fin 4, p.1 ∉ coordBall F ρ → untransportedCurl g p = 0 := by
    intro p hp
    have hs : ρ < supNorm (intCoords p.1) := by
      by_contra hc
      exact hp ((mem_coordBall hroom).2 (by omega))
    have a1 := supNorm_intCoords_le_add_unitStep (h.readsBack_one 0) p.1 p.2.1
    have a2 := supNorm_intCoords_le_add_unitStep (h.readsBack_one 0) p.1 p.2.2
    refine untransportedCurl_eq_zero g p (fun i => ?_) (fun i => ?_) (fun i => ?_)
    · by_contra hc
      have := hg _ _ hc
      omega
    · by_contra hc
      have := hg _ _ hc
      omega
    · by_contra hc
      have := hg _ _ hc
      omega
  have hsite : (r - 1) * cellSide F ≥ ρ + 2 := by
    have e1 : (5 * q + 4) * cellSide F ≤ (r - 1) * cellSide F := Nat.mul_le_mul_right _ (by omega)
    have e2 : 5 * q * cellSide F + 4 ≤ (5 * q + 4) * cellSide F := by nlinarith
    omega
  have hsub : coordBall F ρ ×ˢ orderedPlanes ⊆ innerPlaquettes S 0 := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
    have := (mem_coordBall hroom).1 h1
    exact mem_innerPlaquettes_of_supNorm h p.1 h2 (by omega)
  have hz : ∀ p ∈ innerPlaquettes S 0, p ∉ coordBall F ρ ×ˢ orderedPlanes →
      inner ℝ (untransportedCurl (candidateForm F q A) p : ℍ[ℝ]) (untransportedCurl g p : ℍ[ℝ]) = 0 := by
    intro p hp hn
    have hplane : p.2 ∈ orderedPlanes := Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hp).2.1⟩
    have h1 : p.1 ∉ coordBall F ρ := fun h1 => hn (Finset.mem_product.2 ⟨h1, hplane⟩)
    rw [hfar p h1]
    simp
  rw [← Finset.sum_subset hsub hz, Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_eq_zero fun π _ => ?_
  have hval : ∀ x ∈ coordBall F ρ, inner ℝ (untransportedCurl (candidateForm F q A) (x, π) : ℍ[ℝ])
        (untransportedCurl g (x, π) : ℍ[ℝ]) =
      inner ℝ (((1 / (cellSide F : ℝ) ^ 2) • A π.1 π.2 : imaginaryQuaternions) : ℍ[ℝ])
        (untransportedCurl g (x, π) : ℍ[ℝ]) := by
    intro x hx
    by_cases hs : supNorm (intCoords x) + 1 ≤ 6 * q * cellSide F
    · rw [show ((x, π) : F.Site 0 × Fin 4 × Fin 4) = (x, π.1, π.2) from rfl,
        untransportedCurl_candidate_inner h A hA x π.1 π.2 hs]
    · have hs' : ρ < supNorm (intCoords x) + 0 := by
        have : (5 * q + 1) * cellSide F ≤ 6 * q * cellSide F := Nat.mul_le_mul_right _ (by omega)
        nlinarith
      have : x ∉ coordBall F ρ := fun h1 => by
        have := (mem_coordBall hroom).1 h1
        omega
      exact absurd hx this
  rw [Finset.sum_congr rfl hval, ← inner_sum]
  have hsum : ∑ x ∈ coordBall F ρ, (untransportedCurl g (x, π) : ℍ[ℝ]) = 0 := by
    rw [← Submodule.coe_sum]
    have e : ∑ x ∈ coordBall F ρ, untransportedCurl g (x, π) = 0 := by
      simp only [untransportedCurl, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      have hA1 : ∀ i, ∀ x, g x i ≠ 0 → x ∈ coordBall F ρ := fun i x hx =>
        (mem_coordBall hroom).2 (by have := hg x i hx; omega)
      have hA2 : ∀ (i k : Fin 4), ∀ x, g x i ≠ 0 → x - unitStep 0 k ∈ coordBall F ρ := fun i k x hx =>
        (mem_coordBall hroom).2 (by
          have := hg x i hx
          have := supNorm_intCoords_sub_unitStep (h.readsBack_one 0) x k
          omega)
      rw [sum_translate (fun x => g x π.2) _ _ (hA1 π.2) (hA2 π.2 π.1),
        sum_translate (fun x => g x π.1) _ _ (hA1 π.1) (hA2 π.1 π.2)]
      abel
    rw [e]
    rfl
  rw [hsum, inner_zero_right]
end TestCurl
section Fibres
variable {F : BlockFrame} {S : Finset F.Cell} {r q : ℕ}
theorem natAbs_valMinAbs_intCast_le (p : ℕ) (a : ℤ) : (((a : ZMod p)).valMinAbs).natAbs ≤ a.natAbs := by apply _root_.YangMills.Construction.BlockWeights.natAbs_valMinAbs_intCast_le <;> assumption
theorem supNorm_intCoords_siteOfCoords_le {j : ℕ} (a : Fin 4 → ℤ) :
    supNorm (intCoords (siteOfCoords j a : F.Site j)) ≤ supNorm a := by
  refine Finset.sup_le fun i _ => ?_
  exact (natAbs_valMinAbs_intCast_le _ _).trans (natAbs_le_supNorm a i)
theorem supNorm_le_cellSide_mul (h : ComparisonSetup S r q) (x : F.Site 0) :
    supNorm (intCoords x) ≤ cellSide F * (supNorm (intCoords (enclosingCell x)) + 1) := by
  have hx : x ∈ sitesOfCells {enclosingCell x} 0 :=
    (LumpContours.BlockLevels.mem_sitesOfCells_iff (Nat.zero_le _) h.odd_blockSide).2 (Finset.mem_singleton_self _)
  obtain ⟨y, hy, o, ho, e⟩ := mem_sitesOfCells.1 hx
  have hyc : y = enclosingCell x := Finset.mem_singleton.1 hy
  set w := intCoords y with hw
  have hcen : cellCentre 0 y = siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ (F.top - 0) * w i) := by
    have e1 : y = 0 + siteOfCoords F.top w := by rw [zero_add, hw, siteOfCoords_intCoords]
    have e2 := cellCentre_add (F := F) 0 (Nat.zero_le _) 0 w
    rw [← e1] at e2
    rw [e2]
    have e3 : cellCentre 0 (0 : F.Cell) = 0 := by
      funext i
      simp [cellCentre, siteOfCoords, siteCoords]
    rw [e3, zero_add]
  have hxe : x = siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ (F.top - 0) * w i + o i) := by
    rw [e, hcen, ← siteOfCoords_add]
    rfl
  have hb := supNorm_intCoords_siteOfCoords_le (F := F) (j := 0)
    (fun i => (F.blockSide : ℤ) ^ (F.top - 0) * w i + o i)
  rw [← hxe] at hb
  refine hb.trans ?_
  rw [← hyc, ← hw]
  refine Finset.sup_le fun i _ => ?_
  have h1 := natAbs_le_supNorm w i
  have hc := (mem_centredCube_iff _ o).1 ho i
  have hN := h.cellSide_pos
  have hM : ((F.blockSide ^ (F.top - 0) : ℕ) : ℤ) = (cellSide F : ℤ) := by simp [cellSide]
  have ho2 : (o i).natAbs ≤ cellSide F := by
    have h2 : |o i| ≤ (cellSide F : ℤ) := by
      rw [abs_le, ← hM]
      obtain ⟨k1, k2⟩ := hc
      have hpos : (0 : ℤ) < ((F.blockSide ^ (F.top - 0) : ℕ) : ℤ) := by rw [hM]; exact_mod_cast hN
      constructor <;> omega
    rw [Int.abs_eq_natAbs] at h2
    exact_mod_cast h2
  have h3 : ((F.blockSide : ℤ) ^ (F.top - 0) * w i + o i).natAbs ≤ cellSide F * (w i).natAbs + (o i).natAbs := by
    refine (Int.natAbs_add_le _ _).trans ?_
    rw [Int.natAbs_mul, Int.natAbs_pow]
    simp [cellSide]
  calc _ ≤ cellSide F * (w i).natAbs + (o i).natAbs := h3
    _ ≤ cellSide F * supNorm w + cellSide F := by
      have := Nat.mul_le_mul_left (cellSide F) h1
      omega
    _ = _ := by ring
open Classical in
def plaquettesAtCell (S : Finset F.Cell) (z : F.Cell) : Finset (F.Site 0 × Fin 4 × Fin 4) :=
  (innerPlaquettes S 0).filter fun p => enclosingCell p.1 = z
theorem card_plaquettesAtCell_le (h : ComparisonSetup S r q) (z : F.Cell) :
    ((plaquettesAtCell S z).card : ℝ) ≤ 16 * (cellSide F : ℝ) ^ 4 := by
  classical
  have hsub : plaquettesAtCell S z ⊆ sitesOfCells {z} 0 ×ˢ (Finset.univ : Finset (Fin 4 × Fin 4)) := by
    intro p hp
    refine Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩
    refine (LumpContours.BlockLevels.mem_sitesOfCells_iff (Nat.zero_le _) h.odd_blockSide).2 ?_
    rw [(Finset.mem_filter.1 hp).2]
    exact Finset.mem_singleton_self _
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_product] at h1
  have h2 := card_sitesOfCells_le h.odd_blockSide ({z} : Finset F.Cell) 0
  simp only [Finset.card_singleton, one_mul, Nat.sub_zero] at h2
  have h3 : (Finset.univ : Finset (Fin 4 × Fin 4)).card = 16 := by simp
  rw [h3] at h1
  have h4 : (plaquettesAtCell S z).card ≤ cellSide F ^ 4 * 16 := h1.trans (Nat.mul_le_mul_right _ h2)
  have h5 : ((plaquettesAtCell S z).card : ℝ) ≤ ((cellSide F ^ 4 * 16 : ℕ) : ℝ) := by exact_mod_cast h4
  push_cast at h5
  push_cast [cellSide]
  linarith
theorem sum_sq_untransportedCurl_le (hRef : flatTopReferenceStatement) (h : ComparisonSetup S r q)
    (D : ChainChart F) {z : F.Cell}
    (hz : z ∈ S) :
    ∑ p ∈ plaquettesAtCell S z, ‖untransportedCurl D.fine p‖ ^ 2 ≤
      localNorm S (referenceFieldChain S flatTopField) D (unitWeights F) z ^ 2 := by
  classical
  unfold localNorm
  rw [Real.sq_sqrt (localNormSq_nonneg _ _ _ _ _)]
  have hsub : plaquettesAtCell S z ⊆ plaquettesOver S (cellBall S z 3) 0 := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
    refine Finset.mem_filter.2 ⟨h1, ?_⟩
    rw [h2]
    exact Finset.mem_filter.2 ⟨hz, by simp [cellSupDist_self]⟩
  have e : ∑ p ∈ plaquettesAtCell S z, ‖untransportedCurl D.fine p‖ ^ 2 =
      ∑ p ∈ plaquettesAtCell S z,
        (unitWeights F 0 p.1 * ‖linearizedCurl (referenceFieldChain S flatTopField 0) D.fine p‖) ^ 2 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [linearizedCurl_eq_untransported hRef h D.fine (Finset.mem_filter.1 hp).1]
    simp only [unitWeights, one_mul]
    rfl
  rw [e]
  unfold localNormSq
  have t1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun p =>
    (unitWeights F 0 p.1 * ‖linearizedCurl (referenceFieldChain S flatTopField 0) D.fine p‖) ^ 2)
    (fun _ _ _ => sq_nonneg _)
  have t2 : 0 ≤ Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (unitWeights F 0 b.1 * ‖D.fine b.1 b.2‖) ^ 4) :=
    Real.sqrt_nonneg _
  have t3 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (unitWeights F (j + 1) c.1 * ‖D.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith
theorem sum_pow_four_le_localNorm (R : F.FieldChain) (D : ChainChart F) (z : F.Cell) :
    ∑ b ∈ bondsOver S (cellBall S z 3) 0, ‖D.fine b.1 b.2‖ ^ 4 ≤ localNorm S R D (unitWeights F) z ^ 4 := by
  have hn := localNormSq_nonneg S (cellBall S z 3) R D (unitWeights F)
  have e : localNorm S R D (unitWeights F) z ^ 4 = (localNormSq S (cellBall S z 3) R D (unitWeights F)) ^ 2 := by
    unfold localNorm
    rw [show ∀ t : ℝ, t ^ 4 = (t ^ 2) ^ 2 from fun t => by ring, Real.sq_sqrt hn]
  rw [e]
  set X := ∑ b ∈ bondsOver S (cellBall S z 3) 0, ‖D.fine b.1 b.2‖ ^ 4 with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 4
  have h1 : Real.sqrt X ≤ localNormSq S (cellBall S z 3) R D (unitWeights F) := by
    unfold localNormSq
    have t0 : ∑ b ∈ bondsOver S (cellBall S z 3) 0, (unitWeights F 0 b.1 * ‖D.fine b.1 b.2‖) ^ 4 = X := by
      simp only [unitWeights, one_mul, hX]
    rw [t0]
    have t1 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0,
        (unitWeights F 0 p.1 * ‖linearizedCurl (R 0) D.fine p‖) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have t3 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (unitWeights F (j + 1) c.1 * ‖D.coarse j c.1 c.2‖) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  calc X = Real.sqrt X ^ 2 := (Real.sq_sqrt hX0).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
end Fibres
section FibreSums
variable {F : BlockFrame} {S : Finset F.Cell} {r q : ℕ}
theorem sum_norm_untransportedCurl_le (hRef : flatTopReferenceStatement) (h : ComparisonSetup S r q)
    (D : ChainChart F) {z : F.Cell}
    (hz : z ∈ S) :
    ∑ p ∈ plaquettesAtCell S z, ‖untransportedCurl D.fine p‖ ≤
      4 * (cellSide F : ℝ) ^ 2 * localNorm S (referenceFieldChain S flatTopField) D (unitWeights F) z := by
  set ν := localNorm S (referenceFieldChain S flatTopField) D (unitWeights F) z with hν
  have hν0 : 0 ≤ ν := Real.sqrt_nonneg _
  have hN := h.cellSide_pos_real
  have h1 : (∑ p ∈ plaquettesAtCell S z, ‖untransportedCurl D.fine p‖) ^ 2 ≤
      ((plaquettesAtCell S z).card : ℝ) * ∑ p ∈ plaquettesAtCell S z, ‖untransportedCurl D.fine p‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h2 := sum_sq_untransportedCurl_le hRef h D hz
  have h3 := card_plaquettesAtCell_le h z
  have hs : 0 ≤ ∑ p ∈ plaquettesAtCell S z, ‖untransportedCurl D.fine p‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h4 : (∑ p ∈ plaquettesAtCell S z, ‖untransportedCurl D.fine p‖) ^ 2 ≤ (4 * (cellSide F : ℝ) ^ 2 * ν) ^ 2 := by
    calc _ ≤ ((plaquettesAtCell S z).card : ℝ) * ∑ p ∈ plaquettesAtCell S z, ‖untransportedCurl D.fine p‖ ^ 2 := h1
      _ ≤ (16 * (cellSide F : ℝ) ^ 4) * ν ^ 2 := mul_le_mul h3 h2 hs (by positivity)
      _ = _ := by ring
  have h0 : 0 ≤ ∑ p ∈ plaquettesAtCell S z, ‖untransportedCurl D.fine p‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  exact (pow_le_pow_iff_left₀ h0 (by positivity) (by norm_num)).1 h4
theorem sum_norm_shifted_bond_le (h : ComparisonSetup S r q) (R : F.FieldChain) (D : ChainChart F) (z : F.Cell)
    (i j : Fin 4 × Fin 4 → Fin 4)
    (hb : ∀ p ∈ plaquettesAtCell S z, ((p.1 + unitStep 0 (i p.2), j p.2) : F.Site 0 × Fin 4) ∈
      bondsOver S (cellBall S z 3) 0) :
    ∑ p ∈ plaquettesAtCell S z, ‖D.fine (p.1 + unitStep 0 (i p.2)) (j p.2)‖ ≤
      16 * (cellSide F : ℝ) ^ 3 * localNorm S R D (unitWeights F) z := by
  classical
  set ν := localNorm S R D (unitWeights F) z with hν
  have hν0 : 0 ≤ ν := Real.sqrt_nonneg _
  have hN := h.cellSide_pos_real
  set a : F.Site 0 × Fin 4 × Fin 4 → ℝ := fun p => ‖D.fine (p.1 + unitStep 0 (i p.2)) (j p.2)‖ with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => norm_nonneg _
  set Q := ∑ b ∈ bondsOver S (cellBall S z 3) 0, ‖D.fine b.1 b.2‖ ^ 4 with hQ
  have hQν : Q ≤ ν ^ 4 := sum_pow_four_le_localNorm R D z
  have hone : ∀ π : Fin 4 × Fin 4, ∑ p ∈ (plaquettesAtCell S z).filter (fun p => p.2 = π), a p ^ 4 ≤ Q := by
    intro π
    have hinj : Set.InjOn (fun p : F.Site 0 × Fin 4 × Fin 4 =>
        ((p.1 + unitStep 0 (i p.2), j p.2) : F.Site 0 × Fin 4))
        ((plaquettesAtCell S z).filter (fun p => p.2 = π) : Finset _) := by
      intro p hp p' hp' e
      have e1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
      have e2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hp')).2
      have e3 : p.1 + unitStep 0 (i p.2) = p'.1 + unitStep 0 (i p'.2) := congrArg Prod.fst e
      rw [e1, e2] at e3
      exact Prod.ext (add_right_cancel e3) (e1.trans e2.symm)
    have himg := Finset.sum_image (f := fun b : F.Site 0 × Fin 4 => ‖D.fine b.1 b.2‖ ^ 4) hinj
    simp only at himg
    have e : ∑ p ∈ (plaquettesAtCell S z).filter (fun p => p.2 = π), a p ^ 4 =
        ∑ b ∈ ((plaquettesAtCell S z).filter (fun p => p.2 = π)).image (fun p : F.Site 0 × Fin 4 × Fin 4 =>
          ((p.1 + unitStep 0 (i p.2), j p.2) : F.Site 0 × Fin 4)), ‖D.fine b.1 b.2‖ ^ 4 := himg.symm
    rw [e]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => pow_nonneg (norm_nonneg _) 4
    intro b hbm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hbm
    exact hb p (Finset.mem_filter.1 hp).1
  have hfour : ∑ p ∈ plaquettesAtCell S z, a p ^ 4 ≤ 16 * Q := by
    rw [← Finset.sum_fiberwise (plaquettesAtCell S z) (fun p => p.2) (fun p => a p ^ 4)]
    calc _ ≤ ∑ _π : Fin 4 × Fin 4, Q := Finset.sum_le_sum fun π _ => hone π
      _ = 16 * Q := by simp
  set T := ∑ p ∈ plaquettesAtCell S z, a p with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun p _ => ha0 p
  set n : ℝ := ((plaquettesAtCell S z).card : ℝ) with hn
  have hn0 : 0 ≤ n := by positivity
  have hn1 : n ≤ 16 * (cellSide F : ℝ) ^ 4 := card_plaquettesAtCell_le h z
  have h1 : T ^ 2 ≤ n * ∑ p ∈ plaquettesAtCell S z, a p ^ 2 := sq_sum_le_card_mul_sum_sq
  have h2 : (∑ p ∈ plaquettesAtCell S z, a p ^ 2) ^ 2 ≤ n * ∑ p ∈ plaquettesAtCell S z, (a p ^ 2) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have e4 : ∑ p ∈ plaquettesAtCell S z, (a p ^ 2) ^ 2 = ∑ p ∈ plaquettesAtCell S z, a p ^ 4 :=
    Finset.sum_congr rfl fun p _ => by ring
  rw [e4] at h2
  have h3 : T ^ 4 ≤ n ^ 3 * (16 * Q) := by
    have s1 : (T ^ 2) ^ 2 ≤ (n * ∑ p ∈ plaquettesAtCell S z, a p ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have s2 : (n * ∑ p ∈ plaquettesAtCell S z, a p ^ 2) ^ 2 = n ^ 2 * (∑ p ∈ plaquettesAtCell S z, a p ^ 2) ^ 2 := by
      ring
    have s3 : n ^ 2 * (∑ p ∈ plaquettesAtCell S z, a p ^ 2) ^ 2 ≤ n ^ 2 * (n * (16 * Q)) := by
      refine mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity)
      exact mul_le_mul_of_nonneg_left hfour hn0
    calc T ^ 4 = (T ^ 2) ^ 2 := by ring
      _ ≤ _ := s1
      _ = _ := s2
      _ ≤ _ := s3
      _ = _ := by ring
  have h4 : T ^ 4 ≤ (16 * (cellSide F : ℝ) ^ 3 * ν) ^ 4 := by
    refine h3.trans ?_
    have s1 : n ^ 3 ≤ (16 * (cellSide F : ℝ) ^ 4) ^ 3 := pow_le_pow_left₀ hn0 hn1 3
    have s2 : 16 * Q ≤ 16 * ν ^ 4 := by linarith
    calc n ^ 3 * (16 * Q) ≤ (16 * (cellSide F : ℝ) ^ 4) ^ 3 * (16 * ν ^ 4) :=
          mul_le_mul s1 s2 (by positivity) (by positivity)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ hT0 (by positivity) (by norm_num)).1 h4
theorem cellSupDist_add_unitStep_le (h : ComparisonSetup S r q) (z : F.Cell) (i : Fin 4) :
    cellSupDist z (z + unitStep F.top i) ≤ 1 := by
  unfold cellSupDist
  refine Finset.sup_le fun k _ => ?_
  have e : z k - (z + unitStep F.top i : F.Cell) k = (-unitStep F.top i : F.Cell) k := by
    simp
  rw [e]
  exact natAbs_valMinAbs_neg_unitStep_le (h.readsBack_one F.top) i k
theorem cellSupDist_enclosingCell_step_le (h : ComparisonSetup S r q) (x : F.Site 0) (i : Fin 4) :
    cellSupDist (enclosingCell x) (enclosingCell (x + unitStep 0 i)) ≤ 1 := by
  rcases LumpContours.BlockLevels.enclosingCell_add_unitStep (Nat.zero_le _) h.odd_blockSide.pos x i with e | e
  · rw [e, cellSupDist_self]
    omega
  · rw [e]
    exact cellSupDist_add_unitStep_le h _ i
theorem shifted_mem_bondsOver (h : ComparisonSetup S r q) {z : F.Cell} {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ plaquettesAtCell S z)
    {i j : Fin 4} (hi : i = p.2.1 ∧ j = p.2.2 ∨ i = p.2.2 ∧ j = p.2.1) :
    ((p.1 + unitStep 0 i, j) : F.Site 0 × Fin 4) ∈ bondsOver S (cellBall S z 3) 0 := by
  classical
  obtain ⟨hpl, hz⟩ := Finset.mem_filter.1 hp
  have hc : plaquetteCorners p ⊆ sitesOfCells S 0 := (Finset.mem_filter.1 hpl).2.2
  have m1 : p.1 + unitStep 0 i ∈ plaquetteCorners p := by
    rcases hi with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [plaquetteCorners]
  have m2 : p.1 + unitStep 0 i + unitStep 0 j ∈ plaquetteCorners p := by
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [plaquetteCorners]
    · rw [add_right_comm]
      simp [plaquetteCorners]
  have hcell := LumpContours.BlockLevels.enclosingCell_mem_of_mem_sitesOfCells (Nat.zero_le _) h.odd_blockSide
    (hc m1)
  refine Finset.mem_filter.2 ⟨?_, Finset.mem_filter.2 ⟨hcell, ?_⟩⟩
  · simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hc m1, hc m2⟩
  · have := cellSupDist_enclosingCell_step_le h p.1 i
    rw [hz] at this
    show cellSupDist z (enclosingCell (p.1 + unitStep 0 i)) ≤ 3
    omega
end FibreSums
section OuterPart
variable {F : BlockFrame} {S : Finset F.Cell} {r q : ℕ}
def innerCutForm (F : BlockFrame) (q : ℕ) (g : F.Site 0 → Fin 4 → imaginaryQuaternions) :
    F.Site 0 → Fin 4 → imaginaryQuaternions :=
  fun x i => testCutoff q (cellSide F) (intCoords x) • g x i
def outerCutForm (F : BlockFrame) (q : ℕ) (g : F.Site 0 → Fin 4 → imaginaryQuaternions) :
    F.Site 0 → Fin 4 → imaginaryQuaternions :=
  fun x i => (1 - testCutoff q (cellSide F) (intCoords x)) • g x i
theorem supNorm_le_of_innerCutForm_ne_zero (h : ComparisonSetup S r q) (g : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (x : F.Site 0) (i : Fin 4)
    (hx : innerCutForm F q g x i ≠ 0) : supNorm (intCoords x) ≤ 5 * q * cellSide F := by
  by_contra hc
  apply hx
  have hle : (5 * q * cellSide F : ℝ) ≤ supNorm (intCoords x) := by
    have : 5 * q * cellSide F ≤ supNorm (intCoords x) := by omega
    exact_mod_cast this
  unfold innerCutForm testCutoff
  rw [cutoffRamp_eq_zero_of_ge h.test_gap hle, zero_smul]
theorem outerCutForm_eq_zero (h : ComparisonSetup S r q) (g : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (x : F.Site 0) (i : Fin 4)
    (hx : supNorm (intCoords x) ≤ 4 * q * cellSide F) : outerCutForm F q g x i = 0 := by
  have hle : (supNorm (intCoords x) : ℝ) ≤ 4 * q * cellSide F := by exact_mod_cast hx
  unfold outerCutForm testCutoff
  rw [cutoffRamp_eq_one_of_le h.test_gap hle]
  simp
theorem untransportedCurl_eq_inner_add_outer (g : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (p : F.Site 0 × Fin 4 × Fin 4) :
    untransportedCurl g p = untransportedCurl (innerCutForm F q g) p + untransportedCurl (outerCutForm F q g) p := by
  simp only [untransportedCurl, innerCutForm, outerCutForm]
  module
theorem abs_testCutoff_sub_unitStep_le (h : ComparisonSetup S r q) (x : F.Site 0) (i : Fin 4) :
    |testCutoff q (cellSide F) (intCoords x) - testCutoff q (cellSide F) (intCoords (x + unitStep 0 i))| ≤
      1 / (q * cellSide F) := by
  unfold testCutoff
  refine (abs_cutoffRamp_sub_le h.test_gap _ _).trans ?_
  have hN := h.cellSide_pos_real
  have hq : (0 : ℝ) < q := by
    have := h.five_le_scale
    exact_mod_cast (by omega : 0 < q)
  have e : (5 * q * cellSide F : ℝ) - 4 * q * cellSide F = q * cellSide F := by ring
  rw [e]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have a1 : (supNorm (intCoords (x + unitStep 0 i)) : ℝ) ≤ supNorm (intCoords x) + 1 := by
    exact_mod_cast supNorm_intCoords_add_unitStep (h.readsBack_one 0) x i
  have a2 : (supNorm (intCoords x) : ℝ) ≤ supNorm (intCoords (x + unitStep 0 i)) + 1 := by
    exact_mod_cast supNorm_intCoords_le_add_unitStep (h.readsBack_one 0) x i
  rw [abs_le]
  constructor <;> linarith
theorem norm_untransportedCurl_outer_le (h : ComparisonSetup S r q) (g : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (p : F.Site 0 × Fin 4 × Fin 4) :
    ‖untransportedCurl (outerCutForm F q g) p‖ ≤ ‖untransportedCurl g p‖ + 1 / (q * cellSide F) *
      (‖g (p.1 + unitStep 0 p.2.1) p.2.2‖ + ‖g (p.1 + unitStep 0 p.2.2) p.2.1‖) := by
  obtain ⟨x, μ, ν⟩ := p
  simp only
  set ψ₀ := testCutoff q (cellSide F) (intCoords x) with h0
  set ψ₁ := testCutoff q (cellSide F) (intCoords (x + unitStep 0 μ)) with h1
  set ψ₂ := testCutoff q (cellSide F) (intCoords (x + unitStep 0 ν)) with h2
  have e : untransportedCurl (outerCutForm F q g) (x, μ, ν) = (1 - ψ₀) • untransportedCurl g (x, μ, ν) +
      (ψ₀ - ψ₁) • g (x + unitStep 0 μ) ν - (ψ₀ - ψ₂) • g (x + unitStep 0 ν) μ := by
    simp only [untransportedCurl, outerCutForm, ← h0, ← h1, ← h2]
    module
  rw [e]
  have c0 : |1 - ψ₀| ≤ 1 := by
    have a1 : 0 ≤ ψ₀ := cutoffRamp_nonneg _ _ _
    have a2 : ψ₀ ≤ 1 := cutoffRamp_le_one _ _ _
    rw [abs_le]
    constructor <;> linarith
  have c1 := abs_testCutoff_sub_unitStep_le h x μ
  have c2 := abs_testCutoff_sub_unitStep_le h x ν
  refine (norm_sub_le _ _).trans ?_
  have t0 : ‖(1 - ψ₀) • untransportedCurl g (x, μ, ν)‖ ≤ ‖untransportedCurl g (x, μ, ν)‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc _ ≤ 1 * ‖untransportedCurl g (x, μ, ν)‖ := mul_le_mul_of_nonneg_right c0 (norm_nonneg _)
      _ = _ := one_mul _
  have t1 : ‖(ψ₀ - ψ₁) • g (x + unitStep 0 μ) ν‖ ≤ 1 / (q * cellSide F) * ‖g (x + unitStep 0 μ) ν‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right c1 (norm_nonneg _)
  have t2 : ‖(ψ₀ - ψ₂) • g (x + unitStep 0 ν) μ‖ ≤ 1 / (q * cellSide F) * ‖g (x + unitStep 0 ν) μ‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right c2 (norm_nonneg _)
  have t3 := norm_add_le ((1 - ψ₀) • untransportedCurl g (x, μ, ν)) ((ψ₀ - ψ₁) • g (x + unitStep 0 μ) ν)
  rw [mul_add]
  linarith
theorem norm_imaginary_coe (w : imaginaryQuaternions) : ‖(w : ℍ[ℝ])‖ = ‖w‖ := rfl
theorem sum_abs_inner_outer_le (hRef : flatTopReferenceStatement) (h : ComparisonSetup S r q)
    (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (hA : ∀ μ ν, A μ ν = - A ν μ) (D : ChainChart F) {z : F.Cell} (hz : z ∈ S) :
    ∑ p ∈ plaquettesAtCell S z, |inner ℝ (untransportedCurl (candidateForm F q A) p : ℍ[ℝ])
        (untransportedCurl (outerCutForm F q D.fine) p : ℍ[ℝ])| ≤
      99 * curvatureL1 A * localNorm S (referenceFieldChain S flatTopField) D (unitWeights F) z := by
  set ν := localNorm S (referenceFieldChain S flatTopField) D (unitWeights F) z with hν
  have hν0 : 0 ≤ ν := Real.sqrt_nonneg _
  have hN := h.cellSide_pos_real
  have hS := curvatureL1_nonneg A
  have hq5 : (5 : ℝ) ≤ q := by exact_mod_cast h.five_le_scale
  have hq0 : (0 : ℝ) < q := by linarith
  set c : ℝ := 9 / (cellSide F : ℝ) ^ 2 * curvatureL1 A with hc
  have hc0 : 0 ≤ c := by positivity
  have hterm : ∀ p ∈ plaquettesAtCell S z,
      |inner ℝ (untransportedCurl (candidateForm F q A) p : ℍ[ℝ])
          (untransportedCurl (outerCutForm F q D.fine) p : ℍ[ℝ])| ≤
        c * (‖untransportedCurl D.fine p‖ + 1 / (q * cellSide F) *
          (‖D.fine (p.1 + unitStep 0 p.2.1) p.2.2‖ + ‖D.fine (p.1 + unitStep 0 p.2.2) p.2.1‖)) := by
    intro p _
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_imaginary_coe, norm_imaginary_coe]
    exact mul_le_mul (norm_untransportedCurl_candidate_le h A hA p) (norm_untransportedCurl_outer_le h D.fine p)
      (norm_nonneg _) hc0
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
  have s1 := sum_norm_untransportedCurl_le hRef h D hz
  have s2 := sum_norm_shifted_bond_le h (referenceFieldChain S flatTopField) D z (fun π => π.1) (fun π => π.2)
    (fun p hp => shifted_mem_bondsOver h hp (Or.inl ⟨rfl, rfl⟩))
  have s3 := sum_norm_shifted_bond_le h (referenceFieldChain S flatTopField) D z (fun π => π.2) (fun π => π.1)
    (fun p hp => shifted_mem_bondsOver h hp (Or.inr ⟨rfl, rfl⟩))
  rw [← hν] at s1 s2 s3
  have key : ∑ p ∈ plaquettesAtCell S z, ‖untransportedCurl D.fine p‖ + 1 / (q * cellSide F) *
      (∑ p ∈ plaquettesAtCell S z, ‖D.fine (p.1 + unitStep 0 p.2.1) p.2.2‖ +
        ∑ p ∈ plaquettesAtCell S z, ‖D.fine (p.1 + unitStep 0 p.2.2) p.2.1‖) ≤
      4 * (cellSide F : ℝ) ^ 2 * ν + 1 / (q * cellSide F) * (32 * (cellSide F : ℝ) ^ 3 * ν) := by
    refine add_le_add s1 (mul_le_mul_of_nonneg_left ?_ (by positivity))
    linarith
  calc c * _ ≤ c * (4 * (cellSide F : ℝ) ^ 2 * ν + 1 / (q * cellSide F) * (32 * (cellSide F : ℝ) ^ 3 * ν)) :=
        mul_le_mul_of_nonneg_left key hc0
    _ = 9 * curvatureL1 A * ν * (4 + 32 / q) := by
      rw [hc]
      field_simp
    _ ≤ 9 * curvatureL1 A * ν * 11 := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have : 32 / (q : ℝ) ≤ 7 := by
        rw [div_le_iff₀ hq0]
        linarith
      linarith
    _ = _ := by ring
open Classical in
def comparisonShell (S : Finset F.Cell) (q r : ℕ) : Finset F.Cell :=
  S.filter fun z => 4 * q - 2 ≤ supNorm (intCoords z) ∧ supNorm (intCoords z) ≤ r + 3
theorem inner_outer_eq_zero_off_shell (h : ComparisonSetup S r q) (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (g : F.Site 0 → Fin 4 → imaginaryQuaternions)
    {z : F.Cell} (hz : z ∈ S) (hn : z ∉ comparisonShell S q r) {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ plaquettesAtCell S z) :
    inner ℝ (untransportedCurl (candidateForm F q A) p : ℍ[ℝ]) (untransportedCurl (outerCutForm F q g) p : ℍ[ℝ]) = 0 := by
  classical
  obtain ⟨x, μ, ν⟩ := p
  have hcell : enclosingCell x = z := (Finset.mem_filter.1 hp).2
  have hN := h.cellSide_pos
  have hq := h.five_le_scale
  have hr := h.scale_le_radius
  by_cases hfar : 7 * q * cellSide F + 2 ≤ supNorm (intCoords x)
  · rw [untransportedCurl_candidate_far h A x μ ν hfar]
    simp
  by_cases hin : supNorm (intCoords x) + 1 ≤ 4 * q * cellSide F
  · have a1 := supNorm_intCoords_add_unitStep (h.readsBack_one 0) x μ
    have a2 := supNorm_intCoords_add_unitStep (h.readsBack_one 0) x ν
    have o0 : ∀ i, outerCutForm F q g x i = 0 := fun i => outerCutForm_eq_zero h g x i (by omega)
    have o1 : ∀ i, outerCutForm F q g (x + unitStep 0 μ) i = 0 := fun i => outerCutForm_eq_zero h g _ i (by omega)
    have o2 : ∀ i, outerCutForm F q g (x + unitStep 0 ν) i = 0 := fun i => outerCutForm_eq_zero h g _ i (by omega)
    have : untransportedCurl (outerCutForm F q g) (x, μ, ν) = 0 := untransportedCurl_eq_zero _ _ o0 o1 o2
    rw [this]
    simp
  exfalso
  apply hn
  have hN3 : 3 ≤ cellSide F := by
    calc 3 ≤ F.blockSide := h.three_le_blockSide
      _ = F.blockSide ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right h.odd_blockSide.pos (by simp [BlockFrame.top])
  have h1 : supNorm (intCoords x) ≤ (7 * q + 1) * cellSide F := by
    have : (7 * q + 1) * cellSide F = 7 * q * cellSide F + cellSide F := by ring
    omega
  have h2 := supNorm_enclosingCell_le h x (t := 7 * q + 1) (by omega) h1
  rw [hcell] at h2
  have h3 := supNorm_le_cellSide_mul h x
  rw [hcell] at h3
  have h4 : 4 * q * cellSide F ≤ cellSide F * (supNorm (intCoords z) + 1) := by omega
  have h5 : 4 * q ≤ supNorm (intCoords z) + 1 := by
    have : cellSide F * (4 * q) ≤ cellSide F * (supNorm (intCoords z) + 1) := by
      calc cellSide F * (4 * q) = 4 * q * cellSide F := by ring
        _ ≤ _ := h4
    exact Nat.le_of_mul_le_mul_left this hN
  exact Finset.mem_filter.2 ⟨hz, by omega, by omega⟩
theorem abs_sum_inner_outer_le (hRef : flatTopReferenceStatement) (h : ComparisonSetup S r q)
    (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (hA : ∀ μ ν, A μ ν = - A ν μ) (D : ChainChart F) :
    |∑ p ∈ innerPlaquettes S 0, inner ℝ (untransportedCurl (candidateForm F q A) p : ℍ[ℝ])
        (untransportedCurl (outerCutForm F q D.fine) p : ℍ[ℝ])| ≤
      99 * curvatureL1 A * ∑ z ∈ comparisonShell S q r,
        localNorm S (referenceFieldChain S flatTopField) D (unitWeights F) z := by
  classical
  have hmaps : ∀ p ∈ innerPlaquettes S 0, enclosingCell p.1 ∈ S := by
    intro p hp
    have hc : plaquetteCorners p ⊆ sitesOfCells S 0 := (Finset.mem_filter.1 hp).2.2
    exact LumpContours.BlockLevels.enclosingCell_mem_of_mem_sitesOfCells (Nat.zero_le _) h.odd_blockSide
      (hc (by simp [plaquetteCorners]))
  have e : ∑ p ∈ innerPlaquettes S 0, inner ℝ (untransportedCurl (candidateForm F q A) p : ℍ[ℝ])
        (untransportedCurl (outerCutForm F q D.fine) p : ℍ[ℝ]) =
      ∑ z ∈ S, ∑ p ∈ plaquettesAtCell S z, inner ℝ (untransportedCurl (candidateForm F q A) p : ℍ[ℝ])
        (untransportedCurl (outerCutForm F q D.fine) p : ℍ[ℝ]) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp [plaquettesAtCell]
  have hsub : comparisonShell S q r ⊆ S := Finset.filter_subset _ _
  rw [e, ← Finset.sum_subset hsub (fun z hz hn => Finset.sum_eq_zero fun p hp =>
    inner_outer_eq_zero_off_shell h A D.fine hz hn hp)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  exact (Finset.abs_sum_le_sum_abs _ _).trans (sum_abs_inner_outer_le hRef h A hA D (hsub hz))
end OuterPart
section Defect
variable {F : BlockFrame} {S : Finset F.Cell} {r q : ℕ}
structure IsPotentialCutoff (r : ℕ) (φ : F.Site F.top → Fin 4 → ℝ) : Prop where
  mem_unit : ∀ y i, 0 ≤ φ y i ∧ φ y i ≤ 1
  eq_one : ∀ y μ, BondWithinRadius (r / 2) (minimalCoords y, μ) → φ y μ = 1
  eq_zero : ∀ y μ, ¬ BondWithinRadius r (minimalCoords y, μ) → φ y μ = 0
def cutoffPotential (φ : F.Site F.top → Fin 4 → ℝ) (A : Fin 4 → Fin 4 → imaginaryQuaternions) :
    F.Site F.top → Fin 4 → imaginaryQuaternions :=
  fun y μ => φ y μ • constantCurvaturePotential A y μ
theorem constantCurvaturePotential_eq_graded (A : Fin 4 → Fin 4 → imaginaryQuaternions) (y : F.Cell) (μ : Fin 4) :
    constantCurvaturePotential A y μ = gradedPotential (1 / 2) A (intCoords y) μ := rfl
theorem bondWithinRadius_of_supNorm {t : ℕ} (y : F.Cell) (μ : Fin 4) (hy : supNorm (intCoords y) + 1 ≤ t) :
    BondWithinRadius t (minimalCoords y, μ) := by
  have e : minimalCoords y = intCoords y := rfl
  rw [e]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h1 := natAbs_le_supNorm (intCoords y) i
    rw [Int.abs_eq_natAbs]
    have : (intCoords y i).natAbs ≤ t := by omega
    exact_mod_cast this
  · have h1 := natAbs_le_supNorm (intCoords y + Pi.single μ 1) i
    have h2 := supNorm_add_single_le (intCoords y) μ
    rw [Int.abs_eq_natAbs]
    have : ((intCoords y + Pi.single μ 1 : Fin 4 → ℤ) i).natAbs ≤ t := by omega
    exact_mod_cast this
theorem not_bondWithinRadius_of_supNorm {t : ℕ} (y : F.Cell) (μ : Fin 4) (hy : t < supNorm (intCoords y)) :
    ¬ BondWithinRadius t (minimalCoords y, μ) := by
  intro hb
  have e : minimalCoords y = intCoords y := rfl
  have h1 := hb.1
  simp only [e] at h1
  have : supNorm (intCoords y) ≤ t := by
    refine Finset.sup_le fun i _ => ?_
    have := h1 i
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  omega
theorem supNorm_le_of_bondWithinRadius {t : ℕ} (y : F.Cell) (μ : Fin 4)
    (hb : BondWithinRadius t (minimalCoords y, μ)) : supNorm (intCoords y) ≤ t := by
  by_contra hc
  exact not_bondWithinRadius_of_supNorm y μ (by omega) hb
theorem topDirectionDefect_eq_zero_inner (hRef : flatTopReferenceStatement) (h : ComparisonSetup S r q)
    (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (hA : ∀ μ ν, A μ ν = - A ν μ) {φ : F.Site F.top → Fin 4 → ℝ} (hφ : IsPotentialCutoff r φ) (y : F.Cell)
    (μ : Fin 4)
    (hy : supNorm (intCoords y) + 2 ≤ 6 * q) :
    topDirectionDefect (referenceFieldChain S flatTopField) (candidateChart F q A) (cutoffPotential φ A) (y, μ) = 0 := by
  have hr := h.scale_le_radius
  have hb : BondWithinRadius (r / 2) (minimalCoords y, μ) := bondWithinRadius_of_supNorm y μ (by omega)
  unfold topDirectionDefect
  simp only
  rw [linearPart_candidate_top hRef h A hA y μ hy]
  simp [cutoffPotential, hφ.eq_one y μ hb]
theorem topDirectionDefect_eq_zero_far (h : ComparisonSetup S r q) (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    {φ : F.Site F.top → Fin 4 → ℝ} (hφ : IsPotentialCutoff r φ)
    (R : F.FieldChain) (y : F.Cell) (μ : Fin 4) (hy : r < supNorm (intCoords y)) :
    topDirectionDefect R (candidateChart F q A) (cutoffPotential φ A) (y, μ) = 0 := by
  have hq := h.five_le_scale
  have hr := h.scale_le_radius
  unfold topDirectionDefect
  simp only
  rw [linearPart_candidate_far h A R y μ (by omega)]
  simp [cutoffPotential, hφ.eq_zero y μ (not_bondWithinRadius_of_supNorm y μ hy)]
theorem norm_cutoffPotential_le (A : Fin 4 → Fin 4 → imaginaryQuaternions) {φ : F.Site F.top → Fin 4 → ℝ}
    (hφ : IsPotentialCutoff r φ) (y : F.Cell) (μ : Fin 4) :
    ‖cutoffPotential φ A y μ‖ ≤ r * curvatureL1 A := by
  have hS := curvatureL1_nonneg A
  by_cases hb : BondWithinRadius r (minimalCoords y, μ)
  · have hs := supNorm_le_of_bondWithinRadius y μ hb
    have hs' : (supNorm (intCoords y) : ℝ) ≤ r := by exact_mod_cast hs
    unfold cutoffPotential
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφ.mem_unit y μ).1, constantCurvaturePotential_eq_graded]
    have h1 := norm_gradedPotential_le (1 / 2) A (intCoords y) μ
    have h2 : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_pos (by norm_num)
    rw [h2] at h1
    have h3 := (hφ.mem_unit y μ).2
    calc _ ≤ 1 * ‖gradedPotential (1 / 2) A (intCoords y) μ‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ ≤ 1 / 2 * (supNorm (intCoords y) * curvatureL1 A) := by rw [one_mul]; exact h1
      _ ≤ 1 / 2 * (r * curvatureL1 A) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ r) hS]
  · unfold cutoffPotential
    rw [hφ.eq_zero y μ hb, zero_smul, norm_zero]
    positivity
theorem norm_topDirectionDefect_le (h : ComparisonSetup S r q) (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    {φ : F.Site F.top → Fin 4 → ℝ} (hφ : IsPotentialCutoff r φ)
    (R : F.FieldChain) (c : F.Site F.top × Fin 4) :
    ‖topDirectionDefect R (candidateChart F q A) (cutoffPotential φ A) c‖ ≤ 2 * r * curvatureL1 A := by
  have hS := curvatureL1_nonneg A
  unfold topDirectionDefect
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_cutoffPotential_le A hφ c.1 c.2
  have h2 := norm_linearPart_candidate_le h A R c.1 c.2
  have h3 : (q : ℝ) * 4 ≤ r := by
    have : 4 * q ≤ r := by
      have := h.scale_le_radius
      omega
    have h4 : ((4 * q : ℕ) : ℝ) ≤ r := by exact_mod_cast this
    push_cast at h4
    linarith
  have h5 : 4 * (q : ℝ) * curvatureL1 A ≤ r * curvatureL1 A := by
    refine mul_le_mul_of_nonneg_right (by linarith) hS
  have e : ‖((cutoffPotential φ A c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖cutoffPotential φ A c.1 c.2‖ := rfl
  rw [e]
  linarith
theorem abs_sum_inner_defect_le (hRef : flatTopReferenceStatement) (h : ComparisonSetup S r q)
    (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (hA : ∀ μ ν, A μ ν = - A ν μ) {φ : F.Site F.top → Fin 4 → ℝ} (hφ : IsPotentialCutoff r φ) {C : ℝ} (hC : 0 ≤ C)
    (D : ChainChart F)
    (hT : ∀ c ∈ innerBonds S F.top, ‖linearPart (referenceFieldChain S flatTopField) D F.top c.1 c.2‖ ≤
      C * localNorm S (referenceFieldChain S flatTopField) D (unitWeights F) (enclosingCell c.1)) :
    |∑ c ∈ innerBonds S F.top, inner ℝ
        (topDirectionDefect (referenceFieldChain S flatTopField) (candidateChart F q A) (cutoffPotential φ A) c)
        (linearPart (referenceFieldChain S flatTopField) D F.top c.1 c.2)| ≤
      8 * r * C * curvatureL1 A *
        ∑ z ∈ comparisonShell S q r, localNorm S (referenceFieldChain S flatTopField) D (unitWeights F) z := by
  classical
  set R := referenceFieldChain S flatTopField with hR
  have hS := curvatureL1_nonneg A
  have hq := h.five_le_scale
  set ν : F.Cell → ℝ := fun z => localNorm S R D (unitWeights F) z with hν
  have hν0 : ∀ z, 0 ≤ ν z := fun z => Real.sqrt_nonneg _
  set t : F.Site F.top × Fin 4 → ℝ := fun c => 2 * r * curvatureL1 A * (C * ν c.1) with ht
  have ht0 : ∀ c, 0 ≤ t c := fun c => by
    have := hν0 c.1
    positivity
  have hterm : ∀ c ∈ innerBonds S F.top, |inner ℝ (topDirectionDefect R (candidateChart F q A) (cutoffPotential φ A) c)
      (linearPart R D F.top c.1 c.2)| ≤
        if c ∈ comparisonShell S q r ×ˢ (Finset.univ : Finset (Fin 4)) then t c else 0 := by
    intro c hc
    have hcS : c.1 ∈ S := by
      simp only [innerBonds, Finset.mem_filter, Finset.mem_product] at hc
      exact mem_sitesOfCells_top.1 hc.1.1
    split_ifs with hin
    · refine (abs_real_inner_le_norm _ _).trans ?_
      have h1 := norm_topDirectionDefect_le h A hφ R c
      have h2 := hT c hc
      rw [LumpContours.BlockLevels.enclosingCell_cell h.odd_blockSide.pos] at h2
      exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    · have hz : topDirectionDefect R (candidateChart F q A) (cutoffPotential φ A) c = 0 := by
        by_cases h1 : supNorm (intCoords c.1) + 2 ≤ 6 * q
        · exact topDirectionDefect_eq_zero_inner hRef h A hA hφ c.1 c.2 h1
        by_cases h2 : r < supNorm (intCoords c.1)
        · exact topDirectionDefect_eq_zero_far h A hφ R c.1 c.2 h2
        exfalso
        apply hin
        refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hcS, by omega, by omega⟩, Finset.mem_univ _⟩
      rw [hz]
      simp
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  have hsum : ∑ c ∈ innerBonds S F.top,
      (if c ∈ comparisonShell S q r ×ˢ (Finset.univ : Finset (Fin 4)) then t c else 0) ≤
      ∑ c ∈ comparisonShell S q r ×ˢ (Finset.univ : Finset (Fin 4)), t c := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => ht0 c
    intro c hc
    exact (Finset.mem_filter.1 hc).2
  refine hsum.trans (le_of_eq ?_)
  rw [Finset.sum_product]
  simp only [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  push_cast
  ring
end Defect
section Splitting
variable {F : BlockFrame} {S : Finset F.Cell} {r q : ℕ}
theorem adjointAction_add (g : UnitQuaternion) (p q : ℍ[ℝ]) :
    _root_.YangMills.Construction.BlockAverages.adjointAction g (p + q) = _root_.YangMills.Construction.BlockAverages.adjointAction g p + _root_.YangMills.Construction.BlockAverages.adjointAction g q := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_add <;> assumption
theorem parallelAverage_add {j : ℕ} (R : F.GaugeField j) (f g : F.Site j → Fin 4 → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) :
    parallelAverage R (fun x i => f x i + g x i) c =
      parallelAverage R f c + parallelAverage R g c := by
  simp only [parallelAverage, _root_.YangMills.Construction.BlockAverages.QuadraticResponseAtFlat.adjointAction_add, Finset.sum_add_distrib, smul_add]
theorem linearPart_add (R : F.FieldChain) {U₁ U₂ U₃ : ChainChart F}
    (hu : ∀ x i, U₃.fine x i = U₁.fine x i + U₂.fine x i)
    (hm : ∀ j y i, U₃.coarse j y i = U₁.coarse j y i + U₂.coarse j y i) (k : ℕ) :
    linearPart R U₃ k = fun x i => linearPart R U₁ k x i + linearPart R U₂ k x i := by
  induction k with
  | zero =>
    funext x i
    simp [linearPart, hu]
  | succ k ih =>
    funext y i
    simp only [linearPart]
    rw [ih, parallelAverage_add]
    split_ifs
    · rw [hm]
      push_cast
      abel
    · simp
theorem linearPart_congr (hL : Odd F.blockSide) {U U' : ChainChart F} (R : F.FieldChain)
    (hu : ∀ b ∈ innerBonds S 0, U.fine b.1 b.2 = U'.fine b.1 b.2)
    (hm : ∀ j, ∀ c ∈ innerBonds S (j + 1), U.coarse j c.1 c.2 = U'.coarse j c.1 c.2) (k : ℕ) (hk : k ≤ F.top) :
    ∀ c ∈ innerBonds S k, linearPart R U k c.1 c.2 = linearPart R U' k c.1 c.2 := by
  induction k with
  | zero =>
    intro c hc
    simp [linearPart, hu c hc]
  | succ k ih =>
    intro c hc
    have hk' : k < F.top := by omega
    have ht : parallelAverage (R k) (linearPart R U k) c =
        parallelAverage (R k) (linearPart R U' k) c := by
      unfold parallelAverage
      congr 1
      refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ =>
        Finset.sum_congr rfl fun s hs => ?_
      have hb := lineBond_mem_innerBonds hk' hL c hc h hh s (Finset.mem_range.1 hs)
      have := ih (by omega) _ hb
      simp only [lineBond] at this
      rw [this]
    have e : ∀ W : ChainChart F, linearPart R W (k + 1) c.1 c.2 =
        parallelAverage (R k) (linearPart R W k) c +
          if k + 1 < F.top then ((W.coarse k c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) else 0 := fun W => rfl
    rw [e, e, ht, hm k c hc]
theorem corner_mem_innerBonds (h : ComparisonSetup S r q) {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ innerPlaquettes S 0) :
    (p.1, p.2.1) ∈ innerBonds S 0 ∧ (p.1 + unitStep 0 p.2.1, p.2.2) ∈ innerBonds S 0 ∧
      (p.1 + unitStep 0 p.2.2, p.2.1) ∈ innerBonds S 0 ∧ (p.1, p.2.2) ∈ innerBonds S 0 := by
  classical
  have hc : plaquetteCorners p ⊆ sitesOfCells S 0 := (Finset.mem_filter.1 hp).2.2
  have m0 : p.1 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have m1 : p.1 + unitStep 0 p.2.1 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have m2 : p.1 + unitStep 0 p.2.2 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have m3 : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have m3' : p.1 + unitStep 0 p.2.2 + unitStep 0 p.2.1 ∈ plaquetteCorners p := by
    rw [add_right_comm]
    exact m3
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨⟨hc m0, hc m1⟩, ⟨hc m1, hc m3⟩, ⟨hc m2, hc m3'⟩, ⟨hc m0, hc m2⟩⟩
theorem untransportedCurl_congr (h : ComparisonSetup S r q) {u u' : F.Site 0 → Fin 4 → imaginaryQuaternions}
    (hu : ∀ b ∈ innerBonds S 0, u b.1 b.2 = u' b.1 b.2) {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ innerPlaquettes S 0) :
    untransportedCurl u p = untransportedCurl u' p := by
  obtain ⟨a, b, c, d⟩ := corner_mem_innerBonds h hp
  simp only [untransportedCurl]
  rw [hu _ a, hu _ b, hu _ c, hu _ d]
theorem untransportedCurl_add (u v : F.Site 0 → Fin 4 → imaginaryQuaternions) (p : F.Site 0 × Fin 4 × Fin 4) :
    untransportedCurl (fun x i => u x i + v x i) p = untransportedCurl u p + untransportedCurl v p := by
  simp only [untransportedCurl]
  abel
theorem responseBilinear_eq_untransported (hRef : flatTopReferenceStatement) (h : ComparisonSetup S r q) (a : ℝ)
    (U A : ChainChart F) :
    responseBilinear a S (referenceFieldChain S flatTopField) U A =
      ∑ p ∈ innerPlaquettes S 0, inner ℝ (untransportedCurl U.fine p : ℍ[ℝ]) (untransportedCurl A.fine p : ℍ[ℝ]) +
      a * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ innerBonds S (j + 1),
        inner ℝ (U.coarse j c.1 c.2 : ℍ[ℝ]) (A.coarse j c.1 c.2 : ℍ[ℝ]) +
      a * ∑ c ∈ innerBonds S F.top, inner ℝ (linearPart (referenceFieldChain S flatTopField) U F.top c.1 c.2)
        (linearPart (referenceFieldChain S flatTopField) A F.top c.1 c.2) := by
  unfold responseBilinear
  congr 2
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [linearizedCurl_eq_untransported hRef h _ hp, linearizedCurl_eq_untransported hRef h _ hp]
structure ResponseSplitting (S : Finset F.Cell) (U Ut W : ChainChart F)
    (e : F.Site 0 → Fin 4 → imaginaryQuaternions) : Prop where
  bond_eq : ∀ b ∈ innerBonds S 0, U.fine b.1 b.2 = Ut.fine b.1 b.2 + W.fine b.1 b.2 + e b.1 b.2
  coarse_eq : ∀ j y i, U.coarse j y i = W.coarse j y i
  candidate_coarse_eq_zero : ∀ j y i, Ut.coarse j y i = 0
  rest_curl_eq_zero : ∀ p ∈ innerPlaquettes S 0, untransportedCurl e p = 0
  rest_top_eq_zero : ∀ c ∈ innerBonds S F.top,
    linearPart (referenceFieldChain S flatTopField) (baseOnlyChart e) F.top c.1 c.2 = 0
theorem ResponseSplitting.untransportedCurl_eq (h : ComparisonSetup S r q) {U Ut W : ChainChart F}
    {e : F.Site 0 → Fin 4 → imaginaryQuaternions}
    (hs : ResponseSplitting S U Ut W e) {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S 0) :
    untransportedCurl U.fine p = untransportedCurl Ut.fine p + untransportedCurl W.fine p := by
  have h1 := untransportedCurl_congr h (u := U.fine) (u' := fun x i => (Ut.fine x i + W.fine x i) + e x i)
    hs.bond_eq hp
  rw [h1, untransportedCurl_add, untransportedCurl_add, hs.rest_curl_eq_zero p hp, add_zero]
theorem ResponseSplitting.linearPart_top_eq (hL : Odd F.blockSide) {U Ut W : ChainChart F}
    {e : F.Site 0 → Fin 4 → imaginaryQuaternions}
    (hs : ResponseSplitting S U Ut W e) {c : F.Site F.top × Fin 4} (hc : c ∈ innerBonds S F.top) :
    linearPart (referenceFieldChain S flatTopField) U F.top c.1 c.2 =
      linearPart (referenceFieldChain S flatTopField) Ut F.top c.1 c.2 +
        linearPart (referenceFieldChain S flatTopField) W F.top c.1 c.2 := by
  set R := referenceFieldChain S (flatTopField : F.GaugeField F.top) with hR
  set U₁ : ChainChart F := ⟨fun x i => Ut.fine x i + W.fine x i, W.coarse⟩ with hU₁
  set U₂ : ChainChart F := ⟨fun x i => U₁.fine x i + e x i, U.coarse⟩ with hU₂
  have c1 := linearPart_congr (S := S) hL (U := U) (U' := U₂) R hs.bond_eq (fun j c _ => rfl) F.top le_rfl c hc
  have a2 := congrFun (congrFun (linearPart_add R (U₁ := U₁) (U₂ := baseOnlyChart e) (U₃ := U₂)
    (fun _ _ => rfl) (fun j y i => by simp [hU₂, hU₁, baseOnlyChart, hs.coarse_eq]) F.top) c.1) c.2
  have a1 := congrFun (congrFun (linearPart_add R (U₁ := Ut) (U₂ := W) (U₃ := U₁)
    (fun _ _ => rfl) (fun j y i => by simp [hU₁, hs.candidate_coarse_eq_zero]) F.top) c.1) c.2
  rw [c1, a2, hs.rest_top_eq_zero c hc, add_zero, a1]
theorem ResponseSplitting.responseBilinear_eq (hRef : flatTopReferenceStatement) (h : ComparisonSetup S r q) (a : ℝ)
    {U Ut W : ChainChart F} {e : F.Site 0 → Fin 4 → imaginaryQuaternions} (hs : ResponseSplitting S U Ut W e)
    (A : ChainChart F) :
    responseBilinear a S (referenceFieldChain S flatTopField) W A =
      responseBilinear a S (referenceFieldChain S flatTopField) U A -
        responseBilinear a S (referenceFieldChain S flatTopField) Ut A := by
  rw [responseBilinear_eq_untransported hRef h, responseBilinear_eq_untransported hRef h,
    responseBilinear_eq_untransported hRef h]
  have t1 : ∑ p ∈ innerPlaquettes S 0, inner ℝ (untransportedCurl U.fine p : ℍ[ℝ]) (untransportedCurl A.fine p : ℍ[ℝ]) =
      ∑ p ∈ innerPlaquettes S 0, inner ℝ (untransportedCurl Ut.fine p : ℍ[ℝ]) (untransportedCurl A.fine p : ℍ[ℝ]) +
      ∑ p ∈ innerPlaquettes S 0, inner ℝ (untransportedCurl W.fine p : ℍ[ℝ]) (untransportedCurl A.fine p : ℍ[ℝ]) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hs.untransportedCurl_eq h hp, Submodule.coe_add, inner_add_left]
  have t2 : ∑ c ∈ innerBonds S F.top, inner ℝ (linearPart (referenceFieldChain S flatTopField) U F.top c.1 c.2)
        (linearPart (referenceFieldChain S flatTopField) A F.top c.1 c.2) =
      ∑ c ∈ innerBonds S F.top, inner ℝ (linearPart (referenceFieldChain S flatTopField) Ut F.top c.1 c.2)
        (linearPart (referenceFieldChain S flatTopField) A F.top c.1 c.2) +
      ∑ c ∈ innerBonds S F.top, inner ℝ (linearPart (referenceFieldChain S flatTopField) W F.top c.1 c.2)
        (linearPart (referenceFieldChain S flatTopField) A F.top c.1 c.2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [hs.linearPart_top_eq h.odd_blockSide hc, inner_add_left]
  have t3 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ innerBonds S (j + 1),
      inner ℝ (U.coarse j c.1 c.2 : ℍ[ℝ]) (A.coarse j c.1 c.2 : ℍ[ℝ]) =
      ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ innerBonds S (j + 1),
      inner ℝ (W.coarse j c.1 c.2 : ℍ[ℝ]) (A.coarse j c.1 c.2 : ℍ[ℝ]) :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => by rw [hs.coarse_eq]
  have t4 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ innerBonds S (j + 1),
      inner ℝ (Ut.coarse j c.1 c.2 : ℍ[ℝ]) (A.coarse j c.1 c.2 : ℍ[ℝ]) = 0 :=
    Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun c _ => by
      rw [hs.candidate_coarse_eq_zero]
      simp
  rw [t1, t2, t3, t4]
  ring
end Splitting
section Residual
variable {F : BlockFrame} {S : Finset F.Cell} {r q : ℕ}
theorem responseLinear_sub_bilinear_eq (hRef : flatTopReferenceStatement) (h : ComparisonSetup S r q) (a : ℝ)
    (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (φ : F.Site F.top → Fin 4 → ℝ) (D : ChainChart F) :
    responseLinear a S (referenceFieldChain S flatTopField) (cutoffPotential φ A) D -
        responseBilinear a S (referenceFieldChain S flatTopField) (candidateChart F q A) D =
      a * ∑ c ∈ innerBonds S F.top, inner ℝ
        (topDirectionDefect (referenceFieldChain S flatTopField) (candidateChart F q A) (cutoffPotential φ A) c)
        (linearPart (referenceFieldChain S flatTopField) D F.top c.1 c.2) -
      ∑ p ∈ innerPlaquettes S 0, inner ℝ (untransportedCurl (candidateForm F q A) p : ℍ[ℝ])
        (untransportedCurl D.fine p : ℍ[ℝ]) := by
  rw [responseBilinear_eq_untransported hRef h]
  have t4 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ innerBonds S (j + 1),
      inner ℝ ((candidateChart F q A).coarse j c.1 c.2 : ℍ[ℝ]) (D.coarse j c.1 c.2 : ℍ[ℝ]) = 0 :=
    Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun c _ => by
      simp [candidateChart, baseOnlyChart]
  rw [t4]
  unfold responseLinear topDirectionDefect
  simp only [inner_sub_left, Finset.sum_sub_distrib]
  show _ = _
  have : (candidateChart F q A).fine = candidateForm F q A := rfl
  rw [this]
  ring
theorem abs_responseLinear_sub_bilinear_le (hRef : flatTopReferenceStatement) (h : ComparisonSetup S r q) {a : ℝ}
    (ha : 0 ≤ a)
    (A : Fin 4 → Fin 4 → imaginaryQuaternions) (hA : ∀ μ ν, A μ ν = - A ν μ) {φ : F.Site F.top → Fin 4 → ℝ}
    (hφ : IsPotentialCutoff r φ)
    {C : ℝ} (hC : 0 ≤ C) (D : ChainChart F)
    (hT : ∀ c ∈ innerBonds S F.top, ‖linearPart (referenceFieldChain S flatTopField) D F.top c.1 c.2‖ ≤
      C * localNorm S (referenceFieldChain S flatTopField) D (unitWeights F) (enclosingCell c.1)) :
    |responseLinear a S (referenceFieldChain S flatTopField) (cutoffPotential φ A) D -
        responseBilinear a S (referenceFieldChain S flatTopField) (candidateChart F q A) D| ≤
      (a * (8 * r * C) + 99) * curvatureL1 A *
        ∑ z ∈ comparisonShell S q r, localNorm S (referenceFieldChain S flatTopField) D (unitWeights F) z := by
  rw [responseLinear_sub_bilinear_eq hRef h]
  set X := ∑ z ∈ comparisonShell S q r, localNorm S (referenceFieldChain S flatTopField) D (unitWeights F) z with hX
  have hb1 := abs_sum_inner_defect_le hRef h A hA hφ hC D hT
  have hsplit : ∑ p ∈ innerPlaquettes S 0, inner ℝ (untransportedCurl (candidateForm F q A) p : ℍ[ℝ])
        (untransportedCurl D.fine p : ℍ[ℝ]) =
      ∑ p ∈ innerPlaquettes S 0, inner ℝ (untransportedCurl (candidateForm F q A) p : ℍ[ℝ])
        (untransportedCurl (outerCutForm F q D.fine) p : ℍ[ℝ]) := by
    have h0 := sum_inner_candidate_curl_eq_zero h A hA (innerCutForm F q D.fine)
      (fun x i hx => supNorm_le_of_innerCutForm_ne_zero h D.fine x i hx)
    have e : ∑ p ∈ innerPlaquettes S 0, inner ℝ (untransportedCurl (candidateForm F q A) p : ℍ[ℝ])
          (untransportedCurl D.fine p : ℍ[ℝ]) =
        ∑ p ∈ innerPlaquettes S 0, inner ℝ (untransportedCurl (candidateForm F q A) p : ℍ[ℝ])
          (untransportedCurl (innerCutForm F q D.fine) p : ℍ[ℝ]) +
        ∑ p ∈ innerPlaquettes S 0, inner ℝ (untransportedCurl (candidateForm F q A) p : ℍ[ℝ])
          (untransportedCurl (outerCutForm F q D.fine) p : ℍ[ℝ]) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [untransportedCurl_eq_inner_add_outer (q := q) D.fine p, Submodule.coe_add, inner_add_right]
    rw [e, h0, zero_add]
  rw [hsplit]
  have hb2 := abs_sum_inner_outer_le hRef h A hA D
  rw [← hX] at hb1 hb2
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_nonneg ha]
  calc _ ≤ a * (8 * r * C * curvatureL1 A * X) + 99 * curvatureL1 A * X :=
        add_le_add (mul_le_mul_of_nonneg_left hb1 ha) hb2
    _ = _ := by ring
theorem plaquetteCellShare_nonneg (Y : F.Cell) (p : F.Site 0 × Fin 4 × Fin 4) : 0 ≤ plaquetteCellShare Y p := by
  unfold plaquetteCellShare
  refine Finset.sum_nonneg fun _ _ => ?_
  split_ifs <;> norm_num
theorem plaquetteCellShare_le_one (Y : F.Cell) (p : F.Site 0 × Fin 4 × Fin 4) : plaquetteCellShare Y p ≤ 1 := by
  classical
  unfold plaquetteCellShare
  have h1 : ∀ x ∈ plaquetteCorners p, (if enclosingCell x = Y then (1 / 4 : ℝ) else 0) ≤ 1 / 4 := by
    intro x _
    split_ifs <;> norm_num
  refine (Finset.sum_le_sum h1).trans ?_
  simp only [Finset.sum_const, nsmul_eq_mul]
  have h2 : (plaquetteCorners p).card ≤ 4 := Finset.card_le_four
  have h3 : ((plaquetteCorners p).card : ℝ) ≤ 4 := by exact_mod_cast h2
  linarith
theorem bondCellShare_nonneg {j : ℕ} (Y : F.Cell) (c : F.Site j × Fin 4) : 0 ≤ bondCellShare Y c := by
  unfold bondCellShare
  split_ifs <;> norm_num
theorem bondCellShare_le_one {j : ℕ} (Y : F.Cell) (c : F.Site j × Fin 4) : bondCellShare Y c ≤ 1 := by
  unfold bondCellShare
  split_ifs <;> norm_num
theorem share_le_of_parts (P M T X Vv a s1 s2 s3 : ℝ) (h1 : s1 ≤ P) (h2 : s2 ≤ M) (h3 : s3 ≤ Vv - 2 * X + T)
    (e : P + a * M + a * T = a * X) (ha : 0 ≤ a) (hP : 0 ≤ P) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    s1 + a * s2 + a * s3 ≤ a * Vv := by
  have a2 := mul_le_mul_of_nonneg_left h2 ha
  have a3 := mul_le_mul_of_nonneg_left h3 ha
  have n1 := mul_nonneg ha hM
  have n2 := mul_nonneg ha hT
  linarith
theorem responseCellShare_le_energy {a : ℝ} (ha : 0 ≤ a) (Y : F.Cell)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) {U : ChainChart F}
    (hU : IsFlatTopResponse a S v U) :
    responseCellShare a S Y (referenceFieldChain S flatTopField) U v ≤
      a * ∑ c ∈ innerBonds S F.top, ‖(v c.1 c.2 : ℍ[ℝ])‖ ^ 2 := by
  set R := referenceFieldChain S (flatTopField : F.GaugeField F.top) with hR
  have hself := hU.2 U hU.1
  set P := ∑ p ∈ innerPlaquettes S 0, ‖linearizedCurl (R 0) U.fine p‖ ^ 2 with hP
  set M := ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ innerBonds S (j + 1), ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 with hM
  set T := ∑ c ∈ innerBonds S F.top, ‖linearPart R U F.top c.1 c.2‖ ^ 2 with hT
  set X := ∑ c ∈ innerBonds S F.top, inner ℝ (v c.1 c.2 : ℍ[ℝ]) (linearPart R U F.top c.1 c.2) with hX
  set Vv := ∑ c ∈ innerBonds S F.top, ‖(v c.1 c.2 : ℍ[ℝ])‖ ^ 2 with hV
  have hform : responseBilinear a S R U U = P + a * M + a * T := by
    unfold responseBilinear
    simp only [real_inner_self_eq_norm_sq]
    rfl
  have hsrc : responseLinear a S R v U = a * X := rfl
  have hgap : ∑ c ∈ innerBonds S F.top, ‖topDirectionDefect R U v c‖ ^ 2 = Vv - 2 * X + T := by
    unfold topDirectionDefect
    simp only [norm_sub_sq_real]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ p ∈ innerPlaquettes S 0, plaquetteCellShare Y p * ‖linearizedCurl (R 0) U.fine p‖ ^ 2 ≤ P :=
    Finset.sum_le_sum fun p _ => by
      have := plaquetteCellShare_le_one Y p
      nlinarith [sq_nonneg ‖linearizedCurl (R 0) U.fine p‖]
  have h2 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ innerBonds S (j + 1),
      bondCellShare Y c * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 ≤ M :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun c _ => by
      have := bondCellShare_le_one Y c
      nlinarith [sq_nonneg ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖]
  have h3 : ∑ c ∈ innerBonds S F.top, bondCellShare Y c * ‖topDirectionDefect R U v c‖ ^ 2 ≤ Vv - 2 * X + T := by
    rw [← hgap]
    refine Finset.sum_le_sum fun c _ => ?_
    have := bondCellShare_le_one Y c
    nlinarith [sq_nonneg ‖topDirectionDefect R U v c‖]
  unfold responseCellShare
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have e : P + a * M + a * T = a * X := by rw [← hform, hself, hsrc]
  exact share_le_of_parts _ _ _ _ _ _ _ _ _ h1 h2 h3 e ha hP0 hM0 hT0
end Residual
section Origin
variable {F : BlockFrame} {S : Finset F.Cell} {r q : ℕ}
theorem supNorm_intCoords_zero : supNorm (intCoords (0 : F.Cell)) = 0 := by
  refine Nat.le_zero.1 (Finset.sup_le fun i _ => ?_)
  simp [intCoords]
theorem supNorm_le_cellSide_of_origin (h : ComparisonSetup S r q) {x : F.Site 0} (hx : enclosingCell x = 0) :
    supNorm (intCoords x) ≤ cellSide F := by
  have := supNorm_le_cellSide_mul h x
  rw [hx, supNorm_intCoords_zero] at this
  simpa using this
open Classical in
def originQuarter (F : BlockFrame) (y : F.Site 0) : ℝ := if enclosingCell y = (0 : F.Cell) then 1 / 4 else 0
theorem unitStep_ne_zero (h : ComparisonSetup S r q) (μ : Fin 4) : (unitStep 0 μ : F.Site 0) ≠ 0 := by
  intro e
  have hs : supNorm (Pi.single μ 1 : Fin 4 → ℤ) ≤ 1 := by
    refine Finset.sup_le fun l _ => ?_
    by_cases hl : l = μ
    · subst hl
      simp
    · simp [hl]
  have h1 := intCoords_siteOfCoords (F := F) (h.readsBack_one 0) _ hs
  have h2 : siteOfCoords 0 (Pi.single μ 1 : Fin 4 → ℤ) = (0 : F.Site 0) := e
  rw [h2] at h1
  have := congrFun h1 μ
  simp [intCoords] at this
theorem unitStep_ne_unitStep (h : ComparisonSetup S r q) {μ ν : Fin 4} (hμν : μ ≠ ν) :
    (unitStep 0 μ : F.Site 0) ≠ unitStep 0 ν := by
  intro e
  have hs : ∀ k : Fin 4, supNorm (Pi.single k 1 : Fin 4 → ℤ) ≤ 1 := by
    intro k
    refine Finset.sup_le fun l _ => ?_
    by_cases hl : l = k
    · subst hl
      simp
    · simp [hl]
  have h1 := intCoords_siteOfCoords (F := F) (h.readsBack_one 0) _ (hs μ)
  have h2 := intCoords_siteOfCoords (F := F) (h.readsBack_one 0) _ (hs ν)
  have h3 : (siteOfCoords 0 (Pi.single μ 1 : Fin 4 → ℤ) : F.Site 0) = siteOfCoords 0 (Pi.single ν 1) := e
  rw [h3, h2] at h1
  have := congrFun h1 μ
  simp [Pi.single_apply, hμν] at this
theorem unitStep_add_unitStep_ne_zero (h : ComparisonSetup S r q) {μ ν : Fin 4} (hμν : μ ≠ ν) :
    (unitStep 0 μ + unitStep 0 ν : F.Site 0) ≠ 0 := by
  intro e
  have hs : supNorm (Pi.single μ 1 + Pi.single ν 1 : Fin 4 → ℤ) ≤ 2 := by
    refine Finset.sup_le fun l _ => ?_
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> simp
  have hR : ReadsBack F 0 2 := (h.readsBack 0).mono (by
    have := h.cellSide_pos
    have := h.five_le_scale
    have := h.scale_le_radius
    have h1 : 1 ≤ F.blockSide ^ (F.top - 0) := Nat.one_le_pow _ _ h.odd_blockSide.pos
    nlinarith)
  have h1 := intCoords_siteOfCoords (F := F) hR _ hs
  have h2 : siteOfCoords 0 (Pi.single μ 1 + Pi.single ν 1 : Fin 4 → ℤ) = (0 : F.Site 0) := by
    rw [siteOfCoords_add]
    exact e
  rw [h2] at h1
  have := congrFun h1 μ
  simp [intCoords, Pi.single_apply, hμν] at this
theorem plaquetteCellShare_origin_eq (h : ComparisonSetup S r q) (x : F.Site 0) {μ ν : Fin 4} (hμν : μ ≠ ν) :
    plaquetteCellShare (0 : F.Cell) (x, μ, ν) = originQuarter F x + originQuarter F (x + unitStep 0 μ) +
      originQuarter F (x + unitStep 0 ν) + originQuarter F (x + unitStep 0 μ + unitStep 0 ν) := by
  classical
  have u1 := unitStep_ne_zero h (F := F) μ
  have u2 := unitStep_ne_zero h (F := F) ν
  have u3 := unitStep_ne_unitStep (F := F) h hμν
  have u4 := unitStep_add_unitStep_ne_zero (F := F) h hμν
  have a1 : x ∉ ({x + unitStep 0 μ, x + unitStep 0 ν, x + unitStep 0 μ + unitStep 0 ν} : Finset (F.Site 0)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun e => u1 ?_, fun e => u2 ?_, fun e => u4 ?_⟩
    · simpa using e.symm
    · simpa using e.symm
    · have : x + (unitStep 0 μ + unitStep 0 ν) = x + 0 := by
        rw [add_zero, ← add_assoc]
        exact e.symm
      exact add_left_cancel this
  have a2 : x + unitStep 0 μ ∉ ({x + unitStep 0 ν, x + unitStep 0 μ + unitStep 0 ν} : Finset (F.Site 0)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun e => u3 (add_left_cancel e), fun e => u2 ?_⟩
    simpa using e.symm
  have a3 : x + unitStep 0 ν ∉ ({x + unitStep 0 μ + unitStep 0 ν} : Finset (F.Site 0)) := by
    simp only [Finset.mem_singleton]
    intro e
    apply u1
    have : unitStep 0 ν + (unitStep 0 μ : F.Site 0) = unitStep 0 ν + 0 := by
      have e2 : x + (unitStep 0 ν + unitStep 0 μ) = x + (unitStep 0 ν + 0) := by
        rw [add_zero, add_comm (unitStep 0 ν), ← add_assoc]
        exact e.symm
      exact add_left_cancel e2
    exact add_left_cancel this
  unfold plaquetteCellShare plaquetteCorners
  simp only
  rw [Finset.sum_insert a1, Finset.sum_insert a2, Finset.sum_insert a3, Finset.sum_singleton]
  unfold originQuarter
  ring
theorem card_sitesOfCells_origin (h : ComparisonSetup S r q) :
    ((sitesOfCells ({0} : Finset F.Cell) 0).card : ℝ) = (cellSide F : ℝ) ^ 4 := by
  classical
  unfold sitesOfCells
  rw [Finset.singleton_biUnion, Finset.card_image_of_injOn]
  · have hodd : Odd (F.blockSide ^ (F.top - 0)) := h.odd_blockSide.pow
    rw [card_centredCube hodd]
    push_cast
    simp [cellSide]
  · intro a ha b hb e
    simp only at e
    have hc : ∀ c ∈ (centredCube (F.blockSide ^ (F.top - 0)) : Finset (Fin 4 → ℤ)),
        supNorm c ≤ (r + 1) * F.blockSide ^ (F.top - 0) := by
      intro c hc
      refine Finset.sup_le fun i _ => ?_
      have h1 := (mem_centredCube_iff _ c).1 hc i
      have hM : 0 < F.blockSide ^ (F.top - 0) := pow_pos h.odd_blockSide.pos _
      have h2 : |c i| ≤ (((F.blockSide ^ (F.top - 0) : ℕ) : ℤ)) := by
        rw [abs_le]
        constructor <;> omega
      rw [Int.abs_eq_natAbs] at h2
      have h3 : (c i).natAbs ≤ F.blockSide ^ (F.top - 0) := by exact_mod_cast h2
      nlinarith
    have e' := add_left_cancel e
    have b1 := intCoords_siteOfCoords (h.readsBack 0) a (hc a ha)
    have b2 := intCoords_siteOfCoords (h.readsBack 0) b (hc b hb)
    rw [e', b2] at b1
    exact b1.symm
theorem sum_originQuarter (h : ComparisonSetup S r q) {ρ : ℕ} (hR : ReadsBack F 0 ρ) (hρ : cellSide F ≤ ρ) :
    ∑ x ∈ coordBall F ρ, originQuarter F x = (cellSide F : ℝ) ^ 4 / 4 := by
  classical
  unfold originQuarter
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have e : (coordBall F ρ).filter (fun x => enclosingCell x = (0 : F.Cell)) = sitesOfCells ({0} : Finset F.Cell) 0 := by
    ext x
    rw [Finset.mem_filter, LumpContours.BlockLevels.mem_sitesOfCells_iff (Nat.zero_le _) h.odd_blockSide,
      Finset.mem_singleton]
    constructor
    · exact fun hx => hx.2
    · exact fun hx => ⟨(mem_coordBall hR).2 ((supNorm_le_cellSide_of_origin h hx).trans hρ), hx⟩
  rw [e, card_sitesOfCells_origin h]
  ring
theorem sum_plaquetteCellShare_plane (h : ComparisonSetup S r q) {ρ : ℕ} (hR : ReadsBack F 0 ρ)
    (hρ : cellSide F + 4 ≤ ρ) {μ ν : Fin 4}
    (hμν : μ ≠ ν) : ∑ x ∈ coordBall F ρ, plaquetteCellShare (0 : F.Cell) (x, μ, ν) = (cellSide F : ℝ) ^ 4 := by
  have hr1 := h.readsBack_one 0
  simp only [plaquetteCellShare_origin_eq h _ hμν, Finset.sum_add_distrib]
  have hq : ∀ x, originQuarter F x ≠ 0 → supNorm (intCoords x) ≤ cellSide F := by
    intro x hx
    by_contra hc
    apply hx
    unfold originQuarter
    rw [if_neg]
    intro e
    exact hc (supNorm_le_cellSide_of_origin h e)
  have s1 : ∀ k : Fin 4, ∑ x ∈ coordBall F ρ, originQuarter F (x + unitStep 0 k) =
      ∑ x ∈ coordBall F ρ, originQuarter F x := by
    intro k
    refine sum_translate (fun x => originQuarter F x) (unitStep 0 k) _ (fun x hx => (mem_coordBall hR).2 ?_)
      (fun x hx => (mem_coordBall hR).2 ?_)
    · have := hq x hx
      omega
    · have := hq x hx
      have := supNorm_intCoords_sub_unitStep hr1 x k
      omega
  have s2 : ∑ x ∈ coordBall F ρ, originQuarter F (x + unitStep 0 μ + unitStep 0 ν) =
      ∑ x ∈ coordBall F ρ, originQuarter F (x + unitStep 0 μ) := by
    have e : ∀ x : F.Site 0, x + unitStep 0 μ + unitStep 0 ν = x + unitStep 0 ν + unitStep 0 μ :=
      fun x => add_right_comm _ _ _
    simp only [e]
    refine sum_translate (fun x => originQuarter F (x + unitStep 0 μ)) (unitStep 0 ν) _
      (fun x hx => (mem_coordBall hR).2 ?_) (fun x hx => (mem_coordBall hR).2 ?_)
    · have a1 := hq (x + unitStep 0 μ) hx
      have a2 := supNorm_intCoords_le_add_unitStep hr1 x μ
      omega
    · have a1 := hq (x + unitStep 0 μ) hx
      have a2 := supNorm_intCoords_le_add_unitStep hr1 x μ
      have a3 := supNorm_intCoords_sub_unitStep hr1 x ν
      omega
  rw [s2, s1 μ, s1 ν, sum_originQuarter h hR (by omega)]
  ring
end Origin
section OriginCurl
variable {F : BlockFrame} {S : Finset F.Cell} {r q : ℕ}
def constantCandidateCurl (F : BlockFrame) (A : Fin 4 → Fin 4 → imaginaryQuaternions)
    (p : F.Site 0 × Fin 4 × Fin 4) : imaginaryQuaternions :=
  (1 / (cellSide F : ℝ) ^ 2) • A p.2.1 p.2.2
theorem sum_orderedPlanes (f : Fin 4 × Fin 4 → ℝ) :
    ∑ π ∈ orderedPlanes, f π = ∑ μ, ∑ ν ∈ Finset.univ.filter (μ < ·), f (μ, ν) := by
  unfold orderedPlanes
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_filter]
theorem cellSide_add_six_le (h : ComparisonSetup S r q) : cellSide F + 6 ≤ (r - 1) * cellSide F := by
  have hN := h.cellSide_pos
  have hq := h.five_le_scale
  have hr := h.scale_le_radius
  have h1 : 8 * cellSide F ≤ (r - 1) * cellSide F := Nat.mul_le_mul_right _ (by omega)
  nlinarith
theorem supNorm_le_of_plaquetteCellShare_ne_zero (h : ComparisonSetup S r q) {p : F.Site 0 × Fin 4 × Fin 4}
    (hw : plaquetteCellShare (0 : F.Cell) p ≠ 0) :
    supNorm (intCoords p.1) ≤ cellSide F + 2 := by
  classical
  unfold plaquetteCellShare at hw
  obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  have hc : enclosingCell y = (0 : F.Cell) := by
    by_contra hc
    exact hne (if_neg hc)
  have hs := supNorm_le_cellSide_of_origin h hc
  have hr1 := h.readsBack_one 0
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · omega
  · have := supNorm_intCoords_le_add_unitStep hr1 p.1 p.2.1
    omega
  · have := supNorm_intCoords_le_add_unitStep hr1 p.1 p.2.2
    omega
  · have a1 := supNorm_intCoords_le_add_unitStep hr1 p.1 p.2.1
    have a2 := supNorm_intCoords_le_add_unitStep hr1 (p.1 + unitStep 0 p.2.1) p.2.2
    omega
theorem sum_share_constantCandidateCurl (h : ComparisonSetup S r q) (A : Fin 4 → Fin 4 → imaginaryQuaternions) :
    ∑ p ∈ innerPlaquettes S 0, plaquetteCellShare (0 : F.Cell) p * ‖constantCandidateCurl F A p‖ ^ 2 =
      curvatureNormSq A := by
  classical
  have hN := h.cellSide_pos_real
  have hbig := cellSide_add_six_le h
  set ρ := cellSide F + 4 with hρ
  have hR : ReadsBack F 0 ρ := (h.readsBack 0).mono (by
    have e : F.blockSide ^ (F.top - 0) = cellSide F := by simp [cellSide]
    rw [e]
    have h1 : (r - 1) * cellSide F ≤ (r + 1) * cellSide F := Nat.mul_le_mul_right _ (by omega)
    omega)
  have hsub : coordBall F ρ ×ˢ orderedPlanes ⊆ innerPlaquettes S 0 := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
    have := (mem_coordBall hR).1 h1
    exact mem_innerPlaquettes_of_supNorm h p.1 h2 (by omega)
  have hz : ∀ p ∈ innerPlaquettes S 0, p ∉ coordBall F ρ ×ˢ orderedPlanes →
      plaquetteCellShare (0 : F.Cell) p * ‖constantCandidateCurl F A p‖ ^ 2 = 0 := by
    intro p hp hn
    have hplane : p.2 ∈ orderedPlanes := Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hp).2.1⟩
    have h1 : p.1 ∉ coordBall F ρ := fun h1 => hn (Finset.mem_product.2 ⟨h1, hplane⟩)
    have h2 : plaquetteCellShare (0 : F.Cell) p = 0 := by
      by_contra hw
      exact h1 ((mem_coordBall hR).2 (by have := supNorm_le_of_plaquetteCellShare_ne_zero h hw; omega))
    rw [h2, zero_mul]
  rw [← Finset.sum_subset hsub hz, Finset.sum_product, Finset.sum_comm]
  have hplane : ∀ π ∈ orderedPlanes, ∑ x ∈ coordBall F ρ,
      plaquetteCellShare (0 : F.Cell) (x, π) * ‖constantCandidateCurl F A (x, π)‖ ^ 2 = ‖A π.1 π.2‖ ^ 2 := by
    intro π hπ
    have hlt : π.1 < π.2 := (Finset.mem_filter.1 hπ).2
    have e : ∀ x : F.Site 0, ‖constantCandidateCurl F A (x, π)‖ ^ 2 =
        (1 / (cellSide F : ℝ) ^ 4) * ‖A π.1 π.2‖ ^ 2 := by
      intro x
      simp only [constantCandidateCurl]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), mul_pow]
      congr 1
      field_simp
    simp only [e]
    rw [← Finset.sum_mul]
    have hs := sum_plaquetteCellShare_plane h hR (by omega) (μ := π.1) (ν := π.2) hlt.ne
    rw [show (∑ x ∈ coordBall F ρ, plaquetteCellShare (0 : F.Cell) (x, π)) = (cellSide F : ℝ) ^ 4 from hs,
      ← mul_assoc]
    have : (cellSide F : ℝ) ^ 4 * (1 / (cellSide F : ℝ) ^ 4) = 1 := by field_simp
    rw [this, one_mul]
  rw [Finset.sum_congr rfl hplane]
  exact sum_orderedPlanes (fun π => ‖A π.1 π.2‖ ^ 2)
theorem sum_sq_coarse_le_localNorm (R : F.FieldChain) (D : ChainChart F) (z : F.Cell) :
    ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1), ‖(D.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 ≤
      localNorm S R D (unitWeights F) z ^ 2 := by
  unfold localNorm
  rw [Real.sq_sqrt (localNormSq_nonneg _ _ _ _ _)]
  unfold localNormSq
  have t2 : 0 ≤ Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (unitWeights F 0 b.1 * ‖D.fine b.1 b.2‖) ^ 4) :=
    Real.sqrt_nonneg _
  have t1 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0,
      (unitWeights F 0 p.1 * ‖linearizedCurl (R 0) D.fine p‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have e : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (unitWeights F (j + 1) c.1 * ‖D.coarse j c.1 c.2‖) ^ 2 =
      ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        ‖(D.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 := by
    simp only [unitWeights, one_mul]
    rfl
  rw [e]
  linarith
theorem cellSupDist_zero_left (z : F.Cell) : cellSupDist (0 : F.Cell) z = supNorm (intCoords z) := by
  unfold cellSupDist supNorm intCoords
  congr 1
  funext i
  simp only [Pi.zero_apply, zero_sub]
  rw [ZMod.natAbs_valMinAbs_neg]
theorem zero_mem_cells (h : ComparisonSetup S r q) : (0 : F.Cell) ∈ S := by
  have := h.box_mem 0 (fun i => by simp)
  have e : siteOfCoords F.top (0 : Fin 4 → ℤ) = (0 : F.Cell) := by
    funext i
    simp [siteOfCoords]
  rwa [e] at this
theorem mem_cellBall_zero (hz : ∀ z : F.Cell, z ∈ S → z ∈ S) {z : F.Cell} (hS : z ∈ S)
    (hd : supNorm (intCoords z) ≤ 3) :
    z ∈ cellBall S (0 : F.Cell) 3 := by
  classical
  exact Finset.mem_filter.2 ⟨hS, by rw [cellSupDist_zero_left]; exact hd⟩
end OriginCurl
section OriginShare
variable {F : BlockFrame} {S : Finset F.Cell} {r q : ℕ}
theorem sum_sq_untransportedCurl_cellBall_le (hRef : flatTopReferenceStatement) (h : ComparisonSetup S r q)
    (D : ChainChart F) (z : F.Cell) :
    ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, ‖untransportedCurl D.fine p‖ ^ 2 ≤
      localNorm S (referenceFieldChain S flatTopField) D (unitWeights F) z ^ 2 := by
  classical
  unfold localNorm
  rw [Real.sq_sqrt (localNormSq_nonneg _ _ _ _ _)]
  have e : ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, ‖untransportedCurl D.fine p‖ ^ 2 =
      ∑ p ∈ plaquettesOver S (cellBall S z 3) 0,
        (unitWeights F 0 p.1 * ‖linearizedCurl (referenceFieldChain S flatTopField 0) D.fine p‖) ^ 2 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [linearizedCurl_eq_untransported hRef h D.fine (Finset.mem_filter.1 hp).1]
    simp only [unitWeights, one_mul]
    rfl
  rw [e]
  unfold localNormSq
  have t2 : 0 ≤ Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (unitWeights F 0 b.1 * ‖D.fine b.1 b.2‖) ^ 4) :=
    Real.sqrt_nonneg _
  have t3 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (unitWeights F (j + 1) c.1 * ‖D.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith
theorem supNorm_enclosingCell_of_bond_le_one (h : ComparisonSetup S r q) {j : ℕ} (hj : j ≤ F.top) (x : F.Site j)
    (i : Fin 4)
    (hw : enclosingCell x = (0 : F.Cell) ∨ enclosingCell (x + unitStep j i) = (0 : F.Cell)) :
    supNorm (intCoords (enclosingCell x)) ≤ 1 := by
  rcases hw with hw | hw
  · rw [hw, supNorm_intCoords_zero]
    omega
  · rcases LumpContours.BlockLevels.enclosingCell_add_unitStep hj h.odd_blockSide.pos x i with e | e
    · rw [← e, hw, supNorm_intCoords_zero]
      omega
    · rw [hw] at e
      have e2 : enclosingCell x = -unitStep F.top i := by
        have : enclosingCell x + unitStep F.top i = 0 := e.symm
        exact eq_neg_of_add_eq_zero_left this
      rw [e2]
      refine Finset.sup_le fun k _ => ?_
      exact natAbs_valMinAbs_neg_unitStep_le (h.readsBack_one F.top) i k
theorem bondCellShare_ne_zero_cases {j : ℕ} {c : F.Site j × Fin 4} (hw : bondCellShare (0 : F.Cell) c ≠ 0) :
    enclosingCell c.1 = (0 : F.Cell) ∨ enclosingCell (c.1 + unitStep j c.2) = (0 : F.Cell) := by
  classical
  by_contra hc
  rw [not_or] at hc
  apply hw
  unfold bondCellShare
  rw [if_neg hc.1, if_neg hc.2]
  simp
theorem sum_bondCellShare_top_le (S : Finset F.Cell) (hL : 0 < F.blockSide) :
    ∑ c ∈ innerBonds S F.top, bondCellShare (0 : F.Cell) c ≤ 4 := by
  classical
  unfold bondCellShare
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have c1 : ((innerBonds S F.top).filter fun c => enclosingCell c.1 = (0 : F.Cell)).card ≤ 4 := by
    have hs : (innerBonds S F.top).filter (fun c => enclosingCell c.1 = (0 : F.Cell)) ⊆
        (Finset.univ : Finset (Fin 4)).image (fun μ => ((0 : F.Site F.top), μ)) := by
      intro c hc
      refine Finset.mem_image.2 ⟨c.2, Finset.mem_univ _, ?_⟩
      have := (Finset.mem_filter.1 hc).2
      rw [LumpContours.BlockLevels.enclosingCell_cell hL] at this
      exact Prod.ext this.symm rfl
    exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (by simp))
  have c2 : ((innerBonds S F.top).filter fun c => enclosingCell (c.1 + unitStep F.top c.2) = (0 : F.Cell)).card ≤ 4 := by
    have hs : (innerBonds S F.top).filter (fun c => enclosingCell (c.1 + unitStep F.top c.2) = (0 : F.Cell)) ⊆
        (Finset.univ : Finset (Fin 4)).image (fun μ => ((-unitStep F.top μ : F.Site F.top), μ)) := by
      intro c hc
      refine Finset.mem_image.2 ⟨c.2, Finset.mem_univ _, ?_⟩
      have := (Finset.mem_filter.1 hc).2
      rw [LumpContours.BlockLevels.enclosingCell_cell hL] at this
      exact Prod.ext (neg_eq_of_add_eq_zero_left this) rfl
    exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (by simp))
  have d1 : (((innerBonds S F.top).filter fun c => enclosingCell c.1 = (0 : F.Cell)).card : ℝ) ≤ 4 := by
    exact_mod_cast c1
  have d2 : (((innerBonds S F.top).filter fun c =>
      enclosingCell (c.1 + unitStep F.top c.2) = (0 : F.Cell)).card : ℝ) ≤ 4 := by
    exact_mod_cast c2
  linarith
theorem abs_two_inner_le {η : ℝ} (hη : 0 < η) (x y : ℍ[ℝ]) :
    |2 * inner ℝ x y| ≤ η * ‖x‖ ^ 2 + 1 / η * ‖y‖ ^ 2 := by
  have h1 := abs_real_inner_le_norm x y
  generalize ‖x‖ = a at *
  generalize ‖y‖ = b at *
  generalize (inner ℝ x y : ℝ) = t at *
  have h2 : 2 * (a * b) ≤ η * a ^ 2 + 1 / η * b ^ 2 := by
    have e : η * a ^ 2 + 1 / η * b ^ 2 - 2 * (a * b) = (η * a - b) ^ 2 / η := by
      field_simp
      ring
    have : 0 ≤ (η * a - b) ^ 2 / η := by positivity
    linarith
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith
theorem abs_share_sub_le_of_parts (Tp Tm Tt E X I a η M C : ℝ) (e : Tp = E + I + X)
    (hI : |I| ≤ η * E + 1 / η * X) (hX : 0 ≤ X)
    (hXM : X ≤ M ^ 2) (hm0 : 0 ≤ Tm) (hm : Tm ≤ M ^ 2) (ht0 : 0 ≤ Tt) (ht : Tt ≤ 4 * (C * M) ^ 2) (ha : 0 ≤ a)
    (hη : 0 < η) :
    |Tp + a * Tm + a * Tt - E| ≤ η * E + (1 / η + 1 + a + 4 * a * C ^ 2) * M ^ 2 := by
  have h1 : 1 / η * X ≤ 1 / η * M ^ 2 := mul_le_mul_of_nonneg_left hXM (by positivity)
  have h2 : a * Tm ≤ a * M ^ 2 := mul_le_mul_of_nonneg_left hm ha
  have h3 : a * Tt ≤ a * (4 * (C * M) ^ 2) := mul_le_mul_of_nonneg_left ht ha
  have n2 : 0 ≤ a * Tm := mul_nonneg ha hm0
  have n3 : 0 ≤ a * Tt := mul_nonneg ha ht0
  have e2 : (1 / η + 1 + a + 4 * a * C ^ 2) * M ^ 2 =
      1 / η * M ^ 2 + M ^ 2 + a * M ^ 2 + a * (4 * (C * M) ^ 2) := by ring
  rw [e2, e]
  obtain ⟨i1, i2⟩ := abs_le.1 hI
  rw [abs_le]
  constructor <;> linarith
theorem abs_responseCellShare_sub_le (hRef : flatTopReferenceStatement) (h : ComparisonSetup S r q) {a : ℝ}
    (ha : 0 ≤ a)
    (A : Fin 4 → Fin 4 → imaginaryQuaternions) (hA : ∀ μ ν, A μ ν = - A ν μ) {φ : F.Site F.top → Fin 4 → ℝ}
    (hφ : IsPotentialCutoff r φ)
    {U W : ChainChart F} {e : F.Site 0 → Fin 4 → imaginaryQuaternions}
    (hs : ResponseSplitting S U (candidateChart F q A) W e)
    {C M η : ℝ} (hC : 0 ≤ C) (hη : 0 < η)
    (hT : ∀ c ∈ innerBonds S F.top, ‖linearPart (referenceFieldChain S flatTopField) W F.top c.1 c.2‖ ≤
      C * localNorm S (referenceFieldChain S flatTopField) W (unitWeights F) (enclosingCell c.1))
    (hM : ∀ z ∈ S, supNorm (intCoords z) ≤ 1 →
      localNorm S (referenceFieldChain S flatTopField) W (unitWeights F) z ≤ M) :
    |responseCellShare a S 0 (referenceFieldChain S flatTopField) U (cutoffPotential φ A) - curvatureNormSq A| ≤
      η * curvatureNormSq A + (1 / η + 1 + a + 4 * a * C ^ 2) * M ^ 2 := by
  classical
  set R := referenceFieldChain S (flatTopField : F.GaugeField F.top) with hR
  have hq := h.five_le_scale
  have hr := h.scale_le_radius
  have h0S := zero_mem_cells h
  have hN3 : 3 ≤ cellSide F := by
    calc 3 ≤ F.blockSide := h.three_le_blockSide
      _ = F.blockSide ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right h.odd_blockSide.pos (by simp [BlockFrame.top])
  have hνM : localNorm S R W (unitWeights F) 0 ≤ M := hM 0 h0S (by rw [supNorm_intCoords_zero]; omega)
  have hν0 : 0 ≤ localNorm S R W (unitWeights F) 0 := Real.sqrt_nonneg _
  have hν2 : localNorm S R W (unitWeights F) 0 ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hν0 hνM 2
  set w : F.Site 0 × Fin 4 × Fin 4 → ℝ := fun p => plaquetteCellShare (0 : F.Cell) p with hw
  have hw0 : ∀ p, 0 ≤ w p := fun p => plaquetteCellShare_nonneg _ p
  have hw1 : ∀ p, w p ≤ 1 := fun p => plaquetteCellShare_le_one _ p
  have hcurl : ∀ p ∈ innerPlaquettes S 0, w p ≠ 0 →
      linearizedCurl (R 0) U.fine p = (constantCandidateCurl F A p : ℍ[ℝ]) + (untransportedCurl W.fine p : ℍ[ℝ]) := by
    intro p hp hne
    rw [linearizedCurl_eq_untransported hRef h U.fine hp, hs.untransportedCurl_eq h hp, Submodule.coe_add]
    have hsz := supNorm_le_of_plaquetteCellShare_ne_zero h hne
    have h6 : supNorm (intCoords p.1) + 1 ≤ 6 * q * cellSide F := by
      have : 30 * cellSide F ≤ 6 * q * cellSide F := Nat.mul_le_mul_right _ (by omega)
      omega
    have e1 : untransportedCurl (candidateChart F q A).fine p = constantCandidateCurl F A p :=
      untransportedCurl_candidate_inner h A hA p.1 p.2.1 p.2.2 h6
    rw [e1]
  set E := curvatureNormSq A with hE
  set X := ∑ p ∈ innerPlaquettes S 0, w p * ‖(untransportedCurl W.fine p : ℍ[ℝ])‖ ^ 2 with hX
  set I := ∑ p ∈ innerPlaquettes S 0, w p * (2 * inner ℝ (constantCandidateCurl F A p : ℍ[ℝ])
    (untransportedCurl W.fine p : ℍ[ℝ])) with hI
  have hE0 : ∑ p ∈ innerPlaquettes S 0, w p * ‖(constantCandidateCurl F A p : ℍ[ℝ])‖ ^ 2 = E :=
    sum_share_constantCandidateCurl h A
  have hTp : ∑ p ∈ innerPlaquettes S 0, plaquetteCellShare (0 : F.Cell) p * ‖linearizedCurl (R 0) U.fine p‖ ^ 2 =
      E + I + X := by
    rw [← hE0, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    by_cases hne : w p = 0
    · simp [hne, show plaquetteCellShare (0 : F.Cell) p = 0 from hne]
    · rw [hcurl p hp hne, norm_add_sq_real]
      show w p * _ = _
      ring
  have hIb : |I| ≤ η * E + 1 / η * X := by
    rw [← hE0, hX, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [abs_mul, abs_of_nonneg (hw0 p)]
    have := abs_two_inner_le hη (constantCandidateCurl F A p : ℍ[ℝ]) (untransportedCurl W.fine p : ℍ[ℝ])
    calc w p * _ ≤ w p * (η * ‖(constantCandidateCurl F A p : ℍ[ℝ])‖ ^ 2 +
          1 / η * ‖(untransportedCurl W.fine p : ℍ[ℝ])‖ ^ 2) :=
          mul_le_mul_of_nonneg_left this (hw0 p)
      _ = _ := by ring
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun p _ => mul_nonneg (hw0 p) (sq_nonneg _)
  have hXM : X ≤ M ^ 2 := by
    refine le_trans ?_ ((sum_sq_untransportedCurl_cellBall_le hRef h W 0).trans hν2)
    have hle : ∀ p ∈ innerPlaquettes S 0, w p * ‖(untransportedCurl W.fine p : ℍ[ℝ])‖ ^ 2 ≤
        if p ∈ plaquettesOver S (cellBall S (0 : F.Cell) 3) 0 then ‖untransportedCurl W.fine p‖ ^ 2 else 0 := by
      intro p hp
      split_ifs with hin
      · calc _ ≤ 1 * ‖(untransportedCurl W.fine p : ℍ[ℝ])‖ ^ 2 := mul_le_mul_of_nonneg_right (hw1 p) (sq_nonneg _)
          _ = _ := one_mul _
      · have hz : w p = 0 := by
          by_contra hne
          apply hin
          refine Finset.mem_filter.2 ⟨hp, ?_⟩
          have hsz := supNorm_le_of_plaquetteCellShare_ne_zero h hne
          have hc : plaquetteCorners p ⊆ sitesOfCells S 0 := (Finset.mem_filter.1 hp).2.2
          have hcS := LumpContours.BlockLevels.enclosingCell_mem_of_mem_sitesOfCells (Nat.zero_le _)
            h.odd_blockSide (hc (by simp [plaquetteCorners] : p.1 ∈ plaquetteCorners p))
          have := supNorm_enclosingCell_le h p.1 (t := 2) (by omega) (by omega)
          exact mem_cellBall_zero (fun _ x => x) hcS (by omega)
        rw [hz, zero_mul]
    refine (Finset.sum_le_sum hle).trans ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
    intro p hp
    exact (Finset.mem_filter.1 hp).2
  set Tm := ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ innerBonds S (j + 1),
      bondCellShare (0 : F.Cell) c * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 with hTm
  set Tt := ∑ c ∈ innerBonds S F.top,
      bondCellShare (0 : F.Cell) c * ‖topDirectionDefect R U (cutoffPotential φ A) c‖ ^ 2 with hTt
  have hm0 : 0 ≤ Tm := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun c _ =>
    mul_nonneg (bondCellShare_nonneg _ c) (sq_nonneg _)
  have hmM : Tm ≤ M ^ 2 := by
    refine le_trans ?_ ((sum_sq_coarse_le_localNorm (S := S) R W 0).trans hν2)
    refine Finset.sum_le_sum fun j hj => ?_
    have hjn : j + 1 ≤ F.top := by
      have := Finset.mem_range.1 hj
      omega
    have hle : ∀ c ∈ innerBonds S (j + 1), bondCellShare (0 : F.Cell) c * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 ≤
        if c ∈ bondsOver S (cellBall S (0 : F.Cell) 3) (j + 1) then ‖(W.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 else 0 := by
      intro c hc
      split_ifs with hin
      · rw [hs.coarse_eq]
        calc _ ≤ 1 * ‖(W.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (bondCellShare_le_one _ c) (sq_nonneg _)
          _ = _ := one_mul _
      · have hz : bondCellShare (0 : F.Cell) c = 0 := by
          by_contra hne
          apply hin
          refine Finset.mem_filter.2 ⟨hc, ?_⟩
          have hsz := supNorm_enclosingCell_of_bond_le_one h hjn c.1 c.2 (bondCellShare_ne_zero_cases hne)
          have hc1 : c.1 ∈ sitesOfCells S (j + 1) := by
            simp only [innerBonds, Finset.mem_filter, Finset.mem_product] at hc
            exact hc.1.1
          have hcS := LumpContours.BlockLevels.enclosingCell_mem_of_mem_sitesOfCells hjn h.odd_blockSide hc1
          exact mem_cellBall_zero (fun _ x => x) hcS (by omega)
        rw [hz, zero_mul]
    refine (Finset.sum_le_sum hle).trans ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
    intro c hc
    exact (Finset.mem_filter.1 hc).2
  have ht0 : 0 ≤ Tt := Finset.sum_nonneg fun c _ => mul_nonneg (bondCellShare_nonneg _ c) (sq_nonneg _)
  have htM : Tt ≤ 4 * (C * M) ^ 2 := by
    have hle : ∀ c ∈ innerBonds S F.top,
        bondCellShare (0 : F.Cell) c * ‖topDirectionDefect R U (cutoffPotential φ A) c‖ ^ 2 ≤
        bondCellShare (0 : F.Cell) c * (C * M) ^ 2 := by
      intro c hc
      by_cases hne : bondCellShare (0 : F.Cell) c = 0
      · rw [hne, zero_mul, zero_mul]
      refine mul_le_mul_of_nonneg_left ?_ (bondCellShare_nonneg _ c)
      have hsz := supNorm_enclosingCell_of_bond_le_one h le_rfl c.1 c.2 (bondCellShare_ne_zero_cases hne)
      rw [LumpContours.BlockLevels.enclosingCell_cell h.odd_blockSide.pos] at hsz
      have hgap := topDirectionDefect_eq_zero_inner hRef h A hA hφ c.1 c.2 (by omega)
      have hc1 : c.1 ∈ S := by
        simp only [innerBonds, Finset.mem_filter, Finset.mem_product] at hc
        exact mem_sitesOfCells_top.1 hc.1.1
      have e1 : topDirectionDefect R U (cutoffPotential φ A) c = - linearPart R W F.top c.1 c.2 := by
        have e2 : topDirectionDefect R (candidateChart F q A) (cutoffPotential φ A) c = 0 := hgap
        unfold topDirectionDefect at e2 ⊢
        rw [hs.linearPart_top_eq h.odd_blockSide hc]
        rw [sub_eq_zero] at e2
        rw [e2]
        abel
      rw [e1, norm_neg]
      have h1 := hT c hc
      rw [LumpContours.BlockLevels.enclosingCell_cell h.odd_blockSide.pos] at h1
      have h2 := hM c.1 hc1 hsz
      have h3 : ‖linearPart R W F.top c.1 c.2‖ ≤ C * M := h1.trans (mul_le_mul_of_nonneg_left h2 hC)
      exact pow_le_pow_left₀ (norm_nonneg _) h3 2
    refine (Finset.sum_le_sum hle).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_bondCellShare_top_le S h.odd_blockSide.pos) (sq_nonneg _)
  have hfin := abs_share_sub_le_of_parts _ Tm Tt E X I a η M C hTp hIb hX0 hXM hm0 hmM ht0 htM ha hη
  exact hfin
end OriginShare
section FlatDifference
variable {F : BlockFrame} {S : Finset F.Cell} {r q : ℕ}
theorem isCold_flatTopField (S : Finset F.Cell) {s : ℝ} (hs : 0 < s) :
    IsCold S F.top s (flatTopField : F.GaugeField F.top) := by apply _root_.YangMills.Construction.BlockAverages.CriticalChainFirstOrder.flatTopField_isCold <;> assumption
theorem eq_zero_of_le_mul_small {Y K c : ℝ} (hc : 0 < c) (hY : 0 ≤ Y) (h : ∀ s, 0 < s → s ≤ c → Y ≤ K * s) :
    Y = 0 := by apply _root_.YangMills.Construction.BlockAverages.FlatTopHessian.eq_zero_of_le_mul_small <;> assumption
theorem classWeight_zero_eq_one (p : F.Site 0) (j : ℕ) (x : F.Site j) : classWeight F (fun _ => 0) 0 p j x = 1 := by
  simp [classWeight]
theorem covariantDiff_null_at_flat {c C : ℝ} (hc : 0 < c)
    (hD : ∀ (m : ℕ) (S' : Finset F.Cell), F.blockSide = F.blockSide → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S' m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S' F.top s V →
        ∀ (φ : F.Cell → ℝ) (θ del : ℝ) (p : F.Site 0), |θ| ≤ 1 / 8 → |del| ≤ 1 / 8 →
          (∀ y y', |φ y - φ y'| ≤ |del| * cellSupDist y y') →
          ∀ (ξ : F.Site 0 → ℍ[ℝ]) (v : F.Site 0 → Fin 4 → imaginaryQuaternions), GaugeMap.CellMeanFree S' V ξ →
            (∀ x i, ((v x i : imaginaryQuaternions) : ℍ[ℝ]) = covariantDiff (referenceFieldChain S' V 0) ξ x i) →
            Real.sqrt (∑ q ∈ plaquettesOver S' S' 0, (classWeight F φ θ p 0 q.1 *
                ‖linearizedCurl (referenceFieldChain S' V 0) v q‖) ^ 2) +
              Real.sqrt (∑ c ∈ innerBonds S' F.top, (classWeight F φ θ p F.top c.1 *
                ‖linearPart (referenceFieldChain S' V) (baseOnlyChart v) F.top c.1 c.2‖) ^ 2) ≤
            C * s * cellwiseL4Norm S' (classWeight F φ θ p 0) (fun x i => v x i))
    {m : ℕ} (hamb : IsAdmissibleAmbient F) (hm : 1024 ≤ m) (hreg : IsOrthantRegular S m)
    {ξ : F.Site 0 → ℍ[ℝ]} {e : F.Site 0 → Fin 4 → imaginaryQuaternions}
    (hmf : GaugeMap.CellMeanFree S flatTopField ξ)
    (he : ∀ x i, ((e x i : imaginaryQuaternions) : ℍ[ℝ]) = covariantDiff (referenceFieldChain S flatTopField 0) ξ x i) :
    (∀ p ∈ plaquettesOver S S 0, linearizedCurl (referenceFieldChain S flatTopField 0) e p = 0) ∧
      ∀ b ∈ innerBonds S F.top, linearPart (referenceFieldChain S flatTopField) (baseOnlyChart e) F.top b.1 b.2 = 0 := by
  set X := cellwiseL4Norm S (classWeight F (fun _ => 0) 0 (0 : F.Site 0) 0) (fun x i => e x i) with hX
  set Y1 := ∑ q ∈ plaquettesOver S S 0, (classWeight F (fun _ => 0) 0 (0 : F.Site 0) 0 q.1 *
      ‖linearizedCurl (referenceFieldChain S flatTopField 0) e q‖) ^ 2 with hY1
  set Y2 := ∑ c ∈ innerBonds S F.top, (classWeight F (fun _ => 0) 0 (0 : F.Site 0) F.top c.1 *
      ‖linearPart (referenceFieldChain S flatTopField) (baseOnlyChart e) F.top c.1 c.2‖) ^ 2 with hY2
  have hb : ∀ s, 0 < s → s ≤ c → Real.sqrt Y1 + Real.sqrt Y2 ≤ (C * X) * s := by
    intro s hs hsc
    have := hD m S rfl hamb hm hreg s flatTopField hs hsc (isCold_flatTopField S hs) (fun _ => 0) 0 0 0
      (by norm_num) (by norm_num)
      (fun y y' => by simp) ξ e hmf he
    calc _ ≤ _ := this
      _ = _ := by ring
  have hz := eq_zero_of_le_mul_small hc (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hb
  have s1 : Real.sqrt Y1 = 0 := by
    have := Real.sqrt_nonneg Y1
    have := Real.sqrt_nonneg Y2
    linarith
  have s2 : Real.sqrt Y2 = 0 := by
    have := Real.sqrt_nonneg Y1
    have := Real.sqrt_nonneg Y2
    linarith
  have y1n : 0 ≤ Y1 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have y2n : 0 ≤ Y2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have y1 : Y1 = 0 := (Real.sqrt_eq_zero y1n).1 s1
  have y2 : Y2 = 0 := (Real.sqrt_eq_zero y2n).1 s2
  refine ⟨fun p hp => ?_, fun b hb' => ?_⟩
  · have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 y1 p hp
    rw [classWeight_zero_eq_one, one_mul] at this
    exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
  · have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 y2 b hb'
    rw [classWeight_zero_eq_one, one_mul] at this
    exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
end FlatDifference
section Assembly
variable {F : BlockFrame} {S : Finset F.Cell} {r q : ℕ}
theorem sq_norm_le_curvatureNormSq (A : Fin 4 → Fin 4 → imaginaryQuaternions) (hA : ∀ μ ν, A μ ν = - A ν μ)
    (ν μ : Fin 4) :
    ‖A ν μ‖ ^ 2 ≤ curvatureNormSq A := by
  classical
  have hE0 : 0 ≤ curvatureNormSq A :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have key : ∀ a b : Fin 4, a < b → ‖A a b‖ ^ 2 ≤ curvatureNormSq A := by
    intro a b hab
    unfold curvatureNormSq
    have h1 : ‖A a b‖ ^ 2 ≤ ∑ b' ∈ Finset.univ.filter (a < ·), ‖A a b'‖ ^ 2 :=
      Finset.single_le_sum (f := fun b' => ‖A a b'‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hab⟩)
    refine h1.trans ?_
    exact Finset.single_le_sum (f := fun a' => ∑ b' ∈ Finset.univ.filter (a' < ·), ‖A a' b'‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ a)
  rcases lt_trichotomy ν μ with h | h | h
  · exact key _ _ h
  · subst h
    rw [diag_eq_zero_of_antisymm A hA]
    simpa using hE0
  · rw [hA ν μ, norm_neg]
    exact key _ _ h
theorem sq_curvatureL1_le (A : Fin 4 → Fin 4 → imaginaryQuaternions) (hA : ∀ μ ν, A μ ν = - A ν μ) :
    curvatureL1 A ^ 2 ≤ 256 * curvatureNormSq A := by
  have hE0 : 0 ≤ curvatureNormSq A :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : ∀ ν μ, ‖A ν μ‖ ≤ Real.sqrt (curvatureNormSq A) := fun ν μ =>
    Real.le_sqrt_of_sq_le (sq_norm_le_curvatureNormSq A hA ν μ)
  have h2 : curvatureL1 A ≤ 16 * Real.sqrt (curvatureNormSq A) := by
    unfold curvatureL1
    calc ∑ ν, ∑ μ, ‖A ν μ‖ ≤ ∑ _ν : Fin 4, ∑ _μ : Fin 4, Real.sqrt (curvatureNormSq A) :=
          Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun μ _ => h1 ν μ
      _ = _ := by
        simp
        ring
  have h3 := pow_le_pow_left₀ (curvatureL1_nonneg A) h2 2
  refine h3.trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt hE0]
  norm_num
open Classical in
def cellCoordBall (F : BlockFrame) (ρ : ℕ) : Finset F.Cell :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(ρ : ℤ)) ρ).image (siteOfCoords F.top)
theorem card_cellCoordBall_le (ρ : ℕ) : ((cellCoordBall F ρ).card : ℝ) ≤ (2 * (ρ : ℝ) + 1) ^ 4 := by
  classical
  have h1 := Finset.card_image_le (s := Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(ρ : ℤ)) ρ)
    (f := (siteOfCoords F.top : (Fin 4 → ℤ) → F.Cell))
  have h2 : (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(ρ : ℤ)) ρ).card = (2 * ρ + 1) ^ 4 := by
    rw [Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    omega
  have h3 : (cellCoordBall F ρ).card ≤ (2 * ρ + 1) ^ 4 := h2 ▸ h1
  have h4 : ((cellCoordBall F ρ).card : ℝ) ≤ (((2 * ρ + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast h3
  push_cast at h4
  exact h4
theorem mem_cellCoordBall {ρ : ℕ} {y : F.Cell} (hy : supNorm (intCoords y) ≤ ρ) : y ∈ cellCoordBall F ρ := by
  classical
  refine Finset.mem_image.2 ⟨intCoords y, Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ?_,
    siteOfCoords_intCoords y⟩
  have h1 := natAbs_le_supNorm (intCoords y) i
  have h2 : |intCoords y i| ≤ ρ := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1.trans hy
  exact abs_le.1 h2
theorem card_comparisonShell_le : ((comparisonShell S q r).card : ℝ) ≤ (2 * (r : ℝ) + 7) ^ 4 := by
  classical
  have hsub : comparisonShell S q r ⊆ cellCoordBall F (r + 3) := fun z hz =>
    mem_cellCoordBall (Finset.mem_filter.1 hz).2.2
  have h1 : ((comparisonShell S q r).card : ℝ) ≤ ((cellCoordBall F (r + 3)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  refine h1.trans ((card_cellCoordBall_le _).trans (le_of_eq ?_))
  push_cast
  ring
theorem sum_sq_cutoffPotential_le (A : Fin 4 → Fin 4 → imaginaryQuaternions) {φ : F.Site F.top → Fin 4 → ℝ}
    (hφ : IsPotentialCutoff r φ) :
    ∑ c ∈ innerBonds S F.top, ‖(cutoffPotential φ A c.1 c.2 : ℍ[ℝ])‖ ^ 2 ≤
      4 * (2 * (r : ℝ) + 1) ^ 4 * ((r : ℝ) * curvatureL1 A) ^ 2 := by
  classical
  set t := ((r : ℝ) * curvatureL1 A) ^ 2 with ht
  have ht0 : 0 ≤ t := sq_nonneg _
  have hterm : ∀ c ∈ innerBonds S F.top, ‖(cutoffPotential φ A c.1 c.2 : ℍ[ℝ])‖ ^ 2 ≤
      if c ∈ cellCoordBall F r ×ˢ (Finset.univ : Finset (Fin 4)) then t else 0 := by
    intro c _
    split_ifs with hin
    · exact pow_le_pow_left₀ (norm_nonneg _) (norm_cutoffPotential_le A hφ c.1 c.2) 2
    · have hn : ¬ BondWithinRadius r (minimalCoords c.1, c.2) := by
        intro hb
        exact hin (Finset.mem_product.2 ⟨mem_cellCoordBall (supNorm_le_of_bondWithinRadius c.1 c.2 hb),
          Finset.mem_univ _⟩)
      have : cutoffPotential φ A c.1 c.2 = 0 := by
        unfold cutoffPotential
        rw [hφ.eq_zero _ _ hn, zero_smul]
      rw [this]
      simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_filter]
  have hs : ∑ c ∈ (innerBonds S F.top).filter (fun c => c ∈ cellCoordBall F r ×ˢ (Finset.univ : Finset (Fin 4))), t ≤
      ∑ _c ∈ cellCoordBall F r ×ˢ (Finset.univ : Finset (Fin 4)), t := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => ht0
    intro c hc
    exact (Finset.mem_filter.1 hc).2
  refine hs.trans ?_
  rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
  have h1 := card_cellCoordBall_le (F := F) r
  push_cast
  simp only [Finset.card_univ, Fintype.card_fin]
  push_cast
  nlinarith
theorem abs_share_sub_le_of_estimate (hRef : flatTopReferenceStatement) (h : ComparisonSetup S r q) {a : ℝ}
    (ha : 0 < a)
    (A : Fin 4 → Fin 4 → imaginaryQuaternions) (hA : ∀ μ ν, A μ ν = - A ν μ) {φ : F.Site F.top → Fin 4 → ℝ}
    (hφ : IsPotentialCutoff r φ)
    {del Ca C : ℝ} (hdel : 0 ≤ del) (hCa : 0 ≤ Ca) (hC : 0 ≤ C)
    {U W : ChainChart F} {e : F.Site 0 → Fin 4 → imaginaryQuaternions}
    (hs : ResponseSplitting S U (candidateChart F q A) W e)
    (hEst : ∀ B : ℝ, 0 ≤ B →
      (∀ D : ChainChart F, GaugeMap.InGaugeSlice S flatTopField (referenceFieldChain S flatTopField 0) D.fine →
        |responseLinear a S (referenceFieldChain S flatTopField) (cutoffPotential φ A) D -
          responseBilinear a S (referenceFieldChain S flatTopField) (candidateChart F q A) D| ≤
        B * _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S flatTopField) D
          (invertedWeights (classWeight F (linearDecay del) 0 (0 : F.Site 0)))) →
      _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S flatTopField) W (classWeight F (linearDecay del) 0 (0 : F.Site 0)) ≤ Ca * B)
    (hTop : ∀ (D : ChainChart F), ∀ c ∈ innerBonds S F.top,
      ‖linearPart (referenceFieldChain S flatTopField) D F.top c.1 c.2‖ ≤
        C * localNorm S (referenceFieldChain S flatTopField) D (unitWeights F) (enclosingCell c.1))
    {η : ℝ} (hη : 0 < η) :
    |responseCellShare a S 0 (referenceFieldChain S flatTopField) U (cutoffPotential φ A) - curvatureNormSq A| ≤
      η * curvatureNormSq A + (1 / η + 1 + a + 4 * a * C ^ 2) *
        (Real.exp (4 * del) * (Ca * ((a * (8 * r * C) + 99) * curvatureL1 A *
          (Real.exp (-del * (((4 * q - 2 : ℕ) : ℝ) - 3)) * Real.sqrt ((comparisonShell S q r).card))))) ^ 2 := by
  set R := referenceFieldChain S (flatTopField : F.GaugeField F.top) with hR
  set K := (a * (8 * r * C) + 99) * curvatureL1 A with hK
  have hS := curvatureL1_nonneg A
  have hK0 : 0 ≤ K := by positivity
  set B := K * (Real.exp (-del * (((4 * q - 2 : ℕ) : ℝ) - 3)) * Real.sqrt ((comparisonShell S q r).card)) with hB
  have hB0 : 0 ≤ B := by positivity
  have hbound : ∀ D : ChainChart F, GaugeMap.InGaugeSlice S flatTopField (R 0) D.fine →
      |responseLinear a S R (cutoffPotential φ A) D - responseBilinear a S R (candidateChart F q A) D| ≤
        B * _root_.YangMills.Construction.BlockAverages.weightedNorm S R D (invertedWeights (classWeight F (linearDecay del) 0 (0 : F.Site 0))) := by
    intro D _
    refine (abs_responseLinear_sub_bilinear_le hRef h ha.le A hA hφ hC D (hTop D)).trans ?_
    have h1 := sum_localNorm_le S (comparisonShell S q r) (Finset.filter_subset _ _) R D hdel (0 : F.Site 0)
      (d₀ := ((4 * q - 2 : ℕ) : ℝ)) (fun z hz => by
        rw [cellSupDist_comm, cellSupDist_zero_left]
        exact_mod_cast (Finset.mem_filter.1 hz).2.1)
    calc K * _ ≤ K * _ := mul_le_mul_of_nonneg_left h1 hK0
      _ = _ := by rw [hB]; ring
  have hOver := hEst B hB0 hbound
  set M := Real.exp (4 * del) * (Ca * B) with hMd
  have hM : ∀ z ∈ S, supNorm (intCoords z) ≤ 1 → localNorm S R W (unitWeights F) z ≤ M := by
    intro z hz hsz
    have h1 := localNorm_le_weighted S z R W hdel (0 : F.Site 0)
    have h2 := (localNorm_le_weightedNorm S R W (classWeight F (linearDecay del) 0 (0 : F.Site 0)) hz).trans hOver
    have hd : (cellSupDist z (0 : F.Cell) : ℝ) ≤ 1 := by
      rw [cellSupDist_comm, cellSupDist_zero_left]
      exact_mod_cast hsz
    have hν : 0 ≤ localNorm S R W (unitWeights F) z := Real.sqrt_nonneg _
    have h3 : Real.exp (-del * 4) ≤ Real.exp (-del * ((cellSupDist z (0 : F.Cell) : ℝ) + 3)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h4 : Real.exp (-del * 4) * localNorm S R W (unitWeights F) z ≤ Ca * B :=
      (mul_le_mul_of_nonneg_right h3 hν).trans (h1.trans h2)
    have e : Real.exp (4 * del) * Real.exp (-del * 4) = 1 := by
      rw [← Real.exp_add]
      simp [mul_comm]
    calc localNorm S R W (unitWeights F) z
        = Real.exp (4 * del) * (Real.exp (-del * 4) * localNorm S R W (unitWeights F) z) := by
          rw [← mul_assoc, e, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
  have := abs_responseCellShare_sub_le hRef h ha.le A hA hφ hs hC hη (hTop W) hM
  rw [hMd, hB, hK] at this
  exact this
end Assembly
section Constants
def restConstant (a C Ca del : ℝ) : ℝ := Real.exp (26 * del) * Ca ^ 2 * (8 * a * C + 99) ^ 2 * 20736
theorem restConstant_nonneg {a C Ca del : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) : 0 ≤ restConstant a C Ca del := by
  unfold restConstant
  positivity
theorem rest_sq_le {a C Ca del E Y n r d qr : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hdel : 0 < del)
    (hE : 0 ≤ E) (hY0 : 0 ≤ Y) (hY : Y ^ 2 ≤ 256 * E) (hn0 : 0 ≤ n) (hn : n ≤ (2 * r + 7) ^ 4) (hr : 120 ≤ r)
    (hd : d = 4 * qr - 2) (hq : r < 24 * qr + 24) :
    (Real.exp (4 * del) * (Ca * ((a * (8 * r * C) + 99) * Y * (Real.exp (-del * (d - 3)) * Real.sqrt n)))) ^ 2 ≤
      restConstant a C Ca del * E * r ^ 6 * Real.exp (-del * r / 3) := by
  have hk0 : 0 ≤ a * (8 * r * C) + 99 := by positivity
  have hk : a * (8 * r * C) + 99 ≤ (8 * a * C + 99) * r := by
    have : 0 ≤ 8 * a * C * r := by positivity
    nlinarith
  have e1 : (Real.exp (4 * del) * (Ca * ((a * (8 * r * C) + 99) * Y * (Real.exp (-del * (d - 3)) *
      Real.sqrt n)))) ^ 2 =
      Real.exp (8 * del) * Ca ^ 2 * (a * (8 * r * C) + 99) ^ 2 * Y ^ 2 *
        Real.exp (-2 * del * (d - 3)) * n := by
    have s1 : Real.exp (4 * del) ^ 2 = Real.exp (8 * del) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have s2 : Real.exp (-del * (d - 3)) ^ 2 = Real.exp (-2 * del * (d - 3)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have s3 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0
    calc _ = Real.exp (4 * del) ^ 2 * Ca ^ 2 * (a * (8 * r * C) + 99) ^ 2 * Y ^ 2 *
          Real.exp (-del * (d - 3)) ^ 2 * Real.sqrt n ^ 2 := by ring
      _ = _ := by rw [s1, s2, s3]
  rw [e1]
  have b1 : (a * (8 * r * C) + 99) ^ 2 ≤ (8 * a * C + 99) ^ 2 * r ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hk0 hk 2
  have b3 : Real.exp (-2 * del * (d - 3)) ≤ Real.exp (18 * del) * Real.exp (-del * r / 3) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    rw [hd]
    nlinarith
  have b4 : n ≤ 81 * r ^ 4 := by
    refine hn.trans ?_
    have : 2 * r + 7 ≤ 3 * r := by linarith
    calc (2 * r + 7) ^ 4 ≤ (3 * r) ^ 4 := pow_le_pow_left₀ (by linarith) this 4
      _ = _ := by ring
  have e2 : Real.exp (8 * del) * Real.exp (18 * del) = Real.exp (26 * del) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc Real.exp (8 * del) * Ca ^ 2 * (a * (8 * r * C) + 99) ^ 2 * Y ^ 2 * Real.exp (-2 * del * (d - 3)) * n
      ≤ Real.exp (8 * del) * Ca ^ 2 * ((8 * a * C + 99) ^ 2 * r ^ 2) * (256 * E) *
          (Real.exp (18 * del) * Real.exp (-del * r / 3)) * (81 * r ^ 4) := by gcongr
    _ = (Real.exp (8 * del) * Real.exp (18 * del)) * Ca ^ 2 * (8 * a * C + 99) ^ 2 * 20736 * E * r ^ 6 *
          Real.exp (-del * r / 3) := by ring
    _ = _ := by rw [e2]; rfl
def largeRadiusConstant (a C Ca del : ℝ) : ℝ :=
  1 + restConstant a C Ca del + (1 + a + 4 * a * C ^ 2) * restConstant a C Ca del * (32 / del ^ 2)
theorem large_radius_bound {a C Ca del δ E r T : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hdel : 0 < del) (hδ : 0 < δ)
    (hδ12 : δ ≤ del / 12) (hE : 0 ≤ E) (hr : 120 ≤ r) (hT0 : 0 ≤ T)
    (hT : T ≤ restConstant a C Ca del * E * r ^ 6 * Real.exp (-del * r / 3)) :
    (r ^ 3 * Real.exp (-del * r / 6)) * E +
        (1 / (r ^ 3 * Real.exp (-del * r / 6)) + 1 + a + 4 * a * C ^ 2) * T ≤
      largeRadiusConstant a C Ca del * E * r ^ 4 * Real.exp (-δ * r) := by
  have hr1 : 1 ≤ r := by linarith
  set G := restConstant a C Ca del with hG
  have hG0 : 0 ≤ G := restConstant_nonneg ha hC
  set e6 := Real.exp (-del * r / 6) with he6
  set eδ := Real.exp (-δ * r) with heδ
  have he60 : 0 < e6 := Real.exp_pos _
  have e3 : Real.exp (-del * r / 3) = e6 ^ 2 := by
    rw [he6, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [e3] at hT
  set c₁ := 1 + a + 4 * a * C ^ 2 with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  have t1 : 1 / (r ^ 3 * e6) * T ≤ G * E * r ^ 3 * e6 := by
    calc 1 / (r ^ 3 * e6) * T ≤ 1 / (r ^ 3 * e6) * (G * E * r ^ 6 * e6 ^ 2) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ = _ := by
        field_simp
  have he6δ : e6 ≤ eδ := by
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hr34 : r ^ 3 ≤ r ^ 4 := by
    have : r ^ 3 * 1 ≤ r ^ 3 * r := mul_le_mul_of_nonneg_left hr1 (by positivity)
    calc r ^ 3 = r ^ 3 * 1 := (mul_one _).symm
      _ ≤ r ^ 3 * r := this
      _ = r ^ 4 := by ring
  have p1 : r ^ 3 * e6 ≤ r ^ 4 * eδ := mul_le_mul hr34 he6δ he60.le (by positivity)
  set e4 := Real.exp (-del * r / 4) with he4
  have he40 : 0 < e4 := Real.exp_pos _
  have hsplit : e6 ^ 2 ≤ eδ * e4 := by
    rw [← e3, he4, heδ, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hquad : r ^ 2 * e4 ≤ 32 / del ^ 2 := by
    have hx : 0 ≤ del * r / 4 := by positivity
    have h1 := Real.quadratic_le_exp_of_nonneg hx
    have h2 : (del * r / 4) ^ 2 / 2 ≤ Real.exp (del * r / 4) := by
      have : 0 ≤ 1 + del * r / 4 := by positivity
      linarith
    have e5 : e4 * Real.exp (del * r / 4) = 1 := by
      rw [he4, ← Real.exp_add]
      have : -del * r / 4 + del * r / 4 = 0 := by ring
      rw [this, Real.exp_zero]
    have h3 : (del * r / 4) ^ 2 / 2 * e4 ≤ 1 := by
      calc _ ≤ Real.exp (del * r / 4) * e4 := mul_le_mul_of_nonneg_right h2 he40.le
        _ = 1 := by rw [mul_comm]; exact e5
    have e6' : r ^ 2 * e4 = 32 / del ^ 2 * ((del * r / 4) ^ 2 / 2 * e4) := by
      field_simp
      ring
    rw [e6']
    calc 32 / del ^ 2 * ((del * r / 4) ^ 2 / 2 * e4) ≤ 32 / del ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := mul_one _
  have p2 : r ^ 6 * e6 ^ 2 ≤ r ^ 4 * eδ * (32 / del ^ 2) := by
    calc r ^ 6 * e6 ^ 2 ≤ r ^ 6 * (eδ * e4) := mul_le_mul_of_nonneg_left hsplit (by positivity)
      _ = r ^ 4 * eδ * (r ^ 2 * e4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hquad (by positivity)
  have q1 : G * E * r ^ 3 * e6 ≤ G * E * (r ^ 4 * eδ) := by
    calc G * E * r ^ 3 * e6 = G * E * (r ^ 3 * e6) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left p1 (by positivity)
  have q2 : c₁ * T ≤ c₁ * G * E * (r ^ 4 * eδ * (32 / del ^ 2)) := by
    calc c₁ * T ≤ c₁ * (G * E * r ^ 6 * e6 ^ 2) := mul_le_mul_of_nonneg_left hT hc₁0
      _ = c₁ * G * E * (r ^ 6 * e6 ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left p2 (by positivity)
  have q3 : r ^ 3 * e6 * E ≤ r ^ 4 * eδ * E := mul_le_mul_of_nonneg_right p1 hE
  have e7 : (1 / (r ^ 3 * e6) + 1 + a + 4 * a * C ^ 2) * T = 1 / (r ^ 3 * e6) * T + c₁ * T := by
    rw [hc₁]
    ring
  rw [e7]
  have e8 : largeRadiusConstant a C Ca del * E * r ^ 4 * eδ =
      r ^ 4 * eδ * E + G * E * (r ^ 4 * eδ) + c₁ * G * E * (r ^ 4 * eδ * (32 / del ^ 2)) := by
    unfold largeRadiusConstant
    rw [← hG, ← hc₁]
    ring
  rw [e8]
  linarith
end Constants
section Conclusion
variable {F : BlockFrame} {S : Finset F.Cell}
def smallRadiusConstant (a : ℝ) : ℝ := 8 * (a * (4 * 241 ^ 4 * 120 ^ 2 * 256) + 1)
theorem responseCellShare_nonneg {a : ℝ} (ha : 0 ≤ a) (Y : F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) : 0 ≤ responseCellShare a S Y R U v := by
  unfold responseCellShare
  refine add_nonneg (add_nonneg ?_ (mul_nonneg ha ?_)) (mul_nonneg ha ?_)
  · exact Finset.sum_nonneg fun p _ => mul_nonneg (plaquetteCellShare_nonneg _ p) (sq_nonneg _)
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun c _ => mul_nonneg (bondCellShare_nonneg _ c) (sq_nonneg _)
  · exact Finset.sum_nonneg fun c _ => mul_nonneg (bondCellShare_nonneg _ c) (sq_nonneg _)
theorem abs_share_sub_le_small_radius {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 60) {r : ℕ}
    (hr1 : 1 ≤ r) (hr : r < 120)
    (A : Fin 4 → Fin 4 → imaginaryQuaternions) (hA : ∀ μ ν, A μ ν = - A ν μ) {φ : F.Site F.top → Fin 4 → ℝ}
    (hφ : IsPotentialCutoff r φ)
    {U : ChainChart F} (hU : IsFlatTopResponse a S (cutoffPotential φ A) U) {N0 : ℝ}
    (hN : smallRadiusConstant a ≤ N0) :
    |responseCellShare a S 0 (referenceFieldChain S flatTopField) U (cutoffPotential φ A) - curvatureNormSq A| ≤
      N0 * curvatureNormSq A * (r : ℝ) ^ 4 * Real.exp (-δ * r) := by
  set x := responseCellShare a S 0 (referenceFieldChain S flatTopField) U (cutoffPotential φ A) with hx
  set E := curvatureNormSq A with hE
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hx0 : 0 ≤ x := responseCellShare_nonneg ha.le _ _ _ _
  have hrR : (r : ℝ) ≤ 120 := by
    have : (r : ℝ) < 120 := by exact_mod_cast hr
    linarith
  have hr1R : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hv := sum_sq_cutoffPotential_le (S := S) A hφ
  have hS := sq_curvatureL1_le A hA
  have hSum : 4 * (2 * (r : ℝ) + 1) ^ 4 * ((r : ℝ) * curvatureL1 A) ^ 2 ≤
      (4 * 241 ^ 4 * 120 ^ 2 * 256) * E := by
    have h1 : (2 * (r : ℝ) + 1) ^ 4 ≤ 241 ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    have h2 : (r : ℝ) ^ 2 ≤ 120 ^ 2 := pow_le_pow_left₀ (by positivity) hrR 2
    have e : ((r : ℝ) * curvatureL1 A) ^ 2 = (r : ℝ) ^ 2 * curvatureL1 A ^ 2 := by ring
    rw [e]
    calc 4 * (2 * (r : ℝ) + 1) ^ 4 * ((r : ℝ) ^ 2 * curvatureL1 A ^ 2) ≤
          4 * 241 ^ 4 * (120 ^ 2 * (256 * E)) := by
          gcongr
      _ = _ := by ring
  have hxb : x ≤ a * ((4 * 241 ^ 4 * 120 ^ 2 * 256) * E) :=
    (responseCellShare_le_energy ha.le 0 _ hU).trans (mul_le_mul_of_nonneg_left (hv.trans hSum) ha.le)
  have h1 : |x - E| ≤ (a * (4 * 241 ^ 4 * 120 ^ 2 * 256) + 1) * E := by
    rw [abs_le]
    constructor <;> nlinarith
  have hexp : 1 / 8 ≤ Real.exp (-δ * r) := by
    have h2 : -2 ≤ -δ * r := by nlinarith
    have h3 : Real.exp (-2) ≤ Real.exp (-δ * r) := Real.exp_le_exp.2 h2
    refine le_trans ?_ h3
    have h4 : Real.exp 2 ≤ 8 := by
      have e1 := Real.exp_one_lt_d9
      have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [e2]
      have hp := Real.exp_pos 1
      nlinarith
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos 2) h4
  have hr4 : 1 ≤ (r : ℝ) ^ 4 := one_le_pow₀ hr1R
  have hN0 : 0 ≤ N0 := le_trans (by unfold smallRadiusConstant; positivity) hN
  have h5 : smallRadiusConstant a * E * (1 / 8) ≤ N0 * E * ((r : ℝ) ^ 4 * Real.exp (-δ * r)) := by
    have : 1 / 8 ≤ (r : ℝ) ^ 4 * Real.exp (-δ * r) := by
      have hp := Real.exp_pos (-δ * r)
      nlinarith
    exact mul_le_mul (mul_le_mul_of_nonneg_right hN hE0) this (by norm_num) (by positivity)
  have e : smallRadiusConstant a * E * (1 / 8) = (a * (4 * 241 ^ 4 * 120 ^ 2 * 256) + 1) * E := by
    unfold smallRadiusConstant
    ring
  rw [e] at h5
  calc |x - E| ≤ _ := h1
    _ ≤ _ := h5
    _ = _ := by ring
theorem quadraticResponseAtFlat_holds (hRef : flatTopReferenceStatement) (hForm : referenceHessianFlatTopStatement)
    (hResp : shareSecondDerivAtResponseStatement) (hTop : topAverageLocalBoundStatement)
    (hSplit : sliceDecompositionStatement) (hFlat : covariantDiffNearlyFlatStatement)
    (hW : weightedSliceEstimateStatement) : quadraticResponseAtFlatStatement := by
  intro a ha
  obtain ⟨θ, del, Ca, _, _, hdel, hdel8, hCa, Lw, hWa⟩ := hW a ha
  obtain ⟨C, hC, hTopS⟩ := hTop
  refine ⟨del / 12, by positivity, fun δ hδ hδ12 => ?_⟩
  obtain ⟨Lr, hR⟩ := hResp a ha
  obtain ⟨Lf, hF⟩ := hForm a ha
  obtain ⟨cs, Ls, hcs, hSp⟩ := hSplit
  obtain ⟨Ld, hD⟩ := hFlat
  refine ⟨max (max (max Lw Lr) (max Lf Ls)) (max Ld 5), fun L hodd hLL => ?_⟩
  have l1 : Lw ≤ L := by omega
  have l2 : Lr ≤ L := by omega
  have l3 : Lf ≤ L := by omega
  have l4 : Ls ≤ L := by omega
  have l5 : Ld ≤ L := by omega
  have l6 : 5 ≤ L := by omega
  obtain ⟨cw, hcw, hWe⟩ := hWa L hodd l1
  obtain ⟨cd, Cd, hcd, hCd, hDL⟩ := hD L hodd l5
  refine ⟨max (largeRadiusConstant a C Ca del) (smallRadiusConstant a) + 1, by
    have : 0 < smallRadiusConstant a := by unfold smallRadiusConstant; positivity
    have h1 := le_max_right (largeRadiusConstant a C Ca del) (smallRadiusConstant a)
    linarith, fun F m S hFL hamb hm hreg => ?_⟩
  intro r A φ hr hbox hside hA hφ0 hφ1 hφ2
  have hφ : IsPotentialCutoff r φ := ⟨hφ0, hφ1, hφ2⟩
  have hv : (fun τ : ℝ => minimalCellShare a S 0
        (rotatedField (fun y μ => (τ * φ y μ) • constantCurvaturePotential A y μ) flatTopField)) =
      fun τ : ℝ => minimalCellShare a S 0 (rotatedField (fun y i => τ • cutoffPotential φ A y i) flatTopField) := by
    funext τ
    congr 2
    funext y μ
    simp only [cutoffPotential, mul_smul]
  rw [hv]
  obtain ⟨U, hU, hval⟩ := hR L hodd l2 F m S hFL hamb hm hreg (cutoffPotential φ A)
  rw [hval]
  have hFodd : Odd F.blockSide := by rw [hFL]; exact hodd
  have hF5 : 5 ≤ F.blockSide := by rw [hFL]; exact l6
  have hδ1 : δ ≤ 1 / 60 := by linarith
  set N0 := max (largeRadiusConstant a C Ca del) (smallRadiusConstant a) + 1 with hN0
  have hE0 : 0 ≤ curvatureNormSq A := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hsmall : r < 120
  · exact abs_share_sub_le_small_radius ha hδ hδ1 hr hsmall A hA hφ hU (by
      have := le_max_right (largeRadiusConstant a C Ca del) (smallRadiusConstant a)
      linarith)
  set q := r / 24 with hq
  have hq5 : 5 ≤ q := by omega
  have hq24 : 24 * q ≤ r := by omega
  have hq25 : r < 24 * q + 24 := by omega
  have h : ComparisonSetup S r q := ⟨hFodd, by omega, hamb, hq5, hq24, hbox, hside⟩
  set s₀ := min cs (min cw cd) with hs₀
  have hs₀0 : 0 < s₀ := lt_min hcs (lt_min hcw hcd)
  set R := referenceFieldChain S (flatTopField : F.GaugeField F.top) with hRd
  obtain ⟨u₁, ξ, hslice, hmf, hre, heq⟩ := hSp F m S hFodd (by rw [hFL]; exact l4) hamb hm hreg s₀ flatTopField
    hs₀0 (min_le_left _ _) (isCold_flatTopField S hs₀0)
    (fun x i => U.fine x i - (candidateChart F q A).fine x i)
  have hlie : ∀ x i, covariantDiff (R 0) ξ x i ∈ imaginaryQuaternions := by
    intro x i
    show (covariantDiff (R 0) ξ x i).re = 0
    simp only [covariantDiff, Quaternion.re_sub, GaugeMapLinear.re_adjointAction, hre, sub_self]
  set e : F.Site 0 → Fin 4 → imaginaryQuaternions := fun x i => ⟨covariantDiff (R 0) ξ x i, hlie x i⟩ with he
  obtain ⟨nc, nt⟩ := covariantDiff_null_at_flat (S := S) (F := F) (c := cd) (C := Cd) (e := e) hcd
    (fun m' S' _ => hDL F m' S' hFL) hamb hm hreg hmf (fun x i => rfl)
  set Ut := candidateChart F q A with hUt
  set W : ChainChart F := ⟨u₁, U.coarse⟩ with hWd
  have hs : ResponseSplitting S U Ut W e := by
    refine ⟨fun b _ => ?_, fun _ _ _ => rfl, fun _ _ _ => rfl, fun p hp => ?_, nt⟩
    · apply Subtype.ext
      have h1 := heq b.1 b.2
      rw [Submodule.coe_sub] at h1
      rw [Submodule.coe_add, Submodule.coe_add]
      have h2 : ((e b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) = covariantDiff (R 0) ξ b.1 b.2 := rfl
      rw [h2, add_assoc, ← h1]
      show ((U.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) =
        ((Ut.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) + (_ - _)
      abel
    · have hcS : enclosingCell p.1 ∈ S := by
        have hc : plaquetteCorners p ⊆ sitesOfCells S 0 := (Finset.mem_filter.1 hp).2.2
        exact LumpContours.BlockLevels.enclosingCell_mem_of_mem_sitesOfCells (Nat.zero_le _) hFodd
          (hc (by simp [plaquetteCorners]))
      have c1 := nc p (Finset.mem_filter.2 ⟨hp, hcS⟩)
      rw [linearizedCurl_eq_untransported hRef h e hp] at c1
      exact Subtype.ext c1
  have hTopAll : ∀ (D : ChainChart F), ∀ c ∈ innerBonds S F.top,
      ‖linearPart R D F.top c.1 c.2‖ ≤ C * localNorm S R D (unitWeights F) (enclosingCell c.1) :=
    fun D c hc => hTopS F S hFodd hF5 hamb D c hc
  have hEst : ∀ B : ℝ, 0 ≤ B →
      (∀ D : ChainChart F, GaugeMap.InGaugeSlice S flatTopField (R 0) D.fine →
        |responseLinear a S R (cutoffPotential φ A) D - responseBilinear a S R Ut D| ≤
          B * _root_.YangMills.Construction.BlockAverages.weightedNorm S R D (invertedWeights (classWeight F (linearDecay del) 0 (0 : F.Site 0)))) →
      _root_.YangMills.Construction.BlockAverages.weightedNorm S R W (classWeight F (linearDecay del) 0 (0 : F.Site 0)) ≤ Ca * B := by
    intro B hB0 hb
    refine hWe F m S hFL hamb hm hreg s₀ flatTopField hs₀0 ((min_le_right _ _).trans (min_le_left _ _))
      (isCold_flatTopField S hs₀0) (linearDecay del) 0 0 (Or.inr (Or.inl rfl)) (abs_linearDecay_sub_le hdel.le) W
      (fun D => responseLinear a S R (cutoffPotential φ A) D - responseBilinear a S R Ut D) B hB0 hslice ?_ hb
    intro D hDs
    rw [hF L hodd l3 F m S hFL hamb hm hreg W D, hs.responseBilinear_eq hRef h a D, hU.2 D hDs]
  have hrR : (120 : ℝ) ≤ r := by
    have : 120 ≤ r := by omega
    exact_mod_cast this
  have hrp : (0 : ℝ) < r := by linarith
  set η := (r : ℝ) ^ 3 * Real.exp (-del * r / 6) with hη
  have hη0 : 0 < η := by positivity
  have hmain := abs_share_sub_le_of_estimate hRef h ha A hA hφ hdel.le hCa.le hC.le hs hEst hTopAll hη0
  have hd : ((4 * q - 2 : ℕ) : ℝ) = 4 * (q : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hq25R : (r : ℝ) < 24 * (q : ℝ) + 24 := by exact_mod_cast hq25
  have hsq := rest_sq_le (a := a) (C := C) (Ca := Ca) (del := del) (E := curvatureNormSq A)
    (Y := curvatureL1 A) (n := ((comparisonShell S q r).card : ℝ)) (r := (r : ℝ)) ha.le hC.le hdel hE0
    (curvatureL1_nonneg A) (sq_curvatureL1_le A hA) (by positivity) card_comparisonShell_le hrR hd hq25R
  have hnum := large_radius_bound (a := a) (C := C) (Ca := Ca) (del := del) (δ := δ) (E := curvatureNormSq A)
    (r := (r : ℝ)) ha.le hC.le hdel hδ hδ12 hE0 hrR (sq_nonneg _) hsq
  refine hmain.trans (hnum.trans ?_)
  have hl : largeRadiusConstant a C Ca del ≤ N0 := by
    have := le_max_left (largeRadiusConstant a C Ca del) (smallRadiusConstant a)
    linarith
  have hp : 0 ≤ curvatureNormSq A * (r : ℝ) ^ 4 * Real.exp (-δ * r) := by positivity
  calc largeRadiusConstant a C Ca del * curvatureNormSq A * (r : ℝ) ^ 4 * Real.exp (-δ * r)
      = largeRadiusConstant a C Ca del * (curvatureNormSq A * (r : ℝ) ^ 4 * Real.exp (-δ * r)) := by ring
    _ ≤ N0 * (curvatureNormSq A * (r : ℝ) ^ 4 * Real.exp (-δ * r)) := mul_le_mul_of_nonneg_right hl hp
    _ = _ := by ring
end Conclusion
end YangMills.Construction.BlockAverages.QuadraticResponseAtFlat
end
