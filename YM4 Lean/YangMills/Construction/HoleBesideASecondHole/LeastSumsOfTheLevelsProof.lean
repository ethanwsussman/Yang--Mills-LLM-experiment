import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import YangMills.Construction.HoleBesideASecondHole.LeastSumsOfTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ChainEnergies
open BlockAverages LumpContours
variable {F : BlockFrame}
theorem norm_eq_one_of_mem_unitary {q : ℍ[ℝ]} (hq : q ∈ unitary ℍ[ℝ]) : ‖q‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.norm_eq_one_of_mem_unitary <;> assumption
instance instCompactSpaceUnitQuaternion : CompactSpace UnitQuaternion := by
  have h : IsCompact ((unitary ℍ[ℝ] : Submonoid ℍ[ℝ]) : Set ℍ[ℝ]) := by
    apply Metric.isCompact_of_isClosed_isBounded isClosed_unitary
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, ?_⟩
    intro q hq
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_eq_one_of_mem_unitary hq).le
  exact isCompact_iff_compactSpace.1 h
theorem continuous_pathHolonomy {j : ℕ} (l : List PathStep) :
    ∀ x : F.Site j, Continuous fun A : F.GaugeField j => pathHolonomy A x l := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.continuous_pathHolonomy <;> assumption
theorem continuous_blockFit {T : Type} [TopologicalSpace T] {j : ℕ} (f : T → F.GaugeField j)
    (g : T → F.GaugeField (j + 1)) (hf : Continuous f) (hg : Continuous g)
    (c : F.Site (j + 1) × Fin 4) : Continuous fun u => blockFit (f u) (g u) c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.continuous_blockFit <;> assumption
theorem continuous_cutChainEnergy (a : ℝ) (j : ℕ) (S : Finset (F.Site j)) :
    Continuous fun U : F.FieldChain => cutChainEnergy a j S U := by
  unfold cutChainEnergy
  refine Continuous.add ?_ (continuous_const.mul ?_)
  · refine continuous_finsetSum _ fun p _ => ?_
    unfold plaquetteEnergy
    refine continuous_const.sub ?_
    refine Quaternion.continuous_re.comp (continuous_subtype_val.comp ?_)
    exact (continuous_pathHolonomy _ _).comp (continuous_apply 0)
  · refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun c _ => ?_
    exact continuous_blockFit _ _ (continuous_apply i) (continuous_apply (i + 1)) c
theorem blockFit_nonneg {j : ℕ} (A : F.GaugeField j) (A' : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) : 0 ≤ blockFit A A' c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.blockFit_nonneg <;> assumption
theorem plaquetteEnergy_nonneg (U : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) :
    0 ≤ plaquetteEnergy U p := by apply _root_.YangMills.Construction.LumpContours.CutAction.plaquetteEnergy_nonneg <;> assumption
theorem cutChainEnergy_nonneg {a : ℝ} (ha : 0 ≤ a) (j : ℕ) (S : Finset (F.Site j)) (U : F.FieldChain) :
    0 ≤ cutChainEnergy a j S U := by
  unfold cutChainEnergy
  refine add_nonneg (Finset.sum_nonneg fun p _ => plaquetteEnergy_nonneg _ _) (mul_nonneg ha ?_)
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ => blockFit_nonneg _ _ _
theorem cutEffectiveAction_le {a : ℝ} (ha : 0 ≤ a) (j : ℕ) (S : Finset (F.Site j)) (U : F.FieldChain) :
    cutEffectiveAction a j S (U j) ≤ cutChainEnergy a j S U := by
  refine ciInf_le (f := fun U' : {U' : F.FieldChain // U' j = U j} => cutChainEnergy a j S U'.1) ⟨0, ?_⟩ ⟨U, rfl⟩
  rintro _ ⟨U', rfl⟩
  exact cutChainEnergy_nonneg ha j S U'.1
theorem exists_minimizing_chain {a : ℝ} (ha : 0 ≤ a) (j : ℕ) (S : Finset (F.Site j)) (V : F.GaugeField j) :
    ∃ U : F.FieldChain, U j = V ∧ cutChainEnergy a j S U = cutEffectiveAction a j S V := by
  have hc : Continuous fun U' : F.FieldChain => cutChainEnergy a j S (Function.update U' j V) :=
    (continuous_cutChainEnergy a j S).comp (Continuous.update continuous_id j continuous_const)
  haveI : Nonempty F.FieldChain := ⟨fun _ _ _ => 1⟩
  obtain ⟨U, -, hU⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  have hmin : ∀ U', cutChainEnergy a j S (Function.update U j V) ≤
      cutChainEnergy a j S (Function.update U' j V) :=
    fun U' => hU (Set.mem_univ U')
  have htop : (Function.update U j V) j = V := by simp
  refine ⟨Function.update U j V, htop, le_antisymm ?_ ?_⟩
  · haveI : Nonempty {U' : F.FieldChain // U' j = V} := ⟨⟨_, htop⟩⟩
    refine le_ciInf ?_
    rintro ⟨U', rfl⟩
    have := hmin U'
    rwa [Function.update_eq_self] at this
  · have := cutEffectiveAction_le ha j S (Function.update U j V)
    rwa [htop] at this
theorem siteCoords_cast {j : ℕ} (x : F.Site j) (i : Fin 4) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.siteCoords_cast <;> assumption
theorem siteOfCoords_siteCoords {j : ℕ} (x : F.Site j) : siteOfCoords j (siteCoords x) = x := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
theorem pow_mul_cast_eq {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (k : Fin 4) {a b : ℤ}
    (h : (a : ZMod (F.period j k)) = b) :
    (((F.blockSide : ℤ) ^ (j - i) * a : ℤ) : ZMod (F.period i k)) =
      (((F.blockSide : ℤ) ^ (j - i) * b : ℤ) : ZMod (F.period i k)) := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.pow_mul_cast_eq <;> assumption
theorem mem_centredCube_iff {M : ℕ} {o : Fin 4 → ℤ} :
    o ∈ centredCube M ↔ ∀ m, |o m| ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.mem_centredCube_iff <;> assumption
theorem exists_balanced_digits {A B : ℕ} (hA : Odd A) (hB : Odd B) {h : ℤ}
    (hh : |h| ≤ (((A * B : ℕ) : ℤ) - 1) / 2) :
    ∃ d o : ℤ, h = (A : ℤ) * d + o ∧ |d| ≤ ((B : ℤ) - 1) / 2 ∧ |o| ≤ ((A : ℤ) - 1) / 2 := by
  obtain ⟨p, rfl⟩ := hA
  obtain ⟨q, rfl⟩ := hB
  have e1 : (((2 * q + 1 : ℕ) : ℤ) - 1) / 2 = q := by
    push_cast
    omega
  have e2 : (((2 * p + 1 : ℕ) : ℤ) - 1) / 2 = p := by
    push_cast
    omega
  have e3 : ((((2 * p + 1) * (2 * q + 1) : ℕ) : ℤ) - 1) / 2 = 2 * p * q + p + q := by
    push_cast
    have : (2 * (p : ℤ) + 1) * (2 * q + 1) - 1 = 2 * (2 * p * q + p + q) := by ring
    rw [this]
    omega
  rw [e3] at hh
  rw [e1, e2]
  have hh' := abs_le.1 hh
  set A : ℤ := ((2 * p + 1 : ℕ) : ℤ) with hAd
  have hApos : 0 < A := by rw [hAd]; positivity
  have hAp : A = 2 * p + 1 := by rw [hAd]; push_cast; ring
  set r := (h + p) % A with hr
  set d := (h + p) / A with hd
  have h1 : 0 ≤ r := Int.emod_nonneg _ hApos.ne'
  have h2 : r < A := Int.emod_lt_of_pos _ hApos
  have h3 : A * d + r = h + p := Int.mul_ediv_add_emod _ _
  refine ⟨d, r - p, by linarith, ?_, ?_⟩
  · rw [abs_le]
    constructor
    · by_contra hc
      have hc' : d + 1 ≤ -(q : ℤ) := by omega
      have : A * (d + 1) ≤ A * (-(q : ℤ)) := mul_le_mul_of_nonneg_left hc' hApos.le
      nlinarith
    · by_contra hc
      have hc' : (q : ℤ) + 1 ≤ d := by omega
      have : A * ((q : ℤ) + 1) ≤ A * d := mul_le_mul_of_nonneg_left hc' hApos.le
      nlinarith
  · rw [abs_le]
    constructor <;> omega
theorem exists_mem_sitesBelow_depth {i : ℕ} (hi : i ≤ F.depth) (hL : Odd F.blockSide) (x : F.Cell)
    {z : F.Site i} (hz : z ∈ sitesBelow i x) :
    ∃ w ∈ sitesBelow F.depth x, z ∈ sitesBelow i w := by
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hz
  have hnt : F.top - F.depth = 1 := by
    show F.depth + 1 - F.depth = 1
    omega
  have hni : F.top - i = (F.depth - i) + 1 := by
    show F.depth + 1 - i = (F.depth - i) + 1
    omega
  have hAB : F.blockSide ^ (F.top - i) = F.blockSide ^ (F.depth - i) * F.blockSide := by
    rw [hni, pow_succ]
  have hh1 := mem_centredCube_iff.1 hh
  rw [hAB] at hh1
  choose d o h1 h2 h3 using fun k => exists_balanced_digits (hL.pow (n := F.depth - i)) hL (hh1 k)
  refine ⟨siteOfCoords F.depth fun k => (F.blockSide : ℤ) ^ (F.top - F.depth) * siteCoords x k + d k, ?_, ?_⟩
  · refine Finset.mem_image.2 ⟨d, ?_, rfl⟩
    refine mem_centredCube_iff.2 fun k => ?_
    rw [hnt, pow_one]
    exact h2 k
  · refine Finset.mem_image.2 ⟨o, mem_centredCube_iff.2 h3, ?_⟩
    funext k
    simp only [siteOfCoords]
    have h4 : ((siteCoords (siteOfCoords (F := F) F.depth
          fun k => (F.blockSide : ℤ) ^ (F.top - F.depth) * siteCoords x k + d k) k : ℤ) :
        ZMod (F.period F.depth k)) =
        (((F.blockSide : ℤ) ^ (F.top - F.depth) * siteCoords x k + d k : ℤ) : ZMod (F.period F.depth k)) := by
      rw [siteCoords_cast]
      rfl
    have h5 := pow_mul_cast_eq hi (by show F.depth ≤ F.depth + 1; omega) k h4
    rw [Int.cast_add (R := ZMod (F.period i k)) _ (o k), h5, ← Int.cast_add]
    congr 1
    rw [h1 k, hni, hnt]
    push_cast
    ring
theorem cutBelow_subset_cutBelow_depth {i : ℕ} (hi : i ≤ F.depth) (hL : Odd F.blockSide) (S : Finset F.Cell) :
    cutBelow i S ⊆ cutBelow i (cutBelow F.depth S) := by
  intro z hz
  simp only [cutBelow, Finset.mem_biUnion] at hz ⊢
  obtain ⟨x, hx, hzx⟩ := hz
  obtain ⟨w, hw, hzw⟩ := exists_mem_sitesBelow_depth hi hL x hzx
  exact ⟨w, ⟨x, hx, hw⟩, hzw⟩
theorem cutBelow_top_subset (S : Finset F.Cell) : cutBelow F.top S ⊆ S := by
  intro z hz
  simp only [cutBelow, Finset.mem_biUnion] at hz
  obtain ⟨x, hx, hzx⟩ := hz
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hzx
  have h0 := mem_centredCube_iff.1 hh
  have e : (fun k => (F.blockSide : ℤ) ^ (F.top - F.top) * siteCoords x k + h k) = siteCoords x := by
    funext k
    have := h0 k
    simp only [Nat.sub_self, pow_zero, Nat.cast_one, sub_self, Int.zero_ediv, abs_nonpos_iff] at this
    simp [this]
  rw [e, siteOfCoords_siteCoords]
  exact hx
theorem cutBonds_mono {l : ℕ} {Z Z' : Finset (F.Site l)} (h : Z ⊆ Z') : cutBonds Z ⊆ cutBonds Z' := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.cutBonds_mono <;> assumption
theorem cutPlaquettes_mono {l : ℕ} {Z Z' : Finset (F.Site l)} (h : Z ⊆ Z') :
    cutPlaquettes Z ⊆ cutPlaquettes Z' := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.cutPlaquettes_mono <;> assumption
theorem cutChainEnergy_update_top_le {a : ℝ} (ha : 0 ≤ a) (hL : Odd F.blockSide) (S : Finset F.Cell)
    (U : F.FieldChain) (V : F.GaugeField F.top) :
    cutChainEnergy a F.top S (Function.update U F.top V) ≤
      cutChainEnergy a F.depth (cutBelow F.depth S) U + a * ∑ c ∈ cutBonds S, blockFit (U F.depth) V c := by
  set W := U F.depth with hW
  set U' : F.FieldChain := Function.update U F.top V with hU'
  have htop : U' F.top = V := by simp [hU']
  have hkeep : ∀ i, i ≠ F.top → U' i = U i := fun i hi => by simp [hU', hi]
  have hfit : ∑ i ∈ Finset.range F.top, ∑ c ∈ cutBonds (cutBelow (i + 1) S), blockFit (U' i) (U' (i + 1)) c ≤
      ∑ i ∈ Finset.range F.depth, ∑ c ∈ cutBonds (cutBelow (i + 1) (cutBelow F.depth S)),
          blockFit (U i) (U (i + 1)) c +
        ∑ c ∈ cutBonds S, blockFit W V c := by
    show ∑ i ∈ Finset.range (F.depth + 1), _ ≤ _
    rw [Finset.sum_range_succ]
    refine add_le_add ?_ ?_
    · refine Finset.sum_le_sum fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      have e1 : U' i = U i := hkeep i (by show i ≠ F.depth + 1; omega)
      have e2 : U' (i + 1) = U (i + 1) := hkeep (i + 1) (by show i + 1 ≠ F.depth + 1; omega)
      rw [e1, e2]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (cutBonds_mono (cutBelow_subset_cutBelow_depth (by omega) hL S))
        fun c _ _ => blockFit_nonneg _ _ _
    · have e1 : U' F.depth = W := hkeep F.depth (by show F.depth ≠ F.depth + 1; omega)
      have e2 : U' (F.depth + 1) = V := htop
      rw [e1, e2]
      exact Finset.sum_le_sum_of_subset_of_nonneg (cutBonds_mono (cutBelow_top_subset S))
        fun c _ _ => blockFit_nonneg _ _ _
  have hpl : ∑ p ∈ cutPlaquettes (cutBelow 0 S), plaquetteEnergy (U' 0) p ≤
      ∑ p ∈ cutPlaquettes (cutBelow 0 (cutBelow F.depth S)), plaquetteEnergy (U 0) p := by
    rw [hkeep 0 (by show 0 ≠ F.depth + 1; omega)]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (cutPlaquettes_mono (cutBelow_subset_cutBelow_depth (Nat.zero_le _) hL S))
      fun p _ _ => plaquetteEnergy_nonneg _ _
  have := mul_le_mul_of_nonneg_left hfit ha
  unfold cutChainEnergy
  rw [mul_add] at this
  linarith
theorem mem_sitesBelow_trans {i j m : ℕ} (hij : i ≤ j) (hjm : j ≤ m) (hm : m ≤ F.top) (hL : Odd F.blockSide)
    (x : F.Site m) {w : F.Site j} (hw : w ∈ sitesBelow j x) {z : F.Site i} (hz : z ∈ sitesBelow i w) :
    z ∈ sitesBelow i x := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.sitesBelow_trans <;> assumption
theorem mem_sitesBelow_self {j : ℕ} (hL : Odd F.blockSide) (x : F.Site j) : x ∈ sitesBelow j x := by
  refine Finset.mem_image.2 ⟨0, ?_, ?_⟩
  · refine mem_centredCube_iff.2 fun k => ?_
    simp
  · have e : (fun k => (F.blockSide : ℤ) ^ (j - j) * siteCoords x k + (0 : Fin 4 → ℤ) k) = siteCoords x := by
      funext k
      simp
    show siteOfCoords j (fun k => (F.blockSide : ℤ) ^ (j - j) * siteCoords x k + (0 : Fin 4 → ℤ) k) = x
    rw [e]
    exact siteOfCoords_siteCoords x
theorem plainBlockEnergy_le {a : ℝ} (ha : 0 ≤ a) (hL : Odd F.blockSide) (S : Finset F.Cell) (U : F.FieldChain) :
    plainBlockEnergy a S (U F.depth) (U F.top) ≤ cutChainEnergy a F.top S U := by
  have h1 := cutEffectiveAction_le ha F.depth (cutBelow F.depth S) U
  have hnt : F.depth ≤ F.top := by show F.depth ≤ F.depth + 1; omega
  have hsub : ∀ i, i ≤ F.depth → cutBelow i (cutBelow F.depth S) ⊆ cutBelow i S := by
    intro i hi z hz
    simp only [cutBelow, Finset.mem_biUnion] at hz ⊢
    obtain ⟨w, ⟨x, hx, hw⟩, hzw⟩ := hz
    exact ⟨x, hx, mem_sitesBelow_trans hi hnt le_rfl hL x hw hzw⟩
  have htop : S ⊆ cutBelow F.top S := by
    intro x hx
    simp only [cutBelow, Finset.mem_biUnion]
    exact ⟨x, hx, mem_sitesBelow_self hL x⟩
  have hfit : ∑ i ∈ Finset.range F.depth, ∑ c ∈ cutBonds (cutBelow (i + 1) (cutBelow F.depth S)),
        blockFit (U i) (U (i + 1)) c +
      ∑ c ∈ cutBonds S, blockFit (U F.depth) (U F.top) c ≤
      ∑ i ∈ Finset.range F.top, ∑ c ∈ cutBonds (cutBelow (i + 1) S), blockFit (U i) (U (i + 1)) c := by
    show _ ≤ ∑ i ∈ Finset.range (F.depth + 1), _
    rw [Finset.sum_range_succ]
    refine add_le_add ?_ ?_
    · refine Finset.sum_le_sum fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      exact Finset.sum_le_sum_of_subset_of_nonneg (cutBonds_mono (hsub (i + 1) hi'))
        fun c _ _ => blockFit_nonneg _ _ _
    · exact Finset.sum_le_sum_of_subset_of_nonneg (cutBonds_mono htop) fun c _ _ => blockFit_nonneg _ _ _
  have hpl : ∑ p ∈ cutPlaquettes (cutBelow 0 (cutBelow F.depth S)), plaquetteEnergy (U 0) p ≤
      ∑ p ∈ cutPlaquettes (cutBelow 0 S), plaquetteEnergy (U 0) p :=
    Finset.sum_le_sum_of_subset_of_nonneg (cutPlaquettes_mono (hsub 0 (Nat.zero_le _)))
      fun p _ _ => plaquetteEnergy_nonneg _ _
  have h2 := mul_le_mul_of_nonneg_left hfit ha
  rw [mul_add] at h2
  unfold plainBlockEnergy
  unfold cutChainEnergy at h1 ⊢
  linarith
theorem cutEffectiveAction_le_plainBlockEnergy {a : ℝ} (ha : 0 ≤ a) (hL : Odd F.blockSide) (S : Finset F.Cell)
    (W : F.GaugeField F.depth) (V : F.GaugeField F.top) :
    cutEffectiveAction a F.top S V ≤ plainBlockEnergy a S W V := by
  obtain ⟨U, hU1, hU2⟩ := exists_minimizing_chain ha F.depth (cutBelow F.depth S) W
  have h1 := cutEffectiveAction_le ha F.top S (Function.update U F.top V)
  have htop : (Function.update U F.top V) F.top = V := by simp
  rw [htop] at h1
  refine h1.trans ((cutChainEnergy_update_top_le ha hL S U V).trans (le_of_eq ?_))
  unfold plainBlockEnergy
  rw [hU2, hU1]
theorem minimalChainEnergiesStatement_holds : minimalChainEnergiesStatement := by
  intro F a ha hL
  exact ⟨fun j S V _ => exists_minimizing_chain ha j S V,
    fun j S U => cutEffectiveAction_le ha j S U,
    fun S U V => cutChainEnergy_update_top_le ha hL S U V,
    fun S U => plainBlockEnergy_le ha hL S U,
    fun S W V => cutEffectiveAction_le_plainBlockEnergy ha hL S W V⟩
end YangMills.Construction.ChainEnergies
end
