import YangMills.Construction.ColdChainAtEveryLevel.LeastValuesOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace MinimalChain
variable {F : BlockFrame}
theorem norm_eq_one_of_mem_unitary {q : ℍ[ℝ]} (hq : q ∈ unitary ℍ[ℝ]) : ‖q‖ = 1 := by
  have : q * star q = 1 := (Unitary.mem_iff.1 hq).2
  have h2 : ‖q‖ * ‖star q‖ = 1 := by
    rw [← norm_mul, this, norm_one]
  rw [Quaternion.norm_star] at h2
  nlinarith [norm_nonneg q]
instance compactSpace_unitQuaternion : CompactSpace UnitQuaternion := by
  have h : IsCompact ((unitary ℍ[ℝ] : Submonoid ℍ[ℝ]) : Set ℍ[ℝ]) := by
    apply Metric.isCompact_of_isClosed_isBounded isClosed_unitary
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, ?_⟩
    intro q hq
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_eq_one_of_mem_unitary hq).le
  exact isCompact_iff_compactSpace.1 h
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem re_le_norm (q : ℍ[ℝ]) : q.re ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.quaternion_re_le_norm <;> assumption
theorem blockFit_nonneg {j : ℕ} (X : F.GaugeField j) (X' : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) : 0 ≤ blockFit X X' c := by
  unfold blockFit
  have h := re_le_norm (contourAverage X c * (((X' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]))
  rw [norm_mul, norm_coe_unitQuaternion, mul_one] at h
  linarith
theorem one_sub_re_nonneg (g : UnitQuaternion) : 0 ≤ 1 - (g : ℍ[ℝ]).re := by
  have := re_le_norm (g : ℍ[ℝ])
  rw [norm_coe_unitQuaternion] at this
  linarith
theorem continuous_iInf_of_compactSpace {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    [CompactSpace B] (g : A → B → ℝ) (hg : Continuous fun P : A × B => g P.1 P.2) :
    Continuous fun x => ⨅ y, g x y := by
  have hu : Continuous (Function.uncurry g) := hg
  have := IsCompact.continuous_sInf (K := (Set.univ : Set B)) (f := g) isCompact_univ hu
  simpa only [iInf, Set.image_univ] using this
theorem exists_eq_iInf_of_compactSpace {B : Type} [TopologicalSpace B] [CompactSpace B]
    [Nonempty B] (g : B → ℝ) (hg : Continuous g) : ∃ y, g y = ⨅ y, g y ∧ ∀ y', g y ≤ g y' := by
  obtain ⟨y, -, hy⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hg.continuousOn
  have hmin : ∀ y', g y ≤ g y' := fun y' => hy (Set.mem_univ y')
  refine ⟨y, le_antisymm (le_ciInf hmin) (ciInf_le ⟨g y, ?_⟩ y), hmin⟩
  rintro _ ⟨y', rfl⟩
  exact hmin y'
theorem continuous_pathHolonomy {j : ℕ} (l : List PathStep) :
    ∀ x : F.Site j, Continuous fun X : F.GaugeField j => pathHolonomy X x l := by
  induction l with
  | nil =>
    intro x
    exact continuous_const
  | cons st r ih =>
    intro x
    simp only [pathHolonomy]
    refine Continuous.mul ?_ (ih _)
    unfold linkValue
    split_ifs
    · exact continuous_apply_apply _ _
    · exact (continuous_apply_apply _ _).inv
theorem continuous_contourAverage {j : ℕ} (c : F.Site (j + 1) × Fin 4) :
    Continuous fun X : F.GaugeField j => contourAverage X c := by
  unfold contourAverage
  have h : Continuous fun X : F.GaugeField j => ∑ x ∈ centredCube F.blockSide,
      ∑ σ : Equiv.Perm (Fin 4),
      ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide x σ c.2) : UnitQuaternion) : ℍ[ℝ]) :=
    continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun σ _ =>
      continuous_subtype_val.comp (continuous_pathHolonomy _ _)
  exact h.const_smul (1 / (24 * (F.blockSide : ℝ) ^ 4))
theorem continuous_blockFit {T : Type} [TopologicalSpace T] {j : ℕ} (f : T → F.GaugeField j)
    (g : T → F.GaugeField (j + 1)) (hf : Continuous f) (hg : Continuous g)
    (c : F.Site (j + 1) × Fin 4) : Continuous fun u => blockFit (f u) (g u) c := by
  unfold blockFit
  have h1 : Continuous fun u => contourAverage (f u) c := (continuous_contourAverage c).comp hf
  have h0 : Continuous fun u => g u c.1 c.2 :=
    (continuous_apply_apply c.1 c.2).comp hg
  have h2 : Continuous fun u => (((g u c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) :=
    continuous_subtype_val.comp h0.inv
  refine Continuous.sub h1.norm ?_
  exact Quaternion.continuous_re.comp (h1.mul h2)
theorem continuous_wilsonAction (S : Finset F.Cell) : Continuous (wilsonAction S) := by
  unfold wilsonAction
  refine continuous_finsetSum _ fun p _ => continuous_const.sub ?_
  exact Quaternion.continuous_re.comp
    (continuous_subtype_val.comp (continuous_pathHolonomy _ _))
theorem continuous_sum_blockFit {T : Type} [TopologicalSpace T] (S : Finset F.Cell) (j : ℕ)
    (f : T → F.GaugeField j) (g : T → F.GaugeField (j + 1)) (hf : Continuous f)
    (hg : Continuous g) :
    Continuous fun u => ∑ c ∈ innerBonds S (j + 1), blockFit (f u) (g u) c :=
  continuous_finsetSum _ fun c _ => continuous_blockFit f g hf hg c
theorem sum_blockFit_nonneg (S : Finset F.Cell) (j : ℕ) (W : F.GaugeField j)
    (V : F.GaugeField (j + 1)) : 0 ≤ ∑ c ∈ innerBonds S (j + 1), blockFit W V c :=
  Finset.sum_nonneg fun c _ => blockFit_nonneg _ _ _
instance nonemptyGaugeField (j : ℕ) : Nonempty (F.GaugeField j) := ⟨fun _ _ => 1⟩
theorem minimalAction_nonneg (a : ℝ) (ha : 0 ≤ a) (S : Finset F.Cell) :
    ∀ (j : ℕ) (X : F.GaugeField j), 0 ≤ minimalAction a S j X := by
  intro j
  induction j with
  | zero =>
    intro X
    exact Finset.sum_nonneg fun p _ => one_sub_re_nonneg _
  | succ j ih =>
    intro X
    simp only [minimalAction]
    apply le_ciInf
    intro W
    have := ih W
    have h2 := sum_blockFit_nonneg S j W X
    positivity
theorem continuous_minimalAction (a : ℝ) (S : Finset F.Cell) :
    ∀ j : ℕ, Continuous (minimalAction (F := F) a S j) := by
  intro j
  induction j with
  | zero => exact continuous_wilsonAction S
  | succ j ih =>
    have h1 : Continuous fun P : F.GaugeField (j + 1) × F.GaugeField j =>
        minimalAction a S j P.2 :=
      ih.comp continuous_snd
    have h2 : Continuous fun P : F.GaugeField (j + 1) × F.GaugeField j =>
        ∑ c ∈ innerBonds S (j + 1), blockFit P.2 P.1 c :=
      continuous_sum_blockFit S j _ _ continuous_snd continuous_fst
    have h3 : Continuous fun P : F.GaugeField (j + 1) × F.GaugeField j =>
        a * ∑ c ∈ innerBonds S (j + 1), blockFit P.2 P.1 c := continuous_const.mul h2
    exact continuous_iInf_of_compactSpace
      (fun (V : F.GaugeField (j + 1)) (W : F.GaugeField j) =>
        minimalAction a S j W + a * ∑ c ∈ innerBonds S (j + 1), blockFit W V c) (h1.add h3)
theorem exists_blockEnergy_eq_minimalAction (a : ℝ) (S : Finset F.Cell) (j : ℕ)
    (V : F.GaugeField (j + 1)) :
    ∃ W : F.GaugeField j, blockEnergy a S j W V = minimalAction a S (j + 1) V ∧
      ∀ W', blockEnergy a S j W V ≤ blockEnergy a S j W' V := by
  have h1 : Continuous fun W : F.GaugeField j => minimalAction a S j W :=
    continuous_minimalAction a S j
  have h2 : Continuous fun W : F.GaugeField j => ∑ c ∈ innerBonds S (j + 1), blockFit W V c :=
    continuous_sum_blockFit S j _ _ continuous_id continuous_const
  have h3 : Continuous fun W : F.GaugeField j =>
      a * ∑ c ∈ innerBonds S (j + 1), blockFit W V c :=
    continuous_const.mul h2
  exact exists_eq_iInf_of_compactSpace (fun W : F.GaugeField j =>
    minimalAction a S j W + a * ∑ c ∈ innerBonds S (j + 1), blockFit W V c) (h1.add h3)
def partialChainAction (a : ℝ) (S : Finset F.Cell) (X : F.FieldChain) (j : ℕ) : ℝ :=
  wilsonAction S (X 0) +
    a * ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1), blockFit (X i) (X (i + 1)) c
theorem minimalAction_le_partialChainAction (a : ℝ) (ha : 0 ≤ a) (S : Finset F.Cell)
    (X : F.FieldChain) : ∀ j, minimalAction a S j (X j) ≤ partialChainAction a S X j := by
  intro j
  induction j with
  | zero => simp [partialChainAction, minimalAction]
  | succ j ih =>
    obtain ⟨W, hW, hmin⟩ := exists_blockEnergy_eq_minimalAction a S j (X (j + 1))
    rw [← hW]
    calc blockEnergy a S j W (X (j + 1)) ≤ blockEnergy a S j (X j) (X (j + 1)) := hmin _
      _ = minimalAction a S j (X j) +
          a * ∑ c ∈ innerBonds S (j + 1), blockFit (X j) (X (j + 1)) c := rfl
      _ ≤ partialChainAction a S X j +
          a * ∑ c ∈ innerBonds S (j + 1), blockFit (X j) (X (j + 1)) c := by
          gcongr
      _ = _ := by
          simp only [partialChainAction]
          rw [Finset.sum_range_succ]
          ring
theorem exists_chain_partialChainAction_eq (a : ℝ) (S : Finset F.Cell) :
    ∀ (j : ℕ) (V : F.GaugeField j), ∃ X : F.FieldChain,
      X j = V ∧ partialChainAction a S X j = minimalAction a S j V := by
  intro j
  induction j with
  | zero =>
    intro V
    refine ⟨fun i => if h : i = 0 then h ▸ V else fun _ _ => 1, rfl, ?_⟩
    simp [partialChainAction, minimalAction]
  | succ j ih =>
    intro V
    obtain ⟨W, hW, -⟩ := exists_blockEnergy_eq_minimalAction a S j V
    obtain ⟨X, hX, hT⟩ := ih W
    classical
    refine ⟨Function.update X (j + 1) V, by simp, ?_⟩
    have hlow : ∀ i, i ≤ j → Function.update X (j + 1) V i = X i := by
      intro i hi
      exact Function.update_of_ne (by omega) _ _
    simp only [partialChainAction]
    rw [Finset.sum_range_succ, hlow 0 (Nat.zero_le _), hlow j le_rfl, Function.update_self, ← hW]
    have hsum : ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1),
        blockFit (Function.update X (j + 1) V i) (Function.update X (j + 1) V (i + 1)) c =
        ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1), blockFit (X i) (X (i + 1)) c := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [hlow i (by omega), hlow (i + 1) (by omega)]
    rw [hsum]
    simp only [blockEnergy]
    rw [← hT]
    simp only [partialChainAction, hX]
    ring
end MinimalChain
theorem minimalChainExistence : minimalChainExistenceStatement := by
  intro F a S ha
  refine ⟨fun j X X' c => MinimalChain.blockFit_nonneg X X' c,
    MinimalChain.minimalAction_nonneg a ha S,
    MinimalChain.exists_blockEnergy_eq_minimalAction a S, ?_⟩
  intro V
  obtain ⟨X, hX, hT⟩ := MinimalChain.exists_chain_partialChainAction_eq a S F.top V
  have htotal : ∀ Y : F.FieldChain,
      chainAction a S Y = MinimalChain.partialChainAction a S Y F.top :=
    fun Y => rfl
  refine ⟨X, ⟨hX, ?_⟩, by rw [htotal, hT]⟩
  intro X' hX'
  rw [htotal, htotal, hT]
  have := MinimalChain.minimalAction_le_partialChainAction a ha S X' F.top
  rwa [hX'] at this
end YangMills.Construction.BlockAverages
end
