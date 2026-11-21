import YangMills.Construction.ClusterExpansionOfAStep.BondsOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.CalculusOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.ConvexAtRateOnFewerBonds
import YangMills.Construction.ClusterExpansionOfAStep.ConvexMeasureOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.DoubleDifferenceOfFourSettings
import YangMills.Construction.ClusterExpansionOfAStep.DoubleRatioOverHeldBonds
import YangMills.Construction.ClusterExpansionOfAStep.FineDistanceByBlocks
import YangMills.Construction.ClusterExpansionOfAStep.SlopeFromOscillation
import YangMills.Construction.ClusterExpansionOfAStep.SumBetweenTwoPlaces
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps TorusBalls StepSettings RenormalizationStepParameters
  ConvexPotentials RestrictedPotentials DisjointUnionIntegrals GradientFromOscillation DecayingPairSums
namespace HeldBondRatios
variable {R : StepSetup} {n : ℕ}
theorem coordNorm_eq_norm (v : EuclideanSpace ℝ (Fin 3)) : coordNorm v = ‖v‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coordNorm_eq_norm <;> assumption
def freeInclusion {s : ChartSetting R n} {F : Finset (TorusBond (n * R.params.side))} (h : F ⊆ s.free) (b : F) :
    s.free :=
  ⟨b.1, h b.2⟩
theorem freeInclusion_injective {s : ChartSetting R n} {F : Finset (TorusBond (n * R.params.side))}
    (h : F ⊆ s.free) : Function.Injective (freeInclusion h) := by
  intro a b e
  exact Subtype.ext (congrArg (fun x : s.free => x.1) e)
def heldField (s : ChartSetting R n) {F : Finset (TorusBond (n * R.params.side))} (h : F ⊆ s.free)
    (c : FreeCoords s.free) (ξ : FreeCoords F) : FreeCoords s.free :=
  extendByHeld (freeInclusion h) c ξ
theorem freeCoordinate_heldField (s : ChartSetting R n) {F : Finset (TorusBond (n * R.params.side))}
    (h : F ⊆ s.free) (c : FreeCoords s.free) (hz : ∀ x : s.free, x.1 ∈ F → c x = 0) (ξ : FreeCoords F)
    (x : TorusBond (n * R.params.side)) :
    s.freeCoordinate (heldField s h c ξ) x = if hx : x ∈ F then ξ ⟨x, hx⟩ else s.freeCoordinate c x := by
  classical
  by_cases hx : x ∈ F
  · have hf := h hx
    rw [dif_pos hx]
    simp only [ChartSetting.freeCoordinate, dif_pos hf, heldField, extendByHeld, Pi.add_apply]
    rw [hz ⟨x, hf⟩ hx, zero_add]
    exact (freeInclusion_injective h).extend_apply ξ 0 ⟨x, hx⟩
  · rw [dif_neg hx]
    by_cases hf : x ∈ s.free
    · simp only [ChartSetting.freeCoordinate, dif_pos hf, heldField, extendByHeld, Pi.add_apply]
      have hnot : ¬ ∃ a, freeInclusion h a = ⟨x, hf⟩ := by
        rintro ⟨a, ha⟩
        apply hx
        have := congrArg (fun y : s.free => y.1) ha
        simp only [freeInclusion] at this
        rw [← this]
        exact a.2
      rw [Function.extend_apply' _ _ _ hnot]
      simp
    · simp only [ChartSetting.freeCoordinate, dif_neg hf]
theorem heldField_inBalls (s : ChartSetting R n) {F : Finset (TorusBond (n * R.params.side))} (h : F ⊆ s.free)
    (c : FreeCoords s.free) (hz : ∀ x : s.free, x.1 ∈ F → c x = 0) (ξ : FreeCoords F)
    (hc : ∀ x, ‖c x‖ ≤ R.ballRadius) (hξ : ∀ b, ‖ξ b‖ ≤ R.ballRadius) : s.InBalls (heldField s h c ξ) := by
  classical
  intro x
  rw [coordNorm_eq_norm]
  by_cases hx : x.1 ∈ F
  · have := hz x hx
    simp only [heldField, extendByHeld, Pi.add_apply, this, zero_add]
    have e : Function.extend (freeInclusion h) ξ 0 x = ξ ⟨x.1, hx⟩ :=
      (freeInclusion_injective h).extend_apply ξ 0 ⟨x.1, hx⟩
    rw [e]
    exact hξ _
  · have hnot : ¬ ∃ a, freeInclusion h a = x := by
      rintro ⟨a, ha⟩
      apply hx
      have := congrArg (fun y : s.free => y.1) ha
      simp only [freeInclusion] at this
      rw [← this]
      exact a.2
    simp only [heldField, extendByHeld, Pi.add_apply, Function.extend_apply' _ _ _ hnot, Pi.zero_apply, add_zero]
    exact hc x
variable [NeZero n]
theorem agreeOn_of_two {s s' : ChartSetting R n} {B₁ B₂ B : TorusBond (n * R.params.side) → Prop}
    {Q₁ Q₂ Q : Finset (TorusSite n)} (h₁ : s.AgreeOn s' B₁ Q₁) (h₂ : s.AgreeOn s' B₂ Q₂)
    (hB : ∀ b, B b → B₁ b ∨ B₂ b) (hQ : ∀ y ∈ Q, y ∈ Q₁ ∨ y ∈ Q₂) : s.AgreeOn s' B Q := by
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun z hz => ?_, fun z hz hz' hq => ?_, fun y hy => ?_⟩
  · rcases hB b hb with h | h
    · exact h₁.free_iff b h
    · exact h₂.free_iff b h
  · rcases hB b hb with h | h
    · exact h₁.bad_iff b h
    · exact h₂.bad_iff b h
  · rcases hB b hb with h | h
    · exact h₁.fine_eq b h
    · exact h₂.fine_eq b h
  · rcases hQ _ hz with h | h
    · exact h₁.support_iff z h
    · exact h₂.support_iff z h
  · rcases hQ _ hq with h | h
    · exact h₁.labelling_eq z hz hz' h
    · exact h₂.labelling_eq z hz hz' h
  · rcases hQ y hy with h | h
    · exact h₁.bases_eq y h
    · exact h₂.bases_eq y h
theorem agreeOn_refl (s : ChartSetting R n) (B : TorusBond (n * R.params.side) → Prop) (Q : Finset (TorusSite n)) :
    s.AgreeOn s B Q :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ _ => Iff.rfl, fun _ _ _ _ => rfl,
    fun _ _ => rfl⟩
structure HeldOff (s : Fin 2 → Fin 2 → ChartSetting R n) (P P' : Finset (TorusSite n))
    (F : Finset (TorusBond (n * R.params.side))) (c : ∀ i j, FreeCoords (s i j).free) : Prop where
  subset_free : ∀ i j, F ⊆ (s i j).free
  off_blocks : ∀ b ∈ F, ¬ BondJoinsBlocks R.params.side P b ∧ ¬ BondJoinsBlocks R.params.side P' b
  covered : ∀ i j x, x ∈ (s i j).free → x ∉ F → BondJoinsBlocks R.params.side P x ∨ BondJoinsBlocks R.params.side P' x
  vanish : ∀ i j (x : (s i j).free), x.1 ∈ F → c i j x = 0
  in_ball : ∀ i j x, ‖c i j x‖ < R.ballRadius
  first_agree : ∀ i j j' x, BondJoinsBlocks R.params.side P x →
    (s i j).freeCoordinate (c i j) x = (s i j').freeCoordinate (c i j') x
  second_agree : ∀ i i' j x, BondJoinsBlocks R.params.side P' x →
    (s i j).freeCoordinate (c i j) x = (s i' j).freeCoordinate (c i' j) x
theorem isFourSettings_swap {s : Fin 2 → Fin 2 → ChartSetting R n} {P P' : Finset (TorusSite n)}
    (h : IsFourSettings s P P') : IsFourSettings (fun i j => s j i) P' P := by
  refine ⟨fun i j i' j' => h.coarse_eq j i j' i', fun i j j' => h.second_agree j j' i,
    fun i i' j => h.first_agree j i i', fun i j i' j' => ?_⟩
  refine agreeOn_of_two (h.rest_agree j i j' i') (h.rest_agree j i j' i') (fun b hb => Or.inl ⟨hb.2, hb.1⟩)
    (fun y hy => ?_)
  left
  rw [Finset.union_comm]
  exact hy
theorem heldOff_swap {s : Fin 2 → Fin 2 → ChartSetting R n} {P P' : Finset (TorusSite n)}
    {F : Finset (TorusBond (n * R.params.side))} {c : ∀ i j, FreeCoords (s i j).free} (h : HeldOff s P P' F c) :
    HeldOff (fun i j => s j i) P' P F (fun i j => c j i) :=
  ⟨fun i j => h.subset_free j i, fun b hb => ⟨(h.off_blocks b hb).2, (h.off_blocks b hb).1⟩,
    fun i j x hx hF => (h.covered j i x hx hF).symm, fun i j x hx => h.vanish j i x hx,
    fun i j x => h.in_ball j i x, fun i j j' x hx => h.second_agree j j' i x hx,
    fun i i' j x hx => h.first_agree j i i' x hx⟩
theorem freeCoordinate_indep_first {s : Fin 2 → Fin 2 → ChartSetting R n} {P P' : Finset (TorusSite n)}
    {F : Finset (TorusBond (n * R.params.side))} {c : ∀ i j, FreeCoords (s i j).free} (hh : HeldOff s P P' F c)
    (hfs : IsFourSettings s P P') (i i' j : Fin 2) (x : TorusBond (n * R.params.side)) (hx : x ∉ F)
    (hP : ¬ BondJoinsBlocks R.params.side P x) :
    (s i j).freeCoordinate (c i j) x = (s i' j).freeCoordinate (c i' j) x := by
  classical
  by_cases hP' : BondJoinsBlocks R.params.side P' x
  · exact hh.second_agree i i' j x hP'
  · have h1 : x ∉ (s i j).free := fun h => (hh.covered i j x h hx).elim hP hP'
    have h2 : x ∉ (s i' j).free := fun h => (hh.covered i' j x h hx).elim hP hP'
    simp only [ChartSetting.freeCoordinate, dif_neg h1, dif_neg h2]
def MixedDifferenceBound (R : StepSetup) (n : ℕ) [NeZero n] (CB : ℝ) : Prop :=
  ∀ (s : Fin 2 → Fin 2 → ChartSetting R n) (η : ∀ i j, FreeCoords (s i j).free)
    (P P' : Finset (TorusSite n)) (g : ℕ),
    (∀ i j, (s i j).IsAdmissible) → (∀ i j, (s i j).InBalls (η i j)) → IsFourSettings s P P' →
    FourPointsAgree s η P P' → (∀ y ∈ P, ∀ y' ∈ P', g ≤ _root_.YangMills.Construction.TorusFields.supDist y y') → 16 ≤ g →
    (R.range : ℝ) / 16 ≤ (R.params.side * (g - 5) : ℕ) →
    (∀ i j, ∀ X ∈ chainComponents R.range (s i j).support,
      ¬ ((X ∩ thickening R.range (sitesInBlocks R.params.side (thickening 2 P))).Nonempty ∧
        (X ∩ thickening R.range (sitesInBlocks R.params.side (thickening 2 P'))).Nonempty)) →
    |(s 1 1).potential (η 1 1) + (s 0 0).potential (η 0 0) - (s 1 0).potential (η 1 0) -
        (s 0 1).potential (η 0 1)| ≤
      CB * R.coupling * min (P.card : ℝ) P'.card *
        Real.exp (-(R.params.decayRate * (R.params.side * (g - 5) : ℕ) / 3))
theorem mixedOscillation_far (hfine : FineDistanceLeBlockDistance) {CB : ℝ} (hfit : R.params.Admissible)
    (hCB : 0 ≤ CB) (hx : 0 < R.coupling) (hDD : MixedDifferenceBound R n CB) {s : Fin 2 → Fin 2 → ChartSetting R n}
    {P P' : Finset (TorusSite n)} {F : Finset (TorusBond (n * R.params.side))} {c : ∀ i j, FreeCoords (s i j).free}
    (hset : ∀ i j, (s i j).IsAdmissible) (hfs : IsFourSettings s P P') (hh : HeldOff s P P' F c)
    (hρ : 0 ≤ R.ballRadius) (hL : 2 * R.params.side + 1 ≤ R.range) (j : Fin 2) (b : F)
    (g : ℕ) (hg : ∀ y ∈ P, g + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1.1) y) (h16 : 16 ≤ g)
    (hr : (R.range : ℝ) / 16 ≤ (R.params.side * (g - 5) : ℕ)) (ζ ζ' : FreeCoords F)
    (hζ : ∀ x, ‖ζ x‖ ≤ R.ballRadius) (hζ' : ∀ x, ‖ζ' x‖ ≤ R.ballRadius) (hdiff : ∀ x, x ≠ b → ζ x = ζ' x) :
    |(s 1 j).potential (heldField (s 1 j) (hh.subset_free 1 j) (c 1 j) ζ) +
        (s 0 j).potential (heldField (s 0 j) (hh.subset_free 0 j) (c 0 j) ζ') -
        (s 1 j).potential (heldField (s 1 j) (hh.subset_free 1 j) (c 1 j) ζ') -
        (s 0 j).potential (heldField (s 0 j) (hh.subset_free 0 j) (c 0 j) ζ)| ≤
      min (P.card : ℝ) 2 * CB * R.coupling *
        Real.exp (-(R.params.decayRate * (R.params.side * (g - 5) : ℕ) / 3)) := by
  classical
  have hL2 : 2 ≤ R.params.side := by
    have := hfit.L_ge
    omega
  set x₀ := b.1.1 with hx₀
  set x₁ := b.1.1 + TorusFields.unitStep (n * R.params.side) b.1.2 with hx₁
  set P₂ : Finset (TorusSite n) := {parentBlock R.params.side x₀, parentBlock R.params.side x₁} with hP₂
  have hblk : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side x₁) (parentBlock R.params.side x₀) ≤ 1 := by
    have h1 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one R.params.side x₀ x₁
    have h2 : _root_.YangMills.Construction.TorusFields.supDist x₀ x₁ ≤ 1 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le b.1.1 b.1.2
    have h3 : _root_.YangMills.Construction.TorusFields.supDist x₀ x₁ / R.params.side = 0 := Nat.div_eq_of_lt (by omega)
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
    omega
  have hnear : ∀ y₂ ∈ P₂, _root_.YangMills.Construction.TorusFields.supDist y₂ (parentBlock R.params.side x₀) ≤ 1 := by
    intro y₂ hy₂
    rcases Finset.mem_insert.mp hy₂ with h | h
    · rw [h, _root_.YangMills.Construction.TorusFields.supDist_self]
      omega
    · rw [Finset.mem_singleton.mp h]
      exact hblk
  have hgap : ∀ y ∈ P, ∀ y₂ ∈ P₂, g ≤ _root_.YangMills.Construction.TorusFields.supDist y y₂ := by
    intro y hy y₂ hy₂
    have h1 := hg y hy
    have h2 := hnear y₂ hy₂
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side x₀) y₂ y
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm (parentBlock R.params.side x₀) y₂, _root_.YangMills.Construction.TorusFields.supDist_comm y₂ y] at h3
    omega
  have hnotP : ∀ y₂ ∈ P₂, y₂ ∉ P := by
    intro y₂ hy₂ hin
    have := hgap y₂ hin y₂ hy₂
    rw [supDist_self] at this
    omega
  have hP2 : ∀ x, BondJoinsBlocks R.params.side P₂ x → ¬ BondJoinsBlocks R.params.side P x :=
    fun x hx hP => hnotP _ hx.1 hP.1
  have hbP₂ : BondJoinsBlocks R.params.side P₂ b.1 := by
    refine ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  have offP : ∀ i i', (s i j).AgreeOn (s i' j) (fun x => ¬ BondJoinsBlocks R.params.side P x)
      (Finset.univ \ P) := by
    intro i i'
    refine agreeOn_of_two (hfs.second_agree i i' j) (hfs.rest_agree i j i' j) (fun x hx => ?_) (fun y hy => ?_)
    · by_cases h : BondJoinsBlocks R.params.side P' x
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    · by_cases h : y ∈ P'
      · exact Or.inl h
      · refine Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h2 => ?_⟩)
        rcases Finset.mem_union.mp h2 with h3 | h3
        · exact (Finset.mem_sdiff.mp hy).2 h3
        · exact h h3
  have fs : IsFourSettings (fun i _ => s i j) P P₂ := by
    refine ⟨fun i k i' k' => hfs.coarse_eq i j i' j, fun i k k' => agreeOn_refl _ _ _, fun i i' k => ?_,
      fun i k i' k' => ?_⟩
    · exact agreeOn_of_two (offP i i') (offP i i') (fun x hx => Or.inl (hP2 x hx))
        (fun y hy => Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnotP y hy⟩))
    · refine agreeOn_of_two (offP i i') (offP i i') (fun x hx => Or.inl hx.1) (fun y hy => Or.inl ?_)
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => ?_⟩
      exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_union_left _ h)
  set zz : Fin 2 → FreeCoords F := fun k => if k = 1 then ζ else ζ' with hzz
  have hzz1 : zz 1 = ζ := by simp [hzz]
  have hzz0 : zz 0 = ζ' := by simp [hzz]
  have hzb : ∀ k, ∀ x, ‖zz k x‖ ≤ R.ballRadius := by
    intro k x
    by_cases hk : k = 1
    · simp only [hzz, if_pos hk]
      exact hζ x
    · simp only [hzz, if_neg hk]
      exact hζ' x
  have hzeq : ∀ k k', ∀ x, x ≠ b → zz k x = zz k' x := by
    intro k k' x hne
    have e := hdiff x hne
    by_cases hk : k = 1 <;> by_cases hk' : k' = 1 <;> simp [hzz, hk, hk', e]
  set η' : ∀ i k, FreeCoords ((fun (i _ : Fin 2) => s i j) i k).free := fun i k =>
    heldField (s i j) (hh.subset_free i j) (c i j) (zz k) with hη'
  have hcoord : ∀ i k x, (s i j).freeCoordinate (η' i k) x =
      if hx : x ∈ F then zz k ⟨x, hx⟩ else (s i j).freeCoordinate (c i j) x := fun i k x =>
    freeCoordinate_heldField (s i j) (hh.subset_free i j) (c i j) (hh.vanish i j) (zz k) x
  have fp : FourPointsAgree (fun i _ => s i j) η' P P₂ := by
    refine ⟨fun i k k' x hx => ?_, fun i i' k x hx => ?_, fun i k i' k' x h1 h2 => ?_⟩
    · have hF : x ∉ F := fun h => (hh.off_blocks x h).1 hx
      show (s i j).freeCoordinate (η' i k) x = (s i j).freeCoordinate (η' i k') x
      rw [hcoord, hcoord, dif_neg hF, dif_neg hF]
    · show (s i j).freeCoordinate (η' i k) x = (s i' j).freeCoordinate (η' i' k) x
      rw [hcoord, hcoord]
      by_cases hF : x ∈ F
      · rw [dif_pos hF, dif_pos hF]
      · rw [dif_neg hF, dif_neg hF]
        exact freeCoordinate_indep_first hh hfs i i' j x hF (hP2 x hx)
    · show (s i j).freeCoordinate (η' i k) x = (s i' j).freeCoordinate (η' i' k') x
      rw [hcoord, hcoord]
      by_cases hF : x ∈ F
      · rw [dif_pos hF, dif_pos hF]
        refine hzeq k k' _ fun e => h2 ?_
        have : x = b.1 := congrArg Subtype.val e
        rw [this]
        exact hbP₂
      · rw [dif_neg hF, dif_neg hF]
        exact freeCoordinate_indep_first hh hfs i i' j x hF h1
  have hcl : ∀ i k, ∀ X ∈ chainComponents R.range ((fun (i _ : Fin 2) => s i j) i k).support,
      ¬ ((X ∩ thickening R.range (sitesInBlocks R.params.side (thickening 2 P))).Nonempty ∧
        (X ∩ thickening R.range (sitesInBlocks R.params.side (thickening 2 P₂))).Nonempty) := by
    rintro i k X hX ⟨-, z, hz⟩
    obtain ⟨hzX, hzw⟩ := Finset.mem_inter.mp hz
    obtain ⟨z', hz', hd⟩ := (mem_thickening _ _ _).mp hzw
    have hzY : z ∈ (s i j).support := subset_of_mem_chainComponents hX hzX
    have hm : parentBlock R.params.side z' ∈ thickening 2 P₂ := by
      simpa [sitesInBlocks] using hz'
    obtain ⟨y₂, hy₂, hd₂⟩ := (mem_thickening _ _ _).mp hm
    have h1 := hnear y₂ hy₂
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side z') y₂ (parentBlock R.params.side x₀)
    have h3 := hfine n R.params.side z' x₀
    have h4 : _root_.YangMills.Construction.TorusFields.supDist z' x₀ ≤ R.params.side * 3 + R.params.side :=
      h3.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _)
    have haway := (hset i j).far_from_support b.1 (hh.subset_free i j b.2) z (Finset.mem_union_left _ hzY)
    have h5 := _root_.YangMills.Construction.TorusFields.supDist_triangle x₀ z' z
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm x₀ z', _root_.YangMills.Construction.TorusFields.supDist_comm z' z] at h5
    have h6 : _root_.YangMills.Construction.TorusFields.supDist b.1.1 z = _root_.YangMills.Construction.TorusFields.supDist x₀ z := rfl
    omega
  have hmain := hDD (fun i _ => s i j) η' P P₂ g (fun i _ => hset i j)
    (fun i k => heldField_inBalls (s i j) (hh.subset_free i j) (c i j) (hh.vanish i j) (zz k)
      (fun x => (hh.in_ball i j x).le) (hzb k)) fs fp hgap h16 hr hcl
  have hmin : min (P.card : ℝ) P₂.card ≤ min (P.card : ℝ) 2 := by
    refine min_le_min le_rfl ?_
    exact_mod_cast Finset.card_le_two
  set E := Real.exp (-(R.params.decayRate * (R.params.side * (g - 5) : ℕ) / 3)) with hE
  have hEp : 0 ≤ E := (Real.exp_pos _).le
  have hb := hmain.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmin (mul_nonneg hCB hx.le)) hEp)
  have e1 : CB * R.coupling * min (P.card : ℝ) 2 * E = min (P.card : ℝ) 2 * CB * R.coupling * E := by ring
  rw [e1] at hb
  simpa only [hη', hzz1, hzz0] using hb
section Slopes
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem secondDerivAlong_sub {f g : BondField ι → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (η u v : BondField ι) :
    ColdStepAtMirrorFrames.secondDerivAlong (fun ζ => f ζ - g ζ) η u v =
      ColdStepAtMirrorFrames.secondDerivAlong f η u v - ColdStepAtMirrorFrames.secondDerivAlong g η u v := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdf : Differentiable ℝ (fun ζ => fderiv ℝ f ζ u) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)
  have hdg : Differentiable ℝ (fun ζ => fderiv ℝ g ζ u) :=
    ((hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)
  have h0 : (fun ζ => fderiv ℝ (fun ζ => f ζ - g ζ) ζ u) = fun ζ => fderiv ℝ f ζ u - fderiv ℝ g ζ u := by
    funext ζ
    have h : HasFDerivAt (fun ζ => f ζ - g ζ) (fderiv ℝ f ζ - fderiv ℝ g ζ) ζ :=
      (hf1 ζ).hasFDerivAt.sub (hg1 ζ).hasFDerivAt
    rw [h.fderiv]
    rfl
  unfold ColdStepAtMirrorFrames.secondDerivAlong
  have h : HasFDerivAt (fun ζ => fderiv ℝ f ζ u - fderiv ℝ g ζ u)
      (fderiv ℝ (fun ζ => fderiv ℝ f ζ u) η - fderiv ℝ (fun ζ => fderiv ℝ g ζ u) η) η :=
    (hdf η).hasFDerivAt.sub (hdg η).hasFDerivAt
  rw [h0, h.fderiv]
  rfl
theorem deriv_line_eq_fderiv_of_germ {Ψ u : BondField ι → ℝ} (hΨ : Differentiable ℝ Ψ) {η : BondField ι}
    (h : Ψ =ᶠ[nhds η] u) (b : ι) (X : BondVector) :
    deriv (fun τ : ℝ => u (Function.update η b (η b + τ • X))) 0 = fderiv ℝ Ψ η (bondVariation b X) := by
  set w := bondVariation b X with hw
  have e : ∀ τ : ℝ, Function.update η b (η b + τ • X) = η + τ • w := by
    intro τ
    funext x
    by_cases hx : x = b
    · subst hx
      simp [hw, bondVariation]
    · simp [hw, bondVariation, hx]
  have hline : HasDerivAt (fun τ : ℝ => η + τ • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add η
  have hc : Filter.Tendsto (fun τ : ℝ => η + τ • w) (nhds 0) (nhds η) := by
    have := hline.continuousAt.tendsto
    simpa using this
  have hev : (fun τ : ℝ => u (η + τ • w)) =ᶠ[nhds 0] fun τ => Ψ (η + τ • w) :=
    (hc.eventually h).mono fun τ hτ => hτ.symm
  simp_rw [e]
  rw [hev.deriv_eq]
  have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ η) (η + (0 : ℝ) • w) := by
    simpa using (hΨ η).hasFDerivAt
  exact (h1.comp_hasDerivAt (0 : ℝ) hline).deriv
theorem bondGradNorm_sub_le {A B : BondField ι → ℝ} (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (b : ι) (ξ : BondField ι) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h₁ : ∀ X : BondVector, ‖X‖ = 1 → |fderiv ℝ A ξ (bondVariation b X)| ≤ a)
    (h₂ : ∀ X : BondVector, ‖X‖ = 1 → |fderiv ℝ B ξ (bondVariation b X)| ≤ c) :
    bondGradNorm (fun ζ => A ζ - B ζ) b ξ ≤ a + c := by
  unfold bondGradNorm
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun X hX => ?_
  have h : HasFDerivAt (fun ζ => A ζ - B ζ) (fderiv ℝ A ξ - fderiv ℝ B ξ) ξ :=
    (hA ξ).hasFDerivAt.sub (hB ξ).hasFDerivAt
  rw [Real.norm_eq_abs, h.fderiv]
  have hs : (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b) X = bondVariation b X := rfl
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hs, ContinuousLinearMap.sub_apply]
  exact (abs_sub _ _).trans (add_le_add (h₁ X hX) (h₂ X hX))
end Slopes
structure HeldPotentials {s : Fin 2 → Fin 2 → ChartSetting R n} {P P' : Finset (TorusSite n)}
    {F : Finset (TorusBond (n * R.params.side))} {c : ∀ i j, FreeCoords (s i j).free} (hh : HeldOff s P P' F c)
    (Ψ : Fin 2 → Fin 2 → BondField F → ℝ) (K : Fin 2 → Fin 2 → F → F → ℝ) (m : ℝ) (d : F → F → ℝ) (Cx : ℝ) :
    Prop where
  convex : ∀ i j, IsUniformlyConvexDecaying R.ballRadius m R.params.rt d (Ψ i j) (K i j)
  kernel_le : ∀ i j b b', K i j b b' ≤ Cx
  eq_potential : ∀ i j (ξ : FreeCoords F), (∀ b, ‖ξ b‖ ≤ R.ballRadius) →
    Ψ i j ξ = (s i j).potential (heldField (s i j) (hh.subset_free i j) (c i j) ξ)
  fderiv_le : ∀ i j (ξ : BondField F), (∀ b, ‖ξ b‖ < R.ballRadius) → ∀ (b : F) (X : BondVector), ‖X‖ = 1 →
    |fderiv ℝ (Ψ i j) ξ (bondVariation b X)| ≤ Cx
theorem heldPotentials_swap {s : Fin 2 → Fin 2 → ChartSetting R n} {P P' : Finset (TorusSite n)}
    {F : Finset (TorusBond (n * R.params.side))} {c : ∀ i j, FreeCoords (s i j).free} {hh : HeldOff s P P' F c}
    {Ψ : Fin 2 → Fin 2 → BondField F → ℝ} {K : Fin 2 → Fin 2 → F → F → ℝ} {m : ℝ} {d : F → F → ℝ} {Cx : ℝ}
    (hp : HeldPotentials hh Ψ K m d Cx) :
    HeldPotentials (heldOff_swap hh) (fun i j => Ψ j i) (fun i j => K j i) m d Cx :=
  ⟨fun i j => hp.convex j i, fun i j => hp.kernel_le j i, fun i j => hp.eq_potential j i,
    fun i j => hp.fderiv_le j i⟩
theorem bondGradNorm_far (hSl : BondGradBoundOfOscillation) (hfine : FineDistanceLeBlockDistance) {CB : ℝ}
    (hfit : R.params.Admissible) (hCB : 0 ≤ CB) (hx : 0 < R.coupling) (hDD : MixedDifferenceBound R n CB)
    {s : Fin 2 → Fin 2 → ChartSetting R n} {P P' : Finset (TorusSite n)} {F : Finset (TorusBond (n * R.params.side))}
    {c : ∀ i j, FreeCoords (s i j).free} (hset : ∀ i j, (s i j).IsAdmissible) (hfs : IsFourSettings s P P')
    (hh : HeldOff s P P' F c) {Ψ : Fin 2 → Fin 2 → BondField F → ℝ} {K : Fin 2 → Fin 2 → F → F → ℝ} {m : ℝ}
    {d : F → F → ℝ} {Cx : ℝ} (hp : HeldPotentials hh Ψ K m d Cx) (hCx : 0 ≤ Cx) (hρ : 0 ≤ R.ballRadius)
    (hL : 2 * R.params.side + 1 ≤ R.range) (j : Fin 2) (b : F) (g : ℕ)
    (hg : ∀ y ∈ P, g + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1.1) y) (h16 : 16 ≤ g)
    (hr : (R.range : ℝ) / 16 ≤ (R.params.side * (g - 5) : ℕ)) (τ : ℝ) (hτ : 0 < τ) (hτρ : τ < R.ballRadius)
    (ξ : BondField F) (hξ : ∀ b, ‖ξ b‖ < R.ballRadius) :
    bondGradNorm (fun ζ => Ψ 1 j ζ - Ψ 0 j ζ) b ξ ≤
      min (P.card : ℝ) 2 * CB * R.coupling *
          Real.exp (-(R.params.decayRate * (R.params.side * (g - 5) : ℕ) / 3)) / (2 * τ) +
        4 * (2 * Cx) * τ := by
  refine hSl F (fun ζ => Ψ 1 j ζ - Ψ 0 j ζ) R.ballRadius τ _ (2 * Cx) b
    (((hp.convex 1 j).smooth.sub (hp.convex 0 j).smooth).of_le (by norm_num)) hτ hτρ (by linarith)
    (fun ζ ζ' h1 h2 h3 => ?_) (fun ζ h X => ?_) ξ hξ
  · have h := mixedOscillation_far hfine hfit hCB hx hDD hset hfs hh hρ hL j b g hg h16 hr ζ ζ'
      (fun x => (h1 x).le) (fun x => (h2 x).le) h3
    rw [← hp.eq_potential 1 j ζ (fun x => (h1 x).le), ← hp.eq_potential 0 j ζ' (fun x => (h2 x).le),
      ← hp.eq_potential 1 j ζ' (fun x => (h2 x).le), ← hp.eq_potential 0 j ζ (fun x => (h1 x).le)] at h
    refine le_of_eq_of_le ?_ h
    congr 1
    ring
  · rw [secondDerivAlong_sub (hp.convex 1 j).smooth (hp.convex 0 j).smooth]
    have k1 := (hp.convex 1 j).kernel ζ h b b X X
    have k0 := (hp.convex 0 j).kernel ζ h b b X X
    have b1 := hp.kernel_le 1 j b b
    have b0 := hp.kernel_le 0 j b b
    have hn : 0 ≤ ‖X‖ * ‖X‖ := by positivity
    have e1 : K 1 j b b * ‖X‖ * ‖X‖ ≤ Cx * (‖X‖ * ‖X‖) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right b1 hn
    have e0 : K 0 j b b * ‖X‖ * ‖X‖ ≤ Cx * (‖X‖ * ‖X‖) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right b0 hn
    calc |ColdStepAtMirrorFrames.secondDerivAlong (Ψ 1 j) ζ (bondVariation b X) (bondVariation b X) -
          ColdStepAtMirrorFrames.secondDerivAlong (Ψ 0 j) ζ (bondVariation b X) (bondVariation b X)|
        ≤ |ColdStepAtMirrorFrames.secondDerivAlong (Ψ 1 j) ζ (bondVariation b X) (bondVariation b X)| +
          |ColdStepAtMirrorFrames.secondDerivAlong (Ψ 0 j) ζ (bondVariation b X) (bondVariation b X)| :=
          abs_sub _ _
      _ ≤ 2 * Cx * ‖X‖ ^ 2 := by nlinarith
theorem exists_slope_bounds (hSl : BondGradBoundOfOscillation) (hfine : FineDistanceLeBlockDistance)
    {CB Cq A : ℝ} (hfit : R.params.Admissible) (hCB : 0 ≤ CB) (hCq : 0 ≤ Cq) (hx : 0 < R.coupling)
    (hDD : MixedDifferenceBound R n CB) {s : Fin 2 → Fin 2 → ChartSetting R n}
    {P P' : Finset (TorusSite n)} {F : Finset (TorusBond (n * R.params.side))} {c : ∀ i j, FreeCoords (s i j).free}
    (hset : ∀ i j, (s i j).IsAdmissible) (hfs : IsFourSettings s P P') (hh : HeldOff s P P' F c)
    {Ψ : Fin 2 → Fin 2 → BondField F → ℝ} {K : Fin 2 → Fin 2 → F → F → ℝ} {m : ℝ} {d : F → F → ℝ}
    (hp : HeldPotentials hh Ψ K m d (Cq * R.coupling)) (hρ : 0 < R.ballRadius) (hL : 2 * R.params.side + 1 ≤ R.range)
    (hrt : 0 < R.params.rt) (hLbig : 2 ^ 16 ≤ R.params.side) (G₀ : ℕ) (hG : 18 ≤ G₀)
    (hrG : (R.range : ℝ) / 16 ≤ (R.params.side * (G₀ - 6) : ℕ))
    (hA₁ : 2 * (Cq * R.coupling) * Real.exp (2 * R.params.rt * G₀) ≤ A)
    (hA₂ : (2 * CB / R.ballRadius + 4 * Cq * R.ballRadius) * R.coupling * Real.exp (12 * R.params.rt) ≤ A) :
    ∃ B : F → ℝ, (∀ b, 0 ≤ B b) ∧
      (∀ b, B b = 0 ∨ ∃ y ∈ P,
        B b ≤ A * Real.exp (-(2 * R.params.rt * (_root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1.1) y : ℝ)))) ∧
      ∀ j (ξ : BondField F), (∀ b, ‖ξ b‖ < R.ballRadius) → ∀ b,
        bondGradNorm (fun ζ => Ψ 1 j ζ - Ψ 0 j ζ) b ξ ≤ B b := by
  classical
  have hCx : 0 ≤ Cq * R.coupling := mul_nonneg hCq hx.le
  have hA0 : 0 ≤ A := le_trans (by positivity) hA₁
  by_cases hne : P.Nonempty
  · set gP : F → ℕ := fun b => P.inf' hne fun y => _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1.1) y with hgP
    refine ⟨fun b => A * Real.exp (-(2 * R.params.rt * (gP b : ℝ))), fun b => by positivity, fun b => ?_,
      fun j ξ hξ b => ?_⟩
    · right
      obtain ⟨y, hy, e⟩ := Finset.exists_mem_eq_inf' hne fun y => _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1.1) y
      refine ⟨y, hy, ?_⟩
      have : gP b = _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1.1) y := e
      beta_reduce
      rw [this]
    · have hgle : ∀ y ∈ P, gP b ≤ _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1.1) y := fun y hy =>
        Finset.inf'_le _ hy
      by_cases hfar : G₀ ≤ gP b
      · set g := gP b - 1 with hgdef
        have hg1 : g + 1 = gP b := by omega
        have h16 : 16 ≤ g := by omega
        have hr' : (R.range : ℝ) / 16 ≤ (R.params.side * (g - 5) : ℕ) := by
          refine hrG.trans ?_
          have : R.params.side * (G₀ - 6) ≤ R.params.side * (g - 5) := Nat.mul_le_mul_left _ (by omega)
          exact_mod_cast this
        set q := Real.exp (-(R.params.decayRate * (R.params.side * (g - 5) : ℕ) / 6)) with hq
        have hq0 : 0 < q := Real.exp_pos _
        have hforget : 0 ≤ R.params.decayRate := by
          unfold StepParameters.decayRate
          positivity
        have hq1 : q ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          have : 0 ≤ R.params.decayRate * (R.params.side * (g - 5) : ℕ) / 6 := by positivity
          linarith
        have hE : Real.exp (-(R.params.decayRate * (R.params.side * (g - 5) : ℕ) / 3)) = q ^ 2 := by
          rw [hq, ← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
        set τ := R.ballRadius / 2 * q with hτd
        have hτ : 0 < τ := by positivity
        have hτρ : τ < R.ballRadius := by
          have : R.ballRadius / 2 * q ≤ R.ballRadius / 2 * 1 := by gcongr
          simp only [hτd]
          linarith
        have hs := bondGradNorm_far hSl hfine hfit hCB hx hDD hset hfs hh hp hCx hρ.le hL j b g
          (fun y hy => by rw [hg1]; exact hgle y hy) h16 hr' τ hτ hτρ ξ hξ
        refine hs.trans ?_
        rw [hE]
        have hmin : min (P.card : ℝ) 2 ≤ 2 := min_le_right _ _
        have h1 : min (P.card : ℝ) 2 * CB * R.coupling * q ^ 2 / (2 * τ) + 4 * (2 * (Cq * R.coupling)) * τ =
            (min (P.card : ℝ) 2 * CB / R.ballRadius + 4 * Cq * R.ballRadius) * R.coupling * q := by
          simp only [hτd]
          field_simp
        rw [h1]
        have h2 : (min (P.card : ℝ) 2 * CB / R.ballRadius + 4 * Cq * R.ballRadius) * R.coupling * q ≤
            (2 * CB / R.ballRadius + 4 * Cq * R.ballRadius) * R.coupling * q := by
          gcongr
        refine h2.trans ?_
        have h3 : q ≤ Real.exp (12 * R.params.rt) * Real.exp (-(2 * R.params.rt * (gP b : ℝ))) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hgc : ((gP b : ℕ) : ℝ) = (g - 5 : ℕ) + 6 := by
            have : gP b = (g - 5) + 6 := by omega
            rw [this]
            push_cast
            ring
          have h4 : 2 * R.params.rt * ((g - 5 : ℕ) : ℝ) ≤
              R.params.decayRate * (R.params.side * (g - 5) : ℕ) / 6 := by
            have hLr : (2 ^ 16 : ℝ) ≤ R.params.side := by exact_mod_cast hLbig
            have h5 : R.params.decayRate = R.params.rt / 2 ^ 12 := rfl
            rw [h5]
            push_cast
            have h6 : 0 ≤ R.params.rt * ((g - 5 : ℕ) : ℝ) := by positivity
            nlinarith [mul_le_mul_of_nonneg_right hLr h6]
          rw [hgc]
          nlinarith
        calc (2 * CB / R.ballRadius + 4 * Cq * R.ballRadius) * R.coupling * q
            ≤ (2 * CB / R.ballRadius + 4 * Cq * R.ballRadius) * R.coupling *
                (Real.exp (12 * R.params.rt) * Real.exp (-(2 * R.params.rt * (gP b : ℝ)))) := by
              gcongr
          _ = (2 * CB / R.ballRadius + 4 * Cq * R.ballRadius) * R.coupling * Real.exp (12 * R.params.rt) *
                Real.exp (-(2 * R.params.rt * (gP b : ℝ))) := by ring
          _ ≤ A * Real.exp (-(2 * R.params.rt * (gP b : ℝ))) := by gcongr
      · have hd1 : Differentiable ℝ (Ψ 1 j) := (hp.convex 1 j).smooth.differentiable (by norm_num)
        have hd0 : Differentiable ℝ (Ψ 0 j) := (hp.convex 0 j).smooth.differentiable (by norm_num)
        have hs := bondGradNorm_sub_le hd1 hd0 b ξ hCx hCx (fun X hX => hp.fderiv_le 1 j ξ hξ b X hX)
          (fun X hX => hp.fderiv_le 0 j ξ hξ b X hX)
        refine hs.trans ?_
        have h1 : (1 : ℝ) ≤ Real.exp (2 * R.params.rt * G₀) * Real.exp (-(2 * R.params.rt * (gP b : ℝ))) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          have : ((gP b : ℕ) : ℝ) ≤ G₀ := by
            exact_mod_cast (not_le.mp hfar).le
          nlinarith
        calc Cq * R.coupling + Cq * R.coupling = 2 * (Cq * R.coupling) * 1 := by ring
          _ ≤ 2 * (Cq * R.coupling) *
                (Real.exp (2 * R.params.rt * G₀) * Real.exp (-(2 * R.params.rt * (gP b : ℝ)))) := by
              gcongr
          _ = 2 * (Cq * R.coupling) * Real.exp (2 * R.params.rt * G₀) *
                Real.exp (-(2 * R.params.rt * (gP b : ℝ))) := by ring
          _ ≤ A * Real.exp (-(2 * R.params.rt * (gP b : ℝ))) := by gcongr
  · have hPe : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨fun _ => 0, fun _ => le_rfl, fun _ => Or.inl rfl, fun j ξ hξ b => ?_⟩
    by_contra hpos
    push Not at hpos
    set t := bondGradNorm (fun ζ => Ψ 1 j ζ - Ψ 0 j ζ) b ξ with ht
    set τ := min (R.ballRadius / 2) (t / (16 * (Cq * R.coupling) + 1)) with hτd
    have hden : 0 < 16 * (Cq * R.coupling) + 1 := by linarith
    have hτ : 0 < τ := lt_min (by linarith) (by positivity)
    have hτρ : τ < R.ballRadius := (min_le_left _ _).trans_lt (by linarith)
    have hr' : (R.range : ℝ) / 16 ≤ (R.params.side * (G₀ - 5) : ℕ) := by
      refine hrG.trans ?_
      have : R.params.side * (G₀ - 6) ≤ R.params.side * (G₀ - 5) := Nat.mul_le_mul_left _ (by omega)
      exact_mod_cast this
    have hs := bondGradNorm_far hSl hfine hfit hCB hx hDD hset hfs hh hp hCx hρ.le hL j b G₀
      (fun y hy => by simp [hPe] at hy) (by omega) hr' τ hτ hτρ ξ hξ
    simp only [hPe, Finset.card_empty, Nat.cast_zero] at hs
    have h0 : min (0 : ℝ) 2 = 0 := by norm_num
    rw [h0] at hs
    simp only [zero_mul, zero_div, zero_add] at hs
    have h1 : τ ≤ t / (16 * (Cq * R.coupling) + 1) := min_le_right _ _
    have h2 : τ * (16 * (Cq * R.coupling) + 1) ≤ t := by
      rwa [le_div_iff₀ hden] at h1
    nlinarith
theorem logRatio_held (hFour : FourCornerLogRatioBound) (hSum : DoubleSumBoundBySeparation)
    (hSl : BondGradBoundOfOscillation) (hfine : FineDistanceLeBlockDistance) {CB Cq A W lam : ℝ}
    (hfit : R.params.Admissible) (hCB : 0 ≤ CB) (hCq : 0 ≤ Cq) (hx : 0 < R.coupling) (hlam : 0 < lam)
    (hDD : MixedDifferenceBound R n CB) {s : Fin 2 → Fin 2 → ChartSetting R n} {P P' : Finset (TorusSite n)}
    {F : Finset (TorusBond (n * R.params.side))} {c : ∀ i j, FreeCoords (s i j).free}
    (hset : ∀ i j, (s i j).IsAdmissible) (hfs : IsFourSettings s P P') (hh : HeldOff s P P' F c)
    {Ψ : Fin 2 → Fin 2 → BondField F → ℝ} {K : Fin 2 → Fin 2 → F → F → ℝ}
    (hp : HeldPotentials hh Ψ K (R.coupling * lam / 8)
      (fun b b' => (supDist (parentBlock R.params.side b.1.1) (parentBlock R.params.side b'.1.1) : ℝ))
      (Cq * R.coupling))
    (hρ : 0 < R.ballRadius) (hcut : IsCutoff R.ballRadius R.barrierFn) (hL : 2 * R.params.side + 1 ≤ R.range)
    (hrt : 0 < R.params.rt) (hLbig : 2 ^ 16 ≤ R.params.side)
    (G₀ : ℕ) (hG : 18 ≤ G₀) (hrG : (R.range : ℝ) / 16 ≤ (R.params.side * (G₀ - 6) : ℕ))
    (hA₁ : 2 * (Cq * R.coupling) * Real.exp (2 * R.params.rt * G₀) ≤ A)
    (hA₂ : (2 * CB / R.ballRadius + 4 * Cq * R.ballRadius) * R.coupling * Real.exp (12 * R.params.rt) ≤ A)
    (hW0 : 0 ≤ W)
    (hW : ∀ y : TorusSite n,
      ∑ b : F, Real.exp (-(R.params.rt / 2 * (supDist (parentBlock R.params.side b.1.1) y : ℝ))) ≤ W)
    (D : ℕ) (hD : ∀ y ∈ P, ∀ y' ∈ P', D ≤ supDist y y') (h16 : 16 ≤ D)
    (hrD : (R.range : ℝ) / 16 ≤ (R.params.side * (D - 5) : ℕ))
    (hcl : ∀ i j, ∀ X ∈ chainComponents R.range (s i j).support,
      ¬ ((X ∩ thickening R.range (sitesInBlocks R.params.side (thickening 2 P))).Nonempty ∧
        (X ∩ thickening R.range (sitesInBlocks R.params.side (thickening 2 P'))).Nonempty)) :
    (∀ i j, 0 < cutoffIntegral R.ballRadius R.barrierFn (Ψ i j)) ∧
    |Real.log (cutoffIntegral R.ballRadius R.barrierFn (Ψ 1 1)) +
        Real.log (cutoffIntegral R.ballRadius R.barrierFn (Ψ 0 0)) -
        Real.log (cutoffIntegral R.ballRadius R.barrierFn (Ψ 1 0)) -
        Real.log (cutoffIntegral R.ballRadius R.barrierFn (Ψ 0 1))| ≤
      (R.coupling * lam / 8)⁻¹ *
          (A ^ 2 * W ^ 2 * min (P.card : ℝ) P'.card * Real.exp (-(R.params.rt * D / 2))) +
        CB * R.coupling * min (P.card : ℝ) P'.card *
          Real.exp (-(R.params.decayRate * (R.params.side * (D - 5) : ℕ) / 3)) := by
  classical
  have hm : 0 < R.coupling * lam / 8 := by positivity
  obtain ⟨Bf, hBf0, hBfd, hBf⟩ := exists_slope_bounds hSl hfine hfit hCB hCq hx hDD hset hfs hh hp hρ hL hrt
    hLbig G₀ hG hrG hA₁ hA₂
  obtain ⟨Bg, hBg0, hBgd, hBg⟩ := exists_slope_bounds hSl hfine hfit hCB hCq hx hDD (fun i j => hset j i)
    (isFourSettings_swap hfs) (heldOff_swap hh) (heldPotentials_swap hp) hρ hL hrt hLbig G₀ hG hrG hA₁ hA₂
  have hA0 : 0 ≤ A := le_trans (by positivity) hA₁
  have hbound : ∃ M : ℝ, ∀ i j, ∀ η : BondField F, (∀ b, ‖η b‖ < R.ballRadius) → |Ψ i j η| ≤ M := by
    have h1 : ∀ i j, ∃ M : ℝ, ∀ η ∈ Metric.closedBall (0 : BondField F) R.ballRadius, ‖Ψ i j η‖ ≤ M :=
      fun i j => (isCompact_closedBall (0 : BondField F) R.ballRadius).exists_bound_of_continuousOn
        (hp.convex i j).smooth.continuous.continuousOn
    choose M hM using h1
    obtain ⟨B, hB⟩ := (Set.finite_range fun q : Fin 2 × Fin 2 => M q.1 q.2).bddAbove
    refine ⟨B, fun i j η hη => ?_⟩
    have hin : η ∈ Metric.closedBall (0 : BondField F) R.ballRadius := by
      rw [mem_closedBall_zero_iff]
      exact (pi_norm_le_iff_of_nonneg hρ.le).mpr fun b => (hη b).le
    exact (hM i j η hin).trans (hB ⟨(i, j), rfl⟩)
  obtain ⟨M, hM⟩ := hbound
  have hdist : IsPseudoMetricOnBonds fun b b' : F =>
      (_root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1.1) (parentBlock R.params.side b'.1.1) : ℝ) :=
    ⟨fun b => by simp [_root_.YangMills.Construction.TorusFields.supDist_self], fun b b' => by rw [_root_.YangMills.Construction.TorusFields.supDist_comm], fun b b' b'' => by
      exact_mod_cast _root_.YangMills.Construction.TorusFields.supDist_triangle _ _ _⟩
  have hBc : ∀ η : BondField F, (∀ b, ‖η b‖ < R.ballRadius) →
      |Ψ 1 1 η + Ψ 0 0 η - Ψ 1 0 η - Ψ 0 1 η| ≤
        CB * R.coupling * min (P.card : ℝ) P'.card *
          Real.exp (-(R.params.decayRate * (R.params.side * (D - 5) : ℕ) / 3)) := by
    intro η hη
    have hin := fun b => (hη b).le
    rw [hp.eq_potential 1 1 η hin, hp.eq_potential 0 0 η hin, hp.eq_potential 1 0 η hin,
      hp.eq_potential 0 1 η hin]
    have hcoord : ∀ i j x, (s i j).freeCoordinate (heldField (s i j) (hh.subset_free i j) (c i j) η) x =
        if hx : x ∈ F then η ⟨x, hx⟩ else (s i j).freeCoordinate (c i j) x := fun i j x =>
      freeCoordinate_heldField (s i j) (hh.subset_free i j) (c i j) (hh.vanish i j) η x
    refine hDD s (fun i j => heldField (s i j) (hh.subset_free i j) (c i j) η) P P' D hset
      (fun i j => heldField_inBalls (s i j) (hh.subset_free i j) (c i j) (hh.vanish i j) η
        (fun x => (hh.in_ball i j x).le) hin) hfs ⟨fun i j j' x hx' => ?_, fun i i' j x hx' => ?_,
        fun i j i' j' x h1 h2 => ?_⟩ hD h16 hrD hcl
    · have hF : x ∉ F := fun h => (hh.off_blocks x h).1 hx'
      rw [hcoord, hcoord, dif_neg hF, dif_neg hF]
      exact hh.first_agree i j j' x hx'
    · have hF : x ∉ F := fun h => (hh.off_blocks x h).2 hx'
      rw [hcoord, hcoord, dif_neg hF, dif_neg hF]
      exact hh.second_agree i i' j x hx'
    · rw [hcoord, hcoord]
      by_cases hF : x ∈ F
      · rw [dif_pos hF, dif_pos hF]
      · rw [dif_neg hF, dif_neg hF]
        have a1 : x ∉ (s i j).free := fun h => (hh.covered i j x h hF).elim h1 h2
        have a2 : x ∉ (s i' j').free := fun h => (hh.covered i' j' x h hF).elim h1 h2
        simp only [ChartSetting.freeCoordinate, dif_neg a1, dif_neg a2]
  obtain ⟨hpos, hlog⟩ := hFour F R.ballRadius (R.coupling * lam / 8) R.params.rt _ Ψ K R.barrierFn Bf Bg _ M hρ hm
    hrt.le hcut hdist hp.convex hM hBf hBg hBc
  refine ⟨hpos, hlog.trans ?_⟩
  have hs := hSum F (TorusSite n) (fun b => parentBlock R.params.side b.1.1) (fun y y' => (_root_.YangMills.Construction.TorusFields.supDist y y' : ℝ)) P P'
    Bf Bg R.params.rt A W D (fun y y' => by positivity) (fun y y' => by rw [_root_.YangMills.Construction.TorusFields.supDist_comm])
    (fun y y' y'' => by exact_mod_cast _root_.YangMills.Construction.TorusFields.supDist_triangle _ _ _) hrt.le hA0 hW0 hW
    (fun y hy y' hy' => by exact_mod_cast hD y hy y' hy') hBf0 hBg0 hBfd hBgd
  have hinv : 0 ≤ (R.coupling * lam / 8)⁻¹ := by positivity
  have := mul_le_mul_of_nonneg_left hs hinv
  linarith
theorem exists_site_of_mem_coreBlocks {L r : ℕ} [NeZero L] {θ : Finset (TorusSite (n * L))} {y : TorusSite n}
    (hy : y ∈ coreBlocks L r θ) : ∃ u, parentBlock L u = y ∧ ∃ t ∈ θ, _root_.YangMills.Construction.TorusFields.supDist u t ≤ 4 * r := by
  classical
  obtain ⟨u, hu⟩ := (Finset.mem_filter.mp hy).2
  obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hu
  have h3 : parentBlock L u ∈ ({y} : Finset (TorusSite n)) := by
    simpa [sitesInBlocks] using h1
  obtain ⟨t, ht, hd⟩ := (mem_thickening _ _ _).mp h2
  exact ⟨u, Finset.mem_singleton.mp h3, t, ht, hd⟩
theorem coreBlocks_far_apart (hfine : FineDistanceLeBlockDistance) {L r : ℕ} [NeZero L]
    {θ θ' : Finset (TorusSite (n * L))} (hap : ∀ z ∈ θ, ∀ z' ∈ θ', 10 * r < _root_.YangMills.Construction.TorusFields.supDist z z') {y y' : TorusSite n}
    (hy : y ∈ coreBlocks L r θ) (hy' : y' ∈ coreBlocks L r θ') : 2 * r < L * _root_.YangMills.Construction.TorusFields.supDist y y' + L := by
  obtain ⟨u, rfl, t, ht, hd⟩ := exists_site_of_mem_coreBlocks hy
  obtain ⟨u', rfl, t', ht', hd'⟩ := exists_site_of_mem_coreBlocks hy'
  have h1 := hap t ht t' ht'
  have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle t u t'
  have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle u u' t'
  have h4 := hfine n L u u'
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm t u] at h2
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm u' t'] at h3
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm t' u'] at h3
  omega
theorem exists_near_of_mem_coreBlocks (hfine : FineDistanceLeBlockDistance) {L r : ℕ} [NeZero L]
    {θ : Finset (TorusSite (n * L))} {w : TorusSite (n * L)}
    (hw : w ∈ sitesInBlocks L (thickening 2 (coreBlocks L r θ))) :
    ∃ t ∈ θ, _root_.YangMills.Construction.TorusFields.supDist w t ≤ 3 * L + 4 * r := by
  classical
  have hm : parentBlock L w ∈ thickening 2 (coreBlocks L r θ) := by
    simpa [sitesInBlocks] using hw
  obtain ⟨y, hy, hd⟩ := (mem_thickening _ _ _).mp hm
  obtain ⟨u, rfl, t, ht, hd'⟩ := exists_site_of_mem_coreBlocks hy
  refine ⟨t, ht, ?_⟩
  have h1 := hfine n L w u
  have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle w u t
  have h3 : L * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L w) (parentBlock L u) ≤ L * 2 := Nat.mul_le_mul_left _ hd
  omega
theorem no_component_meets_both (hfine : FineDistanceLeBlockDistance) {s : Fin 2 → Fin 2 → ChartSetting R n}
    {θ θ' : Finset (TorusSite (n * R.params.side))} (hc : CompatibleSupports s θ θ') (hL : R.params.side ≤ R.range)
    (i j : Fin 2) (X : Finset (TorusSite (n * R.params.side))) (hX : X ∈ chainComponents R.range (s i j).support) :
    ¬ ((X ∩ thickening R.range
          (sitesInBlocks R.params.side (thickening 2 (coreBlocks R.params.side R.range θ)))).Nonempty ∧
      (X ∩ thickening R.range
          (sitesInBlocks R.params.side (thickening 2 (coreBlocks R.params.side R.range θ')))).Nonempty) := by
  classical
  have hNe : NeZero (n * R.params.side) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne R.params.side)⟩
  rintro ⟨⟨z₁, h₁⟩, ⟨z₂, h₂⟩⟩
  obtain ⟨hz₁, hw₁⟩ := Finset.mem_inter.mp h₁
  obtain ⟨hz₂, hw₂⟩ := Finset.mem_inter.mp h₂
  obtain ⟨w₁, hw₁, hd₁⟩ := (mem_thickening _ _ _).mp hw₁
  obtain ⟨w₂, hw₂, hd₂⟩ := (mem_thickening _ _ _).mp hw₂
  obtain ⟨t₁, ht₁, he₁⟩ := exists_near_of_mem_coreBlocks hfine hw₁
  obtain ⟨t₂, ht₂, he₂⟩ := exists_near_of_mem_coreBlocks hfine hw₂
  have hY₁ := subset_of_mem_chainComponents hX hz₁
  have hY₂ := subset_of_mem_chainComponents hX hz₂
  have n₁ : _root_.YangMills.Construction.TorusFields.supDist z₁ t₁ ≤ 3 * R.params.side + 5 * R.range := by
    have := _root_.YangMills.Construction.TorusFields.supDist_triangle z₁ w₁ t₁
    omega
  have n₂ : _root_.YangMills.Construction.TorusFields.supDist z₂ t₂ ≤ 3 * R.params.side + 5 * R.range := by
    have := _root_.YangMills.Construction.TorusFields.supDist_triangle z₂ w₂ t₂
    omega
  have hr0 : 0 < R.range := lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne R.params.side)) hL
  have in₁ : z₁ ∈ θ := by
    rcases hc.support_separated i j z₁ hY₁ with h | h | h
    · exact h
    · have := hc.far_apart t₁ ht₁ z₁ h
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at this
      omega
    · have := h t₁ (Finset.mem_union_left _ ht₁)
      omega
  have in₂ : z₂ ∈ θ' := by
    rcases hc.support_separated i j z₂ hY₂ with h | h | h
    · have := hc.far_apart z₂ h t₂ ht₂
      omega
    · exact h
    · have := h t₂ (Finset.mem_union_right _ ht₂)
      omega
  have hjoin := chainConnected_of_mem_chainComponents hX hz₁ hz₂
  have hstay : ∀ v, ChainConnected R.range (s i j).support z₁ v → v ∈ θ := by
    intro v hv
    induction hv with
    | refl => exact in₁
    | tail _ hs ih =>
      obtain ⟨-, hb, hd⟩ := hs
      rcases hc.support_separated i j _ hb with h | h | h
      · exact h
      · have := hc.far_apart _ ih _ h
        omega
      · have := h _ (Finset.mem_union_left _ ih)
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at this
        omega
  have h := hc.far_apart z₂ (hstay z₂ hjoin) z₂ in₂
  rw [_root_.YangMills.Construction.TorusFields.supDist_self] at h
  omega
theorem exists_threshold_clusterRange (K a B : ℝ) (ha : 0 < a) :
    ∃ X : ℝ, ∀ x, X ≤ x → B ≤ clusterRange x ∧ K * x ≤ Real.exp (a * clusterRange x) := by
  refine ⟨max 1 (max (|B| ^ 100) (|K| * (Nat.factorial 200 : ℝ) / a ^ 200)), fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx2 : |B| ^ 100 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx3 : |K| * (Nat.factorial 200 : ℝ) / a ^ 200 ≤ x :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx0 : 0 ≤ x := by linarith
  have hr : x ^ ((1 : ℝ) / 100) ≤ clusterRange x := Nat.le_ceil _
  have hpow0 : 0 ≤ x ^ ((1 : ℝ) / 100) := Real.rpow_nonneg hx0 _
  constructor
  · have h1 : |B| ≤ x ^ ((1 : ℝ) / 100) := by
      have h2 : (|B| ^ 100) ^ ((1 : ℝ) / 100) = |B| := by
        have := Real.pow_rpow_inv_natCast (abs_nonneg B) (n := 100) (by norm_num)
        simpa [one_div] using this
      rw [← h2]
      exact Real.rpow_le_rpow (by positivity) hx2 (by norm_num)
    exact (le_abs_self B).trans (h1.trans hr)
  · have hr0 : (0 : ℝ) ≤ clusterRange x := by positivity
    have ht : 0 ≤ a * clusterRange x := by positivity
    have h1 := Real.pow_div_factorial_le_exp _ ht 200
    refine le_trans ?_ h1
    have h2 : x ^ 2 ≤ (clusterRange x : ℝ) ^ 200 := by
      have h3 : (x ^ ((1 : ℝ) / 100)) ^ 200 = x ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
        norm_num
      rw [← h3]
      exact pow_le_pow_left₀ hpow0 hr 200
    have hf : (0 : ℝ) < Nat.factorial 200 := by positivity
    have ha' : 0 < a ^ 200 := by positivity
    rw [mul_pow, le_div_iff₀ hf]
    have h4 : |K| * (Nat.factorial 200 : ℝ) ≤ x * a ^ 200 := by
      rwa [div_le_iff₀ ha'] at hx3
    calc K * x * (Nat.factorial 200 : ℝ) ≤ |K| * x * (Nat.factorial 200 : ℝ) := by
          have := le_abs_self K
          gcongr
      _ = x * (|K| * (Nat.factorial 200 : ℝ)) := by ring
      _ ≤ x * (x * a ^ 200) := by gcongr
      _ = a ^ 200 * x ^ 2 := by ring
      _ ≤ a ^ 200 * (clusterRange x : ℝ) ^ 200 := by gcongr
theorem product_bounds_of_logs {a b c d ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : |Real.log a + Real.log b - Real.log c - Real.log d| ≤ ε) :
    a * b ≤ Real.exp ε * (c * d) ∧ c * d ≤ Real.exp ε * (a * b) := by
  have e1 : a * b = Real.exp (Real.log a + Real.log b) := by
    rw [Real.exp_add, Real.exp_log ha, Real.exp_log hb]
  have e2 : c * d = Real.exp (Real.log c + Real.log d) := by
    rw [Real.exp_add, Real.exp_log hc, Real.exp_log hd]
  rw [abs_le] at h
  rw [e1, e2, ← Real.exp_add, ← Real.exp_add]
  constructor
  · apply Real.exp_le_exp.mpr
    linarith [h.2]
  · apply Real.exp_le_exp.mpr
    linarith [h.1]
theorem abs_log_ratio_le {a b c d ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h₁ : a * b ≤ Real.exp ε * (c * d)) (h₂ : c * d ≤ Real.exp ε * (a * b)) :
    |Real.log (a * b / (c * d))| ≤ ε := by
  have hab : 0 < a * b := mul_pos ha hb
  have hcd : 0 < c * d := mul_pos hc hd
  rw [Real.log_div hab.ne' hcd.ne', abs_le]
  have l₁ := Real.log_le_log hab h₁
  have l₂ := Real.log_le_log hcd h₂
  rw [Real.log_mul (Real.exp_pos _).ne' hcd.ne', Real.log_exp] at l₁
  rw [Real.log_mul (Real.exp_pos _).ne' hab.ne', Real.log_exp] at l₂
  constructor <;> linarith
theorem numeric_bound {x lam K₂ W CB rt μ f : ℝ} {r L G D : ℝ} (hx : 0 < x) (hlam : 0 < lam) (hrt : 0 < rt)
    (hCB : 0 ≤ CB) (hμ : 0 ≤ μ) (hL : 0 < L) (hD : 2 * r / L - 4 ≤ D) (hD0 : 0 ≤ D)
    (hG : 4 * rt * G ≤ rt * r / (4 * L) + 96 * rt) (hf : rt * (D - 5) ≤ f)
    (hfl : ((8 * K₂ ^ 2 * W ^ 2 / lam * Real.exp ((96 + 1 / 2) * rt) + CB * Real.exp (5 * rt)) *
      Real.exp (rt)) * x ≤ Real.exp (rt * r / (2 * L))) :
    (x * lam / 8)⁻¹ * ((K₂ * x * Real.exp (2 * rt * G)) ^ 2 * W ^ 2 * μ * Real.exp (-(rt * D / 2))) +
        CB * x * μ * Real.exp (-f) ≤ μ * Real.exp (-(rt * D / 8)) := by
  set c₁ := 8 * K₂ ^ 2 * W ^ 2 / lam with hc₁
  set c₂ := c₁ * Real.exp ((96 + 1 / 2) * rt) with hc₂
  set c₃ := CB * Real.exp (5 * rt) with hc₃
  set E8 := Real.exp (-(rt * D / 8)) with hE8
  set E38 := Real.exp (-(3 / 8 * rt * D)) with hE38
  have hE38p : 0 < E38 := Real.exp_pos _
  have hr4 : rt * r / (4 * L) ≤ rt * (D + 4) / 8 := by
    have h1 : r / L ≤ (D + 4) / 2 := by
      have : 2 * r / L = 2 * (r / L) := by ring
      linarith
    have h2 : rt * r / (4 * L) = rt / 4 * (r / L) := by
      field_simp
    rw [h2]
    nlinarith
  have t1 : (x * lam / 8)⁻¹ * ((K₂ * x * Real.exp (2 * rt * G)) ^ 2 * W ^ 2 * μ * Real.exp (-(rt * D / 2))) ≤
      c₂ * x * μ * E38 := by
    have e1 : (x * lam / 8)⁻¹ * ((K₂ * x * Real.exp (2 * rt * G)) ^ 2 * W ^ 2 * μ * Real.exp (-(rt * D / 2))) =
        c₁ * x * μ * Real.exp (4 * rt * G + -(rt * D / 2)) := by
      have e0 : Real.exp (4 * rt * G) = Real.exp (2 * rt * G) ^ 2 := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [Real.exp_add, e0]
      simp only [hc₁]
      field_simp
    rw [e1]
    have e2 : c₂ * x * μ * E38 = c₁ * x * μ * Real.exp ((96 + 1 / 2) * rt + -(3 / 8 * rt * D)) := by
      simp only [hc₂, hE38]
      rw [Real.exp_add]
      ring
    rw [e2]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    nlinarith
  have t2 : CB * x * μ * Real.exp (-f) ≤ c₃ * x * μ * E38 := by
    have e2 : c₃ * x * μ * E38 = CB * x * μ * Real.exp (5 * rt + -(3 / 8 * rt * D)) := by
      simp only [hc₃, hE38]
      rw [Real.exp_add]
      ring
    rw [e2]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have : 0 ≤ rt * D := by positivity
    nlinarith
  have t3 : (c₂ + c₃) * x * E38 ≤ E8 := by
    have e3 : Real.exp (rt * r / (2 * L)) ≤ Real.exp (rt) * Real.exp (rt * D / 4) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h2 : rt * r / (2 * L) = rt / 4 * (2 * r / L) := by
        field_simp
        ring
      rw [h2]
      nlinarith
    have e4 : (c₂ + c₃) * x ≤ Real.exp (rt * D / 4) := by
      have h1 : Real.exp rt * ((c₂ + c₃) * x) ≤ Real.exp rt * Real.exp (rt * D / 4) := by
        calc Real.exp rt * ((c₂ + c₃) * x) = (c₂ + c₃) * Real.exp rt * x := by ring
          _ ≤ Real.exp (rt * r / (2 * L)) := hfl
          _ ≤ _ := e3
      exact le_of_mul_le_mul_left h1 (Real.exp_pos _)
    have e5 : E8 = Real.exp (rt * D / 4) * E38 := by
      simp only [hE8, hE38]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e5]
    exact mul_le_mul_of_nonneg_right e4 hE38p.le
  calc _ ≤ c₂ * x * μ * E38 + c₃ * x * μ * E38 := add_le_add t1 t2
    _ = μ * ((c₂ + c₃) * x * E38) := by ring
    _ ≤ μ * E8 := mul_le_mul_of_nonneg_left t3 hμ
def finTwoPick {M : Fin 2 → Type} (x₀ : M 0) (x₁ : M 1) : (i : Fin 2) → M i
  | 0 => x₀
  | 1 => x₁
theorem sum_exp_bonds_le (hBonds : BondsPerBlockBound) (L : ℕ) [NeZero L] (F : Finset (TorusBond (n * L)))
    (c A₀ : ℝ) (y : TorusSite n) (hA : ∑ Y : TorusSite n, Real.exp (-(c * (_root_.YangMills.Construction.TorusFields.supDist Y y : ℝ))) ≤ A₀) :
    ∑ b : F, Real.exp (-(c * (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1.1) y : ℝ))) ≤ 4 * (2 * (L : ℝ)) ^ 4 * A₀ := by
  classical
  set f : TorusBond (n * L) → ℝ := fun b => Real.exp (-(c * (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) y : ℝ))) with hf
  have h1 : ∑ b : F, f b.1 = ∑ b ∈ F, f b := Finset.sum_coe_sort F f
  have h2 : ∑ b ∈ F, f b ≤ ∑ b, f b :=
    Finset.sum_le_univ_sum_of_nonneg fun _ => (Real.exp_pos _).le
  have h3 : ∑ b, f b = ∑ Y : TorusSite n,
      ∑ b ∈ Finset.univ.filter (fun b : TorusBond (n * L) => parentBlock L b.1 = Y), f b :=
    (Finset.sum_fiberwise Finset.univ (fun b : TorusBond (n * L) => parentBlock L b.1) f).symm
  have h4 : ∀ Y : TorusSite n,
      ∑ b ∈ Finset.univ.filter (fun b : TorusBond (n * L) => parentBlock L b.1 = Y), f b ≤
        4 * (2 * (L : ℝ)) ^ 4 * Real.exp (-(c * (_root_.YangMills.Construction.TorusFields.supDist Y y : ℝ))) := by
    intro Y
    have e1 : ∑ b ∈ Finset.univ.filter (fun b : TorusBond (n * L) => parentBlock L b.1 = Y), f b =
        ((Finset.univ.filter fun b : TorusBond (n * L) => parentBlock L b.1 = Y).card : ℝ) *
          Real.exp (-(c * (_root_.YangMills.Construction.TorusFields.supDist Y y : ℝ))) := by
      have e0 : ∀ b ∈ Finset.univ.filter (fun b : TorusBond (n * L) => parentBlock L b.1 = Y),
          f b = Real.exp (-(c * (_root_.YangMills.Construction.TorusFields.supDist Y y : ℝ))) := fun b hb => by
        simp only [hf, (Finset.mem_filter.mp hb).2]
      rw [Finset.sum_congr rfl e0, Finset.sum_const, nsmul_eq_mul]
    rw [e1]
    exact mul_le_mul_of_nonneg_right (hBonds L n Y) (Real.exp_pos _).le
  have hB : (0 : ℝ) ≤ 4 * (2 * (L : ℝ)) ^ 4 := by positivity
  calc ∑ b : F, Real.exp (-(c * (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1.1) y : ℝ))) = ∑ b : F, f b.1 := rfl
    _ ≤ ∑ b, f b := by rw [h1]; exact h2
    _ ≤ ∑ Y : TorusSite n, 4 * (2 * (L : ℝ)) ^ 4 * Real.exp (-(c * (_root_.YangMills.Construction.TorusFields.supDist Y y : ℝ))) := by
        rw [h3]
        exact Finset.sum_le_sum fun Y _ => h4 Y
    _ = 4 * (2 * (L : ℝ)) ^ 4 * ∑ Y : TorusSite n, Real.exp (-(c * (_root_.YangMills.Construction.TorusFields.supDist Y y : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ 4 * (2 * (L : ℝ)) ^ 4 * A₀ := mul_le_mul_of_nonneg_left hA hB
section Assembled
variable {α : Type} [DecidableEq α]
theorem assembledField_left (C C' F : Finset α) (a : C → BondVector) (b : C' → BondVector) (ξ : F → BondVector)
    {x : α} (h : x ∈ C) : assembledField C C' F a b ξ x = a ⟨x, h⟩ := by
  simp only [assembledField, joinFields, dif_pos h]
theorem assembledField_mid (C C' F : Finset α) (a : C → BondVector) (b : C' → BondVector) (ξ : F → BondVector)
    {x : α} (h₀ : x ∉ C) (h : x ∈ C') : assembledField C C' F a b ξ x = b ⟨x, h⟩ := by
  have h1 : x ∈ C' ∪ F := Finset.mem_union_left _ h
  simp only [assembledField, joinFields, dif_neg h₀, dif_pos h1, dif_pos h]
theorem assembledField_right (C C' F : Finset α) (a : C → BondVector) (b : C' → BondVector) (ξ : F → BondVector)
    {x : α} (h₀ : x ∉ C) (h₁ : x ∉ C') (h : x ∈ F) : assembledField C C' F a b ξ x = ξ ⟨x, h⟩ := by
  have h2 : x ∈ C' ∪ F := Finset.mem_union_right _ h
  simp only [assembledField, joinFields, dif_neg h₀, dif_pos h2, dif_neg h₁, dif_pos h]
end Assembled
theorem heldField_assembled (s : ChartSetting R n) {F C C' : Finset (TorusBond (n * R.params.side))}
    (hS : s.free = C ∪ (C' ∪ F)) (hd1 : Disjoint C (C' ∪ F)) (hd2 : Disjoint C' F) (h : F ⊆ s.free)
    (a : C → BondVector) (b : C' → BondVector) (ξ : FreeCoords F) :
    heldField s h (fun x : s.free => assembledField C C' F a b 0 x) ξ =
      fun x : s.free => assembledField C C' F a b ξ x := by
  classical
  funext x
  have hnC : ∀ {z}, z ∈ F → z ∉ C := fun hz hc =>
    Finset.disjoint_left.mp hd1 hc (Finset.mem_union_right _ hz)
  have hnC' : ∀ {z}, z ∈ F → z ∉ C' := fun hz hc => Finset.disjoint_left.mp hd2 hc hz
  simp only [heldField, extendByHeld, Pi.add_apply]
  by_cases hF : x.1 ∈ F
  · rw [assembledField_right C C' F a b 0 (hnC hF) (hnC' hF) hF,
      assembledField_right C C' F a b ξ (hnC hF) (hnC' hF) hF]
    have e : Function.extend (freeInclusion h) ξ 0 x = ξ ⟨x.1, hF⟩ :=
      (freeInclusion_injective h).extend_apply ξ 0 ⟨x.1, hF⟩
    rw [e]
    simp
  · have hnot : ¬ ∃ a, freeInclusion h a = x := by
      rintro ⟨a', ha⟩
      apply hF
      have := congrArg (fun y : s.free => y.1) ha
      simp only [freeInclusion] at this
      rw [← this]
      exact a'.2
    rw [Function.extend_apply' _ _ _ hnot]
    simp only [Pi.zero_apply, add_zero]
    have hx : x.1 ∈ C ∪ (C' ∪ F) := (Finset.ext_iff.mp hS x.1).mp x.2
    rcases Finset.mem_union.mp hx with h1 | h1
    · rw [assembledField_left C C' F a b 0 h1, assembledField_left C C' F a b ξ h1]
    · rcases Finset.mem_union.mp h1 with h2 | h2
      · have h0 : x.1 ∉ C := fun hc => Finset.disjoint_left.mp hd1 hc (Finset.mem_union_left _ h2)
        rw [assembledField_mid C C' F a b 0 h0 h2, assembledField_mid C C' F a b ξ h0 h2]
      · exact absurd h2 hF
theorem logRatio_assembled (hFew : UniformlyConvexOnSubfamily) (hFour : FourCornerLogRatioBound)
    (hSum : DoubleSumBoundBySeparation) (hSl : BondGradBoundOfOscillation)
    (hfine : FineDistanceLeBlockDistance) {CB Cq A W lam : ℝ} (hfit : R.params.Admissible) (hCB : 0 ≤ CB)
    (hCq : 0 ≤ Cq) (hx : 0 < R.coupling) (hlam : 0 < lam) (hDD : MixedDifferenceBound R n CB)
    {s : Fin 2 → Fin 2 → ChartSetting R n} {P P' : Finset (TorusSite n)}
    (hset : ∀ i j, (s i j).IsAdmissible) (hfs : IsFourSettings s P P') (hρ : 0 < R.ballRadius)
    (hcut : IsCutoff R.ballRadius R.barrierFn) (hL : 2 * R.params.side + 1 ≤ R.range) (hrt : 0 < R.params.rt)
    (hLbig : 2 ^ 16 ≤ R.params.side)
    {F : Finset (TorusBond (n * R.params.side))} {C C' : Fin 2 → Finset (TorusBond (n * R.params.side))}
    (hS : ∀ i j, (s i j).free = C i ∪ (C' j ∪ F)) (hd1 : ∀ i j, Disjoint (C i) (C' j ∪ F))
    (hd2 : ∀ j, Disjoint (C' j) F) (hPC : ∀ i x, x ∈ C i → BondJoinsBlocks R.params.side P x)
    (hPC' : ∀ j x, x ∈ C' j → BondJoinsBlocks R.params.side P' x)
    (hFoff : ∀ b ∈ F, ¬ BondJoinsBlocks R.params.side P b ∧ ¬ BondJoinsBlocks R.params.side P' b)
    (hnb : ∀ b, ¬ (BondJoinsBlocks R.params.side P b ∧ BondJoinsBlocks R.params.side P' b))
    (Ψf : ∀ i j, BondField (s i j).free → ℝ) (Kf : ∀ i j, (s i j).free → (s i j).free → ℝ)
    (hgerm : ∀ i j η, (s i j).InBalls η → Ψf i j =ᶠ[nhds η] (s i j).potential)
    (hcv : ∀ i j, IsUniformlyConvexDecaying R.ballRadius (R.coupling * lam / 8) R.params.rt (s i j).bondDist
      (Ψf i j) (Kf i j))
    (hkb : ∀ i j b b', Kf i j b b' ≤ Cq * R.coupling)
    (hfirst : ∀ i j η, (s i j).InBalls η → ∀ b X, ‖X‖ = 1 →
      |deriv (fun τ : ℝ => (s i j).potential (Function.update η b (η b + τ • X))) 0| ≤ Cq * R.coupling)
    (G₀ : ℕ) (hG : 18 ≤ G₀) (hrG : (R.range : ℝ) / 16 ≤ (R.params.side * (G₀ - 6) : ℕ))
    (hA₁ : 2 * (Cq * R.coupling) * Real.exp (2 * R.params.rt * G₀) ≤ A)
    (hA₂ : (2 * CB / R.ballRadius + 4 * Cq * R.ballRadius) * R.coupling * Real.exp (12 * R.params.rt) ≤ A)
    (hW0 : 0 ≤ W)
    (hW : ∀ y : TorusSite n,
      ∑ b : F, Real.exp (-(R.params.rt / 2 * (supDist (parentBlock R.params.side b.1.1) y : ℝ))) ≤ W)
    (D : ℕ) (hD : ∀ y ∈ P, ∀ y' ∈ P', D ≤ supDist y y') (h16 : 16 ≤ D)
    (hrD : (R.range : ℝ) / 16 ≤ (R.params.side * (D - 5) : ℕ))
    (hcl : ∀ i j, ∀ X ∈ chainComponents R.range (s i j).support,
      ¬ ((X ∩ thickening R.range (sitesInBlocks R.params.side (thickening 2 P))).Nonempty ∧
        (X ∩ thickening R.range (sitesInBlocks R.params.side (thickening 2 P'))).Nonempty))
    (a : ∀ i, C i → BondVector) (b : ∀ j, C' j → BondVector) (ha : ∀ i x, ‖a i x‖ < R.ballRadius)
    (hb : ∀ j x, ‖b j x‖ < R.ballRadius) :
    (∀ i j, 0 < cutoffIntegral R.ballRadius R.barrierFn
      (fun ξ => Ψf i j fun x : (s i j).free => assembledField (C i) (C' j) F (a i) (b j) ξ x)) ∧
    |Real.log (cutoffIntegral R.ballRadius R.barrierFn
        (fun ξ => Ψf 1 1 fun x : (s 1 1).free => assembledField (C 1) (C' 1) F (a 1) (b 1) ξ x)) +
      Real.log (cutoffIntegral R.ballRadius R.barrierFn
        (fun ξ => Ψf 0 0 fun x : (s 0 0).free => assembledField (C 0) (C' 0) F (a 0) (b 0) ξ x)) -
      Real.log (cutoffIntegral R.ballRadius R.barrierFn
        (fun ξ => Ψf 1 0 fun x : (s 1 0).free => assembledField (C 1) (C' 0) F (a 1) (b 0) ξ x)) -
      Real.log (cutoffIntegral R.ballRadius R.barrierFn
        (fun ξ => Ψf 0 1 fun x : (s 0 1).free => assembledField (C 0) (C' 1) F (a 0) (b 1) ξ x))| ≤
      (R.coupling * lam / 8)⁻¹ *
          (A ^ 2 * W ^ 2 * min (P.card : ℝ) P'.card * Real.exp (-(R.params.rt * D / 2))) +
        CB * R.coupling * min (P.card : ℝ) P'.card *
          Real.exp (-(R.params.decayRate * (R.params.side * (D - 5) : ℕ) / 3)) := by
  classical
  have hnC : ∀ i j {z}, z ∈ F → z ∉ C i := fun i j z hz hc =>
    Finset.disjoint_left.mp (hd1 i j) hc (Finset.mem_union_right _ hz)
  have hnC' : ∀ j {z}, z ∈ F → z ∉ C' j := fun j z hz hc => Finset.disjoint_left.mp (hd2 j) hc hz
  have hsub : ∀ i j, F ⊆ (s i j).free := fun i j x hx => by
    rw [hS i j]
    exact Finset.mem_union_right _ (Finset.mem_union_right _ hx)
  set c : ∀ i j, FreeCoords (s i j).free := fun i j x => assembledField (C i) (C' j) F (a i) (b j) 0 x with hc
  have hcoordP : ∀ i j x, BondJoinsBlocks R.params.side P x →
      (s i j).freeCoordinate (c i j) x = if h : x ∈ C i then a i ⟨x, h⟩ else 0 := by
    intro i j x hx
    have hn' : x ∉ C' j := fun h => hnb x ⟨hx, hPC' j x h⟩
    have hnF : x ∉ F := fun h => (hFoff x h).1 hx
    by_cases hf : x ∈ (s i j).free
    · have hC : x ∈ C i := by
        have h1 := hf
        rw [hS i j] at h1
        rcases Finset.mem_union.mp h1 with h2 | h2
        · exact h2
        · rcases Finset.mem_union.mp h2 with h3 | h3
          · exact absurd h3 hn'
          · exact absurd h3 hnF
      simp only [ChartSetting.freeCoordinate, dif_pos hf, dif_pos hC, hc]
      exact assembledField_left _ _ _ _ _ _ hC
    · have hC : x ∉ C i := fun h => hf (by
        rw [hS i j]
        exact Finset.mem_union_left _ h)
      simp only [ChartSetting.freeCoordinate, dif_neg hf, dif_neg hC]
  have hcoordP' : ∀ i j x, BondJoinsBlocks R.params.side P' x →
      (s i j).freeCoordinate (c i j) x = if h : x ∈ C' j then b j ⟨x, h⟩ else 0 := by
    intro i j x hx
    have hn' : x ∉ C i := fun h => hnb x ⟨hPC i x h, hx⟩
    have hnF : x ∉ F := fun h => (hFoff x h).2 hx
    by_cases hf : x ∈ (s i j).free
    · have hC : x ∈ C' j := by
        have h1 := hf
        rw [hS i j] at h1
        rcases Finset.mem_union.mp h1 with h2 | h2
        · exact absurd h2 hn'
        · rcases Finset.mem_union.mp h2 with h3 | h3
          · exact h3
          · exact absurd h3 hnF
      simp only [ChartSetting.freeCoordinate, dif_pos hf, dif_pos hC, hc]
      exact assembledField_mid _ _ _ _ _ _ hn' hC
    · have hC : x ∉ C' j := fun h => hf (by
        rw [hS i j]
        exact Finset.mem_union_right _ (Finset.mem_union_left _ h))
      simp only [ChartSetting.freeCoordinate, dif_neg hf, dif_neg hC]
  have hh : HeldOff s P P' F c := by
    refine ⟨hsub, hFoff, fun i j x hx hF => ?_, fun i j x hx => ?_, fun i j x => ?_, fun i j j' x hx => ?_,
      fun i i' j x hx => ?_⟩
    · rw [hS i j] at hx
      rcases Finset.mem_union.mp hx with h1 | h1
      · exact Or.inl (hPC i x h1)
      · rcases Finset.mem_union.mp h1 with h2 | h2
        · exact Or.inr (hPC' j x h2)
        · exact absurd h2 hF
    · simp only [hc]
      rw [assembledField_right _ _ _ _ _ _ (hnC i j hx) (hnC' j hx) hx]
      rfl
    · simp only [hc]
      have hx : x.1 ∈ C i ∪ (C' j ∪ F) := (Finset.ext_iff.mp (hS i j) x.1).mp x.2
      rcases Finset.mem_union.mp hx with h1 | h1
      · rw [assembledField_left _ _ _ _ _ _ h1]
        exact ha i _
      · by_cases h0 : (x : TorusBond (n * R.params.side)) ∈ C i
        · rw [assembledField_left _ _ _ _ _ _ h0]
          exact ha i _
        · rcases Finset.mem_union.mp h1 with h2 | h2
          · rw [assembledField_mid _ _ _ _ _ _ h0 h2]
            exact hb j _
          · rw [assembledField_right _ _ _ _ _ _ h0 (hnC' j h2) h2]
            simpa using hρ
    · rw [hcoordP i j x hx, hcoordP i j' x hx]
    · rw [hcoordP' i j x hx, hcoordP' i' j x hx]
  have hbd : ∀ i j, IsPseudoMetricOnBonds (s i j).bondDist := fun i j =>
    ⟨fun b => by simp [ChartSetting.bondDist, bondBlockDist, supDist_self],
      fun b b' => by simp only [ChartSetting.bondDist, bondBlockDist]; rw [supDist_comm],
      fun b b' b'' => by
        simp only [ChartSetting.bondDist, bondBlockDist]
        exact_mod_cast supDist_triangle _ _ _⟩
  have hfew := fun i j => hFew (s i j).free F (freeInclusion (hsub i j)) R.ballRadius (R.coupling * lam / 8)
    R.params.rt (s i j).bondDist (Ψf i j) (Kf i j) (c i j) (freeInclusion_injective _) hρ hrt.le (hbd i j)
    (hcv i j) (hh.in_ball i j) (fun x => hh.vanish i j _ x.2)
  set Ψ : Fin 2 → Fin 2 → BondField F → ℝ := fun i j ξ =>
    Ψf i j (extendByHeld (freeInclusion (hsub i j)) (c i j) ξ) with hΨ
  set K : Fin 2 → Fin 2 → F → F → ℝ := fun i j b b' =>
    Kf i j (freeInclusion (hsub i j) b) (freeInclusion (hsub i j) b') with hK
  have hin : ∀ i j (ξ : BondField F), (∀ b, ‖ξ b‖ ≤ R.ballRadius) →
      (s i j).InBalls (heldField (s i j) (hsub i j) (c i j) ξ) := fun i j ξ hξ =>
    heldField_inBalls (s i j) (hsub i j) (c i j) (hh.vanish i j) ξ (fun x => (hh.in_ball i j x).le) hξ
  have hp : HeldPotentials hh Ψ K (R.coupling * lam / 8)
      (fun b b' => (supDist (parentBlock R.params.side b.1.1) (parentBlock R.params.side b'.1.1) : ℝ))
      (Cq * R.coupling) := by
    refine ⟨fun i j => (hfew i j).1, fun i j b b' => hkb i j _ _, fun i j ξ hξ => ?_, fun i j ξ hξ b X hX => ?_⟩
    · exact (hgerm i j _ (hin i j ξ hξ)).eq_of_nhds
    · have hd : Differentiable ℝ (Ψf i j) := (hcv i j).smooth.differentiable (by norm_num)
      have e1 := (hfew i j).2 ξ b X
      have hg := hgerm i j _ (hin i j ξ fun x => (hξ x).le)
      have e2 := deriv_line_eq_fderiv_of_germ hd hg (freeInclusion (hsub i j) b) X
      have h3 := hfirst i j _ (hin i j ξ fun x => (hξ x).le) (freeInclusion (hsub i j) b) X hX
      show |fderiv ℝ (fun ξ => Ψf i j (extendByHeld (freeInclusion (hsub i j)) (c i j) ξ)) ξ
        (bondVariation b X)| ≤ _
      rw [e1]
      have e3 : fderiv ℝ (Ψf i j) (extendByHeld (freeInclusion (hsub i j)) (c i j) ξ)
            (bondVariation (freeInclusion (hsub i j) b) X) =
          deriv (fun τ : ℝ => (s i j).potential (Function.update (heldField (s i j) (hsub i j) (c i j) ξ)
            (freeInclusion (hsub i j) b)
            (heldField (s i j) (hsub i j) (c i j) ξ (freeInclusion (hsub i j) b) + τ • X))) 0 := e2.symm
      rw [e3]
      exact h3
  have hlev := logRatio_held hFour hSum hSl hfine hfit hCB hCq hx hlam hDD hset hfs hh hp hρ hcut hL hrt hLbig
    G₀ hG hrG hA₁ hA₂ hW0 hW D hD h16 hrD hcl
  have hfun : ∀ i j,
      (fun ξ => Ψf i j fun x : (s i j).free => assembledField (C i) (C' j) F (a i) (b j) ξ x) = Ψ i j := by
    intro i j
    funext ξ
    have := heldField_assembled (s i j) (hS i j) (hd1 i j) (hd2 j) (hsub i j) (a i) (b j) ξ
    simp only [hΨ]
    show Ψf i j _ = Ψf i j (heldField (s i j) (hsub i j) (c i j) ξ)
    rw [show heldField (s i j) (hsub i j) (c i j) ξ = _ from this]
  simp only [hfun]
  exact hlev
theorem integral_eq_cutoffIntegral (s : ChartSetting R n) {Ψ : BondField s.free → ℝ}
    (hgerm : ∀ η, s.InBalls η → Ψ =ᶠ[nhds η] s.potential) :
    s.integral = cutoffIntegral R.ballRadius R.barrierFn Ψ := by
  unfold ChartSetting.integral cutoffIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  show s.cutoffProduct η * Real.exp (-s.potential η) =
    radialWeightProd (cutoffFactor R.ballRadius R.barrierFn) η * Real.exp (-Ψ η)
  have hprod : s.cutoffProduct η = radialWeightProd (cutoffFactor R.ballRadius R.barrierFn) η := by
    unfold ChartSetting.cutoffProduct radialWeightProd
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [coordNorm_eq_norm]
  rw [hprod]
  by_cases h : s.InBalls η
  · rw [(hgerm η h).eq_of_nhds]
  · have hz : radialWeightProd (cutoffFactor R.ballRadius R.barrierFn) η = 0 := by
      unfold ChartSetting.InBalls at h
      push Not at h
      obtain ⟨b, hb⟩ := h
      rw [coordNorm_eq_norm] at hb
      refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
      simp only [cutoffFactor]
      rw [if_neg (not_lt.mpr hb.le)]
    rw [hz, zero_mul, zero_mul]
theorem cutoffIntegral_pos (hFour : FourCornerLogRatioBound) {ι : Type} [Fintype ι] [DecidableEq ι] {ρ m κ : ℝ}
    {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hm : 0 < m) (hκ : 0 ≤ κ)
    (hp : IsCutoff ρ p) (hd : IsPseudoMetricOnBonds d) (hc : IsUniformlyConvexDecaying ρ m κ d Ψ K) :
    0 < cutoffIntegral ρ p Ψ := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : BondField ι) ρ).exists_bound_of_continuousOn
    hc.smooth.continuous.continuousOn
  have h := hFour ι ρ m κ d (fun _ _ => Ψ) (fun _ _ => K) p (fun _ => 0) (fun _ => 0) 0 M hρ hm hκ hp hd
    (fun _ _ => hc) (fun _ _ η hη => hM η (by
      rw [mem_closedBall_zero_iff]
      exact (pi_norm_le_iff_of_nonneg hρ.le).mpr fun b => (hη b).le))
    (fun _ η _ b => by simp [bondGradNorm]) (fun _ η _ b => by simp [bondGradNorm]) (fun η _ => by simp)
  exact h.1 0 0
end HeldBondRatios
open HeldBondRatios in
set_option maxHeartbeats 4000000 in
theorem doubleRatioDecay_holds (hConv : SettingsUniformlyConvex)
    (hCM : ChartPotentialConvex) (hDDs : MixedDifferenceDecay)
    (hFour : FourCornerLogRatioBound) (hSum : DoubleSumBoundBySeparation)
    (hSl : BondGradBoundOfOscillation) (hHeld : DoubleRatioPassesToFullIntegrals)
    (hFew : UniformlyConvexOnSubfamily) (hfine : FineDistanceLeBlockDistance)
    (hBonds : BondsPerBlockBound) : DoubleRatioDecay := by
  obtain ⟨rt₀, hrt₀, hC⟩ := hConv
  refine ⟨rt₀, hrt₀, fun T hT hrtT => ?_⟩
  obtain ⟨Cq, yc, hCq, hconv⟩ := hC T hT hrtT
  obtain ⟨CB', yb, hDDT⟩ := hDDs T hT
  have hρT : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold ParameterAssignment.ballRadius
    positivity
  have hrtP : 0 < T.rt := hT.rt_pos
  have hlamP : 0 < T.lam := hT.chain.2.2.1
  have hLT : (0 : ℝ) < T.side := by
    have := hT.L_ge
    have h1 : 0 < T.side := by omega
    exact_mod_cast h1
  obtain ⟨A₀, hA₀0, hA₀⟩ := exists_sum_exp_supDist_le (T.rt / 2) (by positivity)
  set CB : ℝ := |CB'| with hCBd
  have hCB : 0 ≤ CB := abs_nonneg _
  set W : ℝ := 4 * (2 * (T.side : ℝ)) ^ 4 * A₀ with hWd
  have hW0 : 0 ≤ W := by positivity
  set Ks : ℝ := 2 * CB / T.ballRadius + 4 * Cq * T.ballRadius with hKs
  have hKs0 : 0 ≤ Ks := by positivity
  set K₂ : ℝ := 2 * Cq + Ks * Real.exp (12 * T.rt) with hK₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  set K₃ : ℝ := (8 * K₂ ^ 2 * W ^ 2 / T.lam * Real.exp ((96 + 1 / 2) * T.rt) + CB * Real.exp (5 * T.rt)) *
    Real.exp (T.rt) with hK₃
  obtain ⟨X, hX⟩ := exists_threshold_clusterRange K₃ (T.rt / (2 * T.side)) (20 * T.side) (by positivity)
  refine ⟨max (max yc yb) (max X (max T.floorMin 1)), fun y hy R hOn n _ hn s θ θ' hset hcomp hfs => ?_⟩
  have hyx := hOn.le_coupling
  have hy1 : yc ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy2 : yb ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy3 : X ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy4 : T.floorMin ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hy5 : (1 : ℝ) ≤ y := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hR := hOn.params_eq
  have hfit : R.params.Admissible := by
    rw [hR]
    exact hT.fits y hy4
  have hLeq : R.params.side = T.side := by
    rw [hR]
    rfl
  have hrtR : R.params.rt = T.rt := by
    rw [hR]
    rfl
  have hσR : R.params.threshold = T.threshold := by
    rw [hR]
    rfl
  have hρR : R.ballRadius = T.ballRadius := by
    simp only [StepSetup.ballRadius, ParameterAssignment.ballRadius, hσR]
  have hLr : (R.params.side : ℝ) = T.side := congrArg _ hLeq
  have hx : 0 < R.coupling := by linarith
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    rw [hρR, hOn.barrierFn_eq]
    exact hT.cut
  have hρ : 0 < R.ballRadius := hρR ▸ hρT
  have hrt : 0 < R.params.rt := hrtR ▸ hrtP
  have hLbig : 2 ^ 16 ≤ R.params.side := hfit.L_ge
  obtain ⟨hrBig, hrExp⟩ := hX R.coupling (by linarith)
  have hr20 : 20 * R.params.side ≤ R.range := by
    have : ((20 * R.params.side : ℕ) : ℝ) ≤ (R.range : ℝ) := by
      push_cast
      rw [hLr]
      exact hrBig
    exact_mod_cast this
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hDD : MixedDifferenceBound R n CB := fun s' η' Q Q' g a1 a2 a3 a4 a5 a6 a7 a8 => by
    refine (hDDT y hy2 R hR hOn.anchorRadius_eq hyx hOn.isStep.1 n hn s' η' Q Q' g a1 a2 a3 a4 a5 a6 a7 a8).trans ?_
    have hm : 0 ≤ min (Q.card : ℝ) Q'.card := le_min (by positivity) (by positivity)
    have := le_abs_self CB'
    gcongr
  have hfull := fun i j => (hconv y hy1 R hOn n hn (s i j) (hset i j)).1
  have hcm := fun i j => hCM R T.lam Cq (hσR ▸ hT.σ_pos) hrt hx hlamP n (s i j) _ (hfull i j)
  choose Ψf Kf hgerm hcv hkb _ using hcm
  have hfirst : ∀ i j η, (s i j).InBalls η → ∀ b X, ‖X‖ = 1 →
      |deriv (fun τ : ℝ => (s i j).potential (Function.update η b (η b + τ • X))) 0| ≤ Cq * R.coupling :=
    fun i j => (hfull i j).firstDeriv_le
  have hbd : ∀ i j, IsPseudoMetricOnBonds (s i j).bondDist := fun i j =>
    ⟨fun b => by simp [ChartSetting.bondDist, bondBlockDist, supDist_self],
      fun b b' => by simp only [ChartSetting.bondDist, bondBlockDist]; rw [supDist_comm],
      fun b b' b'' => by
        simp only [ChartSetting.bondDist, bondBlockDist]
        exact_mod_cast supDist_triangle _ _ _⟩
  have hm : 0 < R.coupling * T.lam / 8 := by positivity
  have hZeq : ∀ i j, (s i j).integral = cutoffIntegral R.ballRadius R.barrierFn (Ψf i j) := fun i j =>
    integral_eq_cutoffIntegral (s i j) (hgerm i j)
  have hZpos : ∀ i j, 0 < cutoffIntegral R.ballRadius R.barrierFn (Ψf i j) := fun i j =>
    cutoffIntegral_pos hFour hρ hm hrt.le hcut (hbd i j) (hcv i j)
  set P := coreBlocks R.params.side R.range θ with hP
  set P' := coreBlocks R.params.side R.range θ' with hP'
  have hcores : ∀ y ∈ P, ∀ y' ∈ P', 2 * R.range < R.params.side * _root_.YangMills.Construction.TorusFields.supDist y y' + R.params.side :=
    fun y hy y' hy' => coreBlocks_far_apart hfine hcomp.far_apart hy hy'
  have hLcast : (0 : ℝ) < R.params.side := by exact_mod_cast hL0
  have hgapR : ∀ y ∈ P, ∀ y' ∈ P', 2 * (R.range : ℝ) / R.params.side - 3 ≤ _root_.YangMills.Construction.TorusFields.supDist y y' := by
    intro y hy y' hy'
    have h1 := hcores y hy y' hy'
    have h2 : (2 * (R.range : ℝ)) < R.params.side * _root_.YangMills.Construction.TorusFields.supDist y y' + R.params.side := by exact_mod_cast h1
    have h3 : 2 * (R.range : ℝ) / R.params.side < _root_.YangMills.Construction.TorusFields.supDist y y' + 1 := by
      rw [div_lt_iff₀ hLcast]
      nlinarith
    linarith
  refine ⟨fun i j => by rw [hZeq]; exact hZpos i j, hgapR, fun D hD => ?_⟩
  classical
  have hnb : ∀ b, ¬ (BondJoinsBlocks R.params.side P b ∧ BondJoinsBlocks R.params.side P' b) := by
    rintro b ⟨h1, h2⟩
    have := hcores _ h1.1 _ h2.1
    rw [supDist_self] at this
    omega
  set F : Finset (TorusBond (n * R.params.side)) := (s 0 0).free.filter
    fun b => ¬ BondJoinsBlocks R.params.side P b ∧ ¬ BondJoinsBlocks R.params.side P' b with hF
  set C : Fin 2 → Finset (TorusBond (n * R.params.side)) := fun i =>
    (s i 0).free.filter (BondJoinsBlocks R.params.side P) with hCd
  set C' : Fin 2 → Finset (TorusBond (n * R.params.side)) := fun j =>
    (s 0 j).free.filter (BondJoinsBlocks R.params.side P') with hC'd
  have hPC : ∀ i x, x ∈ C i → BondJoinsBlocks R.params.side P x := fun i x hx => (Finset.mem_filter.mp hx).2
  have hPC' : ∀ j x, x ∈ C' j → BondJoinsBlocks R.params.side P' x := fun j x hx => (Finset.mem_filter.mp hx).2
  have hFoff : ∀ b ∈ F, ¬ BondJoinsBlocks R.params.side P b ∧ ¬ BondJoinsBlocks R.params.side P' b :=
    fun b hb => (Finset.mem_filter.mp hb).2
  have hS : ∀ i j, (s i j).free = C i ∪ (C' j ∪ F) := by
    intro i j
    ext x
    simp only [Finset.mem_union, hCd, hC'd, hF, Finset.mem_filter]
    by_cases h1 : BondJoinsBlocks R.params.side P x
    · have h2 : ¬ BondJoinsBlocks R.params.side P' x := fun h => hnb x ⟨h1, h⟩
      have e := (hfs.first_agree i j 0).free_iff x h1
      constructor
      · intro hx
        exact Or.inl ⟨e.mp hx, h1⟩
      · rintro (h | h | h)
        · exact e.mpr h.1
        · exact absurd h.2 h2
        · exact absurd h1 h.2.1
    · by_cases h2 : BondJoinsBlocks R.params.side P' x
      · have e := (hfs.second_agree i 0 j).free_iff x h2
        constructor
        · intro hx
          exact Or.inr (Or.inl ⟨e.mp hx, h2⟩)
        · rintro (h | h | h)
          · exact absurd h.2 h1
          · exact e.mpr h.1
          · exact absurd h2 h.2.2
      · have e := (hfs.rest_agree i j 0 0).free_iff x ⟨h1, h2⟩
        constructor
        · intro hx
          exact Or.inr (Or.inr ⟨e.mp hx, h1, h2⟩)
        · rintro (h | h | h)
          · exact absurd h.2 h1
          · exact absurd h.2 h2
          · exact e.mpr h.1
  have hd1 : ∀ i j, Disjoint (C i) (C' j ∪ F) := by
    intro i j
    refine Finset.disjoint_left.mpr fun x hx hx' => ?_
    rcases Finset.mem_union.mp hx' with h | h
    · exact hnb x ⟨hPC i x hx, hPC' j x h⟩
    · exact (hFoff x h).1 (hPC i x hx)
  have hd2 : ∀ j, Disjoint (C' j) F := fun j =>
    Finset.disjoint_left.mpr fun x hx hx' => (hFoff x hx').2 (hPC' j x hx)
  have hcl := fun i j X hX => no_component_meets_both hfine hcomp (by omega) i j X hX
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ℕ, q₀ = R.range / (16 * R.params.side) := ⟨_, rfl⟩
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : ℕ, G₀ = q₀ + 24 := ⟨_, rfl⟩
  have hG : 18 ≤ G₀ := by omega
  have hrG : (R.range : ℝ) / 16 ≤ (R.params.side * (G₀ - 6) : ℕ) := by
    have h1 : R.range < 16 * R.params.side * (q₀ + 1) := by
      rw [hq₀]
      exact Nat.lt_mul_div_succ _ (by positivity)
    have h2 : R.params.side * (q₀ + 1) ≤ R.params.side * (G₀ - 6) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : (R.range : ℝ) ≤ 16 * ((R.params.side * (G₀ - 6) : ℕ) : ℝ) := by
      have : R.range ≤ 16 * (R.params.side * (G₀ - 6)) := by
        calc R.range ≤ 16 * R.params.side * (q₀ + 1) := h1.le
          _ = 16 * (R.params.side * (q₀ + 1)) := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ h2
      exact_mod_cast this
    linarith
  have hG4 : 4 * T.rt * G₀ ≤ T.rt * R.range / (4 * T.side) + 96 * T.rt := by
    have h1 : (q₀ : ℝ) ≤ (R.range : ℝ) / ((16 * R.params.side : ℕ) : ℝ) := by
      rw [hq₀]
      exact Nat.cast_div_le
    have h2 : (G₀ : ℝ) ≤ (R.range : ℝ) / (16 * T.side) + 24 := by
      rw [hG₀]
      push_cast at h1 ⊢
      rw [hLr] at h1
      linarith
    have h3 : T.rt * R.range / (4 * T.side) = 4 * T.rt * ((R.range : ℝ) / (16 * T.side)) := by
      field_simp
      ring
    rw [h3]
    nlinarith
  set A : ℝ := K₂ * R.coupling * Real.exp (2 * R.params.rt * G₀) with hAd
  have hexp1 : (1 : ℝ) ≤ Real.exp (2 * R.params.rt * G₀) := Real.one_le_exp (by positivity)
  have hA₁ : 2 * (Cq * R.coupling) * Real.exp (2 * R.params.rt * G₀) ≤ A := by
    have : 0 ≤ Ks * Real.exp (12 * T.rt) := by positivity
    have h1 : 2 * Cq ≤ K₂ := by
      simp only [hK₂]
      linarith
    simp only [hAd]
    have e : 2 * (Cq * R.coupling) * Real.exp (2 * R.params.rt * G₀) =
        2 * Cq * R.coupling * Real.exp (2 * R.params.rt * G₀) := by ring
    rw [e]
    gcongr
  have hA₂ : (2 * CB / R.ballRadius + 4 * Cq * R.ballRadius) * R.coupling * Real.exp (12 * R.params.rt) ≤ A := by
    rw [hρR, hrtR]
    have h1 : Ks * Real.exp (12 * T.rt) ≤ K₂ := by
      simp only [hK₂]
      linarith
    have e : (2 * CB / T.ballRadius + 4 * Cq * T.ballRadius) * R.coupling * Real.exp (12 * T.rt) =
        Ks * Real.exp (12 * T.rt) * R.coupling * 1 := by
      simp only [hKs]
      ring
    rw [e]
    simp only [hAd]
    gcongr
  have hW : ∀ y : TorusSite n,
      ∑ b : F, Real.exp (-(R.params.rt / 2 * (_root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1.1) y : ℝ))) ≤ W := by
    intro y
    have h0 := hA₀ n y 0
    have h1 : ∑ Y : TorusSite n, Real.exp (-(T.rt / 2 * (_root_.YangMills.Construction.TorusFields.supDist Y y : ℝ))) ≤ A₀ := by
      simpa using h0
    rw [hrtR]
    have h2 := sum_exp_bonds_le hBonds R.params.side F (T.rt / 2) A₀ y h1
    rw [hLr] at h2
    exact h2
  set Dm : ℕ := max D (2 * R.range / R.params.side - 3) with hDm
  have hgap : ∀ y ∈ P, ∀ y' ∈ P', Dm ≤ _root_.YangMills.Construction.TorusFields.supDist y y' := by
    intro y hy y' hy'
    refine max_le (hD y hy y' hy') ?_
    have h1 := hcores y hy y' hy'
    have h2 : 2 * R.range / R.params.side ≤ _root_.YangMills.Construction.TorusFields.supDist y y' + 1 := by
      rw [Nat.div_le_iff_le_mul_add_pred hL0]
      have : R.params.side * _root_.YangMills.Construction.TorusFields.supDist y y' + R.params.side = R.params.side * (_root_.YangMills.Construction.TorusFields.supDist y y' + 1) := by ring
      omega
    omega
  have hq40 : 40 ≤ 2 * R.range / R.params.side := by
    rw [Nat.le_div_iff_mul_le hL0]
    omega
  have h16 : 16 ≤ Dm := le_trans (by omega) (le_max_right _ _)
  have hq : 2 * R.range < R.params.side * (2 * R.range / R.params.side + 1) := Nat.lt_mul_div_succ _ hL0
  have hDmq : 2 * R.range / R.params.side ≤ Dm + 3 := by
    have := le_max_right D (2 * R.range / R.params.side - 3)
    omega
  have hrD : (R.range : ℝ) / 16 ≤ (R.params.side * (Dm - 5) : ℕ) := by
    have h1 : R.params.side * (2 * R.range / R.params.side + 1) ≤ R.params.side * (Dm - 5 + 9) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : 2 * R.range ≤ R.params.side * (Dm - 5) + 9 * R.params.side := by
      calc 2 * R.range ≤ R.params.side * (2 * R.range / R.params.side + 1) := hq.le
        _ ≤ R.params.side * (Dm - 5 + 9) := h1
        _ = R.params.side * (Dm - 5) + 9 * R.params.side := by ring
    have h3 : R.range ≤ 16 * (R.params.side * (Dm - 5)) := by omega
    have h4 : (R.range : ℝ) ≤ 16 * ((R.params.side * (Dm - 5) : ℕ) : ℝ) := by exact_mod_cast h3
    linarith
  have hcoreMain := fun (a : ∀ i, C i → BondVector) (b : ∀ j, C' j → BondVector) ha hb =>
    logRatio_assembled hFew hFour hSum hSl hfine hfit hCB hCq.le hx hlamP hDD hset hfs hρ hcut (by omega) hrt hLbig
      hS hd1 hd2 hPC hPC' hFoff hnb Ψf Kf hgerm hcv hkb hfirst G₀ hG hrG hA₁ hA₂ hW0 hW Dm hgap h16 hrD hcl a b
      ha hb
  set μ : ℝ := min (P.card : ℝ) P'.card with hμ
  set ε : ℝ := (R.coupling * T.lam / 8)⁻¹ * (A ^ 2 * W ^ 2 * μ * Real.exp (-(R.params.rt * Dm / 2))) +
    CB * R.coupling * μ * Real.exp (-(R.params.decayRate * (R.params.side * (Dm - 5) : ℕ) / 3)) with hε
  have hratio : ∀ (a : ∀ i, C i → BondVector) (b : ∀ j, C' j → BondVector), (∀ i x, ‖a i x‖ < R.ballRadius) →
      (∀ j x, ‖b j x‖ < R.ballRadius) → _ := fun a b ha hb =>
    product_bounds_of_logs ((hcoreMain a b ha hb).1 1 1) ((hcoreMain a b ha hb).1 0 0)
      ((hcoreMain a b ha hb).1 1 0) ((hcoreMain a b ha hb).1 0 1) (hcoreMain a b ha hb).2
  have h₁ := hHeld (TorusBond (n * R.params.side)) (fun i j => (s i j).free) C C' F Ψf R.ballRadius
    (Real.exp ε) R.barrierFn hρ hcut hS hd1 hd2
    (fun i j => (hcv i j).smooth.continuous) (fun a₁ a₀ b₁ b₀ h1 h2 h3 h4 =>
      (hratio (finTwoPick (M := fun i => C i → BondVector) a₀ a₁)
        (finTwoPick (M := fun j => C' j → BondVector) b₀ b₁)
        (by
          intro i x
          fin_cases i
          · exact h2 x
          · exact h1 x)
        (by
          intro j x
          fin_cases j
          · exact h4 x
          · exact h3 x)).1)
  have h₂ := hHeld (TorusBond (n * R.params.side)) (fun i j => (s i (1 - j)).free) C (fun j => C' (1 - j)) F
    (fun i j => Ψf i (1 - j)) R.ballRadius (Real.exp ε) R.barrierFn hρ hcut (fun i j => hS i (1 - j))
    (fun i j => hd1 i (1 - j)) (fun j => hd2 (1 - j)) (fun i j => (hcv i (1 - j)).smooth.continuous)
    (fun a₁ a₀ b₁ b₀ h1 h2 h3 h4 =>
      (hratio (finTwoPick (M := fun i => C i → BondVector) a₀ a₁)
        (finTwoPick (M := fun j => C' j → BondVector) b₁ b₀)
        (by
          intro i x
          fin_cases i
          · exact h2 x
          · exact h1 x)
        (by
          intro j x
          fin_cases j
          · exact h3 x
          · exact h4 x)).2)
  have hlog := abs_log_ratio_le (hZpos 1 1) (hZpos 0 0) (hZpos 1 0) (hZpos 0 1) h₁ h₂
  rw [hZeq 1 1, hZeq 0 0, hZeq 1 0, hZeq 0 1]
  refine hlog.trans ?_
  have hμ0 : 0 ≤ μ := le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hDmR : 2 * (R.range : ℝ) / T.side - 4 ≤ Dm := by
    have h1 : (2 * (R.range : ℝ)) < T.side * ((2 * R.range / R.params.side : ℕ) + 1) := by
      have : (2 * R.range : ℕ) < R.params.side * (2 * R.range / R.params.side + 1) := hq
      have h2 : ((2 * R.range : ℕ) : ℝ) < ((R.params.side * (2 * R.range / R.params.side + 1) : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast at h2
      rw [hLr] at h2
      exact h2
    have h3 : ((2 * R.range / R.params.side : ℕ) : ℝ) ≤ Dm + 3 := by exact_mod_cast hDmq
    have h4 : 2 * (R.range : ℝ) / T.side < ((2 * R.range / R.params.side : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hLT]
      linarith
    linarith
  have hfor : T.rt * ((Dm : ℝ) - 5) ≤ R.params.decayRate * (R.params.side * (Dm - 5) : ℕ) / 3 := by
    have h1 : R.params.decayRate = T.rt / 2 ^ 12 := by
      show R.params.rt / 2 ^ 12 = _
      rw [hrtR]
    have hLb : (2 ^ 16 : ℝ) ≤ R.params.side := by exact_mod_cast hLbig
    have h2 : ((Dm - 5 : ℕ) : ℝ) = (Dm : ℝ) - 5 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [h1]
    push_cast
    rw [h2]
    have h3 : 0 ≤ (Dm : ℝ) - 5 := by
      rw [← h2]
      positivity
    have h4 : 0 ≤ T.rt * ((Dm : ℝ) - 5) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hLb h4]
  have hfinal := numeric_bound (x := R.coupling) (lam := T.lam) (K₂ := K₂) (W := W) (CB := CB) (rt := T.rt)
    (μ := μ) (f := R.params.decayRate * (R.params.side * (Dm - 5) : ℕ) / 3) (r := R.range) (L := T.side) (G := G₀)
    (D := Dm) hx hlamP hrtP hCB hμ0 hLT hDmR (by positivity) hG4 hfor (by
      have h1 := hrExp
      have e : T.rt / (2 * (T.side : ℝ)) * (clusterRange R.coupling : ℝ) = T.rt * R.range / (2 * T.side) := by
        show T.rt / (2 * (T.side : ℝ)) * (R.range : ℝ) = _
        field_simp
      rw [e] at h1
      exact h1)
  have hεeq : ε ≤ μ * Real.exp (-(T.rt * Dm / 8)) := by
    simp only [hε, hAd, hrtR]
    exact hfinal
  refine hεeq.trans ?_
  rw [hrtR]
  have hDDm : (D : ℝ) ≤ Dm := by exact_mod_cast le_max_left _ _
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hμ0
  have : T.rt * (D : ℝ) ≤ T.rt * Dm := mul_le_mul_of_nonneg_left hDDm hrtP.le
  linarith
end YangMills.Construction.ClusterExpansionOfAStep
end
