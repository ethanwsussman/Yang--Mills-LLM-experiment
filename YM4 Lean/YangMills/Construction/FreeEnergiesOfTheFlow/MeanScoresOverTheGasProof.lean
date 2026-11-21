import YangMills.Construction.ClusterExpansionOfAStep.ClassesAreCountedAtTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.ZonesOfAFamily
import YangMills.Construction.FreeEnergiesOfTheFlow.LabelsOfAConfiguration
import YangMills.Construction.FreeEnergiesOfTheFlow.MeanScoresOverTheGas
import YangMills.Construction.ResponseInTheExpansion.MajorantsOfAStep
import YangMills.Construction.ResponseInTheExpansion.ScoreOfAClassIsPaid
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace YangMills.Construction
open Dobrushin
namespace FreeEnergies
open StepGas StepSettings RenormalizationStepParameters TorusLumps TorusFields WeightedResponses ResponseInTheExpansion BlockAverages ClusterBounds
  ClusterExpansionOfAStep
private theorem prod_one_add_sub_one_le {ι : Type} (I : Finset ι) (T W S : ι → ℝ) (hT0 : ∀ j ∈ I, 0 ≤ T j)
    (hS0 : ∀ j ∈ I, 0 ≤ S j) (hW0 : ∀ j ∈ I, 0 ≤ W j) (hW1 : ∀ j ∈ I, W j ≤ 1) (hTW : ∀ j ∈ I, T j ≤ W j * S j) :
    ∏ j ∈ I, (1 + T j) - 1 ≤ (∑ j ∈ I, W j) * Real.exp (∑ j ∈ I, S j) ∧
      ∏ j ∈ I, (1 + T j) ≤ Real.exp (∑ j ∈ I, S j) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih (fun j hj => hT0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => hS0 j (Finset.mem_insert_of_mem hj)) (fun j hj => hW0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => hW1 j (Finset.mem_insert_of_mem hj)) (fun j hj => hTW j (Finset.mem_insert_of_mem hj))
    have mem := Finset.mem_insert_self a s
    have hSa := hS0 a mem
    have hWa := hW0 a mem
    have hWa1 := hW1 a mem
    have hTWa := hTW a mem
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, Real.exp_add]
    set P := ∏ j ∈ s, (1 + T j) with hP
    set E := Real.exp (∑ j ∈ s, S j) with hE
    set F := Real.exp (S a) with hF
    set w := ∑ j ∈ s, W j with hw
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun j hj => by
      linarith [hT0 j (Finset.mem_insert_of_mem hj)]
    have hw0 : 0 ≤ w := Finset.sum_nonneg fun j hj => hW0 j (Finset.mem_insert_of_mem hj)
    have hF1 : 1 + S a ≤ F := by
      have := Real.add_one_le_exp (S a)
      linarith
    have hTS : T a ≤ S a := by nlinarith
    have hTF : T a ≤ W a * F := hTWa.trans (mul_le_mul_of_nonneg_left (by linarith) hWa)
    constructor
    · have e1 : T a * P ≤ (W a * F) * E := mul_le_mul hTF h2 hP0 (mul_nonneg hWa (by linarith))
      have e2 : w * E ≤ w * (F * E) := by
        refine mul_le_mul_of_nonneg_left ?_ hw0
        nlinarith
      nlinarith
    · exact mul_le_mul (by linarith) h2 hP0 (by linarith)
variable {R : StepSetup} {n : ℕ} [NeZero n] {A : ResponseSetup R} {G : GasGround R n}
private theorem familyOf_of_spin_eq_inr {σ : G.Config} {i : G.GasSpin} {w : G.SpinState i} (hv : σ i = Sum.inr w) :
    G.familyOf σ i.1 = Sum.inr w.1 := by
  classical
  have hv' : σ ⟨i.1, i.2⟩ = Sum.inr w := hv
  unfold GasGround.familyOf
  rw [dif_pos i.2]
  simp [hv']
private theorem mem_sites_familyOf_of_spin_eq_inr {σ : G.Config} {i : G.GasSpin} {w : G.SpinState i}
    (hv : σ i = Sum.inr w) {y : TorusSite (n * R.params.side)} (hy : y ∈ i.1.2) : y ∈ (G.familyOf σ).sites := by
  classical
  unfold GasFamily.sites
  refine Finset.mem_biUnion.mpr ⟨i.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hy⟩
  unfold GasFamily.Occupies
  rw [familyOf_of_spin_eq_inr hv]
  rfl
private theorem not_mem_recordedSites_of_mem_spin (i : G.GasSpin) {y : TorusSite (n * R.params.side)} (hy : y ∈ i.1.2) :
    y ∉ G.recordedSites := by apply _root_.YangMills.Construction.FamilyZones.not_mem_recordedSites_of_mem_sites <;> assumption
private theorem siteScore_configSetting_eq {σ : G.Config} (ha : G.pairConstraint.IsAdmissible σ)
    (y : TorusSite (n * R.params.side)) :
    siteScore A.score (configSetting G σ).support (configSetting G σ).labelling y =
      recordedSiteScore A G y + ∑ i, spinSiteScore A G i y (σ i) := by
  classical
  set γ := G.familyOf σ with hγ
  have hY : (configSetting G σ).support = G.recordedSites ∪ γ.sites := rfl
  by_cases hg : y ∈ γ.sites
  · have hy : y ∈ (configSetting G σ).support := by
      rw [hY]
      exact Finset.mem_union_right _ hg
    have hl : (configSetting G σ).labelling ⟨y, hy⟩ = γ.labelAt hg := dif_pos hg
    obtain ⟨hθ, hyθ⟩ := (GasFamily.exists_of_mem_sites hg).choose_spec
    set θ := (GasFamily.exists_of_mem_sites hg).choose with hθdef
    have hsup : G.IsGasSupport θ := by
      by_contra hc
      have : γ θ = Sum.inl () := dif_neg hc
      simp [GasFamily.Occupies, this] at hθ
    rcases hv : σ ⟨θ, hsup⟩ with u | w
    · exfalso
      have : γ θ = Sum.inl () := by
        show G.familyOf σ θ = _
        unfold GasGround.familyOf
        rw [dif_pos hsup]
        simp [hv]
      simp [GasFamily.Occupies, this] at hθ
    · have hγθ : γ θ = Sum.inr w.1 := familyOf_of_spin_eq_inr (i := ⟨θ, hsup⟩) hv
      have hstate : γ.state hθ = w.1 := by
        unfold GasFamily.state
        simp [hγθ]
      have hlab : γ.labelAt hg = (w.1 : SupportState θ).2.1 ⟨y, hyθ⟩ := by
        show (γ.state (GasFamily.exists_of_mem_sites hg).choose_spec.1).2.1
          ⟨y, (GasFamily.exists_of_mem_sites hg).choose_spec.2⟩ = _
        rw [hstate]
      have hterm : spinSiteScore A G ⟨θ, hsup⟩ y (σ ⟨θ, hsup⟩) = A.score (γ.labelAt hg) := by
        rw [hv, hlab]
        simp [spinSiteScore, hyθ]
      have hother : ∀ j : G.GasSpin, j ≠ ⟨θ, hsup⟩ → spinSiteScore A G j y (σ j) = 0 := by
        intro j hj
        rcases hvj : σ j with u | wj
        · rfl
        · by_cases hyj : y ∈ j.1.2
          · exfalso
            rcases ha ⟨θ, hsup⟩ j hj.symm with h | h | h
            · rw [hv] at h
              exact absurd h (by simp)
            · rw [hvj] at h
              exact absurd h (by simp)
            · have := h y (Finset.mem_union_right _ hyθ) y (Finset.mem_union_right _ hyj)
              rw [supDist_self] at this
              omega
          · simp [spinSiteScore, hyj]
      have hsum : ∑ i, spinSiteScore A G i y (σ i) = A.score (γ.labelAt hg) := by
        rw [Finset.sum_eq_single (⟨θ, hsup⟩ : G.GasSpin) (fun j _ hj => hother j hj)
          (fun h => absurd (Finset.mem_univ _) h), hterm]
      have hst : recordedSiteScore A G y = 0 := by
        unfold recordedSiteScore siteScore
        rw [dif_neg (not_mem_recordedSites_of_mem_spin (⟨θ, hsup⟩ : G.GasSpin) hyθ)]
      rw [hst, hsum, zero_add]
      unfold siteScore
      rw [dif_pos hy, hl]
  · have hzero : ∑ i, spinSiteScore A G i y (σ i) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases hvj : σ j with u | wj
      · rfl
      · by_cases hyj : y ∈ j.1.2
        · exact absurd (mem_sites_familyOf_of_spin_eq_inr hvj hyj) hg
        · simp [spinSiteScore, hyj]
    rw [hzero, add_zero]
    unfold recordedSiteScore siteScore
    by_cases hm : y ∈ G.recordedSites
    · have hy : y ∈ (configSetting G σ).support := by
        rw [hY]
        exact Finset.mem_union_left _ hm
      have hl : (configSetting G σ).labelling ⟨y, hy⟩ = G.recordedLabel ⟨y, hm⟩ := dif_neg hg
      rw [dif_pos hy, dif_pos hm, hl]
    · have hy : y ∉ (configSetting G σ).support := by
        rw [hY]
        intro h
        rcases Finset.mem_union.mp h with h | h
        · exact hm h
        · exact hg h
      rw [dif_neg hy, dif_neg hm]
abbrev _root_.YangMills.SharedProofs.p55158 := @siteScore_configSetting_eq
private theorem meanSiteScore_nonneg' {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) {m : ℕ} [NeZero m]
    (S Y : Finset (TorusSite m)) (ω : Y → Ω) : 0 ≤ meanSiteScore s S Y ω := by
  unfold meanSiteScore
  have : 0 ≤ (S.card : ℝ)⁻¹ * ∑ y ∈ S, siteScore s Y ω y :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun y _ => siteScore_nonneg hs _ _ _)
  linarith
private theorem add_sum_le_mul_prod_one_add {κ : Type} (s : Finset κ) (t : κ → ℝ) (ht : ∀ i ∈ s, 0 ≤ t i) {a : ℝ}
    (ha : 1 ≤ a) : a + ∑ i ∈ s, t i ≤ a * ∏ i ∈ s, (1 + t i) ∧ 1 ≤ ∏ i ∈ s, (1 + t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => ht i (Finset.mem_insert_of_mem hi)
    have h0 := ht b (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert hb, Finset.prod_insert hb]
    constructor
    · have h3 : 0 ≤ t b * (a * ∏ i ∈ s, (1 + t i) - 1) := mul_nonneg h0 (by nlinarith)
      nlinarith
    · nlinarith
abbrev _root_.YangMills.SharedProofs.p28055 := @add_sum_le_mul_prod_one_add
private def spinFactor (A : ResponseSetup R) (G : GasGround R n) {ι : Type} (I : Finset ι)
    (B : ι → Finset (TorusSite (n * R.params.side))) (i : G.GasSpin) (v : G.SpinValue i) : ℝ :=
  ∏ j ∈ I, (1 + ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, spinSiteScore A G i y v)
private def recordedMean (A : ResponseSetup R) (G : GasGround R n) (S : Finset (TorusSite (n * R.params.side))) : ℝ :=
  1 + (S.card : ℝ)⁻¹ * ∑ y ∈ S, recordedSiteScore A G y
private theorem one_le_recordedMean (hs : ∀ w, 0 ≤ A.score w) (S : Finset (TorusSite (n * R.params.side))) :
    1 ≤ recordedMean A G S := by
  unfold recordedMean
  have : 0 ≤ (S.card : ℝ)⁻¹ * ∑ y ∈ S, recordedSiteScore A G y :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun y _ => siteScore_nonneg hs _ _ _)
  linarith
abbrev _root_.YangMills.DeltaSharedProofs.p502616 := @one_le_recordedMean
private theorem spinMean_nonneg (hs : ∀ w, 0 ≤ A.score w) (i : G.GasSpin) (v : G.SpinValue i)
    (S : Finset (TorusSite (n * R.params.side))) :
    0 ≤ (S.card : ℝ)⁻¹ * ∑ y ∈ S, spinSiteScore A G i y v :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun y _ => spinSiteScore_nonneg hs i y v)
private theorem prod_gasMeanSiteScore_le {ι : Type} (hs : ∀ w, 0 ≤ A.score w) (I : Finset ι)
    (B : ι → Finset (TorusSite (n * R.params.side))) (σ : G.Config) :
    ∏ j ∈ I, gasMeanSiteScore A G (B j) σ ≤
      (∏ j ∈ I, recordedMean A G (B j)) * ∏ i, spinFactor A G I B i (σ i) := by
  classical
  have h1 : ∀ j ∈ I, gasMeanSiteScore A G (B j) σ ≤
      recordedMean A G (B j) * ∏ i, (1 + ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, spinSiteScore A G i y (σ i)) := by
    intro j _
    refine le_trans ?_ (add_sum_le_mul_prod_one_add Finset.univ _ (fun i _ => spinMean_nonneg hs i (σ i) (B j))
      (one_le_recordedMean hs (B j))).1
    unfold gasMeanSiteScore meanSiteScore recordedMean
    have e : ∑ i, ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, spinSiteScore A G i y (σ i) =
        ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, ∑ i, spinSiteScore A G i y (σ i) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    rw [e, add_assoc, ← mul_add, ← Finset.sum_add_distrib]
    have : ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, siteScore A.score (configSetting G σ).support (configSetting G σ).labelling y ≤
        ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, (recordedSiteScore A G y + ∑ i, spinSiteScore A G i y (σ i)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => siteScore_configSetting_le hs σ y)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    linarith
  calc _ ≤ ∏ j ∈ I, (recordedMean A G (B j) *
        ∏ i, (1 + ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, spinSiteScore A G i y (σ i))) :=
        Finset.prod_le_prod (fun j _ => meanSiteScore_nonneg' hs _ _ _) h1
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_comm]
        rfl
private theorem sum_spinSiteScore_le_spinScore (hs : ∀ w, 0 ≤ A.score w) (i : G.GasSpin) (v : G.SpinValue i)
    (S : Finset (TorusSite (n * R.params.side))) :
    ∑ y ∈ S, spinSiteScore A G i y v ≤ spinScore A i v := by
  classical
  rcases v with u | w
  · simp [spinSiteScore, spinScore]
  · set f : TorusSite (n * R.params.side) → ℝ := fun y => if h : y ∈ i.1.2 then A.score (w.1.2.1 ⟨y, h⟩) else 0
      with hf
    have hf0 : ∀ y, 0 ≤ f y := fun y => by
      simp only [hf]
      split_ifs
      · exact hs _
      · exact le_rfl
    have e1 : ∑ y ∈ S, spinSiteScore A G i y (Sum.inr w) = ∑ y ∈ S, f y := rfl
    have e2 : spinScore A i (Sum.inr w) = ∑ y ∈ i.1.2, f y := by
      show ∑ z : i.1.2, A.score (w.1.2.1 z) = _
      rw [← Finset.sum_coe_sort i.1.2 f]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp [hf]
    rw [e1, e2]
    have e3 : ∑ y ∈ S, f y = ∑ y ∈ S.filter (· ∈ i.1.2), f y := by
      refine (Finset.sum_filter_of_ne fun y _ hy => ?_).symm
      by_contra hn
      exact hy (by simp [hf, hn])
    rw [e3]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => (Finset.mem_filter.mp hy).2) fun y _ _ => hf0 y
abbrev _root_.YangMills.SharedProofs.p40586 := @sum_spinSiteScore_le_spinScore
private def meetWeight {ι : Type} (B : ι → Finset (TorusSite (n * R.params.side))) (i : G.GasSpin) (j : ι) : ℝ :=
  open Classical in if (B j ∩ i.1.2).Nonempty then ((B j).card : ℝ)⁻¹ else 0
private theorem meetWeight_nonneg {ι : Type} (B : ι → Finset (TorusSite (n * R.params.side))) (i : G.GasSpin) (j : ι) :
    0 ≤ meetWeight B i j := by
  classical
  unfold meetWeight
  split_ifs
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact le_rfl
private def meetNumber {ι : Type} (I : Finset ι) (B : ι → Finset (TorusSite (n * R.params.side))) (i : G.GasSpin) : ℝ :=
  ∑ j ∈ I, meetWeight B i j
private theorem meetNumber_nonneg {ι : Type} (I : Finset ι) (B : ι → Finset (TorusSite (n * R.params.side)))
    (i : G.GasSpin) : 0 ≤ meetNumber I B i :=
  Finset.sum_nonneg fun j _ => meetWeight_nonneg B i j
private theorem spinFactor_sub_one_le {ι : Type} (hs : ∀ w, 0 ≤ A.score w) (I : Finset ι)
    (B : ι → Finset (TorusSite (n * R.params.side))) (hB : ∀ j ∈ I, (B j).Nonempty)
    (hD : ∀ j ∈ I, ∀ k ∈ I, j ≠ k → Disjoint (B j) (B k)) (i : G.GasSpin) (v : G.SpinValue i) :
    spinFactor A G I B i v - 1 ≤ meetNumber I B i * Real.exp (spinScore A i v) := by
  classical
  have hTW : ∀ j ∈ I, ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, spinSiteScore A G i y v ≤
      meetWeight B i j * ∑ y ∈ B j, spinSiteScore A G i y v := by
    intro j _
    unfold meetWeight
    split_ifs with hm
    · exact le_rfl
    · have : ∑ y ∈ B j, spinSiteScore A G i y v = 0 := by
        refine Finset.sum_eq_zero fun y hy => ?_
        have hyi : y ∉ i.1.2 := fun h => hm ⟨y, Finset.mem_inter.mpr ⟨hy, h⟩⟩
        rcases v with u | w
        · rfl
        · simp [spinSiteScore, hyi]
      simp [this]
  have hW1 : ∀ j ∈ I, meetWeight B i j ≤ 1 := by
    intro j hj
    unfold meetWeight
    split_ifs
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast Finset.card_pos.mpr (hB j hj))
    · exact zero_le_one
  have key := (prod_one_add_sub_one_le I (fun j => ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, spinSiteScore A G i y v)
    (meetWeight B i) (fun j => ∑ y ∈ B j, spinSiteScore A G i y v) (fun j _ => spinMean_nonneg hs i v (B j))
    (fun j _ => Finset.sum_nonneg fun y _ => spinSiteScore_nonneg hs i y v) (fun j _ => meetWeight_nonneg B i j)
    hW1 hTW).1
  have hsum : ∑ j ∈ I, ∑ y ∈ B j, spinSiteScore A G i y v ≤ spinScore A i v := by
    rw [← Finset.sum_biUnion (fun j hj k hk hjk => hD j hj k hk hjk)]
    exact sum_spinSiteScore_le_spinScore hs i v _
  refine key.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum) (meetNumber_nonneg I B i))
private theorem hasSmallExcess_spinFactor {ι : Type} (hs : ∀ w, 0 ≤ A.score w) (I : Finset ι)
    (B : ι → Finset (TorusSite (n * R.params.side))) (hB : ∀ j ∈ I, (B j).Nonempty)
    (hD : ∀ j ∈ I, ∀ k ∈ I, j ≠ k → Disjoint (B j) (B k)) (z : G.GasSpin → ℝ)
    (hpaid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (spinScore A i v)) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
        ENNReal.ofReal (z i) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i))) :
    G.pairConstraint.HasSmallExcess (G.referenceMeasure ∅) G.weight (spinFactor A G I B)
      fun i => meetNumber I B i * z i := by
  classical
  intro i σ hσ
  have hC := meetNumber_nonneg I B i
  calc ∫⁻ s in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (spinFactor A G I B i s - 1) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i s) ∂(G.referenceMeasure ∅ i)
      ≤ ∫⁻ s in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (meetNumber I B i) *
          (ENNReal.ofReal (Real.exp (spinScore A i s)) *
            G.pairConstraint.weightDensity G.weight (Function.update σ i s)) ∂(G.referenceMeasure ∅ i) := by
        refine lintegral_mono fun s => ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC]
        gcongr
        exact spinFactor_sub_one_le hs I B hB hD i s
    _ = ENNReal.ofReal (meetNumber I B i) * ∫⁻ s in {G.pairConstraint.vacant i}ᶜ,
          ENNReal.ofReal (Real.exp (spinScore A i s)) *
            G.pairConstraint.weightDensity G.weight (Function.update σ i s) ∂(G.referenceMeasure ∅ i) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (meetNumber I B i) * (ENNReal.ofReal (z i) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i))) := by
        gcongr
        exact hpaid i σ hσ
    _ = _ := by rw [ENNReal.ofReal_mul hC, mul_assoc]
private theorem recordedMean_le_meanSiteScore (hs : ∀ w, 0 ≤ A.score w) (h₁ : 0 ≤ A.responseParams.s₁)
    (S : Finset (TorusSite (n * R.params.side))) (hS : S.Nonempty) :
    recordedMean A G S ≤
      meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (parentBlocks S) G.state.1 G.state.2 := by
  classical
  have h1 : ∑ y ∈ S, recordedSiteScore A G y ≤
      ∑ Y ∈ parentBlocks S, siteScore (coarseLabelScore A.responseParams.s₁ A.score) G.state.1 G.state.2 Y :=
    sum_recordedSiteScore_le_parentBlocks hs h₁ S
  have h2 : 0 ≤ ∑ y ∈ S, recordedSiteScore A G y := Finset.sum_nonneg fun y _ => siteScore_nonneg hs _ _ _
  have hc : 0 < (parentBlocks (R := R) S).card := Finset.card_pos.mpr (hS.image _)
  have hle : ((parentBlocks (R := R) S).card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_image_le
  have h3 : (S.card : ℝ)⁻¹ ≤ ((parentBlocks (R := R) S).card : ℝ)⁻¹ :=
    inv_anti₀ (by exact_mod_cast hc) hle
  unfold recordedMean meanSiteScore
  have h4 := mul_le_mul h3 h1 h2 (inv_nonneg.mpr (Nat.cast_nonneg _))
  linarith
abbrev _root_.YangMills.DeltaSharedProofs.p501903 := @recordedMean_le_meanSiteScore
private def spinProduct (A : ResponseSetup R) (G : GasGround R n) {ι : Type} (I : Finset ι)
    (B : ι → Finset (TorusSite (n * R.params.side))) (σ : G.Config) : ℝ :=
  ∏ j ∈ I, (1 + ((B j).card : ℝ)⁻¹ * ∑ y ∈ B j, (recordedSiteScore A G y + ∑ i, spinSiteScore A G i y (σ i)))
private theorem measurable_spinProduct (hb : Measurable A.score) {ι : Type} (I : Finset ι)
    (B : ι → Finset (TorusSite (n * R.params.side))) : Measurable (spinProduct A G I B) := by
  unfold spinProduct
  refine Finset.measurable_prod _ fun j _ => ?_
  refine ((Finset.measurable_sum _ fun y _ => ?_).const_mul _).const_add _
  exact (Finset.measurable_sum _ fun i _ =>
    (measurable_spinSiteScore hb i y).comp (measurable_pi_apply i)).const_add _
private theorem prod_gasMeanSiteScore_eq {ι : Type} (I : Finset ι) (B : ι → Finset (TorusSite (n * R.params.side)))
    {σ : G.Config} (ha : G.pairConstraint.IsAdmissible σ) :
    ∏ j ∈ I, gasMeanSiteScore A G (B j) σ = spinProduct A G I B σ := by
  unfold spinProduct gasMeanSiteScore meanSiteScore
  simp only [siteScore_configSetting_eq ha]
private theorem ae_isAdmissible_gibbsLaw {z : G.GasSpin → ℝ}
    (hW : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight z) :
    ∀ᵐ σ ∂(G.gibbsLaw ∅), G.pairConstraint.IsAdmissible σ := by
  classical
  have hlaw : G.gibbsLaw ∅ = G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight := rfl
  rw [hlaw]
  unfold PairConstraint.gibbsLaw
  refine Measure.ae_smul_measure ?_ _
  refine (ae_withDensity_iff hW.measurable_weightDensity).mpr (Filter.Eventually.of_forall fun σ h => ?_)
  by_contra hc
  exact h (by unfold PairConstraint.weightDensity; rw [if_neg hc])
abbrev _root_.YangMills.SharedProofs.p77920 := @ae_isAdmissible_gibbsLaw
theorem gasMeanScoreProductBound_of_clusterBounds (hS : clusterScoreIntegralBound)
    (hM : productMeanScoreStepBound) (hW : GasIsActivityBounded) (hC : _root_.YangMills.Construction.ClusterBounds.ClusterSumBound)
    (hP : MeanOfProductStatement) : gasMeanScoreProductBound := by
  classical
  obtain ⟨r₁, p₁, hS⟩ := hS
  obtain ⟨r₂, p₂, hM⟩ := hM
  obtain ⟨r₄, p₄, hW⟩ := hW
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (r₄ c)), fun c => lt_min (p₁ c) (lt_min (p₂ c) (p₄ c)),
    fun T hT hT' K => ?_⟩
  have t₁ : T.rt ≤ r₁ T.toChainParameters := hT'.trans (min_le_left _ _)
  have t₂ : T.rt ≤ r₂ T.toChainParameters := hT'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have t₄ : T.rt ≤ r₄ T.toChainParameters := hT'.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨yS, hS⟩ := hS T hT t₁ K
  obtain ⟨yM, hM⟩ := hM T hT t₂ K
  obtain ⟨yW, hW⟩ := hW T hT t₄
  obtain ⟨yC, hC⟩ := hC T hT
  refine ⟨max (max yS yM) (max (max yW yC) (max 0 (200 * T.B))),
    fun y hy R A hK hTab n _ G hG₀ ι I B hB hD => ?_⟩
  have f₁ := le_trans (le_max_left _ _) hy
  have f₂ := le_trans (le_max_right _ _) hy
  have fS : yS ≤ y := le_trans (le_max_left _ _) f₁
  have fM : yM ≤ y := le_trans (le_max_right _ _) f₁
  have fW : yW ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) f₂
  have fC : yC ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) f₂
  have f0 : 0 ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) f₂
  have fB : 200 * T.B ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) f₂
  have hOn := hTab.onFamily
  have hl := hOn.params_eq
  have hxy : y ≤ R.coupling := hOn.le_coupling
  have hx : R.nextCoupling ≤ 1.01 * R.coupling := by
    have := (abs_le.mp hTab.abs_sub_le).2
    linarith
  have hprice := hTab.admissible.price
  have hs := hprice.nonneg
  have hb := hprice.borel
  have hfits := hTab.admissible.params_admissible
  have hκ₁ : 0 < T.κ₁ := by
    have h1 := hT.κ_pos
    have h2 := hT.cE_pos
    have h3 := hT.σ_pos
    exact lt_min (by positivity) (by positivity)
  have hch : 0 < T.gasRate := by
    have h1 := hT.κ_pos
    have h2 := hT.cE_pos
    have h3 := hT.σ_pos
    have h4 : 0 < min T.cE (min (T.κ * T.threshold ^ 2) (T.κ₁ * T.threshold ^ 2)) :=
      lt_min h2 (lt_min (by positivity) (by positivity))
    unfold ParameterAssignment.gasRate
    positivity
  have hs₁ : 0 ≤ A.responseParams.s₁ := by
    have h1 : 1 ≤ R.params.coupling := by
      rw [hl]
      exact hT.a_ge
    have h2 := hfits.N₀_nonneg
    have h3 := hfits.Kc_ge
    have h4 : 0 ≤ A.responseParams.C₀ := by
      rw [hfits.C₀_eq]
      linarith
    rw [hfits.s₁_eq]
    positivity
  have hWt : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity T.gasRate) :=
    hW y fW R hOn hx n G hG₀ fun j => j.1.Touches ∅
  have hz0 : ∀ i, 0 ≤ G.spinActivity T.gasRate i := hWt.activity_nonneg
  have hexc := hasSmallExcess_spinFactor (A := A) (G := G) hs I B hB hD (G.spinActivity T.gasRate)
    fun i σ hσ => hS y fS R A hK hTab n G hG₀ i σ hσ
  set e : G.GasSpin → ℝ := fun i => meetNumber I B i * G.spinActivity T.gasRate i with he
  have he0 : ∀ i, 0 ≤ e i := fun i => mul_nonneg (meetNumber_nonneg I B i) (hz0 i)
  set b : ℝ := Real.exp (-(8 * T.gasRate * R.coupling)) with hbd
  have hb0 : 0 ≤ b := (Real.exp_pos _).le
  have hcount : ∀ Y : TorusSite n,
      ∑ θ ∈ supportsAtBlock R.params.side R.range Y, clusterWeight R.params.side T.gasRate R.coupling R.range θ ≤ b := by
    have gen : ∀ ℓ : StepParameters, ℓ = T.stepParameters y → ∀ Y : TorusSite n,
        ∑ θ ∈ supportsAtBlock ℓ.side (clusterRange R.coupling) Y,
          clusterWeight ℓ.side T.gasRate R.coupling (clusterRange R.coupling) θ ≤ b := by
      rintro ℓ rfl Y
      refine le_trans (Finset.sum_le_sum fun θ hθ => ?_) (hC y fC R.coupling hxy n Y)
      have hY := (Finset.mem_filter.mp hθ).2.2
      have hcard : (1 : ℝ) ≤ (supportCore (T.stepParameters y).side (clusterRange R.coupling) θ).card := by
        exact_mod_cast Finset.card_pos.mpr ⟨Y, hY⟩
      have hz : 0 ≤ clusterWeight (T.stepParameters y).side T.gasRate R.coupling (clusterRange R.coupling) θ :=
        (Real.exp_pos _).le
      have h1 : (1 : ℝ) ≤ ((supportCore (T.stepParameters y).side (clusterRange R.coupling) θ).card : ℝ) ^ 4 :=
        one_le_pow₀ hcard
      have h2 : (1 : ℝ) ≤ Real.exp (2 * T.rt *
          (siteDiameter (supportCore (T.stepParameters y).side (clusterRange R.coupling) θ) : ℝ)) :=
        Real.one_le_exp (by have := hT.rt_pos; positivity)
      calc clusterWeight (T.stepParameters y).side T.gasRate R.coupling (clusterRange R.coupling) θ
          = clusterWeight (T.stepParameters y).side T.gasRate R.coupling (clusterRange R.coupling) θ * 1 * 1 := by
            ring
        _ ≤ _ := by gcongr
    exact gen R.params hl
  have hmeet : ∀ j ∈ I, ∑ i : G.GasSpin, meetWeight B i j * G.spinActivity T.gasRate i ≤ b := by
    intro j hj
    have hsp := sum_spin_weight_le_card_parentBlocks_mul (G := G)
      (fun θ => clusterWeight R.params.side T.gasRate R.coupling R.range θ)
      (fun θ => (Real.exp_pos _).le) hcount (B j)
    have hpos : (0 : ℝ) < (B j).card := by exact_mod_cast Finset.card_pos.mpr (hB j hj)
    have hcard : ((parentBlocks (R := R) (B j)).card : ℝ) ≤ (B j).card := by exact_mod_cast Finset.card_image_le
    calc ∑ i : G.GasSpin, meetWeight B i j * G.spinActivity T.gasRate i
        = ((B j).card : ℝ)⁻¹ * ∑ i : G.GasSpin, if (B j ∩ i.1.2).Nonempty then
            clusterWeight R.params.side T.gasRate R.coupling R.range i.1 else 0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          unfold meetWeight GasGround.spinActivity
          split_ifs
          · rfl
          · simp
      _ ≤ ((B j).card : ℝ)⁻¹ * (((parentBlocks (R := R) (B j)).card : ℝ) * b) :=
          mul_le_mul_of_nonneg_left hsp (inv_nonneg.mpr hpos.le)
      _ ≤ ((B j).card : ℝ)⁻¹ * (((B j).card : ℝ) * b) := by gcongr
      _ = b := by field_simp
  have hsum : ∑ i, e i ≤ (I.card : ℝ) * b := by
    simp only [he, meetNumber, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _j ∈ I, b := Finset.sum_le_sum hmeet
      _ = _ := by simp
  set c : ℝ := ∏ j ∈ I, recordedMean A G (B j) with hc
  have hc1 : 0 ≤ c := Finset.prod_nonneg fun j _ => le_trans zero_le_one (one_le_recordedMean hs _)
  have hprod0 : 0 ≤ ∏ i, (1 + e i) := Finset.prod_nonneg fun i _ => by linarith [he0 i]
  have hg1 : ∀ i s, 1 ≤ spinFactor A G I B i s := by
    intro i s
    unfold spinFactor
    exact (add_sum_le_mul_prod_one_add (a := 1) I _ (fun j _ => spinMean_nonneg hs i s (B j)) le_rfl).2
  have hga : ∀ i, spinFactor A G I B i (G.pairConstraint.vacant i) = 1 := by
    intro i
    unfold spinFactor
    refine Finset.prod_eq_one fun j _ => ?_
    have : ∑ y ∈ B j, spinSiteScore A G i y (G.pairConstraint.vacant i) = 0 := Finset.sum_eq_zero fun y _ => rfl
    rw [this]
    simp
  have hgm : ∀ i, Measurable (spinFactor A G I B i) := by
    intro i
    unfold spinFactor
    exact Finset.measurable_prod _ fun j _ =>
      ((Finset.measurable_sum _ fun y _ => measurable_spinSiteScore hb i y).const_mul _).const_add _
  set H : G.Config → ℝ := fun σ => ∏ j ∈ I, gasMeanSiteScore A G (B j) σ with hH
  have hH0 : ∀ σ, 0 ≤ H σ := fun σ => Finset.prod_nonneg fun j _ => meanSiteScore_nonneg' hs _ _ _
  have hHle : ∀ σ, H σ ≤ c * ∏ i, spinFactor A G I B i (σ i) := fun σ => prod_gasMeanSiteScore_le hs I B σ
  have hint : Integrable H (G.gibbsLaw ∅) := by
    have hae : H =ᵐ[G.gibbsLaw ∅] spinProduct A G I B :=
      (ae_isAdmissible_gibbsLaw hWt).mono fun σ hσ => prod_gasMeanSiteScore_eq I B hσ
    refine ⟨((measurable_spinProduct hb I B).aestronglyMeasurable).congr hae.symm, ?_⟩
    refine (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hH0)).mpr ?_
    have key := hP G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasure ∅) G.weight (G.spinActivity T.gasRate)
      hWt (spinFactor A G I B) e hgm hg1 hga he0 hexc
    have hlaw : G.gibbsLaw ∅ = G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight := rfl
    have e2 : ∫⁻ σ, ENNReal.ofReal (H σ) ∂(G.gibbsLaw ∅) ≤
        ∫⁻ σ, ENNReal.ofReal c * ∏ i, ENNReal.ofReal (spinFactor A G I B i (σ i)) ∂(G.gibbsLaw ∅) := by
      refine lintegral_mono fun σ => ?_
      have hg0 : ∀ i ∈ Finset.univ, 0 ≤ spinFactor A G I B i (σ i) := fun i _ => le_trans zero_le_one (hg1 i _)
      rw [← ENNReal.ofReal_prod_of_nonneg hg0, ← ENNReal.ofReal_mul hc1]
      exact ENNReal.ofReal_le_ofReal (hHle σ)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hlaw] at e2
    refine lt_of_le_of_lt (hlaw ▸ e2) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt key ENNReal.ofReal_lt_top)
  refine ⟨(hM y fM R A hK hTab n G hG₀ ι I B hB).1, hint, ?_⟩
  have hmain : G.expectation ∅ H ≤ c * ∏ i, (1 + e i) :=
    expectation_le_mul_prod hP hWt (spinFactor A G I B) e hgm hg1 hga he0 hexc hc1 hH0 hHle
  refine hmain.trans ?_
  have h7 : b ≤ Real.exp (-(7 * T.gasRate * R.coupling)) := by
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ T.gasRate * R.coupling := mul_nonneg hch.le (f0.trans hxy)
    linarith
  have hexp : ∏ i, (1 + e i) ≤ Real.exp ((I.card : ℝ) * Real.exp (-(7 * T.gasRate * R.coupling))) := by
    calc ∏ i, (1 + e i) ≤ ∏ i, Real.exp (e i) :=
          Finset.prod_le_prod (fun i _ => by linarith [he0 i]) fun i _ => by linarith [Real.add_one_le_exp (e i)]
      _ = Real.exp (∑ i, e i) := (Real.exp_sum _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (hsum.trans (mul_le_mul_of_nonneg_left h7 (Nat.cast_nonneg _)))
  have hstored : c ≤ ∏ i ∈ I,
      meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (parentBlocks (B i)) G.state.1 G.state.2 :=
    Finset.prod_le_prod (fun j _ => le_trans zero_le_one (one_le_recordedMean hs _))
      fun j hj => recordedMean_le_meanSiteScore hs hs₁ (B j) (hB j hj)
  calc c * ∏ i, (1 + e i) ≤ (∏ i ∈ I,
        meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (parentBlocks (B i)) G.state.1 G.state.2) *
        Real.exp ((I.card : ℝ) * Real.exp (-(7 * T.gasRate * R.coupling))) :=
        mul_le_mul hstored hexp hprod0 (hc1.trans hstored)
    _ = _ := mul_comm _ _
end FreeEnergies
end YangMills.Construction
end
