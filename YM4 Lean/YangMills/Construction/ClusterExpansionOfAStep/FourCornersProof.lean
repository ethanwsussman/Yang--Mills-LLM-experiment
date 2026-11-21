import YangMills.Construction.ClusterExpansionOfAStep.MatchingClasses
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsOfATorusProof
import YangMills.Construction.ClusterExpansionOfAStep.AdmissionReadsVOnItsHullProof
import YangMills.Construction.ClusterExpansionOfAStep.FourCorners
import YangMills.Construction.ClusterExpansionOfAStep.SharesAddToTheAction
import YangMills.Construction.ClusterExpansionOfAStep.SumsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep.FourCornerProof
open ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters StepSettings StepCosts ColdChain
open BlockAverages hiding unitStep wilsonAction
open LumpContours hiding plaquetteEnergy
def decaySumBound (δ : ℝ) : ℝ := (2 / (1 - Real.exp (-(δ / 3) / 4))) ^ 4
theorem decaySumBound_nonneg (δ : ℝ) : 0 ≤ decaySumBound δ := by
  unfold decaySumBound
  positivity
def lumpReadRadius : ℕ := 2 ^ 12 + 2 ^ 15 + 5
section Sums
variable {n : ℕ} [NeZero n]
theorem sum_abs_le_of_far_from_one (P P' : Finset (TorusSite n)) (hP : P.Nonempty) (hP' : P'.Nonempty) (d g m₀ : ℕ)
    (hd : ∀ z ∈ P, ∀ z' ∈ P', d ≤ _root_.YangMills.Construction.TorusFields.supDist z z') (hdm : 2 * (m₀ + g) ≤ d) (E : TorusSite n → ℝ) (K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 < δ)
    (H : ∀ (y : TorusSite n) (m : ℕ), m₀ ≤ m →
      ((∀ z ∈ P, m + g ≤ _root_.YangMills.Construction.TorusFields.supDist y z) ∨ (∀ z ∈ P', m + g ≤ _root_.YangMills.Construction.TorusFields.supDist y z)) → |E y| ≤ K * Real.exp (-δ * m)) :
    ∑ y, |E y| ≤ K * Real.exp (δ * g) * decaySumBound δ * P.card * Real.exp (-(δ * d / 3)) := by
  classical
  set B : ℝ := Real.exp (-(δ * d / 3)) with hB
  have hy : ∀ y, |E y| ≤ K * Real.exp (δ * g) * B * ∑ z ∈ P, Real.exp (-(δ / 3) * _root_.YangMills.Construction.TorusFields.supDist y z) := by
    intro y
    obtain ⟨z, hz, hza⟩ := Finset.exists_mem_eq_inf' hP (fun z => _root_.YangMills.Construction.TorusFields.supDist y z)
    obtain ⟨z', hz', hzb⟩ := Finset.exists_mem_eq_inf' hP' (fun z => _root_.YangMills.Construction.TorusFields.supDist y z)
    have hla : ∀ u ∈ P, _root_.YangMills.Construction.TorusFields.supDist y z ≤ _root_.YangMills.Construction.TorusFields.supDist y u := fun u hu => by
      rw [← hza]
      exact Finset.inf'_le (fun z => _root_.YangMills.Construction.TorusFields.supDist y z) hu
    have hlb : ∀ u ∈ P', _root_.YangMills.Construction.TorusFields.supDist y z' ≤ _root_.YangMills.Construction.TorusFields.supDist y u := fun u hu => by
      rw [← hzb]
      exact Finset.inf'_le (fun z => _root_.YangMills.Construction.TorusFields.supDist y z) hu
    have hab : d ≤ _root_.YangMills.Construction.TorusFields.supDist y z + _root_.YangMills.Construction.TorusFields.supDist y z' := by
      have h1 := hd z hz z' hz'
      have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle z y z'
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm z y] at h2
      omega
    obtain ⟨M, hMa, hMb, hMm⟩ : ∃ M, _root_.YangMills.Construction.TorusFields.supDist y z ≤ M ∧ _root_.YangMills.Construction.TorusFields.supDist y z' ≤ M ∧
        ((M = _root_.YangMills.Construction.TorusFields.supDist y z ∧ _root_.YangMills.Construction.TorusFields.supDist y z' ≤ _root_.YangMills.Construction.TorusFields.supDist y z) ∨ (M = _root_.YangMills.Construction.TorusFields.supDist y z' ∧ _root_.YangMills.Construction.TorusFields.supDist y z ≤ _root_.YangMills.Construction.TorusFields.supDist y z')) := by
      rcases le_total (_root_.YangMills.Construction.TorusFields.supDist y z) (_root_.YangMills.Construction.TorusFields.supDist y z') with h | h
      · exact ⟨_, h, le_rfl, Or.inr ⟨rfl, h⟩⟩
      · exact ⟨_, le_rfl, h, Or.inl ⟨rfl, h⟩⟩
    have hMg : m₀ + g ≤ M := by omega
    obtain ⟨m, hm⟩ : ∃ m, M = m + g := ⟨M - g, by omega⟩
    have hm₀ : m₀ ≤ m := by omega
    have hdisj : (∀ u ∈ P, m + g ≤ _root_.YangMills.Construction.TorusFields.supDist y u) ∨ (∀ u ∈ P', m + g ≤ _root_.YangMills.Construction.TorusFields.supDist y u) := by
      rcases hMm with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl fun u hu => by have := hla u hu; omega
      · exact Or.inr fun u hu => by have := hlb u hu; omega
    have h1 := H y m hm₀ hdisj
    have hnat : d + _root_.YangMills.Construction.TorusFields.supDist y z ≤ 3 * M := by omega
    have hreal : (d : ℝ) + _root_.YangMills.Construction.TorusFields.supDist y z ≤ 3 * ((m : ℝ) + g) := by
      have : ((d + _root_.YangMills.Construction.TorusFields.supDist y z : ℕ) : ℝ) ≤ ((3 * (m + g) : ℕ) : ℝ) := by
        rw [hm] at hnat
        exact_mod_cast hnat
      push_cast at this
      linarith
    have h2 : Real.exp (-δ * m) ≤ Real.exp (δ * g) * B * Real.exp (-(δ / 3) * _root_.YangMills.Construction.TorusFields.supDist y z) := by
      rw [hB, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have h3 : Real.exp (-(δ / 3) * _root_.YangMills.Construction.TorusFields.supDist y z) ≤ ∑ u ∈ P, Real.exp (-(δ / 3) * _root_.YangMills.Construction.TorusFields.supDist y u) :=
      Finset.single_le_sum (f := fun u => Real.exp (-(δ / 3) * _root_.YangMills.Construction.TorusFields.supDist y u))
        (fun _ _ => (Real.exp_pos _).le) hz
    have hKe : 0 ≤ K * (Real.exp (δ * g) * B) := by positivity
    calc |E y| ≤ K * Real.exp (-δ * m) := h1
      _ ≤ K * (Real.exp (δ * g) * B * Real.exp (-(δ / 3) * _root_.YangMills.Construction.TorusFields.supDist y z)) :=
          mul_le_mul_of_nonneg_left h2 hK
      _ = K * (Real.exp (δ * g) * B) * Real.exp (-(δ / 3) * _root_.YangMills.Construction.TorusFields.supDist y z) := by ring
      _ ≤ K * (Real.exp (δ * g) * B) * ∑ u ∈ P, Real.exp (-(δ / 3) * _root_.YangMills.Construction.TorusFields.supDist y u) :=
          mul_le_mul_of_nonneg_left h3 hKe
      _ = _ := by ring
  have hKB : 0 ≤ K * Real.exp (δ * g) * B := by positivity
  calc ∑ y, |E y| ≤ ∑ y, K * Real.exp (δ * g) * B * ∑ z ∈ P, Real.exp (-(δ / 3) * _root_.YangMills.Construction.TorusFields.supDist y z) :=
        Finset.sum_le_sum fun y _ => hy y
    _ = K * Real.exp (δ * g) * B * ∑ z ∈ P, ∑ y, Real.exp (-(δ / 3) * _root_.YangMills.Construction.TorusFields.supDist y z) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ K * Real.exp (δ * g) * B * ∑ _z ∈ P, decaySumBound δ :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun z _ => sum_exp_neg_mul_supDist_le (β := δ / 3) (by positivity) z) hKB
    _ = K * Real.exp (δ * g) * decaySumBound δ * P.card * B := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
theorem sum_abs_le_of_far_from_either (P P' : Finset (TorusSite n)) (hP : P.Nonempty) (hP' : P'.Nonempty)
    (d g m₀ : ℕ) (hd : ∀ z ∈ P, ∀ z' ∈ P', d ≤ _root_.YangMills.Construction.TorusFields.supDist z z') (hdm : 2 * (m₀ + g) ≤ d) (E : TorusSite n → ℝ)
    (K δ : ℝ) (hK : 0 ≤ K) (hδ : 0 < δ)
    (H : ∀ (y : TorusSite n) (m : ℕ), m₀ ≤ m →
      ((∀ z ∈ P, m + g ≤ _root_.YangMills.Construction.TorusFields.supDist y z) ∨ (∀ z ∈ P', m + g ≤ _root_.YangMills.Construction.TorusFields.supDist y z)) → |E y| ≤ K * Real.exp (-δ * m)) :
    ∑ y, |E y| ≤
      K * Real.exp (δ * g) * decaySumBound δ * min (P.card : ℝ) P'.card * Real.exp (-(δ * d / 3)) := by
  rcases le_total (P.card : ℝ) P'.card with h | h
  · rw [min_eq_left h]
    exact sum_abs_le_of_far_from_one P P' hP hP' d g m₀ hd hdm E K δ hK hδ H
  · rw [min_eq_right h]
    exact sum_abs_le_of_far_from_one P' P hP' hP d g m₀
      (fun z hz z' hz' => by rw [_root_.YangMills.Construction.TorusFields.supDist_comm]; exact hd z' hz' z hz) hdm E K δ hK hδ
      fun y m h1 h2 => H y m h1 h2.symm
theorem sum_count_eq_length {α : Type} [Fintype α] [DecidableEq α] (l : List α) :
    ∑ y : α, l.count y = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, Finset.sum_add_distrib, ih, List.length_cons]
    simp
theorem actionAtLevel_eq_sum_levelShare (hadd : SharesSumToAction) (a : ℝ) (ha : 0 ≤ a) (L : ℕ) (hL : 0 < L)
    (hn : 2 ≤ n) (t : ℕ) (S : Finset (TorusSite n)) (W : TorusField n) :
    actionAtLevel a L t S W = ∑ y : TorusSite n, levelShare a L t S y W := by
  classical
  symm
  cases t with
  | zero =>
    simp only [levelShare, actionAtLevel, wilsonAction]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [← Finset.sum_mul, ← Finset.sum_div, ← Nat.cast_sum, sum_count_eq_length]
    simp [plaquetteVertices]
  | succ t => exact hadd a L t n S W ha hL hn
end Sums
section Classes
variable {n : ℕ} [NeZero n]
theorem not_mem_of_disjoint_thickening {r : ℕ} {X A : Finset (TorusSite n)} (hn : ¬ (X ∩ thickening r A).Nonempty)
    {z : TorusSite n} (hz : z ∈ X) : z ∉ A := fun hA =>
  hn ⟨z, Finset.mem_inter.mpr ⟨hz, (mem_thickening _ _ _).mpr ⟨z, hA, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; exact Nat.zero_le _⟩⟩⟩
theorem mem_chainComponents_of_agree_off {r : ℕ} {Y Y' A : Finset (TorusSite n)}
    (hY : ∀ z, z ∉ A → (z ∈ Y ↔ z ∈ Y')) {X : Finset (TorusSite n)} (hX : X ∈ chainComponents r Y)
    (hn : ¬ (X ∩ thickening r A).Nonempty) : X ∈ chainComponents r Y' := by
  classical
  obtain ⟨y, hyY, hXe⟩ := mem_chainComponents.mp hX
  have hyX : y ∈ X := by
    rw [hXe]
    exact Finset.mem_filter.mpr ⟨hyY, Relation.ReflTransGen.refl⟩
  have hsub : X ⊆ Y := subset_of_mem_chainComponents hX
  have hYX : ∀ u ∈ X, u ∈ Y' := fun u hu => (hY u (not_mem_of_disjoint_thickening hn hu)).mp (hsub hu)
  refine mem_chainComponents.mpr ⟨y, hYX y hyX, ?_⟩
  ext z
  simp only [Finset.mem_filter]
  constructor
  · intro hz
    refine ⟨hYX z hz, ?_⟩
    have key : ∀ w, ChainConnected r Y y w → ChainConnected r Y' y w := by
      intro w hw
      unfold ChainConnected at hw
      induction hw with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c hab hbc ih =>
        have hbX : b ∈ X := mem_of_chainConnected_of_mem_chainComponents hX hyX hbc.1 hab
        have hcX : c ∈ X :=
          mem_of_chainConnected_of_mem_chainComponents hX hyX hbc.2.1 (Relation.ReflTransGen.tail hab hbc)
        exact Relation.ReflTransGen.tail ih ⟨hYX _ hbX, hYX _ hcX, hbc.2.2⟩
    exact key z (chainConnected_of_mem_chainComponents hX hyX hz)
  · rintro ⟨-, hj⟩
    have key : ∀ w, ChainConnected r Y' y w → w ∈ X := by
      intro w hw
      unfold ChainConnected at hw
      induction hw with
      | refl => exact hyX
      | @tail b c hab hbc ih =>
        have hcA : c ∉ A := fun hA =>
          hn ⟨b, Finset.mem_inter.mpr ⟨ih, (mem_thickening _ _ _).mpr ⟨c, hA, hbc.2.2⟩⟩⟩
        have hcY : c ∈ Y := (hY c hcA).mpr hbc.2.1
        exact mem_of_chainConnected_of_mem_chainComponents hX ih hcY
          (chainConnected_of_supDist_le (hsub ih) hcY hbc.2.2)
    exact key z hj
theorem prod_cross_eq {ι : Type} (C : Fin 2 → Fin 2 → Finset ι) (f : Fin 2 → Fin 2 → ι → ℝ) (NP NQ : ι → Prop)
    (hboth : ∀ i j, ∀ X ∈ C i j, ¬ (NP X ∧ NQ X))
    (hi : ∀ i i' j, ∀ X ∈ C i j, ¬ NP X → X ∈ C i' j ∧ f i j X = f i' j X)
    (hj : ∀ i j j', ∀ X ∈ C i j, ¬ NQ X → X ∈ C i j' ∧ f i j X = f i j' X) :
    (∏ X ∈ C 1 1, f 1 1 X) * (∏ X ∈ C 0 0, f 0 0 X) = (∏ X ∈ C 1 0, f 1 0 X) * ∏ X ∈ C 0 1, f 0 1 X := by
  classical
  have split : ∀ i j, ∏ X ∈ C i j, f i j X =
      (∏ X ∈ (C i j).filter NP, f i j X) * ∏ X ∈ (C i j).filter (fun X => ¬ NP X), f i j X :=
    fun i j => (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  have ha : ∀ i j j', ∏ X ∈ (C i j).filter NP, f i j X = ∏ X ∈ (C i j').filter NP, f i j' X := by
    intro i j j'
    refine Finset.prod_congr ?_ fun X hX => ?_
    · ext X
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(hj i j j' X h1 fun h3 => hboth i j X h1 ⟨h2, h3⟩).1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(hj i j' j X h1 fun h3 => hboth i j' X h1 ⟨h2, h3⟩).1, h2⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hX
      exact (hj i j' j X h1 fun h3 => hboth i j' X h1 ⟨h2, h3⟩).2.symm
  have hb : ∀ i i' j, ∏ X ∈ (C i j).filter (fun X => ¬ NP X), f i j X =
      ∏ X ∈ (C i' j).filter (fun X => ¬ NP X), f i' j X := by
    intro i i' j
    refine Finset.prod_congr ?_ fun X hX => ?_
    · ext X
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(hi i i' j X h1 h2).1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(hi i' i j X h1 h2).1, h2⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hX
      exact (hi i' i j X h1 h2).2.symm
  rw [split 1 1, split 0 0, split 1 0, split 0 1, ha 1 1 0, ha 0 0 1, hb 1 0 1, hb 0 1 0]
  ring
end Classes
section States
variable {n : ℕ} {Ω : Type} {P P' : Finset (TorusSite n)} {W : Fin 2 → Fin 2 → TorusField n}
  {Y : Fin 2 → Fin 2 → Finset (TorusSite n)} {ω : ∀ i j, Y i j → Ω}
theorem field_eq_of_not_mem_first (h : FourCornerStates P P' W Y ω) (i i' j : Fin 2) (b : TorusBond n)
    (h1 : b.1 ∉ P) (h2 : b.1 + unitStep n b.2 ∉ P) : W i j b.1 b.2 = W i' j b.1 b.2 := by
  by_cases hb : b.1 ∈ P' ∨ b.1 + unitStep n b.2 ∈ P'
  · exact h.field_second i i' j b hb
  · obtain ⟨hb1, hb2⟩ := not_or.mp hb
    exact h.field_rest i j i' j b (by simp [h1, hb1]) (by simp [h2, hb2])
theorem field_eq_of_not_mem_second (h : FourCornerStates P P' W Y ω) (i j j' : Fin 2) (b : TorusBond n)
    (h1 : b.1 ∉ P') (h2 : b.1 + unitStep n b.2 ∉ P') : W i j b.1 b.2 = W i j' b.1 b.2 := by
  by_cases hb : b.1 ∈ P ∨ b.1 + unitStep n b.2 ∈ P
  · exact h.field_first i j j' b hb
  · obtain ⟨hb1, hb2⟩ := not_or.mp hb
    exact h.field_rest i j i j' b (by simp [h1, hb1]) (by simp [h2, hb2])
theorem mem_iff_of_not_mem_first (h : FourCornerStates P P' W Y ω) (i i' j : Fin 2) (z : TorusSite n)
    (hz : z ∉ P) : z ∈ Y i j ↔ z ∈ Y i' j := by
  by_cases hb : z ∈ P'
  · exact h.set_second i i' j z hb
  · exact h.set_rest i j i' j z (by simp [hz, hb])
theorem mem_iff_of_not_mem_second (h : FourCornerStates P P' W Y ω) (i j j' : Fin 2) (z : TorusSite n)
    (hz : z ∉ P') : z ∈ Y i j ↔ z ∈ Y i j' := by
  by_cases hb : z ∈ P
  · exact h.set_first i j j' z hb
  · exact h.set_rest i j i j' z (by simp [hz, hb])
theorem label_eq_of_not_mem_first (h : FourCornerStates P P' W Y ω) (i i' j : Fin 2) (z : TorusSite n)
    (hz : z ∈ Y i j) (hz' : z ∈ Y i' j) (hzP : z ∉ P) : ω i j ⟨z, hz⟩ = ω i' j ⟨z, hz'⟩ := by
  by_cases hb : z ∈ P'
  · exact h.label_second i i' j z hz hz' hb
  · exact h.label_rest i j i' j z hz hz' (by simp [hzP, hb])
theorem label_eq_of_not_mem_second (h : FourCornerStates P P' W Y ω) (i j j' : Fin 2) (z : TorusSite n)
    (hz : z ∈ Y i j) (hz' : z ∈ Y i j') (hzP : z ∉ P') : ω i j ⟨z, hz⟩ = ω i j' ⟨z, hz'⟩ := by
  by_cases hb : z ∈ P
  · exact h.label_first i j j' z hz hz' hb
  · exact h.label_rest i j i j' z hz hz' (by simp [hzP, hb])
end States
section Hot
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
theorem two_mul_supDist_le (x y : TorusSite n) : 2 * _root_.YangMills.Construction.TorusFields.supDist x y ≤ n := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.two_mul_supDist_le <;> assumption
theorem natAbs_le_of_offsetInBox {m : ℕ} {h : Fin 4 → ℤ} (hb : OffsetInBox m h) (i : Fin 4) :
    (h i).natAbs ≤ m := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TorusOffsets.natAbs_le_of_withinRadius <;> assumption
omit [NeZero n] in
theorem holonomy_congr {W W' : TorusField n} {x : TorusSite n} {μ ν : Fin 4} {Q : Finset (TorusSite n)}
    (hW : ∀ b : TorusBond n, b.1 ∉ Q → b.1 + unitStep n b.2 ∉ Q → W b.1 b.2 = W' b.1 b.2)
    (hoff : ∀ c ∈ plaquetteVertices x μ ν, c ∉ Q) : holonomy W x μ ν = holonomy W' x μ ν := by
  have c1 : x ∉ Q := hoff _ (by simp [plaquetteVertices])
  have c2 : x + unitStep n μ ∉ Q := hoff _ (by simp [plaquetteVertices])
  have c3 : x + unitStep n ν ∉ Q := hoff _ (by simp [plaquetteVertices])
  have c4 : x + unitStep n μ + unitStep n ν ∉ Q := hoff _ (by simp [plaquetteVertices])
  have c4' : x + unitStep n ν + unitStep n μ ∉ Q := by rwa [add_right_comm]
  have e1 : W x μ = W' x μ := hW (x, μ) c1 c2
  have e2 : W (x + unitStep n μ) ν = W' (x + unitStep n μ) ν := hW (x + unitStep n μ, ν) c2 c4
  have e3 : W (x + unitStep n ν) μ = W' (x + unitStep n ν) μ := hW (x + unitStep n ν, μ) c3 c4'
  have e4 : W x ν = W' x ν := hW (x, ν) c1 c3
  unfold holonomy
  rw [e1, e2, e3, e4]
theorem mem_thickening_hotSites_of_far (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) {W W' : TorusField n}
    {Q : Finset (TorusSite n)}
    (hW : ∀ b : TorusBond n, b.1 ∉ Q → b.1 + unitStep n b.2 ∉ Q → W b.1 b.2 = W' b.1 b.2) {u : TorusSite n}
    (hu : ∀ z ∈ Q, lumpReadRadius ≤ _root_.YangMills.Construction.TorusFields.supDist u z) (hin : u ∈ thickening lumpRange (torusHotSites ℓ W)) :
    u ∈ thickening lumpRange (torusHotSites ℓ W') := by
  classical
  obtain ⟨v, hv, huv⟩ := (mem_thickening _ _ _).mp hin
  obtain ⟨l, hl, hvl⟩ := Finset.mem_biUnion.mp (show v ∈ (torusHotLumps ℓ W).biUnion id from hv)
  obtain ⟨x, μ, ν, hlt, hge, z₁, hz₁, rfl⟩ := (mem_torusHotLumps_iff ℓ hfit hLn W l).mp hl
  have hvz : _root_.YangMills.Construction.TorusFields.supDist v z₁ < 2 ^ 15 :=
    _root_.YangMills.Construction.TorusLumps.supDist_lt_of_mem_torusHotLumps hfit hLn hl hvl (mem_torusLumpOf_self _)
  have hoff : ∀ c ∈ plaquetteVertices x μ ν, c ∉ Q := by
    intro c hc hcQ
    have h1 := hu c hcQ
    have h2 : _root_.YangMills.Construction.TorusFields.supDist z₁ c ≤ 4 := _root_.YangMills.Construction.TorusLumps.supDist_le_four_of_mem_plaquetteVertices (x, μ, ν) hz₁ hc
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle u v c
    have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle v z₁ c
    have h5 : _root_.YangMills.Construction.TorusFields.supDist u v ≤ 2 ^ 12 := huv
    unfold lumpReadRadius at h1
    omega
  have hl' : torusLumpOf ℓ z₁ ∈ torusHotLumps ℓ W' :=
    (mem_torusHotLumps_iff ℓ hfit hLn W' _).mpr
      ⟨x, μ, ν, hlt, by rwa [curvature, ← holonomy_congr hW hoff], z₁, hz₁, rfl⟩
  have hv' : v ∈ (torusHotLumps ℓ W').biUnion id := Finset.mem_biUnion.mpr ⟨_, hl', hvl⟩
  exact (mem_thickening _ _ _).mpr ⟨v, hv', huv⟩
theorem add_siteOfInt_not_mem {Q : Finset (TorusSite n)} {y : TorusSite n} {m g : ℕ} (hg : 1 ≤ g)
    (hm : ∀ z ∈ Q, m + g ≤ _root_.YangMills.Construction.TorusFields.supDist y z) {h : Fin 4 → ℤ} (hb : OffsetInBox m h) : y + siteOfInt h ∉ Q :=
  fun hq => by
  have h1 := hm _ hq
  have h2 := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le y h m (natAbs_le_of_offsetInBox hb)
  omega
theorem bondFrom_end (y : TorusSite n) (b : (Fin 4 → ℤ) × Fin 4) :
    (bondFrom y b).1 + unitStep n (bondFrom y b).2 = y + siteOfInt (b.1 + Pi.single b.2 1) := by apply _root_.YangMills.Construction.TorusLumps.bondFrom_fst_add_unitStep <;> assumption
theorem fieldsAgreeNear_of_far {W W' : TorusField n} {Q : Finset (TorusSite n)}
    (hW : ∀ b : TorusBond n, b.1 ∉ Q → b.1 + unitStep n b.2 ∉ Q → W b.1 b.2 = W' b.1 b.2) {y : TorusSite n}
    {m g : ℕ} (hg : 1 ≤ g) (hm : ∀ z ∈ Q, m + g ≤ _root_.YangMills.Construction.TorusFields.supDist y z) : FieldsAgreeNear W W' y y m := by
  intro b hb
  exact hW (bondFrom y b) (add_siteOfInt_not_mem hg hm hb.1)
    (by rw [bondFrom_end]; exact add_siteOfInt_not_mem hg hm hb.2)
theorem regions_agree_of_far (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) {W W' : TorusField n}
    {Q : Finset (TorusSite n)} (hQ : Q.Nonempty)
    (hW : ∀ b : TorusBond n, b.1 ∉ Q → b.1 + unitStep n b.2 ∉ Q → W b.1 b.2 = W' b.1 b.2) {y : TorusSite n}
    {m : ℕ} (hm : ∀ z ∈ Q, m + lumpReadRadius ≤ _root_.YangMills.Construction.TorusFields.supDist y z) :
    2 * m + 2 < n ∧ (∀ h, OffsetInBox m h →
      (y + siteOfInt h ∈ Finset.univ \ thickening lumpRange (torusHotSites ℓ W) ↔
        y + siteOfInt h ∈ Finset.univ \ thickening lumpRange (torusHotSites ℓ W'))) ∧
      FieldsAgreeNear W W' y y m := by
  classical
  obtain ⟨z, hz⟩ := hQ
  have hg : 1 ≤ lumpReadRadius := by norm_num [lumpReadRadius]
  have hside : 2 * m + 2 < n := by
    have h1 := hm z hz
    have h2 := two_mul_supDist_le y z
    have h3 : 2 ≤ lumpReadRadius := by norm_num [lumpReadRadius]
    omega
  refine ⟨hside, fun h hb => ?_, fieldsAgreeNear_of_far hW hg hm⟩
  have hu : ∀ z ∈ Q, lumpReadRadius ≤ _root_.YangMills.Construction.TorusFields.supDist (y + siteOfInt h) z := by
    intro z hz
    have h1 := hm z hz
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le y h m (natAbs_le_of_offsetInBox hb)
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle y (y + siteOfInt h) z
    omega
  have hW' : ∀ b : TorusBond n, b.1 ∉ Q → b.1 + unitStep n b.2 ∉ Q → W' b.1 b.2 = W b.1 b.2 :=
    fun b h1 h2 => (hW b h1 h2).symm
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact not_congr ⟨mem_thickening_hotSites_of_far hfit hLn hW hu, mem_thickening_hotSites_of_far hfit hLn hW' hu⟩
end Hot
section Shares
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
theorem levelShare_succ_diff_le {δ lam ρ σA cg : ℝ} {N : ℕ → ℝ}
    (hch : ColdChainConstants ℓ.coupling δ ℓ.side lam ρ σA cg N)
    (hreg : ComplementOfThickenedLumpsRegular) (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (hn64 : 64 ≤ n)
    (hσ : ℓ.threshold ≤ σA) (t : ℕ) {W W' : TorusField n} {y : TorusSite n} {m : ℕ} (hside : 2 * m + 2 < n)
    (hbox : ∀ h, OffsetInBox m h →
      (y + siteOfInt h ∈ Finset.univ \ thickening lumpRange (torusHotSites ℓ W) ↔
        y + siteOfInt h ∈ Finset.univ \ thickening lumpRange (torusHotSites ℓ W')))
    (hf : FieldsAgreeNear W W' y y m) :
    |levelShare ℓ.coupling ℓ.side (t + 1) (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) y W -
        levelShare ℓ.coupling ℓ.side (t + 1) (Finset.univ \ thickening lumpRange (torusHotSites ℓ W')) y W'| ≤
      σA ^ 2 * N 0 * Real.exp (-δ * m) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hN, main⟩ := hch
  have hσp := hfit.σ_pos
  have hn : ∀ i, (torusFrame ℓ.side t n).extent i = n := fun _ => rfl
  have hp := TopLevelSites.period_top_of_extent (F := torusFrame ℓ.side t n) hn
  have hamb : IsAdmissibleAmbient (torusFrame ℓ.side t n) := Or.inr fun i => by rw [hn]; exact hn64
  have h := main (torusFrame ℓ.side t n) 2047 _ rfl hamb (by norm_num)
    (TopLevelSites.isOrthantRegular_cellsOfSites_compl_thickening hreg hfit hLn hn W) ℓ.threshold
    (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top W) hσp hσ
    (TopLevelSites.isCold_cellsOfSites_compl_thickening hfit hLn hn W)
  obtain ⟨-, -, -, -, -, h6⟩ := h
  have hag : AgreeOnBall
      (cellsOfSites (torusFrame ℓ.side t n) (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)))
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top W)
      (cellsOfSites (torusFrame ℓ.side t n) (Finset.univ \ thickening lumpRange (torusHotSites ℓ W')))
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top W')
      (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top y)
      (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top y) m := by
    refine ⟨fun i => Or.inr hside, fun i => Or.inr hside, fun e he => ?_, fun b hb => ?_⟩
    · rw [TopLevelSites.mem_cellsOfSites_iff hn, TopLevelSites.mem_cellsOfSites_iff hn,
        TopLevelSites.toTorusSite_add hp, TopLevelSites.toTorusSite_torusSiteInFrame hp,
        TopLevelSites.toTorusSite_siteOfCoords hp]
      exact hbox e he
    · have e : ∀ U : TorusField n, readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top U
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top y +
            siteOfCoords (torusFrame ℓ.side t n).top b.1) b.2 =
          U (y + siteOfInt b.1) b.2 := by
        intro U
        show U (toTorusSite n _) b.2 = _
        rw [TopLevelSites.toTorusSite_add hp, TopLevelSites.toTorusSite_torusSiteInFrame hp,
          TopLevelSites.toTorusSite_siteOfCoords hp]
      rw [e, e]
      exact hf b hb
  have h7 := (h6 (torusFrame ℓ.side t n) _ (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top W')
    _ _ m rfl rfl hamb (TopLevelSites.isOrthantRegular_cellsOfSites_compl_thickening hreg hfit hLn hn W')
    (TopLevelSites.isCold_cellsOfSites_compl_thickening hfit hLn hn W') hag).1
  have h8 := h7 0 Fin.elim0 Fin.elim0 (fun l => l.elim0) (fun l => l.elim0)
  have e0 : ∀ (S : Finset (torusFrame ℓ.side t n).Cell)
      (V : (torusFrame ℓ.side t n).GaugeField (torusFrame ℓ.side t n).top) (Y : (torusFrame ℓ.side t n).Cell),
      mixedBondDerivative (minimalCellShare ℓ.coupling S Y) V (offsetBonds Y (Fin.elim0 : Fin 0 → _))
        (Fin.elim0 : Fin 0 → imaginaryQuaternions) = minimalCellShare ℓ.coupling S Y V := by
    intro S V Y
    unfold mixedBondDerivative
    rw [iteratedFDeriv_zero_apply]
    congr 1
    funext z i
    have : NormedSpace.exp ((0 : imaginaryQuaternions) : ℍ[ℝ]) = 1 := by simp
    simp [rotatedField, BlockAverages.bondSpread]
    apply Subtype.ext
    simp [expUnit]
  rw [e0, e0] at h8
  have hfac : derivativeScale ℓ.threshold 0 = ℓ.threshold ^ 2 := by simp [derivativeScale]
  rw [hfac] at h8
  refine (show _ ≤ _ from h8).trans ?_
  have h2 : ℓ.threshold ^ 2 ≤ σA ^ 2 := by nlinarith
  have h3 := hN 0
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 h3.le) (Real.exp_pos _).le
theorem levelShare_zero_eq (a : ℝ) (L : ℕ) {X X' : Finset (TorusSite n)} {W W' : TorusField n}
    {Q : Finset (TorusSite n)} {y : TorusSite n}
    (hW : ∀ b : TorusBond n, b.1 ∉ Q → b.1 + unitStep n b.2 ∉ Q → W b.1 b.2 = W' b.1 b.2)
    (hq : ∀ z ∈ Q, 5 ≤ _root_.YangMills.Construction.TorusFields.supDist y z) (hX : ∀ c, _root_.YangMills.Construction.TorusFields.supDist y c ≤ 4 → (c ∈ X ↔ c ∈ X')) :
    levelShare a L 0 X y W = levelShare a L 0 X' y W' := by
  classical
  simp only [levelShare]
  have red : ∀ (S : Finset (TorusSite n)) (U : TorusField n),
      ∑ p ∈ plaquettesIn S, (((plaquetteVertices p.1 p.2.1 p.2.2).count y : ℕ) : ℝ) / 4 *
          plaquetteEnergy U p.1 p.2.1 p.2.2 =
      ∑ p ∈ (plaquettesIn S).filter (fun p => y ∈ plaquetteVertices p.1 p.2.1 p.2.2),
        (((plaquetteVertices p.1 p.2.1 p.2.2).count y : ℕ) : ℝ) / 4 * plaquetteEnergy U p.1 p.2.1 p.2.2 := by
    intro S U
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with h
    · rfl
    · rw [List.count_eq_zero_of_not_mem h]
      simp
  rw [red, red]
  have hclose : ∀ p : TorusPlaquette n, y ∈ plaquetteVertices p.1 p.2.1 p.2.2 →
      ∀ c ∈ plaquetteVertices p.1 p.2.1 p.2.2, _root_.YangMills.Construction.TorusFields.supDist y c ≤ 4 :=
    fun p hy c hc => _root_.YangMills.Construction.TorusLumps.supDist_le_four_of_mem_plaquetteVertices p hy hc
  refine Finset.sum_congr ?_ fun p hp => ?_
  · ext p
    simp only [Finset.mem_filter, mem_plaquettesIn_iff_forall_vertex]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, fun c hc => (hX c (hclose p h3 c hc)).mp (h2 c hc)⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, fun c hc => (hX c (hclose p h3 c hc)).mpr (h2 c hc)⟩, h3⟩
  · have hy := (Finset.mem_filter.mp hp).2
    have hoff : ∀ c ∈ plaquetteVertices p.1 p.2.1 p.2.2, c ∉ Q := fun c hc hcQ => by
      have h1 := hq c hcQ
      have h2 := hclose p hy c hc
      omega
    unfold plaquetteEnergy
    rw [holonomy_congr hW hoff]
theorem levelShare_diff_le {δ lam ρ σA cg : ℝ} {N : ℕ → ℝ}
    (hch : ColdChainConstants ℓ.coupling δ ℓ.side lam ρ σA cg N)
    (hreg : ComplementOfThickenedLumpsRegular) (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (hn64 : 64 ≤ n)
    (hσ : ℓ.threshold ≤ σA) (t : ℕ) {W W' : TorusField n} {Q : Finset (TorusSite n)} (hQ : Q.Nonempty)
    (hW : ∀ b : TorusBond n, b.1 ∉ Q → b.1 + unitStep n b.2 ∉ Q → W b.1 b.2 = W' b.1 b.2) {y : TorusSite n}
    {m : ℕ} (hm : ∀ z ∈ Q, m + (lumpReadRadius + 4) ≤ _root_.YangMills.Construction.TorusFields.supDist y z) :
    |levelShare ℓ.coupling ℓ.side t (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) y W -
        levelShare ℓ.coupling ℓ.side t (Finset.univ \ thickening lumpRange (torusHotSites ℓ W')) y W'| ≤
      σA ^ 2 * N 0 * Real.exp (-δ * m) := by
  classical
  have hgap : lumpReadRadius = 36869 := by norm_num [lumpReadRadius]
  cases t with
  | succ t =>
    obtain ⟨hside, hbox, hf⟩ := regions_agree_of_far hfit hLn hQ hW
      (y := y) (m := m) fun z hz => by have := hm z hz; omega
    exact levelShare_succ_diff_le hch hreg hfit hLn hn64 hσ t hside hbox hf
  | zero =>
    have hW' : ∀ b : TorusBond n, b.1 ∉ Q → b.1 + unitStep n b.2 ∉ Q → W' b.1 b.2 = W b.1 b.2 :=
      fun b h1 h2 => (hW b h1 h2).symm
    have e := levelShare_zero_eq ℓ.coupling ℓ.side
      (X := Finset.univ \ thickening lumpRange (torusHotSites ℓ W))
      (X' := Finset.univ \ thickening lumpRange (torusHotSites ℓ W')) (y := y) hW
      (fun z hz => by have := hm z hz; omega) (fun c hc => by
        have hu : ∀ z ∈ Q, lumpReadRadius ≤ _root_.YangMills.Construction.TorusFields.supDist c z := fun z hz => by
          have h1 := hm z hz
          have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle y c z
          omega
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact not_congr ⟨mem_thickening_hotSites_of_far hfit hLn hW hu,
          mem_thickening_hotSites_of_far hfit hLn hW' hu⟩)
    rw [e, sub_self, abs_zero]
    obtain ⟨-, -, -, -, -, -, -, hN, -⟩ := hch
    have := hN 0
    positivity
end Shares
section Reals
theorem abs_cross_diff_le_of_first (s : Fin 2 → Fin 2 → ℝ) (A e : ℝ) (h : ∀ j, |s 1 j - s 0 j| ≤ A * e) :
    |s 1 1 + s 0 0 - s 1 0 - s 0 1| ≤ 2 * A * e := by
  have h1 := abs_le.mp (h 1)
  have h0 := abs_le.mp (h 0)
  exact abs_le.mpr ⟨by linarith [h1.1, h0.2], by linarith [h1.2, h0.1]⟩
theorem abs_cross_diff_le_of_second (s : Fin 2 → Fin 2 → ℝ) (A e : ℝ) (h : ∀ i, |s i 1 - s i 0| ≤ A * e) :
    |s 1 1 + s 0 0 - s 1 0 - s 0 1| ≤ 2 * A * e := by
  have h1 := abs_le.mp (h 1)
  have h0 := abs_le.mp (h 0)
  exact abs_le.mpr ⟨by linarith [h1.1, h0.2], by linarith [h1.2, h0.1]⟩
theorem log_cross_ratio_eq (c : ℝ) (hc : 0 < c) (u p D : Fin 2 → Fin 2 → ℝ)
    (hD : ∀ i j, D i j = c * Real.exp (u i j) * p i j) (hp : ∀ i j, 0 ≤ p i j)
    (hprod : p 1 1 * p 0 0 = p 1 0 * p 0 1) :
    (0 < D 1 1 * D 0 0 ↔ 0 < D 1 0 * D 0 1) ∧
      (0 < D 1 1 * D 0 0 → (∀ i j, 0 < p i j) ∧
        Real.log (D 1 1 * D 0 0 / (D 1 0 * D 0 1)) = u 1 1 + u 0 0 - u 1 0 - u 0 1) := by
  have e1 : D 1 1 * D 0 0 = (c ^ 2 * Real.exp (u 1 1 + u 0 0)) * (p 1 1 * p 0 0) := by
    rw [hD, hD, Real.exp_add]
    ring
  have e2 : D 1 0 * D 0 1 = (c ^ 2 * Real.exp (u 1 0 + u 0 1)) * (p 1 1 * p 0 0) := by
    rw [hprod, hD, hD, Real.exp_add]
    ring
  have k1 : 0 < c ^ 2 * Real.exp (u 1 1 + u 0 0) := by positivity
  have k2 : 0 < c ^ 2 * Real.exp (u 1 0 + u 0 1) := by positivity
  refine ⟨?_, fun hpos => ?_⟩
  · rw [e1, e2]
    exact (mul_pos_iff_of_pos_left k1).trans (mul_pos_iff_of_pos_left k2).symm
  · have q : 0 < p 1 1 * p 0 0 := by
      rw [e1] at hpos
      exact (mul_pos_iff_of_pos_left k1).mp hpos
    have q' : 0 < p 1 0 * p 0 1 := hprod ▸ q
    have h11 : 0 < p 1 1 := lt_of_le_of_ne (hp 1 1) fun e => by rw [← e] at q; simp at q
    have h00 : 0 < p 0 0 := lt_of_le_of_ne (hp 0 0) fun e => by rw [← e] at q; simp at q
    have h10 : 0 < p 1 0 := lt_of_le_of_ne (hp 1 0) fun e => by rw [← e] at q'; simp at q'
    have h01 : 0 < p 0 1 := lt_of_le_of_ne (hp 0 1) fun e => by rw [← e] at q'; simp at q'
    refine ⟨Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨h00, h01⟩, Fin.forall_fin_two.mpr ⟨h10, h11⟩⟩, ?_⟩
    have e3 : D 1 1 * D 0 0 / (D 1 0 * D 0 1) = Real.exp (u 1 1 + u 0 0 - (u 1 0 + u 0 1)) := by
      rw [e1, e2, Real.exp_sub]
      have he := (Real.exp_pos (u 1 0 + u 0 1)).ne'
      have hc' := hc.ne'
      field_simp
    rw [e3, Real.log_exp]
    ring
theorem log_cross_ratio_eq_zero_of_first (D : Fin 2 → Fin 2 → ℝ) (h : ∀ j, D 1 j = D 0 j)
    (hpos : 0 < D 1 1 * D 0 0) : Real.log (D 1 1 * D 0 0 / (D 1 0 * D 0 1)) = 0 := by
  have e : D 1 1 * D 0 0 / (D 1 0 * D 0 1) = 1 := by
    have hq : 0 < D 0 1 * D 0 0 := by rwa [h 1] at hpos
    rw [h 0, h 1, mul_comm (D 0 0)]
    exact div_self hq.ne'
  rw [e, Real.log_one]
theorem log_cross_ratio_eq_zero_of_second (D : Fin 2 → Fin 2 → ℝ) (h : ∀ i, D i 1 = D i 0)
    (hpos : 0 < D 1 1 * D 0 0) : Real.log (D 1 1 * D 0 0 / (D 1 0 * D 0 1)) = 0 := by
  have e : D 1 1 * D 0 0 / (D 1 0 * D 0 1) = 1 := by
    have hq : 0 < D 1 0 * D 0 0 := by rwa [h 1] at hpos
    rw [h 1, h 0]
    exact div_self hq.ne'
  rw [e, Real.log_one]
theorem cross_sum_eq {ι : Type} [Fintype ι] (x : ℝ) (a q : Fin 2 → Fin 2 → ι → ℝ) :
    (-x * ∑ y, a 1 1 y + ∑ y, q 1 1 y) + (-x * ∑ y, a 0 0 y + ∑ y, q 0 0 y) -
        (-x * ∑ y, a 1 0 y + ∑ y, q 1 0 y) - (-x * ∑ y, a 0 1 y + ∑ y, q 0 1 y) =
      -x * ∑ y, (a 1 1 y + a 0 0 y - a 1 0 y - a 0 1 y) + ∑ y, (q 1 1 y + q 0 0 y - q 1 0 y - q 0 1 y) := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring
theorem two_sums_le {x Mn Ef E1 a1 a2 C SA Sq : ℝ} (hx : 1 ≤ x) (hMn : 0 ≤ Mn) (hEf : 0 ≤ Ef) (h1 : E1 ≤ Ef)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hC : a1 + a2 ≤ C) (hSA : SA ≤ a1 * Mn * E1) (hSq : Sq ≤ a2 * Mn * Ef) :
    x * SA + Sq ≤ C * x * Mn * Ef := by
  have hx0 : 0 ≤ x := by linarith
  have p1 : a1 * Mn * E1 ≤ a1 * Mn * Ef := mul_le_mul_of_nonneg_left h1 (mul_nonneg ha1 hMn)
  have p2 : x * SA ≤ x * (a1 * Mn * Ef) := mul_le_mul_of_nonneg_left (hSA.trans p1) hx0
  have p3 : 0 ≤ a2 * Mn * Ef := mul_nonneg (mul_nonneg ha2 hMn) hEf
  have p4 : a2 * Mn * Ef ≤ x * (a2 * Mn * Ef) := le_mul_of_one_le_left p3 hx
  have p5 : (a1 + a2) * (x * Mn * Ef) ≤ C * (x * Mn * Ef) :=
    mul_le_mul_of_nonneg_right hC (mul_nonneg (mul_nonneg hx0 hMn) hEf)
  nlinarith
theorem le_clusterRange_of_le {x : ℝ} (hx : (2 : ℝ) ^ 2200 ≤ x) : 4194304 ≤ clusterRange x := by
  have e : ((2 : ℝ) ^ (2200 : ℕ)) ^ ((1 : ℝ) / 100) = (2 : ℝ) ^ (22 : ℕ) := by
    have e1 : (2 : ℝ) ^ (2200 : ℕ) = ((2 : ℝ) ^ (22 : ℕ)) ^ (100 : ℕ) := by
      rw [← pow_mul]
    rw [e1, ← Real.rpow_natCast ((2 : ℝ) ^ (22 : ℕ)) 100, ← Real.rpow_mul (by positivity)]
    norm_num
  have h1 : (2 : ℝ) ^ (22 : ℕ) ≤ x ^ ((1 : ℝ) / 100) := by
    rw [← e]
    exact Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have h2 : x ^ ((1 : ℝ) / 100) ≤ clusterRange x := Nat.le_ceil _
  have h3 := h1.trans h2
  norm_num at h3
  exact_mod_cast h3
theorem labelWeight_congr {Ω : Type} {n : ℕ}
    (G : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Ω) → ℝ)
    {W W' : TorusField n} {Y Y' : Finset (TorusSite n)} {ω : Y → Ω} {ω' : Y' → Ω} (hW : W = W') (hY : Y = Y')
    (hω : ∀ z (hz : z ∈ Y) (hz' : z ∈ Y'), ω ⟨z, hz⟩ = ω' ⟨z, hz'⟩) : G n W Y ω = G n W' Y' ω' := by
  subst hW hY
  congr 1
  funext z
  exact hω z.1 z.2 z.2
end Reals
section Core
variable {ℓ : StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional} {f : LocalDensity} {Λ : LabelSpace}
  {Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
  {Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ}
  {φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
  {n : ℕ} [NeZero n]
theorem siteDensity_diff_le (hull : HullExpansion ℓ t x D f Λ Dq Φ φ) (hb : IsBlockTorusSide ℓ n)
    {W W' : TorusField n} {Y Y' : Finset (TorusSite n)} {ω : Y → Λ.Ω} {ω' : Y' → Λ.Ω}
    {Q : Finset (TorusSite n)} (hQ : Q.Nonempty)
    (hh : IsHullState ℓ (clusterRange x) W Y) (hh' : IsHullState ℓ (clusterRange x) W' Y')
    (hnz : ∀ X ∈ chainComponents (clusterRange x) Y, Φ n W Y ω X ≠ 0)
    (hnz' : ∀ X ∈ chainComponents (clusterRange x) Y', Φ n W' Y' ω' X ≠ 0)
    (hW : ∀ b : TorusBond n, b.1 ∉ Q → b.1 + unitStep n b.2 ∉ Q → W b.1 b.2 = W' b.1 b.2)
    (hY : ∀ z, z ∉ Q → (z ∈ Y ↔ z ∈ Y'))
    (hω : ∀ z (hz : z ∈ Y) (hz' : z ∈ Y'), z ∉ Q → ω ⟨z, hz⟩ = ω' ⟨z, hz'⟩) {y : TorusSite n} {m : ℕ}
    (hm : ∀ z ∈ Q, m + 2 ≤ _root_.YangMills.Construction.TorusFields.supDist y z) (hr : (clusterRange x : ℝ) / 64 ≤ m) :
    |φ n y W Y ω - φ n y W' Y' ω'| ≤ 1 * Real.exp (-ℓ.decayRate * m) := by
  obtain ⟨z, hz⟩ := hQ
  have hside : 2 * m + 2 < n := by
    have h1 := hm z hz
    have h2 := two_mul_supDist_le y z
    omega
  rw [one_mul]
  exact hull.forget n n hb hb W W' Y Y' ω ω' y y m hh hh' hnz hnz' hr
    ⟨hside, hside, fieldsAgreeNear_of_far hW (by norm_num) hm,
      fun h hbx => hY _ (add_siteOfInt_not_mem (by norm_num) hm hbx),
      fun h hbx hz hz' _ => hω _ hz hz' (add_siteOfInt_not_mem (by norm_num) hm hbx), fun _ i => by simp⟩
theorem log_cross_ratio_le (hadd : SharesSumToAction) (hreg : ComplementOfThickenedLumpsRegular)
    (hfit : ℓ.Admissible) (hcold : ColdExpansion ℓ t x D f) (hull : HullExpansion ℓ t x D f Λ Dq Φ φ)
    {δ₁ lam ρ σA cg C : ℝ} {N : ℕ → ℝ}
    (hδ₁ : 0 < δ₁) (hfp : 0 < ℓ.decayRate) (hfl : ℓ.decayRate ≤ δ₁)
    (hch : ColdChainConstants ℓ.coupling δ₁ ℓ.side lam ρ σA cg N) (hs₀ : ℓ.threshold ≤ σA)
    (hC : 2 * (σA ^ 2 * N 0) * Real.exp (δ₁ * ((lumpReadRadius + 4 : ℕ) : ℝ)) * decaySumBound δ₁ +
      2 * 1 * Real.exp (ℓ.decayRate * ((2 : ℕ) : ℝ)) * decaySumBound ℓ.decayRate ≤ C)
    (hx : 1 ≤ x) (hr : 4194304 ≤ clusterRange x) (hb : IsBlockTorusSide ℓ n) (P P' : Finset (TorusSite n))
    (W : Fin 2 → Fin 2 → TorusField n) (Y : Fin 2 → Fin 2 → Finset (TorusSite n)) (ω : ∀ i j, Y i j → Λ.Ω)
    (d : ℕ) (hfs : FourCornerStates P P' W Y ω) (hhull : ∀ i j, IsHullState ℓ (clusterRange x) (W i j) (Y i j))
    (hd : ∀ z ∈ P, ∀ z' ∈ P', d ≤ _root_.YangMills.Construction.TorusFields.supDist z z') (hrd : (clusterRange x : ℝ) / 16 ≤ d)
    (hcl : ∀ i j, ∀ X ∈ chainComponents (clusterRange x) (Y i j),
      ¬ ((X ∩ thickening (clusterRange x) P).Nonempty ∧ (X ∩ thickening (clusterRange x) P').Nonempty)) :
    let prodΦ := fun i j => ∏ X ∈ chainComponents (clusterRange x) (Y i j), Φ n (W i j) (Y i j) (ω i j) X
    let Dij := fun i j => Dq n (W i j) (Y i j) (ω i j)
    prodΦ 1 1 * prodΦ 0 0 = prodΦ 1 0 * prodΦ 0 1 ∧
    (0 < Dij 1 1 * Dij 0 0 ↔ 0 < Dij 1 0 * Dij 0 1) ∧
    (0 < Dij 1 1 * Dij 0 0 →
      |Real.log (Dij 1 1 * Dij 0 0 / (Dij 1 0 * Dij 0 1))| ≤
        C * x * min (P.card : ℝ) P'.card * Real.exp (-(ℓ.decayRate * d / 3))) := by
  intro prodΦ Dij
  have hLn : ℓ.side ∣ n := hb.1
  have hLge := hfit.L_ge
  have hLpos : 0 < ℓ.side := by omega
  have hn₀ : ℓ.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hLpos) hb.2
  have hn64 : 64 ≤ n := by
    have := hfit.n₀_ge
    omega
  have hσ := hfit.σ_pos
  have hflat : 0 < D n (trivialField n) := hcold.positive n hn₀ (trivialField n) fun x μ ν _ => by
    have : curvature (trivialField n) x μ ν = 0 := by simp [curvature, holonomy_trivialField]
    rw [this]
    exact hσ
  have hprod : prodΦ 1 1 * prodΦ 0 0 = prodΦ 1 0 * prodΦ 0 1 := by
    refine prod_cross_eq (fun i j => chainComponents (clusterRange x) (Y i j))
      (fun i j X => Φ n (W i j) (Y i j) (ω i j) X)
      (fun X => (X ∩ thickening (clusterRange x) P).Nonempty)
      (fun X => (X ∩ thickening (clusterRange x) P').Nonempty) hcl ?_ ?_
    · intro i i' j X hX hnp
      have hX' := mem_chainComponents_of_agree_off (fun z hz => mem_iff_of_not_mem_first hfs i i' j z hz) hX hnp
      exact ⟨hX', hull.reads_class n hb _ _ _ _ _ _ X (subset_of_mem_chainComponents hX)
        (subset_of_mem_chainComponents hX')
        (fun b h1 h2 => field_eq_of_not_mem_first hfs i i' j b (not_mem_of_disjoint_thickening hnp h1)
          (not_mem_of_disjoint_thickening hnp h2))
        (fun z hz hz' hzX => label_eq_of_not_mem_first hfs i i' j z hz hz' (not_mem_of_disjoint_thickening hnp hzX))⟩
    · intro i j j' X hX hnp
      have hX' := mem_chainComponents_of_agree_off (fun z hz => mem_iff_of_not_mem_second hfs i j j' z hz) hX hnp
      exact ⟨hX', hull.reads_class n hb _ _ _ _ _ _ X (subset_of_mem_chainComponents hX)
        (subset_of_mem_chainComponents hX')
        (fun b h1 h2 => field_eq_of_not_mem_second hfs i j j' b (not_mem_of_disjoint_thickening hnp h1)
          (not_mem_of_disjoint_thickening hnp h2))
        (fun z hz hz' hzX => label_eq_of_not_mem_second hfs i j j' z hz hz' (not_mem_of_disjoint_thickening hnp hzX))⟩
  let a : Fin 2 → Fin 2 → TorusSite n → ℝ := fun i j y =>
    levelShare ℓ.coupling ℓ.side t (Finset.univ \ thickening lumpRange (torusHotSites ℓ (W i j))) y (W i j)
  let q : Fin 2 → Fin 2 → TorusSite n → ℝ := fun i j y => φ n y (W i j) (Y i j) (ω i j)
  let u : Fin 2 → Fin 2 → ℝ := fun i j => -x * ∑ y, a i j y + ∑ y, q i j y
  have hn2 : 2 ≤ n := by omega
  have ha0 : 0 ≤ ℓ.coupling := by
    have := hfit.a_ge
    linarith
  have hform : ∀ i j, Dij i j = D n (trivialField n) * Real.exp (u i j) * prodΦ i j := fun i j => by
    have h1 := hull.form n hb (W i j) (Y i j) (ω i j) (hhull i j)
    rw [actionAtLevel_eq_sum_levelShare hadd ℓ.coupling ha0 ℓ.side hLpos hn2] at h1
    exact h1
  have hp : ∀ i j, 0 ≤ prodΦ i j := fun i j =>
    Finset.prod_nonneg fun X _ => hull.factor_nonneg n hb _ _ _ X
  obtain ⟨hiff, hrest⟩ := log_cross_ratio_eq _ hflat u prodΦ Dij hform hp hprod
  refine ⟨hprod, hiff, fun hpos => ?_⟩
  obtain ⟨hppos, hlog⟩ := hrest hpos
  have hnz : ∀ i j, ∀ X ∈ chainComponents (clusterRange x) (Y i j), Φ n (W i j) (Y i j) (ω i j) X ≠ 0 :=
    fun i j => Finset.prod_ne_zero_iff.mp (hppos i j).ne'
  have hb1 := decaySumBound_nonneg δ₁
  have hb2 := decaySumBound_nonneg ℓ.decayRate
  have hA : 0 ≤ σA ^ 2 * N 0 := by
    obtain ⟨-, -, -, -, -, -, -, hN, -⟩ := hch
    have := hN 0
    positivity
  have hc1 : 0 ≤ 2 * (σA ^ 2 * N 0) * Real.exp (δ₁ * ((lumpReadRadius + 4 : ℕ) : ℝ)) * decaySumBound δ₁ := by
    positivity
  have hc2 : 0 ≤ 2 * 1 * Real.exp (ℓ.decayRate * ((2 : ℕ) : ℝ)) * decaySumBound ℓ.decayRate := by positivity
  have hCnn : 0 ≤ C := by linarith
  have hMn : 0 ≤ min (P.card : ℝ) P'.card := le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hx0 : 0 ≤ x := by linarith
  have hRHS : 0 ≤ C * x * min (P.card : ℝ) P'.card * Real.exp (-(ℓ.decayRate * d / 3)) := by positivity
  by_cases hP : P.Nonempty
  swap
  · have hD : ∀ j, Dij 1 j = Dij 0 j := fun j =>
      labelWeight_congr Dq (funext fun x' => funext fun k =>
          field_eq_of_not_mem_first hfs 1 0 j (x', k) (fun h => hP ⟨_, h⟩) fun h => hP ⟨_, h⟩)
        (Finset.ext fun z => mem_iff_of_not_mem_first hfs 1 0 j z fun h => hP ⟨_, h⟩)
        fun z hz hz' => label_eq_of_not_mem_first hfs 1 0 j z hz hz' fun h => hP ⟨_, h⟩
    rw [log_cross_ratio_eq_zero_of_first Dij hD hpos, abs_zero]
    exact hRHS
  by_cases hP' : P'.Nonempty
  swap
  · have hD : ∀ i, Dij i 1 = Dij i 0 := fun i =>
      labelWeight_congr Dq (funext fun x' => funext fun k =>
          field_eq_of_not_mem_second hfs i 1 0 (x', k) (fun h => hP' ⟨_, h⟩) fun h => hP' ⟨_, h⟩)
        (Finset.ext fun z => mem_iff_of_not_mem_second hfs i 1 0 z fun h => hP' ⟨_, h⟩)
        fun z hz hz' => label_eq_of_not_mem_second hfs i 1 0 z hz hz' fun h => hP' ⟨_, h⟩
    rw [log_cross_ratio_eq_zero_of_second Dij hD hpos, abs_zero]
    exact hRHS
  rw [hlog]
  have hrnat : clusterRange x ≤ 16 * d := by
    have h1 : (clusterRange x : ℝ) ≤ 16 * d := by linarith
    exact_mod_cast h1
  have hgap : lumpReadRadius = 36869 := by norm_num [lumpReadRadius]
  have hSA := sum_abs_le_of_far_from_either P P' hP hP' d (lumpReadRadius + 4) 0 hd (by rw [hgap]; omega)
    (fun y => a 1 1 y + a 0 0 y - a 1 0 y - a 0 1 y) (2 * (σA ^ 2 * N 0)) δ₁ (by positivity) hδ₁ (by
      intro y m _ hdis
      rcases hdis with h1 | h1
      · exact abs_cross_diff_le_of_first (fun i j => a i j y) _ _ fun j =>
          levelShare_diff_le hch hreg hfit hLn hn64 hs₀ t hP
            (fun b h2 h3 => field_eq_of_not_mem_first hfs 1 0 j b h2 h3) h1
      · exact abs_cross_diff_le_of_second (fun i j => a i j y) _ _ fun i =>
          levelShare_diff_le hch hreg hfit hLn hn64 hs₀ t hP'
            (fun b h2 h3 => field_eq_of_not_mem_second hfs i 1 0 b h2 h3) h1)
  have hSq := sum_abs_le_of_far_from_either P P' hP hP' d 2 (clusterRange x / 64 + 1) hd (by omega)
    (fun y => q 1 1 y + q 0 0 y - q 1 0 y - q 0 1 y) (2 * 1) ℓ.decayRate (by norm_num) hfp (by
      intro y m hm hdis
      have hr64 : (clusterRange x : ℝ) / 64 ≤ m := by
        have h1 : clusterRange x ≤ 64 * m := by omega
        have h2 : (clusterRange x : ℝ) ≤ 64 * m := by exact_mod_cast h1
        linarith
      rcases hdis with h1 | h1
      · exact abs_cross_diff_le_of_first (fun i j => q i j y) 1 _ fun j =>
          siteDensity_diff_le hull hb hP (hhull 1 j) (hhull 0 j) (hnz 1 j) (hnz 0 j)
            (fun b h2 h3 => field_eq_of_not_mem_first hfs 1 0 j b h2 h3)
            (fun z hz => mem_iff_of_not_mem_first hfs 1 0 j z hz)
            (fun z hz hz' hzP => label_eq_of_not_mem_first hfs 1 0 j z hz hz' hzP) h1 hr64
      · exact abs_cross_diff_le_of_second (fun i j => q i j y) 1 _ fun i =>
          siteDensity_diff_le hull hb hP' (hhull i 1) (hhull i 0) (hnz i 1) (hnz i 0)
            (fun b h2 h3 => field_eq_of_not_mem_second hfs i 1 0 b h2 h3)
            (fun z hz => mem_iff_of_not_mem_second hfs i 1 0 z hz)
            (fun z hz hz' hzP => label_eq_of_not_mem_second hfs i 1 0 z hz hz' hzP) h1 hr64)
  have hE : Real.exp (-(δ₁ * d / 3)) ≤ Real.exp (-(ℓ.decayRate * d / 3)) := by
    apply Real.exp_le_exp.mpr
    have : ℓ.decayRate * d ≤ δ₁ * d := mul_le_mul_of_nonneg_right hfl (Nat.cast_nonneg _)
    linarith
  have hsum := cross_sum_eq x a q
  have habs : |u 1 1 + u 0 0 - u 1 0 - u 0 1| ≤
      x * ∑ y, |a 1 1 y + a 0 0 y - a 1 0 y - a 0 1 y| + ∑ y, |q 1 1 y + q 0 0 y - q 1 0 y - q 0 1 y| := by
    have e : u 1 1 + u 0 0 - u 1 0 - u 0 1 =
        -x * ∑ y, (a 1 1 y + a 0 0 y - a 1 0 y - a 0 1 y) + ∑ y, (q 1 1 y + q 0 0 y - q 1 0 y - q 0 1 y) :=
      hsum
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ (Finset.abs_sum_le_sum_abs _ _))
    rw [abs_mul, abs_neg, abs_of_nonneg hx0]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hx0
  exact habs.trans (two_sums_le hx hMn (Real.exp_pos _).le hE hc1 hc2 hC hSA hSq)
end Core
theorem fourCornerBound_holds (hadd : SharesSumToAction) (hreg : ComplementOfThickenedLumpsRegular) :
    FourCornerBound := by
  intro T hD
  refine ⟨2 * (T.σA ^ 2 * T.N 0) * Real.exp (T.δ₁ * ((lumpReadRadius + 4 : ℕ) : ℝ)) * decaySumBound T.δ₁ +
      2 * 1 * Real.exp (T.rt / 2 ^ 12 * ((2 : ℕ) : ℝ)) * decaySumBound (T.rt / 2 ^ 12),
    max T.floorMin ((2 : ℝ) ^ 2200), ?_⟩
  intro y hy R hℓ hyx hrow n _ hb P P' W Y ω d hfs hhull hd hrd hcl
  have hy0 : T.floorMin ≤ y := le_trans (le_max_left _ _) hy
  have hy1 : (2 : ℝ) ^ 2200 ≤ R.coupling := le_trans (le_max_right _ _) (hy.trans hyx)
  have hfit : R.params.Admissible := by
    rw [hℓ]
    exact hD.fits y hy0
  have hforget : R.params.decayRate = T.rt / 2 ^ 12 := by
    rw [hℓ]
    rfl
  have hch : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam T.ρA T.σA T.cg T.N := by
    rw [hℓ]
    exact hD.chain
  have hσ : R.params.threshold ≤ T.σA := by
    rw [hℓ]
    have h1 := hD.σ_le
    have h2 := hD.σ_pos
    show T.threshold ≤ T.σA
    linarith
  have hrt := hD.rt_pos
  have hrl := hD.rt_le
  have hcl' := hD.δc_le
  have hδ := hD.δ₁_pos
  have hx1 : 1 ≤ R.coupling := le_trans (one_le_pow₀ (by norm_num)) hy1
  exact log_cross_ratio_le hadd hreg hfit hrow.1 hrow.2 hδ (by rw [hforget]; positivity)
    (by rw [hforget]; linarith) hch hσ (by rw [hforget]) hx1 (le_clusterRange_of_le hy1) hb P P' W Y ω d hfs
    hhull hd hrd hcl
end YangMills.Construction.ClusterExpansionOfAStep.FourCornerProof
end
