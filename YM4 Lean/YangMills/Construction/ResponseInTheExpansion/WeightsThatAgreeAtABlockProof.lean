import YangMills.Construction.ResponseInTheExpansion.GasOfAResponseAtColdFieldsProof
import YangMills.Construction.ResponseInTheExpansion.WeightsNearTheirMeansProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AgreeingWeightsProof
open BlockAverages hiding unitStep
open WeightedResponses TorusLumps TorusFields StepSettings BlockOffsets AgreeingWeights
section Weights
variable {L : ℕ} [NeZero L]
private theorem fineCentre_depth_zero {n : ℕ} [NeZero n] (y : TorusSite n) :
    (fineCentre L 0 y : TorusSite (fineSide L 0 n)) = y := by
  have := siteOfInt_cast_self y
  simpa [fineCentre, fineSide] using this
private def offsetSite (L r : ℕ) {n : ℕ} (y : TorusSite n) (z : Fin 4 → ℤ) : TorusSite (fineSide L r n) :=
  fineCentre L r y + siteOfInt z
private def scaledOffset (L t : ℕ) (o : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => (L : ℤ) ^ t * o i
private theorem offsetSite_fineSite (t : ℕ) {n : ℕ} [NeZero n] (Y : TorusSite n) (o z : Fin 4 → ℤ) :
    offsetSite L t (fineSite L Y 0 o) z = offsetSite L (t + 1) Y (scaledOffset L t o + z) := by
  funext i
  show (((L : ℤ) ^ t * ((fineSite L Y 0 o i).cast : ℤ) : ℤ) : ZMod (fineSide L t (n * L))) + ((z i : ℤ) : ZMod _) =
    (((L : ℤ) ^ (t + 1) * ((Y i).cast : ℤ) : ℤ) : ZMod (fineSide L t (n * L))) +
      (((L : ℤ) ^ t * o i + z i : ℤ) : ZMod _)
  rw [← Int.cast_add, ← Int.cast_add, ZMod.intCast_eq_intCast_iff_dvd_sub]
  have h1 : (((fineSite L Y 0 o i).cast : ℤ) : ZMod (n * L)) =
      (((L : ℤ) * (((Y i).cast : ℤ) + (0 : Fin 4 → ℤ) i) + o i : ℤ) : ZMod (n * L)) := by
    rw [ZMod.intCast_zmod_cast]
    rfl
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
  refine ⟨q, ?_⟩
  rw [fineSide_eq]
  push_cast at hq ⊢
  have e : (L : ℤ) ^ (t + 1) = (L : ℤ) ^ t * L := pow_succ _ _
  rw [e]
  simp only [Pi.zero_apply, add_zero] at hq
  linear_combination ((L : ℤ) ^ t) * hq
private theorem mem_sitesInBlocks_iff' {n : ℕ} [NeZero n] (S : Finset (TorusSite n)) (x : TorusSite (n * L)) :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.SharedProofs.p74636 <;> assumption
private theorem fineSite_mem_sitesInBlocks (hodd : Odd L) {n : ℕ} [NeZero n] (Y : TorusSite n) {o : Fin 4 → ℤ}
    (ho : o ∈ centredCube L) : fineSite L Y 0 o ∈ sitesInBlocks L {Y} := by
  rw [mem_sitesInBlocks_iff', parentBlock_fineSite hodd Y 0 o ho, siteOfInt_zero_offset, add_zero]
  exact Finset.mem_singleton_self _
private theorem isPlaquetteAt_of_fineSite (hodd : Odd L) (t : ℕ) {n : ℕ} [NeZero n] (Y : TorusSite n)
    {o : Fin 4 → ℤ} (ho : o ∈ centredCube L)
    (p : TorusPlaquette (fineSide L t (n * L))) (hp : IsPlaquetteAt L t (fineSite L Y 0 o) p) :
    IsPlaquetteAt L (t + 1) Y p := by
  obtain ⟨h1, c, hc, hb⟩ := hp
  exact ⟨h1, c, hc, Finset.mem_biUnion.mpr ⟨_, fineSite_mem_sitesInBlocks hodd Y ho, hb⟩⟩
private theorem weightsAgreeAt_fineSite (hodd : Odd L) (t : ℕ) {n n' : ℕ} [NeZero n] [NeZero n']
    (Y : TorusSite n) (Y' : TorusSite n')
    (h : PlaquetteWeight (fineSide L (t + 1) n)) (h' : PlaquetteWeight (fineSide L (t + 1) n'))
    (hag : WeightsAgreeAt L (t + 1) Y Y' h h') {o : Fin 4 → ℤ} (ho : o ∈ centredCube L) :
    WeightsAgreeAt L t (fineSite L Y 0 o) (fineSite L Y' 0 o) h h' := by
  have hne : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have hne' : NeZero (n' * L) := ⟨mul_ne_zero (NeZero.ne n') (NeZero.ne L)⟩
  intro z μ ν hzb hz
  have e1 : offsetSite L t (fineSite L Y 0 o) z = offsetSite L (t + 1) Y (scaledOffset L t o + z) :=
    offsetSite_fineSite t Y o z
  have e2 : offsetSite L t (fineSite L Y' 0 o) z = offsetSite L (t + 1) Y' (scaledOffset L t o + z) :=
    offsetSite_fineSite t Y' o z
  have hz' : IsPlaquetteAt L (t + 1) Y (offsetSite L (t + 1) Y (scaledOffset L t o + z), μ, ν) := by
    have := isPlaquetteAt_of_fineSite hodd t Y ho _ hz
    have e3 : (fineCentre L t (fineSite L Y 0 o) + siteOfInt z : TorusSite (fineSide L t (n * L))) =
      offsetSite L t (fineSite L Y 0 o) z := rfl
    rw [e3, e1] at this
    exact this
  have hb : ∀ i, |(scaledOffset L t o + z) i| ≤ (L : ℤ) ^ (t + 1) := by
    intro i
    have h2 := (mem_centredCube_iff o).mp ho i
    obtain ⟨H, hH⟩ := hodd
    have hL : ((L : ℤ) - 1) / 2 = (H : ℤ) := by subst hH; push_cast; omega
    have hL' : (L : ℤ) = 2 * H + 1 := by exact_mod_cast hH
    have h3 : |o i| ≤ (H : ℤ) := by
      rw [abs_le]
      rw [hL] at h2
      exact h2
    have hp : (0 : ℤ) ≤ (L : ℤ) ^ t := by positivity
    have h4 : |scaledOffset L t o i| = (L : ℤ) ^ t * |o i| := by
      simp only [scaledOffset, abs_mul, abs_of_nonneg hp]
    have h5 := mul_le_mul_of_nonneg_left h3 hp
    have h6 := abs_add_le (scaledOffset L t o i) (z i)
    have h7 := hzb i
    have e : (L : ℤ) ^ (t + 1) = (L : ℤ) ^ t * (2 * H + 1) := by rw [pow_succ, hL']
    show |scaledOffset L t o i + z i| ≤ _
    rw [e]
    nlinarith
  have h3 := hag _ μ ν hb hz'
  show h (offsetSite L t (fineSite L Y 0 o) z, μ, ν) = h' (offsetSite L t (fineSite L Y' 0 o) z, μ, ν)
  rw [e1, e2]
  exact h3
abbrev _root_.YangMills.SharedProofs.p19862 := @weightsAgreeAt_fineSite
private theorem blockMean_depth_zero {n : ℕ} [NeZero n] (y : TorusSite n) (h : PlaquetteWeight (fineSide L 0 n)) :
    blockMean L 0 n y h = (1 / 24) * ∑ q : Fin 4 × Fin 4, if q.1 < q.2 then
      h (y, q) + h (y - unitStep n q.1, q) + h (y - unitStep n q.2, q) +
        h (y - unitStep n q.1 - unitStep n q.2, q) else 0 := by
  have h1 : plaquettesIn (n := n) Finset.univ = Finset.univ.filter fun p : TorusPlaquette n => p.2.1 < p.2.2 := by
    ext p
    simp [plaquettesIn]
  show (1 / 24 : ℝ) * ∑ p ∈ plaquettesIn (n := n) Finset.univ, vertexMultiplicity y p * h p = _
  congr 1
  rw [h1, Finset.sum_filter, show (Finset.univ : Finset (TorusPlaquette n)) = Finset.univ ×ˢ Finset.univ from rfl,
    Finset.sum_product_right]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with hq
  · have hc : ∀ x : TorusSite n, vertexMultiplicity y (x, q) = (if x = y then (1 : ℝ) else 0) +
        (if x = y - unitStep n q.1 then 1 else 0) + (if x = y - unitStep n q.2 then 1 else 0) +
        (if x = y - unitStep n q.1 - unitStep n q.2 then 1 else 0) := by
      intro x
      have a1 : x + unitStep n q.1 = y ↔ x = y - unitStep n q.1 := eq_sub_iff_add_eq.symm
      have a2 : x + unitStep n q.2 = y ↔ x = y - unitStep n q.2 := eq_sub_iff_add_eq.symm
      have a3 : x + unitStep n q.1 + unitStep n q.2 = y ↔ x = y - unitStep n q.1 - unitStep n q.2 := by
        rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq, add_right_comm]
      simp only [vertexMultiplicity, plaquetteVertices, List.count_cons, List.count_nil, beq_iff_eq, a1, a2, a3]
      push_cast
      ring_nf
    simp only [hc, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rfl
  · simp
private def cornerOffset (a b : ℤ) (μ ν : Fin 4) : Fin 4 → ℤ :=
  fun i => (if i = μ then a else 0) + (if i = ν then b else 0)
private theorem siteOfInt_cornerOffset_zero_zero {m : ℕ} (μ ν : Fin 4) :
    (siteOfInt (cornerOffset 0 0 μ ν) : TorusSite m) = 0 := by
  funext i
  simp [cornerOffset, siteOfInt]
private theorem siteOfInt_cornerOffset_one_zero {m : ℕ} (μ ν : Fin 4) :
    (siteOfInt (cornerOffset 1 0 μ ν) : TorusSite m) = unitStep m μ := by
  funext i
  by_cases h : i = μ <;> simp [cornerOffset, siteOfInt, unitStep, h]
private theorem siteOfInt_cornerOffset_zero_one {m : ℕ} (μ ν : Fin 4) :
    (siteOfInt (cornerOffset 0 1 μ ν) : TorusSite m) = unitStep m ν := by
  funext i
  by_cases h : i = ν <;> simp [cornerOffset, siteOfInt, unitStep, h]
private theorem siteOfInt_cornerOffset_one_one {m : ℕ} (μ ν : Fin 4) :
    (siteOfInt (cornerOffset 1 1 μ ν) : TorusSite m) = unitStep m μ + unitStep m ν := by
  funext i
  by_cases h : i = μ <;> by_cases h' : i = ν <;> simp [cornerOffset, siteOfInt, unitStep, Pi.single_apply, h, h']
private theorem siteOfInt_sub_offsets {m : ℕ} [NeZero m] (e e' : Fin 4 → ℤ) :
    (siteOfInt (e - e') : TorusSite m) = siteOfInt e - siteOfInt e' := by
  funext i
  simp [siteOfInt]
private theorem mem_plaquetteVertices_iff' {m : ℕ} [NeZero m] (x c : TorusSite m) (μ ν : Fin 4) :
    c ∈ plaquetteVertices x μ ν ↔ ∃ a b : ℤ, (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) ∧
      c = x + siteOfInt (cornerOffset a b μ ν) := by
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (h | h | h | h)
    · exact ⟨0, 0, Or.inl rfl, Or.inl rfl, by rw [siteOfInt_cornerOffset_zero_zero, add_zero, h]⟩
    · exact ⟨1, 0, Or.inr rfl, Or.inl rfl, by rw [siteOfInt_cornerOffset_one_zero, h]⟩
    · exact ⟨0, 1, Or.inl rfl, Or.inr rfl, by rw [siteOfInt_cornerOffset_zero_one, h]⟩
    · exact ⟨1, 1, Or.inr rfl, Or.inr rfl, by rw [siteOfInt_cornerOffset_one_one, h, add_assoc]⟩
  · rintro ⟨a, b, rfl | rfl, rfl | rfl, h⟩
    · left; rw [h, siteOfInt_cornerOffset_zero_zero, add_zero]
    · right; right; left; rw [h, siteOfInt_cornerOffset_zero_one]
    · right; left; rw [h, siteOfInt_cornerOffset_one_zero]
    · right; right; right; rw [h, siteOfInt_cornerOffset_one_one, add_assoc]
private def blockOffsetSet (L : ℕ) : ℕ → Set (Fin 4 → ℤ)
  | 0 => {0}
  | t + 1 => {v | ∃ o ∈ centredCube L, ∃ w ∈ blockOffsetSet L t, v = scaledOffset L t o + w}
private theorem mem_fineBlock_iff' (hodd : Odd L) (t : ℕ) :
    ∀ {n : ℕ} [NeZero n] (y : TorusSite n) (c : TorusSite (fineSide L t n)),
    c ∈ fineBlock L t n y ↔ ∃ v ∈ blockOffsetSet L t, c = offsetSite L t y v := by
  induction t with
  | zero =>
    intro n _ y c
    have e0 : offsetSite L 0 y (0 : Fin 4 → ℤ) = fineCentre L 0 y := by
      show fineCentre L 0 y + siteOfInt 0 = fineCentre L 0 y
      rw [siteOfInt_zero_offset, add_zero]
    have e : offsetSite L 0 y 0 = y := e0.trans (fineCentre_depth_zero y)
    constructor
    · intro h
      have h1 : c = y := Finset.mem_singleton.mp h
      exact ⟨0, rfl, h1.trans e.symm⟩
    · rintro ⟨v, hv, hc⟩
      have hv0 : v = 0 := hv
      subst hv0
      exact Finset.mem_singleton.mpr (hc.trans e)
  | succ t ih =>
    intro n _ Y c
    constructor
    · intro h
      obtain ⟨y', hy', hc⟩ := Finset.mem_biUnion.mp h
      have hb : parentBlock L y' = Y := Finset.mem_singleton.mp ((mem_sitesInBlocks_iff' _ _).mp hy')
      obtain ⟨o, ho, rfl⟩ := exists_fineSite_of_parentBlock hodd Y y' hb
      obtain ⟨w, hw, rfl⟩ := (ih _ _).mp hc
      exact ⟨_, ⟨o, ho, w, hw, rfl⟩, offsetSite_fineSite t Y o w⟩
    · rintro ⟨v, ⟨o, ho, w, hw, rfl⟩, hc⟩
      refine Finset.mem_biUnion.mpr ⟨_, fineSite_mem_sitesInBlocks hodd Y ho, (ih _ _).mpr ⟨w, hw, ?_⟩⟩
      exact hc.trans (offsetSite_fineSite t Y o w).symm
private theorem blockOffsetSet_bound (hodd : Odd L) (t : ℕ) (v : Fin 4 → ℤ) (hv : v ∈ blockOffsetSet L t)
    (i : Fin 4) : 2 * |v i| + 1 ≤ (L : ℤ) ^ t := by
  induction t generalizing v with
  | zero =>
    have hv0 : v = 0 := hv
    subst hv0
    simp
  | succ t ih =>
    obtain ⟨o, ho, w, hw, rfl⟩ := hv
    have h1 := ih w hw
    have h2 := (mem_centredCube_iff o).mp ho i
    obtain ⟨H, hH⟩ := hodd
    have hL : ((L : ℤ) - 1) / 2 = (H : ℤ) := by subst hH; push_cast; omega
    have hL' : (L : ℤ) = 2 * H + 1 := by exact_mod_cast hH
    have h3 : |o i| ≤ (H : ℤ) := by
      rw [abs_le]
      rw [hL] at h2
      exact h2
    have hp : (0 : ℤ) ≤ (L : ℤ) ^ t := by positivity
    have h4 : |scaledOffset L t o i + w i| ≤ (L : ℤ) ^ t * H + |w i| := by
      refine (abs_add_le _ _).trans ?_
      have : |scaledOffset L t o i| = (L : ℤ) ^ t * |o i| := by
        simp only [scaledOffset, abs_mul, abs_of_nonneg hp]
      rw [this]
      have := mul_le_mul_of_nonneg_left h3 hp
      linarith
    have e : (L : ℤ) ^ (t + 1) = (L : ℤ) ^ t * (2 * H + 1) := by rw [pow_succ, hL']
    show 2 * |scaledOffset L t o i + w i| + 1 ≤ _
    rw [e]
    nlinarith
private def IsCornerOffset (L t : ℕ) (μ ν : Fin 4) (z : Fin 4 → ℤ) : Prop :=
  ∃ v ∈ blockOffsetSet L t, ∃ a b : ℤ, (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) ∧ z = v - cornerOffset a b μ ν
private theorem abs_le_of_isCornerOffset (hodd : Odd L) (t : ℕ) {μ ν : Fin 4} (hμ : μ ≠ ν) {z : Fin 4 → ℤ}
    (hz : IsCornerOffset L t μ ν z) (i : Fin 4) : |z i| ≤ (L : ℤ) ^ t := by
  obtain ⟨v, hv, a, b, ha, hb, rfl⟩ := hz
  have h1 := blockOffsetSet_bound hodd t v hv i
  have h2 : |cornerOffset a b μ ν i| ≤ 1 := by
    by_cases c1 : i = μ
    · have c2 : ¬ i = ν := fun c => hμ (c1.symm.trans c)
      rcases ha with rfl | rfl <;> simp [cornerOffset, c1, c2, hμ]
    · by_cases c2 : i = ν
      · rcases hb with rfl | rfl <;> simp [cornerOffset, c1, c2, hμ.symm]
      · simp [cornerOffset, c1, c2]
  have h3 := abs_sub (v i) (cornerOffset a b μ ν i)
  have h4 : 0 ≤ |v i| := abs_nonneg _
  show |v i - cornerOffset a b μ ν i| ≤ _
  linarith
private theorem offsetSite_add (t : ℕ) {n : ℕ} [NeZero n] (y : TorusSite n) (z e : Fin 4 → ℤ) :
    offsetSite L t y (z + e) = offsetSite L t y z + siteOfInt e := by
  show fineCentre L t y + siteOfInt (z + e) = fineCentre L t y + siteOfInt z + siteOfInt e
  rw [siteOfInt_add, add_assoc]
private theorem isPlaquetteAt_of_isCornerOffset (hodd : Odd L) (t : ℕ) {n : ℕ} [NeZero n] (y : TorusSite n)
    {μ ν : Fin 4} (hμ : μ < ν) {z : Fin 4 → ℤ} (hz : IsCornerOffset L t μ ν z) :
    IsPlaquetteAt L t y (offsetSite L t y z, μ, ν) := by
  obtain ⟨v, hv, a, b, ha, hb, rfl⟩ := hz
  refine ⟨hμ, offsetSite L t y v, ?_, (mem_fineBlock_iff' hodd t y _).mpr ⟨v, hv, rfl⟩⟩
  refine (mem_plaquetteVertices_iff' _ _ _ _).mpr ⟨a, b, ha, hb, ?_⟩
  rw [← offsetSite_add]
  congr 1
  abel
private theorem exists_isCornerOffset_of_isPlaquetteAt (hodd : Odd L) (t : ℕ) {n : ℕ} [NeZero n] (y : TorusSite n)
    (p : TorusPlaquette (fineSide L t n)) (hp : IsPlaquetteAt L t y p) :
    p.2.1 < p.2.2 ∧ ∃ z, IsCornerOffset L t p.2.1 p.2.2 z ∧ p.1 = offsetSite L t y z := by
  obtain ⟨h1, c, hc, hb⟩ := hp
  refine ⟨h1, ?_⟩
  obtain ⟨v, hv, rfl⟩ := (mem_fineBlock_iff' hodd t y c).mp hb
  obtain ⟨a, b, ha, hb', e⟩ := (mem_plaquetteVertices_iff' _ _ _ _).mp hc
  refine ⟨v - cornerOffset a b p.2.1 p.2.2, ⟨v, hv, a, b, ha, hb', rfl⟩, ?_⟩
  have h2 : offsetSite L t y (v - cornerOffset a b p.2.1 p.2.2 + cornerOffset a b p.2.1 p.2.2) =
      offsetSite L t y (v - cornerOffset a b p.2.1 p.2.2) + siteOfInt (cornerOffset a b p.2.1 p.2.2) :=
    offsetSite_add t y _ _
  rw [sub_add_cancel] at h2
  exact add_right_cancel (e.symm.trans h2)
private theorem sum_sitesInBlocks_singleton (hodd : Odd L) {n : ℕ} [NeZero n] (Y : TorusSite n)
    (f : TorusSite (n * L) → ℝ) :
    ∑ y ∈ sitesInBlocks L {Y}, f y = ∑ o ∈ centredCube L, f (fineSite L Y 0 o) := by apply _root_.YangMills.SharedProofs.p123070 <;> assumption
private def baseOffsetSite (L : ℕ) {n : ℕ} (y : TorusSite n) (z : Fin 4 → ℤ) : TorusSite n :=
  offsetSite L 0 y z
private theorem baseOffsetSite_neg_cornerOffset {n : ℕ} [NeZero n] (y : TorusSite n) (a b : ℤ) (μ ν : Fin 4) :
    baseOffsetSite L y (0 - cornerOffset a b μ ν) = y - siteOfInt (cornerOffset a b μ ν) := by
  have e2 : (fineCentre L 0 y : TorusSite (fineSide L 0 n)) = y := fineCentre_depth_zero y
  have e3 : (siteOfInt (0 - cornerOffset a b μ ν) : TorusSite n) = - siteOfInt (cornerOffset a b μ ν) := by
    rw [siteOfInt_sub_offsets, siteOfInt_zero_offset, zero_sub]
  show (fineCentre L 0 y + siteOfInt (0 - cornerOffset a b μ ν) : TorusSite (fineSide L 0 n)) = _
  rw [e2]
  show y + (siteOfInt (0 - cornerOffset a b μ ν) : TorusSite n) = _
  rw [e3]
  exact (sub_eq_add_neg _ _).symm
private theorem blockMean_eq_of_weightsAgreeAt (hodd : Odd L) (t : ℕ) :
    ∀ {n n' : ℕ} [NeZero n] [NeZero n'] (y : TorusSite n) (y' : TorusSite n')
    (h : PlaquetteWeight (fineSide L t n)) (h' : PlaquetteWeight (fineSide L t n')),
    WeightsAgreeAt L t y y' h h' → blockMean L t n y h = blockMean L t n' y' h' := by
  induction t with
  | zero =>
    intro n n' _ _ y y' h h' hag
    rw [blockMean_depth_zero, blockMean_depth_zero]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs with hq
    · let H : TorusSite n → ℝ := fun w => h (w, q)
      let H' : TorusSite n' → ℝ := fun w => h' (w, q)
      have key : ∀ a b : ℤ, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
          H (y - siteOfInt (cornerOffset a b q.1 q.2)) = H' (y' - siteOfInt (cornerOffset a b q.1 q.2)) := by
        intro a b ha hb
        have hz : IsCornerOffset L 0 q.1 q.2 (0 - cornerOffset a b q.1 q.2) := ⟨0, rfl, a, b, ha, hb, rfl⟩
        have h1 := hag _ q.1 q.2 (abs_le_of_isCornerOffset hodd 0 hq.ne hz)
          (isPlaquetteAt_of_isCornerOffset hodd 0 y hq hz)
        have e1 := baseOffsetSite_neg_cornerOffset (L := L) y a b q.1 q.2
        have e2 := baseOffsetSite_neg_cornerOffset (L := L) y' a b q.1 q.2
        rw [← e1, ← e2]
        exact h1
      have k1 := key 0 0 (Or.inl rfl) (Or.inl rfl)
      have k2 := key 1 0 (Or.inr rfl) (Or.inl rfl)
      have k3 := key 0 1 (Or.inl rfl) (Or.inr rfl)
      have k4 := key 1 1 (Or.inr rfl) (Or.inr rfl)
      simp only [siteOfInt_cornerOffset_zero_zero, siteOfInt_cornerOffset_one_zero,
        siteOfInt_cornerOffset_zero_one, siteOfInt_cornerOffset_one_one, sub_zero, ← sub_sub] at k1 k2 k3 k4
      show H y + H (y - unitStep n q.1) + H (y - unitStep n q.2) + H (y - unitStep n q.1 - unitStep n q.2) =
        H' y' + H' (y' - unitStep n' q.1) + H' (y' - unitStep n' q.2) + H' (y' - unitStep n' q.1 - unitStep n' q.2)
      rw [k1, k2, k3, k4]
    · rfl
  | succ t ih =>
    intro n n' _ _ Y Y' h h' hag
    have hne : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
    have hne' : NeZero (n' * L) := ⟨mul_ne_zero (NeZero.ne n') (NeZero.ne L)⟩
    show ((L : ℝ) ^ 4)⁻¹ * ∑ y ∈ sitesInBlocks L {Y}, blockMean L t (n * L) y h =
      ((L : ℝ) ^ 4)⁻¹ * ∑ y ∈ sitesInBlocks L {Y'}, blockMean L t (n' * L) y h'
    rw [sum_sitesInBlocks_singleton hodd Y, sum_sitesInBlocks_singleton hodd Y']
    congr 1
    exact Finset.sum_congr rfl fun o ho => ih _ _ _ _ (weightsAgreeAt_fineSite hodd t Y Y' h h' hag ho)
private def doubledOffset (z : Fin 4 → ℤ) (μ ν : Fin 4) : Fin 4 → ℤ :=
  fun i => 2 * z i + (if i = μ then 1 else 0) + (if i = ν then 1 else 0)
private theorem doubledBarycentre_siteOfInt {m : ℕ} [NeZero m] (g : Fin 4 → ℤ) (μ ν i : Fin 4) :
    doubledBarycentre ((siteOfInt g : TorusSite m), μ, ν) i = ((doubledOffset g μ ν i : ℤ) : ZMod (2 * m)) := by
  have h1 : ((((siteOfInt g : TorusSite m) i).val : ℤ) : ZMod m) = ((g i : ℤ) : ZMod m) := by
    rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id', id]
    rfl
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
  show ((2 * (((siteOfInt g : TorusSite m) i).val) + (if i = μ then 1 else 0) + (if i = ν then 1 else 0) : ℕ) :
    ZMod (2 * m)) = _
  rw [← Int.cast_natCast, ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨q, ?_⟩
  simp only [doubledOffset]
  split_ifs <;> push_cast <;> linarith
private theorem supDist_doubledBarycentre {m : ℕ} [NeZero m] (g g' : Fin 4 → ℤ) (μ ν μ' ν' : Fin 4)
    (hs : ∀ i, |doubledOffset g μ ν i - doubledOffset g' μ' ν' i| < m) :
    supDist (doubledBarycentre ((siteOfInt g : TorusSite m), μ, ν))
        (doubledBarycentre ((siteOfInt g' : TorusSite m), μ', ν')) =
      Finset.univ.sup fun i => (doubledOffset g μ ν i - doubledOffset g' μ' ν' i).natAbs := by
  have hne : NeZero (2 * m) := ⟨mul_ne_zero two_ne_zero (NeZero.ne m)⟩
  unfold supDist
  congr 1
  funext i
  rw [doubledBarycentre_siteOfInt, doubledBarycentre_siteOfInt, ← Int.cast_sub]
  have h1 := abs_lt.mp (hs i)
  have := (ZMod.valMinAbs_spec (((doubledOffset g μ ν i - doubledOffset g' μ' ν' i : ℤ)) : ZMod (2 * m))
    (doubledOffset g μ ν i - doubledOffset g' μ' ν' i)).mpr ⟨rfl, by
      constructor
      · push_cast; linarith [h1.1]
      · push_cast; linarith [h1.2]⟩
  rw [this]
private def doubledOffsetDist (z : Fin 4 → ℤ) (μ ν : Fin 4) (z' : Fin 4 → ℤ) (μ' ν' : Fin 4) : ℕ :=
  Finset.univ.sup fun i => (doubledOffset z μ ν i - doubledOffset z' μ' ν' i).natAbs
private theorem abs_doubledOffset_le (hodd : Odd L) (r : ℕ) (z : Fin 4 → ℤ) {μ ν : Fin 4} (hμ : μ ≠ ν)
    (hz : IsCornerOffset L r μ ν z) (i : Fin 4) : |doubledOffset z μ ν i| ≤ (L : ℤ) ^ r := by
  obtain ⟨v, hv, a, b, ha, hb, rfl⟩ := hz
  have h1 := blockOffsetSet_bound hodd r v hv i
  have h2 : doubledOffset (v - cornerOffset a b μ ν) μ ν i = 2 * v i + (if i = μ then 1 - 2 * a else 0) +
      (if i = ν then 1 - 2 * b else 0) := by
    simp only [doubledOffset, cornerOffset, Pi.sub_apply]
    split_ifs <;> ring
  rw [h2]
  have h3 : |(if i = μ then 1 - 2 * a else 0) + (if i = ν then 1 - 2 * b else (0 : ℤ))| ≤ 1 := by
    by_cases c1 : i = μ
    · have c2 : ¬ i = ν := fun c => hμ (c1.symm.trans c)
      rcases ha with rfl | rfl <;> simp [c1, c2, hμ]
    · by_cases c2 : i = ν
      · rcases hb with rfl | rfl <;> simp [c1, c2, hμ.symm]
      · simp [c1, c2]
  have h4 := abs_add_le (2 * v i) ((if i = μ then 1 - 2 * a else 0) + (if i = ν then 1 - 2 * b else (0 : ℤ)))
  have h5 : |2 * v i| = 2 * |v i| := by rw [abs_mul]; simp
  rw [add_assoc]
  linarith
private theorem offsetSite_eq_siteOfInt (r : ℕ) {n : ℕ} [NeZero n] (y : TorusSite n) (z : Fin 4 → ℤ) :
    offsetSite L r y z = siteOfInt ((fun i => (L : ℤ) ^ r * ((y i).cast : ℤ)) + z) := by
  rw [siteOfInt_add]
  rfl
private theorem barycentreDist_offsetSite (hodd : Odd L) (r s : ℕ) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (y : TorusSite n) {z z' : Fin 4 → ℤ} {μ ν μ' ν' : Fin 4} (hμ : μ < ν) (hμ' : μ' < ν')
    (hz : IsCornerOffset L r μ ν z) (hz' : IsCornerOffset L r μ' ν' z') :
    barycentreDist L s (offsetSite L r y z, μ, ν) (offsetSite L r y z', μ', ν') =
      (doubledOffsetDist z μ ν z' μ' ν' : ℝ) / (2 * (L : ℝ) ^ s) := by
  have hd : ∀ (c : Fin 4 → ℤ) (i : Fin 4), doubledOffset (c + z) μ ν i - doubledOffset (c + z') μ' ν' i =
      doubledOffset z μ ν i - doubledOffset z' μ' ν' i := by
    intro c i
    simp only [doubledOffset, Pi.add_apply]
    ring
  unfold barycentreDist
  congr 2
  rw [offsetSite_eq_siteOfInt, offsetSite_eq_siteOfInt, supDist_doubledBarycentre]
  · unfold doubledOffsetDist
    congr 1
    funext i
    rw [hd]
  · intro i
    rw [hd]
    have h1 := abs_doubledOffset_le hodd r z hμ.ne hz i
    have h2 := abs_doubledOffset_le hodd r z' hμ'.ne hz' i
    have h3 := abs_sub (doubledOffset z μ ν i) (doubledOffset z' μ' ν' i)
    have hp : (0 : ℤ) < (L : ℤ) ^ r := by
      have : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    have hm : ((fineSide L r n : ℕ) : ℤ) = n * (L : ℤ) ^ r := by
      rw [fineSide_eq]
      push_cast
      ring
    rw [hm]
    nlinarith
private theorem isPlaquetteAt_transfer (hodd : Odd L) (r : ℕ) {n n' : ℕ} [NeZero n] [NeZero n'] (hn : 3 ≤ n)
    (Y : TorusSite n) (Y' : TorusSite n') {z : Fin 4 → ℤ} {μ ν : Fin 4} (hz : ∀ i, |z i| ≤ (L : ℤ) ^ r)
    (hp : IsPlaquetteAt L r Y (offsetSite L r Y z, μ, ν)) : IsPlaquetteAt L r Y' (offsetSite L r Y' z, μ, ν) := by
  obtain ⟨hμ, z₁, hz₁, e⟩ := exists_isCornerOffset_of_isPlaquetteAt hodd r Y _ hp
  have hμ' : μ < ν := hμ
  have hz₁' : IsCornerOffset L r μ ν z₁ := hz₁
  have h1 : (siteOfInt z : TorusSite (fineSide L r n)) = siteOfInt z₁ := add_left_cancel (a := fineCentre L r Y) e
  have hp' : (0 : ℤ) < (L : ℤ) ^ r := by
    have : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hm : ((fineSide L r n : ℕ) : ℤ) = n * (L : ℤ) ^ r := by
    rw [fineSide_eq]
    push_cast
    ring
  have h2 : z = z₁ := eq_of_siteOfInt_eq h1 fun i => by
    have a1 := hz i
    have a2 := abs_le_of_isCornerOffset hodd r hμ'.ne hz₁' i
    have a3 := abs_sub (z i) (z₁ i)
    rw [hm]
    nlinarith
  rw [h2]
  exact isPlaquetteAt_of_isCornerOffset hodd r Y' hμ' hz₁'
private theorem eq_of_direction_parity : ∀ μ ν μ' ν' : Fin 4, μ < ν → μ' < ν' →
    (∀ i : Fin 4, ((if i = μ then 1 else 0) + (if i = ν then 1 else 0) : ℕ) % 2 =
      ((if i = μ' then 1 else 0) + (if i = ν' then 1 else 0) : ℕ) % 2) → μ = μ' ∧ ν = ν' := by
  decide
private theorem eq_of_doubledOffsetDist_eq_zero {z z' : Fin 4 → ℤ} {μ ν μ' ν' : Fin 4} (hμ : μ < ν)
    (hμ' : μ' < ν') (h : doubledOffsetDist z μ ν z' μ' ν' = 0) : z = z' ∧ μ = μ' ∧ ν = ν' := by
  have h0 : ∀ i, doubledOffset z μ ν i = doubledOffset z' μ' ν' i := by
    intro i
    have h1 := Finset.le_sup (f := fun i => (doubledOffset z μ ν i - doubledOffset z' μ' ν' i).natAbs)
      (Finset.mem_univ i)
    have h2 : (doubledOffset z μ ν i - doubledOffset z' μ' ν' i).natAbs = 0 := by
      have : (Finset.univ.sup fun i => (doubledOffset z μ ν i - doubledOffset z' μ' ν' i).natAbs) = 0 := h
      omega
    have := Int.natAbs_eq_zero.mp h2
    linarith
  have hp := eq_of_direction_parity μ ν μ' ν' hμ hμ' (fun i => by
    have h1 := h0 i
    simp only [doubledOffset] at h1
    split_ifs at h1 ⊢ <;> omega)
  obtain ⟨rfl, rfl⟩ := hp
  refine ⟨funext fun i => ?_, rfl, rfl⟩
  have h1 := h0 i
  simp only [doubledOffset] at h1
  linarith
private theorem barycentreDist_nonneg' {m : ℕ} (s : ℕ) (p q : TorusPlaquette m) : 0 ≤ barycentreDist L s p q := by apply _root_.YangMills.Construction.WeightedResponses.NearMeans.barycentreDist_nonneg <;> assumption
private theorem barycentreDist_self' {m : ℕ} [NeZero m] (s : ℕ) (p : TorusPlaquette m) :
    barycentreDist L s p p = 0 := by
  have hne : NeZero (2 * m) := ⟨mul_ne_zero two_ne_zero (NeZero.ne m)⟩
  unfold barycentreDist
  rw [supDist_self]
  simp
private theorem barycentreDist_comm' {m : ℕ} [NeZero m] (s : ℕ) (p q : TorusPlaquette m) :
    barycentreDist L s p q = barycentreDist L s q p := by
  have hne : NeZero (2 * m) := ⟨mul_ne_zero two_ne_zero (NeZero.ne m)⟩
  unfold barycentreDist
  rw [supDist_comm]
private theorem barycentreDist_triangle' {m : ℕ} [NeZero m] (s : ℕ) (p q r : TorusPlaquette m) :
    barycentreDist L s p r ≤ barycentreDist L s p q + barycentreDist L s q r := by
  have hne : NeZero (2 * m) := ⟨mul_ne_zero two_ne_zero (NeZero.ne m)⟩
  unfold barycentreDist
  rw [← add_div]
  have h := supDist_triangle (doubledBarycentre p) (doubledBarycentre q) (doubledBarycentre r)
  have h' : (supDist (doubledBarycentre p) (doubledBarycentre r) : ℝ) ≤
      (supDist (doubledBarycentre p) (doubledBarycentre q) : ℝ) +
        (supDist (doubledBarycentre q) (doubledBarycentre r) : ℝ) := by
    exact_mod_cast h
  exact div_le_div_of_nonneg_right h' (by positivity)
private theorem weightSup_nonneg' {m : ℕ} (h : PlaquetteWeight m) : 0 ≤ weightSup h :=
  Real.iSup_nonneg fun _ => abs_nonneg _
private theorem weightLipschitz_nonneg' {m : ℕ} (s : ℕ) (h : PlaquetteWeight m) : 0 ≤ weightLipschitz L s h :=
  Real.iSup_nonneg fun _ => div_nonneg (abs_nonneg _) (barycentreDist_nonneg' s _ _)
private theorem le_weightSup' {m : ℕ} [NeZero m] (h : PlaquetteWeight m) (p : OrientedPlaquette m) :
    |h p.1| ≤ weightSup h :=
  le_ciSup (f := fun p : OrientedPlaquette m => |h p.1|) (Set.finite_range _).bddAbove p
private theorem le_weightLipschitz' {m : ℕ} [NeZero m] (s : ℕ) (h : PlaquetteWeight m) (p q : OrientedPlaquette m) :
    |h p.1 - h q.1| / barycentreDist L s p.1 q.1 ≤ weightLipschitz L s h :=
  le_ciSup (f := fun pp : OrientedPlaquette m × OrientedPlaquette m =>
      |h pp.1.1 - h pp.2.1| / barycentreDist L s pp.1.1 pp.2.1)
    (Set.finite_range _).bddAbove (p, q)
private theorem orientedPlaquette_nonempty {m : ℕ} [NeZero m] : Nonempty (OrientedPlaquette m) :=
  ⟨⟨(0, 0, 1), show (0 : Fin 4) < 1 by decide⟩⟩
private theorem exists_extension_le (s : ℕ) {m : ℕ} [NeZero m] (S : Finset (OrientedPlaquette m))
    (g : PlaquetteWeight m) (M Λ : ℝ)
    (hM : 0 ≤ M) (hΛ : 0 ≤ Λ) (h1 : ∀ p ∈ S, |g p.1| ≤ M)
    (h2 : ∀ p ∈ S, ∀ q ∈ S, |g p.1 - g q.1| ≤ Λ * barycentreDist L s p.1 q.1) :
    ∃ g' : PlaquetteWeight m, (∀ p ∈ S, g' p.1 = g p.1) ∧ weightSup g' ≤ M ∧ weightLipschitz L s g' ≤ Λ := by
  have hne := orientedPlaquette_nonempty (m := m)
  by_cases hS : S.Nonempty
  · let f : TorusPlaquette m → ℝ := fun p => S.inf' hS fun s' => g s'.1 + Λ * barycentreDist L s p s'.1
    let c : ℝ → ℝ := fun r => max (-M) (min M r)
    have hf : ∀ p ∈ S, f p.1 = g p.1 := by
      intro p hp
      refine le_antisymm ?_ ?_
      · refine (Finset.inf'_le _ hp).trans ?_
        rw [barycentreDist_self', mul_zero, add_zero]
      · refine Finset.le_inf' _ _ fun q hq => ?_
        have := (abs_le.mp (h2 p hp q hq)).2
        linarith
    have hlip : ∀ p q : TorusPlaquette m, f p ≤ f q + Λ * barycentreDist L s p q := by
      intro p q
      obtain ⟨s', hs', e⟩ := Finset.exists_mem_eq_inf' hS fun s' : OrientedPlaquette m =>
        g s'.1 + Λ * barycentreDist L s q s'.1
      have h3 : f p ≤ g s'.1 + Λ * barycentreDist L s p s'.1 :=
        Finset.inf'_le (fun s' : OrientedPlaquette m => g s'.1 + Λ * barycentreDist L s p s'.1) hs'
      have h4 : f q = g s'.1 + Λ * barycentreDist L s q s'.1 := e
      have h5 := mul_le_mul_of_nonneg_left (barycentreDist_triangle' (L := L) s p q s'.1) hΛ
      rw [h4]
      linarith
    have hc : ∀ r r' : ℝ, |c r - c r'| ≤ |r - r'| := by
      intro r r'
      have a1 := abs_max_sub_max_le_max (-M) (min M r) (-M) (min M r')
      have a2 := abs_min_sub_min_le_max M r M r'
      simp only [sub_self, abs_zero] at a1 a2
      have a3 : max 0 |r - r'| = |r - r'| := max_eq_right (abs_nonneg _)
      rw [a3] at a2
      have a4 : max 0 |min M r - min M r'| = |min M r - min M r'| := max_eq_right (abs_nonneg _)
      rw [a4] at a1
      exact a1.trans a2
    have hb : ∀ r : ℝ, |c r| ≤ M := by
      intro r
      refine abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
    refine ⟨fun p => c (f p), fun p hp => ?_, ?_, ?_⟩
    · show c (f p.1) = g p.1
      rw [hf p hp]
      have := abs_le.mp (h1 p hp)
      show max (-M) (min M (g p.1)) = g p.1
      rw [min_eq_right this.2, max_eq_right this.1]
    · exact ciSup_le fun p => hb _
    · refine ciSup_le fun pp => ?_
      have hd := barycentreDist_nonneg' (L := L) s pp.1.1 pp.2.1
      rcases hd.eq_or_lt with h0 | h0
      · rw [← h0, div_zero]
        exact hΛ
      · rw [div_le_iff₀ h0]
        refine (hc _ _).trans (abs_le.mpr ⟨?_, ?_⟩)
        · have := hlip pp.2.1 pp.1.1
          rw [barycentreDist_comm'] at this
          linarith
        · have := hlip pp.1.1 pp.2.1
          linarith
  · have hS' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    refine ⟨fun _ => 0, fun p hp => ?_, ?_, ?_⟩
    · simp [hS'] at hp
    · refine ciSup_le fun p => ?_
      simpa using hM
    · refine ciSup_le fun p => ?_
      simpa using hΛ
private theorem weightsAgreeAt_of_eq_on_block (hodd : Odd L) (r : ℕ) {n n' : ℕ} [NeZero n] [NeZero n'] (hn : 3 ≤ n)
    (Y : TorusSite n) (Y' : TorusSite n') (h : PlaquetteWeight (fineSide L r n))
    (h' g : PlaquetteWeight (fineSide L r n'))
    (hag : WeightsAgreeAt L r Y Y' h h') (hg : ∀ p, IsPlaquetteAt L r Y' p → g p = h' p) :
    WeightsAgreeAt L r Y Y' h g := by
  intro z μ ν hz hp
  have h1 := hag z μ ν hz hp
  have h2 := hg _ (isPlaquetteAt_transfer hodd r hn Y Y' hz hp)
  exact h1.trans h2.symm
private theorem exists_eq_on_block_weightNorm_le (hodd : Odd L) (r s : ℕ) {n n' : ℕ} [NeZero n] [NeZero n']
    (hn : 3 ≤ n) (hn' : 3 ≤ n')
    (Y : TorusSite n) (Y' : TorusSite n') (h : PlaquetteWeight (fineSide L r n))
    (h' : PlaquetteWeight (fineSide L r n'))
    (hag : WeightsAgreeAt L r Y Y' h h') :
    ∃ g : PlaquetteWeight (fineSide L r n'), (∀ p, IsPlaquetteAt L r Y' p → g p = h' p) ∧
      weightNorm L s g ≤ weightNorm L s h := by
  classical
  let S : Finset (OrientedPlaquette (fineSide L r n')) := Finset.univ.filter fun p => IsPlaquetteAt L r Y' p.1
  have key : ∀ p ∈ S, ∃ z, IsCornerOffset L r p.1.2.1 p.1.2.2 z ∧ p.1.1 = offsetSite L r Y' z ∧
      h' p.1 = h (offsetSite L r Y z, p.1.2.1, p.1.2.2) := by
    intro p hp
    have hat : IsPlaquetteAt L r Y' p.1 := (Finset.mem_filter.mp hp).2
    obtain ⟨hμ, z, hz, e⟩ := exists_isCornerOffset_of_isPlaquetteAt hodd r Y' p.1 hat
    refine ⟨z, hz, e, ?_⟩
    have h1 := hag z p.1.2.1 p.1.2.2 (abs_le_of_isCornerOffset hodd r hμ.ne hz)
      (isPlaquetteAt_of_isCornerOffset hodd r Y hμ hz)
    have e2 : p.1 = (offsetSite L r Y' z, p.1.2.1, p.1.2.2) := Prod.ext e rfl
    rw [e2]
    exact h1.symm
  obtain ⟨g, g1, g2, g3⟩ := exists_extension_le (L := L) s S h' (weightSup h) (weightLipschitz L s h)
    (weightSup_nonneg' h) (weightLipschitz_nonneg' s h)
    (fun p hp => by
      obtain ⟨z, hz, -, e⟩ := key p hp
      rw [e]
      exact le_weightSup' h ⟨(offsetSite L r Y z, p.1.2.1, p.1.2.2), p.2⟩)
    (fun p hp q hq => by
      obtain ⟨z, hz, ep, e⟩ := key p hp
      obtain ⟨z', hz', eq', e'⟩ := key q hq
      have hμ : p.1.2.1 < p.1.2.2 := p.2
      have hμ' : q.1.2.1 < q.1.2.2 := q.2
      have b1 := barycentreDist_offsetSite (L := L) hodd r s hn Y hμ hμ' hz hz'
      have b2 := barycentreDist_offsetSite (L := L) hodd r s hn' Y' hμ hμ' hz hz'
      have ep' : p.1 = (offsetSite L r Y' z, p.1.2.1, p.1.2.2) := Prod.ext ep rfl
      have eq'' : q.1 = (offsetSite L r Y' z', q.1.2.1, q.1.2.2) := Prod.ext eq' rfl
      have hd : barycentreDist L s p.1 q.1 =
          (doubledOffsetDist z p.1.2.1 p.1.2.2 z' q.1.2.1 q.1.2.2 : ℝ) / (2 * (L : ℝ) ^ s) := by
        rw [← b2, ← ep', ← eq'']
      rw [e, e', hd, ← b1]
      by_cases h0 : doubledOffsetDist z p.1.2.1 p.1.2.2 z' q.1.2.1 q.1.2.2 = 0
      · obtain ⟨c1, c2, c3⟩ := eq_of_doubledOffsetDist_eq_zero hμ hμ' h0
        rw [c1, c2, c3, sub_self, abs_zero]
        exact mul_nonneg (weightLipschitz_nonneg' s h) (barycentreDist_nonneg' s _ _)
      · have hpos : 0 < barycentreDist L s (offsetSite L r Y z, p.1.2.1, p.1.2.2)
            (offsetSite L r Y z', q.1.2.1, q.1.2.2) := by
          rw [b1]
          have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
          have : (0 : ℝ) < doubledOffsetDist z p.1.2.1 p.1.2.2 z' q.1.2.1 q.1.2.2 := by
            exact_mod_cast Nat.pos_of_ne_zero h0
          positivity
        have := le_weightLipschitz' (L := L) s h ⟨(offsetSite L r Y z, p.1.2.1, p.1.2.2), p.2⟩
          ⟨(offsetSite L r Y z', q.1.2.1, q.1.2.2), q.2⟩
        rwa [div_le_iff₀ hpos] at this)
  refine ⟨g, fun p hp => ?_, max_le_max g2 g3⟩
  exact g1 ⟨p, hp.1⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
end Weights
theorem _root_.YangMills.Construction.AgreeingWeights.weightsAgreeingOnBlock : WeightsAgreeingOnBlock := by
  intro L _ hodd
  refine ⟨fun t n n' _ _ Y Y' h h' hag o ho => weightsAgreeAt_fineSite hodd t Y Y' h h' hag ho,
    fun t n n' _ _ y y' h h' hag => blockMean_eq_of_weightsAgreeAt hodd t y y' h h' hag, ?_⟩
  intro r s n n' _ _ hn hn' Y Y' h h' hag
  obtain ⟨g, g1, g2⟩ := exists_eq_on_block_weightNorm_le hodd r s hn hn' Y Y' h h' hag
  exact ⟨g, g1, g2, weightsAgreeAt_of_eq_on_block hodd r hn Y Y' h h' g hag g1⟩
end YangMills.Construction.AgreeingWeightsProof
end
