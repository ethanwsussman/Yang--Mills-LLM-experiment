import YangMills.Construction.ColdStepAtMirrorFrames.FieldNearTheFlatField
import YangMills.Construction.ColdStepAtMirrorFrames.FlatChainOfTheLeastCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.FlatResponsesAreScalar
import YangMills.Construction.ColdStepAtMirrorFrames.TransportOfTheExpansionProof
import YangMills.Construction.SummableBoundsOfTheFlow.BoundAlongMovesAboveTheFramesProof
import YangMills.Construction.SummableBoundsOfTheFlow.DecayOfTheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.GaugeOfAMotion
import YangMills.Construction.SummableBoundsOfTheFlow.RotationOfTheBlockExpansion
import YangMills.Construction.SummableBoundsOfTheFlow.TheFramesBetween
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames Estimates GaugeAlongMotion SummableBounds
namespace Interpolation
namespace TopOrderNearBlock
theorem sum_partSize_eq_card {k : ℕ} (c : OrderedFinpartition k) : ∑ m, c.partSize m = k := by
  have h := Fintype.card_congr c.equivSigma
  simpa using h
theorem eq_atomic_of_length_eq {k : ℕ} (c : OrderedFinpartition k) (h : c.length = k) :
    c = OrderedFinpartition.atomic k := by
  obtain ⟨len, ps, hpos, emb, hmono, hparts, hdisj, hcov⟩ := c
  simp only at h
  subst h
  have hsum : ∑ m, ps m = len := sum_partSize_eq_card ⟨len, ps, hpos, emb, hmono, hparts, hdisj, hcov⟩
  have hps : ps = fun _ => 1 := by
    funext m
    have h1 : ∑ m : Fin len, (ps m - 1) = 0 := by
      have h2 : ∑ m : Fin len, (ps m - 1 + 1) = len :=
        (Finset.sum_congr rfl fun m _ => Nat.sub_add_cancel (hpos m)).trans hsum
      rw [Finset.sum_add_distrib] at h2
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h2
      omega
    have h3 := (Finset.sum_eq_zero_iff.1 h1) m (Finset.mem_univ m)
    have := hpos m
    omega
  subst hps
  have hg : StrictMono fun m : Fin len => emb m ⟨0, one_pos⟩ := hparts
  have hid : (fun m : Fin len => emb m ⟨0, one_pos⟩) = id := by
    funext m
    exact le_antisymm hg.apply_le hg.le_apply
  have hemb : emb = fun m _ => m := by
    funext m q
    have hq : q = ⟨0, one_pos⟩ := Subsingleton.elim _ _
    subst hq
    exact congrFun hid m
  subst hemb
  rfl
theorem length_lt_of_ne_atomic {k : ℕ} {c : OrderedFinpartition k}
    (h : c ≠ OrderedFinpartition.atomic k) : c.length < k :=
  lt_of_le_of_ne c.length_le fun e => h (eq_atomic_of_length_eq c e)
theorem prod_add_le_prod_add {ι : Type} (s : Finset ι) (a : ι → ℝ) {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (h0 : ∀ l ∈ s, 0 ≤ a l) (h1 : ∀ l ∈ s, a l ≤ A) :
    ∏ l ∈ s, (a l + ε) ≤ ∏ l ∈ s, a l + ε * (2 * (A + 1)) ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hε]
  | insert i s hi ih =>
    have ih' := ih (fun l hl => h0 l (Finset.mem_insert_of_mem hl))
      (fun l hl => h1 l (Finset.mem_insert_of_mem hl))
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have ha0 := h0 i (Finset.mem_insert_self _ _)
    have ha1 := h1 i (Finset.mem_insert_self _ _)
    set P := ∏ l ∈ s, a l with hP
    set D := (2 * (A + 1)) ^ s.card with hD
    have hD0 : 0 ≤ D := by positivity
    have hPD : P ≤ D := by
      calc P ≤ ∏ _l ∈ s, (2 * (A + 1)) := Finset.prod_le_prod
            (fun l hl => h0 l (Finset.mem_insert_of_mem hl))
            (fun l hl => by have := h1 l (Finset.mem_insert_of_mem hl); linarith)
        _ = D := by simp [hD]
    calc (a i + ε) * ∏ l ∈ s, (a l + ε) ≤ (a i + ε) * (P + ε * D) :=
          mul_le_mul_of_nonneg_left ih' (add_nonneg ha0 hε)
      _ = a i * P + ε * (a i * D + P + ε * D) := by ring
      _ ≤ a i * P + ε * ((2 * (A + 1)) * D) := by
          have : a i * D + P + ε * D ≤ (2 * (A + 1)) * D := by
            have e1 : a i * D ≤ A * D := mul_le_mul_of_nonneg_right ha1 hD0
            have e2 : ε * D ≤ 1 * D := mul_le_mul_of_nonneg_right hε1 hD0
            nlinarith
          have := mul_le_mul_of_nonneg_left this hε
          linarith
      _ = a i * P + ε * (2 * (A + 1)) ^ (s.card + 1) := by rw [hD]; ring
theorem sum_mul_prod_le_of_near {ι : Type} {k : ℕ} (T : Finset ι) (g : (Fin k → ι) → ℝ)
    (Z A B : Fin k → ι → ℝ)
    (Nr : ι → Prop) {ε Am Cg Cw γ : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hAm : 0 ≤ Am) (hCw : 0 ≤ Cw)
    (hg0 : ∀ b, 0 ≤ g b) (hZ0 : ∀ l β, 0 ≤ Z l β) (hA0 : ∀ l β, 0 ≤ A l β) (hAm' : ∀ l β, A l β ≤ Am)
    (hZA : ∀ l β, Nr β → Z l β ≤ A l β + ε) (hZB : ∀ l β, Z l β ≤ B l β)
    (hCg : ∑ b ∈ Fintype.piFinset (fun _ : Fin k => T), g b ≤ Cg)
    (hB : ∀ l, ∑ β ∈ T, B l β ≤ Cw)
    (hfar : ∀ b, (∃ l, ¬ Nr (b l)) → g b ≤ γ) (hγ : 0 ≤ γ) :
    ∑ b ∈ Fintype.piFinset (fun _ : Fin k => T), g b * ∏ l, Z l (b l) ≤
      ∑ b ∈ Fintype.piFinset (fun _ : Fin k => T), g b * ∏ l, A l (b l) +
        ε * (2 * (Am + 1)) ^ k * Cg + γ * Cw ^ k := by
  classical
  have hB0 : ∀ l β, 0 ≤ B l β := fun l β => (hZ0 l β).trans (hZB l β)
  have hpt : ∀ b, g b * ∏ l, Z l (b l) ≤
      g b * ∏ l, A l (b l) + ε * (2 * (Am + 1)) ^ k * g b + γ * ∏ l, B l (b l) := by
    intro b
    have hBp : 0 ≤ ∏ l, B l (b l) := Finset.prod_nonneg fun l _ => hB0 l _
    have hAp : 0 ≤ ∏ l, A l (b l) := Finset.prod_nonneg fun l _ => hA0 l _
    by_cases hn : ∃ l, ¬ Nr (b l)
    · have h1 : ∏ l, Z l (b l) ≤ ∏ l, B l (b l) :=
        Finset.prod_le_prod (fun l _ => hZ0 l _) fun l _ => hZB l _
      have h2 := mul_le_mul (hfar b hn) h1 (Finset.prod_nonneg fun l _ => hZ0 l _) hγ
      have h3 := mul_nonneg (hg0 b) hAp
      have h4 : 0 ≤ ε * (2 * (Am + 1)) ^ k * g b := by positivity [hg0 b]
      linarith
    · push_neg at hn
      have h1 : ∏ l, Z l (b l) ≤ ∏ l, (A l (b l) + ε) :=
        Finset.prod_le_prod (fun l _ => hZ0 l _) fun l _ => hZA l _ (hn l)
      have h2 := prod_add_le_prod_add Finset.univ (fun l => A l (b l)) hAm hε hε1
        (fun l _ => hA0 l _) (fun l _ => hAm' l _)
      simp only [Finset.card_univ, Fintype.card_fin] at h2
      have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (hg0 b)
      have h4 := mul_nonneg hγ hBp
      nlinarith
  have hsumB : ∑ b ∈ Fintype.piFinset (fun _ : Fin k => T), ∏ l, B l (b l) ≤ Cw ^ k := by
    rw [← Finset.prod_univ_sum]
    calc ∏ l, ∑ β ∈ T, B l β ≤ ∏ _l : Fin k, Cw :=
          Finset.prod_le_prod (fun l _ => Finset.sum_nonneg fun β _ => hB0 l β) fun l _ => hB l
      _ = _ := by simp
  calc _ ≤ ∑ b ∈ Fintype.piFinset (fun _ : Fin k => T),
        (g b * ∏ l, A l (b l) + ε * (2 * (Am + 1)) ^ k * g b + γ * ∏ l, B l (b l)) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = _ + _ + _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := by
        have h1 := mul_le_mul_of_nonneg_left hCg (by positivity : 0 ≤ ε * (2 * (Am + 1)) ^ k)
        have h2 := mul_le_mul_of_nonneg_left hsumB hγ
        linarith
theorem iteratedFDeriv_along_motion_le {F : BlockFrame} {j k : ℕ} (hk : 1 ≤ k)
    (hexp : expansionAlongMotionStatement)
    (G : F.GaugeField j → ℝ) (W : F.GaugeField j) (α : (Fin k → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions)
    (T : Finset (F.Site j × Fin 4)) (e : ℕ → ℝ) (g : ∀ i : ℕ, (Fin i → F.Site j × Fin 4) → ℝ)
    (M : ℕ → ℝ) (ω : F.Site j × Fin 4 → Fin k → ℝ) (Cw : ℝ)
    (hper : ∀ i, F.period j i ≠ 0) (hT : ∀ b, b ∈ T) (he : ∀ i, 0 ≤ e i)
    (hg0 : ∀ i b, 0 ≤ g i b) (hg1 : ∀ i b, g i b ≤ 1) (hM : ∀ q, 0 ≤ M q) (hCw : 0 ≤ Cw)
    (hω0 : ∀ β l, 0 ≤ ω β l)
    (hG : ∀ (q : ℕ) (c : Fin q → F.Site j × Fin 4) (X : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ k (fun τ : Fin q → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0)
    (hdec : ∀ (i : ℕ) (b : Fin i → F.Site j × Fin 4) (X : Fin i → imaginaryQuaternions), 1 ≤ i → i ≤ k →
      AreUnitVectors X → |bondDeriv G W b X| ≤ e i * g i b)
    (hαs : ∀ x b, ContDiffAt ℝ k (fun τ => α τ x b) 0) (hα0 : ∀ x b, α 0 x b = 0)
    (hpart : ∀ (q : ℕ) (e' : Fin q → Fin k) (β : F.Site j × Fin 4) (l : Fin q), q ≤ k →
      ‖motionComponent α e' β.1 β.2‖ ≤ M q * ω β (e' l))
    (hsum : ∀ l, ∑ β ∈ T, ω β l ≤ Cw) :
    |iteratedFDeriv ℝ k (fun τ => G (leftTranslate (α τ) W)) 0 fun l => Pi.single l 1| ≤
      e k * ∑ b ∈ Fintype.piFinset (fun _ : Fin k => T), g k b *
          ∏ l, ‖motionComponent α (fun _ : Fin 1 => l) (b l).1 (b l).2‖ +
        (∑ c : OrderedFinpartition k, ∏ m, (M (c.partSize m) * Cw)) * runningMax e (k - 1) := by
  classical
  obtain ⟨-, hex⟩ := hexp.1 F j k G W α hper hG hαs hα0
  rw [hex]
  have hlE : ∀ p, 0 ≤ runningMax e p := fun p => by
    induction p with
    | zero => exact le_rfl
    | succ p ih => exact ih.trans (le_max_left _ _)
  have hle : ∀ {i p : ℕ}, 1 ≤ i → i ≤ p → e i ≤ runningMax e p := by
    intro i p hi hp
    induction p with
    | zero => omega
    | succ p ih =>
      rw [runningMax]
      rcases Nat.lt_or_ge i (p + 1) with h | h
      · exact (ih (by omega)).trans (le_max_left _ _)
      · have : i = p + 1 := by omega
        subst this
        exact le_max_right _ _
  have hterm : ∀ c : OrderedFinpartition k,
      |mixedDerivAlong G W fun m => motionComponent α (c.emb m)| ≤
        ∑ b ∈ Fintype.piFinset (fun _ : Fin c.length => T), (e c.length * g c.length b) *
          ∏ m, ‖motionComponent α (c.emb m) (b m).1 (b m).2‖ := by
    intro c
    have hlen : c.length ≤ k := c.length_le
    have hlen0 : c.length ≠ 0 := fun h => by
      have := c.length_pos hk
      omega
    have hlenk : ((c.length : ℕ) : WithTop ℕ∞) ≤ k := by exact_mod_cast hlen
    exact hexp.2 F j c.length G W (fun m => motionComponent α (c.emb m)) T
      (fun b => e c.length * g c.length b) hper hT (fun q c' X => (hG q c' X).of_le hlenk)
      (fun b X hX => hdec _ b X (Nat.one_le_iff_ne_zero.2 hlen0) hlen hX)
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (OrderedFinpartition.atomic k))]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (hterm _).trans ?_
    show ∑ b ∈ Fintype.piFinset (fun _ : Fin k => T), (e k * g k b) *
        ∏ m : Fin k, ‖motionComponent α (fun _ : Fin 1 => m) (b m).1 (b m).2‖ ≤ _
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => le_of_eq (mul_assoc _ _ _)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    have hnon : ∀ c ∈ Finset.univ.erase (OrderedFinpartition.atomic k),
        |mixedDerivAlong G W fun m => motionComponent α (c.emb m)| ≤
          (∏ m, (M (c.partSize m) * Cw)) * runningMax e (k - 1) := by
      intro c hc
      have hne : c ≠ OrderedFinpartition.atomic k := (Finset.mem_erase.1 hc).1
      have hlt := length_lt_of_ne_atomic hne
      have hlen0 : 1 ≤ c.length := c.length_pos hk
      have hei : e c.length ≤ runningMax e (k - 1) := hle hlen0 (by omega)
      refine (hterm c).trans ?_
      have hpt : ∀ b : Fin c.length → F.Site j × Fin 4,
          (e c.length * g c.length b) * ∏ m, ‖motionComponent α (c.emb m) (b m).1 (b m).2‖ ≤
            runningMax e (k - 1) * ∏ m, (M (c.partSize m) * ω (b m) (c.emb m ⟨0, c.partSize_pos m⟩)) := by
        intro b
        have h1 : e c.length * g c.length b ≤ runningMax e (k - 1) := by
          have := mul_le_mul hei (hg1 _ b) (hg0 _ b) (hlE _)
          simpa using this
        have h2 : ∏ m, ‖motionComponent α (c.emb m) (b m).1 (b m).2‖ ≤
            ∏ m, (M (c.partSize m) * ω (b m) (c.emb m ⟨0, c.partSize_pos m⟩)) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun m _ =>
            hpart _ (c.emb m) (b m) ⟨0, c.partSize_pos m⟩ (c.partSize_le m)
        exact mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (hlE _)
      refine (Finset.sum_le_sum fun b _ => hpt b).trans ?_
      have hprodsum := Finset.prod_univ_sum (fun _ : Fin c.length => T)
        (fun m β => M (c.partSize m) * ω β (c.emb m ⟨0, c.partSize_pos m⟩))
      rw [← Finset.mul_sum, ← hprodsum, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (hlE _)
      refine Finset.prod_le_prod (fun m _ => Finset.sum_nonneg fun β _ =>
        mul_nonneg (hM _) (hω0 _ _)) fun m _ => ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hsum _) (hM _)
    refine (Finset.sum_le_sum hnon).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun c _ _ =>
      mul_nonneg (Finset.prod_nonneg fun m _ => mul_nonneg (hM _) hCw) (hlE _)
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem norm_sub_adjointAction_le (g : UnitQuaternion) (v : imaginaryQuaternions) :
    ‖v - _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g v‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ * ‖v‖ := by
  set d : ℍ[ℝ] := (g : ℍ[ℝ]) - 1 with hd
  set u : ℍ[ℝ] := (v : ℍ[ℝ]) with hu
  set E : ℍ[ℝ] := ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hE
  have hgE : (g : ℍ[ℝ]) * E = 1 := by
    show ((g * g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1
    rw [mul_inv_cancel]
    rfl
  have hEn : ‖E‖ = 1 := _root_.YangMills.Construction.Interpolation.TopOrderNearBlock.norm_coe_unitQuaternion _
  have hn : ‖v - _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g v‖ = ‖u - (g : ℍ[ℝ]) * u * E‖ := rfl
  have heq : u - (g : ℍ[ℝ]) * u * E = (u * d - d * u) * E := by
    have hg : (g : ℍ[ℝ]) = d + 1 := by simp [hd]
    have h1 : u = u * (g : ℍ[ℝ]) * E := by rw [mul_assoc, hgE, mul_one]
    calc u - (g : ℍ[ℝ]) * u * E = u * (g : ℍ[ℝ]) * E - (g : ℍ[ℝ]) * u * E := by rw [← h1]
      _ = (u * d - d * u) * E := by rw [hg]; noncomm_ring
  rw [hn, heq, norm_mul, hEn, mul_one]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have : ‖u‖ = ‖v‖ := rfl
  rw [this]
  linarith [mul_comm ‖v‖ ‖d‖]
theorem norm_gauged_first_order_le {Zg Z : imaginaryQuaternions} {Wv φ₁ φ₂ : ℝ} {X : imaginaryQuaternions}
    (g : UnitQuaternion)
    (hZ : Zg = Z + -(φ₁ • X) - _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (-(φ₂ • X))) (hX : ‖X‖ = 1) :
    ‖Zg‖ ≤ |Wv + (φ₂ - φ₁)| + ‖Z - Wv • X‖ + 2 * ‖(g : ℍ[ℝ]) - 1‖ * |φ₂| := by
  have h1 : Zg = (Wv + (φ₂ - φ₁)) • X + (Z - Wv • X) +
      (-(φ₂ • X) - _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (-(φ₂ • X))) := by
    rw [hZ]
    module
  have h2 := norm_sub_adjointAction_le g (-(φ₂ • X))
  have h3 : ‖-(φ₂ • X)‖ = |φ₂| := by
    rw [norm_neg, norm_smul, hX, mul_one, Real.norm_eq_abs]
  rw [h3] at h2
  rw [h1]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ le_rfl)) h2)
  rw [norm_smul, hX, mul_one, Real.norm_eq_abs]
theorem bondDeriv_subtractTrivial {F : BlockFrame} {N i : ℕ} {f : LocalFamily} {y : F.Site F.depth}
    {W : F.GaugeField F.depth}
    {c : Fin i → F.Site F.depth × Fin 4} {X : Fin i → imaginaryQuaternions} (hi : i ≠ 0) (hN : i ≤ N)
    (h : ContDiffAt ℝ N (fun τ : Fin i → ℝ => f F y (leftTranslate (bondSpread c X τ) W)) 0) :
    bondDeriv (subtractTrivial f F y) W c X = bondDeriv (f F y) W c X := by apply _root_.YangMills.Construction.Estimates.bondDeriv_subtractTrivial <;> assumption
theorem one_le_torusDecayFactor (L : ℕ) {δ u : ℝ} (hδ : 0 ≤ δ) (hu : 0 ≤ u) :
    1 ≤ torusDecayFactor L δ u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.one_le_decayWeight <;> assumption
theorem interpolatedExpansion_deriv_le {F : BlockFrame} {L n₀ k m : ℕ} {σ δ s a ρA Cw : ℝ} {e : ℕ → ℝ}
    {f : LocalFamily} {V : F.GaugeField F.top} {η : StepVariable (finiteCells F)} {y : F.Site F.depth}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    (hexp : expansionAlongMotionStatement) (hk : 1 ≤ k)
    (hfam : HasBoundedDerivatives L F.depth n₀ σ δ k e f) (hlow : IsCubicTorusAbove L F.depth n₀ F)
    (he : ∀ j, 0 ≤ e j) (hδ : 0 ≤ δ) (hper : ∀ i, F.period F.depth i ≠ 0) (hT : ∀ b, b ∈ fineBonds F)
    (hcold0 : IsSmallCurvature σ (interpolatedField s a ρA m V η))
    (hcoldτ : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ),
      IsSmallCurvature σ (interpolatedField s a ρA m (leftTranslate (bondSpread c X τ) V) η))
    (α α' : (Fin k → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (ψ : Fin k → F.Site F.depth → imaginaryQuaternions)
    (hαe : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), interpolatedField s a ρA m (leftTranslate (bondSpread c X τ) V) η =
      leftTranslate (α τ) (interpolatedField s a ρA m V η))
    (hα'0 : ∀ x b, α' 0 x b = 0) (hα's : ∀ x b, ContDiffAt ℝ k (fun τ => α' τ x b) 0)
    (hα'e : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), _root_.YangMills.Construction.BlockAverages.gaugeTransform (gaugeExponential ψ τ)
      (leftTranslate (α τ) (interpolatedField s a ρA m V η)) =
        leftTranslate (α' τ) (interpolatedField s a ρA m V η))
    (M : ℕ → ℝ) (ω : F.Site F.depth × Fin 4 → Fin k → ℝ) (hM : ∀ q, 0 ≤ M q) (hCw : 0 ≤ Cw)
    (hω0 : ∀ β l, 0 ≤ ω β l)
    (hpart : ∀ (q : ℕ) (e' : Fin q → Fin k) (β : F.Site F.depth × Fin 4) (l : Fin q), q ≤ k →
      ‖motionComponent α' e' β.1 β.2‖ ≤ M q * ω β (e' l))
    (hsum : ∀ l, ∑ β ∈ fineBonds F, ω β l ≤ Cw) :
    |bondDeriv (interpolatedExpansion s a ρA m f y η) V c X| ≤
      e k * ∑ b ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F),
          (torusDecayFactor L δ (bondSpan y b))⁻¹ *
            ∏ l, ‖motionComponent α' (fun _ : Fin 1 => l) (b l).1 (b l).2‖ +
        (∑ c' : OrderedFinpartition k, ∏ m', (M (c'.partSize m') * Cw)) * runningMax e (k - 1) := by
  set W₀ := interpolatedField s a ρA m V η with hW₀
  set G : F.GaugeField F.depth → ℝ := subtractTrivial f F y with hG
  have hev : (fun τ : Fin k → ℝ => interpolatedExpansion s a ρA m f y η (leftTranslate (bondSpread c X τ) V))
      =ᶠ[𝓝 0] fun τ => G (leftTranslate (α' τ) W₀) := by
    filter_upwards [hcoldτ, hαe, hα'e] with τ h1 h2 h3
    simp only [interpolatedExpansion, hG]
    rw [← h3, ← h2]
    simp only [subtractTrivial]
    rw [hfam.gauge_invariant F hlow y _ _ h1]
  have hGf : ∀ (q : ℕ) (c' : Fin q → F.Site F.depth × Fin 4) (X' : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ k (fun τ : Fin q → ℝ => f F y (leftTranslate (bondSpread c' X' τ) W₀)) 0 :=
    hfam.smooth F hlow y W₀ hcold0
  have hder : bondDeriv (interpolatedExpansion s a ρA m f y η) V c X =
      iteratedFDeriv ℝ k (fun τ => G (leftTranslate (α' τ) W₀)) 0 fun l => Pi.single l 1 := by
    simp only [bondDeriv]
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev k).eq_of_nhds]
  rw [hder]
  refine iteratedFDeriv_along_motion_le hk hexp G W₀ α' (fineBonds F) e
    (fun i b => (torusDecayFactor L δ (bondSpan y b))⁻¹) M ω Cw hper hT he
    (fun i b => ?_) (fun i b => ?_) hM hCw hω0 (fun q c' X' => (hGf q c' X').sub contDiffAt_const)
    (fun i b X' hi hik hX => ?_) hα's hα'0 hpart hsum
  · exact inv_nonneg.2 (le_trans zero_le_one (one_le_torusDecayFactor L hδ (Nat.cast_nonneg _)))
  · exact inv_le_one_of_one_le₀ (one_le_torusDecayFactor L hδ (Nat.cast_nonneg _))
  · rw [hG, bondDeriv_subtractTrivial (by omega) hik (hGf _ b X')]
    exact hfam.decay F hlow y W₀ i b X' hcold0 hi hik hX
theorem abs_pathSum_le {F : BlockFrame} {j : ℕ} (W : LevelForm F j) {Wm : ℝ} (hW : ∀ x i, |W x i| ≤ Wm)
    (x : F.Site j) (l : List PathStep) : |pathSum W x l| ≤ l.length * Wm := by
  induction l generalizing x with
  | nil => simp [pathSum]
  | cons st r ih =>
    simp only [pathSum, List.length_cons]
    have h1 : |if st.2 then W x st.1 else - W (x - unitStep j st.1) st.1| ≤ Wm := by
      split_ifs
      · exact hW _ _
      · rw [abs_neg]
        exact hW _ _
    have h2 := ih (x + stepDisplacement j st)
    refine (abs_add_le _ _).trans ?_
    push_cast
    linarith
theorem length_axisPath_le {F : BlockFrame} {j : ℕ} (y z : F.Site j) :
    (axisPath (siteOffset y z) 1).length ≤ 4 * siteSupDist z y := by
  have hle : ∀ k : Fin 4, (siteOffset y z k).natAbs ≤ siteSupDist z y := fun k =>
    Finset.le_sup (f := fun i => ((z i - y i).valMinAbs).natAbs) (Finset.mem_univ k)
  simp only [axisPath, List.length_flatMap, List.length_replicate, Equiv.Perm.coe_one, id]
  have h := hle 0
  have h1 := hle 1
  have h2 := hle 2
  have h3 := hle 3
  simp [List.finRange_succ]
  omega
theorem smoothCutoff_eq_zero {F : BlockFrame} {R : ℝ} {y z : F.Site F.depth} (hR : 0 < R)
    (h : 2 * R ≤ siteSupDist z y) : smoothCutoff R y z = 0 := by
  have h1 : 2 - (siteSupDist z y : ℝ) / R ≤ 0 := by
    have : 2 ≤ (siteSupDist z y : ℝ) / R := by
      rw [le_div_iff₀ hR]
      exact h
    linarith
  simp [smoothCutoff, max_eq_left h1]
def axialGaugeFunction {F : BlockFrame} (R : ℝ) (y : F.Site F.depth) (W : LevelForm F F.depth)
    (z : F.Site F.depth) : ℝ :=
  smoothCutoff R y z * (- pathSum W y (axisPath (siteOffset y z) 1))
theorem abs_axialGaugeFunction_le {F : BlockFrame} {R Wm : ℝ} {y : F.Site F.depth}
    {W : LevelForm F F.depth} (hR : 0 < R)
    (hW : ∀ x i, |W x i| ≤ Wm) (z : F.Site F.depth) : |axialGaugeFunction R y W z| ≤ 8 * R * Wm := by
  have hW0 : 0 ≤ Wm := (abs_nonneg _).trans (hW 0 0)
  by_cases h : 2 * R ≤ siteSupDist z y
  · rw [axialGaugeFunction, smoothCutoff_eq_zero hR h]
    simp
    positivity
  · push_neg at h
    have hc0 : 0 ≤ smoothCutoff R y z := le_min zero_le_one (le_max_left _ _)
    have hc1 : smoothCutoff R y z ≤ 1 := min_le_left _ _
    have h1 := abs_pathSum_le W hW y (axisPath (siteOffset y z) 1)
    have h2 : ((axisPath (siteOffset y z) 1).length : ℝ) ≤ 4 * siteSupDist z y := by
      exact_mod_cast length_axisPath_le y z
    rw [axialGaugeFunction, abs_mul, abs_neg, abs_of_nonneg hc0]
    calc _ ≤ 1 * |pathSum W y (axisPath (siteOffset y z) 1)| :=
          mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
      _ ≤ (axisPath (siteOffset y z) 1).length * Wm := by rw [one_mul]; exact h1
      _ ≤ (4 * siteSupDist z y) * Wm := mul_le_mul_of_nonneg_right h2 hW0
      _ ≤ (4 * (2 * R)) * Wm := by
          refine mul_le_mul_of_nonneg_right ?_ hW0
          linarith
      _ = _ := by ring
theorem siteSupDist_add_unitStep_le {F : BlockFrame} {j : ℕ} (hper : ∀ l, 1 < F.period j l)
    (x : F.Site j) (i : Fin 4) :
    siteSupDist x (x + unitStep j i) ≤ 1 := by
  refine Finset.sup_le fun l _ => ?_
  have hne : NeZero (F.period j l) := ⟨by have := hper l; omega⟩
  have h1 : (x l - (x + unitStep j i : F.Site j) l) = -(unitStep j i : F.Site j) l := by
    show x l - (x l + (unitStep j i : F.Site j) l) = _
    ring
  rw [h1, ZMod.natAbs_valMinAbs_neg]
  by_cases h : l = i
  · subst h
    have hu : (unitStep j l l : ZMod (F.period j l)) = 1 := by
      simp [unitStep, siteOfCoords]
    rw [hu, ZMod.valMinAbs_natAbs_eq_min]
    have hf : Fact (1 < F.period j l) := ⟨hper l⟩
    rw [ZMod.val_one]
    omega
  · have hu : (unitStep j i l : ZMod (F.period j l)) = 0 := by
      simp [unitStep, siteOfCoords, Pi.single_apply, h]
    rw [hu]
    simp
theorem cellSupDist_le_one_of_near {F : BlockFrame} {y x : F.Site F.depth} {R : ℝ}
    (hls : ∀ x y : F.Site F.depth,
      F.blockSide * cellSupDist (enclosingCell x) (enclosingCell y) ≤ siteSupDist x y + F.blockSide)
    (htri : ∀ x y z : F.Site F.depth, siteSupDist x z ≤ siteSupDist x y + siteSupDist y z)
    (hRL : 2 * R + 2 ≤ F.blockSide) (h : (siteSupDist x y : ℝ) < 2 * R + 1) :
    cellSupDist (enclosingCell x) (enclosingCell y) ≤ 1 := by
  have h1 := hls x y
  by_contra hc
  push_neg at hc
  have h2 : 2 * F.blockSide ≤ F.blockSide * cellSupDist (enclosingCell x) (enclosingCell y) := by
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ hc
  have h3 : F.blockSide ≤ siteSupDist x y := by omega
  have h4 : (F.blockSide : ℝ) ≤ siteSupDist x y := by exact_mod_cast h3
  linarith
theorem inv_torusDecayFactor_le_exp (L : ℕ) {δ : ℝ} (u : ℝ) :
    (torusDecayFactor L δ u)⁻¹ ≤ Real.exp (-(δ * u)) := by apply _root_.YangMills.Construction.Estimates.inv_decayWeight_le_exp <;> assumption
theorem cellSupDist_le_bondSpan {F : BlockFrame} {k : ℕ} {y : F.Site F.depth}
    (b : Fin k → F.Site F.depth × Fin 4) (l : Fin k)
    (hls : ∀ x y : F.Site F.depth,
      F.blockSide * cellSupDist (enclosingCell x) (enclosingCell y) ≤ siteSupDist x y + F.blockSide)
    (hsite : ∀ x y : F.Site F.depth, siteSupDist x y = siteSupDist y x) :
    F.blockSide * cellSupDist (enclosingCell (b l).1) (enclosingCell y) ≤ bondSpan y b + F.blockSide := by
  have h1 := hls (b l).1 y
  have h2 : siteSupDist y (b l).1 ≤ bondSpan y b :=
    le_max_of_le_left (Finset.le_sup (f := fun l : Fin k => siteSupDist y (b l).1) (Finset.mem_univ l))
  rw [hsite] at h1
  omega
theorem sum_inv_torusDecayFactor_le {F : BlockFrame} {k : ℕ} {δ Cr : ℝ} {y : F.Site F.depth}
    (hδ : 0 ≤ δ) (hk6 : k ≤ 6)
    (hls : ∀ x y : F.Site F.depth,
      F.blockSide * cellSupDist (enclosingCell x) (enclosingCell y) ≤ siteSupDist x y + F.blockSide)
    (hsite : ∀ x y : F.Site F.depth, siteSupDist x y = siteSupDist y x)
    (hsum : ∑ b ∈ fineBonds F,
      Real.exp (-(δ * F.blockSide / 6 * cellSupDist (enclosingCell b.1) (enclosingCell y))) ≤ Cr) :
    ∑ b ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F), (torusDecayFactor F.blockSide δ (bondSpan y b))⁻¹ ≤
      Real.exp (δ * F.blockSide) * Cr ^ k := by
  classical
  let g : Fin k → F.Site F.depth × Fin 4 → ℝ := fun _ β =>
    Real.exp (-(δ * F.blockSide / 6 * cellSupDist (enclosingCell β.1) (enclosingCell y)))
  have hpt : ∀ b : Fin k → F.Site F.depth × Fin 4, (torusDecayFactor F.blockSide δ (bondSpan y b))⁻¹ ≤
      Real.exp (δ * F.blockSide) * ∏ l, g l (b l) := by
    intro b
    refine (inv_torusDecayFactor_le_exp F.blockSide _).trans ?_
    simp only [g]
    rw [← Real.exp_sum, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hu : ∀ l, (F.blockSide : ℝ) * cellSupDist (enclosingCell (b l).1) (enclosingCell y) ≤
        bondSpan y b + F.blockSide := fun l => by
      exact_mod_cast cellSupDist_le_bondSpan b l hls hsite
    have hs : ∑ l : Fin k, (F.blockSide : ℝ) * cellSupDist (enclosingCell (b l).1) (enclosingCell y) ≤
        6 * ((bondSpan y b : ℝ) + F.blockSide) := by
      have h1 := Finset.sum_le_sum fun (l : Fin k) (_ : l ∈ Finset.univ) => hu l
      refine h1.trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h6 : (k : ℝ) ≤ 6 := by exact_mod_cast hk6
      exact mul_le_mul_of_nonneg_right h6 (by positivity)
    have h2 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ δ / 6)
    rw [Finset.mul_sum] at h2
    have h3 : ∑ l : Fin k, -(δ * F.blockSide / 6 * cellSupDist (enclosingCell (b l).1) (enclosingCell y)) =
        -∑ l : Fin k, δ / 6 * ((F.blockSide : ℝ) * cellSupDist (enclosingCell (b l).1) (enclosingCell y)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [h3]
    nlinarith
  have hsumg : ∑ b ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F), ∏ l, g l (b l) ≤ Cr ^ k := by
    rw [← Finset.prod_univ_sum]
    calc ∏ l, ∑ β ∈ fineBonds F, g l β ≤ ∏ _l : Fin k, Cr :=
          Finset.prod_le_prod (fun l _ => Finset.sum_nonneg fun β _ => (Real.exp_pos _).le)
            fun l _ => hsum
      _ = _ := by simp
  calc _ ≤ ∑ b ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F),
        Real.exp (δ * F.blockSide) * ∏ l, g l (b l) := Finset.sum_le_sum fun b _ => hpt b
    _ = Real.exp (δ * F.blockSide) *
        ∑ b ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F), ∏ l, g l (b l) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsumg (Real.exp_pos _).le
theorem inv_torusDecayFactor_le_of_far {F : BlockFrame} {k : ℕ} {δ R : ℝ} {y : F.Site F.depth}
    (hδ : 0 ≤ δ)
    (hls : ∀ x y : F.Site F.depth,
      F.blockSide * cellSupDist (enclosingCell x) (enclosingCell y) ≤ siteSupDist x y + F.blockSide)
    (hsite : ∀ x y : F.Site F.depth, siteSupDist x y = siteSupDist y x)
    (b : Fin k → F.Site F.depth × Fin 4) (l : Fin k)
    (hfar : R < 4 * cellSupDist (enclosingCell (b l).1) (enclosingCell y)) :
    (torusDecayFactor F.blockSide δ (bondSpan y b))⁻¹ ≤
      Real.exp (-(δ * (F.blockSide * (R / 4 - 1)))) := by
  refine (inv_torusDecayFactor_le_exp F.blockSide _).trans ?_
  apply Real.exp_le_exp.2
  have hu : (F.blockSide : ℝ) * cellSupDist (enclosingCell (b l).1) (enclosingCell y) ≤
      bondSpan y b + F.blockSide := by
    exact_mod_cast cellSupDist_le_bondSpan b l hls hsite
  have h1 : (F.blockSide : ℝ) * (R / 4) ≤
      (F.blockSide : ℝ) * cellSupDist (enclosingCell (b l).1) (enclosingCell y) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have h2 : (F.blockSide : ℝ) * (R / 4 - 1) ≤ bondSpan y b := by nlinarith
  have := mul_le_mul_of_nonneg_left h2 hδ
  linarith
theorem vecCons_nil_eq_const {α : Type*} (c : α) : (![c] : Fin 1 → α) = fun _ => c := by
  funext i
  fin_cases i
  rfl
theorem re_mul_self_of_norm_eq_one {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    ((X : ℍ[ℝ]) * (X : ℍ[ℝ])).re = -1 := by
  have hre : (X : ℍ[ℝ]).re = 0 := X.2
  have h1 : Quaternion.normSq (X : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self]
    have : ‖(X : ℍ[ℝ])‖ = 1 := hX
    rw [this]
    norm_num
  rw [Quaternion.normSq_def'] at h1
  simp only [Quaternion.re_mul, hre]
  nlinarith
theorem re_mul_smul_eq_of_norm_eq_one {D X : imaginaryQuaternions} {r : ℝ} (hX : ‖X‖ = 1)
    (hD : D = r • X) :
    (-((D : ℍ[ℝ]) * (X : ℍ[ℝ])).re) • X = D := by
  subst hD
  have h1 : (((r • X : imaginaryQuaternions) : ℍ[ℝ]) * (X : ℍ[ℝ])).re =
      r * ((X : ℍ[ℝ]) * (X : ℍ[ℝ])).re := by
    rw [Submodule.coe_smul, smul_mul_assoc]
    rfl
  rw [h1, re_mul_self_of_norm_eq_one hX]
  congr 1
  ring
theorem norm_interpolatedFrame_deriv_sub_le {F : BlockFrame} {s a ρA B : ℝ} {m k : ℕ}
    {d : F.Site F.depth × Fin 4}
    {V : F.GaugeField F.top} {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h₁ : IsBondAnalyticAt (stepFrame true a ρA m d) V) (h₂ : IsBondAnalyticAt (stepFrame false a ρA m d) V)
    (hb : ‖bondDeriv (frameGap a ρA m d) V c X‖ ≤ B) :
    ‖bondDeriv (interpolatedFrame s a ρA m d) V c X - bondDeriv (stepFrame true a ρA m d) V c X‖ ≤ B := by
  have c₁ : ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
      stepFrame true a ρA m d (leftTranslate (bondSpread c X τ) V)) 0 :=
    (h₁ k c X).contDiffAt
  have c₂ : ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
      stepFrame false a ρA m d (leftTranslate (bondSpread c X τ) V)) 0 :=
    (h₂ k c X).contDiffAt
  have cd : ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
      frameGap a ρA m d (leftTranslate (bondSpread c X τ) V)) 0 :=
    c₂.sub c₁
  have hfun : (fun τ : Fin k → ℝ => interpolatedFrame s a ρA m d (leftTranslate (bondSpread c X τ) V)) =
      (fun τ => stepFrame true a ρA m d (leftTranslate (bondSpread c X τ) V)) +
        fun τ => s • frameGap a ρA m d (leftTranslate (bondSpread c X τ) V) := by
    funext τ
    simp only [interpolatedFrame, frameGap, Pi.add_apply]
    module
  have cd' : ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
      s • frameGap a ρA m d (leftTranslate (bondSpread c X τ) V)) 0 := cd.const_smul s
  have hE : bondDeriv (interpolatedFrame s a ρA m d) V c X =
      bondDeriv (stepFrame true a ρA m d) V c X + s • bondDeriv (frameGap a ρA m d) V c X := by
    simp only [bondDeriv]
    rw [hfun, iteratedFDeriv_add_apply c₁ cd', iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := s) cd]
    rfl
  rw [hE, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0]
  calc s * _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
    _ ≤ B := by rw [one_mul]; exact hb
open Classical in
theorem norm_bondResponse_sub_flat_le {F : BlockFrame} {s a ρA ε₁ ε₂ : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    {c : F.Site F.top × Fin 4} {X : imaginaryQuaternions} {x : F.Site F.depth} {i : Fin 4} (hX : ‖X‖ = 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h₁ : IsBondAnalyticAt (stepFrame true a ρA m (x, i)) V)
    (h₂ : IsBondAnalyticAt (stepFrame false a ρA m (x, i)) V)
    (hdiff : ‖bondDeriv (frameGap a ρA m (x, i)) V ![c] ![X]‖ ≤ ε₂)
    (hresp : ‖bondDeriv (torusCoordinate a ρA (x, i)) V ![c] ![X] -
      bondDeriv (torusCoordinate a ρA (x, i)) (uniformField F F.top) ![c] ![X]‖ ≤ ε₁)
    (hsc : ∃ r : ℝ, bondDeriv (torusCoordinate a ρA (x, i)) (uniformField F F.top) ![c] ![X] = r • X) :
    ‖bondResponse s a ρA m V c X x i - flatMinimizerResponse a ρA c X x i • X‖ ≤ ε₁ + ε₂ := by
  obtain ⟨r, hr⟩ := hsc
  set D₁ := bondDeriv (torusCoordinate a ρA (x, i)) (uniformField F F.top) ![c] ![X] with hD₁
  have hread := re_mul_smul_eq_of_norm_eq_one hX hr
  have hnear := norm_interpolatedFrame_deriv_sub_le hs0 hs1 h₁ h₂ hdiff
  have hwhole : (stepFrame true a ρA m (x, i)) = torusCoordinate a ρA (x, i) := by
    funext V'
    simp [stepFrame, torusCoordinate]
  rw [hwhole] at hnear
  have hcond : (IsCrossingBond (x, i) ∧ c = (enclosingCell x, i)) ↔
      (IsCrossingBond (x, i) ∧ enclosingCell x = c.1 ∧ i = c.2) := by
    constructor
    · rintro ⟨h1, rfl⟩
      exact ⟨h1, rfl, rfl⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, Prod.ext h2.symm h3.symm⟩
  have hflat : flatMinimizerResponse a ρA c X x i • X = D₁ +
      (if IsCrossingBond (x, i) ∧ c = (enclosingCell x, i) then X else 0) := by
    simp only [flatMinimizerResponse, add_smul]
    rw [hread]
    congr 1
    by_cases h : IsCrossingBond (x, i) ∧ c = (enclosingCell x, i)
    · rw [if_pos h, if_pos (hcond.1 h), one_smul]
    · rw [if_neg h, if_neg (fun e => h (hcond.2 e)), zero_smul]
  rw [hflat, bondResponse, ← vecCons_nil_eq_const c, ← vecCons_nil_eq_const X]
  rw [add_sub_add_right_eq_sub]
  calc _ = ‖(bondDeriv (interpolatedFrame s a ρA m (x, i)) V ![c] ![X] -
        bondDeriv (torusCoordinate a ρA (x, i)) V ![c] ![X]) +
        (bondDeriv (torusCoordinate a ρA (x, i)) V ![c] ![X] - D₁)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (by linarith)
theorem iteratedFDeriv_finset_sum_apply_zero {k : ℕ} {ι : Type} (u : Finset ι) (g : ι → (Fin k → ℝ) → ℝ)
    (hg : ∀ y ∈ u, ContDiffAt ℝ k (g y) 0) :
    iteratedFDeriv ℝ k (fun τ => ∑ y ∈ u, g y τ) 0 = ∑ y ∈ u, iteratedFDeriv ℝ k (g y) 0 := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u ha ih =>
    have hfun : (fun τ => ∑ y ∈ insert a u, g y τ) = g a + fun τ => ∑ y ∈ u, g y τ := by
      funext τ
      simp [Finset.sum_insert ha]
    have hu : ContDiffAt ℝ k (fun τ => ∑ y ∈ u, g y τ) 0 :=
      ContDiffAt.sum fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [hfun, iteratedFDeriv_add_apply (hg a (Finset.mem_insert_self _ _)) hu,
      ih fun y hy => hg y (Finset.mem_insert_of_mem hy), Finset.sum_insert ha]
structure AxialGaugedMotion {F : BlockFrame} {k : ℕ} (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (α : (Fin k → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (y : F.Site F.depth) (Wf : Fin k → LevelForm F F.depth) (M : ℕ → ℝ) (Cw ε : ℝ)
    (Nr : F.Site F.depth × Fin 4 → Prop)
    (α' : (Fin k → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (ψ : Fin k → F.Site F.depth → imaginaryQuaternions) (ω : F.Site F.depth × Fin 4 → Fin k → ℝ) : Prop where
  at_zero : ∀ x b, α' 0 x b = 0
  smooth : ∀ x b, ContDiffAt ℝ k (fun τ => α' τ x b) 0
  gauge_eq : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), _root_.YangMills.Construction.BlockAverages.gaugeTransform (gaugeExponential ψ τ)
    (leftTranslate (α τ) (interpolatedField s a ρA m V η)) =
      leftTranslate (α' τ) (interpolatedField s a ρA m V η)
  weight_nonneg : ∀ β l, 0 ≤ ω β l
  component_le : ∀ (q : ℕ) (e' : Fin q → Fin k) (β : F.Site F.depth × Fin 4) (l : Fin q), q ≤ k →
    ‖motionComponent α' e' β.1 β.2‖ ≤ M q * ω β (e' l)
  weight_sum_le : ∀ l, ∑ β ∈ fineBonds F, ω β l ≤ Cw
  first_order_le : ∀ (l : Fin k) (β : F.Site F.depth × Fin 4), Nr β →
    ‖motionComponent α' (fun _ : Fin 1 => l) β.1 β.2‖ ≤
      |localAxialGauge (Real.sqrt F.blockSide) y (Wf l) β.1 β.2| + ε
theorem abs_interpolatedBlockExpansion_deriv_le {F : BlockFrame} {L n₀ k m : ℕ}
    {σ δ s a ρA Cw Cg Ay ε γ Am : ℝ} {e : ℕ → ℝ}
    {f : LocalFamily} {V : F.GaugeField F.top} {η : StepVariable (finiteCells F)} {Y : F.Cell}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    (hFL : F.blockSide = L) (hexp : expansionAlongMotionStatement) (hk : 1 ≤ k)
    (hfam : HasBoundedDerivatives L F.depth n₀ σ δ k e f) (hlow : IsCubicTorusAbove L F.depth n₀ F)
    (he : ∀ j, 0 ≤ e j) (hδ : 0 ≤ δ) (hper : ∀ i, F.period F.depth i ≠ 0) (hT : ∀ b, b ∈ fineBonds F)
    (hcold0 : IsSmallCurvature σ (interpolatedField s a ρA m V η))
    (hcoldτ : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ),
      IsSmallCurvature σ (interpolatedField s a ρA m (leftTranslate (bondSpread c X τ) V) η))
    (α : (Fin k → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (hαe : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), interpolatedField s a ρA m (leftTranslate (bondSpread c X τ) V) η =
      leftTranslate (α τ) (interpolatedField s a ρA m V η))
    (hsmooth : ∀ y, ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
      interpolatedExpansion s a ρA m f y η (leftTranslate (bondSpread c X τ) V)) 0)
    (Wf : Fin k → LevelForm F F.depth) (M : ℕ → ℝ) (Nr : F.Site F.depth → F.Site F.depth × Fin 4 → Prop)
    (hM : ∀ q, 0 ≤ M q) (hCw : 0 ≤ Cw) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hAm : 0 ≤ Am) (hγ : 0 ≤ γ)
    (hCg0 : 0 ≤ Cg)
    (hAy : ((blockFineSites Y).card : ℝ) ≤ Ay)
    (hgauged : ∀ y ∈ blockFineSites Y, ∃ α' ψ ω,
      AxialGaugedMotion s a ρA m V η α y Wf M Cw ε (Nr y) α' ψ ω)
    (hAmax : ∀ y (l : Fin k) (β : F.Site F.depth × Fin 4),
      |localAxialGauge (Real.sqrt F.blockSide) y (Wf l) β.1 β.2| ≤ Am)
    (hCg : ∀ y ∈ blockFineSites Y, ∑ b ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F),
      (torusDecayFactor L δ (bondSpan y b))⁻¹ ≤ Cg)
    (hfar : ∀ y ∈ blockFineSites Y, ∀ b : Fin k → F.Site F.depth × Fin 4, (∃ l, ¬ Nr y (b l)) →
      (torusDecayFactor L δ (bondSpan y b))⁻¹ ≤ γ) :
    |bondDeriv (interpolatedBlockExpansion s a ρA m f Y η) V c X| ≤
      e k * (flatResponseSum δ Y Wf +
          Ay * (ε * (2 * (Am + 1)) ^ k * Cg + γ * (M 1 * Cw) ^ k)) +
        Ay * (∑ c' : OrderedFinpartition k, ∏ m', (M (c'.partSize m') * Cw)) *
          runningMax e (k - 1) := by
  classical
  subst hFL
  have hlE : ∀ p, 0 ≤ runningMax e p := fun p => by
    induction p with
    | zero => exact le_rfl
    | succ p ih => exact ih.trans (le_max_left _ _)
  set Cnon := ∑ c' : OrderedFinpartition k, ∏ m', (M (c'.partSize m') * Cw) with hCnon
  have hCnon0 : 0 ≤ Cnon := Finset.sum_nonneg fun c' _ =>
    Finset.prod_nonneg fun m' _ => mul_nonneg (hM _) hCw
  set E₁ := ε * (2 * (Am + 1)) ^ k * Cg + γ * (M 1 * Cw) ^ k with hE₁
  have hrow : ∀ y ∈ blockFineSites Y, |bondDeriv (interpolatedExpansion s a ρA m f y η) V c X| ≤
      e k * (∑ b ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F),
          (torusDecayFactor F.blockSide δ (bondSpan y b))⁻¹ *
            ∏ i, |localAxialGauge (Real.sqrt F.blockSide) y (Wf i) (b i).1 (b i).2| + E₁) +
        Cnon * runningMax e (k - 1) := by
    intro y hy
    obtain ⟨α', ψ, ω, hg⟩ := hgauged y hy
    have h1 := interpolatedExpansion_deriv_le (y := y) hexp hk hfam hlow he hδ hper hT hcold0 hcoldτ α α' ψ hαe
      hg.at_zero hg.smooth hg.gauge_eq M ω hM hCw hg.weight_nonneg hg.component_le hg.weight_sum_le
    refine h1.trans (add_le_add (mul_le_mul_of_nonneg_left ?_ (he k)) le_rfl)
    refine (sum_mul_prod_le_of_near (fineBonds F) (fun b => (torusDecayFactor F.blockSide δ (bondSpan y b))⁻¹)
      (fun l β => ‖motionComponent α' (fun _ : Fin 1 => l) β.1 β.2‖)
      (fun l β => |localAxialGauge (Real.sqrt F.blockSide) y (Wf l) β.1 β.2|)
      (fun l β => M 1 * ω β l) (Nr y) hε hε1 hAm (mul_nonneg (hM 1) hCw)
      (fun b => inv_nonneg.2 (le_trans zero_le_one
        (one_le_torusDecayFactor F.blockSide hδ (Nat.cast_nonneg _))))
      (fun l β => norm_nonneg _) (fun l β => abs_nonneg _) (fun l β => hAmax y l β)
      (fun l β h => hg.first_order_le l β h)
      (fun l β => hg.component_le 1 (fun _ => l) β 0 hk) (hCg y hy)
      (fun l => by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hg.weight_sum_le l) (hM 1))
      (fun b hb => hfar y hy b hb) hγ).trans (le_of_eq ?_)
    rw [hE₁]
    ring
  have hE0 : 0 ≤ E₁ :=
    add_nonneg (mul_nonneg (mul_nonneg hε (by positivity)) hCg0)
      (mul_nonneg hγ (pow_nonneg (mul_nonneg (hM 1) hCw) _))
  have hfun : (fun τ : Fin k → ℝ =>
      interpolatedBlockExpansion s a ρA m f Y η (leftTranslate (bondSpread c X τ) V)) =
      fun τ => ∑ y ∈ blockFineSites Y, interpolatedExpansion s a ρA m f y η (leftTranslate (bondSpread c X τ) V) := rfl
  have hsum := iteratedFDeriv_finset_sum_apply_zero (blockFineSites Y)
    (fun y τ => interpolatedExpansion s a ρA m f y η (leftTranslate (bondSpread c X τ) V)) (fun y _ => hsmooth y)
  have hd1 : bondDeriv (interpolatedBlockExpansion s a ρA m f Y η) V c X =
      ∑ y ∈ blockFineSites Y, bondDeriv (interpolatedExpansion s a ρA m f y η) V c X := by
    simp only [bondDeriv]
    rw [hfun, hsum, _root_.sum_apply]
  rw [hd1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hrow).trans ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hsA : (∑ y ∈ blockFineSites Y, ∑ b ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F),
      (torusDecayFactor F.blockSide δ (bondSpan y b))⁻¹ *
        ∏ i, |localAxialGauge (Real.sqrt F.blockSide) y (Wf i) (b i).1 (b i).2|) =
      flatResponseSum δ Y Wf := rfl
  rw [hsA]
  have h1 := mul_le_mul_of_nonneg_right hAy hE0
  have h2 := mul_le_mul_of_nonneg_right hAy (mul_nonneg hCnon0 (hlE (k - 1)))
  have h3 := mul_le_mul_of_nonneg_left (add_le_add (le_refl (flatResponseSum δ Y Wf)) h1) (he k)
  nlinarith
def axialBondWeight {F : BlockFrame} {k : ℕ} (r : ℝ) (y : F.Site F.depth) (c : Fin k → F.Site F.top × Fin 4)
    (β : F.Site F.depth × Fin 4) (l : Fin k) : ℝ :=
  min 1 (Real.exp (-(r * cellSupDist (enclosingCell β.1) (c l).1)) +
    Real.exp r * Real.exp (-(r * cellSupDist (enclosingCell β.1) (enclosingCell y))))
theorem axialBondWeight_nonneg {F : BlockFrame} {k : ℕ} (r : ℝ) (y : F.Site F.depth)
    (c : Fin k → F.Site F.top × Fin 4) (β : F.Site F.depth × Fin 4) (l : Fin k) :
    0 ≤ axialBondWeight r y c β l :=
  le_min zero_le_one (add_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
theorem axialBondWeight_eq_one {F : BlockFrame} {k : ℕ} {r : ℝ} {y : F.Site F.depth}
    {c : Fin k → F.Site F.top × Fin 4} {β : F.Site F.depth × Fin 4} (l : Fin k) (hr : 0 ≤ r)
    (h : cellSupDist (enclosingCell β.1) (enclosingCell y) ≤ 1) : axialBondWeight r y c β l = 1 := by
  refine min_eq_left ?_
  have h1 : (cellSupDist (enclosingCell β.1) (enclosingCell y) : ℝ) ≤ 1 := by exact_mod_cast h
  have h2 : (1 : ℝ) ≤ Real.exp r * Real.exp (-(r * cellSupDist (enclosingCell β.1) (enclosingCell y))) := by
    rw [← Real.exp_add]
    apply Real.one_le_exp
    nlinarith
  linarith [Real.exp_pos (-(r * cellSupDist (enclosingCell β.1) (c l).1))]
theorem exp_le_axialBondWeight {F : BlockFrame} {k : ℕ} {r : ℝ} (y : F.Site F.depth)
    (c : Fin k → F.Site F.top × Fin 4) (β : F.Site F.depth × Fin 4) (l : Fin k) (hr : 0 ≤ r) :
    Real.exp (-(r * cellSupDist (enclosingCell β.1) (c l).1)) ≤ axialBondWeight r y c β l := by
  refine le_min ?_ ?_
  · exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hr (Nat.cast_nonneg _)))
  · have : 0 ≤ Real.exp r * Real.exp (-(r * cellSupDist (enclosingCell β.1) (enclosingCell y))) :=
      mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    linarith
theorem sum_axialBondWeight_le {F : BlockFrame} {k : ℕ} {r Cr : ℝ} (y : F.Site F.depth)
    (c : Fin k → F.Site F.top × Fin 4) (l : Fin k)
    (hsum : ∀ z : F.Cell, ∑ b ∈ fineBonds F, Real.exp (-(r * cellSupDist (enclosingCell b.1) z)) ≤ Cr) :
    ∑ β ∈ fineBonds F, axialBondWeight r y c β l ≤ Cr * (1 + Real.exp r) := by
  calc _ ≤ ∑ β ∈ fineBonds F, (Real.exp (-(r * cellSupDist (enclosingCell β.1) (c l).1)) +
        Real.exp r * Real.exp (-(r * cellSupDist (enclosingCell β.1) (enclosingCell y)))) :=
        Finset.sum_le_sum fun β _ => min_le_right _ _
    _ = _ + Real.exp r * _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ Cr + Real.exp r * Cr := add_le_add (hsum _)
        (mul_le_mul_of_nonneg_left (hsum _) (Real.exp_pos _).le)
    _ = _ := by ring
def topPerturbations {F : BlockFrame} {j : ℕ} (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions) : Fin j → Perturbation F :=
  fun q => Perturbation.top (c q) (X q)
theorem exists_axialGaugedMotion (hgau : gaugeAlongMotionStatement) {F : BlockFrame} {k m : ℕ}
    {s a ρA r Wm q ε₁ ε₃ Cw : ℝ}
    {A : ℕ → ℝ} {V : F.GaugeField F.top} {η : StepVariable (finiteCells F)}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} (hk6 : k ≤ 6)
    (hA : ∀ q, 0 ≤ A q) (hWm : 0 ≤ Wm) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (hper : ∀ i, F.period F.depth i ≠ 0) (hper1 : ∀ i, 1 < F.period F.depth i) (hX : AreUnitVectors X)
    (hL : 2 * Real.sqrt F.blockSide + 3 ≤ F.blockSide)
    (hls : ∀ x y : F.Site F.depth,
      F.blockSide * cellSupDist (enclosingCell x) (enclosingCell y) ≤ siteSupDist x y + F.blockSide)
    (htri : ∀ x y z : F.Site F.depth, siteSupDist x z ≤ siteSupDist x y + siteSupDist y z)
    (hcsum : ∀ z : F.Cell,
      ∑ b ∈ fineBonds F, Real.exp (-(r * cellSupDist (enclosingCell b.1) z)) * 1 ≤ Cw)
    (α : (Fin k → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (hα0 : ∀ x i, α 0 x i = 0) (hαs : ∀ x i, ContDiffAt ℝ (6 : ℕ) (fun τ => α τ x i) 0)
    (htree : ∀ x i, IsAxialTreeBond (x, i) → ∀ τ, α τ x i = 0)
    (hαp : ∀ (q : ℕ) (e' : Fin q → Fin k) (x : F.Site F.depth) (i : Fin 4) (l : Fin q), q ≤ 6 →
      ‖motionComponent α e' x i‖ ≤ A q * Real.exp (-(r * cellSupDist (enclosingCell x) (c (e' l)).1)))
    (hfirst : ∀ (l : Fin k) (x : F.Site F.depth) (i : Fin 4), ¬ IsAxialTreeBond (x, i) →
      ‖motionComponent α (fun _ : Fin 1 => l) x i - bondResponse s a ρA m V (c l) (X l) x i‖ ≤
        A 0 * ‖interpolatedCoords s a ρA m V η x i‖)
    (y : F.Site F.depth) (Wf : Fin k → LevelForm F F.depth) (hWf : ∀ l x i, |Wf l x i| ≤ Wm)
    (hWtree : ∀ l (b : F.Site F.depth × Fin 4), IsAxialTreeBond b → Wf l b.1 b.2 = 0)
    (Nr : F.Site F.depth × Fin 4 → Prop)
    (hq' : ∀ x i, ¬ IsAxialTreeBond (x, i) → ‖interpolatedCoords s a ρA m V η x i‖ ≤ q)
    (hnear1 : ∀ l (β : F.Site F.depth × Fin 4), Nr β → ¬ IsAxialTreeBond β →
      ‖bondResponse s a ρA m V (c l) (X l) β.1 β.2 - Wf l β.1 β.2 • X l‖ ≤ ε₁)
    (hnear3 : ∀ β : F.Site F.depth × Fin 4, Nr β →
      ‖((interpolatedField s a ρA m V η β.1 β.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε₃)
    (hε₃ : 0 ≤ ε₃) (hε₁ : 0 ≤ ε₁)
    {B : ℝ} (hB : B = 8 * Real.sqrt F.blockSide * Wm) (hB0 : 0 ≤ B) :
    ∃ α' ψ ω, AxialGaugedMotion s a ρA m V η α y Wf
      (Classical.choose (hgau 6 A B hA hB0)) (Cw * (1 + Real.exp r))
      (A 0 * q + ε₁ + 2 * ε₃ * B) Nr α' ψ ω := by
  classical
  have hspec := Classical.choose_spec (hgau 6 A B hA hB0)
  set M := Classical.choose (hgau 6 A B hA hB0) with hMd
  have hL0 : (0 : ℝ) < F.blockSide := by
    have := Real.sqrt_nonneg (F.blockSide : ℝ)
    linarith
  have hR : 0 < Real.sqrt F.blockSide := Real.sqrt_pos.2 hL0
  let φ : Fin k → F.Site F.depth → ℝ := fun l => axialGaugeFunction (Real.sqrt F.blockSide) y (Wf l)
  let ψ : Fin k → F.Site F.depth → imaginaryQuaternions := fun l z => -(φ l z • X l)
  let ω : F.Site F.depth × Fin 4 → Fin k → ℝ := axialBondWeight r y c
  have hφ : ∀ l z, |φ l z| ≤ B := fun l z => by
    rw [hB]
    exact abs_axialGaugeFunction_le hR (hWf l) z
  have hψn : ∀ l z, ‖ψ l z‖ = |φ l z| := fun l z => by
    simp only [ψ]
    rw [norm_neg, norm_smul, hX l, mul_one, Real.norm_eq_abs]
  have hnz : ∀ l z, φ l z ≠ 0 → (siteSupDist z y : ℝ) < 2 * Real.sqrt F.blockSide := by
    intro l z h
    by_contra hc
    push_neg at hc
    apply h
    simp only [φ, axialGaugeFunction]
    rw [smoothCutoff_eq_zero hR hc, zero_mul]
  have hψ : ∀ x i l, ‖ψ l x‖ ≤ B * ω (x, i) l ∧ ‖ψ l (x + unitStep F.depth i)‖ ≤ B * ω (x, i) l := by
    intro x i l
    have hω0 := axialBondWeight_nonneg r y c (x, i) l
    constructor
    · rw [hψn]
      by_cases h : φ l x = 0
      · rw [h, abs_zero]
        exact mul_nonneg hB0 hω0
      · have hc := cellSupDist_le_one_of_near (R := Real.sqrt F.blockSide) hls htri (by linarith)
          (by linarith [hnz l x h])
        have : ω (x, i) l = 1 := axialBondWeight_eq_one l hr hc
        rw [this, mul_one]
        exact hφ l x
    · rw [hψn]
      by_cases h : φ l (x + unitStep F.depth i) = 0
      · rw [h, abs_zero]
        exact mul_nonneg hB0 hω0
      · have h1 := hnz l _ h
        have h2 := htri x (x + unitStep F.depth i) y
        have h3 := siteSupDist_add_unitStep_le hper1 x i
        have h4 : (siteSupDist x y : ℝ) ≤ siteSupDist (x + unitStep F.depth i) y + 1 := by
          have : siteSupDist x y ≤ siteSupDist (x + unitStep F.depth i) y + 1 := by omega
          exact_mod_cast this
        have hc := cellSupDist_le_one_of_near (R := Real.sqrt F.blockSide) hls htri (by linarith) (by linarith)
        have : ω (x, i) l = 1 := axialBondWeight_eq_one l hr hc
        rw [this, mul_one]
        exact hφ l _
  obtain ⟨hM, hgau'⟩ := hspec
  obtain ⟨α', h0, hs, ht, hf, hp⟩ := hgau' F F.depth k (interpolatedField s a ρA m V η) α ψ
    (fun x i l => ω (x, i) l) hper hα0 hαs
    (fun x i l => axialBondWeight_nonneg r y c (x, i) l) (fun x i l => min_le_left _ _)
    (fun q' e' x i l hq' => (hαp q' e' x i l hq').trans
      (mul_le_mul_of_nonneg_left (exp_le_axialBondWeight y c (x, i) (e' l) hr) (hA q'))) hψ
  have hk' : ((k : ℕ) : WithTop ℕ∞) ≤ (6 : ℕ) := by exact_mod_cast hk6
  refine ⟨α', ψ, ω, ?_⟩
  refine { at_zero := h0, smooth := fun x b => (hs x b).of_le hk', gauge_eq := ht,
           weight_nonneg := fun β l => axialBondWeight_nonneg r y c β l,
           component_le := fun q' e' β l hq' => hp q' e' β.1 β.2 l (hq'.trans hk6),
           weight_sum_le := fun l => ?_, first_order_le := ?_ }
  · refine sum_axialBondWeight_le y c l fun z => ?_
    simpa using hcsum z
  · rintro l ⟨x, i⟩ hNr
    have hfo := hf (by norm_num) l x i
    have hb := norm_gauged_first_order_le (Wv := Wf l x i) (φ₁ := φ l x)
      (φ₂ := φ l (x + unitStep F.depth i))
      (Z := motionComponent α (fun _ : Fin 1 => l) x i) (X := X l)
      (Zg := motionComponent α' (fun _ : Fin 1 => l) x i) (interpolatedField s a ρA m V η x i) hfo (hX l)
    have hA0 := hA 0
    have hZ : ‖motionComponent α (fun _ : Fin 1 => l) x i - Wf l x i • X l‖ ≤ A 0 * q + ε₁ := by
      by_cases htb : IsAxialTreeBond (x, i)
      · have hz : (fun τ => α τ x i) = fun _ => 0 := funext fun τ => htree x i htb τ
        have h1 : motionComponent α (fun _ : Fin 1 => l) x i = 0 := by
          simp only [motionComponent]
          rw [hz, iteratedFDeriv_const_of_ne (by norm_num)]
          rfl
        rw [h1, hWtree l (x, i) htb]
        simp only [zero_smul, sub_zero, norm_zero]
        exact add_nonneg (mul_nonneg hA0 hq) hε₁
      · calc _ = ‖(motionComponent α (fun _ : Fin 1 => l) x i - bondResponse s a ρA m V (c l) (X l) x i) +
              (bondResponse s a ρA m V (c l) (X l) x i - Wf l x i • X l)‖ := by
              rw [sub_add_sub_cancel]
          _ ≤ _ := (norm_add_le _ _).trans (add_le_add
              ((hfirst l x i htb).trans (mul_le_mul_of_nonneg_left (hq' x i htb) hA0))
              (hnear1 l (x, i) hNr htb))
    have hW₃ := hnear3 (x, i) hNr
    have hφ₂ := hφ l (x + unitStep F.depth i)
    have hlast : 2 * ‖((interpolatedField s a ρA m V η x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ *
        |φ l (x + unitStep F.depth i)| ≤ 2 * ε₃ * B := by
      have := mul_le_mul hW₃ hφ₂ (abs_nonneg _) hε₃
      nlinarith
    have hid : Wf l x i + (φ l (x + unitStep F.depth i) - φ l x) =
        localAxialGauge (Real.sqrt F.blockSide) y (Wf l) x i := rfl
    rw [hid] at hb
    show ‖motionComponent α' (fun _ : Fin 1 => l) x i‖ ≤ _
    linarith
theorem continuous_expUnit_comp {k : ℕ} (g : (Fin k → ℝ) → imaginaryQuaternions) (hg : Continuous g) :
    Continuous fun τ => expUnit (g τ) := by
  refine Continuous.subtype_mk ?_ _
  have hexp : Continuous fun q : ℍ[ℝ] => NormedSpace.exp q :=
    continuous_iff_continuousAt.2 fun q => (NormedSpace.exp_analytic (𝕂 := ℝ) q).continuousAt
  exact hexp.comp (continuous_subtype_val.comp hg)
theorem continuous_bondSpread {F : BlockFrame} {j k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (y : F.Site j) (i : Fin 4) : Continuous fun τ : Fin k → ℝ => bondSpread c X τ y i := by
  unfold bondSpread
  refine continuous_finsetSum _ fun l _ => ?_
  split_ifs
  · exact (continuous_apply l).smul continuous_const
  · exact continuous_const
theorem continuous_linkValue {F : BlockFrame} {j k : ℕ} (Φ : (Fin k → ℝ) → F.GaugeField j)
    (h : ∀ x i, Continuous fun τ => Φ τ x i) (x : F.Site j) (st : PathStep) :
    Continuous fun τ => linkValue (Φ τ) x st := by
  unfold linkValue
  split_ifs
  · exact h _ _
  · exact (h _ _).inv
theorem continuous_pathHolonomy {F : BlockFrame} {j k : ℕ} (Φ : (Fin k → ℝ) → F.GaugeField j)
    (h : ∀ x i, Continuous fun τ => Φ τ x i) (l : List PathStep) :
    ∀ x : F.Site j, Continuous fun τ => pathHolonomy (Φ τ) x l := by
  induction l with
  | nil =>
    intro x
    exact continuous_const
  | cons st r ih =>
    intro x
    exact (continuous_linkValue Φ h x st).mul (ih _)
theorem continuous_plaquetteDefect {F : BlockFrame} {j k : ℕ} (Φ : (Fin k → ℝ) → F.GaugeField j)
    (h : ∀ x i, Continuous fun τ => Φ τ x i) (p : F.Site j × Fin 4 × Fin 4) :
    Continuous fun τ => plaquetteDefect (Φ τ) p := by
  unfold plaquetteDefect plaquetteHolonomy
  exact ((continuous_subtype_val.comp (continuous_pathHolonomy Φ h _ _)).sub continuous_const).norm
theorem leftTranslate_bondSpread_zero {F : BlockFrame} {j k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (V : F.GaugeField j) : leftTranslate (bondSpread c X 0) V = V := by apply _root_.YangMills.SharedProofs.p1939 <;> assumption
theorem eventually_isSmallCurvature_leftTranslate {F : BlockFrame} {j k : ℕ} {r : ℝ}
    (hper : ∀ i, F.period j i ≠ 0)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) {V : F.GaugeField j}
    (hV : IsSmallCurvature r V) :
    ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), IsSmallCurvature r (leftTranslate (bondSpread c X τ) V) := by
  have : ∀ i, NeZero (F.period j i) := fun i => ⟨hper i⟩
  have : Finite (F.Site j × Fin 4 × Fin 4) := inferInstance
  have hall : ∀ p : F.Site j × Fin 4 × Fin 4, ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ),
      p.2.1 < p.2.2 → plaquetteDefect (leftTranslate (bondSpread c X τ) V) p < r := by
    intro p
    by_cases hp : p.2.1 < p.2.2
    · have hc : Continuous fun τ : Fin k → ℝ => plaquetteDefect (leftTranslate (bondSpread c X τ) V) p :=
        continuous_plaquetteDefect _ (fun x i => ((continuous_expUnit_comp _ (continuous_bondSpread c X x i)).mul
          continuous_const)) p
      have h0 : plaquetteDefect (leftTranslate (bondSpread c X (0 : Fin k → ℝ)) V) p < r := by
        rw [leftTranslate_bondSpread_zero]
        exact hV p hp
      filter_upwards [(hc.tendsto 0).eventually (gt_mem_nhds h0)] with τ hτ _
      exact hτ
    · exact Filter.Eventually.of_forall fun τ h => absurd h hp
  filter_upwards [Filter.eventually_all.2 hall] with τ hτ p hp
  exact hτ p hp
theorem perturbedVariable_topPerturbations {F : BlockFrame} {j : ℕ} (η : StepVariable (finiteCells F))
    (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions) (τ : Fin j → ℝ) :
    perturbedVariable η (topPerturbations c X) τ = η := by
  simp [perturbedVariable, topPerturbations, Perturbation.variableDirection]
theorem card_blockFineSites_le {F : BlockFrame} {Cy : ℝ} (Y : F.Cell)
    (hall : ∀ y : F.Site F.depth, y ∈ sitesOfCells (finiteCells F) F.depth)
    (hcount : ∑ b ∈ fineBonds F, Real.exp (-(1 * (cellSupDist (enclosingCell b.1) Y : ℝ))) ≤ Cy) :
    ((blockFineSites Y).card : ℝ) ≤ Cy := by
  classical
  refine le_trans ?_ hcount
  have h2 : ∑ b ∈ (blockFineSites Y).image (fun y => (y, (0 : Fin 4))),
      Real.exp (-(1 * (cellSupDist (enclosingCell b.1) Y : ℝ))) ≤
      ∑ b ∈ fineBonds F, Real.exp (-(1 * (cellSupDist (enclosingCell b.1) Y : ℝ))) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => (Real.exp_pos _).le
    intro b hb'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb'
    simp [fineBonds, hall]
  refine le_trans ?_ h2
  rw [Finset.sum_image (fun y _ y' _ h => congrArg Prod.fst h)]
  have h3 : ∀ y ∈ blockFineSites Y, Real.exp (-(1 * (cellSupDist (enclosingCell y) Y : ℝ))) = 1 := by
    intro y hy
    rw [(Finset.mem_filter.1 hy).2]
    simp [cellSupDist]
  rw [Finset.sum_congr rfl h3]
  simp
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
theorem torusDecayFactor_mono (L : ℕ) {δ u v : ℝ} (hδ : 0 ≤ δ) (hu : 0 ≤ u) (huv : u ≤ v) :
    torusDecayFactor L δ u ≤ torusDecayFactor L δ v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionTransport.torusDecayFactor_mono <;> assumption
theorem rpow_neg_quarter_le {L : ℕ} (hL : 2 ^ 40 ≤ L) : (L : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 2⁻¹ ^ 10 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionTransport.rpow_neg_quarter_le <;> assumption
theorem two_sqrt_add_three_le {L : ℕ} (hL : 2 ^ 40 ≤ L) : 2 * Real.sqrt L + 3 ≤ L := by
  have h1 : ((2 : ℝ) ^ 40) ≤ L := by exact_mod_cast hL
  have h2 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have h3 : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (by positivity)
  have h4 : (8 : ℝ) ≤ Real.sqrt L := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  nlinarith
structure NearUniformBase (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (N R : ℕ) (Aq Bv ε₀ γ₀ del : ℝ) (L₁ : ℕ) : Prop where
  odd : Odd T.L
  L_ge : 2 ^ 40 ≤ T.L
  L₁_le : L₁ ≤ T.L
  holds : T.chainParams.Admissible T.a T.L
  a_ge : 1 ≤ T.a
  κ_pos : 0 < T.κ
  κ_le : 2 ^ 9 * T.κ ≤ T.chainParams.κ₂
  δ_le : T.decayRate ≤ del / 64
  σ_pos : 0 < T.σ
  Ct_nonneg : 0 ≤ T.Ct
  n₀_ge : 64 ≤ T.n₀
  ε₀_pos : 0 < ε₀
  ε₀_le : ε₀ ≤ 1
  γ₀_pos : 0 < γ₀
  R_ge : 4 * N + 8 ≤ R
  far : Real.exp (-(T.decayRate * (T.L * ((R : ℝ) / 4 - 1)))) ≤ γ₀
  side : 2 * R + 2 < T.n₀
  resp : ∀ (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell), IsBlockTorus T.L F →
    (∀ i, 2 * R + 2 < F.extent i) → IsSmallCurvature (5 / 4 * T.σ) V →
    IsNearUniformAbout (5 / 4 * T.σ) R V Y →
    ∀ (b : F.Site F.depth × Fin 4) (e : F.Site F.top × Fin 4) (X : imaginaryQuaternions),
      b ∈ chordBonds (finiteCells F) → 4 * cellSupDist Y (enclosingCell b.1) ≤ R →
      4 * cellSupDist Y e.1 ≤ R →
      ‖X‖ = 1 →
      ‖bondDeriv (torusCoordinate T.a T.chainParams.ρA b) V ![e] ![X] -
        bondDeriv (torusCoordinate T.a T.chainParams.ρA b) (uniformField F F.top) ![e] ![X]‖ ≤ ε₀ / 4
  small : Aq * (T.Ct * T.σ + T.ballRadius) +
    2 * ((T.Ct * T.σ + T.ballRadius) + 3 * ((R : ℝ) + 1) * (5 / 4 * T.σ)) * Bv ≤ ε₀ / 2
  floor : ∀ x : ℝ, T.coupling ≤ x → frameGapBound T (frameRadius x) ≤ ε₀ / 4
theorem AxialGaugedMotion.mono {F : BlockFrame} {k m : ℕ} {s a ρA Cw ε ε' : ℝ} {V : F.GaugeField F.top}
    {η : StepVariable (finiteCells F)}
    {α α' : (Fin k → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {y : F.Site F.depth} {Wf : Fin k → LevelForm F F.depth} {M : ℕ → ℝ}
    {Nr : F.Site F.depth × Fin 4 → Prop}
    {ψ : Fin k → F.Site F.depth → imaginaryQuaternions} {ω : F.Site F.depth × Fin 4 → Fin k → ℝ}
    (h : AxialGaugedMotion s a ρA m V η α y Wf M Cw ε Nr α' ψ ω) (hε : ε ≤ ε') :
    AxialGaugedMotion s a ρA m V η α y Wf M Cw ε' Nr α' ψ ω :=
  { h with first_order_le := fun l β hβ => (h.first_order_le l β hβ).trans (by linarith) }
set_option maxHeartbeats 2000000 in
theorem abs_interpolatedBlockExpansion_deriv_le_of_nearUniform (hexp : expansionAlongMotionStatement)
    (hgau : gaugeAlongMotionStatement)
    (hmot : motionAboveFrameStatement) (hbd : boundAlongPerturbationsStatement)
    (hcov : BlocksCoverLowerLevel) (hgeo : CubicTorusCellGeometry)
    (hfield : ChartedFieldNearOne) (hsc : FlatCoordinatesScalar)
    {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {Cz₀ : ℝ} {Cq Cz' : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
    (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k) (hKb : ∀ k, 16 ^ k * T.chainParams.Kk k ≤ K k)
    (Cgeo : ℝ → ℝ) (hCgeo : ∀ r, 0 < r → 0 < Cgeo r)
    (hgS : ∀ r, 0 < r → ∀ F : BlockFrame, Odd F.blockSide → IsLargeCubicTorus F → ∀ z : F.Cell,
      ∑ b ∈ fineBonds F, Real.exp (-(r * cellSupDist (enclosingCell b.1) z)) ≤
        Cgeo r * (F.blockSide : ℝ) ^ 4)
    {N R : ℕ} {ε₀ γ₀ del : ℝ} {L₁ : ℕ}
    (hb : NearUniformBase T N R (Classical.choose (hmot 6 K hK) 0) (8 * Real.sqrt T.L * (K 1 + 1))
      ε₀ γ₀ del L₁)
    (hdk : InterpolatedFrameDecay T Cz₀)
    (hfr : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFrameBoundsAt T Cq Cz' Cr t x)
    (hF3 : ∀ (F : BlockFrame) (δ : ℝ) (Y : F.Cell) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (B : Fin k → FormChain F) (W : Fin k → LevelForm F F.depth), 3 ≤ k → k ≤ 6 → Odd F.blockSide →
      L₁ ≤ F.blockSide →
      IsLargeCubicTorus F → 0 < δ → δ ≤ del / 64 → (∀ i, IsFlatChain T.a (c i) (B i)) →
      (∀ i, IsAxialResponse (c i) (B i) (W i)) →
      flatResponseSum δ Y W ≤ (F.blockSide : ℝ) ^ (-(1 / 4 : ℝ)) / torusDecayFactor F.blockSide δ (bondSpan Y c))
    (hflat : ∀ (F : BlockFrame) (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions), F.blockSide = T.L →
      IsLargeCubicTorus F → ‖X‖ = 1 →
      ∃ B : FormChain F, IsFlatChain T.a c B ∧
        IsAxialResponse c B (flatMinimizerResponse T.a T.chainParams.ρA c X))
    {x : ℝ} {t k : ℕ} {e : ℕ → ℝ} {f : LocalFamily} {F : BlockFrame} {V : F.GaugeField F.top} {s : ℝ}
    {η : StepVariable (finiteCells F)} {Y : F.Cell} {c : Fin k → F.Site F.top × Fin 4}
    {X : Fin k → imaginaryQuaternions}
    (hx : T.coupling ≤ x) (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (he : ∀ j, 0 ≤ e j)
    (hfam : HasBoundedDerivatives T.L t T.n₀ T.σ T.decayRate k e f) (htor : IsCubicTopTorus T.L t T.n₀ F)
    (hcold : IsSmallCurvature (5 / 4 * T.σ) V) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hη : ∀ b, ‖η b‖ ≤ T.ballRadius)
    (hX : AreUnitVectors X) (hN : bondSpan Y c < N) (hnf : IsNearUniformAbout (5 / 4 * T.σ) R V Y)
    {Cnk : ℝ} (hB0 : 0 ≤ 8 * Real.sqrt T.L * (K 1 + 1))
    (hbud : (Cgeo 1 * (T.L : ℝ) ^ 4) *
        (ε₀ * (2 * (((K 1 + 1) + 2 * (8 * Real.sqrt T.L * (K 1 + 1))) + 1)) ^ k *
            (Real.exp (T.decayRate * T.L) * (Cgeo (T.decayRate * T.L / 6) * (T.L : ℝ) ^ 4) ^ k) +
          γ₀ * (Classical.choose (hgau 6 (Classical.choose (hmot 6 K hK)) (8 * Real.sqrt T.L * (K 1 + 1))
              (Classical.choose_spec (hmot 6 K hK)).1 hB0) 1 *
            (Cgeo T.chainParams.κ₂ * (T.L : ℝ) ^ 4 * (1 + Real.exp T.chainParams.κ₂))) ^ k) ≤
      2⁻¹ ^ 10 / torusDecayFactor T.L T.decayRate N)
    (hCn : (Cgeo 1 * (T.L : ℝ) ^ 4) *
        (∑ c' : OrderedFinpartition k, ∏ m',
          (Classical.choose (hgau 6 (Classical.choose (hmot 6 K hK)) (8 * Real.sqrt T.L * (K 1 + 1))
              (Classical.choose_spec (hmot 6 K hK)).1 hB0) (c'.partSize m') *
            (Cgeo T.chainParams.κ₂ * (T.L : ℝ) ^ 4 * (1 + Real.exp T.chainParams.κ₂)))) *
        torusDecayFactor T.L T.decayRate N ≤ Cnk) :
    |bondDeriv (interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) f Y η) V c X| ≤
      (2⁻¹ ^ 9 * e k + Cnk * runningMax e (k - 1)) / torusDecayFactor T.L T.decayRate (bondSpan Y c) := by
  classical
  set A := Classical.choose (hmot 6 K hK) with hAd
  obtain ⟨hA, hmo⟩ := Classical.choose_spec (hmot 6 K hK)
  rw [← hAd] at hA hmo
  have hσ := hb.σ_pos
  have htor' := htor
  obtain ⟨hFL, htt, n, hside, hn⟩ := htor'
  subst htt
  have hL2 := hb.L_ge
  have hL0 : 0 < T.L := by omega
  have hn64 : 64 ≤ n := hb.n₀_ge.trans hn
  have hcub : IsLargeCubicTorus F := ⟨n, hn64, hside⟩
  have hlow : IsCubicTorusAbove T.L F.depth T.n₀ F :=
    ⟨hFL, rfl, n, hside, hn.trans (Nat.le_mul_of_pos_right n hL0)⟩
  have hodd : Odd F.blockSide := hFL ▸ hb.odd
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    rw [hside i]
    omega
  have hall := hcov F hodd hpos
  have hT : ∀ b : F.Site F.depth × Fin 4, b ∈ fineBonds F := fun b => by simp [fineBonds, hall]
  have hchart : ∀ d : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) :=
    fun d hd' => by
      simp [chordBonds, innerBonds, hall, hd']
  have hFL0 : 0 < F.blockSide := by rw [hFL]; exact hL0
  have hper1 : ∀ j i, 1 < F.period j i := fun j i => by
    simp only [BlockFrame.period]
    have h1 : 1 ≤ F.blockSide ^ (F.top - j) := Nat.one_le_pow _ _ hFL0
    have h2 : 64 ≤ F.extent i := by rw [hside i]; exact hn64
    nlinarith
  have hper : ∀ j i, F.period j i ≠ 0 := fun j i => by have := hper1 j i; omega
  obtain ⟨hsite, htriS, hsym, htriC, hls⟩ := hgeo.1 F hodd hcub
  set m := frameRadius x with hm
  have hκ := hb.κ_pos
  have hδ : 0 < T.decayRate := by
    show 0 < T.κ / 2 ^ 10
    positivity
  have hr : 0 < T.chainParams.κ₂ := by
    have := hb.κ_le
    nlinarith
  have hd0 := hdk x F.depth F V 0 hx htor hcold le_rfl zero_le_one
  have hd1 := hdk x F.depth F V 1 hx htor hcold zero_le_one le_rfl
  have hds := hdk x F.depth F V s hx htor hcold hs0 hs1
  have hfb0 : ∀ d : F.Site F.depth × Fin 4,
      interpolatedFrame 0 T.a T.chainParams.ρA m d = stepFrame true T.a T.chainParams.ρA m d := fun d => by
    funext V'
    simp [interpolatedFrame]
  have hfb1 : ∀ d : F.Site F.depth × Fin 4,
      interpolatedFrame 1 T.a T.chainParams.ρA m d = stepFrame false T.a T.chainParams.ρA m d := fun d => by
    funext V'
    simp [interpolatedFrame]
  have hone := (hfr F.depth x hx).one_torus F V s htor hcold hs0 hs1
  have hsm := hone.small
  have hnl := hone.near_minimizer
  have hcold0 : IsSmallCurvature T.σ (interpolatedField s T.a T.chainParams.ρA m V η) := fun q hq =>
    (hsm.small_curvature_nearby η hη q hq).trans_le (by linarith)
  have hcoldτ : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ),
      IsSmallCurvature T.σ (interpolatedField s T.a T.chainParams.ρA m (leftTranslate (bondSpread c X τ) V) η) :=
    (eventually_isSmallCurvature_leftTranslate (hper F.top) c X hcold).mono fun τ hτ q hq =>
      (((hfr F.depth x hx).one_torus F _ s htor hτ hs0 hs1).small.small_curvature_nearby η hη q hq).trans_le
        (by linarith)
  have hρ1 : T.chainParams.ρA ≤ 1 := hb.holds.classical.1.2.1
  set q : ℝ := T.Ct * T.σ + T.ballRadius with hqd
  have hρ0 : 0 ≤ T.ballRadius := by
    show 0 ≤ T.σ / 64
    positivity
  have hq0 : 0 ≤ q := add_nonneg (mul_nonneg hb.Ct_nonneg hσ.le) hρ0
  have habove : ∀ x' i, ¬ IsAxialTreeBond (x', i) →
      ‖interpolatedCoords s T.a T.chainParams.ρA m V η x' i‖ ≤ q ∧
        ‖interpolatedCoords s T.a T.chainParams.ρA m V η x' i‖ ≤ 1 := by
    intro x' i ht
    have hd := hchart _ ht
    have h1 : stepCoordinates η x' i = toImaginary (η ⟨(x', i), hd⟩) := by
      simp [stepCoordinates, hd]
    have h2 := hsm.norm_le _ hd
    have h3 := hsm.norm_add_le _ hd
    have h4 := hη ⟨(x', i), hd⟩
    have h5 : ‖interpolatedCoords s T.a T.chainParams.ρA m V η x' i‖ ≤
        ‖interpolatedFrame s T.a T.chainParams.ρA m (x', i) V‖ + ‖η ⟨(x', i), hd⟩‖ := by
      simp only [interpolatedCoords]
      refine (norm_add_le _ _).trans ?_
      rw [h1, norm_toImaginary]
    constructor
    · linarith
    · have : T.ballRadius = T.σ / 64 := rfl
      linarith
  have hsmall : ∀ x' i, ¬ IsAxialTreeBond (x', i) →
      ‖interpolatedCoords s T.a T.chainParams.ρA m V η x' i‖ ≤ 1 :=
    fun x' i ht => (habove x' i ht).2
  have hana : ∀ d ∈ chordBonds (finiteCells F),
      IsBondAnalyticAt (interpolatedFrame s T.a T.chainParams.ρA m d) V :=
    fun d h => (hds d h).2.1
  have hdec : ∀ d ∈ chordBonds (finiteCells F), ∀ (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4)
      (X' : Fin k' → imaginaryQuaternions), 1 ≤ k' → AreUnitVectors X' →
      ‖bondDeriv (interpolatedFrame s T.a T.chainParams.ρA m d) V c' X'‖ ≤
        K k' * Real.exp (-(T.chainParams.κ₂ * bondListDistance (enclosingCell d.1) c')) :=
    fun d h k' c' X' h1 hX' =>
      ((hds d h).2.2 k' c' X' h1 hX').trans
        (mul_le_mul_of_nonneg_right (hKb k') (Real.exp_pos _).le)
  have hunit : ∀ l, (topPerturbations c X l).IsUnit := fun l => hX l
  obtain ⟨α, hα0, hαs, htree, hαe, hαp, hfirst⟩ :=
    hmo F s T.a T.chainParams.ρA T.chainParams.κ₂ m k V η (topPerturbations c X) (hper F.depth) hr.le
      hchart hsmall hana hdec hunit
  have hαe' : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ),
      interpolatedField s T.a T.chainParams.ρA m (leftTranslate (bondSpread c X τ) V) η =
        leftTranslate (α τ) (interpolatedField s T.a T.chainParams.ρA m V η) := hαe.mono fun τ h => by
    rw [perturbedVariable_topPerturbations] at h
    exact h
  let Wf : Fin k → LevelForm F F.depth := fun l => flatMinimizerResponse T.a T.chainParams.ρA (c l) (X l)
  choose Bc hB1 hB2 using fun l => hflat F (c l) (X l) hFL hcub (hX l)
  have hS := hF3 F T.decayRate Y k c Bc Wf hk3 hk6 hodd (by rw [hFL]; exact hb.L₁_le) hcub hδ hb.δ_le hB1 hB2
  rw [hFL] at hS
  have hWtree : ∀ l (b : F.Site F.depth × Fin 4), IsAxialTreeBond b → Wf l b.1 b.2 = 0 := fun l b ht =>
    (hB2 l).vanishes_on_tree b ht
  have hflatcold : IsSmallCurvature (5 / 4 * T.σ) (uniformField F F.top) := fun q' _ => by
    have : plaquetteDefect (uniformField F F.top) q' = 0 := by
      simp [plaquetteDefect, plaquetteHolonomy, pathHolonomy, linkValue, uniformField]
    rw [this]
    positivity
  have hWm : ∀ l x' i, |Wf l x' i| ≤ K 1 + 1 := by
    intro l x' i
    by_cases ht : IsAxialTreeBond (x', i)
    · have := hWtree l (x', i) ht
      simp only at this
      rw [this, abs_zero]
      linarith [hK 1]
    · have hd := hchart _ ht
      have h1 := (hdk x F.depth F (uniformField F F.top) 0 hx htor hflatcold le_rfl zero_le_one _ hd).2.2 1
        ![c l] ![X l] le_rfl (fun q' => by
          have hq' : q' = 0 := Subsingleton.elim _ _
          subst hq'
          exact hX l)
      rw [hfb0] at h1
      have hw : stepFrame true T.a T.chainParams.ρA m (x', i) = torusCoordinate T.a T.chainParams.ρA (x', i) := by
        funext V'
        simp [stepFrame, torusCoordinate]
      rw [hw] at h1
      have h2 : ‖bondDeriv (torusCoordinate T.a T.chainParams.ρA (x', i)) (uniformField F F.top)
          ![c l] ![X l]‖ ≤ K 1 := by
        refine h1.trans ?_
        have h3 : Real.exp (-(T.chainParams.κ₂ * bondListDistance (enclosingCell (x', i).1) ![c l])) ≤ 1 :=
          Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hr.le (Nat.cast_nonneg _)))
        have h4 := hKb 1
        have h5 : 0 ≤ 16 ^ 1 * T.chainParams.Kk 1 := by
          have := hb.holds.classical.1.2.2.2.2.2.2.2 1
          positivity
        calc _ ≤ 16 ^ 1 * T.chainParams.Kk 1 * 1 := mul_le_mul_of_nonneg_left h3 h5
          _ ≤ K 1 := by linarith
      set D₁ := bondDeriv (torusCoordinate T.a T.chainParams.ρA (x', i)) (uniformField F F.top)
        ![c l] ![X l] with hD₁
      have hre : |((D₁ : ℍ[ℝ]) * (X l : ℍ[ℝ])).re| ≤ ‖D₁‖ := by
        refine (abs_re_le_norm _).trans ?_
        rw [norm_mul]
        have hX1 : ‖(X l : ℍ[ℝ])‖ = 1 := hX l
        rw [hX1, mul_one]
        rfl
      have hind : |(if IsCrossingBond (x', i) ∧ enclosingCell x' = (c l).1 ∧ i = (c l).2
          then (1 : ℝ) else 0)| ≤ 1 := by
        split_ifs <;> simp
      show |-((D₁ : ℍ[ℝ]) * (X l : ℍ[ℝ])).re +
        (if IsCrossingBond (x', i) ∧ enclosingCell x' = (c l).1 ∧ i = (c l).2 then 1 else 0)| ≤ _
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg]
      linarith
  have hsq : 2 * Real.sqrt F.blockSide + 3 ≤ F.blockSide := two_sqrt_add_three_le (by rw [hFL]; exact hL2)
  have hsideR : ∀ i, 2 * R + 2 < F.extent i := fun i => by
    rw [hside i]
    exact hb.side.trans_le hn
  have hWm0 : 0 ≤ K 1 + 1 := by linarith [hK 1]
  set ε₃ : ℝ := q + 3 * ((R : ℝ) + 1) * (5 / 4 * T.σ) with hε₃d
  have hε₃0 : 0 ≤ ε₃ := by positivity
  have hε₀ := hb.ε₀_pos
  have hε₁0 : 0 ≤ ε₀ / 4 + ε₀ / 4 := by positivity
  set Bv : ℝ := 8 * Real.sqrt T.L * (K 1 + 1) with hBv
  have hε' : A 0 * q + (ε₀ / 4 + ε₀ / 4) + 2 * ε₃ * Bv ≤ ε₀ := by
    have h : A 0 * q + 2 * ε₃ * Bv ≤ ε₀ / 2 := hb.small
    linarith
  have hcsum : ∀ z : F.Cell, ∑ b ∈ fineBonds F,
      Real.exp (-(T.chainParams.κ₂ * cellSupDist (enclosingCell b.1) z)) * 1 ≤
        Cgeo T.chainParams.κ₂ * (T.L : ℝ) ^ 4 := fun z => by
    have := hgS _ hr F hodd hcub z
    rw [hFL] at this
    simpa using this
  set M := Classical.choose (hgau 6 A Bv hA hB0) with hMd
  have hM : ∀ q', 0 ≤ M q' := (Classical.choose_spec (hgau 6 A Bv hA hB0)).1
  set Cw : ℝ := Cgeo T.chainParams.κ₂ * (T.L : ℝ) ^ 4 * (1 + Real.exp T.chainParams.κ₂) with hCwd
  have hCw0 : 0 ≤ Cw := by
    have := hCgeo _ hr
    positivity
  let Nr : F.Site F.depth → F.Site F.depth × Fin 4 → Prop :=
    fun y β => 4 * cellSupDist (enclosingCell β.1) (enclosingCell y) ≤ R
  have hGauged : ∀ y ∈ blockFineSites Y, ∃ α' ψ ω,
      AxialGaugedMotion s T.a T.chainParams.ρA m V η α y Wf M Cw ε₀ (Nr y) α' ψ ω := by
    intro y hy
    have hyY : enclosingCell y = Y := (Finset.mem_filter.1 hy).2
    have hnear1 : ∀ l (β : F.Site F.depth × Fin 4), Nr y β → ¬ IsAxialTreeBond β →
        ‖bondResponse s T.a T.chainParams.ρA m V (c l) (X l) β.1 β.2 - Wf l β.1 β.2 • X l‖ ≤
          ε₀ / 4 + ε₀ / 4 := by
      rintro l ⟨x', i⟩ hN' ht
      have hd := hchart _ ht
      have h1 : 4 * cellSupDist Y (enclosingCell x') ≤ R := by
        rw [hsym Y, ← hyY]
        exact hN'
      have h2 : 4 * cellSupDist Y (c l).1 ≤ R := by
        have h3 : cellSupDist Y (c l).1 ≤ bondSpan Y c :=
          le_max_of_le_left (Finset.le_sup (f := fun l : Fin k => siteSupDist Y (c l).1) (Finset.mem_univ l))
        have := hb.R_ge
        omega
      have hresp := hb.resp F V Y ⟨hFL, hcub⟩ hsideR hcold hnf (x', i) (c l) (X l) hd h1 h2 (hX l)
      have hdiff : ‖bondDeriv (frameGap T.a T.chainParams.ρA m (x', i)) V ![c l] ![X l]‖ ≤ ε₀ / 4 := by
        have h3 := hnl.deriv_decay (x', i) hd 1 ![c l] ![X l] le_rfl (by norm_num) (fun q' => by
          have hq' : q' = 0 := Subsingleton.elim _ _
          subst hq'
          exact hX l)
        set E := Real.exp (-(T.chainParams.δ₂ / 4 * bondListDistance (enclosingCell (x', i).1) ![c l]))
          with hE
        have hE0 : 0 < E := Real.exp_pos _
        have hE1 : E ≤ 1 := by
          have hδ₂ : 0 < T.chainParams.δ₂ := hb.holds.classical.1.2.2.2.1
          exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (by positivity) (Nat.cast_nonneg _)))
        have hg0 : 0 ≤ frameGapBound T m := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h3) hE0
        exact h3.trans ((mul_le_of_le_one_right hg0 hE1).trans (hb.floor x hx))
      have A1 : IsBondAnalyticAt (stepFrame true T.a T.chainParams.ρA m (x', i)) V := by
        have := (hd0 _ hd).2.1
        rwa [hfb0] at this
      have A2 : IsBondAnalyticAt (stepFrame false T.a T.chainParams.ρA m (x', i)) V := by
        have := (hd1 _ hd).2.1
        rwa [hfb1] at this
      exact norm_bondResponse_sub_flat_le (hX l) hs0 hs1 A1 A2 hdiff hresp
        ⟨_, (hsc T.a T.L T.chainParams hb.odd hb.holds F (x', i) (c l) (X l) ⟨hFL, hcub⟩ (hX l)).2⟩
    have hnear3 : ∀ β : F.Site F.depth × Fin 4, Nr y β →
        ‖((interpolatedField s T.a T.chainParams.ρA m V η β.1 β.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε₃ := by
      rintro ⟨x', i⟩ hN'
      have hd4 : 4 * cellSupDist (enclosingCell x') (enclosingCell y) ≤ R := hN'
      have hdR : cellSupDist Y (enclosingCell x') + 1 ≤ R := by
        rw [hsym Y, ← hyY]
        have := hb.R_ge
        omega
      have h := hfield F (interpolatedCoords s T.a T.chainParams.ρA m V η) V Y q (5 / 4 * T.σ) R (x', i)
        hsideR hq0 (by positivity) hnf (fun b' hb' => (habove b'.1 b'.2 hb').1) hdR
      refine h.trans ?_
      have h2 : ((cellSupDist Y (enclosingCell x') : ℕ) : ℝ) + 1 ≤ (R : ℝ) + 1 := by
        have : cellSupDist Y (enclosingCell x') ≤ R := by omega
        have h3 : ((cellSupDist Y (enclosingCell x') : ℕ) : ℝ) ≤ R := by exact_mod_cast this
        linarith
      have h3 : 0 ≤ 5 / 4 * T.σ := by positivity
      have h4 := mul_le_mul_of_nonneg_right h2 h3
      simp only [hε₃d]
      nlinarith
    obtain ⟨α', ψ, ω, hg⟩ := exists_axialGaugedMotion hgau (k := k) (m := m) (s := s) (a := T.a)
      (ρA := T.chainParams.ρA) (r := T.chainParams.κ₂) (Wm := K 1 + 1) (q := q) (ε₁ := ε₀ / 4 + ε₀ / 4)
      (ε₃ := ε₃)
      (Cw := Cgeo T.chainParams.κ₂ * (T.L : ℝ) ^ 4) (A := A) (V := V) (η := η) (c := c) (X := X)
      hk6 hA hWm0 hr.le hq0 (hper F.depth) (hper1 F.depth) hX hsq hls (htriS F.depth) hcsum α hα0 hαs htree
      (fun q' e' x' i l hq' => hαp q' e' x' i l hq')
      (fun l x' i ht => hfirst l (c l) (X l) x' i (by norm_num) rfl ht) y Wf hWm hWtree (Nr y)
      (fun x' i ht => (habove x' i ht).1) hnear1 hnear3 hε₃0 hε₁0 (B := Bv) (by rw [hBv, hFL]) hB0
    exact ⟨α', ψ, ω, hg.mono hε'⟩
  have hKbd : ∀ d ∈ chordBonds (finiteCells F), ∀ (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4)
      (X' : Fin k' → imaginaryQuaternions), 1 ≤ k' → AreUnitVectors X' →
      ‖bondDeriv (interpolatedFrame s T.a T.chainParams.ρA m d) V c' X'‖ ≤
        K k' * Real.exp (-(T.chainParams.κ₂ * bondListDistance (enclosingCell d.1) c')) := hdec
  obtain ⟨Cb, -, hU⟩ := hbd K T.chainParams.κ₂ T.κ T.L hK hκ hb.κ_le hb.odd hL2
  have hsmooth : ∀ y, ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
      interpolatedExpansion s T.a T.chainParams.ρA m f y η (leftTranslate (bondSpread c X τ) V)) 0 := by
    intro y
    have h1 := (hU F T.n₀ k k m T.σ s T.a T.chainParams.ρA e f V η (topPerturbations c X) y hFL hcub hlow
      hk6 he hfam hcold0 hsmall hana hKbd hunit).1
    have h2 : (fun τ : Fin k → ℝ =>
        interpolatedExpansion s T.a T.chainParams.ρA m f y η (leftTranslate (bondSpread c X τ) V)) =
        fun τ => subtractTrivial f F y
          (perturbedField s T.a T.chainParams.ρA m V η (topPerturbations c X) τ) := by
      funext τ
      simp only [interpolatedExpansion, perturbedField, perturbedVariable_topPerturbations]
      rfl
    rw [h2]
    exact h1
  have hR0 : 0 < Real.sqrt F.blockSide := Real.sqrt_pos.2 (by exact_mod_cast hFL0)
  set Am : ℝ := (K 1 + 1) + 2 * Bv with hAmd
  have hAm0 : 0 ≤ Am := by positivity
  have hAmax : ∀ y (l : Fin k) (β : F.Site F.depth × Fin 4),
      |localAxialGauge (Real.sqrt F.blockSide) y (Wf l) β.1 β.2| ≤ Am := by
    rintro y l ⟨x', i⟩
    have h1 := hWm l x' i
    have h2 := abs_axialGaugeFunction_le (y := y) hR0 (hWm l) (x' + unitStep F.depth i)
    have h3 := abs_axialGaugeFunction_le (y := y) hR0 (hWm l) x'
    have h4 : localAxialGauge (Real.sqrt F.blockSide) y (Wf l) x' i = Wf l x' i +
        (axialGaugeFunction (Real.sqrt F.blockSide) y (Wf l) (x' + unitStep F.depth i) -
          axialGaugeFunction (Real.sqrt F.blockSide) y (Wf l) x') := rfl
    show |localAxialGauge (Real.sqrt F.blockSide) y (Wf l) x' i| ≤ _
    rw [h4]
    have h5 : 8 * Real.sqrt F.blockSide * (K 1 + 1) = Bv := by rw [hBv, hFL]
    rw [h5] at h2 h3
    refine (abs_add_le _ _).trans ?_
    have h6 := abs_sub (axialGaugeFunction (Real.sqrt F.blockSide) y (Wf l) (x' + unitStep F.depth i))
      (axialGaugeFunction (Real.sqrt F.blockSide) y (Wf l) x')
    simp only [hAmd]
    linarith
  set Cr : ℝ := Cgeo (T.decayRate * T.L / 6) * (T.L : ℝ) ^ 4 with hCrd
  have hpos6 : 0 < T.decayRate * T.L / 6 := by
    have : (0 : ℝ) < T.L := by exact_mod_cast hL0
    positivity
  have hCr0 : 0 ≤ Cr := by
    have := hCgeo _ hpos6
    positivity
  set Cg : ℝ := Real.exp (T.decayRate * T.L) * Cr ^ k with hCgd
  have hCg0 : 0 ≤ Cg := by positivity
  have hCgy : ∀ y ∈ blockFineSites Y, ∑ b ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F),
      (torusDecayFactor T.L T.decayRate (bondSpan y b))⁻¹ ≤ Cg := by
    intro y _
    have h1 := hgS _ hpos6 F hodd hcub (enclosingCell y)
    rw [hFL] at h1
    have h2 := sum_inv_torusDecayFactor_le (F := F) (k := k) (δ := T.decayRate) (Cr := Cr) (y := y) hδ.le hk6
      hls (hsite F.depth) (by rw [hFL]; exact h1)
    rw [hFL] at h2
    exact h2
  have hfar : ∀ y ∈ blockFineSites Y, ∀ b : Fin k → F.Site F.depth × Fin 4, (∃ l, ¬ Nr y (b l)) →
      (torusDecayFactor T.L T.decayRate (bondSpan y b))⁻¹ ≤ γ₀ := by
    rintro y _ b ⟨l, hl⟩
    have h1 : (R : ℝ) < 4 * cellSupDist (enclosingCell (b l).1) (enclosingCell y) := by
      have : R < 4 * cellSupDist (enclosingCell (b l).1) (enclosingCell y) := not_le.1 hl
      exact_mod_cast this
    have h2 := inv_torusDecayFactor_le_of_far (F := F) (δ := T.decayRate) (R := (R : ℝ)) (y := y) hδ.le hls
      (hsite F.depth) b l h1
    rw [hFL] at h2
    exact h2.trans hb.far
  have hAy : ((blockFineSites Y).card : ℝ) ≤ Cgeo 1 * (T.L : ℝ) ^ 4 := by
    refine card_blockFineSites_le Y hall ?_
    have := hgS 1 one_pos F hodd hcub Y
    rw [hFL] at this
    exact this
  have hbb := abs_interpolatedBlockExpansion_deriv_le (L := T.L) (n₀ := T.n₀) (σ := T.σ) (δ := T.decayRate)
    (s := s) (a := T.a)
    (ρA := T.chainParams.ρA) (Cw := Cw) (Cg := Cg) (Ay := Cgeo 1 * (T.L : ℝ) ^ 4) (ε := ε₀) (γ := γ₀)
    (Am := Am) (e := e) (f := f) (V := V) (η := η) (Y := Y) (c := c) (X := X) (m := m) hFL hexp
    (by omega) hfam hlow he hδ.le (hper F.depth) hT hcold0 hcoldτ α hαe' hsmooth Wf M Nr hM hCw0 hε₀.le
    hb.ε₀_le hAm0 hb.γ₀_pos.le hCg0 hAy hGauged hAmax hCgy hfar
  set G := torusDecayFactor T.L T.decayRate (bondSpan Y c) with hG
  set GN := torusDecayFactor T.L T.decayRate N with hGN
  have hG1 : 1 ≤ G := one_le_torusDecayFactor _ hδ.le (Nat.cast_nonneg _)
  have hG0 : 0 < G := by linarith
  have hGle : G ≤ GN := torusDecayFactor_mono _ hδ.le (Nat.cast_nonneg _) (by exact_mod_cast hN.le)
  have hS' : flatResponseSum T.decayRate Y Wf ≤ 2⁻¹ ^ 10 / G :=
    hS.trans (div_le_div_of_nonneg_right (rpow_neg_quarter_le hL2) hG0.le)
  have hbud' := hbud.trans (div_le_div_of_nonneg_left (by positivity) hG0 hGle)
  have hAy0 : 0 ≤ Cgeo 1 * (T.L : ℝ) ^ 4 := by
    have := hCgeo 1 one_pos
    positivity
  have hCnon0 : 0 ≤ ∑ c' : OrderedFinpartition k, ∏ m', (M (c'.partSize m') * Cw) :=
    Finset.sum_nonneg fun c' _ => Finset.prod_nonneg fun m' _ => mul_nonneg (hM _) hCw0
  have hCn' : (Cgeo 1 * (T.L : ℝ) ^ 4) * (∑ c' : OrderedFinpartition k, ∏ m', (M (c'.partSize m') * Cw)) ≤
      Cnk / G := by
    rw [le_div_iff₀ hG0]
    exact (mul_le_mul_of_nonneg_left hGle (mul_nonneg hAy0 hCnon0)).trans hCn
  have hlE : 0 ≤ runningMax e (k - 1) := by
    have : ∀ p, 0 ≤ runningMax e p := fun p => by
      induction p with
      | zero => exact le_rfl
      | succ p ih => exact ih.trans (le_max_left _ _)
    exact this _
  refine hbb.trans ?_
  have h1 := mul_le_mul_of_nonneg_left (add_le_add hS' hbud') (he k)
  have h2 := mul_le_mul_of_nonneg_right hCn' hlE
  have h3 : e k * (2⁻¹ ^ 10 / G + 2⁻¹ ^ 10 / G) + Cnk / G * runningMax e (k - 1) =
      (2⁻¹ ^ 9 * e k + Cnk * runningMax e (k - 1)) / G := by
    field_simp
    ring
  linarith
theorem margin_le_of_le {Ay a b ε γ GN P Q c : ℝ} (hGN : 0 < GN) (hc : 0 < c) (hε0 : 0 ≤ ε) (hP0 : 0 ≤ P)
    (hQ0 : 0 ≤ Q) (hP : |Ay * a| ≤ P) (hQ : |Ay * b| ≤ Q) (hε : ε ≤ c / (GN * (P + 1)))
    (hγ : γ = c / (GN * (Q + 1))) : Ay * (ε * a + γ * b) ≤ 2 * c / GN := by
  have hγ0 : 0 ≤ γ := by
    rw [hγ]
    positivity
  have h1 : ε * (Ay * a) ≤ c / GN := by
    calc ε * (Ay * a) ≤ ε * P := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hP) hε0
      _ ≤ c / (GN * (P + 1)) * P := mul_le_mul_of_nonneg_right hε hP0
      _ ≤ c / GN := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hGN]
          nlinarith [mul_pos hc hGN]
  have h2 : γ * (Ay * b) ≤ c / GN := by
    calc γ * (Ay * b) ≤ γ * Q := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hQ) hγ0
      _ = c / (GN * (Q + 1)) * Q := by rw [hγ]
      _ ≤ c / GN := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hGN]
          nlinarith [mul_pos hc hGN]
  calc Ay * (ε * a + γ * b) = ε * (Ay * a) + γ * (Ay * b) := by ring
    _ ≤ c / GN + c / GN := add_le_add h1 h2
    _ = _ := by ring
theorem eventuallyInParameters_map₂ {P Q R : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → Prop} (h : ∀ T, P T → Q T → R T)
    (hP : EventuallyInParameters P) (hQ : EventuallyInParameters Q) : EventuallyInParameters R := by
  intro a ha
  obtain ⟨L₁, g₁⟩ := hP a ha
  obtain ⟨L₂, g₂⟩ := hQ a ha
  refine ⟨max L₁ L₂, fun L hodd hL c hc => ?_⟩
  obtain ⟨A₁, g₁⟩ := g₁ L hodd (le_of_max_le_left hL) c hc
  obtain ⟨A₂, g₂⟩ := g₂ L hodd (le_of_max_le_right hL) c hc
  refine ⟨max A₁ A₂, fun Ct hCt => ?_⟩
  obtain ⟨κ₁, hκ₁, g₁⟩ := g₁ Ct (le_of_max_le_left hCt)
  obtain ⟨κ₂, hκ₂, g₂⟩ := g₂ Ct (le_of_max_le_right hCt)
  refine ⟨min κ₁ κ₂, lt_min hκ₁ hκ₂, fun κ hκ hκ' => ?_⟩
  obtain ⟨η₁, hη₁, g₁⟩ := g₁ κ hκ (hκ'.trans (min_le_left _ _))
  obtain ⟨η₂, hη₂, g₂⟩ := g₂ κ hκ (hκ'.trans (min_le_right _ _))
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun η₃ h0 h1 h2 => ?_⟩
  obtain ⟨N₁, g₁⟩ := g₁ η₃ h0 h1 (h2.trans (min_le_left _ _))
  obtain ⟨N₂, g₂⟩ := g₂ η₃ h0 h1 (h2.trans (min_le_right _ _))
  refine ⟨max N₁ N₂, fun nss hn => ?_⟩
  obtain ⟨σ₁, hσ₁, g₁⟩ := g₁ nss (le_of_max_le_left hn)
  obtain ⟨σ₂, hσ₂, g₂⟩ := g₂ nss (le_of_max_le_right hn)
  refine ⟨min σ₁ σ₂, lt_min hσ₁ hσ₂, fun σ hσ hσ' p hp => ?_⟩
  obtain ⟨C₁, g₁⟩ := g₁ σ hσ (hσ'.trans (min_le_left _ _)) p hp
  obtain ⟨C₂, g₂⟩ := g₂ σ hσ (hσ'.trans (min_le_right _ _)) p hp
  refine ⟨max C₁ C₂, fun Cs hCs E hE => ?_⟩
  obtain ⟨m₁, g₁⟩ := g₁ Cs (le_of_max_le_left hCs) E hE
  obtain ⟨m₂, g₂⟩ := g₂ Cs (le_of_max_le_right hCs) E hE
  refine ⟨max m₁ m₂, fun n₀ hn₀ => ?_⟩
  obtain ⟨D₁, g₁⟩ := g₁ n₀ (le_of_max_le_left hn₀)
  obtain ⟨D₂, g₂⟩ := g₂ n₀ (le_of_max_le_right hn₀)
  refine ⟨max D₁ D₂, fun CE hCE => ?_⟩
  obtain ⟨y₁, g₁⟩ := g₁ CE (le_of_max_le_left hCE)
  obtain ⟨y₂, g₂⟩ := g₂ CE (le_of_max_le_right hCE)
  exact ⟨max y₁ y₂, fun y hy => h _ (g₁ y (le_of_max_le_left hy)) (g₂ y (le_of_max_le_right hy))⟩
theorem eventuallyInParameters_nearUniformBase (hresp : DerivsNearUniformTop)
    (hfl : frameRadiusGrowthStatement)
    (L₀ : ℝ → ℕ) (hL₀ : ∀ a, 2 ^ 40 ≤ L₀ a) (del : ℝ → ℝ) (hdel : ∀ a, 1 ≤ a → 0 < del a)
    (L₁ : ℝ → ℕ) (hL₁ : ∀ a, L₁ a ≤ L₀ a) (Nf : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ) (Aq Bv ε₀ γ₀ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ)
    (hAq : ∀ T, 0 ≤ Aq T) (hBv : ∀ T, 0 ≤ Bv T) (hε₀ : ∀ T, 0 < ε₀ T) (hε₁ : ∀ T, ε₀ T ≤ 1)
    (hγ₀ : ∀ T, 0 < γ₀ T) :
    EventuallyInParameters fun T => ∃ R, NearUniformBase T (Nf (rateParameters T)) R
      (Aq (rateParameters T)) (Bv (rateParameters T)) (ε₀ (rateParameters T))
      (γ₀ (rateParameters T)) (del T.a) (L₁ T.a) := by
  intro a ha
  refine ⟨L₀ a, fun L hodd hL c hc => ?_⟩
  have hL40 : 2 ^ 40 ≤ L := (hL₀ a).trans hL
  have hδ₂ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  have hκ₂ : 2 ^ 6 * c.δ₂ ≤ c.κ₂ := hc.classical.1.2.2.2.2.1
  have hκp : 0 < c.κ₂ := by nlinarith
  have hdp := hdel a ha
  refine ⟨0, fun Ct hCt => ⟨min (c.κ₂ / 2 ^ 9) (del a * 2 ^ 10 / 64), lt_min (by positivity) (by positivity),
    fun κ hκ hκ₀ => ?_⟩⟩
  let T₀ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters := ⟨a, L, c, Ct, κ, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  have hε := hε₀ T₀
  have hγ := hγ₀ T₀
  have hu : 0 < κ / 2 ^ 10 * L := by positivity
  refine ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun nss _ => ?_⟩⟩
  obtain ⟨R₀, hR₀⟩ := hresp a L c ha hodd hc (ε₀ T₀ / 4) (by positivity)
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R →
      Real.exp (-(κ / 2 ^ 10 * ((L : ℝ) * ((R : ℝ) / 4 - 1)))) ≤ γ₀ T₀ := by
    refine ⟨⌈4 * (1 - Real.log (γ₀ T₀) / (κ / 2 ^ 10 * L))⌉₊, fun R hR => ?_⟩
    have h1 : 4 * (1 - Real.log (γ₀ T₀) / (κ / 2 ^ 10 * L)) ≤ R :=
      (Nat.le_ceil _).trans (by exact_mod_cast hR)
    rw [← Real.le_log_iff_exp_le hγ]
    have h2 : -Real.log (γ₀ T₀) / (κ / 2 ^ 10 * L) ≤ (R : ℝ) / 4 - 1 := by
      have : -Real.log (γ₀ T₀) / (κ / 2 ^ 10 * L) = -(Real.log (γ₀ T₀) / (κ / 2 ^ 10 * L)) := by ring
      rw [this]
      linarith
    have h3 := (div_le_iff₀ hu).1 h2
    nlinarith
  set N := Nf T₀ with hN
  let R : ℕ := max R₀ (max R₁ (4 * N + 8))
  have hRR₀ : R₀ ≤ R := le_max_left _ _
  have hRR₁ : R₁ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRN : 4 * N + 8 ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨σ₁, hσ₁, hre⟩ := hR₀ R hRR₀
  set D : ℝ := Aq T₀ * (Ct + 1 / 64) + 2 * ((Ct + 1 / 64) + 3 * ((R : ℝ) + 1) * (5 / 4)) * Bv T₀ with hD
  have hCt0 : 0 ≤ Ct := hCt
  have hD0 : 0 ≤ D := by
    have := hAq T₀
    have := hBv T₀
    positivity
  refine ⟨min σ₁ (ε₀ T₀ / (2 * (D + 1))), lt_min hσ₁ (by positivity), fun σ hσ hσ' p hp => ?_⟩
  refine ⟨0, fun Cs hCs E hE => ⟨max 64 (2 * R + 3), fun n₀ hn₀ => ⟨0, fun CE _ => ?_⟩⟩⟩
  obtain ⟨y₁, hy₁, hy⟩ := hfl (|Ct| * 4 / ε₀ T₀ + 1) (c.δ₂ / 4) (by positivity) (by positivity)
  refine ⟨y₁, fun y hyy => ⟨R, ?_⟩⟩
  have hσ₂ : σ ≤ ε₀ T₀ / (2 * (D + 1)) := hσ'.trans (min_le_right _ _)
  have hn64 : 64 ≤ n₀ := (le_max_left _ _).trans hn₀
  have hnR : 2 * R + 3 ≤ n₀ := (le_max_right _ _).trans hn₀
  refine
    { odd := hodd
      L_ge := hL40
      L₁_le := (hL₁ a).trans hL
      holds := hc
      a_ge := ha
      κ_pos := hκ
      κ_le := ?_
      δ_le := ?_
      σ_pos := hσ
      Ct_nonneg := hCt0
      n₀_ge := hn64
      ε₀_pos := hε
      ε₀_le := hε₁ T₀
      γ₀_pos := hγ
      R_ge := hRN
      far := hR₁ R hRR₁
      side := show 2 * R + 2 < n₀ by omega
      resp := fun F V Y h1 h2 h3 h4 b e X h5 h6 h7 h8 =>
        hre _ F V Y hσ (hσ'.trans (min_le_left _ _)) h1 h2 h3 h4 b e X h5 h6 h7 h8
      small := ?_
      floor := ?_ }
  · have := hκ₀.trans (min_le_left _ _)
    show 2 ^ 9 * κ ≤ c.κ₂
    have h2 : κ * 2 ^ 9 ≤ c.κ₂ := (le_div_iff₀ (by positivity)).1 this
    linarith
  · have := hκ₀.trans (min_le_right _ _)
    show κ / 2 ^ 10 ≤ del a / 64
    have h1 : κ ≤ del a * 2 ^ 10 / 64 := this
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · show Aq T₀ * (Ct * σ + σ / 64) +
      2 * ((Ct * σ + σ / 64) + 3 * ((R : ℝ) + 1) * (5 / 4 * σ)) * Bv T₀ ≤ ε₀ T₀ / 2
    have h1 : Aq T₀ * (Ct * σ + σ / 64) +
        2 * ((Ct * σ + σ / 64) + 3 * ((R : ℝ) + 1) * (5 / 4 * σ)) * Bv T₀ = D * σ := by
      rw [hD]
      ring
    rw [h1]
    have h2 : D * σ ≤ D * (ε₀ T₀ / (2 * (D + 1))) := mul_le_mul_of_nonneg_left hσ₂ hD0
    refine h2.trans ?_
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  · intro x hx
    have hxy : y₁ ≤ x := hyy.trans hx
    have hx1 : 1 ≤ x := hy₁.trans hxy
    obtain ⟨h1, -⟩ := hy x hxy
    show Ct * Real.exp (-(c.δ₂ / 4 * frameRadius x)) ≤ ε₀ T₀ / 4
    have hE0 := Real.exp_pos (-(c.δ₂ / 4 * (frameRadius x : ℝ)))
    have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx1
    have h2 : (|Ct| * 4 / ε₀ T₀) * Real.exp (-(c.δ₂ / 4 * frameRadius x)) ≤ 1 := by
      have h3 : 0 ≤ |Ct| * 4 / ε₀ T₀ := by positivity
      calc _ ≤ (|Ct| * 4 / ε₀ T₀ + 1) * Real.exp (-(c.δ₂ / 4 * frameRadius x)) :=
            mul_le_mul_of_nonneg_right (by linarith) hE0.le
        _ ≤ (|Ct| * 4 / ε₀ T₀ + 1) * x ^ 2 * Real.exp (-(c.δ₂ / 4 * frameRadius x)) := by
            refine mul_le_mul_of_nonneg_right ?_ hE0.le
            exact le_mul_of_one_le_right (by positivity) hx2
        _ ≤ 1 := h1
    have h3 : |Ct| * Real.exp (-(c.δ₂ / 4 * frameRadius x)) ≤ ε₀ T₀ / 4 := by
      have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ ε₀ T₀ / 4)
      have e1 : ε₀ T₀ / 4 * (|Ct| * 4 / ε₀ T₀ * Real.exp (-(c.δ₂ / 4 * frameRadius x))) =
          |Ct| * Real.exp (-(c.δ₂ / 4 * frameRadius x)) := by
        field_simp
      linarith
    exact (mul_le_mul_of_nonneg_right (le_abs_self Ct) hE0.le).trans h3
end TopOrderNearBlock
set_option maxHeartbeats 2000000 in
open TopOrderNearBlock in
theorem topOrderNearBlockStatement_holds (hexp : expansionAlongMotionStatement)
    (hgau : gaugeAlongMotionStatement) (hmot : motionAboveFrameStatement)
    (hbd : boundAlongPerturbationsStatement) (hcov : BlocksCoverLowerLevel)
    (hgeo : CubicTorusCellGeometry) (hfield : ChartedFieldNearOne)
    (hsc : FlatCoordinatesScalar) (hF3 : multilinearResponseBound)
    (hflat : flatChainOfMinimizerCoords) (hresp : DerivsNearUniformTop)
    (hturn : BlockMeans.interpolatedBlockExpansionGaugeCovariance) (hdecay : interpolatedFrameDecayStatement)
    (hframes : interpolatedFramesStatement) (hfl : frameRadiusGrowthStatement)
    (hrow : GaugeCovarianceOfFrame) :
    topOrderNearBlockStatement := by
  classical
  let K : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ := fun T k => |16 ^ k * T.chainParams.Kk k|
  have hK : ∀ T k, 0 ≤ K T k := fun T k => abs_nonneg _
  choose! Cgeo hCgeo hgS using hgeo.2
  choose! del hdel L₁ hF3' using hF3
  choose! L₂ hflat' using hflat
  let Bv : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun T => 8 * Real.sqrt T.L * (K T 1 + 1)
  have hBv0 : ∀ T, 0 ≤ Bv T := fun T => by
    have := hK T 1
    positivity
  let A : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ := fun T => Classical.choose (hmot 6 (K T) (hK T))
  have hA : ∀ T q, 0 ≤ A T q := fun T => (Classical.choose_spec (hmot 6 (K T) (hK T))).1
  let M : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ := fun T => Classical.choose (hgau 6 (A T) (Bv T) (hA T) (hBv0 T))
  let Cw : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun T =>
    Cgeo T.chainParams.κ₂ * (T.L : ℝ) ^ 4 * (1 + Real.exp T.chainParams.κ₂)
  let Ay : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun T => Cgeo 1 * (T.L : ℝ) ^ 4
  let Am : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun T => (K T 1 + 1) + 2 * Bv T
  let Cgk : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ := fun T k =>
    Real.exp (T.decayRate * T.L) * (Cgeo (T.decayRate * T.L / 6) * (T.L : ℝ) ^ 4) ^ k
  let Cnon : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ := fun T k =>
    ∑ c' : OrderedFinpartition k, ∏ m', (M T (c'.partSize m') * Cw T)
  let Cn : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℕ → ℝ := fun T N k =>
    |Ay T * Cnon T k * torusDecayFactor T.L T.decayRate N| + 1
  refine ⟨Cn, fun T N k => by positivity, fun Nf => ?_⟩
  let P : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun T =>
    ∑ k ∈ Finset.range 7, |Ay T * ((2 * (Am T + 1)) ^ k * Cgk T k)|
  let Q : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun T => ∑ k ∈ Finset.range 7, |Ay T * (M T 1 * Cw T) ^ k|
  have hP0 : ∀ T, 0 ≤ P T := fun T => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hQ0 : ∀ T, 0 ≤ Q T := fun T => Finset.sum_nonneg fun _ _ => abs_nonneg _
  let GN : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun T => torusDecayFactor T.L T.decayRate (Nf T)
  have hGN : ∀ T, 0 < GN T := fun T => by
    simp only [GN, torusDecayFactor]
    exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
  let c₀ : ℝ := 2⁻¹ ^ 11
  have hc₀ : 0 < c₀ := by positivity
  let ε₀ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun T => min 1 (c₀ / (GN T * (P T + 1)))
  let γ₀ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun T => c₀ / (GN T * (Q T + 1))
  have hε₀ : ∀ T, 0 < ε₀ T := fun T => lt_min one_pos (by
    have := hGN T
    have := hP0 T
    positivity)
  have hγ₀ : ∀ T, 0 < γ₀ T := fun T => by
    have := hGN T
    have := hQ0 T
    positivity
  let Lx : ℝ → ℕ := fun a => max (L₁ a) (L₂ a)
  have base := eventuallyInParameters_nearUniformBase hresp hfl (fun a => max (2 ^ 40) (Lx a))
    (fun a => le_max_left _ _) del hdel
    Lx (fun a => le_max_right _ _) Nf (fun T => A T 0) Bv ε₀ γ₀ (fun T => hA T 0) hBv0 hε₀
    (fun T => min_le_left _ _) hγ₀
  obtain ⟨Cz, -, hD⟩ := hdecay
  obtain ⟨Cq, Cz', Cr, hFr⟩ := hframes
  have J := eventuallyInParameters_map₂ (R := fun T => (∀ (x : ℝ) (t k : ℕ) (e : ℕ → ℝ) (f : LocalFamily)
      (F : BlockFrame)
      (V : F.GaugeField F.top) (s : ℝ) (η : StepVariable (finiteCells F)) (Y : F.Cell)
      (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (γ : F.Cell → UnitQuaternion),
      T.coupling ≤ x →
      HasBoundedDerivatives T.L t T.n₀ T.σ T.decayRate k e f → IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 → (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsSmallCurvature (5 / 4 * T.σ) (gaugeTransform γ V) ∧
      (∀ R : ℕ, (∀ i, 2 * R + 2 < F.extent i) →
        IsNearUniformAbout (5 / 4 * T.σ) R (gaugeTransform (axialGaugeHolonomy V Y) V) Y) ∧
      bondDeriv (interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) f Y η) V c X =
        bondDeriv (interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) f Y (adjointStepVariable γ η))
          (gaugeTransform γ V) c fun l => adjointAction (γ (c l).1) (X l)) ∧
      InterpolatedFrameDecay T (Cz T.a T.L T.chainParams))
    (fun T a b => ⟨a, b⟩) hturn hD
  have J2 := eventuallyInParameters_map₂ (R := fun T => ((∀ (x : ℝ) (t k : ℕ) (e : ℕ → ℝ) (f : LocalFamily)
      (F : BlockFrame)
      (V : F.GaugeField F.top) (s : ℝ) (η : StepVariable (finiteCells F)) (Y : F.Cell)
      (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (γ : F.Cell → UnitQuaternion),
      T.coupling ≤ x →
      HasBoundedDerivatives T.L t T.n₀ T.σ T.decayRate k e f → IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 → (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsSmallCurvature (5 / 4 * T.σ) (gaugeTransform γ V) ∧
      (∀ R : ℕ, (∀ i, 2 * R + 2 < F.extent i) →
        IsNearUniformAbout (5 / 4 * T.σ) R (gaugeTransform (axialGaugeHolonomy V Y) V) Y) ∧
      bondDeriv (interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) f Y η) V c X =
        bondDeriv (interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) f Y (adjointStepVariable γ η))
          (gaugeTransform γ V) c fun l => adjointAction (γ (c l).1) (X l)) ∧
      InterpolatedFrameDecay T (Cz T.a T.L T.chainParams)) ∧
      ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x →
        InterpolatedFrameBoundsAt T (Cq (momentParameters T)) (Cz' (momentParameters T))
          (Cr (momentParameters T)) t x)
    (fun T a b => ⟨a, b⟩) J hFr
  refine eventuallyInParameters_map₂ ?_ J2 base
  rintro T ⟨⟨ht, hd⟩, hf⟩ ⟨R, hb⟩
  intro x t k e f F V s η Y c X hx hk3 hk6 he hfam htor hcold hs0 hs1 hη hX hN
  obtain ⟨hc₁, hnf, hEq⟩ := ht x t k e f F V s η Y c X (axialGaugeHolonomy V Y) hx hfam htor hcold hs0 hs1 hη
  rw [hEq]
  have htor' := htor
  obtain ⟨hFL, htt, n, hside, hn⟩ := htor'
  have hsideR : ∀ i, 2 * R + 2 < F.extent i := fun i => by
    rw [hside i]
    exact hb.side.trans_le hn
  set T' := rateParameters T with hT'
  have hη₁ : ∀ b, ‖adjointStepVariable (axialGaugeHolonomy V Y) η b‖ ≤ T.ballRadius := fun b => by
    rw [hrow.2.2 F (axialGaugeHolonomy V Y) η b]
    exact hη b
  have hX₁ : AreUnitVectors fun l => _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (axialGaugeHolonomy V Y (c l).1) (X l) := fun l => by
    show ‖((axialGaugeHolonomy V Y (c l).1 : ℍ[ℝ]) * (X l : ℍ[ℝ]) *
      ((axialGaugeHolonomy V Y (c l).1)⁻¹ : UnitQuaternion))‖ = 1
    rw [norm_mul, norm_mul, _root_.YangMills.Construction.Interpolation.TopOrderNearBlock.norm_coe_unitQuaternion, _root_.YangMills.Construction.Interpolation.TopOrderNearBlock.norm_coe_unitQuaternion, one_mul, mul_one]
    exact hX l
  have hspan : bondSpan Y c < Nf T' := hN
  have hk7 : k ∈ Finset.range 7 := Finset.mem_range.2 (by omega)
  have hbud := margin_le_of_le (Ay := Ay T')
    (a := (2 * (Am T' + 1)) ^ k * Cgk T' k) (b := (M T' 1 * Cw T') ^ k) (ε := ε₀ T') (γ := γ₀ T')
    (GN := GN T') (P := P T') (Q := Q T') (c := c₀) (hGN T') hc₀ (hε₀ T').le (hP0 T') (hQ0 T')
    (Finset.single_le_sum (f := fun k => |Ay T' * ((2 * (Am T' + 1)) ^ k * Cgk T' k)|)
      (fun _ _ => abs_nonneg _) hk7)
    (Finset.single_le_sum (f := fun k => |Ay T' * (M T' 1 * Cw T') ^ k|)
      (fun _ _ => abs_nonneg _) hk7)
    (min_le_right _ _) rfl
  refine abs_interpolatedBlockExpansion_deriv_le_of_nearUniform (T := T) hexp hgau hmot hbd hcov hgeo hfield hsc
    (K T') (hK T')
    (fun k' => le_abs_self _) Cgeo hCgeo hgS hb hd hf
    (fun F' δ Y' k' c' B W h3 h6 ho hL hc hδ hd' h1 h2 =>
      hF3' T.a hb.a_ge F' δ Y' k' c' B W h3 h6 ho ((le_max_left _ _).trans hL) hc hδ hd' h1 h2)
    (fun F' c' X' h1 h2 h3 => hflat' T.a hb.a_ge T.L T.chainParams hb.odd
      ((le_max_right _ _).trans hb.L₁_le) hb.holds F' c' X' h1 h2 h3)
    hx hk3 hk6 he hfam htor hc₁ hs0 hs1 hη₁ hX₁ hspan (hnf R hsideR) (hBv0 T') ?_ ?_
  · refine le_trans (le_of_eq ?_) (hbud.trans (le_of_eq ?_))
    · show Ay T' * (ε₀ T' * (2 * (Am T' + 1)) ^ k * Cgk T' k + γ₀ T' * (M T' 1 * Cw T') ^ k) = _
      ring
    · show 2 * c₀ / GN T' = _
      simp only [c₀]
      norm_num
      rfl
  · exact (le_abs_self _).trans (le_add_of_nonneg_right (zero_le_one' ℝ))
end Interpolation
end YangMills.Construction
end
