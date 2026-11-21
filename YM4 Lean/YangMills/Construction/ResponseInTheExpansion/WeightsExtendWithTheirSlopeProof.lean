import YangMills.Construction.Lattice.LatticeIsometriesAsMapsOfPairsProof
import YangMills.Construction.ResponseInTheExpansion.WeightsExtendToATorusProof
import YangMills.Construction.ResponseInTheExpansion.RemainderOfTheResponseReturnsProof
import YangMills.Construction.ResponseInTheExpansion.WeightsExtendWithTheirSlope
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps BlockAverages
namespace Extension
private theorem abs_clamp_sub_le (S a b : ℝ) : |max (-S) (min S a) - max (-S) (min S b)| ≤ |a - b| := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.abs_clamp_sub_le <;> assumption
private theorem exists_bounded_lipschitz_extension_local {P ι : Type} (D : P → P → ℝ) (hD0 : ∀ p, D p p = 0)
    (hDs : ∀ p p', D p p' = D p' p) (hDt : ∀ p p' p'', D p p'' ≤ D p p' + D p' p'') (Q : Finset ι) (P' : ι → P)
    (v : ι → ℝ) {S Λ : ℝ} (hS : 0 ≤ S) (hΛ : 0 ≤ Λ) (hv : ∀ q ∈ Q, |v q| ≤ S)
    (hL : ∀ q ∈ Q, ∀ q₂ ∈ Q, v q ≤ v q₂ + Λ * D (P' q) (P' q₂)) :
    ∃ f : P → ℝ, (∀ q ∈ Q, f (P' q) = v q) ∧ (∀ p, |f p| ≤ S) ∧ ∀ p p', |f p - f p'| ≤ Λ * D p p' := by
  by_cases hQ : Q.Nonempty
  · obtain ⟨g, hg⟩ : ∃ g : P → ℝ, g = fun p => Q.inf' hQ fun q => v q + Λ * D p (P' q) := ⟨_, rfl⟩
    have hgl : ∀ p p', g p ≤ g p' + Λ * D p p' := by
      intro p p'
      obtain ⟨q, hq, e⟩ := Finset.exists_mem_eq_inf' hQ (fun q => v q + Λ * D p' (P' q))
      have h1 : g p ≤ v q + Λ * D p (P' q) := by
        rw [hg]
        exact Finset.inf'_le (fun q => v q + Λ * D p (P' q)) hq
      have h3 : g p' = v q + Λ * D p' (P' q) := by
        rw [hg]
        exact e
      have h4 := mul_le_mul_of_nonneg_left (hDt p p' (P' q)) hΛ
      rw [h3]
      rw [mul_add] at h4
      linarith only [h1, h4]
    refine ⟨fun p => max (-S) (min S (g p)), ?_, ?_, ?_⟩
    · intro q hq
      have h1 : g (P' q) ≤ v q := by
        have h0 := Finset.inf'_le (fun q₂ => v q₂ + Λ * D (P' q) (P' q₂)) hq
        have e : v q + Λ * D (P' q) (P' q) = v q := by
          rw [hD0, mul_zero, add_zero]
        rw [hg]
        exact le_trans h0 (le_of_eq e)
      have h2 : v q ≤ g (P' q) := by
        rw [hg]
        exact Finset.le_inf' _ _ fun q₂ hq₂ => hL q hq q₂ hq₂
      have h3 : g (P' q) = v q := le_antisymm h1 h2
      show max (-S) (min S (g (P' q))) = v q
      rw [h3]
      have := abs_le.mp (hv q hq)
      rw [min_eq_right this.2, max_eq_right this.1]
    · intro p
      rw [abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith only [hS]) (min_le_left _ _)⟩
    · intro p p'
      refine (abs_clamp_sub_le S _ _).trans ?_
      rw [abs_le]
      have h1 := hgl p p'
      have h2 := hgl p' p
      rw [hDs p' p] at h2
      constructor <;> linarith only [h1, h2]
  · refine ⟨fun _ => 0, fun q hq => absurd ⟨q, hq⟩ hQ, fun _ => by simpa using hS, fun p p' => ?_⟩
    have h0 : 0 ≤ D p p' := by
      have h1 := hDt p p' p
      rw [hD0, hDs p' p] at h1
      linarith only [h1]
    simpa using mul_nonneg hΛ h0
private def directionCount_local (μ ν i : Fin 4) : ℤ := (if i = μ then 1 else 0) + (if i = ν then 1 else 0)
private theorem doubledBarycentre_apply {M : ℕ} [NeZero M] (x : TorusSite M) (z : Fin 4 → ℤ) (μ ν i : Fin 4) :
    doubledBarycentre (x + siteOfInt z, μ, ν) i =
      ((2 * (((x i).cast : ℤ) + z i) + directionCount_local μ ν i : ℤ) : ZMod (2 * M)) := by apply _root_.YangMills.Construction.WeightedResponses.Extension.doubledBarycentre_add_apply <;> assumption
private def doubledGap (z z₂ : Fin 4 → ℤ) (μ ν μ₂ ν₂ i : Fin 4) : ℤ :=
  2 * (z i - z₂ i) + directionCount_local μ ν i - directionCount_local μ₂ ν₂ i
private theorem supDist_doubledBarycentre_local {M : ℕ} [NeZero M] (x : TorusSite M) (z z₂ : Fin 4 → ℤ) (μ ν μ₂ ν₂ : Fin 4)
    (hs : ∀ i, |doubledGap z z₂ μ ν μ₂ ν₂ i| < (M : ℤ)) :
    supDist (doubledBarycentre (x + siteOfInt z, μ, ν)) (doubledBarycentre (x + siteOfInt z₂, μ₂, ν₂)) =
      Finset.univ.sup fun i => (doubledGap z z₂ μ ν μ₂ ν₂ i).natAbs := by apply _root_.YangMills.Construction.WeightedResponses.Extension.supDist_doubledBarycentre <;> assumption
private theorem directionCount_bounds (μ ν i : Fin 4) (h : μ < ν) :
    0 ≤ directionCount_local μ ν i ∧ directionCount_local μ ν i ≤ 1 := by apply _root_.YangMills.Construction.WeightedResponses.Extension.directionCount_nonneg_le_one <;> assumption
private theorem directionCount_injective_local : ∀ μ ν μ₂ ν₂ : Fin 4, μ < ν → μ₂ < ν₂ →
    (∀ i, directionCount_local μ ν i = directionCount_local μ₂ ν₂ i) → μ = μ₂ ∧ ν = ν₂ := by apply _root_.YangMills.Construction.AffineTorusIsometries.axes_eq_of_axisCount <;> assumption
private theorem exists_offset_parentBlock {L : ℕ} [NeZero L] {n : ℕ} [NeZero n] (hodd : Odd L) (Y : TorusSite n)
    (y : TorusSite (n * L)) (hb : parentBlock L y = Y) (i : Fin 4) :
    ∃ o k : ℤ, 2 * |o| + 1 ≤ (L : ℤ) ∧ ((y i).cast : ℤ) = (L : ℤ) * (((Y i).cast : ℤ) + (n : ℤ) * k) + o := by
  obtain ⟨m, hm⟩ := hodd
  have hLz : (L : ℤ) = 2 * (m : ℤ) + 1 := by exact_mod_cast hm
  have hH : ((L : ℤ) - 1) / 2 = (m : ℤ) := by
    rw [hLz]
    omega
  have hLpos : (0 : ℤ) < L := by
    rw [hLz]
    omega
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = ((y i).cast : ℤ) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = ((Y i).cast : ℤ) := ⟨_, rfl⟩
  have hY : ((B : ℤ) : ZMod n) = (((a + (m : ℤ)) / (L : ℤ) : ℤ) : ZMod n) := by
    rw [hB, ZMod.intCast_zmod_cast, ha, ← hb, ← hH]
    rfl
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hY
  have hr0 := Int.emod_nonneg (a + (m : ℤ)) hLpos.ne'
  have hr1 := Int.emod_lt_of_pos (a + (m : ℤ)) hLpos
  have hdef := Int.emod_def (a + (m : ℤ)) (L : ℤ)
  refine ⟨(a + (m : ℤ)) % (L : ℤ) - (m : ℤ), k, ?_, ?_⟩
  · have : |(a + (m : ℤ)) % (L : ℤ) - (m : ℤ)| ≤ (m : ℤ) := by
      rw [abs_le]
      constructor <;> linarith only [hr0, hr1, hLz]
    linarith only [this, hLz]
  · have hb' : (a + (m : ℤ)) / (L : ℤ) = B + (n : ℤ) * k := by linarith only [hk]
    rw [← ha, ← hB, hdef, hb']
    ring
private theorem exists_offset_fineBlock {L : ℕ} [NeZero L] (hodd : Odd L) (t : ℕ) :
    ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (x : TorusSite (fineSide L t n)), x ∈ fineBlock L t n y →
      ∃ w : Fin 4 → ℤ, (∀ i, 2 * |w i| + 1 ≤ (L : ℤ) ^ t) ∧ x = fineCentre L t y + siteOfInt w := by
  induction t with
  | zero =>
    intro n _ y x hx
    have hx' : x = y := Finset.mem_singleton.mp hx
    refine ⟨0, fun i => by simp, ?_⟩
    subst hx'
    funext i
    show (x i : ZMod n) = (((L : ℤ) ^ 0 * ((x i).cast : ℤ) : ℤ) : ZMod n) + ((0 : ℤ) : ZMod n)
    rw [pow_zero, one_mul, Int.cast_zero, add_zero]
    exact (ZMod.intCast_zmod_cast (n := n) (x i)).symm
  | succ t ih =>
    intro n _ Y x hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨w, hw, e⟩ := ih (n * L) y x hxy
    have hb : parentBlock L y = Y := Finset.mem_singleton.mp (Finset.mem_filter.mp hy).2
    choose o k ho hk using exists_offset_parentBlock hodd Y y hb
    have hLt : (0 : ℤ) ≤ (L : ℤ) ^ t := by positivity
    refine ⟨fun i => (L : ℤ) ^ t * o i + w i, fun i => ?_, ?_⟩
    · have h1 : |(L : ℤ) ^ t * o i + w i| ≤ (L : ℤ) ^ t * |o i| + |w i| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hLt]
      have h2 := mul_le_mul_of_nonneg_left (ho i) hLt
      have h3 := hw i
      rw [pow_succ]
      nlinarith only [h1, h2, h3]
    · funext i
      have hi : (x i : ZMod (fineSide L t (n * L))) =
          (((L : ℤ) ^ t * ((y i).cast : ℤ) + w i : ℤ) : ZMod (fineSide L t (n * L))) := by
        rw [congrFun e i]
        exact (Int.cast_add _ _).symm
      show (x i : ZMod (fineSide L t (n * L))) =
        (((L : ℤ) ^ (t + 1) * ((Y i).cast : ℤ) : ℤ) : ZMod (fineSide L t (n * L))) +
          (((L : ℤ) ^ t * o i + w i : ℤ) : ZMod (fineSide L t (n * L)))
      rw [hi, ← Int.cast_add]
      refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ⟨-k i, ?_⟩
      rw [fineSide_eq, hk i]
      push_cast
      ring
private theorem unitStep_eq (M : ℕ) (j : Fin 4) : TorusFields.unitStep M j = siteOfInt fun i => if i = j then 1 else 0 := by
  funext i
  simp only [TorusFields.unitStep, siteOfInt, Pi.single_apply]
  split_ifs <;> simp
private theorem siteOfInt_add {M : ℕ} (e e' : Fin 4 → ℤ) :
    (siteOfInt e + siteOfInt e' : TorusSite M) = siteOfInt fun i => e i + e' i := by
  funext i
  simp [siteOfInt]
private theorem exists_step_of_mem_vertices {M : ℕ} (x c : TorusSite M) (μ ν : Fin 4) (h : μ < ν)
    (hc : c ∈ plaquetteVertices x μ ν) :
    ∃ f : Fin 4 → ℤ, (∀ i, 0 ≤ f i ∧ f i ≤ 1) ∧ c = x + siteOfInt f := by
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with e | e | e | e
  · refine ⟨0, fun i => by simp, ?_⟩
    rw [e]
    funext i
    simp [siteOfInt]
  · refine ⟨fun i => if i = μ then 1 else 0, fun i => ?_, ?_⟩
    · dsimp only
      split_ifs <;> simp
    · rw [e, unitStep_eq]
  · refine ⟨fun i => if i = ν then 1 else 0, fun i => ?_, ?_⟩
    · dsimp only
      split_ifs <;> simp
    · rw [e, unitStep_eq]
  · refine ⟨fun i => (if i = μ then 1 else 0) + (if i = ν then 1 else 0), fun i => ?_, ?_⟩
    · have := directionCount_bounds μ ν i h
      exact this
    · rw [e, unitStep_eq, unitStep_eq, add_assoc, siteOfInt_add]
private theorem offset_bounds_of_isPlaquetteAt {L : ℕ} [NeZero L] (hodd : Odd L) (t n : ℕ) [NeZero n] (hn : 4 ≤ n)
    (y : TorusSite n) (z : Fin 4 → ℤ) (μ ν : Fin 4) (hz : ∀ i, |z i| ≤ (L : ℤ) ^ t)
    (hat : IsPlaquetteAt L t y (fineCentre L t y + siteOfInt z, μ, ν)) (i : Fin 4) :
    2 * z i + 1 ≤ (L : ℤ) ^ t ∧ -(L : ℤ) ^ t - 1 ≤ 2 * z i := by
  obtain ⟨hlt, c, hc, hb⟩ := hat
  obtain ⟨w, hw, e⟩ := exists_offset_fineBlock hodd t n y c hb
  obtain ⟨f, hf, e'⟩ := exists_step_of_mem_vertices _ c μ ν hlt hc
  have hL1 : (1 : ℤ) ≤ (L : ℤ) ^ t := by
    have : (1 : ℤ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    exact one_le_pow₀ this
  have hside : 4 * (L : ℤ) ^ t ≤ ((fineSide L t n : ℕ) : ℤ) := by
    rw [fineSide_eq]
    push_cast
    have hn' : (4 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith only [hn', hL1]
  have hzero : ((z i + f i - w i : ℤ) : ZMod (fineSide L t n)) = 0 := by
    have h1 := congrFun (e'.symm.trans e) i
    simp only [siteOfInt, Pi.add_apply] at h1
    have h2 : ((z i : ℤ) : ZMod (fineSide L t n)) + ((f i : ℤ) : ZMod (fineSide L t n)) =
        ((w i : ℤ) : ZMod (fineSide L t n)) := by
      have h3 := add_assoc (fineCentre L t y i) ((z i : ℤ) : ZMod (fineSide L t n)) ((f i : ℤ) : ZMod (fineSide L t n))
      exact add_left_cancel (h3.symm.trans h1)
    push_cast
    rw [h2, sub_self]
  have hdvd : ((fineSide L t n : ℕ) : ℤ) ∣ z i + f i - w i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have h4 := abs_le.mp (hz i)
  have h5 : |w i| ≤ (L : ℤ) ^ t := by
    have := hw i
    have h0 := abs_nonneg (w i)
    linarith only [this, h0]
  have h6 := abs_le.mp h5
  have h7 := hf i
  have hlt' : |z i + f i - w i| < ((fineSide L t n : ℕ) : ℤ) := by
    rw [abs_lt]
    constructor <;> linarith only [h4.1, h4.2, h6.1, h6.2, h7.1, h7.2, hside, hL1]
  have h8 : z i + f i - w i = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt'
  have h9 := abs_le.mp (show |w i| ≤ |w i| from le_rfl)
  have h10 := hw i
  constructor <;> linarith only [h8, h9.1, h9.2, h10, h7.1, h7.2]
end Extension
open Extension in
theorem weightExtensionLipschitz : weightExtensionLipschitzStatement := by
  classical
  intro L _ hodd t n n' _ _ hn hn' y y' h
  have hLpos : (1 : ℤ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = (L : ℤ) ^ t := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by
    rw [hQ]
    exact one_le_pow₀ hLpos
  have hside : ∀ N : ℕ, 4 ≤ N → 4 * Q ≤ ((fineSide L t N : ℕ) : ℤ) := by
    intro N hN
    rw [fineSide_eq, hQ]
    push_cast
    have hN' : (4 : ℤ) ≤ N := by exact_mod_cast hN
    have hp : (0 : ℤ) ≤ (L : ℤ) ^ t := by positivity
    nlinarith only [hN', hp]
  have hL0 : (0 : ℝ) < 2 * (L : ℝ) ^ t := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  obtain ⟨S, hS⟩ : ∃ S, S = weightSup h := ⟨_, rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = weightLipschitz L t h := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact Real.iSup_nonneg fun _ => abs_nonneg _
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛ]
    exact Real.iSup_nonneg fun _ => div_nonneg (abs_nonneg _) (div_nonneg (Nat.cast_nonneg _) hL0.le)
  obtain ⟨c, hc⟩ : ∃ c, c = fineCentre L t y := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', c' = fineCentre L t y' := ⟨_, rfl⟩
  let Z : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-Q) Q
  let Qs : Finset ((Fin 4 → ℤ) × Fin 4 × Fin 4) :=
    (Z ×ˢ (Finset.univ : Finset (Fin 4 × Fin 4))).filter fun q => IsPlaquetteAt L t y (c + siteOfInt q.1, q.2.1, q.2.2)
  have hmem : ∀ q, q ∈ Qs ↔ (∀ i, |q.1 i| ≤ Q) ∧ IsPlaquetteAt L t y (c + siteOfInt q.1, q.2.1, q.2.2) := by
    intro q
    simp only [Qs, Z, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc, Finset.mem_univ,
      and_true, abs_le]
  have hbd : BddAbove (Set.range fun p : OrientedPlaquette (fineSide L t n) => |h p.1|) := (Set.finite_range _).bddAbove
  have hbd2 : BddAbove (Set.range fun pp : OrientedPlaquette (fineSide L t n) × OrientedPlaquette (fineSide L t n) =>
      |h pp.1.1 - h pp.2.1| / barycentreDist L t pp.1.1 pp.2.1) := (Set.finite_range _).bddAbove
  have hv : ∀ q ∈ Qs, |h (c + siteOfInt q.1, q.2.1, q.2.2)| ≤ S := by
    intro q hq
    have hlt := ((hmem q).mp hq).2.1
    rw [hS]
    exact le_ciSup hbd ⟨(c + siteOfInt q.1, q.2.1, q.2.2), hlt⟩
  have hrange : ∀ q ∈ Qs, ∀ i, 2 * q.1 i + 1 ≤ Q ∧ -Q - 1 ≤ 2 * q.1 i := by
    intro q hq i
    have h1 := (hmem q).mp hq
    rw [hc] at h1
    rw [hQ]
    exact offset_bounds_of_isPlaquetteAt hodd t n hn y q.1 q.2.1 q.2.2 (fun i => by rw [← hQ]; exact h1.1 i) h1.2 i
  have hsm : ∀ q ∈ Qs, ∀ q₂ ∈ Qs, ∀ i, ∀ N : ℕ, 4 ≤ N →
      |doubledGap q.1 q₂.1 q.2.1 q.2.2 q₂.2.1 q₂.2.2 i| < ((fineSide L t N : ℕ) : ℤ) := by
    intro q hq q₂ hq₂ i N hN
    have h1 := hrange q hq i
    have h2 := hrange q₂ hq₂ i
    have h3 := directionCount_bounds q.2.1 q.2.2 i ((hmem q).mp hq).2.1
    have h4 := directionCount_bounds q₂.2.1 q₂.2.2 i ((hmem q₂).mp hq₂).2.1
    have h5 := hside N hN
    unfold doubledGap
    rw [abs_lt]
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5, hQ1]
  have hdist : ∀ q ∈ Qs, ∀ q₂ ∈ Qs,
      barycentreDist L t ((c + siteOfInt q.1, q.2.1, q.2.2) : TorusPlaquette (fineSide L t n))
          (c + siteOfInt q₂.1, q₂.2.1, q₂.2.2) =
        barycentreDist L t ((c' + siteOfInt q.1, q.2.1, q.2.2) : TorusPlaquette (fineSide L t n'))
          (c' + siteOfInt q₂.1, q₂.2.1, q₂.2.2) := by
    intro q hq q₂ hq₂
    unfold barycentreDist
    rw [supDist_doubledBarycentre_local c q.1 q₂.1 _ _ _ _ fun i => hsm q hq q₂ hq₂ i n hn,
      supDist_doubledBarycentre_local c' q.1 q₂.1 _ _ _ _ fun i => hsm q hq q₂ hq₂ i n' hn']
  have hLip : ∀ q ∈ Qs, ∀ q₂ ∈ Qs, h (c + siteOfInt q.1, q.2.1, q.2.2) ≤ h (c + siteOfInt q₂.1, q₂.2.1, q₂.2.2) +
      Λ * barycentreDist L t ((c' + siteOfInt q.1, q.2.1, q.2.2) : TorusPlaquette (fineSide L t n'))
        (c' + siteOfInt q₂.1, q₂.2.1, q₂.2.2) := by
    intro q hq q₂ hq₂
    rw [← hdist q hq q₂ hq₂]
    have hlt := ((hmem q).mp hq).2.1
    have hlt₂ := ((hmem q₂).mp hq₂).2.1
    by_cases hd : barycentreDist L t ((c + siteOfInt q.1, q.2.1, q.2.2) : TorusPlaquette (fineSide L t n))
        (c + siteOfInt q₂.1, q₂.2.1, q₂.2.2) = 0
    · have hz : supDist (doubledBarycentre ((c + siteOfInt q.1, q.2.1, q.2.2) : TorusPlaquette (fineSide L t n)))
          (doubledBarycentre (c + siteOfInt q₂.1, q₂.2.1, q₂.2.2)) = 0 := by
        unfold barycentreDist at hd
        have := (div_eq_zero_iff.mp hd).resolve_right hL0.ne'
        exact_mod_cast this
      rw [supDist_doubledBarycentre_local c q.1 q₂.1 _ _ _ _ fun i => hsm q hq q₂ hq₂ i n hn] at hz
      have hg : ∀ i, doubledGap q.1 q₂.1 q.2.1 q.2.2 q₂.2.1 q₂.2.2 i = 0 := by
        intro i
        have h1 : (doubledGap q.1 q₂.1 q.2.1 q.2.2 q₂.2.1 q₂.2.2 i).natAbs ≤ 0 := by
          rw [← hz]
          exact Finset.le_sup (f := fun i => (doubledGap q.1 q₂.1 q.2.1 q.2.2 q₂.2.1 q₂.2.2 i).natAbs)
            (Finset.mem_univ i)
        omega
      have hzz : ∀ i, q.1 i = q₂.1 i ∧ directionCount_local q.2.1 q.2.2 i = directionCount_local q₂.2.1 q₂.2.2 i := by
        intro i
        have h1 := hg i
        have h3 := directionCount_bounds q.2.1 q.2.2 i hlt
        have h4 := directionCount_bounds q₂.2.1 q₂.2.2 i hlt₂
        unfold doubledGap at h1
        constructor <;> omega
      obtain ⟨e1, e2⟩ := directionCount_injective_local _ _ _ _ hlt hlt₂ fun i => (hzz i).2
      have e3 : q.1 = q₂.1 := funext fun i => (hzz i).1
      rw [e1, e2, e3]
      have := mul_nonneg hΛ0 (div_nonneg (Nat.cast_nonneg _) hL0.le :
        0 ≤ barycentreDist L t ((c + siteOfInt q₂.1, q₂.2.1, q₂.2.2) : TorusPlaquette (fineSide L t n))
          (c + siteOfInt q₂.1, q₂.2.1, q₂.2.2))
      exact le_add_of_nonneg_right this
    · have hpos : 0 < barycentreDist L t ((c + siteOfInt q.1, q.2.1, q.2.2) : TorusPlaquette (fineSide L t n))
          (c + siteOfInt q₂.1, q₂.2.1, q₂.2.2) :=
        lt_of_le_of_ne (div_nonneg (Nat.cast_nonneg _) hL0.le) (Ne.symm hd)
      have h1 := le_ciSup hbd2
        (⟨(c + siteOfInt q.1, q.2.1, q.2.2), hlt⟩, ⟨(c + siteOfInt q₂.1, q₂.2.1, q₂.2.2), hlt₂⟩)
      have h3 : |h (c + siteOfInt q.1, q.2.1, q.2.2) - h (c + siteOfInt q₂.1, q₂.2.1, q₂.2.2)| /
          barycentreDist L t ((c + siteOfInt q.1, q.2.1, q.2.2) : TorusPlaquette (fineSide L t n))
            (c + siteOfInt q₂.1, q₂.2.1, q₂.2.2) ≤ Λ := by
        rw [hΛ]
        exact h1
      have h4 := (div_le_iff₀ hpos).mp h3
      have h5 := le_abs_self (h (c + siteOfInt q.1, q.2.1, q.2.2) - h (c + siteOfInt q₂.1, q₂.2.1, q₂.2.2))
      linarith only [h4, h5]
  obtain ⟨f, hf1, hf2, hf3⟩ := exists_bounded_lipschitz_extension_local (P := TorusPlaquette (fineSide L t n'))
    (barycentreDist L t)
    (fun p => by simp [barycentreDist, supDist_self])
    (fun p p' => by
      unfold barycentreDist
      rw [supDist_comm])
    (fun p p' p'' => by
      unfold barycentreDist
      rw [← add_div]
      refine div_le_div_of_nonneg_right ?_ hL0.le
      exact_mod_cast supDist_triangle _ _ _)
    Qs (fun q => ((c' + siteOfInt q.1, q.2.1, q.2.2) : TorusPlaquette (fineSide L t n')))
    (fun q => h (c + siteOfInt q.1, q.2.1, q.2.2)) hS0 hΛ0 hv hLip
  have : Nonempty (OrientedPlaquette (fineSide L t n')) :=
    ⟨⟨(0, (0 : Fin 4), (1 : Fin 4)), by show (0 : Fin 4) < 1; decide⟩⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro z μ ν hz hat
    rw [← hc, ← hc'] at *
    have hq : (z, μ, ν) ∈ Qs := (hmem _).mpr ⟨fun i => by rw [hQ]; exact hz i, hat⟩
    exact (hf1 _ hq).symm
  · rw [← hS]
    exact ciSup_le fun p => hf2 _
  · rw [← hΛ]
    refine ciSup_le fun pp => ?_
    by_cases hd : barycentreDist L t pp.1.1 pp.2.1 = 0
    · rw [hd, div_zero]
      exact hΛ0
    · have hpos : 0 < barycentreDist L t pp.1.1 pp.2.1 :=
        lt_of_le_of_ne (div_nonneg (Nat.cast_nonneg _) hL0.le) (Ne.symm hd)
      rw [div_le_iff₀ hpos]
      exact hf3 _ _
end YangMills.Construction.WeightedResponses
end
