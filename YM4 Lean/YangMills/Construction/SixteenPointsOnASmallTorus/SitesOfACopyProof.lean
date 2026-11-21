import YangMills.Construction.SixteenPointsOnASmallTorus.SitesOfACopy
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion TestFunctions
private theorem exists_offset_of_mem_block {L n : ℕ} [NeZero L] [NeZero n] (hL : Odd L) {x : ZMod (n * L)} {Y : ℤ}
    (hY : (Y : ZMod n) = (((((x.cast : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ)) : ZMod n)) :
    ∃ z : ℤ, 2 * |z| ≤ (L : ℤ) - 1 ∧ x = (((L : ℤ) * Y + z : ℤ) : ZMod (n * L)) := by
  obtain ⟨r, hr⟩ := hL
  have hLpos : (0 : ℤ) < L := by omega
  have hhalf : ((L : ℤ) - 1) / 2 = r := by omega
  rw [hhalf] at hY
  set v : ℤ := (x.cast : ℤ) with hv
  set q : ℤ := (v + r) / (L : ℤ) with hq
  have hmod := Int.emod_add_mul_ediv (v + r) (L : ℤ)
  have hm0 := Int.emod_nonneg (v + r) hLpos.ne'
  have hm1 := Int.emod_lt_of_pos (v + r) hLpos
  rw [← hq] at hmod
  obtain ⟨u, hu⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hY
  refine ⟨v - (L : ℤ) * q, ?_, ?_⟩
  · have : |v - (L : ℤ) * q| ≤ r := by
      rw [abs_le]
      constructor <;> nlinarith
    linarith
  · have hx : x = (v : ZMod (n * L)) := by
      rw [hv]
      simp
    rw [hx, ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨-u, ?_⟩
    push_cast
    have : q - Y = (n : ℤ) * u := hu
    have hq' : q = Y + (n : ℤ) * u := by linarith
    rw [hq']
    ring
private theorem exists_offset_of_mem_fineBlock {L : ℕ} [NeZero L] (hL : Odd L) (t : ℕ) :
    ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (c : TorusSite (fineSide L t n)), c ∈ fineBlock L t n y → ∀ (i : Fin 4) (Y : ℤ),
      (Y : ZMod n) = y i →
      ∃ z : ℤ, 2 * |z| ≤ (L : ℤ) ^ t - 1 ∧ c i = (((L : ℤ) ^ t * Y + z : ℤ) : ZMod (fineSide L t n)) := by
  induction t with
  | zero =>
    intro n _ y c hc i Y hY
    have hcy : c = y := Finset.mem_singleton.mp hc
    have hcy' : (c : TorusSite n) i = y i := congrFun hcy i
    have hYi : ((((L : ℤ) ^ 0 * Y + 0 : ℤ)) : ZMod n) = y i := by simpa using hY
    exact ⟨0, by simp, hcy'.trans hYi.symm⟩
  | succ t ih =>
    intro n _ y c hc i Y hY
    have hc₁ : c ∈ (sitesInBlocks L {y}).biUnion fun y' => fineBlock L t (n * L) y' := hc
    obtain ⟨y', hy', hc'⟩ := Finset.mem_biUnion.mp hc₁
    have hb : parentBlock L y' = y := by simpa [sitesInBlocks] using hy'
    have hYb : (Y : ZMod n) = (((((y' i).cast : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ) : ZMod n) := by
      rw [hY, ← hb]
      rfl
    obtain ⟨z₁, hz₁, hy'i⟩ := exists_offset_of_mem_block hL hYb
    obtain ⟨z₂, hz₂, hci⟩ := ih (n * L) y' c hc' i ((L : ℤ) * Y + z₁) hy'i.symm
    refine ⟨(L : ℤ) ^ t * z₁ + z₂, ?_, ?_⟩
    · have hp : (0 : ℤ) < (L : ℤ) ^ t := by
        have : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
        positivity
      have h1 : |(L : ℤ) ^ t * z₁ + z₂| ≤ (L : ℤ) ^ t * |z₁| + |z₂| := by
        calc _ ≤ |(L : ℤ) ^ t * z₁| + |z₂| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_of_pos hp]
      have h2 : (L : ℤ) ^ t * (2 * |z₁|) ≤ (L : ℤ) ^ t * ((L : ℤ) - 1) := mul_le_mul_of_nonneg_left hz₁ hp.le
      rw [pow_succ]
      nlinarith
    · have : (((L : ℤ) ^ (t + 1) * Y + ((L : ℤ) ^ t * z₁ + z₂) : ℤ)) = (L : ℤ) ^ t * ((L : ℤ) * Y + z₁) + z₂ := by ring
      rw [this]
      exact hci
private theorem intCast_two_mul_eq_of_intCast_eq {m : ℕ} {a b : ℤ} (h : (a : ZMod m) = (b : ZMod m)) : ((2 * a : ℤ) : ZMod (2 * m)) = ((2 * b : ℤ) : ZMod (2 * m)) := by
  obtain ⟨u, hu⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨u, ?_⟩
  push_cast
  linear_combination 2 * hu
private theorem plaquetteVertices_coord {m : ℕ} (x c : TorusSite m) {a b : Fin 4} (hab : a < b) (hc : c ∈ plaquetteVertices x a b) (μ : Fin 4) :
    ∃ ε : ℤ, |(((if μ = a then 1 else 0) + (if μ = b then 1 else 0) : ℤ)) - 2 * ε| ≤ 1 ∧ c μ = x μ + (ε : ZMod m) := by
  have hne : a ≠ b := hab.ne
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hc
  by_cases h1 : μ = a
  · have h2 : μ ≠ b := fun h => hne (h1.symm.trans h)
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [h1, hne], by simp⟩
    · exact ⟨1, by simp [h1, hne], by simp [unitStep, h1]⟩
    · exact ⟨0, by simp [h1, hne], by simp [unitStep, h1, hne]⟩
    · exact ⟨1, by simp [h1, hne], by simp [unitStep, h1, hne]⟩
  · by_cases h2 : μ = b
    · have h3 : b ≠ a := hne.symm
      rcases hc with rfl | rfl | rfl | rfl
      · exact ⟨0, by simp [h2, h3], by simp⟩
      · exact ⟨0, by simp [h2, h3], by simp [unitStep, h2, h3]⟩
      · exact ⟨1, by simp [h2, h3], by simp [unitStep, h2]⟩
      · exact ⟨1, by simp [h2, h3], by simp [unitStep, h2, h3]⟩
    · rcases hc with rfl | rfl | rfl | rfl
      · exact ⟨0, by simp [h1, h2], by simp⟩
      · exact ⟨0, by simp [h1, h2], by simp [unitStep, h1]⟩
      · exact ⟨0, by simp [h1, h2], by simp [unitStep, h2]⟩
      · exact ⟨0, by simp [h1, h2], by simp [unitStep, h1, h2]⟩
private theorem levelSpacing_eq_pow_mul {L : ℕ} [NeZero L] (K t : ℕ) : levelSpacing L K t = (L : ℝ) ^ t * levelSpacing L K 0 := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  rw [levelSpacing, levelSpacing, ← zpow_natCast, ← zpow_add₀ hL]
  congr 1
  push_cast
  ring
private theorem levelSpacing_pos_aux {L : ℕ} [NeZero L] (K t : ℕ) : 0 < levelSpacing L K t := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact zpow_pos hL _
private def mirroredCoord (n pw k : ℕ) (v : ZMod n) : ℤ :=
  ((-1 : ZMod n) ^ k * (v - (pw : ZMod n) * (k : ZMod n))).valMinAbs
private theorem mirroredCoord_near_center {L : ℕ} [NeZero L] {K κ t n m pw : ℕ} [NeZero n] [NeZero m] {ρ H : ℝ} {Λ : NNReal} {h : EuclideanFourSpace → ℝ}
    (hρ : 0 < ρ) (hs : IsLocalizedSource (cellLength L K κ) ρ H Λ h) (k : Fin 4 → ℕ) {c : EuclideanFourSpace}
    (hc : ∀ x, h x ≠ 0 → dist x c ≤ ρ) (hpow : (L : ℤ) ^ t * (pw : ℤ) = (L : ℤ) ^ κ) (hpw : 0 < pw)
    (hnZ : (n : ℤ) = 2 * (pw : ℤ)) (hmZ : (m : ℤ) = 2 * (L : ℤ) ^ κ) {v : ZMod n} {p : TorusPlaquette m} {cc : TorusSite m}
    (hlt : p.2.1 < p.2.2) (hcc : cc ∈ plaquetteVertices p.1 p.2.1 p.2.2) (μ : Fin 4)
    (hcb : ∀ Y : ℤ, (Y : ZMod n) = v → ∃ z : ℤ, 2 * |z| ≤ (L : ℤ) ^ t - 1 ∧ cc μ = (((L : ℤ) ^ t * Y + z : ℤ) : ZMod m))
    (hne : reflectedWeight (levelSpacing L K 0) (L ^ κ) k h p ≠ 0) :
    |levelSpacing L K t * (mirroredCoord n pw (k μ) v : ℝ) - c μ| ≤ ρ + levelSpacing L K t / 2 := by
  have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set sg : ℤ := (-1) ^ (k μ) with hsg
  have hsg2 : sg * sg = 1 := by
    rw [hsg, ← mul_pow]
    simp
  set w : ℤ := mirroredCoord n pw (k μ) v with hw
  have hwc : (w : ZMod n) = (-1 : ZMod n) ^ (k μ) * (v - (pw : ZMod n) * ((k μ : ℕ) : ZMod n)) := by
    rw [hw, mirroredCoord, ZMod.coe_valMinAbs]
  have hwb' : -(n : ℤ) < w * 2 ∧ w * 2 ≤ n :=
    ZMod.valMinAbs_mem_Ioc ((-1 : ZMod n) ^ (k μ) * (v - (pw : ZMod n) * ((k μ : ℕ) : ZMod n)))
  set Y : ℤ := sg * w + (pw : ℤ) * (k μ : ℤ) with hY
  have hYc : (Y : ZMod n) = v := by
    have hs2 : ((-1 : ZMod n) ^ (k μ)) * ((-1 : ZMod n) ^ (k μ)) = 1 := by
      rw [← mul_pow]
      simp
    rw [hY]
    push_cast
    rw [hsg]
    push_cast
    rw [hwc]
    linear_combination (v - (pw : ZMod n) * ((k μ : ℕ) : ZMod n)) * hs2
  obtain ⟨z, hz, hcμ⟩ := hcb Y hYc
  obtain ⟨ε, hε, hcμ'⟩ := plaquetteVertices_coord p.1 cc hlt hcc μ
  set e : ℤ := (if μ = p.2.1 then 1 else 0) + (if μ = p.2.2 then 1 else 0) with he
  set a₁ : ℤ := ((p.1 μ).val : ℤ) with ha₁
  have ha₁c : (a₁ : ZMod m) = p.1 μ := by
    rw [ha₁]
    simp
  have hres : ((a₁ + ε : ℤ) : ZMod m) = (((L : ℤ) ^ t * Y + z : ℤ) : ZMod m) := by
    rw [← hcμ, hcμ']
    push_cast
    rw [ha₁c]
  have hdbl := intCast_two_mul_eq_of_intCast_eq hres
  have hd : doubledBarycentre p μ = ((2 * ((L : ℤ) ^ t * Y + z) - 2 * ε + e : ℤ) : ZMod (2 * m)) := by
    have h1 : doubledBarycentre p μ = ((2 * a₁ + e : ℤ) : ZMod (2 * m)) := by
      simp only [doubledBarycentre, he, ha₁]
      split_ifs <;> push_cast <;> ring
    rw [h1]
    have h2 : ((2 * a₁ + e : ℤ)) = 2 * (a₁ + ε) - 2 * ε + e := by ring
    rw [h2]
    push_cast
    push_cast at hdbl
    rw [hdbl]
  set δ : ℤ := 2 * z + e - 2 * ε with hδ
  set A : ZMod (2 * m) := (-1 : ZMod (2 * m)) ^ (k μ) * (doubledBarycentre p μ - 2 * (((L ^ κ : ℕ)) : ZMod (2 * m)) * ((k μ : ℕ) : ZMod (2 * m))) with hA
  have hAint : A = ((2 * (L : ℤ) ^ t * w + sg * δ : ℤ) : ZMod (2 * m)) := by
    have h1 : A = ((sg * ((2 * ((L : ℤ) ^ t * Y + z) - 2 * ε + e) - 2 * (L : ℤ) ^ κ * (k μ : ℤ)) : ℤ) : ZMod (2 * m)) := by
      rw [hA, hd, hsg]
      push_cast
      ring
    rw [h1]
    congr 1
    rw [hY, hδ]
    linear_combination (2 * (L : ℤ) ^ t * w) * hsg2 + (2 * sg * (k μ : ℤ)) * hpow
  set E : ℤ := A.valMinAbs with hE
  have hEc : (E : ZMod (2 * m)) = A := by
    rw [hE, ZMod.coe_valMinAbs]
  set x : EuclideanFourSpace := reflectedPoint (levelSpacing L K 0) (L ^ κ) k p with hx
  have hhx : h x ≠ 0 := hne
  have hxμ : x μ = levelSpacing L K 0 / 2 * (E : ℝ) := by
    rfl
  have hf := hs.away_from_faces x hhx μ
  have hb := hc x hhx
  have hxc : |x μ - c μ| ≤ ρ := by
    have h1 : ‖(x - c) μ‖ ≤ ‖x - c‖ := PiLp.norm_apply_le (x - c) μ
    rw [← dist_eq_norm] at h1
    have h2 : (x - c) μ = x μ - c μ := rfl
    rw [h2, Real.norm_eq_abs] at h1
    exact h1.trans hb
  have ha₀ : 0 < levelSpacing L K 0 := levelSpacing_pos_aux K 0
  have hEl : |E| < (L : ℤ) ^ κ := by
    have h1 : |(E : ℝ)| * (levelSpacing L K 0 / 2) + ρ ≤ (L : ℝ) ^ κ * levelSpacing L K 0 / 2 := by
      have h2 : |x μ| = |(E : ℝ)| * (levelSpacing L K 0 / 2) := by
        rw [hxμ, abs_mul, abs_of_pos (by positivity : 0 < levelSpacing L K 0 / 2), mul_comm]
      rw [← h2]
      simpa [cellLength] using hf
    have h3 : |(E : ℝ)| < (L : ℝ) ^ κ := by
      by_contra hcon
      replace hcon := not_lt.mp hcon
      have h4 := mul_le_mul_of_nonneg_right hcon (by positivity : 0 ≤ levelSpacing L K 0 / 2)
      nlinarith
    exact_mod_cast h3
  have hδb : |δ| ≤ (L : ℤ) ^ t := by
    have h1 : |δ| ≤ 2 * |z| + |e - 2 * ε| := by
      have : δ = 2 * z + (e - 2 * ε) := by rw [hδ]; ring
      rw [this]
      calc _ ≤ |2 * z| + |e - 2 * ε| := abs_add_le _ _
        _ = _ := by rw [abs_mul]; simp
    linarith
  have hsgδ : |sg * δ| ≤ (L : ℤ) ^ t := by
    have : |sg| = 1 := by rw [hsg]; simp
    rw [abs_mul, this, one_mul]
    exact hδb
  have hLt : (L : ℤ) ^ t ≤ (L : ℤ) ^ κ := by
    have h1 : (1 : ℤ) ≤ (pw : ℤ) := by exact_mod_cast hpw
    rw [← hpow]
    nlinarith [pow_pos hLpos t]
  have hwL : |2 * (L : ℤ) ^ t * w| ≤ 2 * (L : ℤ) ^ κ := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 * (L : ℤ) ^ t)]
    have h1 : |w| ≤ (pw : ℤ) := by
      rw [abs_le]
      constructor <;> linarith [hwb'.1, hwb'.2]
    calc 2 * (L : ℤ) ^ t * |w| ≤ 2 * (L : ℤ) ^ t * (pw : ℤ) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * (L : ℤ) ^ κ := by rw [mul_assoc, hpow]
  have hEeq : E = 2 * (L : ℤ) ^ t * w + sg * δ := by
    have hdvd : ((2 * m : ℕ) : ℤ) ∣ (2 * (L : ℤ) ^ t * w + sg * δ) - E := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, hEc, hAint]
    have hlt' : |(2 * (L : ℤ) ^ t * w + sg * δ) - E| < ((2 * m : ℕ) : ℤ) := by
      have h1 : ((2 * m : ℕ) : ℤ) = 4 * (L : ℤ) ^ κ := by
        push_cast
        rw [hmZ]
        ring
      rw [h1]
      calc _ ≤ |2 * (L : ℤ) ^ t * w + sg * δ| + |E| := abs_sub _ _
        _ ≤ |2 * (L : ℤ) ^ t * w| + |sg * δ| + |E| := by linarith [abs_add_le (2 * (L : ℤ) ^ t * w) (sg * δ)]
        _ < _ := by linarith
    have := Int.eq_zero_of_abs_lt_dvd hdvd hlt'
    linarith
  have hEr : (E : ℝ) = 2 * (L : ℝ) ^ t * (w : ℝ) + ((sg * δ : ℤ) : ℝ) := by
    rw [hEeq]
    push_cast
    ring
  have hDb : |((sg * δ : ℤ) : ℝ)| ≤ (L : ℝ) ^ t := by
    exact_mod_cast hsgδ
  rw [levelSpacing_eq_pow_mul K t]
  have hxμ' : x μ = (L : ℝ) ^ t * levelSpacing L K 0 * (w : ℝ) + levelSpacing L K 0 / 2 * ((sg * δ : ℤ) : ℝ) := by
    rw [hxμ, hEr]
    ring
  have hD2 : |levelSpacing L K 0 / 2 * ((sg * δ : ℤ) : ℝ)| ≤ (L : ℝ) ^ t * levelSpacing L K 0 / 2 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < levelSpacing L K 0 / 2)]
    have := mul_le_mul_of_nonneg_left hDb (by positivity : 0 ≤ levelSpacing L K 0 / 2)
    linarith
  have hsplit : (L : ℝ) ^ t * levelSpacing L K 0 * (w : ℝ) - c μ = (x μ - c μ) - levelSpacing L K 0 / 2 * ((sg * δ : ℤ) : ℝ) := by
    rw [hxμ']
    ring
  rw [hsplit]
  calc _ ≤ |x μ - c μ| + |levelSpacing L K 0 / 2 * ((sg * δ : ℤ) : ℝ)| := abs_sub _ _
    _ ≤ _ := by linarith
theorem reflectedWeightSupport_holds : reflectedWeightSupportStatement := by
  intro L _ hL K κ t ρ H Λ h ht hρ _ hs h3 k
  obtain ⟨c, hc⟩ := hs.exists_ball
  have ha : 0 < levelSpacing L K t := levelSpacing_pos_aux K t
  set a := levelSpacing L K t with ha_def
  have hX : 3 ≤ ρ / a := by
    rw [le_div_iff₀ ha]
    exact h3
  set X := ρ / a with hXdef
  let I : Fin 4 → Finset ℤ := fun μ => Finset.Icc ⌈(c μ - ρ) / a - 1 / 2⌉ ⌊(c μ + ρ) / a + 1 / 2⌋
  let word : TorusSite (twoCellSide L κ t) → Fin 4 → ℤ := fun y μ => mirroredCoord (twoCellSide L κ t) (L ^ (κ - t)) (k μ : ℕ) (y μ)
  have hpow : (L : ℤ) ^ t * ((L ^ (κ - t) : ℕ) : ℤ) = (L : ℤ) ^ κ := by
    push_cast
    rw [← pow_add, Nat.add_sub_cancel' ht]
  have hLpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hnZ : ((twoCellSide L κ t : ℕ) : ℤ) = 2 * ((L ^ (κ - t) : ℕ) : ℤ) := by
    simp [twoCellSide]
  have hmZ : ((fineSide L t (twoCellSide L κ t) : ℕ) : ℤ) = 2 * (L : ℤ) ^ κ := by
    rw [fineSide_eq]
    push_cast
    rw [hnZ, ← hpow]
    push_cast
    ring
  have hmaps : ∀ y ∈ weightSupportSites L t (twoCellSide L κ t)
      (reflectedWeight (levelSpacing L K 0) (L ^ κ) (fun μ => (k μ : ℕ)) h), word y ∈ Fintype.piFinset I := by
    intro y hy
    simp only [weightSupportSites, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨p, ⟨hlt, cc, hcc, hcb⟩, hne⟩ := hy
    rw [Fintype.mem_piFinset]
    intro μ
    have hnear := mirroredCoord_near_center hρ hs (fun μ => (k μ : ℕ)) hc hpow (pow_pos hLpos _) hnZ hmZ hlt hcc μ
      (fun Y hY => exists_offset_of_mem_fineBlock hL t _ y cc hcb μ Y hY) hne
    have hnear' := abs_le.mp hnear
    simp only [I, Finset.mem_Icc]
    constructor
    · rw [Int.ceil_le, sub_le_iff_le_add, div_le_iff₀ ha]
      have : a * (word y μ : ℝ) - c μ = (word y μ : ℝ) * a - c μ := by ring
      nlinarith [hnear'.1]
    · rw [Int.le_floor, ← sub_le_iff_le_add, le_div_iff₀ ha]
      nlinarith [hnear'.2]
  have hinj : Set.InjOn word (weightSupportSites L t (twoCellSide L κ t)
      (reflectedWeight (levelSpacing L K 0) (L ^ κ) (fun μ => (k μ : ℕ)) h) : Set (TorusSite (twoCellSide L κ t))) := by
    intro y _ y' _ hyy
    funext μ
    have h1 : word y μ = word y' μ := congrFun hyy μ
    have h2 := congrArg (fun z : ℤ => (z : ZMod (twoCellSide L κ t))) h1
    simp only [word, mirroredCoord, ZMod.coe_valMinAbs] at h2
    have hs2 : ((-1 : ZMod (twoCellSide L κ t)) ^ (k μ : ℕ)) * ((-1 : ZMod (twoCellSide L κ t)) ^ (k μ : ℕ)) = 1 := by
      rw [← mul_pow]
      simp
    linear_combination ((-1 : ZMod (twoCellSide L κ t)) ^ (k μ : ℕ)) * h2 - (y μ - y' μ) * hs2
  have hcard := Finset.card_le_card_of_injOn word hmaps hinj
  rw [Fintype.card_piFinset] at hcard
  have hI : ∀ μ, ((I μ).card : ℝ) ≤ 2 * X + 2 := by
    intro μ
    simp only [I, Int.card_Icc]
    set A := ⌈(c μ - ρ) / a - 1 / 2⌉ with hA
    set B := ⌊(c μ + ρ) / a + 1 / 2⌋ with hB
    have h1 : (c μ - ρ) / a - 1 / 2 ≤ (A : ℝ) := Int.le_ceil _
    have h2 : (B : ℝ) ≤ (c μ + ρ) / a + 1 / 2 := Int.floor_le _
    have h3 : (c μ + ρ) / a - (c μ - ρ) / a = 2 * X := by
      rw [hXdef]
      ring
    have h4 : ((B + 1 - A : ℤ) : ℝ) ≤ 2 * X + 2 := by
      push_cast
      linarith
    rcases le_total 0 (B + 1 - A) with h6 | h6
    · have h7 : (((B + 1 - A).toNat : ℕ) : ℤ) = B + 1 - A := Int.toNat_of_nonneg h6
      have h8 : (((B + 1 - A).toNat : ℕ) : ℝ) = ((B + 1 - A : ℤ) : ℝ) := by exact_mod_cast h7
      rw [h8]
      exact h4
    · rw [Int.toNat_of_nonpos h6, Nat.cast_zero]
      linarith
  have hprod : ((∏ μ, (I μ).card : ℕ) : ℝ) ≤ (3 * X) ^ 4 := by
    push_cast
    calc ∏ μ, ((I μ).card : ℝ) ≤ ∏ _μ : Fin 4, (3 * X) :=
          Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun μ _ => (hI μ).trans (by linarith))
      _ = (3 * X) ^ 4 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc _ ≤ ((∏ μ, (I μ).card : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ (3 * X) ^ 4 := hprod
    _ = 81 * X ^ 4 := by ring
end YangMills.Construction.SmallTorusCopies
end
