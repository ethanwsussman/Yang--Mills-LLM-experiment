import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import YangMills.Construction.ColdStepAtMirrorFrames.BlocksCoverTheLevelBelow
import YangMills.Construction.ColdStepAtMirrorFrames.CellGeometryOfATorus
import YangMills.Construction.ColdStepAtMirrorFrames.ShiftOfTheCurlOfAFlatChain
import YangMills.Construction.ColdStepAtMirrorFrames.SizeOfTheCurlOfAFlatChain
import YangMills.Construction.ColdStepAtMirrorFrames.SquareSumOfTheCurlOfAFlatChain
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames.CurlSize
def offsetCube (m : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Ico 0 (m : ℤ)
def unitCorners : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Ico 0 2
theorem mem_offsetCube {m : ℕ} {h : Fin 4 → ℤ} : h ∈ offsetCube m ↔ ∀ i, 0 ≤ h i ∧ h i < m := by
  simp [offsetCube, Fintype.mem_piFinset]
theorem mem_unitCorners {h : Fin 4 → ℤ} : h ∈ unitCorners ↔ ∀ i, 0 ≤ h i ∧ h i < 2 := by
  simp [unitCorners, Fintype.mem_piFinset]
theorem card_offsetCube (m : ℕ) : (offsetCube m).card = m ^ 4 := by
  simp [offsetCube, Fintype.card_piFinset]
theorem card_unitCorners : unitCorners.card = 16 := by
  simp [unitCorners, Fintype.card_piFinset]
theorem offsetCube_one : offsetCube 1 = {0} := by
  ext h
  simp only [mem_offsetCube, Finset.mem_singleton, Nat.cast_one]
  constructor
  · intro hh
    funext i
    have := hh i
    simp only [Pi.zero_apply]
    omega
  · rintro rfl i
    simp
theorem sum_offsetCube_two_mul (m : ℕ) (hm : 0 < m) (f : (Fin 4 → ℤ) → ℝ) :
    ∑ h ∈ offsetCube (2 * m), f h = ∑ e ∈ unitCorners, ∑ h ∈ offsetCube m, f (h + (m : ℤ) • e) := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun x => x.2 + (m : ℤ) • x.1)
    (fun h => (fun i => h i / m, fun i => h i % m)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨e, h⟩ hx
    obtain ⟨he, hh⟩ := Finset.mem_product.mp hx
    replace he : e ∈ unitCorners := he
    replace hh : h ∈ offsetCube m := hh
    rw [mem_unitCorners] at he
    rw [mem_offsetCube] at hh
    rw [mem_offsetCube]
    intro i
    have h1 := he i
    have h2 := hh i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    have h3 : (m : ℤ) * e i = 0 ∨ (m : ℤ) * e i = m := by
      have : e i = 0 ∨ e i = 1 := by omega
      rcases this with h | h <;> simp [h]
    omega
  · intro h hh
    rw [mem_offsetCube] at hh
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · rw [mem_unitCorners]
      intro i
      have h1 := hh i
      push_cast at h1
      exact ⟨Int.ediv_nonneg h1.1 hm'.le, Int.ediv_lt_of_lt_mul hm' (by linarith [h1.2])⟩
    · rw [mem_offsetCube]
      intro i
      exact ⟨Int.emod_nonneg _ hm'.ne', Int.emod_lt_of_pos _ hm'⟩
  · rintro ⟨e, h⟩ hx
    obtain ⟨he, hh⟩ := Finset.mem_product.mp hx
    replace hh : h ∈ offsetCube m := hh
    rw [mem_offsetCube] at hh
    have key : ∀ i, (h i + (m : ℤ) * e i) / m = e i ∧ (h i + (m : ℤ) * e i) % m = h i := by
      intro i
      have h2 := hh i
      constructor
      · rw [Int.add_mul_ediv_left _ _ hm'.ne', Int.ediv_eq_zero_of_lt h2.1 h2.2, zero_add]
      · rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt h2.1 h2.2]
    refine Prod.ext ?_ ?_
    · funext i
      exact (key i).1
    · funext i
      exact (key i).2
  · intro h _
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact Int.emod_add_mul_ediv _ _
  · rintro ⟨e, h⟩ _
    rfl
def cubeMean (G : (Fin 4 → ℤ) → ℝ) (m : ℕ) : ℝ := (∑ h ∈ offsetCube m, G h) / (m : ℝ) ^ 4
theorem abs_sum_le_of_sum_sq_le (s : Finset (Fin 4 → ℤ)) (g : (Fin 4 → ℤ) → ℝ) (b S : ℝ) (hb : 0 ≤ b)
    (hc : (s.card : ℝ) * S ≤ b ^ 2) (hS : ∑ h ∈ s, g h ^ 2 ≤ S) : |∑ h ∈ s, g h| ≤ b := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := s) (f := g)
  have h2 : (∑ h ∈ s, g h) ^ 2 ≤ b ^ 2 :=
    h1.trans ((mul_le_mul_of_nonneg_left hS (by positivity)).trans hc)
  exact abs_le_of_sq_le_sq h2 hb
theorem abs_cubeMean_succ_sub_le (G : (Fin 4 → ℤ) → ℝ) (A : ℝ) (hA : 0 ≤ A) (k : ℕ)
    (h1 : ∀ e ∈ unitCorners, ∑ h ∈ offsetCube (2 ^ k), (G (h + ((2 ^ k : ℕ) : ℤ) • e) - G h) ^ 2 ≤ A * 2 ^ k) :
    |cubeMean G (2 ^ (k + 1)) - cubeMean G (2 ^ k)| ≤ Real.sqrt A * (1 / 2) ^ k := by
  have hpow : (2 : ℝ) ^ k = ((2 ^ k : ℕ) : ℝ) := by simp
  generalize hmdef : 2 ^ k = m at h1 hpow ⊢
  have hm : 0 < m := by rw [← hmdef]; positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have e1 : 2 ^ (k + 1) = 2 * m := by rw [← hmdef, pow_succ]; ring
  set s := Real.sqrt A with hs
  have hs2 : s ^ 2 = A := Real.sq_sqrt hA
  have hD : ∀ e ∈ unitCorners, |∑ h ∈ offsetCube m, (G (h + (m : ℤ) • e) - G h)| ≤ (m : ℝ) ^ 3 * s := by
    intro e he
    refine abs_sum_le_of_sum_sq_le _ _ _ (A * m) (by positivity) ?_ ?_
    · rw [card_offsetCube, mul_pow, hs2]
      push_cast
      have h5 : (m : ℝ) ^ 5 ≤ (m : ℝ) ^ 6 := pow_le_pow_right₀ hm1 (by norm_num)
      calc (m : ℝ) ^ 4 * (A * m) = (m : ℝ) ^ 5 * A := by ring
        _ ≤ (m : ℝ) ^ 6 * A := mul_le_mul_of_nonneg_right h5 hA
        _ = ((m : ℝ) ^ 3) ^ 2 * A := by ring
    · have := h1 e he
      rwa [hpow] at this
  have hdiff : cubeMean G (2 ^ (k + 1)) - cubeMean G m =
      (∑ e ∈ unitCorners, ∑ h ∈ offsetCube m, (G (h + (m : ℤ) • e) - G h)) / (16 * (m : ℝ) ^ 4) := by
    unfold cubeMean
    rw [e1, sum_offsetCube_two_mul m hm G]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, card_unitCorners, nsmul_eq_mul]
    push_cast
    field_simp
    ring
  rw [hdiff, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 16 * (m : ℝ) ^ 4),
    div_le_iff₀ (by positivity)]
  have hhalf : (1 / 2 : ℝ) ^ k = 1 / m := by rw [one_div_pow, hpow]
  rw [hhalf]
  calc |∑ e ∈ unitCorners, ∑ h ∈ offsetCube m, (G (h + (m : ℤ) • e) - G h)|
      ≤ ∑ e ∈ unitCorners, |∑ h ∈ offsetCube m, (G (h + (m : ℤ) • e) - G h)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ unitCorners, (m : ℝ) ^ 3 * s := Finset.sum_le_sum hD
    _ = s * (1 / m) * (16 * (m : ℝ) ^ 4) := by
      rw [Finset.sum_const, card_unitCorners, nsmul_eq_mul]
      push_cast
      field_simp
theorem abs_apply_zero_le_dyadic (G : (Fin 4 → ℤ) → ℝ) (A S : ℝ) (hA : 0 ≤ A) (hS : 0 ≤ S) (K : ℕ)
    (h1 : ∀ k < K, ∀ e ∈ unitCorners,
      ∑ h ∈ offsetCube (2 ^ k), (G (h + ((2 ^ k : ℕ) : ℤ) • e) - G h) ^ 2 ≤ A * 2 ^ k)
    (h2 : ∑ h ∈ offsetCube (2 ^ K), G h ^ 2 ≤ S) :
    |G 0| ≤ 2 * Real.sqrt A + Real.sqrt S / ((2 : ℝ) ^ K) ^ 2 := by
  set s := Real.sqrt A with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hind : ∀ k ≤ K, |G 0| ≤ |cubeMean G (2 ^ k)| + 2 * s * (1 - (1 / 2) ^ k) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [cubeMean, offsetCube_one]
    | succ k ih =>
      intro hk
      have h3 := ih (by omega)
      have h4 := abs_cubeMean_succ_sub_le G A hA k (h1 k (by omega))
      have h5 := abs_sub_abs_le_abs_sub (cubeMean G (2 ^ k)) (cubeMean G (2 ^ (k + 1)))
      rw [abs_sub_comm (cubeMean G (2 ^ k))] at h5
      have e1 : 2 * s * (1 - (1 / 2 : ℝ) ^ (k + 1)) = 2 * s - s * (1 / 2) ^ k := by
        rw [pow_succ]; ring
      have e2 : 2 * s * (1 - (1 / 2 : ℝ) ^ k) = 2 * s - 2 * (s * (1 / 2) ^ k) := by ring
      rw [e1]
      rw [e2] at h3
      linarith
  have h3 := hind K le_rfl
  have hM : |cubeMean G (2 ^ K)| ≤ Real.sqrt S / ((2 : ℝ) ^ K) ^ 2 := by
    have hpow : (2 : ℝ) ^ K = ((2 ^ K : ℕ) : ℝ) := by simp
    rw [hpow]
    have hm : 0 < 2 ^ K := by positivity
    generalize 2 ^ K = m at h2 hm ⊢
    unfold cubeMean
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) ^ 4), div_le_iff₀ (by positivity)]
    have hb : |∑ h ∈ offsetCube m, G h| ≤ (m : ℝ) ^ 2 * Real.sqrt S := by
      refine abs_sum_le_of_sum_sq_le _ _ _ S (by positivity) ?_ h2
      rw [card_offsetCube, mul_pow, Real.sq_sqrt hS]
      push_cast
      apply le_of_eq
      ring
    calc |∑ h ∈ offsetCube m, G h| ≤ (m : ℝ) ^ 2 * Real.sqrt S := hb
      _ = Real.sqrt S / (m : ℝ) ^ 2 * (m : ℝ) ^ 4 := by field_simp
  have h4 : 2 * s * (1 - (1 / 2 : ℝ) ^ K) ≤ 2 * s := by
    have : (0 : ℝ) ≤ (1 / 2) ^ K := by positivity
    nlinarith
  linarith
variable {F : BlockFrame}
theorem siteOfCoords_add (j : ℕ) (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j (a + b) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem natAbs_valMinAbs_intCast_le (N : ℕ) [NeZero N] (b : ℤ) :
    ((b : ZMod N).valMinAbs).natAbs ≤ b.natAbs := by apply _root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le <;> assumption
theorem period_pos (hodd : Odd F.blockSide) (hs : ∀ i, 64 ≤ F.extent i) (j : ℕ) (i : Fin 4) :
    0 < F.period j i := by
  have h1 := hs i
  have h2 := hodd.pos
  unfold BlockFrame.period
  positivity
theorem siteCoords_intCast {j : ℕ} (x : F.Site j) (i : Fin 4) (hpos : 0 < F.period j i) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by
  have : NeZero (F.period j i) := ⟨hpos.ne'⟩
  simp [siteCoords]
theorem period_depth (F : BlockFrame) (i : Fin 4) :
    F.period F.depth i = F.period F.top i * F.blockSide := by
  simp [BlockFrame.period, BlockFrame.top]
theorem enclosingCell_apply_of_intCast (hodd : Odd F.blockSide) (hs : ∀ i, 64 ≤ F.extent i)
    (x : F.Site F.depth) (i : Fin 4) (w : ℤ)
    (hw : ((w : ℤ) : ZMod (F.period F.depth i)) = x i) :
    enclosingCell x i = (((w + ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ) : ℤ) :
      ZMod (F.period F.top i)) := by
  have hL : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
  have hc := siteCoords_intCast x i (period_pos hodd hs F.depth i)
  have h0 : ((w - siteCoords x i : ℤ) : ZMod (F.period F.depth i)) = 0 := by
    rw [Int.cast_sub, hw, hc, sub_self]
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  rw [period_depth] at hm
  push_cast at hm
  have hw' : w + ((F.blockSide : ℤ) - 1) / 2 =
      (siteCoords x i + ((F.blockSide : ℤ) - 1) / 2) + (m * (F.period F.top i : ℤ)) * F.blockSide := by
    linear_combination hm
  have hn : F.top - F.depth = 1 := by simp [BlockFrame.top]
  show (((siteCoords x i + ((F.blockSide : ℤ) ^ (F.top - F.depth) - 1) / 2) /
    (F.blockSide : ℤ) ^ (F.top - F.depth) : ℤ) : ZMod (F.period F.top i)) = _
  rw [hn, pow_one, hw', Int.add_mul_ediv_right _ _ hL.ne']
  push_cast
  simp
theorem centred_ediv_ediv (A P c : ℤ) (hA : 0 < A) (hP : 0 < P) (hAo : A % 2 = 1) (hPo : P % 2 = 1) :
    ((c + (A - 1) / 2) / A + (P - 1) / 2) / P = (c + (A * P - 1) / 2) / (A * P) := by
  obtain ⟨u, rfl⟩ : ∃ u, A = 2 * u + 1 := ⟨A / 2, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, P = 2 * v + 1 := ⟨P / 2, by omega⟩
  have e1 : (2 * u + 1 - 1) / 2 = u := by omega
  have e2 : (2 * v + 1 - 1) / 2 = v := by omega
  have e3 : ((2 * u + 1) * (2 * v + 1) - 1) / 2 = 2 * u * v + u + v := by
    have : (2 * u + 1) * (2 * v + 1) - 1 = 2 * (2 * u * v + u + v) := by ring
    rw [this]
    omega
  rw [e1, e2, e3, ← Int.add_mul_ediv_right _ _ hA.ne',
    Int.ediv_ediv_of_nonneg hA.le]
  congr 1
  ring
theorem enclosingCell_depthSite (hodd : Odd F.blockSide) (hs : ∀ i, 64 ≤ F.extent i) {j : ℕ}
    (hj : j ≤ F.top) (x : F.Site j) : enclosingCell (depthSite x) = enclosingCell x := by
  have hL : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
  have hLo : (F.blockSide : ℤ) % 2 = 1 := by
    have : Odd (F.blockSide : ℤ) := by exact_mod_cast hodd
    exact Int.odd_iff.mp this
  by_cases h : j ≤ F.depth
  · unfold depthSite
    rw [if_pos h]
    funext i
    unfold ancestorSite
    rw [enclosingCell_apply_of_intCast hodd hs _ i _ rfl]
    show _ = (((siteCoords x i + ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2) /
      (F.blockSide : ℤ) ^ (F.top - j) : ℤ) : ZMod (F.period F.top i))
    have hexp : F.top - j = (F.depth - j) + 1 := by simp only [BlockFrame.top]; omega
    rw [hexp, pow_succ]
    congr 1
    exact centred_ediv_ediv _ _ _ (by positivity) hL
      (Int.odd_iff.mp (Odd.pow (by exact_mod_cast hodd))) hLo
  · have hjn : j = F.top := by simp only [BlockFrame.top] at hj ⊢; omega
    subst hjn
    unfold depthSite
    rw [if_neg h]
    funext i
    rw [enclosingCell_apply_of_intCast hodd hs _ i _ rfl]
    show _ = (((siteCoords x i + ((F.blockSide : ℤ) ^ (F.top - F.top) - 1) / 2) /
      (F.blockSide : ℤ) ^ (F.top - F.top) : ℤ) : ZMod (F.period F.top i))
    have e1 : ((F.blockSide : ℤ) * siteCoords x i + ((F.blockSide : ℤ) - 1) / 2) /
        (F.blockSide : ℤ) = siteCoords x i := by
      rw [add_comm, Int.add_mul_ediv_left _ _ hL.ne',
        Int.ediv_eq_zero_of_lt (by omega) (by omega), zero_add]
    rw [e1]
    simp
theorem ediv_le_add_ediv_le (L v h : ℤ) (hL : 0 < L) (h0 : 0 ≤ h) (h1 : h < L) :
    v / L ≤ (v + h) / L ∧ (v + h) / L ≤ v / L + 1 := by
  constructor
  · exact Int.ediv_le_ediv hL (by omega)
  · have : (v + 1 * L) / L = v / L + 1 := Int.add_mul_ediv_right _ _ hL.ne'
    rw [← this]
    exact Int.ediv_le_ediv hL (by omega)
theorem ediv_sub_le_sub_ediv_le (L v h : ℤ) (hL : 0 < L) (h0 : 0 ≤ h) (h1 : h < L) :
    v / L - 1 ≤ (v - h) / L ∧ (v - h) / L ≤ v / L := by
  constructor
  · have : (v + (-1) * L) / L = v / L + (-1) := Int.add_mul_ediv_right _ _ hL.ne'
    have h2 : v / L - 1 = (v + (-1) * L) / L := by rw [this]; ring
    rw [h2]
    exact Int.ediv_le_ediv hL (by omega)
  · exact Int.ediv_le_ediv hL (by omega)
def signsToward (p : F.Site F.depth) (Y : F.Cell) : Fin 4 → ℤ := fun i =>
  if 0 ≤ ((enclosingCell p - Y) i).valMinAbs then -1 else 1
theorem signsToward_eq_one_or_neg_one (p : F.Site F.depth) (Y : F.Cell) (i : Fin 4) :
    signsToward p Y i = 1 ∨ signsToward p Y i = -1 := by
  unfold signsToward
  split <;> simp
def orientedOffsetSite (p : F.Site F.depth) (σ h : Fin 4 → ℤ) : F.Site F.depth :=
  p + siteOfCoords F.depth (σ * h)
theorem orientedOffsetSite_apply (p : F.Site F.depth) (σ h : Fin 4 → ℤ) (i : Fin 4) :
    orientedOffsetSite p σ h i = p i + ((σ i * h i : ℤ) : ZMod (F.period F.depth i)) := rfl
theorem orientedOffsetSite_zero (p : F.Site F.depth) (σ : Fin 4 → ℤ) :
    orientedOffsetSite p σ 0 = p := by
  funext i
  simp [orientedOffsetSite_apply]
theorem orientedOffsetSite_injOn (hodd : Odd F.blockSide) (hs : ∀ i, 64 ≤ F.extent i)
    (p : F.Site F.depth) (σ : Fin 4 → ℤ) (hσ : ∀ i, σ i = 1 ∨ σ i = -1) {m : ℕ}
    (hm : m ≤ F.blockSide) :
    Set.InjOn (orientedOffsetSite p σ) (offsetCube m : Set (Fin 4 → ℤ)) := by
  intro h hh h' hh' heq
  have hb := mem_offsetCube.mp (Finset.mem_coe.mp hh)
  have hb' := mem_offsetCube.mp (Finset.mem_coe.mp hh')
  funext i
  have h1 := congrFun heq i
  rw [orientedOffsetSite_apply, orientedOffsetSite_apply] at h1
  have h2 := add_left_cancel h1
  have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h2
  have hper : (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ) := by
    have : F.blockSide ≤ F.period F.depth i := by
      rw [period_depth]
      have : 0 < F.period F.top i := period_pos hodd hs F.top i
      exact Nat.le_mul_of_pos_left _ this
    exact_mod_cast this
  have h4 := hb i
  have h5 := hb' i
  have habs : |σ i * h' i - σ i * h i| < (F.period F.depth i : ℤ) := by
    rw [abs_lt]
    rcases hσ i with h | h <;> rw [h] <;> constructor <;> omega
  have h6 := Int.eq_zero_of_abs_lt_dvd h3 habs
  rcases hσ i with h | h <;> rw [h] at h6 <;> omega
theorem siteSupDist_orientedOffsetSite_le (hodd : Odd F.blockSide) (hs : ∀ i, 64 ≤ F.extent i)
    (p : F.Site F.depth) (σ : Fin 4 → ℤ) (hσ : ∀ i, σ i = 1 ∨ σ i = -1) {m : ℕ}
    (hm : m ≤ F.blockSide) {h : Fin 4 → ℤ} (hh : h ∈ offsetCube m) :
    siteSupDist (orientedOffsetSite p σ h) p ≤ F.blockSide := by
  unfold siteSupDist
  refine Finset.sup_le fun i _ => ?_
  have : NeZero (F.period F.depth i) := ⟨(period_pos hodd hs F.depth i).ne'⟩
  rw [orientedOffsetSite_apply, add_sub_cancel_left]
  refine (natAbs_valMinAbs_intCast_le _ _).trans ?_
  have h1 := mem_offsetCube.mp hh i
  rcases hσ i with h' | h' <;> rw [h'] <;> omega
theorem cellSupDist_enclosingCell_orientedOffsetSite_le (hodd : Odd F.blockSide)
    (hs : ∀ i, 64 ≤ F.extent i) (p : F.Site F.depth) (Y : F.Cell)
    (hd : cellSupDist (enclosingCell p) Y ≤ 2) {m : ℕ} (hm : m ≤ F.blockSide) {h : Fin 4 → ℤ}
    (hh : h ∈ offsetCube m) :
    cellSupDist (enclosingCell (orientedOffsetSite p (signsToward p Y) h)) Y ≤ 2 := by
  unfold cellSupDist
  refine Finset.sup_le fun i _ => ?_
  have : NeZero (F.period F.top i) := ⟨(period_pos hodd hs F.top i).ne'⟩
  have hL : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
  have h1 := mem_offsetCube.mp hh i
  have hc := siteCoords_intCast p i (period_pos hodd hs F.depth i)
  set σ := signsToward p Y with hσdef
  have hcell0 := enclosingCell_apply_of_intCast hodd hs p i (siteCoords p i) hc
  have hcell1 := enclosingCell_apply_of_intCast hodd hs (orientedOffsetSite p σ h) i
    (siteCoords p i + σ i * h i) (by rw [orientedOffsetSite_apply, Int.cast_add, hc])
  obtain ⟨r, hr⟩ : ∃ r : ℤ, r = ((F.blockSide : ℤ) - 1) / 2 := ⟨_, rfl⟩
  rw [← hr] at hcell0 hcell1
  set d := ((enclosingCell p - Y) i).valMinAbs with hddef
  have hd' : d.natAbs ≤ 2 := by
    have := Finset.le_sup (f := fun i => ((enclosingCell p i - Y i).valMinAbs).natAbs)
      (Finset.mem_univ i)
    exact this.trans hd
  have hdcast : (d : ZMod (F.period F.top i)) = enclosingCell p i - Y i := ZMod.coe_valMinAbs _
  set u0 := (siteCoords p i + r) / (F.blockSide : ℤ) with hu0
  set u1 := (siteCoords p i + σ i * h i + r) / (F.blockSide : ℤ) with hu1
  have hval : enclosingCell (orientedOffsetSite p σ h) i - Y i =
      ((d + (u1 - u0) : ℤ) : ZMod (F.period F.top i)) := by
    rw [hcell1]
    push_cast
    rw [hdcast, hcell0]
    ring
  rw [hval]
  refine (natAbs_valMinAbs_intCast_le _ _).trans ?_
  by_cases hsign : 0 ≤ d
  · have hσi : σ i = -1 := if_pos hsign
    have e : siteCoords p i + σ i * h i + r = (siteCoords p i + r) - h i := by rw [hσi]; ring
    have := ediv_sub_le_sub_ediv_le (F.blockSide : ℤ) (siteCoords p i + r) (h i) hL h1.1 (by omega)
    rw [← e] at this
    omega
  · have hσi : σ i = 1 := if_neg hsign
    have e : siteCoords p i + σ i * h i + r = (siteCoords p i + r) + h i := by rw [hσi]; ring
    have := ediv_le_add_ediv_le (F.blockSide : ℤ) (siteCoords p i + r) (h i) hL h1.1 (by omega)
    rw [← e] at this
    omega
theorem sum_comp_le_of_injOn {β : Type*} (s : Finset (Fin 4 → ℤ)) (T : Finset β)
    (Φ : (Fin 4 → ℤ) → β) (hΦ : Set.InjOn Φ (s : Set (Fin 4 → ℤ))) (hT : ∀ h ∈ s, Φ h ∈ T)
    (f : β → ℝ) (hf : ∀ x, 0 ≤ f x) : ∑ h ∈ s, f (Φ h) ≤ ∑ x ∈ T, f x := by
  classical
  rw [← Finset.sum_image (f := f) (g := Φ) hΦ]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ => hf x
  intro x hx
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
  exact hT h hh
theorem chainEnergyOnCells_nonneg {a : ℝ} (ha : 0 ≤ a) (B : FormChain F) (X : Set F.Cell) :
    0 ≤ chainEnergyOnCells a B X := by
  unfold chainEnergyOnCells
  refine add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (mul_nonneg ha (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _))
open Classical in
theorem chainEnergyOnSites_depthBall_le (hodd : Odd F.blockSide) (hs : ∀ i, 64 ≤ F.extent i)
    {a : ℝ} (ha : 0 ≤ a) (B : FormChain F) (p : F.Site F.depth) (Y : F.Cell)
    (hd : cellSupDist (enclosingCell p) Y ≤ 2)
    (htri : ∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z)
    (hgeo : ∀ x y : F.Site F.depth,
      F.blockSide * cellSupDist (enclosingCell x) (enclosingCell y) ≤ siteSupDist x y + F.blockSide) :
    chainEnergyOnSites a B (depthBall p (9 * F.blockSide)) ≤ chainEnergyOnCells a B (cellBall Y 24) := by
  have key : ∀ {j : ℕ} (x : F.Site j), j ≤ F.top → depthSite x ∈ depthBall p (9 * F.blockSide) →
      enclosingCell x ∈ cellBall Y 24 := by
    intro j x hj hx
    have h1 : siteSupDist (depthSite x) p ≤ 9 * F.blockSide := hx
    have h2 := hgeo (depthSite x) p
    rw [enclosingCell_depthSite hodd hs hj] at h2
    have hLpos := hodd.pos
    have h3 : cellSupDist (enclosingCell x) (enclosingCell p) ≤ 10 := by
      have : F.blockSide * cellSupDist (enclosingCell x) (enclosingCell p) ≤ F.blockSide * 10 := by
        omega
      exact Nat.le_of_mul_le_mul_left this hLpos
    have h4 := htri (enclosingCell x) (enclosingCell p) Y
    show cellSupDist (enclosingCell x) Y ≤ 24
    omega
  unfold chainEnergyOnSites chainEnergyOnCells
  refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ ha)
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨h1, key x (Nat.zero_le _) h2⟩
  · refine Finset.sum_le_sum fun j hj => ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨h1, key x (Finset.mem_range.mp hj) h2⟩
theorem curlSizeBound (hShift : CurlShiftBound) (hSquare : CurlSquareSumBound)
    (hCells : CubicTorusCellGeometry) (hBlocks : BlocksCoverLowerLevel) : CurlSizeBound := by
  intro a ha
  obtain ⟨C1, hC1, L1, h9⟩ := hShift a ha
  obtain ⟨C2, hC2, L2, hsq⟩ := hSquare a ha
  have hr1 : 0 ≤ Real.sqrt C1 := Real.sqrt_nonneg _
  have hr2 : 0 < Real.sqrt C2 := Real.sqrt_pos.mpr hC2
  refine ⟨2 * Real.sqrt C1 + 4 * Real.sqrt C2, by linarith, max L1 L2, ?_⟩
  intro F c B hodd hL hcub hflat Y p e he hd
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨n, hn64, hside⟩ := hcub
  have hs : ∀ i, 64 ≤ F.extent i := fun i => by rw [hside i]; exact hn64
  have hcub' : IsLargeCubicTorus F := ⟨n, hn64, hside⟩
  obtain ⟨-, -, -, htri, hgeo⟩ := (hCells.1 F hodd hcub')
  have hall : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth :=
    hBlocks F hodd fun i => by have := hs i; omega
  have hLpos : 0 < F.blockSide := hodd.pos
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hLpos
  have hL1R : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hLpos
  set E := chainEnergyOnCells a B (cellBall Y 24) with hE
  have hE0 : 0 ≤ E := chainEnergyOnCells_nonneg ha0 B _
  have hEs : chainEnergyOnSites a B (depthBall p (9 * F.blockSide)) ≤ E :=
    chainEnergyOnSites_depthBall_le hodd hs ha0 B p Y hd htri hgeo
  set σ := signsToward p Y with hσdef
  have hσ : ∀ i, σ i = 1 ∨ σ i = -1 := signsToward_eq_one_or_neg_one p Y
  set G : (Fin 4 → ℤ) → ℝ := fun h => plaquetteCurl (B F.depth) (orientedOffsetSite p σ h) e.1 e.2
    with hG
  set K := Nat.log 2 F.blockSide with hK
  have hKle : 2 ^ K ≤ F.blockSide := Nat.pow_log_le_self 2 hLpos.ne'
  have hKlt : F.blockSide < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) F.blockSide
  have h1 : ∀ k < K, ∀ e' ∈ unitCorners,
      ∑ h ∈ offsetCube (2 ^ k), (G (h + ((2 ^ k : ℕ) : ℤ) • e') - G h) ^ 2 ≤
        (C1 * E / F.blockSide) * 2 ^ k := by
    intro k hk e' he'
    have hkL : 2 ^ k ≤ F.blockSide := (Nat.pow_le_pow_right (by norm_num) hk.le).trans hKle
    by_cases h0 : e' = 0
    · subst h0
      simp only [smul_zero, add_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Finset.sum_const_zero]
      positivity
    · obtain ⟨i0, hi0⟩ := Function.ne_iff.mp h0
      have hbit := mem_unitCorners.mp he'
      have hi1 : e' i0 = 1 := by
        have := hbit i0
        simp only [Pi.zero_apply] at hi0
        omega
      set H : Fin 4 → ℤ := σ * (((2 ^ k : ℕ) : ℤ) • e') with hH
      have hHabs : ∀ i, |H i| ≤ ((2 ^ k : ℕ) : ℤ) := by
        intro i
        have h2 := hbit i
        have h3 : e' i = 0 ∨ e' i = 1 := by omega
        simp only [hH, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
        rcases hσ i with h | h <;> rcases h3 with h' | h' <;> rw [h, h'] <;> simp
      have hHex : ∃ i, |H i| = ((2 ^ k : ℕ) : ℤ) := by
        refine ⟨i0, ?_⟩
        simp only [hH, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
        rcases hσ i0 with h | h <;> rw [h, hi1] <;> simp
      have hb := h9 F c B hodd ((le_max_left _ _).trans hL) hcub' hflat p H (2 ^ k) hHabs hHex
        Nat.one_le_two_pow hkL
      have hmove : ∀ h, orientedOffsetSite p σ (h + ((2 ^ k : ℕ) : ℤ) • e') =
          orientedOffsetSite p σ h + siteOfCoords F.depth H := by
        intro h
        unfold orientedOffsetSite
        rw [mul_add, siteOfCoords_add, add_assoc]
      set f : F.Site F.depth → ℝ := fun x =>
        (plaquetteCurl (B F.depth) (x + siteOfCoords F.depth H) e.1 e.2 -
          plaquetteCurl (B F.depth) x e.1 e.2) ^ 2 with hf
      have hstep : ∑ h ∈ offsetCube (2 ^ k), (G (h + ((2 ^ k : ℕ) : ℤ) • e') - G h) ^ 2 =
          ∑ h ∈ offsetCube (2 ^ k), f (orientedOffsetSite p σ h) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        simp only [hG, hf, hmove]
      rw [hstep]
      calc ∑ h ∈ offsetCube (2 ^ k), f (orientedOffsetSite p σ h)
          ≤ ∑ x ∈ (sitesOfCells (finiteCells F) F.depth).filter
              (fun x => siteSupDist x p ≤ F.blockSide), f x := by
            refine sum_comp_le_of_injOn _ _ _ (orientedOffsetSite_injOn hodd hs p σ hσ hkL) ?_ f
              fun x => sq_nonneg _
            intro h hh
            exact Finset.mem_filter.mpr ⟨hall _, siteSupDist_orientedOffsetSite_le hodd hs p σ hσ hkL hh⟩
        _ ≤ ∑ x ∈ (sitesOfCells (finiteCells F) F.depth).filter
              (fun x => siteSupDist x p ≤ F.blockSide),
            ∑ e ∈ orientedPlanes,
              (plaquetteCurl (B F.depth) (x + siteOfCoords F.depth H) e.1 e.2 -
                plaquetteCurl (B F.depth) x e.1 e.2) ^ 2 := by
            refine Finset.sum_le_sum fun x _ => ?_
            exact Finset.single_le_sum (f := fun e : Fin 4 × Fin 4 =>
              (plaquetteCurl (B F.depth) (x + siteOfCoords F.depth H) e.1 e.2 -
                plaquetteCurl (B F.depth) x e.1 e.2) ^ 2)
              (fun _ _ => sq_nonneg _) he
        _ ≤ C1 * (((2 ^ k : ℕ) : ℝ) / F.blockSide) *
              chainEnergyOnSites a B (depthBall p (9 * F.blockSide)) := hb
        _ ≤ C1 * (((2 ^ k : ℕ) : ℝ) / F.blockSide) * E :=
            mul_le_mul_of_nonneg_left hEs (by positivity)
        _ = (C1 * E / F.blockSide) * 2 ^ k := by
            push_cast
            ring
  have h2 : ∑ h ∈ offsetCube (2 ^ K), G h ^ 2 ≤ C2 * E := by
    have hb := hsq F c B hodd ((le_max_right _ _).trans hL) hcub' hflat Y
    set f : F.Site F.depth → ℝ := fun x => plaquetteCurl (B F.depth) x e.1 e.2 ^ 2 with hf
    calc ∑ h ∈ offsetCube (2 ^ K), G h ^ 2
          = ∑ h ∈ offsetCube (2 ^ K), f (orientedOffsetSite p σ h) := rfl
      _ ≤ ∑ x ∈ (sitesOfCells (finiteCells F) F.depth).filter
            (fun x => cellSupDist (enclosingCell x) Y ≤ 2), f x := by
          refine sum_comp_le_of_injOn _ _ _ (orientedOffsetSite_injOn hodd hs p σ hσ hKle) ?_ f
            fun x => sq_nonneg _
          intro h hh
          exact Finset.mem_filter.mpr
            ⟨hall _, cellSupDist_enclosingCell_orientedOffsetSite_le hodd hs p Y hd hKle hh⟩
      _ ≤ ∑ x ∈ (sitesOfCells (finiteCells F) F.depth).filter
            (fun x => cellSupDist (enclosingCell x) Y ≤ 2),
          ∑ e ∈ orientedPlanes, plaquetteCurl (B F.depth) x e.1 e.2 ^ 2 := by
          refine Finset.sum_le_sum fun x _ => ?_
          exact Finset.single_le_sum
            (f := fun e : Fin 4 × Fin 4 => plaquetteCurl (B F.depth) x e.1 e.2 ^ 2)
            (fun _ _ => sq_nonneg _) he
      _ ≤ C2 * E := hb
  have hdy := abs_apply_zero_le_dyadic G (C1 * E / F.blockSide) (C2 * E) (by positivity)
    (by positivity) K h1 h2
  have hG0 : G 0 = plaquetteCurl (B F.depth) p e.1 e.2 := by
    simp only [hG, orientedOffsetSite_zero]
  rw [hG0] at hdy
  refine hdy.trans ?_
  have hrL : 0 < Real.sqrt F.blockSide := Real.sqrt_pos.mpr hLR
  have hpw : (F.blockSide : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt F.blockSide := by
    rw [Real.rpow_neg hLR.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hpw]
  have hA1 : Real.sqrt (C1 * E / F.blockSide) =
      Real.sqrt C1 * Real.sqrt E / Real.sqrt F.blockSide := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul hC1.le]
  have hA2 : Real.sqrt (C2 * E) = Real.sqrt C2 * Real.sqrt E := Real.sqrt_mul hC2.le _
  rw [hA1, hA2]
  have hrE : 0 ≤ Real.sqrt E := Real.sqrt_nonneg _
  set D : ℝ := (2 : ℝ) ^ K with hD
  have hD1 : 1 ≤ D := one_le_pow₀ (by norm_num)
  have hLD : (F.blockSide : ℝ) ≤ 2 * D := by
    have : (F.blockSide : ℝ) < ((2 ^ (K + 1) : ℕ) : ℝ) := by exact_mod_cast hKlt
    rw [hD]
    push_cast at this
    rw [pow_succ] at this
    linarith
  have hsqrtL : Real.sqrt F.blockSide ≤ F.blockSide := by
    rw [Real.sqrt_le_left hLR.le]
    nlinarith
  have hlast : Real.sqrt C2 * Real.sqrt E / D ^ 2 ≤
      4 * Real.sqrt C2 * Real.sqrt E / Real.sqrt F.blockSide := by
    rw [div_le_div_iff₀ (by positivity) hrL]
    have hk : Real.sqrt F.blockSide ≤ 4 * D ^ 2 := by nlinarith
    have hpos : 0 ≤ Real.sqrt C2 * Real.sqrt E := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hk hpos]
  calc 2 * (Real.sqrt C1 * Real.sqrt E / Real.sqrt F.blockSide) + Real.sqrt C2 * Real.sqrt E / D ^ 2
      ≤ 2 * (Real.sqrt C1 * Real.sqrt E / Real.sqrt F.blockSide) +
          4 * Real.sqrt C2 * Real.sqrt E / Real.sqrt F.blockSide := by linarith
    _ = (2 * Real.sqrt C1 + 4 * Real.sqrt C2) * (1 / Real.sqrt F.blockSide) * Real.sqrt E := by ring
end YangMills.Construction.ColdStepAtMirrorFrames.CurlSize
end
