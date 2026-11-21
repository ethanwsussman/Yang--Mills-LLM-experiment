import YangMills.Construction.ColdChainAtEveryLevel.DifferencesAreNearlyFlatProof
import YangMills.Construction.ColdChainAtEveryLevel.PlaquettesNearACell
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false

noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def smoothWeightCurlCommutatorStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ θ₀ δ₀ : ℝ, 0 < θ₀ ∧ θ₀ ≤ 1 / 8 ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 8 ∧
    ∀ (F : BlockFrame) (S : Finset F.Cell) (R : F.GaugeField 0), Odd F.blockSide → 5 ≤ F.blockSide →
      ∀ (φ : F.Cell → ℝ) (θ δ : ℝ) (p : F.Site 0), |θ| ≤ θ₀ → 0 ≤ δ → δ ≤ δ₀ →
        (∀ y y', |φ y - φ y'| ≤ δ * cellSupDist y y') →
        ∃ ω : F.Site 0 → ℝ, (∀ x, 0 < ω x) ∧
          (∀ x ∈ sitesOfCells S 0, Real.exp (-δ) * classWeight F φ θ p 0 x ≤ ω x ∧
            ω x ≤ Real.exp δ * classWeight F φ θ p 0 x) ∧
          ∀ u : F.Site 0 → Fin 4 → imaginaryQuaternions,
            ∑ q ∈ plaquettesOver S S 0, ((ω q.1)⁻¹ *
                ‖linearizedCurl R (fun x i => (ω x ^ 2) • u x i) q - (ω q.1 ^ 2) • linearizedCurl R u q‖) ^ 2 ≤
              ε ^ 2 * weightedBondL2Norm S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
                (fun x i => u x i) ^ 2
end YangMills.Construction.BlockAverages
end

noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace SmoothWeightCurl
variable {F : BlockFrame}
theorem natAbs_valMinAbs_intCast_le (n : ℕ) (d : ℤ) : ((d : ZMod n).valMinAbs).natAbs ≤ d.natAbs := by apply _root_.YangMills.Construction.BlockWeights.natAbs_valMinAbs_intCast_le <;> assumption
theorem period_eq {j : ℕ} (i : Fin 4) :
    (F.period j i : ℤ) = (F.extent i : ℤ) * (F.blockSide : ℤ) ^ (F.top - j) := by
  simp [BlockFrame.period]
theorem mem_centredCube (M : ℕ) (h : Fin 4 → ℤ) :
    h ∈ centredCube M ↔ ∀ i, -(((M : ℤ) - 1) / 2) ≤ h i ∧ h i ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.CutAction.mem_centredCube <;> assumption
theorem odd_pow_half (hodd : Odd F.blockSide) (e : ℕ) : ∃ k : ℕ, F.blockSide ^ e = 2 * k + 1 ∧
    (((F.blockSide ^ e : ℕ) : ℤ) - 1) / 2 = k ∧ (F.blockSide : ℤ) ^ e = 2 * (k : ℤ) + 1 := by apply _root_.YangMills.Construction.BlockLines.odd_pow_eq_two_mul_add_one <;> assumption
theorem scaleRadius_pos (hL : 0 < F.blockSide) (j : ℕ) (p : F.Site 0) (x : F.Site j) :
    0 < scaleRadius F j p x := by apply _root_.YangMills.Construction.CoordinateSeminorms.scaleRadius_pos <;> assumption
theorem norm_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : ‖adjointAction g w‖ = ‖w‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction <;> assumption
theorem add_sq_le_two_mul (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]
variable {S : Finset F.Cell}
theorem enclosingCell_cellCentre_add (hodd : Odd F.blockSide) {j : ℕ} (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j z + siteOfCoords j h) = z := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_cellCentre_add <;> assumption
theorem enclosingCell_mem (hodd : Odd F.blockSide) {j : ℕ} (x : F.Site j) (hx : x ∈ sitesOfCells S j) :
    enclosingCell x ∈ S := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_mem <;> assumption
theorem natAbs_le_baseDistance {l : ℕ} (x : F.Site l) (p : F.Site 0) (i : Fin 4) :
    (((baseSite x - p : F.Site 0) i).valMinAbs).natAbs ≤ baseDistance x p :=
  Finset.le_sup (f := fun i => (((baseSite x - p : F.Site 0) i).valMinAbs).natAbs) (Finset.mem_univ i)
theorem cellSupDist_enclosingCell_le {l : ℕ} (hl : l ≤ F.top) (hodd : Odd F.blockSide) (x : F.Site l)
    (y : F.Cell) (B : ℕ) (h : baseDistance x (baseSite y) ≤ B * F.blockSide ^ F.top) :
    cellSupDist (enclosingCell x) y ≤ B := by
  simp only [cellSupDist]
  apply Finset.sup_le
  intro i _
  obtain ⟨K, hK1, hK2, hK3⟩ := odd_pow_half hodd (F.top - l)
  set M : ℤ := 2 * (K : ℤ) + 1 with hM
  have hMpos : 0 < M := by omega
  have hRpos : (0 : ℤ) < (F.blockSide : ℤ) ^ l := by
    have : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
    positivity
  set R₀ : ℤ := (F.blockSide : ℤ) ^ l with hR₀
  have hN : (F.blockSide : ℤ) ^ F.top = R₀ * M := by
    have e : (F.blockSide : ℤ) ^ F.top = R₀ * (F.blockSide : ℤ) ^ (F.top - l) := by
      rw [hR₀, ← pow_add]
      congr 1
      omega
    rw [e, hK3]
  set d : ℤ := ((baseSite x - baseSite y : F.Site 0) i).valMinAbs with hd
  have hdb : d.natAbs ≤ B * F.blockSide ^ F.top := le_trans (natAbs_le_baseDistance x (baseSite y) i) h
  set a : ℤ := siteCoords x i with ha
  set b : ℤ := siteCoords y i with hb
  set sd : ℤ := (F.extent i : ℤ) with hsd
  have hxb : (baseSite x : F.Site 0) i = ((R₀ * a : ℤ) : ZMod (F.period 0 i)) := rfl
  have hyb : (baseSite y : F.Site 0) i = (((F.blockSide : ℤ) ^ F.top * b : ℤ) : ZMod (F.period 0 i)) := rfl
  have hcd : ((d : ℤ) : ZMod (F.period 0 i)) =
      ((R₀ * a - (F.blockSide : ℤ) ^ F.top * b : ℤ) : ZMod (F.period 0 i)) := by
    rw [hd, ZMod.coe_valMinAbs, Pi.sub_apply, hxb, hyb, Int.cast_sub]
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hcd
  rw [period_eq, Nat.sub_zero, hN] at hq
  set d' : ℤ := a - M * b - sd * M * q with hd'
  have hdd : d = R₀ * d' := by
    rw [hN] at *
    rw [hd']
    linear_combination (-1 : ℤ) * hq
  have hdabs : |d'| ≤ B * M := by
    have h1 : |d| ≤ B * (R₀ * M) := by
      have h2 : ((d.natAbs : ℕ) : ℤ) ≤ ((B * F.blockSide ^ F.top : ℕ) : ℤ) := by exact_mod_cast hdb
      rw [Int.natCast_natAbs] at h2
      push_cast at h2
      rw [hN] at h2
      exact h2
    rw [hdd, abs_mul, abs_of_pos hRpos] at h1
    have h3 : R₀ * |d'| ≤ R₀ * (B * M) := by linarith
    exact le_of_mul_le_mul_left h3 hRpos
  obtain ⟨h4, h5⟩ := abs_le.1 hdabs
  set T : ℤ := (d' + K) / M with hT
  have hTb : -(B : ℤ) ≤ T ∧ T ≤ B := by
    constructor
    · have : -(B : ℤ) ≤ (d' + K) / M := by
        rw [Int.le_ediv_iff_mul_le hMpos]
        nlinarith
      exact this
    · have : (d' + K) / M < (B : ℤ) + 1 := Int.ediv_lt_of_lt_mul hMpos (by nlinarith)
      omega
  have hcell : (enclosingCell x - y : F.Cell) i = ((T : ℤ) : ZMod (F.period F.top i)) := by
    have e1 : a + K = (d' + K) + M * (b + sd * q) := by
      rw [hd']
      ring
    have e2 : (a + ((F.blockSide : ℤ) ^ (F.top - l) - 1) / 2) / (F.blockSide : ℤ) ^ (F.top - l) =
        b + sd * q + T := by
      rw [hK3]
      have h2 : (2 * (K : ℤ) + 1 - 1) / 2 = K := by omega
      rw [h2, e1, Int.add_mul_ediv_left _ _ hMpos.ne', hT]
      ring
    have hyc : ((b : ℤ) : ZMod (F.period F.top i)) = y i := ZMod.intCast_zmod_cast (y i)
    have hz0 : ((sd * q : ℤ) : ZMod (F.period F.top i)) = 0 := by
      refine (CharP.intCast_eq_zero_iff (ZMod (F.period F.top i)) (F.period F.top i) _).2 ?_
      rw [period_eq]
      simp only [Nat.sub_self, pow_zero, mul_one]
      exact Dvd.intro _ rfl
    have e3 : (enclosingCell x : F.Cell) i = ((b + sd * q + T : ℤ) : ZMod (F.period F.top i)) := by
      rw [← e2]
      rfl
    rw [Pi.sub_apply, e3, Int.cast_add, Int.cast_add, hz0, hyc]
    ring
  rw [Pi.sub_apply] at hcell
  rw [hcell]
  refine le_trans (natAbs_valMinAbs_intCast_le _ _) ?_
  omega
theorem baseSite_zero (x : F.Site 0) : baseSite x = x := by apply _root_.YangMills.Construction.CellBumps.baseSite_zero <;> assumption
theorem baseDistance_add_unitStep (x : F.Site 0) (j : Fin 4) (p : F.Site 0) :
    baseDistance (x + unitStep 0 j) p ≤ baseDistance x p + 1 ∧
      baseDistance x p ≤ baseDistance (x + unitStep 0 j) p + 1 := by apply _root_.YangMills.Construction.PlaquettesNearCell.baseDistance_add_unitStep <;> assumption
def slowExponent (S : Finset F.Cell) (hS : S.Nonempty) (φ : F.Cell → ℝ) (del : ℝ) (x : F.Site 0) : ℝ :=
  S.inf' hS fun y => φ y + del * ((baseDistance x (baseSite y) : ℝ) / (F.blockSide : ℝ) ^ F.top)
theorem slowExponent_step (hS : S.Nonempty) (φ : F.Cell → ℝ) (del : ℝ) (hdel : 0 ≤ del)
    (hL : 0 < F.blockSide) (x x' : F.Site 0)
    (h : ∀ y : F.Cell, baseDistance x' (baseSite y) ≤ baseDistance x (baseSite y) + 1) :
    slowExponent S hS φ del x' ≤ slowExponent S hS φ del x + del / (F.blockSide : ℝ) ^ F.top := by
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  obtain ⟨y, hy, he⟩ := Finset.exists_mem_eq_inf' hS
    (fun y => φ y + del * ((baseDistance x (baseSite y) : ℝ) / (F.blockSide : ℝ) ^ F.top))
  have h1 : slowExponent S hS φ del x' ≤
      φ y + del * ((baseDistance x' (baseSite y) : ℝ) / (F.blockSide : ℝ) ^ F.top) :=
    Finset.inf'_le (fun y => φ y + del * ((baseDistance x' (baseSite y) : ℝ) / (F.blockSide : ℝ) ^ F.top)) hy
  have h2 : slowExponent S hS φ del x =
      φ y + del * ((baseDistance x (baseSite y) : ℝ) / (F.blockSide : ℝ) ^ F.top) := he
  have h3 : ((baseDistance x' (baseSite y) : ℕ) : ℝ) ≤ (baseDistance x (baseSite y) : ℝ) + 1 := by
    exact_mod_cast h y
  have h4 : del * ((baseDistance x' (baseSite y) : ℝ) / (F.blockSide : ℝ) ^ F.top) ≤
      del * ((baseDistance x (baseSite y) : ℝ) / (F.blockSide : ℝ) ^ F.top) +
        del / (F.blockSide : ℝ) ^ F.top := by
    have h5 : (baseDistance x' (baseSite y) : ℝ) / (F.blockSide : ℝ) ^ F.top ≤
        (baseDistance x (baseSite y) : ℝ) / (F.blockSide : ℝ) ^ F.top + 1 / (F.blockSide : ℝ) ^ F.top := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right h3 hN.le
    have h6 := mul_le_mul_of_nonneg_left h5 hdel
    rw [mul_add] at h6
    have e : del * (1 / (F.blockSide : ℝ) ^ F.top) = del / (F.blockSide : ℝ) ^ F.top := by ring
    rw [e] at h6
    exact h6
  linarith
theorem slowExponent_near (hS : S.Nonempty) (hodd : Odd F.blockSide) (φ : F.Cell → ℝ) (del : ℝ)
    (hdel : 0 ≤ del) (hφ : ∀ y y', |φ y - φ y'| ≤ del * cellSupDist y y') (x : F.Site 0)
    (hx : x ∈ sitesOfCells S 0) : |slowExponent S hS φ del x - φ (enclosingCell x)| ≤ del := by
  have hL := hodd.pos
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  have hz := enclosingCell_mem (S := S) hodd x hx
  set z := enclosingCell x with hzd
  have hup : baseDistance x (baseSite z) ≤ F.blockSide ^ F.top := by
    simp only [sitesOfCells, Finset.mem_biUnion, Finset.mem_image] at hx
    obtain ⟨z', hz', h, hh, rfl⟩ := hx
    have hzz : z = z' := enclosingCell_cellCentre_add hodd z' h hh
    rw [hzz]
    apply Finset.sup_le
    intro i _
    have e : (baseSite (cellCentre 0 z' + siteOfCoords 0 h) - baseSite z' : F.Site 0) i =
        ((h i : ℤ) : ZMod (F.period 0 i)) := by
      rw [baseSite_zero]
      have e2 : baseSite z' = cellCentre 0 z' := by
        simp [baseSite, cellCentre]
      rw [e2]
      simp [siteOfCoords]
    rw [e]
    refine le_trans (natAbs_valMinAbs_intCast_le _ _) ?_
    obtain ⟨K, hK1, hK2, hK3⟩ := odd_pow_half hodd (F.top - 0)
    have h1 := (mem_centredCube _ _).1 hh i
    rw [hK2] at h1
    rw [Nat.sub_zero] at hK1
    rw [hK1]
    omega
  rw [abs_le]
  constructor
  · have hlow : φ z - del ≤ slowExponent S hS φ del x := by
      apply Finset.le_inf'
      intro y hy
      set bd := baseDistance x (baseSite y) with hbd
      have hB : bd ≤ (bd / F.blockSide ^ F.top + 1) * F.blockSide ^ F.top := by
        have hp : 0 < F.blockSide ^ F.top := by positivity
        have := Nat.div_add_mod bd (F.blockSide ^ F.top)
        have h2 := Nat.mod_lt bd hp
        nlinarith
      have hcd := cellSupDist_enclosingCell_le (Nat.zero_le F.top) hodd x y (bd / F.blockSide ^ F.top + 1) hB
      have h1 := hφ z y
      have h2 : (cellSupDist z y : ℝ) ≤ ((bd / F.blockSide ^ F.top : ℕ) : ℝ) + 1 := by exact_mod_cast hcd
      have h3 : ((bd / F.blockSide ^ F.top : ℕ) : ℝ) ≤ (bd : ℝ) / (F.blockSide : ℝ) ^ F.top := by
        have := Nat.cast_div_le (α := ℝ) (m := bd) (n := F.blockSide ^ F.top)
        simpa using this
      have h4 := le_abs_self (φ z - φ y)
      have h5 : del * (cellSupDist z y : ℝ) ≤ del * ((bd : ℝ) / (F.blockSide : ℝ) ^ F.top + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hdel
      nlinarith
    linarith
  · have h1 : slowExponent S hS φ del x ≤
        φ z + del * ((baseDistance x (baseSite z) : ℝ) / (F.blockSide : ℝ) ^ F.top) :=
      Finset.inf'_le (fun y => φ y + del * ((baseDistance x (baseSite y) : ℝ) / (F.blockSide : ℝ) ^ F.top)) hz
    have h2 : (baseDistance x (baseSite z) : ℝ) / (F.blockSide : ℝ) ^ F.top ≤ 1 := by
      rw [div_le_one hN]
      exact_mod_cast hup
    have h3 := mul_le_mul_of_nonneg_left h2 hdel
    linarith
theorem pow_le_scaleRadius {l : ℕ} (hl : l ≤ F.top) (hL : 0 < F.blockSide) (p : F.Site 0) (x : F.Site l) :
    (F.blockSide : ℝ) ^ l ≤ scaleRadius F l p x := by apply _root_.YangMills.Construction.WeightedAverages.Chains.pow_le_scaleRadius <;> assumption
theorem exp_le_one_add_two_mul (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) : Real.exp u ≤ 1 + 2 * u := by
  have h := Real.exp_bound_div_one_sub_of_interval h0 (by linarith : u < 1)
  refine le_trans h ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith
theorem abs_exp_sub_one_le (v : ℝ) (hv : |v| ≤ 1 / 2) : |Real.exp v - 1| ≤ 2 * |v| := by
  rcases le_total 0 v with h | h
  · rw [abs_of_nonneg h] at hv ⊢
    have h1 := exp_le_one_add_two_mul v h hv
    have h2 := Real.add_one_le_exp v
    rw [abs_le]
    constructor <;> linarith
  · rw [abs_of_nonpos h] at hv ⊢
    have h2 := Real.add_one_le_exp v
    have h3 : Real.exp v ≤ 1 := Real.exp_le_one_iff.2 h
    rw [abs_le]
    constructor <;> linarith
theorem min_max_step (N d d' : ℝ) (h : d' ≤ d + 1) : min N (max 1 d') ≤ min N (max 1 d) + 1 := by
  rcases le_total N (max 1 d) with h1 | h1
  · rw [min_eq_left h1]
    have := min_le_left N (max 1 d')
    linarith
  · rw [min_eq_right h1]
    have h2 := min_le_right N (max 1 d')
    have h3 : max 1 d' ≤ max 1 d + 1 := by
      apply max_le
      · have := le_max_left 1 d
        linarith
      · have := le_max_right 1 d
        linarith
    linarith
theorem scaleRadius_add_unitStep (x : F.Site 0) (j : Fin 4) (p : F.Site 0) :
    scaleRadius F 0 p (x + unitStep 0 j) ≤ scaleRadius F 0 p x + 1 ∧
      scaleRadius F 0 p x ≤ scaleRadius F 0 p (x + unitStep 0 j) + 1 := by
  obtain ⟨h1, h2⟩ := baseDistance_add_unitStep x j p
  have h3 : ((baseDistance (x + unitStep 0 j) p : ℕ) : ℝ) ≤ (baseDistance x p : ℝ) + 1 := by
    exact_mod_cast h1
  have h4 : ((baseDistance x p : ℕ) : ℝ) ≤ (baseDistance (x + unitStep 0 j) p : ℝ) + 1 := by
    exact_mod_cast h2
  simp only [scaleRadius, pow_zero]
  exact ⟨min_max_step _ _ _ h3, min_max_step _ _ _ h4⟩
def slowWeight (S : Finset F.Cell) (hS : S.Nonempty) (φ : F.Cell → ℝ) (del θ : ℝ) (p : F.Site 0)
    (x : F.Site 0) : ℝ :=
  Real.exp (slowExponent S hS φ del x) * (scaleRadius F 0 p x / (F.blockSide : ℝ) ^ F.top) ^ (-θ)
theorem slowWeight_pos (hS : S.Nonempty) (hL : 0 < F.blockSide) (φ : F.Cell → ℝ) (del θ : ℝ)
    (p x : F.Site 0) : 0 < slowWeight S hS φ del θ p x := by
  simp only [slowWeight]
  have := scaleRadius_pos hL 0 p x
  positivity
theorem slowWeight_neighbour (hS : S.Nonempty) (hL : 0 < F.blockSide) (φ : F.Cell → ℝ) (del θ : ℝ)
    (p : F.Site 0) (hdel : 0 ≤ del) (hτ : 2 * del + 4 * |θ| ≤ 1 / 2) (x : F.Site 0) (j : Fin 4) :
    |slowWeight S hS φ del θ p (x + unitStep 0 j) ^ 2 - slowWeight S hS φ del θ p x ^ 2| ≤
        slowWeight S hS φ del θ p x ^ 2 * (2 * (2 * del + 4 * |θ|) / scaleRadius F 0 p x) ∧
      slowWeight S hS φ del θ p x ≤ 2 * slowWeight S hS φ del θ p (x + unitStep 0 j) ∧
      1 / scaleRadius F 0 p x ≤ 2 / scaleRadius F 0 p (x + unitStep 0 j) := by
  set y := x + unitStep 0 j with hy
  set ρx := scaleRadius F 0 p x with hρx
  set ρy := scaleRadius F 0 p y with hρy
  have hρx1 : 1 ≤ ρx := by
    have := pow_le_scaleRadius (Nat.zero_le F.top) hL p x
    simpa using this
  have hρy1 : 1 ≤ ρy := by
    have := pow_le_scaleRadius (Nat.zero_le F.top) hL p y
    simpa using this
  have hρxN : ρx ≤ (F.blockSide : ℝ) ^ F.top := min_le_left _ _
  obtain ⟨hr1, hr2⟩ := scaleRadius_add_unitStep x j p
  rw [← hy, ← hρx, ← hρy] at hr1 hr2
  have hρx0 : 0 < ρx := by linarith
  have hρy0 : 0 < ρy := by linarith
  have hdy : ∀ c : F.Cell, baseDistance y (baseSite c) ≤ baseDistance x (baseSite c) + 1 :=
    fun c => (baseDistance_add_unitStep x j (baseSite c)).1
  have hdx : ∀ c : F.Cell, baseDistance x (baseSite c) ≤ baseDistance y (baseSite c) + 1 :=
    fun c => (baseDistance_add_unitStep x j (baseSite c)).2
  have ha1 := slowExponent_step hS φ del hdel hL x y hdy
  have ha2 := slowExponent_step hS φ del hdel hL y x hdx
  set a := slowExponent S hS φ del y - slowExponent S hS φ del x with ha
  have hab : |a| ≤ del / (F.blockSide : ℝ) ^ F.top := by
    rw [abs_le]
    constructor <;> linarith
  set r := ρy / ρx with hr
  have hr0 : 0 < r := by positivity
  have hlog1 : Real.log r ≤ 2 / ρx := by
    have h1 := Real.log_le_sub_one_of_pos hr0
    have h2 : r - 1 ≤ 2 / ρx := by
      rw [hr, div_sub_one hρx0.ne']
      apply div_le_div_of_nonneg_right _ hρx0.le
      linarith
    linarith
  have hlog2 : -(2 / ρx) ≤ Real.log r := by
    have h1 := Real.log_le_sub_one_of_pos (inv_pos.2 hr0)
    rw [Real.log_inv] at h1
    have h2 : r⁻¹ - 1 ≤ 2 / ρx := by
      have e : r⁻¹ - 1 = (ρx - ρy) / ρy := by
        rw [hr, inv_div]
        field_simp
      rw [e, div_le_div_iff₀ hρy0 hρx0]
      nlinarith
    linarith
  have hlogabs : |Real.log r| ≤ 2 / ρx := abs_le.2 ⟨hlog2, hlog1⟩
  set z := a - θ * Real.log r with hz
  have hinvN : del / (F.blockSide : ℝ) ^ F.top ≤ del / ρx := div_le_div_of_nonneg_left hdel hρx0 hρxN
  have hzb : |z| ≤ (del + 2 * |θ|) / ρx := by
    calc |z| ≤ |a| + |θ * Real.log r| := abs_sub _ _
      _ ≤ del / ρx + |θ| * (2 / ρx) := by
          rw [abs_mul]
          have := mul_le_mul_of_nonneg_left hlogabs (abs_nonneg θ)
          linarith
      _ = _ := by ring
  have hωy : slowWeight S hS φ del θ p y = slowWeight S hS φ del θ p x * Real.exp z := by
    simp only [slowWeight]
    have e1 : ρy / (F.blockSide : ℝ) ^ F.top = r * (ρx / (F.blockSide : ℝ) ^ F.top) := by
      rw [hr]
      field_simp
    have e2 : r ^ (-θ) = Real.exp (-(θ * Real.log r)) := by
      rw [Real.rpow_def_of_pos hr0]
      congr 1
      ring
    rw [← hρy, ← hρx, e1, Real.mul_rpow hr0.le (by positivity), e2, hz, ha, sub_eq_add_neg,
      sub_eq_add_neg, Real.exp_add, Real.exp_add]
    have e3 : Real.exp (slowExponent S hS φ del y) = Real.exp (slowExponent S hS φ del x) *
        (Real.exp (slowExponent S hS φ del y) * Real.exp (-slowExponent S hS φ del x)) := by
      rw [Real.exp_neg]
      field_simp
    conv_lhs => rw [e3]
    ring
  have hτ1 : 2 * del + 4 * |θ| ≥ 0 := by positivity
  have h2z : |2 * z| ≤ (2 * del + 4 * |θ|) / ρx := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := mul_le_mul_of_nonneg_left hzb (by norm_num : (0 : ℝ) ≤ 2)
    refine le_trans this (le_of_eq ?_)
    ring
  have hsmall : (2 * del + 4 * |θ|) / ρx ≤ 2 * del + 4 * |θ| := div_le_self hτ1 hρx1
  have hωx0 := slowWeight_pos hS hL φ del θ p x
  refine ⟨?_, ?_, ?_⟩
  · rw [hωy, mul_pow, ← Real.exp_nat_mul]
    have e : ((2 : ℕ) : ℝ) * z = 2 * z := by norm_num
    rw [e]
    have e2 : slowWeight S hS φ del θ p x ^ 2 * Real.exp (2 * z) - slowWeight S hS φ del θ p x ^ 2 =
        slowWeight S hS φ del θ p x ^ 2 * (Real.exp (2 * z) - 1) := by ring
    rw [e2, abs_mul, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 := abs_exp_sub_one_le (2 * z) (by linarith)
    refine le_trans h1 ?_
    have := mul_le_mul_of_nonneg_left h2z (by norm_num : (0 : ℝ) ≤ 2)
    refine le_trans this (le_of_eq ?_)
    ring
  · rw [hωy]
    have h1 : Real.exp (-z) ≤ 2 := by
      have h2 : -z ≤ 1 / 4 := by
        have h3 : |z| ≤ 1 / 4 := by
          have h4 : |2 * z| ≤ 1 / 2 := by linarith
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h4
          linarith
        linarith [neg_abs_le z, (abs_le.1 h3).1]
      have h5 := exp_le_one_add_two_mul (1 / 4) (by norm_num) (by norm_num)
      have h6 := Real.exp_le_exp.2 h2
      linarith
    have h7 : 1 ≤ 2 * Real.exp z := by
      have h8 : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
      have h9 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos z).le
      rw [h8] at h9
      exact h9
    have := mul_le_mul_of_nonneg_left h7 hωx0.le
    linarith
  · rw [div_le_div_iff₀ hρx0 hρy0]
    linarith
theorem classWeights_pos (hL : 0 < F.blockSide) (φ : F.Cell → ℝ) (θ : ℝ) (p : F.Site 0) (l : ℕ)
    (x : F.Site l) : 0 < classWeight F φ θ p l x := by apply _root_.YangMills.Construction.NearlyFlatDifferences.classWeight_pos <;> assumption
theorem norm_coe_imaginaryQuaternion (x : imaginaryQuaternions) : ‖(x : ℍ[ℝ])‖ = ‖x‖ := rfl
theorem adjointAction_smul (g : UnitQuaternion) (a : ℝ) (w : ℍ[ℝ]) :
    adjointAction g (a • w) = a • adjointAction g w := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_smul <;> assumption
theorem linearizedCurl_weighted_sub (R : F.GaugeField 0) (ω : F.Site 0 → ℝ)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (q : F.Site 0 × Fin 4 × Fin 4) :
    linearizedCurl R (fun x i => (ω x ^ 2) • u x i) q - (ω q.1 ^ 2) • linearizedCurl R u q =
      (ω (q.1 + unitStep 0 q.2.1) ^ 2 - ω q.1 ^ 2) •
          adjointAction (R q.1 q.2.1) ((u (q.1 + unitStep 0 q.2.1) q.2.2 : imaginaryQuaternions) : ℍ[ℝ]) -
        (ω (q.1 + unitStep 0 q.2.2) ^ 2 - ω q.1 ^ 2) •
          adjointAction (R q.1 q.2.1 * R (q.1 + unitStep 0 q.2.1) q.2.2 * (R (q.1 + unitStep 0 q.2.2) q.2.1)⁻¹)
            ((u (q.1 + unitStep 0 q.2.2) q.2.1 : imaginaryQuaternions) : ℍ[ℝ]) := by
  simp only [linearizedCurl, Submodule.coe_smul, adjointAction_smul]
  module
theorem weighted_term_le (hS : S.Nonempty) (hodd : Odd F.blockSide) (φ : F.Cell → ℝ) (del θ : ℝ)
    (p : F.Site 0) (hdel : 0 ≤ del) (hdel8 : del ≤ 1 / 8) (hτ : 2 * del + 4 * |θ| ≤ 1 / 2)
    (x : F.Site 0) (j : Fin 4)
    (hcmp : slowWeight S hS φ del θ p (x + unitStep 0 j) ≤
      Real.exp del * classWeight F φ θ p 0 (x + unitStep 0 j)) (v : ℝ) (hv : 0 ≤ v) :
    (slowWeight S hS φ del θ p x)⁻¹ *
        (|slowWeight S hS φ del θ p (x + unitStep 0 j) ^ 2 - slowWeight S hS φ del θ p x ^ 2| * v) ≤
      16 * (2 * del + 4 * |θ|) * (classWeight F φ θ p 0 (x + unitStep 0 j) /
        scaleRadius F 0 p (x + unitStep 0 j) * v) := by
  have hL := hodd.pos
  obtain ⟨h1, h2, h3⟩ := slowWeight_neighbour hS hL φ del θ p hdel hτ x j
  set ωx := slowWeight S hS φ del θ p x with hωx
  set ωy := slowWeight S hS φ del θ p (x + unitStep 0 j) with hωy
  have hωx0 : 0 < ωx := slowWeight_pos hS hL φ del θ p x
  set τ := 2 * del + 4 * |θ| with hτd
  set ρx := scaleRadius F 0 p x with hρx
  set ρy := scaleRadius F 0 p (x + unitStep 0 j) with hρy
  have hρx0 : 0 < ρx := scaleRadius_pos hL 0 p x
  set Wy := classWeight F φ θ p 0 (x + unitStep 0 j) with hWy
  have hWy0 : 0 < Wy := classWeights_pos hL φ θ p 0 _
  have hexp : Real.exp del ≤ 2 := by
    have := exp_le_one_add_two_mul del hdel (by linarith)
    linarith
  have hωyW : ωy ≤ 2 * Wy := le_trans hcmp (mul_le_mul_of_nonneg_right hexp hWy0.le)
  have h4 : ωx⁻¹ * |ωy ^ 2 - ωx ^ 2| ≤ ωx * (2 * τ / ρx) := by
    calc ωx⁻¹ * |ωy ^ 2 - ωx ^ 2| ≤ ωx⁻¹ * (ωx ^ 2 * (2 * τ / ρx)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ωx * (2 * τ / ρx) := by field_simp
  have h5 : ωx * (2 * τ / ρx) ≤ 16 * τ * (Wy / ρy) := by
    have e1 : ωx * (2 * τ / ρx) = 2 * τ * ωx * (1 / ρx) := by ring
    have e2 : 16 * τ * (Wy / ρy) = 2 * τ * (2 * (2 * Wy)) * (2 / ρy) := by ring
    have h6 : ωx ≤ 2 * (2 * Wy) := le_trans h2 (by linarith)
    rw [e1, e2]
    apply mul_le_mul _ h3 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left h6 (by positivity)
  calc ωx⁻¹ * (|ωy ^ 2 - ωx ^ 2| * v) = (ωx⁻¹ * |ωy ^ 2 - ωx ^ 2|) * v := by ring
    _ ≤ (16 * τ * (Wy / ρy)) * v := mul_le_mul_of_nonneg_right (le_trans h4 h5) hv
    _ = _ := by ring
def plaquetteFirstBond (q : F.Site 0 × Fin 4 × Fin 4) : F.Site 0 × Fin 4 := (q.1 + unitStep 0 q.2.1, q.2.2)
def plaquetteSecondBond (q : F.Site 0 × Fin 4 × Fin 4) : F.Site 0 × Fin 4 := (q.1 + unitStep 0 q.2.2, q.2.1)
theorem plaquetteBonds_mem (q : F.Site 0 × Fin 4 × Fin 4) (hq : q ∈ plaquettesOver S S 0) :
    plaquetteFirstBond q ∈ innerBonds S 0 ∧ plaquetteSecondBond q ∈ innerBonds S 0 := by
  classical
  have h1 : q ∈ innerPlaquettes S 0 := by
    simp only [plaquettesOver, Finset.mem_filter] at hq
    exact hq.1
  simp only [innerPlaquettes, Finset.mem_filter] at h1
  have hc := h1.2.2
  have h2 : q.1 + unitStep 0 q.2.1 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have h3 : q.1 + unitStep 0 q.2.2 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have h4 : q.1 + unitStep 0 q.2.1 + unitStep 0 q.2.2 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have h5 : q.1 + unitStep 0 q.2.2 + unitStep 0 q.2.1 ∈ sitesOfCells S 0 := by
    rw [add_right_comm]
    exact h4
  simp only [innerBonds, plaquetteFirstBond, plaquetteSecondBond, Finset.mem_filter, Finset.mem_product,
    Finset.mem_univ, and_true]
  exact ⟨⟨h2, h4⟩, ⟨h3, h5⟩⟩
theorem sum_comp_le_four_mul (P : Finset (F.Site 0 × Fin 4 × Fin 4)) (B : Finset (F.Site 0 × Fin 4))
    (τ : F.Site 0 × Fin 4 × Fin 4 → F.Site 0 × Fin 4) (κ : F.Site 0 × Fin 4 × Fin 4 → Fin 4)
    (hτ : ∀ q ∈ P, τ q ∈ B) (hinj : ∀ q ∈ P, ∀ q' ∈ P, τ q = τ q' → κ q = κ q' → q = q')
    (g : F.Site 0 × Fin 4 → ℝ) (hg : ∀ b, 0 ≤ g b) :
    ∑ q ∈ P, g (τ q) ≤ 4 * ∑ b ∈ B, g b := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hτ, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  have hc : ((P.filter fun q => τ q = b).card : ℝ) ≤ 4 := by
    have h1 : (P.filter fun q => τ q = b).card ≤ (Finset.univ : Finset (Fin 4)).card := by
      apply Finset.card_le_card_of_injOn κ (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
      intro q hq q' hq' e
      obtain ⟨h2, h3⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hq)
      obtain ⟨h4, h5⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hq')
      exact hinj q h2 q' h4 (h3.trans h5.symm) e
    simpa using (by exact_mod_cast h1 : ((P.filter fun q => τ q = b).card : ℝ) ≤
      ((Finset.univ : Finset (Fin 4)).card : ℝ))
  calc ∑ q ∈ P.filter (fun q => τ q = b), g (τ q) = ∑ q ∈ P.filter (fun q => τ q = b), g b := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [(Finset.mem_filter.1 hq).2]
    _ = ((P.filter fun q => τ q = b).card : ℝ) * g b := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 4 * g b := mul_le_mul_of_nonneg_right hc (hg b)
end SmoothWeightCurl
open SmoothWeightCurl in
theorem smoothWeightCurlCommutator : smoothWeightCurlCommutatorStatement := by
  classical
  intro ε hε
  set t : ℝ := min (1 / 2) (ε / 64) with ht
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have ht2 : t ≤ ε / 64 := min_le_right _ _
  refine ⟨min (1 / 8) (t / 8), min (1 / 8) (t / 4), lt_min (by norm_num) (by positivity), min_le_left _ _,
    lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
  intro F S R hodd h5 φ θ del p hθ hdel0 hdel1 hφ
  have hL := hodd.pos
  have hθt : |θ| ≤ t / 8 := le_trans hθ (min_le_right _ _)
  have hdelt : del ≤ t / 4 := le_trans hdel1 (min_le_right _ _)
  have hdel8 : del ≤ 1 / 8 := le_trans hdel1 (min_le_left _ _)
  rcases S.eq_empty_or_nonempty with rfl | hS
  · refine ⟨fun _ => 1, fun _ => one_pos, ?_, ?_⟩
    · intro x hx
      simp [sitesOfCells] at hx
    · intro u
      have hP : plaquettesOver (∅ : Finset F.Cell) ∅ 0 = ∅ := by
        simp [plaquettesOver]
      rw [hP, Finset.sum_empty]
      positivity
  · have hτ : 2 * del + 4 * |θ| ≤ t := by linarith
    have hτ2 : 2 * del + 4 * |θ| ≤ 1 / 2 := by linarith
    have hcmp : ∀ x ∈ sitesOfCells S 0,
        Real.exp (-del) * classWeight F φ θ p 0 x ≤ slowWeight S hS φ del θ p x ∧
          slowWeight S hS φ del θ p x ≤ Real.exp del * classWeight F φ θ p 0 x := by
      intro x hx
      have hn := slowExponent_near hS hodd φ del hdel0 hφ x hx
      obtain ⟨h1, h2⟩ := abs_le.1 hn
      have hP : 0 ≤ (scaleRadius F 0 p x / (F.blockSide : ℝ) ^ F.top) ^ (-θ) := by
        have := scaleRadius_pos hL 0 p x
        positivity
      simp only [slowWeight, classWeight]
      constructor
      · rw [← mul_assoc, ← Real.exp_add]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hP
      · rw [← mul_assoc, ← Real.exp_add]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hP
    refine ⟨slowWeight S hS φ del θ p, fun x => slowWeight_pos hS hL φ del θ p x, hcmp, ?_⟩
    intro u
    set ω := slowWeight S hS φ del θ p with hω
    set τ := 2 * del + 4 * |θ| with hτd
    set A : F.Site 0 × Fin 4 → ℝ :=
      fun b => classWeight F φ θ p 0 b.1 / scaleRadius F 0 p b.1 * ‖u b.1 b.2‖ with hA
    have hterm : ∀ q ∈ plaquettesOver S S 0, ((ω q.1)⁻¹ *
        ‖linearizedCurl R (fun x i => (ω x ^ 2) • u x i) q - (ω q.1 ^ 2) • linearizedCurl R u q‖) ^ 2 ≤
        2 * (16 * τ) ^ 2 * (A (plaquetteFirstBond q) ^ 2 + A (plaquetteSecondBond q) ^ 2) := by
      intro q hq
      obtain ⟨hb1, hb2⟩ := plaquetteBonds_mem q hq
      have hs1 : q.1 + unitStep 0 q.2.1 ∈ sitesOfCells S 0 := by
        simp only [innerBonds, plaquetteFirstBond, Finset.mem_filter, Finset.mem_product] at hb1
        exact hb1.1.1
      have hs2 : q.1 + unitStep 0 q.2.2 ∈ sitesOfCells S 0 := by
        simp only [innerBonds, plaquetteSecondBond, Finset.mem_filter, Finset.mem_product] at hb2
        exact hb2.1.1
      have ht1' := weighted_term_le hS hodd φ del θ p hdel0 hdel8 hτ2 q.1 q.2.1 (hcmp _ hs1).2
        ‖u (q.1 + unitStep 0 q.2.1) q.2.2‖ (norm_nonneg _)
      have ht2' := weighted_term_le hS hodd φ del θ p hdel0 hdel8 hτ2 q.1 q.2.2 (hcmp _ hs2).2
        ‖u (q.1 + unitStep 0 q.2.2) q.2.1‖ (norm_nonneg _)
      have hn : ‖linearizedCurl R (fun x i => (ω x ^ 2) • u x i) q - (ω q.1 ^ 2) • linearizedCurl R u q‖ ≤
          |ω (q.1 + unitStep 0 q.2.1) ^ 2 - ω q.1 ^ 2| * ‖u (q.1 + unitStep 0 q.2.1) q.2.2‖ +
            |ω (q.1 + unitStep 0 q.2.2) ^ 2 - ω q.1 ^ 2| * ‖u (q.1 + unitStep 0 q.2.2) q.2.1‖ := by
        rw [linearizedCurl_weighted_sub]
        refine le_trans (norm_sub_le _ _) (le_of_eq ?_)
        rw [norm_smul, norm_smul, norm_adjointAction, norm_adjointAction]
        rfl
      have hinv : 0 ≤ (ω q.1)⁻¹ := inv_nonneg.2 (slowWeight_pos hS hL φ del θ p _).le
      have h1 : (ω q.1)⁻¹ *
          ‖linearizedCurl R (fun x i => (ω x ^ 2) • u x i) q - (ω q.1 ^ 2) • linearizedCurl R u q‖ ≤
          16 * τ * A (plaquetteFirstBond q) + 16 * τ * A (plaquetteSecondBond q) := by
        refine le_trans (mul_le_mul_of_nonneg_left hn hinv) ?_
        rw [mul_add]
        exact add_le_add ht1' ht2'
      have h0 : 0 ≤ (ω q.1)⁻¹ *
          ‖linearizedCurl R (fun x i => (ω x ^ 2) • u x i) q - (ω q.1 ^ 2) • linearizedCurl R u q‖ :=
        mul_nonneg hinv (norm_nonneg _)
      refine le_trans (pow_le_pow_left₀ h0 h1 2) (le_trans (add_sq_le_two_mul _ _) (le_of_eq ?_))
      ring
    have hsum1 := sum_comp_le_four_mul (plaquettesOver S S 0) (innerBonds S 0) plaquetteFirstBond
      (fun q => q.2.1) (fun q hq => (plaquetteBonds_mem q hq).1) (by
        intro q _ q' _ e e2
        have e' := Prod.ext_iff.1 e
        have e3 : q.1 + unitStep 0 q.2.1 = q'.1 + unitStep 0 q'.2.1 := e'.1
        have e4 : q.2.2 = q'.2.2 := e'.2
        have e5 : q.2.1 = q'.2.1 := e2
        rw [e5] at e3
        exact Prod.ext (add_right_cancel e3) (Prod.ext e5 e4))
      (fun b => A b ^ 2) (fun b => by positivity)
    have hsum2 := sum_comp_le_four_mul (plaquettesOver S S 0) (innerBonds S 0) plaquetteSecondBond
      (fun q => q.2.2) (fun q hq => (plaquetteBonds_mem q hq).2) (by
        intro q _ q' _ e e2
        have e' := Prod.ext_iff.1 e
        have e3 : q.1 + unitStep 0 q.2.2 = q'.1 + unitStep 0 q'.2.2 := e'.1
        have e4 : q.2.1 = q'.2.1 := e'.2
        have e5 : q.2.2 = q'.2.2 := e2
        rw [e5] at e3
        exact Prod.ext (add_right_cancel e3) (Prod.ext e4 e5))
      (fun b => A b ^ 2) (fun b => by positivity)
    have hbs : weightedBondL2Norm S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
        (fun x i => u x i) ^ 2 = ∑ b ∈ innerBonds S 0, A b ^ 2 := by
      simp only [weightedBondL2Norm]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun b _ => by positivity)]
      simp only [hA, norm_coe_imaginaryQuaternion]
    rw [hbs]
    have hAs : 0 ≤ ∑ b ∈ innerBonds S 0, A b ^ 2 := Finset.sum_nonneg fun b _ => by positivity
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have hτε : (64 * τ) ^ 2 ≤ ε ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    calc 2 * (16 * τ) ^ 2 * (∑ q ∈ plaquettesOver S S 0, A (plaquetteFirstBond q) ^ 2 +
          ∑ q ∈ plaquettesOver S S 0, A (plaquetteSecondBond q) ^ 2)
        ≤ 2 * (16 * τ) ^ 2 * (4 * ∑ b ∈ innerBonds S 0, A b ^ 2 + 4 * ∑ b ∈ innerBonds S 0, A b ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hsum1 hsum2) (by positivity)
      _ = (64 * τ) ^ 2 * ∑ b ∈ innerBonds S 0, A b ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hτε hAs
end YangMills.Construction.BlockAverages
end
