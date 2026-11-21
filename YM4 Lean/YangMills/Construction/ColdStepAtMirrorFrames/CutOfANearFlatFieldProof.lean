import YangMills.Construction.ColdStepAtMirrorFrames.CellGeometryOfATorus
import YangMills.Construction.ColdStepAtMirrorFrames.CutOfANearFlatField
import YangMills.Construction.ColdStepAtMirrorFrames.FlowOfACutField
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfANearElement
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace NearFlatCutoff
open BlockOffsets
variable {F : BlockFrame}
def logCutoff (r : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  min 1 (max 0 (1 - ε * Real.log ((max d r : ℕ) / (r : ℝ))))
theorem logCutoff_nonneg (r : ℕ) (ε : ℝ) (d : ℕ) : 0 ≤ logCutoff r ε d := le_min zero_le_one (le_max_left _ _)
theorem logCutoff_le_one (r : ℕ) (ε : ℝ) (d : ℕ) : logCutoff r ε d ≤ 1 := min_le_left _ _
theorem logCutoff_eq_one {r d : ℕ} {ε : ℝ} (hr : 0 < r) (h : d ≤ r) : logCutoff r ε d = 1 := by
  unfold logCutoff
  have hm : max d r = r := max_eq_right h
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [hm, div_self hr', Real.log_one]
  simp
theorem logCutoff_eq_zero {r s d : ℕ} {ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hs : (r : ℝ) * Real.exp (1 / ε) ≤ s)
    (h : s ≤ d) : logCutoff r ε d = 0 := by
  unfold logCutoff
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hd : (r : ℝ) * Real.exp (1 / ε) ≤ (max d r : ℕ) := by
    refine hs.trans ?_
    have : s ≤ max d r := h.trans (le_max_left _ _)
    exact_mod_cast this
  have hl : 1 / ε ≤ Real.log ((max d r : ℕ) / (r : ℝ)) := by
    rw [Real.le_log_iff_exp_le (by
      have : 0 < max d r := lt_of_lt_of_le hr (le_max_right _ _)
      positivity)]
    rw [le_div_iff₀ hr']
    linarith
  have : 1 - ε * Real.log ((max d r : ℕ) / (r : ℝ)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_left hl hε.le
    rw [mul_one_div, div_self hε.ne'] at this
    linarith
  rw [max_eq_left this]
  simp
theorem abs_logCutoff_sub_mul_le {r d e : ℕ} {ε : ℝ} (hr : 4 ≤ r) (hε : 0 ≤ ε) (h1 : d ≤ e + 1) (h2 : e ≤ d + 1) :
    |logCutoff r ε d - logCutoff r ε e| * (1 + (d : ℝ)) ≤ 2 * ε := by
  have hr0 : (0 : ℝ) < r := by
    have : 0 < r := by omega
    exact_mod_cast this
  have hr4 : (4 : ℝ) ≤ r := by exact_mod_cast hr
  set a : ℝ := ((max d r : ℕ) : ℝ) with ha
  set b : ℝ := ((max e r : ℕ) : ℝ) with hb
  have ha4 : (r : ℝ) ≤ a := Nat.cast_le.mpr (le_max_right _ _)
  have hb4 : (r : ℝ) ≤ b := Nat.cast_le.mpr (le_max_right _ _)
  have hab : a ≤ b + 1 := by
    have h0 : max d r ≤ max e r + 1 := by omega
    have h2 : ((max d r : ℕ) : ℝ) ≤ ((max e r + 1 : ℕ) : ℝ) := Nat.cast_le.mpr h0
    rw [Nat.cast_add, Nat.cast_one] at h2
    exact h2
  have hba : b ≤ a + 1 := by
    have h0 : max e r ≤ max d r + 1 := by omega
    have h2 : ((max e r : ℕ) : ℝ) ≤ ((max d r + 1 : ℕ) : ℝ) := Nat.cast_le.mpr h0
    rw [Nat.cast_add, Nat.cast_one] at h2
    exact h2
  have hda : (d : ℝ) ≤ a := Nat.cast_le.mpr (le_max_left _ _)
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hlog : |Real.log a - Real.log b| * (1 + (d : ℝ)) ≤ 2 := by
    rcases le_total a b with h | h
    · have h1 : Real.log b - Real.log a ≤ 1 / a := by
        rw [← Real.log_div hb0.ne' ha0.ne']
        have h2 := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
        have h3 : b / a - 1 ≤ 1 / a := by
          rw [div_sub_one ha0.ne']
          gcongr
          linarith
        linarith
      have h4 : Real.log a ≤ Real.log b := Real.log_le_log ha0 h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      calc _ ≤ 1 / a * (1 + a) := by
            apply mul_le_mul h1 (by linarith) (by positivity) (by positivity)
        _ ≤ 2 := by
            rw [one_div, inv_mul_le_iff₀ ha0]
            linarith
    · have h1 : Real.log a - Real.log b ≤ 1 / b := by
        rw [← Real.log_div ha0.ne' hb0.ne']
        have h2 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
        have h3 : a / b - 1 ≤ 1 / b := by
          rw [div_sub_one hb0.ne']
          gcongr
          linarith
        linarith
      have h4 : Real.log b ≤ Real.log a := Real.log_le_log hb0 h
      rw [abs_of_nonneg (by linarith)]
      calc _ ≤ 1 / b * (2 + b) := by
            apply mul_le_mul h1 (by linarith) (by positivity) (by positivity)
        _ ≤ 2 := by
            rw [one_div, inv_mul_le_iff₀ hb0]
            linarith
  have hc : |logCutoff r ε d - logCutoff r ε e| ≤ ε * |Real.log a - Real.log b| := by
    unfold logCutoff
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    simp only [sub_self, abs_zero]
    refine max_le (by positivity) ?_
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp; positivity) ?_)
    have hsub : (1 - ε * Real.log (a / r)) - (1 - ε * Real.log (b / r)) =
        -(ε * (Real.log a - Real.log b)) := by
      rw [Real.log_div ha0.ne' hr0.ne', Real.log_div hb0.ne' hr0.ne']
      ring
    rw [hsub, abs_neg, abs_mul, abs_of_nonneg hε]
  have hd0 : (0 : ℝ) ≤ 1 + d := by positivity
  calc _ ≤ ε * |Real.log a - Real.log b| * (1 + (d : ℝ)) := mul_le_mul_of_nonneg_right hc hd0
    _ = ε * (|Real.log a - Real.log b| * (1 + (d : ℝ))) := by ring
    _ ≤ ε * 2 := mul_le_mul_of_nonneg_left hlog hε
    _ = 2 * ε := by ring
open Classical in
def bondLog {j : ℕ} (W : F.GaugeField j) : F.Site j → Fin 4 → imaginaryQuaternions := fun z i =>
  if h : ∃ A : imaginaryQuaternions, expUnit A = W z i ∧ ‖A‖ ≤ 2 * distFromOne (W z i) then h.choose else 0
theorem expUnit_bondLog (hlog : LogNearOne) {j : ℕ} (W : F.GaugeField j) (z : F.Site j) (i : Fin 4)
    (h : distFromOne (W z i) ≤ 1) :
    expUnit (bondLog W z i) = W z i ∧ ‖bondLog W z i‖ ≤ 2 * distFromOne (W z i) := by
  have hx := hlog (W z i) h
  unfold bondLog
  rw [dif_pos hx]
  exact hx.choose_spec
theorem siteSupDist_add_unitStep_le (hc : IsLargeCubicTorus F) (hL : 3 ≤ F.blockSide) (x : F.Site F.depth) (i : Fin 4) :
    siteSupDist (x + unitStep F.depth i) x ≤ 1 := by
  obtain ⟨n, hn, hs⟩ := hc
  refine Finset.sup_le fun l _ => ?_
  have hp : F.period F.depth l = F.extent l * F.blockSide := period_depth l
  have hp2 : 2 < F.period F.depth l := by
    rw [hp, hs l]
    nlinarith
  have : NeZero (F.period F.depth l) := ⟨by omega⟩
  have hsite : ((x + unitStep F.depth i - x : F.Site F.depth)) l =
      (((Pi.single i 1 : Fin 4 → ℤ) l : ℤ) : ZMod (F.period F.depth l)) := by
    simp [unitStep, siteOfCoords]
  show (((x + unitStep F.depth i - x : F.Site F.depth)) l).valMinAbs.natAbs ≤ 1
  rw [hsite]
  have h1 := ZMod.natAbs_min_of_le_div_two (F.period F.depth l)
    ((((Pi.single i 1 : Fin 4 → ℤ) l : ℤ) : ZMod (F.period F.depth l))).valMinAbs ((Pi.single i 1 : Fin 4 → ℤ) l)
    (by rw [ZMod.coe_valMinAbs]) (ZMod.natAbs_valMinAbs_le _)
  refine h1.trans ?_
  by_cases hli : l = i
  · subst hli; simp
  · simp [Pi.single_eq_of_ne hli]
theorem cellSupDist_add_unitStep (hgeo : CubicTorusCellGeometry) (hodd : Odd F.blockSide) (hc : IsLargeCubicTorus F)
    (hL : 3 ≤ F.blockSide) (x : F.Site F.depth) (i : Fin 4) (Y : F.Cell) :
    cellSupDist (enclosingCell (x + unitStep F.depth i)) Y ≤ cellSupDist (enclosingCell x) Y + 1 ∧
      cellSupDist (enclosingCell x) Y ≤ cellSupDist (enclosingCell (x + unitStep F.depth i)) Y + 1 := by
  obtain ⟨_, _, hsym, htri, hcell⟩ := hgeo.1 F hodd hc
  have h1 := hcell (x + unitStep F.depth i) x
  have h2 := siteSupDist_add_unitStep_le hc hL x i
  have h3 : cellSupDist (enclosingCell (x + unitStep F.depth i)) (enclosingCell x) ≤ 1 := by
    by_contra hcon
    have : 2 ≤ cellSupDist (enclosingCell (x + unitStep F.depth i)) (enclosingCell x) := by omega
    nlinarith
  constructor
  · have := htri (enclosingCell (x + unitStep F.depth i)) (enclosingCell x) Y
    omega
  · have := htri (enclosingCell x) (enclosingCell (x + unitStep F.depth i)) Y
    have h4 := hsym (enclosingCell x) (enclosingCell (x + unitStep F.depth i))
    omega
theorem constants_fit {C Q σ : ℝ} (hC : 1 ≤ C) (hQ : 4 ≤ Q) (hσ : 0 < σ) (h : 2 ^ 14 * C ^ 2 * Q ^ 2 * σ ≤ 1) :
    8 * C * Q * σ ≤ 1 ∧ C * Q * σ ≤ 1 ∧ 4 * (8 * C * Q * σ) ^ 2 ≤ σ / 64 := by
  have h1 : 1 ≤ C * Q := by nlinarith
  have h2 : C * Q ≤ (C * Q) ^ 2 := by nlinarith
  have h3 : 2 ^ 14 * ((C * Q) ^ 2 * σ) ≤ 1 := by
    have : 2 ^ 14 * ((C * Q) ^ 2 * σ) = 2 ^ 14 * C ^ 2 * Q ^ 2 * σ := by ring
    linarith
  have h4 : C * Q * σ ≤ (C * Q) ^ 2 * σ := mul_le_mul_of_nonneg_right h2 hσ.le
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have hsq : 4 * (8 * C * Q * σ) ^ 2 = 256 * ((C * Q) ^ 2 * σ) * σ := by ring
  rw [hsq]
  nlinarith [mul_le_mul_of_nonneg_right h3 hσ.le]
end NearFlatCutoff
open NearFlatCutoff
open BlockOffsets
set_option maxHeartbeats 1000000 in
theorem cutoffNearFlatField_holds (hgeo : CubicTorusCellGeometry) (hcf : CutoffFlowSmallCurvature)
    (hlog : LogNearOne) : CutoffNearFlatField := by
  intro C r hC hr
  obtain ⟨K, hK, hsum⟩ := hgeo.2 1 one_pos
  have hr0 : 0 < r := by omega
  set ε : ℝ := 1 / (2 ^ 10 * C) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨s, hsa, hsb⟩ : ∃ s : ℕ, (r : ℝ) * Real.exp (1 / ε) ≤ s ∧ r ≤ s :=
    ⟨max ⌈(r : ℝ) * Real.exp (1 / ε)⌉₊ r,
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_left _ _), le_max_right _ _⟩
  set Q : ℝ := (s : ℝ) + 4 with hQ
  have hQ4 : 4 ≤ Q := by
    have : (0 : ℝ) ≤ s := by positivity
    linarith
  refine ⟨s, 1 / (2 ^ 14 * C ^ 2 * Q ^ 2), 2 * C * Q * Real.exp s * K, hsb, by positivity, by positivity, ?_⟩
  intro σ F W Y hσ hσ0 hodd hL3 hcub hW hnear
  rw [le_div_iff₀ (by positivity)] at hσ0
  have hnum : 2 ^ 14 * C ^ 2 * Q ^ 2 * σ ≤ 1 := by linarith
  obtain ⟨n1, n2, n3⟩ := constants_fit hC hQ4 hσ hnum
  have hA : ∀ b : F.Site F.depth × Fin 4, cellSupDist (enclosingCell b.1) Y ≤ s + 2 →
      expUnit (bondLog W b.1 b.2) = W b.1 b.2 ∧
        ‖bondLog W b.1 b.2‖ ≤ 2 * (C * (1 + cellSupDist (enclosingCell b.1) Y) * σ) := by
    intro b hb
    have h1 := hnear b hb
    have hd : (1 + (cellSupDist (enclosingCell b.1) Y : ℝ)) ≤ Q := by
      have : (cellSupDist (enclosingCell b.1) Y : ℝ) ≤ s + 2 := by exact_mod_cast hb
      rw [hQ]; linarith
    have h2 : C * (1 + cellSupDist (enclosingCell b.1) Y) * σ ≤ C * Q * σ := by gcongr
    obtain ⟨a, b'⟩ := expUnit_bondLog hlog W b.1 b.2 (h1.trans (h2.trans n2))
    exact ⟨a, b'.trans (by linarith)⟩
  let ch : F.Site F.depth → Fin 4 → ℝ := fun y _ => logCutoff r ε (cellSupDist (enclosingCell y) Y)
  have hflow := hcf F F.depth W (bondLog W) ch σ hσ
    (fun y i => ⟨logCutoff_nonneg _ _ _, logCutoff_le_one _ _ _⟩) (by
      intro p hp
      obtain ⟨x, μ, ν⟩ := p
      set D := cellSupDist (enclosingCell x) Y with hD
      have c1 := cellSupDist_add_unitStep hgeo hodd hcub hL3 x μ Y
      have c2 := cellSupDist_add_unitStep hgeo hodd hcub hL3 x ν Y
      by_cases hDs : s + 1 ≤ D
      · left
        intro l
        fin_cases l
        · exact logCutoff_eq_zero hr0 hε hsa (by show s ≤ cellSupDist (enclosingCell x) Y; omega)
        · exact logCutoff_eq_zero hr0 hε hsa
            (by show s ≤ cellSupDist (enclosingCell (x + unitStep F.depth μ)) Y; omega)
        · exact logCutoff_eq_zero hr0 hε hsa
            (by show s ≤ cellSupDist (enclosingCell (x + unitStep F.depth ν)) Y; omega)
        · exact logCutoff_eq_zero hr0 hε hsa (by show s ≤ cellSupDist (enclosingCell x) Y; omega)
      · right
        have hd : ∀ l, cellSupDist (enclosingCell (plaquetteBondList (x, μ, ν) l).1) Y ≤ D + 1 ∧
            D ≤ cellSupDist (enclosingCell (plaquetteBondList (x, μ, ν) l).1) Y + 1 := by
          intro l
          fin_cases l
          · exact ⟨Nat.le_succ _, Nat.le_succ _⟩
          · exact c1
          · exact c2
          · exact ⟨Nat.le_succ _, Nat.le_succ _⟩
        have hb := fun l => hA (plaquetteBondList (x, μ, ν) l) (by have := (hd l).1; omega)
        have hnorm : ∀ l, ‖bondLog W (plaquetteBondList (x, μ, ν) l).1 (plaquetteBondList (x, μ, ν) l).2‖ ≤
            2 * C * Q * σ := by
          intro l
          refine (hb l).2.trans ?_
          have h1 : (cellSupDist (enclosingCell (plaquetteBondList (x, μ, ν) l).1) Y : ℝ) ≤ s + 1 := by
            have := (hd l).1
            have h2 : cellSupDist (enclosingCell (plaquetteBondList (x, μ, ν) l).1) Y ≤ s + 1 := by omega
            exact_mod_cast h2
          have h3 : 1 + (cellSupDist (enclosingCell (plaquetteBondList (x, μ, ν) l).1) Y : ℝ) ≤ Q := by
            rw [hQ]; linarith
          have : C * (1 + cellSupDist (enclosingCell (plaquetteBondList (x, μ, ν) l).1) Y) * σ ≤ C * Q * σ := by
            gcongr
          linarith
        have hsumA : ∑ l, ‖bondLog W (plaquetteBondList (x, μ, ν) l).1 (plaquetteBondList (x, μ, ν) l).2‖ ≤
            8 * C * Q * σ := by
          have := Finset.sum_le_sum (s := Finset.univ) fun l _ => hnorm l
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
          push_cast at this
          linarith
        have hs0 : 0 ≤ ∑ l, ‖bondLog W (plaquetteBondList (x, μ, ν) l).1 (plaquetteBondList (x, μ, ν) l).2‖ :=
          Finset.sum_nonneg fun _ _ => norm_nonneg _
        refine ⟨fun l => (hb l).1.symm, hsumA.trans n1, ?_⟩
        have hcurv := hW (x, μ, ν) hp
        have hsq := pow_le_pow_left₀ hs0 hsumA 2
        have hlip : ∑ l, |ch (plaquetteBondList (x, μ, ν) l).1 (plaquetteBondList (x, μ, ν) l).2 - ch x μ| *
            ‖bondLog W (plaquetteBondList (x, μ, ν) l).1 (plaquetteBondList (x, μ, ν) l).2‖ ≤ σ / 64 := by
          have each : ∀ l, |ch (plaquetteBondList (x, μ, ν) l).1 (plaquetteBondList (x, μ, ν) l).2 - ch x μ| *
              ‖bondLog W (plaquetteBondList (x, μ, ν) l).1 (plaquetteBondList (x, μ, ν) l).2‖ ≤ σ / 256 := by
            intro l
            have hs := abs_logCutoff_sub_mul_le (r := r) (ε := ε) hr hε.le (hd l).1 (hd l).2
            have h1 := mul_le_mul_of_nonneg_left (hb l).2
              (abs_nonneg (logCutoff r ε (cellSupDist (enclosingCell (plaquetteBondList (x, μ, ν) l).1) Y) -
                logCutoff r ε D))
            refine h1.trans ?_
            have hre : |logCutoff r ε (cellSupDist (enclosingCell (plaquetteBondList (x, μ, ν) l).1) Y) -
                logCutoff r ε D| *
                (2 * (C * (1 + cellSupDist (enclosingCell (plaquetteBondList (x, μ, ν) l).1) Y) * σ)) =
                (|logCutoff r ε (cellSupDist (enclosingCell (plaquetteBondList (x, μ, ν) l).1) Y) -
                  logCutoff r ε D| *
                  (1 + cellSupDist (enclosingCell (plaquetteBondList (x, μ, ν) l).1) Y)) * (2 * C * σ) := by
              ring
            rw [hre]
            have h2 := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ 2 * C * σ)
            refine h2.trans (le_of_eq ?_)
            rw [hεdef]
            field_simp
            norm_num
          have := Finset.sum_le_sum (s := Finset.univ) fun l _ => each l
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
          push_cast at this
          linarith
        have : 4 * (∑ l, ‖bondLog W (plaquetteBondList (x, μ, ν) l).1 (plaquetteBondList (x, μ, ν) l).2‖) ^ 2 ≤
            σ / 64 := by
          linarith
        show plaquetteDefect W (x, μ, ν) + _ + _ < σ
        linarith)
  refine ⟨fun y i => ch y i • bondLog W y i, hflow, ?_, ?_⟩
  · intro b hb
    have h1 := (hA b (by omega)).1
    have hc : ch b.1 b.2 = 1 := logCutoff_eq_one hr0 hb
    simp only [expFlow, leftTranslate, uniformField, hc, one_smul, mul_one]
    exact h1
  · have hb : ∀ b ∈ fineBonds F, ‖ch b.1 b.2 • bondLog W b.1 b.2‖ ≤
        2 * C * Q * Real.exp s * σ * Real.exp (-(1 * cellSupDist (enclosingCell b.1) Y)) := by
      intro b _
      by_cases hd : s ≤ cellSupDist (enclosingCell b.1) Y
      · have : ch b.1 b.2 = 0 := logCutoff_eq_zero hr0 hε hsa hd
        rw [this, zero_smul, norm_zero]
        positivity
      · have hd' : cellSupDist (enclosingCell b.1) Y < s := not_le.mp hd
        have hA' := (hA b (by omega)).2
        have hc : ‖ch b.1 b.2‖ ≤ 1 := by
          rw [Real.norm_of_nonneg (logCutoff_nonneg _ _ _)]
          exact logCutoff_le_one _ _ _
        rw [norm_smul]
        have hdr : (cellSupDist (enclosingCell b.1) Y : ℝ) ≤ s := by exact_mod_cast hd'.le
        have h1 : 1 + (cellSupDist (enclosingCell b.1) Y : ℝ) ≤ Q := by rw [hQ]; linarith
        have h2 : ‖bondLog W b.1 b.2‖ ≤ 2 * C * Q * σ := by
          refine hA'.trans ?_
          have : C * (1 + cellSupDist (enclosingCell b.1) Y) * σ ≤ C * Q * σ := by gcongr
          linarith
        have h3 : 1 ≤ Real.exp s * Real.exp (-(1 * (cellSupDist (enclosingCell b.1) Y : ℝ))) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by linarith)
        calc _ ≤ 1 * ‖bondLog W b.1 b.2‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
          _ ≤ 2 * C * Q * σ := by rw [one_mul]; exact h2
          _ ≤ 2 * C * Q * σ * (Real.exp s * Real.exp (-(1 * (cellSupDist (enclosingCell b.1) Y : ℝ)))) :=
              le_mul_of_one_le_right (by positivity) h3
          _ = _ := by ring
    have h5 := Finset.sum_le_sum hb
    rw [← Finset.mul_sum] at h5
    have h6 := hsum F hodd hcub Y
    refine h5.trans ?_
    have h7 := mul_le_mul_of_nonneg_left h6 (by positivity : 0 ≤ 2 * C * Q * Real.exp s * σ)
    refine h7.trans (le_of_eq ?_)
    ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
