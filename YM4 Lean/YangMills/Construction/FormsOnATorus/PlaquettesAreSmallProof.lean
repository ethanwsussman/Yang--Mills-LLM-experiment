import YangMills.Construction.FormsOnATorus.ChanceOfAPlaquetteAgainstItsMirrors
import YangMills.Construction.FormsOnATorus.CornersOfTheImagesOfAPlaquette
import YangMills.Construction.FormsOnATorus.HotPlaquettesAtFarPlacesAreRare
import YangMills.Construction.LawOnABoxOfTheFlow.PlaquettesAreSmall
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.BoxEvents
open TorusFields TorusLumps RenormalizationStepParameters WeightedResponses ResponseInTheExpansion
section Separation
private theorem mem_plaquettesIn_iff_lt_and_vertices {m : ℕ} [NeZero m] {S : Finset (TorusSite m)}
    {p : TorusPlaquette m} :
    p ∈ plaquettesIn S ↔ p.2.1 < p.2.2 ∧ ∀ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, z ∈ S := by apply _root_.YangMills.Construction.TorusLumps.mem_plaquettesIn_iff_forall_vertex <;> assumption
private theorem natAbs_valMinAbs_shift_ge {L M : ℕ} [NeZero (L * M)] (hL : 2 ^ 18 ≤ L) {i j : ℕ}
    (hi : i < M) (hj : j < M) (hij : i ≠ j) {e : ℤ} (he : |e| ≤ 2) :
    2 ^ 17 ≤ (((((L : ℤ) * ((i : ℤ) - j) + e : ℤ)) : ZMod (L * M)).valMinAbs).natAbs := by
  by_contra hcon
  push Not at hcon
  set w : ℤ := (L : ℤ) * ((i : ℤ) - j) + e with hw
  set a : ℤ := ((w : ZMod (L * M))).valMinAbs with ha
  have hcast : ((a : ℤ) : ZMod (L * M)) = (w : ZMod (L * M)) := ZMod.coe_valMinAbs _
  have hdvd : ((L * M : ℕ) : ℤ) ∣ w - a := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub a w (L * M)).mp hcast
    exact this
  have hLd : (L : ℤ) ∣ e - a := by
    have h1 : (L : ℤ) ∣ w - a := dvd_trans (by push_cast; exact Dvd.intro _ rfl) hdvd
    have h2 : w - a = (L : ℤ) * ((i : ℤ) - j) + (e - a) := by rw [hw]; ring
    rw [h2] at h1
    exact (dvd_add_right (Dvd.intro _ rfl)).mp h1
  have hea : e - a = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd hLd ?_
    have h1 : |a| < 2 ^ 17 := by
      have : a.natAbs < 2 ^ 17 := hcon
      rw [Int.abs_eq_natAbs]
      exact_mod_cast this
    have h2 : (2 : ℤ) ^ 18 ≤ L := by exact_mod_cast hL
    have := abs_le.mp he
    have := abs_lt.mp h1
    rw [abs_lt]
    constructor <;> norm_num at * <;> omega
  have hMd : ((L * M : ℕ) : ℤ) ∣ (L : ℤ) * ((i : ℤ) - j) := by
    have h2 : w - a = (L : ℤ) * ((i : ℤ) - j) := by rw [hw]; linarith
    rwa [h2] at hdvd
  have hL0 : (L : ℤ) ≠ 0 := by
    have : (2 : ℤ) ^ 18 ≤ L := by exact_mod_cast hL
    norm_num at this
    omega
  have hMd' : (M : ℤ) ∣ (i : ℤ) - j := by
    push_cast at hMd
    exact (mul_dvd_mul_iff_left hL0).mp hMd
  have hz : (i : ℤ) - j = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd hMd' ?_
    rw [abs_lt]
    constructor <;> omega
  omega
theorem plaquetteCellImage_vertices_far {L M : ℕ} [NeZero (L * M)] (hL : 2 ^ 18 ≤ L)
    (p : TorusPlaquette (L * M)) (hp : p.2.1 < p.2.2)
    (k k' : Fin 4 → Fin M) (hk : k ≠ k') (z : TorusSite (L * M))
    (hz : z ∈ plaquetteVertices (plaquetteCellImage L M p k).1 (plaquetteCellImage L M p k).2.1
      (plaquetteCellImage L M p k).2.2) (z' : TorusSite (L * M))
    (hz' : z' ∈ plaquetteVertices (plaquetteCellImage L M p k').1 (plaquetteCellImage L M p k').2.1
      (plaquetteCellImage L M p k').2.2) : 2 ^ 17 ≤ supDist z z' := by
  obtain ⟨x, μ, ν⟩ := p
  obtain ⟨d, hd, rfl⟩ := reflectedPlaquette_vertex_near_centre L x μ ν hp _ hz
  obtain ⟨d', hd', rfl⟩ := reflectedPlaquette_vertex_near_centre L x μ ν hp _ hz'
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ k' i := by
    by_contra hcon
    push Not at hcon
    exact hk (funext hcon)
  have hne : ((k i : ℕ)) ≠ ((k' i : ℕ)) := fun h => hi (Fin.ext h)
  have hfar := natAbs_valMinAbs_shift_ge (M := M) hL (k i).2 (k' i).2 hne (e := d i - d' i) (by
    have h1 := abs_le.mp (hd i)
    have h2 := abs_le.mp (hd' i)
    rw [abs_le]
    constructor <;> omega)
  have e : (siteOfInt (fun i => integerCoords x i + (L : ℤ) * ((k i : ℕ) : ℤ) + d i) : TorusSite (L * M)) i -
      (siteOfInt (fun i => integerCoords x i + (L : ℤ) * ((k' i : ℕ) : ℤ) + d' i) : TorusSite (L * M)) i =
      ((((L : ℤ) * (((k i : ℕ) : ℤ) - ((k' i : ℕ) : ℤ)) + (d i - d' i) : ℤ)) : ZMod (L * M)) := by
    simp only [siteOfInt]
    push_cast
    ring
  refine hfar.trans ?_
  rw [← e]
  exact Finset.le_sup (f := fun i => (((siteOfInt (fun i => integerCoords x i + (L : ℤ) * ((k i : ℕ) : ℤ) + d i) : TorusSite (L * M)) i -
    (siteOfInt (fun i => integerCoords x i + (L : ℤ) * ((k' i : ℕ) : ℤ) + d' i) : TorusSite (L * M)) i).valMinAbs).natAbs)
    (Finset.mem_univ i)
end Separation
theorem plaquetteEnergyTailStatement_holds (h₁ : separatedHotPlaquettesRareStatement)
    (h₂ : plaquetteChessboardStatement) : plaquetteEnergyTailStatement := by
  intro a ha
  obtain ⟨L₁, r₁, hr₁, H₁⟩ := h₁ a ha
  obtain ⟨L₂, r₂, hr₂, H₂⟩ := h₂ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hodd hLe Tb hTa hTL hD hrt
  obtain ⟨y₁, Y₁⟩ := H₁ L hodd (le_trans (le_max_left _ _) hLe) Tb hTa hTL hD (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, Y₂⟩ := H₂ L hodd (le_trans (le_max_right _ _) hLe) Tb hTa hTL hD (hrt.trans (min_le_right _ _))
  refine ⟨max y₁ y₂, fun y hy hR hW => ?_⟩
  obtain ⟨c, t₀, yP, ht₀, A⟩ := Y₁ y ((le_max_left _ _).trans hy) hR hW
  have B := Y₂ y ((le_max_right _ _).trans hy) hR hW
  have hLbig : 2 ^ 18 ≤ Tb.side := le_trans (by norm_num) hD.L_ge
  refine ⟨2 * |c| * (Tb.side : ℝ) ^ 4, t₀, max yP (Real.exp 1), ht₀, ?_⟩
  intro T β j n _ hS hC hy' hdvd hn p hp t ht htt
  obtain ⟨m', hm'⟩ := hdvd
  have hn' : n = Tb.side * (2 * m') := by rw [hm']; show 2 * Tb.side * m' = _; ring
  subst hn'
  have hm0 : 0 < 2 * m' := by
    rcases Nat.eq_zero_or_pos (2 * m') with h | h
    · exfalso
      have := NeZero.ne (Tb.side * (2 * m'))
      rw [h] at this
      simp at this
    · exact h
  have hMn : (Tb.stepParameters y).n₀ ≤ 2 * m' := by
    have hn2 : Tb.side * (Tb.stepParameters y).n₀ ≤ Tb.side * (2 * m') := hn
    exact Nat.le_of_mul_le_mul_left hn2 (by omega)
  have hcoup : max yP (Real.exp 1) ≤ (couplingFlow (Tb.stepParameters y) β j).1 := hy'
  have hyP : yP ≤ (couplingFlow (Tb.stepParameters y) β j).1 := (le_max_left _ _).trans hcoup
  have hex : Real.exp 1 ≤ (couplingFlow (Tb.stepParameters y) β j).1 := (le_max_right _ _).trans hcoup
  set x := (couplingFlow (Tb.stepParameters y) β j).1 with hx
  have hlog : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hex)]
    exact hex
  have hB := B T β j (2 * m') hS hC (even_two_mul m') hMn p hp t
  have hlt : p.2.1 < p.2.2 := (mem_plaquettesIn_iff_lt_and_vertices.mp hp).1
  have hA := A T β j (Tb.side * (2 * m')) hS hC hyP ⟨Dvd.intro _ rfl, hn⟩ (Fin 4 → Fin (2 * m'))
    (plaquetteCellImage Tb.side (2 * m') p) (fun k => ?_)
    (fun k k' hk z hz z' hz' => plaquetteCellImage_vertices_far hLbig p hlt k k' hk z hz z' hz') t ht htt
  · set P := (markedSampleLaw T β j (Tb.side * (2 * m'))).real
      {u | t < plaquetteEnergy (topField (Tb.stepParameters y) j (Tb.side * (2 * m')) u) p.1 p.2.1 p.2.2} with hP
    have hP0 : 0 ≤ P := measureReal_nonneg
    have hcard : (Fintype.card (Fin 4 → Fin (2 * m')) : ℝ) = ((2 * m' : ℕ) : ℝ) ^ 4 := by
      simp
    set N := (2 * m') ^ 4 with hN
    have hNpos : N ≠ 0 := by
      rw [hN]
      exact pow_ne_zero _ hm0.ne'
    have hNr : (N : ℝ) = ((2 * m' : ℕ) : ℝ) ^ 4 := by
      rw [hN]
      push_cast
      ring
    set E : ℝ := c * (Real.log x + 1) * (Tb.side : ℝ) ^ 4 - 2 * Tb.coercivity * x * t with hE
    have hn4 : (((Tb.side * (2 * m') : ℕ)) : ℝ) ^ 4 = (Tb.side : ℝ) ^ 4 * (N : ℝ) := by
      rw [hNr]
      push_cast
      ring
    rw [← hx] at hA
    have hpow : P ^ N ≤ Real.exp E ^ N := by
      refine hB.trans (hA.trans (le_of_eq ?_))
      rw [← Real.exp_nat_mul, hcard, ← hNr, hn4, hE]
      congr 1
      ring
    have hroot : P ≤ Real.exp E := (pow_le_pow_iff_left₀ hP0 (Real.exp_pos _).le hNpos).mp hpow
    refine hroot.trans (Real.exp_le_exp.mpr ?_)
    have hLp : (0 : ℝ) ≤ (Tb.side : ℝ) ^ 4 := by positivity
    have h1 : c * (Real.log x + 1) ≤ 2 * |c| * Real.log x := by
      have h2 : c * (Real.log x + 1) ≤ |c| * (Real.log x + 1) :=
        mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith)
      have h3 : |c| * (Real.log x + 1) ≤ |c| * (2 * Real.log x) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
      linarith
    have h4 := mul_le_mul_of_nonneg_right h1 hLp
    rw [hE]
    show _ ≤ 2 * |c| * (Tb.side : ℝ) ^ 4 * Real.log x - 2 * Tb.coercivity * x * t
    nlinarith
  · exact mem_plaquettesIn_iff_lt_and_vertices.mpr ⟨by
      obtain ⟨x₀, μ, ν⟩ := p
      have h0 : μ < ν := hlt
      show ((cellReflection Tb.side _ _).mapPlaquette (x₀, μ, ν)).2.1 < ((cellReflection Tb.side _ _).mapPlaquette (x₀, μ, ν)).2.2
      unfold TorusIsometry.mapPlaquette
      have hdir : ∀ (g : TorusIsometry) i, g.axisPerm = 1 → g.imageAxis i = i := fun g i h => by
        rw [TorusIsometry.imageAxis, h]
        rfl
      simp only [hdir _ _ (show (cellReflection Tb.side _ _).axisPerm = 1 from rfl)]
      rw [if_pos h0]
      exact h0, fun _ _ => Finset.mem_univ _⟩
end YangMills.Construction.BoxEvents
end
