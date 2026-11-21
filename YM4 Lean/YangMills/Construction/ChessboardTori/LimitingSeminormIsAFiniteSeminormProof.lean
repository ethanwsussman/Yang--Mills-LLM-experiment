import YangMills.Construction.ChessboardTori.ChessboardValueAtAGrid
import YangMills.Construction.ChessboardTori.LimitingSeminormIsAFiniteSeminorm
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.ChessboardTori.LimChessboardNormSeminorm
variable {D : ChessboardSetup}
theorem smul_mem_cellObservables {S : Set InfiniteLattice.AmbientSpace} {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) (c : ℂ) :
    c • F ∈ ReflectionGrid.cellObservables (D := D) S := by
  obtain ⟨f, hf, ⟨C, hC⟩, rfl⟩ := hF
  refine ⟨fun u => c * f u, hf.const_mul c, ⟨‖c‖ * C, fun u => ?_⟩, ?_⟩
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC u) (norm_nonneg _)
  · funext U
    simp [Function.comp]
theorem add_mem_cellObservables {S : Set InfiniteLattice.AmbientSpace} {F G : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S)
    (hG : G ∈ ReflectionGrid.cellObservables (D := D) S) :
    F + G ∈ ReflectionGrid.cellObservables (D := D) S := by
  obtain ⟨f, hf, ⟨C, hC⟩, rfl⟩ := hF
  obtain ⟨f', hf', ⟨C', hC'⟩, rfl⟩ := hG
  refine ⟨fun u => f u + f' u, hf.add hf', ⟨C + C', fun u => ?_⟩, ?_⟩
  · exact (norm_add_le _ _).trans (add_le_add (hC u) (hC' u))
  · funext U
    simp [Function.comp]
theorem eventually_two_mul_cellSide_le (g : ReflectionGrid D) :
    ∀ᶠ n : ℕ+ in atTop,
      2 * (g.withExponent n).cellSide ≤
        PeriodicLattice.torusSide (D.withExponent n).L (D.withExponent n).m := by
  have hL : (1 : ℝ) ≤ D.L := D.one_lt_factor.le
  filter_upwards [eventually_ge_atTop (⟨g.q.toNat + 1, Nat.succ_pos _⟩ : ℕ+)] with n hn
  have hn' : g.q.toNat + 1 ≤ (n : ℕ) := hn
  have hq : g.q ≤ (((n : ℕ)) : ℤ) := by omega
  have h := zpow_le_zpow_right₀ hL hq
  rw [zpow_natCast] at h
  show 2 * (D.L : ℝ) ^ g.q ≤ 2 * (D.L : ℝ) ^ (n : ℕ)
  linarith
theorem eventually_normAtExponent_props (hV : GridChessboardNorm.Statement) (g : ReflectionGrid D)
    (hg : g.IsCoarse) :
    ∀ᶠ n : ℕ+ in atTop,
      (∀ F ∈ ReflectionGrid.cellObservables (D := D) (g.cell 0),
        (∀ c : ℂ, g.normAtExponent n (g.cell 0) (c • F) =
          ‖c‖ * g.normAtExponent n (g.cell 0) F) ∧
        (∀ G ∈ ReflectionGrid.cellObservables (D := D) (g.cell 0),
          g.normAtExponent n (g.cell 0) (F + G) ≤
            g.normAtExponent n (g.cell 0) F + g.normAtExponent n (g.cell 0) G) ∧
        g.normAtExponent n (g.cell 0) (fun U => starRingEnd ℂ (F U)) =
          g.normAtExponent n (g.cell 0) F ∧
        g.normAtExponent n (g.cell 0) F ≤ InfiniteLattice.observableSupNorm F ∧
        0 ≤ g.normAtExponent n (g.cell 0) F) ∧
      g.normAtExponent n (g.cell 0) (fun _ => 1) = 1 := by
  filter_upwards [eventually_two_mul_cellSide_le g] with n hn
  obtain ⟨-, -, hc, -⟩ := hV (D.withExponent n) (g.withExponent n) hg hn ((g.withExponent n).block 0) ⟨0, rfl⟩
  obtain ⟨h1, h2⟩ := hc ((g.withExponent n).cell 0) ⟨0, rfl⟩
  refine ⟨fun F hF => ?_, h2⟩
  obtain ⟨hs', ha', -, hconj, hn⟩ := h1 F hF
  have hs : ∀ c : ℂ, g.normAtExponent n (g.cell 0) (c • F) =
      ‖c‖ * g.normAtExponent n (g.cell 0) F := hs'
  have ha : ∀ G ∈ ReflectionGrid.cellObservables (D := D) (g.cell 0),
      g.normAtExponent n (g.cell 0) (F + G) ≤
        g.normAtExponent n (g.cell 0) F + g.normAtExponent n (g.cell 0) G := ha'
  refine ⟨hs, ha, hconj, hn, ?_⟩
  have h3 := ha _ (smul_mem_cellObservables hF (-1))
  have h6 : F + (-1 : ℂ) • F = (0 : ℂ) • F := by
    funext U
    simp
  rw [h6, hs 0, hs (-1)] at h3
  simp only [norm_zero, zero_mul, norm_neg, norm_one, one_mul] at h3
  linarith
theorem isBoundedUnder_le_normAtExponent (hV : GridChessboardNorm.Statement) (g : ReflectionGrid D)
    (hg : g.IsCoarse) {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) (g.cell 0)) :
    IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ+ => g.normAtExponent n (g.cell 0) F) :=
  isBoundedUnder_of_eventually_le
    ((eventually_normAtExponent_props hV g hg).mono fun _ h => (h.1 F hF).2.2.2.1)
theorem isBoundedUnder_ge_normAtExponent (hV : GridChessboardNorm.Statement) (g : ReflectionGrid D)
    (hg : g.IsCoarse) {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) (g.cell 0)) :
    IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ+ => g.normAtExponent n (g.cell 0) F) :=
  isBoundedUnder_of_eventually_ge
    ((eventually_normAtExponent_props hV g hg).mono fun _ h => (h.1 F hF).2.2.2.2)
theorem limChessboardNorm_isSeminorm (hV : GridChessboardNorm.Statement) :
    LimChessboardNormIsSeminorm.Statement := by
  intro D g hg
  have hev := eventually_normAtExponent_props hV g hg
  refine ⟨fun F hF => ?_, ?_⟩
  · have hB := isBoundedUnder_le_normAtExponent hV g hg hF
    have hb := isBoundedUnder_ge_normAtExponent hV g hg hF
    have hC := hb.isCoboundedUnder_le
    refine ⟨hB, hb, ?_, fun c => ?_, fun G hG => ?_, ?_, ?_⟩
    · exact le_limsup_of_frequently_le
        (hev.mono fun _ h => (h.1 F hF).2.2.2.2).frequently hB
    · have h1 : g.limChessboardNorm (c • F) =
          limsup ((fun x : ℝ => ‖c‖ * x) ∘ fun n : ℕ+ => g.normAtExponent n (g.cell 0) F) atTop :=
        limsup_congr (hev.mono fun _ h => (h.1 F hF).1 c)
      rw [h1]
      exact (Monotone.map_limsup_of_continuousAt
        (f := fun x : ℝ => ‖c‖ * x) (fun _ _ h => mul_le_mul_of_nonneg_left h (norm_nonneg c))
        _ (continuous_const.mul continuous_id).continuousAt hB hC).symm
    · have hB' := isBoundedUnder_le_normAtExponent hV g hg hG
      have hb' := isBoundedUnder_ge_normAtExponent hV g hg hG
      have hsum := isBoundedUnder_ge_normAtExponent hV g hg (add_mem_cellObservables hF hG)
      have hadd := limsup_add_le hb hB hb'.isCoboundedUnder_le hB'
      refine le_trans (limsup_le_limsup (hev.mono fun _ h => (h.1 F hF).2.1 G hG)
        hsum.isCoboundedUnder_le (isBoundedUnder_le_add hB hB')) hadd
    · exact limsup_congr (hev.mono fun _ h => (h.1 F hF).2.2.1)
    · exact limsup_le_of_le hC (hev.mono fun _ h => (h.1 F hF).2.2.2.1)
  · have h1 : g.limChessboardNorm (fun _ => 1) = limsup (fun _ : ℕ+ => (1 : ℝ)) atTop :=
      limsup_congr (hev.mono fun _ h => h.2)
    rw [h1, limsup_const]
end YangMills.Construction.ChessboardTori.LimChessboardNormSeminorm
end
