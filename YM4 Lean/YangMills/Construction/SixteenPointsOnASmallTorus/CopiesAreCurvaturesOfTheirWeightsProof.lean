import YangMills.Construction.ChessboardTori.GroupCoordinateByCoordinate
import YangMills.Construction.ChessboardTori.LinksAndPlaquettesUnderLatticeIsometries
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import YangMills.Construction.SixteenPointsOnASmallTorus.ArrayMeanIsTheMeanOfTheCopiesProof
import YangMills.Construction.SixteenPointsOnASmallTorus.ConfigurationsOfACubicPeriodGroup
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
open TorusFields WeightedResponses TestFunctions
private theorem valMinAbs_intCast_eq_of_two_mul_abs_lt {N : ℕ} [NeZero N] (Y : ℤ) (hY : 2 * |Y| < (N : ℤ)) :
    ((Y : ZMod N)).valMinAbs = Y := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
private theorem doubled_val_neg_add_cast {m : ℕ} [NeZero m] (x z : ZMod m) (i : ℤ) (hz : z = (i : ZMod m)) (b b' : ℕ) :
    ((2 * (x + -z).val + b + b' : ℕ) : ZMod (2 * m)) =
      ((2 * x.val + b + b' : ℕ) : ZMod (2 * m)) - ((2 * i : ℤ) : ZMod (2 * m)) := by
  subst hz
  have h1 : (((x + -(i : ZMod m)).val : ℤ) : ZMod m) = (((x.val : ℤ) - i : ℤ) : ZMod m) := by
    simp only [Int.cast_natCast, Int.cast_sub, ZMod.natCast_zmod_val]
    ring
  obtain ⟨u, hu⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
  have hv : (((2 * (x + -(i : ZMod m)).val + b + b' : ℕ) : ℤ)) =
      ((2 * x.val + b + b' : ℕ) : ℤ) - 2 * i - 2 * m * u := by
    push_cast
    linarith
  have h0 : (2 : ZMod (2 * m)) * (m : ZMod (2 * m)) = 0 := by
    exact_mod_cast ZMod.natCast_self (2 * m)
  have hc : ((2 * (x + -(i : ZMod m)).val + b + b' : ℕ) : ZMod (2 * m)) =
      ((((2 * (x + -(i : ZMod m)).val + b + b' : ℕ) : ℤ)) : ZMod (2 * m)) := by
    rw [Int.cast_natCast]
  rw [hc, hv]
  push_cast
  linear_combination -(u : ZMod (2 * m)) * h0
private theorem doubledBarycentre_translate {m : ℕ} [NeZero m] (p : TorusPlaquette m) (z : TorusSite m) (i : Fin 4 → ℤ)
    (hz : ∀ μ, z μ = (i μ : ZMod m)) (μ : Fin 4) :
    doubledBarycentre ((p.1 + -z, p.2) : TorusPlaquette m) μ = doubledBarycentre p μ - ((2 * i μ : ℤ) : ZMod (2 * m)) :=
  doubled_val_neg_add_cast (p.1 μ) (z μ) (i μ) (hz μ) _ _
private theorem signed_residue_cast {m M nn : ℕ} (hm : m = nn * M) (X i d : ℤ) (k : ℕ) (hk : (nn : ℤ) ∣ d - k)
    (Dd : ZMod (2 * m)) (hX : (X : ZMod (2 * m)) = Dd) (eps : ℤ)
    (heps : (-1 : ZMod (2 * m)) ^ k = (eps : ZMod (2 * m))) :
    (-1 : ZMod (2 * m)) ^ k * (Dd - ((2 * i : ℤ) : ZMod (2 * m)) - 2 * (M : ZMod (2 * m)) * (k : ZMod (2 * m))) =
      ((eps * (X - 2 * i - 2 * M * d) : ℤ) : ZMod (2 * m)) := by
  obtain ⟨t, ht⟩ := hk
  have hd : (d : ZMod (2 * m)) - (k : ZMod (2 * m)) = (nn : ZMod (2 * m)) * (t : ZMod (2 * m)) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod (2 * m)) ht
  have h0 : (2 : ZMod (2 * m)) * ((nn : ZMod (2 * m)) * (M : ZMod (2 * m))) = 0 := by
    have := ZMod.natCast_self (2 * m)
    rw [hm] at this ⊢
    exact_mod_cast this
  rw [heps, ← hX]
  push_cast
  linear_combination (2 * (eps : ZMod (2 * m)) * (M : ZMod (2 * m))) * hd + ((eps : ZMod (2 * m)) * (t : ZMod (2 * m))) * h0
private theorem center_injective {D : ChessboardTori.ChessboardSetup} {p p' : D.Plaquette}
    (h : ∀ μ, p.center μ = p'.center μ) : p = p' := by
  have ha : D.mesh ≠ 0 := D.mesh_pos.ne'
  obtain ⟨n, hn⟩ := p.corner.2
  obtain ⟨n', hn'⟩ := p'.corner.2
  have hlt := p.lowAxis_lt_highAxis
  have hlt' := p'.lowAxis_lt_highAxis
  have hint : ∀ μ, 2 * n μ + ((if μ = p.lowAxis then 1 else 0) + (if μ = p.highAxis then 1 else 0) : ℤ) =
      2 * n' μ + ((if μ = p'.lowAxis then 1 else 0) + (if μ = p'.highAxis then 1 else 0) : ℤ) := by
    intro μ
    have h1 := h μ
    simp only [InfiniteLattice.ElementaryPlaquette.center, Pi.add_apply, Pi.single_apply, hn μ, hn' μ] at h1
    have h2 : ((2 * n μ + ((if μ = p.lowAxis then 1 else 0) + (if μ = p.highAxis then 1 else 0) : ℤ) : ℤ) : ℝ) =
        ((2 * n' μ + ((if μ = p'.lowAxis then 1 else 0) + (if μ = p'.highAxis then 1 else 0) : ℤ) : ℤ) : ℝ) := by
      apply mul_right_cancel₀ ha
      push_cast
      split_ifs at h1 ⊢ <;> linear_combination 2 * h1
    exact_mod_cast h2
  have key : ∀ f s f' s' : Fin 4, f < s → f' < s' → (∀ μ, (μ = f ∨ μ = s) ↔ (μ = f' ∨ μ = s')) → f = f' ∧ s = s' := by
    decide
  have par : ∀ μ, (μ = p.lowAxis ∨ μ = p.highAxis) ↔ (μ = p'.lowAxis ∨ μ = p'.highAxis) := by
    intro μ
    have h3 := hint μ
    have hne : ¬(μ = p.lowAxis ∧ μ = p.highAxis) := fun hh => hlt.ne (hh.1.symm.trans hh.2)
    have hne' : ¬(μ = p'.lowAxis ∧ μ = p'.highAxis) := fun hh => hlt'.ne (hh.1.symm.trans hh.2)
    split_ifs at h3 <;> first | (exfalso; omega) | tauto
  obtain ⟨e1, e2⟩ := key _ _ _ _ hlt hlt' par
  have hnn : ∀ μ, n μ = n' μ := fun μ => by
    have h3 := hint μ
    rw [e1, e2] at h3
    linarith
  apply InfiniteLattice.ElementaryPlaquette.ext
  · apply Subtype.ext
    funext μ
    rw [hn μ, hn' μ, hnn μ]
  · exact e1
  · exact e2
private theorem center_shiftPlaquette {D : ChessboardTori.ChessboardSetup} (q : D.Plaquette)
    (v : InfiniteLattice.LatticePoint D.mesh) (μ : Fin 4) :
    (D.shiftPlaquette q v).center μ = q.center μ + (v : InfiniteLattice.AmbientSpace) μ := by
  simp only [ChessboardTori.ChessboardSetup.shiftPlaquette, InfiniteLattice.ElementaryPlaquette.center, Pi.add_apply,
    AddSubgroup.coe_add]
  ring
private theorem mover_cell_apply {D : ChessboardTori.ChessboardSetup} (g : ChessboardTori.ReflectionGrid D)
    (hg : g.ReflectionGroupCoordForm) (i k : Fin 4 → ℤ) (x : InfiniteLattice.AmbientSpace) (μ : Fin 4) :
    (g.mover (g.cell i) (g.cell k)).1 x μ =
      (g.origin μ + g.cellSide * (i μ : ℝ) + g.cellSide / 2) + g.cellSide * ((k μ - i μ : ℤ) : ℝ) +
        ((if Even (k μ - i μ) then 1 else -1 : ℤ) : ℝ) *
          (x μ - (g.origin μ + g.cellSide * (i μ : ℝ) + g.cellSide / 2)) := by
  have hex := hg.2.2.2.2.2.2.1 (g.cell i) ⟨i, rfl⟩ (g.cell k) ⟨k, rfl⟩
  have hr : (g.mover (g.cell i) (g.cell k)).1 '' g.cell i = g.cell k :=
    Classical.epsilon_spec (p := fun r : g.reflectionGroup => r.1 '' g.cell i = g.cell k) hex.exists
  generalize g.mover (g.cell i) (g.cell k) = r at hr ⊢
  have hl : 0 < g.cellSide := zpow_pos (by linarith [D.one_lt_factor]) _
  have hm : ∀ y ∈ g.cell i, r.1 y μ - (g.origin μ + g.cellSide * k μ) ∈ Set.Icc 0 g.cellSide := fun y hy => by
    have h1 : r.1 y ∈ g.cell k := hr ▸ Set.mem_image_of_mem _ hy
    exact h1 μ
  have h0 : (fun ν => g.origin ν + g.cellSide * i ν : InfiniteLattice.AmbientSpace) ∈ g.cell i := fun ν => by
    have e : g.origin ν + g.cellSide * i ν - (g.origin ν + g.cellSide * i ν) = 0 := by ring
    simp only [e]
    exact ⟨le_rfl, hl.le⟩
  have h1 : (fun ν => g.origin ν + g.cellSide * (i ν + 1) : InfiniteLattice.AmbientSpace) ∈ g.cell i := fun ν => by
    have e : g.origin ν + g.cellSide * (i ν + 1) - (g.origin ν + g.cellSide * i ν) = g.cellSide := by ring
    simp only [e]
    exact ⟨hl.le, le_rfl⟩
  have a0 := hm _ h0
  have a1 := hm _ h1
  rcases hg.1 r.1 r.2 μ with ⟨t, ht⟩ | ⟨k1, hk1⟩
  · have ht' : ∀ y : InfiniteLattice.AmbientSpace, r.1 y μ = y μ + 2 * t * g.cellSide := fun y => by
      have h2 := ht y
      simp only [ChessboardTori.ReflectionGrid.coordShift] at h2
      linarith
    rw [ht'] at a0 a1
    have c0 : (0 : ℝ) ≤ ((i μ + 2 * t - k μ : ℤ) : ℝ) := by
      by_contra hh
      have h2 := mul_neg_of_neg_of_pos (not_le.mp hh) hl
      push_cast at h2
      nlinarith [a0.1]
    have c1 : ((i μ + 2 * t - k μ : ℤ) : ℝ) ≤ 0 := by
      by_contra hh
      have h2 := mul_pos (not_le.mp hh) hl
      push_cast at h2
      nlinarith [a1.2]
    have c2 : i μ + 2 * t - k μ = 0 := le_antisymm (by exact_mod_cast c1) (by exact_mod_cast c0)
    have hev : Even (k μ - i μ) := ⟨t, by omega⟩
    rw [if_pos hev, ht' x]
    have c3 : ((k μ : ℝ) - (i μ : ℝ)) = 2 * t := by
      have : ((i μ + 2 * t - k μ : ℤ) : ℝ) = 0 := by rw [c2]; simp
      push_cast at this
      linarith
    push_cast
    rw [c3]
    ring
  · have ht' : ∀ y : InfiniteLattice.AmbientSpace, r.1 y μ = 2 * g.origin μ + 2 * k1 * g.cellSide - y μ := fun y => by
      have h2 := hk1 y
      simp only [ChessboardTori.ReflectionGrid.coordReflect] at h2
      linarith
    rw [ht'] at a0 a1
    have c0 : (0 : ℝ) ≤ ((2 * k1 - i μ - k μ - 1 : ℤ) : ℝ) := by
      by_contra hh
      have h2 := mul_neg_of_neg_of_pos (not_le.mp hh) hl
      push_cast at h2
      nlinarith [a1.1]
    have c1 : ((2 * k1 - i μ - k μ - 1 : ℤ) : ℝ) ≤ 0 := by
      by_contra hh
      have h2 := mul_pos (not_le.mp hh) hl
      push_cast at h2
      nlinarith [a0.2]
    have c2 : 2 * k1 - i μ - k μ - 1 = 0 := le_antisymm (by exact_mod_cast c1) (by exact_mod_cast c0)
    have hev : ¬Even (k μ - i μ) := by
      rintro ⟨u, hu⟩
      omega
    rw [if_neg hev, ht' x]
    have c3 : 2 * (k1 : ℝ) = (i μ : ℝ) + (k μ : ℝ) + 1 := by
      have : ((2 * k1 - i μ - k μ - 1 : ℤ) : ℝ) = 0 := by rw [c2]; simp
      push_cast at this
      linarith
    push_cast
    rw [c3]
    ring
section CubicChartSection
set_option linter.unusedSectionVars false
variable {D : ChessboardTori.ChessboardSetup} {P : ChessboardTori.PeriodSubgroup D} {m M nn : ℕ} [NeZero m]
  {τ : OrientedPlaquette m ≃ P.Face} {z : TorusSite m} {i : Fin 4 → ℤ} {C : Fin 4 → ℝ}
  {k : Fin 4 → ℕ} {d eps : Fin 4 → ℤ}
private structure CubicChart (P : ChessboardTori.PeriodSubgroup D) (m M nn : ℕ) [NeZero m]
    (τ : OrientedPlaquette m ≃ P.Face) (z : TorusSite m) (i : Fin 4 → ℤ) (C : Fin 4 → ℝ) : Prop where
  mult_eq : ∀ μ, P.mult μ = (m : ℤ)
  m_eq : m = nn * M
  two_le : 2 ≤ nn
  M_pos : 0 < M
  site : ∀ μ, z μ = (i μ : ZMod m)
  centre : ∀ μ, D.mesh * (i μ : ℝ) = C μ
  faceCenter_eq : ∀ p, P.faceCenter (τ p) = P.proj fun μ => D.mesh / 2 * ((doubledBarycentre p.1 μ).val : ℝ)
  maps : P.ProjMapsEdgesAndFaces
  fibres : P.ProjFibresArePeriodOrbits
private structure CopyTwist (m nn : ℕ) (k : Fin 4 → ℕ) (d eps : Fin 4 → ℤ) : Prop where
  dvd : ∀ μ, (nn : ℤ) ∣ d μ - k μ
  sign : ∀ μ, eps μ = 1 ∨ eps μ = -1
  pow : ∀ μ, (-1 : ZMod (2 * m)) ^ k μ = (eps μ : ZMod (2 * m))
private theorem CopyTwist.sign_mul_self (W : CopyTwist m nn k d eps) (μ : Fin 4) : (eps μ : ℝ) * (eps μ : ℝ) = 1 := by
  rcases W.sign μ with h | h <;> simp [h]
private theorem CubicChart.sideLengths_eq (H : CubicChart P m M nn τ z i C) (μ : Fin 4) :
    P.sideLengths μ = (m : ℝ) * D.mesh := by
  show ((P.mult μ : ℤ) : ℝ) * D.mesh = _
  rw [H.mult_eq]
  simp
private theorem CubicChart.two_mul_le (H : CubicChart P m M nn τ z i C) : 2 * M ≤ m := by
  rw [H.m_eq]
  exact Nat.mul_le_mul_right M H.two_le
private theorem CubicChart.exists_lift (H : CubicChart P m M nn τ z i C) (q : D.Plaquette) (pp : OrientedPlaquette m)
    (hq : P.projFace q = τ pp) (μ : Fin 4) :
    ∃ X : ℤ, (X : ZMod (2 * m)) = doubledBarycentre pp.1 μ ∧ q.center μ = D.mesh / 2 * (X : ℝ) := by
  have hb := H.maps.2.2.2.2.2.2 q
  rw [hq, H.faceCenter_eq] at hb
  have hk : q.center - (fun μ => D.mesh / 2 * ((doubledBarycentre pp.1 μ).val : ℝ)) ∈
      (BoxTorus.projection P.sideLengths).ker := by
    rw [AddMonoidHom.mem_ker, map_sub, sub_eq_zero]
    exact hb.symm
  rw [BoxTorus.projection_ker] at hk
  obtain ⟨t, ht⟩ := AddSubgroup.mem_zmultiples_iff.mp (((AddSubgroup.mem_pi _).mp hk) μ (Set.mem_univ μ))
  rw [H.sideLengths_eq, zsmul_eq_mul] at ht
  have h0 : (2 : ZMod (2 * m)) * (m : ZMod (2 * m)) = 0 := by
    exact_mod_cast ZMod.natCast_self (2 * m)
  refine ⟨((doubledBarycentre pp.1 μ).val : ℤ) + 2 * m * t, ?_, ?_⟩
  · push_cast
    rw [ZMod.natCast_zmod_val]
    linear_combination (t : ZMod (2 * m)) * h0
  · simp only [Pi.sub_apply] at ht
    push_cast
    linarith
private theorem CubicChart.exists_period (H : CubicChart P m M nn τ z i C) (u : Fin 4 → ℤ) :
    ∃ v : InfiniteLattice.LatticePoint D.mesh, v ∈ D.periodSubgroupOfGrid P.mult ∧
      ∀ μ, (v : InfiniteLattice.AmbientSpace) μ = (u μ : ℝ) * ((m : ℝ) * D.mesh) := by
  have hy : (fun μ => (u μ : ℝ) * ((m : ℝ) * D.mesh) : InfiniteLattice.AmbientSpace) ∈ D.periodGroup P.mult := by
    refine (AddSubgroup.mem_pi _).mpr fun μ _ => AddSubgroup.mem_zmultiples_iff.mpr ⟨u μ, ?_⟩
    rw [zsmul_eq_mul]
    show (u μ : ℝ) * (((P.mult μ : ℤ) : ℝ) * D.mesh) = _
    rw [H.mult_eq]
    simp
  exact ⟨⟨_, D.periodGroup_le_gridPoints _ hy⟩, hy, fun _ => rfl⟩
private theorem CubicChart.period_apply (H : CubicChart P m M nn τ z i C) {v : InfiniteLattice.LatticePoint D.mesh}
    (hv : v ∈ D.periodSubgroupOfGrid P.mult) (μ : Fin 4) :
    ∃ t : ℤ, (v : InfiniteLattice.AmbientSpace) μ = (t : ℝ) * ((m : ℝ) * D.mesh) := by
  have hv' : (v : InfiniteLattice.AmbientSpace) ∈ D.periodGroup P.mult := hv
  obtain ⟨t, ht⟩ := AddSubgroup.mem_zmultiples_iff.mp (((AddSubgroup.mem_pi _).mp hv') μ (Set.mem_univ μ))
  refine ⟨t, ?_⟩
  rw [← ht, zsmul_eq_mul]
  show (t : ℝ) * (((P.mult μ : ℤ) : ℝ) * D.mesh) = _
  rw [H.mult_eq]
  simp
private theorem reflectedPoint_apply (a₀ : ℝ) (M : ℕ) (k : Fin 4 → ℕ) (p : TorusPlaquette m) (μ : Fin 4) :
    (reflectedPoint a₀ M k p) μ = a₀ / 2 *
      ((((-1 : ZMod (2 * m)) ^ k μ *
        (doubledBarycentre p μ - 2 * (M : ZMod (2 * m)) * (k μ : ZMod (2 * m)))).valMinAbs : ℤ) : ℝ) :=
  rfl
private theorem CubicChart.reflected_residue (H : CubicChart P m M nn τ z i C) (W : CopyTwist m nn k d eps)
    (pp : OrientedPlaquette m) (μ : Fin 4) (X : ℤ) (hX : (X : ZMod (2 * m)) = doubledBarycentre pp.1 μ) :
    (-1 : ZMod (2 * m)) ^ k μ *
        (doubledBarycentre ((pp.1.1 + -z, pp.1.2) : TorusPlaquette m) μ - 2 * (M : ZMod (2 * m)) * (k μ : ZMod (2 * m))) =
      ((eps μ * (X - 2 * i μ - 2 * M * d μ) : ℤ) : ZMod (2 * m)) := by
  rw [doubledBarycentre_translate pp.1 z i H.site μ]
  exact signed_residue_cast H.m_eq X (i μ) (d μ) (k μ) (W.dvd μ) _ hX (eps μ) (W.pow μ)
private theorem CubicChart.reflectedPoint_of_lift (H : CubicChart P m M nn τ z i C) (W : CopyTwist m nn k d eps)
    (q : D.Plaquette) (pp : OrientedPlaquette m) (hq : P.projFace q = τ pp) (x : InfiniteLattice.AmbientSpace)
    (hx : ∀ μ, q.center μ = C μ + D.mesh * M * (d μ : ℝ) + (eps μ : ℝ) * (x μ - C μ))
    (hs : ∀ μ, |x μ - C μ| ≤ D.mesh * M / 2) (μ : Fin 4) :
    (reflectedPoint D.mesh M k ((pp.1.1 + -z, pp.1.2) : TorusPlaquette m)) μ = x μ - C μ := by
  obtain ⟨X, hX, hb⟩ := H.exists_lift q pp hq μ
  have ha := D.mesh_pos
  have hxY : x μ - C μ = D.mesh / 2 * ((eps μ * (X - 2 * i μ - 2 * M * d μ) : ℤ) : ℝ) := by
    have h1 : (eps μ : ℝ) * (x μ - C μ) = D.mesh / 2 * ((X : ℝ) - 2 * i μ - 2 * M * d μ) := by
      have h2 := hx μ
      rw [hb, ← H.centre μ] at h2
      rw [← H.centre μ]
      linarith
    push_cast
    calc x μ - C μ = ((eps μ : ℝ) * (eps μ : ℝ)) * (x μ - C μ) := by rw [W.sign_mul_self, one_mul]
      _ = (eps μ : ℝ) * ((eps μ : ℝ) * (x μ - C μ)) := by ring
      _ = _ := by rw [h1]; ring
  have hYM : |eps μ * (X - 2 * i μ - 2 * M * d μ)| ≤ (M : ℤ) := by
    have h1 := hs μ
    rw [hxY, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < D.mesh / 2)] at h1
    have h2 : |((eps μ * (X - 2 * i μ - 2 * M * d μ) : ℤ) : ℝ)| ≤ (M : ℝ) := by
      have h3 : D.mesh / 2 * |((eps μ * (X - 2 * i μ - 2 * M * d μ) : ℤ) : ℝ)| ≤ D.mesh / 2 * (M : ℝ) := by linarith
      exact le_of_mul_le_mul_left h3 (by positivity)
    exact_mod_cast h2
  have hsm : 2 * |eps μ * (X - 2 * i μ - 2 * M * d μ)| < ((2 * m : ℕ) : ℤ) := by
    have h1 := H.two_mul_le
    have h2 := H.M_pos
    push_cast
    omega
  rw [reflectedPoint_apply, H.reflected_residue W pp μ X hX, valMinAbs_intCast_eq_of_two_mul_abs_lt _ hsm, hxY]
private theorem CubicChart.exists_lift_of_reflected (H : CubicChart P m M nn τ z i C) (W : CopyTwist m nn k d eps)
    (pp : OrientedPlaquette m) :
    ∃ q : D.Plaquette, P.projFace q = τ pp ∧
      ∀ μ, q.center μ =
        C μ + D.mesh * M * (d μ : ℝ) + (eps μ : ℝ) * (reflectedPoint D.mesh M k ((pp.1.1 + -z, pp.1.2) : TorusPlaquette m)) μ := by
  obtain ⟨q0, hq0⟩ := H.maps.2.2.2.1 (τ pp)
  choose X hX hb using fun μ => H.exists_lift q0 pp hq0 μ
  have hcong : ∀ μ, ∃ u : ℤ, ((-1 : ZMod (2 * m)) ^ k μ *
      (doubledBarycentre ((pp.1.1 + -z, pp.1.2) : TorusPlaquette m) μ - 2 * (M : ZMod (2 * m)) * (k μ : ZMod (2 * m)))).valMinAbs =
      eps μ * (X μ - 2 * i μ - 2 * M * d μ) + 2 * m * u := by
    intro μ
    have h1 : ((((-1 : ZMod (2 * m)) ^ k μ * (doubledBarycentre ((pp.1.1 + -z, pp.1.2) : TorusPlaquette m) μ -
        2 * (M : ZMod (2 * m)) * (k μ : ZMod (2 * m)))).valMinAbs : ℤ) : ZMod (2 * m)) =
        ((eps μ * (X μ - 2 * i μ - 2 * M * d μ) : ℤ) : ZMod (2 * m)) := by
      rw [ZMod.coe_valMinAbs]
      exact H.reflected_residue W pp μ (X μ) (hX μ)
    obtain ⟨u, hu⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
    refine ⟨-u, ?_⟩
    push_cast at hu
    linarith
  choose u hu using hcong
  obtain ⟨v, hv, hvc⟩ := H.exists_period (fun μ => eps μ * u μ)
  refine ⟨D.shiftPlaquette q0 v, ?_, fun μ => ?_⟩
  · rw [← hq0]
    exact ((H.fibres.2.2 q0 _).mpr ⟨v, hv, rfl⟩).symm
  · rw [center_shiftPlaquette, hb μ, hvc μ, reflectedPoint_apply, hu μ, ← H.centre μ]
    push_cast
    linear_combination (-(D.mesh / 2) * ((X μ : ℝ) - 2 * i μ - 2 * M * d μ)) * W.sign_mul_self μ
private theorem CubicChart.finsum_eq_sum (H : CubicChart P m M nn τ z i C) (W : CopyTwist m nn k d eps)
    {σ : D.Plaquette → D.Plaquette} (hσ : Function.Surjective σ)
    (hb : ∀ p μ, (σ p).center μ = C μ + D.mesh * M * (d μ : ℝ) + (eps μ : ℝ) * (p.center μ - C μ))
    {h : InfiniteLattice.AmbientSpace → ℝ} {h' : EuclideanFourSpace → ℝ}
    (hsup : ∀ x, h x ≠ 0 → ∀ μ, |x μ - C μ| ≤ D.mesh * M / 2)
    (hh' : ∀ y, h' y = h fun μ => C μ + y μ)
    (A : D.Plaquette → ℝ) (E : TorusPlaquette m → ℝ)
    (hE : ∀ p (pp : OrientedPlaquette m), P.projFace (σ p) = τ pp → A p = E pp.1) :
    ∑ᶠ p : D.Plaquette, A p • h p.center =
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), reflectedWeightAbout D.mesh M z k h' p * E p := by
  classical
  have ha := D.mesh_pos
  let e : D.Plaquette → OrientedPlaquette m := fun p => τ.symm (P.projFace (σ p))
  have he : ∀ p, P.projFace (σ p) = τ (e p) := fun p => (τ.apply_symm_apply _).symm
  have hwv : ∀ pp : TorusPlaquette m,
      reflectedWeightAbout D.mesh M z k h' pp = h' (reflectedPoint D.mesh M k ((pp.1 + -z, pp.2) : TorusPlaquette m)) :=
    fun _ => rfl
  have hval : ∀ p, h p.center ≠ 0 → reflectedWeightAbout D.mesh M z k h' (e p).1 = h p.center := by
    intro p hp
    rw [hwv, hh']
    congr 1
    funext μ
    rw [H.reflectedPoint_of_lift W (σ p) (e p) (he p) p.center (hb p) (hsup _ hp) μ]
    ring
  let T : Finset (TorusPlaquette m) :=
    (plaquettesIn (Finset.univ : Finset (TorusSite m))).filter fun pp => reflectedWeightAbout D.mesh M z k h' pp ≠ 0
  have hmem : ∀ pp : OrientedPlaquette m, pp.1 ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)) := by
    intro pp
    simp [plaquettesIn, pp.2]
  have hmaps : ∀ p, h p.center ≠ 0 → (e p).1 ∈ T := fun p hp =>
    Finset.mem_filter.mpr ⟨hmem _, by rw [hval p hp]; exact hp⟩
  have hinj : ∀ p₁ p₂, h p₁.center ≠ 0 → h p₂.center ≠ 0 → (e p₁).1 = (e p₂).1 → p₁ = p₂ := by
    intro p₁ p₂ h₁ h₂ h12
    have h3 : P.projFace (σ p₁) = P.projFace (σ p₂) := by
      rw [he, he, Subtype.ext h12]
    obtain ⟨v, hv, hv2⟩ := (H.fibres.2.2 _ _).mp h3
    apply center_injective
    intro μ
    obtain ⟨t, ht⟩ := H.period_apply hv μ
    have b1 := hb p₁ μ
    have b2 := hb p₂ μ
    have b3 := center_shiftPlaquette (σ p₁) v μ
    rw [← hv2, ht] at b3
    have s1 := abs_le.mp (hsup _ h₁ μ)
    have s2 := abs_le.mp (hsup _ h₂ μ)
    have hM : (0 : ℝ) < (M : ℝ) := by exact_mod_cast H.M_pos
    have hmM : 2 * (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast H.two_mul_le
    have hsgn : (eps μ : ℝ) = 1 ∨ (eps μ : ℝ) = -1 := by
      rcases W.sign μ with h4 | h4 <;> simp [h4]
    have hbound : |(t : ℝ) * ((m : ℝ) * D.mesh)| ≤ D.mesh * M := by
      rw [abs_le]
      rcases hsgn with h4 | h4 <;> rw [h4] at b1 b2 <;> constructor <;> linarith [s1.1, s1.2, s2.1, s2.2]
    have ht0 : t = 0 := by
      by_contra hne
      have h5 : (1 : ℝ) ≤ |(t : ℝ)| := by exact_mod_cast Int.one_le_abs hne
      rw [abs_mul, abs_of_pos (mul_pos (by linarith) ha : (0 : ℝ) < (m : ℝ) * D.mesh)] at hbound
      have h6 : (m : ℝ) * D.mesh ≤ D.mesh * M := by nlinarith [mul_pos ha hM]
      nlinarith [mul_pos ha hM]
    rw [ht0] at b3
    rcases hsgn with h4 | h4 <;> rw [h4] at b1 b2 <;> push_cast at b3 <;> linarith
  have hsurj : ∀ pp ∈ T, ∃ p, h p.center ≠ 0 ∧ (e p).1 = pp := by
    intro pp hpp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hpp
    have hord : pp.2.1 < pp.2.2 := (Finset.mem_filter.mp h1).2.1
    obtain ⟨q, hq, hqb⟩ := H.exists_lift_of_reflected W (⟨pp, hord⟩ : OrientedPlaquette m)
    obtain ⟨p, rfl⟩ := hσ q
    have hx : p.center = fun μ => C μ + (reflectedPoint D.mesh M k ((pp.1 + -z, pp.2) : TorusPlaquette m)) μ := by
      funext μ
      have b1 := hb p μ
      have b2 := hqb μ
      have hsgn : (eps μ : ℝ) = 1 ∨ (eps μ : ℝ) = -1 := by
        rcases W.sign μ with h4 | h4 <;> simp [h4]
      rcases hsgn with h4 | h4 <;> rw [h4] at b1 b2 <;> simp only at b2 <;> linarith
    refine ⟨p, ?_, ?_⟩
    · rw [hx, ← hh', ← hwv]
      exact h2
    · have h3 : e p = ⟨pp, hord⟩ := τ.symm_apply_eq.mpr hq
      rw [h3]
  have hfin : {p : D.Plaquette | h p.center ≠ 0}.Finite :=
    Set.Finite.of_injOn (f := fun p => (e p).1) (t := (T : Set (TorusPlaquette m)))
      (fun p hp => hmaps p hp) (fun p₁ h₁ p₂ h₂ h12 => hinj p₁ p₂ h₁ h₂ h12) T.finite_toSet
  calc ∑ᶠ p : D.Plaquette, A p • h p.center
      = ∑ p ∈ hfin.toFinset, A p • h p.center := by
        refine finsum_eq_sum_of_support_subset _ ?_
        intro p hp
        simp only [Function.mem_support] at hp
        have h0 : h p.center ≠ 0 := fun h1 => hp (by simp [h1])
        simpa using h0
    _ = ∑ pp ∈ T, reflectedWeightAbout D.mesh M z k h' pp * E pp := by
        refine Finset.sum_bij (fun p _ => (e p).1) ?_ ?_ ?_ ?_
        · intro p hp
          exact hmaps p (by simpa using hp)
        · intro p₁ h₁ p₂ h₂ h12
          exact hinj p₁ p₂ (by simpa using h₁) (by simpa using h₂) h12
        · intro pp hpp
          obtain ⟨p, h1, h2⟩ := hsurj pp hpp
          exact ⟨p, by simpa using h1, h2⟩
        · intro p hp
          have h1 : h p.center ≠ 0 := by simpa using hp
          rw [hval p h1, hE p (e p) (he p), smul_eq_mul]
          ring
    _ = ∑ pp ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), reflectedWeightAbout D.mesh M z k h' pp * E pp := by
        refine Finset.sum_subset (Finset.filter_subset _ _) ?_
        intro pp h1 h2
        have h3 : reflectedWeightAbout D.mesh M z k h' pp = 0 := by
          by_contra hne
          exact h2 (Finset.mem_filter.mpr ⟨h1, hne⟩)
        rw [h3, zero_mul]
end CubicChartSection
private theorem signedConj_ofReal (s : ℤˣ) (x : ℝ) : Conventions.signedConj s (x : ℂ) = (x : ℂ) := by apply _root_.YangMills.SharedProofs.p21399 <;> assumption
private theorem neg_one_pow_eq_of_dvd {N nn : ℕ} (hnn : Even nn) {d : ℤ} {k : ℕ} (h : (nn : ℤ) ∣ d - k) :
    (-1 : ZMod N) ^ k = (((if Even d then 1 else -1 : ℤ)) : ZMod N) := by
  have hpar : Even d ↔ Even (k : ℤ) := by
    have h1 : Even (d - k) := ((Int.even_coe_nat nn).mpr hnn).trans_dvd h
    exact Int.even_sub.mp h1
  rw [Int.even_coe_nat] at hpar
  by_cases hk : Even k
  · rw [if_pos (hpar.mpr hk), hk.neg_one_pow]
    simp
  · rw [if_neg (fun h1 => hk (hpar.mp h1)), (Nat.not_even_iff_odd.mp hk).neg_one_pow]
    simp
theorem reflectedCopiesAsCurvatureStatement_holds (hC : cubicPeriodFieldsStatement)
    (hLP : ChessboardTori.LatticeSymmetryAction.Statement)
    (hG : ChessboardTori.ReflectionGroupCoordinates.Statement)
    (hQ : ChessboardTori.ProjOnEdgesAndFaces.Statement) :
    reflectedCopiesAsCurvatureStatement := by
  intro L _ D c κ j h h' z hDL hκ hsup hh' hz
  subst hDL
  obtain ⟨hcar, hsame, hext⟩ := hQ D (ReflectedCopies.gridPeriods c.grid (ReflectedCopies.cubicCounts D j))
  have hs : ∀ μ, (ReflectedCopies.gridPeriods c.grid (ReflectedCopies.cubicCounts D j)).mult μ =
      ((twoCellSide D.L j 0 * D.L ^ κ : ℕ) : ℤ) := by
    intro μ
    have hk : (c.grid.q + ((D.K : ℕ) : ℤ)).toNat = κ := by omega
    show (2 * (D.L : ℤ) ^ j) * ((D.L : ℤ) ^ (c.grid.q + ((D.K : ℕ) : ℤ)).toNat) = _
    rw [hk]
    simp [twoCellSide]
  obtain ⟨Ψ, τ, hmp, hact, hpl⟩ := hC D _ (twoCellSide D.L j 0 * D.L ^ κ) hs
  refine ⟨Ψ, hmp, hact, fun U => ?_⟩
  choose i hi1 hi2 using hz
  have hMpos : 0 < D.L ^ κ := Nat.pos_of_ne_zero (NeZero.ne _)
  have hside : c.grid.cellSide = D.mesh * ((D.L ^ κ : ℕ) : ℝ) := by
    have hk : (c.grid.q + ((D.K : ℕ) : ℤ)).toNat = κ := by omega
    rw [c.grid.cellSide_eq, ChessboardTori.ReflectionGrid.cellRatio, hk]
    push_cast
    ring
  have H : CubicChart _ (twoCellSide D.L j 0 * D.L ^ κ) (D.L ^ κ) (twoCellSide D.L j 0) τ z i
      (fun μ => c.grid.origin μ + c.grid.cellSide * (c.index μ : ℝ) + c.grid.cellSide / 2) :=
    { mult_eq := hs
      m_eq := rfl
      two_le := by
        have hL : 0 < D.L ^ j := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne _))
        simp only [twoCellSide, Nat.sub_zero]
        omega
      M_pos := hMpos
      site := hi1
      centre := hi2
      faceCenter_eq := fun p => (hpl U p).2
      maps := hcar
      fibres := hsame }
  have hsup' : ∀ x, h x ≠ 0 → ∀ μ, |x μ - (c.grid.origin μ + c.grid.cellSide * (c.index μ : ℝ) + c.grid.cellSide / 2)| ≤
      D.mesh * ((D.L ^ κ : ℕ) : ℝ) / 2 := by
    intro x hx μ
    have h1 : x ∈ c.cell := interior_subset (hsup x hx)
    have h2 := h1 μ
    rw [← hside, abs_le]
    constructor <;> linarith [h2.1, h2.2]
  refine ⟨?_, fun k k' hk => ?_⟩
  · have W : CopyTwist (twoCellSide D.L j 0 * D.L ^ κ) (twoCellSide D.L j 0) (fun _ => 0) (fun _ => 0) (fun _ => 1) :=
      { dvd := fun μ => by simp
        sign := fun μ => Or.inl rfl
        pow := fun μ => by simp }
    have := H.finsum_eq_sum W (σ := id) Function.surjective_id
      (fun p μ => by simp) hsup' hh'
      (fun p => InfiniteLattice.faceEnergy
        ((ReflectedCopies.gridPeriods c.grid (ReflectedCopies.cubicCounts D j)).liftGaugeField U) p)
      (plaquetteEnergyOf (Ψ U))
      (fun p pp hpp => (hext.2.2 U p).2.trans
        ((congrArg ((ReflectedCopies.gridPeriods c.grid
          (ReflectedCopies.cubicCounts D j)).faceEnergy U) hpp).trans (hpl U pp).1))
    show ((InfiniteLattice.smearedEnergy h _ : ℝ) : ℂ) = _
    congr 1
  · have W : CopyTwist (twoCellSide D.L j 0 * D.L ^ κ) (twoCellSide D.L j 0) k' (fun μ => k μ - c.index μ)
        (fun μ => if Even (k μ - c.index μ) then 1 else -1) :=
      { dvd := hk
        sign := fun μ => by
          by_cases h1 : Even (k μ - c.index μ)
          · exact Or.inl (if_pos h1)
          · exact Or.inr (if_neg h1)
        pow := fun μ => neg_one_pow_eq_of_dvd (even_two_mul _) (hk μ) }
    obtain ⟨-, hsur, -, hbar, hactn⟩ := hLP D (c.grid.toLatticeSym (c.grid.mover c.cell (c.grid.cell k)))
    have hb : ∀ (p : D.Plaquette) (μ : Fin 4),
        (D.imageFace (c.grid.toLatticeSym (c.grid.mover c.cell (c.grid.cell k))) p).center μ =
          (c.grid.origin μ + c.grid.cellSide * (c.index μ : ℝ) + c.grid.cellSide / 2) +
            D.mesh * ((D.L ^ κ : ℕ) : ℝ) * ((k μ - c.index μ : ℤ) : ℝ) +
            ((if Even (k μ - c.index μ) then 1 else -1 : ℤ) : ℝ) *
              (p.center μ - (c.grid.origin μ + c.grid.cellSide * (c.index μ : ℝ) + c.grid.cellSide / 2)) := by
      intro p μ
      rw [hbar p, ← hside]
      exact mover_cell_apply c.grid (hG D c.grid) c.index k p.center μ
    have := H.finsum_eq_sum W hsur hb hsup' hh'
      (fun p => InfiniteLattice.faceEnergy
        ((c.grid.toLatticeSym (c.grid.mover c.cell (c.grid.cell k))).pullbackField
          ((ReflectedCopies.gridPeriods c.grid (ReflectedCopies.cubicCounts D j)).liftGaugeField U)) p)
      (plaquetteEnergyOf (Ψ U))
      (fun p pp hpp => (hactn p _).trans ((hext.2.2 U _).2.trans
        ((congrArg ((ReflectedCopies.gridPeriods c.grid
          (ReflectedCopies.cubicCounts D j)).faceEnergy U) hpp).trans (hpl U pp).1)))
    show Conventions.signedConj _ ((InfiniteLattice.smearedEnergy h _ : ℝ) : ℂ) = _
    rw [signedConj_ofReal]
    congr 1
end YangMills.Construction.SmallTorusCopies
end
