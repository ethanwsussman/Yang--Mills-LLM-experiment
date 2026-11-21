import YangMills.Construction.HoleBesideASecondHole.DistancesBlocksAndLumpsProof
import YangMills.Construction.Lattice.DoubleBlockStraightPathCorridorAndPivotBond
import YangMills.Construction.Lattice.SiteCoordinatesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j j' : ℤ}
private structure FinerLevel (L m : ℕ) (j j' : ℤ) : Prop where
  odd : Odd L
  large : 13 ≤ L
  fine : SublatticeCoordinates L m j'
  centre : RefinedBlockAroundCentre L m j j' 1
  cover : RefinedBlocksCover L m j j' 1
  incl : sublattice L m j ≤ sublattice L m j'
  room : (L : ℤ) < halfPeriod L m j'
  halfPeriod_cast : ((halfPeriod L m j' : ℕ) : ℝ) = (L : ℝ) ^ ((m : ℤ) + j')
private def axialBond (x : Site L m j') (μ : Fin 4) (s : ℕ) : Bond L m j' :=
  Bond.forwardFrom (x + (s : ℤ) • unitStep L m j' μ) μ
private theorem two_mul_centreToFaceSteps_add_one (h : Odd L) :
    2 * centreToFaceSteps L + 1 = (L : ℤ) := by apply _root_.YangMills.Construction.LumpContours.two_mul_half_pred_add_one_of_odd <;> assumption
private theorem coe_toSublattice (y : Site L m j) (h : (y : FourTorus L m) ∈ sublattice L m j') :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.coe_toSublattice <;> assumption
private theorem zsmul_pointOnAxis (a : ℤ) (μ : Fin 4) (t : ℝ) :
    a • pointOnAxis L m μ t = pointOnAxis L m μ ((a : ℝ) * t) := by apply _root_.YangMills.SharedProofs.p34729 <;> assumption
private theorem offsetSite_offsetSite (y : Site L m j) (n n' : Fin 4 → ℤ) :
    offsetSite (offsetSite y n) n' = offsetSite y (n + n') := by
  simp only [offsetSite, Pi.add_apply, add_zsmul, Finset.sum_add_distrib, add_assoc]
private theorem add_zsmul_unitStep (y : Site L m j) (μ : Fin 4) (t : ℤ) :
    y + t • unitStep L m j μ = offsetSite y (Pi.single μ t) := by apply _root_.YangMills.SharedProofs.p86227 <;> assumption
private theorem offsetSite_of_shift {x x' : Site L m j'} {μ : Fin 4}
    (hc : x' = x + (L : ℤ) • unitStep L m j' μ) (n : Fin 4 → ℤ) :
    offsetSite x' n = offsetSite x (Pi.single μ (L : ℤ) + n) := by
  rw [hc, add_zsmul_unitStep, offsetSite_offsetSite]
private theorem single_bound (μ ν : Fin 4) {t T : ℤ} (h : |t| ≤ T) (hT : 0 ≤ T) :
    -T ≤ (Pi.single μ t : Fin 4 → ℤ) ν ∧ (Pi.single μ t : Fin 4 → ℤ) ν ≤ T := by
  by_cases e : ν = μ
  · subst e
    simpa using abs_le.1 h
  · simp only [Pi.single_eq_of_ne e]
    omega
private theorem abs_natCast_le : |(L : ℤ)| ≤ L := (abs_of_nonneg (by positivity)).le
private theorem forwardFlow_eq_map (x : Site L m j') (μ : Fin 4) (n : ℕ) :
    forwardAxisPath x μ n = (List.range n).map (axialBond x μ) := by
  induction n generalizing x with
  | zero => simp [forwardAxisPath]
  | succ n ih =>
    rw [forwardAxisPath, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · simp [axialBond]
    · refine List.map_congr_left fun s _ => ?_
      simp only [axialBond, Function.comp]
      congr 1
      push_cast
      rw [add_zsmul, one_zsmul]
      abel
private theorem axialBond_target (x : Site L m j') (μ : Fin 4) (s : ℕ) :
    (axialBond x μ s).target = x + ((s : ℤ) + 1) • unitStep L m j' μ := by
  change x + (s : ℤ) • unitStep L m j' μ + unitStep L m j' μ = _
  rw [add_zsmul, one_zsmul, add_assoc]
private theorem add_zsmul_eq_of_shift {x x' : Site L m j'} {μ : Fin 4}
    (hc : x' = x + (L : ℤ) • unitStep L m j' μ) (t : ℤ) :
    x + t • unitStep L m j' μ = x' + (t - L) • unitStep L m j' μ := by
  rw [hc, sub_zsmul]
  abel
private theorem corridor_target {x x' : Site L m j'} {μ : Fin 4} {h : ℤ}
    (hL : (L : ℤ) = h + h + 1) (hc : x' = x + (L : ℤ) • unitStep L m j' μ) (u : Fin 4 → ℤ) :
    offsetSite x u + h • unitStep L m j' μ + unitStep L m j' μ =
      offsetSite x' u - h • unitStep L m j' μ := by
  unfold offsetSite
  rw [hc, hL, add_zsmul, add_zsmul, one_zsmul]
  abel
namespace FinerLevel
private theorem coords_eq (F : FinerLevel L m j j') (y : Site L m j') {n n' : Fin 4 → ℤ}
    (h : offsetSite y n = offsetSite y n')
    (hb : ∀ ν, |n ν - n' ν| < 2 * (halfPeriod L m j' : ℤ)) : n = n' := by
  have hm := (F.fine.2.2.2.2.1 y n n').1 h
  funext ν
  have h₁ : ((2 * halfPeriod L m j' : ℕ) : ℤ) ∣ n' ν - n ν := (hm ν).dvd
  have h₂ := Int.eq_zero_of_abs_lt_dvd h₁ (by
    rw [abs_sub_comm]
    push_cast
    exact hb ν)
  omega
private theorem coordinatePoint_eq (F : FinerLevel L m j j') (y : Site L m j) (p : Fin 4 → ℤ) :
    coordinatePoint j' (y : FourTorus L m) p =
      ((offsetSite (y.toSublattice j') p : Site L m j') : FourTorus L m) := by
  have hy : ((y.toSublattice j' : Site L m j') : FourTorus L m) = y :=
    coe_toSublattice y (F.incl y.2)
  unfold coordinatePoint offsetSite
  rw [AddSubgroup.coe_add, hy, AddSubgroup.val_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [AddSubgroup.coe_zsmul, ← zsmul_pointOnAxis]
  rfl
private theorem half_iff (F : FinerLevel L m j j') (t : ℤ) :
    2 * |t| ≤ (L : ℤ) ^ 1 - 1 ↔ |t| ≤ centreToFaceSteps L := by
  have := two_mul_centreToFaceSteps_add_one F.odd
  rw [pow_one]
  omega
private theorem unitBlock_eq (F : FinerLevel L m j j') (y : Site L m j) :
    unitBlock y = {x : FourTorus L m | ∃ n : Fin 4 → ℤ, (∀ ν, |n ν| ≤ centreToFaceSteps L) ∧
      x = (offsetSite (y.toSublattice j') n : Site L m j')} := by
  rw [unitBlock, (F.centre y).1]
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, fun ν => (F.half_iff _).1 (hp ν), F.coordinatePoint_eq y p⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, fun ν => (F.half_iff _).2 (hn ν), F.coordinatePoint_eq y n⟩
private theorem mem_unitBlock (F : FinerLevel L m j j') (y : Site L m j) {n : Fin 4 → ℤ}
    (hn : ∀ ν, |n ν| ≤ centreToFaceSteps L) :
    ((offsetSite (y.toSublattice j') n : Site L m j') : FourTorus L m) ∈ unitBlock y := by
  rw [F.unitBlock_eq]
  exact ⟨n, hn, rfl⟩
private theorem near_centre (F : FinerLevel L m j j') (y : Site L m j) (μ : Fin 4) {t : ℤ}
    (ht : |t| ≤ centreToFaceSteps L) :
    ((y.toSublattice j' + t • unitStep L m j' μ : Site L m j') : FourTorus L m) ∈ unitBlock y := by
  rw [add_zsmul_unitStep]
  exact F.mem_unitBlock y fun ν => abs_le.2 (single_bound μ ν ht ((abs_nonneg t).trans ht))
private theorem no_common_site (F : FinerLevel L m j j') {x x' : Site L m j'} {μ : Fin 4}
    (hc : x' = x + (L : ℤ) • unitStep L m j' μ) {n n' : Fin 4 → ℤ}
    (hn : ∀ ν, |n ν| ≤ centreToFaceSteps L) (hn' : ∀ ν, |n' ν| ≤ centreToFaceSteps L) :
    offsetSite x n ≠ offsetSite x' n' := by
  intro h
  rw [offsetSite_of_shift hc] at h
  have hL := two_mul_centreToFaceSteps_add_one F.odd
  have hR := F.room
  have e := F.coords_eq x h (fun ν => by
    have h₁ := abs_le.1 (hn ν)
    have h₂ := abs_le.1 (hn' ν)
    have h₃ := single_bound μ ν (abs_natCast_le (L := L)) (by positivity)
    simp only [Pi.add_apply]
    exact abs_lt.2 ⟨by omega, by omega⟩)
  have e₁ := congrFun e μ
  simp only [Pi.add_apply, Pi.single_eq_same] at e₁
  have h₁ := abs_le.1 (hn μ)
  have h₂ := abs_le.1 (hn' μ)
  omega
private theorem crossing_step (F : FinerLevel L m j j') {x x' : Site L m j'} {μ : Fin 4}
    (hc : x' = x + (L : ℤ) • unitStep L m j' μ) {n n' : Fin 4 → ℤ}
    (hn : ∀ ν, |n ν| ≤ centreToFaceSteps L) (hn' : ∀ ν, |n' ν| ≤ centreToFaceSteps L)
    {ν : Fin 4} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h : offsetSite x' n' = offsetSite x n + ε • unitStep L m j' ν) :
    ν = μ ∧ ε = 1 ∧ n μ = centreToFaceSteps L := by
  rw [offsetSite_of_shift hc, add_zsmul_unitStep, offsetSite_offsetSite] at h
  have hL := two_mul_centreToFaceSteps_add_one F.odd
  have hR := F.room
  have hε' : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> simp
  have e := F.coords_eq x h (fun ρ => by
    have h₁ := abs_le.1 (hn ρ)
    have h₂ := abs_le.1 (hn' ρ)
    have h₃ := single_bound μ ρ (abs_natCast_le (L := L)) (by positivity)
    have h₄ := single_bound ν ρ hε' (by positivity)
    have := F.large
    simp only [Pi.add_apply]
    exact abs_lt.2 ⟨by omega, by omega⟩)
  have h₁ := abs_le.1 (hn μ)
  have h₂ := abs_le.1 (hn' μ)
  by_cases hν : ν = μ
  · subst hν
    have e₁ := congrFun e ν
    simp only [Pi.add_apply, Pi.single_eq_same] at e₁
    refine ⟨rfl, ?_, ?_⟩ <;> rcases hε with rfl | rfl <;> omega
  · exfalso
    have e₁ := congrFun e μ
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hν)] at e₁
    omega
private theorem unitBlocks_disjoint (F : FinerLevel L m j j') {c : Bond L m j} {μ : Fin 4}
    (hc : c.target.toSublattice j' = c.source.toSublattice j' + (L : ℤ) • unitStep L m j' μ) :
    Disjoint (unitBlock c.source) (unitBlock c.target) := by
  rw [Set.disjoint_left]
  intro p hp hq
  rw [F.unitBlock_eq] at hp hq
  obtain ⟨n, hn, rfl⟩ := hp
  obtain ⟨n', hn', h⟩ := hq
  exact F.no_common_site hc hn hn' (Subtype.ext h)
private theorem mem_source_block (F : FinerLevel L m j j') (y : Site L m j) (μ : Fin 4) {t : ℤ}
    (h₀ : 0 ≤ t) (h₁ : t ≤ centreToFaceSteps L) :
    ((y.toSublattice j' + t • unitStep L m j' μ : Site L m j') : FourTorus L m) ∈ unitBlock y :=
  F.near_centre y μ (abs_le.2 ⟨by omega, h₁⟩)
private theorem mem_target_block (F : FinerLevel L m j j') {c : Bond L m j} {μ : Fin 4}
    (hc : c.target.toSublattice j' = c.source.toSublattice j' + (L : ℤ) • unitStep L m j' μ)
    {t : ℤ} (h₀ : centreToFaceSteps L + 1 ≤ t) (h₁ : t ≤ L) :
    ((c.source.toSublattice j' + t • unitStep L m j' μ : Site L m j') : FourTorus L m) ∈
      unitBlock c.target := by
  have hL := two_mul_centreToFaceSteps_add_one F.odd
  have := F.large
  rw [add_zsmul_eq_of_shift hc t]
  exact F.near_centre c.target μ (abs_le.2 ⟨by omega, by omega⟩)
private theorem axialBond_mem_bondCorridor_iff (F : FinerLevel L m j j') {c : Bond L m j}
    {μ : Fin 4}
    (hc : c.target.toSublattice j' = c.source.toSublattice j' + (L : ℤ) • unitStep L m j' μ)
    {s : ℕ} (hs : s < L) :
    axialBond (c.source.toSublattice j') μ s ∈ (bondCorridor c : Set (Bond L m j')) ↔
      (s : ℤ) = centreToFaceSteps L := by
  have hL := two_mul_centreToFaceSteps_add_one F.odd
  have hd := Set.disjoint_left.1 (F.unitBlocks_disjoint hc)
  constructor
  · rintro ⟨h₁, h₂⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [axialBond_target] at h₂
      exact hd (F.mem_source_block c.source μ (by omega) (by omega)) h₂
    · exact hd h₁ (F.mem_target_block hc (by omega) (by omega))
  · intro h
    refine ⟨F.mem_source_block c.source μ (by omega) (by omega), ?_⟩
    rw [axialBond_target]
    exact F.mem_target_block hc (by omega) (by omega)
private theorem axialPath_eq_map (F : FinerLevel L m j j') {x x' : Site L m j'} {μ : Fin 4}
    (hc : x' = x + (L : ℤ) • unitStep L m j' μ) :
    axialPath x x' = (List.range L).map (axialBond x μ) := by
  have hR := F.room
  have hlarge := F.large
  have hwit : IsAxialDisplacement x x' μ (L : ℤ) := by
    refine ⟨by rw [hc]; abel, ?_⟩
    have h₁ : ((L : ℤ) : ℝ) < ((halfPeriod L m j' : ℤ) : ℝ) := by exact_mod_cast hR
    rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ L), ← F.halfPeriod_cast]
    simpa using h₁
  have hex : ∃ q : Fin 4 × ℤ, IsAxialDisplacement x x' q.1 q.2 := ⟨(μ, (L : ℤ)), hwit⟩
  have hq : hex.choose = (μ, (L : ℤ)) := by
    obtain ⟨h₁, h₂⟩ := hex.choose_spec
    rcases hc' : hex.choose with ⟨μ', a⟩
    rw [hc'] at h₁ h₂
    simp only at h₁ h₂
    have h₃ : |a| < (halfPeriod L m j' : ℤ) := by
      have h₄ : ((|a| : ℤ) : ℝ) < ((halfPeriod L m j' : ℤ) : ℝ) := by
        rw [Int.cast_natCast, F.halfPeriod_cast]
        exact h₂
      exact_mod_cast h₄
    have h₄ : offsetSite x (Pi.single μ (L : ℤ)) = offsetSite x (Pi.single μ' a) := by
      rw [← add_zsmul_unitStep, ← add_zsmul_unitStep, ← hc, ← h₁]
      abel
    have e := F.coords_eq x h₄ (fun ν => by
      have g₁ := single_bound μ ν (abs_natCast_le (L := L)) (by positivity)
      have g₂ := single_bound μ' ν (le_refl |a|) (abs_nonneg a)
      exact abs_lt.2 ⟨by omega, by omega⟩)
    by_cases hμ : μ' = μ
    · subst hμ
      have e₁ := congrFun e μ'
      simp only [Pi.single_eq_same] at e₁
      rw [e₁]
    · exfalso
      have e₁ := congrFun e μ
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hμ)] at e₁
      omega
  have hs : flowAlong x μ (L : ℤ) = forwardAxisPath x μ L := by simp [flowAlong]
  unfold axialPath
  rw [dif_pos hex, hq]
  change flowAlong x μ (L : ℤ) = _
  rw [hs, forwardFlow_eq_map]
private theorem pivot_eq_axialBond (F : FinerLevel L m j j') {c : Bond L m j} {μ : Fin 4}
    (hc : c.target.toSublattice j' = c.source.toSublattice j' + (L : ℤ) • unitStep L m j' μ) :
    (pivot c : Bond L m j') =
      axialBond (c.source.toSublattice j') μ (centreToFaceSteps L).toNat := by
  have hL := two_mul_centreToFaceSteps_add_one F.odd
  have hlarge := F.large
  have hpath := F.axialPath_eq_map hc
  have hw : IsPivot c (axialBond (c.source.toSublattice j') μ (centreToFaceSteps L).toNat) := by
    refine ⟨(F.axialBond_mem_bondCorridor_iff hc (by omega)).2 (by omega), ?_⟩
    rw [hpath]
    exact List.mem_map.2 ⟨_, List.mem_range.2 (by omega), rfl⟩
  have spec : IsPivot c (pivot c : Bond L m j') :=
    Classical.epsilon_spec (p := IsPivot c) ⟨_, hw⟩
  obtain ⟨h₁, h₂⟩ := spec
  rw [hpath] at h₂
  obtain ⟨s, hs, e⟩ := List.mem_map.1 h₂
  have hs' := List.mem_range.1 hs
  rw [← e] at h₁
  have h₃ := (F.axialBond_mem_bondCorridor_iff hc hs').1 h₁
  rw [← e]
  congr 1
  omega
private theorem bondCorridor_eq_set (F : FinerLevel L m j j') {c : Bond L m j} {μ : Fin 4}
    (hc : c.target.toSublattice j' = c.source.toSublattice j' + (L : ℤ) • unitStep L m j' μ) :
    (bondCorridor c : Set (Bond L m j')) =
      {b | ∃ u : Fin 4 → ℤ, u μ = 0 ∧ (∀ ν, |u ν| ≤ centreToFaceSteps L) ∧
        b = Bond.forwardFrom (offsetSite (c.source.toSublattice j') u +
          centreToFaceSteps L • unitStep L m j' μ) μ} := by
  have hL := two_mul_centreToFaceSteps_add_one F.odd
  have hlarge := F.large
  have hh : 0 ≤ centreToFaceSteps L := by omega
  ext b
  constructor
  · rintro ⟨h₁, h₂⟩
    rw [F.unitBlock_eq] at h₁ h₂
    obtain ⟨n, hn, e₁⟩ := h₁
    obtain ⟨n', hn', e₂⟩ := h₂
    have e₁' : b.source = offsetSite (c.source.toSublattice j') n := Subtype.ext e₁
    have e₂' : b.target = offsetSite (c.target.toSublattice j') n' := Subtype.ext e₂
    obtain ⟨ν, ε, hε, hd⟩ : ∃ ν : Fin 4, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        b.target = b.source + ε • unitStep L m j' ν := by
      obtain ⟨ν, h | h⟩ := b.isNeighbour
      · exact ⟨ν, 1, Or.inl rfl, by rw [one_zsmul, ← h]; abel⟩
      · exact ⟨ν, -1, Or.inr rfl, by rw [neg_one_zsmul, ← h]; abel⟩
    rw [e₂', e₁'] at hd
    obtain ⟨rfl, rfl, hμ⟩ := F.crossing_step hc hn hn' hε hd
    have hb : b = Bond.forwardFrom (offsetSite (c.source.toSublattice j') n) ν :=
      Bond.ext e₁' (by
        change b.target = offsetSite (c.source.toSublattice j') n + unitStep L m j' ν
        rw [e₂', hd, one_zsmul])
    have key : offsetSite (c.source.toSublattice j') (Function.update n ν 0) +
        centreToFaceSteps L • unitStep L m j' ν = offsetSite (c.source.toSublattice j') n := by
      rw [add_zsmul_unitStep, offsetSite_offsetSite]
      congr 1
      funext ρ
      by_cases hρ : ρ = ν
      · subst hρ
        simp [hμ]
      · simp [hρ]
    refine ⟨Function.update n ν 0, by simp, fun ρ => ?_, by rw [key]; exact hb⟩
    by_cases hρ : ρ = ν
    · subst hρ
      simpa using hh
    · simpa [hρ] using hn ρ
  · rintro ⟨u, hu, hb, rfl⟩
    have bound : ∀ t : ℤ, |t| ≤ centreToFaceSteps L → ∀ ν,
        |(u + Pi.single μ t : Fin 4 → ℤ) ν| ≤ centreToFaceSteps L := by
      intro t ht ν
      by_cases hν : ν = μ
      · subst hν
        simpa [hu] using ht
      · simpa [hν] using hb ν
    constructor
    · change ((offsetSite (c.source.toSublattice j') u + centreToFaceSteps L • unitStep L m j' μ :
        Site L m j') : FourTorus L m) ∈ unitBlock c.source
      rw [add_zsmul_unitStep, offsetSite_offsetSite]
      exact F.mem_unitBlock c.source (bound _ (by rw [abs_of_nonneg hh]))
    · change ((offsetSite (c.source.toSublattice j') u + centreToFaceSteps L • unitStep L m j' μ +
        unitStep L m j' μ : Site L m j') : FourTorus L m) ∈ unitBlock c.target
      rw [corridor_target (by omega) hc, sub_eq_add_neg, ← neg_zsmul, add_zsmul_unitStep,
        offsetSite_offsetSite]
      exact F.mem_unitBlock c.target (bound _ (by rw [abs_neg, abs_of_nonneg hh]))
private theorem bond_covered (F : FinerLevel L m j j') (b : Bond L m j') :
    ((∃ y : Site L m j, b.LiesIn (sitesInBlock j' y)) ∨
      ∃ c : Bond L m j, c.IsPositivelyOriented ∧ b ∈ (bondCorridor c : Set (Bond L m j'))) ∨
    ((∃ y : Site L m j, b.opposite.LiesIn (sitesInBlock j' y)) ∨
      ∃ c : Bond L m j, c.IsPositivelyOriented ∧
        b.opposite ∈ (bondCorridor c : Set (Bond L m j'))) := by
  obtain ⟨y', hy', -⟩ := (F.cover.1 b.source b.source.2).2
  obtain ⟨y'', hy'', -⟩ := (F.cover.1 b.target b.target.2).2
  by_cases hne : y'' = y'
  · subst hne
    exact Or.inl (Or.inl ⟨y'', hy', hy''⟩)
  have coeTarget : ∀ (ε : ℤ) (ν : Fin 4), b.target = b.source + ε • unitStep L m j' ν →
      ((b.target : Site L m j') : FourTorus L m) =
        b.source + pointOnAxis L m ν ((ε : ℝ) * meshSize L j') := by
    intro ε ν h
    rw [h, AddSubgroup.coe_add, AddSubgroup.coe_zsmul, ← zsmul_pointOnAxis]
    rfl
  obtain ⟨ν, h | h⟩ := b.isNeighbour
  · have hh := coeTarget 1 ν (by rw [one_zsmul, ← h]; abel)
    have hs := F.cover.2 b.source y' y'' 1 ν (Or.inl rfl) hy' (by rw [← hh]; exact hy'') hne
    have hd : y'' - y' = unitStep L m j ν := by
      apply Subtype.ext
      rw [AddSubgroup.coe_sub, hs, ← zsmul_pointOnAxis, one_zsmul]
      change _ = pointOnAxis L m ν (meshSize L j)
      abel
    exact Or.inl (Or.inr ⟨⟨y', y'', ν, Or.inl hd⟩, ⟨ν, hd⟩, hy', hy''⟩)
  · have hh := coeTarget (-1) ν (by rw [neg_one_zsmul, ← h]; abel)
    have hs := F.cover.2 b.source y' y'' (-1) ν (Or.inr rfl) hy' (by rw [← hh]; exact hy'') hne
    have hd : y' - y'' = unitStep L m j ν := by
      apply Subtype.ext
      rw [AddSubgroup.coe_sub, hs, ← zsmul_pointOnAxis, neg_one_zsmul]
      change _ = pointOnAxis L m ν (meshSize L j)
      abel
    exact Or.inr (Or.inr ⟨⟨y'', y', ν, Or.inl hd⟩, ⟨ν, hd⟩, hy'', hy'⟩)
end FinerLevel
theorem doubleBlockGeometryClaim_holds
    (hLat : CoordinateDescription)
    (hBlk : RefinedBlockCoordinatesHold) :
    DoubleBlockGeometryClaim := by
  intro L K m hs
  have hodd := hs.odd_factor
  have hlarge := hs.thirteen_le_factor
  have hm := hs.exponent_pos
  have hK := hs.cutoff_pos
  refine ⟨?_, fun i hi => ?_⟩
  · have h₂ : ((2 * centreToFaceSteps L + 1 : ℤ) : ℝ) = ((L : ℤ) : ℝ) := by
      rw [two_mul_centreToFaceSteps_add_one hodd]
    push_cast at h₂
    unfold YangMills.Construction.Averaging.LayerwiseParameters.halfFactor
    linarith
  · obtain ⟨hA, hU, -, -⟩ := hLat L m hodd hlarge hm
    obtain ⟨-, hLev, -⟩ := hBlk L K m hs
    obtain ⟨⟨-, hFin, hCen, hCov⟩, -⟩ := hLev i (i + 1) (by omega) (by omega)
    have e₁ : i + 1 - i = 1 := by omega
    rw [e₁] at hFin hCen hCov
    have hnn : 0 ≤ (m : ℤ) + levelDepth K i := by simp only [levelDepth]; omega
    have hexp : 2 ≤ ((m : ℤ) + levelDepth K i).toNat := by simp only [levelDepth]; omega
    have hroom : L < halfPeriod L m (levelDepth K i) := by
      unfold halfPeriod
      calc L < L ^ 2 := by nlinarith
        _ ≤ L ^ ((m : ℤ) + levelDepth K i).toNat := Nat.pow_le_pow_right (by omega) hexp
    have F : FinerLevel L m (levelDepth K (i + 1)) (levelDepth K i) :=
      { odd := hodd
        large := hlarge
        fine := hA _ (by simp only [levelDepth]; omega)
        centre := hCen
        cover := hCov
        incl := hFin.2.2.2.1
        room := by exact_mod_cast hroom
        halfPeriod_cast := by
          unfold halfPeriod
          rw [Nat.cast_pow, ← zpow_natCast, Int.toNat_of_nonneg hnn] }
    refine ⟨fun c μ hcμ => ?_, fun b => F.bond_covered b⟩
    have hc := (hU K i hK hi.le).2.2.2.2 hi c μ hcμ
    have hL := two_mul_centreToFaceSteps_add_one hodd
    exact
      { target_eq := hc
        source_block := F.unitBlock_eq c.source
        target_block := F.unitBlock_eq c.target
        blocks_disjoint := F.unitBlocks_disjoint hc
        axialPath_eq := F.axialPath_eq_map hc
        liesIn_source_block := fun s _ hs' =>
          ⟨F.mem_source_block c.source μ (by omega) (by omega), by
            have := F.mem_source_block (j' := levelDepth K i) c.source μ (t := (s : ℤ) + 1)
              (by omega) (by omega)
            change (((axialBond (c.source.toSublattice (levelDepth K i)) μ s).target :
              Site L m (levelDepth K i)) : FourTorus L m) ∈ unitBlock c.source
            rw [axialBond_target]
            exact this⟩
        liesIn_target_block := fun s hsL hs' =>
          ⟨F.mem_target_block hc (by omega) (by omega), by
            have := F.mem_target_block hc (t := (s : ℤ) + 1) (by omega) (by omega)
            change (((axialBond (c.source.toSublattice (levelDepth K i)) μ s).target :
              Site L m (levelDepth K i)) : FourTorus L m) ∈ unitBlock c.target
            rw [axialBond_target]
            exact this⟩
        mem_bondCorridor_iff := fun s hs' => F.axialBond_mem_bondCorridor_iff hc hs'
        pivot_eq := F.pivot_eq_axialBond hc
        bondCorridor_eq := F.bondCorridor_eq_set hc
        corridor_bond_target := fun u _ _ => corridor_target (by omega) hc u
        doubleBlock_bond_cover := fun b hb => by
          obtain ⟨h₁, h₂⟩ := hb
          rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
          · exact Or.inl (Or.inl ⟨h₁, h₂⟩)
          · exact Or.inl (Or.inr (Or.inr ⟨h₁, h₂⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨h₂, h₁⟩))
          · exact Or.inl (Or.inr (Or.inl ⟨h₁, h₂⟩)) }
end YangMills.Construction.PeriodicLattice
