import YangMills.Construction.Lattice.BareBaseSitesOfTheSchemesProof
import YangMills.Construction.Lattice.BlocksInTheCoordinatesOfAFinerLatticeProof
import YangMills.Construction.Lattice.BoxesOfOrderFromACorner
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.PeriodicLattice.OrderBoxes
variable {L m : ℕ} {j : ℤ}
theorem coordinatePoint_apply (s : ℤ) (y : FourTorus L m) (p : Fin 4 → ℤ) (ν : Fin 4) :
    coordinatePoint s y p ν =
      y ν + (((p ν : ℝ) * meshSize L s : ℝ) : AddCircle (torusSide L m)) := by
  simp [coordinatePoint, pointOnAxis, Finset.sum_apply, Pi.single_apply]
theorem coe_offsetSite (y : Site L m j) (n : Fin 4 → ℤ) :
    ((offsetSite y n : Site L m j) : FourTorus L m) =
      coordinatePoint j (y : FourTorus L m) n := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.coe_offsetSite <;> assumption
theorem offsetSite_apply (y : Site L m j) (n : Fin 4 → ℤ) (ν : Fin 4) :
    ((offsetSite y n : Site L m j) : FourTorus L m) ν =
      (y : FourTorus L m) ν + (((n ν : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) := by
  rw [coe_offsetSite, coordinatePoint_apply]
theorem coe_intMul_eq_iff_modEq {S a : ℝ} {N : ℤ} (ha : a ≠ 0) (hS : S = (N : ℝ) * a)
    (p q : ℤ) :
    (((p : ℝ) * a : ℝ) : AddCircle S) = (((q : ℝ) * a : ℝ) : AddCircle S) ↔ p ≡ q [ZMOD N] := by
  rw [Int.modEq_iff_dvd]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp h)
    refine ⟨c, ?_⟩
    have h1 : ((c : ℝ) * ((N : ℝ) * a)) = -((p : ℝ) * a) + (q : ℝ) * a := by
      rw [← hc, hS, zsmul_eq_mul]
    have h2 : ((q - p : ℤ) : ℝ) = ((N * c : ℤ) : ℝ) := by
      push_cast
      apply mul_right_cancel₀ ha
      linarith
    exact_mod_cast h2
  · rintro ⟨c, hc⟩
    refine QuotientAddGroup.eq.mpr (AddSubgroup.mem_zmultiples_iff.mpr ⟨c, ?_⟩)
    have h2 : ((q : ℝ) - (p : ℝ)) = (N : ℝ) * (c : ℝ) := by exact_mod_cast hc
    rw [hS, zsmul_eq_mul]
    linear_combination (-a) * h2
theorem eq_of_modEq_of_abs_sub_lt {N a b : ℤ} (h : a ≡ b [ZMOD N]) (hab : |b - a| < N) :
    a = b := by
  have := Int.eq_zero_of_abs_lt_dvd (Int.modEq_iff_dvd.mp h) hab
  omega
theorem offsetSite_eq_iff {N : ℤ} (ha : meshSize L j ≠ 0)
    (hS : torusSide L m = (N : ℝ) * meshSize L j) (y : Site L m j) (n n' : Fin 4 → ℤ) :
    offsetSite y n = offsetSite y n' ↔ ∀ μ, n μ ≡ n' μ [ZMOD N] := by
  constructor
  · intro h μ
    have h1 := congrFun (congrArg (fun x : Site L m j => (x : FourTorus L m)) h) μ
    simp only [offsetSite_apply] at h1
    exact (coe_intMul_eq_iff_modEq ha hS _ _).mp (add_left_cancel h1)
  · intro h
    refine Subtype.ext (funext fun μ => ?_)
    rw [offsetSite_apply, offsetSite_apply,
      (coe_intMul_eq_iff_modEq ha hS _ _).mpr (h μ)]
theorem offsetSite_offsetSite (y : Site L m j) (n n' : Fin 4 → ℤ) :
    offsetSite (offsetSite y n) n' = offsetSite y (n + n') := by
  simp only [offsetSite, Pi.add_apply, add_smul, Finset.sum_add_distrib, add_assoc]
theorem offsetSite_zero (y : Site L m j) : offsetSite y 0 = y := by
  simp [offsetSite]
theorem offsetSite_of_two_axes {μ ν : Fin 4} (hμν : μ ≠ ν) (y : Site L m j) (t : Fin 4 → ℤ)
    (ht : ∀ ρ, ρ ≠ μ → ρ ≠ ν → t ρ = 0) :
    offsetSite y t = y + t μ • unitStep L m j μ + t ν • unitStep L m j ν := by
  rw [offsetSite, add_assoc,
    Fintype.sum_eq_add μ ν hμν fun ρ hρ => by rw [ht ρ hρ.1 hρ.2, zero_smul]]
theorem coordCount_cornerBox {K j : ℕ} {N : ℤ} (ha : meshSize L (levelDepth K j) ≠ 0)
    (hS : torusSide L m = (N : ℝ) * meshSize L (levelDepth K j)) (hN : 3 ≤ N)
    (s : SiteAtLevel L m K j) (k : Fin 4 → ℕ) (hk : IsSmallCountVector k) (μ : Fin 4) :
    coordCount μ (cornerBox s k) = (k μ : ℕ∞) := by
  have hk' : ∀ ν, 1 ≤ k ν ∧ k ν ≤ 3 := fun ν => by
    have := hk ν
    simp only [mem_insert_iff, mem_singleton_iff] at this
    omega
  have himage : (fun x : SiteAtLevel L m K j => (x : FourTorus L m) μ) '' cornerBox s k =
      (fun c : ℤ => (s : FourTorus L m) μ + (((c : ℝ) * meshSize L (levelDepth K j) : ℝ) :
        AddCircle (torusSide L m))) '' Ico 0 (k μ : ℤ) := by
    ext x
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t μ, ⟨(ht μ).1, (ht μ).2⟩, (offsetSite_apply s t μ).symm⟩
    · rintro ⟨c, ⟨hc0, hc⟩, rfl⟩
      refine ⟨offsetSite s (Pi.single μ c), ⟨Pi.single μ c, fun ν => ?_, rfl⟩, ?_⟩
      · by_cases h : ν = μ
        · subst h
          simpa using ⟨hc0, hc⟩
        · have := (hk' ν).1
          simp only [Pi.single_eq_of_ne h]
          omega
      · simp only [offsetSite_apply, Pi.single_eq_same]
  have hinj : InjOn (fun c : ℤ => (s : FourTorus L m) μ +
      (((c : ℝ) * meshSize L (levelDepth K j) : ℝ) : AddCircle (torusSide L m)))
      (Ico 0 (k μ : ℤ)) := by
    intro c hc c' hc' h
    have h1 := (coe_intMul_eq_iff_modEq ha hS _ _).mp (add_left_cancel h)
    refine eq_of_modEq_of_abs_sub_lt h1 ?_
    have := (hk' μ).2
    have h2 := hc.1
    have h3 := hc.2
    have h4 := hc'.1
    have h5 := hc'.2
    rw [abs_lt]
    omega
  rw [coordCount, himage, hinj.encard_image]
  rw [← Finset.coe_Ico, Set.encard_coe_eq_coe_finsetCard, Int.card_Ico]
  simp
theorem cornerBox_two_axes {K j : ℕ} {μ ν : Fin 4} (hμν : μ ≠ ν) (s : SiteAtLevel L m K j)
    (a b : ℕ) :
    cornerBox s (Function.update (Function.update (fun _ => 1) μ a) ν b) =
      {x | ∃ c d : ℤ, (0 ≤ c ∧ c < a) ∧ (0 ≤ d ∧ d < b) ∧
        x = s + c • unitStep L m (levelDepth K j) μ + d • unitStep L m (levelDepth K j) ν} := by
  have hμ : Function.update (Function.update (fun _ : Fin 4 => 1) μ a) ν b μ = a := by
    rw [Function.update_of_ne hμν, Function.update_self]
  have hν : Function.update (Function.update (fun _ : Fin 4 => 1) μ a) ν b ν = b :=
    Function.update_self ..
  have hρ : ∀ ρ, ρ ≠ μ → ρ ≠ ν →
      Function.update (Function.update (fun _ : Fin 4 => 1) μ a) ν b ρ = 1 := fun ρ h1 h2 => by
    rw [Function.update_of_ne h2, Function.update_of_ne h1]
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t μ, t ν, ?_, ?_, offsetSite_of_two_axes hμν s t fun ρ h1 h2 => ?_⟩
    · simpa [hμ] using ht μ
    · simpa [hν] using ht ν
    · have := ht ρ
      simp only [hρ ρ h1 h2] at this
      omega
  · rintro ⟨c, d, hc, hd, rfl⟩
    refine ⟨Function.update (Function.update 0 μ c) ν d, fun ρ => ?_, ?_⟩
    · by_cases h2 : ρ = ν
      · subst h2
        simpa [hν] using hd
      · by_cases h1 : ρ = μ
        · subst h1
          simpa [hμ, Function.update_of_ne h2] using hc
        · simp [hρ ρ h1 h2, Function.update_of_ne h2, Function.update_of_ne h1]
    · rw [offsetSite_of_two_axes hμν s _ fun ρ h1 h2 => by
        simp [Function.update_of_ne h2, Function.update_of_ne h1]]
      simp [Function.update_of_ne hμν]
theorem isSmallCountVector_update_update {μ ν : Fin 4} (hμν : μ ≠ ν) {a b : ℕ}
    (ha : a ∈ ({1, 2, 3} : Set ℕ)) (hb : b ∈ ({1, 2, 3} : Set ℕ)) :
    IsSmallCountVector (Function.update (Function.update (fun _ => 1) μ a) ν b) := by
  intro ρ
  by_cases h2 : ρ = ν
  · subst h2
    simpa using hb
  · by_cases h1 : ρ = μ
    · subst h1
      simpa [Function.update_of_ne h2] using ha
    · simp [Function.update_of_ne h2, Function.update_of_ne h1]
theorem isCornerBox_singleton {K j : ℕ} (y : SiteAtLevel L m K j) :
    IsCornerBox ({y} : Set (SiteAtLevel L m K j)) := by
  refine ⟨y, fun _ => 1, fun _ => by simp, ?_⟩
  ext x
  constructor
  · rintro rfl
    exact ⟨0, fun μ => by simp, (offsetSite_zero x).symm⟩
  · rintro ⟨t, ht, rfl⟩
    have h0 : t = 0 := funext fun μ => by
      have := ht μ
      simp only [Nat.cast_one, Pi.zero_apply] at this ⊢
      omega
    rw [h0, offsetSite_zero]
    rfl
theorem isCornerBox_pair {K j : ℕ} (s : SiteAtLevel L m K j) (μ : Fin 4) :
    IsCornerBox ({s, s + unitStep L m (levelDepth K j) μ} : Set (SiteAtLevel L m K j)) := by
  obtain ⟨ν, hν⟩ := exists_ne μ
  refine ⟨s, Function.update (Function.update (fun _ => 1) μ 2) ν 1,
    isSmallCountVector_update_update hν.symm (by simp) (by simp), ?_⟩
  rw [cornerBox_two_axes hν.symm s 2 1]
  ext x
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, 0, by simp, by simp, by simp⟩
    · exact ⟨1, 0, by simp, by simp, by simp⟩
  · rintro ⟨c, d, hc, hd, rfl⟩
    have hd0 : d = 0 := by
      simp only [Nat.cast_one] at hd
      omega
    have hc01 : c = 0 ∨ c = 1 := by
      simp only [Nat.cast_ofNat] at hc
      omega
    rcases hc01 with rfl | rfl <;> simp [hd0]
theorem isCornerBox_bond {K j : ℕ} (b : BondAtLevel L m K j) :
    IsCornerBox ({b.source, b.target} : Set (SiteAtLevel L m K j)) := by
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · have h1 : b.target = b.source + unitStep L m (levelDepth K j) μ := by
      rw [← h]
      abel
    rw [h1]
    exact isCornerBox_pair _ μ
  · have h1 : b.source = b.target + unitStep L m (levelDepth K j) μ := by
      rw [← neg_eq_iff_eq_neg.mpr h]
      abel
    rw [pair_comm, h1]
    exact isCornerBox_pair _ μ
theorem isCornerBox_plaquette {K j : ℕ} (p : PlaquetteAtLevel L m K j) :
    IsCornerBox p.vertices := by
  have hne : p.firstAxis ≠ p.secondAxis := p.firstAxis_lt_secondAxis.ne
  refine ⟨p.origin, Function.update (Function.update (fun _ => 1) p.firstAxis 2) p.secondAxis 2,
    isSmallCountVector_update_update hne (by simp) (by simp), ?_⟩
  rw [cornerBox_two_axes hne p.origin 2 2]
  ext x
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp, by simp, by simp⟩
    · exact ⟨1, 0, by simp, by simp, by simp⟩
    · exact ⟨1, 1, by simp, by simp, by simp⟩
    · exact ⟨0, 1, by simp, by simp, by simp⟩
  · rintro ⟨c, d, hc, hd, rfl⟩
    have hc01 : c = 0 ∨ c = 1 := by
      simp only [Nat.cast_ofNat] at hc
      omega
    have hd01 : d = 0 ∨ d = 1 := by
      simp only [Nat.cast_ofNat] at hd
      omega
    rcases hc01 with rfl | rfl <;> rcases hd01 with rfl | rfl <;> simp [Plaquette.vertices]
theorem unitNeighbourhood_eq_image {K j n : ℕ} (hL : 0 < L)
    (hF : FinerLatticeAroundSite L m (levelDepth K j) (levelDepth K j) n)
    (hN : 2 ≤ (axisSiteCount L m (levelDepth K j) : ℤ)) (y : SiteAtLevel L m K j) :
    unitNeighbourhood y = offsetSite y '' {p | ∀ μ, |p μ| ≤ 1} := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hunits : ∀ v : ℝ, toLevelUnits L K j (meshSize L (levelDepth K j) * v) = v := fun v => by
    rw [toLevelUnits, meshSize, zpow_neg, mul_inv_cancel_left₀ (zpow_ne_zero _ hL')]
  have hsup := hF.2.2.2.2.1 y
  ext x
  constructor
  · intro hx
    obtain ⟨⟨p, hp, hb⟩, -, hs⟩ := hsup (x : FourTorus L m) x.2
    have hx' : toLevelUnits L K j
        (_root_.YangMills.Construction.TorusMetric.torusSupNorm ((x : FourTorus L m) - (y : FourTorus L m))) ≤ 1 := hx
    rw [hs p hp hb, hunits] at hx'
    refine ⟨p, fun μ => ?_, Subtype.ext ((coe_offsetSite y p).trans hp.symm)⟩
    have h1 : |(p μ : ℝ)| ≤ supNormVec fun μ => (p μ : ℝ) :=
      Finset.le_sup' (fun μ => |(p μ : ℝ)|) (Finset.mem_univ μ)
    have h2 : |(p μ : ℝ)| ≤ 1 := h1.trans hx'
    exact_mod_cast h2
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨-, -, hs⟩ := hsup _ (offsetSite y p).2
    have hb : ∀ μ, 2 * |p μ| ≤ (axisSiteCount L m (levelDepth K j) : ℤ) := fun μ => by
      have := hp μ
      omega
    show toLevelUnits L K j (_root_.YangMills.Construction.TorusMetric.torusSupNorm
      (((offsetSite y p : SiteAtLevel L m K j) : FourTorus L m) - (y : FourTorus L m))) ≤ 1
    rw [hs p (coe_offsetSite y p) hb, hunits]
    refine Finset.sup'_le _ _ fun μ _ => ?_
    have := hp μ
    show |(p μ : ℝ)| ≤ 1
    exact_mod_cast this
theorem unitNeighbourhood_ncard_and_isCornerBox {K j n : ℕ} {N : ℤ} (hL : 0 < L)
    (ha : meshSize L (levelDepth K j) ≠ 0)
    (hS : torusSide L m = (N : ℝ) * meshSize L (levelDepth K j)) (hN3 : 3 ≤ N)
    (hF : FinerLatticeAroundSite L m (levelDepth K j) (levelDepth K j) n)
    (hN : 2 ≤ (axisSiteCount L m (levelDepth K j) : ℤ)) (y : SiteAtLevel L m K j) :
    (unitNeighbourhood y).ncard = 3 ^ 4 ∧ IsCornerBox (unitNeighbourhood y) := by
  have heq : unitNeighbourhood y =
      cornerBox (offsetSite y fun _ => -1) fun _ => 3 := by
    rw [unitNeighbourhood_eq_image hL hF hN]
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p + 1, fun μ => ?_, ?_⟩
      · have := abs_le.mp (hp μ)
        simp only [Pi.add_apply, Pi.one_apply, Nat.cast_ofNat]
        omega
      · rw [offsetSite_offsetSite]
        congr 1
        funext μ
        simp
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(fun _ => -1) + t, fun μ => ?_, (offsetSite_offsetSite _ _ _).symm⟩
      have := ht μ
      simp only [Nat.cast_ofNat] at this
      rw [abs_le]
      simp only [Pi.add_apply]
      omega
  refine ⟨?_, _, _, fun _ => by simp, heq⟩
  have himage : cornerBox (offsetSite y fun _ => -1) (fun _ => 3) =
      offsetSite (offsetSite y fun _ => -1) ''
        ((Fintype.piFinset fun _ : Fin 4 => Finset.Ico (0 : ℤ) 3 : Finset (Fin 4 → ℤ)) :
          Set (Fin 4 → ℤ)) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t, ?_, rfl⟩
      simpa [Fintype.mem_piFinset] using ht
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t, fun μ => ?_, rfl⟩
      simpa [Fintype.mem_piFinset] using (Fintype.mem_piFinset.mp (Finset.mem_coe.mp ht)) μ
  have hinj : InjOn (offsetSite (offsetSite y fun _ => -1))
      ((Fintype.piFinset fun _ : Fin 4 => Finset.Ico (0 : ℤ) 3 : Finset (Fin 4 → ℤ)) :
        Set (Fin 4 → ℤ)) := by
    intro t ht t' ht' h
    funext μ
    have h1 := (offsetSite_eq_iff ha hS _ t t').mp h μ
    have h2 := Finset.mem_Ico.mp ((Fintype.mem_piFinset.mp (Finset.mem_coe.mp ht)) μ)
    have h3 := Finset.mem_Ico.mp ((Fintype.mem_piFinset.mp (Finset.mem_coe.mp ht')) μ)
    refine eq_of_modEq_of_abs_sub_lt h1 ?_
    rw [abs_lt]
    omega
  rw [heq, himage, hinj.ncard_image, ncard_coe_finset, Fintype.card_piFinset]
  simp
def integerSite (j : ℤ) (n : Fin 4 → ℤ) : Site L m j :=
  ⟨fun μ => (((n μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)), n, fun _ => rfl⟩
theorem offsetSite_integerSite (n t : Fin 4 → ℤ) :
    offsetSite (integerSite (L := L) (m := m) j n) t = integerSite j (n + t) := by
  refine Subtype.ext (funext fun μ => ?_)
  rw [offsetSite_apply]
  show (((n μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) + _ =
    ((((n + t) μ : ℤ) : ℝ) * meshSize L j : ℝ)
  rw [← AddCircle.coe_add]
  congr 1
  simp only [Pi.add_apply, Int.cast_add]
  ring
theorem isCornerBox_of_isOrderBox {K j : ℕ} {N : ℤ} (ha : 0 < meshSize L (levelDepth K j))
    (hS : torusSide L m = (N : ℝ) * meshSize L (levelDepth K j))
    {P : Set (SiteAtLevel L m K j)} (hP : IsOrderBox K j P) (hne : P.Nonempty) :
    IsCornerBox P := by
  obtain ⟨-, ⟨i, X, -, -, -, ⟨c, -⟩, rfl⟩, h3⟩ := hP
  set a := meshSize L (levelDepth K j) with ha_def
  let lo : Fin 4 → ℤ := fun μ => ⌈c.lower μ / a⌉
  let hi : Fin 4 → ℤ := fun μ => ⌊c.upper μ / a⌋
  have hprod : ∀ n : Fin 4 → ℤ, (∀ μ, lo μ ≤ n μ ∧ n μ ≤ hi μ) →
      (fun μ => (n μ : ℝ) * a) ∈ TorusBox.boxOfIntervals c.lower c.upper := by
    intro n hn μ _
    exact ⟨(div_le_iff₀ ha).mp (Int.ceil_le.mp (hn μ).1),
      (le_div_iff₀ ha).mp (Int.le_floor.mp (hn μ).2)⟩
  have hlift : ∀ x : SiteAtLevel L m K j, x ∈ (sitesIn X : Set (SiteAtLevel L m K j)) →
      ∃ n : Fin 4 → ℤ, (∀ μ, lo μ ≤ n μ ∧ n μ ≤ hi μ) ∧ x = integerSite _ n := by
    intro x hx
    have hxX : (x : FourTorus L m) ∈
        torusProj (torusSide L m) '' TorusBox.boxOfIntervals c.lower c.upper := by
      rw [c.image_proj]
      exact hx
    obtain ⟨v, hv, hvx⟩ := hxX
    obtain ⟨n0, hn0⟩ := x.2
    have hmul : ∀ μ, ∃ n : ℤ, v μ = (n : ℝ) * a := by
      intro μ
      have h1 : ((v μ : ℝ) : AddCircle (torusSide L m)) =
          (((n0 μ : ℝ) * a : ℝ) : AddCircle (torusSide L m)) := by
        rw [← hn0 μ, ← hvx]
        rfl
      obtain ⟨q, hq⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp h1)
      have hq' : (q : ℝ) * torusSide L m = -(v μ) + (n0 μ : ℝ) * a := by
        rw [← zsmul_eq_mul]
        exact hq
      rw [hS] at hq'
      refine ⟨n0 μ - q * N, ?_⟩
      push_cast
      linarith
    choose n hn using hmul
    refine ⟨n, fun μ => ⟨?_, ?_⟩, ?_⟩
    · exact Int.ceil_le.mpr ((div_le_iff₀ ha).mpr (by rw [← hn μ]; exact (hv μ (mem_univ μ)).1))
    · exact Int.le_floor.mpr ((le_div_iff₀ ha).mpr (by rw [← hn μ]; exact (hv μ (mem_univ μ)).2))
    · refine Subtype.ext (funext fun μ => ?_)
      rw [← hvx]
      show ((v μ : ℝ) : AddCircle (torusSide L m)) = _
      rw [hn μ]
      rfl
  have hmem : ∀ n : Fin 4 → ℤ, (∀ μ, lo μ ≤ n μ ∧ n μ ≤ hi μ) →
      (integerSite _ n : SiteAtLevel L m K j) ∈ (sitesIn X : Set (SiteAtLevel L m K j)) := by
    intro n hn
    show ((integerSite _ n : SiteAtLevel L m K j) : FourTorus L m) ∈ X
    rw [← c.image_proj]
    exact ⟨_, hprod n hn, rfl⟩
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨n0, hn0, -⟩ := hlift x0 hx0
  have hup : ∀ (μ : Fin 4) (d : ℤ), lo μ ≤ d → d ≤ hi μ →
      ∀ ν, lo ν ≤ Function.update n0 μ d ν ∧ Function.update n0 μ d ν ≤ hi ν := by
    intro μ d h1 h2 ν
    by_cases h : ν = μ
    · subst h
      simpa using ⟨h1, h2⟩
    · simpa [Function.update_of_ne h] using hn0 ν
  have hinj : ∀ μ, InjOn (fun d : ℤ => (((d : ℝ) * a : ℝ) : AddCircle (torusSide L m)))
      (Icc (lo μ) (hi μ)) := by
    intro μ d hd d' hd' h
    have h1 := c.injOn_proj (hprod _ (hup μ d hd.1 hd.2)) (hprod _ (hup μ d' hd'.1 hd'.2)) (by
      funext ν
      by_cases hν : ν = μ
      · subst hν
        simpa [torusProj] using h
      · simp [torusProj, Function.update_of_ne hν])
    have h2 := congrFun h1 μ
    simp only [Function.update_self] at h2
    exact_mod_cast mul_right_cancel₀ ha.ne' h2
  have hcount : ∀ μ, coordCount μ (sitesIn X : Set (SiteAtLevel L m K j)) =
      ((hi μ + 1 - lo μ).toNat : ℕ∞) := by
    intro μ
    have himage : (fun x : SiteAtLevel L m K j => (x : FourTorus L m) μ) ''
        (sitesIn X : Set (SiteAtLevel L m K j)) =
        (fun d : ℤ => (((d : ℝ) * a : ℝ) : AddCircle (torusSide L m))) '' Icc (lo μ) (hi μ) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨n, hn, rfl⟩ := hlift x hx
        exact ⟨n μ, hn μ, rfl⟩
      · rintro ⟨d, hd, rfl⟩
        refine ⟨_, hmem _ (hup μ d hd.1 hd.2), ?_⟩
        simp [integerSite, ha_def]
    rw [coordCount, himage, (hinj μ).encard_image, ← Finset.coe_Icc,
      Set.encard_coe_eq_coe_finsetCard, Int.card_Icc]
  have hk : ∀ μ, 1 ≤ (hi μ + 1 - lo μ).toNat ∧ (hi μ + 1 - lo μ).toNat ≤ 3 := by
    intro μ
    have h1 := h3 μ
    rw [hcount μ] at h1
    have h2 : (hi μ + 1 - lo μ).toNat ≤ 3 := by exact_mod_cast h1
    have h4 := hn0 μ
    omega
  refine ⟨integerSite _ lo, fun μ => (hi μ + 1 - lo μ).toNat, fun μ => ?_, ?_⟩
  · have := hk μ
    simp only [mem_insert_iff, mem_singleton_iff]
    omega
  · ext x
    constructor
    · intro hx
      obtain ⟨n, hn, rfl⟩ := hlift x hx
      refine ⟨n - lo, fun μ => ?_, ?_⟩
      · have := hn μ
        simp only [Pi.sub_apply]
        omega
      · rw [offsetSite_integerSite]
        simp
    · rintro ⟨t, ht, rfl⟩
      rw [offsetSite_integerSite]
      refine hmem _ fun μ => ?_
      have h2 : 0 ≤ t μ ∧ t μ < ((hi μ + 1 - lo μ).toNat : ℤ) := ht μ
      have h1 := hn0 μ
      simp only [Pi.add_apply]
      omega
theorem coe_toSublattice (hL : 0 < L) {j j' : ℤ} (h : j ≤ j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = (y : FourTorus L m) := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
theorem exists_mul_add_of_mem_blockRange {l : ℕ} {k : ℕ} (hl : Odd l) {t : ℤ}
    (ht : t ∈ blockRange l k) :
    ∃ t' r : ℤ, 0 ≤ t' ∧ t' < k ∧ 2 * |r| ≤ (l : ℤ) - 1 ∧ t = (l : ℤ) * t' + r := by
  obtain ⟨h, hh⟩ := hl
  obtain ⟨h1, h2⟩ := ht
  have hlpos : (0 : ℤ) < l := by omega
  have hmod := Int.emod_add_mul_ediv (t + h) l
  have hr0 := Int.emod_nonneg (t + h) hlpos.ne'
  have hr1 := Int.emod_lt_of_pos (t + h) hlpos
  refine ⟨(t + h) / l, (t + h) % l - h, ?_, ?_, ?_, ?_⟩
  · exact Int.ediv_nonneg (by omega) hlpos.le
  · refine Int.ediv_lt_of_lt_mul hlpos ?_
    have : ((k : ℤ) - 1) * (l : ℤ) + l = (k : ℤ) * l := by ring
    omega
  · have : |(t + h) % l - (h : ℤ)| ≤ h := abs_le.mpr ⟨by omega, by omega⟩
    omega
  · omega
theorem mul_add_mem_blockRange {l k : ℕ} {t' r : ℤ} (h0 : 0 ≤ t') (h1 : t' < k)
    (h2 : 2 * |r| ≤ (l : ℤ) - 1) : (l : ℤ) * t' + r ∈ blockRange l k := by
  have hl0 : (0 : ℤ) ≤ l := by positivity
  have hr := abs_le.mp (le_refl |r|)
  have h3 : 0 ≤ (l : ℤ) * t' := mul_nonneg hl0 h0
  have h4 : (l : ℤ) * t' ≤ ((k : ℤ) - 1) * l := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (by omega) hl0
  constructor <;> omega
theorem ncard_blockRange {l k : ℕ} (hl : Odd l) :
    (blockRange l k).ncard = (((k : ℤ) - 1) * (l : ℤ) + l).toNat := by
  obtain ⟨h, hh⟩ := hl
  have heq : blockRange l k =
      ((Finset.Icc (-(h : ℤ)) (((k : ℤ) - 1) * (l : ℤ) + h) : Finset ℤ) : Set ℤ) := by
    ext t
    simp only [blockRange, mem_ofPred_eq, Finset.coe_Icc, mem_Icc]
    omega
  rw [heq, ncard_coe_finset, Int.card_Icc]
  congr 1
  omega
theorem blockUnionAtLevel_cornerBox {K i j : ℕ} (hL : 0 < L) (hij : i ≤ j)
    (hblock : RefinedBlockAroundCentre L m (levelDepth K j) (levelDepth K i) (j - i))
    (hsp : meshSize L (levelDepth K j) = (L : ℝ) ^ (j - i) * meshSize L (levelDepth K i))
    (hodd : Odd (L ^ (j - i))) (s : SiteAtLevel L m K j) (k : Fin 4 → ℕ) :
    blockUnionAtLevel i (cornerBox s k) = sitesAsTorusPoints (cornerBlockBox i s k) := by
  have hle : levelDepth K j ≤ levelDepth K i := by
    simp only [levelDepth]
    omega
  have hcoord : ∀ (t' p : Fin 4 → ℤ),
      ((cornerOffsetSite i s (fun μ => ((L ^ (j - i) : ℕ) : ℤ) * t' μ + p μ) :
        SiteAtLevel L m K i) : FourTorus L m) =
      coordinatePoint (levelDepth K i)
        ((offsetSite s t' : SiteAtLevel L m K j) : FourTorus L m) p := by
    intro t' p
    funext ν
    rw [cornerOffsetSite, offsetSite_apply, coe_toSublattice hL hle,
      coordinatePoint_apply, offsetSite_apply, add_assoc, ← AddCircle.coe_add, hsp]
    congr 2
    push_cast
    ring
  ext x
  simp only [blockUnionAtLevel, refinedBlockUnion, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨_, ⟨t', ht', rfl⟩, hx⟩
    rw [(hblock _).1] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨_, ⟨fun μ => ((L ^ (j - i) : ℕ) : ℤ) * t' μ + p μ, fun μ _ => ?_, rfl⟩, hcoord t' p⟩
    refine mul_add_mem_blockRange (ht' μ).1 (ht' μ).2 ?_
    have := hp μ
    push_cast
    exact this
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    have hd : ∀ μ, ∃ t' r : ℤ, 0 ≤ t' ∧ t' < k μ ∧ 2 * |r| ≤ ((L ^ (j - i) : ℕ) : ℤ) - 1 ∧
        t μ = ((L ^ (j - i) : ℕ) : ℤ) * t' + r :=
      fun μ => exists_mul_add_of_mem_blockRange hodd (ht μ (mem_univ μ))
    choose t' p h0 h1 h2 h3 using hd
    refine ⟨offsetSite s t', ⟨t', fun μ => ⟨h0 μ, h1 μ⟩, rfl⟩, ?_⟩
    rw [(hblock _).1]
    refine ⟨p, fun μ => ?_, ?_⟩
    · have := h2 μ
      push_cast at this
      exact this
    · rw [← hcoord t' p]
      congr 2
      funext μ
      exact (h3 μ).symm
theorem cornerBlockBox_eq_sitesFromCorner {K i j : ℕ} {h : ℕ} (hh : L ^ (j - i) = 2 * h + 1)
    (s : SiteAtLevel L m K j) (k : Fin 4 → ℕ) :
    cornerBlockBox i s k =
      sitesFromCorner (offsetSite (s.toSublattice (levelDepth K i)) fun _ => -(h : ℤ))
        fun μ => (k μ : ℤ) * ((L ^ (j - i) : ℕ) : ℤ) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t + fun _ => (h : ℤ), fun μ => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := ht μ (mem_univ μ)
      have h3 : ((k μ : ℤ) - 1) * ((L ^ (j - i) : ℕ) : ℤ) + ((L ^ (j - i) : ℕ) : ℤ) =
          (k μ : ℤ) * ((L ^ (j - i) : ℕ) : ℤ) := by ring
      simp only [Pi.add_apply]
      omega
    · rw [offsetSite_offsetSite, cornerOffsetSite]
      congr 1
      funext μ
      simp
  · rintro ⟨t, ht, rfl⟩
    rw [offsetSite_offsetSite]
    refine ⟨_, fun μ _ => ?_, rfl⟩
    have ht' : 0 ≤ t μ ∧ t μ < (k μ : ℤ) * ((L ^ (j - i) : ℕ) : ℤ) := ht μ
    obtain ⟨h1, h2⟩ := ht'
    have h3 : ((k μ : ℤ) - 1) * ((L ^ (j - i) : ℕ) : ℤ) + ((L ^ (j - i) : ℕ) : ℤ) =
        (k μ : ℤ) * ((L ^ (j - i) : ℕ) : ℤ) := by ring
    constructor
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega
theorem orderBoxesFromCorners (hB : CornerBoxProperties)
    (hC : RefinedBlockCoordinatesHold) :
    OrderBoxesFromCorners := by
  intro L K m h j hj
  have hodd := h.odd_factor
  have h13 := h.thirteen_le_factor
  have hK := h.cutoff_pos
  have hm := h.exponent_pos
  have hL : 0 < L := by omega
  have hstd : Conventions.IsAdmissibleBlockingFactor L := ⟨hodd, h13⟩
  obtain ⟨-, hlev, -⟩ := hC L K m h
  have hpos : ∀ t : ℤ, 0 < meshSize L t := fun t => zpow_pos (by exact_mod_cast hL) _
  have hside : ∀ i, i ≤ K →
      torusSide L m = (((2 * L ^ (m + K - i) : ℕ) : ℤ) : ℝ) * meshSize L (levelDepth K i) := by
    intro i hi
    obtain ⟨hb, -, hsa, -⟩ := hlev i i le_rfl hi
    have h1 := hb.2.1.2.1
    rw [hsa] at h1
    simpa using h1
  have hlarge : ∀ i, i ≤ j → 3 * L ^ (j - i) < L ^ (m + K - i) := by
    intro i hi
    have h1 : m + K - i = (j - i) + (m + K - j) := by omega
    have h2 : L ≤ L ^ (m + K - j) := Nat.le_self_pow (by omega) L
    have h3 : 0 < L ^ (j - i) := pow_pos hL _
    rw [h1, pow_add]
    nlinarith
  have hN3 : ∀ i, i ≤ j → (3 : ℤ) ≤ ((2 * L ^ (m + K - i) : ℕ) : ℤ) := by
    intro i hi
    have := hlarge i hi
    have h3 : 0 < L ^ (j - i) := pow_pos hL _
    have h4 : 3 ≤ 2 * L ^ (m + K - i) := by nlinarith
    exact_mod_cast h4
  have hcounts : ∀ (k : Fin 4 → ℕ), IsSmallCountVector k → ∀ μ, 1 ≤ k μ ∧ k μ ≤ 3 := by
    intro k hk μ
    have := hk μ
    simp only [mem_insert_iff, mem_singleton_iff] at this
    omega
  refine ⟨fun s k hk => ?_, ?_, fun P hP hne => ?_, fun i hi s k hk => ?_⟩
  · have hbox := ((hB L m K hstd hm hK j hj).1 s (fun μ => (k μ : ℤ)) fun μ => by
      have h1 := hcounts k hk μ
      have h2 := hlarge j le_rfl
      simp only [Nat.sub_self, pow_zero, mul_one] at h2
      have h3 : (3 : ℤ) < (L : ℤ) ^ (m + K - j) := by exact_mod_cast h2
      omega).1
    have hcnt := coordCount_cornerBox (hpos _).ne' (hside j hj) (hN3 j le_rfl) s k hk
    refine ⟨⟨hj, hbox, fun μ => ?_⟩, hcnt⟩
    rw [hcnt μ]
    exact_mod_cast (hcounts k hk μ).2
  · obtain ⟨hb, -, hsa, -⟩ := hlev j j le_rfl hj
    refine ⟨isCornerBox_singleton, isCornerBox_bond, isCornerBox_plaquette, ?_⟩
    refine unitNeighbourhood_ncard_and_isCornerBox hL (hpos _).ne' (hside j hj) (hN3 j le_rfl)
      hb.2.1 ?_
    rw [hsa]
    have := hN3 j le_rfl
    push_cast at this ⊢
    omega
  · exact isCornerBox_of_isOrderBox (hpos _) (hside j hj) hP hne
  · have hiK : i ≤ K := hi.trans hj
    obtain ⟨hb, -, hsa, -, halong, -⟩ := hlev i j hi hj
    have hlodd : Odd (L ^ (j - i)) := hodd.pow
    have hk' := hcounts k hk
    have hlpos : 0 < L ^ (j - i) := pow_pos hL _
    have hl3 := hlarge i hi
    refine ⟨blockUnionAtLevel_cornerBox hL hi hb.2.2.1 hb.2.1.1 hlodd s k, ?_,
      fun μ => ⟨?_, ?_, hl3⟩, ?_, ?_⟩
    · intro t ht t' ht' heq
      funext μ
      have h1 := (offsetSite_eq_iff (hpos _).ne' (hside i hiK) _ t t').mp heq μ
      refine eq_of_modEq_of_abs_sub_lt h1 ?_
      obtain ⟨a1, a2⟩ := ht μ (mem_univ μ)
      obtain ⟨b1, b2⟩ := ht' μ (mem_univ μ)
      have h3 : ((k μ : ℤ) - 1) * ((L ^ (j - i) : ℕ) : ℤ) ≤ 2 * ((L ^ (j - i) : ℕ) : ℤ) := by
        have : (k μ : ℤ) - 1 ≤ 2 := by have := (hk' μ).2; omega
        nlinarith
      have h4 : (3 : ℤ) * ((L ^ (j - i) : ℕ) : ℤ) < ((L ^ (m + K - i) : ℕ) : ℤ) := by
        exact_mod_cast hl3
      push_cast at h3 h4 a1 a2 b1 b2 ⊢
      rw [abs_lt]
      constructor <;> omega
    · rw [ncard_blockRange hlodd]
      have h3 : ((k μ : ℤ) - 1) * ((L ^ (j - i) : ℕ) : ℤ) + ((L ^ (j - i) : ℕ) : ℤ) =
          ((k μ * L ^ (j - i) : ℕ) : ℤ) := by
        push_cast
        ring
      rw [h3, Int.toNat_natCast]
    · exact Nat.mul_le_mul_right _ (hk' μ).2
    · intro y μ
      rw [halong y μ, hsa]
    · obtain ⟨c, hc⟩ := hlodd
      rw [cornerBlockBox_eq_sitesFromCorner hc s k]
      refine ((hB L m K hstd hm hK i hiK).1 _ _ fun μ => ⟨?_, ?_⟩).1
      · have h1 : (1 : ℤ) ≤ k μ := by exact_mod_cast (hk' μ).1
        have h2 : (1 : ℤ) ≤ ((L ^ (j - i) : ℕ) : ℤ) := by exact_mod_cast hlpos
        nlinarith
      · have h1 : k μ * L ^ (j - i) < L ^ (m + K - i) := by
          have := Nat.mul_le_mul_right (L ^ (j - i)) (hk' μ).2
          omega
        exact_mod_cast h1
end YangMills.Construction.PeriodicLattice.OrderBoxes
