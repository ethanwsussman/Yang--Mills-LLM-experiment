import YangMills.Construction.Lattice.ClosedFormsWithVanishingAveragesAreDifferencesProof
import YangMills.Construction.Dirichlet.NearCentresOfCubeProof
import YangMills.Construction.Lattice.BlocksCorridorsPivotBondsAndTheWeightsOfTheOneStepAverage
import Mathlib
set_option autoImplicit false
open YangMills.Construction.GeneralTorus YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.UnitSpacingLattice.BlockAverageProof
variable {Λ : UnitSpacingLattice}
def latticeVec (Λ : UnitSpacingLattice) (k : Fin 4 → ℤ) : Λ.Point := ∑ ν, k ν • Λ.basisVec ν
theorem latticeVec_add (k k' : Fin 4 → ℤ) : latticeVec Λ (k + k') = latticeVec Λ k + latticeVec Λ k' := by
  simp [latticeVec, add_smul, Finset.sum_add_distrib]
theorem latticeVec_zero : latticeVec Λ 0 = 0 := by simp [latticeVec]
theorem latticeVec_neg (k : Fin 4 → ℤ) : latticeVec Λ (-k) = -latticeVec Λ k := by
  simp [latticeVec, Finset.sum_neg_distrib]
theorem latticeVec_sub (k k' : Fin 4 → ℤ) : latticeVec Λ (k - k') = latticeVec Λ k - latticeVec Λ k' := by
  rw [sub_eq_add_neg, latticeVec_add, latticeVec_neg, sub_eq_add_neg]
theorem latticeVec_single (μ : Fin 4) (n : ℤ) : latticeVec Λ (Pi.single μ n) = n • Λ.basisVec μ := by
  classical
  unfold latticeVec
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ν _ hν
    simp [Pi.single_eq_of_ne hν]
  · simp
def InCubeBox (h : ℕ) (k : Fin 4 → ℤ) : Prop := ∀ ν, |k ν| ≤ (h : ℤ)
structure IntCoords (Λ : UnitSpacingLattice) (h P : ℕ) : Prop where
  blockFactor_eq : Λ.blockFactor = 2 * h + 1
  period_eq : P = 0 ∨ ∃ m : ℕ, 0 < m ∧ P = 2 * m * (2 * h + 1)
  surjective : ∀ x : Λ.Point, ∃ k, x = latticeVec Λ k
  ker_iff : ∀ k, latticeVec Λ k = 0 ↔ ∀ ν, (P : ℤ) ∣ k ν
  center : ∃ y₀ : Λ.Point, ∀ x, x ∈ Λ.blockCenters ↔
    ∃ m : Fin 4 → ℤ, x = y₀ + latticeVec Λ (fun ν => (2 * (h : ℤ) + 1) * m ν)
  mem_cube_iff : ∀ x y : Λ.Point, x ∈ Λ.cube y ↔ ∃ k, InCubeBox h k ∧ x = y + latticeVec Λ k
theorem exists_centered_divmod (h : ℕ) (a : ℤ) :
    ∃ m r : ℤ, a = (2 * (h : ℤ) + 1) * m + r ∧ |r| ≤ (h : ℤ) := by
  refine ⟨(a + h) / (2 * (h : ℤ) + 1), (a + h) % (2 * (h : ℤ) + 1) - h, ?_, ?_⟩
  · have := Int.mul_ediv_add_emod (a + h) (2 * (h : ℤ) + 1)
    linarith
  · have h0 := Int.emod_nonneg (a + h) (show 2 * (h : ℤ) + 1 ≠ 0 by omega)
    have h1 := Int.emod_lt_of_pos (a + h) (show 0 < 2 * (h : ℤ) + 1 by omega)
    rw [abs_le]
    constructor <;> omega
namespace IntCoords
variable {h P : ℕ}
theorem halfWidth_eq (G : IntCoords Λ h P) : Λ.halfWidth = (h : ℝ) := by
  unfold halfWidth halfSpan
  rw [G.blockFactor_eq]
  push_cast
  ring
theorem natCast_eq_intCast (h : ℕ) : (h : ℝ) = ((h : ℤ) : ℝ) := by simp
theorem abs_le_halfWidth_iff (G : IntCoords Λ h P) (s : ℤ) :
    |(s : ℝ)| ≤ Λ.halfWidth ↔ |s| ≤ (h : ℤ) := by
  rw [G.halfWidth_eq, natCast_eq_intCast, ← Int.cast_abs, Int.cast_le]
theorem le_halfWidth_iff (G : IntCoords Λ h P) (s : ℤ) : (s : ℝ) ≤ Λ.halfWidth ↔ s ≤ (h : ℤ) := by
  rw [G.halfWidth_eq, natCast_eq_intCast, Int.cast_le]
theorem lt_halfWidth_iff (G : IntCoords Λ h P) (s : ℤ) : (s : ℝ) < Λ.halfWidth ↔ s < (h : ℤ) := by
  rw [G.halfWidth_eq, natCast_eq_intCast, Int.cast_lt]
theorem halfWidth_lt_iff (G : IntCoords Λ h P) (s : ℤ) : Λ.halfWidth < (s : ℝ) ↔ (h : ℤ) < s := by
  rw [G.halfWidth_eq, natCast_eq_intCast, Int.cast_lt]
theorem eq_halfWidth_iff (G : IntCoords Λ h P) (s : ℤ) : (s : ℝ) = Λ.halfWidth ↔ s = (h : ℤ) := by
  rw [G.halfWidth_eq, natCast_eq_intCast, Int.cast_inj]
theorem eq_zero_of_latticeVec_eq_zero (G : IntCoords Λ h P) {k : Fin 4 → ℤ} (hk : latticeVec Λ k = 0)
    (hs : ∀ ν, |k ν| < 2 * (2 * (h : ℤ) + 1)) : k = 0 := by
  funext ν
  have hd := (G.ker_iff k).1 hk ν
  rcases G.period_eq with rfl | ⟨m, hm, rfl⟩
  · simpa using hd
  · by_contra hne
    have hne' : k ν ≠ 0 := hne
    have hle := Int.le_of_dvd (abs_pos.2 hne') ((dvd_abs _ _).2 hd)
    have hs' := hs ν
    push_cast at hle
    nlinarith
theorem latticeVec_injOn (G : IntCoords Λ h P) {k k' : Fin 4 → ℤ} (hk : latticeVec Λ k = latticeVec Λ k')
    (hs : ∀ ν, |k ν - k' ν| < 2 * (2 * (h : ℤ) + 1)) : k = k' := by
  have := G.eq_zero_of_latticeVec_eq_zero (k := k - k') (by rw [latticeVec_sub, hk, sub_self]) hs
  exact sub_eq_zero.1 this
theorem dvd_of_center_add (G : IntCoords Λ h P) {y : Λ.Point} {k : Fin 4 → ℤ} (hy : y ∈ Λ.blockCenters)
    (hy' : y + latticeVec Λ k ∈ Λ.blockCenters) (ν : Fin 4) : (2 * (h : ℤ) + 1) ∣ k ν := by
  obtain ⟨y₀, hc⟩ := G.center
  obtain ⟨m, hm⟩ := (hc _).1 hy
  obtain ⟨m', hm'⟩ := (hc _).1 hy'
  have h0 : latticeVec Λ (k + (fun ν => (2 * (h : ℤ) + 1) * m ν) -
      fun ν => (2 * (h : ℤ) + 1) * m' ν) = 0 := by
    rw [latticeVec_sub, latticeVec_add]
    have : y₀ + latticeVec Λ (fun ν => (2 * (h : ℤ) + 1) * m ν) + latticeVec Λ k =
        y₀ + latticeVec Λ fun ν => (2 * (h : ℤ) + 1) * m' ν := by rw [← hm, hm']
    rw [add_right_comm] at this
    rw [sub_eq_zero]
    have h2 := congrArg (fun t => -y₀ + t) this
    simpa [add_assoc, add_comm, add_left_comm] using h2
  have hd := (G.ker_iff _).1 h0 ν
  have hL : (2 * (h : ℤ) + 1) ∣ (P : ℤ) := by
    rcases G.period_eq with rfl | ⟨m, _, rfl⟩
    · simp
    · exact ⟨2 * m, by push_cast; ring⟩
  have h3 := hL.trans hd
  simp only [Pi.sub_apply, Pi.add_apply] at h3
  have h4 : k ν = (k ν + (2 * (h : ℤ) + 1) * m ν - (2 * (h : ℤ) + 1) * m' ν) +
      (2 * (h : ℤ) + 1) * (m' ν - m ν) := by ring
  rw [h4]
  exact dvd_add h3 (dvd_mul_right _ _)
theorem center_add_mem (G : IntCoords Λ h P) {y : Λ.Point} (hy : y ∈ Λ.blockCenters) (m : Fin 4 → ℤ) :
    y + latticeVec Λ (fun ν => (2 * (h : ℤ) + 1) * m ν) ∈ Λ.blockCenters := by
  obtain ⟨y₀, hc⟩ := G.center
  obtain ⟨m₀, hm⟩ := (hc _).1 hy
  refine (hc _).2 ⟨m₀ + m, ?_⟩
  rw [hm, add_assoc, ← latticeVec_add]
  congr 2
  funext ν
  simp [mul_add]
theorem mem_cube_self (G : IntCoords Λ h P) (y : Λ.Point) : y ∈ Λ.cube y :=
  (G.mem_cube_iff _ _).2 ⟨0, fun ν => by simp, by simp [latticeVec_zero]⟩
theorem center_unique (G : IntCoords Λ h P) {x y y' : Λ.Point} (hy : y ∈ Λ.blockCenters)
    (hy' : y' ∈ Λ.blockCenters) (hx : x ∈ Λ.cube y) (hx' : x ∈ Λ.cube y') : y = y' := by
  obtain ⟨r, hr, e⟩ := (G.mem_cube_iff _ _).1 hx
  obtain ⟨r', hr', e'⟩ := (G.mem_cube_iff _ _).1 hx'
  have hyy : y' = y + latticeVec Λ (r - r') := by
    rw [latticeVec_sub]
    have : y + latticeVec Λ r = y' + latticeVec Λ r' := by rw [← e, ← e']
    rw [add_sub_assoc', this]
    abel
  have hz : r - r' = 0 := by
    funext ν
    have hd := G.dvd_of_center_add hy (hyy ▸ hy') ν
    have h1 := abs_le.1 (hr ν)
    have h2 := abs_le.1 (hr' ν)
    refine Int.eq_zero_of_abs_lt_dvd hd ?_
    rw [abs_lt]
    simp only [Pi.sub_apply]
    constructor <;> omega
  rw [hyy, hz, latticeVec_zero, add_zero]
theorem cubesPartition (G : IntCoords Λ h P) : Λ.CubesPartition := by
  obtain ⟨y₀, hc⟩ := G.center
  have hy₀ : y₀ ∈ Λ.blockCenters := (hc _).2 ⟨0, by simp; exact latticeVec_zero⟩
  refine ⟨fun y _ => ⟨y, G.mem_cube_self y⟩, fun x => ?_⟩
  obtain ⟨a, ha⟩ := G.surjective (x - y₀)
  choose m r hmr hr using fun ν => exists_centered_divmod h (a ν)
  refine ⟨y₀ + latticeVec Λ (fun ν => (2 * (h : ℤ) + 1) * m ν), ⟨G.center_add_mem hy₀ m, ?_⟩, ?_⟩
  · refine (G.mem_cube_iff _ _).2 ⟨r, hr, ?_⟩
    rw [add_assoc, ← latticeVec_add]
    have : (fun ν => (2 * (h : ℤ) + 1) * m ν) + r = a := by
      funext ν
      simp [hmr ν]
    rw [this, ← ha]
    abel
  · rintro y' ⟨hy', hx'⟩
    refine G.center_unique hy' (G.center_add_mem hy₀ m) hx' ((G.mem_cube_iff _ _).2 ⟨r, hr, ?_⟩)
    rw [add_assoc, ← latticeVec_add]
    have : (fun ν => (2 * (h : ℤ) + 1) * m ν) + r = a := by
      funext ν
      simp [hmr ν]
    rw [this, ← ha]
    abel
def longStep (h : ℕ) (μ : Fin 4) : Fin 4 → ℤ := Pi.single μ (2 * (h : ℤ) + 1)
theorem tgt_eq (G : IntCoords Λ h P) (c : Λ.CenterEdge) :
    c.tgt = c.src + latticeVec Λ (longStep h c.axis) := by
  unfold CenterEdge.tgt longStep
  rw [latticeVec_single, G.blockFactor_eq, ← natCast_zsmul]
  push_cast
  rfl
theorem tgt_mem (G : IntCoords Λ h P) (c : Λ.CenterEdge) : c.tgt ∈ Λ.blockCenters := by
  rw [G.tgt_eq]
  have := G.center_add_mem c.src_mem (Pi.single c.axis 1)
  convert this using 3
  funext ν
  by_cases hν : ν = c.axis
  · subst hν; simp [longStep]
  · simp [longStep, Pi.single_eq_of_ne hν]
theorem tgt_ne (G : IntCoords Λ h P) (c : Λ.CenterEdge) : c.tgt ≠ c.src := by
  intro e
  rw [G.tgt_eq] at e
  have h0 : latticeVec Λ (longStep h c.axis) = 0 := by simpa using e
  have hz := G.eq_zero_of_latticeVec_eq_zero h0 (fun ν => by
    by_cases hν : ν = c.axis
    · subst hν
      simp only [longStep, Pi.single_eq_same]
      rw [abs_of_nonneg (by omega)]
      omega
    · simp only [longStep, Pi.single_eq_of_ne hν, abs_zero]
      omega)
  have := congrFun hz c.axis
  simp only [longStep, Pi.single_eq_same, Pi.zero_apply] at this
  omega
theorem tgt_shiftedEdge (x : Λ.Point) (μ : Fin 4) (k : Fin 4 → ℤ) :
    (shiftedEdge x μ k).tgt = x + latticeVec Λ (k + Pi.single μ 1) := by
  rw [latticeVec_add, latticeVec_single, one_smul, ← add_assoc]
  rfl
theorem basisVec_eq (μ : Fin 4) : Λ.basisVec μ = latticeVec Λ (Pi.single μ 1) := by
  rw [latticeVec_single, one_smul]
theorem inCube_iff (G : IntCoords Λ h P) {y : Λ.Point} {b : Λ.Edge} {μ : Fin 4} (hb : b.axis = μ) :
    b.InCube y ↔ ∃ r, InCubeBox h r ∧ r μ < h ∧ b = shiftedEdge y μ r := by
  constructor
  · rintro ⟨ht, hh⟩
    obtain ⟨r, hr, e⟩ := (G.mem_cube_iff _ _).1 ht
    obtain ⟨r', hr', e'⟩ := (G.mem_cube_iff _ _).1 hh
    have hv : latticeVec Λ (r + Pi.single μ 1) = latticeVec Λ r' := by
      have h1 : b.tgt = b.src + Λ.basisVec μ := by rw [← hb]; rfl
      rw [e, e', basisVec_eq, add_assoc, ← latticeVec_add] at h1
      exact (add_left_cancel h1).symm
    have hk := G.latticeVec_injOn hv (fun ν => by
      have h1 := abs_le.1 (hr ν)
      have h2 := abs_le.1 (hr' ν)
      by_cases hν : ν = μ
      · subst hν
        simp only [Pi.add_apply, Pi.single_eq_same]
        rw [abs_lt]
        constructor <;> omega
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hν]
        rw [abs_lt]
        constructor <;> omega)
    refine ⟨r, hr, ?_, Edge.ext e hb⟩
    have h3 := congrFun hk μ
    simp only [Pi.add_apply, Pi.single_eq_same] at h3
    have := abs_le.1 (hr' μ)
    omega
  · rintro ⟨r, hr, hlt, rfl⟩
    refine ⟨(G.mem_cube_iff _ _).2 ⟨r, hr, rfl⟩, (G.mem_cube_iff _ _).2 ⟨r + Pi.single μ 1, fun ν => ?_, ?_⟩⟩
    · have h1 := abs_le.1 (hr ν)
      rw [abs_le]
      by_cases hν : ν = μ
      · subst hν
        simp only [Pi.add_apply, Pi.single_eq_same]
        constructor <;> omega
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hν]
        constructor <;> omega
    · exact tgt_shiftedEdge y μ r
theorem mem_edgeCorridor_iff (G : IntCoords Λ h P) (c : Λ.CenterEdge) (b : Λ.Edge) :
    b ∈ edgeCorridor c ↔ b.axis = c.axis ∧
      ∃ r, InCubeBox h r ∧ r c.axis = h ∧ b = shiftedEdge c.src c.axis r := by
  constructor
  · rintro ⟨ht, hh⟩
    obtain ⟨r, hr, e⟩ := (G.mem_cube_iff _ _).1 ht
    obtain ⟨r', hr', e'⟩ := (G.mem_cube_iff _ _).1 hh
    have hv : latticeVec Λ (r + Pi.single b.axis 1) =
        latticeVec Λ (longStep h c.axis + r') := by
      have h1 : b.tgt = b.src + Λ.basisVec b.axis := rfl
      rw [e, e', G.tgt_eq, basisVec_eq, add_assoc, ← latticeVec_add, add_assoc, ← latticeVec_add] at h1
      exact (add_left_cancel h1).symm
    have hsub : latticeVec Λ (longStep h c.axis + r' - r - Pi.single b.axis 1) = 0 := by
      rw [sub_sub, latticeVec_sub, hv.symm, sub_self]
    have hμ := abs_le.1 (hr c.axis)
    have hμ' := abs_le.1 (hr' c.axis)
    have hdir : b.axis = c.axis := by
      by_contra hne
      have hz := G.eq_zero_of_latticeVec_eq_zero hsub (fun ν => by
        have h1 := abs_le.1 (hr ν)
        have h2 := abs_le.1 (hr' ν)
        rw [abs_lt]
        simp only [Pi.sub_apply, Pi.add_apply, longStep, Pi.single_apply]
        split_ifs <;> constructor <;> omega)
      have := congrFun hz c.axis
      simp only [Pi.sub_apply, Pi.add_apply, longStep, Pi.single_eq_same, Pi.zero_apply,
        Pi.single_eq_of_ne (Ne.symm hne)] at this
      omega
    have hz := G.eq_zero_of_latticeVec_eq_zero hsub (fun ν => by
      have h1 := abs_le.1 (hr ν)
      have h2 := abs_le.1 (hr' ν)
      rw [abs_lt]
      simp only [Pi.sub_apply, Pi.add_apply, longStep, Pi.single_apply, hdir]
      split_ifs <;> constructor <;> omega)
    have h3 := congrFun hz c.axis
    simp only [Pi.sub_apply, Pi.add_apply, longStep, Pi.single_eq_same, Pi.zero_apply, hdir] at h3
    refine ⟨hdir, r, hr, ?_, Edge.ext e hdir⟩
    omega
  · rintro ⟨-, r, hr, hh, rfl⟩
    refine ⟨(G.mem_cube_iff _ _).2 ⟨r, hr, rfl⟩, (G.mem_cube_iff _ _).2
      ⟨r + Pi.single c.axis 1 - longStep h c.axis, fun ν => ?_, ?_⟩⟩
    · have h1 := abs_le.1 (hr ν)
      rw [abs_le]
      by_cases hν : ν = c.axis
      · subst hν
        simp only [Pi.sub_apply, Pi.add_apply, longStep, Pi.single_eq_same]
        constructor <;> omega
      · simp only [Pi.sub_apply, Pi.add_apply, longStep, Pi.single_eq_of_ne hν]
        constructor <;> omega
    · rw [tgt_shiftedEdge, G.tgt_eq, add_assoc, ← latticeVec_add]
      congr 2
      abel
theorem edgesFromACube (G : IntCoords Λ h P) : Λ.EdgesFromACube := by
  intro y hy k hk ν
  have hk' : InCubeBox h k := fun ρ => (G.abs_le_halfWidth_iff _).1 (hk ρ)
  have hst : (shiftedEdge y ν k).src ∈ Λ.cube y := (G.mem_cube_iff _ _).2 ⟨k, hk', rfl⟩
  refine ⟨fun hlt => ?_, fun heq => ?_⟩
  · have hlt' : k ν < h := (G.lt_halfWidth_iff _).1 hlt
    have hin : (shiftedEdge y ν k).InCube y := (G.inCube_iff rfl).2 ⟨k, hk', hlt', rfl⟩
    refine ⟨hin, fun y' hy' hne hi => hne (G.center_unique hy' hy hi.1 hst), fun c hc => ?_⟩
    have h1 : c.src = y := G.center_unique c.src_mem hy hc.1 hst
    have h2 : c.tgt = y := G.center_unique (G.tgt_mem c) hy hc.2 hin.2
    exact G.tgt_ne c (h2.trans h1.symm)
  · have heq' : k ν = h := (G.eq_halfWidth_iff _).1 heq
    have hc0 : shiftedEdge y ν k ∈ edgeCorridor (⟨y, hy, ν⟩ : Λ.CenterEdge) :=
      (G.mem_edgeCorridor_iff _ _).2 ⟨rfl, k, hk', heq', rfl⟩
    refine ⟨fun y' hy' hi => ?_, hc0, fun c hc => ?_⟩
    · have h1 : y' = y := G.center_unique hy' hy hi.1 hst
      have h2 : y' = (⟨y, hy, ν⟩ : Λ.CenterEdge).tgt :=
        G.center_unique hy' (G.tgt_mem _) hi.2 hc0.2
      exact G.tgt_ne ⟨y, hy, ν⟩ (h2.symm.trans h1)
    · have h1 : c.src = y := G.center_unique c.src_mem hy hc.1 hst
      have h2 := ((G.mem_edgeCorridor_iff _ _).1 hc).1
      exact CenterEdge.ext h1 h2.symm
theorem isAverageIndex_iff (G : IntCoords Λ h P) (μ : Fin 4) (k : Fin 4 → ℤ) :
    Λ.IsAverageIndex μ k ↔
      -(h : ℤ) ≤ k μ ∧ k μ ≤ 3 * h ∧ ∀ ν, ν ≠ μ → |k ν| ≤ (h : ℤ) := by
  unfold IsAverageIndex
  rw [G.halfWidth_eq]
  have h1 : -(h : ℝ) ≤ (k μ : ℝ) ↔ -(h : ℤ) ≤ k μ := by
    rw [natCast_eq_intCast, ← Int.cast_neg, Int.cast_le]
  have h2 : (k μ : ℝ) ≤ 3 * (h : ℝ) ↔ k μ ≤ 3 * h := by
    have e : 3 * (h : ℝ) = ((3 * (h : ℤ) : ℤ) : ℝ) := by push_cast; ring
    rw [e, Int.cast_le]
  have h3 : ∀ ν, |(k ν : ℝ)| ≤ (h : ℝ) ↔ |k ν| ≤ (h : ℤ) := fun ν => by
    rw [natCast_eq_intCast, ← Int.cast_abs, Int.cast_le]
  simp only [h1, h2, h3]
theorem memBondWindow_iff (G : IntCoords Λ h P) (μ : Fin 4) (k : Fin 4 → ℤ) :
    MemBondWindow Λ.blockFactor μ k ↔
      -(h : ℤ) ≤ k μ ∧ k μ ≤ 3 * h + 1 ∧ ∀ ν, ν ≠ μ → |k ν| ≤ (h : ℤ) := by
  unfold MemBondWindow
  have hw : halfSpan Λ.blockFactor = (h : ℝ) := G.halfWidth_eq
  rw [hw]
  have h1 : -(h : ℝ) ≤ (k μ : ℝ) ↔ -(h : ℤ) ≤ k μ := by
    rw [natCast_eq_intCast, ← Int.cast_neg, Int.cast_le]
  have h2 : (k μ : ℝ) ≤ 3 * (h : ℝ) + 1 ↔ k μ ≤ 3 * h + 1 := by
    have e : 3 * (h : ℝ) + 1 = ((3 * (h : ℤ) + 1 : ℤ) : ℝ) := by push_cast; ring
    rw [e, Int.cast_le]
  have h3 : ∀ ν, |(k ν : ℝ)| ≤ (h : ℝ) ↔ |k ν| ≤ (h : ℤ) := fun ν => by
    rw [natCast_eq_intCast, ← Int.cast_abs, Int.cast_le]
  simp only [h1, h2, h3]
theorem pointsOfTheTwoCubes (G : IntCoords Λ h P) (c : Λ.CenterEdge) : PointsOfTheTwoCubes c := by
  have hbox : ∀ {k : Fin 4 → ℤ}, MemBondWindow Λ.blockFactor c.axis k →
      -(h : ℤ) ≤ k c.axis ∧ k c.axis ≤ 3 * h + 1 ∧
        ∀ ν, ν ≠ c.axis → |k ν| ≤ (h : ℤ) := fun hk => (G.memBondWindow_iff _ _).1 hk
  refine ⟨?_, ?_, ?_⟩
  · intro k hk k' hk' e
    have hk1 := hbox hk
    have hk2 := hbox hk'
    have hv : latticeVec Λ k = latticeVec Λ k' := add_left_cancel (a := c.src) e
    refine G.latticeVec_injOn hv (fun ν => ?_)
    by_cases hν : ν = c.axis
    · subst hν
      rw [abs_lt]
      constructor <;> omega
    · have h1 := abs_le.1 (hk1.2.2 ν hν)
      have h2 := abs_le.1 (hk2.2.2 ν hν)
      rw [abs_lt]
      constructor <;> omega
  · ext x
    constructor
    · rintro ⟨k, ⟨hk, hle⟩, rfl⟩
      have hk1 := hbox hk
      refine (G.mem_cube_iff _ _).2 ⟨k, fun ν => ?_, rfl⟩
      by_cases hν : ν = c.axis
      · subst hν
        rw [abs_le]
        exact ⟨hk1.1, (G.le_halfWidth_iff _).1 hle⟩
      · exact hk1.2.2 ν hν
    · intro hx
      obtain ⟨r, hr, rfl⟩ := (G.mem_cube_iff _ _).1 hx
      have hμ := abs_le.1 (hr c.axis)
      refine ⟨r, ⟨(G.memBondWindow_iff _ _).2 ⟨hμ.1, by omega, fun ν _ => hr ν⟩,
        (G.le_halfWidth_iff _).2 hμ.2⟩, rfl⟩
  · ext x
    constructor
    · rintro ⟨k, ⟨hk, hlt⟩, rfl⟩
      have hk1 := hbox hk
      have hlt' : (h : ℤ) < k c.axis := (G.halfWidth_lt_iff _).1 hlt
      refine (G.mem_cube_iff _ _).2 ⟨k - longStep h c.axis, fun ν => ?_, ?_⟩
      · by_cases hν : ν = c.axis
        · subst hν
          simp only [Pi.sub_apply, longStep, Pi.single_eq_same]
          rw [abs_le]
          constructor <;> omega
        · simp only [Pi.sub_apply, longStep, Pi.single_eq_of_ne hν, sub_zero]
          exact hk1.2.2 ν hν
      · rw [G.tgt_eq, add_assoc, ← latticeVec_add]
        show c.src + latticeVec Λ k = _
        congr 2
        abel
    · intro hx
      obtain ⟨r, hr, rfl⟩ := (G.mem_cube_iff _ _).1 hx
      have hμ := abs_le.1 (hr c.axis)
      refine ⟨r + longStep h c.axis, ⟨(G.memBondWindow_iff _ _).2 ⟨?_, ?_, fun ν hν => ?_⟩,
        (G.halfWidth_lt_iff _).2 ?_⟩, ?_⟩
      · simp only [Pi.add_apply, longStep, Pi.single_eq_same]; omega
      · simp only [Pi.add_apply, longStep, Pi.single_eq_same]; omega
      · simpa only [Pi.add_apply, longStep, Pi.single_eq_of_ne hν, add_zero] using hr ν
      · simp only [Pi.add_apply, longStep, Pi.single_eq_same]; omega
      · rw [G.tgt_eq, add_assoc, ← latticeVec_add]
        show c.src + latticeVec Λ _ = _
        congr 2
        abel
theorem shiftedEdge_injOn (G : IntCoords Λ h P) (c : Λ.CenterEdge) {k k' : Fin 4 → ℤ}
    (hk : Λ.IsAverageIndex c.axis k) (hk' : Λ.IsAverageIndex c.axis k')
    (e : shiftedEdge c.src c.axis k = shiftedEdge c.src c.axis k') : k = k' := by
  have h1 := (G.isAverageIndex_iff _ _).1 hk
  have h2 := (G.isAverageIndex_iff _ _).1 hk'
  have hv : latticeVec Λ k = latticeVec Λ k' := add_left_cancel (a := c.src) (congrArg Edge.src e)
  refine G.latticeVec_injOn hv (fun ν => ?_)
  by_cases hν : ν = c.axis
  · subst hν
    rw [abs_lt]
    constructor <;> omega
  · have h3 := abs_le.1 (h1.2.2 ν hν)
    have h4 := abs_le.1 (h2.2.2 ν hν)
    rw [abs_lt]
    constructor <;> omega
theorem exists_blockAverageWeight (G : IntCoords Λ h P) (c : Λ.CenterEdge) :
    ∃ q, IsBlockAverageWeight c q := by
  classical
  refine ⟨fun b => if hb : ∃ k, Λ.IsAverageIndex c.axis k ∧
      b = shiftedEdge c.src c.axis k then
    (Λ.blockFactor : ℝ) ^ (-4 - 1 : ℤ) *
      (tentMultiplicity Λ.blockFactor (hb.choose c.axis) : ℝ) else 0, ?_, ?_⟩
  · intro k hk
    have hb : ∃ k', Λ.IsAverageIndex c.axis k' ∧
        shiftedEdge c.src c.axis k = shiftedEdge c.src c.axis k' := ⟨k, hk, rfl⟩
    have hc := G.shiftedEdge_injOn c hb.choose_spec.1 hk hb.choose_spec.2.symm
    simp only [dif_pos hb, hc]
  · intro b hb
    simp only [dif_neg hb]
theorem blockAverageWeight_spec (G : IntCoords Λ h P) (c : Λ.CenterEdge) :
    IsBlockAverageWeight c (blockAverageWeight c) :=
  Classical.epsilon_spec (G.exists_blockAverageWeight c)
theorem neg_halfWidth_le_iff (G : IntCoords Λ h P) (s : ℤ) : -Λ.halfWidth ≤ (s : ℝ) ↔ -(h : ℤ) ≤ s := by
  rw [G.halfWidth_eq, natCast_eq_intCast, ← Int.cast_neg, Int.cast_le]
theorem abs_sub_le_halfSpan_iff (h : ℕ) (s : ℤ) (i : ℕ) :
    |(s : ℝ) - (i : ℝ)| ≤ halfSpan (2 * h + 1) ↔ |s - (i : ℤ)| ≤ (h : ℤ) := by
  have hw : halfSpan (2 * h + 1) = (h : ℝ) := by
    unfold halfSpan
    push_cast
    ring
  have e : |(s : ℝ) - (i : ℝ)| = ((|s - (i : ℤ)| : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [hw, e, natCast_eq_intCast, Int.cast_le]
theorem tentMultiplicity_eq (h : ℕ) (s : ℤ) :
    (tentMultiplicity (2 * h + 1) s : ℤ) = (min (2 * (h : ℤ)) (s + h) + 1 - max 0 (s - h)).toNat := by
  classical
  have hc : tentMultiplicity (2 * h + 1) s =
      (Finset.Icc (max 0 (s - h)) (min (2 * (h : ℤ)) (s + h))).card := by
    unfold tentMultiplicity
    refine Finset.card_bij (fun i _ => (i : ℤ)) ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter, Finset.mem_range, abs_sub_le_halfSpan_iff, abs_le] at hi
      rw [Finset.mem_Icc]
      omega
    · intro i _ j _ e
      exact_mod_cast e
    · intro t ht
      rw [Finset.mem_Icc] at ht
      refine ⟨t.toNat, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_range, abs_sub_le_halfSpan_iff, abs_le]
        omega
      · omega
  rw [hc, Int.card_Icc]
theorem tentMultiplicity_pos (h : ℕ) {s : ℤ} (h1 : -(h : ℤ) ≤ s) (h2 : s ≤ 3 * h) :
    0 < tentMultiplicity (2 * h + 1) s := by
  have := tentMultiplicity_eq h s
  omega
theorem tentMultiplicity_le (N : ℕ) (s : ℤ) : tentMultiplicity N s ≤ N := by
  classical
  unfold tentMultiplicity
  exact (Finset.card_filter_le _ _).trans (by simp)
theorem tentMultiplicityValues (G : IntCoords Λ h P) : Λ.TentMultiplicityValues := by
  have hL := G.blockFactor_eq
  have hcast : (Λ.blockFactor : ℝ) = 2 * (h : ℝ) + 1 := by
    rw [hL]
    push_cast
    rfl
  have key : ∀ s : ℤ, (tentMultiplicity Λ.blockFactor s : ℤ) =
      (min (2 * (h : ℤ)) (s + h) + 1 - max 0 (s - h)).toNat := fun s => by
    rw [hL]
    exact tentMultiplicity_eq h s
  refine ⟨fun s h1 h2 => ?_, fun s h1 => ?_, fun s h1 h2 => ?_⟩
  · have h1' := (G.neg_halfWidth_le_iff s).1 h1
    have h2' := (G.lt_halfWidth_iff s).1 h2
    have hv : (tentMultiplicity Λ.blockFactor s : ℤ) = s + h + 1 := by
      have := key s
      omega
    have hr : (tentMultiplicity Λ.blockFactor s : ℝ) = (s : ℝ) + (h : ℝ) + 1 := by
      exact_mod_cast hv
    rw [hr, G.halfWidth_eq, hcast]
    refine ⟨rfl, ?_, ?_⟩
    · have : (1 : ℤ) ≤ s + h + 1 := by omega
      exact_mod_cast this
    · have : s + h + 1 ≤ 2 * (h : ℤ) := by omega
      have h3 : (s : ℝ) + (h : ℝ) + 1 ≤ 2 * (h : ℝ) := by exact_mod_cast this
      linarith
  · have h1' := (G.eq_halfWidth_iff s).1 h1
    have := key s
    omega
  · have h1' := (G.halfWidth_lt_iff s).1 h1
    have h2' : s ≤ 3 * (h : ℤ) := by
      rw [G.halfWidth_eq] at h2
      have : (s : ℝ) ≤ ((3 * (h : ℤ) : ℤ) : ℝ) := by
        push_cast
        exact h2
      exact_mod_cast this
    have hv : (tentMultiplicity Λ.blockFactor s : ℤ) = 3 * h + 1 - s := by
      have := key s
      omega
    have hr : (tentMultiplicity Λ.blockFactor s : ℝ) = 3 * (h : ℝ) + 1 - (s : ℝ) := by
      exact_mod_cast hv
    rw [hr, G.halfWidth_eq, hcast]
    refine ⟨rfl, ?_, ?_⟩
    · have : (1 : ℤ) ≤ 3 * h + 1 - s := by omega
      exact_mod_cast this
    · have : 3 * (h : ℤ) + 1 - s ≤ 2 * (h : ℤ) := by omega
      have h3 : 3 * (h : ℝ) + 1 - (s : ℝ) ≤ 2 * (h : ℝ) := by exact_mod_cast this
      linarith
def boxFinset (h : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(h : ℤ)) h
def indexFinset (h : ℕ) (μ : Fin 4) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun ν => if ν = μ then Finset.Icc (-(h : ℤ)) (3 * h) else Finset.Icc (-(h : ℤ)) h
theorem mem_boxFinset {k : Fin 4 → ℤ} : k ∈ boxFinset h ↔ InCubeBox h k := by
  simp [boxFinset, Fintype.mem_piFinset, InCubeBox, _root_.abs_le]
theorem mem_indexFinset {μ : Fin 4} {k : Fin 4 → ℤ} :
    k ∈ indexFinset h μ ↔ -(h : ℤ) ≤ k μ ∧ k μ ≤ 3 * h ∧ ∀ ν, ν ≠ μ → |k ν| ≤ (h : ℤ) := by
  simp only [indexFinset, Fintype.mem_piFinset]
  constructor
  · intro H
    have h1 := H μ
    simp only [if_true, Finset.mem_Icc] at h1
    refine ⟨h1.1, h1.2, fun ν hν => ?_⟩
    have h2 := H ν
    simp only [if_neg hν, Finset.mem_Icc] at h2
    exact _root_.abs_le.2 h2
  · rintro ⟨a, b, c⟩ ν
    by_cases hν : ν = μ
    · subst hν
      simp only [if_true, Finset.mem_Icc]
      exact ⟨a, b⟩
    · simp only [if_neg hν, Finset.mem_Icc]
      exact _root_.abs_le.1 (c ν hν)
theorem card_boxFinset : (boxFinset h).card = (2 * h + 1) ^ 4 := by apply _root_.YangMills.Construction.PeriodicLattice.VanishingAverageGradients.card_cubeBox <;> assumption
theorem card_indexFinset (μ : Fin 4) : (indexFinset h μ).card = (4 * h + 1) * (2 * h + 1) ^ 3 := by
  have h1 : ((Finset.Icc (-(h : ℤ)) h).card) = 2 * h + 1 := by
    rw [Int.card_Icc]
    omega
  have h2 : ((Finset.Icc (-(h : ℤ)) (3 * h)).card) = 4 * h + 1 := by
    rw [Int.card_Icc]
    omega
  have h3 : ∀ ν, (if ν = μ then Finset.Icc (-(h : ℤ)) (3 * h)
      else Finset.Icc (-(h : ℤ)) h).card = if ν = μ then 4 * h + 1 else 2 * h + 1 := fun ν => by
    split_ifs <;> assumption
  unfold indexFinset
  rw [Fintype.card_piFinset]
  simp only [h3]
  fin_cases μ <;> simp [Fin.prod_univ_four] <;> ring
theorem sum_sum_eq_sum_tentMultiplicity (h : ℕ) (μ : Fin 4) (g : (Fin 4 → ℤ) → ℝ) :
    ∑ k ∈ boxFinset h, ∑ i ∈ Finset.range (2 * h + 1), g (k + Pi.single μ (i : ℤ)) =
      ∑ k ∈ indexFinset h μ, (tentMultiplicity (2 * h + 1) (k μ) : ℝ) * g k := by
  classical
  have hτ : ∀ s : ℤ, (tentMultiplicity (2 * h + 1) s : ℝ) =
      ∑ i ∈ Finset.range (2 * h + 1), if |s - (i : ℤ)| ≤ (h : ℤ) then (1 : ℝ) else 0 := by
    intro s
    unfold tentMultiplicity
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [abs_sub_le_halfSpan_iff]
  simp_rw [hτ, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_comm (s := indexFinset h μ)]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hi' : (i : ℤ) ≤ 2 * h := by
    have := Finset.mem_range.1 hi
    omega
  refine Finset.sum_nbij' (· + Pi.single μ (i : ℤ)) (· - Pi.single μ (i : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    have hb := mem_boxFinset.1 hk
    have hμ := _root_.abs_le.1 (hb μ)
    rw [Finset.mem_filter, mem_indexFinset]
    simp only [Pi.add_apply, Pi.single_eq_same]
    refine ⟨⟨by omega, by omega, fun ν hν => ?_⟩, ?_⟩
    · simpa only [Pi.single_eq_of_ne hν, add_zero] using hb ν
    · rw [_root_.abs_le]
      constructor <;> omega
  · intro k hk
    rw [Finset.mem_filter, mem_indexFinset] at hk
    obtain ⟨⟨-, -, hν⟩, hab⟩ := hk
    refine mem_boxFinset.2 fun ν => ?_
    by_cases e : ν = μ
    · subst e
      simp only [Pi.sub_apply, Pi.single_eq_same]
      exact hab
    · simpa only [Pi.sub_apply, Pi.single_eq_of_ne e, sub_zero] using hν ν e
  · intro k _
    simp
  · intro k _
    simp
  · intro k _
    rfl
theorem finsum_cube_eq (G : IntCoords Λ h P) (y : Λ.Point) (f : Λ.Point → ℝ) :
    ∑ᶠ x ∈ Λ.cube y, f x = ∑ k ∈ boxFinset h, f (y + latticeVec Λ k) := by
  have himg : Λ.cube y = (fun k => y + latticeVec Λ k) '' (↑(boxFinset h) : Set (Fin 4 → ℤ)) := by
    ext x
    rw [G.mem_cube_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, mem_boxFinset.2 hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, mem_boxFinset.1 hk, rfl⟩
  have hinj : Set.InjOn (fun k => y + latticeVec Λ k) (↑(boxFinset h) : Set (Fin 4 → ℤ)) := by
    intro k hk k' hk' e
    refine G.latticeVec_injOn (add_left_cancel e) (fun ν => ?_)
    have h1 := _root_.abs_le.1 (mem_boxFinset.1 hk ν)
    have h2 := _root_.abs_le.1 (mem_boxFinset.1 hk' ν)
    rw [abs_lt]
    constructor <;> omega
  rw [himg, finsum_mem_image hinj, finsum_mem_coe_finset]
theorem blockAverage_eq_sum (G : IntCoords Λ h P) (B : Λ.Edge → ℝ) (c : Λ.CenterEdge) :
    blockAverage B c = (Λ.blockFactor : ℝ) ^ (-4 - 1 : ℤ) *
      ∑ k ∈ indexFinset h c.axis, (tentMultiplicity Λ.blockFactor (k c.axis) : ℝ) *
        B (shiftedEdge c.src c.axis k) := by
  unfold blockAverage
  rw [G.finsum_cube_eq]
  congr 1
  have hr := sum_sum_eq_sum_tentMultiplicity h c.axis fun k => B (shiftedEdge c.src c.axis k)
  rw [G.blockFactor_eq, ← hr]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Edge.ext ?_ rfl
  show c.src + latticeVec Λ k + i • Λ.basisVec c.axis =
    c.src + latticeVec Λ (k + Pi.single c.axis (i : ℤ))
  rw [latticeVec_add, latticeVec_single, natCast_zsmul, add_assoc]
theorem isAverageIndex_of_mem (G : IntCoords Λ h P) (c : Λ.CenterEdge) {k : Fin 4 → ℤ}
    (hk : k ∈ indexFinset h c.axis) : Λ.IsAverageIndex c.axis k :=
  (G.isAverageIndex_iff _ _).2 (mem_indexFinset.1 hk)
theorem finsum_weight_mul (G : IntCoords Λ h P) (c : Λ.CenterEdge) (F : Λ.Edge → ℝ) :
    ∑ᶠ b, blockAverageWeight c b * F b =
      ∑ k ∈ indexFinset h c.axis, (Λ.blockFactor : ℝ) ^ (-4 - 1 : ℤ) *
        (tentMultiplicity Λ.blockFactor (k c.axis) : ℝ) *
          F (shiftedEdge c.src c.axis k) := by
  classical
  have hs := G.blockAverageWeight_spec c
  have hsub : Function.support (fun b => blockAverageWeight c b * F b) ⊆
      ↑((indexFinset h c.axis).image (shiftedEdge c.src c.axis)) := by
    intro b hb
    by_contra hn
    apply hb
    have hno : ¬∃ k, Λ.IsAverageIndex c.axis k ∧ b = shiftedEdge c.src c.axis k := by
      rintro ⟨k, hk, e⟩
      apply hn
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨k, mem_indexFinset.2 ((G.isAverageIndex_iff _ _).1 hk), e.symm⟩
    show blockAverageWeight c b * F b = 0
    rw [hs.2 b hno, zero_mul]
  rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_image
    (fun k hk k' hk' e => G.shiftedEdge_injOn c (G.isAverageIndex_of_mem c hk)
      (G.isAverageIndex_of_mem c hk') e)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [hs.1 k (G.isAverageIndex_of_mem c hk)]
theorem blockAverage_eq_finsum (G : IntCoords Λ h P) (c : Λ.CenterEdge) (B : Λ.Edge → ℝ) :
    blockAverage B c = ∑ᶠ b, blockAverageWeight c b * B b := by
  rw [G.blockAverage_eq_sum, G.finsum_weight_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _).symm
theorem blockFactor_pos (G : IntCoords Λ h P) : (0 : ℝ) < (Λ.blockFactor : ℝ) := by
  rw [G.blockFactor_eq]
  positivity
theorem zpow_neg_five_mul (G : IntCoords Λ h P) :
    (Λ.blockFactor : ℝ) ^ (-4 - 1 : ℤ) * (Λ.blockFactor : ℝ) =
      (Λ.blockFactor : ℝ) ^ (-4 : ℤ) := by
  have h0 := G.blockFactor_pos.ne'
  rw [← zpow_add_one₀ h0]
  norm_num
theorem finsum_weight_eq_one (G : IntCoords Λ h P) (c : Λ.CenterEdge) :
    ∑ᶠ b, blockAverageWeight c b = 1 := by
  have h0 := G.blockFactor_pos.ne'
  have h1 := G.blockAverage_eq_finsum c (fun _ => 1)
  simp only [mul_one] at h1
  rw [← h1]
  unfold blockAverage
  rw [G.finsum_cube_eq]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, card_boxFinset]
  rw [← G.blockFactor_eq]
  push_cast
  rw [zpow_neg]
  have : (Λ.blockFactor : ℝ) ^ (5 : ℤ) = (Λ.blockFactor : ℝ) ^ 4 * (Λ.blockFactor : ℝ) := by
    norm_cast
  rw [this]
  exact inv_mul_cancel₀ (by positivity)
theorem blockAverageWeightBounds (G : IntCoords Λ h P) (c : Λ.CenterEdge) :
    BlockAverageWeightBounds c := by
  classical
  have hs := G.blockAverageWeight_spec c
  have hpos := G.blockFactor_pos
  refine ⟨fun b => ?_, G.finsum_weight_eq_one c, ?_⟩
  · by_cases hb : ∃ k, Λ.IsAverageIndex c.axis k ∧ b = shiftedEdge c.src c.axis k
    · obtain ⟨k, hk, rfl⟩ := hb
      rw [hs.1 k hk]
      refine ⟨by positivity, ?_⟩
      rw [← G.zpow_neg_five_mul]
      have hle : (tentMultiplicity Λ.blockFactor (k c.axis) : ℝ) ≤ (Λ.blockFactor : ℝ) := by
        exact_mod_cast tentMultiplicity_le _ _
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    · rw [hs.2 b hb]
      exact ⟨le_rfl, by positivity⟩
  · have hsup : Function.support (blockAverageWeight c) =
        shiftedEdge c.src c.axis '' (↑(indexFinset h c.axis) : Set (Fin 4 → ℤ)) := by
      ext b
      constructor
      · intro hb
        by_contra hn
        apply hb
        refine hs.2 b ?_
        rintro ⟨k, hk, e⟩
        exact hn ⟨k, mem_indexFinset.2 ((G.isAverageIndex_iff _ _).1 hk), e.symm⟩
      · rintro ⟨k, hk, rfl⟩
        have hk' := mem_indexFinset.1 hk
        have hp : 0 < tentMultiplicity Λ.blockFactor (k c.axis) := by
          rw [G.blockFactor_eq]
          exact tentMultiplicity_pos h hk'.1 hk'.2.1
        show blockAverageWeight c _ ≠ 0
        rw [hs.1 k (G.isAverageIndex_of_mem c hk)]
        have : (0 : ℝ) < (tentMultiplicity Λ.blockFactor (k c.axis) : ℝ) := by exact_mod_cast hp
        positivity
    have hinj : Set.InjOn (shiftedEdge c.src c.axis)
        (↑(indexFinset h c.axis) : Set (Fin 4 → ℤ)) :=
      fun k hk k' hk' e => G.shiftedEdge_injOn c (G.isAverageIndex_of_mem c hk)
        (G.isAverageIndex_of_mem c hk') e
    rw [hsup, hinj.encard_image, Set.encard_coe_eq_coe_finsetCard, card_indexFinset, G.blockFactor_eq]
    congr 2
    rw [show 2 * (2 * h + 1) - 1 = 4 * h + 1 by omega]
theorem shiftedEdge_tgt (G : IntCoords Λ h P) (c : Λ.CenterEdge) (r : Fin 4 → ℤ) :
    shiftedEdge c.tgt c.axis r =
      shiftedEdge c.src c.axis (r + longStep h c.axis) := by
  refine Edge.ext ?_ rfl
  show c.tgt + latticeVec Λ r = c.src + latticeVec Λ _
  rw [G.tgt_eq, add_assoc, ← latticeVec_add, add_comm r]
theorem edgesOfTheWeights (G : IntCoords Λ h P) (c : Λ.CenterEdge) : EdgesOfTheWeights c := by
  have hidx := fun k => G.isAverageIndex_iff c.axis k
  refine ⟨?_, ?_, ?_⟩
  · ext b
    constructor
    · rintro ⟨k, ⟨hk, hlt⟩, rfl⟩
      have hk1 := (hidx k).1 hk
      have hlt' := (G.lt_halfWidth_iff _).1 hlt
      refine ⟨rfl, (G.inCube_iff rfl).2 ⟨k, fun ν => ?_, hlt', rfl⟩⟩
      by_cases hν : ν = c.axis
      · subst hν
        rw [_root_.abs_le]
        constructor <;> omega
      · exact hk1.2.2 ν hν
    · rintro ⟨hd, hi⟩
      obtain ⟨r, hr, hlt, rfl⟩ := (G.inCube_iff hd).1 hi
      have hμ := _root_.abs_le.1 (hr c.axis)
      exact ⟨r, ⟨(hidx r).2 ⟨hμ.1, by omega, fun ν _ => hr ν⟩, (G.lt_halfWidth_iff _).2 hlt⟩, rfl⟩
  · ext b
    constructor
    · rintro ⟨k, ⟨hk, he⟩, rfl⟩
      have hk1 := (hidx k).1 hk
      have he' := (G.eq_halfWidth_iff _).1 he
      refine (G.mem_edgeCorridor_iff _ _).2 ⟨rfl, k, fun ν => ?_, he', rfl⟩
      by_cases hν : ν = c.axis
      · subst hν
        rw [_root_.abs_le]
        constructor <;> omega
      · exact hk1.2.2 ν hν
    · intro hb
      obtain ⟨-, r, hr, he, rfl⟩ := (G.mem_edgeCorridor_iff _ _).1 hb
      exact ⟨r, ⟨(hidx r).2 ⟨by omega, by omega, fun ν _ => hr ν⟩, (G.eq_halfWidth_iff _).2 he⟩, rfl⟩
  · ext b
    constructor
    · rintro ⟨k, ⟨hk, hlt⟩, rfl⟩
      have hk1 := (hidx k).1 hk
      have hlt' := (G.halfWidth_lt_iff _).1 hlt
      refine ⟨rfl, (G.inCube_iff (μ := c.axis) rfl).2
        ⟨k - longStep h c.axis, fun ν => ?_, ?_, ?_⟩⟩
      · by_cases hν : ν = c.axis
        · subst hν
          simp only [Pi.sub_apply, longStep, Pi.single_eq_same]
          rw [_root_.abs_le]
          constructor <;> omega
        · simp only [Pi.sub_apply, longStep, Pi.single_eq_of_ne hν, sub_zero]
          exact hk1.2.2 ν hν
      · simp only [Pi.sub_apply, longStep, Pi.single_eq_same]
        omega
      · rw [G.shiftedEdge_tgt, sub_add_cancel]
    · rintro ⟨hd, hi⟩
      obtain ⟨r, hr, hlt, rfl⟩ := (G.inCube_iff hd).1 hi
      have hμ := _root_.abs_le.1 (hr c.axis)
      refine ⟨r + longStep h c.axis, ⟨(hidx _).2 ⟨?_, ?_, fun ν hν => ?_⟩,
        (G.halfWidth_lt_iff _).2 ?_⟩, (G.shiftedEdge_tgt c r).symm⟩
      · simp only [Pi.add_apply, longStep, Pi.single_eq_same]; omega
      · simp only [Pi.add_apply, longStep, Pi.single_eq_same]; omega
      · simpa only [Pi.add_apply, longStep, Pi.single_eq_of_ne hν, add_zero] using hr ν
      · simp only [Pi.add_apply, longStep, Pi.single_eq_same]; omega
theorem axisPathEdge_eq (c : Λ.CenterEdge) (i : ℕ) :
    axisPathEdge c i = shiftedEdge c.src c.axis (Pi.single c.axis (i : ℤ)) := by
  refine Edge.ext ?_ rfl
  show c.src + i • Λ.basisVec c.axis = c.src + latticeVec Λ _
  rw [latticeVec_single, natCast_zsmul]
theorem inCubeBox_single (μ : Fin 4) : InCubeBox h (Pi.single μ (h : ℤ)) := fun ν => by
  by_cases hν : ν = μ
  · subst hν
    simp
  · simp [Pi.single_eq_of_ne hν]
theorem axisPathEdge_mem (G : IntCoords Λ h P) (c : Λ.CenterEdge) : axisPathEdge c h ∈ edgeCorridor c :=
  (G.mem_edgeCorridor_iff _ _).2 ⟨rfl, _, inCubeBox_single _, by simp, axisPathEdge_eq c h⟩
theorem axisPathEdge_unique (G : IntCoords Λ h P) (c : Λ.CenterEdge) {j : ℕ}
    (hj : j < Λ.blockFactor) (hc : axisPathEdge c j ∈ edgeCorridor c) : j = h := by
  have hj' : (j : ℤ) < 2 * h + 1 := by
    rw [G.blockFactor_eq] at hj
    omega
  obtain ⟨-, r, hr, he, e⟩ := (G.mem_edgeCorridor_iff _ _).1 hc
  rw [axisPathEdge_eq] at e
  have hv : latticeVec Λ (Pi.single c.axis (j : ℤ)) = latticeVec Λ r :=
    add_left_cancel (a := c.src) (congrArg Edge.src e)
  have hk := G.latticeVec_injOn hv (fun ν => by
    have h1 := _root_.abs_le.1 (hr ν)
    rw [abs_lt]
    simp only [Pi.single_apply]
    split_ifs <;> constructor <;> omega)
  have := congrFun hk c.axis
  simp only [Pi.single_eq_same] at this
  omega
theorem pivotEdge_eq (G : IntCoords Λ h P) (c : Λ.CenterEdge) : pivotEdge c = axisPathEdge c h := by
  have hLt : h < Λ.blockFactor := by
    rw [G.blockFactor_eq]
    omega
  have hspec : IsPivotEdge c (pivotEdge c) :=
    Classical.epsilon_spec (p := IsPivotEdge c) ⟨_, G.axisPathEdge_mem c, h, hLt, rfl⟩
  obtain ⟨hc, i, hi, e⟩ := hspec
  rw [e, G.axisPathEdge_unique c hi (e ▸ hc)]
theorem pivotEdgeOfACenterEdge (G : IntCoords Λ h P) (c : Λ.CenterEdge) : PivotEdgeOfACenterEdge c := by
  have hs := G.blockAverageWeight_spec c
  have hLt : h < Λ.blockFactor := by
    rw [G.blockFactor_eq]
    omega
  have hp := G.pivotEdge_eq c
  have hindex : Λ.IsAverageIndex c.axis (Pi.single c.axis (h : ℤ)) := by
    refine (G.isAverageIndex_iff _ _).2 ⟨?_, ?_, fun ν _ => inCubeBox_single _ ν⟩
    · simp only [Pi.single_eq_same]; omega
    · simp only [Pi.single_eq_same]; omega
  refine ⟨⟨h, G.halfWidth_eq.symm, hLt, G.axisPathEdge_mem c,
      fun j hj hc => G.axisPathEdge_unique c hj hc, hp⟩,
    fun y hy ht => ?_, ?_, fun c' hne => ?_⟩
  · have hin : (pivotEdge c).InCube y := ht.1
    rw [hp, axisPathEdge_eq] at hin
    exact (G.edgesFromACube c.src c.src_mem _
      (fun ρ => (G.abs_le_halfWidth_iff _).2 (inCubeBox_single _ ρ))
      c.axis).2 ((G.eq_halfWidth_iff _).2 (by simp)) |>.1 y hy hin
  · rw [hp, axisPathEdge_eq, hs.1 _ hindex, Pi.single_eq_same, ← G.zpow_neg_five_mul]
    congr 2
    have := G.tentMultiplicityValues.2.1 (h : ℤ) (by rw [G.halfWidth_eq]; simp)
    exact this
  · by_contra hq
    have hex : ∃ k, Λ.IsAverageIndex c.axis k ∧
        pivotEdge c' = shiftedEdge c.src c.axis k := by
      by_contra hn
      exact hq (hs.2 _ hn)
    obtain ⟨k, hk, e⟩ := hex
    rw [G.pivotEdge_eq c', axisPathEdge_eq] at e
    have hd : c'.axis = c.axis := congrArg Edge.axis e
    have ht : c'.src + latticeVec Λ (Pi.single c'.axis (h : ℤ)) = c.src + latticeVec Λ k :=
      congrArg Edge.src e
    rw [hd] at ht
    have hcc : c'.src = c.src + latticeVec Λ (k - Pi.single c.axis (h : ℤ)) := by
      rw [latticeVec_sub, add_sub_assoc', ← ht]
      abel
    have hk1 := (G.isAverageIndex_iff _ _).1 hk
    have hz : k - Pi.single c.axis (h : ℤ) = 0 := by
      funext ν
      have hdv := G.dvd_of_center_add c.src_mem (hcc ▸ c'.src_mem) ν
      refine Int.eq_zero_of_abs_lt_dvd hdv ?_
      by_cases hν : ν = c.axis
      · subst hν
        simp only [Pi.sub_apply, Pi.single_eq_same]
        rw [abs_lt]
        constructor <;> omega
      · have h3 := _root_.abs_le.1 (hk1.2.2 ν hν)
        simp only [Pi.sub_apply, Pi.single_eq_of_ne hν, sub_zero]
        rw [abs_lt]
        constructor <;> omega
    rw [hz, latticeVec_zero, add_zero] at hcc
    exact hne (CenterEdge.ext hcc hd)
theorem all (G : IntCoords Λ h P) :
    Λ.CubesPartition ∧ Λ.EdgesFromACube ∧ Λ.TentMultiplicityValues ∧
    ∀ c : Λ.CenterEdge,
      PointsOfTheTwoCubes c ∧
      IsBlockAverageWeight c (blockAverageWeight c) ∧
      (∀ B : Λ.Edge → ℝ, blockAverage B c = ∑ᶠ b, blockAverageWeight c b * B b) ∧
      EdgesOfTheWeights c ∧ BlockAverageWeightBounds c ∧ PivotEdgeOfACenterEdge c :=
  ⟨G.cubesPartition, G.edgesFromACube, G.tentMultiplicityValues, fun c =>
    ⟨G.pointsOfTheTwoCubes c, G.blockAverageWeight_spec c, G.blockAverage_eq_finsum c,
      G.edgesOfTheWeights c, G.blockAverageWeightBounds c, G.pivotEdgeOfACenterEdge c⟩⟩
end IntCoords
theorem norm_coe_le_abs {S : ℝ} (hS : 0 < S) (a : ℝ) : ‖(a : AddCircle S)‖ ≤ |a| := by apply _root_.YangMills.Construction.Dirichlet.NearCentres.norm_coe_le_abs_of_pos <;> assumption
variable {D : ScaleData}
theorem point_ext {x y : D.SiteAt D.lastLevel} (e : ∀ κ, (x : D.Space) κ = (y : D.Space) κ) : x = y :=
  Subtype.ext (funext e)
end YangMills.Construction.UnitSpacingLattice.BlockAverageProof
