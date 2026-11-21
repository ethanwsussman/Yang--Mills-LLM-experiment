import YangMills.Construction.Lattice.BareBaseSitesOfTheSchemes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
private def diagonalLift (L m : ℕ) (j t : ℤ) : FourTorus L m :=
  fun _ => (((t : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m))
private theorem coe_sum_unitStep {j : ℤ} (t : ℤ) :
    ((∑ μ, t • unitStep L m j μ : Site L m j) : FourTorus L m) = diagonalLift L m j t := by
  funext ν
  rw [AddSubgroup.val_finsetSum, Finset.sum_apply, Finset.sum_eq_single ν]
  · simp [unitStep, pointOnAxis, diagonalLift]
  · intro μ _ hne
    simp [unitStep, pointOnAxis, Pi.single_eq_of_ne hne.symm]
  · simp
private theorem coe_toSublattice (hL : 0 < L) {j j' : ℤ} (hj : j ≤ j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y :=
  Classical.epsilon_spec (p := fun x : Site L m j' => (x : FourTorus L m) = y)
    ⟨⟨y, sublattice_mono hL m hj y.2⟩, rfl⟩
abbrev _root_.YangMills.SharedProofs.p9023 := @coe_toSublattice
private theorem diagonalLift_rescale (hL : 0 < L) (j t : ℤ) (n : ℕ) :
    diagonalLift L m j t = diagonalLift L m (j + n) (t * (L : ℤ) ^ n) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have e : meshSize L j = (L : ℝ) ^ n * meshSize L (j + n) := by
    unfold meshSize
    rw [← zpow_natCast, ← zpow_add₀ hL']
    congr 1
    ring
  funext ν
  have e' : (t : ℝ) * meshSize L j = ((t * (L : ℤ) ^ n : ℤ) : ℝ) * meshSize L (j + n) := by
    rw [e]
    push_cast
    ring
  simp only [diagonalLift, e']
private theorem diagonalLift_add (j t t' : ℤ) :
    diagonalLift L m j t + diagonalLift L m j t' = diagonalLift L m j (t + t') := by
  funext ν
  simp only [diagonalLift, Pi.add_apply, Int.cast_add, add_mul, AddCircle.coe_add]
private theorem coe_schemeBaseSite_cornered (hL : 0 < L) {j j' : ℤ} (hj : j ≤ j')
    (y : Site L m j) :
    ((schemeBaseSite .cornered j' y : Site L m j') : FourTorus L m) =
      (y : FourTorus L m) + diagonalLift L m j' (-centreToFaceSteps L) := by
  have e : schemeBaseSite .cornered j' y =
      y.toSublattice j' + ∑ μ, (-centreToFaceSteps L) • unitStep L m j' μ := by
    simp only [schemeBaseSite]
    rw [sub_eq_add_neg, ← neg_smul, Finset.smul_sum]
  rw [e, AddSubgroup.coe_add, coe_toSublattice hL hj, coe_sum_unitStep]
private theorem coe_finestBaseSite_centred (hL : 0 < L) (K : ℕ) :
    ∀ (j : ℕ) (y : SiteAtLevel L m K j),
      ((finestBaseSite .centred K j y : SiteAtLevel L m K 0) : FourTorus L m) =
        (y : FourTorus L m)
  | 0, _ => rfl
  | j + 1, y => by
    rw [finestBaseSite, coe_finestBaseSite_centred hL K j]
    exact coe_toSublattice hL (by simp only [levelDepth]; push_cast; omega) y
private theorem coe_finestBaseSite_cornered (hodd : Odd L) (K : ℕ) :
    ∀ (j : ℕ) (y : SiteAtLevel L m K j),
      ((finestBaseSite .cornered K j y : SiteAtLevel L m K 0) : FourTorus L m) =
        (y : FourTorus L m) + diagonalLift L m (levelDepth K 0) (-(((L : ℤ) ^ j - 1) / 2))
  | 0, y => by
    funext ν
    simp [finestBaseSite, diagonalLift]
  | j + 1, y => by
    have hL : 0 < L := hodd.pos
    rw [finestBaseSite, coe_finestBaseSite_cornered hodd K j,
      coe_schemeBaseSite_cornered hL (by simp only [levelDepth]; push_cast; omega) y, add_assoc,
      diagonalLift_rescale hL (levelDepth K j) _ j,
      show levelDepth K j + (j : ℤ) = levelDepth K 0 by simp only [levelDepth]; push_cast; omega,
      diagonalLift_add]
    congr 2
    obtain ⟨a, ha⟩ : Odd (L : ℤ) := by exact_mod_cast hodd
    obtain ⟨b, hb⟩ : Odd ((L : ℤ) ^ j) := Odd.pow (by exact_mod_cast hodd)
    have e1 : ((L : ℤ) - 1) / 2 = a := by omega
    have e2 : ((L : ℤ) ^ j - 1) / 2 = b := by omega
    have e3 : ((L : ℤ) ^ (j + 1) - 1) / 2 = 2 * a * b + a + b := by
      have e : (L : ℤ) ^ (j + 1) - 1 = 2 * (2 * a * b + a + b) := by
        rw [pow_succ, hb, ha]
        ring
      rw [e]
      omega
    simp only [centreToFaceSteps, e1, e2, e3]
    rw [hb]
    ring
private theorem lowestBlockSite_eq (hodd : Odd L) {j : ℤ} (n : ℕ) (y : Site L m j) :
    lowestBlockSite n y = refinedOffsetSite n y (fun _ => -(((L : ℤ) ^ n - 1) / 2)) := by
  obtain ⟨b, hb⟩ : Odd ((L : ℤ) ^ n) := Odd.pow (by exact_mod_cast hodd)
  have hpos : 0 < (L : ℤ) ^ n := pow_pos (by exact_mod_cast hodd.pos) n
  have e : ((L : ℤ) ^ n - 1) / 2 = b := by omega
  have hb0 : 0 ≤ b := by omega
  rw [e]
  have hp : (fun _ => -b : Fin 4 → ℤ) ∈ blockOffsets L n := by
    intro μ
    simp only [abs_neg, abs_of_nonneg hb0, hb]
    omega
  have hmin : ∀ q ∈ blockOffsets L n, ∀ μ, (fun _ => -b : Fin 4 → ℤ) μ ≤ q μ := by
    intro q hq μ
    have hqμ := hq μ
    rw [hb] at hqμ
    have h' := neg_abs_le (q μ)
    show -b ≤ q μ
    linarith
  have hspec : IsLowestBlockSite n y (refinedOffsetSite n y fun _ => -b) := ⟨_, hp, rfl, hmin⟩
  obtain ⟨p, hp', hx, hmin'⟩ : IsLowestBlockSite n y (lowestBlockSite n y) :=
    Classical.epsilon_spec ⟨_, hspec⟩
  have hpe : p = fun _ => -b := funext fun μ => le_antisymm (hmin' _ hp μ) (hmin p hp' μ)
  rw [hx, hpe]
private theorem coe_refinedOffsetSite (hL : 0 < L) {j : ℤ} (n : ℕ) (y : Site L m j) (t : ℤ) :
    ((refinedOffsetSite n y (fun _ => t) : Site L m (j + n)) : FourTorus L m) =
      (y : FourTorus L m) + diagonalLift L m (j + n) t := by
  simp only [refinedOffsetSite, offsetSite]
  rw [AddSubgroup.coe_add, coe_toSublattice hL (by omega), coe_sum_unitStep]
theorem schemeFinestBaseSites_holds : SchemeFinestBaseSites := by
  intro d N L K m G hData j _ y
  have hodd := hData.odd_L
  have hL : 0 < L := hodd.pos
  refine ⟨coe_finestBaseSite_centred hL K j y, ?_⟩
  rw [coe_finestBaseSite_cornered hodd K j y, lowestBlockSite_eq hodd j y, coe_refinedOffsetSite hL,
    show levelDepth K j + (j : ℤ) = levelDepth K 0 by simp only [levelDepth]; push_cast; omega]
end PeriodicLattice
end YangMills.Construction
