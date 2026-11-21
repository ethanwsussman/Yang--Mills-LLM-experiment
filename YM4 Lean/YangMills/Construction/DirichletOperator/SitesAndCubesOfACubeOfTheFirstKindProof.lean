import YangMills.Construction.DirichletOperator.BondsNearACubeCarriedToItsTorusProof
import YangMills.Construction.DirichletOperator.DifferenceOperatorsAgreeOnTheLocalTorusProof
import YangMills.Construction.DirichletOperator.SidesOfTheBlocksAtALevel
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes.FirstTypeLattice
variable {S : ℝ}
theorem torusProj_add (p q : Fin 4 → ℝ) :
    torusProj 4 S (p + q) = torusProj 4 S p + torusProj 4 S q := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_add <;> assumption
theorem torusProj_sub (p q : Fin 4 → ℝ) :
    torusProj 4 S (p - q) = torusProj 4 S p - torusProj 4 S q := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusBonds.torusProj_sub <;> assumption
theorem torusProj_eq_iff {p q : Fin 4 → ℝ} :
    torusProj 4 S p = torusProj 4 S q ↔ ∀ μ, ∃ l : ℤ, p μ - q μ = (l : ℝ) * S := by
  constructor
  · intro h μ
    have h₁ : (p μ : AddCircle S) = (q μ : AddCircle S) := congrFun h μ
    have h₀ : ((p μ - q μ : ℝ) : AddCircle S) = 0 := by
      rw [AddCircle.coe_sub]
      exact sub_eq_zero.2 h₁
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff S).1 h₀
    exact ⟨n, by rw [← hn]; simp⟩
  · intro h
    funext μ
    obtain ⟨l, hl⟩ := h μ
    have h₀ : ((p μ - q μ : ℝ) : AddCircle S) = 0 :=
      (AddCircle.coe_eq_zero_iff S).2 ⟨l, by simp [hl]⟩
    rw [AddCircle.coe_sub] at h₀
    exact sub_eq_zero.1 h₀
theorem mem_spacingLattice_iff {σ : ℝ} {x : PeriodicTorus 4 S} :
    x ∈ spacingLattice 4 S σ ↔ ∃ k : Fin 4 → ℤ, x = torusProj 4 S fun μ => (k μ : ℝ) * σ :=
  Iff.rfl
theorem torusProj_mem_spacingLattice_iff {σ : ℝ} {a : ℤ} (hS : S = (a : ℝ) * σ)
    {p : Fin 4 → ℝ} :
    torusProj 4 S p ∈ spacingLattice 4 S σ ↔ ∃ k : Fin 4 → ℤ, ∀ μ, p μ = (k μ : ℝ) * σ := by
  rw [mem_spacingLattice_iff]
  constructor
  · rintro ⟨k, hk⟩
    have h := torusProj_eq_iff.1 hk
    choose l hl using h
    refine ⟨fun μ => k μ + l μ * a, fun μ => ?_⟩
    have := hl μ
    rw [hS] at this
    push_cast
    linarith
  · rintro ⟨k, hk⟩
    exact ⟨k, by congr 1; funext μ; exact hk μ⟩
theorem supNorm_torusProj_le (v : Fin 4 → ℝ) : supNorm (torusProj 4 S v) ≤ ‖v‖ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_proj_le <;> assumption
theorem exists_lift_abs_le (hS : 0 < S) (p : PeriodicTorus 4 S) {r : ℝ} (h : supNorm p ≤ r) :
    ∃ v : Fin 4 → ℝ, torusProj 4 S v = p ∧ ∀ μ, |v μ| ≤ r := by
  have hsurj : ∃ u : Fin 4 → ℝ, torusProj 4 S u = p := by
    choose u hu using fun μ => QuotientAddGroup.mk_surjective (p μ)
    exact ⟨u, funext hu⟩
  obtain ⟨u, rfl⟩ := hsurj
  set v : Fin 4 → ℝ := fun μ => u μ - (round (u μ / S) : ℝ) * S with hv
  have hcov : torusProj 4 S v = torusProj 4 S u :=
    torusProj_eq_iff.2 fun μ => ⟨-round (u μ / S), by simp [hv]⟩
  have hmin : ∀ w : Fin 4 → ℝ, torusProj 4 S w = torusProj 4 S u → ‖v‖ ≤ ‖w‖ := by
    intro w hw
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun μ => ?_
    refine le_trans ?_ (norm_le_pi_norm w μ)
    obtain ⟨l, hl⟩ := torusProj_eq_iff.1 hw μ
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have h₁ := round_le (u μ / S) (-l)
    have e₁ : v μ = (u μ / S - (round (u μ / S) : ℝ)) * S := by
      simp only [hv]
      field_simp
    have e₂ : w μ = (u μ / S - ((-l : ℤ) : ℝ)) * S := by
      push_cast
      field_simp
      linarith
    rw [e₁, e₂, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right h₁ (abs_nonneg S)
  have hle : ‖v‖ ≤ supNorm (torusProj 4 S u) := by
    refine le_csInf ⟨_, u, rfl, rfl⟩ ?_
    rintro r' ⟨w, hw, rfl⟩
    exact hmin w hw
  exact ⟨v, hcov, fun μ => by
    have := norm_le_pi_norm v μ
    rw [Real.norm_eq_abs] at this
    linarith⟩
theorem cubeAt_torusProj (hS : 0 < S) {σ : ℝ} (hσ : 0 < σ) (c : Fin 4 → ℝ) :
    cubeAt (torusProj 4 S c) σ = torusProj 4 S '' {p | ∀ μ, |p μ - c μ| ≤ σ / 2} := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, hb⟩ := exists_lift_abs_le hS _ hx
    refine ⟨c + v, fun μ => by simpa using hb μ, ?_⟩
    rw [torusProj_add, hv]
    abel
  · rintro ⟨p, hp, rfl⟩
    show supNorm (torusProj 4 S p - torusProj 4 S c) ≤ σ / 2
    rw [← torusProj_sub]
    refine (supNorm_torusProj_le _).trans ?_
    exact (pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ => by
      simpa [Real.norm_eq_abs] using hp μ
theorem self_mem_cubeAt {σ : ℝ} (hσ : 0 < σ) (c : PeriodicTorus 4 S) : c ∈ cubeAt c σ := by
  show supNorm (c - c) ≤ σ / 2
  have h₀ : c - c = torusProj 4 S 0 := by
    rw [sub_self]
    funext μ
    simp [torusProj]
  rw [h₀]
  refine (supNorm_torusProj_le _).trans ?_
  simpa using (by positivity : 0 ≤ σ / 2)
theorem le_supNorm_sub {B : ℝ} (hB : 0 < B) (h2B : 2 * B ≤ S) {u z : Fin 4 → ℝ} {μ : Fin 4}
    (hu : |u μ - z μ| = B) : B ≤ supNorm (torusProj 4 S u - torusProj 4 S z) := by
  rw [← torusProj_sub]
  refine le_csInf ⟨_, u - z, rfl, rfl⟩ ?_
  rintro r ⟨v, hv, rfl⟩
  obtain ⟨l, hl⟩ := torusProj_eq_iff.1 hv μ
  refine le_trans ?_ (norm_le_pi_norm v μ)
  rw [Real.norm_eq_abs]
  have hl' : v μ = (u μ - z μ) + (l : ℝ) * S := by
    have : (u - z) μ = u μ - z μ := rfl
    rw [this] at hl
    linarith
  have hSpos : 0 < S := by linarith
  by_cases h0 : l = 0
  · simp [hl', h0, hu]
  · have h1 : (1 : ℝ) ≤ |(l : ℝ)| := by
      have : (1 : ℤ) ≤ |l| := Int.one_le_abs h0
      exact_mod_cast this
    have h2 : S ≤ |(l : ℝ) * S| := by
      rw [abs_mul, abs_of_pos hSpos]
      nlinarith
    have h3 : |(l : ℝ) * S| ≤ |v μ| + |u μ - z μ| := by
      have e : (l : ℝ) * S = v μ - (u μ - z μ) := by linarith
      rw [e]
      exact abs_sub _ _
    linarith
theorem abs_sub_add_half_eq {σ B p z : ℝ} (hσ : 0 < σ) {b w k : ℤ} (hB : B = (b : ℝ) * σ)
    (hz : z = ((w : ℝ) + 1 / 2) * σ) (hp : p = (k : ℝ) * σ) (hlt : |p - z| < B)
    (hge : B ≤ |p - z| + σ / 2) : |p - z| + σ / 2 = B := by
  have hh : 0 < σ / 2 := half_pos hσ
  set e : ℤ := 2 * (k - w) - 1 with he
  have h₀ : |p - z| = ((|e| : ℤ) : ℝ) * (σ / 2) := by
    have : p - z = (e : ℝ) * (σ / 2) := by
      rw [hp, hz, he]
      push_cast
      ring
    rw [this, abs_mul, abs_of_pos hh, Int.cast_abs]
  rw [h₀] at hlt hge ⊢
  have h₁ : |e| < 2 * b := by
    have : ((|e| : ℤ) : ℝ) * (σ / 2) < ((2 * b : ℤ) : ℝ) * (σ / 2) := by
      push_cast at hlt ⊢
      rw [hB] at hlt
      linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hh.le
  have h₂ : 2 * b ≤ |e| + 1 := by
    have : ((2 * b : ℤ) : ℝ) * (σ / 2) ≤ ((|e| + 1 : ℤ) : ℝ) * (σ / 2) := by
      push_cast at hge ⊢
      rw [hB] at hge
      linarith
    exact_mod_cast le_of_mul_le_mul_right this hh
  have h₃ : |e| + 1 = 2 * b := by omega
  have h₄ : ((|e| : ℤ) : ℝ) + 1 = 2 * (b : ℝ) := by exact_mod_cast h₃
  rw [hB]
  linear_combination (σ / 2) * h₄
theorem exists_boundary_point {σ B : ℝ} (hσ : 0 < σ) {b : ℤ} (hB : B = (b : ℝ) * σ)
    {z p : Fin 4 → ℝ} (hz : ∀ μ, ∃ w : ℤ, z μ = ((w : ℝ) + 1 / 2) * σ) {k : Fin 4 → ℤ}
    (hp : ∀ μ, p μ = (k μ : ℝ) * σ) (hpO : ∀ μ, |p μ - z μ| < B)
    (hnot : ¬∀ μ, |p μ - z μ| + σ / 2 < B) :
    ∃ (u : Fin 4 → ℝ) (μ : Fin 4), (∀ ν, |u ν - p ν| ≤ σ / 2) ∧ |u μ - z μ| = B ∧
      ∀ ν, |u ν - z ν| ≤ B := by
  push Not at hnot
  obtain ⟨μ, hμ⟩ := hnot
  obtain ⟨w, hw⟩ := hz μ
  have heq := abs_sub_add_half_eq hσ hB hw (hp μ) (hpO μ) hμ
  have hh : 0 < σ / 2 := half_pos hσ
  rcases le_total (z μ) (p μ) with h | h
  · have hd : p μ - z μ + σ / 2 = B := by
      rwa [abs_of_nonneg (by linarith)] at heq
    have hval : |p μ + σ / 2 - z μ| = B := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    refine ⟨Function.update p μ (p μ + σ / 2), μ, fun ν => ?_, ?_, fun ν => ?_⟩
    · by_cases hν : ν = μ
      · subst hν
        simp [abs_of_pos hh]
      · simp [Function.update_of_ne hν, hh.le]
    · simpa using hval
    · by_cases hν : ν = μ
      · subst hν
        simp [hval]
      · simpa [Function.update_of_ne hν] using (hpO ν).le
  · have hd : z μ - p μ + σ / 2 = B := by
      rw [abs_of_nonpos (by linarith)] at heq
      linarith
    have hval : |p μ - σ / 2 - z μ| = B := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    refine ⟨Function.update p μ (p μ - σ / 2), μ, fun ν => ?_, ?_, fun ν => ?_⟩
    · by_cases hν : ν = μ
      · subst hν
        simp [abs_of_pos hh]
      · simp [Function.update_of_ne hν, hh.le]
    · simpa using hval
    · by_cases hν : ν = μ
      · subst hν
        simp [hval]
      · simpa [Function.update_of_ne hν] using (hpO ν).le
theorem image_lattice_and_cubes {T σ B : ℝ} (hS : 0 < S) (hT : 0 < T) (hσ : 0 < σ)
    {a a' b : ℤ} (haS : S = (a : ℝ) * σ) (haT : T = (a' : ℝ) * σ) (hB : B = (b : ℝ) * σ)
    (hB0 : 0 < B) (h2B : 2 * B ≤ S) (z : Fin 4 → ℝ)
    (hz : ∀ μ, ∃ w : ℤ, z μ = ((w : ℝ) + 1 / 2) * σ)
    (I : Set (PeriodicTorus 4 S)) (hI : I = {x | supNorm (x - torusProj 4 S z) < B})
    (e : PeriodicTorus 4 S → PeriodicTorus 4 T)
    (hbij : BijOn (torusProj 4 S) {p | ∀ μ, |p μ - z μ| < B} I)
    (hinj : InjOn (torusProj 4 T) (closedCube z (6 * B)))
    (hem : ∀ p ∈ {p : Fin 4 → ℝ | ∀ μ, |p μ - z μ| < B}, e (torusProj 4 S p) = torusProj 4 T p) :
    e '' ((spacingLattice 4 S σ : Set (PeriodicTorus 4 S)) ∩ I) =
        (spacingLattice 4 T σ : Set (PeriodicTorus 4 T)) ∩
          torusProj 4 T '' {p | ∀ μ, |p μ - z μ| < B} ∧
      (fun C => e '' C) '' {C | C ∈ cubePartition 4 S σ ∧ C ⊆ I} =
        {C | C ∈ cubePartition 4 T σ ∧ C ⊆ torusProj 4 T '' {p | ∀ μ, |p μ - z μ| < B}} := by
  have hbox : ∀ p : Fin 4 → ℝ, (∀ μ, |p μ - z μ| + σ / 2 < B) →
      ∀ q ∈ {q : Fin 4 → ℝ | ∀ μ, |q μ - p μ| ≤ σ / 2}, ∀ μ, |q μ - z μ| < B := by
    intro p hA q hq μ
    have h₁ : |q μ - z μ| ≤ |q μ - p μ| + |p μ - z μ| := abs_sub_le _ _ _
    have h₂ := hq μ
    have h₃ := hA μ
    linarith
  have hcube : ∀ p : Fin 4 → ℝ, (∀ μ, |p μ - z μ| + σ / 2 < B) →
      e '' cubeAt (torusProj 4 S p) σ = cubeAt (torusProj 4 T p) σ := by
    intro p hA
    rw [cubeAt_torusProj hS hσ, cubeAt_torusProj hT hσ, image_image]
    exact image_congr fun q hq => hem q (hbox p hA q hq)
  refine ⟨?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, ⟨hxL, hxI⟩, rfl⟩
      obtain ⟨p, hpO, rfl⟩ := hbij.surjOn hxI
      obtain ⟨k, hk⟩ := (torusProj_mem_spacingLattice_iff haS).1 hxL
      rw [hem p hpO]
      exact ⟨(torusProj_mem_spacingLattice_iff haT).2 ⟨k, hk⟩, p, hpO, rfl⟩
    · rintro ⟨hyL, p, hpO, rfl⟩
      obtain ⟨k, hk⟩ := (torusProj_mem_spacingLattice_iff haT).1 hyL
      exact ⟨torusProj 4 S p, ⟨(torusProj_mem_spacingLattice_iff haS).2 ⟨k, hk⟩,
        hbij.mapsTo hpO⟩, hem p hpO⟩
  · ext D
    constructor
    · rintro ⟨C, ⟨⟨c, hc, rfl⟩, hCI⟩, rfl⟩
      obtain ⟨p, hpO, rfl⟩ := hbij.surjOn (hCI (self_mem_cubeAt hσ c))
      obtain ⟨k, hk⟩ := (torusProj_mem_spacingLattice_iff haS).1 hc
      have hA : ∀ μ, |p μ - z μ| + σ / 2 < B := by
        by_contra hnot
        obtain ⟨u, μ, hu, huμ, -⟩ := exists_boundary_point hσ hB hz hk hpO hnot
        have huC : torusProj 4 S u ∈ cubeAt (torusProj 4 S p) σ := by
          rw [cubeAt_torusProj hS hσ]
          exact ⟨u, hu, rfl⟩
        have h₁ := hCI huC
        rw [hI] at h₁
        have h₂ := le_supNorm_sub hB0 h2B huμ
        exact absurd h₁ (not_lt.2 h₂)
      have hkT : torusProj 4 T p ∈ spacingLattice 4 T σ :=
        (torusProj_mem_spacingLattice_iff haT).2 ⟨k, hk⟩
      show e '' cubeAt (torusProj 4 S p) σ ∈ _
      rw [hcube p hA]
      refine ⟨⟨_, hkT, rfl⟩, ?_⟩
      rw [cubeAt_torusProj hT hσ]
      exact image_mono fun q hq => hbox p hA q hq
    · rintro ⟨⟨d, hd, rfl⟩, hDO⟩
      obtain ⟨p, hpO, rfl⟩ := hDO (self_mem_cubeAt hσ d)
      obtain ⟨k, hk⟩ := (torusProj_mem_spacingLattice_iff haT).1 hd
      have hA : ∀ μ, |p μ - z μ| + σ / 2 < B := by
        by_contra hnot
        obtain ⟨u, μ, hu, huμ, hub⟩ := exists_boundary_point hσ hB hz hk hpO hnot
        have huC : torusProj 4 T u ∈ cubeAt (torusProj 4 T p) σ := by
          rw [cubeAt_torusProj hT hσ]
          exact ⟨u, hu, rfl⟩
        obtain ⟨p', hp'O, hp'⟩ := hDO huC
        have hmem₁ : p' ∈ closedCube z (6 * B) := fun ν => by
          have := hp'O ν
          linarith
        have hmem₂ : u ∈ closedCube z (6 * B) := fun ν => by
          have := hub ν
          linarith
        have hpu : p' = u := hinj hmem₁ hmem₂ hp'
        have := hp'O μ
        rw [hpu, huμ] at this
        exact lt_irrefl _ this
      have hkS : torusProj 4 S p ∈ spacingLattice 4 S σ :=
        (torusProj_mem_spacingLattice_iff haS).2 ⟨k, hk⟩
      refine ⟨cubeAt (torusProj 4 S p) σ, ⟨⟨_, hkS, rfl⟩, ?_⟩, hcube p hA⟩
      rw [cubeAt_torusProj hS hσ]
      rintro _ ⟨q, hq, rfl⟩
      exact hbij.mapsTo (hbox p hA q hq)
theorem corner_mem_halfLattice {σ B : ℝ} {a b : ℤ} (haS : S = (a : ℝ) * σ)
    (hB : B = (b : ℝ) * σ) (hodd : Odd b) {c : PeriodicTorus 4 S}
    (hc : c ∈ spacingLattice 4 S B) {ε : Fin 4 → ℝ}
    (hε : ∀ μ, ε μ = 1 ∨ ε μ = -1) {z : Fin 4 → ℝ}
    (hz : torusProj 4 S z = c + torusProj 4 S fun μ => ε μ * (B / 2)) :
    ∀ μ, ∃ w : ℤ, z μ = ((w : ℝ) + 1 / 2) * σ := by
  obtain ⟨k, rfl⟩ := mem_spacingLattice_iff.1 hc
  rw [← torusProj_add] at hz
  intro μ
  obtain ⟨l, hl⟩ := torusProj_eq_iff.1 hz μ
  obtain ⟨c', hc'⟩ := hodd
  have hbr : (b : ℝ) = 2 * (c' : ℝ) + 1 := by exact_mod_cast hc'
  have hl' : z μ - ((k μ : ℝ) * B + ε μ * (B / 2)) = (l : ℝ) * S := hl
  rw [haS, hB] at hl'
  rcases hε μ with h | h
  · refine ⟨l * a + k μ * b + c', ?_⟩
    rw [h] at hl'
    push_cast
    linear_combination hl' + (σ / 2) * hbr
  · refine ⟨l * a + k μ * b - c' - 1, ?_⟩
    rw [h] at hl'
    push_cast
    linear_combination hl' - (σ / 2) * hbr
theorem coe_circleCentredRep (hS : 0 < S) (θ : AddCircle S) :
    ((circleCentredRep θ : ℝ) : AddCircle S) = θ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.coe_circleCentredRep <;> assumption
theorem unitSide_eq_mul {L : ℕ} (hL : (0 : ℝ) < L) (m K s j : ℕ) (hj : j ≤ K) :
    unitSide L m K s =
      ((2 * (L : ℤ) ^ (m + K - j) : ℤ) : ℝ) * scaleSpacing L (unitSpacing L s) (j : ℤ) := by
  have hne : (L : ℝ) ≠ 0 := hL.ne'
  have e : (m : ℤ) + (K : ℤ) - (s : ℤ) = ((m + K - j : ℕ) : ℤ) + (j : ℤ) + -(s : ℤ) := by
    omega
  simp only [unitSide, scaleSpacing, unitSpacing]
  rw [e, zpow_add₀ hne, zpow_add₀ hne, zpow_natCast]
  push_cast
  ring
theorem pow_mul_scaleSpacing_eq {L : ℕ} (μ n j : ℕ) (ξ : ℝ) (hj : j ≤ μ + n) :
    ((L ^ μ : ℕ) : ℝ) * scaleSpacing L ξ (n : ℤ) =
      (((L : ℤ) ^ (μ + n - j) : ℤ) : ℝ) * scaleSpacing L ξ (j : ℤ) := by
  have e : μ + n = (μ + n - j) + j := by omega
  have h₁ : (L : ℝ) ^ μ * (L : ℝ) ^ n = (L : ℝ) ^ (μ + n - j) * (L : ℝ) ^ j := by
    rw [← pow_add, ← pow_add, ← e]
  simp only [scaleSpacing, zpow_natCast]
  push_cast
  linear_combination ξ * h₁
theorem holds (h₁ : FirstTypeMaps.Statement) (h₂ : LevelCubeSides.Statement) :
    Statement := by
  intro 𝒮 K m M R₁ hseq Q hQ j hj
  obtain ⟨⟨hadm, hset⟩, hbij, hinj, hem, -⟩ := h₁ 𝒮 K m M R₁ hseq Q hQ
  obtain ⟨-, h2B, -⟩ := h₂ 𝒮 K m M R₁ hseq Q.level Q.level_le
  have hsep := hseq.separated
  obtain ⟨hLM, μ₀, hM⟩ := hsep.blockSize_isPowerGe
  have hL13 := 𝒮.thirteen_le_L
  have hμ : 1 ≤ μ₀ := by
    rcases Nat.eq_zero_or_pos μ₀ with h | h
    · subst h
      simp at hM
      omega
    · exact h
  have hlast : topLevel 𝒮 ≤ 𝒮.s := by
    refine csSup_le ⟨0, hsep.zero_nonempty⟩ fun n hn => ?_
    by_contra h
    have hne : (𝒮.Ω n).Nonempty := hn
    rw [𝒮.Ω_eq_empty n (by omega)] at hne
    exact not_nonempty_empty hne
  have hn := Q.level_le.trans hlast
  have hjs : j ≤ 𝒮.s := by
    rcases hj with h | ⟨h, h'⟩ <;> omega
  have hjn : j ≤ μ₀ + Q.level := by
    rcases hj with h | ⟨h, -⟩ <;> omega
  have hjK : j ≤ K := hjs.trans hseq.level_le
  have hLpos : (0 : ℝ) < 𝒮.L := by exact_mod_cast (by omega : 0 < 𝒮.L)
  have hσ : 0 < 𝒮.scale j := mul_pos (zpow_pos hLpos _) 𝒮.ξ_pos
  have haS : 𝒮.side = ((2 * (𝒮.L : ℤ) ^ (m + K - j) : ℤ) : ℝ) * 𝒮.scale j := by
    have h := unitSide_eq_mul hLpos m K 𝒮.s j hjK
    rw [← hseq.side_eq, ← hseq.spacing_eq] at h
    exact h
  have hB : cubeSide 𝒮 M Q.level =
      (((𝒮.L : ℤ) ^ (μ₀ + Q.level - j) : ℤ) : ℝ) * 𝒮.scale j := by
    have h := pow_mul_scaleSpacing_eq (L := 𝒮.L) μ₀ Q.level j 𝒮.ξ hjn
    rw [← hM] at h
    exact h
  have hB0 : 0 < cubeSide 𝒮 M Q.level := by
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    exact mul_pos hM0 (mul_pos (zpow_pos hLpos _) 𝒮.ξ_pos)
  have hodd : Odd ((𝒮.L : ℤ) ^ (μ₀ + Q.level - j)) :=
    Odd.pow (by exact_mod_cast 𝒮.odd_L)
  have hside : Q.system.setting.side = Q.torusSide := by
    rw [congrArg NestedRegions.side hset]
    rfl
  have haT : Q.system.setting.side =
      ((8 * (𝒮.L : ℤ) ^ (μ₀ + Q.level - j) : ℤ) : ℝ) * 𝒮.scale j := by
    rw [hside]
    show 8 * cubeSide 𝒮 M Q.level = _
    rw [hB]
    push_cast
    ring
  have hlift : torusProj 4 𝒮.side Q.liftedCentre = Q.centre :=
    funext fun μ => coe_circleCentredRep 𝒮.side_pos (Q.centre μ)
  obtain ⟨c, hc, ε, hε, hzc⟩ := Q.centre_mem
  have hz := corner_mem_halfLattice haS hB hodd hc hε (z := Q.liftedCentre)
    (by rw [hlift]; exact hzc)
  have hI : Q.strictPts =
      {x | supNorm (x - torusProj 4 𝒮.side Q.liftedCentre) < cubeSide 𝒮 M Q.level} := by
    rw [hlift]
    rfl
  exact image_lattice_and_cubes 𝒮.side_pos Q.system.setting.side_pos hσ haS haT hB hB0 h2B
    Q.liftedCentre hz Q.strictPts hI Q.system.embed hbij hinj hem
end YangMills.Construction.PartitionCubes.FirstTypeLattice
