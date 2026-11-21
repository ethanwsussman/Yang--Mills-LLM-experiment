import YangMills.Construction.ChessboardTori.GroupCoordinateByCoordinate
import YangMills.Construction.ChessboardTori.InducedIsometriesOfTheTorus
import YangMills.Construction.Lattice.LatticeIsometriesAsMapsOfPairsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
open TorusMetric
namespace TorusInducedSymmetries
variable {D : ChessboardSetup}
def signFlip (ε : Fin 4 → ℤ) (v : AmbientSpace) : AmbientSpace := fun μ => (ε μ : ℝ) * v μ
def IsSignVector (ε : Fin 4 → ℤ) : Prop := ∀ μ, ε μ = 1 ∨ ε μ = -1
theorem signFlip_add (ε : Fin 4 → ℤ) (v w : AmbientSpace) :
    signFlip ε (v + w) = signFlip ε v + signFlip ε w := by
  funext μ
  simp [signFlip, mul_add]
theorem signFlip_latticeTranslate (ε : Fin 4 → ℤ) (ℓ : ℝ) (k : Fin 4 → ℤ) :
    signFlip ε (TestFunctions.latticeTranslate ℓ k) = TestFunctions.latticeTranslate ℓ (ε * k) := by
  funext μ
  simp only [signFlip, TestFunctions.latticeTranslate, Pi.mul_apply, Int.cast_mul]
  ring
theorem signFlip_signFlip {ε : Fin 4 → ℤ} (hε : IsSignVector ε) (v : AmbientSpace) :
    signFlip ε (signFlip ε v) = v := by
  funext μ
  rcases hε μ with h | h <;> simp [signFlip, h]
theorem euclidNormVec_signFlip {ε : Fin 4 → ℤ} (hε : IsSignVector ε) (v : AmbientSpace) :
    euclidNormVec (signFlip ε v) = euclidNormVec v := by
  unfold euclidNormVec
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rcases hε μ with h | h <;> simp [signFlip, h]
theorem exists_signVector_of_isProductOfCoordMaps {g : ReflectionGrid D}
    {r : AmbientSpace → AmbientSpace} (h : g.IsProductOfCoordMaps r) :
    ∃ ε : Fin 4 → ℤ, IsSignVector ε ∧ ∀ x v : AmbientSpace, r (x + v) = r x + signFlip ε v := by
  have hμ : ∀ μ, ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
      ∀ x v : AmbientSpace, r (x + v) μ = r x μ + (e : ℝ) * v μ := by
    intro μ
    rcases h μ with ⟨t, ht⟩ | ⟨k, hk⟩
    · refine ⟨1, Or.inl rfl, fun x v => ?_⟩
      have h1 := ht (x + v)
      have h2 := ht x
      simp only [ReflectionGrid.coordShift, Pi.add_apply] at h1 h2
      push_cast
      linarith
    · refine ⟨-1, Or.inr rfl, fun x v => ?_⟩
      have h1 := hk (x + v)
      have h2 := hk x
      simp only [ReflectionGrid.coordReflect, Pi.add_apply] at h1 h2
      push_cast
      linarith
  choose ε hε hr using hμ
  exact ⟨ε, hε, fun x v => funext fun μ => by simpa [signFlip] using hr μ x v⟩
theorem torusProj_sub (ℓ : ℝ) (x y : AmbientSpace) :
    torusProj ℓ (x - y) = torusProj ℓ x - torusProj ℓ y := by apply _root_.YangMills.Construction.AffineTorusIsometries.torusProj_sub' <;> assumption
theorem torusProj_signFlip_eq {ℓ : ℝ} (ε : Fin 4 → ℤ) {z w : AmbientSpace}
    (h : torusProj ℓ z = torusProj ℓ w) :
    torusProj ℓ (signFlip ε z) = torusProj ℓ (signFlip ε w) := by
  obtain ⟨k, rfl⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq h
  rw [signFlip_add, signFlip_latticeTranslate, TestFunctions.torusProj_add_latticeTranslate]
theorem torusEuclidNorm_torusProj_signFlip {ℓ : ℝ} {ε : Fin 4 → ℤ} (hε : IsSignVector ε)
    (w : AmbientSpace) :
    torusEuclidNorm (torusProj ℓ (signFlip ε w)) = torusEuclidNorm (torusProj ℓ w) := by
  unfold torusEuclidNorm
  congr 1
  ext a
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨signFlip ε z, ?_, euclidNormVec_signFlip hε z⟩
    have h := torusProj_signFlip_eq ε (show torusProj ℓ z = torusProj ℓ (signFlip ε w) from hz)
    rw [signFlip_signFlip hε] at h
    exact h
  · rintro ⟨z, hz, rfl⟩
    exact ⟨signFlip ε z, torusProj_signFlip_eq ε (show torusProj ℓ z = torusProj ℓ w from hz),
      euclidNormVec_signFlip hε z⟩
theorem eq_translate_of_torusProj_eq {g : ReflectionGrid D} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {ρ : AmbientSpace → AmbientSpace}
    (h : g.IsProductOfCoordMaps ρ) (hc : ∀ x, torusProj ℓ (ρ x) = torusProj ℓ x) :
    ∃ k : Fin 4 → ℤ, ρ = translate (TestFunctions.latticeTranslate ℓ k) := by
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq (hc 0)
  refine ⟨k, funext fun x => funext fun μ => ?_⟩
  have h3 := congrFun hk μ
  simp only [TestFunctions.latticeTranslate, Pi.zero_apply, Pi.add_apply, zero_add] at h3
  rcases h μ with ⟨t, ht⟩ | ⟨j, hj⟩
  · have h1 := ht x
    have h2 := ht 0
    simp only [ReflectionGrid.coordShift, Pi.zero_apply] at h1 h2
    simp only [translate, TestFunctions.latticeTranslate, Pi.add_apply]
    linarith
  · exfalso
    obtain ⟨k', hk'⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq (hc fun _ => ℓ / 4)
    have h4 := congrFun hk' μ
    have h1 := hj fun _ => ℓ / 4
    have h2 := hj 0
    simp only [ReflectionGrid.coordReflect, Pi.zero_apply] at h1 h2
    simp only [TestFunctions.latticeTranslate, Pi.add_apply] at h4
    have h5 : ℓ * (2 * ((k' μ : ℝ) - (k μ : ℝ)) + 1) = 0 := by linarith
    have h6 : 2 * ((k' μ : ℝ) - (k μ : ℝ)) + 1 = 0 :=
      (mul_eq_zero.mp h5).resolve_left hℓ.ne'
    have h7 : 2 * (k' μ - k μ) + 1 = 0 := by exact_mod_cast h6
    omega
theorem mem_periodTranslations {r : Equiv.Perm AmbientSpace} :
    r ∈ D.periodTranslations ↔ ∃ k : Fin 4 → ℤ, (r : AmbientSpace → AmbientSpace) =
      translate (TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k) := Iff.rfl
theorem exists_torusSide_eq {g : ReflectionGrid D} (h : g.TorusSideCells) (hpos : 0 < g.cellSide) :
    ∃ c : ℤ, PeriodicLattice.torusSide D.L D.m = 2 * g.cellSide * (c : ℝ) := by
  obtain ⟨-, hcells, ⟨c, hc⟩, -⟩ := h
  refine ⟨c, ?_⟩
  unfold ReflectionGrid.cellsAcross at hcells
  rw [hc] at hcells
  push_cast at hcells
  rw [div_eq_iff hpos.ne'] at hcells
  rw [hcells]
  ring
theorem statement_proof (h₁ : ReflectionGroupCoordinates.Statement)
    (h₂ : ReflectionGridArithmetic.Statement) : TorusInducedSymmetries.Statement := by
  intro D g hside
  obtain ⟨hcw, -, -, -, -, -, -, htr⟩ := h₁ D g
  have hpos : 0 < g.cellSide :=
    zpow_pos (by linarith [D.one_lt_factor]) _
  obtain ⟨c, hc⟩ := exists_torusSide_eq (((h₂ D).2.2.2 g).2 hside).1 hpos
  have hℓ : 0 < PeriodicLattice.torusSide D.L D.m := by linarith
  have hmem : ∀ (k : Fin 4 → ℤ) (r : Equiv.Perm AmbientSpace), (r : AmbientSpace → AmbientSpace) =
      translate (TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k) →
      r ∈ g.reflectionGroup := by
    intro k r hr
    obtain ⟨s, hs, hs', -⟩ := htr fun μ => c * k μ
    have e : s = r := by
      apply DFunLike.coe_injective
      rw [hs', hr]
      congr 1
      funext μ
      simp only [TestFunctions.latticeTranslate, hc]
      push_cast
      ring
    exact e ▸ hs
  refine ⟨fun r hr => ?_, ⟨fun n hn x => ?_⟩, fun r hr => ?_, fun r hr s hs r' s' hr' hs' => ?_⟩
  · obtain ⟨k, hk⟩ := mem_periodTranslations.mp hr
    exact hmem k r hk
  · rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := mem_periodTranslations.mp hn
    obtain ⟨ε, -, hx⟩ := exists_signVector_of_isProductOfCoordMaps (hcw x.1 x.2)
    refine mem_periodTranslations.mpr ⟨ε * k, funext fun y => ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hk]
    change x.1 (x.1⁻¹ y + _) = y + _
    rw [hx, signFlip_latticeTranslate, show x.1 (x.1⁻¹ y) = y by simp]
  · obtain ⟨ε, hε, hx⟩ := exists_signVector_of_isProductOfCoordMaps (hcw r hr)
    have hind : ∀ x y : AmbientSpace, torusProj (PeriodicLattice.torusSide D.L D.m) x =
        torusProj (PeriodicLattice.torusSide D.L D.m) y →
        torusProj (PeriodicLattice.torusSide D.L D.m) (r x) =
          torusProj (PeriodicLattice.torusSide D.L D.m) (r y) := by
      intro x y h
      obtain ⟨k, rfl⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq h
      rw [hx, signFlip_latticeTranslate, TestFunctions.torusProj_add_latticeTranslate]
    have hcomp : ∀ x : AmbientSpace, torusProj (PeriodicLattice.torusSide D.L D.m)
        (r (TestFunctions.liftPoint (torusProj (PeriodicLattice.torusSide D.L D.m) x))) =
        torusProj (PeriodicLattice.torusSide D.L D.m) (r x) :=
      fun x => hind _ _ (TestFunctions.torusProj_liftPoint _)
    refine ⟨fun u => torusProj (PeriodicLattice.torusSide D.L D.m)
      (r (TestFunctions.liftPoint (ℓ := PeriodicLattice.torusSide D.L D.m) u)),
      funext fun x => (hcomp x).symm, fun u v => ?_⟩
    obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
    obtain ⟨y, rfl⟩ := TestFunctions.torusProj_surjective _ v
    have e : r x - r y = signFlip ε (x - y) := by
      have h := hx y (x - y)
      rw [add_sub_cancel] at h
      rw [h]
      simp
    change torusEuclidNorm (torusProj (PeriodicLattice.torusSide D.L D.m)
        (r (TestFunctions.liftPoint _)) -
      torusProj (PeriodicLattice.torusSide D.L D.m) (r (TestFunctions.liftPoint _))) =
      torusEuclidNorm (torusProj (PeriodicLattice.torusSide D.L D.m) x -
        torusProj (PeriodicLattice.torusSide D.L D.m) y)
    rw [hcomp, hcomp, ← torusProj_sub, ← torusProj_sub, e,
      torusEuclidNorm_torusProj_signFlip hε]
  · have hcr : ∀ x : AmbientSpace, r' (torusProj (PeriodicLattice.torusSide D.L D.m) x) =
        torusProj (PeriodicLattice.torusSide D.L D.m) (r x) := fun x => (congrFun hr' x).symm
    have hcs : ∀ x : AmbientSpace, s' (torusProj (PeriodicLattice.torusSide D.L D.m) x) =
        torusProj (PeriodicLattice.torusSide D.L D.m) (s x) := fun x => (congrFun hs' x).symm
    constructor
    · intro e
      have hinv : s⁻¹ ∈ g.reflectionGroup := g.reflectionGroup.inv_mem hs
      obtain ⟨ε, -, hx⟩ := exists_signVector_of_isProductOfCoordMaps (hcw _ hinv)
      have hcg : ∀ x : AmbientSpace, torusProj (PeriodicLattice.torusSide D.L D.m) ((s⁻¹ * r) x) =
          torusProj (PeriodicLattice.torusSide D.L D.m) x := by
        intro x
        have h : torusProj (PeriodicLattice.torusSide D.L D.m) (r x) =
            torusProj (PeriodicLattice.torusSide D.L D.m) (s x) := by rw [← hcr, ← hcs, e]
        obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq h
        rw [Equiv.Perm.mul_apply, hk, hx, show s⁻¹ (s x) = x by simp, signFlip_latticeTranslate,
          TestFunctions.torusProj_add_latticeTranslate]
      exact mem_periodTranslations.mpr
        (eq_translate_of_torusProj_eq hℓ (hcw _ (g.reflectionGroup.mul_mem hinv hr)) hcg)
    · intro h
      obtain ⟨k, hk⟩ := mem_periodTranslations.mp h
      obtain ⟨ε, -, hx⟩ := exists_signVector_of_isProductOfCoordMaps (hcw s hs)
      have hr2 : ∀ x : AmbientSpace, r x = s x + TestFunctions.latticeTranslate
          (PeriodicLattice.torusSide D.L D.m) (ε * k) := by
        intro x
        have e : r x = s ((s⁻¹ * r) x) := by simp
        rw [e, hk]
        change s (x + _) = _
        rw [hx, signFlip_latticeTranslate]
      funext u
      obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
      rw [hcr, hcs, hr2, TestFunctions.torusProj_add_latticeTranslate]
end TorusInducedSymmetries
end YangMills.Construction.ChessboardTori
end
