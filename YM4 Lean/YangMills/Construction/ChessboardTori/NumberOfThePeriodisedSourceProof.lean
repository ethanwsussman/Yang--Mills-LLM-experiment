import YangMills.Construction.ChessboardTori.ChessboardEstimateOnMirrorGridsProof
import YangMills.Construction.ChessboardTori.NumberOfThePeriodisedSource
import YangMills.Construction.ChessboardTori.TermsOfThePeriodisedSource
import YangMills.Construction.ChessboardTori.ThreeEvaluationRules
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace PeriodizedSourceExpectation
def IsTame (u : AmbientSpace → ℂ) : Prop :=
  (∃ C : ℝ, ∀ x, ‖u x‖ ≤ C) ∧ ChessboardSetup.HasBoundedSupport u
theorem IsTame.add {u u' : AmbientSpace → ℂ} (hu : IsTame u) (hu' : IsTame u') :
    IsTame (u + u') := by
  obtain ⟨⟨C, hC⟩, A, hA, hzero⟩ := hu
  obtain ⟨⟨C', hC'⟩, A', hA', hzero'⟩ := hu'
  refine ⟨⟨C + C', fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hC' x))⟩,
    A ∪ A', hA.union hA', fun x hx => ?_⟩
  simp only [mem_union, not_or] at hx
  simp [hzero x hx.1, hzero' x hx.2]
theorem isTame_zero : IsTame fun _ => 0 :=
  ⟨⟨0, fun _ => by simp⟩, ∅, Bornology.isBounded_empty, fun _ _ => rfl⟩
theorem norm_signedConj (σ : ℤˣ) (z : ℂ) : ‖Conventions.signedConj σ z‖ = ‖z‖ := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardBoundOnReflectionGrids.norm_signedConj <;> assumption
def reflectedTerm {D : ChessboardSetup} (g : ReflectionGrid D) (v : AmbientSpace → ℂ)
    (r : g.reflectionGroup) (x : AmbientSpace) : ℂ :=
  Conventions.signedConj (orientationSign r.1) (v (r.1⁻¹ x))
abbrev periodVec (D : ChessboardSetup) (k : Fin 4 → ℤ) : AmbientSpace :=
  TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k
def periodShift (D : ChessboardSetup) (k : Fin 4 → ℤ) : Equiv.Perm AmbientSpace :=
  Equiv.addRight (periodVec D k)
theorem periodShift_mem (D : ChessboardSetup) (k : Fin 4 → ℤ) :
    periodShift D k ∈ D.periodTranslations :=
  ⟨k, funext fun _ => rfl⟩
theorem periodVec_neg (D : ChessboardSetup) (k : Fin 4 → ℤ) :
    periodVec D (-k) = -periodVec D k := by
  funext μ
  simp [periodVec, TestFunctions.latticeTranslate]
theorem periodVec_add (D : ChessboardSetup) (k k' : Fin 4 → ℤ) :
    periodVec D (k + k') = periodVec D k + periodVec D k' :=
  TestFunctions.latticeTranslate_add _ _ _
theorem orientationSign_periodShift_mul {D : ChessboardSetup} {g : ReflectionGrid D}
    {B S : Set AmbientSpace} (h : g.BlockElementsRepresent B S)
    (hle : D.periodTranslations ≤ g.reflectionGroup)
    (k : Fin 4 → ℤ) {r : Equiv.Perm AmbientSpace} (hr : r ∈ g.reflectionGroup) :
    orientationSign (periodShift D k * r : Equiv.Perm AmbientSpace) = orientationSign r := by
  obtain ⟨⟨w, r₀⟩, ⟨hw, hr₀, hrw⟩, -⟩ := h.1 r hr
  obtain ⟨j, rfl⟩ := hw
  have h1 := (h.2.1 r hr _ ⟨j, rfl⟩ r₀ hr₀ hrw).1
  have h2 := (h.2.1 (periodShift D k * r)
    (g.reflectionGroup.mul_mem (hle (periodShift_mem D k)) hr) (periodVec D (k + j))
    ⟨k + j, rfl⟩ r₀ hr₀ (by
      funext x
      have hx := congrFun hrw x
      simp only [Function.comp, translate] at hx ⊢
      rw [Equiv.Perm.coe_mul, Function.comp, periodVec_add]
      change r x + periodVec D k = _
      rw [hx, add_comm (periodVec D k), add_assoc])).1
  rw [h1, h2]
def periodElem {D : ChessboardSetup} {g : ReflectionGrid D}
    (hle : D.periodTranslations ≤ g.reflectionGroup) (k : Fin 4 → ℤ) :
    g.reflectionGroup := ⟨periodShift D k, hle (periodShift_mem D k)⟩
theorem reflectedTerm_add_periodVec {D : ChessboardSetup} {g : ReflectionGrid D}
    {B S : Set AmbientSpace} (h : g.BlockElementsRepresent B S)
    (hle : D.periodTranslations ≤ g.reflectionGroup)
    (v : AmbientSpace → ℂ) (r : g.reflectionGroup) (x : AmbientSpace) (k : Fin 4 → ℤ) :
    reflectedTerm g v r (x + periodVec D k) = reflectedTerm g v (periodElem hle (-k) * r) x := by
  have hs : orientationSign ((periodElem hle (-k) * r : g.reflectionGroup) :
      Equiv.Perm AmbientSpace) = orientationSign r.1 :=
    orientationSign_periodShift_mul h hle (-k) r.2
  have hi : ((periodElem hle (-k) * r : g.reflectionGroup) : Equiv.Perm AmbientSpace)⁻¹ x =
      r.1⁻¹ (x + periodVec D k) := by
    rw [Subgroup.coe_mul, mul_inv_rev, Equiv.Perm.mul_apply]
    congr 1
    rw [Equiv.Perm.inv_eq_iff_eq]
    change x = x + periodVec D k + periodVec D (-k)
    rw [periodVec_neg]
    simp
  simp only [reflectedTerm, hs, hi]
theorem transport_exp {D : ChessboardSetup} (g : ReflectionGrid D) (hR : D.ExpSmearedRules)
    (r : g.reflectionGroup) {v : AmbientSpace → ℂ} (hv : IsTame v)
    (hv' : IsTame (fun y => v (r.1⁻¹ y))) :
    g.transport r (fun U => Complex.exp (D.smeared v U)) =
      fun U => Complex.exp (D.smeared (reflectedTerm g v r) U) := by
  have hinv : invMap (g.toLatticeSym r).toFun = fun y => r.1⁻¹ y := by
    funext y
    apply r.1.injective
    have h := Function.invFun_eq (f := (r.1 : AmbientSpace → AmbientSpace)) (b := y)
      ⟨r.1⁻¹ y, by simp⟩
    have h' : r.1 (r.1⁻¹ y) = y := by simp
    exact h.trans h'.symm
  have h1 := (hR (g.toLatticeSym r) v v hv.1 hv.2 hv.1 hv.2).1
  have h2 := (hR (g.toLatticeSym r) (fun y => v (r.1⁻¹ y)) (fun y => v (r.1⁻¹ y))
    hv'.1 hv'.2 hv'.1 hv'.2).2.1
  have hcomp : v ∘ invMap (g.toLatticeSym r).toFun = fun y => v (r.1⁻¹ y) := by
    rw [hinv]
    rfl
  rw [hcomp] at h1
  funext U
  simp only [ReflectionGrid.transport, Conventions.signedConjFun]
  rw [h1]
  by_cases hσ : orientationSign r.1 = 1
  · have ht : reflectedTerm g v r = fun y => v (r.1⁻¹ y) := by
      funext y
      simp [reflectedTerm, Conventions.signedConj, hσ]
    rw [ht]
    simp [Conventions.signedConj, hσ]
  · have ht : reflectedTerm g v r = fun y => starRingEnd ℂ (v (r.1⁻¹ y)) := by
      funext y
      simp [reflectedTerm, Conventions.signedConj, hσ]
    rw [ht]
    simpa [Conventions.signedConj, hσ] using congrFun h2 U
theorem prod_exp_smeared {D : ChessboardSetup} {ι : Type*} (r : D.LatticeSym)
    (hR : D.ExpSmearedRules) (T : Finset ι) (u : ι → AmbientSpace → ℂ)
    (hu : ∀ i ∈ T, IsTame (u i)) :
    IsTame (fun y => ∑ i ∈ T, u i y) ∧
      ∀ U, ∏ i ∈ T, Complex.exp (D.smeared (u i) U) =
        Complex.exp (D.smeared (fun y => ∑ i ∈ T, u i y) U) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using isTame_zero, fun U => ?_⟩
    simp [ChessboardSetup.smeared, InfiniteLattice.smearedEnergy]
  | insert i T hi ih =>
    obtain ⟨ht, hp⟩ := ih fun j hj => hu j (Finset.mem_insert_of_mem hj)
    have hui := hu i (Finset.mem_insert_self i T)
    have hsum : (fun y => ∑ j ∈ insert i T, u j y) = u i + fun y => ∑ j ∈ T, u j y := by
      funext y
      simp [Finset.sum_insert hi]
    rw [hsum]
    refine ⟨hui.add ht, fun U => ?_⟩
    rw [Finset.prod_insert hi, hp U]
    exact congrFun (hR r _ _ hui.1 hui.2 ht.1 ht.2).2.2 U
theorem isBounded_block {D : ChessboardSetup} (g : ReflectionGrid D) {B : Set AmbientSpace}
    (hB : B ∈ g.blocks) : Bornology.IsBounded B := by
  obtain ⟨k, rfl⟩ := hB
  refine (isCompact_Icc (a := fun μ => g.origin μ + g.cellSide * k μ)
    (b := fun μ => g.origin μ + g.cellSide * k μ + PeriodicLattice.torusSide D.L D.m)).isBounded.subset ?_
  intro x hx
  exact ⟨fun μ => by have := (hx μ).1; linarith, fun μ => by have := (hx μ).2; linarith⟩
end PeriodizedSourceExpectation
open PeriodizedSourceExpectation in
theorem PeriodizedSourceExpectation.proof (hE : GridBasicProperties.Statement)
    (hT : PeriodizedSourceTerms.Statement) (hC : CellsBlocksAndSigns.Statement)
    (hR : LiftingRules.Statement) : PeriodizedSourceExpectation.Statement := by
  classical
  intro D g hside S hS v Q hvb hvQ hQc hQS hQd
  obtain ⟨-, -, hexp, hform, -, -, hbig⟩ := hE D g
  obtain ⟨-, -, -, -, -, -, hsimple, -⟩ := hform
  obtain ⟨hind, -, -⟩ := hbig hside
  have hle : D.periodTranslations ≤ g.reflectionGroup := hind.1
  obtain ⟨-, hblocks⟩ := (hC D g).2 hside
  have hsub := (hT D g hside S hS v Q hvb hvQ hQc hQS hQd).2.1
  have hside_pos : 0 < g.cellSide := zpow_pos (by linarith [D.one_lt_factor]) _
  have hℓ : 0 < PeriodicLattice.torusSide D.L D.m := by linarith
  have hrep0 := ((hblocks (g.block 0) ⟨0, rfl⟩).2 S hS).1
  refine ⟨fun x k => ?_, fun B hB => ?_⟩
  · have h1 : ∀ r : g.reflectionGroup, reflectedTerm g v r (x + periodVec D k) =
        reflectedTerm g v (periodElem hle (-k) * r) x :=
      fun r => reflectedTerm_add_periodVec hrep0 hle v r x k
    have h2 := finsum_comp_equiv (Equiv.mulLeft (periodElem hle (-k)))
      (f := fun r => reflectedTerm g v r x)
    calc (∑ᶠ r : g.reflectionGroup, reflectedTerm g v r (x + periodVec D k))
        = ∑ᶠ r : g.reflectionGroup, reflectedTerm g v (periodElem hle (-k) * r) x :=
          finsum_congr h1
      _ = ∑ᶠ r : g.reflectionGroup, reflectedTerm g v r x := h2
  · obtain ⟨hcells, -⟩ := (hblocks B hB)
    obtain ⟨hrep, hhalf⟩ := (hblocks B hB).2 S hS
    have hfin : (g.cellsWithin B).Finite := by
      refine Set.finite_of_ncard_pos ?_
      have h := hhalf.1
      have hpos : 0 < g.cellsAcross ^ 4 := pow_pos (div_pos hℓ hside_pos) 4
      rw [← h] at hpos
      exact_mod_cast hpos
    have hc : ∀ S' ∈ g.cellsWithin B, (g.mover S S').1 '' S = S' := fun S' hS' =>
      Classical.epsilon_spec (p := fun r : g.reflectionGroup => r.1 '' S = S')
        (hsimple S hS S' hS'.1).exists
    have hBb := isBounded_block g hB
    obtain ⟨C, hCv⟩ := hvb
    have hvtame : IsTame v :=
      ⟨⟨C, hCv⟩, Q, hQc.isBounded, hvQ⟩
    have hvan : ∀ S' ∈ g.cellsWithin B, ∀ y, y ∉ B → v ((g.mover S S').1⁻¹ y) = 0 := by
      intro S' hS' y hy
      refine hvQ _ fun hq => hy (hS'.2 ?_)
      rw [← hc S' hS']
      exact ⟨_, interior_subset (hQS hq), by simp⟩
    have htame' : ∀ S' ∈ g.cellsWithin B, IsTame (fun y => v ((g.mover S S').1⁻¹ y)) :=
      fun S' hS' => ⟨⟨C, fun _ => hCv _⟩, B, hBb, hvan S' hS'⟩
    have htame : ∀ S' ∈ g.cellsWithin B, IsTame (reflectedTerm g v (g.mover S S')) :=
      fun S' hS' =>
      ⟨⟨C, fun y => by rw [reflectedTerm, norm_signedConj]; exact hCv _⟩, B, hBb, fun y hy => by
        rw [reflectedTerm, hvan S' hS' y hy]
        simp [Conventions.signedConj]⟩
    set T := hfin.toFinset with hTdef
    have hTmem : ∀ S', S' ∈ T ↔ S' ∈ g.cellsWithin B := fun S' => hfin.mem_toFinset
    obtain ⟨hwt, hwp⟩ := prod_exp_smeared (g.toLatticeSym 1) (hexp) T
      (fun S' => reflectedTerm g v (g.mover S S')) fun S' h => htame S' ((hTmem S').mp h)
    set w : AmbientSpace → ℂ := fun y => ∑ S' ∈ T, reflectedTerm g v (g.mover S S') y with hw
    have hfun : (fun U => ∏ᶠ S' ∈ g.cellsWithin B,
        g.transportTo S S' (fun U' => Complex.exp (D.smeared v U')) U) =
        fun U => Complex.exp (D.smeared w U) := by
      funext U
      rw [finprod_mem_eq_finite_toFinset_prod _ hfin, ← hwp U]
      refine Finset.prod_congr rfl fun S' hS' => ?_
      exact congrFun (transport_exp g hexp _ hvtame (htame' S' ((hTmem S').mp hS'))) U
    have hper : D.periodize w = fun x => ∑ᶠ r : g.reflectionGroup, reflectedTerm g v r x := by
      funext x
      change (∑ᶠ k : Fin 4 → ℤ, w (x + periodVec D k)) = _
      have hwk : ∀ k : Fin 4 → ℤ, w (x + periodVec D k) =
          ∑ S' ∈ T, reflectedTerm g v (periodElem hle (-k) * g.mover S S') x := fun k =>
        Finset.sum_congr rfl fun S' _ => reflectedTerm_add_periodVec hrep0 hle v _ x k
      rw [finsum_congr hwk]
      by_cases hex : ∃ r₀ : g.reflectionGroup, reflectedTerm g v r₀ x ≠ 0
      · obtain ⟨r₀, h₀⟩ := hex
        have hone : ∀ r : g.reflectionGroup, reflectedTerm g v r x ≠ 0 → r = r₀ :=
          fun r hr => hsub x hr h₀
        obtain ⟨⟨w₀, ρ⟩, ⟨hw₀, hρ, hr₀⟩, huniq⟩ := hrep.1 r₀.1 r₀.2
        obtain ⟨j, rfl⟩ := hw₀
        have hS₀ : ρ '' S ∈ g.cellsWithin B := hρ.2
        have hcρ : (g.mover S (ρ '' S)).1 = ρ := by
          have := (hsimple S hS _ hS₀.1).unique (hc _ hS₀) (y₂ := ⟨ρ, hρ.1⟩) rfl
          exact congrArg Subtype.val this
        have hvinj : ∀ k k' : Fin 4 → ℤ, periodVec D k = periodVec D k' → k = k' := by
          intro k k' h
          funext μ
          have := congrFun h μ
          simp only [periodVec, TestFunctions.latticeTranslate] at this
          exact_mod_cast mul_left_cancel₀ hℓ.ne' this
        have hinj : ∀ S' ∈ T, ∀ k : Fin 4 → ℤ, periodElem hle (-k) * g.mover S S' = r₀ →
            S' = ρ '' S ∧ k = -j := by
          intro S' hS' k he
          have hS'B := (hTmem S').mp hS'
          have hpair := huniq (periodVec D (-k), (g.mover S S').1) ⟨⟨-k, rfl⟩,
            ⟨(g.mover S S').2, by rw [hc S' hS'B]; exact hS'B⟩, by
              rw [← he]; rfl⟩
          have hp1 : periodVec D (-k) = periodVec D j := congrArg Prod.fst hpair
          have hp2 : (g.mover S S').1 = ρ := congrArg Prod.snd hpair
          refine ⟨?_, ?_⟩
          · rw [← hp2, hc S' hS'B]
          · have := hvinj _ _ hp1
            rw [← this, neg_neg]
        have hr₀' : periodElem hle (- -j) * g.mover S (ρ '' S) = r₀ := by
          apply Subtype.ext
          apply Equiv.ext
          intro y
          have hy := congrFun hr₀ y
          rw [Subgroup.coe_mul, hcρ, neg_neg]
          exact hy.symm
        have hS₀T : ρ '' S ∈ T := (hTmem _).mpr hS₀
        rw [finsum_eq_single (fun r : g.reflectionGroup => reflectedTerm g v r x) r₀
            (fun r hr => by_contra fun h => hr (hone r h)),
          finsum_eq_single _ (-j) (fun k hk => Finset.sum_eq_zero fun S' hS' =>
            by_contra fun h => hk (hinj S' hS' k (hone _ h)).2),
          Finset.sum_eq_single (ρ '' S)
            (fun S' hS' hne => by_contra fun h => hne (hinj S' hS' _ (hone _ h)).1)
            (fun hn => absurd hS₀T hn), hr₀']
      · have hz : ∀ r : g.reflectionGroup, reflectedTerm g v r x = 0 := fun r => by
          by_contra h
          exact hex ⟨r, h⟩
        rw [finsum_eq_zero_of_forall_eq_zero hz,
          finsum_eq_zero_of_forall_eq_zero fun k => Finset.sum_eq_zero fun S' _ => hz _]
    have hfinal := ((hR D).2.1 w hwt.1 hwt.2).2.2.2.1
    rw [hper] at hfinal
    rw [hfun]
    exact hfinal
end YangMills.Construction.ChessboardTori
end
