import YangMills.Construction.ChessboardTori.CellsBoxesAndParities
import YangMills.Construction.ChessboardTori.GroupCoordinateByCoordinate
import YangMills.Construction.ChessboardTori.GroupOnTheTorusAsAQuotient
import YangMills.Construction.ChessboardTori.InducedIsometriesOfTheTorus
import YangMills.Construction.MirrorGridsOfEverySide.GroupOnTheCellsOfTheTorusAtEveryMirrorGrid
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open InfiniteLattice (AmbientSpace)
open ChessboardTori (ReflectionGrid orientationSign translate)
namespace MirrorGridsAllSides
namespace TorusGroupOnCells
theorem orientationSign_translate (v : AmbientSpace) :
    orientationSign (ChessboardTori.translate v) = 1 := by
  have hid : ChessboardTori.linearComponent (ChessboardTori.translate v) = LinearMap.id := by
    obtain ⟨w, hw⟩ : ChessboardTori.HasLinearComponent (ChessboardTori.translate v)
        (ChessboardTori.linearComponent (ChessboardTori.translate v)) :=
      Classical.epsilon_spec ⟨LinearMap.id, v, fun x => by simp [ChessboardTori.translate]⟩
    have hvw : v = w := by simpa [ChessboardTori.translate] using hw 0
    refine LinearMap.ext fun x => ?_
    have h := hw x
    rw [← hvw] at h
    simpa [ChessboardTori.translate] using h.symm
  simp [orientationSign, hid]
end TorusGroupOnCells
open TorusGroupOnCells in
theorem allGridsTorusGroupActsOnCells
    (h₁ : ChessboardTori.TorusInducedSymmetries.Statement)
    (h₂ : ChessboardTori.TorusReflectionGroup.Statement)
    (h₃ : ChessboardTori.ReflectionGroupCoordinates.Statement)
    (h₄ : ChessboardTori.CellsBlocksAndSigns.Statement) :
    AllGridsTorusGroupActsOnCells := by
  intro D g _ hℓ
  obtain ⟨-, hnormal, hind, hsame⟩ := h₁ D g hℓ
  obtain ⟨⟨φ, -, -, himg⟩, hcard, hiso, hsgn, hlat, -, hsimple, -⟩ := h₂ D g hℓ
  obtain ⟨-, -, -, hmul, -⟩ := h₃ D g
  have hhalf := (((h₄ D g).2 hℓ).2 (g.block 0) ⟨0, rfl⟩).2 (g.cell 0) ⟨0, rfl⟩ |>.2
  obtain ⟨-, -, hgcard, hodd⟩ := hhalf
  have hpar : ∀ r' ∈ g.inducedTorusMaps, g.HasTorusParity r' (g.torusSign r') := by
    intro r' hr' r hr
    obtain ⟨s, hsG, hs⟩ := hr'
    have hspec : D.proj ∘ (g.inducingElement r').1 = r' ∘ D.proj :=
      Classical.epsilon_spec (p := fun r : g.reflectionGroup =>
        D.proj ∘ r.1 = r' ∘ D.proj) ⟨⟨s, hsG⟩, hs⟩
    exact hsgn r.1 r.2 _ (g.inducingElement r').2 r' hr hspec
  have hconj : ∀ (u : g.reflectionGroup) (t : g.reflectionGroup), t.1 ∈ D.periodTranslations →
      (u * t * u⁻¹).1 ∈ D.periodTranslations := by
    intro u t ht
    have h := hnormal.conj_mem t (Subgroup.mem_subgroupOf.mpr ht) u
    exact Subgroup.mem_subgroupOf.mp h
  refine ⟨?_, ?_, ?_, hpar, ?_, hsimple, hcard, ?_⟩
  · intro r hr
    obtain ⟨r', hr', hI⟩ := hind r hr
    exact ⟨⟨r', hI, (hlat r' ⟨r, hr, hr'⟩).1⟩, hr'.symm⟩
  · intro r s r' s' hr hs
    rw [hsame r.1 r.2 s.1 s.2 r' s' hr.symm hs.symm]
    constructor
    · intro h
      have hmem : (s⁻¹ * r : g.reflectionGroup).1 ∈ D.periodTranslations := h
      have ht := hconj s (s⁻¹ * r) hmem
      obtain ⟨k, hk⟩ := ht
      refine ⟨s * (s⁻¹ * r) * s⁻¹, ?_, by group, k, hk⟩
      change orientationSign ((s * (s⁻¹ * r) * s⁻¹).1 : AmbientSpace → AmbientSpace) = 1
      rw [hk]
      exact orientationSign_translate _
    · rintro ⟨t, -, rfl, k, hk⟩
      have ht : t.1 ∈ D.periodTranslations := ⟨k, hk⟩
      have h := hconj s⁻¹ t ht
      have e : s⁻¹ * (t * s) = s⁻¹ * t * s⁻¹⁻¹ := by group
      change (s⁻¹ * (t * s) : g.reflectionGroup).1 ∈ D.periodTranslations
      rw [e]
      exact h
  · exact ⟨φ.range, himg⟩
  · intro r' hr' s' hs'
    obtain ⟨r, hrG, hr⟩ := id hr'
    obtain ⟨s, hsG, hs⟩ := id hs'
    have hcomp : D.proj ∘ (r * s : Equiv.Perm AmbientSpace) = (r' ∘ s') ∘ D.proj := by
      funext x
      have e₁ := congrFun hr (s x)
      have e₂ := congrFun hs x
      simp only [Function.comp_apply, Equiv.Perm.coe_mul] at e₁ e₂ ⊢
      rw [e₁, e₂]
    have hmem : r' ∘ s' ∈ g.inducedTorusMaps :=
      ⟨r * s, g.reflectionGroup.mul_mem hrG hsG, hcomp⟩
    rw [← hpar _ hmem ⟨r * s, g.reflectionGroup.mul_mem hrG hsG⟩ hcomp, ← hpar _ hr' ⟨r, hrG⟩ hr,
      ← hpar _ hs' ⟨s, hsG⟩ hs]
    exact hmul r hrG s hsG
  · intro ε
    have hn : 0 < g.cellsAcross := by
      have hs : 0 < g.cellSide := zpow_pos (by linarith [D.one_lt_factor]) _
      exact div_pos (by linarith) hs
    have hn4 : 0 < g.cellsAcross ^ 4 := by positivity
    have hfin : g.inducedTorusMaps.Finite := by
      by_contra hinf
      have h0 : g.inducedTorusMaps.ncard = 0 := Set.Infinite.ncard hinf
      rw [h0] at hgcard
      simp only [Nat.cast_zero] at hgcard
      linarith
    have hcount : ∀ ε : ℤˣ, Nat.card {r' // r' ∈ g.inducedTorusMaps ∧ g.torusSign r' = ε} =
        ({r' ∈ g.inducedTorusMaps | g.torusSign r' = ε}).ncard := fun ε =>
      Nat.card_coe_set_eq {r' | r' ∈ g.inducedTorusMaps ∧ g.torusSign r' = ε}
    rw [hcount ε]
    change _ = g.cellsAcross ^ 4 / 2
    rcases Int.units_eq_one_or ε with rfl | rfl
    · have hunion : {r' ∈ g.inducedTorusMaps | g.torusSign r' = 1} ∪
          {r' ∈ g.inducedTorusMaps | g.torusSign r' = -1} = g.inducedTorusMaps := by
        ext r'
        constructor
        · rintro (h | h) <;> exact h.1
        · intro h
          rcases Int.units_eq_one_or (g.torusSign r') with e | e
          · exact Or.inl ⟨h, e⟩
          · exact Or.inr ⟨h, e⟩
      have hdisj : Disjoint {r' ∈ g.inducedTorusMaps | g.torusSign r' = 1}
          {r' ∈ g.inducedTorusMaps | g.torusSign r' = -1} := by
        rw [Set.disjoint_left]
        rintro r' ⟨-, e₁⟩ ⟨-, e₂⟩
        rw [e₁] at e₂
        exact absurd e₂ (by decide)
      have hsum := Set.ncard_union_eq hdisj (hfin.subset (fun _ h => h.1))
        (hfin.subset (fun _ h => h.1))
      rw [hunion] at hsum
      have hsumR : (g.inducedTorusMaps.ncard : ℝ) =
          (({r' ∈ g.inducedTorusMaps | g.torusSign r' = 1}).ncard : ℝ) +
            (({r' ∈ g.inducedTorusMaps | g.torusSign r' = -1}).ncard : ℝ) := by
        exact_mod_cast hsum
      linarith
    · exact hodd
end MirrorGridsAllSides
end YangMills.Construction
end
