import YangMills.Construction.ClusterExpansionOfAStep.HullsOfHotLumps
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace TorusFields
open BlockAverages
section HolonomyWords
theorem re_unitQuaternion_inv (q : UnitQuaternion) :
    ((q⁻¹ : UnitQuaternion) : ℍ[ℝ]).re = (q : ℍ[ℝ]).re := by
  rw [coe_inv_unitQuaternion]
  simp
theorem re_reversed_word_left (A B C D : UnitQuaternion) :
    ((A⁻¹ * B * C * D⁻¹ : UnitQuaternion) : ℍ[ℝ]).re =
      ((A * D * C⁻¹ * B⁻¹ : UnitQuaternion) : ℍ[ℝ]).re := by
  have e : A⁻¹ * B * C * D⁻¹ = A⁻¹ * (A * D * C⁻¹ * B⁻¹)⁻¹ * A⁻¹⁻¹ := by group
  rw [e, re_unitQuaternion_conj, re_unitQuaternion_inv]
theorem re_reversed_word_right (A B C D : UnitQuaternion) :
    ((C * D⁻¹ * A⁻¹ * B : UnitQuaternion) : ℍ[ℝ]).re =
      ((A * D * C⁻¹ * B⁻¹ : UnitQuaternion) : ℍ[ℝ]).re := by
  have e : C * D⁻¹ * A⁻¹ * B = B⁻¹ * (A * D * C⁻¹ * B⁻¹)⁻¹ * B⁻¹⁻¹ := by group
  rw [e, re_unitQuaternion_conj, re_unitQuaternion_inv]
theorem re_cyclic_word (A B C D : UnitQuaternion) :
    ((C⁻¹ * B⁻¹ * A * D : UnitQuaternion) : ℍ[ℝ]).re =
      ((A * D * C⁻¹ * B⁻¹ : UnitQuaternion) : ℍ[ℝ]).re := by
  have e : C⁻¹ * B⁻¹ * A * D = (A * D)⁻¹ * (A * D * C⁻¹ * B⁻¹) * (A * D)⁻¹⁻¹ := by group
  rw [e, re_unitQuaternion_conj]
end HolonomyWords
variable {n : ℕ}
theorem plaquetteEnergy_symm (U : TorusField n) (y : TorusSite n) (a b : Fin 4) :
    plaquetteEnergy U y a b = plaquetteEnergy U y b a := by
  unfold plaquetteEnergy
  have e : holonomy U y b a = (holonomy U y a b)⁻¹ := by
    unfold holonomy
    group
  rw [e, re_unitQuaternion_inv]
variable (g : TorusIsometry)
def TorusIsometry.imageAxis (k : Fin 4) : Fin 4 := g.axisPerm.symm k
theorem mapSite_add_unitStep_of_pos (x : TorusSite n) (k : Fin 4)
    (hs : g.axisSign (g.imageAxis k) = 1) :
    g.mapSite (x + unitStep n k) = g.mapSite x + unitStep n (g.imageAxis k) := by
  have hs' : g.axisSign (g.axisPerm.symm k) = 1 := hs
  funext i
  by_cases hi : i = g.imageAxis k
  · subst hi
    simp [TorusIsometry.mapSite, TorusIsometry.imageAxis, unitStep, hs']
    ring
  · have hk : g.axisPerm i ≠ k := fun h => hi (by simp [TorusIsometry.imageAxis, ← h])
    simp [TorusIsometry.mapSite, unitStep, hk, hi]
theorem mapSite_add_unitStep_of_neg (x : TorusSite n) (k : Fin 4)
    (hs : g.axisSign (g.imageAxis k) = -1) :
    g.mapSite (x + unitStep n k) = g.mapSite x - unitStep n (g.imageAxis k) := by
  have hs' : g.axisSign (g.axisPerm.symm k) = -1 := hs
  funext i
  by_cases hi : i = g.imageAxis k
  · subst hi
    simp [TorusIsometry.mapSite, TorusIsometry.imageAxis, unitStep, hs']
    ring
  · have hk : g.axisPerm i ≠ k := fun h => hi (by simp [TorusIsometry.imageAxis, ← h])
    simp [TorusIsometry.mapSite, unitStep, hk, hi]
theorem mapSite_injective [NeZero n] : Function.Injective (g.mapSite (n := n)) := by
  intro x x' h
  have hc : ∀ i, x (g.axisPerm i) = x' (g.axisPerm i) := by
    intro i
    have h1 := congrFun h i
    simp only [TorusIsometry.mapSite, add_left_inj] at h1
    rcases g.axisSign_unit i with hs | hs
    · simpa [hs] using h1
    · simpa [hs] using h1
  funext k
  have := hc (g.axisPerm.symm k)
  simpa using this
def TorusIsometry.imageCorner (x : TorusSite n) (μ ν : Fin 4) : TorusSite n :=
  g.mapSite x - (if g.axisSign (g.imageAxis μ) = 1 then 0 else unitStep n (g.imageAxis μ)) -
    (if g.axisSign (g.imageAxis ν) = 1 then 0 else unitStep n (g.imageAxis ν))
variable {g}
theorem plaquetteEnergy_of_transports {U U' : TorusField n} (h : g.Transports U U')
    (x : TorusSite n) (μ ν : Fin 4) :
    plaquetteEnergy U x μ ν =
      plaquetteEnergy U' (g.imageCorner x μ ν) (g.imageAxis μ) (g.imageAxis ν) := by
  have hpos : ∀ (k : Fin 4), g.axisSign (g.imageAxis k) = 1 → ∀ z,
      U' (g.mapSite z) (g.imageAxis k) = U z k := by
    intro k hk z
    have := h z k
    have h3 : g.axisSign (g.axisPerm.symm k) = 1 := hk
    rw [if_pos h3] at this
    exact this
  have hneg : ∀ (k : Fin 4), g.axisSign (g.imageAxis k) = -1 → ∀ z,
      (U' (g.mapSite z - unitStep n (g.imageAxis k)) (g.imageAxis k))⁻¹ = U z k := by
    intro k hk z
    have := h z k
    have h2 : g.axisSign (g.axisPerm.symm k) ≠ 1 := by
      have h3 : g.axisSign (g.axisPerm.symm k) = -1 := hk
      rw [h3]
      norm_num
    rw [if_neg h2] at this
    exact this
  set a := g.imageAxis μ with ha
  set b := g.imageAxis ν with hb
  set y := g.mapSite x with hy
  unfold plaquetteEnergy
  congr 1
  rcases g.axisSign_unit a with sa | sa <;> rcases g.axisSign_unit b with sb | sb
  · have hcorner : g.imageCorner x μ ν = y := by
      simp [TorusIsometry.imageCorner, ← ha, ← hb, sa, sb, hy]
    rw [hcorner]
    unfold holonomy
    rw [← hpos μ sa x, ← hpos ν sb (x + unitStep n μ), mapSite_add_unitStep_of_pos g x μ sa,
      ← hpos μ sa (x + unitStep n ν), mapSite_add_unitStep_of_pos g x ν sb, ← hpos ν sb x]
  · have hcorner : g.imageCorner x μ ν = y - unitStep n b := by
      simp [TorusIsometry.imageCorner, ← ha, ← hb, sa, sb, hy]
    rw [hcorner]
    have e1 : U x μ = U' (y - unitStep n b + unitStep n b) a := by
      rw [sub_add_cancel]
      exact (hpos μ sa x).symm
    have e2 : U (x + unitStep n μ) ν = (U' (y - unitStep n b + unitStep n a) b)⁻¹ := by
      rw [← hneg ν sb (x + unitStep n μ), mapSite_add_unitStep_of_pos g x μ sa]
      congr 2
      abel
    have e3 : U (x + unitStep n ν) μ = U' (y - unitStep n b) a := by
      rw [← hpos μ sa (x + unitStep n ν), mapSite_add_unitStep_of_neg g x ν sb]
    have e4 : U x ν = (U' (y - unitStep n b) b)⁻¹ := (hneg ν sb x).symm
    unfold holonomy
    rw [e1, e2, e3, e4, inv_inv]
    exact re_reversed_word_right _ _ _ _
  · have hcorner : g.imageCorner x μ ν = y - unitStep n a := by
      simp [TorusIsometry.imageCorner, ← ha, ← hb, sa, sb, hy]
    rw [hcorner]
    have e1 : U x μ = (U' (y - unitStep n a) a)⁻¹ := (hneg μ sa x).symm
    have e2 : U (x + unitStep n μ) ν = U' (y - unitStep n a) b := by
      rw [← hpos ν sb (x + unitStep n μ), mapSite_add_unitStep_of_neg g x μ sa]
    have e3 : U (x + unitStep n ν) μ = (U' (y - unitStep n a + unitStep n b) a)⁻¹ := by
      rw [← hneg μ sa (x + unitStep n ν), mapSite_add_unitStep_of_pos g x ν sb]
      congr 2
      abel
    have e4 : U x ν = U' (y - unitStep n a + unitStep n a) b := by
      rw [sub_add_cancel]
      exact (hpos ν sb x).symm
    unfold holonomy
    rw [e1, e2, e3, e4, inv_inv]
    exact re_reversed_word_left _ _ _ _
  · have hcorner : g.imageCorner x μ ν = y - unitStep n a - unitStep n b := by
      simp [TorusIsometry.imageCorner, ← ha, ← hb, sa, sb, hy]
    rw [hcorner]
    have e1 : U x μ = (U' (y - unitStep n a - unitStep n b + unitStep n b) a)⁻¹ := by
      rw [sub_add_cancel]
      exact (hneg μ sa x).symm
    have e2 : U (x + unitStep n μ) ν = (U' (y - unitStep n a - unitStep n b) b)⁻¹ := by
      rw [← hneg ν sb (x + unitStep n μ), mapSite_add_unitStep_of_neg g x μ sa]
    have e3 : U (x + unitStep n ν) μ = (U' (y - unitStep n a - unitStep n b) a)⁻¹ := by
      rw [← hneg μ sa (x + unitStep n ν), mapSite_add_unitStep_of_neg g x ν sb]
      congr 2
      abel
    have e4 : U x ν = (U' (y - unitStep n a - unitStep n b + unitStep n a) b)⁻¹ := by
      rw [← hneg ν sb x]
      congr 2
      abel
    unfold holonomy
    rw [e1, e2, e3, e4, inv_inv, inv_inv]
    exact re_cyclic_word _ _ _ _
theorem mem_plaquettesIn [NeZero n] {S : Finset (TorusSite n)} {p : TorusPlaquette n} :
    p ∈ plaquettesIn S ↔ p.2.1 < p.2.2 ∧ ∀ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, z ∈ S := by apply _root_.YangMills.Construction.TorusLumps.mem_plaquettesIn_iff_forall_vertex <;> assumption
def TorusIsometry.mapPlaquette (g : TorusIsometry) (p : TorusPlaquette n) : TorusPlaquette n :=
  if g.imageAxis p.2.1 < g.imageAxis p.2.2 then
    (g.imageCorner p.1 p.2.1 p.2.2, g.imageAxis p.2.1, g.imageAxis p.2.2)
  else (g.imageCorner p.1 p.2.1 p.2.2, g.imageAxis p.2.2, g.imageAxis p.2.1)
theorem wilsonAction_of_transports [NeZero n] {U U' : TorusField n} (h : g.Transports U U') :
    wilsonAction Finset.univ U' = wilsonAction Finset.univ U := by
  classical
  have hne : ∀ {μ ν : Fin 4}, μ < ν → g.imageAxis μ ≠ g.imageAxis ν := by
    intro μ ν hlt he
    exact hlt.ne (g.axisPerm.symm.injective he)
  have hmem : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
      g.mapPlaquette p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)) := by
    intro p hp
    have hlt := (mem_plaquettesIn.mp hp).1
    refine mem_plaquettesIn.mpr ⟨?_, fun _ _ => Finset.mem_univ _⟩
    unfold TorusIsometry.mapPlaquette
    split_ifs with hd
    · exact hd
    · exact lt_of_le_of_ne (not_lt.mp hd) (hne hlt).symm
  have hinj : Set.InjOn (g.mapPlaquette (n := n))
      (plaquettesIn (Finset.univ : Finset (TorusSite n))) := by
    rintro ⟨x, μ, ν⟩ hp ⟨x', μ', ν'⟩ hp' he
    have hlt : μ < ν := (mem_plaquettesIn.mp hp).1
    have hlt' : μ' < ν' := (mem_plaquettesIn.mp hp').1
    have hplane : (μ = μ' ∧ ν = ν') := by
      have hinjd := g.axisPerm.symm.injective
      unfold TorusIsometry.mapPlaquette at he
      simp only at he
      split_ifs at he with h1 h2 h2
      · simp only [Prod.mk.injEq] at he
        exact ⟨hinjd he.2.1, hinjd he.2.2⟩
      · simp only [Prod.mk.injEq] at he
        have e1 := hinjd he.2.1
        have e2 := hinjd he.2.2
        omega
      · simp only [Prod.mk.injEq] at he
        have e1 := hinjd he.2.1
        have e2 := hinjd he.2.2
        omega
      · simp only [Prod.mk.injEq] at he
        exact ⟨hinjd he.2.2, hinjd he.2.1⟩
    obtain ⟨rfl, rfl⟩ := hplane
    have hc : g.imageCorner x μ ν = g.imageCorner x' μ ν := by
      unfold TorusIsometry.mapPlaquette at he
      simp only at he
      split_ifs at he <;> exact (Prod.mk.inj he).1
    have hx : x = x' := by
      apply mapSite_injective g
      unfold TorusIsometry.imageCorner at hc
      simpa using hc
    rw [hx]
  have himg : (plaquettesIn (Finset.univ : Finset (TorusSite n))).image (g.mapPlaquette (n := n)) =
      plaquettesIn (Finset.univ : Finset (TorusSite n)) :=
    Finset.eq_of_subset_of_card_le
      (Finset.image_subset_iff.mpr hmem) (by rw [Finset.card_image_of_injOn hinj])
  unfold wilsonAction
  conv_lhs => rw [← himg]
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl ?_
  rintro ⟨x, μ, ν⟩ _
  rw [plaquetteEnergy_of_transports h x μ ν]
  unfold TorusIsometry.mapPlaquette
  simp only
  split_ifs
  · rfl
  · exact plaquetteEnergy_symm _ _ _ _
end TorusFields
end YangMills.Construction
end
