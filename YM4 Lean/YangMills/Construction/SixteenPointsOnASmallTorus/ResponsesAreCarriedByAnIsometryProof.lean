import YangMills.Construction.ClusterExpansionOfAStep.HaarOfFieldsIsKept
import YangMills.Construction.ClusterExpansionOfAStep.IsometriesOfTheEnergy
import YangMills.Construction.SixteenPointsOnASmallTorus.ResponsesAreCarriedByAnIsometry
import YangMills.Construction.SixteenPointsOnASmallTorus.ScoresAreCarriedByAnIsometry
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion FieldHaar
section Barycentres
variable {m : ℕ}
private def doubleCoord (m : ℕ) (u : ZMod m) : ZMod (2 * m) := ((2 * u.val : ℕ) : ZMod (2 * m))
private theorem doubleCoord_intCast [NeZero m] (k : ℤ) : doubleCoord m (k : ZMod m) = 2 * (k : ZMod (2 * m)) := by
  have hval : (((k : ZMod m).val : ℕ) : ℤ) = k % (m : ℤ) := ZMod.val_intCast k
  have hexp : ((2 * (k : ZMod m).val : ℕ) : ℤ) = 2 * k - (2 * (m : ℤ)) * (k / (m : ℤ)) := by
    push_cast
    rw [hval, Int.emod_def]
    ring
  have hzero : (2 * (m : ZMod (2 * m))) = 0 := by exact_mod_cast ZMod.natCast_self (2 * m)
  have hcast := congrArg (fun j : ℤ => (j : ZMod (2 * m))) hexp
  simp only [Int.cast_natCast] at hcast
  unfold doubleCoord
  rw [hcast]
  push_cast
  rw [hzero]
  ring
private theorem doubledBarycentre_apply (y : TorusSite m) (a b i : Fin 4) :
    doubledBarycentre ((y, a, b) : TorusPlaquette m) i = doubleCoord m (y i) + (((if i = a then 1 else 0 : ℤ)) : ZMod (2 * m)) +
      (((if i = b then 1 else 0 : ℤ)) : ZMod (2 * m)) := by
  unfold doubledBarycentre doubleCoord
  simp only
  push_cast
  split_ifs <;> simp
private theorem unitStep_coord (a i : Fin 4) (c : Prop) [Decidable c] :
    ((if c then 0 else unitStep m a : TorusSite m)) i = (((if c then 0 else if i = a then 1 else 0 : ℤ)) : ZMod m) := by
  by_cases hc : c
  · simp [hc]
  · by_cases hi : i = a
    · subst hi
      simp [hc, unitStep]
    · simp [hc, unitStep, hi]
private theorem imageAxis_ne (g : TorusIsometry) {μ ν : Fin 4} (h : μ < ν) : g.imageAxis μ ≠ g.imageAxis ν :=
  fun e => h.ne (g.axisPerm.symm.injective e)
private theorem axisSign_mul_indicator (g : TorusIsometry) (i a : Fin 4) :
    g.axisSign i * (if i = g.imageAxis a then 1 else 0 : ℤ) =
      (if i = g.imageAxis a then 1 else 0 : ℤ) - 2 * (if g.axisSign (g.imageAxis a) = 1 then 0 else if i = g.imageAxis a then 1 else 0 : ℤ) := by
  by_cases hi : i = g.imageAxis a
  · subst hi
    rcases g.axisSign_unit (g.imageAxis a) with s | s <;> simp [s]
  · simp [hi]
private theorem axisPerm_eq_iff (g : TorusIsometry) (i a : Fin 4) : g.axisPerm i = a ↔ i = g.imageAxis a := by
  unfold TorusIsometry.imageAxis
  constructor
  · rintro rfl
    simp
  · rintro rfl
    simp
private theorem doubledBarycentre_imageCorner [NeZero m] (g : TorusIsometry) (x : TorusSite m) (μ ν : Fin 4) :
    doubledBarycentre ((g.imageCorner x μ ν, g.imageAxis μ, g.imageAxis ν) : TorusPlaquette m) =
      doubledSiteImage g (doubledBarycentre ((x, μ, ν) : TorusPlaquette m)) := by
  funext i
  rw [doubledBarycentre_apply]
  unfold doubledSiteImage
  rw [doubledBarycentre_apply]
  simp only [axisPerm_eq_iff]
  set eμ : ℤ := if i = g.imageAxis μ then 1 else 0 with heμ
  set eν : ℤ := if i = g.imageAxis ν then 1 else 0 with heν
  set dμ : ℤ := if g.axisSign (g.imageAxis μ) = 1 then 0 else if i = g.imageAxis μ then 1 else 0 with hdμ
  set dν : ℤ := if g.axisSign (g.imageAxis ν) = 1 then 0 else if i = g.imageAxis ν then 1 else 0 with hdν
  set u : ℤ := ((x (g.axisPerm i)).cast : ℤ) with hu
  have hxu : x (g.axisPerm i) = (u : ZMod m) := by rw [hu]; simp
  have hcorner : g.imageCorner x μ ν i = ((g.axisSign i * u + g.offset i - dμ - dν : ℤ) : ZMod m) := by
    have t1 : ((if g.axisSign (g.imageAxis μ) = 1 then 0 else unitStep m (g.imageAxis μ) : TorusSite m)) i = (dμ : ZMod m) :=
      unitStep_coord _ _ _
    have t2 : ((if g.axisSign (g.imageAxis ν) = 1 then 0 else unitStep m (g.imageAxis ν) : TorusSite m)) i = (dν : ZMod m) :=
      unitStep_coord _ _ _
    unfold TorusIsometry.imageCorner
    simp only [Pi.sub_apply]
    rw [t1, t2]
    simp only [TorusIsometry.mapSite]
    rw [hxu]
    push_cast
    ring
  rw [hcorner, hxu, doubleCoord_intCast, doubleCoord_intCast]
  have hμ := axisSign_mul_indicator g i μ
  have hν := axisSign_mul_indicator g i ν
  have key : 2 * (g.axisSign i * u + g.offset i - dμ - dν) + eμ + eν = g.axisSign i * (2 * u + eμ + eν) + 2 * g.offset i := by
    linear_combination -hμ - hν
  have hcast : ((2 * (g.axisSign i * u + g.offset i - dμ - dν) + eμ + eν : ℤ) : ZMod (2 * m)) =
      ((g.axisSign i * (2 * u + eμ + eν) + 2 * g.offset i : ℤ) : ZMod (2 * m)) := by rw [key]
  push_cast at hcast ⊢
  exact hcast
private theorem doubledBarycentre_swap (y : TorusSite m) (a b : Fin 4) :
    doubledBarycentre ((y, a, b) : TorusPlaquette m) = doubledBarycentre ((y, b, a) : TorusPlaquette m) := by
  funext i
  rw [doubledBarycentre_apply, doubledBarycentre_apply]
  ring
private theorem doubledBarycentre_mapPlaquette [NeZero m] (g : TorusIsometry) (p : TorusPlaquette m) :
    doubledBarycentre (g.mapPlaquette p) = doubledSiteImage g (doubledBarycentre p) := by
  obtain ⟨x, μ, ν⟩ := p
  rw [← doubledBarycentre_imageCorner]
  unfold TorusIsometry.mapPlaquette
  simp only
  split_ifs
  · rfl
  · exact doubledBarycentre_swap _ _ _
end Barycentres
section Plaquettes
variable {n : ℕ} [NeZero n]
private theorem mapPlaquette_lt (g : TorusIsometry) {p : TorusPlaquette n} (hp : p.2.1 < p.2.2) :
    (g.mapPlaquette p).2.1 < (g.mapPlaquette p).2.2 := by
  unfold TorusIsometry.mapPlaquette
  split_ifs with hd
  · exact hd
  · exact lt_of_le_of_ne (not_lt.mp hd) (imageAxis_ne g hp).symm
private theorem mapPlaquette_mem (g : TorusIsometry) {p : TorusPlaquette n}
    (hp : p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n))) :
    g.mapPlaquette p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)) :=
  mem_plaquettesIn.mpr ⟨mapPlaquette_lt g (mem_plaquettesIn.mp hp).1, fun _ _ => Finset.mem_univ _⟩
private theorem mapPlaquette_injOn (g : TorusIsometry) :
    Set.InjOn (g.mapPlaquette (n := n)) (plaquettesIn (Finset.univ : Finset (TorusSite n))) := by
  rintro ⟨x, μ, ν⟩ hp ⟨x', μ', ν'⟩ hp' he
  have hlt : μ < ν := (mem_plaquettesIn.mp hp).1
  have hlt' : μ' < ν' := (mem_plaquettesIn.mp hp').1
  have hplane : μ = μ' ∧ ν = ν' := by
    have hinj := g.axisPerm.symm.injective
    unfold TorusIsometry.mapPlaquette at he
    simp only at he
    split_ifs at he with h1 h2 h2
    · simp only [Prod.mk.injEq] at he
      exact ⟨hinj he.2.1, hinj he.2.2⟩
    · simp only [Prod.mk.injEq] at he
      have e1 := hinj he.2.1
      have e2 := hinj he.2.2
      omega
    · simp only [Prod.mk.injEq] at he
      have e1 := hinj he.2.1
      have e2 := hinj he.2.2
      omega
    · simp only [Prod.mk.injEq] at he
      exact ⟨hinj he.2.2, hinj he.2.1⟩
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
private theorem sum_plaquettes_mapPlaquette (g : TorusIsometry) (f f' : TorusPlaquette n → ℝ)
    (h : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), f' (g.mapPlaquette p) = f p) :
    ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), f' p =
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), f p := by
  classical
  have himg : (plaquettesIn (Finset.univ : Finset (TorusSite n))).image (g.mapPlaquette (n := n)) =
      plaquettesIn (Finset.univ : Finset (TorusSite n)) :=
    Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun p hp => mapPlaquette_mem g hp)
      (by rw [Finset.card_image_of_injOn (mapPlaquette_injOn g)])
  conv_lhs => rw [← himg]
  rw [Finset.sum_image (mapPlaquette_injOn g)]
  exact Finset.sum_congr rfl h
private theorem weight_mapPlaquette {g : TorusIsometry} {w w' : PlaquetteWeight n} (hw : WeightTransported g w w')
    {p : TorusPlaquette n} (hp : p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n))) : w' (g.mapPlaquette p) = w p :=
  hw ⟨p, (mem_plaquettesIn.mp hp).1⟩ ⟨g.mapPlaquette p, mapPlaquette_lt g (mem_plaquettesIn.mp hp).1⟩
    (doubledBarycentre_mapPlaquette g p)
private theorem energy_mapPlaquette {g : TorusIsometry} {U U' : TorusField n} (h : g.Transports U U')
    (p : TorusPlaquette n) : plaquetteEnergyOf U' (g.mapPlaquette p) = plaquetteEnergyOf U p := by
  obtain ⟨x, μ, ν⟩ := p
  unfold plaquetteEnergyOf
  rw [plaquetteEnergy_of_transports h x μ ν]
  unfold TorusIsometry.mapPlaquette
  simp only
  split_ifs
  · rfl
  · exact plaquetteEnergy_symm _ _ _ _
private theorem plaquetteVertices_swap (y : TorusSite n) (a b : Fin 4) :
    (plaquetteVertices y a b).Perm (plaquetteVertices y b a) := by
  unfold plaquetteVertices
  have e : y + unitStep n b + unitStep n a = y + unitStep n a + unitStep n b := by abel
  rw [e]
  exact List.perm_iff_count.mpr fun c => by
    simp only [List.count_cons, List.count_nil]
    ring
private theorem plaquetteVertices_imageCorner (g : TorusIsometry) (x : TorusSite n) (μ ν : Fin 4) :
    ((plaquetteVertices x μ ν).map (g.mapSite (n := n))).Perm
      (plaquetteVertices (g.imageCorner x μ ν) (g.imageAxis μ) (g.imageAxis ν)) := by
  have hadd : ∀ (k : Fin 4) (z : TorusSite n), g.mapSite (z + unitStep n k) =
      g.mapSite z + (if g.axisSign (g.imageAxis k) = 1 then unitStep n (g.imageAxis k) else - unitStep n (g.imageAxis k)) := by
    intro k z
    rcases g.axisSign_unit (g.imageAxis k) with s | s
    · rw [mapSite_add_unitStep_of_pos g z k s]
      simp [s]
    · rw [mapSite_add_unitStep_of_neg g z k s, sub_eq_add_neg]
      simp [s]
  unfold plaquetteVertices TorusIsometry.imageCorner
  simp only [List.map_cons, List.map_nil, hadd]
  set y := g.mapSite x
  set A := unitStep n (g.imageAxis μ)
  set B := unitStep n (g.imageAxis ν)
  rcases g.axisSign_unit (g.imageAxis μ) with s | s <;> rcases g.axisSign_unit (g.imageAxis ν) with s' | s'
  · simp only [s, s', if_true, sub_zero]
    exact List.Perm.refl _
  · simp only [s, s', if_true, sub_zero]
    have h1 : (-1 : ℤ) ≠ 1 := by norm_num
    simp only [h1, if_false]
    have e1 : y + A + -B = y - B + A := by abel
    have e2 : y + -B = y - B := by abel
    have e3 : y - B + B = y := by abel
    have e4 : y - B + A + B = y + A := by abel
    rw [e1, e2, e3, e4]
    exact List.perm_iff_count.mpr fun c => by
      simp only [List.count_cons, List.count_nil]
      ring
  · simp only [s, s', if_true, sub_zero]
    have h1 : (-1 : ℤ) ≠ 1 := by norm_num
    simp only [h1, if_false]
    have e1 : y + -A + B = y - A + B := by abel
    have e2 : y + -A = y - A := by abel
    have e3 : y - A + A = y := by abel
    rw [e1, e2, e3]
    exact List.perm_iff_count.mpr fun c => by
      simp only [List.count_cons, List.count_nil]
      ring
  · have h1 : (-1 : ℤ) ≠ 1 := by norm_num
    simp only [s, s', h1, if_false]
    have e1 : y + -A + -B = y - A - B := by abel
    have e2 : y + -A = y - A := by abel
    have e3 : y + -B = y - B := by abel
    have e4 : y - A - B + A = y - B := by abel
    have e5 : y - A - B + B = y - A := by abel
    have e6 : y - B + B = y := by abel
    rw [e1, e2, e3, e4, e5, e6]
    exact List.perm_iff_count.mpr fun c => by
      simp only [List.count_cons, List.count_nil]
      ring
private theorem plaquetteVertices_mapPlaquette (g : TorusIsometry) (p : TorusPlaquette n) :
    ((plaquetteVertices p.1 p.2.1 p.2.2).map (g.mapSite (n := n))).Perm
      (plaquetteVertices (g.mapPlaquette p).1 (g.mapPlaquette p).2.1 (g.mapPlaquette p).2.2) := by
  obtain ⟨x, μ, ν⟩ := p
  unfold TorusIsometry.mapPlaquette
  simp only
  split_ifs
  · exact plaquetteVertices_imageCorner g x μ ν
  · exact (plaquetteVertices_imageCorner g x μ ν).trans (plaquetteVertices_swap _ _ _)
private theorem vertexMultiplicity_mapPlaquette (g : TorusIsometry) (y : TorusSite n) (p : TorusPlaquette n) :
    vertexMultiplicity (g.mapSite y) (g.mapPlaquette p) = vertexMultiplicity y p := by
  unfold vertexMultiplicity
  rw [← (plaquetteVertices_mapPlaquette g p).count_eq, List.count_map_of_injective _ _ (mapSite_injective g)]
private theorem siteResponse_transport {g : TorusIsometry} {U U' : TorusField n} {w w' : PlaquetteWeight n}
    (y : TorusSite n) (h : g.Transports U U') (hw : WeightTransported g w w') :
    siteResponse (g.mapSite y) U' w' = siteResponse y U w := by
  unfold siteResponse
  refine sum_plaquettes_mapPlaquette g _ _ fun p hp => ?_
  rw [vertexMultiplicity_mapPlaquette, weight_mapPlaquette hw hp, energy_mapPlaquette h]
end Plaquettes
section Blocks
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem parentBlock_intCast (k : ℤ) :
    (((((k : ZMod (n * L)).cast : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ) : ZMod n) =
      (((k + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ) : ZMod n) := by
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have e : (((k : ZMod (n * L)).cast : ℤ)) + ((L : ℤ) - 1) / 2 =
      (k + ((L : ℤ) - 1) / 2) + (L : ℤ) * (-((n : ℤ) * (k / ((n * L : ℕ) : ℤ)))) := by
    rw [ZMod.coe_intCast, Int.emod_def]
    push_cast
    ring
  rw [e, Int.add_mul_ediv_left _ _ hL]
  push_cast
  simp
private theorem centredDiv_neg (hL : Odd L) (k : ℤ) :
    (-k + ((L : ℤ) - 1) / 2) / (L : ℤ) = -((k + ((L : ℤ) - 1) / 2) / (L : ℤ)) := by
  obtain ⟨j, hj⟩ := hL
  have hLz : (L : ℤ) = 2 * j + 1 := by exact_mod_cast hj
  have hhalf : ((L : ℤ) - 1) / 2 = j := by rw [hLz]; omega
  rw [hhalf]
  have hpos : (0 : ℤ) < L := by rw [hLz]; omega
  set q := (k + j) / (L : ℤ) with hq
  set r := (k + j) % (L : ℤ) with hr
  have hdm : (L : ℤ) * q + r = k + j := Int.mul_ediv_add_emod _ _
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hpos.ne'
  have hr1 : r < L := Int.emod_lt_of_pos _ hpos
  have hmain := (Int.ediv_emod_unique (a := -k + j) (r := 2 * j - r) (q := -q) hpos).mpr
    ⟨by linear_combination -hdm, by omega, by omega⟩
  exact hmain.1
private theorem centredDiv_add_mul (k c : ℤ) :
    (k + (L : ℤ) * c + ((L : ℤ) - 1) / 2) / (L : ℤ) = (k + ((L : ℤ) - 1) / 2) / (L : ℤ) + c := by
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have e : k + (L : ℤ) * c + ((L : ℤ) - 1) / 2 = (k + ((L : ℤ) - 1) / 2) + (L : ℤ) * c := by ring
  rw [e, Int.add_mul_ediv_left _ _ hL]
private theorem parentBlock_scaledLift (hL : Odd L) (g : TorusIsometry) (z : TorusSite (n * L)) :
    parentBlock L ((g.scaledLift L).mapSite z) = g.mapSite (parentBlock L z) := by
  funext i
  set u : ℤ := ((z (g.axisPerm i)).cast : ℤ) with hu
  have hzu : z (g.axisPerm i) = (u : ZMod (n * L)) := by rw [hu]; simp
  have hsite : (g.scaledLift L).mapSite z i = ((g.axisSign i * u + (L : ℤ) * g.offset i : ℤ) : ZMod (n * L)) := by
    simp only [TorusIsometry.mapSite, TorusIsometry.scaledLift]
    rw [hzu]
    push_cast
    ring
  unfold parentBlock
  rw [hsite, parentBlock_intCast, centredDiv_add_mul]
  simp only [TorusIsometry.mapSite]
  rw [← hu]
  rcases g.axisSign_unit i with s | s
  · simp [s]
  · rw [s, neg_one_mul, centredDiv_neg hL]
    simp [s]
private theorem sum_sitesInBlocks_mapSite (hL : Odd L) (g : TorusIsometry) (Y : TorusSite n)
    (f : TorusSite (n * L) → ℝ) :
    ∑ z ∈ sitesInBlocks L {g.mapSite Y}, f z = ∑ z ∈ sitesInBlocks L {Y}, f ((g.scaledLift L).mapSite z) := by
  classical
  have hinj := mapSite_injective (n := n * L) (g.scaledLift L)
  have hbij := (Finite.injective_iff_bijective).mp hinj
  symm
  refine Finset.sum_bij (fun z _ => (g.scaledLift L).mapSite z) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hz ⊢
    rw [parentBlock_scaledLift hL, hz]
  · intro z _ z' _ h
    exact hinj h
  · intro z hz
    obtain ⟨z', rfl⟩ := hbij.2 z
    refine ⟨z', ?_, rfl⟩
    simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hz ⊢
    rw [parentBlock_scaledLift hL] at hz
    exact mapSite_injective g hz
  · intro z _
    rfl
end Blocks
private theorem blockMean_transport {L : ℕ} [NeZero L] (hL : Odd L) : ∀ (t n : ℕ) [NeZero n] (g : TorusIsometry)
    (w w' : PlaquetteWeight (fineSide L t n)) (y : TorusSite n), WeightTransported (iteratedLift L t g) w w' →
    WeightedResponses.blockMean L t n (g.mapSite y) w' = WeightedResponses.blockMean L t n y w := by
  intro t
  induction t with
  | zero =>
    intro n _ g w w' y hw
    show (1 / 24) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity (g.mapSite y) p * w' p =
      (1 / 24) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * w p
    congr 1
    refine sum_plaquettes_mapPlaquette (n := n) g _ _ fun p hp => ?_
    rw [vertexMultiplicity_mapPlaquette, weight_mapPlaquette (n := n) (g := g) (w := w) (w' := w') hw hp]
  | succ t ih =>
    intro n _ g w w' y hw
    show ((L : ℝ) ^ 4)⁻¹ * ∑ z ∈ sitesInBlocks L {g.mapSite y}, WeightedResponses.blockMean L t (n * L) z w' =
      ((L : ℝ) ^ 4)⁻¹ * ∑ z ∈ sitesInBlocks L {y}, WeightedResponses.blockMean L t (n * L) z w
    rw [sum_sitesInBlocks_mapSite hL]
    congr 1
    exact Finset.sum_congr rfl fun z _ => ih (n * L) (g.scaledLift L) w w' z hw
section Change
variable {n : ℕ} [NeZero n]
private def fieldPreimage (g : TorusIsometry) (U' : TorusField n) : TorusField n := fun x k =>
  if g.axisSign (g.axisPerm.symm k) = 1 then U' (g.mapSite x) (g.axisPerm.symm k)
  else (U' (g.mapSite x - unitStep n (g.axisPerm.symm k)) (g.axisPerm.symm k))⁻¹
private theorem fieldPreimage_of_transports {g : TorusIsometry} {U U' : TorusField n} (h : g.Transports U U') :
    fieldPreimage g U' = U := by
  funext x k
  have := h x k
  unfold fieldPreimage
  split_ifs at this ⊢ <;> exact this
private theorem measurable_link (z : TorusSite n) (j : Fin 4) : Measurable fun U : TorusField n => U z j :=
  (measurable_pi_apply j).comp (measurable_pi_apply z)
private theorem fieldPreimage_measurable (g : TorusIsometry) : Measurable (fieldPreimage (n := n) g) := by
  refine measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun k => ?_
  by_cases h : g.axisSign (g.axisPerm.symm k) = 1
  · simp only [fieldPreimage, h, if_true]
    exact measurable_link _ _
  · simp only [fieldPreimage, h, if_false]
    exact (measurable_link _ _).inv
private theorem fieldPreimage_injective (g : TorusIsometry) : Function.Injective (fieldPreimage (n := n) g) := by
  intro U₁ U₂ h
  have hbij : Function.Bijective (g.mapSite (n := n)) := (Finite.injective_iff_bijective).mp (mapSite_injective g)
  funext y j
  have hj : g.axisPerm.symm (g.axisPerm j) = j := by simp
  by_cases s : g.axisSign j = 1
  · obtain ⟨x, hx⟩ := hbij.2 y
    have e := congrFun (congrFun h x) (g.axisPerm j)
    simpa only [fieldPreimage, hj, s, if_true, hx] using e
  · obtain ⟨x, hx⟩ := hbij.2 (y + unitStep n j)
    have e := congrFun (congrFun h x) (g.axisPerm j)
    simpa only [fieldPreimage, hj, s, if_false, hx, add_sub_cancel_right, inv_inj] using e
private theorem measurableEmbedding_of_transports {g : TorusIsometry} {Ψ : TorusField n → TorusField n}
    (hm : Measurable Ψ) (hc : ∀ U, g.Transports U (Ψ U)) : MeasurableEmbedding Ψ := by
  have hl : Function.LeftInverse (fieldPreimage g) Ψ := fun U => fieldPreimage_of_transports (hc U)
  have hr : Function.Surjective Ψ := fun U' => ⟨fieldPreimage g U', fieldPreimage_injective g (hl _)⟩
  exact MeasurableEmbedding.of_measurable_inverse hm (by rw [hr.range_eq]; exact MeasurableSet.univ)
    (fieldPreimage_measurable g) hl
end Change
private theorem kernelImage_eq (ℓ : TorusLumps.StepParameters) (x : ℝ) (D : TorusFunctional) {n : ℕ} [NeZero n]
    (V : TorusField n) :
    kernelImage ℓ x D n V = ∫ U : TorusField (n * ℓ.side), D (n * ℓ.side) U *
      averagedKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 U) (readAtLevel (stepBlockFrame ℓ.side n) 1 V)
        ∂(fieldHaar (n * ℓ.side)) := by
  simp [kernelImage, NeZero.ne n]
private theorem n₀_le_mul_side (ℓ : TorusLumps.StepParameters) {n : ℕ} (hn : ℓ.n₀ ≤ n) : ℓ.n₀ ≤ n * ℓ.side :=
  hn.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne _)))
private theorem chainFunctional_transport (hH : HaarInvariantUnderSymmetries)
    (hK : IsometriesPreserveAveragedKernel) (ℓ : TorusLumps.StepParameters) (hadm : ℓ.Admissible) (β : ℝ)
    (x : ℕ → ℝ) : ∀ (t n : ℕ) [NeZero n], ℓ.n₀ ≤ n →
    ∀ (g : TorusIsometry) (U U' : TorusField n), g.Transports U U' →
      chainFunctional ℓ β x t n U' = chainFunctional ℓ β x t n U := by
  intro t
  induction t with
  | zero =>
    intro n _ _ g U U' h
    simp only [chainFunctional, wilsonWeight, NeZero.ne n, dite_false]
    rw [wilsonAction_of_transports h]
  | succ t ih =>
    intro n _ hn g V V' h
    obtain ⟨Ψ, hΨ, hc⟩ := (hH (n * ℓ.side)).2 (g.scaledLift ℓ.side)
    have hemb := measurableEmbedding_of_transports hΨ.measurable hc
    simp only [chainFunctional]
    rw [kernelImage_eq, kernelImage_eq, ← hΨ.integral_comp hemb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    simp only
    rw [ih (n * ℓ.side) (n₀_le_mul_side ℓ hn) (g.scaledLift ℓ.side) U (Ψ U) (hc U)]
    have := hK ℓ hadm (x t) n hn g U (Ψ U) V V' (hc U) h
    simp only [fineLevelField, coarseLevelField] at this
    rw [this]
private theorem coldResponseChain_transport (hH : HaarInvariantUnderSymmetries)
    (hK : IsometriesPreserveAveragedKernel) (hS : scoreIsometryInvariantStatement)
    (ℓ : TorusLumps.StepParameters) (hadm : ℓ.Admissible) (β : ℝ) (x al : ℕ → ℝ) :
    ∀ (t n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ (g : TorusIsometry) (V V' : TorusField n)
      (w w' : PlaquetteWeight (fineSide ℓ.side t n)) (y : TorusSite n), g.Transports V V' →
      WeightTransported (iteratedLift ℓ.side t g) w w' →
      coldResponseChain ℓ β x al t n (g.mapSite y) V' w' = coldResponseChain ℓ β x al t n y V w := by
  intro t
  induction t with
  | zero =>
    intro n _ _ g V V' w w' y h hw
    exact siteResponse_transport (n := n) y h hw
  | succ t ih =>
    intro n _ hn g V V' w w' y h hw
    obtain ⟨Ψ, hΨ, hc⟩ := (hH (n * ℓ.side)).2 (g.scaledLift ℓ.side)
    have hemb := measurableEmbedding_of_transports hΨ.measurable hc
    have hden : kernelImage ℓ (x t) (chainFunctional ℓ β x t) n V' =
        kernelImage ℓ (x t) (chainFunctional ℓ β x t) n V :=
      chainFunctional_transport hH hK ℓ hadm β x (t + 1) n hn g V V' h
    have hmean : WeightedResponses.blockMean ℓ.side (t + 1) n (g.mapSite y) w' =
        WeightedResponses.blockMean ℓ.side (t + 1) n y w :=
      blockMean_transport hadm.L_odd (t + 1) n g w w' y hw
    simp only [coldResponseChain, stepColdResponse, conditionalMean]
    rw [hden, ← hΨ.integral_comp hemb]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    simp only
    obtain ⟨τ, hτ⟩ := hS ℓ hadm (x t) n hn g U (Ψ U) V V' (hc U) h
    rw [chainFunctional_transport hH hK ℓ hadm β x t (n * ℓ.side) (n₀_le_mul_side ℓ hn) (g.scaledLift ℓ.side)
      U (Ψ U) (hc U), hmean]
    refine congrArg₂ (· * ·) rfl ?_
    refine (Equiv.sum_comp τ _).symm.trans ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [(hτ b).1]
    by_cases hb : b ∈ baseChoices ℓ (fineLevelField ℓ n U)
    · rw [(hτ b).2 hb y, sum_sitesInBlocks_mapSite hadm.L_odd g y,
        Finset.sum_congr rfl fun z _ => ih (n * ℓ.side) (n₀_le_mul_side ℓ hn) (g.scaledLift ℓ.side) U (Ψ U) w w' z
          (hc U) hw]
    · have h0 : stepTransitionDensity ℓ (x t) U b V = 0 := if_neg hb
      rw [h0, zero_mul, zero_mul]
theorem responseIsometryInvariant (hH : HaarInvariantUnderSymmetries)
    (hK : IsometriesPreserveAveragedKernel) (hS : scoreIsometryInvariantStatement) :
    responseIsometryInvariantStatement := by
  intro ℓ hadm β x al t n _ hn g V V' w w' y h hw
  exact coldResponseChain_transport hH hK hS ℓ hadm β x al t n hn g V V' w w' y h hw
end YangMills.Construction.SmallTorusCopies
end
