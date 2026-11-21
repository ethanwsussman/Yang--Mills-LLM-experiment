import YangMills.Construction.ColdChainAtEveryLevel.MeansOfAPotential
import YangMills.Construction.ClusterExpansionOfAStep.ActionAlongMoves
import YangMills.Construction.ClusterExpansionOfAStep.ContoursFromBases
import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TorusChain
open BlockAverages TorusFields TorusLumps TorusContours LevelAction StepCosts
theorem natAbs_valMinAbs_sub_intCast_cast {p q : ℕ} (h : p = q) [NeZero p] (a b : ZMod p) :
    ((((a.cast : ℤ) : ZMod q) - ((b.cast : ℤ) : ZMod q)).valMinAbs).natAbs = ((a - b).valMinAbs).natAbs := by
  subst h
  simp
variable {F : BlockFrame} {n : ℕ} [NeZero n]
section Top
variable [∀ i, NeZero (F.period F.top i)] (hp : ∀ i, F.period F.top i = n)
include hp
omit [NeZero n] in
theorem toTorusSite_torusSiteInFrame (x : TorusSite n) : toTorusSite n (torusSiteInFrame F F.top x) = x := by
  have h : (toTorusSite n (siteOfCoords F.top fun i => ((x i).cast : ℤ) : F.Site F.top) : TorusSite n) =
      siteOfInt fun i => ((x i).cast : ℤ) := toTorusSite_siteOfCoords hp _
  show toTorusSite n (siteOfCoords F.top fun i => ((x i).cast : ℤ) : F.Site F.top) = x
  rw [h]
  funext i
  simp [siteOfInt]
theorem torusSiteInFrame_toTorusSite (y : F.Cell) : torusSiteInFrame F F.top (toTorusSite n y) = y := by
  funext k
  show (((((((siteCoords y k : ℤ)) : ZMod n)).cast : ℤ)) : ZMod (F.period F.top k)) = y k
  rw [intCast_cast_intCast_of_eq (hp k).symm]
  exact intCast_siteCoords y k
def torusSiteEquivCell : TorusSite n ≃ F.Cell where
  toFun := torusSiteInFrame F F.top
  invFun := toTorusSite n
  left_inv := toTorusSite_torusSiteInFrame hp
  right_inv := torusSiteInFrame_toTorusSite hp
theorem torusSiteInFrame_add (x x' : TorusSite n) :
    torusSiteInFrame F F.top (x + x') = torusSiteInFrame F F.top x + torusSiteInFrame F F.top x' := by
  have h := toTorusSite_add (F := F) (j := F.top) hp (torusSiteInFrame F F.top x) (torusSiteInFrame F F.top x')
  rw [toTorusSite_torusSiteInFrame hp, toTorusSite_torusSiteInFrame hp] at h
  rw [← h, torusSiteInFrame_toTorusSite hp]
theorem torusSiteInFrame_siteOfInt (h : Fin 4 → ℤ) :
    torusSiteInFrame F F.top (siteOfInt h : TorusSite n) = siteOfCoords F.top h := by
  rw [← toTorusSite_siteOfCoords (F := F) (j := F.top) hp h]
  exact torusSiteInFrame_toTorusSite hp _
theorem torusSiteInFrame_unitStep (i : Fin 4) :
    torusSiteInFrame F F.top (TorusFields.unitStep n i) = BlockAverages.unitStep F.top i := by
  rw [← toTorusSite_unitStep (F := F) (j := F.top) hp i]
  exact torusSiteInFrame_toTorusSite hp _
omit [∀ i, NeZero (F.period F.top i)] in
theorem cellSupDist_torusSiteInFrame (x y : TorusSite n) :
    cellSupDist (torusSiteInFrame F F.top x) (torusSiteInFrame F F.top y) = supDist x y := by
  unfold cellSupDist supDist
  congr 1
  funext i
  exact natAbs_valMinAbs_sub_intCast_cast (hp i).symm (x i) (y i)
theorem mem_cellsOfSites_iff (X : Finset (TorusSite n)) (z : F.Cell) :
    z ∈ TorusFields.cellsOfSites F X ↔ toTorusSite n z ∈ X := by
  unfold TorusFields.cellsOfSites
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : toTorusSite n (torusSiteInFrame F F.top x) = x := toTorusSite_torusSiteInFrame hp x
    unfold torusSiteInFrame at this
    rw [this]
    exact hx
  · intro h
    exact ⟨_, h, torusSiteInFrame_toTorusSite hp z⟩
omit [NeZero n] [∀ i, NeZero (F.period F.top i)] hp in
theorem centredCube_one : centredCube 1 = ({0} : Finset (Fin 4 → ℤ)) := by apply _root_.YangMills.Construction.PotentialMeans.centredCube_one <;> assumption
omit [NeZero n] hp in
theorem sitesOfCells_top (S : Finset F.Cell) : sitesOfCells S F.top = S := by
  ext x
  unfold sitesOfCells
  rw [Nat.sub_self, pow_zero, centredCube_one]
  simp only [Finset.mem_biUnion, Finset.image_singleton, Finset.mem_singleton]
  have hc : ∀ z : F.Cell, (cellCentre F.top z : F.Site F.top) + siteOfCoords F.top 0 = z := by
    intro z
    unfold cellCentre
    rw [Nat.sub_self, pow_zero]
    simp only [one_mul]
    rw [_root_.YangMills.Construction.TorusContours.siteOfCoords_zero, add_zero]
    exact _root_.YangMills.Construction.TorusContours.siteOfCoords_siteCoords z
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [hc]
    exact hz
  · intro hx
    exact ⟨x, hx, (hc x).symm⟩
theorem isOrthantRegular_of_isRegularRegion {X : Finset (TorusSite n)} {m : ℕ} (hX : IsRegularRegion X m) :
    IsOrthantRegular (TorusFields.cellsOfSites F X) m := by
  intro z
  obtain ⟨eps, he, h⟩ := hX (toTorusSite n z)
  refine ⟨eps, he, fun q hq hd hh hb hb' => ?_⟩
  rw [mem_cellsOfSites_iff hp] at hq ⊢
  have hq' : q = torusSiteInFrame F F.top (toTorusSite n q) := (torusSiteInFrame_toTorusSite hp q).symm
  have hz' : z = torusSiteInFrame F F.top (toTorusSite n z) := (torusSiteInFrame_toTorusSite hp z).symm
  have hd' : supDist (toTorusSite n q) (toTorusSite n z) ≤ m := by
    rw [← cellSupDist_torusSiteInFrame hp, ← hq', ← hz']
    exact hd
  have := h _ hq hd' hh hb hb'
  rw [toTorusSite_add hp, toTorusSite_siteOfCoords hp]
  exact this
omit [NeZero n] in
theorem toTorusSite_sub_of_top (x u : F.Cell) :
    (toTorusSite n (x - u) : TorusSite n) = toTorusSite n x - toTorusSite n u := by
  have h := toTorusSite_add (F := F) (j := F.top) hp (x - u) u
  rw [sub_add_cancel] at h
  rw [h]
  abel
omit [NeZero n] in
theorem plaquetteHolonomy_readAtLevel (W : TorusField n) (p : F.Cell × Fin 4 × Fin 4) :
    plaquetteHolonomy (readAtLevel F F.top W) p = TorusFields.holonomy W (toTorusSite n p.1) p.2.1 p.2.2 := by
  obtain ⟨x, μ, ν⟩ := p
  have hr : ∀ (y : F.Cell) (i : Fin 4), readAtLevel F F.top W y i = W (toTorusSite n y) i := fun _ _ => rfl
  simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true, if_false, hr,
    ← sub_eq_add_neg, toTorusSite_add hp, toTorusSite_sub_of_top hp, toTorusSite_unitStep hp, mul_one]
  have e1 : toTorusSite n x + TorusFields.unitStep n μ + TorusFields.unitStep n ν - TorusFields.unitStep n μ =
      toTorusSite n x + TorusFields.unitStep n ν := by abel
  have e2 : toTorusSite n x + TorusFields.unitStep n ν - TorusFields.unitStep n ν = toTorusSite n x := by abel
  rw [e1, e2]
  simp [TorusFields.holonomy, mul_assoc]
theorem isCold_of_isColdOn {s : ℝ} {X : Finset (TorusSite n)} {W : TorusField n} (h : IsColdOn s X W) :
    IsCold (TorusFields.cellsOfSites F X) F.top s (readAtLevel F F.top W) := by
  intro p hpl
  obtain ⟨hp1, hp2⟩ := (Finset.mem_filter.mp hpl).2, (Finset.mem_filter.mp hpl).2
  have hlt : p.2.1 < p.2.2 := hp1.1
  have hsub : plaquetteCorners p ⊆ TorusFields.cellsOfSites F X := by
    have := hp1.2
    rwa [sitesOfCells_top] at this
  have hin : ((toTorusSite n p.1, p.2.1, p.2.2) : TorusPlaquette n) ∈ plaquettesIn X := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, fun z hz => ?_⟩
    have key : ∀ c ∈ plaquetteCorners p, toTorusSite n c ∈ X := fun c hc => (mem_cellsOfSites_iff hp X c).mp (hsub hc)
    simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact key _ (by simp [plaquetteCorners])
    · have := key (p.1 + BlockAverages.unitStep F.top p.2.1) (by simp [plaquetteCorners])
      rwa [toTorusSite_add hp, toTorusSite_unitStep hp] at this
    · have := key (p.1 + BlockAverages.unitStep F.top p.2.2) (by simp [plaquetteCorners])
      rwa [toTorusSite_add hp, toTorusSite_unitStep hp] at this
    · have := key (p.1 + BlockAverages.unitStep F.top p.2.1 + BlockAverages.unitStep F.top p.2.2)
        (by simp [plaquetteCorners])
      rwa [toTorusSite_add hp, toTorusSite_add hp, toTorusSite_unitStep hp, toTorusSite_unitStep hp] at this
  have := h _ hin
  show ‖((plaquetteHolonomy (readAtLevel F F.top W) p : UnitQuaternion) : ℍ[ℝ]) - 1‖ < s
  rw [plaquetteHolonomy_readAtLevel hp]
  exact this
theorem readAtLevel_perturb {k : ℕ} (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (W : TorusField n) :
    readAtLevel F F.top (perturb c Xs σ W) =
      rotatedField (bondSpread (fun l => (torusSiteInFrame F F.top (c l).1, (c l).2)) Xs σ)
        (readAtLevel F F.top W) := by
  funext y i
  show expUnit (∑ l, if c l = (toTorusSite n y, i) then σ l • Xs l else 0) * W (toTorusSite n y) i =
    expUnit (∑ l, if ((torusSiteInFrame F F.top (c l).1, (c l).2) : F.Cell × Fin 4) = (y, i) then σ l • Xs l else 0) *
      W (toTorusSite n y) i
  congr 2
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hc : c l = (toTorusSite n y, i)
  · have h2 : ((torusSiteInFrame F F.top (c l).1, (c l).2) : F.Cell × Fin 4) = (y, i) := by
      rw [hc]
      exact Prod.ext (torusSiteInFrame_toTorusSite hp y) rfl
    rw [if_pos hc, if_pos h2]
  · have h2 : ¬ ((torusSiteInFrame F F.top (c l).1, (c l).2) : F.Cell × Fin 4) = (y, i) := by
      intro he
      apply hc
      have h3 : torusSiteInFrame F F.top (c l).1 = y := congrArg Prod.fst he
      have h4 : (c l).2 = i := congrArg Prod.snd he
      refine Prod.ext ?_ h4
      rw [← h3]
      exact (toTorusSite_torusSiteInFrame hp _).symm
    rw [if_neg hc, if_neg h2]
theorem mixedDeriv_readAtLevel {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (G : F.GaugeField F.top → E) (W : TorusField n) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun W' => G (readAtLevel F F.top W')) W c Xs =
      mixedBondDerivative G (readAtLevel F F.top W) (fun l => (torusSiteInFrame F F.top (c l).1, (c l).2)) Xs := by
  unfold mixedDeriv mixedBondDerivative
  have : (fun σ : Fin k → ℝ => G (readAtLevel F F.top (perturb c Xs σ W))) =
      fun σ => G (rotatedField (bondSpread (fun l => (torusSiteInFrame F F.top (c l).1, (c l).2)) Xs σ)
        (readAtLevel F F.top W)) :=
    funext fun σ => by rw [readAtLevel_perturb hp]
  rw [this]
theorem contDiffThreeAt_of_isBondAnalyticAt {G : F.GaugeField F.top → ℝ} {W : TorusField n}
    (hG : IsBondAnalyticAt G (readAtLevel F F.top W)) :
    ContDiffThreeAt (fun W' => G (readAtLevel F F.top W')) W := by
  intro k c Xs
  have h := hG k (fun l => (torusSiteInFrame F F.top (c l).1, (c l).2)) Xs
  have e : (fun σ : Fin k → ℝ => G (readAtLevel F F.top (perturb c Xs σ W))) =
      fun σ => G (rotatedField (bondSpread (fun l => (torusSiteInFrame F F.top (c l).1, (c l).2)) Xs σ)
        (readAtLevel F F.top W)) :=
    funext fun σ => by rw [readAtLevel_perturb hp]
  rw [e]
  exact h.contDiffAt
end Top
section Sums
variable [∀ j i, NeZero (F.period j i)]
omit [∀ j i, NeZero (F.period j i)] in
theorem unitStep_apply_self_ne_zero (h1 : ∀ i, 1 < F.period 0 i) (i : Fin 4) :
    (BlockAverages.unitStep 0 i : F.Site 0) i ≠ 0 := by
  have : Fact (1 < F.period 0 i) := ⟨h1 i⟩
  simp [BlockAverages.unitStep, siteOfCoords]
omit [∀ j i, NeZero (F.period j i)] in
theorem card_plaquetteCorners (h1 : ∀ i, 1 < F.period 0 i) (p : F.Site 0 × Fin 4 × Fin 4) (hlt : p.2.1 < p.2.2) :
    (plaquetteCorners p).card = 4 := by
  obtain ⟨x, μ, ν⟩ := p
  have hne : μ ≠ ν := ne_of_lt hlt
  have hu : ∀ i : Fin 4, (BlockAverages.unitStep 0 i : F.Site 0) ≠ 0 := fun i h =>
    unitStep_apply_self_ne_zero h1 i (by rw [h]; rfl)
  have hv : (BlockAverages.unitStep 0 μ : F.Site 0) ≠ BlockAverages.unitStep 0 ν := fun h => by
    have h2 := congrFun h μ
    have h3 : (BlockAverages.unitStep 0 ν : F.Site 0) μ = 0 := by
      simp [BlockAverages.unitStep, siteOfCoords, hne]
    rw [h3] at h2
    exact unitStep_apply_self_ne_zero h1 μ h2
  have hw : (BlockAverages.unitStep 0 μ + BlockAverages.unitStep 0 ν : F.Site 0) ≠ 0 := fun h => by
    have h2 := congrFun h μ
    have h3 : (BlockAverages.unitStep 0 ν : F.Site 0) μ = 0 := by
      simp [BlockAverages.unitStep, siteOfCoords, hne]
    simp only [Pi.add_apply, h3, add_zero, Pi.zero_apply] at h2
    exact unitStep_apply_self_ne_zero h1 μ h2
  have n1 : x + BlockAverages.unitStep 0 ν ∉
      ({x + BlockAverages.unitStep 0 μ + BlockAverages.unitStep 0 ν} : Finset (F.Site 0)) := by
    simp only [Finset.mem_singleton]
    intro h
    apply hu μ
    have h2 : (BlockAverages.unitStep 0 μ : F.Site 0) =
        (x + BlockAverages.unitStep 0 μ + BlockAverages.unitStep 0 ν) - (x + BlockAverages.unitStep 0 ν) := by abel
    rw [h2, ← h, sub_self]
  have n2 : x + BlockAverages.unitStep 0 μ ∉ ({x + BlockAverages.unitStep 0 ν,
      x + BlockAverages.unitStep 0 μ + BlockAverages.unitStep 0 ν} : Finset (F.Site 0)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h => hv (add_left_cancel h), fun h => hu ν ?_⟩
    have h2 : (BlockAverages.unitStep 0 ν : F.Site 0) =
        (x + BlockAverages.unitStep 0 μ + BlockAverages.unitStep 0 ν) - (x + BlockAverages.unitStep 0 μ) := by abel
    rw [h2, ← h, sub_self]
  have n3 : x ∉ ({x + BlockAverages.unitStep 0 μ, x + BlockAverages.unitStep 0 ν,
      x + BlockAverages.unitStep 0 μ + BlockAverages.unitStep 0 ν} : Finset (F.Site 0)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h => hu μ ?_, fun h => hu ν ?_, fun h => hw ?_⟩
    · have h2 : (BlockAverages.unitStep 0 μ : F.Site 0) = (x + BlockAverages.unitStep 0 μ) - x := by abel
      rw [h2, ← h, sub_self]
    · have h2 : (BlockAverages.unitStep 0 ν : F.Site 0) = (x + BlockAverages.unitStep 0 ν) - x := by abel
      rw [h2, ← h, sub_self]
    · have h2 : (BlockAverages.unitStep 0 μ + BlockAverages.unitStep 0 ν : F.Site 0) =
          (x + BlockAverages.unitStep 0 μ + BlockAverages.unitStep 0 ν) - x := by abel
      rw [h2, ← h, sub_self]
  show ({x, x + BlockAverages.unitStep 0 μ, x + BlockAverages.unitStep 0 ν,
    x + BlockAverages.unitStep 0 μ + BlockAverages.unitStep 0 ν} : Finset (F.Site 0)).card = 4
  rw [Finset.card_insert_of_notMem n3, Finset.card_insert_of_notMem n2, Finset.card_insert_of_notMem n1,
    Finset.card_singleton]
theorem sum_cellShare (h1 : ∀ i, 1 < F.period 0 i) (a : ℝ) (S : Finset F.Cell) (X : F.FieldChain) :
    ∑ Y : F.Cell, cellShare a S Y X = chainAction a S X := by
  classical
  unfold cellShare chainAction BlockAverages.wilsonAction
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.sum_mul]
    have hlt : p.2.1 < p.2.2 := (Finset.mem_filter.mp hp).2.1
    have : ∑ Y : F.Cell, ∑ x ∈ plaquetteCorners p, (if enclosingCell x = Y then (1 / 4 : ℝ) else 0) = 1 := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, nsmul_eq_mul]
      rw [card_plaquetteCorners h1 p hlt]
      norm_num
    rw [this, one_mul]
  · congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ Y : F.Cell, ((if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
        (if enclosingCell (c.1 + BlockAverages.unitStep (j + 1) c.2) = Y then (1 / 2 : ℝ) else 0)) = 1 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      norm_num
    rw [this, one_mul]
theorem minimalAction_eq_sum_minimalCellShare (hLV : minimalChainExistenceStatement)
    (h1 : ∀ i, 1 < F.period 0 i) {a : ℝ} (ha : 0 ≤ a) (S : Finset F.Cell) (V : F.GaugeField F.top) :
    minimalAction a S F.top V = ∑ Y : F.Cell, minimalCellShare a S Y V := by
  classical
  obtain ⟨X1, hm1, ht1⟩ := (hLV F a S ha).2.2.2 V
  have hex : ∃ X, IsMinimalChain a S V X := ⟨X1, hm1⟩
  have hs : ∀ Y, minimalCellShare a S Y V = cellShare a S Y hex.choose := fun Y => by
    unfold minimalCellShare
    rw [dif_pos hex]
  simp only [hs]
  rw [sum_cellShare h1, ← ht1]
  exact le_antisymm (hm1.2 _ hex.choose_spec.1) (hex.choose_spec.2 _ hm1.1)
end Sums
end YangMills.Construction.TorusChain
end
