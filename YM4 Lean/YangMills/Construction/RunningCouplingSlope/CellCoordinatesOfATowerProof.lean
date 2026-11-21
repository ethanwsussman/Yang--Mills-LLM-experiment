import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.RunningCouplingSlope.CellCoordinatesOfATower
import YangMills.Construction.Towers.CellsAndClassesOfThePeriodicExtension
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.CellQuotientProof
open Tower PeriodicOperators
open LocalKernels LocalKernels.Periodisation
open InfiniteLattice (AmbientSpace)
open TorusMetric (torusProj supNormVec)
variable {L n k : ℕ}
private theorem coe_cellOfCoords (L n k : ℕ) (w : Fin 4 → ℤ) (μ : Fin 4) :
    ((cellOfCoords L n k w : Vertex L n k k) : PeriodicLattice.FourTorus L n) μ =
      (((w μ : ℝ)) : AddCircle (PeriodicLattice.torusSide L n)) := by
  have hsp : PeriodicLattice.meshSize L 0 = 1 := by
    simp [PeriodicLattice.meshSize]
  simp only [cellOfCoords, PeriodicLattice.offsetSite]
  rw [zero_add, AddSubgroup.val_finsetSum]
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single μ]
  · have e : (((w μ : ℝ)) : AddCircle (PeriodicLattice.torusSide L n)) =
        (((w μ • (1 : ℝ) : ℝ)) : AddCircle (PeriodicLattice.torusSide L n)) := by simp
    rw [e]
    simp only [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, PeriodicLattice.levelDepth,
      sub_self, hsp, AddSubgroup.coe_zsmul, Pi.smul_apply, Pi.single_eq_same]
    exact (QuotientAddGroup.mk_zsmul _ _ _).symm
  · intro ν _ hν
    simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne (Ne.symm hν)]
  · simp
private theorem torusSide_eq_periodSide (L n : ℕ) :
    PeriodicLattice.torusSide L n = (periodSide L n : ℝ) := by
  simp [PeriodicLattice.torusSide, periodSide]
private theorem periodSide_smul_apply (L n : ℕ) (t : Fin 4 → ℤ) (ν : Fin 4) :
    (periodSide L n • t) ν = (periodSide L n : ℤ) * t ν := by
  rw [Pi.smul_apply, nsmul_eq_mul]
private theorem exists_period_of_cellOfCoords_eq {w w' : Fin 4 → ℤ}
    (h : cellOfCoords L n k w = cellOfCoords L n k w') :
    ∃ m : Fin 4 → ℤ, w' = w + periodSide L n • m := by
  have hμ : ∀ μ, ∃ t : ℤ, w' μ = w μ + periodSide L n * t := by
    intro μ
    have e := congrFun (congrArg (fun y : Vertex L n k k => (y : PeriodicLattice.FourTorus L n)) h) μ
    simp only [coe_cellOfCoords L n k] at e
    have e2 : (((w' μ - w μ : ℝ)) : AddCircle (PeriodicLattice.torusSide L n)) = 0 := by
      rw [AddCircle.coe_sub, e, sub_self]
    obtain ⟨t, ht⟩ := (AddCircle.coe_eq_zero_iff _).1 e2
    refine ⟨t, ?_⟩
    rw [torusSide_eq_periodSide] at ht
    have : ((w' μ : ℤ) : ℝ) = ((w μ + periodSide L n * t : ℤ) : ℝ) := by
      push_cast
      simp only [zsmul_eq_mul] at ht
      linarith
    exact_mod_cast this
  choose m hm using hμ
  refine ⟨m, ?_⟩
  funext μ
  simp [hm μ]
private theorem isCellQuotient_of_near {I : PeriodicData}
    (hpos : ∀ n i, I.pos (I.translate n i) = I.pos i + castVec n)
    {ι : Type} {q : I.Carrier → ι} {c : ι → Vertex L n k k} (hs : Function.Surjective q)
    (hsame : ∀ i i', q i = q i' ↔ ∃ m : Fin 4 → ℤ, i' = I.translate (periodSide L n • m) i)
    (hnear : ∀ i, ∃ w : Fin 4 → ℤ, cellOfCoords L n k w = c (q i) ∧
      ∀ μ, |I.pos i μ - (w μ : ℝ)| < 1 / 2) : IsCellQuotient L n k I q c where
  surjective := hs
  image_eq_iff := hsame
  exists_near_cell i := by
    obtain ⟨w, h, h'⟩ := hnear i
    exact ⟨w, h, fun μ => (h' μ).le.trans (by norm_num)⟩
  eq_of_same_cell i m e := by
    obtain ⟨w₁, h₁, b₁⟩ := hnear i
    obtain ⟨w₂, h₂, b₂⟩ := hnear (I.translate m i)
    obtain ⟨m', hm'⟩ := exists_period_of_cellOfCoords_eq (h₁.trans (e.trans h₂.symm))
    have hm : m = periodSide L n • m' := by
      funext μ
      have a := b₁ μ
      have b := b₂ μ
      rw [hpos] at b
      have hw : (w₂ μ : ℝ) = (w₁ μ : ℝ) + (((periodSide L n • m') μ : ℤ) : ℝ) := by
        rw [hm']
        simp only [Pi.add_apply]
        push_cast
        rfl
      have hlt : |((m μ - (periodSide L n • m') μ : ℤ) : ℝ)| < 1 := by
        rw [abs_lt] at a b ⊢
        simp only [castVec, Pi.add_apply] at b
        push_cast
        constructor <;> linarith [a.1, a.2, b.1, b.2, hw]
      have hlt' : |m μ - (periodSide L n • m') μ| < 1 := by exact_mod_cast hlt
      have := Int.abs_lt_one_iff.1 hlt'
      omega
    exact (hsame _ _).2 ⟨m', by rw [hm]⟩
private theorem meshSize_top (L k : ℕ) :
    PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) = 1 := by
  simp [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
private theorem torusProj_surj {S : ℝ} : Function.Surjective (torusProj S) := by apply _root_.YangMills.Construction.TestFunctions.torusProj_surjective <;> assumption
private theorem exists_lift_supNormVec_lt {S r : ℝ} {x : TorusMetric.Torus4 S}
    (h : TorusMetric.torusSupNorm x < r) : ∃ u, torusProj S u = x ∧ supNormVec u < r := by
  unfold TorusMetric.torusSupNorm at h
  have hne : (supNormVec '' (torusProj S ⁻¹' {x})).Nonempty := by
    obtain ⟨u, hu⟩ := torusProj_surj x
    exact ⟨_, u, hu, rfl⟩
  obtain ⟨_, ⟨u, hu, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne h
  exact ⟨u, hu, hlt⟩
private theorem torusSupNorm_le_supNormVec {S : ℝ} {v : Fin 4 → ℝ} {x : TorusMetric.Torus4 S}
    (hv : torusProj S v = x) : TorusMetric.torusSupNorm x ≤ supNormVec v := by
  refine csInf_le ⟨0, ?_⟩ ⟨v, hv, rfl⟩
  rintro _ ⟨w, _, rfl⟩
  exact (abs_nonneg (w 0)).trans (Finset.le_sup' (fun μ => |w μ|) (Finset.mem_univ 0))
private theorem exists_block_containing (x : FullSpace.Vertex L k 0) :
    ∃ y : Vertex L n k k, ((FullSpace.projVertex L n k 0 x : Vertex L n k 0) :
      PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k y := by
  let r : Fin 4 → ℤ := fun μ => round ((x : AmbientSpace) μ)
  refine ⟨cellOfCoords L n k r, ?_, ?_⟩
  · show TorusMetric.torusSupNorm _ ≤
      PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) / 2
    rw [meshSize_top]
    have hv : torusProj (PeriodicLattice.torusSide L n) (fun μ => (x : AmbientSpace) μ - (r μ : ℝ)) =
        ((FullSpace.projVertex L n k 0 x : Vertex L n k 0) : PeriodicLattice.FourTorus L n) -
          ((cellOfCoords L n k r : Vertex L n k k) : PeriodicLattice.FourTorus L n) := by
      funext μ
      rw [Pi.sub_apply, coe_cellOfCoords]
      simp only [torusProj]
      rw [AddCircle.coe_sub]
      rfl
    refine (torusSupNorm_le_supNormVec hv).trans ?_
    refine Finset.sup'_le _ _ fun μ _ => ?_
    exact abs_sub_round _
  · have e : PeriodicLattice.levelDepth k k + (k : ℤ) = PeriodicLattice.levelDepth k 0 := by
      simp [PeriodicLattice.levelDepth]
    show _ ∈ PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k k + (k : ℤ))
    rw [e]
    exact (FullSpace.projVertex L n k 0 x).2
private theorem exists_near_coords_fine (hL : Conventions.IsAdmissibleBlockingFactor L)
    (x : FullSpace.Vertex L k 0) :
    ∃ w : Fin 4 → ℤ, cellOfCoords L n k w = fineVertexCell (FullSpace.projVertex L n k 0 x) ∧
      ∀ μ, |(x : AmbientSpace) μ - (w μ : ℝ)| < 1 / 2 := by
  have hL0 : 0 < L := by have := hL.2; omega
  set t := fineVertexCell (FullSpace.projVertex L n k 0 x) with ht
  have hm : ((FullSpace.projVertex L n k 0 x : Vertex L n k 0) : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.refinedBlock k t := Classical.epsilon_spec (exists_block_containing x)
  have h₁ : TorusMetric.torusSupNorm
      (((FullSpace.projVertex L n k 0 x : Vertex L n k 0) : PeriodicLattice.FourTorus L n) -
        (t : PeriodicLattice.FourTorus L n)) ≤
      PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) / 2 := hm.1
  rw [meshSize_top] at h₁
  set P : ℤ := (L : ℤ) ^ k with hP
  have hPpos : 0 < P := by positivity
  have hPr : ((P : ℤ) : ℝ) = (L : ℝ) ^ k := by simp [hP]
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hPpos
  obtain ⟨u, hu, hlt⟩ := exists_lift_supNormVec_lt (r := 1 / 2 + 1 / (2 * (P : ℝ)))
    (lt_of_le_of_lt h₁ (by
      have : 0 < 1 / (2 * (P : ℝ)) := by positivity
      linarith))
  obtain ⟨c, hc⟩ := t.2
  have htc : t = cellOfCoords L n k c := by
    refine Subtype.ext ?_
    funext μ
    rw [coe_cellOfCoords, hc μ, meshSize_top, mul_one]
  have hμ : ∀ μ, ∃ τ : ℤ, τ • PeriodicLattice.torusSide L n =
      (x : AmbientSpace) μ - (c μ : ℝ) - u μ := by
    intro μ
    have e : ((u μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) =
        (((x : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) -
          ((c μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
      have := congrFun hu μ
      rw [Pi.sub_apply, htc, coe_cellOfCoords] at this
      exact this
    refine (AddCircle.coe_eq_zero_iff _).1 ?_
    rw [AddCircle.coe_sub, AddCircle.coe_sub, e, sub_self]
  choose τ hτ using hμ
  refine ⟨c + periodSide L n • τ, ?_, fun μ => ?_⟩
  · rw [htc]
    refine Subtype.ext ?_
    funext μ
    rw [coe_cellOfCoords, coe_cellOfCoords]
    have e : (((c + periodSide L n • τ) μ : ℤ) : ℝ) =
        (c μ : ℝ) + τ μ • PeriodicLattice.torusSide L n := by
      rw [torusSide_eq_periodSide, zsmul_eq_mul]
      simp only [Pi.add_apply, periodSide_smul_apply]
      push_cast
      ring
    rw [e, AddCircle.coe_add]
    have : (((τ μ • PeriodicLattice.torusSide L n : ℝ)) :
        AddCircle (PeriodicLattice.torusSide L n)) = 0 :=
      (AddCircle.coe_eq_zero_iff _).2 ⟨τ μ, rfl⟩
    rw [this, add_zero]
  · have hu_eq : (x : AmbientSpace) μ - (((c + periodSide L n • τ) μ : ℤ) : ℝ) = u μ := by
      have e : (((c + periodSide L n • τ) μ : ℤ) : ℝ) =
          (c μ : ℝ) + τ μ • PeriodicLattice.torusSide L n := by
        rw [torusSide_eq_periodSide, zsmul_eq_mul]
        simp only [Pi.add_apply, periodSide_smul_apply]
        push_cast
        ring
      rw [e, hτ μ]
      ring
    rw [hu_eq]
    have hsup : |u μ| < 1 / 2 + 1 / (2 * (P : ℝ)) :=
      (Finset.le_sup' (fun μ => |u μ|) (Finset.mem_univ μ)).trans_lt hlt
    obtain ⟨a, ha⟩ := x.2
    set w₁ := (c + periodSide L n • τ) μ with hw₁
    have hxa : (x : AmbientSpace) μ = (a μ : ℝ) / (P : ℝ) := by
      rw [ha μ, meshAt, hPr]
      simp only [zero_sub, CharP.cast_eq_zero]
      rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
    set e : ℤ := a μ - w₁ * P with he
    have hue : u μ = (e : ℝ) / (P : ℝ) := by
      rw [← hu_eq, hxa, he]
      push_cast
      field_simp
    rw [hue, abs_div, abs_of_pos hPR] at hsup ⊢
    have h2 : 2 * |(e : ℝ)| < (P : ℝ) + 1 := by
      have : |(e : ℝ)| / (P : ℝ) * (2 * (P : ℝ)) <
          (1 / 2 + 1 / (2 * (P : ℝ))) * (2 * (P : ℝ)) :=
        mul_lt_mul_of_pos_right hsup (by positivity)
      have e1 : |(e : ℝ)| / (P : ℝ) * (2 * (P : ℝ)) = 2 * |(e : ℝ)| := by field_simp
      have e2 : (1 / 2 + 1 / (2 * (P : ℝ))) * (2 * (P : ℝ)) = (P : ℝ) + 1 := by field_simp
      rwa [e1, e2] at this
    have h3 : 2 * |e| < P + 1 := by exact_mod_cast h2
    obtain ⟨ρ, hρ⟩ : Odd P := by
      have : Odd (L : ℤ) := by exact_mod_cast hL.1
      exact this.pow
    have h4 : 2 * |e| < P := by omega
    have h5 : 2 * |(e : ℝ)| < (P : ℝ) := by exact_mod_cast h4
    rw [div_lt_iff₀ hPR]
    linarith
private theorem exists_near_coords_top (x : FullSpace.Vertex L k k) :
    ∃ w : Fin 4 → ℤ, cellOfCoords L n k w = FullSpace.projVertex L n k k x ∧
      ∀ μ, |(x : AmbientSpace) μ - (w μ : ℝ)| < 1 / 2 := by
  obtain ⟨a, ha⟩ := x.2
  have h1 : ∀ μ, (x : AmbientSpace) μ = (a μ : ℝ) := by
    intro μ
    rw [ha μ]
    simp [meshAt]
  refine ⟨a, ?_, fun μ => ?_⟩
  · refine Subtype.ext ?_
    funext μ
    rw [coe_cellOfCoords]
    show _ = (((x : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n))
    rw [h1]
  · rw [h1]
    simp
private theorem colour_pairs_quotient {A A' : Type} (sh : (Fin 4 → ℤ) → A → A) (π : A → A')
    (hs : Function.Surjective π)
    (hf : ∀ x y, π x = π y ↔ ∃ m : Fin 4 → ℤ, y = sh (periodSide L n • m) x) :
    Function.Surjective (fun i : Fin 3 × A => (i.1, π i.2)) ∧
    ∀ i i' : Fin 3 × A, ((i.1, π i.2) : Fin 3 × A') = (i'.1, π i'.2) ↔
      ∃ m : Fin 4 → ℤ, i' = (i.1, sh (periodSide L n • m) i.2) := by
  refine ⟨fun p => ?_, fun i i' => ?_⟩
  · obtain ⟨x, hx⟩ := hs p.2
    exact ⟨(p.1, x), by simp [hx]⟩
  · constructor
    · intro e
      obtain ⟨m, hm⟩ := (hf i.2 i'.2).1 (Prod.ext_iff.1 e).2
      refine ⟨m, Prod.ext (Prod.ext_iff.1 e).1.symm hm⟩
    · rintro ⟨m, rfl⟩
      exact Prod.ext rfl ((hf _ _).2 ⟨m, rfl⟩)
theorem cellQuotientsOfTower_holds (hCells : PeriodicLiftCells.CellsAndClassesHold)
    (hSets : TowerIndexSets.Claim) : CellQuotientsOfTower := by
  intro L n k hL hn
  have hc0 := ((hCells L hL k n hn).1 0 (Nat.zero_le _))
  have hck := ((hCells L hL k n hn).1 k le_rfl)
  obtain ⟨hs0, hb0, hp0⟩ := hSets L hL k 0 (Nat.zero_le _)
  obtain ⟨hsk, hbk, -⟩ := hSets L hL k k le_rfl
  have ps0 := colour_pairs_quotient (L := L) (n := n) (fun m (x : FullSpace.Vertex L k 0) =>
    FullSpace.vertexImage (intShift m) x) (FullSpace.projVertex L n k 0) (hc0.1 .vertex).1
    (hc0.1 .vertex).2
  have pb0 := colour_pairs_quotient (L := L) (n := n) (fun m (b : PosEdge L k 0) =>
    shiftEdge m b) (projPositiveEdge L n k 0) (hc0.1 .edge).1 (hc0.1 .edge).2
  have pp0 := colour_pairs_quotient (L := L) (n := n) (fun m (p : FullSpace.Face L k 0) =>
    shiftFace m p) (FullSpace.projFace L n k 0) (hc0.1 .face).1 (hc0.1 .face).2
  have psk := colour_pairs_quotient (L := L) (n := n) (fun m (x : FullSpace.Vertex L k k) =>
    FullSpace.vertexImage (intShift m) x) (FullSpace.projVertex L n k k) (hck.1 .vertex).1
    (hck.1 .vertex).2
  have pbk := colour_pairs_quotient (L := L) (n := n) (fun m (b : PosEdge L k k) =>
    shiftEdge m b) (projPositiveEdge L n k k) (hck.1 .edge).1 (hck.1 .edge).2
  have source_eq : ∀ j (hc : ProjEdgesCompatible L n k j) (b : PosEdge L k j),
      (projPositiveEdge L n k j b).1.source = FullSpace.projVertex L n k j b.1.initial := by
    intro j hc b
    rw [hc.2.1 b]
    exact (hc.1 b.1).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isCellQuotient_of_near hs0.pos_translate ps0.1 ps0.2
      fun i => exists_near_coords_fine hL i.2
  · refine isCellQuotient_of_near hb0.pos_translate pb0.1 pb0.2 fun i => ?_
    obtain ⟨w, h, h'⟩ := exists_near_coords_fine (n := n) hL i.2.1.initial
    refine ⟨w, ?_, h'⟩
    rw [h]
    show _ = fineVertexCell (projPositiveEdge L n k 0 i.2).1.source
    rw [source_eq 0 hc0.2]
  · exact isCellQuotient_of_near hp0.pos_translate pp0.1 pp0.2
      fun i => exists_near_coords_fine hL i.2.corner
  · exact isCellQuotient_of_near hsk.pos_translate psk.1 psk.2
      fun i => exists_near_coords_top i.2
  · refine isCellQuotient_of_near hbk.pos_translate pbk.1 pbk.2 fun i => ?_
    obtain ⟨w, h, h'⟩ := exists_near_coords_top (n := n) i.2.1.initial
    refine ⟨w, ?_, h'⟩
    rw [h]
    show _ = (projPositiveEdge L n k k i.2).1.source
    rw [source_eq k hck.2]
end YangMills.Construction.RunningCouplingSlope.CellQuotientProof
end
