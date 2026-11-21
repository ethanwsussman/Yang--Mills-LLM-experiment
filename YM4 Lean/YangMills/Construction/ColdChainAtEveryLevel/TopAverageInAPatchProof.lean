import YangMills.Construction.ColdChainAtEveryLevel.CurlOfACarriedFormProof
import YangMills.Construction.ColdChainAtEveryLevel.TopAverageInAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LatticePaths ChartCoordinates PlaquetteLinearization PatchPoints GaugeMap LatticeFractionalIntegration
namespace PatchAverage
variable {F : BlockFrame}
section Means
theorem norm_permMean_sub_mean_le (hL : 0 < F.blockSide) (a : Lattice4 → Equiv.Perm (Fin 4) → ℕ → ℍ[ℝ])
    (b : Lattice4 → ℕ → ℍ[ℝ]) (g : Lattice4 → ℕ → ℝ)
    (hab : ∀ p ∈ centredCube F.blockSide, ∀ σ, ∀ r ∈ Finset.range F.blockSide, ‖a p σ r - b p r‖ ≤ g p r) :
    ‖(1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ p ∈ centredCube F.blockSide, ∑ σ : Equiv.Perm (Fin 4),
        ∑ r ∈ Finset.range F.blockSide, a p σ r -
        (1 / (F.blockSide : ℝ) ^ 4) • ∑ p ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide, b p r‖ ≤
      (1 / (F.blockSide : ℝ) ^ 4) * ∑ p ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide, g p r := by
  have hperm : ∀ {M : Type} [AddCommMonoid M] [Module ℝ M] (x : M),
      ∑ _σ : Equiv.Perm (Fin 4), x = (24 : ℝ) • x := by
    intro M _ _ x
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ]
    norm_num [Nat.factorial]
  have e : (1 / (F.blockSide : ℝ) ^ 4) • ∑ p ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide, b p r =
      (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ p ∈ centredCube F.blockSide, ∑ _σ : Equiv.Perm (Fin 4),
        ∑ r ∈ Finset.range F.blockSide, b p r := by
    simp only [hperm, ← Finset.smul_sum, smul_smul]
    congr 1
    field_simp
  rw [e, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity), ← Finset.sum_sub_distrib]
  have h1 : ‖∑ p ∈ centredCube F.blockSide, (∑ σ : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide, a p σ r -
      ∑ _σ : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide, b p r)‖ ≤
      24 * ∑ p ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide, g p r := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have h2 : ∀ σ : Equiv.Perm (Fin 4), ‖∑ r ∈ Finset.range F.blockSide, a p σ r -
        ∑ r ∈ Finset.range F.blockSide, b p r‖ ≤ ∑ r ∈ Finset.range F.blockSide, g p r := by
      intro σ
      rw [← Finset.sum_sub_distrib]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => hab p hp σ r hr)
    refine (Finset.sum_le_sum fun σ _ => h2 σ).trans (le_of_eq ?_)
    rw [hperm, smul_eq_mul]
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _ ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) *
        (24 * ∑ p ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide, g p r) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by field_simp
theorem linearPart_succ (R : F.FieldChain) (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (j : ℕ)
    (y : F.Site (j + 1)) (i : Fin 4) :
    linearPart R (baseOnlyChart u) (j + 1) y i =
      parallelAverage (R j) (linearPart R (baseOnlyChart u) j) (y, i) := by
  simp [linearPart, baseOnlyChart]
theorem nestedAverage_succ {E : Type} [AddCommMonoid E] [Module ℝ E] (f : F.Site 0 → Fin 4 → E) (j : ℕ)
    (y : F.Site (j + 1)) (i : Fin 4) :
    nestedAverage f (j + 1) y i = (1 / (F.blockSide : ℝ) ^ 4) • ∑ p ∈ centredCube F.blockSide,
      ∑ r ∈ Finset.range F.blockSide,
        nestedAverage f j (_root_.YangMills.Construction.BlockAverages.refineSite y + siteOfCoords j p + (r : ℤ) • unitStep j i) i := rfl
theorem nestedAverage_nonneg (hL : 0 < F.blockSide) (f : F.Site 0 → Fin 4 → ℝ) (hf : ∀ x i, 0 ≤ f x i) :
    ∀ (k : ℕ) (x : F.Site k) (i : Fin 4), 0 ≤ nestedAverage f k x i := by
  intro k
  induction k with
  | zero => exact hf
  | succ j ih =>
    intro x i
    rw [nestedAverage_succ, smul_eq_mul]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ih _ _)
theorem norm_linearPart_le (hL : 0 < F.blockSide) (R : F.FieldChain)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) :
    ∀ (k : ℕ) (x : F.Site k) (i : Fin 4), ‖linearPart R (baseOnlyChart u) k x i‖ ≤
      nestedAverage (fun x i => ‖((u x i : imaginaryQuaternions) : ℍ[ℝ])‖) k x i := by
  intro k
  induction k with
  | zero => intro x i; exact le_refl _
  | succ j ih =>
    intro x i
    rw [linearPart_succ, nestedAverage_succ, smul_eq_mul]
    have h := norm_permMean_sub_mean_le (F := F) hL
      (fun p σ r => _root_.YangMills.Construction.BlockAverages.adjointAction (pathHolonomy (R j) (refineSite x) (axisPath p σ ++ List.replicate r (i, true)))
        (linearPart R (baseOnlyChart u) j (_root_.YangMills.Construction.BlockAverages.refineSite x + siteOfCoords j p + (r : ℤ) • unitStep j i) i))
      (fun _ _ => 0)
      (fun p r => nestedAverage (fun x i => ‖((u x i : imaginaryQuaternions) : ℍ[ℝ])‖) j
        (_root_.YangMills.Construction.BlockAverages.refineSite x + siteOfCoords j p + (r : ℤ) • unitStep j i) i)
      (fun p _ σ r _ => by
        rw [sub_zero, _root_.YangMills.Construction.PlaquetteLinearization.norm_adjointAction]
        exact ih _ _)
    simpa [parallelAverage] using h
end Means
section Group
theorem adjointAction_sum {ι : Type} (g : UnitQuaternion) (t : Finset ι) (a : ι → ℍ[ℝ]) :
    _root_.YangMills.Construction.BlockAverages.adjointAction g (∑ i ∈ t, a i) = ∑ i ∈ t, _root_.YangMills.Construction.BlockAverages.adjointAction g (a i) := by
  simp only [_root_.YangMills.Construction.BlockAverages.adjointAction, Finset.mul_sum, Finset.sum_mul]
theorem norm_adjointAction_sub_le (T : UnitQuaternion) (a : ℍ[ℝ]) :
    ‖_root_.YangMills.Construction.BlockAverages.adjointAction T a - a‖ ≤ 2 * ‖(T : ℍ[ℝ]) - 1‖ * ‖a‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction_sub_le <;> assumption
theorem norm_framed_pathHolonomy_sub_one_le {j : ℕ} {f : F.Site j → UnitQuaternion} {R : F.GaugeField j}
    {w0 : F.Site j} {good : Lattice4 → Prop} {ε : ℝ}
    (hstep : ∀ a st, good a → good (a + FlatPairing.stepDisplacement st) →
      ‖(((f (w0 + siteOfCoords j a))⁻¹ * linkValue R (w0 + siteOfCoords j a) st *
        f (w0 + siteOfCoords j (a + FlatPairing.stepDisplacement st)) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    {a : Lattice4} {l : List PathStep} (hp : AllAlong good a l) :
    ‖(((f (w0 + siteOfCoords j a))⁻¹ * pathHolonomy R (w0 + siteOfCoords j a) l *
        f (w0 + siteOfCoords j (endpoint a l)) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ l.length * ε := by
  induction l generalizing a with
  | nil => simp [pathHolonomy, endpoint]
  | cons st r ih =>
    have e1 : w0 + siteOfCoords j a + stepDisplacement j st =
        w0 + siteOfCoords j (a + FlatPairing.stepDisplacement st) := by
      rw [siteOfCoords_add, ← stepDisplacement_eq_siteOfCoords, add_assoc]
    have e2 : (f (w0 + siteOfCoords j a))⁻¹ * pathHolonomy R (w0 + siteOfCoords j a) (st :: r) *
        f (w0 + siteOfCoords j (endpoint a (st :: r))) =
        ((f (w0 + siteOfCoords j a))⁻¹ * linkValue R (w0 + siteOfCoords j a) st *
          f (w0 + siteOfCoords j (a + FlatPairing.stepDisplacement st))) *
          ((f (w0 + siteOfCoords j (a + FlatPairing.stepDisplacement st)))⁻¹ *
            pathHolonomy R (w0 + siteOfCoords j (a + FlatPairing.stepDisplacement st)) r *
            f (w0 + siteOfCoords j (endpoint (a + FlatPairing.stepDisplacement st) r))) := by
      show (f (w0 + siteOfCoords j a))⁻¹ * (linkValue R (w0 + siteOfCoords j a) st *
        pathHolonomy R (w0 + siteOfCoords j a + stepDisplacement j st) r) *
        f (w0 + siteOfCoords j (endpoint (a + FlatPairing.stepDisplacement st) r)) = _
      rw [e1]
      group
    rw [e2]
    refine (norm_coe_mul_sub_one_le _ _).trans ?_
    have h1 := hstep a st hp.1 (allAlong_head hp.2)
    have h2 := ih hp.2
    have hl : (((st :: r).length : ℕ) : ℝ) = r.length + 1 := by simp
    rw [hl]
    linarith
end Group
section Patch
variable {S : Finset F.Cell} {z : F.Cell}
theorem pow_smul_mem_centredCube (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) {p : Lattice4}
    (hp : p ∈ centredCube (F.blockSide ^ (F.top - j))) :
    (fun i => (F.blockSide : ℤ) ^ j * p i) ∈ centredCube (F.blockSide ^ F.top) := by apply _root_.YangMills.Construction.CarriedCurl.scaled_mem_centredCube <;> assumption
theorem baseSite_mem_patch (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {j : ℕ} (hj : j ≤ F.top) {w : F.Site j} (hw : w ∈ sitesOfCells (cellBall S z 10) j) :
    baseSite w ∈ (patchDomain S z).image (patchSite S z) := by
  classical
  obtain ⟨y, hy, p, hp, rfl⟩ := mem_sitesOfCells.1 hw
  obtain ⟨hyS, hyd⟩ := Finset.mem_filter.1 hy
  have e : baseSite (cellCentre j y + siteOfCoords j p) =
      cellCentre 0 y + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ j * p i) := by
    rw [baseSite_add j hj, baseSite_cellCentre j hj]
  rw [e]
  exact Finset.mem_image.2 ⟨_, patchChart_mem_patchDomain hamb hodd he hyS hyd (pow_smul_mem_centredCube hodd hj hp),
    patchSite_patchChart he _⟩
theorem sitesOfCells_mono {S' : Finset F.Cell} (hS : S' ⊆ S) {j : ℕ} {w : F.Site j}
    (hw : w ∈ sitesOfCells S' j) : w ∈ sitesOfCells S j := by
  obtain ⟨y, hy, p, hp, rfl⟩ := mem_sitesOfCells.1 hw
  exact mem_sitesOfCells.2 ⟨y, hS hy, p, hp, rfl⟩
variable {V : F.GaugeField F.top}
theorem norm_framed_linkValue_sub_one_le {j : ℕ} {ε : ℝ} (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (hj : j ≤ F.top)
    (hb : ∀ b ∈ innerBonds S j, baseSite b.1 ∈ (patchDomain S z).image (patchSite S z) →
      baseSite (b.1 + unitStep j b.2) ∈ (patchDomain S z).image (patchSite S z) →
      unitDeviation (referenceInPatchFrame S V z j b.1 b.2) ≤ ε)
    {x : F.Site j} {st : PathStep} (h1 : x ∈ sitesOfCells (cellBall S z 10) j)
    (h2 : x + stepDisplacement j st ∈ sitesOfCells (cellBall S z 10) j) :
    ‖(((frameChange S V z (baseSite x))⁻¹ * linkValue (referenceFieldChain S V j) x st *
        frameChange S V z (baseSite (x + stepDisplacement j st)) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε := by
  classical
  have hsub : cellBall S z 10 ⊆ S := fun y hy => (Finset.mem_filter.1 hy).1
  rcases st with ⟨i, b⟩
  cases b with
  | true =>
    have e : x + stepDisplacement j (i, true) = x + unitStep j i := by simp [stepDisplacement]
    rw [e] at h2 ⊢
    have h3 := hb (x, i) (mem_innerBonds (sitesOfCells_mono hsub h1) (sitesOfCells_mono hsub h2))
      (baseSite_mem_patch hamb hodd he hj h1) (baseSite_mem_patch hamb hodd he hj h2)
    simpa [unitDeviation, referenceInPatchFrame, _root_.YangMills.Construction.BlockAverages.gaugeTransform, linkValue] using h3
  | false =>
    have e : x + stepDisplacement j (i, false) = x - unitStep j i := by simp [stepDisplacement, sub_eq_add_neg]
    rw [e] at h2 ⊢
    have e2 : x - unitStep j i + unitStep j i = x := by abel
    have h3 := hb (x - unitStep j i, i)
      (mem_innerBonds (sitesOfCells_mono hsub h2) (by rw [e2]; exact sitesOfCells_mono hsub h1))
      (baseSite_mem_patch hamb hodd he hj h2) (by simp only [e2]; exact baseSite_mem_patch hamb hodd he hj h1)
    simp only [unitDeviation, referenceInPatchFrame, _root_.YangMills.Construction.BlockAverages.gaugeTransform, e2, inv_inv] at h3
    rw [← norm_coe_inv_sub_one] at h3
    have e3 : ((frameChange S V z (baseSite (x - unitStep j i)))⁻¹ *
        referenceFieldChain S V j (x - unitStep j i) i * frameChange S V z (baseSite x))⁻¹ =
        (frameChange S V z (baseSite x))⁻¹ * linkValue (referenceFieldChain S V j) x (i, false) *
          frameChange S V z (baseSite (x - unitStep j i)) := by
      simp only [linkValue, Bool.false_eq_true, if_false]
      group
    rwa [e3] at h3
theorem add_smul_basisVector_mem_twoBlockHull {L : ℕ} {p : Lattice4} {k : ℕ} (hp : p ∈ centredCube L)
    (hk : k ≤ L) (i : Fin 4) : p + (k : ℤ) • basisVector i ∈ FlatPairing.twoBlockHull L i := by
  intro μ
  have h1 := ((_root_.YangMills.Construction.LatticePaths.mem_centredCube_iff L p).1 hp) μ
  have e : (p + (k : ℤ) • basisVector i) μ = p μ + if μ = i then (k : ℤ) else 0 := by
    by_cases hμ : μ = i
    · subst hμ
      simp [basisVector]
    · simp [basisVector, hμ]
  rw [e]
  split_ifs <;> constructor <;> omega
theorem siteOfCoords_add_smul_basisVector {j : ℕ} (w : F.Site j) (p : Lattice4) (k : ℤ) (i : Fin 4) :
    w + siteOfCoords j (p + k • basisVector i) = w + siteOfCoords j p + k • unitStep j i := by
  rw [_root_.YangMills.Construction.BlockAverages.siteOfCoords_add, add_assoc]
  congr 2
  funext l
  simp [siteOfCoords, unitStep_eq]
theorem line_mem_innerBonds {S' : Finset F.Cell} (hodd : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S' (j + 1)) {p : Lattice4}
    (hp : p ∈ centredCube F.blockSide) {r : ℕ} (hr : r < F.blockSide) :
    (_root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j p + (r : ℤ) • unitStep j c.2, c.2) ∈ innerBonds S' j := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.line_mem_innerBonds <;> assumption
theorem norm_framed_contour_sub_one_le {j : ℕ} {ε : ℝ} (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (hj : j + 1 ≤ F.top) (hε : 0 ≤ ε)
    (hb : ∀ b ∈ innerBonds S j, baseSite b.1 ∈ (patchDomain S z).image (patchSite S z) →
      baseSite (b.1 + unitStep j b.2) ∈ (patchDomain S z).image (patchSite S z) →
      unitDeviation (referenceInPatchFrame S V z j b.1 b.2) ≤ ε)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds (cellBall S z 10) (j + 1)) {p : Lattice4}
    (hp : p ∈ centredCube F.blockSide) (σ : Equiv.Perm (Fin 4)) {r : ℕ} (hr : r < F.blockSide) :
    ‖(((frameChange S V z (baseSite (_root_.YangMills.Construction.BlockAverages.refineSite c.1)))⁻¹ *
        pathHolonomy (referenceFieldChain S V j) (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (axisPath p σ ++ List.replicate r (c.2, true)) *
        frameChange S V z (baseSite (_root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j p + (r : ℤ) • unitStep j c.2)) :
          UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ (3 * F.blockSide) * ε := by
  have hL1 : 1 ≤ F.blockSide := hodd.pos
  have e1 : FlatPairing.stepDisplacement (c.2, true) = basisVector c.2 := by simp [FlatPairing.stepDisplacement]
  have q1 : AllAlong (fun a => a ∈ FlatPairing.twoBlockHull F.blockSide c.2) 0 (axisPath p σ) :=
    allAlong_mono (fun v hv => mem_twoBlockHull_of_between hp hv hL1) (axisPath_spec p σ).1
  have q2 : AllAlong (fun a => a ∈ FlatPairing.twoBlockHull F.blockSide c.2) (endpoint 0 (axisPath p σ))
      (List.replicate r (c.2, true)) := by
    rw [(axisPath_spec p σ).2]
    refine allAlong_replicate fun k hk => ?_
    rw [e1]
    exact add_smul_basisVector_mem_twoBlockHull hp (by omega) c.2
  have hstep : ∀ a st, a ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      a + FlatPairing.stepDisplacement st ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      ‖(((frameChange S V z (baseSite (_root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j a)))⁻¹ *
        linkValue (referenceFieldChain S V j) (_root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j a) st *
        frameChange S V z (baseSite (_root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j (a + FlatPairing.stepDisplacement st))) :
          UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε := by
    intro a st h1 h2
    have s1 := refineSite_add_mem_of_mem_twoBlockHull hodd hj hc h1
    have s2 := refineSite_add_mem_of_mem_twoBlockHull hodd hj hc h2
    have e2 : _root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j a + stepDisplacement j st =
        _root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j (a + FlatPairing.stepDisplacement st) := by
      rw [siteOfCoords_add, ← stepDisplacement_eq_siteOfCoords, add_assoc]
    have h3 := norm_framed_linkValue_sub_one_le (x := _root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j a) (st := st)
      hamb hodd he (by omega) hb s1 (by rw [e2]; exact s2)
    rwa [e2] at h3
  have main : ‖(((frameChange S V z (baseSite (_root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j (0 : Lattice4))))⁻¹ *
      pathHolonomy (referenceFieldChain S V j) (_root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j (0 : Lattice4))
        (axisPath p σ ++ List.replicate r (c.2, true)) *
      frameChange S V z (baseSite (_root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j
        (endpoint 0 (axisPath p σ ++ List.replicate r (c.2, true))))) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      ((axisPath p σ ++ List.replicate r (c.2, true)).length : ℝ) * ε :=
    norm_framed_pathHolonomy_sub_one_le (f := fun w => frameChange S V z (baseSite w))
      (R := referenceFieldChain S V j) (w0 := _root_.YangMills.Construction.BlockAverages.refineSite c.1)
      (good := fun a => a ∈ FlatPairing.twoBlockHull F.blockSide c.2) hstep (allAlong_append q1 q2)
  have eEnd : _root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j (endpoint 0 (axisPath p σ ++ List.replicate r (c.2, true))) =
      _root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j p + (r : ℤ) • unitStep j c.2 := by
    rw [endpoint_append, (axisPath_spec p σ).2, endpoint_replicate, e1, siteOfCoords_add_smul_basisVector]
  rw [add_siteOfCoords_zero, eEnd] at main
  refine main.trans (mul_le_mul_of_nonneg_right ?_ hε)
  rw [List.length_append, length_axisPath, List.length_replicate]
  obtain ⟨k, hk⟩ := hodd
  have hhalf : ((F.blockSide : ℤ) - 1) / 2 = k := by rw [hk]; push_cast; omega
  have hb' : ∀ μ, (p μ).natAbs ≤ k := by
    intro μ
    have h1 := ((_root_.YangMills.Construction.LatticePaths.mem_centredCube_iff _ _).1 hp) μ
    rw [hhalf] at h1
    omega
  have h5 : (p (σ 0)).natAbs + (p (σ 1)).natAbs + (p (σ 2)).natAbs + (p (σ 3)).natAbs + r ≤
      3 * F.blockSide := by
    have := hb' (σ 0)
    have := hb' (σ 1)
    have := hb' (σ 2)
    have := hb' (σ 3)
    omega
  exact_mod_cast h5
theorem patchFrameForm_linearPart_succ {j : ℕ} (hj' : j + 1 ≤ F.top) (R : F.FieldChain)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (y : F.Site (j + 1)) (i : Fin 4) :
    patchFrameForm S V z (linearPart R (baseOnlyChart u) (j + 1)) y i =
      (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ p ∈ centredCube F.blockSide, ∑ σ : Equiv.Perm (Fin 4),
        ∑ r ∈ Finset.range F.blockSide,
        _root_.YangMills.Construction.BlockAverages.adjointAction ((frameChange S V z (baseSite (refineSite y)))⁻¹ *
            pathHolonomy (R j) (_root_.YangMills.Construction.BlockAverages.refineSite y) (axisPath p σ ++ List.replicate r (i, true)) *
            frameChange S V z (baseSite (_root_.YangMills.Construction.BlockAverages.refineSite y + siteOfCoords j p + (r : ℤ) • unitStep j i)))
          (patchFrameForm S V z (linearPart R (baseOnlyChart u) j)
            (_root_.YangMills.Construction.BlockAverages.refineSite y + siteOfCoords j p + (r : ℤ) • unitStep j i) i) := by
  show _root_.YangMills.Construction.BlockAverages.adjointAction (frameChange S V z (baseSite y))⁻¹ (linearPart R (baseOnlyChart u) (j + 1) y i) = _
  rw [linearPart_succ, ← baseSite_refineSite j hj' y]
  simp only [parallelAverage, _root_.YangMills.Construction.PlaquetteLinearization.adjointAction_smul, adjointAction_sum, patchFrameForm]
  congr 1
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun r _ => ?_
  rw [← _root_.YangMills.Construction.PlaquetteLinearization.adjointAction_mul, ← _root_.YangMills.Construction.PlaquetteLinearization.adjointAction_mul]
  congr 1
  group
end Patch
theorem norm_adjointAction_sub_le_of (T : UnitQuaternion) {A P : ℍ[ℝ]} {t e g : ℝ} (hT : ‖(T : ℍ[ℝ]) - 1‖ ≤ t)
    (hA : ‖A‖ ≤ g) (hP : ‖A - P‖ ≤ e * g) : ‖_root_.YangMills.Construction.BlockAverages.adjointAction T A - P‖ ≤ (2 * t + e) * g := by
  have h1 := norm_adjointAction_sub_le T A
  have h2 := norm_sub_le_norm_sub_add_norm_sub (_root_.YangMills.Construction.BlockAverages.adjointAction T A) A P
  have h3 : ‖(T : ℍ[ℝ]) - 1‖ * ‖A‖ ≤ t * g := mul_le_mul hT hA (norm_nonneg _) ((norm_nonneg _).trans hT)
  nlinarith
theorem levelScale_succ (hL : 0 < F.blockSide) {j : ℕ} (hj : j < F.top) :
    levelScale F (j + 1) = F.blockSide * levelScale F j := by apply _root_.YangMills.Construction.CarriedCurl.levelScale_succ <;> assumption
end PatchAverage
open PatchAverage in
theorem PatchAverage.patchNestedAverage_holds (hB : referenceBoundsStatement) : patchNestedAverageStatement := by
  obtain ⟨C0, c, L1, hC0, hc, hB⟩ := hB
  refine ⟨12 * C0, c, max L1 2, by positivity, hc, ?_⟩
  intro F m S hodd hL1 hamb hm hreg s V hs hsc hcold z hz u k hk b hb hb1 hb2
  classical
  have hL1' : L1 ≤ F.blockSide := (le_max_left _ _).trans hL1
  have hL2 : 2 ≤ F.blockSide := (le_max_right _ _).trans hL1
  have hL := hodd.pos
  have hLR : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast hL2
  obtain ⟨hr1, -⟩ := hB F m S hodd hL1' hamb hm hreg s V hs hsc hcold
  obtain ⟨he, -⟩ := closedOrthant_spec (S := S) hreg (show 32 ≤ m by omega) z
  have hl0 : ∀ j, 0 ≤ levelScale F j := fun j => by
    simp only [levelScale]
    positivity
  have hG : ∀ (k : ℕ) (x : F.Site k) (i : Fin 4),
      0 ≤ nestedAverage (fun x i => ‖((u x i : imaginaryQuaternions) : ℍ[ℝ])‖) k x i :=
    nestedAverage_nonneg hL _ fun _ _ => norm_nonneg _
  have main : ∀ k, k ≤ F.top → ∀ b ∈ innerBonds (cellBall S z 10) k,
      ‖patchFrameForm S V z (linearPart (referenceFieldChain S V) (baseOnlyChart u) k) b.1 b.2 -
          nestedAverage (patchFrameForm S V z (fun x i => ((u x i : imaginaryQuaternions) : ℍ[ℝ]))) k b.1 b.2‖ ≤
        12 * C0 * s * levelScale F k *
          nestedAverage (fun x i => ‖((u x i : imaginaryQuaternions) : ℍ[ℝ])‖) k b.1 b.2 := by
    intro k
    induction k with
    | zero =>
      intro _ b _
      have e : patchFrameForm S V z (linearPart (referenceFieldChain S V) (baseOnlyChart u) 0) b.1 b.2 -
          nestedAverage (patchFrameForm S V z (fun x i => ((u x i : imaginaryQuaternions) : ℍ[ℝ]))) 0 b.1 b.2 = 0 :=
        sub_self _
      rw [e, norm_zero]
      exact mul_nonneg (mul_nonneg (by positivity) (hl0 0)) (hG 0 _ _)
    | succ j ih =>
      intro hj c' hc'
      have hjn : j < F.top := hj
      have hε : 0 ≤ C0 * s * levelScale F j := mul_nonneg (by positivity) (hl0 j)
      set κ : ℝ := 2 * ((3 * F.blockSide) * (C0 * s * levelScale F j)) + 12 * C0 * s * levelScale F j with hκd
      rw [patchFrameForm_linearPart_succ hj, nestedAverage_succ]
      have hm' := norm_permMean_sub_mean_le (F := F) hL
        (fun p σ r => _root_.YangMills.Construction.BlockAverages.adjointAction ((frameChange S V z (baseSite (refineSite c'.1)))⁻¹ *
            pathHolonomy (referenceFieldChain S V j) (_root_.YangMills.Construction.BlockAverages.refineSite c'.1) (axisPath p σ ++ List.replicate r (c'.2, true)) *
            frameChange S V z (baseSite (_root_.YangMills.Construction.BlockAverages.refineSite c'.1 + siteOfCoords j p + (r : ℤ) • unitStep j c'.2)))
          (patchFrameForm S V z (linearPart (referenceFieldChain S V) (baseOnlyChart u) j)
            (_root_.YangMills.Construction.BlockAverages.refineSite c'.1 + siteOfCoords j p + (r : ℤ) • unitStep j c'.2) c'.2))
        (fun p r => nestedAverage (patchFrameForm S V z (fun x i => ((u x i : imaginaryQuaternions) : ℍ[ℝ]))) j
            (refineSite c'.1 + siteOfCoords j p + (r : ℤ) • unitStep j c'.2) c'.2)
        (fun p r => κ * nestedAverage (fun x i => ‖((u x i : imaginaryQuaternions) : ℍ[ℝ])‖) j
            (refineSite c'.1 + siteOfCoords j p + (r : ℤ) • unitStep j c'.2) c'.2)
        (fun p hp σ r hr => by
          have hr' := Finset.mem_range.1 hr
          have hT := norm_framed_contour_sub_one_le hamb hodd he hj hε (hr1 j hjn z hz) hc' hp σ hr'
          have hbond := line_mem_innerBonds hodd hj hc' hp hr'
          have hP := ih (by omega) _ hbond
          refine norm_adjointAction_sub_le_of _ hT ?_ hP
          rw [patchFrameForm, _root_.YangMills.Construction.PlaquetteLinearization.norm_adjointAction]
          exact norm_linearPart_le hL _ u j _ _)
      refine hm'.trans ?_
      have e : (1 / (F.blockSide : ℝ) ^ 4) * ∑ p ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
            κ * nestedAverage (fun x i => ‖((u x i : imaginaryQuaternions) : ℍ[ℝ])‖) j
              (_root_.YangMills.Construction.BlockAverages.refineSite c'.1 + siteOfCoords j p + (r : ℤ) • unitStep j c'.2) c'.2 =
          κ * nestedAverage (fun x i => ‖((u x i : imaginaryQuaternions) : ℍ[ℝ])‖) (j + 1) c'.1 c'.2 := by
        rw [nestedAverage_succ, smul_eq_mul]
        simp only [← Finset.mul_sum]
        ring
      rw [e]
      refine mul_le_mul_of_nonneg_right ?_ (hG _ _ _)
      rw [levelScale_succ hL hjn, hκd]
      have h1 : 0 ≤ C0 * s * levelScale F j := hε
      have h2 : 0 ≤ (6 * (F.blockSide : ℝ) - 12) * (C0 * s * levelScale F j) :=
        mul_nonneg (by linarith) h1
      nlinarith
  have hcell : ∀ {w : F.Site k}, w ∈ sitesOfCells S k → enclosingCell w ∈ cellBall S z 10 →
      w ∈ sitesOfCells (cellBall S z 10) k := by
    intro w hw hc2
    obtain ⟨y, hy, p, hp, rfl⟩ := mem_sitesOfCells.1 hw
    rw [enclosingCell_cellCentre_add hodd y p hp] at hc2
    exact mem_sitesOfCells.2 ⟨y, hc2, p, hp, rfl⟩
  have hbS := Finset.mem_filter.1 hb
  have h1 : b.1 ∈ sitesOfCells S k := (Finset.mem_product.1 hbS.1).1
  exact main k hk b (mem_innerBonds (hcell h1 hb1) (hcell hbS.2 hb2))
end YangMills.Construction
end
