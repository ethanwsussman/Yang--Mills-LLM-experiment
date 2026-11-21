import YangMills.Construction.ColdChainAtEveryLevel.CurlOfACarriedFormProof
import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.ColdChainAtEveryLevel.VariationsOfAField
import Mathlib
import YangMills.Construction.ColdChainAtEveryLevel.OneStepOfTheCoordinatesProof
set_option autoImplicit false

noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def topLevelAverage (R : F.FieldChain) (A : ChainChart F) : F.Site F.top → Fin 4 → imaginaryQuaternions :=
  fun y i => ⟨pureComponent (linearPart R A F.top y i), by show (pureComponent _).re = 0; simp [pureComponent]⟩
def topAverageCurlBoundStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c : ℝ, 0 < c ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V → ∀ A : ChainChart F,
        ∑ p ∈ innerPlaquettes S F.top, ‖variationCurl V (topLevelAverage (referenceFieldChain S V) A) p‖ ^ 2 ≤
          C * (∑ q ∈ plaquettesOver S S 0, ‖linearizedCurl (referenceFieldChain S V 0) A.fine q‖ ^ 2 +
              ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1), ‖A.coarse j c.1 c.2‖ ^ 2) +
            C * s ^ 2 * weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ^ 2
end YangMills.Construction.BlockAverages
end

noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TopAverageCurl
open BlockAverages BlockLines BlockWeights PlaquetteExpansion LatticePaths LatticeFractionalIntegration GaugeMap
  PatchPoints BlockAverages.ChartCoordinates
variable {F : BlockFrame}
def gaugedForm (γ : F.Site 0 → UnitQuaternion) {j : ℕ} (f : F.Site j → Fin 4 → ℍ[ℝ]) : F.Site j → Fin 4 → ℍ[ℝ] :=
  fun x i => _root_.YangMills.Construction.BlockAverages.adjointAction (γ (baseSite x)) (f x i)
def gaugedField (γ : F.Site 0 → UnitQuaternion) {j : ℕ} (X : F.GaugeField j) : F.GaugeField j :=
  gaugeTransform (fun x => γ (baseSite x)) X
theorem endpoint_axisPath_append_replicate (h : Lattice4) (π : Equiv.Perm (Fin 4)) (i : Fin 4) (r : ℕ) :
    endpoint 0 (axisPath h π ++ List.replicate r (i, true)) = h + (r : ℤ) • basisVector i := by apply _root_.YangMills.Construction.CarriedCurl.endpoint_axisPath_append_replicate <;> assumption
theorem adjointAction_conj_pair (a b g : UnitQuaternion) (w : ℍ[ℝ]) :
    _root_.YangMills.Construction.BlockAverages.adjointAction (a * g * b⁻¹) (_root_.YangMills.Construction.BlockAverages.adjointAction b w) = _root_.YangMills.Construction.BlockAverages.adjointAction a (_root_.YangMills.Construction.BlockAverages.adjointAction g w) := by
  rw [_root_.YangMills.Construction.BlockAverages.adjointAction_mul, _root_.YangMills.Construction.BlockAverages.adjointAction_mul, ← _root_.YangMills.Construction.BlockAverages.adjointAction_mul b⁻¹ b, inv_mul_cancel, _root_.YangMills.Construction.BlockAverages.adjointAction_one]
theorem covariantCurlAt_gaugedField (γ : F.Site 0 → UnitQuaternion) {j : ℕ} (X : F.GaugeField j)
    (f : F.Site j → Fin 4 → ℍ[ℝ]) (q : F.Site j × Fin 4 × Fin 4) :
    covariantCurlAt (gaugedField γ X) (gaugedForm γ f) q = adjointAction (γ (baseSite q.1)) (covariantCurlAt X f q) := by apply _root_.YangMills.Construction.CarriedCurl.covariantCurlAt_frameField <;> assumption
theorem norm_pathHolonomy_sub_one_le {j : ℕ} {Dset : Set (F.Site j)} {Y : F.GaugeField j} {ε : ℝ}
    (hY : ∀ x i, x ∈ Dset → x + unitStep j i ∈ Dset → ‖((Y x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε) (x0 : F.Site j) :
    ∀ (l : List PathStep) (v : Lattice4), AllAlong (fun v => x0 + siteOfCoords j v ∈ Dset) v l →
      ‖((pathHolonomy Y (x0 + siteOfCoords j v) l : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ l.length * ε := by apply _root_.YangMills.Construction.CarriedCurl.norm_pathHolonomy_sub_one_le <;> assumption
theorem allAlong_transportPath {D : Finset F.Cell} (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds D (j + 1)) {h : Lattice4} (hh : h ∈ centredCube F.blockSide)
    (π : Equiv.Perm (Fin 4)) {r : ℕ} (hr : r < F.blockSide) :
    AllAlong (fun v => refineSite c.1 + siteOfCoords j v ∈ (sitesOfCells D j : Set (F.Site j))) 0
      (axisPath h π ++ List.replicate r (c.2, true)) := by apply _root_.YangMills.Construction.CarriedCurl.allAlong_transportPath <;> assumption
theorem length_transportPath_le (hL : 1 ≤ F.blockSide) {h : Lattice4} (hh : h ∈ centredCube F.blockSide)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) {r : ℕ} (hr : r < F.blockSide) :
    ((axisPath h π ++ List.replicate r (i, true)).length : ℝ) ≤ 3 * F.blockSide := by apply _root_.YangMills.Construction.CarriedCurl.length_transportPath_le <;> assumption
def flatAverage {j : ℕ} (g : F.Site j → Fin 4 → ℍ[ℝ]) (c : F.Site (j + 1) × Fin 4) : ℍ[ℝ] :=
  (1 / (F.blockSide : ℝ) ^ 4) • ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
    g (lineBond c h r).1 (lineBond c h r).2
theorem flatAverage_eq_perm_sum (hL : 0 < F.blockSide) {j : ℕ} (g : F.Site j → Fin 4 → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) :
    flatAverage g c = (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide,
      ∑ _π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide, g (lineBond c h r).1 (lineBond c h r).2 := by
  have e : ∀ h, ∑ _π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide, g (lineBond c h r).1 (lineBond c h r).2 =
      (24 : ℝ) • ∑ r ∈ Finset.range F.blockSide, g (lineBond c h r).1 (lineBond c h r).2 := by
    intro h
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    simp [Nat.factorial, ← Nat.cast_smul_eq_nsmul ℝ]
  simp only [e]
  rw [← Finset.smul_sum, smul_smul]
  unfold flatAverage
  congr 1
  field_simp
theorem norm_parallelAverage_sub_flatAverage_le (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top)
    {D : Finset F.Cell} {Y : F.GaugeField j} {ε : ℝ} (hε : 0 ≤ ε)
    (hY : ∀ x i, x ∈ sitesOfCells D j → x + unitStep j i ∈ sitesOfCells D j →
      ‖((Y x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (g : F.Site j → Fin 4 → ℍ[ℝ]) {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds D (j + 1)) :
    ‖parallelAverage Y g c - flatAverage g c‖ ≤
      6 * F.blockSide * ε * lineBlockAverage (fun x i => ‖g x i‖) c := by
  have hL := hodd.pos
  rw [flatAverage_eq_perm_sum hL, lineBlockAverage_eq]
  unfold parallelAverage
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
  simp only [← Finset.sum_sub_distrib]
  have hterm : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4), ∀ r ∈ Finset.range F.blockSide,
      ‖_root_.YangMills.Construction.BlockAverages.adjointAction (pathHolonomy Y (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
          (g (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2) -
          g (lineBond c h r).1 (lineBond c h r).2‖ ≤
        6 * F.blockSide * ε * ‖g (lineBond c h r).1 (lineBond c h r).2‖ := by
    intro h hh π r hr
    have hr' := Finset.mem_range.1 hr
    have h1 := norm_pathHolonomy_sub_one_le (Dset := (sitesOfCells D j : Set (F.Site j))) (Y := Y) hY
      (refineSite c.1) _ 0 (allAlong_transportPath hodd hj hc hh π hr')
    rw [add_siteOfCoords_zero] at h1
    have h2 := length_transportPath_le hL hh π c.2 hr'
    have h3 : ‖((pathHolonomy Y (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)) : UnitQuaternion) :
        ℍ[ℝ]) - 1‖ ≤ 3 * F.blockSide * ε :=
      h1.trans (mul_le_mul_of_nonneg_right h2 hε)
    have h4 := norm_adjointAction_sub_le
      (pathHolonomy Y (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
      (g (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2)
    refine h4.trans ?_
    have h5 := mul_le_mul_of_nonneg_right h3
      (norm_nonneg (g (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2))
    show _ ≤ 6 * F.blockSide * ε * ‖g (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2‖
    linarith
  have hsum : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide,
      (_root_.YangMills.Construction.BlockAverages.adjointAction (pathHolonomy Y (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
          (g (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2) -
        g (lineBond c h r).1 (lineBond c h r).2)‖ ≤
      24 * (6 * F.blockSide * ε * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
        ‖g (lineBond c h r).1 (lineBond c h r).2‖) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun h hh => ?_
    refine (norm_sum_le _ _).trans ?_
    have h2 : ∀ π : Equiv.Perm (Fin 4), ‖∑ r ∈ Finset.range F.blockSide,
        (_root_.YangMills.Construction.BlockAverages.adjointAction (pathHolonomy Y (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
          (g (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2) -
          g (lineBond c h r).1 (lineBond c h r).2)‖ ≤
        6 * F.blockSide * ε * ∑ r ∈ Finset.range F.blockSide, ‖g (lineBond c h r).1 (lineBond c h r).2‖ := by
      intro π
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun r hr => hterm h hh π r hr
    refine (Finset.sum_le_sum fun π _ => h2 π).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    simp [Nat.factorial]
  calc _ ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) *
        (24 * (6 * F.blockSide * ε * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
          ‖g (lineBond c h r).1 (lineBond c h r).2‖)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
        field_simp
def flatTransported (g0 : F.Site 0 → Fin 4 → ℍ[ℝ]) : (j : ℕ) → F.Site j → Fin 4 → ℍ[ℝ]
  | 0 => g0
  | j + 1 => fun y i => flatAverage (flatTransported g0 j) (y, i)
def normTransported (g0 : F.Site 0 → Fin 4 → ℝ) : (j : ℕ) → F.Site j → Fin 4 → ℝ
  | 0 => g0
  | j + 1 => fun y i => lineBlockAverage (normTransported g0 j) (y, i)
theorem normTransported_nonneg {g0 : F.Site 0 → Fin 4 → ℝ} (h : ∀ x i, 0 ≤ g0 x i) :
    ∀ j x i, 0 ≤ normTransported g0 j x i := by
  intro j
  induction j with
  | zero => exact h
  | succ j ih => exact fun y i => lineBlockAverage_nonneg ih (y, i)
theorem sum_normTransported_pow_four_le (hodd : Odd F.blockSide) (D : Finset F.Cell) {g0 : F.Site 0 → Fin 4 → ℝ}
    (h : ∀ x i, 0 ≤ g0 x i) :
    ∀ j, j ≤ F.top → ∑ b ∈ innerBonds D j, normTransported g0 j b.1 b.2 ^ 4 ≤
      ∑ b ∈ innerBonds D 0, g0 b.1 b.2 ^ 4 := by
  intro j
  induction j with
  | zero => intro _; exact le_rfl
  | succ j ih =>
    intro hj
    exact (sum_lineBlockAverage_pow_four_le (by omega) hodd (innerBonds D (j + 1)) subset_rfl _
      (normTransported_nonneg h j)).trans (ih (by omega))
section Levels
variable (R : F.FieldChain) (γ : F.Site 0 → UnitQuaternion) (f : F.Site 0 → Fin 4 → ℍ[ℝ])
def gaugedTransportedForm (j : ℕ) : F.Site j → Fin 4 → ℍ[ℝ] := gaugedForm γ (transportedForm R f j)
theorem gaugedTransportedForm_succ {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (i : Fin 4) :
    gaugedTransportedForm R γ f (j + 1) y i =
      parallelAverage (gaugedField γ (R j)) (gaugedTransportedForm R γ f j) (y, i) := by apply _root_.YangMills.Construction.CarriedCurl.framedTransportedForm_succ <;> assumption
theorem norm_gaugedTransportedForm_le (hodd : Odd F.blockSide) : ∀ j, j ≤ F.top → ∀ x i,
    ‖gaugedTransportedForm R γ f j x i‖ ≤
      normTransported (fun x i => ‖gaugedTransportedForm R γ f 0 x i‖) j x i := by
  intro j
  induction j with
  | zero => intro _ x i; exact le_rfl
  | succ j ih =>
    intro hj y i
    rw [gaugedTransportedForm_succ R γ f (by omega)]
    refine (norm_parallelAverage_le hodd _ _ (y, i)).trans ?_
    have e := lineBlockAverage_eq (fun x i => ‖gaugedTransportedForm R γ f j x i‖)
      ((y, i) : F.Site (j + 1) × Fin 4)
    rw [← e]
    exact lineBlockAverage_mono (ih (by omega)) (y, i)
theorem levelScale_succ_eq (hL : 0 < F.blockSide) {j : ℕ} (hj : j < F.top) :
    levelScale F (j + 1) = F.blockSide * levelScale F j := by apply _root_.YangMills.Construction.CarriedCurl.levelScale_succ <;> assumption
theorem norm_gaugedTransportedForm_sub_flat_le (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide) {D : Finset F.Cell}
    {E : ℝ} (hE : 0 ≤ E)
    (hR : ∀ j, j < F.top → ∀ x i, x ∈ sitesOfCells D j → x + unitStep j i ∈ sitesOfCells D j →
      ‖((gaugedField γ (R j) x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ E * levelScale F j) :
    ∀ j, j ≤ F.top → ∀ b ∈ innerBonds D j,
      ‖gaugedTransportedForm R γ f j b.1 b.2 - flatTransported (gaugedTransportedForm R γ f 0) j b.1 b.2‖ ≤
        12 * E * levelScale F j * normTransported (fun x i => ‖gaugedTransportedForm R γ f 0 x i‖) j b.1 b.2 := by
  have hLpos := hodd.pos
  have hL2 : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
  have hl0 : ∀ j, 0 ≤ levelScale F j := fun j => by
    unfold levelScale
    positivity
  have hm0 := normTransported_nonneg (g0 := fun x i => ‖gaugedTransportedForm R γ f 0 x i‖)
    (fun _ _ => norm_nonneg _)
  intro j
  induction j with
  | zero =>
    intro _ b _
    simp only [flatTransported, sub_self, norm_zero]
    have := hm0 0 b.1 b.2
    have h2 := hl0 0
    positivity
  | succ j ih =>
    intro hj c hc
    have hjn : j < F.top := by omega
    have e1 : gaugedTransportedForm R γ f (j + 1) c.1 c.2 =
        parallelAverage (gaugedField γ (R j)) (gaugedTransportedForm R γ f j) c :=
      gaugedTransportedForm_succ R γ f hjn c.1 c.2
    have e2 : flatTransported (gaugedTransportedForm R γ f 0) (j + 1) c.1 c.2 =
        flatAverage (flatTransported (gaugedTransportedForm R γ f 0) j) c := rfl
    rw [e1, e2]
    set g := gaugedTransportedForm R γ f j with hg
    set P := flatTransported (gaugedTransportedForm R γ f 0) j with hP
    set m := normTransported (fun x i => ‖gaugedTransportedForm R γ f 0 x i‖) j with hm
    have hmc : normTransported (fun x i => ‖gaugedTransportedForm R γ f 0 x i‖) (j + 1) c.1 c.2 =
        lineBlockAverage m c := rfl
    rw [hmc]
    have a1 := norm_parallelAverage_sub_flatAverage_le hodd hjn (mul_nonneg hE (hl0 j)) (hR j hjn) g hc
    have a2 : lineBlockAverage (fun x i => ‖g x i‖) c ≤ lineBlockAverage m c :=
      lineBlockAverage_mono (norm_gaugedTransportedForm_le R γ f hodd j hjn.le) c
    have a3 : ‖flatAverage g c - flatAverage P c‖ ≤ 12 * E * levelScale F j * lineBlockAverage m c := by
      unfold flatAverage
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity), lineBlockAverage_eq]
      simp only [← Finset.sum_sub_distrib]
      have hb : ‖∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
          (g (lineBond c h r).1 (lineBond c h r).2 - P (lineBond c h r).1 (lineBond c h r).2)‖ ≤
          12 * E * levelScale F j * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
            m (lineBond c h r).1 (lineBond c h r).2 := by
        refine (norm_sum_le _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun h hh => ?_
        refine (norm_sum_le _ _).trans ?_
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun r hr =>
          ih hjn.le _ (lineBond_mem_innerBonds hjn hodd c hc h hh r (Finset.mem_range.1 hr))
      have h3 := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 1 / (F.blockSide : ℝ) ^ 4)
      refine h3.trans (le_of_eq ?_)
      ring
    have hpa : 0 ≤ lineBlockAverage m c := lineBlockAverage_nonneg (hm0 j) c
    have hstep := levelScale_succ_eq hLpos hjn
    have hlj := hl0 j
    have e3 : parallelAverage (gaugedField γ (R j)) g c - flatAverage P c =
        (parallelAverage (gaugedField γ (R j)) g c - flatAverage g c) + (flatAverage g c - flatAverage P c) := by
      abel
    rw [e3, hstep]
    refine (norm_add_le _ _).trans ?_
    have h5 : 6 * F.blockSide * (E * levelScale F j) * lineBlockAverage (fun x i => ‖g x i‖) c ≤
        6 * F.blockSide * (E * levelScale F j) * lineBlockAverage m c :=
      mul_le_mul_of_nonneg_left a2 (by positivity)
    have h6 : 0 ≤ E * levelScale F j * lineBlockAverage m c := by positivity
    nlinarith
end Levels
def flatCurl {j : ℕ} (f : F.Site j → Fin 4 → ℍ[ℝ]) (q : F.Site j × Fin 4 × Fin 4) : ℍ[ℝ] :=
  f q.1 q.2.1 + f (q.1 + unitStep j q.2.1) q.2.2 - f (q.1 + unitStep j q.2.2) q.2.1 - f q.1 q.2.2
def subSquareCorner {j : ℕ} (y : F.Site (j + 1)) (μ ν : Fin 4) (h : Fin 4 → ℤ) (a b : ℕ) : F.Site j :=
  refineSite y + siteOfCoords j h + (a : ℤ) • unitStep j μ + (b : ℤ) • unitStep j ν
theorem sum_sum_telescope (A B : ℕ → ℕ → ℍ[ℝ]) (L : ℕ) :
    ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, ((A a b - A a (b + 1)) + (B (a + 1) b - B a b)) =
      ∑ a ∈ Finset.range L, (A a 0 - A a L) + ∑ b ∈ Finset.range L, (B L b - B 0 b) := by apply _root_.YangMills.Construction.CarriedCurl.sum_sum_telescope <;> assumption
theorem siteOfCoords_zsmul_basisVector {j : ℕ} (k : ℤ) (μ : Fin 4) :
    siteOfCoords (F := F) j (k • basisVector μ) = k • unitStep j μ := by apply _root_.YangMills.Construction.CarriedCurl.siteOfCoords_zsmul_basisVector <;> assumption
theorem refineSite_add_unitStep_eq {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (μ : Fin 4) :
    refineSite (y + unitStep (j + 1) μ) = refineSite y + (F.blockSide : ℤ) • unitStep j μ := by
  rw [refineSite_add_unitStep hj, siteOfCoords_zsmul_basisVector]
theorem flatCurl_flatAverage {j : ℕ} (hj : j < F.top) (g : F.Site j → Fin 4 → ℍ[ℝ]) (y : F.Site (j + 1))
    (μ ν : Fin 4) :
    flatCurl (fun y' i => flatAverage g (y', i)) (y, μ, ν) = (1 / (F.blockSide : ℝ) ^ 4) •
      ∑ h ∈ centredCube F.blockSide, ∑ a ∈ Finset.range F.blockSide, ∑ b ∈ Finset.range F.blockSide,
        flatCurl g (subSquareCorner y μ ν h a b, μ, ν) := by
  simp only [flatCurl, flatAverage, lineBond]
  rw [← smul_add, ← smul_sub, ← smul_sub]
  congr 1
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  set x := refineSite y + siteOfCoords j h with hx
  set E1 := unitStep (F := F) j μ with hE1
  set E2 := unitStep (F := F) j ν with hE2
  set A : ℕ → ℕ → ℍ[ℝ] := fun a b => g (x + (a : ℤ) • E1 + (b : ℤ) • E2) μ with hA
  set B : ℕ → ℕ → ℍ[ℝ] := fun a b => g (x + (a : ℤ) • E1 + (b : ℤ) • E2) ν with hB
  have hsum := sum_sum_telescope A B F.blockSide
  have e1 : ∀ a b : ℕ, subSquareCorner y μ ν h a b = x + (a : ℤ) • E1 + (b : ℤ) • E2 := fun _ _ => rfl
  have e2 : ∀ a b : ℕ, x + (a : ℤ) • E1 + (b : ℤ) • E2 + E1 = x + ((a + 1 : ℕ) : ℤ) • E1 + (b : ℤ) • E2 := by
    intro a b
    push_cast
    rw [add_smul, one_smul]
    abel
  have e3 : ∀ a b : ℕ, x + (a : ℤ) • E1 + (b : ℤ) • E2 + E2 = x + (a : ℤ) • E1 + ((b + 1 : ℕ) : ℤ) • E2 := by
    intro a b
    push_cast
    rw [add_smul, one_smul]
    abel
  have hterm : ∀ a b : ℕ, flatCurl g (subSquareCorner y μ ν h a b, μ, ν) =
      (A a b - A a (b + 1)) + (B (a + 1) b - B a b) := by
    intro a b
    simp only [flatCurl, e1, hA, hB]
    rw [e2, e3]
    abel
  simp only [flatCurl, e1] at hterm
  have hrhs : ∑ a ∈ Finset.range F.blockSide, ∑ b ∈ Finset.range F.blockSide,
      (g (x + (a : ℤ) • E1 + (b : ℤ) • E2) μ + g (x + (a : ℤ) • E1 + (b : ℤ) • E2 + E1) ν -
        g (x + (a : ℤ) • E1 + (b : ℤ) • E2 + E2) μ - g (x + (a : ℤ) • E1 + (b : ℤ) • E2) ν) =
      ∑ a ∈ Finset.range F.blockSide, (A a 0 - A a F.blockSide) +
        ∑ b ∈ Finset.range F.blockSide, (B F.blockSide b - B 0 b) := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hterm a b
  simp only [subSquareCorner]
  rw [hrhs, refineSite_add_unitStep_eq hj, refineSite_add_unitStep_eq hj, ← hE1, ← hE2]
  simp only [hA, hB, Finset.sum_sub_distrib]
  have f1 : ∀ r : ℕ, refineSite y + (F.blockSide : ℤ) • E1 + siteOfCoords j h + (r : ℤ) • E2 =
      x + ((F.blockSide : ℕ) : ℤ) • E1 + (r : ℤ) • E2 := by
    intro r
    rw [hx]
    abel
  have f2 : ∀ r : ℕ, refineSite y + (F.blockSide : ℤ) • E2 + siteOfCoords j h + (r : ℤ) • E1 =
      x + (r : ℤ) • E1 + ((F.blockSide : ℕ) : ℤ) • E2 := by
    intro r
    rw [hx]
    abel
  have f3 : ∀ a : ℕ, x + (a : ℤ) • E1 + ((0 : ℕ) : ℤ) • E2 = x + (a : ℤ) • E1 := by
    intro a
    simp
  have f4 : ∀ b : ℕ, x + ((0 : ℕ) : ℤ) • E1 + (b : ℤ) • E2 = x + (b : ℤ) • E2 := by
    intro b
    simp
  simp only [f1, f2, f3, f4]
  abel
theorem plaquette_bonds_mem {D : Finset F.Cell} {j : ℕ} {q : F.Site j × Fin 4 × Fin 4}
    (hq : q ∈ innerPlaquettes D j) :
    (q.1, q.2.1) ∈ innerBonds D j ∧ (q.1 + unitStep j q.2.1, q.2.2) ∈ innerBonds D j ∧
      (q.1 + unitStep j q.2.2, q.2.1) ∈ innerBonds D j ∧ (q.1, q.2.2) ∈ innerBonds D j := by apply _root_.YangMills.Construction.BlockAverages.ColdBelowTop.plaquette_edges_mem_innerBonds <;> assumption
theorem norm_flatCurl_sub_covariantCurlAt_le {j : ℕ} (Y : F.GaugeField j) (g : F.Site j → Fin 4 → ℍ[ℝ])
    (q : F.Site j × Fin 4 × Fin 4) {ε : ℝ}
    (h1 : ‖((Y q.1 q.2.1 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (h2 : ‖((Y (q.1 + unitStep j q.2.1) q.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (h3 : ‖((Y (q.1 + unitStep j q.2.2) q.2.1 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (h4 : ‖((Y q.1 q.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε) :
    ‖flatCurl g q - covariantCurlAt Y g q‖ ≤ 8 * ε * (‖g (q.1 + unitStep j q.2.1) q.2.2‖ +
      ‖g (q.1 + unitStep j q.2.2) q.2.1‖ + ‖g q.1 q.2.2‖) := by
  obtain ⟨x, μ, ν⟩ := q
  simp only [flatCurl, covariantCurlAt] at *
  set r1 := Y x μ
  set r2 := Y (x + unitStep j μ) ν
  set r3 := Y (x + unitStep j ν) μ
  set r4 := Y x ν
  set g2 := g (x + unitStep j μ) ν
  set g3 := g (x + unitStep j ν) μ
  set g4 := g x ν
  have hε : 0 ≤ ε := (norm_nonneg _).trans h1
  have n2 : ‖((r1 * r2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * ε := by
    have := norm_coe_mul_sub_one_le r1 r2
    linarith
  have n3 : ‖((r1 * r2 * r3⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 3 * ε := by
    have := norm_coe_mul_sub_one_le (r1 * r2) r3⁻¹
    rw [norm_coe_inv_sub_one] at this
    linarith
  have n4 : ‖((r1 * r2 * r3⁻¹ * r4⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 4 * ε := by
    have := norm_coe_mul_sub_one_le (r1 * r2 * r3⁻¹) r4⁻¹
    rw [norm_coe_inv_sub_one] at this
    linarith
  have a2 := norm_adjointAction_sub_le r1 g2
  have a3 := norm_adjointAction_sub_le (r1 * r2 * r3⁻¹) g3
  have a4 := norm_adjointAction_sub_le (r1 * r2 * r3⁻¹ * r4⁻¹) g4
  have e : g x μ + g2 - g3 - g4 - (g x μ + _root_.YangMills.Construction.BlockAverages.adjointAction r1 g2 - _root_.YangMills.Construction.BlockAverages.adjointAction (r1 * r2 * r3⁻¹) g3 -
      _root_.YangMills.Construction.BlockAverages.adjointAction (r1 * r2 * r3⁻¹ * r4⁻¹) g4) =
      -(_root_.YangMills.Construction.BlockAverages.adjointAction r1 g2 - g2) + (_root_.YangMills.Construction.BlockAverages.adjointAction (r1 * r2 * r3⁻¹) g3 - g3) +
        (_root_.YangMills.Construction.BlockAverages.adjointAction (r1 * r2 * r3⁻¹ * r4⁻¹) g4 - g4) := by abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have b1 := norm_add_le (-(_root_.YangMills.Construction.BlockAverages.adjointAction r1 g2 - g2)) (_root_.YangMills.Construction.BlockAverages.adjointAction (r1 * r2 * r3⁻¹) g3 - g3)
  rw [norm_neg] at b1
  have p2 : 0 ≤ ‖g2‖ := norm_nonneg _
  have p3 : 0 ≤ ‖g3‖ := norm_nonneg _
  have p4 : 0 ≤ ‖g4‖ := norm_nonneg _
  have c2 : 2 * ‖(r1 : ℍ[ℝ]) - 1‖ * ‖g2‖ ≤ 2 * ε * ‖g2‖ := by
    have := mul_le_mul_of_nonneg_right h1 p2
    linarith
  have c3 : 2 * ‖((r1 * r2 * r3⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ * ‖g3‖ ≤ 6 * ε * ‖g3‖ := by
    have := mul_le_mul_of_nonneg_right n3 p3
    linarith
  have c4 : 2 * ‖((r1 * r2 * r3⁻¹ * r4⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ * ‖g4‖ ≤ 8 * ε * ‖g4‖ := by
    have := mul_le_mul_of_nonneg_right n4 p4
    linarith
  have d2 : 0 ≤ ε * ‖g2‖ := by positivity
  have d3 : 0 ≤ ε * ‖g3‖ := by positivity
  nlinarith
theorem subSquareCorner_eq {j : ℕ} (y : F.Site (j + 1)) (μ ν : Fin 4) (h : Fin 4 → ℤ) (a b : ℕ) :
    subSquareCorner y μ ν h a b =
      refineSite y + siteOfCoords j (h + (a : ℤ) • basisVector μ + (b : ℤ) • basisVector ν) := by
  simp only [subSquareCorner]
  rw [siteOfCoords_add, siteOfCoords_add, siteOfCoords_zsmul_basisVector, siteOfCoords_zsmul_basisVector]
  abel
theorem subSquareOffset_bounds {L : ℕ} {h : Fin 4 → ℤ} (hh : h ∈ centredCube L) {μ ν : Fin 4} (hμν : μ ≠ ν)
    {a b : ℕ} (ha : a ≤ L) (hb : b ≤ L) (k : Fin 4) :
    -(((L : ℤ) - 1) / 2) ≤ (h + (a : ℤ) • basisVector μ + (b : ℤ) • basisVector ν) k ∧
      (h + (a : ℤ) • basisVector μ + (b : ℤ) • basisVector ν) k ≤
        ((L : ℤ) - 1) / 2 + (if k = μ then (a : ℤ) else 0) + (if k = ν then (b : ℤ) else 0) := by apply _root_.YangMills.Construction.CarriedCurl.subSquare_offset_bounds <;> assumption
theorem subSquareCorner_mem {D : Finset F.Cell} (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top)
    {y : F.Site (j + 1)} {μ ν : Fin 4} (hμν : μ ≠ ν) (c1 : y ∈ sitesOfCells D (j + 1))
    (c2 : y + unitStep (j + 1) μ ∈ sitesOfCells D (j + 1)) (c3 : y + unitStep (j + 1) ν ∈ sitesOfCells D (j + 1))
    (c4 : y + unitStep (j + 1) μ + unitStep (j + 1) ν ∈ sitesOfCells D (j + 1)) {h : Fin 4 → ℤ}
    (hh : h ∈ centredCube F.blockSide) {a b : ℕ} (ha : a ≤ F.blockSide) (hb : b ≤ F.blockSide) :
    subSquareCorner y μ ν h a b ∈ sitesOfCells D j := by
  rw [subSquareCorner_eq]
  set v := h + (a : ℤ) • basisVector μ + (b : ℤ) • basisVector ν with hv
  have hk : ∀ k, -(((F.blockSide : ℤ) - 1) / 2) ≤ v k ∧ v k ≤ ((F.blockSide : ℤ) - 1) / 2 +
      (if k = μ then (a : ℤ) else 0) + (if k = ν then (b : ℤ) else 0) := fun k =>
    subSquareOffset_bounds hh hμν ha hb k
  have hLodd : (F.blockSide : ℤ) = 2 * (((F.blockSide : ℤ) - 1) / 2) + 1 := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm]
    push_cast
    omega
  by_cases hc : v ν ≤ ((F.blockSide : ℤ) - 1) / 2
  · refine BlockLines.refineSite_add_mem_of_mem_twoBlockHull hj hodd y μ c1 c2 v fun k => ?_
    obtain ⟨k1, k2⟩ := hk k
    refine ⟨k1, ?_⟩
    by_cases h1 : k = ν
    · subst h1
      have : k ≠ μ := fun e => hμν e.symm
      simp only [if_neg this]
      omega
    · by_cases h2 : k = μ
      · subst h2
        simp only [if_true, if_neg h1] at k2 ⊢
        omega
      · simp only [if_neg h1, if_neg h2] at k2 ⊢
        omega
  · have e : refineSite y + siteOfCoords j v =
        refineSite (y + unitStep (j + 1) ν) + siteOfCoords j (v - (F.blockSide : ℤ) • basisVector ν) := by
      rw [refineSite_add_unitStep hj, add_assoc, ← siteOfCoords_add]
      congr 2
      abel
    rw [e]
    refine BlockLines.refineSite_add_mem_of_mem_twoBlockHull hj hodd _ μ c3 ?_ _ fun k => ?_
    · rwa [add_right_comm]
    · obtain ⟨k1, k2⟩ := hk k
      by_cases h1 : k = ν
      · subst h1
        have hne : k ≠ μ := fun e => hμν e.symm
        simp only [if_neg hne, if_true, add_zero] at k2
        simp only [Pi.sub_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, mul_one, if_neg hne,
          add_zero]
        omega
      · have : ((F.blockSide : ℤ) • basisVector ν) k = 0 := by
          simp [basisVector, Pi.single_eq_of_ne h1]
        simp only [Pi.sub_apply, this, sub_zero]
        by_cases h2 : k = μ
        · subst h2
          simp only [if_true, if_neg h1, add_zero] at k2 ⊢
          omega
        · simp only [if_neg h1, if_neg h2, add_zero] at k2 ⊢
          omega
theorem subSquareCorner_add_unitStep_left {j : ℕ} (y : F.Site (j + 1)) (μ ν : Fin 4) (h : Fin 4 → ℤ) (a b : ℕ) :
    subSquareCorner y μ ν h a b + unitStep j μ = subSquareCorner y μ ν h (a + 1) b := by
  simp only [subSquareCorner]
  push_cast
  rw [add_smul, one_smul]
  abel
theorem subSquareCorner_add_unitStep_right {j : ℕ} (y : F.Site (j + 1)) (μ ν : Fin 4) (h : Fin 4 → ℤ) (a b : ℕ) :
    subSquareCorner y μ ν h a b + unitStep j ν = subSquareCorner y μ ν h a (b + 1) := by
  simp only [subSquareCorner]
  push_cast
  rw [add_smul, one_smul]
  abel
theorem subSquare_mem_innerPlaquettes {D : Finset F.Cell} (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top)
    {q : F.Site (j + 1) × Fin 4 × Fin 4} (hq : q ∈ innerPlaquettes D (j + 1)) {h : Fin 4 → ℤ}
    (hh : h ∈ centredCube F.blockSide) {a b : ℕ} (ha : a < F.blockSide) (hb : b < F.blockSide) :
    (subSquareCorner q.1 q.2.1 q.2.2 h a b, q.2.1, q.2.2) ∈ innerPlaquettes D j := by
  classical
  obtain ⟨h1, hlt, hc⟩ := Finset.mem_filter.1 hq
  have hne : q.2.1 ≠ q.2.2 := ne_of_lt hlt
  have c1 : q.1 ∈ sitesOfCells D (j + 1) := hc (by simp [plaquetteCorners])
  have c2 : q.1 + unitStep (j + 1) q.2.1 ∈ sitesOfCells D (j + 1) := hc (by simp [plaquetteCorners])
  have c3 : q.1 + unitStep (j + 1) q.2.2 ∈ sitesOfCells D (j + 1) := hc (by simp [plaquetteCorners])
  have c4 : q.1 + unitStep (j + 1) q.2.1 + unitStep (j + 1) q.2.2 ∈ sitesOfCells D (j + 1) :=
    hc (by simp [plaquetteCorners])
  have hs : ∀ a' b' : ℕ, a' ≤ F.blockSide → b' ≤ F.blockSide →
      subSquareCorner q.1 q.2.1 q.2.2 h a' b' ∈ sitesOfCells D j :=
    fun a' b' ha' hb' => subSquareCorner_mem hodd hj hne c1 c2 c3 c4 hh ha' hb'
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hs a b ha.le hb.le, by simp⟩, hlt, ?_⟩
  intro x hx
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hs a b ha.le hb.le
  · rw [subSquareCorner_add_unitStep_left]
    exact hs _ _ ha hb.le
  · rw [subSquareCorner_add_unitStep_right]
    exact hs _ _ ha.le hb
  · rw [subSquareCorner_add_unitStep_left, subSquareCorner_add_unitStep_right]
    exact hs _ _ ha hb
theorem shiftedWeight_succ_le_subSquareCorner (hL : 2 ≤ F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) (p : F.Site 0) {j : ℕ}
    (hj : j < F.top) (y : F.Site (j + 1)) {μ ν : Fin 4} (hμν : μ ≠ ν) {h : Fin 4 → ℤ}
    (hh : h ∈ centredCube F.blockSide) {a b : ℕ} (ha : a < F.blockSide) (hb : b < F.blockSide) :
    shiftedWeight F θ p (j + 1) y ≤ shiftedWeight F θ p j (subSquareCorner y μ ν h a b) := by
  rw [subSquareCorner_eq]
  refine shiftedWeight_succ_le hL hθ p hj y _ fun k => ?_
  obtain ⟨k1, k2⟩ := subSquareOffset_bounds hh hμν ha.le hb.le k
  have hbound : (if k = μ then (a : ℤ) else 0) + (if k = ν then (b : ℤ) else 0) ≤ F.blockSide := by
    by_cases h1 : k = μ
    · subst h1
      have : k ≠ ν := hμν
      simp only [if_true, if_neg this]
      omega
    · simp only [if_neg h1]
      split_ifs <;> omega
  omega
theorem sum_flatCurl_sq_succ_le (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ)
    (p : F.Site 0) (D : Finset F.Cell) {j : ℕ} (hj : j < F.top) (g : F.Site j → Fin 4 → ℍ[ℝ]) :
    ∑ q ∈ innerPlaquettes D (j + 1),
        (shiftedWeight F θ p (j + 1) q.1 * ‖flatCurl (fun y i => flatAverage g (y, i)) q‖) ^ 2 ≤
      ∑ q ∈ innerPlaquettes D j, (shiftedWeight F θ p j q.1 * ‖flatCurl g q‖) ^ 2 := by
  classical
  have hLpos := hodd.pos
  set W : F.Site j × Fin 4 × Fin 4 → ℝ := fun q => shiftedWeight F θ p j q.1 * ‖flatCurl g q‖ with hW
  have hΩ0 : ∀ {j : ℕ} (x : F.Site j), 0 ≤ shiftedWeight F θ p j x := fun x =>
    zero_le_one.trans (one_le_shiftedWeight hLpos hθ p _ x)
  set I : Finset ((Fin 4 → ℤ) × ℕ × ℕ) :=
    centredCube F.blockSide ×ˢ (Finset.range F.blockSide ×ˢ Finset.range F.blockSide) with hI
  have hcard : (I.card : ℝ) = (F.blockSide : ℝ) ^ 6 := by
    rw [hI, Finset.card_product, Finset.card_product, card_centredCube hodd, Finset.card_range]
    push_cast
    ring
  set pt : F.Site (j + 1) × Fin 4 × Fin 4 → (Fin 4 → ℤ) × ℕ × ℕ → F.Site j × Fin 4 × Fin 4 :=
    fun q i => (subSquareCorner q.1 q.2.1 q.2.2 i.1 i.2.1 i.2.2, q.2.1, q.2.2) with hpt
  have hone : ∀ q ∈ innerPlaquettes D (j + 1),
      (shiftedWeight F θ p (j + 1) q.1 * ‖flatCurl (fun y i => flatAverage g (y, i)) q‖) ^ 2 ≤
        (1 / (F.blockSide : ℝ) ^ 2) * ∑ i ∈ I, W (pt q i) ^ 2 := by
    intro q hq
    have hne : q.2.1 ≠ q.2.2 := ne_of_lt (Finset.mem_filter.1 hq).2.1
    have hA : shiftedWeight F θ p (j + 1) q.1 * ‖flatCurl (fun y i => flatAverage g (y, i)) q‖ ≤
        (1 / (F.blockSide : ℝ) ^ 4) * ∑ i ∈ I, W (pt q i) := by
      obtain ⟨y, μ, ν⟩ := q
      simp only at hne
      rw [flatCurl_flatAverage hj, norm_smul, Real.norm_of_nonneg (by positivity), mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hI, Finset.sum_product]
      refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hΩ0 _)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun h hh => ?_
      rw [Finset.sum_product]
      refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hΩ0 _)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a ha => ?_
      refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hΩ0 _)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b hb => ?_
      exact mul_le_mul_of_nonneg_right
        (shiftedWeight_succ_le_subSquareCorner hL hθ p hj y hne hh (Finset.mem_range.1 ha) (Finset.mem_range.1 hb))
        (norm_nonneg _)
    have hA0 : 0 ≤ shiftedWeight F θ p (j + 1) q.1 * ‖flatCurl (fun y i => flatAverage g (y, i)) q‖ :=
      mul_nonneg (hΩ0 _) (norm_nonneg _)
    have h2 := pow_le_pow_left₀ hA0 hA 2
    have h3 := sq_sum_le_card_mul_sum_sq (s := I) (f := fun i => W (pt q i))
    rw [hcard] at h3
    refine h2.trans ?_
    rw [mul_pow]
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ (1 / (F.blockSide : ℝ) ^ 4) ^ 2)
    refine h4.trans (le_of_eq ?_)
    field_simp
  have hab : ∀ a ∈ Finset.range F.blockSide, ∀ b ∈ Finset.range F.blockSide,
      ∑ q ∈ innerPlaquettes D (j + 1), ∑ h ∈ centredCube F.blockSide, W (pt q (h, a, b)) ^ 2 ≤
        ∑ q ∈ innerPlaquettes D j, W q ^ 2 := by
    intro a ha b hb
    have ha' := Finset.mem_range.1 ha
    have hb' := Finset.mem_range.1 hb
    rw [← Finset.sum_product']
    have hinj : Set.InjOn (fun x : (F.Site (j + 1) × Fin 4 × Fin 4) × (Fin 4 → ℤ) => pt x.1 (x.2, a, b))
        (innerPlaquettes D (j + 1) ×ˢ centredCube F.blockSide : Finset _) := by
      intro x hx x' hx' e
      have h1 := Finset.mem_product.1 (Finset.mem_coe.1 hx)
      have h2 := Finset.mem_product.1 (Finset.mem_coe.1 hx')
      simp only [hpt] at e
      obtain ⟨e1, e2⟩ := Prod.ext_iff.1 e
      obtain ⟨e3, e4⟩ := Prod.ext_iff.1 e2
      simp only at e1 e3 e4
      simp only [subSquareCorner] at e1
      rw [e3, e4] at e1
      have e5 := add_right_cancel (add_right_cancel e1)
      obtain ⟨i1, i2⟩ := refineSite_add_injective hj hodd x.1.1 x'.1.1 x.2 x'.2 h1.2 h2.2 e5
      exact Prod.ext (Prod.ext i1 (Prod.ext e3 e4)) i2
    have := Finset.sum_image (f := fun q => W q ^ 2) hinj
    rw [← this]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => by positivity
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hq
    have h1 := Finset.mem_product.1 hx
    exact subSquare_mem_innerPlaquettes hodd hj h1.1 h1.2 ha' hb'
  refine (Finset.sum_le_sum hone).trans ?_
  rw [← Finset.mul_sum]
  have hswap : ∑ q ∈ innerPlaquettes D (j + 1), ∑ i ∈ I, W (pt q i) ^ 2 =
      ∑ a ∈ Finset.range F.blockSide, ∑ b ∈ Finset.range F.blockSide, ∑ q ∈ innerPlaquettes D (j + 1),
        ∑ h ∈ centredCube F.blockSide, W (pt q (h, a, b)) ^ 2 := by
    calc _ = ∑ q ∈ innerPlaquettes D (j + 1), ∑ h ∈ centredCube F.blockSide, ∑ a ∈ Finset.range F.blockSide,
          ∑ b ∈ Finset.range F.blockSide, W (pt q (h, a, b)) ^ 2 := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [hI, Finset.sum_product]
          exact Finset.sum_congr rfl fun h _ => Finset.sum_product _ _ _
      _ = ∑ q ∈ innerPlaquettes D (j + 1), ∑ a ∈ Finset.range F.blockSide, ∑ b ∈ Finset.range F.blockSide,
          ∑ h ∈ centredCube F.blockSide, W (pt q (h, a, b)) ^ 2 := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ a ∈ Finset.range F.blockSide, ∑ q ∈ innerPlaquettes D (j + 1), ∑ b ∈ Finset.range F.blockSide,
          ∑ h ∈ centredCube F.blockSide, W (pt q (h, a, b)) ^ 2 := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [hswap]
  have hle : ∑ a ∈ Finset.range F.blockSide, ∑ b ∈ Finset.range F.blockSide, ∑ q ∈ innerPlaquettes D (j + 1),
      ∑ h ∈ centredCube F.blockSide, W (pt q (h, a, b)) ^ 2 ≤
        (F.blockSide : ℝ) ^ 2 * ∑ q ∈ innerPlaquettes D j, W q ^ 2 := by
    refine (Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hab a ha b hb).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have h5 := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 1 / (F.blockSide : ℝ) ^ 2)
  refine h5.trans (le_of_eq ?_)
  rw [← mul_assoc, one_div, inv_mul_cancel₀ (by positivity), one_mul]
theorem sum_flatCurl_sq_le_base (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ)
    (p : F.Site 0) (D : Finset F.Cell) (g0 : F.Site 0 → Fin 4 → ℍ[ℝ]) : ∀ j, j ≤ F.top →
    ∑ q ∈ innerPlaquettes D j, (shiftedWeight F θ p j q.1 * ‖flatCurl (flatTransported g0 j) q‖) ^ 2 ≤
      ∑ q ∈ innerPlaquettes D 0, (shiftedWeight F θ p 0 q.1 * ‖flatCurl g0 q‖) ^ 2 := by
  intro j
  induction j with
  | zero => intro _; exact le_rfl
  | succ j ih =>
    intro hj
    exact (sum_flatCurl_sq_succ_le hodd hL hθ p D (by omega) (flatTransported g0 j)).trans (ih (by omega))
theorem sum_plaquette_bond_le {P : Finset (F.Site 0 × Fin 4 × Fin 4)} {B : Finset (F.Site 0 × Fin 4)}
    (g : F.Site 0 × Fin 4 → ℝ) (hg : ∀ b, 0 ≤ g b) (T : F.Site 0 × Fin 4 × Fin 4 → F.Site 0 × Fin 4)
    (hT : ∀ q ∈ P, T q ∈ B) (hinj : ∀ q ∈ P, ∀ q' ∈ P, q.2 = q'.2 → T q = T q' → q.1 = q'.1) :
    ∑ q ∈ P, g (T q) ≤ 16 * ∑ b ∈ B, g b := by apply _root_.YangMills.Construction.CarriedCurl.sum_plaquettes_le_sixteen_mul_sum_bonds <;> assumption
theorem sq_le_of_le_add_mul_sum {X e a b c y : ℝ} (hy0 : 0 ≤ y) (h : y ≤ X + e * (a + b + c)) (hX : 0 ≤ X)
    (he : 0 ≤ e) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    y ^ 2 ≤ 2 * X ^ 2 + 6 * e ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by apply _root_.YangMills.Construction.CarriedCurl.sq_le_of_le_add_mul_sum <;> assumption
theorem sum_flatCurl_base_le (hodd : Odd F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (p : F.Site 0)
    {D : Finset F.Cell} (γ : F.Site 0 → UnitQuaternion) (R0 : F.GaugeField 0) (f : F.Site 0 → Fin 4 → ℍ[ℝ])
    {ε E A B : ℝ} (hε : 0 ≤ ε) (hE : 0 ≤ E) (hεN : ε * (F.blockSide : ℝ) ^ F.top ≤ E) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hR : ∀ x i, x ∈ sitesOfCells D 0 → x + unitStep 0 i ∈ sitesOfCells D 0 →
      ‖((gaugedField γ R0 x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε)
    (hcard : ((innerBonds D 0).card : ℝ) ≤ 2500 * ((F.blockSide : ℝ) ^ F.top) ^ 4)
    (hA : ∑ q ∈ innerPlaquettes D 0, (shiftedWeight F θ p 0 q.1 * ‖covariantCurlAt R0 f q‖) ^ 2 ≤ A ^ 2)
    (hB : ∑ b ∈ innerBonds D 0, (shiftedWeight F θ p 0 b.1 * ‖f b.1 b.2‖) ^ 4 ≤ B ^ 4) :
    ∑ q ∈ innerPlaquettes D 0, (shiftedWeight F θ p 0 q.1 * ‖flatCurl (gaugedForm γ f) q‖) ^ 2 ≤
      (2 * A + 2000 * E * B) ^ 2 := by
  classical
  have hLpos := hodd.pos
  have hΩ0 : ∀ (x : F.Site 0), 0 ≤ shiftedWeight F θ p 0 x := fun x =>
    zero_le_one.trans (one_le_shiftedWeight hLpos hθ p _ x)
  set Gf : F.Site 0 × Fin 4 → ℝ := fun b => (shiftedWeight F θ p 0 b.1 * ‖f b.1 b.2‖) ^ 2 with hGf
  have hGf0 : ∀ b, 0 ≤ Gf b := fun b => by positivity
  have hnear : ∀ (x x' : F.Site 0), baseDistance x' p ≤ baseDistance x p + 1 → ∀ i,
      shiftedWeight F θ p 0 x * ‖f x' i‖ ≤ 2 * (shiftedWeight F θ p 0 x' * ‖f x' i‖) := by
    intro x x' h i
    have := shiftedWeight_le_two_mul_of_near hLpos hθ hθ1 p (j := 0) (Nat.zero_le _) x x' (by simpa using h)
    have h2 := mul_le_mul_of_nonneg_right this (norm_nonneg (f x' i))
    linarith
  have hstep : ∀ (x : F.Site 0) (i : Fin 4), baseDistance (x + unitStep 0 i) p ≤ baseDistance x p + 1 := by
    intro x i
    have := baseDistance_add_unitStep_le (F := F) (j := 0) (Nat.zero_le _) x i p
    simpa using this
  have hone : ∀ q ∈ innerPlaquettes D 0,
      (shiftedWeight F θ p 0 q.1 * ‖flatCurl (gaugedForm γ f) q‖) ^ 2 ≤
        2 * (shiftedWeight F θ p 0 q.1 * ‖covariantCurlAt R0 f q‖) ^ 2 + 6 * (16 * ε) ^ 2 *
          (Gf (q.1 + unitStep 0 q.2.1, q.2.2) + Gf (q.1 + unitStep 0 q.2.2, q.2.1) + Gf (q.1, q.2.2)) := by
    intro q hq
    obtain ⟨b1, b2, b3, b4⟩ := plaquette_bonds_mem hq
    have e1 := ChartCoordinates.innerBonds_ends b1
    have e2 := ChartCoordinates.innerBonds_ends b2
    have e3 := ChartCoordinates.innerBonds_ends b3
    have e4 := ChartCoordinates.innerBonds_ends b4
    have h1 := norm_flatCurl_sub_covariantCurlAt_le (gaugedField γ R0) (gaugedForm γ f) q (hR _ _ e1.1 e1.2)
      (hR _ _ e2.1 e2.2) (hR _ _ e3.1 e3.2) (hR _ _ e4.1 e4.2)
    have h2 : ‖covariantCurlAt (gaugedField γ R0) (gaugedForm γ f) q‖ = ‖covariantCurlAt R0 f q‖ := by
      rw [covariantCurlAt_gaugedField, BlockLines.norm_adjointAction]
    have h3 : ∀ x i, ‖gaugedForm γ f x i‖ = ‖f x i‖ := fun x i => BlockLines.norm_adjointAction _ _
    rw [h3, h3, h3] at h1
    have h4 : ‖flatCurl (gaugedForm γ f) q‖ ≤ ‖covariantCurlAt R0 f q‖ + 8 * ε *
        (‖f (q.1 + unitStep 0 q.2.1) q.2.2‖ + ‖f (q.1 + unitStep 0 q.2.2) q.2.1‖ + ‖f q.1 q.2.2‖) := by
      have := norm_sub_norm_le (flatCurl (gaugedForm γ f) q)
        (covariantCurlAt (gaugedField γ R0) (gaugedForm γ f) q)
      rw [h2] at this
      linarith
    have hΩ := hΩ0 q.1
    have h5 := mul_le_mul_of_nonneg_left h4 hΩ
    have n2 := hnear q.1 _ (hstep q.1 q.2.1) q.2.2
    have n3 := hnear q.1 _ (hstep q.1 q.2.2) q.2.1
    have n4 := hnear q.1 q.1 (by omega) q.2.2
    set a := shiftedWeight F θ p 0 (q.1 + unitStep 0 q.2.1) * ‖f (q.1 + unitStep 0 q.2.1) q.2.2‖ with ha
    set b := shiftedWeight F θ p 0 (q.1 + unitStep 0 q.2.2) * ‖f (q.1 + unitStep 0 q.2.2) q.2.1‖ with hb
    set c := shiftedWeight F θ p 0 q.1 * ‖f q.1 q.2.2‖ with hc
    have ha0 : 0 ≤ a := mul_nonneg (hΩ0 _) (norm_nonneg _)
    have hb0 : 0 ≤ b := mul_nonneg (hΩ0 _) (norm_nonneg _)
    have hc0 : 0 ≤ c := mul_nonneg (hΩ0 _) (norm_nonneg _)
    have h6 : shiftedWeight F θ p 0 q.1 * ‖flatCurl (gaugedForm γ f) q‖ ≤
        shiftedWeight F θ p 0 q.1 * ‖covariantCurlAt R0 f q‖ + 16 * ε * (a + b + c) := by
      have hk : shiftedWeight F θ p 0 q.1 * (8 * ε * (‖f (q.1 + unitStep 0 q.2.1) q.2.2‖ +
          ‖f (q.1 + unitStep 0 q.2.2) q.2.1‖ + ‖f q.1 q.2.2‖)) =
          8 * ε * (shiftedWeight F θ p 0 q.1 * ‖f (q.1 + unitStep 0 q.2.1) q.2.2‖ +
            shiftedWeight F θ p 0 q.1 * ‖f (q.1 + unitStep 0 q.2.2) q.2.1‖ +
            shiftedWeight F θ p 0 q.1 * ‖f q.1 q.2.2‖) := by
        ring
      have hk2 : 8 * ε * (shiftedWeight F θ p 0 q.1 * ‖f (q.1 + unitStep 0 q.2.1) q.2.2‖ +
          shiftedWeight F θ p 0 q.1 * ‖f (q.1 + unitStep 0 q.2.2) q.2.1‖ +
          shiftedWeight F θ p 0 q.1 * ‖f q.1 q.2.2‖) ≤ 8 * ε * (2 * a + 2 * b + 2 * c) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add n2 n3) n4) (by positivity)
      rw [mul_add, hk] at h5
      nlinarith
    exact sq_le_of_le_add_mul_sum (mul_nonneg hΩ (norm_nonneg _)) h6 (mul_nonneg hΩ (norm_nonneg _))
      (by positivity) ha0 hb0 hc0
  refine (Finset.sum_le_sum hone).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  have t2 := sum_plaquette_bond_le (P := innerPlaquettes D 0) (B := innerBonds D 0) Gf hGf0
    (fun q => (q.1 + unitStep 0 q.2.1, q.2.2)) (fun q hq => (plaquette_bonds_mem hq).2.1) (fun q _ q' _ h e => by
      have e1 := (Prod.ext_iff.1 e).1
      simp only at e1
      rw [h] at e1
      exact add_right_cancel e1)
  have t3 := sum_plaquette_bond_le (P := innerPlaquettes D 0) (B := innerBonds D 0) Gf hGf0
    (fun q => (q.1 + unitStep 0 q.2.2, q.2.1)) (fun q hq => (plaquette_bonds_mem hq).2.2.1) (fun q _ q' _ h e => by
      have e1 := (Prod.ext_iff.1 e).1
      simp only at e1
      rw [h] at e1
      exact add_right_cancel e1)
  have t4 := sum_plaquette_bond_le (P := innerPlaquettes D 0) (B := innerBonds D 0) Gf hGf0 (fun q => (q.1, q.2.2))
    (fun q hq => (plaquette_bonds_mem hq).2.2.2) (fun q _ q' _ _ e => (Prod.ext_iff.1 e).1)
  have hsq : (∑ b ∈ innerBonds D 0, Gf b) ^ 2 ≤ (50 * ((F.blockSide : ℝ) ^ F.top) ^ 2 * B ^ 2) ^ 2 := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := innerBonds D 0) (f := Gf)
    have h2 : ∑ b ∈ innerBonds D 0, Gf b ^ 2 ≤ B ^ 4 := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) hB
      simp only [hGf]
      ring
    have h3 : ((innerBonds D 0).card : ℝ) * ∑ b ∈ innerBonds D 0, Gf b ^ 2 ≤
        (2500 * ((F.blockSide : ℝ) ^ F.top) ^ 4) * B ^ 4 :=
      mul_le_mul hcard h2 (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    refine h1.trans (h3.trans (le_of_eq ?_))
    ring
  have hS : ∑ b ∈ innerBonds D 0, Gf b ≤ 50 * ((F.blockSide : ℝ) ^ F.top) ^ 2 * B ^ 2 :=
    le_of_not_gt fun hlt => absurd hsq (not_le.2 (pow_lt_pow_left₀ hlt (by positivity) (by norm_num)))
  have hεS : ε ^ 2 * ∑ b ∈ innerBonds D 0, Gf b ≤ 50 * E ^ 2 * B ^ 2 := by
    have h1 : (ε * (F.blockSide : ℝ) ^ F.top) ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ (by positivity) hεN 2
    have h2 := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ ε ^ 2)
    have h3 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 50 * B ^ 2)
    nlinarith
  set S0 := ∑ b ∈ innerBonds D 0, Gf b with hS0
  set T2 := ∑ q ∈ innerPlaquettes D 0, Gf (q.1 + unitStep 0 q.2.1, q.2.2)
  set T3 := ∑ q ∈ innerPlaquettes D 0, Gf (q.1 + unitStep 0 q.2.2, q.2.1)
  set T4 := ∑ q ∈ innerPlaquettes D 0, Gf (q.1, q.2.2)
  have hT : T2 + T3 + T4 ≤ 48 * S0 := by
    linarith
  have hfin : 6 * (16 * ε) ^ 2 * (T2 + T3 + T4) ≤ 6 * (16 * ε) ^ 2 * (48 * S0) :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  have hAB : 0 ≤ A * (E * B) := by positivity
  nlinarith
theorem norm_flatCurl_le_add {j : ℕ} (f g : F.Site j → Fin 4 → ℍ[ℝ]) (q : F.Site j × Fin 4 × Fin 4) :
    ‖flatCurl f q‖ ≤ ‖flatCurl g q‖ + ‖f q.1 q.2.1 - g q.1 q.2.1‖ +
      ‖f (q.1 + unitStep j q.2.1) q.2.2 - g (q.1 + unitStep j q.2.1) q.2.2‖ +
      ‖f (q.1 + unitStep j q.2.2) q.2.1 - g (q.1 + unitStep j q.2.2) q.2.1‖ + ‖f q.1 q.2.2 - g q.1 q.2.2‖ := by
  set a := f q.1 q.2.1 - g q.1 q.2.1
  set b := f (q.1 + unitStep j q.2.1) q.2.2 - g (q.1 + unitStep j q.2.1) q.2.2
  set c := f (q.1 + unitStep j q.2.2) q.2.1 - g (q.1 + unitStep j q.2.2) q.2.1
  set d := f q.1 q.2.2 - g q.1 q.2.2
  have e : flatCurl f q = flatCurl g q + a + b - c - d := by
    simp only [flatCurl, a, b, c, d]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_sub_le (flatCurl g q + a + b) c
  have h2 := norm_add_le (flatCurl g q + a) b
  have h3 := norm_add_le (flatCurl g q) a
  linarith
theorem baseSite_mem_patch {F : BlockFrame} (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S : Finset F.Cell} {z : F.Cell} (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {D : Finset F.Cell} (hDS : D ⊆ S) (hd : ∀ y ∈ D, cellSupDist z y ≤ 10) {j : ℕ} (hj : j ≤ F.top)
    {x : F.Site j} (hx : x ∈ sitesOfCells D j) :
    baseSite x ∈ (patchDomain S z).image (patchSite S z) := by apply _root_.YangMills.Construction.CarriedCurl.baseSite_mem_patch <;> assumption
theorem norm_covariantCurlAt_top_le (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide) (R : F.FieldChain)
    (γ : F.Site 0 → UnitQuaternion) {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) {D : Finset F.Cell} {E : ℝ} (hE : 0 ≤ E)
    (hR : ∀ j, j < F.top → ∀ x i, x ∈ sitesOfCells D j → x + unitStep j i ∈ sitesOfCells D j →
      ‖((gaugedField γ (R j) x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ E * levelScale F j)
    (hT : ∀ x i, x ∈ sitesOfCells D F.top → x + unitStep F.top i ∈ sitesOfCells D F.top →
      ‖((gaugedField γ (R F.top) x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ E)
    (hcard : ((innerBonds D 0).card : ℝ) ≤ 2500 * ((F.blockSide : ℝ) ^ F.top) ^ 4) (f : F.Site 0 → Fin 4 → ℍ[ℝ])
    (p : F.Site 0) {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∑ q ∈ innerPlaquettes D 0, (shiftedWeight F θ p 0 q.1 * ‖covariantCurlAt (R 0) f q‖) ^ 2 ≤ A ^ 2)
    (hB : ∑ b ∈ innerBonds D 0, (shiftedWeight F θ p 0 b.1 * ‖f b.1 b.2‖) ^ 4 ≤ B ^ 4)
    {q : F.Site F.top × Fin 4 × Fin 4} (hq : q ∈ innerPlaquettes D F.top) :
    ‖covariantCurlAt (R F.top) (transportedForm R f F.top) q‖ ≤ 2 * A + 2072 * E * B := by
  classical
  have hLpos := hodd.pos
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hLpos
  have hl0 : ∀ j, 0 ≤ levelScale F j := fun j => by
    unfold levelScale
    positivity
  have hl1 : levelScale F F.top = 1 := by
    unfold levelScale
    simp
  have hln : levelScale F 0 * (F.blockSide : ℝ) ^ F.top = 1 := by
    unfold levelScale
    rw [Nat.sub_zero, ← mul_pow, one_div, inv_mul_cancel₀ hLr.ne', one_pow]
  set G := gaugedTransportedForm R γ f with hG
  set P := flatTransported (G 0) with hP
  set m := normTransported (fun x i => ‖G 0 x i‖) with hm
  have hG0 : G 0 = gaugedForm γ f := rfl
  have hGn : ∀ x i, ‖G 0 x i‖ = ‖f x i‖ := fun x i => BlockLines.norm_adjointAction _ _
  have hbot := sum_flatCurl_base_le hodd hθ hθ1 p γ (R 0) f (mul_nonneg hE (hl0 0)) hE
    (by rw [mul_assoc, hln, mul_one]) hA0 hB0 (hR 0 (Nat.succ_pos _)) hcard hA hB
  have hlev := sum_flatCurl_sq_le_base hodd hL hθ p D (G 0) F.top le_rfl
  rw [hG0] at hlev
  have hΩ := one_le_shiftedWeight hLpos hθ p F.top q.1
  have hP1 : shiftedWeight F θ p F.top q.1 * ‖flatCurl (P F.top) q‖ ≤ 2 * A + 2000 * E * B := by
    have h1 := Finset.single_le_sum
      (f := fun q' => (shiftedWeight F θ p F.top q'.1 * ‖flatCurl (P F.top) q'‖) ^ 2)
      (fun _ _ => by positivity) hq
    have h2 := h1.trans (hlev.trans hbot)
    exact le_of_not_gt fun hlt => absurd h2 (not_le.2 (pow_lt_pow_left₀ hlt (by positivity) (by norm_num)))
  have hP2 : ‖flatCurl (P F.top) q‖ ≤ 2 * A + 2000 * E * B :=
    (le_mul_of_one_le_left (norm_nonneg _) hΩ).trans hP1
  obtain ⟨b1, b2, b3, b4⟩ := plaquette_bonds_mem hq
  have hmB : ∀ b ∈ innerBonds D F.top, m F.top b.1 b.2 ≤ B := by
    intro b hb
    have h1 := Finset.single_le_sum (f := fun b' : F.Site F.top × Fin 4 => m F.top b'.1 b'.2 ^ 4)
      (fun _ _ => by positivity) hb
    have h2 := sum_normTransported_pow_four_le hodd D (g0 := fun x i => ‖G 0 x i‖) (fun _ _ => norm_nonneg _)
      F.top le_rfl
    have h3 : ∑ b ∈ innerBonds D 0, ‖G 0 b.1 b.2‖ ^ 4 ≤ B ^ 4 := by
      refine le_trans (Finset.sum_le_sum fun b _ => ?_) hB
      rw [hGn]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 4
      exact le_mul_of_one_le_left (norm_nonneg _) (one_le_shiftedWeight hLpos hθ p 0 b.1)
    have h4 := h1.trans (h2.trans h3)
    exact le_of_not_gt fun hlt => absurd h4 (not_le.2 (pow_lt_pow_left₀ hlt hB0 (by norm_num)))
  have hGB : ∀ b ∈ innerBonds D F.top, ‖G F.top b.1 b.2‖ ≤ B := fun b hb =>
    (norm_gaugedTransportedForm_le R γ f hodd F.top le_rfl b.1 b.2).trans (hmB b hb)
  have hnear := norm_gaugedTransportedForm_sub_flat_le R γ f hodd hL hE hR F.top le_rfl
  have hGP : ∀ b ∈ innerBonds D F.top, ‖G F.top b.1 b.2 - P F.top b.1 b.2‖ ≤ 12 * E * B := by
    intro b hb
    refine (hnear b hb).trans ?_
    rw [hl1, mul_one]
    exact mul_le_mul_of_nonneg_left (hmB b hb) (by positivity)
  have e1 := ChartCoordinates.innerBonds_ends b1
  have e2 := ChartCoordinates.innerBonds_ends b2
  have e3 := ChartCoordinates.innerBonds_ends b3
  have e4 := ChartCoordinates.innerBonds_ends b4
  have h1 := norm_flatCurl_sub_covariantCurlAt_le (gaugedField γ (R F.top)) (G F.top) q (hT _ _ e1.1 e1.2)
    (hT _ _ e2.1 e2.2) (hT _ _ e3.1 e3.2) (hT _ _ e4.1 e4.2)
  have h2 : ‖covariantCurlAt (gaugedField γ (R F.top)) (G F.top) q‖ =
      ‖covariantCurlAt (R F.top) (transportedForm R f F.top) q‖ := by
    show ‖covariantCurlAt (gaugedField γ (R F.top)) (gaugedForm γ (transportedForm R f F.top)) q‖ = _
    rw [covariantCurlAt_gaugedField, BlockLines.norm_adjointAction]
  have h3 := norm_flatCurl_le_add (G F.top) (P F.top) q
  have g2 := hGB _ b2
  have g3 := hGB _ b3
  have g4 := hGB _ b4
  have p1 := hGP _ b1
  have p2 := hGP _ b2
  have p3 := hGP _ b3
  have p4 := hGP _ b4
  have h4 : 8 * E * (‖G F.top (q.1 + unitStep F.top q.2.1) q.2.2‖ + ‖G F.top (q.1 + unitStep F.top q.2.2) q.2.1‖ +
      ‖G F.top q.1 q.2.2‖) ≤ 8 * E * (B + B + B) :=
    mul_le_mul_of_nonneg_left (add_le_add (add_le_add g2 g3) g4) (by positivity)
  have h5 := norm_sub_norm_le (covariantCurlAt (gaugedField γ (R F.top)) (G F.top) q) (flatCurl (G F.top) q)
  rw [norm_sub_rev, h2] at h5
  simp only [] at p1 p2 p3 p4
  nlinarith
theorem norm_gaugedField_top_sub_one_le (hodd : Odd F.blockSide) (R : F.FieldChain) (γ : F.Site 0 → UnitQuaternion)
    {D : Finset F.Cell} {E a : ℝ} (hE : 0 ≤ E)
    (hR : ∀ x i, x ∈ sitesOfCells D F.depth → x + unitStep F.depth i ∈ sitesOfCells D F.depth →
      ‖((gaugedField γ (R F.depth) x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ E * levelScale F F.depth)
    {c : F.Site F.top × Fin 4} (hc : c ∈ innerBonds D F.top) (U : UnitQuaternion)
    (h1 : ‖((R F.top c.1 c.2 * U⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ a)
    (h2 : ‖((pathHolonomy (R F.depth) (refineSite c.1) (bondContour F.blockSide 0 1 c.2) * U⁻¹ : UnitQuaternion) :
      ℍ[ℝ]) - 1‖ ≤ a) :
    ‖((gaugedField γ (R F.top) c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * a + 5 * E := by
  have hLpos := hodd.pos
  have h0 : (0 : Lattice4) ∈ centredCube F.blockSide := by
    refine Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ?_
    simp only [Pi.zero_apply]
    omega
  set l := bondContour F.blockSide 0 1 c.2 with hl
  set H := pathHolonomy (R F.depth) (refineSite c.1) l with hH
  have hscale : levelScale F F.depth = 1 / (F.blockSide : ℝ) := by
    unfold levelScale
    simp
  have hend : refineSite c.1 + siteOfCoords F.depth (endpoint 0 l) = refineSite (c.1 + unitStep F.top c.2) := by
    rw [hl, (bondContour_spec 1 c.2 hLpos h0).2]
    exact (refineSite_add_unitStep (j := F.depth) (Nat.lt_succ_self _) c.1 c.2).symm
  have hfr := GaugeMotions.pathHolonomy_gaugeTransform_of_base (fun x => γ (baseSite x)) (R F.depth)
    (refineSite c.1) l
  rw [hend, baseSite_refineSite F.depth le_rfl, baseSite_refineSite F.depth le_rfl] at hfr
  set a' := γ (baseSite c.1) with ha'
  set b' := γ (baseSite (c.1 + unitStep F.top c.2)) with hb'
  have hnear := norm_pathHolonomy_sub_one_le (Dset := (sitesOfCells D F.depth : Set (F.Site F.depth)))
    (Y := gaugedField γ (R F.depth)) (ε := E * levelScale F F.depth) hR (refineSite c.1) l 0
    (allAlong_bondContour hodd le_rfl hc h0 1)
  rw [add_siteOfCoords_zero] at hnear
  have hlen : (l.length : ℝ) ≤ 5 * F.blockSide := by
    have := length_bondContour_le (L := F.blockSide) (h := 0) 1 c.2 hLpos h0
    exact_mod_cast this
  have hfrH : ‖((a' * H * b'⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 5 * E := by
    have e : pathHolonomy (gaugedField γ (R F.depth)) (refineSite c.1) l = a' * H * b'⁻¹ := hfr
    rw [← e]
    refine hnear.trans ?_
    rw [hscale]
    have h3 : (l.length : ℝ) * (E * (1 / (F.blockSide : ℝ))) ≤ (5 * F.blockSide) * (E * (1 / (F.blockSide : ℝ))) :=
      mul_le_mul_of_nonneg_right hlen (by positivity)
    refine h3.trans (le_of_eq ?_)
    field_simp
  have hVH : ‖((R F.top c.1 c.2 * H⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * a := by
    have e : R F.top c.1 c.2 * H⁻¹ = (R F.top c.1 c.2 * U⁻¹) * (H * U⁻¹)⁻¹ := by group
    rw [e]
    refine (norm_coe_mul_sub_one_le _ _).trans ?_
    rw [norm_coe_inv_sub_one]
    linarith
  have e : gaugedField γ (R F.top) c.1 c.2 = (a' * (R F.top c.1 c.2 * H⁻¹) * a'⁻¹) * (a' * H * b'⁻¹) := by
    show a' * R F.top c.1 c.2 * b'⁻¹ = _
    group
  rw [e]
  refine (norm_coe_mul_sub_one_le _ _).trans ?_
  rw [norm_coe_conj_sub_one]
  linarith
theorem variationCurl_eq_covariantCurlAt {j : ℕ} (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions)
    (q : F.Site j × Fin 4 × Fin 4) :
    variationCurl X v q = covariantCurlAt X (fun x i => (v x i : ℍ[ℝ])) q := by
  obtain ⟨x, μ, ν⟩ := q
  have e3 : x + unitStep j μ + unitStep j ν - unitStep j μ = x + unitStep j ν := by abel
  have hneg : ∀ (g : UnitQuaternion) (w : ℍ[ℝ]), _root_.YangMills.Construction.BlockAverages.adjointAction g (-w) = -_root_.YangMills.Construction.BlockAverages.adjointAction g w := fun g w => by
    simp [_root_.YangMills.Construction.BlockAverages.adjointAction]
  have hzero : ∀ g : UnitQuaternion, _root_.YangMills.Construction.BlockAverages.adjointAction g 0 = 0 := fun g => by simp [_root_.YangMills.Construction.BlockAverages.adjointAction]
  simp only [variationCurl, pathHolonomyVariation, linkValueVariation, linkValue, BlockAverages.stepDisplacement,
    covariantCurlAt, if_true, Bool.false_eq_true, if_false]
  have e5 : x + unitStep j μ + unitStep j ν + -unitStep j μ - unitStep j ν = x := by abel
  rw [e3, e5]
  simp only [hzero, add_zero, hneg, BlockAverages.adjointAction_add, _root_.YangMills.Construction.BlockAverages.adjointAction_mul]
  abel
theorem covariantCurlAt_add {j : ℕ} (X : F.GaugeField j) (f g : F.Site j → Fin 4 → ℍ[ℝ])
    (q : F.Site j × Fin 4 × Fin 4) :
    covariantCurlAt X (fun x i => f x i + g x i) q = covariantCurlAt X f q + covariantCurlAt X g q := by
  simp only [covariantCurlAt, BlockAverages.adjointAction_add]
  abel
theorem norm_covariantCurlAt_le {j : ℕ} (X : F.GaugeField j) (g : F.Site j → Fin 4 → ℍ[ℝ])
    (q : F.Site j × Fin 4 × Fin 4) :
    ‖covariantCurlAt X g q‖ ≤ ‖g q.1 q.2.1‖ + ‖g (q.1 + unitStep j q.2.1) q.2.2‖ +
      ‖g (q.1 + unitStep j q.2.2) q.2.1‖ + ‖g q.1 q.2.2‖ := by
  simp only [covariantCurlAt]
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_sub_le (g q.1 q.2.1 + _root_.YangMills.Construction.BlockAverages.adjointAction (X q.1 q.2.1) (g (q.1 + unitStep j q.2.1) q.2.2))
    (_root_.YangMills.Construction.BlockAverages.adjointAction (X q.1 q.2.1 * X (q.1 + unitStep j q.2.1) q.2.2 * (X (q.1 + unitStep j q.2.2) q.2.1)⁻¹)
      (g (q.1 + unitStep j q.2.2) q.2.1))
  have h2 := norm_add_le (g q.1 q.2.1) (_root_.YangMills.Construction.BlockAverages.adjointAction (X q.1 q.2.1) (g (q.1 + unitStep j q.2.1) q.2.2))
  rw [BlockLines.norm_adjointAction] at h1 h2 ⊢
  linarith
theorem sum_comp_le_card_mul_sum {α β ι : Type} [Fintype ι] (P : Finset α) (B : Finset β) (f : α → β) (g : β → ℝ)
    (hg : ∀ b, 0 ≤ g b) (hm : ∀ p ∈ P, f p ∈ B) (r : α → ι)
    (hr : ∀ p ∈ P, ∀ q ∈ P, f p = f q → r p = r q → p = q) :
    ∑ p ∈ P, g (f p) ≤ Fintype.card ι * ∑ b ∈ B, g b := by
  classical
  have h1 : ∑ p ∈ P, g (f p) = ∑ b ∈ B, ∑ p ∈ P.filter (fun p => f p = b), g (f p) :=
    (Finset.sum_fiberwise_of_maps_to hm _).symm
  rw [h1, Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  have h2 : ∑ p ∈ P.filter (fun p => f p = b), g (f p) = (P.filter (fun p => f p = b)).card * g b := by
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.1 hp).2]), Finset.sum_const, nsmul_eq_mul]
  rw [h2]
  have h3 : (P.filter (fun p => f p = b)).card ≤ Fintype.card ι := by
    refine Finset.card_le_card_of_injOn (t := Finset.univ) r (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
    intro p hp q hq h
    have hp' := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
    have hq' := Finset.mem_filter.1 (Finset.mem_coe.1 hq)
    exact hr p hp'.1 q hq'.1 (hp'.2.trans hq'.2.symm) h
  have h4 : ((P.filter (fun p => f p = b)).card : ℝ) ≤ Fintype.card ι := by exact_mod_cast h3
  exact mul_le_mul_of_nonneg_right h4 (hg b)
theorem sum_covariantCurlAt_sq_le {j : ℕ} (S : Finset F.Cell) (X : F.GaugeField j) (g : F.Site j → Fin 4 → ℍ[ℝ]) :
    ∑ q ∈ innerPlaquettes S j, ‖covariantCurlAt X g q‖ ^ 2 ≤ 64 * ∑ b ∈ innerBonds S j, ‖g b.1 b.2‖ ^ 2 := by
  set G : F.Site j × Fin 4 → ℝ := fun b => ‖g b.1 b.2‖ ^ 2 with hG
  have hG0 : ∀ b, 0 ≤ G b := fun b => by positivity
  have s1 : ∑ q ∈ innerPlaquettes S j, G (q.1, q.2.1) ≤ (Fintype.card (Fin 4)) * ∑ b ∈ innerBonds S j, G b :=
    sum_comp_le_card_mul_sum _ _ (fun q : F.Site j × Fin 4 × Fin 4 => (q.1, q.2.1)) G hG0
      (fun q hq => (plaquette_bonds_mem hq).1) (fun q => q.2.2) (by
      rintro ⟨x, μ, ν⟩ _ ⟨x', μ', ν'⟩ _ h h'
      simp only [Prod.mk.injEq] at h
      simp only at h'
      simp [h.1, h.2, h'])
  have s2 : ∑ q ∈ innerPlaquettes S j, G (q.1 + unitStep j q.2.1, q.2.2) ≤
      (Fintype.card (Fin 4)) * ∑ b ∈ innerBonds S j, G b :=
    sum_comp_le_card_mul_sum _ _ (fun q : F.Site j × Fin 4 × Fin 4 => (q.1 + unitStep j q.2.1, q.2.2)) G hG0
      (fun q hq => (plaquette_bonds_mem hq).2.1) (fun q => q.2.1) (by
      rintro ⟨x, μ, ν⟩ _ ⟨x', μ', ν'⟩ _ h h'
      simp only [Prod.mk.injEq] at h
      simp only at h'
      subst h'
      simp [add_right_cancel h.1, h.2])
  have s3 : ∑ q ∈ innerPlaquettes S j, G (q.1 + unitStep j q.2.2, q.2.1) ≤
      (Fintype.card (Fin 4)) * ∑ b ∈ innerBonds S j, G b :=
    sum_comp_le_card_mul_sum _ _ (fun q : F.Site j × Fin 4 × Fin 4 => (q.1 + unitStep j q.2.2, q.2.1)) G hG0
      (fun q hq => (plaquette_bonds_mem hq).2.2.1) (fun q => q.2.2) (by
      rintro ⟨x, μ, ν⟩ _ ⟨x', μ', ν'⟩ _ h h'
      simp only [Prod.mk.injEq] at h
      simp only at h'
      subst h'
      simp [add_right_cancel h.1, h.2])
  have s4 : ∑ q ∈ innerPlaquettes S j, G (q.1, q.2.2) ≤ (Fintype.card (Fin 4)) * ∑ b ∈ innerBonds S j, G b :=
    sum_comp_le_card_mul_sum _ _ (fun q : F.Site j × Fin 4 × Fin 4 => (q.1, q.2.2)) G hG0
      (fun q hq => (plaquette_bonds_mem hq).2.2.2) (fun q => q.2.1) (by
      rintro ⟨x, μ, ν⟩ _ ⟨x', μ', ν'⟩ _ h h'
      simp only [Prod.mk.injEq] at h
      simp only at h'
      simp [h.1, h.2, h'])
  have h1 : ∑ q ∈ innerPlaquettes S j, ‖covariantCurlAt X g q‖ ^ 2 ≤
      ∑ q ∈ innerPlaquettes S j, 4 * (G (q.1, q.2.1) + G (q.1 + unitStep j q.2.1, q.2.2) +
        G (q.1 + unitStep j q.2.2, q.2.1) + G (q.1, q.2.2)) := by
    refine Finset.sum_le_sum fun q _ => ?_
    have h := norm_covariantCurlAt_le X g q
    simp only [hG]
    set A := ‖g q.1 q.2.1‖
    set B := ‖g (q.1 + unitStep j q.2.1) q.2.2‖
    set C := ‖g (q.1 + unitStep j q.2.2) q.2.1‖
    set D := ‖g q.1 q.2.2‖
    have h2 : ‖covariantCurlAt X g q‖ ^ 2 ≤ (A + B + C + D) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (A - D), sq_nonneg (B - C),
      sq_nonneg (B - D), sq_nonneg (C - D)]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at h1
  simp only [Fintype.card_fin, Nat.cast_ofNat] at s1 s2 s3 s4
  linarith
theorem shiftedWeight_zero (p : F.Site 0) (j : ℕ) (x : F.Site j) : shiftedWeight F 0 p j x = 1 := by
  simp [shiftedWeight]
theorem zero_mem_centredCube (hodd : Odd F.blockSide) : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by apply _root_.YangMills.Construction.GaugeFixing.zero_mem_centredCube <;> assumption
theorem cellSupDist_add_siteOfCoords_le (z : F.Cell) (v : Fin 4 → ℤ) (hv : ∀ i, (v i).natAbs ≤ 2) :
    cellSupDist (z + siteOfCoords F.top v) z ≤ 2 := by
  refine Finset.sup_le fun i _ => ?_
  have e : (z + siteOfCoords F.top v : F.Cell) i - z i = ((v i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  rw [e]
  exact (natAbs_valMinAbs_intCast_le _ _).trans (hv i)
theorem enclosingCell_cellCentre (hodd : Odd F.blockSide) (z : F.Cell) : enclosingCell (cellCentre 0 z) = z := by
  have h := PatchPoints.enclosingCell_cellCentre_add (j := 0) hodd z 0 (by
    refine Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ?_
    have hL : (1 : ℤ) ≤ ((F.blockSide ^ (F.top - 0) : ℕ) : ℤ) := by exact_mod_cast hodd.pow.pos
    simp only [Pi.zero_apply]
    omega)
  rwa [siteOfCoords_zero, add_zero] at h
theorem natAbs_basisVector_add_le (μ ν : Fin 4) (i : Fin 4) : ((basisVector μ + basisVector ν) i).natAbs ≤ 2 := by
  simp only [Pi.add_apply, basisVector, Pi.single_apply]
  split_ifs <;> simp
theorem natAbs_basisVector_le (μ : Fin 4) (i : Fin 4) : (basisVector μ i).natAbs ≤ 2 := by
  simp only [basisVector, Pi.single_apply]
  split_ifs <;> simp
theorem mem_innerPlaquettes_cellsNearPoint (hodd : Odd F.blockSide) {S : Finset F.Cell}
    {q : F.Site F.top × Fin 4 × Fin 4} (hq : q ∈ innerPlaquettes S F.top) :
    q ∈ innerPlaquettes (cellsNearPoint S (cellCentre 0 q.1)) F.top := by
  classical
  obtain ⟨h1, hlt, hc⟩ := Finset.mem_filter.1 hq
  have hcell := enclosingCell_cellCentre hodd q.1
  have hmem : ∀ y ∈ plaquetteCorners q, y ∈ sitesOfCells (cellsNearPoint S (cellCentre 0 q.1)) F.top := by
    intro y hy
    have hyS : y ∈ S := mem_sitesOfCells_top.1 (hc hy)
    refine mem_sitesOfCells_top.2 (Finset.mem_filter.2 ⟨hyS, ?_⟩)
    rw [hcell]
    simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · rw [BlockLines.cellSupDist_self]
      omega
    · exact cellSupDist_add_siteOfCoords_le q.1 (basisVector q.2.1) (natAbs_basisVector_le _)
    · exact cellSupDist_add_siteOfCoords_le q.1 (basisVector q.2.2) (natAbs_basisVector_le _)
    · have := cellSupDist_add_siteOfCoords_le q.1 (basisVector q.2.1 + basisVector q.2.2)
        (natAbs_basisVector_add_le _ _)
      rwa [siteOfCoords_add, ← add_assoc] at this
  exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hmem _ (by simp [plaquetteCorners]),
    (Finset.mem_product.1 h1).2⟩, hlt, fun y hy => hmem y hy⟩
def localCurlSq (S : Finset F.Cell) (R : F.FieldChain) (A : ChainChart F) (z : F.Cell) : ℝ :=
  ∑ q ∈ innerPlaquettes (cellsNearPoint S (cellCentre 0 z)) 0, ‖linearizedCurl (R 0) A.fine q‖ ^ 2
theorem localCurlSq_nonneg (S : Finset F.Cell) (R : F.FieldChain) (A : ChainChart F) (z : F.Cell) :
    0 ≤ localCurlSq S R A z :=
  Finset.sum_nonneg fun _ _ => by positivity
theorem sum_localCurlSq_le (hodd : Odd F.blockSide) (S : Finset F.Cell) (R : F.FieldChain) (A : ChainChart F) :
    ∑ z ∈ S, localCurlSq S R A z ≤ 625 * ∑ q ∈ plaquettesOver S S 0, ‖linearizedCurl (R 0) A.fine q‖ ^ 2 := by
  classical
  set P := plaquettesOver S S 0 with hP
  set w : F.Site 0 × Fin 4 × Fin 4 → ℝ := fun q => ‖linearizedCurl (R 0) A.fine q‖ ^ 2 with hw
  have hw0 : ∀ q, 0 ≤ w q := fun q => by positivity
  have hone : ∀ z ∈ S, localCurlSq S R A z ≤ ∑ q ∈ P, if z ∈ cellsNearPoint S q.1 then w q else 0 := by
    intro z hz
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => hw0 q
    intro q hq
    have hDS : cellsNearPoint S (cellCentre 0 z) ⊆ S := Finset.filter_subset _ _
    have hq1 : q.1 ∈ sitesOfCells (cellsNearPoint S (cellCentre 0 z)) 0 :=
      (Finset.mem_filter.1 hq).2.2 (by simp [plaquetteCorners])
    have hc := enclosingCell_mem hodd hq1
    have hd := (Finset.mem_filter.1 hc).2
    rw [enclosingCell_cellCentre hodd] at hd
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨?_, hDS hc⟩, Finset.mem_filter.2 ⟨hz, ?_⟩⟩
    · obtain ⟨h1, hlt, h3⟩ := Finset.mem_filter.1 hq
      have hsub : sitesOfCells (cellsNearPoint S (cellCentre 0 z)) 0 ⊆ sitesOfCells S 0 := by
        intro x hx
        obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
        exact mem_sitesOfCells.2 ⟨y, hDS hy, h, hh, rfl⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hsub (Finset.mem_product.1 h1).1,
        (Finset.mem_product.1 h1).2⟩, hlt, h3.trans hsub⟩
    · rwa [BlockLines.cellSupDist_comm]
  refine (Finset.sum_le_sum hone).trans ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hw0 q)
  have h1 : (S.filter fun z => z ∈ cellsNearPoint S q.1).card ≤ 625 :=
    (Finset.card_le_card fun z hz => (Finset.mem_filter.1 hz).2).trans (card_cellsNearPoint_le S q.1)
  exact_mod_cast h1
theorem localNorm_sq (S : Finset F.Cell) (R : F.FieldChain) (A : ChainChart F) (w : F.SiteWeights) (z : F.Cell) :
    localNorm S R A w z ^ 2 = localNormSq S (cellBall S z 3) R A w := by
  unfold localNorm
  refine Real.sq_sqrt ?_
  unfold localNormSq
  have h1 := Real.sqrt_nonneg (∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4)
  have h2 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 p.1 * ‖linearizedCurl (R 0) A.fine p‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have h3 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (w (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  linarith
theorem sq_le_of_le_two_mul_add {y a e b : ℝ} (hy : 0 ≤ y) (h : y ≤ 2 * a + e * b) (ha : 0 ≤ a) (he : 0 ≤ e)
    (hb : 0 ≤ b) : y ^ 2 ≤ 8 * a ^ 2 + 2 * e ^ 2 * b ^ 2 := by
  have h1 := pow_le_pow_left₀ hy h 2
  nlinarith [sq_nonneg (2 * a - e * b)]
theorem sq_norm_covariantCurlAt_top_le (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide)
    (hamb : IsAdmissibleAmbient F) {m : ℕ} (hm : 1024 ≤ m) {S : Finset F.Cell} (hreg : IsOrthantRegular S m)
    {V : F.GaugeField F.top} {Db s : ℝ} (hDb : 0 < Db) (hs : 0 < s)
    (c1 : ∀ j, j < F.top → ∀ z ∈ S, ∀ b ∈ innerBonds S j, baseSite b.1 ∈ (patchDomain S z).image (patchSite S z) →
      baseSite (b.1 + unitStep j b.2) ∈ (patchDomain S z).image (patchSite S z) →
      unitDeviation (referenceInPatchFrame S V z j b.1 b.2) ≤ Db * s * levelScale F j)
    (c4 : ∀ c' ∈ innerBonds S F.top,
      unitDeviation (referenceDefect (referenceFieldChain S V) F.depth c') ≤ Db * s)
    (c5 : ∀ j, j < F.top → ∀ c' ∈ innerBonds S (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      unitDeviation (pathHolonomy (referenceFieldChain S V j) (refineSite c'.1) (bondContour F.blockSide h π c'.2) *
          (polarUnit (contourAverage (referenceFieldChain S V j) c'))⁻¹) ≤ Db * s * levelScale F (j + 1) ^ 2)
    (A : ChainChart F) {q : F.Site F.top × Fin 4 × Fin 4} (hq : q ∈ innerPlaquettes S F.top) :
    ‖covariantCurlAt (referenceFieldChain S V F.top)
        (transportedForm (referenceFieldChain S V) (fun x i => (A.fine x i : ℍ[ℝ])) F.top) q‖ ^ 2 ≤
      8 * localCurlSq S (referenceFieldChain S V) A q.1 +
        2 * (2072 * (7 * Db * s)) ^ 2 * localNorm S (referenceFieldChain S V) A (oneSiteWeights F) q.1 ^ 2 := by
  classical
  have hzS : q.1 ∈ S := mem_sitesOfCells_top.1 ((Finset.mem_filter.1 hq).2.2 (by simp [plaquetteCorners]))
  set R := referenceFieldChain S V with hRdef
  set u : F.Site 0 → Fin 4 → ℍ[ℝ] := fun x i => (A.fine x i : ℍ[ℝ]) with hu
  set z := q.1 with hzdef
  set D := cellsNearPoint S (cellCentre 0 z) with hD
  have hDS : D ⊆ S := Finset.filter_subset _ _
  have hcell := enclosingCell_cellCentre hodd z
  have hqD : q ∈ innerPlaquettes D F.top := mem_innerPlaquettes_cellsNearPoint hodd hq
  have he := (closedOrthant_spec hreg (by omega : 32 ≤ m) z).1
  have hd2 : ∀ y ∈ D, cellSupDist y z ≤ 2 := by
    intro y hy
    have := (Finset.mem_filter.1 hy).2
    rwa [hcell] at this
  have hd : ∀ y ∈ D, cellSupDist z y ≤ 10 := by
    intro y hy
    have := hd2 y hy
    rw [BlockLines.cellSupDist_comm] at this
    omega
  set γ : F.Site 0 → UnitQuaternion := fun x => (frameChange S V z x)⁻¹ with hγ
  have hl0 : ∀ j, 0 ≤ levelScale F j := fun j => by
    unfold levelScale
    positivity
  have hDs : 0 < Db * s := by positivity
  have hR0 : ∀ j, j < F.top → ∀ x i, x ∈ sitesOfCells D j → x + unitStep j i ∈ sitesOfCells D j →
      ‖((gaugedField γ (R j) x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ (Db * s) * levelScale F j := by
    intro j hj x i h1 h2
    exact c1 j hj z hzS (x, i) (innerBonds_mono hDS j (ChartCoordinates.mem_innerBonds h1 h2))
      (baseSite_mem_patch hamb hodd he hDS hd hj.le h1) (baseSite_mem_patch hamb hodd he hDS hd hj.le h2)
  set E := 7 * Db * s with hE
  have hE0 : 0 ≤ E := by positivity
  have hR : ∀ j, j < F.top → ∀ x i, x ∈ sitesOfCells D j → x + unitStep j i ∈ sitesOfCells D j →
      ‖((gaugedField γ (R j) x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ E * levelScale F j := by
    intro j hj x i h1 h2
    refine (hR0 j hj x i h1 h2).trans (mul_le_mul_of_nonneg_right ?_ (hl0 j))
    rw [hE]
    nlinarith
  have htop : levelScale F (F.depth + 1) = 1 := by
    unfold levelScale
    simp
  have hT : ∀ x i, x ∈ sitesOfCells D F.top → x + unitStep F.top i ∈ sitesOfCells D F.top →
      ‖((gaugedField γ (R F.top) x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ E := by
    intro x i h1 h2
    have hb : ((x, i) : F.Site F.top × Fin 4) ∈ innerBonds D F.top := ChartCoordinates.mem_innerBonds h1 h2
    have hbS := innerBonds_mono hDS F.top hb
    have a1 := c4 (x, i) hbS
    simp only [unitDeviation, referenceDefect] at a1
    have a2 := c5 F.depth (Nat.lt_succ_self _) (x, i) hbS 0 (zero_mem_centredCube hodd) 1
    rw [htop, one_pow, mul_one] at a2
    simp only [unitDeviation] at a2
    have h3 := norm_gaugedField_top_sub_one_le hodd R γ hDs.le
      (fun x i a b => hR0 F.depth (Nat.lt_succ_self _) x i a b) hb _ a1 a2
    refine h3.trans (le_of_eq ?_)
    rw [hE]
    ring
  have hcard : ((innerBonds D 0).card : ℝ) ≤ 2500 * ((F.blockSide : ℝ) ^ F.top) ^ 4 := by
    have h2 := card_innerBonds_le hodd D 0
    have h3 : D.card * (F.blockSide ^ (F.top - 0)) ^ 4 ≤ 625 * (F.blockSide ^ (F.top - 0)) ^ 4 :=
      Nat.mul_le_mul_right _ (card_cellsNearPoint_le S _)
    have h4 : (innerBonds D 0).card ≤ 4 * (625 * (F.blockSide ^ (F.top - 0)) ^ 4) :=
      h2.trans (Nat.mul_le_mul_left 4 h3)
    have h5 : ((innerBonds D 0).card : ℝ) ≤ ((4 * (625 * (F.blockSide ^ (F.top - 0)) ^ 4) : ℕ) : ℝ) := by
      exact_mod_cast h4
    refine h5.trans (le_of_eq ?_)
    push_cast
    simp only [Nat.sub_zero]
    ring
  set T := localCurlSq S R A z with hTdef
  have hT0 : 0 ≤ T := localCurlSq_nonneg S R A z
  set X := ∑ b ∈ innerBonds D 0, ‖u b.1 b.2‖ ^ 4 with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun _ _ => by positivity
  have hA : ∑ q ∈ innerPlaquettes D 0, (shiftedWeight F 0 (cellCentre 0 z) 0 q.1 * ‖covariantCurlAt (R 0) u q‖) ^ 2 ≤
      Real.sqrt T ^ 2 := by
    rw [Real.sq_sqrt hT0]
    refine le_of_eq (Finset.sum_congr rfl fun q' _ => ?_)
    rw [shiftedWeight_zero, one_mul]
    rfl
  have hB : ∑ b ∈ innerBonds D 0, (shiftedWeight F 0 (cellCentre 0 z) 0 b.1 * ‖u b.1 b.2‖) ^ 4 ≤
      Real.sqrt (Real.sqrt X) ^ 4 := by
    have e : Real.sqrt (Real.sqrt X) ^ 4 = X := by
      have e1 : Real.sqrt (Real.sqrt X) ^ 4 = (Real.sqrt (Real.sqrt X) ^ 2) ^ 2 := by ring
      rw [e1, Real.sq_sqrt (Real.sqrt_nonneg X), Real.sq_sqrt hX0]
    rw [e]
    refine le_of_eq (Finset.sum_congr rfl fun b _ => ?_)
    rw [shiftedWeight_zero, one_mul]
  have main := norm_covariantCurlAt_top_le hodd hL R γ (θ := 0) le_rfl zero_le_one hE0 hR hT hcard u (cellCentre 0 z)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hA hB hqD
  have hsq := sq_le_of_le_two_mul_add (norm_nonneg _) (by
    refine main.trans (le_of_eq ?_)
    ring : ‖covariantCurlAt (R F.top) (transportedForm R u F.top) q‖ ≤
      2 * Real.sqrt T + (2072 * E) * Real.sqrt (Real.sqrt X))
    (Real.sqrt_nonneg T) (by positivity) (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt hT0, Real.sq_sqrt (Real.sqrt_nonneg X)] at hsq
  refine hsq.trans ?_
  have hN : Real.sqrt X ≤ localNorm S R A (oneSiteWeights F) z ^ 2 := by
    rw [localNorm_sq]
    unfold localNormSq
    have h1 : Real.sqrt X ≤ Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0,
        (oneSiteWeights F 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4) := by
      refine Real.sqrt_le_sqrt ?_
      have hsub : innerBonds D 0 ⊆ bondsOver S (cellBall S z 3) 0 := by
        intro b hb
        have hc := enclosingCell_mem hodd (ChartCoordinates.innerBonds_ends hb).1
        have hbS := innerBonds_mono hDS 0 hb
        refine Finset.mem_filter.2 ⟨hbS, Finset.mem_filter.2 ⟨hDS hc, ?_⟩⟩
        have := hd2 _ hc
        rw [BlockLines.cellSupDist_comm] at this
        omega
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity) (le_of_eq ?_)
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [oneSiteWeights, one_mul]
      rfl
    have h2 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0,
        (oneSiteWeights F 0 p.1 * ‖linearizedCurl (R 0) A.fine p‖) ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    have h3 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (oneSiteWeights F (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    linarith
  have h6 := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ 2 * (2072 * E) ^ 2)
  linarith
def coarseOnly (U : ChainChart F) : ChainChart F := ⟨fun _ _ => 0, U.coarse⟩
theorem adjointAction_add' (g : UnitQuaternion) (p q : ℍ[ℝ]) :
    adjointAction g (p + q) = adjointAction g p + adjointAction g q := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_add <;> assumption
theorem parallelAverage_add {j : ℕ} (R : F.GaugeField j) (f g : F.Site j → Fin 4 → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) :
    parallelAverage R (fun x i => f x i + g x i) c = parallelAverage R f c + parallelAverage R g c := by
  simp only [parallelAverage, adjointAction_add', Finset.sum_add_distrib, smul_add]
theorem norm_add_sq_le (p q : ℍ[ℝ]) : ‖p + q‖ ^ 2 ≤ 2 * ‖p‖ ^ 2 + 2 * ‖q‖ ^ 2 := by
  have h := norm_add_le p q
  have h0 := norm_nonneg (p + q)
  have hx := norm_nonneg p
  have hy := norm_nonneg q
  generalize ‖p + q‖ = z at *
  generalize ‖p‖ = x at *
  generalize ‖q‖ = y at *
  nlinarith [sq_nonneg (x - y)]
theorem le_four_mul_of_step (a t q P m : ℝ) (h1 : m ≤ 2 * t + 2 * q) (h2 : t ≤ 1 / 9 * a) (h3 : a ≤ 4 * P)
    (h4 : 0 ≤ q) (h5 : 0 ≤ P) : m ≤ 4 * (q + P) := by
  linarith
theorem le_four_mul_of_step' (a t P : ℝ) (h2 : t ≤ 1 / 9 * a) (h3 : a ≤ 4 * P) (h4 : 0 ≤ P) : t ≤ 4 * P := by
  linarith
theorem sum_linearPart_coarseOnly_sq_le (hL : Odd F.blockSide) (hL3 : 3 ≤ F.blockSide) (B : Finset F.Cell)
    (R : F.FieldChain) (U : ChainChart F) (k : ℕ) (hk : k ≤ F.top) :
    ∑ b ∈ innerBonds B k, ‖linearPart R (coarseOnly U) k b.1 b.2‖ ^ 2 ≤
      4 * ∑ j ∈ (Finset.range k).filter (fun j => j + 1 < F.top), ∑ c ∈ innerBonds B (j + 1),
        ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 := by
  induction k with
  | zero => simp [linearPart, coarseOnly]
  | succ k ih =>
    have hLR : (3 : ℝ) ≤ F.blockSide := by exact_mod_cast hL3
    have h := sum_norm_parallelAverage_sq_le (B := B) (j := k) (by omega) hL (innerBonds B (k + 1)) subset_rfl (R k)
      (linearPart R (coarseOnly U) k)
    have hq : 1 / (F.blockSide : ℝ) ^ 2 ≤ 1 / 9 := by
      apply one_div_le_one_div_of_le (by norm_num)
      nlinarith
    have hnn : 0 ≤ ∑ b ∈ innerBonds B k, ‖linearPart R (coarseOnly U) k b.1 b.2‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 2
    have hprev := ih (by omega)
    have hfil : (Finset.range (k + 1)).filter (fun j => j + 1 < F.top) =
        if k + 1 < F.top then insert k ((Finset.range k).filter (fun j => j + 1 < F.top))
        else (Finset.range k).filter (fun j => j + 1 < F.top) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      split_ifs with hk1
      · simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h3 | h3
          · exact Or.inr ⟨h3, h2⟩
          · exact Or.inl h3
        · rintro (h1 | ⟨h1, h2⟩)
          · subst h1
            exact ⟨by omega, hk1⟩
          · exact ⟨by omega, h2⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
    by_cases hk1 : k + 1 < F.top
    · have hnot : k ∉ (Finset.range k).filter (fun j => j + 1 < F.top) := by simp
      rw [hfil, if_pos hk1, Finset.sum_insert hnot]
      have hpt : ∀ c ∈ innerBonds B (k + 1), ‖linearPart R (coarseOnly U) (k + 1) c.1 c.2‖ ^ 2 ≤
          2 * ‖parallelAverage (R k) (linearPart R (coarseOnly U) k) c‖ ^ 2 +
            2 * ‖(U.coarse k c.1 c.2 : ℍ[ℝ])‖ ^ 2 := by
        intro c _
        simp only [linearPart, if_pos hk1]
        exact norm_add_sq_le _ _
      have hsum := Finset.sum_le_sum hpt
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
      have hm : ∑ c ∈ innerBonds B (k + 1), ‖parallelAverage (R k) (linearPart R (coarseOnly U) k) c‖ ^ 2 ≤
          (1 / 9) * ∑ b ∈ innerBonds B k, ‖linearPart R (coarseOnly U) k b.1 b.2‖ ^ 2 :=
        h.trans (mul_le_mul_of_nonneg_right hq hnn)
      have hq0 : 0 ≤ ∑ c ∈ innerBonds B (k + 1), ‖(U.coarse k c.1 c.2 : ℍ[ℝ])‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 2
      have hP0 : 0 ≤ ∑ j ∈ (Finset.range k).filter (fun j => j + 1 < F.top), ∑ c ∈ innerBonds B (j + 1),
          ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 2
      exact le_four_mul_of_step _ _ _ _ _ hsum hm hprev hq0 hP0
    · rw [hfil, if_neg hk1]
      have hpt : ∀ c ∈ innerBonds B (k + 1), ‖linearPart R (coarseOnly U) (k + 1) c.1 c.2‖ ^ 2 =
          ‖parallelAverage (R k) (linearPart R (coarseOnly U) k) c‖ ^ 2 := by
        intro c _
        simp only [linearPart, if_neg hk1, add_zero]
      rw [Finset.sum_congr rfl hpt]
      have : 0 ≤ ∑ j ∈ (Finset.range k).filter (fun j => j + 1 < F.top), ∑ c ∈ innerBonds B (j + 1),
          ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 2
      have h2 : ∑ c ∈ innerBonds B (k + 1), ‖parallelAverage (R k) (linearPart R (coarseOnly U) k) c‖ ^ 2 ≤
          (1 / 9) * ∑ b ∈ innerBonds B k, ‖linearPart R (coarseOnly U) k b.1 b.2‖ ^ 2 :=
        h.trans (mul_le_mul_of_nonneg_right hq hnn)
      exact le_four_mul_of_step' _ _ _ h2 hprev this
theorem re_parallelAverage {j : ℕ} (R : F.GaugeField j) {f : F.Site j → Fin 4 → ℍ[ℝ]} (hf : ∀ x i, (f x i).re = 0)
    (c : F.Site (j + 1) × Fin 4) : (parallelAverage R f c).re = 0 := by apply _root_.YangMills.Construction.BlockAverages.CoordinateStep.re_parallelAverage_eq_zero <;> assumption
theorem re_linearPart (R : F.FieldChain) (U : ChainChart F) : ∀ k x i, (linearPart R U k x i).re = 0 := by
  intro k
  induction k with
  | zero => exact fun x i => (U.fine x i).2
  | succ k ih =>
    intro y i
    simp only [linearPart]
    have h1 := re_parallelAverage (R k) ih ((y, i) : F.Site (k + 1) × Fin 4)
    split_ifs
    · have h2 : ((U.coarse k y i : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := (U.coarse k y i).2
      simp [h1, h2]
    · simp [h1]
theorem coe_topLevelAverage (R : F.FieldChain) (A : ChainChart F) (y : F.Site F.top) (i : Fin 4) :
    ((topLevelAverage R A y i : imaginaryQuaternions) : ℍ[ℝ]) = linearPart R A F.top y i :=
  BlockAverages.pureComponent_of_re_eq_zero (re_linearPart R A F.top y i)
theorem linearPart_eq_add (R : F.FieldChain) (U : ChainChart F) (k : ℕ) :
    linearPart R U k = fun x i =>
      transportedForm R (fun x i => (U.fine x i : ℍ[ℝ])) k x i + linearPart R (coarseOnly U) k x i := by
  induction k with
  | zero =>
    funext x i
    simp [linearPart, transportedForm, coarseOnly]
  | succ k ih =>
    funext y i
    simp only [linearPart, transportedForm]
    rw [ih, parallelAverage_add]
    split_ifs
    · simp only [coarseOnly]
      abel
    · simp
theorem sum_variationCurl_sq_le {F : BlockFrame} (hodd : Odd F.blockSide) (hL : 5 ≤ F.blockSide) (S : Finset F.Cell)
    {V : F.GaugeField F.top} {Db s : ℝ} (hDb : 0 < Db) (hs : 0 < s) (A : ChainChart F)
    (hV : referenceFieldChain S V F.top = V)
    (hone : ∀ q ∈ innerPlaquettes S F.top,
      ‖covariantCurlAt (referenceFieldChain S V F.top)
          (transportedForm (referenceFieldChain S V) (fun x i => (A.fine x i : ℍ[ℝ])) F.top) q‖ ^ 2 ≤
        8 * localCurlSq S (referenceFieldChain S V) A q.1 +
          2 * (2072 * (7 * Db * s)) ^ 2 * localNorm S (referenceFieldChain S V) A (oneSiteWeights F) q.1 ^ 2) :
    ∑ p ∈ innerPlaquettes S F.top, ‖variationCurl V (topLevelAverage (referenceFieldChain S V) A) p‖ ^ 2 ≤
      (160000 + 64 * 2072 ^ 2 * 49 * Db ^ 2) *
        (∑ q ∈ plaquettesOver S S 0, ‖linearizedCurl (referenceFieldChain S V 0) A.fine q‖ ^ 2 +
          ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1), ‖A.coarse j c.1 c.2‖ ^ 2) +
        (160000 + 64 * 2072 ^ 2 * 49 * Db ^ 2) * s ^ 2 *
          _root_.YangMills.Construction.BlockAverages.weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ^ 2 := by
  classical
  set R := referenceFieldChain S V with hRdef
  set u : F.Site 0 → Fin 4 → ℍ[ℝ] := fun x i => (A.fine x i : ℍ[ℝ]) with hu
  set G := transportedForm R u F.top with hG
  set M := linearPart R (coarseOnly A) F.top with hM
  have hfield : ∀ p, variationCurl V (topLevelAverage R A) p = covariantCurlAt V G p + covariantCurlAt V M p := by
    intro p
    rw [variationCurl_eq_covariantCurlAt]
    have e : (fun x i => ((topLevelAverage R A x i : imaginaryQuaternions) : ℍ[ℝ])) = fun x i => G x i + M x i := by
      funext x i
      rw [coe_topLevelAverage, linearPart_eq_add]
    rw [e, covariantCurlAt_add]
  set P := innerPlaquettes S F.top with hP
  have h1 : ∑ p ∈ P, ‖variationCurl V (topLevelAverage R A) p‖ ^ 2 ≤
      2 * ∑ p ∈ P, ‖covariantCurlAt V G p‖ ^ 2 + 2 * ∑ p ∈ P, ‖covariantCurlAt V M p‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [hfield]
    exact norm_add_sq_le _ _
  set K := 2 * (2072 * (7 * Db * s)) ^ 2 with hK
  set g : F.Cell → ℝ := fun z => 8 * localCurlSq S R A z + K * localNorm S R A (oneSiteWeights F) z ^ 2 with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z => by
    have := localCurlSq_nonneg S R A z
    simp only [hg]
    positivity
  have h2 : ∑ p ∈ P, ‖covariantCurlAt V G p‖ ^ 2 ≤ ∑ p ∈ P, g p.1 := by
    refine Finset.sum_le_sum fun p hp => ?_
    have := hone p hp
    rwa [hV] at this
  have h3 : ∑ p ∈ P, g p.1 ≤ (Fintype.card (Fin 4 × Fin 4)) * ∑ z ∈ S, g z :=
    sum_comp_le_card_mul_sum P S (fun p : F.Site F.top × Fin 4 × Fin 4 => p.1) g hg0
      (fun p hp => mem_sitesOfCells_top.1 ((Finset.mem_filter.1 hp).2.2 (by simp [plaquetteCorners])))
      (fun p => p.2) (fun p _ q _ e e' => Prod.ext e e')
  have h3' : ∑ p ∈ P, g p.1 ≤ 16 * ∑ z ∈ S, g z := by
    refine h3.trans (le_of_eq ?_)
    simp
  have hNO : _root_.YangMills.Construction.BlockAverages.weightedNorm S R A (oneSiteWeights F) ^ 2 = ∑ z ∈ S, localNorm S R A (oneSiteWeights F) z ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
  have h4 : ∑ z ∈ S, g z = 8 * ∑ z ∈ S, localCurlSq S R A z + K * _root_.YangMills.Construction.BlockAverages.weightedNorm S R A (oneSiteWeights F) ^ 2 := by
    rw [hNO, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  have h5 := sum_localCurlSq_le hodd S R A
  have h6 := sum_covariantCurlAt_sq_le S V M
  have h7 := sum_linearPart_coarseOnly_sq_le hodd (by omega) S R A F.top le_rfl
  set Tsum := ∑ q ∈ plaquettesOver S S 0, ‖linearizedCurl (R 0) A.fine q‖ ^ 2 with hTs
  set Msum := ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1), ‖A.coarse j c.1 c.2‖ ^ 2 with hMs
  have h8 : ∑ j ∈ (Finset.range F.top).filter (fun j => j + 1 < F.top), ∑ c ∈ innerBonds S (j + 1),
      ‖(A.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 ≤ Msum := by
    have hfil : (Finset.range F.top).filter (fun j => j + 1 < F.top) ⊆ Finset.range (F.top - 1) := by
      intro j hj
      have := (Finset.mem_filter.1 hj).2
      exact Finset.mem_range.2 (by omega)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hfil
      fun _ _ _ => Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 2).trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (s := innerBonds S (j + 1))
      (t := bondsOver S S (j + 1)) ?_ fun _ _ _ => pow_nonneg (norm_nonneg _) 2) (le_of_eq rfl)
    intro b hb
    exact Finset.mem_filter.2 ⟨hb, enclosingCell_mem hodd (ChartCoordinates.innerBonds_ends hb).1⟩
  set NO := _root_.YangMills.Construction.BlockAverages.weightedNorm S R A (oneSiteWeights F) ^ 2 with hNOdef
  have hT0 : 0 ≤ Tsum := Finset.sum_nonneg fun _ _ => by positivity
  have hM0 : 0 ≤ Msum := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  set W := 64 * 2072 ^ 2 * 49 * Db ^ 2 with hW
  have hW0 : 0 ≤ W := by positivity
  have hKW : 32 * K = W * s ^ 2 := by
    rw [hK, hW]
    ring
  have hfin : ∑ p ∈ P, ‖variationCurl V (topLevelAverage R A) p‖ ^ 2 ≤ 160000 * Tsum + 32 * K * NO + 512 * Msum := by
    nlinarith
  refine hfin.trans ?_
  rw [hKW]
  have b1 : 0 ≤ W * Tsum := mul_nonneg hW0 hT0
  have b2 : 0 ≤ W * Msum := mul_nonneg hW0 hM0
  have b3 : 0 ≤ s ^ 2 * NO := by positivity
  nlinarith
theorem topAverageCurlBoundStatement_holds (hB : BlockAverages.referenceBoundsStatement) :
    BlockAverages.topAverageCurlBoundStatement := by
  obtain ⟨Db, cb, L1, hDb, hcb, hBd⟩ := hB
  refine ⟨160000 + 64 * 2072 ^ 2 * 49 * Db ^ 2, by positivity, max L1 5, fun L hLo hLm => ⟨cb, hcb, ?_⟩⟩
  intro F m S hFL hamb hm hreg s V hs0 hsc hcold A
  subst hFL
  have hL1 : L1 ≤ F.blockSide := (le_max_left _ _).trans hLm
  have hL5 : 5 ≤ F.blockSide := (le_max_right _ _).trans hLm
  obtain ⟨c1, -, -, c4, c5, -⟩ := hBd F m S hLo hL1 hamb hm hreg s V hs0 hsc hcold
  have hV : referenceFieldChain S V F.top = V := by
    simp [referenceFieldChain]
  exact sum_variationCurl_sq_le hLo hL5 S hDb hs0 A hV fun q hq =>
    sq_norm_covariantCurlAt_top_le hLo (by omega) hamb hm hreg hDb hs0 c1 c4 c5 A hq
end YangMills.Construction.TopAverageCurl
end
