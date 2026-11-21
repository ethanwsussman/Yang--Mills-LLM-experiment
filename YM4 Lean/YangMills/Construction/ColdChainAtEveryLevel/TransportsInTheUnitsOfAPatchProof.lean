import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.ColdChainAtEveryLevel.GaugeOfAStaircaseProof
import YangMills.Construction.ColdChainAtEveryLevel.PlaquettesNearAPoint
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
open YangMills.Construction.LatticePaths
open YangMills.Construction.LatticeFractionalIntegration
open YangMills.Construction.StaircaseGauge
section Steps
variable {F : BlockFrame}
theorem stepDisplacement_forward (j : ℕ) (i : Fin 4) :
    stepDisplacement (F := F) j (i, true) = unitStep j i := by simp [stepDisplacement]
theorem stepDisplacement_backward (j : ℕ) (i : Fin 4) :
    stepDisplacement (F := F) j (i, false) = - unitStep j i := by simp [stepDisplacement]
theorem linkValue_forward {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (i : Fin 4) :
    linkValue X x (i, true) = X x i := by
  simp [linkValue]
theorem linkValue_backward {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (i : Fin 4) :
    linkValue X x (i, false) = (X (x - unitStep j i) i)⁻¹ := by simp [linkValue]
theorem stepDisplacement_reverse (j : ℕ) (st : PathStep) :
    stepDisplacement (F := F) j (st.1, !st.2) = - stepDisplacement j st := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.stepDisplacement_flip <;> assumption
theorem linkValue_reverse {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (st : PathStep) :
    linkValue X (x + stepDisplacement j st) (st.1, !st.2) = (linkValue X x st)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_reverse <;> assumption
theorem plaquetteHolonomy_eq {j : ℕ} (X : F.GaugeField j) (b : F.Site j) (μ ν : Fin 4) :
    plaquetteHolonomy X (b, μ, ν) =
      X b μ * X (b + unitStep j μ) ν * (X (b + unitStep j ν) μ)⁻¹ * (X b ν)⁻¹ := by apply _root_.YangMills.Construction.PlaquetteExpansion.plaquetteHolonomy_eq <;> assumption
variable {S : Finset F.Cell} {V : F.GaugeField F.top} {s : ℝ}
theorem norm_plaquette_sub_one_le_of_isCold (hcold : IsCold S F.top s V) {b : F.Cell} {m k : Fin 4}
    (hmk : m < k) (h0 : b ∈ S) (h1 : b + unitStep F.top m ∈ S) (h2 : b + unitStep F.top k ∈ S)
    (h3 : b + unitStep F.top m + unitStep F.top k ∈ S) :
    ‖((V b m * V (b + unitStep F.top m) k * (V (b + unitStep F.top k) m)⁻¹ * (V b k)⁻¹ : UnitQuaternion) :
        ℍ[ℝ]) - 1‖ ≤ s := by
  have hp : (b, m, k) ∈ innerPlaquettes S F.top := by
    simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, true_and]
    refine ⟨mem_sitesOfCells_top.2 h0, hmk, ?_⟩
    intro y hy
    simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact mem_sitesOfCells_top.2 h0
    · exact mem_sitesOfCells_top.2 h1
    · exact mem_sitesOfCells_top.2 h2
    · exact mem_sitesOfCells_top.2 h3
  have := (hcold _ hp).le
  unfold plaquetteDefect at this
  rwa [plaquetteHolonomy_eq] at this
theorem norm_corner_loop_sub_one_le_of_lt (hcold : IsCold S F.top s V) {x : F.Cell} {m k : Fin 4}
    (hmk : m < k) (σ τ : Bool)
    (h0 : x ∈ S) (h1 : x + stepDisplacement F.top (m, σ) ∈ S) (h2 : x + stepDisplacement F.top (k, τ) ∈ S)
    (h3 : x + stepDisplacement F.top (m, σ) + stepDisplacement F.top (k, τ) ∈ S) :
    ‖(((linkValue V x (m, σ))⁻¹ * linkValue V x (k, τ) * linkValue V (x + stepDisplacement F.top (k, τ)) (m, σ) *
        (linkValue V (x + stepDisplacement F.top (m, σ)) (k, τ))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ s := by
  set um := unitStep (F := F) F.top m with hum
  set uk := unitStep (F := F) F.top k with huk
  cases σ <;> cases τ
  · simp only [stepDisplacement_backward, linkValue_backward, ← hum, ← huk] at h1 h2 h3 ⊢
    set b := x + - um + - uk with hb
    have a1 : x - um = b + uk := by rw [hb]; abel
    have a2 : x - uk = b + um := by rw [hb]; abel
    have a3 : x + - uk - um = b := by rw [hb]; abel
    have a4 : x + - um - uk = b := by rw [hb]; abel
    have c1 : b ∈ S := h3
    have c2 : b + um ∈ S := by
      have : b + um = x + - uk := by rw [hb]; abel
      rwa [this]
    have c3 : b + uk ∈ S := by
      have : b + uk = x + - um := by rw [hb]; abel
      rwa [this]
    have c4 : b + um + uk ∈ S := by
      have : b + um + uk = x := by rw [hb]; abel
      rwa [this]
    have hq := norm_plaquette_sub_one_le_of_isCold (V := V) hcold hmk c1 c2 c3 c4
    rw [← hum, ← huk] at hq
    rw [a1, a2, a3, a4]
    set p : UnitQuaternion := V b m * V (b + um) k * (V (b + uk) m)⁻¹ * (V b k)⁻¹ with hp
    have e : (V (b + uk) m)⁻¹⁻¹ * (V (b + um) k)⁻¹ * (V b m)⁻¹ * (V b k)⁻¹⁻¹ =
        (V b k)⁻¹ * p⁻¹ * (V b k)⁻¹⁻¹ := by
      rw [hp]
      group
    rw [e]
    have := norm_coe_conj_sub_one (V b k)⁻¹ p⁻¹
    rw [this, norm_coe_inv_sub_one]
    exact hq
  · simp only [stepDisplacement_backward, stepDisplacement_forward, linkValue_backward, linkValue_forward,
      ← hum, ← huk] at h1 h2 h3 ⊢
    set b := x + - um with hb
    have a1 : x - um = b := by rw [hb]; abel
    have a2 : x + uk - um = b + uk := by rw [hb]; abel
    have c4 : b + um = x := by rw [hb]; abel
    have hq := norm_plaquette_sub_one_le_of_isCold (V := V) hcold hmk h1 (by rw [c4]; exact h0) h3
      (by rw [c4]; exact h2)
    rw [← hum, ← huk, c4] at hq
    rw [a1, a2]
    have e : (V b m)⁻¹⁻¹ * V x k * (V (b + uk) m)⁻¹ * (V b k)⁻¹ =
        V b m * V x k * (V (b + uk) m)⁻¹ * (V b k)⁻¹ := by rw [inv_inv]
    rw [e]
    exact hq
  · simp only [stepDisplacement_backward, stepDisplacement_forward, linkValue_backward, linkValue_forward,
      ← hum, ← huk] at h1 h2 h3 ⊢
    set b := x + - uk with hb
    have a1 : x - uk = b := by rw [hb]; abel
    have a2 : x + um - uk = b + um := by rw [hb]; abel
    have c4 : b + uk = x := by rw [hb]; abel
    have c5 : b + um + uk = x + um := by rw [hb]; abel
    have c6 : b + um = x + um + - uk := by rw [hb]; abel
    have hq := norm_plaquette_sub_one_le_of_isCold (V := V) hcold hmk h2 (by rw [c6]; exact h3)
      (by rw [c4]; exact h0) (by rw [c5]; exact h1)
    rw [← hum, ← huk, c4] at hq
    rw [a1, a2]
    set p : UnitQuaternion := V b m * V (b + um) k * (V x m)⁻¹ * (V b k)⁻¹ with hp
    have e : (V x m)⁻¹ * (V b k)⁻¹ * V b m * (V (b + um) k)⁻¹⁻¹ =
        ((V x m)⁻¹ * (V b k)⁻¹) * p * ((V x m)⁻¹ * (V b k)⁻¹)⁻¹ := by
      rw [hp]
      group
    rw [e, norm_coe_conj_sub_one]
    exact hq
  · simp only [stepDisplacement_forward, linkValue_forward, ← hum, ← huk] at h1 h2 h3 ⊢
    have hq := norm_plaquette_sub_one_le_of_isCold (V := V) hcold hmk h0 h1 h2 h3
    rw [← hum, ← huk] at hq
    set p : UnitQuaternion := V x m * V (x + um) k * (V (x + uk) m)⁻¹ * (V x k)⁻¹ with hp
    have e : (V x m)⁻¹ * V x k * V (x + uk) m * (V (x + um) k)⁻¹ = (V x m)⁻¹ * p⁻¹ * (V x m)⁻¹⁻¹ := by
      rw [hp]
      group
    rw [e, norm_coe_conj_sub_one, norm_coe_inv_sub_one]
    exact hq
theorem norm_corner_loop_sub_one_le (hcold : IsCold S F.top s V) {x : F.Cell} {m k : Fin 4} (hmk : m ≠ k)
    (σ τ : Bool)
    (h0 : x ∈ S) (h1 : x + stepDisplacement F.top (m, σ) ∈ S) (h2 : x + stepDisplacement F.top (k, τ) ∈ S)
    (h3 : x + stepDisplacement F.top (m, σ) + stepDisplacement F.top (k, τ) ∈ S) :
    ‖(((linkValue V x (m, σ))⁻¹ * linkValue V x (k, τ) * linkValue V (x + stepDisplacement F.top (k, τ)) (m, σ) *
        (linkValue V (x + stepDisplacement F.top (m, σ)) (k, τ))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ s := by
  rcases lt_or_gt_of_ne hmk with h | h
  · exact norm_corner_loop_sub_one_le_of_lt hcold h σ τ h0 h1 h2 h3
  · have h3' : x + stepDisplacement F.top (k, τ) + stepDisplacement F.top (m, σ) ∈ S := by
      rwa [add_right_comm]
    have q := norm_corner_loop_sub_one_le_of_lt (V := V) hcold h τ σ h0 h2 h1 h3'
    set A : UnitQuaternion := (linkValue V x (m, σ))⁻¹ * linkValue V x (k, τ) with hA
    set Q' : UnitQuaternion := (linkValue V x (k, τ))⁻¹ * linkValue V x (m, σ) *
      linkValue V (x + stepDisplacement F.top (m, σ)) (k, τ) *
      (linkValue V (x + stepDisplacement F.top (k, τ)) (m, σ))⁻¹ with hQ
    have e : (linkValue V x (m, σ))⁻¹ * linkValue V x (k, τ) *
        linkValue V (x + stepDisplacement F.top (k, τ)) (m, σ) *
        (linkValue V (x + stepDisplacement F.top (m, σ)) (k, τ))⁻¹ = A * Q'⁻¹ * A⁻¹ := by
      rw [hQ, hA]
      group
    rw [e, norm_coe_conj_sub_one, norm_coe_inv_sub_one]
    exact q
end Steps
section Local
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
def orthantStep (S : Finset F.Cell) (z : F.Cell) (i : Fin 4) : PathStep := (i, decide (closedOrthant S z i = 1))
def orthantField (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (a : Lattice4) (i : Fin 4) :
    UnitQuaternion :=
  linkValue V (localCell S z a) (orthantStep S z i)
def patchCorner : Lattice4 := fun _ => 21
def orthantGauge (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (a : Lattice4) : UnitQuaternion :=
  staircaseProduct (orthantField S V z) patchCorner [0, 1, 2, 3] a
theorem stepDisplacement_orthantStep (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (i : Fin 4) :
    stepDisplacement (F := F) F.top (orthantStep S z i) =
      siteOfCoords F.top (fun k => closedOrthant S z k * basisVector i k) := by
  have hk : ∀ k, k ≠ i → closedOrthant S z k * basisVector i k = 0 := by
    intro k hk
    simp [basisVector, hk]
  rcases he i with h | h
  · have e : (fun k => closedOrthant S z k * basisVector i k) = basisVector i := by
      funext k
      by_cases hki : k = i
      · subst hki; simp [h, basisVector]
      · rw [hk k hki]; simp [basisVector, hki]
    rw [e]
    simp [orthantStep, h, stepDisplacement, unitStep_eq]
  · have e : (fun k => closedOrthant S z k * basisVector i k) = - basisVector i := by
      funext k
      by_cases hki : k = i
      · subst hki; simp [h, basisVector]
      · rw [hk k hki]; simp [basisVector, hki]
    rw [e, siteOfCoords_neg]
    simp [orthantStep, h, stepDisplacement, unitStep_eq]
theorem localCell_add_basisVector (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (a : Lattice4)
    (i : Fin 4) :
    localCell S z (a + basisVector i) = localCell S z a + stepDisplacement F.top (orthantStep S z i) := by
  rw [localCell_add, stepDisplacement_orthantStep he]
theorem axisProduct_succ (W : Lattice4 → Fin 4 → UnitQuaternion) (v : Lattice4) (m : Fin 4) (n : ℕ) :
    axisProduct W v m (n + 1) = W v m * axisProduct W (v + basisVector m) m n := by apply _root_.YangMills.Construction.StaircaseGauge.axisProduct_succ <;> assumption
theorem pathHolonomy_replicate_append (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (b : Lattice4) (i : Fin 4) (n : ℕ) (l : List PathStep) :
    pathHolonomy V (localCell S z b) (List.replicate n (orthantStep S z i) ++ l) =
      axisProduct (orthantField S V z) b i n *
        pathHolonomy V (localCell S z (b + (n : ℤ) • basisVector i)) l := by
  induction n generalizing b with
  | zero => simp [axisProduct]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append]
    show linkValue V (localCell S z b) (orthantStep S z i) *
      pathHolonomy V (localCell S z b + stepDisplacement F.top (orthantStep S z i))
        (List.replicate n (orthantStep S z i) ++ l) = _
    rw [← localCell_add_basisVector he, ih, axisProduct_succ, mul_assoc]
    have e : b + basisVector i + (n : ℤ) • basisVector i = b + ((n + 1 : ℕ) : ℤ) • basisVector i := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [e]
    rfl
theorem list_flatMap_congr {α β : Type} {f g : α → List β} {l : List α} (h : ∀ i ∈ l, f i = g i) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a r ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih fun i hi => h i (by simp [hi])]
theorem pathHolonomy_staircase (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (l : List (Fin 4))
    (hl : l.Nodup) (b : Lattice4) (hb : ∀ i, b i ≤ 21) :
    pathHolonomy V (localCell S z b) (l.flatMap fun i => List.replicate (21 - b i).toNat (orthantStep S z i)) =
      staircaseProduct (orthantField S V z) patchCorner l b := by
  induction l generalizing b with
  | nil => rfl
  | cons m r ih =>
    have hm : m ∉ r := (List.nodup_cons.1 hl).1
    simp only [List.flatMap_cons]
    rw [pathHolonomy_replicate_append he]
    have e1 : b + (((21 - b m).toNat : ℕ) : ℤ) • basisVector m = Function.update b m 21 := by
      funext i
      by_cases hi : i = m
      · subst hi
        have := hb i
        simp [basisVector]
        omega
      · simp [basisVector, hi]
    rw [e1]
    have hb' : ∀ i, Function.update b m 21 i ≤ 21 := by
      intro i
      by_cases hi : i = m
      · subst hi; simp
      · simp [hi, hb i]
    have e2 : (r.flatMap fun i => List.replicate (21 - b i).toNat (orthantStep S z i)) =
        r.flatMap fun i => List.replicate (21 - Function.update b m 21 i).toNat (orthantStep S z i) := by
      refine list_flatMap_congr fun i hi => ?_
      have : i ≠ m := fun h => hm (h ▸ hi)
      simp [this]
    rw [e2, ih (List.nodup_cons.1 hl).2 _ hb']
    rfl
theorem cellTransport_eq_orthantGauge (hamb : IsAdmissibleAmbient F)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {a : Lattice4}
    (ha : ∀ i, -11 ≤ a i ∧ a i ≤ 21) :
    GaugeMap.cellTransport S V z (localCell S z a) = orthantGauge S V z a := by
  have hoff : cellDisplacement z (localCell S z a) = fun i => closedOrthant S z i * a i := by
    refine cellDisplacement_add_siteOfCoords hamb z fun i => ?_
    rw [abs_mul, abs_closedOrthant he, one_mul, abs_lt]
    have := ha i
    constructor <;> omega
  have e1 : (fun i => 21 * closedOrthant S z i - cellDisplacement z (localCell S z a) i) =
      fun i => closedOrthant S z i * (21 - a i) := by
    funext i
    rw [hoff]
    ring
  unfold GaugeMap.cellTransport
  rw [e1]
  have e2 : axisPath (fun i => closedOrthant S z i * (21 - a i)) 1 =
      (List.finRange 4).flatMap fun i => List.replicate (21 - a i).toNat (orthantStep S z i) := by
    unfold axisPath
    refine list_flatMap_congr fun i _ => ?_
    simp only [Equiv.Perm.coe_one, id_eq]
    have h2 := ha i
    have hn : (closedOrthant S z i * (21 - a i)).natAbs = (21 - a i).toNat := by
      rcases he i with h | h <;> rw [h] <;> omega
    rw [hn]
    by_cases h0 : a i = 21
    · have ht : (21 - a i).toNat = 0 := by omega
      rw [ht]
      rfl
    · have key : ∀ (P : Prop) [Decidable P], (P ↔ closedOrthant S z i = 1) →
          (i, decide P) = orthantStep S z i := by
        intro P _ hP
        simp only [orthantStep]
        congr 1
        exact decide_eq_decide.2 hP
      have hiff : (0 ≤ closedOrthant S z i * (21 - a i)) ↔ closedOrthant S z i = 1 := by
        rcases he i with h | h <;> rw [h] <;> constructor <;> intro _ <;> omega
      exact congrArg (List.replicate _) (key _ hiff)
  rw [e2]
  have e3 : List.finRange 4 = [0, 1, 2, 3] := by decide
  rw [e3]
  exact pathHolonomy_staircase he _ (by decide) a fun i => (ha i).2
end Local
section Gauge
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell} {s : ℝ}
def orthantBox (S : Finset F.Cell) (z : F.Cell) : Set Lattice4 :=
  {a | (∀ i, -11 ≤ a i ∧ a i ≤ 21) ∧ localCell S z a ∈ S}
def orthantDisplacement (S : Finset F.Cell) (z : F.Cell) (st : PathStep) : Lattice4 :=
  if st.2 = decide (closedOrthant S z st.1 = 1) then basisVector st.1 else - basisVector st.1
theorem localCell_add_orthantDisplacement (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (a : Lattice4) (st : PathStep) :
    localCell S z (a + orthantDisplacement S z st) = localCell S z a + stepDisplacement F.top st := by
  rcases st with ⟨i, b⟩
  by_cases hb : b = decide (closedOrthant S z i = 1)
  · have h1 : orthantDisplacement S z (i, b) = basisVector i := by simp [orthantDisplacement, hb]
    rw [h1, localCell_add_basisVector he, hb]
    rfl
  · have h1 : orthantDisplacement S z (i, b) = - basisVector i := by simp [orthantDisplacement, hb]
    have h2 : (i, b) = ((orthantStep S z i).1, !(orthantStep S z i).2) := by
      have : b = !decide (closedOrthant S z i = 1) := by
        cases b <;> simp_all
      simp [orthantStep, ← this]
    have h3 := localCell_add_basisVector he (a + - basisVector i) i
    have h4 : a + - basisVector i + basisVector i = a := by abel
    rw [h4] at h3
    rw [h1, h2, stepDisplacement_reverse, h3]
    abel
variable (hamb : IsAdmissibleAmbient F) (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
  (hcl : IsOrthantClosedNear S z (closedOrthant S z))
include hamb he hcl in
theorem orthantBox_upward_closed : ∀ a ∈ orthantBox S z, ∀ w : Lattice4,
    (∀ i, a i ≤ w i ∧ w i ≤ patchCorner i) → w ∈ orthantBox S z := by
  rintro a ⟨hb, ha⟩ w hw
  have hw' : ∀ i, -11 ≤ w i ∧ w i ≤ 21 := fun i => by
    have h1 := hw i
    have h2 := hb i
    simp only [patchCorner] at h1
    constructor <;> omega
  refine ⟨hw', ?_⟩
  have e : localCell S z w = localCell S z a + siteOfCoords F.top (fun i => closedOrthant S z i * (w i - a i)) := by
    have := localCell_add (S := S) (z := z) a (w - a)
    simpa using this
  rw [e]
  refine hcl _ ha ?_ _ (fun i => ?_) (fun i => ?_)
  · refine (cellSupDist_add_le hamb z (r := 21) (by norm_num) fun i => ?_).trans (by norm_num)
    rw [abs_mul, abs_closedOrthant he, one_mul, abs_le]
    have := hb i
    constructor <;> omega
  · rw [← mul_assoc, closedOrthant_mul_self he, one_mul]
    have := hw i
    omega
  · rw [abs_mul, abs_closedOrthant he, one_mul, abs_le]
    have h1 := hw' i
    have h2 := hb i
    constructor <;> omega
include he in
theorem norm_orthantField_loop_sub_one_le (hcold : IsCold S F.top s V) (a : Lattice4) (m k : Fin 4) (hmk : m ≠ k)
    (h0 : a ∈ orthantBox S z) (h1 : a + basisVector m ∈ orthantBox S z) (h2 : a + basisVector k ∈ orthantBox S z)
    (h3 : a + basisVector m + basisVector k ∈ orthantBox S z) :
    ‖(((orthantField S V z a m)⁻¹ * orthantField S V z a k * orthantField S V z (a + basisVector k) m *
        (orthantField S V z (a + basisVector m) k)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ s := by
  have c0 := h0.2
  have c1 := h1.2
  have c2 := h2.2
  have c3 := h3.2
  rw [localCell_add_basisVector he] at c1 c2
  rw [localCell_add_basisVector he, localCell_add_basisVector he] at c3
  unfold orthantField
  rw [localCell_add_basisVector he a k, localCell_add_basisVector he a m]
  exact norm_corner_loop_sub_one_le hcold hmk _ _ c0 c1 c2 c3
include hamb he hcl in
theorem norm_gauged_orthantField_sub_one_le (hg : staircaseGaugeStatement) (hs : 0 ≤ s)
    (hcold : IsCold S F.top s V) {a : Lattice4} {k : Fin 4}
    (ha : a ∈ orthantBox S z) (hak : a + basisVector k ∈ orthantBox S z) :
    ‖(((orthantGauge S V z a)⁻¹ * orthantField S V z a k * orthantGauge S V z (a + basisVector k) :
        UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 128 * s := by
  have := hg (orthantField S V z) (orthantBox S z) patchCorner 32 s hs (orthantBox_upward_closed hamb he hcl)
    (fun v hv i => by
      have := hv.1 i
      simp only [patchCorner]
      constructor <;> push_cast <;> omega)
    (fun a m k hmk h0 h1 h2 h3 => norm_orthantField_loop_sub_one_le he hcold a m k hmk h0 h1 h2 h3)
    [0, 1, 2, 3] a k (by decide) (by fin_cases k <;> simp) ha hak
  refine this.trans (le_of_eq ?_)
  simp only [List.length_cons, List.length_nil]
  push_cast
  ring
include hamb he hcl in
theorem norm_gauged_linkValue_sub_one_le (hg : staircaseGaugeStatement) (hs : 0 ≤ s)
    (hcold : IsCold S F.top s V) {a : Lattice4} {st : PathStep}
    (ha : a ∈ orthantBox S z) (hak : a + orthantDisplacement S z st ∈ orthantBox S z) :
    ‖(((orthantGauge S V z a)⁻¹ * linkValue V (localCell S z a) st *
        orthantGauge S V z (a + orthantDisplacement S z st) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 128 * s := by
  rcases st with ⟨i, b⟩
  by_cases hb : b = decide (closedOrthant S z i = 1)
  · have h1 : orthantDisplacement S z (i, b) = basisVector i := by simp [orthantDisplacement, hb]
    rw [h1] at hak ⊢
    have := norm_gauged_orthantField_sub_one_le hamb he hcl hg hs hcold ha hak
    rw [hb]
    exact this
  · have h1 : orthantDisplacement S z (i, b) = - basisVector i := by simp [orthantDisplacement, hb]
    rw [h1] at hak ⊢
    set a' := a + - basisVector i with ha'
    have h4 : a' + basisVector i = a := by rw [ha']; abel
    have hb' : b = !(orthantStep S z i).2 := by
      simp only [orthantStep]
      cases b <;> simp_all
    have h5 := norm_gauged_orthantField_sub_one_le (k := i) hamb he hcl hg hs hcold hak (by rw [h4]; exact ha)
    rw [h4] at h5
    have h6 : linkValue V (localCell S z a) (i, b) = (orthantField S V z a' i)⁻¹ := by
      have := linkValue_reverse V (localCell S z a') (orthantStep S z i)
      rw [← localCell_add_basisVector he, h4] at this
      rw [hb']
      exact this
    rw [h6]
    have e : (orthantGauge S V z a)⁻¹ * (orthantField S V z a' i)⁻¹ * orthantGauge S V z a' =
        ((orthantGauge S V z a')⁻¹ * orthantField S V z a' i * orthantGauge S V z a)⁻¹ := by
      group
    rw [e, norm_coe_inv_sub_one]
    exact h5
def orthantOffset (S : Finset F.Cell) (z : F.Cell) (v u : Lattice4) : Lattice4 :=
  fun i => v i + closedOrthant S z i * u i
include he in
theorem orthantOffset_add_step (v u : Lattice4) (st : PathStep) :
    orthantOffset S z v (u + FlatPairing.stepDisplacement st) =
      orthantOffset S z v u + orthantDisplacement S z st := by
  funext k
  rcases st with ⟨i, b⟩
  by_cases hk : k = i
  · subst hk
    rcases he k with h | h <;> cases b <;>
      simp [orthantOffset, orthantDisplacement, FlatPairing.stepDisplacement, h, basisVector] <;> ring
  · simp [orthantOffset, orthantDisplacement, FlatPairing.stepDisplacement, basisVector, hk]
    split_ifs <;> simp [hk]
include hamb he hcl in
theorem norm_gauged_pathHolonomy_sub_one_le (hg : staircaseGaugeStatement) (hs : 0 ≤ s)
    (hcold : IsCold S F.top s V) (v : Lattice4) {u : Lattice4}
    {l : List PathStep} (hp : AllAlong (fun w => orthantOffset S z v w ∈ orthantBox S z) u l) :
    ‖(((orthantGauge S V z (orthantOffset S z v u))⁻¹ * pathHolonomy V (localCell S z (orthantOffset S z v u)) l *
        orthantGauge S V z (orthantOffset S z v (endpoint u l)) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      l.length * (128 * s) := by
  induction l generalizing u with
  | nil => simp [pathHolonomy, endpoint]
  | cons st r ih =>
    have h0 := hp.1
    have h1 := allAlong_head hp.2
    have e0 := orthantOffset_add_step (S := S) (z := z) he v u st
    have e1 := localCell_add_orthantDisplacement (S := S) (z := z) he (orthantOffset S z v u) st
    rw [e0] at h1
    have i1 := norm_gauged_linkValue_sub_one_le hamb he hcl hg hs hcold h0 h1
    have i2 := ih hp.2
    have e1' : localCell S z (orthantOffset S z v (u + FlatPairing.stepDisplacement st)) =
        localCell S z (orthantOffset S z v u) + stepDisplacement F.top st := by rw [e0]; exact e1
    rw [e1'] at i2
    rw [← e0] at i1
    have e2 : pathHolonomy V (localCell S z (orthantOffset S z v u)) (st :: r) =
        linkValue V (localCell S z (orthantOffset S z v u)) st *
          pathHolonomy V (localCell S z (orthantOffset S z v u) + stepDisplacement F.top st) r := rfl
    rw [e2]
    set A := orthantGauge S V z (orthantOffset S z v u)
    set B := orthantGauge S V z (orthantOffset S z v (u + FlatPairing.stepDisplacement st))
    set Cc := orthantGauge S V z (orthantOffset S z v (endpoint (u + FlatPairing.stepDisplacement st) r))
    set X := linkValue V (localCell S z (orthantOffset S z v u)) st
    set Y := pathHolonomy V (localCell S z (orthantOffset S z v u) + stepDisplacement F.top st) r
    have e3 : A⁻¹ * (X * Y) * Cc = (A⁻¹ * X * B) * (B⁻¹ * Y * Cc) := by group
    show ‖((A⁻¹ * (X * Y) * Cc : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ _
    rw [e3]
    refine (norm_coe_mul_sub_one_le _ _).trans ?_
    have hl : (((st :: r).length : ℕ) : ℝ) = r.length + 1 := by simp
    rw [hl]
    have e4 : ((r.length : ℝ) + 1) * (128 * s) = 128 * s + r.length * (128 * s) := by ring
    rw [e4]
    exact add_le_add i1 i2
end Gauge
section Transport
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell} {s : ℝ}
theorem sign_mul_nonneg_of_between {p u : ℤ} {e : ℤ} (he : e = 1 ∨ e = -1) (hp : 0 ≤ e * p)
    (h1 : min 0 p ≤ u) (h2 : u ≤ max 0 p) :
    0 ≤ e * u := by
  rcases he with rfl | rfl <;> omega
theorem norm_gauged_transport_sub_one_le (hamb : IsAdmissibleAmbient F)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (hcl : IsOrthantClosedNear S z (closedOrthant S z)) (hg : staircaseGaugeStatement) (hs : 0 ≤ s)
    (hcold : IsCold S F.top s V) {v v' : Lattice4} (hv : v ∈ localCellIndex S z) (hv' : v' ∈ localCellIndex S z)
    (hd : supNorm (v' - v) ≤ 3)
    (he' : ∀ i, closedOrthant S (localCell S z v) i = 1 ∨ closedOrthant S (localCell S z v) i = -1)
    (hcl' : IsOrthantClosedNear S (localCell S z v) (closedOrthant S (localCell S z v))) :
    ‖(((orthantGauge S V z v)⁻¹ * cellParallelTransport S V (localCell S z v) (localCell S z v') *
        orthantGauge S V z v' : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 12 * (128 * s) := by
  obtain ⟨hb, hy⟩ := mem_localCellIndex.1 hv
  obtain ⟨hb', hy'⟩ := mem_localCellIndex.1 hv'
  set y := localCell S z v with hydef
  set y' := localCell S z v' with hy'def
  set ε := closedOrthant S y with hε
  set o : Lattice4 := fun i => closedOrthant S z i * (v' i - v i) with ho
  have hdi : ∀ i, |v' i - v i| ≤ 3 := by
    intro i
    have := natAbs_le_supNorm (v' - v) i
    have h2 : ((v' - v) i).natAbs ≤ 3 := this.trans hd
    rw [Int.abs_eq_natAbs]
    simpa using (by exact_mod_cast h2 : (((v' - v) i).natAbs : ℤ) ≤ 3)
  have hoi : ∀ i, |o i| ≤ 3 := by
    intro i
    simp only [ho]
    rw [abs_mul, abs_closedOrthant he, one_mul]
    exact hdi i
  have hyo : y' = y + siteOfCoords F.top o := by
    have := localCell_add (S := S) (z := z) v (v' - v)
    simpa using this
  have hco : cellDisplacement y y' = o := by
    rw [hyo]
    exact cellDisplacement_add_siteOfCoords hamb y fun i => lt_of_le_of_lt (hoi i) (by norm_num)
  set p : Lattice4 := orthantPart ε o with hp
  set r : Lattice4 := o - p with hr
  have hpi : ∀ i, (0 ≤ ε i * o i ∧ p i = o i ∧ r i = 0) ∨ (¬ 0 ≤ ε i * o i ∧ p i = 0 ∧ r i = o i) := by
    intro i
    by_cases h : 0 ≤ ε i * o i
    · left
      simp [hr, hp, orthantPart, h]
    · right
      simp [hr, hp, orthantPart, h]
  have ee : ∀ w : Lattice4, (fun i => closedOrthant S z i * (closedOrthant S z i * w i)) = w := by
    intro w
    funext i
    rw [← mul_assoc, closedOrthant_mul_self he, one_mul]
  have hcell : ∀ u : Lattice4, localCell S z (orthantOffset S z v u) = y + siteOfCoords F.top u := by
    intro u
    have := localCell_add (S := S) (z := z) v (fun i => closedOrthant S z i * u i)
    rw [ee] at this
    exact this
  have hbetw : ∀ u : Lattice4, (∀ i, min 0 (o i) ≤ u i ∧ u i ≤ max 0 (o i)) →
      ∀ i, -11 ≤ orthantOffset S z v u i ∧ orthantOffset S z v u i ≤ 21 := by
    intro u hu i
    have h1 := hu i
    have h2 := hb i
    have h3 := hb' i
    simp only [orthantOffset]
    simp only [ho] at h1
    rcases he i with h | h <;> rw [h] at h1 ⊢ <;> omega
  have hfirst : ∀ u, BetweenOrigin p u → orthantOffset S z v u ∈ orthantBox S z := by
    intro u hu
    have hu2 : ∀ i, min 0 (o i) ≤ u i ∧ u i ≤ max 0 (o i) := by
      intro i
      have h1 := hu i
      rcases hpi i with ⟨_, a, _⟩ | ⟨_, a, _⟩ <;> rw [a] at h1
      · exact h1
      · have : u i = 0 := by simp at h1; omega
        rw [this]
        omega
    refine ⟨hbetw u hu2, ?_⟩
    rw [hcell]
    refine hcl' y hy ?_ u (fun i => ?_) (fun i => ?_)
    · have := cellSupDist_add_le (a := 0) hamb y (r := 0) (by norm_num) (fun i => by simp)
      rw [siteOfCoords_zero, add_zero] at this
      omega
    · rcases hpi i with ⟨a, b, _⟩ | ⟨_, b, _⟩
      · have h1 := hu i
        rw [b] at h1
        exact sign_mul_nonneg_of_between (he' i) a h1.1 h1.2
      · have h1 := hu i
        rw [b] at h1
        have : u i = 0 := by simp at h1; omega
        rw [this]; simp
    · have h1 := hu2 i
      have h2 := abs_le.1 (hoi i)
      rw [abs_le]
      constructor <;> omega
  have hsecond : ∀ u, BetweenOrigin r (u - p) → orthantOffset S z v u ∈ orthantBox S z := by
    intro u hu
    have hu2 : ∀ i, min 0 (o i) ≤ u i ∧ u i ≤ max 0 (o i) := by
      intro i
      have h1 := hu i
      simp only [Pi.sub_apply] at h1
      rcases hpi i with ⟨_, a, b⟩ | ⟨_, a, b⟩ <;> rw [a, b] at h1
      · have : u i = o i := by simp at h1; omega
        rw [this]
        omega
      · simpa using h1
    refine ⟨hbetw u hu2, ?_⟩
    rw [hcell]
    have hyy : y + siteOfCoords F.top u = y' + siteOfCoords F.top (u - o) := by
      rw [hyo, siteOfCoords_sub]
      abel
    rw [hyy]
    refine hcl' y' hy' ?_ (u - o) (fun i => ?_) (fun i => ?_)
    · rw [hyo]
      exact (cellSupDist_add_le hamb y (r := 3) (by norm_num) hoi).trans (by norm_num)
    · simp only [Pi.sub_apply]
      have h1 := hu i
      simp only [Pi.sub_apply] at h1
      rcases hpi i with ⟨_, a, b⟩ | ⟨c, a, b⟩ <;> rw [a, b] at h1
      · have : u i = o i := by simp at h1; omega
        rw [this]; simp
      · have h2 := he' i
        rcases h2 with h2 | h2 <;> rw [h2] at c ⊢ <;> simp at h1 <;> omega
    · simp only [Pi.sub_apply]
      have h1 := hu2 i
      have h2 := abs_le.1 (hoi i)
      rw [abs_le]
      constructor <;> omega
  obtain ⟨l1, l2⟩ := axisPath_spec p 1
  obtain ⟨m1, m2⟩ := axisPath_spec r 1
  have q1 : AllAlong (fun w => orthantOffset S z v w ∈ orthantBox S z) 0 (axisPath p 1) :=
    allAlong_mono hfirst l1
  have q2 : AllAlong (fun w => orthantOffset S z v w ∈ orthantBox S z) (endpoint 0 (axisPath p 1))
      (axisPath r 1) := by
    rw [l2]
    have := allAlong_add (w := p) m1
    rw [zero_add] at this
    exact allAlong_mono hsecond this
  have hq := allAlong_append q1 q2
  have hg' := norm_gauged_pathHolonomy_sub_one_le hamb he hcl hg hs hcold v hq
  have hz0 : orthantOffset S z v 0 = v := by
    funext i
    simp [orthantOffset]
  have hend : endpoint 0 (axisPath p 1 ++ axisPath r 1) = o := by
    rw [endpoint_append, l2]
    have h1 := endpoint_add 0 p (axisPath r 1)
    rw [zero_add, m2] at h1
    rw [h1, hr]
    abel
  have hzo : orthantOffset S z v o = v' := by
    funext i
    simp only [orthantOffset, ho]
    rw [← mul_assoc, closedOrthant_mul_self he, one_mul]
    ring
  rw [hz0, hend, hzo] at hg'
  have hT : cellParallelTransport S V y y' = pathHolonomy V y (axisPath p 1 ++ axisPath r 1) := by
    unfold cellParallelTransport
    rw [hco]
  rw [hT]
  refine hg'.trans ?_
  have hlen : (axisPath p 1 ++ axisPath r 1).length ≤ 12 := by
    rw [List.length_append, length_axisPath, length_axisPath]
    have hk : ∀ i, (p i).natAbs + (r i).natAbs ≤ 3 := by
      intro i
      have h2 := abs_le.1 (hoi i)
      rcases hpi i with ⟨_, a, b⟩ | ⟨_, a, b⟩ <;> rw [a, b] <;> omega
    have k0 := hk ((1 : Equiv.Perm (Fin 4)) 0)
    have k1 := hk ((1 : Equiv.Perm (Fin 4)) 1)
    have k2 := hk ((1 : Equiv.Perm (Fin 4)) 2)
    have k3 := hk ((1 : Equiv.Perm (Fin 4)) 3)
    omega
  have hlen' : (((axisPath p 1 ++ axisPath r 1).length : ℕ) : ℝ) ≤ 12 := by exact_mod_cast hlen
  exact mul_le_mul_of_nonneg_right hlen' (by positivity)
end Transport
theorem patchTransport (hg : staircaseGaugeStatement) : patchTransportStatement := by
  refine ⟨1536, by norm_num, ?_⟩
  intro F m S hodd hamb hm hreg s V hs hcold z hz
  have hm32 : 32 ≤ m := by omega
  obtain ⟨he, hcl⟩ := closedOrthant_spec hreg hm32 z
  have hz0 : localCell S z 0 = z := by
    have : (fun i => closedOrthant S z i * (0 : Lattice4) i) = (0 : Lattice4) := by
      funext i
      simp
    unfold localCell
    rw [this, siteOfCoords_zero, add_zero]
  have hbox0 : ∀ i, -11 ≤ (0 : Lattice4) i ∧ (0 : Lattice4) i ≤ 21 := fun i => by simp
  refine ⟨fun v hv v' hv' hd => ?_, fun i hi => ?_⟩
  · rw [cellTransport_eq_orthantGauge hamb he (mem_localCellIndex.1 hv).1,
      cellTransport_eq_orthantGauge hamb he (mem_localCellIndex.1 hv').1]
    obtain ⟨he', hcl'⟩ := closedOrthant_spec hreg hm32 (localCell S z v)
    refine (norm_gauged_transport_sub_one_le hamb he hcl hg hs hcold hv hv' hd he' hcl').trans (le_of_eq ?_)
    ring
  · have h0 : (0 : Lattice4) ∈ orthantBox S z := ⟨hbox0, by rw [hz0]; exact hz⟩
    set st : PathStep := (i, true) with hst
    have e1 := localCell_add_orthantDisplacement (S := S) (z := z) he 0 st
    rw [hz0, zero_add] at e1
    have e2 : stepDisplacement (F := F) F.top st = unitStep F.top i := stepDisplacement_forward _ _
    rw [e2] at e1
    have hb1 : ∀ k, -11 ≤ orthantDisplacement S z st k ∧ orthantDisplacement S z st k ≤ 21 := by
      intro k
      by_cases hk : k = i
      · subst hk
        simp only [orthantDisplacement, hst]
        split_ifs <;> simp [basisVector]
      · simp only [orthantDisplacement, hst]
        split_ifs <;> simp [basisVector, hk]
    have h1 : (0 : Lattice4) + orthantDisplacement S z st ∈ orthantBox S z := by
      rw [zero_add]
      exact ⟨hb1, by rw [e1]; exact hi⟩
    have hgs := norm_gauged_linkValue_sub_one_le hamb he hcl hg hs hcold h0 h1
    rw [zero_add, hz0] at hgs
    rw [← e1, cellTransport_eq_orthantGauge hamb he hb1]
    have e3 : GaugeMap.cellTransport S V z z = orthantGauge S V z 0 := by
      have := cellTransport_eq_orthantGauge (V := V) hamb he hbox0
      rwa [hz0] at this
    rw [e3]
    have e4 : linkValue V z st = V z i := linkValue_forward _ _ _
    rw [e4] at hgs
    refine hgs.trans ?_
    linarith
end YangMills.Construction.BlockAverages
end
