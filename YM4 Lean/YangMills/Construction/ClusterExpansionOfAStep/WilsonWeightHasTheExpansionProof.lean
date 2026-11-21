import YangMills.Construction.ClusterExpansionOfAStep.BottomOfTheChainIsWilsonsMeasureProof
import YangMills.Construction.ClusterExpansionOfAStep.DerivativesOfTheWilsonEnergy
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslationsProof
import YangMills.Construction.ClusterExpansionOfAStep.IsometriesOfTheEnergy
import YangMills.Construction.ClusterExpansionOfAStep.MatchingClasses
import YangMills.Construction.ClusterExpansionOfAStep.PriceOfTheHotLumps
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open TorusFields TorusLumps
open LumpContours hiding plaquetteEnergy
open BlockAverages hiding unitStep wilsonAction
namespace WilsonExpansion
def pointLabelSpace : LabelSpace where
  Ω := Unit
  μ := Measure.dirac ()
  act := fun _ _ ω => ω
  act_borel := fun _ => measurable_snd
  act_one := fun _ _ => rfl
  act_mul := fun _ _ _ _ => rfl
  act_keeps := fun _ _ => MeasurePreserving.id _
  act_local := fun _ _ _ _ _ _ y hy hy' _ _ h => h y hy hy' (by rw [supDist_self]; omega)
  act_free := fun _ _ _ _ _ => rfl
variable (ℓ : StepParameters) (β : ℝ)
section
open Classical in
def localLumpCore {n : ℕ} [NeZero n] (ℓ : StepParameters) (W : TorusField n) (X : Finset (TorusSite n)) :
    Finset (TorusSite n) :=
  X.filter fun x => torusLumpOf ℓ x ⊆ X ∧ ∃ (x₀ : TorusSite n) (μ ν : Fin 4), μ < ν ∧
    ℓ.threshold ≤ curvature W x₀ μ ν ∧
    (∀ c ∈ plaquetteVertices x₀ μ ν, c ∈ X) ∧ ∃ z ∈ plaquetteVertices x₀ μ ν, torusLumpOf ℓ z = torusLumpOf ℓ x
open Classical in
def localNearPlaquettes {n : ℕ} [NeZero n] (ℓ : StepParameters) (W : TorusField n) (X : Finset (TorusSite n)) :
    Finset (TorusPlaquette n) :=
  (plaquettesIn X).filter fun p => ∃ z ∈ plaquetteVertices p.1 p.2.1 p.2.2,
    z ∈ thickening lumpRange (localLumpCore ℓ W X)
def localEnergy {n : ℕ} [NeZero n] (ℓ : StepParameters) (W : TorusField n) (X : Finset (TorusSite n)) : ℝ :=
  ∑ p ∈ localNearPlaquettes ℓ W X, plaquetteEnergy W p.1 p.2.1 p.2.2
end
def wilsonComponentFactor (n : ℕ) (W : TorusField n) (Y : Finset (TorusSite n)) (_ω : Y → pointLabelSpace.Ω)
    (X : Finset (TorusSite n)) : ℝ :=
  open Classical in
  if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    if X = thickening (2 * clusterRange β) (localLumpCore ℓ W X) then Real.exp (-β * localEnergy ℓ W X) else 0
def wilsonHullWeight (n : ℕ) (W : TorusField n) (Y : Finset (TorusSite n)) (_ω : Y → pointLabelSpace.Ω) : ℝ :=
  open Classical in
  if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    if Y = minimalHull ℓ (clusterRange β) W then wilsonWeight β n W else 0
variable {ℓ β}
section
variable {n : ℕ} [NeZero n]
theorem wilsonWeight_eq (W : TorusField n) :
    wilsonWeight β n W = Real.exp (-β * wilsonAction Finset.univ W) := by
  simp [wilsonWeight, NeZero.ne n]
open Classical in
theorem wilsonComponentFactor_eq (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → pointLabelSpace.Ω)
    (X : Finset (TorusSite n)) :
    wilsonComponentFactor ℓ β n W Y ω X =
      if X = thickening (2 * clusterRange β) (localLumpCore ℓ W X) then Real.exp (-β * localEnergy ℓ W X)
      else 0 := by
  simp [wilsonComponentFactor, NeZero.ne n]
open Classical in
theorem wilsonHullWeight_eq (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → pointLabelSpace.Ω) :
    wilsonHullWeight ℓ β n W Y ω =
      if Y = minimalHull ℓ (clusterRange β) W then wilsonWeight β n W else 0 := by
  simp [wilsonHullWeight, NeZero.ne n]
theorem wilsonWeight_trivialField : wilsonWeight β n (trivialField n) = 1 := by
  simp [wilsonWeight_eq, wilsonAction_trivialField]
end
section
theorem weight_pos (ℓ : StepParameters) (m : ℕ) : 0 < ℓ.weight m := by
  unfold StepParameters.weight
  exact mul_pos (lt_max_of_lt_left one_pos) (Real.exp_pos _)
theorem centered_zero : centered (fun _ _ _ => 0) = fun _ _ _ => 0 := by
  funext n y W
  simp [centered]
theorem mixedDeriv_zero {n k : ℕ} (W : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun _ : TorusField n => (0 : ℝ)) W c X = 0 := by
  unfold mixedDeriv
  have : (fun σ : Fin k → ℝ => (0 : ℝ)) = 0 := rfl
  rw [this]
  simp [iteratedFDeriv_zero_fun]
theorem wilsonWeight_coldExpansion (hfit : ℓ.Admissible) :
    ColdExpansion ℓ 0 β (wilsonWeight β) (fun _ _ _ => 0) where
  positive := fun n _ _ W _ => by
    rw [wilsonWeight_eq]
    exact Real.exp_pos _
  smooth := fun n _ _ y W _ k c X => contDiffAt_const
  gauge := fun _ _ _ _ _ _ _ => rfl
  translation := fun _ _ _ _ _ _ _ => rfl
  form := fun n _ _ W _ => by
    rw [wilsonWeight_eq, wilsonWeight_eq, Real.log_exp, Real.log_exp, wilsonAction_trivialField, centered_zero]
    simp [actionAtLevel]
  decay := fun n _ _ y W _ k c X _ _ _ => by
    rw [mixedDeriv_zero, abs_zero]
    have h1 := weight_pos ℓ (supportDiam y c)
    split_ifs
    · exact div_nonneg hfit.E₃_pos.le h1.le
    · exact div_nonneg hfit.E_pos.le h1.le
  local_density := fun n n' _ _ _ _ y y' W W' m _ _ _ _ _ k h X _ _ _ => by
    rw [centered_zero]
    simp only [mixedDeriv_zero, sub_zero, abs_zero]
    exact div_nonneg hfit.E_pos.le (weight_pos ℓ m).le
  no_curvature_term := fun A A' _ _ => by
    have h0 : ∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
        secondDerivLimit (fun _ _ _ => 0) c c' X X' = 0 := by
      intro c c' X X'
      unfold secondDerivLimit
      simp only [mixedDeriv_zero]
      exact (tendsto_const_nhds).limUnder_eq
    simp only [h0]
    exact hasSum_zero
end
section
variable {ℓ : StepParameters} {n : ℕ} [NeZero n] {r : ℕ}
theorem holonomy_eq_of_agree_on_vertices {W W' : TorusField n} {X : Finset (TorusSite n)}
    (hb : ∀ b : TorusBond n, b.1 ∈ X → b.1 + unitStep n b.2 ∈ X → W b.1 b.2 = W' b.1 b.2) (x : TorusSite n)
    (μ ν : Fin 4) (hc : ∀ z ∈ plaquetteVertices x μ ν, z ∈ X) : holonomy W x μ ν = holonomy W' x μ ν := by
  have c0 : x ∈ X := hc _ (by simp [plaquetteVertices])
  have c1 : x + unitStep n μ ∈ X := hc _ (by simp [plaquetteVertices])
  have c2 : x + unitStep n ν ∈ X := hc _ (by simp [plaquetteVertices])
  have c3 : x + unitStep n μ + unitStep n ν ∈ X := hc _ (by simp [plaquetteVertices])
  have c3' : x + unitStep n ν + unitStep n μ ∈ X := by
    have : x + unitStep n ν + unitStep n μ = x + unitStep n μ + unitStep n ν := by abel
    rwa [this]
  unfold holonomy
  rw [hb (x, μ) c0 c1, hb (x + unitStep n μ, ν) c1 c3, hb (x + unitStep n ν, μ) c2 c3', hb (x, ν) c0 c2]
theorem localLumpCore_eq_of_agree {W W' : TorusField n} {X : Finset (TorusSite n)}
    (hb : ∀ b : TorusBond n, b.1 ∈ X → b.1 + unitStep n b.2 ∈ X → W b.1 b.2 = W' b.1 b.2) :
    localLumpCore ℓ W X = localLumpCore ℓ W' X := by
  classical
  have hcurv : ∀ (x₀ : TorusSite n) (μ ν : Fin 4), (∀ c ∈ plaquetteVertices x₀ μ ν, c ∈ X) →
      curvature W x₀ μ ν = curvature W' x₀ μ ν := by
    intro x₀ μ ν hc
    unfold curvature
    rw [holonomy_eq_of_agree_on_vertices hb x₀ μ ν hc]
  ext x
  simp only [localLumpCore, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2, x₀, μ, ν, h3, h4, h5, h6⟩
    exact ⟨h1, h2, x₀, μ, ν, h3, by rwa [← hcurv x₀ μ ν h5], h5, h6⟩
  · rintro ⟨h1, h2, x₀, μ, ν, h3, h4, h5, h6⟩
    exact ⟨h1, h2, x₀, μ, ν, h3, by rwa [hcurv x₀ μ ν h5], h5, h6⟩
theorem localEnergy_eq_of_agree {W W' : TorusField n} {X : Finset (TorusSite n)}
    (hb : ∀ b : TorusBond n, b.1 ∈ X → b.1 + unitStep n b.2 ∈ X → W b.1 b.2 = W' b.1 b.2) :
    localEnergy ℓ W X = localEnergy ℓ W' X := by
  classical
  have hnear : localNearPlaquettes ℓ W X = localNearPlaquettes ℓ W' X := by
    unfold localNearPlaquettes
    rw [localLumpCore_eq_of_agree hb]
  unfold localEnergy
  rw [← hnear]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hc := (mem_plaquettesIn.mp (Finset.mem_filter.mp hp).1).2
  unfold plaquetteEnergy
  rw [holonomy_eq_of_agree_on_vertices hb p.1 p.2.1 p.2.2 hc]
theorem torusLumpOf_eq_of_mem {x z : TorusSite n} (h : x ∈ torusLumpOf ℓ z) :
    torusLumpOf ℓ x = torusLumpOf ℓ z := by
  classical
  have hk := (Finset.mem_filter.mp h).2
  ext u
  simp only [torusLumpOf, Finset.mem_filter, Finset.mem_univ, true_and, hk]
variable {W : TorusField n} {Y X : Finset (TorusSite n)}
theorem plaquetteVertices_subset_of_hull (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (hr : 2 ^ 16 ≤ r)
    (hY : IsHullState ℓ r W Y) (hX : X ∈ chainComponents r Y) {l : Finset (TorusSite n)}
    (hl : l ∈ torusHotLumps ℓ W) (hlX : l ⊆ X) {z x₀ : TorusSite n} {μ ν : Fin 4} (hzl : z ∈ l)
    (hz : z ∈ plaquetteVertices x₀ μ ν) : ∀ c ∈ plaquetteVertices x₀ μ ν, c ∈ X := by
  intro c hcc
  have hd := supDist_le_four_of_mem_plaquetteVertices (x₀, μ, ν) hcc hz
  exact thickening_subset_of_mem_chainComponents hfit hLn hr hY.1 hX hl hzl (hlX hzl)
    ((mem_thickening _ _ _).mpr ⟨z, hzl, by omega⟩)
theorem localLumpCore_eq_lumpCore (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (hr : 2 ^ 16 ≤ r)
    (hY : IsHullState ℓ r W Y) (hX : X ∈ chainComponents r Y) : localLumpCore ℓ W X = lumpCore ℓ W X := by
  classical
  ext x
  simp only [localLumpCore, Finset.mem_filter]
  constructor
  · rintro ⟨hxX, hsub, x₀, μ, ν, hlt, hs, -, z, hz, hlz⟩
    refine mem_lumpCore.mpr ⟨torusLumpOf ℓ x, ?_, hsub, mem_torusLumpOf_self x⟩
    exact (mem_torusHotLumps_iff ℓ hfit hLn W _).mpr ⟨x₀, μ, ν, hlt, hs, z, hz, hlz.symm⟩
  · intro hx
    obtain ⟨l, hl, hlX, hxl⟩ := mem_lumpCore.mp hx
    obtain ⟨x₀, μ, ν, hlt, hs, z, hz, rfl⟩ := (mem_torusHotLumps_iff ℓ hfit hLn W l).mp hl
    have he := torusLumpOf_eq_of_mem hxl
    refine ⟨hlX hxl, by rwa [he], x₀, μ, ν, hlt, hs, ?_, z, hz, he.symm⟩
    exact plaquetteVertices_subset_of_hull hfit hLn hr hY hX hl hlX (mem_torusLumpOf_self z) hz
theorem localEnergy_eq_componentEnergy (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (hr : 2 ^ 16 ≤ r)
    (hY : IsHullState ℓ r W Y) (hX : X ∈ chainComponents r Y) : localEnergy ℓ W X = componentEnergy ℓ W X := by
  classical
  have hc := localLumpCore_eq_lumpCore hfit hLn hr hY hX
  have hnear : localNearPlaquettes ℓ W X = nearPlaquettes ℓ W X := by
    ext p
    simp only [localNearPlaquettes, nearPlaquettes, Finset.mem_filter, hc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨mem_plaquettesIn.mpr ⟨(mem_plaquettesIn.mp h1).1, fun _ _ => Finset.mem_univ _⟩, h2⟩
    · rintro ⟨h1, z, hzc, hz⟩
      refine ⟨mem_plaquettesIn.mpr ⟨(mem_plaquettesIn.mp h1).1, fun c hcc => ?_⟩, z, hzc, hz⟩
      obtain ⟨x₀, hx₀, hzx⟩ := (mem_thickening _ _ _).mp hz
      obtain ⟨l, hl, hlX, hxl⟩ := mem_lumpCore.mp hx₀
      have hw : lumpRange = 2 ^ 12 := rfl
      have hd := supDist_le_four_of_mem_plaquetteVertices p hcc hzc
      have ht := supDist_triangle c z x₀
      rw [hw] at hzx
      exact thickening_subset_of_mem_chainComponents hfit hLn hr hY.1 hX hl hxl (hlX hxl)
        ((mem_thickening _ _ _).mpr ⟨x₀, hxl, by omega⟩)
  unfold localEnergy componentEnergy
  rw [hnear]
open Classical in
theorem wilsonComponentFactor_of_hull {β : ℝ} (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    (hr : 2 ^ 16 ≤ clusterRange β) (hY : IsHullState ℓ (clusterRange β) W Y)
    (hX : X ∈ chainComponents (clusterRange β) Y) (ω : Y → pointLabelSpace.Ω) :
    wilsonComponentFactor ℓ β n W Y ω X =
      if X = thickening (2 * clusterRange β) (lumpCore ℓ W X) then Real.exp (-β * componentEnergy ℓ W X)
      else 0 := by
  rw [wilsonComponentFactor_eq, localLumpCore_eq_lumpCore hfit hLn hr hY hX,
    localEnergy_eq_componentEnergy hfit hLn hr hY hX]
end
theorem plaquetteOffsets_apply_eq_zero_or_one {μ ν : Fin 4} (hne : μ ≠ ν) {d : Fin 4 → ℤ}
    (hd : d ∈ plaquetteOffsets μ ν) (i : Fin 4) : d i = 0 ∨ d i = 1 := by
  simp only [plaquetteOffsets, List.mem_cons, List.not_mem_nil, or_false] at hd
  have h1 : ∀ k : Fin 4, (Pi.single k 1 : Fin 4 → ℤ) i = 0 ∨ (Pi.single k 1 : Fin 4 → ℤ) i = 1 := by
    intro k
    by_cases hk : i = k
    · subst hk
      simp
    · simp [hk]
  rcases hd with rfl | rfl | rfl | rfl
  · simp
  · exact h1 μ
  · exact h1 ν
  · by_cases h2 : i = μ
    · subst h2
      simp [hne]
    · simp [Pi.single_apply, h2]
      tauto
section
variable {ℓ : StepParameters} {n n' : ℕ} [NeZero n] [NeZero n'] {r : ℕ}
structure LocalMatch (ℓ : StepParameters) (W : TorusField n) (W' : TorusField n') (X : Finset (TorusSite n))
    (X' : Finset (TorusSite n')) (y : TorusSite n) (y' : TorusSite n') (m : ℕ) : Prop where
  admissible : ℓ.Admissible
  side_dvd : ℓ.side ∣ n
  side_dvd' : ℓ.side ∣ n'
  big : 2 ^ 17 < n
  big' : 2 ^ 17 < n'
  box_lt : 2 * m + 2 < n
  box_lt' : 2 * m + 2 < n'
  sameBlock : SameBlockPosition ℓ y y'
  congruent : CongruentInBoxes X X' y y' m
  agree : FieldsAgreeOnSet W W' y y' m X
variable {W : TorusField n} {W' : TorusField n'} {X : Finset (TorusSite n)} {X' : Finset (TorusSite n')}
  {y : TorusSite n} {y' : TorusSite n'} {m : ℕ}
theorem LocalMatch.symm (M : LocalMatch ℓ W W' X X' y y' m) : LocalMatch ℓ W' W X' X y' y m where
  admissible := M.admissible
  side_dvd := M.side_dvd'
  side_dvd' := M.side_dvd
  big := M.big'
  big' := M.big
  box_lt := M.box_lt'
  box_lt' := M.box_lt
  sameBlock := fun i => by
    have h := M.sameBlock i
    have h2 : (ℓ.side : ℤ) ∣ ((y i).cast : ℤ) - ((y' i).cast : ℤ) := Int.dvd_of_emod_eq_zero h
    have h3 := dvd_neg.mpr h2
    rw [neg_sub] at h3
    exact Int.emod_eq_zero_of_dvd h3
  congruent := ⟨M.congruent.2.1, M.congruent.1, fun h hh => (M.congruent.2.2 h hh).symm⟩
  agree := fun b hb h1 h2 => by
    have e1 : (bondFrom y b).1 ∈ X := (M.congruent.2.2 b.1 hb.1).mpr h1
    have e2 : (bondFrom y b).1 + unitStep n b.2 ∈ X := by
      rw [bondFrom_fst_add_unitStep] at h2 ⊢
      exact (M.congruent.2.2 _ hb.2).mpr h2
    exact (M.agree b hb e1 e2).symm
theorem offsetInBox_of_steps {y z : TorusSite n} {a : Fin 4 → ℤ} {m : ℕ} {S : Finset (TorusSite n)}
    (hn : 2 * m + 2 < n) (hS : ∀ s ∈ S, ∃ h, OffsetInBox m h ∧ s = y + siteOfInt h) (ha : OffsetInBox m a)
    (hz : z = y + siteOfInt a) (P : (Fin 4 → ℤ) → Prop)
    (hstep : ∀ e, P e → ∀ i, e i ≠ 0 → P (Function.update e i (e i - Int.sign (e i))))
    (hin : ∀ e, P e → z + siteOfInt e ∈ S) : ∀ e, P e → OffsetInBox m (a + e) := by
  have key : ∀ (N : ℕ) (e : Fin 4 → ℤ), ∑ i, (e i).natAbs = N → P e → OffsetInBox m (a + e) := by
    intro N
    induction N with
    | zero =>
      intro e he _
      have h0 : e = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff.mp he) i (Finset.mem_univ i)
        simpa using this
      simpa [h0] using ha
    | succ N ih =>
      intro e he hP
      have hne : ∃ i, e i ≠ 0 := by
        by_contra hc
        push_neg at hc
        simp [hc] at he
      obtain ⟨i, hi⟩ := hne
      let e' : Fin 4 → ℤ := Function.update e i (e i - Int.sign (e i))
      have hsign : (e i - Int.sign (e i)).natAbs + 1 = (e i).natAbs := by
        rcases lt_or_gt_of_ne hi with h | h
        · rw [Int.sign_eq_neg_one_of_neg h]
          omega
        · rw [Int.sign_eq_one_of_pos h]
          omega
      have hsum : ∑ j, (e' j).natAbs = N := by
        have h1 : ∑ j, (e j).natAbs = (e i).natAbs + ∑ j ∈ Finset.univ.erase i, (e j).natAbs :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
        have h2 : ∑ j, (e' j).natAbs = (e' i).natAbs + ∑ j ∈ Finset.univ.erase i, (e' j).natAbs :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
        have h3 : ∑ j ∈ Finset.univ.erase i, (e' j).natAbs = ∑ j ∈ Finset.univ.erase i, (e j).natAbs :=
          Finset.sum_congr rfl fun j hj => by
            simp [e', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        have h4 : (e' i).natAbs = (e i - Int.sign (e i)).natAbs := by simp [e']
        omega
      have hbox' := ih e' hsum (hstep e hP i hi)
      obtain ⟨h, hh, hs⟩ := hS _ (hin e hP)
      have heq : h = a + e := by
        have h1 : y + siteOfInt (a + e) = y + siteOfInt h := by rw [add_siteOfInt_add, ← hz, hs]
        refine (eq_of_siteOfInt_eq (add_left_cancel h1) fun j => ?_).symm
        have b1 := hh j
        have b2 := hbox' j
        have b3 : |(a + e) j - (a + e') j| ≤ 1 := by
          by_cases hj : j = i
          · subst hj
            simp only [Pi.add_apply, e', Function.update_self]
            rcases lt_or_gt_of_ne hi with h | h
            · rw [Int.sign_eq_neg_one_of_neg h, abs_le]
              omega
            · rw [Int.sign_eq_one_of_pos h, abs_le]
              omega
          · simp [e', Function.update_of_ne hj]
        rw [abs_le] at b1 b2 b3
        rw [abs_lt]
        constructor <;> omega
      rw [← heq]
      exact hh
  exact fun e he => key _ e rfl he
def InOffsetRectangle (e₀ e : Fin 4 → ℤ) : Prop :=
  ∀ i, (0 ≤ e₀ i → 0 ≤ e i ∧ e i ≤ e₀ i) ∧ (e₀ i ≤ 0 → e₀ i ≤ e i ∧ e i ≤ 0)
theorem InOffsetRectangle.step {e₀ e : Fin 4 → ℤ} (h : InOffsetRectangle e₀ e) (i : Fin 4) (hi : e i ≠ 0) :
    InOffsetRectangle e₀ (Function.update e i (e i - Int.sign (e i))) := by
  intro j
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    have h1 := h j
    rcases lt_or_gt_of_ne hi with hn | hn
    · rw [Int.sign_eq_neg_one_of_neg hn]
      omega
    · rw [Int.sign_eq_one_of_pos hn]
      omega
  · simp only [Function.update_of_ne hj]
    exact h j
theorem lumpCorner_add_of_inOffsetRectangle (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (hbig : 2 ^ 17 < n)
    {x : TorusSite n} {e₀ e : Fin 4 → ℤ} (he₀ : ∀ i, |e₀ i| ≤ 2 ^ 15)
    (hk : lumpCorner ℓ (x + siteOfInt e₀) = lumpCorner ℓ x) (he : InOffsetRectangle e₀ e) :
    lumpCorner ℓ (x + siteOfInt e) = lumpCorner ℓ x := by
  have hLpos : 0 < ℓ.side := by have := hfit.L_ge; omega
  have hX : ∀ b : Fin 4 → ℤ, x + siteOfInt b = siteOfInt ((fun i => ((x i).cast : ℤ)) + b) := by
    intro b
    rw [siteOfInt_add, ← eq_siteOfInt_cast x]
  have hx0 : x = siteOfInt fun i => ((x i).cast : ℤ) := eq_siteOfInt_cast x
  have hkey : ∀ b : Fin 4 → ℤ, lumpCorner ℓ (x + siteOfInt b) =
      fun i => (stripStart ℓ.grid (((x i).cast : ℤ) + b i) : ZMod n) := by
    intro b
    rw [hX, lumpCorner_siteOfInt hfit hLn]
    rfl
  have hkey0 : lumpCorner ℓ x = fun i => (stripStart ℓ.grid ((x i).cast : ℤ) : ZMod n) := by
    conv_lhs => rw [hx0]
    exact lumpCorner_siteOfInt hfit hLn _
  rw [hkey, hkey0]
  rw [hkey, hkey0] at hk
  funext i
  set c : ℤ := ((x i).cast : ℤ)
  have h1 := congrFun hk i
  have hD : stripStart ℓ.grid (c + e₀ i) = stripStart ℓ.grid c := by
    refine int_eq_of_zmod_cast_eq h1 ?_
    have s1 := stripStart_near hfit (c + e₀ i)
    have s2 := stripStart_near hfit c
    have hei := he₀ i
    rw [abs_le] at hei
    rw [abs_lt]
    have hbig' : ((2 : ℤ) ^ 17) < n := by exact_mod_cast hbig
    constructor <;> linarith [s1.1, s1.2, s2.1, s2.2, hei.1, hei.2]
  obtain ⟨m1, m2⟩ := mem_of_stripStart_eq hLpos hfit.L_odd ℓ.grid c _ hD
  obtain ⟨m3, m4⟩ := mem_of_stripStart_eq hLpos hfit.L_odd ℓ.grid c c rfl
  have hei := he i
  have hs : stripStart ℓ.grid (c + e i) = stripStart ℓ.grid c := by
    refine stripStart_eq_of_mem hLpos hfit.L_odd ℓ.grid c _ ?_ ?_
    · rcases le_total 0 (e₀ i) with h0 | h0
      · linarith [(hei.1 h0).1]
      · linarith [(hei.2 h0).1]
    · rcases le_total 0 (e₀ i) with h0 | h0
      · linarith [(hei.1 h0).2]
      · linarith [(hei.2 h0).2]
  rw [hs]
theorem LocalMatch.holonomy_eq (M : LocalMatch ℓ W W' X X' y y' m) (a : Fin 4 → ℤ) (μ ν : Fin 4)
    (h : ∀ d ∈ plaquetteOffsets μ ν, OffsetInBox m (a + d) ∧ y + siteOfInt (a + d) ∈ X) :
    holonomy W (y + siteOfInt a) μ ν = holonomy W' (y' + siteOfInt a) μ ν := by
  have d0 := h 0 (by simp [plaquetteOffsets])
  have d1 := h (Pi.single μ 1) (by simp [plaquetteOffsets])
  have d2 := h (Pi.single ν 1) (by simp [plaquetteOffsets])
  have d3 := h (Pi.single μ 1 + Pi.single ν 1) (by simp [plaquetteOffsets])
  rw [add_zero] at d0
  have hv : ∀ (c : Fin 4 → ℤ) (i : Fin 4), OffsetInBox m c → OffsetInBox m (c + Pi.single i 1) →
      y + siteOfInt c ∈ X → y + siteOfInt (c + Pi.single i 1) ∈ X →
      W (y + siteOfInt c) i = W' (y' + siteOfInt c) i := by
    intro c i h1 h2 h3 h4
    refine M.agree (c, i) ⟨h1, h2⟩ h3 ?_
    rw [bondFrom_fst_add_unitStep]
    exact h4
  have a3 : a + (Pi.single μ 1 + Pi.single ν 1) = (a + Pi.single μ 1) + Pi.single ν 1 := by
    rw [add_assoc]
  have a4 : a + (Pi.single μ 1 + Pi.single ν 1) = (a + Pi.single ν 1) + Pi.single μ 1 := by
    rw [add_assoc, add_comm (Pi.single μ 1)]
  have e1 := hv a μ d0.1 d1.1 d0.2 d1.2
  have e2 := hv (a + Pi.single μ 1) ν d1.1 (a3 ▸ d3.1) d1.2 (a3 ▸ d3.2)
  have e3 := hv (a + Pi.single ν 1) μ d2.1 (a4 ▸ d3.1) d2.2 (a4 ▸ d3.2)
  have e4 := hv a ν d0.1 d2.1 d0.2 d2.2
  unfold holonomy
  simp only [unitStep_eq_siteOfInt]
  rw [add_siteOfInt_add, add_siteOfInt_add] at e2 e3
  rw [e1, e2, e3, e4]
theorem LocalMatch.exists_offset_of_vertices (M : LocalMatch ℓ W W' X X' y y' m) {a : Fin 4 → ℤ}
    (ha : OffsetInBox m a) {μ ν : Fin 4} (hne : μ ≠ ν) {x₀ : TorusSite n}
    (hc : ∀ c ∈ plaquetteVertices x₀ μ ν, c ∈ X) {d : Fin 4 → ℤ} (hd : d ∈ plaquetteOffsets μ ν)
    (hz : x₀ + siteOfInt d = y + siteOfInt a) :
    ∃ b, x₀ = y + siteOfInt b ∧ ∀ d' ∈ plaquetteOffsets μ ν, OffsetInBox m (b + d') ∧ y + siteOfInt (b + d') ∈ X := by
  have hall : ∀ d' ∈ plaquetteOffsets μ ν, OffsetInBox m (a - d + d') ∧ y + siteOfInt (a - d + d') ∈ X := by
    intro d' hd'
    have hmem : x₀ + siteOfInt d' ∈ X := hc _ ((mem_plaquetteVertices_iff_offset _ _ _ _).mpr ⟨d', hd', rfl⟩)
    have hx : x₀ + siteOfInt d' = y + siteOfInt (a - d + d') := by
      have e1 : a - d + d' = a + (d' - d) := by abel
      rw [e1, add_siteOfInt_add, ← hz, add_assoc, ← siteOfInt_add]
      congr 2
      abel
    obtain ⟨h, hh, hs⟩ := M.congruent.1 _ hmem
    have heq : h = a - d + d' := by
      have h1 : y + siteOfInt h = y + siteOfInt (a - d + d') := by rw [← hs, hx]
      refine eq_of_siteOfInt_eq (add_left_cancel h1) fun i => ?_
      have b1 := hh i
      have b2 := ha i
      have b3 := plaquetteOffsets_apply_eq_zero_or_one hne hd i
      have b4 := plaquetteOffsets_apply_eq_zero_or_one hne hd' i
      have hs2 := M.box_lt
      rw [abs_le] at b1 b2
      rw [abs_lt]
      simp only [Pi.add_apply, Pi.sub_apply]
      constructor <;> omega
    rw [← heq]
    exact ⟨hh, by rw [← hs]; exact hmem⟩
  refine ⟨a - d, ?_, hall⟩
  have e1 : y + siteOfInt a = y + siteOfInt (a - d) + siteOfInt d := by
    rw [← add_siteOfInt_add]
    simp
  exact add_right_cancel (hz.trans e1)
theorem torusLumpOf_eq_of_lumpCorner_eq {n : ℕ} [NeZero n] {u v : TorusSite n}
    (h : lumpCorner ℓ u = lumpCorner ℓ v) : torusLumpOf ℓ u = torusLumpOf ℓ v := by
  classical
  ext t
  simp only [torusLumpOf, Finset.mem_filter, Finset.mem_univ, true_and, h]
theorem LocalMatch.mapsTo_localLumpCore (M : LocalMatch ℓ W W' X X' y y' m) {a₀ : Fin 4 → ℤ}
    (ha : OffsetInBox m a₀) (hx : y + siteOfInt a₀ ∈ localLumpCore ℓ W X) :
    y' + siteOfInt a₀ ∈ localLumpCore ℓ W' X' := by
  classical
  obtain ⟨hxX, hsub, x, μ, ν, hlt, hs, hcorn, z₀, hz₀, hlz⟩ := Finset.mem_filter.mp hx
  have hkey : lumpCorner ℓ z₀ = lumpCorner ℓ (y + siteOfInt a₀) := by
    have h1 : z₀ ∈ torusLumpOf ℓ (y + siteOfInt a₀) := by rw [← hlz]; exact mem_torusLumpOf_self z₀
    exact (Finset.mem_filter.mp h1).2
  have hbox : ∀ e₀ : Fin 4 → ℤ, (∀ i, |e₀ i| ≤ 2 ^ 15) →
      lumpCorner ℓ (y + siteOfInt a₀ + siteOfInt e₀) = lumpCorner ℓ (y + siteOfInt a₀) →
      OffsetInBox m (a₀ + e₀) ∧ y + siteOfInt a₀ + siteOfInt e₀ ∈ X := by
    intro e₀ he₀ hk
    refine ⟨offsetInBox_of_steps M.box_lt M.congruent.1 ha rfl (InOffsetRectangle e₀)
      (fun e h i hi => h.step i hi)
      (fun e h => hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lumpCorner_add_of_inOffsetRectangle M.admissible M.side_dvd M.big he₀ hk h⟩)) e₀ ?_, ?_⟩
    · intro i
      constructor
      · exact fun h => ⟨h, le_rfl⟩
      · exact fun h => ⟨le_rfl, h⟩
    · exact hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
  have hclose := supDist_lt_of_lumpCorner_eq M.admissible M.side_dvd hkey
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist (y + siteOfInt a₀) z₀
  have hebound : ∀ i, |e i| ≤ 2 ^ 15 := fun i => by
    have h1 := (hb i).trans hclose.le
    rw [abs_le]
    omega
  have hk1 : lumpCorner ℓ (y + siteOfInt a₀ + siteOfInt e) = lumpCorner ℓ (y + siteOfInt a₀) := by
    rw [← he]; exact hkey
  obtain ⟨hbox₁, -⟩ := hbox e hebound hk1
  obtain ⟨d, hd, hzd⟩ := (mem_plaquetteVertices_iff_offset x z₀ μ ν).mp hz₀
  have hzy : x + siteOfInt d = y + siteOfInt (a₀ + e) := by
    rw [← hzd, he, add_siteOfInt_add]
  obtain ⟨b, hxb, hall⟩ := M.exists_offset_of_vertices hbox₁ hlt.ne hcorn hd hzy
  have hplaq : holonomy W x μ ν = holonomy W' (y' + siteOfInt b) μ ν := by
    rw [hxb]
    exact M.holonomy_eq b μ ν hall
  have hs' : ℓ.threshold ≤ curvature W' (y' + siteOfInt b) μ ν := by
    unfold curvature at hs ⊢
    rwa [← hplaq]
  have hbd : b + d = a₀ + e := by
    have h1 : y + siteOfInt (b + d) = y + siteOfInt (a₀ + e) := by rw [add_siteOfInt_add, ← hxb, hzy]
    refine eq_of_siteOfInt_eq (add_left_cancel h1) fun i => ?_
    have b1 := (hall d hd).1 i
    have b2 := hbox₁ i
    have hs2 := M.box_lt
    rw [abs_le] at b1 b2
    rw [abs_lt]
    constructor <;> omega
  have hkeys : lumpCorner ℓ (y + siteOfInt a₀) = lumpCorner ℓ (y + siteOfInt (a₀ + e)) := by
    rw [add_siteOfInt_add]
    exact hk1.symm
  have hk' := lumpCorner_eq_of_sameBlockPosition M.admissible M.side_dvd M.side_dvd' M.big M.sameBlock a₀ e
    hebound hkeys
  refine Finset.mem_filter.mpr ⟨(M.congruent.2.2 a₀ ha).mp hxX, fun z' hz' => ?_, y' + siteOfInt b, μ, ν,
    hlt, hs', fun c hc => ?_, y' + siteOfInt (a₀ + e), ?_, torusLumpOf_eq_of_lumpCorner_eq hk'.symm⟩
  · have hz'k := (Finset.mem_filter.mp hz').2
    have hclose' := supDist_lt_of_lumpCorner_eq M.admissible M.side_dvd' hz'k
    obtain ⟨e', he', hb'⟩ := exists_offset_of_supDist (y' + siteOfInt a₀) z'
    have hebound' : ∀ i, |e' i| ≤ 2 ^ 15 := fun i => by
      have h1 := (hb' i).trans hclose'.le
      rw [abs_le]
      omega
    have hk2 : lumpCorner ℓ (y' + siteOfInt a₀) = lumpCorner ℓ (y' + siteOfInt (a₀ + e')) := by
      rw [add_siteOfInt_add, ← he']
      exact hz'k.symm
    have hk3 := lumpCorner_eq_of_sameBlockPosition M.admissible M.side_dvd' M.side_dvd M.big'
      M.symm.sameBlock a₀ e' hebound' hk2
    have hk4 : lumpCorner ℓ (y + siteOfInt a₀ + siteOfInt e') = lumpCorner ℓ (y + siteOfInt a₀) := by
      rw [← add_siteOfInt_add]
      exact hk3.symm
    obtain ⟨h5, h6⟩ := hbox e' hebound' hk4
    rw [he', ← add_siteOfInt_add]
    rw [← add_siteOfInt_add] at h6
    exact (M.congruent.2.2 _ h5).mp h6
  · obtain ⟨d', hd', rfl⟩ := (mem_plaquetteVertices_iff_offset _ _ _ _).mp hc
    rw [← add_siteOfInt_add]
    exact (M.congruent.2.2 _ (hall d' hd').1).mp (hall d' hd').2
  · refine (mem_plaquetteVertices_iff_offset _ _ _ _).mpr ⟨d, hd, ?_⟩
    rw [← add_siteOfInt_add, hbd]
theorem LocalMatch.eq_thickening_localLumpCore (M : LocalMatch ℓ W W' X X' y y' m) (hr : 2 ^ 16 ≤ r)
    (hX : X = thickening (2 * r) (localLumpCore ℓ W X)) :
    X' = thickening (2 * r) (localLumpCore ℓ W' X') := by
  classical
  have hball : ∀ x ∈ localLumpCore ℓ W X, ∀ e : Fin 4 → ℤ, (∀ i, |e i| ≤ ((2 * r : ℕ) : ℤ)) →
      x + siteOfInt e ∈ X := by
    intro x hx e he
    rw [hX]
    refine (mem_thickening _ _ _).mpr ⟨x, hx, ?_⟩
    rw [supDist_comm]
    refine supDist_add_siteOfInt_le _ _ _ fun i => ?_
    have := he i
    rw [abs_le] at this
    omega
  have hbox : ∀ a₀ : Fin 4 → ℤ, OffsetInBox m a₀ → y + siteOfInt a₀ ∈ localLumpCore ℓ W X →
      ∀ e : Fin 4 → ℤ, (∀ i, |e i| ≤ ((2 * r : ℕ) : ℤ)) → OffsetInBox m (a₀ + e) :=
    fun a₀ ha hx => offsetInBox_add_of_ball_subset M.box_lt M.congruent.1 ha rfl (hball _ hx)
  refine Finset.Subset.antisymm (fun z' hz' => ?_) (fun z' hz' => ?_)
  · obtain ⟨h, hh, rfl⟩ := M.congruent.2.1 z' hz'
    have hzX : y + siteOfInt h ∈ X := (M.congruent.2.2 h hh).mpr hz'
    have hz2 := hzX
    rw [hX] at hz2
    obtain ⟨x₀, hx₀, hd⟩ := (mem_thickening _ _ _).mp hz2
    obtain ⟨a₀, ha₀, rfl⟩ := M.congruent.1 x₀ (Finset.mem_filter.mp hx₀).1
    rw [supDist_comm] at hd
    obtain ⟨e, he, hb⟩ := exists_offset_of_supDist (y + siteOfInt a₀) (y + siteOfInt h)
    have hbe : ∀ i, |e i| ≤ ((2 * r : ℕ) : ℤ) := fun i => by
      have h1 := (hb i).trans hd
      rw [abs_le]
      omega
    have hbx := hbox a₀ ha₀ hx₀ e hbe
    have heq : h = a₀ + e := by
      have h1 : y + siteOfInt h = y + siteOfInt (a₀ + e) := by rw [add_siteOfInt_add]; exact he
      refine eq_of_siteOfInt_eq (add_left_cancel h1) fun i => ?_
      have b1 := hh i
      have b2 := hbx i
      have hn := M.box_lt
      rw [abs_le] at b1 b2
      rw [abs_lt]
      constructor <;> omega
    refine (mem_thickening _ _ _).mpr ⟨y' + siteOfInt a₀, M.mapsTo_localLumpCore ha₀ hx₀, ?_⟩
    rw [supDist_comm, heq, add_siteOfInt_add]
    exact supDist_add_siteOfInt_le _ _ _ fun i => (hb i).trans hd
  · obtain ⟨x', hx', hd⟩ := (mem_thickening _ _ _).mp hz'
    obtain ⟨a₀, ha₀, rfl⟩ := M.congruent.2.1 x' (Finset.mem_filter.mp hx').1
    have hx₀ := M.symm.mapsTo_localLumpCore ha₀ hx'
    rw [supDist_comm] at hd
    obtain ⟨e, he, hb⟩ := exists_offset_of_supDist (y' + siteOfInt a₀) z'
    have hbe : ∀ i, |e i| ≤ ((2 * r : ℕ) : ℤ) := fun i => by
      have h1 := (hb i).trans hd
      rw [abs_le]
      omega
    have h1 := hball _ hx₀ e hbe
    have h2 := hbox a₀ ha₀ hx₀ e hbe
    rw [← add_siteOfInt_add] at h1
    rw [he, ← add_siteOfInt_add]
    exact (M.congruent.2.2 _ h2).mp h1
theorem LocalMatch.exists_mem_localNearPlaquettes (M : LocalMatch ℓ W W' X X' y y' m) (hr : 2 ^ 16 ≤ r)
    (hX : X = thickening (2 * r) (localLumpCore ℓ W X)) {p : TorusPlaquette n}
    (hp : p ∈ localNearPlaquettes ℓ W X) :
    ∃ a, OffsetInBox m a ∧ p.1 = y + siteOfInt a ∧
      (y' + siteOfInt a, p.2.1, p.2.2) ∈ localNearPlaquettes ℓ W' X' ∧
      holonomy W p.1 p.2.1 p.2.2 = holonomy W' (y' + siteOfInt a) p.2.1 p.2.2 := by
  classical
  obtain ⟨x, μ, ν⟩ := p
  obtain ⟨hpl, c, hc, hcw⟩ := Finset.mem_filter.mp hp
  obtain ⟨hlt, hcorn⟩ := mem_plaquettesIn.mp hpl
  simp only at hc hcw hlt hcorn ⊢
  have hxX : x ∈ X := hcorn x (by simp [plaquetteVertices])
  obtain ⟨a, ha, rfl⟩ := M.congruent.1 x hxX
  obtain ⟨b, hxb, hall⟩ := M.exists_offset_of_vertices ha hlt.ne hcorn (d := 0)
    (by simp [plaquetteOffsets]) (by rw [siteOfInt_zero_offset, add_zero])
  have hab : b = a := by
    refine eq_of_siteOfInt_eq (add_left_cancel hxb.symm) fun i => ?_
    have b1 := (hall 0 (by simp [plaquetteOffsets])).1 i
    have b2 := ha i
    have hs2 := M.box_lt
    simp only [add_zero] at b1
    rw [abs_le] at b1 b2
    rw [abs_lt]
    constructor <;> omega
  subst hab
  obtain ⟨x₀, hx₀, hcx⟩ := (mem_thickening _ _ _).mp hcw
  obtain ⟨a₀, ha₀, rfl⟩ := M.congruent.1 x₀ (Finset.mem_filter.mp hx₀).1
  rw [supDist_comm] at hcx
  obtain ⟨e₁, he₁, hb₁⟩ := exists_offset_of_supDist (y + siteOfInt a₀) c
  obtain ⟨d, hd, hcd⟩ := (mem_plaquetteVertices_iff_offset _ c μ ν).mp hc
  have hw : lumpRange = 2 ^ 12 := rfl
  have hball : ∀ e : Fin 4 → ℤ, (∀ i, |e i| ≤ ((2 * r : ℕ) : ℤ)) → y + siteOfInt a₀ + siteOfInt e ∈ X := by
    intro e he
    rw [hX]
    refine (mem_thickening _ _ _).mpr ⟨_, hx₀, ?_⟩
    rw [supDist_comm]
    refine supDist_add_siteOfInt_le _ _ _ fun i => ?_
    have := he i
    rw [abs_le] at this
    omega
  have hbox := offsetInBox_add_of_ball_subset M.box_lt M.congruent.1 ha₀ rfl hball e₁ (fun i => by
    have h1 := (hb₁ i).trans hcx
    rw [hw] at h1
    rw [abs_le]
    omega)
  have hsame : b + d = a₀ + e₁ := by
    have h1 : y + siteOfInt (b + d) = y + siteOfInt (a₀ + e₁) := by
      rw [add_siteOfInt_add, add_siteOfInt_add, ← hcd, he₁]
    refine eq_of_siteOfInt_eq (add_left_cancel h1) fun i => ?_
    have b1 := (hall d hd).1 i
    have b2 := hbox i
    have hs2 := M.box_lt
    rw [abs_le] at b1 b2
    rw [abs_lt]
    constructor <;> omega
  refine ⟨b, ha, rfl, ?_, M.holonomy_eq b μ ν hall⟩
  refine Finset.mem_filter.mpr ⟨mem_plaquettesIn.mpr ⟨hlt, fun c' hc' => ?_⟩, y' + siteOfInt (a₀ + e₁), ?_,
    (mem_thickening _ _ _).mpr ⟨y' + siteOfInt a₀, M.mapsTo_localLumpCore ha₀ hx₀, ?_⟩⟩
  · obtain ⟨d', hd', rfl⟩ := (mem_plaquetteVertices_iff_offset _ _ _ _).mp hc'
    rw [← add_siteOfInt_add]
    exact (M.congruent.2.2 _ (hall d' hd').1).mp (hall d' hd').2
  · refine (mem_plaquetteVertices_iff_offset _ _ _ _).mpr ⟨d, hd, ?_⟩
    rw [← add_siteOfInt_add, hsame]
  · rw [supDist_comm, add_siteOfInt_add]
    exact supDist_add_siteOfInt_le _ _ _ fun i => (hb₁ i).trans hcx
open Classical in
theorem LocalMatch.localEnergy_eq (M : LocalMatch ℓ W W' X X' y y' m) (hr : 2 ^ 16 ≤ r)
    (hX : X = thickening (2 * r) (localLumpCore ℓ W X))
    (hX' : X' = thickening (2 * r) (localLumpCore ℓ W' X')) :
    localEnergy ℓ W X = localEnergy ℓ W' X' := by
  let A : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m
  have hA : ∀ a, a ∈ A ↔ OffsetInBox m a := by
    intro a
    simp only [A, Fintype.mem_piFinset, Finset.mem_Icc, OffsetInBox, abs_le]
  let Q : Finset ((Fin 4 → ℤ) × Fin 4 × Fin 4) := (A ×ˢ Finset.univ).filter fun q =>
    (y + siteOfInt q.1, q.2.1, q.2.2) ∈ localNearPlaquettes ℓ W X
  let f : ((Fin 4 → ℤ) × Fin 4 × Fin 4) → TorusPlaquette n := fun q => (y + siteOfInt q.1, q.2.1, q.2.2)
  let f' : ((Fin 4 → ℤ) × Fin 4 × Fin 4) → TorusPlaquette n' := fun q => (y' + siteOfInt q.1, q.2.1, q.2.2)
  have hinj : ∀ {k : ℕ} [NeZero k] (u : TorusSite k), 2 * m + 2 < k → ∀ a b : Fin 4 → ℤ,
      OffsetInBox m a → OffsetInBox m b → u + siteOfInt a = u + siteOfInt b → a = b := by
    intro k _ u hk a b ha hb h
    refine eq_of_siteOfInt_eq (add_left_cancel h) fun i => ?_
    have b1 := ha i
    have b2 := hb i
    rw [abs_le] at b1 b2
    rw [abs_lt]
    constructor <;> omega
  have himg : localNearPlaquettes ℓ W X = Q.image f := by
    ext p
    simp only [Finset.mem_image]
    constructor
    · intro hp
      obtain ⟨a, ha, hp1, -, -⟩ := M.exists_mem_localNearPlaquettes hr hX hp
      refine ⟨(a, p.2.1, p.2.2), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨(hA a).mpr ha, Finset.mem_univ _⟩, ?_⟩, ?_⟩
      · simp only
        rw [← hp1]
        exact hp
      · obtain ⟨x, μ, ν⟩ := p
        simp only [f]
        rw [← hp1]
    · rintro ⟨q, hq, rfl⟩
      exact (Finset.mem_filter.mp hq).2
  have hback : ∀ a μ ν, OffsetInBox m a → (y + siteOfInt a, μ, ν) ∈ localNearPlaquettes ℓ W X →
      (y' + siteOfInt a, μ, ν) ∈ localNearPlaquettes ℓ W' X' ∧
        holonomy W (y + siteOfInt a) μ ν = holonomy W' (y' + siteOfInt a) μ ν := by
    intro a μ ν ha hp
    obtain ⟨a', ha', h1, h2, h3⟩ := M.exists_mem_localNearPlaquettes hr hX hp
    have : a = a' := hinj y M.box_lt a a' ha ha' h1
    subst this
    exact ⟨h2, h3⟩
  have himg' : localNearPlaquettes ℓ W' X' = Q.image f' := by
    ext p
    simp only [Finset.mem_image]
    constructor
    · intro hp
      obtain ⟨a, ha, hp1, hp2, -⟩ := M.symm.exists_mem_localNearPlaquettes hr hX' hp
      refine ⟨(a, p.2.1, p.2.2), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨(hA a).mpr ha, Finset.mem_univ _⟩, hp2⟩, ?_⟩
      obtain ⟨x, μ, ν⟩ := p
      simp only [f']
      rw [← hp1]
    · rintro ⟨⟨a, μ, ν⟩, hq, rfl⟩
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq
      exact (hback a μ ν ((hA a).mp (Finset.mem_product.mp h1).1) h2).1
  have hinjf : Set.InjOn f Q := by
    rintro ⟨a, μ, ν⟩ hq ⟨b, μ', ν'⟩ hq' he
    have h1 := (Finset.mem_filter.mp hq).1
    have h2 := (Finset.mem_filter.mp hq').1
    simp only [f, Prod.mk.injEq] at he
    rw [hinj y M.box_lt a b ((hA a).mp (Finset.mem_product.mp h1).1)
      ((hA b).mp (Finset.mem_product.mp h2).1) he.1, he.2.1, he.2.2]
  have hinjf' : Set.InjOn f' Q := by
    rintro ⟨a, μ, ν⟩ hq ⟨b, μ', ν'⟩ hq' he
    have h1 := (Finset.mem_filter.mp hq).1
    have h2 := (Finset.mem_filter.mp hq').1
    simp only [f', Prod.mk.injEq] at he
    rw [hinj y' M.box_lt' a b ((hA a).mp (Finset.mem_product.mp h1).1)
      ((hA b).mp (Finset.mem_product.mp h2).1) he.1, he.2.1, he.2.2]
  unfold localEnergy
  rw [himg, himg', Finset.sum_image hinjf, Finset.sum_image hinjf']
  refine Finset.sum_congr rfl ?_
  rintro ⟨a, μ, ν⟩ hq
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq
  have := (hback a μ ν ((hA a).mp (Finset.mem_product.mp h1).1) h2).2
  simp only [f, f', plaquetteEnergy]
  rw [this]
end
section
variable {n : ℕ} [NeZero n]
theorem torusHotSites_congr {W W' : TorusField n} (h : torusHotLumps ℓ W = torusHotLumps ℓ W') :
    torusHotSites ℓ W = torusHotSites ℓ W' := by
  unfold torusHotSites
  rw [h]
theorem minimalHull_congr {r : ℕ} {W W' : TorusField n} (h : torusHotLumps ℓ W = torusHotLumps ℓ W') :
    minimalHull ℓ r W = minimalHull ℓ r W' := by
  unfold minimalHull
  rw [torusHotSites_congr h]
theorem isHullState_congr {r : ℕ} {W W' : TorusField n} {Y : Finset (TorusSite n)}
    (h : torusHotLumps ℓ W = torusHotLumps ℓ W') : IsHullState ℓ r W Y ↔ IsHullState ℓ r W' Y := by
  unfold IsHullState
  rw [torusHotSites_congr h, h]
theorem torusHotLumps_gaugeTransform (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (g : TorusSite n → UnitQuaternion)
    (W : TorusField n) : torusHotLumps ℓ (gaugeTransform g W) = torusHotLumps ℓ W := by
  classical
  refine torusHotLumps_eq_of_hotPlaquettes_eq hfit hLn ?_
  ext p
  simp [hotPlaquettes, curvature_gaugeTransform]
theorem add_mem_plaquetteVertices_add (x u : TorusSite n) (μ ν : Fin 4) {z : TorusSite n}
    (hz : z ∈ plaquetteVertices x μ ν) : z + u ∈ plaquetteVertices (x + u) μ ν := by
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (by abel))
  · exact Or.inr (Or.inr (Or.inl (by abel)))
  · exact Or.inr (Or.inr (Or.inr (by abel)))
theorem add_mem_torusHotSites_of_translate (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (W : TorusField n)
    (v : Fin 4 → ℤ) {a : TorusSite n}
    (ha : a ∈ torusHotSites ℓ (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W)) :
    a + siteOfInt (fun i => (ℓ.side : ℤ) * v i) ∈ torusHotSites ℓ W := by
  classical
  set u : TorusSite n := siteOfInt fun i => (ℓ.side : ℤ) * v i with hu
  obtain ⟨l, hl, hal⟩ := mem_torusHotSites_iff.mp ha
  obtain ⟨x, μ, ν, hlt, hs, z, hz, rfl⟩ := (mem_torusHotLumps_iff ℓ hfit hLn _ l).mp hl
  rw [curvature_translate] at hs
  refine mem_torusHotSites_iff.mpr ⟨torusLumpOf ℓ (z + u), (mem_torusHotLumps_iff ℓ hfit hLn W _).mpr
    ⟨x + u, μ, ν, hlt, hs, z + u, add_mem_plaquetteVertices_add x u μ ν hz, rfl⟩, ?_⟩
  have hk := (Finset.mem_filter.mp hal).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [hu, lumpCorner_add_side_mul hfit hLn, lumpCorner_add_side_mul hfit hLn, hk]
theorem translate_neg_translate (u : TorusSite n) (W : TorusField n) :
    TorusFields.translate (-u) (TorusFields.translate u W) = W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translate_neg_translate <;> assumption
theorem siteOfInt_block_neg (ℓ : StepParameters) (v : Fin 4 → ℤ) :
    (siteOfInt (fun i => (ℓ.side : ℤ) * (-v) i) : TorusSite n) = -siteOfInt fun i => (ℓ.side : ℤ) * v i := by
  funext i
  simp [siteOfInt]
theorem mem_torusHotSites_translate_iff (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (W : TorusField n)
    (v : Fin 4 → ℤ) (a : TorusSite n) :
    a ∈ torusHotSites ℓ (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W) ↔
      a + siteOfInt (fun i => (ℓ.side : ℤ) * v i) ∈ torusHotSites ℓ W := by
  refine ⟨add_mem_torusHotSites_of_translate hfit hLn W v, fun h => ?_⟩
  have h1 := add_mem_torusHotSites_of_translate hfit hLn
    (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W) (-v)
    (a := a + siteOfInt (fun i => (ℓ.side : ℤ) * v i))
  rw [siteOfInt_block_neg, translate_neg_translate] at h1
  simpa using h1 h
theorem mem_minimalHull_translate_iff (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (r : ℕ) (W : TorusField n)
    (v : Fin 4 → ℤ) (a : TorusSite n) :
    a ∈ minimalHull ℓ r (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W) ↔
      a + siteOfInt (fun i => (ℓ.side : ℤ) * v i) ∈ minimalHull ℓ r W := by
  set u : TorusSite n := siteOfInt fun i => (ℓ.side : ℤ) * v i with hu
  unfold minimalHull
  rw [mem_thickening, mem_thickening]
  constructor
  · rintro ⟨b, hb, hab⟩
    exact ⟨b + u, (mem_torusHotSites_translate_iff hfit hLn W v b).mp hb, by rw [supDist_add_right]; exact hab⟩
  · rintro ⟨b, hb, hab⟩
    refine ⟨b - u, (mem_torusHotSites_translate_iff hfit hLn W v _).mpr (by simpa [hu] using hb), ?_⟩
    rw [← supDist_add_right a (b - u) u]
    simpa using hab
theorem wilsonAction_translate (W : TorusField n) (v : Fin 4 → ℤ) :
    wilsonAction Finset.univ (TorusFields.translate (siteOfInt v) W) = wilsonAction Finset.univ W := by
  let g : TorusIsometry := ⟨1, fun _ => 1, -v, fun _ => Or.inl rfl⟩
  refine wilsonAction_of_transports (g := g) ?_
  intro x k
  have hs : g.axisSign (g.axisPerm.symm k) = 1 := rfl
  rw [if_pos hs]
  have hd : g.axisPerm.symm k = k := rfl
  rw [hd]
  have hx : g.mapSite x + siteOfInt v = x := by
    funext i
    simp [g, TorusIsometry.mapSite, siteOfInt]
  simp [TorusFields.translate, hx]
theorem exp_wilsonAction_eq_mul_prod (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (hr : 2 ^ 16 ≤ clusterRange β)
    (W : TorusField n) :
    Real.exp (-β * wilsonAction Finset.univ W) =
      Real.exp (-β * wilsonAction (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W) *
        ∏ X ∈ chainComponents (clusterRange β) (minimalHull ℓ (clusterRange β) W),
          Real.exp (-β * componentEnergy ℓ W X) := by
  rw [wilsonAction_univ_eq_add_sum_componentEnergy (Y := minimalHull ℓ (clusterRange β) W) hfit hLn hr subset_rfl,
    ← Real.exp_sum, ← Real.exp_add]
  congr 1
  rw [mul_add, Finset.mul_sum]
open Classical in
theorem wilsonHullWeight_form (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (hr : 2 ^ 16 ≤ clusterRange β)
    (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → pointLabelSpace.Ω)
    (hY : IsHullState ℓ (clusterRange β) W Y) :
    wilsonHullWeight ℓ β n W Y ω = wilsonWeight β n (trivialField n) *
      Real.exp (-β * actionAtLevel ℓ.coupling ℓ.side 0
          (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W +
        ∑ y : TorusSite n, (0 : ℝ)) *
      ∏ X ∈ chainComponents (clusterRange β) Y, wilsonComponentFactor ℓ β n W Y ω X := by
  have hprod : ∏ X ∈ chainComponents (clusterRange β) Y, wilsonComponentFactor ℓ β n W Y ω X =
      ∏ X ∈ chainComponents (clusterRange β) Y,
        if X = thickening (2 * clusterRange β) (lumpCore ℓ W X) then Real.exp (-β * componentEnergy ℓ W X)
        else 0 :=
    Finset.prod_congr rfl fun X hX => wilsonComponentFactor_of_hull hfit hLn hr hY hX ω
  rw [hprod]
  simp only [wilsonWeight_trivialField, Finset.sum_const_zero, add_zero, one_mul, wilsonHullWeight_eq,
    actionAtLevel]
  by_cases hYe : Y = minimalHull ℓ (clusterRange β) W
  · rw [if_pos hYe, wilsonWeight_eq, exp_wilsonAction_eq_mul_prod hfit hLn hr W, ← hYe]
    congr 1
    refine Finset.prod_congr rfl fun X hX => ?_
    rw [hYe] at hX
    rw [if_pos (eq_thickening_lumpCore_of_mem_chainComponents hfit hLn hr hX)]
  · rw [if_neg hYe]
    have hex : ∃ X ∈ chainComponents (clusterRange β) Y, X ≠ thickening (2 * clusterRange β) (lumpCore ℓ W X) := by
      by_contra hc
      push_neg at hc
      exact hYe (eq_minimalHull_of_forall_eq_thickening hY hc)
    obtain ⟨X, hX, hne⟩ := hex
    rw [Finset.prod_eq_zero hX (if_neg hne), mul_zero]
end
section
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
theorem measurable_of_eqOn_hotPlaquettes_fibres {F : TorusField n → ℝ}
    (hF : ∀ W₀ : TorusField n, ∃ g : TorusField n → ℝ, Measurable g ∧
      ∀ W, hotPlaquettes ℓ W = hotPlaquettes ℓ W₀ → F W = g W) :
    Measurable F := by
  classical
  intro s hs
  have h2 : F ⁻¹' s = ⋃ A ∈ {A : Finset (TorusPlaquette n) | ∃ W₀ : TorusField n, hotPlaquettes ℓ W₀ = A},
      ({W | hotPlaquettes ℓ W = A} ∩ F ⁻¹' s) := by
    ext W
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
    exact ⟨fun h => ⟨_, ⟨W, rfl⟩, rfl, h⟩, fun ⟨_, _, _, h⟩ => h⟩
  rw [h2]
  refine MeasurableSet.biUnion (Set.to_countable _) ?_
  rintro A ⟨W₀, rfl⟩
  obtain ⟨g, hg, hgF⟩ := hF W₀
  have h3 : {W | hotPlaquettes ℓ W = hotPlaquettes ℓ W₀} ∩ F ⁻¹' s =
      {W | hotPlaquettes ℓ W = hotPlaquettes ℓ W₀} ∩ g ⁻¹' s := by
    ext W
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
    exact and_congr_right fun h => by rw [hgF W h]
  rw [h3]
  exact (measurableSet_hotPlaquettes_eq _).inter (hg hs)
theorem localLumpCore_congr {W W' : TorusField n} (h : hotPlaquettes ℓ W = hotPlaquettes ℓ W')
    (X : Finset (TorusSite n)) : localLumpCore ℓ W X = localLumpCore ℓ W' X := by
  classical
  have hiff : ∀ (x : TorusSite n) (μ ν : Fin 4), μ < ν →
      (ℓ.threshold ≤ curvature W x μ ν ↔ ℓ.threshold ≤ curvature W' x μ ν) := by
    intro x μ ν hlt
    have h1 : (x, μ, ν) ∈ hotPlaquettes ℓ W ↔ (x, μ, ν) ∈ hotPlaquettes ℓ W' := by rw [h]
    simpa [hotPlaquettes, hlt] using h1
  ext x
  simp only [localLumpCore, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2, x₀, μ, ν, h3, h4, h5⟩
    exact ⟨h1, h2, x₀, μ, ν, h3, (hiff x₀ μ ν h3).mp h4, h5⟩
  · rintro ⟨h1, h2, x₀, μ, ν, h3, h4, h5⟩
    exact ⟨h1, h2, x₀, μ, ν, h3, (hiff x₀ μ ν h3).mpr h4, h5⟩
theorem localNearPlaquettes_congr {W W' : TorusField n} (h : hotPlaquettes ℓ W = hotPlaquettes ℓ W')
    (X : Finset (TorusSite n)) : localNearPlaquettes ℓ W X = localNearPlaquettes ℓ W' X := by
  unfold localNearPlaquettes
  rw [localLumpCore_congr h]
end
section
theorem clusterRange_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : clusterRange x ≤ clusterRange y :=
  Nat.ceil_mono (Real.rpow_le_rpow hx hxy (by norm_num))
theorem measurable_wilsonWeight {n : ℕ} [NeZero n] : Measurable (wilsonWeight β n) := by apply _root_.YangMills.SharedProofs.p419 <;> assumption
instance isProbabilityMeasure_pointLabelSpace : IsProbabilityMeasure pointLabelSpace.μ := by
  show IsProbabilityMeasure (Measure.dirac ())
  infer_instance
theorem wilsonWeight_hullExpansion (hfit : ℓ.Admissible) (hr : 2 ^ 16 ≤ clusterRange β) (hβ : 1 ≤ β) (C : ℝ)
    (hCd : C ≤ ℓ.derivBound) (hone : 1 ≤ ℓ.derivBound)
    (hD : ∀ (n : ℕ) [NeZero n] (W : TorusField n), ContDiffThreeAt (wilsonAction Finset.univ) W ∧
      ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
        |mixedDeriv (wilsonAction Finset.univ) W c X| ≤ C) :
    HullExpansion ℓ 0 β (wilsonWeight β) (fun _ _ _ => 0) pointLabelSpace (wilsonHullWeight ℓ β)
      (wilsonComponentFactor ℓ β) (fun _ _ _ _ _ => 0) where
  nonneg := fun n _ _ W Y ω _ => by
    rw [wilsonHullWeight_eq]
    split_ifs
    · rw [wilsonWeight_eq]
      exact (Real.exp_pos _).le
    · exact le_rfl
  borel := fun n _ hs Y => by
    classical
    refine ⟨?_, fun X => ?_, fun y => ?_⟩
    · have hF : Measurable fun W : TorusField n => if IsHullState ℓ (clusterRange β) W Y then
          (if Y = minimalHull ℓ (clusterRange β) W then wilsonWeight β n W else 0) else 0 := by
        refine measurable_of_eqOn_torusHotLumps_fibres hfit hs.1 fun W₀ => ⟨fun W =>
          if IsHullState ℓ (clusterRange β) W₀ Y then
            (if Y = minimalHull ℓ (clusterRange β) W₀ then wilsonWeight β n W else 0) else 0, ?_, fun W hW => ?_⟩
        · by_cases h1 : IsHullState ℓ (clusterRange β) W₀ Y
          · by_cases h2 : Y = minimalHull ℓ (clusterRange β) W₀
            · simp only [h1, if_true, if_pos h2]
              exact measurable_wilsonWeight
            · simp only [h1, if_true, h2, if_false]
              exact measurable_const
          · simp only [h1, if_false]
            exact measurable_const
        · simp only [isHullState_congr hW, minimalHull_congr hW]
      convert hF.comp measurable_fst using 2 with p
      simp only [wilsonHullWeight_eq, Function.comp]
    · have hF : Measurable fun W : TorusField n =>
          if X = thickening (2 * clusterRange β) (localLumpCore ℓ W X) then Real.exp (-β * localEnergy ℓ W X)
          else 0 := by
        refine measurable_of_eqOn_hotPlaquettes_fibres (ℓ := ℓ) fun W₀ => ⟨fun W =>
          if X = thickening (2 * clusterRange β) (localLumpCore ℓ W₀ X) then
            Real.exp (-β * ∑ p ∈ localNearPlaquettes ℓ W₀ X, plaquetteEnergy W p.1 p.2.1 p.2.2) else 0,
          ?_, fun W hW => ?_⟩
        · by_cases h2 : X = thickening (2 * clusterRange β) (localLumpCore ℓ W₀ X)
          · simp only [if_pos h2]
            have hc : Continuous fun W : TorusField n =>
                Real.exp (-β * ∑ p ∈ localNearPlaquettes ℓ W₀ X, plaquetteEnergy W p.1 p.2.1 p.2.2) :=
              Real.continuous_exp.comp (continuous_const.mul
                (continuous_finset_sum _ fun p _ => continuous_plaquetteEnergy p.1 p.2.1 p.2.2))
            exact hc.measurable
          · simp only [if_neg h2]
            exact measurable_const
        · simp only [localLumpCore_congr hW, localEnergy, localNearPlaquettes_congr hW]
      convert hF.comp measurable_fst using 2 with p
      simp only [wilsonComponentFactor_eq, Function.comp]
    · simp only [ite_self]
      exact measurable_const
  sum := fun n _ hs W => by
    classical
    have hconst : ∀ Y : Finset (TorusSite n),
        ∫⁻ ω, ENNReal.ofReal (wilsonHullWeight ℓ β n W Y ω) ∂(Measure.pi fun _ : Y => pointLabelSpace.μ) =
          ENNReal.ofReal (if Y = minimalHull ℓ (clusterRange β) W then wilsonWeight β n W else 0) := by
      intro Y
      simp only [wilsonHullWeight_eq, lintegral_const, measure_univ, mul_one]
    simp only [hconst]
    rw [Finset.sum_eq_single (minimalHull ℓ (clusterRange β) W)]
    · simp
    · intro Y _ hne
      simp [hne]
    · intro hnot
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, minimalHull_isHullState⟩) hnot
  gauge := fun n _ hs W Y ω g hY => by
    have hg := torusHotLumps_gaugeTransform hfit hs.1 g W
    simp only [wilsonHullWeight_eq, minimalHull_congr hg, wilsonWeight_eq, wilsonAction_gaugeTransform]
  translation := fun n _ hs W Y ω u hu hY => by
    classical
    obtain ⟨v, rfl⟩ := hu
    simp only [wilsonHullWeight_eq]
    have hset : translateSet (siteOfInt fun i => (ℓ.side : ℤ) * v i) Y =
        minimalHull ℓ (clusterRange β) (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W) ↔
        Y = minimalHull ℓ (clusterRange β) W := by
      constructor
      · intro h
        ext a
        have h1 : a - siteOfInt (fun i => (ℓ.side : ℤ) * v i) ∈
            translateSet (siteOfInt fun i => (ℓ.side : ℤ) * v i) Y ↔
            a - siteOfInt (fun i => (ℓ.side : ℤ) * v i) ∈
              minimalHull ℓ (clusterRange β) (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W) := by
          rw [h]
        rw [mem_minimalHull_translate_iff hfit hs.1] at h1
        simpa [translateSet] using h1
      · intro h
        ext a
        rw [mem_minimalHull_translate_iff hfit hs.1, ← h]
        simp [translateSet]
    have hw : wilsonWeight β n (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W) = wilsonWeight β n W := by
      simp only [wilsonWeight_eq, wilsonAction_translate]
    simp only [hset, hw]
  form := fun n _ hs W Y ω hY => wilsonHullWeight_form hfit hs.1 hr W Y ω hY
  factor_nonneg := fun n _ _ W Y ω X => by
    rw [wilsonComponentFactor_eq]
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  one_rule := fun n n' _ _ hs hs' W W' Y Y' ω ω' X X' y y' m h1 h2 _ _ hb hbox hf _ => by
    classical
    have hbig : ∀ k : ℕ, IsBlockTorusSide ℓ k → 2 ^ 17 < k := by
      intro k hk
      have h3 : 2 ^ 16 * 4096 ≤ ℓ.side * ℓ.n₀ := Nat.mul_le_mul hfit.L_ge hfit.n₀_ge
      have h4 := hk.2
      omega
    have M : LocalMatch ℓ W W' X X' y y' m :=
      { admissible := hfit, side_dvd := hs.1, side_dvd' := hs'.1, big := hbig n hs, big' := hbig n' hs',
        box_lt := h1, box_lt' := h2, sameBlock := hb, congruent := hbox, agree := hf }
    rw [wilsonComponentFactor_eq, wilsonComponentFactor_eq]
    by_cases hc : X = thickening (2 * clusterRange β) (localLumpCore ℓ W X)
    · have hc' := M.eq_thickening_localLumpCore hr hc
      rw [if_pos hc, if_pos hc', M.localEnergy_eq hr hc hc']
    · rw [if_neg hc, if_neg fun h => hc (M.symm.eq_thickening_localLumpCore hr h)]
  reads_class := fun n _ hs W W' Y Y' ω ω' X _ _ hb _ => by
    classical
    rw [wilsonComponentFactor_eq, wilsonComponentFactor_eq, localLumpCore_eq_of_agree hb,
      localEnergy_eq_of_agree hb]
  empty := fun n _ _ W ω y _ => by simp [centered]
  forget := fun n n' _ _ _ _ W W' Y Y' ω ω' y y' m _ _ _ _ _ _ => by
    simp only [sub_self, abs_zero]
    exact (Real.exp_pos _).le
  forget_cold := fun n n' _ _ _ _ W W' Y ω ω' y y' m _ _ _ _ _ => by
    rw [centered_zero]
    simp only [sub_self, abs_zero]
    exact (Real.exp_pos _).le
  smooth := fun n _ hs W Y ω hY hpos k c X hfar => by
    classical
    have hYe : Y = minimalHull ℓ (clusterRange β) W := by
      by_contra hne
      rw [wilsonHullWeight_eq, if_neg hne] at hpos
      exact lt_irrefl _ hpos
    have hfar' : ∀ l, ∀ z ∈ torusHotSites ℓ W, clusterRange β ≤ supDist (c l).1 z := fun l z hz =>
      hfar l z (hY.1 ((mem_thickening _ _ _).mpr ⟨z, hz, by rw [supDist_self]; omega⟩))
    have hev := eventually_torusHotLumps_perturb_eq hfit hs.1 (by omega) c X hfar'
    have hE : (fun σ : Fin k → ℝ => wilsonHullWeight ℓ β n (perturb c X σ W) Y ω) =ᶠ[nhds 0]
        fun σ => Real.exp (-β * wilsonAction Finset.univ (perturb c X σ W)) := by
      filter_upwards [hev] with σ hσ
      rw [wilsonHullWeight_eq, if_pos (hYe.trans (minimalHull_congr hσ.symm)), wilsonWeight_eq]
    have hc3 : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => wilsonAction Finset.univ (perturb c X σ W)) 0 :=
      (hD n W).1 k c X
    refine ⟨?_, fun hk1 hk3 hX => ?_⟩
    · exact ((contDiffAt_const.mul hc3).exp).congr_of_eventuallyEq hE
    · have hE' : (fun σ : Fin k → ℝ => Real.log (wilsonHullWeight ℓ β n (perturb c X σ W) Y ω)) =ᶠ[nhds 0]
          (-β) • fun σ : Fin k → ℝ => wilsonAction Finset.univ (perturb c X σ W) := by
        filter_upwards [hE] with σ hσ
        rw [hσ, Real.log_exp]
        simp
      unfold mixedDeriv
      rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hE' k).eq_of_nhds,
        iteratedFDeriv_const_smul_apply (hc3.of_le (by exact_mod_cast hk3))]
      have hb := (hD n W).2 k c X hk1 hk3 hX
      unfold mixedDeriv at hb
      simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul, abs_mul, abs_neg]
      rw [abs_of_pos (by linarith : (0 : ℝ) < β)]
      have h1 : (1 : ℝ) ≤ ℓ.derivBound * β := by nlinarith
      calc β * _ ≤ β * C := by gcongr
        _ ≤ β * ℓ.derivBound := by gcongr
        _ = ℓ.derivBound * β := by ring
        _ ≤ (ℓ.derivBound * β) ^ k := le_self_pow₀ h1 (by omega)
  price := fun n _ hs W Y ω P hY hP hother => by
    classical
    have hle : ∀ ν : ↥(P.biUnion id) → pointLabelSpace.Ω,
        (if ∃ X ∈ P, wilsonComponentFactor ℓ β n W Y (glueLabel Y (P.biUnion id) ω ν) X = 0 then 0 else
          ENNReal.ofReal ((∏ X ∈ P, wilsonComponentFactor ℓ β n W Y (glueLabel Y (P.biUnion id) ω ν) X) *
            Real.exp (∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
                ∃ z ∈ P.biUnion id, (supDist y z : ℝ) < (clusterRange β : ℝ) / 4), (0 : ℝ)))) ≤
        ENNReal.ofReal (Real.exp (-(β * ℓ.κ * ℓ.threshold ^ 2 *
            (((torusHotLumps ℓ W).filter (· ⊆ P.biUnion id)).card : ℝ)) -
          ℓ.κ₁ * β * ℓ.threshold ^ 2 * (excessLength ℓ (clusterRange β) (P.biUnion id) W : ℝ))) := by
      intro ν
      split_ifs with hz
      · exact zero_le
      · push_neg at hz
        have hcond : ∀ X ∈ P, X = thickening (2 * clusterRange β) (lumpCore ℓ W X) := by
          intro X hX
          by_contra hne
          exact hz X hX (by rw [wilsonComponentFactor_of_hull hfit hs.1 hr hY (hP hX), if_neg hne])
        apply ENNReal.ofReal_le_ofReal
        have hprod : ∏ X ∈ P, wilsonComponentFactor ℓ β n W Y (glueLabel Y (P.biUnion id) ω ν) X =
            Real.exp (-β * ∑ X ∈ P, componentEnergy ℓ W X) := by
          rw [Finset.mul_sum, Real.exp_sum]
          refine Finset.prod_congr rfl fun X hX => ?_
          rw [wilsonComponentFactor_of_hull hfit hs.1 hr hY (hP hX), if_pos (hcond X hX)]
        rw [hprod, Finset.sum_const_zero, Real.exp_zero, mul_one, excessLength_eq_zero hfit hs.1 hr hcond]
        apply Real.exp_le_exp.mpr
        have hp := card_hot_le_sum_componentEnergy hfit hs.1 hr hY.1 hP
        have hκ := hfit.κ_le
        have hcard : (0 : ℝ) ≤ (((torusHotLumps ℓ W).filter (· ⊆ P.biUnion id)).card : ℝ) := by positivity
        have hσ : 0 ≤ ℓ.threshold ^ 2 := by positivity
        have h1 : ℓ.κ * ℓ.threshold ^ 2 * (((torusHotLumps ℓ W).filter (· ⊆ P.biUnion id)).card : ℝ) ≤
            ℓ.threshold ^ 2 / 8 * (((torusHotLumps ℓ W).filter (· ⊆ P.biUnion id)).card : ℝ) := by
          have : ℓ.κ * ℓ.threshold ^ 2 ≤ 1 / 8 * ℓ.threshold ^ 2 := by gcongr
          nlinarith
        have h2 : ℓ.κ * ℓ.threshold ^ 2 * (((torusHotLumps ℓ W).filter (· ⊆ P.biUnion id)).card : ℝ) ≤
            ∑ X ∈ P, componentEnergy ℓ W X := h1.trans hp
        have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ β)
        simp only [Nat.cast_zero, mul_zero, sub_zero]
        nlinarith
    refine (lintegral_mono hle).trans ?_
    simp
end
theorem wilsonWeightHasExpansion (hD : WilsonDerivatives.BoundedDerivativesOfWilsonAction) :
    WilsonWeightHasExpansion := by
  classical
  obtain ⟨C, hC0, hC⟩ := hD
  refine ⟨C, fun ℓ hfit hCd β hβ => ?_⟩
  have hβ1 : 1 ≤ β := hfit.y₁_ge.trans hβ
  have hr : 2 ^ 16 ≤ clusterRange β :=
    hfit.range_ge.trans (clusterRange_mono (by linarith [hfit.y₁_ge]) hβ)
  refine ⟨fun n _ _ => ⟨measurable_wilsonWeight, fun W => ?_, fun g W => ?_, fun g W W' h => ?_⟩,
    fun _ _ _ => 0, wilsonWeight_coldExpansion hfit, pointLabelSpace, wilsonHullWeight ℓ β,
    wilsonComponentFactor ℓ β, fun _ _ _ _ _ => 0,
    wilsonWeight_hullExpansion hfit hr hβ1 C hCd hfit.Cder_ge hC⟩
  · rw [wilsonWeight_eq]
    exact (Real.exp_pos _).le
  · simp only [wilsonWeight_eq, wilsonAction_gaugeTransform]
  · simp only [wilsonWeight_eq, wilsonAction_of_transports h]
end WilsonExpansion
end YangMills.Construction
end
