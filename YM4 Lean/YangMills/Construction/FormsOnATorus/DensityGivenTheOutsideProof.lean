import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ClusterExpansionOfAStep.DensitiesAgainstAMirror
import YangMills.Construction.ClusterExpansionOfAStep.GeometryOfFreeBonds
import YangMills.Construction.ClusterExpansionOfAStep.RegionOffTheHotLumpsIsRegular
import YangMills.Construction.ClusterExpansionOfAStep.SumsOnATorus
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import YangMills.Construction.LawOnABoxOfTheFlow.DensityGivenTheOutside
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open TorusFields TorusLumps TorusShares TorusMirror MirrorDensities StepCosts FreeBonds HotLumps LumpContours
  WeightedResponses ResponseInTheExpansion BoxGaussian StepSettings RenormalizationStepParameters
namespace BoxEvents
namespace ConditionalDensity
section Sites
variable {n : ℕ} [NeZero n]
private theorem natAbs_le_of_abs_le {a : ℤ} {m : ℕ} (h : |a| ≤ (m : ℤ)) : a.natAbs ≤ m := by apply _root_.YangMills.Construction.CongruentBoxes.natAbs_le_of_abs_le_natCast <;> assumption
private theorem mem_supBall {o z : TorusSite n} {r : ℝ} : z ∈ supBall o r ↔ (_root_.YangMills.Construction.TorusFields.supDist z o : ℝ) ≤ r := by
  simp [supBall]
private theorem mem_supBall_nat {o z : TorusSite n} {R : ℕ} : z ∈ supBall o (R : ℝ) ↔ _root_.YangMills.Construction.TorusFields.supDist z o ≤ R := by
  rw [mem_supBall]
  exact_mod_cast Iff.rfl
private theorem mem_supBall_two_mul {o z : TorusSite n} {R : ℕ} :
    z ∈ supBall o (2 * (R : ℝ)) ↔ _root_.YangMills.Construction.TorusFields.supDist z o ≤ 2 * R := by
  rw [mem_supBall]
  exact_mod_cast Iff.rfl
private theorem mem_supBall_three_mul {o z : TorusSite n} {R : ℕ} :
    z ∈ supBall o (3 * (R : ℝ)) ↔ _root_.YangMills.Construction.TorusFields.supDist z o ≤ 3 * R := by
  rw [mem_supBall]
  exact_mod_cast Iff.rfl
private theorem mem_supBall_three_halves {o z : TorusSite n} {R : ℕ} :
    z ∈ supBall o (3 * (R : ℝ) / 2) ↔ 2 * _root_.YangMills.Construction.TorusFields.supDist z o ≤ 3 * R := by
  rw [mem_supBall, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  constructor
  · intro h
    have : ((2 * _root_.YangMills.Construction.TorusFields.supDist z o : ℕ) : ℝ) ≤ ((3 * R : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  · intro h
    have : ((2 * _root_.YangMills.Construction.TorusFields.supDist z o : ℕ) : ℝ) ≤ ((3 * R : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
private theorem valMinAbs_intCast_of_lt {e : ℤ} (h : 2 * |e| < (n : ℤ)) : ((e : ZMod n)).valMinAbs = e := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
private theorem supDist_le_two_of_vertex {x z : TorusSite n} {μ ν : Fin 4} (hz : z ∈ plaquetteVertices x μ ν) :
    _root_.YangMills.Construction.TorusFields.supDist x z ≤ 2 := by apply _root_.YangMills.Construction.InBoxTransfer.supDist_le_two_of_mem_plaquetteVertices <;> assumption
private theorem supDist_le_of_offsetInBox {y z : TorusSite n} {v : Fin 4 → ℤ} {m : ℕ} (hv : OffsetInBox m v)
    (hz : z = y + siteOfInt v) : _root_.YangMills.Construction.TorusFields.supDist y z ≤ m := by
  rw [hz]
  exact _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le y v m fun i => natAbs_le_of_abs_le (hv i)
private theorem supBall_locallyOrthantClosed {o : TorusSite n} {R : ℕ} (hR : 1024 ≤ R) (hn : 8 * R < n) :
    IsLocallyOrthantClosed (supBall o (2 * (R : ℝ))) 1024 := by
  intro z
  refine ⟨fun i => if 0 ≤ ((z i - o i).valMinAbs) then -1 else 1, fun i => ?_, ?_⟩
  · by_cases h : 0 ≤ ((z i - o i).valMinAbs)
    · simp [h]
    · simp [h]
  intro q hq hdist v hsign hsmall
  rw [mem_supBall_two_mul] at hq ⊢
  rw [_root_.YangMills.Construction.TorusFields.supDist_le_iff] at hq ⊢
  rw [_root_.YangMills.Construction.TorusFields.supDist_le_iff] at hdist
  intro i
  set a : ℤ := (q i - o i).valMinAbs with ha
  set b : ℤ := (q i - z i).valMinAbs with hb
  have ha' : a.natAbs ≤ 2 * R := hq i
  have hb' : b.natAbs ≤ 1024 := hdist i
  have hcast_a : ((a : ℤ) : ZMod n) = q i - o i := by simp [ha]
  have hcast_b : ((b : ℤ) : ZMod n) = q i - z i := by simp [hb]
  have hz : (z i - o i) = ((a - b : ℤ) : ZMod n) := by
    push_cast
    rw [hcast_a, hcast_b]
    ring
  have hc : (z i - o i).valMinAbs = a - b := by
    rw [hz]
    apply valMinAbs_intCast_of_lt
    have : |a - b| ≤ 2 * (R : ℤ) + 1024 := by
      rw [abs_le]
      omega
    omega
  have hsum : (q i + (siteOfInt v : TorusSite n) i - o i) = ((a + v i : ℤ) : ZMod n) := by
    push_cast
    rw [hcast_a]
    simp only [siteOfInt]
    ring
  have hs : 0 ≤ (if 0 ≤ ((z i - o i).valMinAbs) then (-1 : ℤ) else 1) * v i := hsign i
  have hm : -1024 ≤ v i ∧ v i ≤ 1024 := by simpa [abs_le] using hsmall i
  have hval : ((q + siteOfInt v : TorusSite n) i - o i) = ((a + v i : ℤ) : ZMod n) := hsum
  rw [hval]
  refine (_root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le _).trans ?_
  by_cases hcs : 0 ≤ (z i - o i).valMinAbs
  · rw [if_pos hcs] at hs
    rw [hc] at hcs
    omega
  · rw [if_neg hcs] at hs
    rw [hc] at hcs
    omega
end Sites
section Fields
variable {n : ℕ} [NeZero n] {ℓ : StepParameters}
private theorem eq_of_outside {o : TorusSite n} {R : ℕ} {W W' : TorusField n}
    (hout : restrictOuter o R W = restrictOuter o R W') {x : TorusSite n}
    {i : Fin 4} (h1 : x ∉ supBall o (R : ℝ)) (h2 : x + unitStep n i ∉ supBall o (R : ℝ)) : W x i = W' x i := by
  have hb : (x, i) ∉ bondsTouching o R := by
    intro h
    rcases (Finset.mem_filter.mp h).2 with h | h
    · exact h1 h
    · exact h2 h
  exact congrFun hout ⟨(x, i), hb⟩
private theorem curvature_eq_of_outside {o : TorusSite n} {R : ℕ} {W W' : TorusField n}
    (hout : restrictOuter o R W = restrictOuter o R W') {x : TorusSite n}
    {μ ν : Fin 4} (h : ∀ z ∈ plaquetteVertices x μ ν, z ∉ supBall o (R : ℝ)) :
    curvature W x μ ν = curvature W' x μ ν := by
  have c0 := h x (by simp [plaquetteVertices])
  have c1 := h (x + unitStep n μ) (by simp [plaquetteVertices])
  have c2 := h (x + unitStep n ν) (by simp [plaquetteVertices])
  have c3 := h (x + unitStep n μ + unitStep n ν) (by simp [plaquetteVertices])
  have e1 := eq_of_outside hout c0 c1
  have e2 := eq_of_outside (i := ν) hout c1 c3
  have e3 := eq_of_outside (i := μ) hout c2 (by rwa [add_right_comm])
  have e4 := eq_of_outside (i := ν) hout c0 c2
  unfold curvature holonomy
  rw [e1, e2, e3, e4]
private theorem torusHotLumps_subset (hadm : ℓ.Admissible) (hLn : ℓ.side ∣ n) {o : TorusSite n} {R : ℕ}
    (hR : 4 ≤ R) {W W' : TorusField n} (hout : restrictOuter o R W = restrictOuter o R W')
    (hcold : ∀ p ∈ plaquettesIn (supBall o (2 * (R : ℝ))), curvature W p.1 p.2.1 p.2.2 < ℓ.threshold) :
    torusHotLumps ℓ W ⊆ torusHotLumps ℓ W' := by
  intro l hl
  obtain ⟨x, μ, ν, hlt, hh, z, hz, rfl⟩ := (mem_torusHotLumps_iff ℓ hadm hLn W l).mp hl
  have hout' : ∀ z ∈ plaquetteVertices x μ ν, z ∉ supBall o (R : ℝ) := by
    intro z₀ hz₀ hin
    have hp : ((x, μ, ν) : TorusPlaquette n) ∈ plaquettesIn (supBall o (2 * (R : ℝ))) := by
      refine mem_plaquettesIn.mpr ⟨hlt, fun c hc => ?_⟩
      rw [mem_supBall_two_mul]
      have h1 : _root_.YangMills.Construction.TorusFields.supDist c x ≤ 2 := by
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
        exact supDist_le_two_of_vertex hc
      have h2 : _root_.YangMills.Construction.TorusFields.supDist x z₀ ≤ 2 := supDist_le_two_of_vertex hz₀
      have h3 : _root_.YangMills.Construction.TorusFields.supDist z₀ o ≤ R := mem_supBall_nat.mp hin
      have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle c x o
      have h5 := _root_.YangMills.Construction.TorusFields.supDist_triangle x z₀ o
      omega
    exact absurd (hcold _ hp) (not_lt.mpr hh)
  have he := curvature_eq_of_outside hout hout'
  exact (mem_torusHotLumps_iff ℓ hadm hLn W' _).mpr ⟨x, μ, ν, hlt, he ▸ hh, z, hz, rfl⟩
private theorem offHot_locallyOrthantClosed (hreg : OffHotRegionIsRegular) (hadm : ℓ.Admissible)
    (hLn : ℓ.side ∣ n) (W : TorusField n) :
    IsLocallyOrthantClosed (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) 1024 := by
  obtain ⟨m, hm⟩ := hLn
  rw [mul_comm] at hm
  subst hm
  have : NeZero m := ⟨fun h => by
    subst h
    exact absurd (zero_mul ℓ.side) (NeZero.ne _)⟩
  exact hreg ℓ m W hadm
private theorem offHot_isColdOn (hadm : ℓ.Admissible) (hLn : ℓ.side ∣ n) (W : TorusField n) :
    IsColdOn (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) ℓ.threshold W := by
  intro x μ ν hlt hc
  by_contra hnot
  have hh : ℓ.threshold ≤ curvature W x μ ν := not_lt.mp hnot
  have hl : torusLumpOf ℓ x ∈ torusHotLumps ℓ W :=
    (mem_torusHotLumps_iff ℓ hadm hLn W _).mpr ⟨x, μ, ν, hlt, hh, x, by simp [plaquetteVertices], rfl⟩
  have hz : x ∈ torusHotSites ℓ W := Finset.mem_biUnion.mpr ⟨_, hl, mem_torusLumpOf_self x⟩
  have hx := hc x (by simp [plaquetteVertices])
  refine (Finset.mem_sdiff.mp hx).2 ((mem_thickening _ _ _).mpr ⟨x, hz, ?_⟩)
  simp [_root_.YangMills.Construction.TorusFields.supDist_self]
private theorem supBall_isColdOn {o : TorusSite n} {R : ℕ} {s : ℝ} {W : TorusField n}
    (h : ∀ p ∈ plaquettesIn (supBall o (2 * (R : ℝ))), curvature W p.1 p.2.1 p.2.2 < s) :
    IsColdOn (supBall o (2 * (R : ℝ))) s W := fun x μ ν hlt hc =>
  h (x, μ, ν) (mem_plaquettesIn.mpr ⟨hlt, hc⟩)
end Fields
section Core
variable {n : ℕ} [NeZero n] {ℓ : StepParameters}
private structure OuterPair (ℓ : StepParameters) (x : ℝ) (o : TorusSite n) (R : ℕ) (W W' : TorusField n)
    (Y : Finset (TorusSite n)) : Prop where
  admissible : ℓ.Admissible
  blockSide : IsBlockTorusSide ℓ n
  large : 1024 ≤ R
  wide : 16 * R < n
  floor : ℓ.n₀ ≤ 8 * R
  range : clusterRange x ≤ R
  reach : lumpRange ≤ 2 * clusterRange x
  outer : restrictOuter o R W = restrictOuter o R W'
  far : Disjoint Y (supBall o (3 * (R : ℝ)))
  cold : ∀ p ∈ plaquettesIn (supBall o (2 * (R : ℝ))), curvature W p.1 p.2.1 p.2.2 < ℓ.threshold
  cold' : ∀ p ∈ plaquettesIn (supBall o (2 * (R : ℝ))), curvature W' p.1 p.2.1 p.2.2 < ℓ.threshold
variable {x : ℝ} {o : TorusSite n} {R : ℕ} {W W' : TorusField n} {Y : Finset (TorusSite n)}
private theorem OuterPair.hot_eq (g : OuterPair ℓ x o R W W' Y) : torusHotLumps ℓ W' = torusHotLumps ℓ W :=
  Finset.Subset.antisymm
    (torusHotLumps_subset g.admissible g.blockSide.1 (by have := g.large; omega) g.outer.symm g.cold')
    (torusHotLumps_subset g.admissible g.blockSide.1 (by have := g.large; omega) g.outer g.cold)
private theorem OuterPair.sites_eq (g : OuterPair ℓ x o R W W' Y) : torusHotSites ℓ W' = torusHotSites ℓ W := by
  unfold torusHotSites
  rw [g.hot_eq]
private theorem OuterPair.isHullState (g : OuterPair ℓ x o R W W' Y) (h : IsHullState ℓ (clusterRange x) W Y) :
    IsHullState ℓ (clusterRange x) W' Y := by
  unfold IsHullState at *
  rw [g.sites_eq, g.hot_eq]
  exact h
private theorem OuterPair.mem_offHot (g : OuterPair ℓ x o R W W' Y) (hh : IsHullState ℓ (clusterRange x) W Y)
    {z : TorusSite n} (hz : _root_.YangMills.Construction.TorusFields.supDist z o ≤ 3 * R) :
    z ∈ Finset.univ \ thickening lumpRange (torusHotSites ℓ W) := by
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hw => ?_⟩
  obtain ⟨u, hu, hdist⟩ := (mem_thickening _ _ _).mp hw
  have hy : z ∈ Y := hh.1 ((mem_thickening _ _ _).mpr ⟨u, hu, hdist.trans g.reach⟩)
  exact Finset.disjoint_left.mp g.far hy (mem_supBall_three_mul.mpr hz)
private theorem OuterPair.not_mem_supBall (g : OuterPair ℓ x o R W W' Y) {z : TorusSite n} (hz : z ∈ Y) :
    z ∉ supBall o (R : ℝ) := by
  intro hb
  have h1 : _root_.YangMills.Construction.TorusFields.supDist z o ≤ R := mem_supBall_nat.mp hb
  exact Finset.disjoint_left.mp g.far hz (mem_supBall_three_mul.mpr (by omega))
private theorem subset_of_mem_chainComponents {r : ℕ} {X : Finset (TorusSite n)} (hX : X ∈ chainComponents r Y) :
    X ⊆ Y := by
  classical
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hX
  exact fun z hz => (Finset.mem_filter.mp hz).1
variable {t : ℕ} {D : TorusFunctional} {f : LocalDensity} {Λ : LabelSpace}
  {Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
  {Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ}
  {φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
private theorem OuterPair.clusterFactor_eq (g : OuterPair ℓ x o R W W' Y)
    (hexp : HullExpansion ℓ t x D f Λ Dq Φ φ) (ω : Y → Λ.Ω)
    {X : Finset (TorusSite n)} (hX : X ∈ chainComponents (clusterRange x) Y) : Φ n W Y ω X = Φ n W' Y ω X :=
  hexp.reads_class n g.blockSide W W' Y Y ω ω X (subset_of_mem_chainComponents hX)
    (subset_of_mem_chainComponents hX)
    (fun _ h1 h2 => eq_of_outside g.outer (g.not_mem_supBall (subset_of_mem_chainComponents hX h1))
      (g.not_mem_supBall (subset_of_mem_chainComponents hX h2)))
    (fun _ _ _ _ => rfl)
private theorem OuterPair.log_labelWeight_sub (g : OuterPair ℓ x o R W W' Y)
    (hexp : HullExpansion ℓ t x D f Λ Dq Φ φ) (ω : Y → Λ.Ω)
    (hh : IsHullState ℓ (clusterRange x) W Y) (hp : 0 < Dq n W Y ω) :
    0 < Dq n W' Y ω ∧ (∀ X ∈ chainComponents (clusterRange x) Y, Φ n W Y ω X ≠ 0) ∧
      (∀ X ∈ chainComponents (clusterRange x) Y, Φ n W' Y ω X ≠ 0) ∧
      Real.log (Dq n W' Y ω) - Real.log (Dq n W Y ω) =
        (-x * actionAtLevel ℓ.coupling ℓ.side t (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W' +
            ∑ y, φ n y W' Y ω) -
        (-x * actionAtLevel ℓ.coupling ℓ.side t (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W +
            ∑ y, φ n y W Y ω) := by
  have e := hexp.form n g.blockSide W Y ω hh
  have e' := hexp.form n g.blockSide W' Y ω (g.isHullState hh)
  rw [g.sites_eq] at e'
  have hP : ∏ X ∈ chainComponents (clusterRange x) Y, Φ n W' Y ω X =
      ∏ X ∈ chainComponents (clusterRange x) Y, Φ n W Y ω X :=
    Finset.prod_congr rfl fun X hX => (g.clusterFactor_eq hexp ω hX).symm
  rw [hP] at e'
  set P := ∏ X ∈ chainComponents (clusterRange x) Y, Φ n W Y ω X with hPd
  set E := -x * actionAtLevel ℓ.coupling ℓ.side t (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W +
    ∑ y, φ n y W Y ω with hE
  set E' := -x * actionAtLevel ℓ.coupling ℓ.side t (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W' +
    ∑ y, φ n y W' Y ω with hE'
  set Q := D n (trivialField n) * P with hQ
  have r1 : Dq n W Y ω = Real.exp E * Q := by rw [e, hQ]; ring
  have r2 : Dq n W' Y ω = Real.exp E' * Q := by rw [e', hQ]; ring
  have hQpos : 0 < Q := by
    by_contra hc
    have := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos E).le (not_lt.mp hc)
    rw [← r1] at this
    linarith
  have hPne : P ≠ 0 := by
    intro h0
    rw [hQ, h0, mul_zero] at hQpos
    exact lt_irrefl _ hQpos
  have hall : ∀ X ∈ chainComponents (clusterRange x) Y, Φ n W Y ω X ≠ 0 := Finset.prod_ne_zero_iff.mp hPne
  refine ⟨?_, hall, fun X hX => ?_, ?_⟩
  · rw [r2]
    exact mul_pos (Real.exp_pos _) hQpos
  · rw [← g.clusterFactor_eq hexp ω hX]
    exact hall X hX
  · rw [r1, r2, Real.log_mul (Real.exp_pos _).ne' hQpos.ne', Real.log_mul (Real.exp_pos _).ne' hQpos.ne',
      Real.log_exp, Real.log_exp]
    ring
private theorem fieldsAgreeNear_of_far (hout : restrictOuter o R W = restrictOuter o R W') {y : TorusSite n} {ρ : ℕ}
    (hρ : ρ + R < _root_.YangMills.Construction.TorusFields.supDist y o) : FieldsAgreeNear W W' y y ρ := by
  have key : ∀ v : Fin 4 → ℤ, OffsetInBox ρ v → y + siteOfInt v ∉ supBall o (R : ℝ) := by
    intro v hb hz
    have h1 : _root_.YangMills.Construction.TorusFields.supDist y (y + siteOfInt v) ≤ ρ := supDist_le_of_offsetInBox hb rfl
    have h2 : _root_.YangMills.Construction.TorusFields.supDist (y + siteOfInt v) o ≤ R := mem_supBall_nat.mp hz
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle y (y + siteOfInt v) o
    omega
  rintro ⟨v, i⟩ ⟨h1, h2⟩
  refine eq_of_outside hout (key v h1) ?_
  have e : y + siteOfInt v + unitStep n i = y + siteOfInt (v + Pi.single i 1) := by
    rw [add_siteOfInt_add, unitStep_eq_siteOfInt]
  show y + siteOfInt v + unitStep n i ∉ _
  rw [e]
  exact key _ h2
variable {s₀ A δ : ℝ}
private theorem OuterPair.levelShare_near (g : OuterPair ℓ x o R W W' Y)
    (hS : ShareLocality ℓ.coupling ℓ.side s₀ A δ) (hs : ℓ.threshold ≤ s₀)
    {V : TorusField n} {U : Finset (TorusSite n)} (hU : IsLocallyOrthantClosed U 1024)
    (hUc : IsColdOn U ℓ.threshold V) (hin : ∀ z, _root_.YangMills.Construction.TorusFields.supDist z o ≤ 3 * R → z ∈ U)
    (hV : IsColdOn (supBall o (2 * (R : ℝ))) ℓ.threshold V) (t : ℕ) {y : TorusSite n}
    (hy : 2 * _root_.YangMills.Construction.TorusFields.supDist y o ≤ 3 * R) :
    |levelShare ℓ.coupling ℓ.side t U y V - levelShare ℓ.coupling ℓ.side t (supBall o (2 * (R : ℝ))) y V| ≤
      A * Real.exp (-(δ * ((R / 2 - 1 : ℕ) : ℝ))) := by
  have hR := g.large
  have hn := g.wide
  refine hS.decay_of_agreement t n U _ V V y (R / 2 - 1) ℓ.threshold (by omega) g.admissible.σ_pos hs hU
    (supBall_locallyOrthantClosed hR (by omega)) hUc hV ⟨by omega, fun v hb => ?_, fun _ _ => rfl⟩
  have h1 : _root_.YangMills.Construction.TorusFields.supDist y (y + siteOfInt v) ≤ R / 2 - 1 := supDist_le_of_offsetInBox hb rfl
  have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (y + siteOfInt v) y o
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm (y + siteOfInt v) y] at h2
  constructor
  · intro _
    exact mem_supBall_two_mul.mpr (by omega)
  · intro _
    exact hin _ (by omega)
private theorem OuterPair.levelShare_far (g : OuterPair ℓ x o R W W' Y)
    (hS : ShareLocality ℓ.coupling ℓ.side s₀ A δ) (hs : ℓ.threshold ≤ s₀)
    {U : Finset (TorusSite n)} (hU : IsLocallyOrthantClosed U 1024) (hUc : IsColdOn U ℓ.threshold W)
    (hUc' : IsColdOn U ℓ.threshold W') (t : ℕ) {y : TorusSite n} (hy : R + 2 ≤ _root_.YangMills.Construction.TorusFields.supDist y o) :
    |levelShare ℓ.coupling ℓ.side t U y W - levelShare ℓ.coupling ℓ.side t U y W'| ≤
      A * Real.exp (-(δ * ((_root_.YangMills.Construction.TorusFields.supDist y o - R - 2 : ℕ) : ℝ))) := by
  have hn := g.wide
  have h2 := two_mul_supDist_le y o
  exact hS.decay_of_agreement t n U U W W' y (_root_.YangMills.Construction.TorusFields.supDist y o - R - 2) ℓ.threshold (by have := g.large; omega)
    g.admissible.σ_pos hs hU hU hUc hUc' ⟨by omega, fun _ _ => Iff.rfl, fieldsAgreeNear_of_far g.outer (by omega)⟩
private theorem OuterPair.siteDensity_far (g : OuterPair ℓ x o R W W' Y) (hexp : HullExpansion ℓ t x D f Λ Dq Φ φ)
    (ω : Y → Λ.Ω) (hh : IsHullState ℓ (clusterRange x) W Y)
    (hΦ : ∀ X ∈ chainComponents (clusterRange x) Y, Φ n W Y ω X ≠ 0)
    (hΦ' : ∀ X ∈ chainComponents (clusterRange x) Y, Φ n W' Y ω X ≠ 0) {y : TorusSite n}
    (hy : 3 * R ≤ 2 * _root_.YangMills.Construction.TorusFields.supDist y o) :
    |φ n y W Y ω - φ n y W' Y ω| ≤ Real.exp (-ℓ.decayRate * ((_root_.YangMills.Construction.TorusFields.supDist y o - R - 2 : ℕ) : ℝ)) := by
  have hR := g.large
  have hr := g.range
  have h2 := two_mul_supDist_le y o
  refine hexp.forget n n g.blockSide g.blockSide W W' Y Y ω ω y y (_root_.YangMills.Construction.TorusFields.supDist y o - R - 2) hh (g.isHullState hh) hΦ hΦ'
    ?_ ⟨by omega, by omega, fieldsAgreeNear_of_far g.outer (by omega), fun _ _ => Iff.rfl, fun _ _ _ _ _ => rfl,
      fun _ i => by simp⟩
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 64)]
  have : clusterRange x ≤ (_root_.YangMills.Construction.TorusFields.supDist y o - R - 2) * 64 := by omega
  exact_mod_cast this
private theorem OuterPair.siteDensity_near (g : OuterPair ℓ x o R W W' Y) (hexp : HullExpansion ℓ t x D f Λ Dq Φ φ)
    (ω : Y → Λ.Ω) {V : TorusField n} (hh : IsHullState ℓ (clusterRange x) V Y)
    (hΦ : ∀ X ∈ chainComponents (clusterRange x) Y, Φ n V Y ω X ≠ 0)
    (hV : ∀ p ∈ plaquettesIn (supBall o (2 * (R : ℝ))), curvature V p.1 p.2.1 p.2.2 < ℓ.threshold)
    {y : TorusSite n} (hy : 2 * _root_.YangMills.Construction.TorusFields.supDist y o ≤ 3 * R) :
    |φ n y V Y ω - centered f (4 * (2 * R)) (siteOfInt (offset o y)) (mirrorField (2 * R) o V)| ≤
      Real.exp (-ℓ.decayRate * ((R / 2 - 1 : ℕ) : ℝ)) := by
  have hn := g.wide
  have hR := g.large
  have hr := g.range
  have hf := g.floor
  have : NeZero (4 * (2 * R)) := ⟨by omega⟩
  set m := R / 2 - 1 with hm
  set gy := offset o y with hgy
  have hg : ∀ j, |gy j| ≤ (_root_.YangMills.Construction.TorusFields.supDist y o : ℤ) := fun j => abs_offset_le o y j
  have hcold : IsCold ℓ.threshold (mirrorField (2 * R) o V) := by
    refine isCold_mirrorField (by omega) o V g.admissible.σ_pos fun a μ ν hlt hc => ?_
    refine hV (o + siteOfInt a, μ, ν) (mem_plaquettesIn.mpr ⟨hlt, fun c hcm => ?_⟩)
    obtain ⟨e, he, rfl⟩ := (mem_plaquetteVertices_iff_offset _ c μ ν).mp hcm
    rw [mem_supBall_two_mul, ← add_siteOfInt_add, _root_.YangMills.Construction.TorusFields.supDist_comm]
    exact _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le o (a + e) _ fun i => natAbs_le_of_abs_le (hc e he i)
  have hsum : ∀ v : Fin 4 → ℤ, OffsetInBox m v → OffsetInBox (2 * R) (gy + v) := by
    intro v hb j
    have h1 := hg j
    have h2 := hb j
    have h3 : |(gy + v) j| ≤ |gy j| + |v j| := abs_add_le _ _
    have h4 : ((_root_.YangMills.Construction.TorusFields.supDist y o : ℤ) + (m : ℤ)) ≤ ((2 * R : ℕ) : ℤ) := by
      have : _root_.YangMills.Construction.TorusFields.supDist y o + m ≤ 2 * R := by omega
      exact_mod_cast this
    linarith
  have hnot : ∀ v : Fin 4 → ℤ, OffsetInBox m v → y + siteOfInt v ∉ Y := by
    intro v hb hY
    have h1 : _root_.YangMills.Construction.TorusFields.supDist y (y + siteOfInt v) ≤ m := supDist_le_of_offsetInBox hb rfl
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (y + siteOfInt v) y o
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm (y + siteOfInt v) y] at h2
    exact Finset.disjoint_left.mp g.far hY (mem_supBall_three_mul.mpr (by omega))
  refine hexp.forget_cold n (4 * (2 * R)) g.blockSide (by omega) V (mirrorField (2 * R) o V) Y ω
    (fun q => absurd q.2 (Finset.notMem_empty _)) y (siteOfInt gy) m hh hcold hΦ ?_
    ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 64)]
    have : clusterRange x ≤ m * 64 := by omega
    exact_mod_cast this
  · rintro ⟨b, i⟩ hb
    have e1 : (bondFrom (siteOfInt gy : TorusSite (4 * (2 * R))) (b, i)).1 = siteOfInt (gy + b) := by
      simp only [bondFrom]
      rw [siteOfInt_add]
    have e2 : o + siteOfInt (gy + b) = y + siteOfInt b := by
      rw [add_siteOfInt_add, hgy, add_siteOfInt_offset]
    have hbox : BondOffsetInBox (2 * R) (gy + b, i) := by
      refine ⟨hsum b hb.1, ?_⟩
      have := hsum _ hb.2
      rwa [← add_assoc] at this
    have h3 := mirrorField_siteOfInt (by omega) o V (gy + b, i) hbox
    show V (y + siteOfInt b) i = mirrorField (2 * R) o V (bondFrom (siteOfInt gy : TorusSite (4 * (2 * R))) (b, i)).1 i
    rw [e1]
    simp only at h3
    rw [h3, e2]
  · intro v hb
    constructor
    · intro hY
      exact absurd hY (hnot v hb)
    · intro hY
      exact absurd hY (Finset.notMem_empty _)
  · intro v _ _ hz' _
    exact absurd hz' (Finset.notMem_empty _)
  · rintro ⟨v, hb, hY⟩
    exact absurd hY (hnot v hb)
end Core
section Sum
variable {n : ℕ} [NeZero n] {ℓ : StepParameters}
private theorem mirrorSum_eq_sum_supBall {f : LocalDensity} {o : TorusSite n} {R : ℕ} (hR : 0 < R) (hn : 8 * R < n)
    (V : TorusField n) :
    mirrorSum f o R id V = ∑ y ∈ supBall o (3 * (R : ℝ) / 2),
      centered f (4 * (2 * R)) (siteOfInt (offset o y)) (mirrorField (2 * R) o V) := by
  have h0 : 4 * (2 * R) ≠ 0 := by omega
  unfold mirrorSum
  rw [dif_neg h0]
  have : NeZero (4 * (2 * R)) := ⟨h0⟩
  symm
  refine Finset.sum_nbij' (fun y => siteOfInt (offset o y)) (fun z => o + siteOfInt (offset 0 z)) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    have h1 := mem_supBall_three_halves.mp hy
    refine mem_supBall_three_halves.mpr ?_
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le (0 : TorusSite (4 * (2 * R))) (offset o y) (_root_.YangMills.Construction.TorusFields.supDist y o)
      fun i => natAbs_offset_le o y i
    rw [zero_add, _root_.YangMills.Construction.TorusFields.supDist_comm] at h2
    omega
  · intro z hz
    have h1 := mem_supBall_three_halves.mp hz
    refine mem_supBall_three_halves.mpr ?_
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le o (offset 0 z) (_root_.YangMills.Construction.TorusFields.supDist z 0) fun i => natAbs_offset_le 0 z i
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h2
    omega
  · intro y hy
    have h1 := mem_supBall_three_halves.mp hy
    have e : offset (0 : TorusSite (4 * (2 * R))) (siteOfInt (offset o y)) = offset o y := by
      funext i
      have h2 := abs_offset_le o y i
      have h3 : 2 * |offset o y i| < ((4 * (2 * R) : ℕ) : ℤ) := by
        push_cast
        omega
      simp only [offset, siteOfInt, Pi.zero_apply, sub_zero]
      exact valMinAbs_intCast_of_lt h3
    rw [e, add_siteOfInt_offset]
  · intro z hz
    have h1 := mem_supBall_three_halves.mp hz
    have e : offset o (o + siteOfInt (offset 0 z)) = offset 0 z := by
      funext i
      have h2 := abs_offset_le 0 z i
      have h3 : 2 * |offset 0 z i| < (n : ℤ) := by
        have : (8 * (R : ℤ)) < n := by exact_mod_cast hn
        omega
      simp only [offset, siteOfInt, Pi.add_apply, add_sub_cancel_left]
      simpa [offset] using valMinAbs_intCast_of_lt h3
    rw [e]
    simpa using add_siteOfInt_offset 0 z
  · intro y _
    rfl
private theorem abs_four_terms_le {x B C u v p q : ℝ} (hx : 0 ≤ x) (hu : |u| ≤ B) (hv : |v| ≤ B) (hp : |p| ≤ C)
    (hq : |q| ≤ C) : |-x * u + x * v + p - q| ≤ 2 * x * B + 2 * C := by
  rw [abs_le] at *
  have h1 := mul_le_mul_of_nonneg_left hu.1 hx
  have h2 := mul_le_mul_of_nonneg_left hu.2 hx
  have h3 := mul_le_mul_of_nonneg_left hv.1 hx
  have h4 := mul_le_mul_of_nonneg_left hv.2 hx
  constructor <;> nlinarith
private theorem exp_le_weight {e f₀ ρ d r : ℝ} (hf : 0 < f₀) (he : f₀ ≤ e) (hρ : 0 ≤ ρ) (h : d / 8 + r ≤ ρ) :
    Real.exp (-(e * ρ)) ≤ Real.exp (-(f₀ / 8) * d) * Real.exp (-(f₀ * r)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : f₀ * ρ ≤ e * ρ := mul_le_mul_of_nonneg_right he hρ
  have h2 : f₀ * (d / 8 + r) ≤ f₀ * ρ := mul_le_mul_of_nonneg_left h hf.le
  nlinarith
variable {x : ℝ} {o : TorusSite n} {R : ℕ} {W W' : TorusField n} {Y : Finset (TorusSite n)} {t : ℕ}
  {D : TorusFunctional} {f : LocalDensity} {Λ : LabelSpace}
  {Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
  {Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ}
  {φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
  {s₀ A δ f₀ : ℝ}
private theorem OuterPair.logRatio_bound (g : OuterPair ℓ x o R W W' Y) (hreg : OffHotRegionIsRegular)
    (hadd : SharesSumToAction) (hS : ShareLocality ℓ.coupling ℓ.side s₀ A δ) (hs : ℓ.threshold ≤ s₀)
    (hA : 0 ≤ A) (hexp : HullExpansion ℓ t x D f Λ Dq Φ φ) (hf : 0 < f₀) (hf₁ : f₀ ≤ δ)
    (hf₂ : f₀ ≤ ℓ.decayRate) (hx : 0 ≤ x)
    (ω : Y → Λ.Ω) (hh : IsHullState ℓ (clusterRange x) W Y) (hp : 0 < Dq n W Y ω) :
    IsHullState ℓ (clusterRange x) W' Y ∧ 0 < Dq n W' Y ω ∧
      |Real.log (Dq n W' Y ω) - Real.log (Dq n W Y ω) +
          x * (actionAtLevel ℓ.coupling ℓ.side t (supBall o (2 * (R : ℝ))) W' -
            actionAtLevel ℓ.coupling ℓ.side t (supBall o (2 * (R : ℝ))) W) -
          (mirrorSum f o R id W' - mirrorSum f o R id W)| ≤
        (2 * x * A + 2) * ((2 / (1 - Real.exp (-(f₀ / 8) / 4))) ^ 4 * Real.exp (-(f₀ * (5 * R / 16 - 2)))) := by
  classical
  obtain ⟨hp', hΦ, hΦ', hlog⟩ := g.log_labelWeight_sub hexp ω hh hp
  refine ⟨g.isHullState hh, hp', ?_⟩
  have hR := g.large
  have hn := g.wide
  have hLn := g.blockSide.1
  have hadm := g.admissible
  have hh' := g.isHullState hh
  set U := Finset.univ \ thickening lumpRange (torusHotSites ℓ W) with hU
  set S := supBall o (2 * (R : ℝ)) with hSd
  set N := supBall o (3 * (R : ℝ) / 2) with hN
  have hUr : IsLocallyOrthantClosed U 1024 := offHot_locallyOrthantClosed hreg hadm hLn W
  have hUc : IsColdOn U ℓ.threshold W := offHot_isColdOn hadm hLn W
  have hUc' : IsColdOn U ℓ.threshold W' := by
    have := offHot_isColdOn hadm hLn W'
    rwa [g.sites_eq] at this
  have hSr : IsLocallyOrthantClosed S 1024 := supBall_locallyOrthantClosed hR (by omega)
  have hSc : IsColdOn S ℓ.threshold W := supBall_isColdOn g.cold
  have hSc' : IsColdOn S ℓ.threshold W' := supBall_isColdOn g.cold'
  have hin : ∀ z, _root_.YangMills.Construction.TorusFields.supDist z o ≤ 3 * R → z ∈ U := fun z hz => g.mem_offHot hh hz
  let wt : TorusSite n → ℝ := fun y =>
    Real.exp (-(f₀ / 8) * (_root_.YangMills.Construction.TorusFields.supDist y o : ℝ)) * Real.exp (-(f₀ * (5 * R / 16 - 2)))
  let sh : Finset (TorusSite n) → TorusSite n → TorusField n → ℝ := fun X y V =>
    levelShare ℓ.coupling ℓ.side t X y V
  let T : TorusSite n → ℝ := fun y => -x * (sh U y W' - sh U y W) + x * (sh S y W' - sh S y W) +
    (φ n y W' Y ω - φ n y W Y ω)
  let H : TorusSite n → ℝ := fun y => if y ∈ N then
    centered f (4 * (2 * R)) (siteOfInt (offset o y)) (mirrorField (2 * R) o W') -
      centered f (4 * (2 * R)) (siteOfInt (offset o y)) (mirrorField (2 * R) o W) else 0
  have hM : mirrorSum f o R id W' - mirrorSum f o R id W = ∑ y, H y := by
    rw [mirrorSum_eq_sum_supBall (by omega) (by omega), mirrorSum_eq_sum_supBall (by omega) (by omega),
      ← Finset.sum_sub_distrib]
    simp only [H]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hsum : ∀ (X : Finset (TorusSite n)) (V : TorusField n), ∑ y, sh X y V = actionAtLevel ℓ.coupling ℓ.side t X V :=
    fun X V => sum_levelShare hadd (by have := hadm.a_ge; linarith) (by have := hadm.L_ge; omega) (by omega) t X V
  have hT : Real.log (Dq n W' Y ω) - Real.log (Dq n W Y ω) +
      x * (actionAtLevel ℓ.coupling ℓ.side t S W' - actionAtLevel ℓ.coupling ℓ.side t S W) = ∑ y, T y := by
    rw [hlog]
    simp only [T, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
    ring
  have hterm : ∀ y, |T y - H y| ≤ (2 * x * A + 2) * wt y := by
    intro y
    have hw0 : 0 ≤ wt y := by positivity
    by_cases hy : y ∈ N
    · have hy2 : 2 * _root_.YangMills.Construction.TorusFields.supDist y o ≤ 3 * R := mem_supBall_three_halves.mp hy
      have hm : (_root_.YangMills.Construction.TorusFields.supDist y o : ℝ) / 8 + ((5 * R / 16 - 2 : ℝ)) ≤ ((R / 2 - 1 : ℕ) : ℝ) := by
        have k1 : R ≤ 2 * (R / 2 - 1) + 3 := by omega
        have k2 : (R : ℝ) ≤ 2 * ((R / 2 - 1 : ℕ) : ℝ) + 3 := by exact_mod_cast k1
        have k3 : 2 * (_root_.YangMills.Construction.TorusFields.supDist y o : ℝ) ≤ 3 * (R : ℝ) := by exact_mod_cast hy2
        linarith
      have he1 : Real.exp (-(δ * ((R / 2 - 1 : ℕ) : ℝ))) ≤ wt y :=
        exp_le_weight hf hf₁ (by positivity) hm
      have he2 : Real.exp (-ℓ.decayRate * ((R / 2 - 1 : ℕ) : ℝ)) ≤ wt y := by
        rw [neg_mul]
        exact exp_le_weight hf hf₂ (by positivity) hm
      have a1 := g.levelShare_near hS hs hUr hUc hin hSc t hy2
      have a2 := g.levelShare_near hS hs hUr hUc' hin hSc' t hy2
      have b1 := g.siteDensity_near hexp ω hh hΦ g.cold hy2
      have b2 := g.siteDensity_near hexp ω hh' hΦ' g.cold' hy2
      have e : T y - H y = -x * (sh U y W' - sh S y W') + x * (sh U y W - sh S y W) +
          (φ n y W' Y ω - centered f (4 * (2 * R)) (siteOfInt (offset o y)) (mirrorField (2 * R) o W')) -
          (φ n y W Y ω - centered f (4 * (2 * R)) (siteOfInt (offset o y)) (mirrorField (2 * R) o W)) := by
        simp only [T, H, if_pos hy]
        ring
      rw [e]
      have := abs_four_terms_le hx (a2.trans (mul_le_mul_of_nonneg_left he1 hA))
        (a1.trans (mul_le_mul_of_nonneg_left he1 hA)) (b2.trans he2) (b1.trans he2)
      calc _ ≤ _ := this
        _ = _ := by ring
    · have hy2 : 3 * R < 2 * _root_.YangMills.Construction.TorusFields.supDist y o := by
        by_contra hc
        exact hy (mem_supBall_three_halves.mpr (by omega))
      have hy3 : R + 2 ≤ _root_.YangMills.Construction.TorusFields.supDist y o := by omega
      have hm : (_root_.YangMills.Construction.TorusFields.supDist y o : ℝ) / 8 + ((5 * R / 16 - 2 : ℝ)) ≤ ((_root_.YangMills.Construction.TorusFields.supDist y o - R - 2 : ℕ) : ℝ) := by
        have k1 : (_root_.YangMills.Construction.TorusFields.supDist y o - R - 2) + R + 2 = _root_.YangMills.Construction.TorusFields.supDist y o := by omega
        have k2 : ((_root_.YangMills.Construction.TorusFields.supDist y o - R - 2 : ℕ) : ℝ) + R + 2 = _root_.YangMills.Construction.TorusFields.supDist y o := by exact_mod_cast k1
        have k3 : 3 * (R : ℝ) ≤ 2 * (_root_.YangMills.Construction.TorusFields.supDist y o : ℝ) := by exact_mod_cast hy2.le
        linarith
      have he1 : Real.exp (-(δ * ((_root_.YangMills.Construction.TorusFields.supDist y o - R - 2 : ℕ) : ℝ))) ≤ wt y :=
        exp_le_weight hf hf₁ (by positivity) hm
      have he2 : Real.exp (-ℓ.decayRate * ((_root_.YangMills.Construction.TorusFields.supDist y o - R - 2 : ℕ) : ℝ)) ≤ wt y := by
        rw [neg_mul]
        exact exp_le_weight hf hf₂ (by positivity) hm
      have a1 := g.levelShare_far hS hs hUr hUc hUc' t hy3
      have a2 := g.levelShare_far hS hs hSr hSc hSc' t hy3
      have b1 := g.siteDensity_far hexp ω hh hΦ hΦ' hy2.le
      have e : T y - H y = -x * (sh U y W' - sh U y W) + x * (sh S y W' - sh S y W) +
          (φ n y W' Y ω - φ n y W Y ω) - 0 := by
        simp only [T, H, if_neg hy]
      rw [e]
      have hnn : |(0 : ℝ)| ≤ wt y := by simpa using hw0
      have := abs_four_terms_le hx ((abs_sub_comm _ _).le.trans (a1.trans (mul_le_mul_of_nonneg_left he1 hA)))
        ((abs_sub_comm _ _).le.trans (a2.trans (mul_le_mul_of_nonneg_left he1 hA)))
        ((abs_sub_comm _ _).le.trans (b1.trans he2)) hnn
      calc _ ≤ _ := this
        _ = _ := by ring
  rw [hT, hM, ← Finset.sum_sub_distrib]
  have hC : 0 ≤ 2 * x * A + 2 := by positivity
  calc |∑ y, (T y - H y)| ≤ ∑ y, |T y - H y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, (2 * x * A + 2) * wt y := Finset.sum_le_sum fun y _ => hterm y
    _ = (2 * x * A + 2) * ((∑ y, Real.exp (-(f₀ / 8) * (_root_.YangMills.Construction.TorusFields.supDist y o : ℝ))) *
        Real.exp (-(f₀ * (5 * R / 16 - 2)))) := by
        rw [← Finset.mul_sum, Finset.sum_mul]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le) hC
        exact sum_exp_neg_mul_supDist_le (by positivity) o
end Sum
section Floors
open Filter
private theorem eventually_poly_le_exp {A K b : ℝ} (hb : 0 < b) :
    ∀ᶠ u : ℝ in atTop, (2 * u ^ 27 * A + 2) * K ≤ Real.exp (b * u) := by
  have ho := (isLittleO_pow_exp_pos_mul_atTop 28 hb).def (c := 1) one_pos
  filter_upwards [ho, eventually_ge_atTop (max 1 ((2 * |A| + 2) * |K|))] with u hu hu2
  have u1 : 1 ≤ u := le_trans (le_max_left _ _) hu2
  have uc : (2 * |A| + 2) * |K| ≤ u := le_trans (le_max_right _ _) hu2
  have p1 : 1 ≤ u ^ 27 := one_le_pow₀ u1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul, abs_of_nonneg (by positivity)] at hu
  have h1 : |2 * u ^ 27 * A + 2| ≤ u ^ 27 * (2 * |A| + 2) := by
    have h2 : |2 * u ^ 27 * A + 2| ≤ |2 * u ^ 27 * A| + |(2 : ℝ)| := abs_add_le _ _
    have h3 : |2 * u ^ 27 * A| = 2 * u ^ 27 * |A| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
    rw [h3, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
    nlinarith
  calc (2 * u ^ 27 * A + 2) * K ≤ |(2 * u ^ 27 * A + 2) * K| := le_abs_self _
    _ = |2 * u ^ 27 * A + 2| * |K| := abs_mul _ _
    _ ≤ (u ^ 27 * (2 * |A| + 2)) * |K| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = u ^ 27 * ((2 * |A| + 2) * |K|) := by ring
    _ ≤ u ^ 27 * u := mul_le_mul_of_nonneg_left uc (by positivity)
    _ = u ^ 28 := by ring
    _ ≤ _ := hu
private theorem eventually_radius_bounds {κ₀ C₁ σ A K B f₀ : ℝ} (N₀ : ℕ) (h1 : 1 / 27 ≤ κ₀) (h2 : κ₀ ≤ 1 / 21)
    (hσ : 0 < σ) (hf : 0 < f₀) :
    ∃ xs : ℝ, ∀ x : ℝ, xs ≤ x →
      0 ≤ x ∧ 1024 ≤ boxRadius κ₀ x ∧ C₁ * (boxRadius κ₀ x : ℝ) ^ 2 * boxScale x < σ ∧
      16 * (boxRadius κ₀ x : ℝ) < x ^ (1 / 10 : ℝ) ∧ B ≤ x ^ (1 / 10 : ℝ) ∧
      N₀ ≤ 8 * boxRadius κ₀ x ∧ clusterRange x ≤ boxRadius κ₀ x ∧ 2 ^ 12 ≤ 2 * clusterRange x ∧
      (2 * x * A + 2) * K ≤ Real.exp (f₀ * (boxRadius κ₀ x : ℝ) / 16) := by
  have t27 : Tendsto (fun x : ℝ => x ^ (1 / 27 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have E1 := eventually_ge_atTop (1 : ℝ)
  have E2 := t27.eventually_ge_atTop (max 1024 (N₀ : ℝ))
  have E3 : ∀ᶠ x : ℝ in atTop, 80 * |C₁| * x ^ (-(32 / 105 : ℝ)) < σ := by
    have h := (tendsto_rpow_neg_atTop (y := 32 / 105) (by norm_num)).const_mul (80 * |C₁|)
    rw [mul_zero] at h
    exact h.eventually_lt_const hσ
  have E4 := (tendsto_rpow_atTop (y := 11 / 210) (by norm_num)).eventually_ge_atTop (33 : ℝ)
  have E5 := (tendsto_rpow_atTop (y := 1 / 10) (by norm_num)).eventually_ge_atTop B
  have E6 := (tendsto_rpow_atTop (y := 1 / 100) (by norm_num)).eventually_ge_atTop (2 ^ 11 : ℝ)
  have E7 := t27.eventually (eventually_poly_le_exp (A := A) (K := K) (b := f₀ / 16) (by positivity))
  obtain ⟨xs, hxs⟩ := eventually_atTop.mp (E1.and (E2.and (E3.and (E4.and (E5.and (E6.and E7))))))
  refine ⟨xs, fun x hx => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hxs x hx
  have x0 : 0 < x := by linarith
  set R := boxRadius κ₀ x with hR
  have hlow : x ^ (1 / 27 : ℝ) ≤ x ^ κ₀ := Real.rpow_le_rpow_of_exponent_le e1 h1
  have hhigh : x ^ κ₀ ≤ x ^ (1 / 21 : ℝ) := Real.rpow_le_rpow_of_exponent_le e1 h2
  have hone : 1 ≤ x ^ (1 / 21 : ℝ) := Real.one_le_rpow e1 (by norm_num)
  have hR1 : x ^ (1 / 27 : ℝ) ≤ R := hlow.trans (Nat.le_ceil _)
  have hR2 : (R : ℝ) ≤ 2 * x ^ (1 / 21 : ℝ) := by
    have := Nat.ceil_lt_add_one (a := x ^ κ₀) (Real.rpow_nonneg x0.le _)
    have h3 : (R : ℝ) < x ^ κ₀ + 1 := this
    linarith
  have hbig : (1024 : ℝ) ≤ R := ((le_max_left _ _).trans e2).trans hR1
  have hNR : (N₀ : ℝ) ≤ R := ((le_max_right _ _).trans e2).trans hR1
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  refine ⟨x0.le, by exact_mod_cast hbig, ?_, ?_, e5, ?_, ?_, ?_, ?_⟩
  · have hlog0 : 0 ≤ Real.log x := Real.log_nonneg e1
    have hlog : Real.log x ≤ x ^ (1 / 10 : ℝ) / (1 / 10) := Real.log_le_rpow_div x0.le (by norm_num)
    have hm : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg x0.le _
    have hsz : boxScale x ≤ 20 * x ^ (-(2 / 5 : ℝ)) := by
      have k : x ^ (-(1 / 2 : ℝ)) * x ^ (1 / 10 : ℝ) = x ^ (-(2 / 5 : ℝ)) := by
        rw [← Real.rpow_add x0]
        norm_num
      unfold boxScale
      have k2 := mul_le_mul_of_nonneg_left hlog hm
      have k3 : x ^ (-(1 / 2 : ℝ)) * (x ^ (1 / 10 : ℝ) / (1 / 10)) = 10 * x ^ (-(2 / 5 : ℝ)) := by
        rw [← k]
        ring
      rw [k3] at k2
      nlinarith
    have hsz0 : 0 ≤ boxScale x := by
      unfold boxScale
      positivity
    have hsq : (R : ℝ) ^ 2 ≤ 4 * x ^ (2 / 21 : ℝ) := by
      have k : (x ^ (1 / 21 : ℝ)) ^ 2 = x ^ (2 / 21 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul x0.le]
        norm_num
      have k2 : (R : ℝ) ^ 2 ≤ (2 * x ^ (1 / 21 : ℝ)) ^ 2 := pow_le_pow_left₀ hR0 hR2 2
      rw [mul_pow, k] at k2
      linarith
    have hprod : x ^ (2 / 21 : ℝ) * x ^ (-(2 / 5 : ℝ)) = x ^ (-(32 / 105 : ℝ)) := by
      rw [← Real.rpow_add x0]
      norm_num
    have hq : (R : ℝ) ^ 2 * boxScale x ≤ 80 * x ^ (-(32 / 105 : ℝ)) := by
      calc (R : ℝ) ^ 2 * boxScale x ≤ (4 * x ^ (2 / 21 : ℝ)) * (20 * x ^ (-(2 / 5 : ℝ))) :=
            mul_le_mul hsq hsz hsz0 (by positivity)
        _ = 80 * (x ^ (2 / 21 : ℝ) * x ^ (-(2 / 5 : ℝ))) := by ring
        _ = _ := by rw [hprod]
    have hq0 : 0 ≤ (R : ℝ) ^ 2 * boxScale x := by positivity
    calc C₁ * (R : ℝ) ^ 2 * boxScale x = C₁ * ((R : ℝ) ^ 2 * boxScale x) := by ring
      _ ≤ |C₁| * ((R : ℝ) ^ 2 * boxScale x) := mul_le_mul_of_nonneg_right (le_abs_self _) hq0
      _ ≤ |C₁| * (80 * x ^ (-(32 / 105 : ℝ))) := mul_le_mul_of_nonneg_left hq (abs_nonneg _)
      _ = 80 * |C₁| * x ^ (-(32 / 105 : ℝ)) := by ring
      _ < σ := e3
  · have k : x ^ (1 / 21 : ℝ) * x ^ (11 / 210 : ℝ) = x ^ (1 / 10 : ℝ) := by
      rw [← Real.rpow_add x0]
      norm_num
    rw [← k]
    nlinarith
  · have : N₀ ≤ R := by exact_mod_cast hNR
    omega
  · exact Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le e1 (by linarith))
  · have k : (2 ^ 11 : ℝ) ≤ clusterRange x := e6.trans (Nat.le_ceil _)
    have k2 : 2 ^ 11 ≤ clusterRange x := by exact_mod_cast k
    omega
  · have hu : (x ^ (1 / 27 : ℝ)) ^ 27 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul x0.le]
      norm_num
    rw [hu] at e7
    refine e7.trans (Real.exp_le_exp.mpr ?_)
    have := mul_le_mul_of_nonneg_left hR1 hf.le
    linarith
end Floors
private theorem depth_stage {ℓ : StepParameters} (T : StageTower ℓ) (h : T.base.depth = 0) :
    ∀ k, (T.stage k).depth = k
  | 0 => h
  | k + 1 => by
    show (T.stage k).depth + 1 = k + 1
    rw [depth_stage T h k]
end ConditionalDensity
theorem conditionalDensity_holds (hS : ShareLocalityExists) (hreg : OffHotRegionIsRegular)
    (hadd : SharesSumToAction) : conditionalDensityStatement := by
  unfold conditionalDensityStatement HoldsAtAdmissibleParameters
  intro a ha
  refine ⟨0, fun _ => 1, fun _ => one_pos, fun L hL _ Tb hTa hTL hD _ => ?_⟩
  refine ⟨Tb.floorMin, fun y hy _ _ κ₀ h1 h2 C₁ => ?_⟩
  have hadm : (Tb.stepParameters y).Admissible := hD.fits y hy
  obtain ⟨A, hA, hSR⟩ := hS Tb.coupling Tb.δ₁ Tb.side Tb.lam Tb.ρA Tb.σA Tb.cg Tb.N (by have := hD.a_ge; linarith)
    hD.L_odd hD.chain
  have hdecay : 0 < (Tb.stepParameters y).decayRate := by
    unfold StepParameters.decayRate
    have := hadm.rt_pos
    positivity
  set f₀ := min Tb.δ₁ (Tb.stepParameters y).decayRate with hf₀
  have hfpos : 0 < f₀ := lt_min hD.δ₁_pos hdecay
  set K₀ := (2 / (1 - Real.exp (-(f₀ / 8) / 4))) ^ 4 with hK₀
  obtain ⟨xs, hxs⟩ := ConditionalDensity.eventually_radius_bounds (C₁ := C₁) (σ := (Tb.stepParameters y).threshold)
    (A := A) (K := K₀ * Real.exp (2 * f₀))
    (B := max 3 (((Tb.stepParameters y).side : ℝ) * ((Tb.stepParameters y).n₀ : ℝ))) (f₀ := f₀)
    (Tb.stepParameters y).n₀ h1 h2 hadm.σ_pos hfpos
  refine ⟨f₀ / 4, xs, by positivity, ?_⟩
  intro T β k n _ o x R hbox hxk hRk W W' Y ω hout hY hc hc' hh hp
  have hx0 : xs ≤ x := hxk ▸ hbox.le_coupling
  have fl := hxs x hx0
  rw [← hRk] at fl
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := fl
  have hn : x ^ (1 / 10 : ℝ) ≤ n := hxk ▸ hbox.coupling_rpow_le
  have hn3 : (3 : ℝ) ≤ n := ((le_max_left _ _).trans c4).trans hn
  have hn3' : 3 ≤ n := by exact_mod_cast hn3
  have hblock : IsBlockTorusSide (Tb.stepParameters y) n := by
    refine ⟨?_, ?_⟩
    · obtain ⟨e, he⟩ := hbox.side_eq
      cases e with
      | zero =>
        simp at he
        omega
      | succ e =>
        rw [he, pow_succ]
        exact Dvd.intro_left (2 * (Tb.stepParameters y).side ^ e) (by ring)
    · have : (((Tb.stepParameters y).side : ℝ) * ((Tb.stepParameters y).n₀ : ℝ)) ≤ n :=
        ((le_max_right _ _).trans c4).trans hn
      exact_mod_cast this
  have hwide : 16 * R < n := by
    have : (16 : ℝ) * (R : ℝ) < n := c3.trans_le hn
    exact_mod_cast this
  have g : ConditionalDensity.OuterPair (Tb.stepParameters y) x o R W W' Y :=
    { admissible := hadm, blockSide := hblock, large := c1, wide := hwide, floor := c5, range := c6,
      reach := c7, outer := hout, far := hY, cold := fun p hp => (hc p hp).trans_lt c2,
      cold' := fun p hp => (hc' p hp).trans_lt c2 }
  have hst := hbox.onFamily.onFamily k (Nat.le_add_right _ _)
  have htk : (T.stage k).depth = k := ConditionalDensity.depth_stage T hbox.onFamily.startsAtWilson.depth_eq k
  have hxl : (T.stage k).coupling = x := (hbox.onFamily.coupling_eq k (by omega)).trans hxk.symm
  have hexp : HullExpansion (Tb.stepParameters y) k x (T.stage k).functional (T.stage k).density
      (T.stage k).labels (T.stage k).labelWeight (T.stage k).clusterFactor (T.stage k).siteDensity := by
    have h0 : HullExpansion (Tb.stepParameters y) (T.stage k).depth (T.stage k).coupling (T.stage k).functional
        (T.stage k).density (T.stage k).labels (T.stage k).labelWeight (T.stage k).clusterFactor
        (T.stage k).siteDensity := hst.isStep.1.2
    rwa [htk, hxl] at h0
  have hσA : (Tb.stepParameters y).threshold ≤ Tb.σA := by
    have e1 := hD.σ_le
    have e2 := hD.σ_pos
    show Tb.threshold ≤ Tb.σA
    linarith
  obtain ⟨r1, r2, r3⟩ := g.logRatio_bound hreg hadd hSR hσA hA.le hexp hfpos (min_le_left _ _) (min_le_right _ _)
    c0 ω hh hp
  refine ⟨r1, r2, r3.trans ?_⟩
  have e1 : Real.exp (-(f₀ * (5 * R / 16 - 2))) = Real.exp (2 * f₀) * Real.exp (-(5 * f₀ * R / 16)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e2 : Real.exp (-(f₀ / 4 * R)) = Real.exp (f₀ * R / 16) * Real.exp (-(5 * f₀ * R / 16)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e1, e2]
  calc (2 * x * A + 2) * (K₀ * (Real.exp (2 * f₀) * Real.exp (-(5 * f₀ * R / 16))))
      = ((2 * x * A + 2) * (K₀ * Real.exp (2 * f₀))) * Real.exp (-(5 * f₀ * R / 16)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right c8 (Real.exp_pos _).le
end BoxEvents
end YangMills.Construction
end
