import YangMills.Construction.Lattice.ComponentBoxIndependentOfCube
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ComponentBox
variable {L m : ℕ}
theorem mem_cornerCube_iff {y v : Fin 4 → ℝ} {t : ℝ} :
    v ∈ cornerCube y t ↔ ∀ μ, v μ ∈ Icc (y μ) (y μ + t) :=
  ⟨fun h μ => h μ (mem_univ μ), fun h μ _ => h μ⟩
theorem mem_boxOfIntervals_iff {a b v : Fin 4 → ℝ} :
    v ∈ TorusBox.boxOfIntervals a b ↔ ∀ μ, a μ ≤ v μ ∧ v μ ≤ b μ :=
  ⟨fun h μ => h μ (mem_univ μ), fun h μ _ => h μ⟩
theorem mem_boundingBox_iff {A : Set (Fin 4 → ℝ)} {x : Fin 4 → ℝ} :
    x ∈ boundingBox A ↔
      ∀ a b, A ⊆ TorusBox.boxOfIntervals a b → x ∈ TorusBox.boxOfIntervals a b :=
  ⟨fun h a b hA => h _ ⟨hA, a, b, rfl⟩, fun h P hP => by
    obtain ⟨hA, a, b, rfl⟩ := hP
    exact h a b hA⟩
theorem int_eq_zero_of_sub_eq_mul {S T p a b : ℝ} {d : ℤ} (hS : 0 < S) (hT : T < S)
    (ha : a ∈ Icc p (p + T)) (hb : b ∈ Icc p (p + T)) (h : b - a = d * S) : d = 0 := by
  by_contra hd
  have h1 : S ≤ |(d : ℝ) * S| := by
    rw [abs_mul, abs_of_pos hS]
    have h2 : (1 : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast Int.one_le_abs hd
    nlinarith
  rw [← h] at h1
  have h3 : |b - a| ≤ T := by
    rw [abs_le]
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  linarith
theorem exists_int_sub_eq_mul_of_coe_eq {S a b : ℝ} (h : (a : AddCircle S) = b) :
    ∃ d : ℤ, b - a = d * S := by
  have h0 : ((b - a : ℝ) : AddCircle S) = 0 := by rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff S).1 h0
  exact ⟨n, by rw [← hn]; simp⟩
theorem torusProj_add_period {w : Fin 4 → ℝ} (hw : IsTorusPeriod L m w) (v : Fin 4 → ℝ) :
    torusProj (torusSide L m) (v + w) = torusProj (torusSide L m) v := by
  obtain ⟨n, hn⟩ := hw
  funext μ
  have h0 : (((n μ : ℝ) * torusSide L m : ℝ) : AddCircle (torusSide L m)) = 0 :=
    (AddCircle.coe_eq_zero_iff _).2 ⟨n μ, by simp⟩
  simp only [torusProj, Pi.add_apply, hn μ]
  rw [AddCircle.coe_add, h0, add_zero]
theorem injOn_torusProj_cornerCube {S t : ℝ} (hS : 0 < S) (ht : t < S) (y : Fin 4 → ℝ) :
    InjOn (torusProj S) (cornerCube y t) := by
  intro a ha b hb hab
  funext μ
  obtain ⟨d, hd⟩ := exists_int_sub_eq_mul_of_coe_eq (S := S) (a := a μ) (b := b μ) (congrFun hab μ)
  have hd0 := int_eq_zero_of_sub_eq_mul hS ht (mem_cornerCube_iff.1 ha μ) (mem_cornerCube_iff.1 hb μ) hd
  rw [hd0] at hd
  simp only [Int.cast_zero, zero_mul] at hd
  linarith
theorem exists_int_interval_shift {S T p a b : ℝ} (hT : T < S) (hab : a ≤ b) (hS : 0 < S)
    (h : ∀ t ∈ Icc a b, ∃ k : ℤ, t + k * S ∈ Icc p (p + T)) :
    ∃ k : ℤ, ∀ t ∈ Icc a b, t + k * S ∈ Icc p (p + T) := by
  obtain ⟨k, hk⟩ := h a ⟨le_rfl, hab⟩
  refine ⟨k, fun t ht => ⟨by linarith [hk.1, ht.1], ?_⟩⟩
  by_contra hlt
  obtain ⟨δ, hδ0, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ (S - T) / 2 ∧ δ ≤ t + k * S - (p + T) :=
    ⟨min ((S - T) / 2) (t + k * S - (p + T)), lt_min (by linarith) (by linarith),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨k', hk'⟩ := h (p + T + δ - k * S) ⟨by linarith [hk.2], by linarith [ht.2]⟩
  have e : p + T + δ - k * S + k' * S = p + T + δ + ((k' - k : ℤ) : ℝ) * S := by
    push_cast
    ring
  rw [e] at hk'
  have hneg : ((k' - k : ℤ) : ℝ) * S < 0 := by linarith [hk'.2]
  have hd : ((k' - k : ℤ) : ℝ) ≤ -1 := by
    have h1 : k' - k < 0 := by
      by_contra hh
      have h2 : (0 : ℝ) ≤ ((k' - k : ℤ) : ℝ) := by exact_mod_cast not_lt.1 hh
      nlinarith
    have h3 : k' - k ≤ -1 := by omega
    exact_mod_cast h3
  nlinarith [hk'.1]
theorem supNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ supNormVec v :=
  (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
theorem torusProj_mem_cubeAround {i : ℤ} (z : Site L m i) {zt u : Fin 4 → ℝ}
    (hz : torusProj (torusSide L m) zt = (z : FourTorus L m))
    (hu : ∀ μ, |u μ - zt μ| ≤ meshSize L i / 2) :
    torusProj (torusSide L m) u ∈ cubeAround z := by
  show torusSupNorm (torusProj (torusSide L m) u - (z : FourTorus L m)) ≤ meshSize L i / 2
  have hle : torusSupNorm (torusProj (torusSide L m) u - (z : FourTorus L m)) ≤
      supNormVec (u - zt) := by
    refine csInf_le ⟨0, ?_⟩ ⟨u - zt, ?_, rfl⟩
    · rintro _ ⟨v, -, rfl⟩
      exact supNormVec_nonneg v
    · show torusProj (torusSide L m) (u - zt) = torusProj (torusSide L m) u - (z : FourTorus L m)
      rw [← hz]
      funext μ
      simp [torusProj]
  exact hle.trans (Finset.sup'_le _ _ fun μ _ => hu μ)
theorem exists_int_shift_of_mem_cubeAround {i : ℤ} (z : Site L m i) {zt v : Fin 4 → ℝ}
    (hz : torusProj (torusSide L m) zt = (z : FourTorus L m))
    (hv : torusProj (torusSide L m) v ∈ cubeAround z) :
    ∃ n : Fin 4 → ℤ, ∀ μ, |v μ + n μ * torusSide L m - zt μ| ≤ meshSize L i / 2 := by
  have hv' : torusSupNorm (torusProj (torusSide L m) v - (z : FourTorus L m)) ≤
      meshSize L i / 2 := hv
  set x : FourTorus L m := torusProj (torusSide L m) v - (z : FourTorus L m) with hx
  have hnorm : ∀ μ, ‖x μ‖ ≤ torusSupNorm x := by
    intro μ
    choose b₀ hb₀ _ using fun ν => exists_coe_eq_abs_eq_norm (x ν)
    have h₀ : torusProj (torusSide L m) b₀ = x := funext hb₀
    refine le_csInf ⟨_, b₀, h₀, rfl⟩ ?_
    rintro _ ⟨u, hu, rfl⟩
    have hu' : torusProj (torusSide L m) u = x := hu
    rw [← hu']
    exact (addCircle_norm_coe_le_abs _).trans
      (Finset.le_sup' (fun μ => |u μ|) (Finset.mem_univ μ))
  have hcoord : ∀ μ, ∃ n : ℤ, |v μ + n * torusSide L m - zt μ| ≤ meshSize L i / 2 := by
    intro μ
    obtain ⟨b, hb, hb'⟩ := exists_coe_eq_abs_eq_norm (x μ)
    have he : ((v μ - zt μ : ℝ) : AddCircle (torusSide L m)) = (b : AddCircle (torusSide L m)) := by
      rw [hb, hx, ← hz, AddCircle.coe_sub]
      rfl
    obtain ⟨d, hd⟩ := exists_int_sub_eq_mul_of_coe_eq he
    refine ⟨d, ?_⟩
    have e : v μ + d * torusSide L m - zt μ = b := by linarith
    rw [e, hb']
    exact (hnorm μ).trans hv'
  choose n hn using hcoord
  exact ⟨n, hn⟩
theorem exists_int_cube_shift {i : ℤ} (hW : 0 < meshSize L i) {t : ℝ} (hS : 0 < torusSide L m)
    (ht : t < torusSide L m) (z : Site L m i) {zt y : Fin 4 → ℝ}
    (hz : torusProj (torusSide L m) zt = (z : FourTorus L m))
    (h : cubeAround z ⊆ torusProj (torusSide L m) '' cornerCube y t) :
    ∃ k : Fin 4 → ℤ, ∀ μ, ∀ τ ∈ Icc (zt μ - meshSize L i / 2) (zt μ + meshSize L i / 2),
      τ + k μ * torusSide L m ∈ Icc (y μ) (y μ + t) := by
  have hcoord : ∀ μ, ∃ k : ℤ, ∀ τ ∈ Icc (zt μ - meshSize L i / 2) (zt μ + meshSize L i / 2),
      τ + k * torusSide L m ∈ Icc (y μ) (y μ + t) := by
    intro μ
    refine exists_int_interval_shift ht (by linarith) hS fun τ hτ => ?_
    have hu : torusProj (torusSide L m) (Function.update zt μ τ) ∈ cubeAround z := by
      refine torusProj_mem_cubeAround z hz fun ν => ?_
      by_cases hν : ν = μ
      · subst hν
        rw [Function.update_self, abs_le]
        constructor <;> linarith [hτ.1, hτ.2]
      · rw [Function.update_of_ne hν, sub_self, abs_zero]
        linarith
    obtain ⟨v, hv, hvu⟩ := h hu
    obtain ⟨d, hd⟩ := exists_int_sub_eq_mul_of_coe_eq (S := torusSide L m) (a := v μ)
      (b := Function.update zt μ τ μ) (congrFun hvu μ)
    rw [Function.update_self] at hd
    refine ⟨-d, ?_⟩
    have e : τ + ((-d : ℤ) : ℝ) * torusSide L m = v μ := by
      push_cast
      linarith
    rw [e]
    exact mem_cornerCube_iff.1 hv μ
  choose k hk using hcoord
  exact ⟨k, hk⟩
theorem exists_period_of_cubeAround {i : ℤ} (hW : 0 < meshSize L i) {t : ℝ}
    (hS : 0 < torusSide L m) (ht : t < torusSide L m) (z : Site L m i) {y y' : Fin 4 → ℝ}
    (h : cubeAround z ⊆ torusProj (torusSide L m) '' cornerCube y t)
    (h' : cubeAround z ⊆ torusProj (torusSide L m) '' cornerCube y' t) :
    ∃ w, IsTorusPeriod L m w ∧
      ∀ v ∈ cornerCube y t, torusProj (torusSide L m) v ∈ cubeAround z →
        v + w ∈ cornerCube y' t := by
  choose zt hzt _ using fun μ => exists_coe_eq_abs_eq_norm ((z : FourTorus L m) μ)
  have hz : torusProj (torusSide L m) zt = (z : FourTorus L m) := funext hzt
  obtain ⟨k, hk⟩ := exists_int_cube_shift hW hS ht z hz h
  obtain ⟨k', hk'⟩ := exists_int_cube_shift hW hS ht z hz h'
  refine ⟨fun μ => ((k' μ - k μ : ℤ) : ℝ) * torusSide L m, ⟨fun μ => k' μ - k μ, fun μ => rfl⟩,
    fun v hv hvz => ?_⟩
  obtain ⟨n, hn⟩ := exists_int_shift_of_mem_cubeAround z hz hvz
  refine mem_cornerCube_iff.2 fun μ => ?_
  have hτ : v μ + n μ * torusSide L m ∈
      Icc (zt μ - meshSize L i / 2) (zt μ + meshSize L i / 2) := by
    have hab := abs_le.1 (hn μ)
    constructor <;> linarith [hab.1, hab.2]
  have h0 : n μ + k μ = 0 :=
    int_eq_zero_of_sub_eq_mul hS ht (mem_cornerCube_iff.1 hv μ) (hk μ _ hτ) (by push_cast; ring)
  have h1 : (n μ : ℝ) = -(k μ : ℝ) := by
    have h2 : ((n μ + k μ : ℤ) : ℝ) = 0 := by rw [h0]; simp
    push_cast at h2
    linarith
  have e : (v + fun μ => ((k' μ - k μ : ℤ) : ℝ) * torusSide L m) μ =
      v μ + n μ * torusSide L m + k' μ * torusSide L m := by
    simp only [Pi.add_apply]
    push_cast
    rw [h1]
    ring
  rw [e]
  exact hk' μ _ hτ
theorem boundingBox_translateSet (w : Fin 4 → ℝ) (A : Set (Fin 4 → ℝ)) :
    boundingBox (shiftByVector w A) = shiftByVector w (boundingBox A) := by
  ext x
  constructor
  · intro hx
    refine ⟨x - w, mem_boundingBox_iff.2 fun a b hA => ?_, by simp⟩
    have hmem : x ∈ TorusBox.boxOfIntervals (a + w) (b + w) := by
      refine mem_boundingBox_iff.1 hx _ _ ?_
      rintro _ ⟨v, hv, rfl⟩
      have hv' := mem_boxOfIntervals_iff.1 (hA hv)
      refine mem_boxOfIntervals_iff.2 fun μ => ?_
      simp only [Pi.add_apply]
      constructor <;> linarith [(hv' μ).1, (hv' μ).2]
    have hx' := mem_boxOfIntervals_iff.1 hmem
    refine mem_boxOfIntervals_iff.2 fun μ => ?_
    have h1 := (hx' μ).1
    have h2 := (hx' μ).2
    simp only [Pi.add_apply] at h1 h2
    simp only [Pi.sub_apply]
    constructor <;> linarith
  · rintro ⟨v, hv, rfl⟩
    refine mem_boundingBox_iff.2 fun a b hA => ?_
    have hmem : v ∈ TorusBox.boxOfIntervals (a - w) (b - w) := by
      refine mem_boundingBox_iff.1 hv _ _ fun u hu => ?_
      have hu' := mem_boxOfIntervals_iff.1 (hA ⟨u, hu, rfl⟩)
      refine mem_boxOfIntervals_iff.2 fun μ => ?_
      have h1 := (hu' μ).1
      have h2 := (hu' μ).2
      simp only [Pi.add_apply] at h1 h2
      simp only [Pi.sub_apply]
      constructor <;> linarith
    have hv' := mem_boxOfIntervals_iff.1 hmem
    refine mem_boxOfIntervals_iff.2 fun μ => ?_
    have h1 := (hv' μ).1
    have h2 := (hv' μ).2
    simp only [Pi.sub_apply] at h1 h2
    simp only [Pi.add_apply]
    constructor <;> linarith
theorem image_translateSet {w : Fin 4 → ℝ} (hw : IsTorusPeriod L m w) (A : Set (Fin 4 → ℝ)) :
    torusProj (torusSide L m) '' shiftByVector w A = torusProj (torusSide L m) '' A := by
  ext x
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, (torusProj_add_period hw v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v + w, ⟨v, hv, rfl⟩, torusProj_add_period hw v⟩
theorem exists_period_liftToCornerCube {i : ℤ} (hW : 0 < meshSize L i) (hS : 0 < torusSide L m)
    (ht : 100 * meshSize L i < torusSide L m) {X C : Set (FourTorus L m)}
    (hC : C ∈ regionComponents i X) {y y' : Fin 4 → ℝ}
    (hy : LiesInCornerCube L m i C y) (hy' : LiesInCornerCube L m i C y') :
    ∃ w, IsTorusPeriod L m w ∧ liftToCornerCube i C y' = shiftByVector w (liftToCornerCube i C y) := by
  obtain ⟨Q₀, hQ₀, hCQ⟩ := hC
  have hy₁ : C ⊆ torusProj (torusSide L m) '' cornerCube y (100 * meshSize L i) := hy
  have hy₂ : C ⊆ torusProj (torusSide L m) '' cornerCube y' (100 * meshSize L i) := hy'
  let Moves (B : Set (FourTorus L m)) (w : Fin 4 → ℝ) : Prop :=
    ∀ v ∈ cornerCube y (100 * meshSize L i), torusProj (torusSide L m) v ∈ B →
      v + w ∈ cornerCube y' (100 * meshSize L i)
  have sub : ∀ B, ChainConnectedIn i X Q₀ B → B ⊆ C := fun B hB => by
    rw [hCQ]
    exact subset_sUnion_of_mem (show B ∈ {Q' | ChainConnectedIn i X Q₀ Q'} from hB)
  have ex : ∀ B, ChainConnectedIn i X Q₀ B → ∃ w, IsTorusPeriod L m w ∧ Moves B w := by
    intro B hB
    obtain ⟨c, hc, -, hl⟩ := id hB
    obtain ⟨⟨z, rfl⟩, -⟩ := hc.1 B (List.mem_of_getLast? hl)
    exact exists_period_of_cubeAround hW hS ht z ((sub _ hB).trans hy₁) ((sub _ hB).trans hy₂)
  have injQ' := injOn_torusProj_cornerCube hS ht y'
  have uniq : ∀ A B wA wB, IsTorusPeriod L m wA → IsTorusPeriod L m wB → Moves A wA →
      Moves B wB → A ⊆ C → (A ∩ B).Nonempty → wA = wB := by
    rintro A B wA wB pA pB mA mB hAC ⟨x, hxA, hxB⟩
    obtain ⟨v, hv, rfl⟩ := hy₁ (hAC hxA)
    exact add_left_cancel (injQ' (mA v hv hxA) (mB v hv hxB)
      ((torusProj_add_period pA v).trans (torusProj_add_period pB v).symm))
  have connectedSelf : ChainConnectedIn i X Q₀ Q₀ :=
    ⟨[Q₀], ⟨by simpa using hQ₀, by simp⟩, rfl, rfl⟩
  obtain ⟨w, hw, hR⟩ := ex Q₀ connectedSelf
  have all : ∀ c, IsCubeChainIn i X c → c.head? = some Q₀ → ∀ B, c.getLast? = some B →
      Moves B w := by
    intro c
    induction c using List.reverseRecOn with
    | nil => simp
    | append_singleton c' A ih =>
      intro hc hh B hl
      have hAB : A = B := by simpa using hl
      subst hAB
      by_cases hne : c' = []
      · subst hne
        have hAQ : A = Q₀ := by simpa using hh
        rw [hAQ]
        exact hR
      · obtain ⟨A', hA'⟩ : ∃ A', c'.getLast? = some A' := by
          cases hg : c'.getLast? with
          | some a => exact ⟨a, rfl⟩
          | none => exact absurd (List.getLast?_eq_none_iff.1 hg) hne
        have hcc : IsCubeChainIn i X c' :=
          ⟨fun Q hQ => hc.1 Q (List.mem_append_left _ hQ), hc.2.left_of_append⟩
        have hh' : c'.head? = some Q₀ := by
          rw [← hh, List.head?_append_of_ne_nil _ hne]
        have hRA' := ih hcc hh' A' hA'
        have touch : CubesMeet A' A :=
          (List.isChain_append.1 hc.2).2.2 A' hA' A (by simp)
        obtain ⟨wA, hwA, hRA⟩ := ex A ⟨c' ++ [A], hc, hh, by simp⟩
        have hww : w = wA := uniq A' A w wA hw hwA hRA' hRA (sub _ ⟨c', hcc, hh', hA'⟩) touch
        rw [hww]
        exact hRA
  have forward : ∀ v ∈ cornerCube y (100 * meshSize L i), torusProj (torusSide L m) v ∈ C →
      v + w ∈ cornerCube y' (100 * meshSize L i) := by
    intro v hv hvC
    rw [hCQ] at hvC
    obtain ⟨B, hB, hvB⟩ := hvC
    obtain ⟨c, hc, hh, hl⟩ := id hB
    exact all c hc hh B hl v hv hvB
  refine ⟨w, hw, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hxC⟩
    obtain ⟨v, hv, hvx⟩ := hy₁ hxC
    have hvC : torusProj (torusSide L m) v ∈ C := by rw [hvx]; exact hxC
    refine ⟨v, ⟨hv, hvC⟩, ?_⟩
    exact injQ' (forward v hv hvC) hx ((torusProj_add_period hw v).trans hvx)
  · rintro ⟨v, ⟨hv, hvC⟩, rfl⟩
    refine ⟨forward v hv hvC, ?_⟩
    rw [torusProj_add_period hw v]
    exact hvC
theorem componentBoxIndependentOfCube_holds : ComponentBoxIndependentOfCube := by
  intro L m _ hL _ i _ hlt X C _ hC y y' hy hy'
  have hW : 0 < meshSize L i :=
    zpow_pos (by exact_mod_cast (by omega : 0 < L)) _
  have hS : 0 < torusSide L m := by linarith
  have image_eq : ∀ {u u' : Fin 4 → ℝ}, LiesInCornerCube L m i C u →
      LiesInCornerCube L m i C u' →
      torusProj (torusSide L m) '' boundingBox (liftToCornerCube i C u') =
        torusProj (torusSide L m) '' boundingBox (liftToCornerCube i C u) := by
    intro u u' hu hu'
    obtain ⟨w, hw, hl⟩ := exists_period_liftToCornerCube hW hS hlt hC hu hu'
    rw [hl, boundingBox_translateSet]
    exact image_translateSet hw _
  obtain ⟨w, hw, hl⟩ := exists_period_liftToCornerCube hW hS hlt hC hy hy'
  refine ⟨injOn_torusProj_cornerCube hS hlt y, injOn_torusProj_cornerCube hS hlt y',
    ⟨w, hw, hl, by rw [hl, boundingBox_translateSet]⟩, image_eq hy hy', ?_⟩
  exact image_eq hy (Classical.epsilon_spec (⟨y, hy⟩ : ∃ u, LiesInCornerCube L m i C u))
end YangMills.Construction.PeriodicLattice.ComponentBox
