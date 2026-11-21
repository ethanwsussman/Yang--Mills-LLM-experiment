import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.PeriodicOperators.WaveSpacesOnATorus
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.PeriodicOperators.BlochDecomposition
open InfiniteLattice (AmbientSpace)
open RiemannSums (DualClasses periodLattice)
open Quotients (WeightFactorsThroughQuot PairingNormFiniteSum)
variable {I : PeriodicData}
def latticePhase (κ : AmbientSpace) (m : Fin 4 → ℤ) : ℂ :=
  Complex.exp (Complex.I * bilinDot (toComplexVec κ) (toComplexVec (castVec m)))
theorem bilinDot_add_right (κ : Fin 4 → ℂ) (x y : AmbientSpace) :
    bilinDot κ (toComplexVec (x + y)) = bilinDot κ (toComplexVec x) + bilinDot κ (toComplexVec y) := by
  simp [bilinDot, toComplexVec, mul_add, Finset.sum_add_distrib]
theorem bilinDot_sub_left (κ κ' : AmbientSpace) (y : Fin 4 → ℂ) :
    bilinDot (toComplexVec (κ - κ')) y = bilinDot (toComplexVec κ) y - bilinDot (toComplexVec κ') y := by
  simp [bilinDot, toComplexVec, sub_mul, Finset.sum_sub_distrib]
theorem mkQuot_one_translate (ι : I.Carrier) (m : Fin 4 → ℤ) :
    I.mkQuot 1 (I.translate m ι) = I.mkQuot 1 ι :=
  (Quot.sound ⟨m, by rw [one_smul]⟩).symm
theorem blochWave_translate (h : IsPeriodic I) (κ : AmbientSpace) (φ : I.UnitQuot → ℂ)
    (m : Fin 4 → ℤ) (ι : I.Carrier) :
    blochWave I (toComplexVec κ) φ (I.translate m ι) =
      latticePhase κ m * blochWave I (toComplexVec κ) φ ι := by
  unfold blochWave latticePhase
  rw [h.pos_translate, mkQuot_one_translate, bilinDot_add_right, mul_add, Complex.exp_add]
  ring
theorem latticePhase_eq_one (κ : AmbientSpace) (m k : Fin 4 → ℤ)
    (hk : ∀ μ, κ μ * (m μ : ℝ) = (k μ : ℝ) * (2 * Real.pi)) : latticePhase κ m = 1 := by
  rw [latticePhase, Complex.exp_eq_one_iff]
  refine ⟨∑ μ, k μ, ?_⟩
  have hk' : ∀ μ, (κ μ : ℂ) * (m μ : ℂ) = (k μ : ℂ) * (2 * Real.pi) := fun μ => by
    have := congrArg (fun t : ℝ => (t : ℂ)) (hk μ)
    simpa using this
  simp only [bilinDot, toComplexVec, castVec, Complex.ofReal_intCast, hk']
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun μ _ => by ring
theorem latticePhase_of_mem_dualLattice {s : ℕ} (hs : 0 < s) {κ : AmbientSpace}
    (hκ : κ ∈ dualLattice s) (n : Fin 4 → ℤ) : latticePhase κ (s • n) = 1 := by
  obtain ⟨k, hk⟩ := hκ
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  refine latticePhase_eq_one κ _ (fun μ => k μ * n μ) fun μ => ?_
  rw [hk μ]
  simp only [Pi.smul_apply, nsmul_eq_mul]
  push_cast
  field_simp
theorem latticePhase_of_mem_periodLattice {κ : AmbientSpace} (hκ : κ ∈ periodLattice)
    (m : Fin 4 → ℤ) : latticePhase κ m = 1 := by
  obtain ⟨k, hk⟩ := hκ
  refine latticePhase_eq_one κ _ (fun μ => k μ * m μ) fun μ => ?_
  rw [hk μ]
  push_cast
  ring
theorem conj_latticePhase_mul (κ κ' : AmbientSpace) (m : Fin 4 → ℤ) :
    conj (latticePhase κ m) * latticePhase κ' m = latticePhase (κ' - κ) m := by
  have hr : ∀ (a : AmbientSpace) (y : AmbientSpace), bilinDot (toComplexVec a) (toComplexVec y) =
      ((∑ μ, a μ * y μ : ℝ) : ℂ) := fun a y => by
    simp [bilinDot, toComplexVec]
  unfold latticePhase
  rw [← Complex.exp_conj, ← Complex.exp_add, bilinDot_sub_left, hr κ, hr κ']
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring
def blochMap (h : IsPeriodic I) {s : ℕ} (hs : 0 < s) {κ : AmbientSpace} (hκ : κ ∈ dualLattice s) :
    (I.UnitQuot → ℂ) →ₗ[ℂ] (I.QuotMod s → ℂ) where
  toFun := fun φ => Quot.lift (blochWave I (toComplexVec κ) φ) (by
    rintro ι _ ⟨n, rfl⟩
    rw [blochWave_translate h, latticePhase_of_mem_dualLattice hs hκ, one_mul])
  map_add' := fun φ φ' => by
    funext c
    induction c using Quot.ind with
    | mk ι =>
      change blochWave I _ (φ + φ') ι = blochWave I _ φ ι + blochWave I _ φ' ι
      simp [blochWave, mul_add]
  map_smul' := fun z φ => by
    funext c
    induction c using Quot.ind with
    | mk ι =>
      change blochWave I _ (z • φ) ι = z * blochWave I _ φ ι
      simp only [blochWave, Pi.smul_apply, smul_eq_mul]
      ring
theorem blochMap_mkQuot (h : IsPeriodic I) {s : ℕ} (hs : 0 < s) {κ : AmbientSpace}
    (hκ : κ ∈ dualLattice s) (φ : I.UnitQuot → ℂ) (ι : I.Carrier) :
    blochMap h hs hκ φ (I.mkQuot s ι) = blochWave I (toComplexVec κ) φ ι := rfl
theorem blochMap_mem (h : IsPeriodic I) {s : ℕ} (hs : 0 < s) {κ : AmbientSpace}
    (hκ : κ ∈ dualLattice s) (φ : I.UnitQuot → ℂ) : blochMap h hs hκ φ ∈ blochWaveSubspace I s κ :=
  ⟨φ, fun ι => blochMap_mkQuot h hs hκ φ ι⟩
theorem eq_zero_of_blochWave_eq_zero (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ)
    (H : ∀ ι, blochWave I κ φ ι = 0) : φ = 0 := by
  funext c
  induction c using Quot.ind with
  | mk ι =>
    have := H ι
    simp only [blochWave] at this
    exact (mul_eq_zero.1 this).resolve_left (Complex.exp_ne_zero _)
theorem eq_zero_of_blochMap_eq_zero (h : IsPeriodic I) {s : ℕ} (hs : 0 < s) {κ : AmbientSpace}
    (hκ : κ ∈ dualLattice s) (φ : I.UnitQuot → ℂ) (H : blochMap h hs hκ φ = 0) : φ = 0 :=
  eq_zero_of_blochWave_eq_zero _ φ fun ι => by
    rw [← blochMap_mkQuot h hs hκ, H]
    rfl
theorem blochWaveSubspace_le (h : IsPeriodic I) (s : ℕ) {κ κ' : AmbientSpace}
    (hp : κ - κ' ∈ periodLattice) :
    blochWaveSubspace I s κ ≤ blochWaveSubspace I s κ' := by
  rintro g ⟨φ, hφ⟩
  let e : I.Carrier → ℂ := fun ι =>
    Complex.exp (Complex.I * bilinDot (toComplexVec (κ - κ')) (toComplexVec (I.pos ι))) *
      φ (I.mkQuot 1 ι)
  have he : ∀ a b : I.Carrier, (∃ n : Fin 4 → ℤ, b = I.translate (1 • n) a) → e a = e b := by
    rintro a _ ⟨n, rfl⟩
    have := blochWave_translate h (κ - κ') φ (1 • n) a
    rw [latticePhase_of_mem_periodLattice hp, one_mul] at this
    exact this.symm
  refine ⟨Quot.lift e he, fun ι => ?_⟩
  rw [hφ]
  simp only [blochWave]
  change _ = _ * e ι
  simp only [e]
  rw [← mul_assoc, ← Complex.exp_add, bilinDot_sub_left]
  congr 2
  ring
def translatePerm (h : IsPeriodic I) (s : ℕ) (m : Fin 4 → ℤ) :
    Equiv.Perm (I.QuotMod s) where
  toFun := Quot.map (I.translate m) (by
    rintro a _ ⟨n, rfl⟩
    exact ⟨n, by rw [← h.translate_add, ← h.translate_add, add_comm]⟩)
  invFun := Quot.map (I.translate (-m)) (by
    rintro a _ ⟨n, rfl⟩
    exact ⟨n, by rw [← h.translate_add, ← h.translate_add, add_comm]⟩)
  left_inv := fun c => by
    induction c using Quot.ind with
    | mk ι =>
      change I.mkQuot s (I.translate (-m) (I.translate m ι)) = I.mkQuot s ι
      rw [← h.translate_add, add_neg_cancel, h.translate_zero]
  right_inv := fun c => by
    induction c using Quot.ind with
    | mk ι =>
      change I.mkQuot s (I.translate m (I.translate (-m) ι)) = I.mkQuot s ι
      rw [← h.translate_add, neg_add_cancel, h.translate_zero]
theorem apply_translatePerm (h : IsPeriodic I) {s : ℕ} {κ : AmbientSpace} {g : I.QuotMod s → ℂ}
    (hg : g ∈ blochWaveSubspace I s κ) (m : Fin 4 → ℤ) (c : I.QuotMod s) :
    g (translatePerm h s m c) = latticePhase κ m * g c := by
  obtain ⟨φ, hφ⟩ := hg
  induction c using Quot.ind with
  | mk ι =>
    change g (I.mkQuot s (I.translate m ι)) = latticePhase κ m * g (I.mkQuot s ι)
    rw [hφ, hφ, blochWave_translate h]
theorem quotWeight_translatePerm (h : IsPeriodic I) {s : ℕ} (hW : WeightFactorsThroughQuot I s)
    (m : Fin 4 → ℤ) (c : I.QuotMod s) :
    I.quotWeight s (translatePerm h s m c) = I.quotWeight s c := by
  induction c using Quot.ind with
  | mk ι =>
    change I.quotWeight s (I.mkQuot s (I.translate m ι)) = I.quotWeight s (I.mkQuot s ι)
    rw [hW.2, hW.2]
    simp only [PeriodicData.weightOf, h.componentOf_translate]
def innerLeft {s : ℕ} [Fintype (I.QuotMod s)] (g : I.QuotMod s → ℂ) :
    (I.QuotMod s → ℂ) →ₗ[ℂ] ℂ :=
  ∑ c, ((I.quotWeight s c : ℂ) * conj (g c)) • LinearMap.proj c
theorem innerLeft_apply {s : ℕ} [Fintype (I.QuotMod s)] (g g' : I.QuotMod s → ℂ) :
    innerLeft g g' = ∑ c, (I.quotWeight s c : ℂ) * (conj (g c) * g' c) := by
  simp [innerLeft, LinearMap.sum_apply, mul_assoc]
theorem wInner_eq_innerLeft {s : ℕ} [Fintype (I.QuotMod s)]
    (hF : PairingNormFiniteSum I s) (g g' : I.QuotMod s → ℂ) :
    wInner (I.quotWeight s) g g' = innerLeft g g' := by
  rw [innerLeft_apply, wInner, (hF _ _).2.2.1, finsum_eq_sum_of_fintype]
theorem eq_zero_of_innerLeft_self {s : ℕ} [Fintype (I.QuotMod s)]
    (hpos : ∀ c, 0 < I.quotWeight s c) {g : I.QuotMod s → ℂ} (H : innerLeft g g = 0) : g = 0 := by
  rw [innerLeft_apply] at H
  have hterm : ∀ c, (I.quotWeight s c : ℂ) * (conj (g c) * g c) =
      ((I.quotWeight s c * ‖g c‖ ^ 2 : ℝ) : ℂ) := fun c => by
    rw [Complex.conj_mul']
    push_cast
    ring
  simp only [hterm] at H
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun c _ => (mul_nonneg (hpos c).le (by positivity))] at H
  funext c
  have := H c (Finset.mem_univ c)
  have h2 : ‖g c‖ ^ 2 = 0 := (mul_eq_zero.1 this).resolve_left (hpos c).ne'
  simpa using h2
theorem exists_latticePhase_ne_one {δ : AmbientSpace} (hδ : δ ∉ periodLattice) :
    ∃ m, latticePhase δ m ≠ 1 := by
  by_contra hnone
  have hall : ∀ m, latticePhase δ m = 1 := fun m => by_contra fun hm => hnone ⟨m, hm⟩
  apply hδ
  have hμ : ∀ μ, ∃ k : ℤ, δ μ = (k : ℝ) * (2 * Real.pi) := fun μ => by
    have h1 := hall (Pi.single μ 1)
    rw [latticePhase, Complex.exp_eq_one_iff] at h1
    obtain ⟨k, hk⟩ := h1
    refine ⟨k, ?_⟩
    have hd : bilinDot (toComplexVec δ) (toComplexVec (castVec (Pi.single μ 1))) = (δ μ : ℂ) := by
      simp only [bilinDot, toComplexVec, castVec]
      rw [Finset.sum_eq_single μ]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hn
        exact absurd (Finset.mem_univ μ) hn
    rw [hd] at hk
    have h2 : (δ μ : ℂ) = ((k * (2 * Real.pi) : ℝ) : ℂ) := by
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      apply mul_left_cancel₀ hI
      rw [hk]
      push_cast
      ring
    exact_mod_cast h2
  choose k hk using hμ
  exact ⟨k, hk⟩
theorem innerLeft_eq_zero_of_sub_not_mem (h : IsPeriodic I) {s : ℕ} [Fintype (I.QuotMod s)]
    (hW : WeightFactorsThroughQuot I s) {κ κ' : AmbientSpace} (hδ : κ' - κ ∉ periodLattice)
    {g g' : I.QuotMod s → ℂ} (hg : g ∈ blochWaveSubspace I s κ)
    (hg' : g' ∈ blochWaveSubspace I s κ') :
    innerLeft g g' = 0 := by
  obtain ⟨m, hm⟩ := exists_latticePhase_ne_one hδ
  rw [innerLeft_apply]
  set F : I.QuotMod s → ℂ := fun c => (I.quotWeight s c : ℂ) * (conj (g c) * g' c) with hFdef
  have hshift : ∀ c, F (translatePerm h s m c) = latticePhase (κ' - κ) m * F c := fun c => by
    simp only [hFdef]
    rw [quotWeight_translatePerm h hW, apply_translatePerm h hg, apply_translatePerm h hg', map_mul,
      ← conj_latticePhase_mul]
    ring
  have hsum : ∑ c, F c = latticePhase (κ' - κ) m * ∑ c, F c := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (translatePerm h s m) F]
    exact Finset.sum_congr rfl fun c _ => hshift c
  have h1 : (1 - latticePhase (κ' - κ) m) * ∑ c, F c = 0 := by
    rw [sub_mul, one_mul, ← hsum, sub_self]
  exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (Ne.symm hm))
def boxDualClass (s : ℕ) (n : Fin 4 → Fin s) : DualClasses s :=
  QuotientAddGroup.mk
    ⟨fun μ => ((n μ : ℕ) : ℝ) * (2 * Real.pi / s), ⟨fun μ => ((n μ : ℕ) : ℤ), fun μ => by simp⟩⟩
theorem boxDualClass_bijective {s : ℕ} (hs : 0 < s) : Function.Bijective (boxDualClass s) := by
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  constructor
  · intro n n' e
    have e' := QuotientAddGroup.eq.1 e
    rw [AddSubgroup.mem_addSubgroupOf] at e'
    obtain ⟨k, hk⟩ := e'
    funext μ
    have h1 := hk μ
    simp only [AddSubgroup.coe_add, NegMemClass.coe_neg, Pi.add_apply, Pi.neg_apply] at h1
    have h2 : ((n' μ : ℕ) : ℝ) - (n μ : ℕ) = (k μ : ℝ) * s := by
      field_simp at h1
      linarith
    have h3 : ((n' μ : ℕ) : ℤ) - (n μ : ℕ) = k μ * s := by exact_mod_cast h2
    have hd : (s : ℤ) ∣ ((n' μ : ℕ) : ℤ) - (n μ : ℕ) := ⟨k μ, by rw [h3]; ring⟩
    have hlt : |((n' μ : ℕ) : ℤ) - (n μ : ℕ)| < s := by
      have := (n μ).isLt
      have := (n' μ).isLt
      rw [abs_lt]
      omega
    have h0 := Int.eq_zero_of_abs_lt_dvd hd hlt
    apply Fin.ext
    omega
  · intro q
    obtain ⟨⟨y, k, hk⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    have hsz : (0 : ℤ) < s := by exact_mod_cast hs
    let n : Fin 4 → Fin s := fun μ => ⟨(k μ % s).toNat, by
      have h1 := Int.emod_nonneg (k μ) hsz.ne'
      have h2 := Int.emod_lt_of_pos (k μ) hsz
      omega⟩
    refine ⟨n, ?_⟩
    apply QuotientAddGroup.eq.2
    rw [AddSubgroup.mem_addSubgroupOf]
    refine ⟨fun μ => k μ / s, fun μ => ?_⟩
    have h1 : ((n μ : ℕ) : ℤ) = k μ % s := by
      have h1 := Int.emod_nonneg (k μ) hsz.ne'
      simp only [n]
      omega
    have h2 : (((n μ : ℕ) : ℝ)) = ((k μ % s : ℤ) : ℝ) := by exact_mod_cast h1
    have h3 : (k μ : ℝ) = (s : ℝ) * ((k μ / s : ℤ) : ℝ) + ((k μ % s : ℤ) : ℝ) := by
      exact_mod_cast (Int.mul_ediv_add_emod (k μ) s).symm
    simp only [AddSubgroup.coe_add, NegMemClass.coe_neg, Pi.add_apply, Pi.neg_apply]
    rw [hk μ, h2]
    rw [h3]
    field_simp
    ring
theorem card_dualClasses {s : ℕ} (hs : 0 < s) : Nat.card (DualClasses s) = s ^ 4 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (boxDualClass_bijective hs))]
  simp
theorem sub_not_mem_periodLattice {s : ℕ} {r : DualClasses s → dualLattice s}
    (hr : IsDualSection s r) {q q' : DualClasses s} (hne : q ≠ q') :
    ((r q' : AmbientSpace) - r q) ∉ periodLattice := by
  intro hmem
  apply hne
  rw [← hr q, ← hr q']
  apply QuotientAddGroup.eq.2
  rw [AddSubgroup.mem_addSubgroupOf]
  simpa [sub_eq_neg_add] using hmem
theorem internal_sum_of_section (h : IsPeriodic I) {s : ℕ} (hs : 0 < s)
    (hcard : Nat.card (I.QuotMod s) = s ^ 4 * Nat.card I.UnitQuot)
    [Fintype (I.QuotMod s)] [Fintype I.UnitQuot] [Fintype (DualClasses s)]
    (hW : WeightFactorsThroughQuot I s) (r : DualClasses s → dualLattice s)
    (hr : IsDualSection s r) :
    iSupIndep (fun q => blochWaveSubspace I s (r q)) ∧ ⨆ q, blochWaveSubspace I s (r q) = ⊤ := by
  classical
  have hpos : ∀ c, 0 < I.quotWeight s c := fun c => by
    induction c using Quot.ind with
    | mk ι =>
      change 0 < I.quotWeight s (I.mkQuot s ι)
      rw [hW.2]
      exact h.weight_pos _
  have horth : ∀ {q q'}, q ≠ q' → ∀ {g g'}, g ∈ blochWaveSubspace I s (r q) →
      g' ∈ blochWaveSubspace I s (r q') → innerLeft g g' = 0 := fun hne _ _ hg hg' =>
    innerLeft_eq_zero_of_sub_not_mem h hW (sub_not_mem_periodLattice hr hne) hg hg'
  constructor
  · rw [iSupIndep_def]
    intro q
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hle : (⨆ (j) (_ : j ≠ q), blochWaveSubspace I s (r j)) ≤ LinearMap.ker (innerLeft x) :=
      iSup₂_le fun j hj y hy => LinearMap.mem_ker.2 (horth (Ne.symm hj) hx hy)
    exact eq_zero_of_innerLeft_self hpos (LinearMap.mem_ker.1 (hle hx'))
  · let Ψ : (DualClasses s → I.UnitQuot → ℂ) →ₗ[ℂ] (I.QuotMod s → ℂ) :=
      ∑ q, (blochMap h hs (r q).2).comp (LinearMap.proj q)
    have hΨ : ∀ u, Ψ u = ∑ q, blochMap h hs (r q).2 (u q) := fun u => by
      simp [Ψ, LinearMap.sum_apply]
    have hinj : Function.Injective Ψ := by
      rw [injective_iff_map_eq_zero]
      intro u hu
      funext p
      have hself : innerLeft (blochMap h hs (r p).2 (u p)) (blochMap h hs (r p).2 (u p)) = 0 := by
        have h0 : innerLeft (blochMap h hs (r p).2 (u p)) (Ψ u) = 0 := by rw [hu, map_zero]
        rw [hΨ, map_sum, Finset.sum_eq_single p] at h0
        · exact h0
        · intro q _ hq
          exact horth (Ne.symm hq) (blochMap_mem h hs (r p).2 _) (blochMap_mem h hs (r q).2 _)
        · intro hp
          exact absurd (Finset.mem_univ p) hp
      exact eq_zero_of_blochMap_eq_zero h hs (r p).2 _ (eq_zero_of_innerLeft_self hpos hself)
    have hdim : Module.finrank ℂ (DualClasses s → I.UnitQuot → ℂ) =
        Module.finrank ℂ (I.QuotMod s → ℂ) := by
      rw [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card]
      simp only [Module.finrank_fintype_fun_eq_card, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard,
        card_dualClasses hs]
    have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
    rw [eq_top_iff]
    intro f _
    obtain ⟨u, rfl⟩ := hsurj f
    rw [hΨ]
    exact Submodule.sum_mem _ fun q _ =>
      (le_iSup (fun q => blochWaveSubspace I s (r q)) q) (blochMap_mem h hs (r q).2 _)
theorem claim_holds (hQ : Quotients.QuotientTransposeNorm) : Claim := by
  intro I h
  have hfin : ∀ s, 0 < s → Finite (DualClasses s) := fun s hs =>
    Finite.of_surjective _ (boxDualClass_bijective hs).2
  refine
    { dualClasses_finite := hfin
      blochWave_descends := fun s hs κ hκ φ => ⟨blochMap h hs hκ φ, blochMap_mkQuot h hs hκ φ⟩
      blochWave_injective := fun κ φ H => eq_zero_of_blochWave_eq_zero κ φ H
      subspace_congr := fun s _ κ _ κ' _ hp => le_antisymm
        (blochWaveSubspace_le h s (by simpa using neg_mem hp))
        (blochWaveSubspace_le h s hp)
      internal_sum := fun s hs r hr => ?_
      orthogonal := fun s hs r hr q q' hne g hg g' hg' => ?_ }
  · obtain ⟨⟨hC, hCs, hcard⟩, hT, -⟩ := hQ I I h h s hs
    have := hfin s hs
    have := Fintype.ofFinite (I.QuotMod s)
    have := Fintype.ofFinite I.UnitQuot
    have := Fintype.ofFinite (DualClasses s)
    exact internal_sum_of_section h hs hcard (hT s (Or.inr rfl)).1 r hr
  · obtain ⟨⟨hC, hCs, hcard⟩, hT, -⟩ := hQ I I h h s hs
    have := Fintype.ofFinite (I.QuotMod s)
    obtain ⟨hW, hF⟩ := hT s (Or.inr rfl)
    rw [wInner_eq_innerLeft hF]
    exact innerLeft_eq_zero_of_sub_not_mem h hW (sub_not_mem_periodLattice hr hne) hg hg'
end YangMills.Construction.PeriodicOperators.BlochDecomposition
end
