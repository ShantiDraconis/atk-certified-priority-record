import ATK.ZeroClasses.BDTheta
import ATK.ZeroClasses.Unilateral
import ATK.ZeroClasses.LittlewoodMu
import ATK.ZeroClasses.BDTaxaPiso
import ATK.ZeroClasses.BDEspectral
import ATK.PerronSuave
import ATK.MellinPlancherel
import ATK.PlancherelL1L2

/-!
# O piso ponderado exato: `κ(σ) = 2(σ − Θ)` e `PisoPonderado` (rodada 109, proposta R105)

`D_N(σ) = inf_c ∫_0^∞ (χ − Σ_{k<N} c_k {1/((k+1)t)})² t^{2σ−1} dt` (`BDPonderado.DNσ`), `Θ = sup Re ρ`
(`BDTheta.Teta`) e `TaxaDN σ κ`: `D_N(σ) ≪ N^{−δ}` para todo `δ < κ`. A rodada 75/76 provou `κ(σ) ≥ 2(σ − Θ)`
(`BDTheta.taxa_Teta`); as rodadas 79 e 83 provaram tetos com fator (`κ ≤ (2σ + 3)(σ − Θ)/Θ`). Aqui sai o teto exato:

  **`TaxaDN σ κ ⟹ κ ≤ 2(σ − Θ)`** para `Θ < σ < 1`   (`taxa_le_Teta`),

logo `2(σ − Θ)` é o maior expoente (`kappa_exato`, `sSup_taxa`, `Teta_eq_taxa`), a proposição
`BDTheta.PisoPonderado` (Q2(iii), declarada OPEN_MATH na rodada 76) é um teorema (`pisoPonderado`), e
**RH ⟺ `TaxaDN σ₀ (2σ₀ − 1)` para um único `σ₀ ∈ (½, 1)` fixado** (`rh_iff_taxa_um`).

A prova:

1. **Núcleo.** `K(s) = 1/((2 − s)(3 − s)(4 − s))` é a transformada de Mellin de `ψ(t) = (t − 1)₊²/(2t⁴)`
   (`hasMellin_psi`), e `(1/2π) ∫ y^{−(σ+iτ)} K(σ + iτ) dτ = ψ(y)` (`inv_K`). Como `ψ = 0` em `(0, 1]`,
   `∫ y^{σ+iτ} K = 0` para `y ≥ 1` (`inv_K_zero`).
2. **Pareamento** (`piso_G`). Na reta `Re s = σ ∈ (Θ, 1)`, `s M f(s) = 1 + ζ(s)P(s)` (a densidade espectral
   `espectroσ`, rodada 73) e `F = 1/ζ`. Então `M(s) · s K(s) F(s) x^s = x^s K F + Σ c_k (x/(k+1))^s K`; os termos de
   `P` integram a `0` porque `x/(k + 1) ≥ 1` para `k + 1 ≤ N ≤ x`. Cauchy–Schwarz e Plancherel ponderado dão, para
   **todo** `c`, `(2π)² ‖G_σ(x)‖² ≤ x^{2σ} (2π W_σ(c)) B`, `B = ∫ ‖sKF‖²` (`piso_DN`), com
   `G_σ(x) = (1/2π) ∫ x^{σ+iτ} K(σ + iτ)/ζ(σ + iτ) dτ`.
3. **Deslocamento e série** (`Gl_desloca`, `Gl_serie`, `Gl_mobius`). `G_σ(x) = G_{3/2}(x) = Σ_n μ(n) ψ(n/x)
   = Σ_{n > x} μ(n) φ(x/n)` com `φ(y) = y²(1 − y)²/2`: uma função de Mertens suavizada.
4. **Mellin** (`mellin_gU`). `g(u) = G(1/u)` tem `∫_0^∞ u^{s−1} g(u) du = K(s)/ζ(s)` em `1 < Re s < 2`.
5. **Continuação** (`semZeros_of_cota`). Se `‖G_σ(x)‖ ≤ C x^θ` para `x ≥ 1`, então `g = O(u^{−θ})` em `0⁺` e
   `O(u^{−3/2})` em `∞`, a transformada é holomorfa em `θ < Re s < 3/2` (`mellin_differentiableAt_of_isBigO_rpow`),
   `1/ζ` estende-se a `Re s > θ` e não há zeros lá (`Unilateral.semZeros_of_ext_mertens`).
6. **Montagem** (`taxa_le_Teta`). Se `κ > 2(σ − Θ)`, escolha `2(σ − Θ) < δ < κ`. Com `N = ⌊x⌋`, os passos 2 e a taxa
   dão `‖G_σ(x)‖ ≪ x^{σ−δ/2}`, e `σ − δ/2 < Θ`: o passo 5 daria um semiplano sem zeros à esquerda de `Θ`
   (`Unilateral.nao_semZeros`). Em `σ = Θ`, uma taxa positiva daria `Θ < σ` (`BDTaxaPiso.taxaDN_pos`).

Consequências: `Teta_le_de_taxa` (`Θ ≤ σ − κ/2`, a forma exata de `BDTaxaPiso.Teta_le_de_taxaDN`), `taxa_le_perfil`
(`κ ≤ 2 max(σ − Θ, 0)` em `(0, 1)`), `nao_taxa`, e `Gl_omega` (para `θ < Θ`, a Mertens suavizada `G_σ` não é
`O(x^θ)`).

Literatura (checagem da proposta R105, issue #176): o piso polinomial de Burnol (2002, Nota 2.2) e a cota implícita
de Balazard–Saias (1998) são os análogos mais próximos; Manzur–Noor–Quintero (2026) é qualitativo. Não achamos o
expoente exato `2(σ − Θ)` publicado; isso é uma leitura de fontes, não uma prova de novidade.

Nada aqui diz qual é o valor de `Θ`, e o enunciado sobre `(Θ, 1)` é vazio se `Θ = 1`. `rh_iff_taxa_um` é uma
reformulação de RH. Classificação (rodada 109): **novo** (proposta R105). Só os axiomas padrão. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace ATK.ZeroClasses.BDPisoExato

/-! ## 1. O núcleo `K` e a sua inversa de Mellin `ψ` -/

/-- `K(s) = 1/((2 − s)(3 − s)(4 − s))`: polos só em `2, 3, 4`. -/
noncomputable def K (s : ℂ) : ℂ := 1 / ((2 - s) * (3 - s) * (4 - s))

/-- `ψ(t) = max(t − 1, 0)²/(2t⁴)`. É `t^{−2}/2 − t^{−3} + t^{−4}/2` em `t ≥ 1` e `0` em `t ≤ 1`. -/
noncomputable def ψ (t : ℝ) : ℝ := max (t - 1) 0 ^ 2 / (2 * t ^ 4)

theorem psi_eq_zero {t : ℝ} (ht : t ≤ 1) : ψ t = 0 := by
  unfold ψ; rw [max_eq_right (by linarith)]; simp

theorem psi_nonneg (t : ℝ) : 0 ≤ ψ t := by unfold ψ; positivity

theorem continuousAt_psi {t : ℝ} (_ht : 0 < t) : ContinuousAt (fun t : ℝ => (ψ t : ℂ)) t := by
  unfold ψ
  refine continuous_ofReal.continuousAt.comp ?_
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)

theorem cpow_neg_nat {t : ℝ} (_ht : 0 < t) (n : ℕ) : (t : ℂ) ^ (-(n : ℂ)) = ((t ^ n)⁻¹ : ℝ) := by
  rw [show (-(n : ℂ)) = ((-(n : ℤ) : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast, zpow_neg,
    zpow_natCast]
  push_cast
  rfl

theorem psi_formula {t : ℝ} (ht : 1 ≤ t) :
    (ψ t : ℂ) = (1 / 2) * (t : ℂ) ^ (-(2 : ℕ) : ℂ) - (t : ℂ) ^ (-(3 : ℕ) : ℂ) +
      (1 / 2) * (t : ℂ) ^ (-(4 : ℕ) : ℂ) := by
  have ht0 : (0 : ℝ) < t := by linarith
  rw [cpow_neg_nat ht0, cpow_neg_nat ht0, cpow_neg_nat ht0, ψ, max_eq_left (by linarith)]
  have : t ≠ 0 := ht0.ne'
  push_cast
  field_simp
  ring

/-- `t^{s−1}ψ(t)` em `t > 1`, termo a termo. -/
theorem integrando_formula {s : ℂ} {t : ℝ} (ht : 1 < t) :
    (t : ℂ) ^ (s - 1) * (ψ t : ℂ) = (1 / 2) * (t : ℂ) ^ (s - 3) - (t : ℂ) ^ (s - 4) +
      (1 / 2) * (t : ℂ) ^ (s - 5) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by linarith)
  rw [psi_formula ht.le]
  have e : ∀ n : ℕ, (t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-(n : ℂ)) = (t : ℂ) ^ (s - 1 - n) := by
    intro n
    rw [← Complex.cpow_add _ _ ht0]
    ring_nf
  have e2 := e 2
  have e3 := e 3
  have e4 := e 4
  push_cast at e2 e3 e4
  rw [show s - 3 = s - 1 - 2 by ring, show s - 4 = s - 1 - 3 by ring, show s - 5 = s - 1 - 4 by ring,
    ← e2, ← e3, ← e4]
  ring

theorem integrableOn_pow {s : ℂ} {a : ℕ} (hs : s.re < (a : ℝ) - 1) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - a)) (Ioi 1) :=
  integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos

theorem integral_pow {s : ℂ} {a : ℕ} (hs : s.re < (a : ℝ) - 1) :
    ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - a) = 1 / (a - 1 - s) := by
  rw [integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
  have h : s - a + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h' : (a : ℂ) - 1 - s ≠ 0 := by
    intro h2; apply h; linear_combination -h2
  push_cast
  rw [Complex.one_cpow]
  field_simp
  ring

/-- `t^{s−1}ψ(t)` só vive em `t > 1`. -/
theorem integrando_indicator {s : ℂ} {t : ℝ} (_ht : 0 < t) :
    (t : ℂ) ^ (s - 1) • (ψ t : ℂ) = (Ioi (1 : ℝ)).indicator
      (fun t : ℝ => (1 / 2) * (t : ℂ) ^ (s - 3) - (t : ℂ) ^ (s - 4) + (1 / 2) * (t : ℂ) ^ (s - 5)) t := by
  by_cases h1 : 1 < t
  · rw [Set.indicator_of_mem (show t ∈ Ioi (1 : ℝ) from h1), smul_eq_mul, integrando_formula h1]
  · rw [Set.indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from h1), psi_eq_zero (not_lt.mp h1)]
    simp

/-- **A transformada de Mellin de `ψ` é `K`** em `Re s < 2`. -/
theorem hasMellin_psi {s : ℂ} (hs : s.re < 2) : HasMellin (fun t : ℝ => (ψ t : ℂ)) s (K s) := by
  set g : ℝ → ℂ := fun t => (1 / 2) * (t : ℂ) ^ (s - 3) - (t : ℂ) ^ (s - 4) + (1 / 2) * (t : ℂ) ^ (s - 5)
    with hg
  have i3 := integrableOn_pow (s := s) (a := 3) (by norm_num; linarith)
  have i4 := integrableOn_pow (s := s) (a := 4) (by norm_num; linarith)
  have i5 := integrableOn_pow (s := s) (a := 5) (by norm_num; linarith)
  push_cast at i3 i4 i5
  have hgi : IntegrableOn g (Ioi 1) := ((i3.const_mul _).sub i4).add (i5.const_mul _)
  have hcongr : EqOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (ψ t : ℂ)) ((Ioi (1 : ℝ)).indicator g) (Ioi 0) :=
    fun t ht => integrando_indicator ht
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
  constructor
  · unfold MellinConvergent
    rw [integrableOn_congr_fun hcongr measurableSet_Ioi]
    exact (hgi.integrable_indicator measurableSet_Ioi).integrableOn
  · unfold mellin
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr hsub]
    have hsplit : ∫ t in Ioi (1 : ℝ), g t = (1 / 2) * (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 3)) -
        (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 4)) + (1 / 2) * (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 5)) := by
      have a1 := integral_add ((i3.const_mul (1 / 2 : ℂ)).sub i4) (i5.const_mul (1 / 2 : ℂ))
      have a2 := integral_sub (i3.const_mul (1 / 2 : ℂ)) i4
      have a3 := integral_const_mul (μ := volume.restrict (Ioi (1 : ℝ))) (1 / 2 : ℂ) (fun t : ℝ => (t : ℂ) ^ (s - 3))
      have a4 := integral_const_mul (μ := volume.restrict (Ioi (1 : ℝ))) (1 / 2 : ℂ) (fun t : ℝ => (t : ℂ) ^ (s - 5))
      simp only [Pi.sub_apply] at a1 a2
      rw [hg]
      simp only
      rw [a1, a2, a3, a4]
    rw [hsplit]
    have e3 := integral_pow (s := s) (a := 3) (by norm_num; linarith)
    have e4 := integral_pow (s := s) (a := 4) (by norm_num; linarith)
    have e5 := integral_pow (s := s) (a := 5) (by norm_num; linarith)
    push_cast at e3 e4 e5
    rw [e3, e4, e5, K]
    have h2 : (2 : ℂ) - s ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h3 : (3 : ℂ) - s ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h4 : (4 : ℂ) - s ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h2' : (3 : ℂ) - 1 - s = 2 - s := by ring
    have h3' : (4 : ℂ) - 1 - s = 3 - s := by ring
    have h4' : (5 : ℂ) - 1 - s = 4 - s := by ring
    rw [h2', h3', h4']
    field_simp
    ring

/-! ## 2. Cotas de `K` em faixas verticais e a inversão de Mellin -/

theorem norm_sub_sq_ge {a σ₀ : ℝ} {s : ℂ} (ha : σ₀ < a) (hs : s.re ≤ σ₀) :
    min ((a - σ₀) ^ 2) 1 * (1 + s.im ^ 2) ≤ ‖(a : ℂ) - s‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, zero_sub]
  have h1 : (a - σ₀) ^ 2 ≤ (a - s.re) ^ 2 := by nlinarith
  have hm1 := min_le_left ((a - σ₀) ^ 2) 1
  have hm2 := min_le_right ((a - σ₀) ^ 2) 1
  have hm0 : 0 ≤ min ((a - σ₀) ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
  nlinarith [sq_nonneg s.im, mul_nonneg hm0 (sq_nonneg s.im)]

/-- A constante de faixa `m = min((2 − σ₀)², 1)`. -/
noncomputable def mK (σ₀ : ℝ) : ℝ := min ((2 - σ₀) ^ 2) 1

theorem mK_pos {σ₀ : ℝ} (h : σ₀ < 2) : 0 < mK σ₀ := lt_min (by nlinarith) one_pos

theorem norm_sub_sq_ge' {a σ₀ : ℝ} {s : ℂ} (h2 : σ₀ < 2) (ha : 2 ≤ a) (hs : s.re ≤ σ₀) :
    mK σ₀ * (1 + s.im ^ 2) ≤ ‖(a : ℂ) - s‖ ^ 2 := by
  refine le_trans ?_ (norm_sub_sq_ge (by linarith) hs)
  have : mK σ₀ ≤ min ((a - σ₀) ^ 2) 1 := by
    unfold mK
    exact min_le_min_right _ (by nlinarith)
  exact mul_le_mul_of_nonneg_right this (by positivity)

/-- `‖K(s)‖² ≤ 1/(m³(1 + (Im s)²)³)` em `Re s ≤ σ₀ < 2`. -/
theorem norm_K_sq_le {σ₀ : ℝ} (h2 : σ₀ < 2) {s : ℂ} (hs : s.re ≤ σ₀) :
    ‖K s‖ ^ 2 ≤ 1 / (mK σ₀ ^ 3 * (1 + s.im ^ 2) ^ 3) := by
  have hm := mK_pos h2
  have a2 := norm_sub_sq_ge' (a := 2) h2 le_rfl hs
  have a3 := norm_sub_sq_ge' (a := 3) h2 (by norm_num) hs
  have a4 := norm_sub_sq_ge' (a := 4) h2 (by norm_num) hs
  push_cast at a2 a3 a4
  have hp : 0 < mK σ₀ * (1 + s.im ^ 2) := by positivity
  have key := mul_le_mul a2 (mul_le_mul a3 a4 hp.le (sq_nonneg _)) (by positivity) (sq_nonneg _)
  rw [K, norm_div, norm_one, div_pow, one_pow, norm_mul, norm_mul, mul_pow, mul_pow]
  have e : mK σ₀ ^ 3 * (1 + s.im ^ 2) ^ 3 =
      mK σ₀ * (1 + s.im ^ 2) * (mK σ₀ * (1 + s.im ^ 2) * (mK σ₀ * (1 + s.im ^ 2))) := by ring
  rw [e, mul_assoc (‖(2 : ℂ) - s‖ ^ 2)]
  exact one_div_le_one_div_of_le (by positivity) key

/-- `‖K(s)‖ ≤ 1/(m(1 + (Im s)²))` em `Re s ≤ σ₀ < 2`. -/
theorem norm_K_le {σ₀ : ℝ} (h2 : σ₀ < 2) {s : ℂ} (hs : s.re ≤ σ₀) :
    ‖K s‖ ≤ 1 / (mK σ₀ * (1 + s.im ^ 2)) := by
  have hm := mK_pos h2
  have a2 := norm_sub_sq_ge' (a := 2) h2 le_rfl hs
  have a3 := norm_sub_sq_ge' (a := 3) h2 (by norm_num) hs
  push_cast at a2 a3
  have hp : 0 < mK σ₀ * (1 + s.im ^ 2) := by positivity
  have h23 : mK σ₀ * (1 + s.im ^ 2) ≤ ‖(2 : ℂ) - s‖ * ‖(3 : ℂ) - s‖ := by
    have hsq : (mK σ₀ * (1 + s.im ^ 2)) ^ 2 ≤ (‖(2 : ℂ) - s‖ * ‖(3 : ℂ) - s‖) ^ 2 := by
      rw [mul_pow (‖(2 : ℂ) - s‖), pow_two]
      exact mul_le_mul a2 a3 hp.le (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ hp.le (by positivity) two_ne_zero).mp hsq
  have h4 : 1 ≤ ‖(4 : ℂ) - s‖ := by
    have := Complex.abs_re_le_norm ((4 : ℂ) - s)
    simp at this
    have : (1 : ℝ) ≤ |4 - s.re| := by rw [abs_of_pos (by linarith)]; linarith
    linarith
  rw [K, norm_div, norm_one, norm_mul, norm_mul]
  refine one_div_le_one_div_of_le hp ?_
  calc mK σ₀ * (1 + s.im ^ 2) ≤ ‖(2 : ℂ) - s‖ * ‖(3 : ℂ) - s‖ := h23
    _ ≤ ‖(2 : ℂ) - s‖ * ‖(3 : ℂ) - s‖ * ‖(4 : ℂ) - s‖ :=
      le_mul_of_one_le_right (by positivity) h4

theorem continuous_K_linha {σ : ℝ} (hσ : σ < 2) : Continuous (fun y : ℝ => K (σ + y * I)) := by
  unfold K
  refine Continuous.div continuous_const (by fun_prop) fun y => ?_
  have hne : ∀ a : ℝ, σ < a → ((a : ℂ) - (σ + y * I)) ≠ 0 := by
    intro a ha h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2 := hne 2 hσ
  have h3 := hne 3 (by linarith)
  have h4 := hne 4 (by linarith)
  push_cast at h2 h3 h4
  exact mul_ne_zero (mul_ne_zero h2 h3) h4

theorem integrable_K_linha {σ : ℝ} (hσ : σ < 2) : Integrable (fun y : ℝ => K (σ + y * I)) := by
  have hm := mK_pos hσ
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (1 / mK σ))
    (continuous_K_linha hσ).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have h := norm_K_le hσ (s := σ + y * I) (by simp)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add] at h
  calc ‖K (σ + y * I)‖ ≤ 1 / (mK σ * (1 + y ^ 2)) := h
    _ = 1 / mK σ * (1 + y ^ 2)⁻¹ := by field_simp

/-- **Inversão de Mellin de `K`**: `(1/2π) ∫ x^{−(σ+iy)} K(σ + iy) dy = ψ(x)` para `σ < 2`, `x > 0`. -/
theorem inv_K {σ : ℝ} (hσ : σ < 2) {x : ℝ} (hx : 0 < x) :
    (1 / (2 * π)) * ∫ y : ℝ, (x : ℂ) ^ (-((σ : ℂ) + y * I)) * K (σ + y * I) = (ψ x : ℂ) := by
  have hM : ∀ y : ℝ, mellin (fun t : ℝ => (ψ t : ℂ)) (σ + y * I) = K (σ + y * I) := fun y =>
    (hasMellin_psi (by simpa using hσ)).2
  have hconv : MellinConvergent (fun t : ℝ => (ψ t : ℂ)) σ := (hasMellin_psi (by simpa using hσ)).1
  have hvi : VerticalIntegrable (mellin (fun t : ℝ => (ψ t : ℂ))) σ := by
    unfold VerticalIntegrable
    simp_rw [hM]
    exact integrable_K_linha hσ
  have h := mellinInv_mellin_eq σ (fun t : ℝ => (ψ t : ℂ)) hx hconv hvi (continuousAt_psi hx)
  unfold mellinInv at h
  simp_rw [hM, smul_eq_mul] at h
  have e : ((1 / (2 * π) : ℝ) : ℂ) = 1 / (2 * π) := by push_cast; ring
  rw [← h]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- Para `y ≥ 1` (o caso dos termos do polinômio de Dirichlet): `∫ y^{σ+iτ} K(σ + iτ) dτ = 0`. -/
theorem inv_K_zero {σ : ℝ} (hσ : σ < 2) {y : ℝ} (hy : 1 ≤ y) :
    ∫ τ : ℝ, (y : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I) = 0 := by
  have hy0 : 0 < y := by linarith
  have h := inv_K hσ (x := y⁻¹) (inv_pos.mpr hy0)
  rw [psi_eq_zero (inv_le_one_of_one_le₀ hy)] at h
  have e : ∀ τ : ℝ, ((y⁻¹ : ℝ) : ℂ) ^ (-((σ : ℂ) + τ * I)) = (y : ℂ) ^ ((σ : ℂ) + τ * I) := by
    intro τ
    rw [ofReal_inv, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg hy0.le]; exact Real.pi_pos.ne), Complex.cpow_neg, inv_inv]
  simp_rw [e] at h
  have : (1 / (2 * π) : ℂ) ≠ 0 := by simp
  push_cast at h
  exact (mul_eq_zero.mp h).resolve_left this

/-! ## 3. A densidade espectral é integrável -/

open ATK.ZeroClasses.BDPonderado ATK.ZeroClasses.BDEspectral in
/-- `τ ↦ ‖(1 + ζ(s)P(s))/s‖²` é integrável na reta `Re s = σ` (Plancherel: `𝓜 res ∈ L²`). -/
theorem integrable_espectro {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (c : Fin N → ℝ) :
    Integrable (espectroσ σ c) := by
  set f : ℝ → ℂ := fun t => ((ATK.BaezDuarteBridge.res c t : ℝ) : ℂ) with hf
  have hM := fun τ : ℝ => (ATK.EspectralDN.mellin_res_geral c (s := (σ : ℂ) + (τ : ℂ) * I)
    (by simpa using hσ0) (by simpa using hσ1))
  have hM1 := (ATK.EspectralDN.mellin_res_geral c (s := (σ : ℂ)) (by simpa using hσ0)
    (by simpa using hσ1)).1
  set g : ℝ → ℂ := fun t => (t : ℂ) ^ (((σ - 1 / 2 : ℝ)) : ℂ) • f t with hg
  have hg1 : MellinConvergent g ((1 / 2 : ℝ) : ℂ) := by
    rw [hg, MellinConvergent.cpow_smul]
    have e : ((1 / 2 : ℝ) : ℂ) + ((σ - 1 / 2 : ℝ) : ℂ) = (σ : ℂ) := by push_cast; ring
    rw [e]
    exact hM1
  have hnorm : ∀ t ∈ Ioi (0 : ℝ), ‖g t‖ ^ 2 = ‖f t‖ ^ 2 * t ^ (2 * σ - 1) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [hg]
    simp only
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, ofReal_re, mul_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    push_cast
    rw [show (σ - 1 / 2) * 2 = 2 * σ - 1 by ring]
    ring
  have h2 : IntegrableOn (fun t => ‖f t‖ ^ 2 * t ^ (2 * σ - 1)) (Ioi 0) := by
    refine (integrable_w c hσ0 hσ1).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [hf, Complex.norm_real, sq_abs]
  have hg2 : IntegrableOn (fun t => ‖g t‖ ^ 2) (Ioi 0) :=
    h2.congr_fun (fun t ht => (hnorm t ht).symm) measurableSet_Ioi
  have hl1 : Integrable (ATK.MellinPlancherel.lado g) := ATK.MellinPlancherel.integrable_lado hg1
  have hsq : Integrable (fun u => ‖ATK.MellinPlancherel.lado g u‖ ^ 2) := by
    have h := (ATK.MellinPlancherel.integrableOn_Ioi_iff (fun t => ‖g t‖ ^ 2)).mp hg2
    simpa [ATK.MellinPlancherel.norm_sq_lado] using h
  have hl2 : MemLp (ATK.MellinPlancherel.lado g) 2 :=
    (memLp_two_iff_integrable_sq_norm hl1.aestronglyMeasurable).mpr hsq
  have hF2 := ATK.PlancherelL1L2.memLp_two_fourier hl1 hl2
  have hFi : Integrable (fun ξ => ‖FourierTransform.fourier (ATK.MellinPlancherel.lado g) ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hF2.aestronglyMeasurable).mp hF2
  -- `‖𝓕 lado g (ξ)‖² = espectro(2πξ)`
  have hid : ∀ ξ : ℝ, ‖FourierTransform.fourier (ATK.MellinPlancherel.lado g) ξ‖ ^ 2 =
      espectroσ σ c (2 * π * ξ) := by
    intro ξ
    rw [ATK.MellinPlancherel.fourier_lado, hg, mellin_cpow_smul, espectroσ]
    have e : (1 / 2 + ((2 * π * ξ : ℝ) : ℂ) * I) + ((σ - 1 / 2 : ℝ) : ℂ) =
        (σ : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I := by push_cast; ring
    rw [e, (hM (2 * π * ξ)).2]
  have hcomp : Integrable (fun ξ : ℝ => espectroσ σ c (2 * π * ξ)) := hFi.congr (ae_of_all _ hid)
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  have h3 := hcomp.comp_mul_left' (inv_ne_zero hpi)
  refine h3.congr (ae_of_all _ fun τ => ?_)
  simp only
  congr 1
  field_simp

/-! ## 4. A cota inferior: `D_N(σ) ≥ c_σ N^{−2σ} |G(N)|²` para todos os coeficientes -/

open ATK.RHLogZeta (F F_eq)
open ATK.ZeroClasses.QuasiRH (SemZeros differentiableAt_F norm_F_le)
open ATK.ZeroClasses.BDTheta (Teta semZeros_Teta meio_le_Teta TaxaDN taxa_Teta)
open ATK.ZeroClasses.BDPonderado (Wσ DNσ Wσ_nonneg)
open ATK.ZeroClasses.BDEspectral (espectroσ Wσ_espectral)

/-- `G_σ(x) = (1/2π) ∫ x^{σ+iτ} K(σ + iτ) F(σ + iτ) dτ`, com `F = 1/ζ`. -/
noncomputable def Gl (σ x : ℝ) : ℂ :=
  (1 / (2 * π)) * ∫ τ : ℝ, (x : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I) * F (σ + τ * I)

theorem norm_K_mul_le {σ₀ : ℝ} (h2 : σ₀ < 2) {s : ℂ} (hs : s.re ≤ σ₀) :
    ‖K s‖ * (1 + |s.im|) ≤ 2 / (mK σ₀ * (1 + s.im ^ 2)) := by
  have hm := mK_pos h2
  have a2 := norm_sub_sq_ge' (a := 2) h2 le_rfl hs
  have a3 := norm_sub_sq_ge' (a := 3) h2 (by norm_num) hs
  push_cast at a2 a3
  have hp : 0 < mK σ₀ * (1 + s.im ^ 2) := by positivity
  have h23 : mK σ₀ * (1 + s.im ^ 2) ≤ ‖(2 : ℂ) - s‖ * ‖(3 : ℂ) - s‖ := by
    have hsq : (mK σ₀ * (1 + s.im ^ 2)) ^ 2 ≤ (‖(2 : ℂ) - s‖ * ‖(3 : ℂ) - s‖) ^ 2 := by
      rw [mul_pow (‖(2 : ℂ) - s‖), pow_two]
      exact mul_le_mul a2 a3 hp.le (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ hp.le (by positivity) two_ne_zero).mp hsq
  have h4 : (1 + |s.im|) / 2 ≤ ‖(4 : ℂ) - s‖ := by
    have hr := Complex.abs_re_le_norm ((4 : ℂ) - s)
    have hi := Complex.abs_im_le_norm ((4 : ℂ) - s)
    simp at hr hi
    have : (1 : ℝ) ≤ |4 - s.re| := by rw [abs_of_pos (by linarith)]; linarith
    linarith
  have h4pos : 0 < ‖(4 : ℂ) - s‖ := lt_of_lt_of_le (by positivity) h4
  rw [K, norm_div, norm_one, norm_mul, norm_mul]
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by
    have := lt_of_lt_of_le hp h23
    positivity) hp]
  calc (1 + |s.im|) * (mK σ₀ * (1 + s.im ^ 2)) ≤ (2 * ‖(4 : ℂ) - s‖) * (‖(2 : ℂ) - s‖ * ‖(3 : ℂ) - s‖) :=
        mul_le_mul (by linarith) h23 hp.le (by positivity)
    _ = 2 * (‖(2 : ℂ) - s‖ * ‖(3 : ℂ) - s‖ * ‖(4 : ℂ) - s‖) := by ring

/-- Os dados da reta `Re s = σ` com `Θ < σ < 1`: `ζ ≠ 0`, `F = 1/ζ` e `‖F‖ ≤ C(1 + |τ|)`. -/
theorem dados_reta {σ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) :
    ∃ C, 0 < C ∧ ∀ τ : ℝ, riemannZeta (σ + τ * I) ≠ 0 ∧
      F (σ + τ * I) * riemannZeta (σ + τ * I) = 1 ∧ ‖F (σ + τ * I)‖ ≤ C * (1 + |τ|) := by
  have hθ := meio_le_Teta
  obtain ⟨C, hC, hF⟩ := norm_F_le semZeros_Teta hθ (by linarith) (δ := σ - Teta) (η := 1 / 2)
    (by linarith) (by linarith) (by norm_num)
  refine ⟨C, hC, fun τ => ?_⟩
  have hre : ((σ : ℂ) + τ * I).re = σ := by simp
  have hz : riemannZeta (σ + τ * I) ≠ 0 := semZeros_Teta _ (by rw [hre]; exact hσ)
  have hne1 : ((σ : ℂ) + τ * I) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  refine ⟨hz, by rw [F_eq hne1, inv_mul_cancel₀ hz], ?_⟩
  have h := hF (σ + τ * I) (by rw [hre]; linarith)
  have him : ((σ : ℂ) + τ * I).im = τ := by simp
  rw [him] at h
  have h1 : (1 + |τ|) ^ (1 / 2 : ℝ) ≤ 1 + |τ| := by
    have : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
    calc (1 + |τ|) ^ (1 / 2 : ℝ) ≤ (1 + |τ|) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le this (by norm_num)
      _ = 1 + |τ| := Real.rpow_one _
  exact h.trans (mul_le_mul_of_nonneg_left h1 hC.le)

theorem continuous_F_linha {σ : ℝ} (hσ : Teta < σ) :
    Continuous (fun τ : ℝ => F (σ + τ * I)) := by
  rw [continuous_iff_continuousAt]
  intro τ
  have hre : ((σ : ℂ) + τ * I).re = σ := by simp
  exact (differentiableAt_F semZeros_Teta (by rw [hre]; exact hσ)).continuousAt.comp (by fun_prop)

theorem norm_cpow_real {x : ℝ} (hx : 0 < x) (σ τ : ℝ) : ‖(x : ℂ) ^ ((σ : ℂ) + τ * I)‖ = x ^ σ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- A função `τ ↦ ‖s K(s) F(s)‖` da reta e a constante `B = ∫ ‖sKF‖²`. -/
noncomputable def hK (σ : ℝ) (τ : ℝ) : ℝ := ‖((σ : ℂ) + τ * I) * K (σ + τ * I) * F (σ + τ * I)‖

theorem integrable_hK_sq {σ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) :
    Integrable (fun τ => hK σ τ ^ 2) := by
  obtain ⟨C, hC, hd⟩ := dados_reta hσ hσ1
  have hθ := meio_le_Teta
  have hσ0 : 0 < σ := by linarith
  have hm := mK_pos (σ₀ := σ) (by linarith)
  have hcont : Continuous (fun τ : ℝ => ((σ : ℂ) + τ * I) * K (σ + τ * I) * F (σ + τ * I)) :=
    ((by fun_prop : Continuous (fun τ : ℝ => ((σ : ℂ) + τ * I))).mul
      (continuous_K_linha (by linarith))).mul (continuous_F_linha hσ)
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (8 * C ^ 2 / mK σ ^ 2))
    (by unfold hK; exact (hcont.norm.pow 2).aestronglyMeasurable) (Eventually.of_forall fun τ => ?_)
  have hKb := norm_K_mul_le (σ₀ := σ) (by linarith) (s := σ + τ * I) (by simp)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add] at hKb
  have hs : ‖((σ : ℂ) + τ * I)‖ ≤ 1 + |τ| := by
    calc ‖((σ : ℂ) + τ * I)‖ ≤ ‖(σ : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
      _ = |σ| + |τ| := by simp
      _ ≤ 1 + |τ| := by rw [abs_of_pos hσ0]; linarith
  have hFb := (hd τ).2.2
  have hn : 0 ≤ hK σ τ := norm_nonneg _
  have hbound : hK σ τ ≤ C * (1 + |τ|) * (2 / (mK σ * (1 + τ ^ 2))) := by
    unfold hK
    rw [norm_mul, norm_mul]
    calc ‖((σ : ℂ) + τ * I)‖ * ‖K (σ + τ * I)‖ * ‖F (σ + τ * I)‖
        ≤ (1 + |τ|) * ‖K (σ + τ * I)‖ * (C * (1 + |τ|)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hs (norm_nonneg _)) hFb (norm_nonneg _) (by positivity)
      _ = C * (1 + |τ|) * (‖K (σ + τ * I)‖ * (1 + |τ|)) := by ring
      _ ≤ C * (1 + |τ|) * (2 / (mK σ * (1 + τ ^ 2))) :=
          mul_le_mul_of_nonneg_left hKb (by positivity)
  have hsq : (1 + |τ|) ^ 2 ≤ 2 * (1 + τ ^ 2) := by
    have := sq_abs τ
    nlinarith [sq_nonneg (|τ| - 1)]
  rw [Real.norm_of_nonneg (by positivity)]
  calc hK σ τ ^ 2 ≤ (C * (1 + |τ|) * (2 / (mK σ * (1 + τ ^ 2)))) ^ 2 :=
        pow_le_pow_left₀ hn hbound 2
    _ = C ^ 2 * (1 + |τ|) ^ 2 * 4 / (mK σ ^ 2 * (1 + τ ^ 2) ^ 2) := by
        field_simp
        norm_num
    _ ≤ C ^ 2 * (2 * (1 + τ ^ 2)) * 4 / (mK σ ^ 2 * (1 + τ ^ 2) ^ 2) := by
        gcongr
    _ = 8 * C ^ 2 / mK σ ^ 2 * (1 + τ ^ 2)⁻¹ := by
        field_simp
        ring

theorem integrable_KF {σ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) {x : ℝ} (hx : 0 < x) :
    Integrable (fun τ : ℝ => (x : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I) * F (σ + τ * I)) := by
  obtain ⟨C, hC, hd⟩ := dados_reta hσ hσ1
  have hθ := meio_le_Teta
  have hm := mK_pos (σ₀ := σ) (by linarith)
  have hcont : Continuous (fun τ : ℝ => (x : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I) * F (σ + τ * I)) := by
    refine ((Continuous.const_cpow (by fun_prop) (Or.inl ?_)).mul
      (continuous_K_linha (by linarith))).mul (continuous_F_linha hσ)
    exact_mod_cast hx.ne'
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (x ^ σ * C * (2 / mK σ)))
    hcont.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
  have hKb := norm_K_mul_le (σ₀ := σ) (by linarith) (s := σ + τ * I) (by simp)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add] at hKb
  rw [norm_mul, norm_mul, norm_cpow_real hx]
  have hFb := (hd τ).2.2
  have hxσ : 0 ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  calc x ^ σ * ‖K (σ + τ * I)‖ * ‖F (σ + τ * I)‖ ≤ x ^ σ * ‖K (σ + τ * I)‖ * (C * (1 + |τ|)) :=
        mul_le_mul_of_nonneg_left hFb (by positivity)
    _ = x ^ σ * C * (‖K (σ + τ * I)‖ * (1 + |τ|)) := by ring
    _ ≤ x ^ σ * C * (2 / (mK σ * (1 + τ ^ 2))) := mul_le_mul_of_nonneg_left hKb (by positivity)
    _ = x ^ σ * C * (2 / mK σ) * (1 + τ ^ 2)⁻¹ := by field_simp

theorem integrable_K_cpow {σ : ℝ} (hσ : σ < 2) {y : ℝ} (hy : 0 < y) :
    Integrable (fun τ : ℝ => (y : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I)) := by
  have hcont : Continuous (fun τ : ℝ => (y : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I)) := by
    refine (Continuous.const_cpow (by fun_prop) (Or.inl ?_)).mul (continuous_K_linha hσ)
    exact_mod_cast hy.ne'
  refine Integrable.mono' ((integrable_K_linha hσ).norm.const_mul (y ^ σ))
    hcont.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
  rw [norm_mul, norm_cpow_real hy]

/-- `(k + 1)^{−s} N^s = (N/(k + 1))^s`. -/
theorem cpow_quociente {x : ℝ} (hx : 0 < x) (k : ℕ) (s : ℂ) :
    ((k + 1 : ℕ) : ℂ) ^ (-s) * (x : ℂ) ^ s = (((x / (k + 1 : ℕ) : ℝ)) : ℂ) ^ s := by
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  rw [div_eq_mul_inv, ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx.le (inv_nonneg.mpr hk.le),
    ofReal_inv, Complex.inv_cpow _ _ (by
      rw [show ((k + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℂ).re by simp]
      rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_pos.ne),
    Complex.cpow_neg]
  push_cast
  ring

/-- **A cota inferior** (`piso_G`): para `Θ < σ < 1`, `N ≥ 1`, `x ≥ N` e **todo** `c : Fin N → ℝ`,
`(2π)² ‖G_σ(x)‖² ≤ x^{2σ} (2π W_σ(c)) B`, com `B = ∫ ‖s K(s) F(s)‖² dτ` (só depende de `σ`).
Os termos de `P(s) = Σ c_k (k + 1)^{−s}` somem porque `ψ((k + 1)/x) = 0` para `k + 1 ≤ N ≤ x`. -/
theorem piso_G {σ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : (N : ℝ) ≤ x)
    (c : Fin N → ℝ) :
    (2 * π) ^ 2 * ‖Gl σ x‖ ^ 2 ≤ x ^ (2 * σ) * ((2 * π) * Wσ σ c) * ∫ τ, hK σ τ ^ 2 := by
  obtain ⟨C, hC, hd⟩ := dados_reta hσ hσ1
  have hθ := meio_le_Teta
  have hσ0 : 0 < σ := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hx0 : 0 < x := lt_of_lt_of_le hN0 hx
  set P : ℂ → ℂ := fun s => ∑ k : Fin N, (c k : ℂ) * ((k.val + 1 : ℕ) : ℂ) ^ (-s) with hP
  set M : ℝ → ℂ := fun τ => (1 + riemannZeta ((σ : ℂ) + τ * I) * P ((σ : ℂ) + τ * I)) /
    ((σ : ℂ) + τ * I) with hM
  set L : ℝ → ℂ := fun τ => M τ * (((σ : ℂ) + τ * I) * K (σ + τ * I) * F (σ + τ * I) *
    (x : ℂ) ^ ((σ : ℂ) + τ * I)) with hL
  -- identidade ponto a ponto
  have hs0 : ∀ τ : ℝ, ((σ : ℂ) + τ * I) ≠ 0 := by
    intro τ h; have := congrArg Complex.re h; simp at this; linarith
  have hid : ∀ τ : ℝ, L τ = (x : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I) * F (σ + τ * I) +
      ∑ k : Fin N, (c k : ℂ) * (((x / (k.val + 1 : ℕ) : ℝ) : ℂ) ^ ((σ : ℂ) + τ * I) *
        K (σ + τ * I)) := by
    intro τ
    have hzF := (hd τ).2.1
    have e1 : M τ * ((σ : ℂ) + τ * I) = 1 + riemannZeta ((σ : ℂ) + τ * I) * P ((σ : ℂ) + τ * I) := by
      rw [hM]; field_simp [hs0 τ]
    have e2 : P ((σ : ℂ) + τ * I) * (x : ℂ) ^ ((σ : ℂ) + τ * I) =
        ∑ k : Fin N, (c k : ℂ) * ((x / (k.val + 1 : ℕ) : ℝ) : ℂ) ^ ((σ : ℂ) + τ * I) := by
      rw [hP, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_assoc, cpow_quociente hx0]
    have e3 : (1 + riemannZeta ((σ : ℂ) + τ * I) * P ((σ : ℂ) + τ * I)) * F ((σ : ℂ) + τ * I) =
        F ((σ : ℂ) + τ * I) + P ((σ : ℂ) + τ * I) := by
      linear_combination P ((σ : ℂ) + τ * I) * hzF
    calc L τ = (M τ * ((σ : ℂ) + τ * I)) * F (σ + τ * I) * K (σ + τ * I) *
          (x : ℂ) ^ ((σ : ℂ) + τ * I) := by rw [hL]; ring
      _ = (F (σ + τ * I) + P ((σ : ℂ) + τ * I)) * K (σ + τ * I) * (x : ℂ) ^ ((σ : ℂ) + τ * I) := by
          rw [e1, e3]
      _ = (x : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I) * F (σ + τ * I) +
          (P ((σ : ℂ) + τ * I) * (x : ℂ) ^ ((σ : ℂ) + τ * I)) * K (σ + τ * I) := by ring
      _ = _ := by rw [e2, Finset.sum_mul]; congr 1; refine Finset.sum_congr rfl fun k _ => ?_; ring
  -- a integral de `L` é `2π G(N)`
  have hint0 := integrable_KF hσ hσ1 hx0
  have hintk : ∀ k : Fin N, Integrable (fun τ : ℝ => (c k : ℂ) * (((x / (k.val + 1 : ℕ) : ℝ) : ℂ) ^
      ((σ : ℂ) + τ * I) * K (σ + τ * I))) := fun k =>
    (integrable_K_cpow (by linarith) (by positivity)).const_mul _
  have hzero : ∀ k : Fin N, ∫ τ : ℝ, (c k : ℂ) * (((x / (k.val + 1 : ℕ) : ℝ) : ℂ) ^
      ((σ : ℂ) + τ * I) * K (σ + τ * I)) = 0 := by
    intro k
    rw [integral_const_mul, inv_K_zero (by linarith), mul_zero]
    rw [le_div_iff₀ (by positivity), one_mul]
    exact le_trans (by exact_mod_cast k.isLt) hx
  have hIL : ∫ τ, L τ = 2 * π * Gl σ x := by
    simp_rw [hid]
    rw [integral_add hint0 (integrable_finsetSum _ fun k _ => hintk k), integral_finsetSum _ fun k _ => hintk k]
    simp_rw [hzero]
    rw [Finset.sum_const_zero, add_zero, Gl]
    have : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity)
    rw [← mul_assoc, mul_one_div_cancel this, one_mul]
  -- norma de `L`
  have hnormL : ∀ τ : ℝ, ‖L τ‖ = Real.sqrt (espectroσ σ c τ) * hK σ τ * x ^ σ := by
    intro τ
    rw [hL, norm_mul, norm_mul, norm_cpow_real hx0, espectroσ, Real.sqrt_sq (norm_nonneg _), hK]
    exact (mul_assoc _ _ _).symm
  have hesp := integrable_espectro hσ0 hσ1 c
  have hesp0 : ∀ τ, 0 ≤ espectroσ σ c τ := fun τ => by unfold espectroσ; positivity
  have hB := integrable_hK_sq hσ hσ1
  -- Cauchy–Schwarz
  have hf : MemLp (fun τ => Real.sqrt (espectroσ σ c τ)) (ENNReal.ofReal 2) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq_norm
      (Real.continuous_sqrt.comp_aestronglyMeasurable hesp.aestronglyMeasurable)).mpr ?_
    refine hesp.congr (ae_of_all _ fun τ => ?_)
    simp only [Real.norm_eq_abs, sq_abs]
    rw [Real.sq_sqrt (hesp0 τ)]
  have hg : MemLp (fun τ => hK σ τ) (ENNReal.ofReal 2) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    have hmeas : AEStronglyMeasurable (fun τ => hK σ τ) :=
      (Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable).congr
        (ae_of_all _ fun τ => by
          show Real.sqrt (hK σ τ ^ 2) = hK σ τ
          exact Real.sqrt_sq (norm_nonneg _))
    refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
    refine hB.congr (ae_of_all _ fun τ => ?_)
    simp [Real.norm_eq_abs, sq_abs]
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun τ => Real.sqrt_nonneg _) (ae_of_all _ fun τ => norm_nonneg _) hf hg
  simp only [Real.rpow_two] at hCS
  have e4 : ∫ τ, Real.sqrt (espectroσ σ c τ) ^ 2 = 2 * π * Wσ σ c := by
    rw [Wσ_espectral hσ0 hσ1 c]
    have : ∀ τ, Real.sqrt (espectroσ σ c τ) ^ 2 = espectroσ σ c τ := fun τ => Real.sq_sqrt (hesp0 τ)
    simp_rw [this]
    field_simp
  rw [e4] at hCS
  -- montagem
  have hle : ‖2 * π * Gl σ x‖ ≤ x ^ σ * ((2 * π * Wσ σ c) ^ (1 / 2 : ℝ) *
      (∫ τ, hK σ τ ^ 2) ^ (1 / 2 : ℝ)) := by
    rw [← hIL]
    calc ‖∫ τ, L τ‖ ≤ ∫ τ, ‖L τ‖ := norm_integral_le_integral_norm _
      _ = (∫ τ, Real.sqrt (espectroσ σ c τ) * hK σ τ) * x ^ σ := by
          simp_rw [hnormL]; rw [integral_mul_const]
      _ ≤ ((2 * π * Wσ σ c) ^ (1 / 2 : ℝ) * (∫ τ, hK σ τ ^ 2) ^ (1 / 2 : ℝ)) * x ^ σ :=
          mul_le_mul_of_nonneg_right hCS (Real.rpow_nonneg hx0.le _)
      _ = _ := by ring
  have hW0 : 0 ≤ 2 * π * Wσ σ c := by have := Wσ_nonneg σ c; positivity
  have hB0 : 0 ≤ ∫ τ, hK σ τ ^ 2 := integral_nonneg fun τ => sq_nonneg _
  have hl0 : 0 ≤ ‖2 * π * Gl σ x‖ := norm_nonneg _
  have hsq := pow_le_pow_left₀ hl0 hle 2
  rw [mul_pow, mul_pow, ← Real.rpow_natCast ((2 * π * Wσ σ c) ^ (1 / 2 : ℝ)),
    ← Real.rpow_natCast ((∫ τ, hK σ τ ^ 2) ^ (1 / 2 : ℝ)), ← Real.rpow_mul hW0, ← Real.rpow_mul hB0,
    ← Real.rpow_natCast (x ^ σ), ← Real.rpow_mul hx0.le] at hsq
  norm_num at hsq
  rw [show σ * 2 = 2 * σ by ring] at hsq
  calc (2 * π) ^ 2 * ‖Gl σ x‖ ^ 2 = (2 * π * ‖Gl σ x‖) ^ 2 := by ring
    _ ≤ _ := hsq
    _ = _ := by ring

/-! ## 5. O deslocamento até a reta `Re s = 3/2` e a série de Möbius -/

open ATK.ZeroClasses.LittlewoodMu (mu norm_mu_le LSeries_mu)

theorem K_ne_zero {s : ℂ} (hs : s.re < 2) : K s ≠ 0 := by
  have h2 : (2 : ℂ) - s ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h3 : (3 : ℂ) - s ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h4 : (4 : ℂ) - s ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  unfold K
  exact one_div_ne_zero (mul_ne_zero (mul_ne_zero h2 h3) h4)

theorem differentiableAt_K {s : ℂ} (hs : s.re < 2) : DifferentiableAt ℂ K s := by
  have hne : (2 - s) * (3 - s) * (4 - s) ≠ 0 := by
    intro h; apply K_ne_zero hs; unfold K; rw [h, div_zero]
  show DifferentiableAt ℂ (fun s : ℂ => 1 / ((2 - s) * (3 - s) * (4 - s))) s
  exact (differentiableAt_const (1 : ℂ)).div (by fun_prop) hne

/-- `‖F(s)‖ ≤ C(1 + |Im s|)` em todo o semiplano `Re s ≥ σ₀` (`Θ < σ₀ < 1`). -/
theorem faixa_F {σ₀ : ℝ} (h0 : Teta < σ₀) (h1 : σ₀ < 1) :
    ∃ C, 0 < C ∧ ∀ s : ℂ, σ₀ ≤ s.re → ‖F s‖ ≤ C * (1 + |s.im|) := by
  have hθ := meio_le_Teta
  obtain ⟨C, hC, hF⟩ := norm_F_le semZeros_Teta hθ (by linarith) (δ := σ₀ - Teta) (η := 1 / 2)
    (by linarith) (by linarith) (by norm_num)
  refine ⟨C, hC, fun s hs => ?_⟩
  have h := hF s (by linarith)
  have h1' : (1 + |s.im|) ^ (1 / 2 : ℝ) ≤ 1 + |s.im| := by
    have : 1 ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
    calc (1 + |s.im|) ^ (1 / 2 : ℝ) ≤ (1 + |s.im|) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le this (by norm_num)
      _ = 1 + |s.im| := Real.rpow_one _
  exact h.trans (mul_le_mul_of_nonneg_left h1' hC.le)

theorem integrable_KF' {σ₀ σ : ℝ} (h0 : Teta < σ₀) (h1 : σ₀ < 1) (hσ : σ₀ ≤ σ) (hσ2 : σ < 2)
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun τ : ℝ => (x : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I) * F (σ + τ * I)) := by
  obtain ⟨C, hC, hF⟩ := faixa_F h0 h1
  have hm := mK_pos hσ2
  have hcont : Continuous (fun τ : ℝ => (x : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I) * F (σ + τ * I)) := by
    refine ((Continuous.const_cpow (by fun_prop) (Or.inl ?_)).mul
      (continuous_K_linha hσ2)).mul (continuous_F_linha (by linarith))
    exact_mod_cast hx.ne'
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (x ^ σ * C * (2 / mK σ)))
    hcont.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
  have hKb := norm_K_mul_le (σ₀ := σ) hσ2 (s := σ + τ * I) (by simp)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add] at hKb
  have hFb := hF (σ + τ * I) (by simpa using hσ)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add] at hFb
  rw [norm_mul, norm_mul, norm_cpow_real hx]
  have hxσ : 0 ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  calc x ^ σ * ‖K (σ + τ * I)‖ * ‖F (σ + τ * I)‖ ≤ x ^ σ * ‖K (σ + τ * I)‖ * (C * (1 + |τ|)) :=
        mul_le_mul_of_nonneg_left hFb (by positivity)
    _ = x ^ σ * C * (‖K (σ + τ * I)‖ * (1 + |τ|)) := by ring
    _ ≤ x ^ σ * C * (2 / (mK σ * (1 + τ ^ 2))) := mul_le_mul_of_nonneg_left hKb (by positivity)
    _ = x ^ σ * C * (2 / mK σ) * (1 + τ ^ 2)⁻¹ := by field_simp

theorem differentiableAt_f {x : ℝ} (hx : 0 < x) {z : ℂ} (h1 : Teta < z.re) (h2 : z.re < 2) :
    DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s * K s * F s) z := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hc : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) z :=
    differentiableAt_id.const_cpow (Or.inl hx')
  exact (hc.mul (differentiableAt_K h2)).mul (differentiableAt_F semZeros_Teta h1)

theorem rpow_le_soma {x a b u : ℝ} (hx : 0 < x) (hu : u ∈ Icc a b) : x ^ u ≤ x ^ a + x ^ b := by
  rcases le_or_gt 1 x with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h hu.2
    linarith [Real.rpow_nonneg hx.le a]
  · have := Real.rpow_le_rpow_of_exponent_ge hx h.le hu.1
    linarith [Real.rpow_nonneg hx.le b]

/-- **Deslocamento**: `G_σ(x) = G_{3/2}(x)` para `Θ < σ < 1`, `x > 0` (o integrando `x^s K(s)/ζ(s)` é
holomorfo em `σ ≤ Re s ≤ 3/2` e decai como `|Im s|^{−1}` nos segmentos horizontais). -/
theorem Gl_desloca {σ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) {x : ℝ} (hx : 0 < x) :
    Gl σ x = Gl (3 / 2) x := by
  obtain ⟨C, hC, hF⟩ := faixa_F hσ hσ1
  have hm := mK_pos (σ₀ := 3 / 2) (by norm_num)
  set f : ℂ → ℂ := fun s => (x : ℂ) ^ s * K s * F s with hf
  have hdiff : ∀ z : ℂ, z.re ∈ Icc σ (3 / 2) → DifferentiableAt ℂ f z := fun z hz =>
    differentiableAt_f hx (by linarith [hz.1]) (by linarith [hz.2])
  have hdecay : ∀ η > 0, ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc σ (3 / 2 : ℝ),
      ‖f (u + T * I)‖ ≤ η ∧ ‖f (u + ((-T : ℝ) : ℂ) * I)‖ ≤ η := by
    intro η hη
    set A := (x ^ σ + x ^ (3 / 2 : ℝ)) * C * (2 / mK (3 / 2)) with hA
    have hA0 : 0 ≤ A := by positivity
    filter_upwards [eventually_ge_atTop (A / η + 1)] with T hT
    have hAη : 0 ≤ A / η := by positivity
    have hT1 : 1 ≤ T := by linarith
    have hbound : ∀ u ∈ Icc σ (3 / 2 : ℝ), ∀ t : ℝ, |t| = T → ‖f (u + t * I)‖ ≤ η := by
      intro u hu t ht
      have hre : ((u : ℂ) + t * I).re = u := by simp
      have him : ((u : ℂ) + t * I).im = t := by simp
      have hKb := norm_K_mul_le (σ₀ := 3 / 2) (by norm_num) (s := u + t * I) (by rw [hre]; exact hu.2)
      rw [him] at hKb
      have hFb := hF (u + t * I) (by rw [hre]; exact hu.1)
      rw [him] at hFb
      have hxu := rpow_le_soma hx hu
      have ht2 : t ^ 2 = T ^ 2 := by rw [← sq_abs, ht]
      have hxs : 0 ≤ x ^ σ + x ^ (3 / 2 : ℝ) := by positivity
      simp only [hf]
      rw [norm_mul, norm_mul, norm_cpow_real hx]
      calc x ^ u * ‖K (u + t * I)‖ * ‖F (u + t * I)‖
          ≤ (x ^ σ + x ^ (3 / 2 : ℝ)) * ‖K (u + t * I)‖ * (C * (1 + |t|)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hxu (norm_nonneg _)) hFb (norm_nonneg _)
              (by positivity)
        _ = (x ^ σ + x ^ (3 / 2 : ℝ)) * C * (‖K (u + t * I)‖ * (1 + |t|)) := by ring
        _ ≤ (x ^ σ + x ^ (3 / 2 : ℝ)) * C * (2 / (mK (3 / 2) * (1 + t ^ 2))) :=
            mul_le_mul_of_nonneg_left hKb (by positivity)
        _ = A / (1 + T ^ 2) := by rw [hA, ht2]; field_simp
        _ ≤ η := by
            rw [div_le_iff₀ (by positivity)]
            have hAT : A ≤ T * η := (div_le_iff₀ hη).mp (by linarith)
            have hTT : T ≤ T ^ 2 := by nlinarith
            nlinarith [mul_le_mul_of_nonneg_right hTT hη.le]
    intro u hu
    exact ⟨hbound u hu T (abs_of_pos (by linarith)),
      hbound u hu (-T) (by rw [abs_neg, abs_of_pos (by linarith)])⟩
  have key := ATK.PerronSuave.desloca (f := f) (a := σ) (b := 3 / 2) (by linarith) (s := ∅)
    countable_empty (fun z hz => (hdiff z hz).continuousAt.continuousWithinAt)
    (fun z hz => hdiff z (Ioo_subset_Icc_self hz.1))
    (integrable_KF' hσ hσ1 le_rfl (by linarith) hx)
    (integrable_KF' hσ hσ1 (by linarith) (by norm_num) hx) hdecay
  show (1 / (2 * π) : ℂ) * ∫ τ : ℝ, f (σ + τ * I) = (1 / (2 * π) : ℂ) * ∫ τ : ℝ, f ((3 / 2 : ℝ) + τ * I)
  rw [key]

theorem cpow_inv_neg {a : ℝ} (ha : 0 < a) (s : ℂ) : ((a⁻¹ : ℝ) : ℂ) ^ (-s) = (a : ℂ) ^ s := by
  rw [ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg ha.le]; exact Real.pi_pos.ne),
    Complex.cpow_neg, inv_inv]

/-- `∫ y^{σ+iτ} K(σ + iτ) dτ = 2π ψ(1/y)`. -/
theorem inv_K' {σ : ℝ} (hσ : σ < 2) {y : ℝ} (hy : 0 < y) :
    ∫ τ : ℝ, (y : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I) = 2 * π * (ψ y⁻¹ : ℂ) := by
  have h := inv_K hσ (inv_pos.mpr hy)
  simp_rw [cpow_inv_neg hy] at h
  rw [← h]
  have : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity)
  rw [← mul_assoc, mul_one_div_cancel this, one_mul]

/-- **A série de Möbius**: `G_{3/2}(x) = Σ_n μ(n) ψ(n/x)` (`= Σ_{n > x} μ(n) φ(x/n)`, `φ(y) = y²(1 − y)²/2`).
Na reta `Re s = 3/2`, `1/ζ(s) = Σ μ(n) n^{−s}` converge absolutamente e cada termo dá `inv_K'`. -/
theorem Gl_serie {x : ℝ} (hx : 0 < x) :
    Gl (3 / 2) x = ∑' n : ℕ, mu n * (ψ (n / x) : ℂ) := by
  set T : ℕ → ℝ → ℂ := fun n τ =>
    mu n * ((((x / n : ℝ)) : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + τ * I) * K (((3 / 2 : ℝ) : ℂ) + τ * I)) with hT
  have hre : ∀ τ : ℝ, 1 < (((3 / 2 : ℝ) : ℂ) + τ * I).re := fun τ => by simp; norm_num
  have hpt : ∀ τ : ℝ, (x : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + τ * I) * K (((3 / 2 : ℝ) : ℂ) + τ * I) *
      F (((3 / 2 : ℝ) : ℂ) + τ * I) = ∑' n : ℕ, T n τ := by
    intro τ
    rw [← LSeries_mu (hre τ), LSeries, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hT, mu]
    · rw [LSeries.term_of_ne_zero hn.ne']
      simp only [hT]
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_eq_mul_inv x, ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx.le (inv_nonneg.mpr hn'.le),
        ofReal_inv, Complex.inv_cpow _ _ (by
          rw [Complex.arg_ofReal_of_nonneg hn'.le]; exact Real.pi_pos.ne)]
      push_cast
      ring
  have hT0 : T 0 = fun _ => 0 := by funext τ; simp [hT, mu]
  have hTint : ∀ n : ℕ, Integrable (T n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hT0]; exact integrable_zero _ _ _
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      exact (integrable_K_cpow (σ := 3 / 2) (by norm_num) (div_pos hx hn')).const_mul (mu n)
  have hnorm : ∀ n : ℕ, ∫ τ, ‖T n τ‖ ≤
      x ^ (3 / 2 : ℝ) * (∫ τ : ℝ, ‖K (((3 / 2 : ℝ) : ℂ) + τ * I)‖) * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hT0]
      simp only [norm_zero, integral_zero]
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num), inv_zero, mul_zero]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have heq : ∀ τ : ℝ, ‖T n τ‖ = ‖mu n‖ * (x / n) ^ (3 / 2 : ℝ) * ‖K (((3 / 2 : ℝ) : ℂ) + τ * I)‖ := by
        intro τ
        simp only [hT]
        rw [norm_mul, norm_mul, norm_cpow_real (div_pos hx hn')]
        ring
      simp_rw [heq]
      rw [integral_const_mul, Real.div_rpow hx.le hn'.le]
      have hmu := norm_mu_le n
      calc ‖mu n‖ * (x ^ (3 / 2 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) * ∫ τ : ℝ, ‖K (((3 / 2 : ℝ) : ℂ) + τ * I)‖
          ≤ 1 * (x ^ (3 / 2 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) * ∫ τ : ℝ, ‖K (((3 / 2 : ℝ) : ℂ) + τ * I)‖ := by
            gcongr
        _ = _ := by ring
  have hsum : Summable (fun n : ℕ => ∫ τ, ‖T n τ‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hnorm
      ((Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2)).mul_left _)
  have hint : ∀ n : ℕ, ∫ τ, T n τ = mu n * (2 * π * (ψ (n / x) : ℂ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hT0, integral_zero]; simp [mu]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [hT]
      rw [integral_const_mul, inv_K' (σ := 3 / 2) (by norm_num) (div_pos hx hn'), inv_div]
  show (1 / (2 * π) : ℂ) * ∫ τ : ℝ, (x : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + τ * I) *
      K (((3 / 2 : ℝ) : ℂ) + τ * I) * F (((3 / 2 : ℝ) : ℂ) + τ * I) = _
  rw [integral_congr_ae (ae_of_all _ hpt), ← integral_tsum_of_summable_integral_norm hTint hsum]
  simp_rw [hint]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity)
  rw [show (1 / (2 * π) : ℂ) * (mu n * (2 * π * (ψ (n / x) : ℂ))) =
    mu n * (ψ (n / x) : ℂ) * ((2 * π : ℂ) * (1 / (2 * π))) by ring, mul_one_div_cancel this, mul_one]

/-- `G_σ(x) = Σ μ(n) ψ(n/x)` em qualquer reta `Θ < σ < 1`. -/
theorem Gl_mobius {σ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) {x : ℝ} (hx : 0 < x) :
    Gl σ x = ∑' n : ℕ, mu n * (ψ (n / x) : ℂ) := by
  rw [Gl_desloca hσ hσ1 hx, Gl_serie hx]

theorem norm_Gl_le (c : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖Gl c x‖ ≤ 1 / (2 * π) * x ^ c * ∫ τ : ℝ, ‖K (c + τ * I) * F (c + τ * I)‖ := by
  unfold Gl
  rw [norm_mul]
  have h1 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by simp [abs_of_pos Real.pi_pos]
  rw [h1]
  have h2 : ‖∫ τ : ℝ, (x : ℂ) ^ ((c : ℂ) + τ * I) * K (c + τ * I) * F (c + τ * I)‖ ≤
      x ^ c * ∫ τ : ℝ, ‖K (c + τ * I) * F (c + τ * I)‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    rw [mul_assoc, norm_mul, norm_cpow_real hx]
  have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 1 / (2 * π) by positivity)
  linarith

theorem continuousAt_Gl {σ₀ c : ℝ} (h0 : Teta < σ₀) (h1 : σ₀ < 1) (hc : σ₀ ≤ c) (hc2 : c < 2)
    {x₀ : ℝ} (hx₀ : 0 < x₀) : ContinuousAt (Gl c) x₀ := by
  have hθ := meio_le_Teta
  have hc0 : 0 ≤ c := by linarith
  have hint := (integrable_KF' h0 h1 hc hc2 (x := 1) one_pos).norm
  show ContinuousAt (fun x : ℝ => (1 / (2 * π) : ℂ) *
    ∫ τ : ℝ, (x : ℂ) ^ ((c : ℂ) + τ * I) * K (c + τ * I) * F (c + τ * I)) x₀
  refine ContinuousAt.mul continuousAt_const ?_
  refine continuousAt_of_dominated (bound := fun τ => (2 * x₀) ^ c * ‖K (c + τ * I) * F (c + τ * I)‖)
    ?_ ?_ ?_ ?_
  · filter_upwards [lt_mem_nhds hx₀] with x hx
    exact (integrable_KF' h0 h1 hc hc2 hx).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds (half_lt_self hx₀) (by linarith : x₀ < 2 * x₀)] with x hx
    refine ae_of_all _ fun τ => ?_
    have hxpos : 0 < x := lt_trans (half_pos hx₀) hx.1
    rw [mul_assoc, norm_mul, norm_cpow_real hxpos]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hxpos.le hx.2.le hc0) (norm_nonneg _)
  · refine (hint.const_mul ((2 * x₀) ^ c)).congr (ae_of_all _ fun τ => ?_)
    simp only
    rw [mul_assoc, norm_mul (((1 : ℝ) : ℂ) ^ _), ofReal_one, one_cpow, norm_one, one_mul]
  · refine ae_of_all _ fun τ => ?_
    exact ((continuousAt_ofReal_cpow_const x₀ _ (Or.inr hx₀.ne')).mul continuousAt_const).mul
      continuousAt_const

/-! ## 6. A transformada de Mellin de `u ↦ G(1/u)`: `K(s)/ζ(s)` -/

/-- `g(u) = G_{3/2}(1/u) = Σ μ(n) ψ(nu)`. -/
noncomputable def gU (u : ℝ) : ℂ := Gl (3 / 2) u⁻¹

theorem gU_serie {u : ℝ} (hu : 0 < u) :
    gU u = ∑' n : ℕ, mu n * (ψ (n * u) : ℂ) := by
  rw [gU, Gl_serie (inv_pos.mpr hu)]
  simp_rw [div_inv_eq_mul]

theorem hasMellin_psi_n {s : ℂ} (hs : s.re < 2) {n : ℕ} (hn : 0 < n) :
    HasMellin (fun u : ℝ => (ψ (n * u) : ℂ)) s (((n : ℝ) : ℂ) ^ (-s) * K s) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := hasMellin_psi hs
  refine ⟨(MellinConvergent.comp_mul_left hn').mpr h.1, ?_⟩
  exact (mellin_comp_mul_left (fun t : ℝ => (ψ t : ℂ)) s hn').trans (by rw [smul_eq_mul, h.2])

theorem norm_integral_ofReal_nonneg {f : ℝ → ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hf : ∀ u ∈ S, 0 ≤ f u) : ∫ u in S, ‖(f u : ℂ)‖ = ‖∫ u in S, (f u : ℂ)‖ := by
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (setIntegral_nonneg hS hf)]
  refine setIntegral_congr_fun hS fun u hu => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (hf u hu)]

/-- **A transformada de Mellin**: `∫₀^∞ u^{s−1} G(1/u) du = K(s)/ζ(s)` para `1 < Re s < 2`. -/
theorem mellin_gU {s : ℂ} (hs1 : 1 < s.re) (hs2 : s.re < 2) :
    mellin gU s = K s * F s := by
  set Fn : ℕ → ℝ → ℂ := fun n u => (u : ℂ) ^ (s - 1) * (mu n * (ψ (n * u) : ℂ)) with hFn
  have e1 : mellin gU s = ∫ u in Ioi (0 : ℝ), ∑' n : ℕ, Fn n u := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    simp only [hFn, smul_eq_mul]
    rw [gU_serie hu, tsum_mul_left]
  have hF0 : Fn 0 = fun _ => 0 := by funext u; simp [hFn, mu]
  have hint : ∀ n : ℕ, Integrable (Fn n) (volume.restrict (Ioi 0)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hF0]; exact integrable_zero _ _ _
    · have h := (hasMellin_psi_n hs2 hn).1
      refine (Integrable.const_mul h (mu n)).congr (ae_of_all _ fun u => ?_)
      simp only [hFn, smul_eq_mul]
      ring
  have hnorm : ∀ n : ℕ, ∫ u, ‖Fn n u‖ ∂(volume.restrict (Ioi 0)) ≤
      ‖K (s.re : ℂ)‖ * ((n : ℝ) ^ s.re)⁻¹ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hF0]
      simp only [norm_zero, integral_zero]
      rw [Nat.cast_zero, Real.zero_rpow (by linarith), inv_zero, mul_zero]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hσ2 : ((s.re : ℂ)).re < 2 := by simpa using hs2
      have hM := hasMellin_psi_n hσ2 hn
      set r : ℝ → ℝ := fun u => u ^ (s.re - 1) * ψ (n * u) with hr
      have hr0 : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ r u := fun u hu =>
        mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _) (psi_nonneg _)
      have hg : ∀ u ∈ Ioi (0 : ℝ), (u : ℂ) ^ ((s.re : ℂ) - 1) • (ψ (n * u) : ℂ) = (r u : ℂ) := by
        intro u hu
        simp only [hr, smul_eq_mul, Complex.ofReal_mul]
        rw [Complex.ofReal_cpow (le_of_lt hu)]
        push_cast
        try ring
      have step1 : ∫ u in Ioi (0 : ℝ), ‖Fn n u‖ = ∫ u in Ioi (0 : ℝ), ‖mu n‖ * ‖(r u : ℂ)‖ := by
        refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
        have hu' : (0 : ℝ) < u := hu
        simp only [hFn]
        rw [← hg u hu, smul_eq_mul]
        simp only [norm_mul]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hu', Complex.norm_cpow_eq_rpow_re_of_pos hu']
        simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
        ring
      have e3 : ∫ u in Ioi (0 : ℝ), (r u : ℂ) = ((n : ℝ) : ℂ) ^ (-(s.re : ℂ)) * K (s.re : ℂ) := by
        rw [← hM.2, mellin]
        exact (setIntegral_congr_fun measurableSet_Ioi hg).symm
      rw [step1, integral_const_mul, norm_integral_ofReal_nonneg measurableSet_Ioi hr0, e3, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hn']
      simp only [neg_re, ofReal_re]
      rw [Real.rpow_neg hn'.le]
      have hmu := norm_mu_le n
      have hP : 0 ≤ ((n : ℝ) ^ s.re)⁻¹ * ‖K (s.re : ℂ)‖ := by positivity
      calc ‖mu n‖ * (((n : ℝ) ^ s.re)⁻¹ * ‖K (s.re : ℂ)‖) ≤ 1 * (((n : ℝ) ^ s.re)⁻¹ * ‖K (s.re : ℂ)‖) :=
            mul_le_mul_of_nonneg_right hmu hP
        _ = _ := by ring
  have hsum : Summable (fun n : ℕ => ∫ u, ‖Fn n u‖ ∂(volume.restrict (Ioi 0))) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hnorm
      ((Real.summable_nat_rpow_inv.mpr hs1).mul_left _)
  have hval : ∀ n : ℕ, ∫ u in Ioi (0 : ℝ), Fn n u = K s * LSeries.term mu s n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hF0, integral_zero]; simp
    · have hM := hasMellin_psi_n hs2 hn
      rw [LSeries.term_of_ne_zero hn.ne']
      have e : ∫ u in Ioi (0 : ℝ), Fn n u = mu n * mellin (fun u : ℝ => (ψ (n * u) : ℂ)) s := by
        rw [mellin, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
        simp only [hFn, smul_eq_mul]
        ring
      rw [e, hM.2, Complex.cpow_neg]
      push_cast
      ring
  rw [e1, ← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [hval]
  rw [tsum_mul_left]
  show K s * LSeries mu s = K s * F s
  rw [LSeries_mu hs1]

theorem gU_top :
    gU =O[atTop] (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound
    (1 / (2 * π) * ∫ τ : ℝ, ‖K (((3 / 2 : ℝ) : ℂ) + τ * I) * F (((3 / 2 : ℝ) : ℂ) + τ * I)‖) ?_
  filter_upwards [eventually_gt_atTop 0] with u hu
  rw [gU, Real.norm_of_nonneg (Real.rpow_nonneg hu.le _)]
  have h := norm_Gl_le (3 / 2) (inv_pos.mpr hu)
  rw [Real.inv_rpow hu.le, ← Real.rpow_neg hu.le] at h
  linarith

theorem gU_bot {σ θ C : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1)
    (h : ∀ x : ℝ, 1 ≤ x → ‖Gl σ x‖ ≤ C * x ^ θ) : gU =O[𝓝[>] 0] (fun u : ℝ => u ^ (-θ)) := by
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
  rw [gU, ← Gl_desloca hσ hσ1 (inv_pos.mpr hu.1), Real.norm_of_nonneg (Real.rpow_nonneg hu.1.le _),
    Real.rpow_neg hu.1.le, ← Real.inv_rpow hu.1.le]
  exact h u⁻¹ ((one_le_inv₀ hu.1).mpr hu.2.le)

/-! ## 7. A cota `|G(x)| ≤ C x^θ` dá `ζ ≠ 0` em `Re s > θ`; o expoente exato -/

/-- **Continuação**: se `‖G_σ(x)‖ ≤ C x^θ` para `x ≥ 1`, então `K(s)/ζ(s)` (a transformada de Mellin de
`G(1/u)`) é holomorfa em `θ < Re s < 3/2`, e `1/ζ` estende-se a `Re s > θ`: não há zeros em `Re s > θ`. -/
theorem semZeros_of_cota {σ θ C : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1)
    (h : ∀ x : ℝ, 1 ≤ x → ‖Gl σ x‖ ≤ C * x ^ θ) : SemZeros θ := by
  have hloc : LocallyIntegrableOn gU (Ioi 0) := by
    refine ContinuousOn.locallyIntegrableOn (fun u hu => ?_) measurableSet_Ioi
    have hu' : (0 : ℝ) < u := hu
    exact ((continuousAt_Gl hσ hσ1 (c := 3 / 2) (by linarith) (by norm_num) (inv_pos.mpr hu')).comp
      (continuousAt_inv₀ hu'.ne')).continuousWithinAt
  have htop := gU_top
  have hbot := gU_bot hσ hσ1 h
  have hM : ∀ s : ℂ, 1 < s.re → s.re < 2 → mellin gU s / K s = F s := fun s h1 h2 => by
    rw [mellin_gU h1 h2, mul_div_cancel_left₀ _ (K_ne_zero h2)]
  set G : ℂ → ℂ := fun s => if s.re < 5 / 4 then mellin gU s / K s else F s with hG
  refine ATK.ZeroClasses.Unilateral.semZeros_of_ext_mertens (G := G) (fun s hs => ?_) (fun s hs => ?_)
  · rcases lt_or_ge s.re (3 / 2) with h32 | h32
    · have hev : G =ᶠ[𝓝 s] fun w => mellin gU w / K w := by
        filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds h32] with w hw
        have hw' : w.re < 3 / 2 := hw
        simp only [hG]
        by_cases h54 : w.re < 5 / 4
        · simp only [h54, ↓reduceIte]
        · simp only [h54, ↓reduceIte]
          exact (hM w (by linarith) (by linarith)).symm
      exact DifferentiableAt.congr_of_eventuallyEq
        ((mellin_differentiableAt_of_isBigO_rpow hloc htop h32 hbot hs).div
          (differentiableAt_K (by linarith)) (K_ne_zero (by linarith))) hev
    · have hev : G =ᶠ[𝓝 s] F := by
        filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
          (show (5 / 4 : ℝ) < s.re by linarith)] with w hw
        have hw' : (5 / 4 : ℝ) < w.re := hw
        have h54 : ¬ w.re < 5 / 4 := by linarith
        simp only [hG, h54, ↓reduceIte]
      exact (differentiableAt_F semZeros_Teta (by linarith)).congr_of_eventuallyEq hev
  · simp only [hG]
    by_cases h54 : s.re < 5 / 4
    · simp only [h54, ↓reduceIte]; exact hM s hs (by linarith)
    · simp only [h54, ↓reduceIte]

/-- **O piso em `D_N(σ)`**: para `Θ < σ < 1`, `N ≥ 1` e `x ≥ N`,
`(2π)² ‖G_σ(x)‖² ≤ 2π B x^{2σ} D_N(σ)`. -/
theorem piso_DN {σ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : (N : ℝ) ≤ x) :
    (2 * π) ^ 2 * ‖Gl σ x‖ ^ 2 ≤ x ^ (2 * σ) * (2 * π) * (∫ τ, hK σ τ ^ 2) * DNσ σ N := by
  have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hN) hx
  have hB0 : 0 ≤ ∫ τ, hK σ τ ^ 2 := integral_nonneg fun τ => sq_nonneg _
  have hk : 0 ≤ x ^ (2 * σ) * (2 * π) * ∫ τ, hK σ τ ^ 2 := by positivity
  rw [DNσ, Real.mul_iInf_of_nonneg hk]
  refine le_ciInf fun c => ?_
  have := piso_G hσ hσ1 hN hx c
  linarith

/-- **O teto**: `TaxaDN σ κ ⟹ κ ≤ 2(σ − Θ)` para `Θ < σ < 1`. -/
theorem taxa_le_Teta {σ κ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) (h : TaxaDN σ κ) :
    κ ≤ 2 * (σ - Teta) := by
  by_contra hlt
  push Not at hlt
  set δ := (2 * (σ - Teta) + κ) / 2 with hδ
  have hδκ : δ < κ := by linarith
  have hδT : 2 * (σ - Teta) < δ := by linarith
  have hδ0 : 0 < δ := by linarith
  obtain ⟨K₀, hK₀⟩ := h δ hδκ
  set K₁ := max K₀ 0 with hK₁
  have hK₁0 : 0 ≤ K₁ := le_max_right _ _
  set B := ∫ τ, hK σ τ ^ 2 with hB
  have hB0 : 0 ≤ B := integral_nonneg fun τ => sq_nonneg _
  set A := 2 * π * B * K₁ * 2 ^ δ with hA
  have hA0 : 0 ≤ A := by positivity
  set θ := σ - δ / 2 with hθ
  have hθT : θ < Teta := by linarith
  have hcota : ∀ x : ℝ, 1 ≤ x → ‖Gl σ x‖ ≤ Real.sqrt A / (2 * π) * x ^ θ := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
    have hxN : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    have hN1' : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
    have hpiso := piso_DN hσ hσ1 hN1 hNx
    have hD' : DNσ σ ⌊x⌋₊ ≤ K₁ * (⌊x⌋₊ : ℝ) ^ (-δ) :=
      (hK₀ _ hN1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hNd : (⌊x⌋₊ : ℝ) ^ (-δ) ≤ 2 ^ δ * x ^ (-δ) := by
      have h1 : (⌊x⌋₊ : ℝ) ^ (-δ) ≤ (x / 2) ^ (-δ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      rw [Real.div_rpow hx0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_inv_eq_mul] at h1
      linarith
    have hsq : (2 * π) ^ 2 * ‖Gl σ x‖ ^ 2 ≤ A * x ^ (2 * θ) := by
      have e : x ^ (2 * θ) = x ^ (2 * σ) * x ^ (-δ) := by
        rw [← Real.rpow_add hx0]; congr 1; rw [hθ]; ring
      rw [e]
      calc (2 * π) ^ 2 * ‖Gl σ x‖ ^ 2 ≤ x ^ (2 * σ) * (2 * π) * B * DNσ σ ⌊x⌋₊ := hpiso
        _ ≤ x ^ (2 * σ) * (2 * π) * B * (K₁ * (2 ^ δ * x ^ (-δ))) := by
            gcongr
            exact hD'.trans (mul_le_mul_of_nonneg_left hNd hK₁0)
        _ = A * (x ^ (2 * σ) * x ^ (-δ)) := by rw [hA]; ring
    have hR : 0 ≤ Real.sqrt A / (2 * π) * x ^ θ := by positivity
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero]
    have hxθ : (x ^ θ) ^ 2 = x ^ (2 * θ) := by
      rw [mul_comm (2 : ℝ) θ, Real.rpow_mul hx0.le, Real.rpow_two]
    have e2 : (Real.sqrt A / (2 * π) * x ^ θ) ^ 2 = A * x ^ (2 * θ) / (2 * π) ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt hA0, hxθ]; ring
    rw [e2, le_div_iff₀ (by positivity)]
    linarith
  exact ATK.ZeroClasses.Unilateral.nao_semZeros hθT (semZeros_of_cota hσ hσ1 hcota)

/-- **O expoente exato** (proposta R105): `2(σ − Θ)` é o **maior** `κ` com `TaxaDN σ κ`. -/
theorem kappa_exato {σ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) :
    IsGreatest {κ : ℝ | TaxaDN σ κ} (2 * (σ - Teta)) :=
  ⟨taxa_Teta hσ hσ1, fun _ hκ => taxa_le_Teta hσ hσ1 hκ⟩

theorem sSup_taxa {σ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) :
    sSup {κ : ℝ | TaxaDN σ κ} = 2 * (σ - Teta) :=
  (kappa_exato hσ hσ1).csSup_eq

/-- `Θ` lido numa única reta: `Θ = σ − κ(σ)/2`. -/
theorem Teta_eq_taxa {σ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) :
    Teta = σ - sSup {κ : ℝ | TaxaDN σ κ} / 2 := by
  rw [sSup_taxa hσ hσ1]; ring

theorem nao_taxa {σ κ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) (hκ : 2 * (σ - Teta) < κ) : ¬ TaxaDN σ κ :=
  fun h => absurd (taxa_le_Teta hσ hσ1 h) (not_le.mpr hκ)

/-- Numa reta `Θ < σ < 1`: RH ⟺ `D_N(σ) ≪ N^{−δ}` para todo `δ < 2σ − 1`. -/
theorem rh_iff_taxa {σ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) :
    RiemannHypothesis ↔ TaxaDN σ (2 * σ - 1) := by
  rw [ATK.ZeroClasses.BDTheta.rh_iff_Teta]
  constructor
  · intro hT
    have := taxa_Teta hσ hσ1
    rw [hT] at this
    convert this using 1
    ring
  · intro h
    have h1 := taxa_le_Teta hσ hσ1 h
    have h2 := meio_le_Teta
    exact le_antisymm (by linarith) h2

/-- **`Ω` para a Mertens suavizada**: para `θ < Θ`, `G_σ(x) = Σ μ(n) ψ(n/x)` não é `O(x^θ)`. -/
theorem Gl_omega {σ θ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) (hθ : θ < Teta) (C : ℝ) :
    ∃ x : ℝ, 1 ≤ x ∧ C * x ^ θ < ‖Gl σ x‖ := by
  by_contra hne
  push Not at hne
  exact ATK.ZeroClasses.Unilateral.nao_semZeros hθ (semZeros_of_cota hσ hσ1 hne)

/-! ## 8. `PisoPonderado` (Q2(iii)) é um teorema -/

open ATK.ZeroClasses.BDTheta (PisoPonderado rh_iff_taxa_de_piso nao_taxa_abaixo)

/-- **Q2(iii)**: a proposição `BDTheta.PisoPonderado` (rodada 76, declarada OPEN_MATH) vale: para `Θ ≤ σ < 1`,
`TaxaDN σ κ ⟹ κ ≤ 2(σ − Θ)`. Em `σ = Θ`, uma taxa positiva daria `Θ < σ` (`BDTaxaPiso.taxaDN_pos`). -/
theorem pisoPonderado : PisoPonderado := by
  intro σ hσ hσ1 κ hκ
  rcases eq_or_lt_of_le hσ with heq | hlt
  · by_contra hgt
    push Not at hgt
    have hκ0 : 0 < κ := by rw [heq] at hgt; linarith
    have h0 : 0 < σ := by linarith [meio_le_Teta]
    have := ATK.ZeroClasses.BDTaxaPiso.taxaDN_pos h0 hσ1 hκ0 hκ
    linarith
  · exact taxa_le_Teta hlt hσ1 hκ

/-- **RH num único `σ₀`**, sem hipóteses: para qualquer `σ₀ ∈ (½, 1)` fixado,
RH ⟺ `D_N(σ₀) ≪ N^{−δ}` para todo `δ < 2σ₀ − 1`. -/
theorem rh_iff_taxa_um {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    RiemannHypothesis ↔ TaxaDN σ₀ (2 * σ₀ - 1) :=
  rh_iff_taxa_de_piso pisoPonderado h0 h1

/-- **O teto exato de `Θ` por uma taxa**: `TaxaDN σ κ` com `κ > 0`, `0 < σ < 1`, dá `Θ ≤ σ − κ/2`
(a forma exata de `BDTaxaPiso.Teta_le_de_taxaDN`). -/
theorem Teta_le_de_taxa {σ κ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hκ : 0 < κ) (h : TaxaDN σ κ) :
    Teta ≤ σ - κ / 2 := by
  have hT := ATK.ZeroClasses.BDTaxaPiso.taxaDN_pos hσ0 hσ1 hκ h
  have := taxa_le_Teta hT hσ1 h
  linarith

/-- **O perfil completo**: para `0 < σ < 1`, `TaxaDN σ κ ⟹ κ ≤ 2 max(σ − Θ, 0)`. -/
theorem taxa_le_perfil {σ κ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (h : TaxaDN σ κ) :
    κ ≤ 2 * max (σ - Teta) 0 := by
  rcases le_or_gt Teta σ with hT | hT
  · exact (pisoPonderado σ hT hσ1 κ h).trans (by gcongr; exact le_max_left _ _)
  · by_contra hgt
    push Not at hgt
    have hκ : 0 < κ := lt_of_le_of_lt (by positivity) hgt
    exact nao_taxa_abaixo hσ0 hT hκ h

end ATK.ZeroClasses.BDPisoExato

#print axioms ATK.ZeroClasses.BDPisoExato.psi_eq_zero
#print axioms ATK.ZeroClasses.BDPisoExato.psi_nonneg
#print axioms ATK.ZeroClasses.BDPisoExato.continuousAt_psi
#print axioms ATK.ZeroClasses.BDPisoExato.cpow_neg_nat
#print axioms ATK.ZeroClasses.BDPisoExato.psi_formula
#print axioms ATK.ZeroClasses.BDPisoExato.integrando_formula
#print axioms ATK.ZeroClasses.BDPisoExato.integrableOn_pow
#print axioms ATK.ZeroClasses.BDPisoExato.integral_pow
#print axioms ATK.ZeroClasses.BDPisoExato.integrando_indicator
#print axioms ATK.ZeroClasses.BDPisoExato.hasMellin_psi
#print axioms ATK.ZeroClasses.BDPisoExato.norm_sub_sq_ge
#print axioms ATK.ZeroClasses.BDPisoExato.mK_pos
#print axioms ATK.ZeroClasses.BDPisoExato.norm_sub_sq_ge'
#print axioms ATK.ZeroClasses.BDPisoExato.norm_K_sq_le
#print axioms ATK.ZeroClasses.BDPisoExato.norm_K_le
#print axioms ATK.ZeroClasses.BDPisoExato.continuous_K_linha
#print axioms ATK.ZeroClasses.BDPisoExato.integrable_K_linha
#print axioms ATK.ZeroClasses.BDPisoExato.inv_K
#print axioms ATK.ZeroClasses.BDPisoExato.inv_K_zero
#print axioms ATK.ZeroClasses.BDPisoExato.integrable_espectro
#print axioms ATK.ZeroClasses.BDPisoExato.norm_K_mul_le
#print axioms ATK.ZeroClasses.BDPisoExato.dados_reta
#print axioms ATK.ZeroClasses.BDPisoExato.continuous_F_linha
#print axioms ATK.ZeroClasses.BDPisoExato.norm_cpow_real
#print axioms ATK.ZeroClasses.BDPisoExato.integrable_hK_sq
#print axioms ATK.ZeroClasses.BDPisoExato.integrable_KF
#print axioms ATK.ZeroClasses.BDPisoExato.integrable_K_cpow
#print axioms ATK.ZeroClasses.BDPisoExato.cpow_quociente
#print axioms ATK.ZeroClasses.BDPisoExato.piso_G
#print axioms ATK.ZeroClasses.BDPisoExato.K_ne_zero
#print axioms ATK.ZeroClasses.BDPisoExato.differentiableAt_K
#print axioms ATK.ZeroClasses.BDPisoExato.faixa_F
#print axioms ATK.ZeroClasses.BDPisoExato.integrable_KF'
#print axioms ATK.ZeroClasses.BDPisoExato.differentiableAt_f
#print axioms ATK.ZeroClasses.BDPisoExato.rpow_le_soma
#print axioms ATK.ZeroClasses.BDPisoExato.Gl_desloca
#print axioms ATK.ZeroClasses.BDPisoExato.cpow_inv_neg
#print axioms ATK.ZeroClasses.BDPisoExato.inv_K'
#print axioms ATK.ZeroClasses.BDPisoExato.Gl_serie
#print axioms ATK.ZeroClasses.BDPisoExato.Gl_mobius
#print axioms ATK.ZeroClasses.BDPisoExato.norm_Gl_le
#print axioms ATK.ZeroClasses.BDPisoExato.continuousAt_Gl
#print axioms ATK.ZeroClasses.BDPisoExato.gU_serie
#print axioms ATK.ZeroClasses.BDPisoExato.hasMellin_psi_n
#print axioms ATK.ZeroClasses.BDPisoExato.norm_integral_ofReal_nonneg
#print axioms ATK.ZeroClasses.BDPisoExato.mellin_gU
#print axioms ATK.ZeroClasses.BDPisoExato.gU_top
#print axioms ATK.ZeroClasses.BDPisoExato.gU_bot
#print axioms ATK.ZeroClasses.BDPisoExato.semZeros_of_cota
#print axioms ATK.ZeroClasses.BDPisoExato.piso_DN
#print axioms ATK.ZeroClasses.BDPisoExato.taxa_le_Teta
#print axioms ATK.ZeroClasses.BDPisoExato.kappa_exato
#print axioms ATK.ZeroClasses.BDPisoExato.sSup_taxa
#print axioms ATK.ZeroClasses.BDPisoExato.Teta_eq_taxa
#print axioms ATK.ZeroClasses.BDPisoExato.nao_taxa
#print axioms ATK.ZeroClasses.BDPisoExato.rh_iff_taxa
#print axioms ATK.ZeroClasses.BDPisoExato.Gl_omega
#print axioms ATK.ZeroClasses.BDPisoExato.pisoPonderado
#print axioms ATK.ZeroClasses.BDPisoExato.rh_iff_taxa_um
#print axioms ATK.ZeroClasses.BDPisoExato.Teta_le_de_taxa
#print axioms ATK.ZeroClasses.BDPisoExato.taxa_le_perfil
