# CvS index law in Lean 4

Lean 4 / Mathlib formalization of the finite-dimensional theorems in

> M. A. Oltulu, *Odd-sector, Pontryagin-space and index-law extensions of the Connes–van Suijlekom real-zeros theorem*, Zenodo, [doi:10.5281/zenodo.23459269](https://doi.org/10.5281/zenodo.23459269) (2026). ORCID [0009-0003-0928-0854](https://orcid.org/0009-0003-0928-0854).

## The statement (Theorem 6, resolvent lock)

Let $Q$ be a real symmetric matrix on $I=\{-N,\dots,N\}$ of Connes–van Suijlekom type,
$q_{ii}=a_i,\ q_{ij}=(b_i-b_j)/(i-j)$, $a$ even, $b$ odd. Put
$P_\xi(s)=\sum_k \xi_k\prod_{j\ne k}(j-s)$, let $\mu$ avoid the spectrum and $x=(Q-\mu)^{-1}e_0$. Then

$$N_c(P_x)+d(x)+[x_0<0]=\kappa(\mu),$$

where $N_c$ counts pairs of non-real zeros, $`d(x)=\mathrm{card}\,\lbrace s\in\mathbb{R}\setminus\lbrace 0\rbrace : P_x(s)=0,\ P_x'(s)\,P_{\beta\odot x}(s)>0\rbrace`$ and $\kappa(\mu)$ is the number of eigenvalues below $\mu$. At $\mu=0$ this reads the positivity of $Q$ from the zeros of one polynomial. The pen-and-paper proof is in the note; it goes through $[D,Q]=\beta\wedge\eta$ and a Bezout-matrix congruence (a Hermite-type signature count).

The theorem has been verified numerically with interval arithmetic on truncated Weil quadratic forms and on an Epstein zeta function with genuine off-line zeros ([doi:10.5281/zenodo.23458944](https://doi.org/10.5281/zenodo.23458944)).

## Status

| Lean declaration | Content | Proof |
|---|---|---|
| `CvS.isSymm_of_isCvS` | CvS matrices are symmetric | **proved** |
| `CvS.commutator` | Lemma 5.1, $`[D,Q]=\beta\wedge\eta`$ | **proved** |
| `CvS.commutator_shift` | the same for $`Q-\mu`$ | **proved** |
| `CvS.Dprime_mulVec_self` | Lemma 5.2(a), $`D'_\varphi\xi=0`$ | **proved** |
| `CvS.det_Dprime` | Lemma 5.2(b), rank-one determinant | **proved** |
| `CvS.Qlam_Dprime_isSymm` | Lemma 5.3, $`Q_\lambda D'_\varphi`$ symmetric for $`\varphi\in\mathrm{span}\{\eta,\beta\}`$ | **proved** |
| `CvS.nondeg_even` | Lemma 5.4, even sector: $`\langle\beta,\xi\rangle=0`$, $`\langle\eta,\xi\rangle\neq0`$ | **proved** |
| `CvS.Qlam_norm` | Lemma 5.5, $`Q_\lambda(w_s,w_s)=FG'-F'G`$ | **proved** |
| `CvS.kappa_eq_sigNeg` | bridge: eigenvalue count below $`\mu`$ = `sigNeg` of $`Q-\mu`$ (Sylvester) | **proved** |
| `CvS.eigvec_orth`, `CvS.block2_sigNeg` | Lemma 5.6 steps: eigenvector orthogonality; a 2×2 block with $`\det<0`$ has one negative direction | **proved** |
| `CvS.sigNeg_of_congr_diag`, `CvS.sigNeg_of_orth_family` | Lemma 5.6 step 3: a $`B`$-orthogonal family with nonzero norms counts $`\kappa`$ | **proved** |
| `CvS.eigvec_orth_field`, `CvS.conj_eigvec`, `CvS.herm_norm_zero` | Lemma 5.6 step 4a: a complex eigenvector with non-real eigenvalue has zero hermitian $`B`$-norm | **proved** |
| `CvS.herm_re`, `CvS.herm_split`, `CvS.real_pair_re_im`, `CvS.cross_orth` | Lemma 5.6 step 4b: $`B(u,u)+B(w,w)=0`$; real eigenvectors are $`B`$-orthogonal to $`u,w`$ | **proved** |
| `CvS.pair_orth`, `CvS.plane_split` | Lemma 5.6 step 4c: different pairs are $`B`$-orthogonal; each pair's plane splits into one positive and one negative direction | **proved** |
| `CvS.re_im_combo`, `CvS.real_family_indep` | Lemma 5.6 step 4d: the real family $`\{v_i,\ \mathrm{Re}\,z_k,\ \mathrm{Im}\,z_k\}`$ is linearly independent | **proved** |
| `CvS.null_vec_zero`, `CvS.not_null_member` | Lemma 5.6 step 4d: no member of a complete independent family is $`B`$-null to all members | **proved** |
| `CvS.pontryagin_balance` | **Lemma 5.6 (Pontryagin balance)**: $`\kappa = \#\{\text{real eigenvectors of negative norm}\} + \#\{\text{non-real pairs}\}`$ | **proved** |
| `CvS.Qmu_Dprime_lock_isSymm`, `CvS.F_zero_of_root`, `CvS.Dprime_eigvec_r`, `CvS.Dprime_eigvec_c` | Theorem 6 steps: lock symmetry; explicit eigenvectors $`v_s=\mathrm{lab}\,x/(\mathrm{lab}-s)`$ | **proved** |
| `CvS.lock_norm_x`, `CvS.lock_norm` | Theorem 6 step: $`Q_\mu(x,x)=x_0`$, $`Q_\mu(v_s,v_s)=s^2(FG_2-F_2G)`$ | **proved** |
| `CvS.P_deriv_eval`, `CvS.lock_sign` | Theorem 6 step: $`Q_\mu(v_s,v_s)<0 \iff P_x'(s)\,P_{\beta\odot x}(s)>0`$ | **proved** |
| `CvS.charpoly_lock`, `CvS.natDegree_P_lock`, `CvS.card_roots_lock` | Theorem 6 step: $`\chi_{D'_\eta}=c^{-1}X\,P_x`$, $`\deg P_x=2N`$ | **proved** |
| `CvS.card_roots_split` | Theorem 6 step: $`\#\{\text{real roots}\}+2\,\#\{\operatorname{Im}>0\}=\deg p`$ (separable real $`p`$) | **proved** |
| `CvS.F_zero_of_root_c`, `CvS.vr_ne_zero`, `CvS.vc_ne_zero`, `CvS.inj_sum_elim`, `CvS.Nc_eq` | Theorem 6 step: eigenvectors nonzero, eigenvalues distinct, $`N_c=\#\{\operatorname{Im}>0\}`$ | **proved** |
| `CvS.index_even` | Theorem 5(a), index law | to be completed |
| `CvS.exists_qform` | every real square matrix gives the quadratic form $`w^{\top}Aw`$ | **proved** |
| `CvS.lock` | **Theorem 6, resolvent lock**: $`N_c(P_x)+d(x)+[x_0<0]=\kappa(\mu)`$ | **proved** |

Contributions are welcome: open an issue or a pull request. A natural reusable by-product is Hermite's theorem (signature of the Bezoutian counts real roots), which would also be a Mathlib contribution.

## Build

The library compiles against Mathlib (Lean v4.36.0-rc1). Theorem 6 (`CvS.lock`) is fully proved; Theorem 5(a) (`CvS.index_even`) is the remaining statement.

```
lake exe cache get
lake build
lake env lean kontrol/NegatifKontrol.lean   # negative control: exactly fifty-four errors expected
```

## License

Apache 2.0, the Mathlib license.

---

**Türkçe.** Bu depo, Connes–van Suijlekom sınıfı için kanıtlanan indeks yasası (Teorem 5) ve rezolvent kilidinin (Teorem 6) Lean 4 / Mathlib ifadelerini içerir. Rezolvent kilidi (Teorem 6, `CvS.lock`) Lean'de tam olarak kanıtlanmıştır; indeks yasasının (Teorem 5(a)) biçimselleştirilmesi sürmektedir ve katkıya açıktır.

_Lean statements and proofs drafted with AI assistance from the author's paper; compiled and checked by the author (CI + negative control)._
