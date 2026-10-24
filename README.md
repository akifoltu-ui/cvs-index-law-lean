# CvS index law in Lean 4

Lean 4 / Mathlib formalization of the finite-dimensional theorems in

> M. A. Oltulu, *Odd-sector, Pontryagin-space and index-law extensions of the Connes–van Suijlekom real-zeros theorem*, Zenodo, [doi:10.5281/zenodo.23459269](https://doi.org/10.5281/zenodo.23459269) (2026). ORCID [0009-0003-0928-0854](https://orcid.org/0009-0003-0928-0854).
>
> Formal verification supplement (EN/TR): M. A. Oltulu, *Formal verification of the index law and the resolvent lock in Lean 4*, Zenodo, [doi:10.5281/zenodo.23561287](https://doi.org/10.5281/zenodo.23561287) (2026); verified state: tag `v1.0`, commit `08a1c67`.
>
> Latest release: `v1.3.1`, [doi:10.5281/zenodo.23605691](https://doi.org/10.5281/zenodo.23605691); the supplement above documents `v1.0`.
>
> Lemma numbers follow the note (version 2.2): Lemma 1 commutator, 2 rank-one determinant, 3 $`Q_\lambda`$-symmetry, 4 non-degeneracy, 6 norm identity, 7 Pontryagin balance.

## The statement (Theorem 6, resolvent lock)

Let $Q$ be a real symmetric matrix on $I=\{-N,\dots,N\}$ of Loewner type,
$q_{ii}=a_i,\ q_{ij}=(b_i-b_j)/(i-j)$, with no parity condition on $a$ or $b$. Put
$P_\xi(s)=\sum_k \xi_k\prod_{j\ne k}(j-s)$, let $\mu$ avoid the spectrum and $x=(Q-\mu)^{-1}e_0$. Then

$$N_c(P_x)+d(x)+[x_0<0]=\kappa(\mu),$$

where $N_c$ counts pairs of non-real zeros, $`d(x)=\mathrm{card}\,\lbrace s\in\mathbb{R}\setminus\lbrace 0\rbrace : P_x(s)=0,\ P_x'(s)\,P_{\beta\odot x}(s)>0\rbrace`$ and $\kappa(\mu)$ is the number of eigenvalues below $\mu$. At $\mu=0$ this reads the positivity of $Q$ from the zeros of one polynomial. The Connes–van Suijlekom class of the note ($a$ even, $b$ odd) is the special case `CvS.lock_cvs`.

**Arbitrary real nodes.** The same identity holds for every finite set of pairwise distinct real nodes $\nu_i$, with $q_{ij}=(b_i-b_j)/(\nu_i-\nu_j)$ and the resolvent index at the node $\nu_{k_0}=0$; any node set and any index reduce to this form by the shift $\nu\mapsto\nu-\nu_k$. This is `LoewnerLock.lock` in `CvsIndexLaw/Loewner.lean`; there $\deg P_x=n-1$ for $n$ nodes, and the integer nodes $-N,\dots,N$ are the instance `LoewnerLock.instNodesIdx`. The pen-and-paper proof is in the note; it goes through $[D,Q]=\beta\wedge\eta$ and a Bezout-matrix congruence (a Hermite-type signature count).

The theorem has been verified numerically with interval arithmetic on truncated Weil quadratic forms and on an Epstein zeta function with genuine off-line zeros ([doi:10.5281/zenodo.23458944](https://doi.org/10.5281/zenodo.23458944)).

## Status

| Lean declaration | Content | Proof |
|---|---|---|
| `CvS.IsLoewner`, `CvS.IsCvS.toLoewner` | Loewner-type matrices (no parity); every CvS matrix is one | definition |
| `CvS.isSymm_of_isCvS` | Loewner-type matrices are symmetric | **proved** |
| `CvS.commutator` | Lemma 1 (CvS Lemma 5.1), $`[D,Q]=\beta\wedge\eta`$ | **proved** |
| `CvS.commutator_shift` | the same for $`Q-\mu`$ | **proved** |
| `CvS.Dprime_mulVec_self` | Lemma 2(a), $`D'_\varphi\xi=0`$ | **proved** |
| `CvS.det_Dprime` | Lemma 2(b), rank-one determinant | **proved** |
| `CvS.Qlam_Dprime_isSymm` | Lemma 3, $`Q_\lambda D'_\varphi`$ symmetric for $`\varphi\in\mathrm{span}\{\eta,\beta\}`$ | **proved** |
| `CvS.nondeg_even` | Lemma 4, even sector, for $`b`$ odd: $`\langle\beta,\xi\rangle=0`$, $`\langle\eta,\xi\rangle\neq0`$ | **proved** |
| `CvS.Qlam_norm` | Lemma 6, $`Q_\lambda(w_s,w_s)=FG'-F'G`$ | **proved** |
| `CvS.kappa_eq_sigNeg` | bridge: eigenvalue count below $`\mu`$ = `sigNeg` of $`Q-\mu`$ (Sylvester) | **proved** |
| `CvS.eigvec_orth`, `CvS.block2_sigNeg` | Lemma 7 steps: eigenvector orthogonality; a 2×2 block with $`\det<0`$ has one negative direction | **proved** |
| `CvS.sigNeg_of_congr_diag`, `CvS.sigNeg_of_orth_family` | Lemma 7 step 3: a $`B`$-orthogonal family with nonzero norms counts $`\kappa`$ | **proved** |
| `CvS.eigvec_orth_field`, `CvS.conj_eigvec`, `CvS.herm_norm_zero` | Lemma 7 step 4a: a complex eigenvector with non-real eigenvalue has zero hermitian $`B`$-norm | **proved** |
| `CvS.herm_re`, `CvS.herm_split`, `CvS.real_pair_re_im`, `CvS.cross_orth` | Lemma 7 step 4b: $`B(u,u)+B(w,w)=0`$; real eigenvectors are $`B`$-orthogonal to $`u,w`$ | **proved** |
| `CvS.pair_orth`, `CvS.plane_split` | Lemma 7 step 4c: different pairs are $`B`$-orthogonal; each pair's plane splits into one positive and one negative direction | **proved** |
| `CvS.re_im_combo`, `CvS.real_family_indep` | Lemma 7 step 4d: the real family $`\{v_i,\ \mathrm{Re}\,z_k,\ \mathrm{Im}\,z_k\}`$ is linearly independent | **proved** |
| `CvS.null_vec_zero`, `CvS.not_null_member` | Lemma 7 step 4d: no member of a complete independent family is $`B`$-null to all members | **proved** |
| `CvS.pontryagin_balance` | **Lemma 7 (Pontryagin balance)**: $`\kappa = \#\{\text{real eigenvectors of negative norm}\} + \#\{\text{non-real pairs}\}`$ | **proved** |
| `CvS.Qmu_Dprime_lock_isSymm`, `CvS.F_zero_of_root`, `CvS.Dprime_eigvec_r`, `CvS.Dprime_eigvec_c` | Theorem 6 steps: lock symmetry; explicit eigenvectors $`v_s=\mathrm{lab}\,x/(\mathrm{lab}-s)`$ | **proved** |
| `CvS.lock_norm_x`, `CvS.lock_norm` | Theorem 6 step: $`Q_\mu(x,x)=x_0`$, $`Q_\mu(v_s,v_s)=s^2(FG_2-F_2G)`$ | **proved** |
| `CvS.P_deriv_eval`, `CvS.lock_sign` | Theorem 6 step: $`Q_\mu(v_s,v_s)<0 \iff P_x'(s)\,P_{\beta\odot x}(s)>0`$ | **proved** |
| `CvS.charpoly_lock`, `CvS.natDegree_P_lock`, `CvS.card_roots_lock` | Theorem 6 step: $`\chi_{D'_\eta}=c^{-1}X\,P_x`$, $`\deg P_x=2N`$ | **proved** |
| `CvS.card_roots_split` | Theorem 6 step: $`\#\{\text{real roots}\}+2\,\#\{\operatorname{Im}>0\}=\deg p`$ (separable real $`p`$) | **proved** |
| `CvS.F_zero_of_root_c`, `CvS.vr_ne_zero`, `CvS.vc_ne_zero`, `CvS.inj_sum_elim`, `CvS.Nc_eq` | Theorem 6 step: eigenvectors nonzero, eigenvalues distinct, $`N_c=\#\{\operatorname{Im}>0\}`$ | **proved** |
| `CvS.orth_all_ker`, `CvS.sigNeg_of_orth_family_ker`, `CvS.pontryagin_balance_ker` | Theorem 5(a) step: Lemma 7 for a form with one-dimensional kernel | **proved** |
| `CvS.simple_ker`, `CvS.eig_sign` | Theorem 5(a) steps: $`\ker(Q-\lambda)=\mathbb{R}\xi`$; $`Q_\lambda(v_s,v_s)<0\iff P_\xi'(s)\,P_{\beta\odot\xi}(s)>0`$ | **proved** |
| `CvS.index_even` | **Theorem 5(a), index law (even sector)**, Loewner matrix with $`b`$ odd: $`N_c(P_\xi)+d(\xi)=\kappa(\lambda)`$ | **proved** |
| `CvS.exists_qform` | every real square matrix gives the quadratic form $`w^{\top}Aw`$ | **proved** |
| `CvS.lock` | **Theorem 6, resolvent lock**, every Loewner matrix: $`N_c(P_x)+d(x)+[x_0<0]=\kappa(\mu)`$ | **proved** |
| `CvS.lock_cvs`, `CvS.index_even_cvs` | Theorems 6 and 5(a) for the CvS class, as stated in the note | **proved** |
| `LoewnerLock.Nodes`, `LoewnerLock.lock` | **Theorem 6 for arbitrary distinct real nodes** (any finite node set, resolvent index at the node $`0`$); integer nodes: `LoewnerLock.instNodesIdx` | **proved** |

Contributions are welcome: open an issue or a pull request. A natural reusable by-product is Hermite's theorem (signature of the Bezoutian counts real roots), which would also be a Mathlib contribution.

## Build

The library compiles against Mathlib (Lean v4.36.0-rc1). Theorem 5(a) (`CvS.index_even`) and Theorem 6 (`CvS.lock`) are fully proved; the library contains no `sorry` (axiom audit: `kontrol/Aksiyom.lean`). Theorem 6 (`CvS.lock`) is stated and proved for every Loewner-type matrix; Theorem 5(a) (`CvS.index_even`) uses `b` odd and the even eigenvector, and `a` is free. The statements of the note for the CvS class are `CvS.lock_cvs` and `CvS.index_even_cvs`.

```
lake exe cache get
lake build
lake env lean kontrol/NegatifKontrol.lean   # negative control: exactly sixty errors expected
lake env lean kontrol/LoewnerKontrol.lean   # negative control (arbitrary nodes): exactly three errors expected
```

## License

Apache 2.0, the Mathlib license.

---

**Türkçe.** Bu depo, Connes–van Suijlekom sınıfı için kanıtlanan indeks yasası (Teorem 5) ve rezolvent kilidinin (Teorem 6) Lean 4 / Mathlib ifadelerini içerir. İndeks yasası (Teorem 5(a), `CvS.index_even`) ve rezolvent kilidi (Teorem 6, `CvS.lock`) Lean'de tam olarak kanıtlanmıştır; Teorem 6 her Loewner tipi matris için (parite koşulu olmadan), Teorem 5(a) `b` tek iken geçerlidir; Teorem 6 ayrıca keyfi farklı gerçel düğümler için kanıtlanmıştır (`LoewnerLock.lock`); kütüphanede `sorry` yoktur (aksiyom denetimi: `kontrol/Aksiyom.lean`). Katkıya açıktır.

_Lean statements and proofs drafted with AI assistance from the author's paper; compiled and checked by the author (CI + negative control)._
