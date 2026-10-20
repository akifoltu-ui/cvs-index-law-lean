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
| `CvS.isSymm_of_isCvS` | CvS matrices are symmetric | to be completed — good first target |
| `CvS.index_even` | Theorem 5(a), index law | to be completed |
| `CvS.lock` | Theorem 6, resolvent lock | to be completed |

Contributions are welcome: open an issue or a pull request. A natural reusable by-product is Hermite's theorem (signature of the Bezoutian counts real roots), which would also be a Mathlib contribution.

## Build

The statements compile against Mathlib (Lean v4.36.0-rc1).

```
lake exe cache get
lake build
lake env lean kontrol/NegatifKontrol.lean   # negative control: exactly one error expected
```

## License

Apache 2.0, the Mathlib license.

---

**Türkçe.** Bu depo, Connes–van Suijlekom sınıfı için kanıtlanan indeks yasası (Teorem 5) ve rezolvent kilidinin (Teorem 6) Lean 4 / Mathlib ifadelerini içerir. İfadeler derlenir; ispatların biçimselleştirilmesi sürmektedir ve katkıya açıktır.

_Lean statements drafted with AI assistance from the author's paper; compiled and checked by the author (CI + negative control)._
