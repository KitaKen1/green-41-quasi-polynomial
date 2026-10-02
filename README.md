# A Lean proof of a quasi-polynomial bound in Green's Problem 41

**The problem.** Ben Green's Problem 41 (the pyjama problem) asks how many rotated copies of the
pyjama set

```text
E(ε) = { z ∈ ℂ : |Re z − k| ≤ ε for some k ∈ ℤ }
```

are needed to cover the plane. Write `minCopies ε` for the least such number, as in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/GreensOpenProblems/41.lean).
Manners (2015) showed that finitely many copies suffice, and Green asks whether `ε^(−C)` copies
suffice.

| Bound | Upper bound for `minCopies ε` | Proof |
|---|---|---|
| Triple exponential | `exp exp exp(ε^(−C))` | Kravitz and Leng (2025) |
| Double exponential | `exp exp(ε^(−C))` | Lean: [KitaKen1/green-41-double-exponential](https://github.com/KitaKen1/green-41-double-exponential) |
| Single exponential | `exp(ε^(−201))` for `0 < ε ≤ 1/400000` | Lean: **this repository** |
| Quasi-polynomial | `exp(10^16 · (log(1/ε) + 2)^4)` for `0 < ε < 1/10` | Lean: **this repository** |
| Polynomial | `ε^(−C)` | open (Green's question) |

The quasi-polynomial bound is `exp(O(log⁴(1/ε)))`. In Formal Conjectures form it reads
`minCopies ε ≤ exp((log ε⁻¹)^5)` for `0 < ε ≤ exp(−10^18)`.

**Try it in Lean4Web:**
[open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fgreen-41-quasi-polynomial%2Frefs%2Fheads%2Fmain%2Flean4web%2FGreen41QuasiPolynomialLean4Web.lean)
(one file with the double-exponential, single-exponential and quasi-polynomial proofs; checked
with "Latest Mathlib with Lean v4.35.0-rc3"; the file is long, so elaboration takes a few minutes)

This does **not** solve the exact-value theorem `Green41.green_41` or the polynomial variant
`Green41.green_41.variants.polynomial_bound`.

## Formal Conjectures targets

The files in `lean/` import the Formal Conjectures definitions `pyjamaSet`, `coveringCopies` and
`minCopies` and prove:

```lean
theorem Green41Proof.quasiPolynomialBound_explicit {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 10) :
    (minCopies ε : ℝ) ≤ Real.exp (10 ^ 16 * (Real.log (1 / ε) + 2) ^ 4)

theorem Green41Proof.green_41_quasi_polynomial_bound_solved : answer(True) ↔
    ∃ C : ℝ, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀,
      (minCopies ε : ℝ) ≤ Real.exp (Real.log ε⁻¹ ^ C)

theorem Green41Proof.green_41_single_exponential_bound_solved : answer(True) ↔
    ∃ C : ℝ, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀, (minCopies ε : ℝ) ≤ Real.exp (ε ^ (-C))
```

with `C = 5`, `ε₀ = exp(−10^18)` and `C = 201`, `ε₀ = 1/400000`. Formal Conjectures has no
statements for these two bounds yet. The quasi-polynomial bound implies the single-exponential
and double-exponential ones, so one new variant `green_41.variants.quasi_polynomial_bound` with
the statement above would record all of them.

The proofs construct an explicit covering set, so the bounds are not artefacts of the junk value
of `sInf ∅`.

## Mathematical Explanation (AI generated)

This is a human-readable sketch of the argument formalized in `lean/`. It follows the
double-exponential proof, which is explained in detail in the README of
[KitaKen1/green-41-double-exponential](https://github.com/KitaKen1/green-41-double-exponential),
and describes what changes.

**Overview.** The double-exponential proof uses the full cyclic orbit of a rotation
$`\theta=Q/\bar Q`$ (or $`P/\bar P`$) in two places: Step A reaches every residue class with the powers
$`\theta^t`$, $`t\lt(p-1)p^{n+3}`$, and the discrete core uses the multipliers of $`\theta^t`$,
$`t\lt(p-1)p^{\ell-1}`$. Each orbit forces a common denominator $`\bar Q^{E}`$ with $`E`$
exponential in the number of digits, and these denominators set the size of all the parameters.
Both steps only need rotations whose multipliers reach every unit and whose denominators divide
one common denominator. Base-$`p`$ **digit rotations** $`(1+p^ki)/(1-p^ki)`$ do this with a
common denominator of norm $`p^{O(N^2)}`$ instead of $`p^{p^N}`$. Using them in Step A gives the
single-exponential bound; using them in the discrete core as well makes every parameter
$`O(\log^2(1/\varepsilon))`$ and gives the quasi-polynomial bound.

**Notation.** For $`x\inℝ`$ write $`\|x\|`$ for the distance from $`x`$ to $`ℤ`$. For
$`|u|=1`$ put

```math
S_u(\varepsilon)=\{z\inℂ:\ \|\mathrm{Re}(uz)\|\lt \varepsilon\}.
```

Since $`S_u(\varepsilon)\subseteq \bar u\,E(\varepsilon)`$, it suffices to find a finite set
$`\Omega`$ of unit complex numbers with $`\bigcup_{u\in\Omega}S_u(\varepsilon)=ℂ`$; then
$`\mathrm{minCopies}\,\varepsilon\le|\Omega|`$. The rotations come from the Gaussian primes
$`P=1+2i`$ (norm $`5`$) and $`Q=2+3i`$ (norm $`13`$):

```math
\theta_5=P/\bar P,\qquad \theta_{13}=Q/\bar Q,\qquad \rho(s,t)=\theta_5^{\,s}\theta_{13}^{\,t}\quad(s,t\ge0).
```

For $`q\inℤ[i]`$ put $`|q|_5=5^{-v_{\bar P}(q)}`$ and $`|q|_{13}=13^{-v_{\bar Q}(q)}`$.

### 1. Digit rotations

Fix a digit prime $`\pi`$ of norm $`p`$ and a second prime $`\kappa`$: either
$`(\pi,p,\kappa)=(P,5,Q)`$ or $`(Q,13,P)`$. Let $`\psi_N:ℤ[i]\toℤ/p^N`$ be the ring map with kernel
$`\pi^Nℤ[i]`$, and for $`\pi\nmid C\bar C`$ let $`\mu_N(C)=\psi_N(C)/\psi_N(\bar C)`$ be the
multiplier of the rotation $`C/\bar C`$ on $`ℤ[i]/\pi^N`$. For $`N\ge1`$ the **digit family** and
its **common denominator** are

```math
𝒜_N=\Bigl\{\kappa^{m}\prod_{1\le k\lt N}(1+p^ki)^{d_k}:\ 0\le m\lt p-1,\ 0\le d_k\lt p\Bigr\},\qquad D_N=\bar\kappa^{\,p-2}\prod_{1\le k\lt N}(1-p^ki)^{p-1}.
```

Every $`F\in𝒜_N`$ has $`\bar F\mid D_N`$, and
$`N(D_N)=N(\kappa)^{p-2}\prod_{1\le k\lt N}(1+p^{2k})^{p-1}\le 2^{44+96N^2}`$.

> **Lemma E (digit cover).** If $`\mu_N(\bar\kappa)`$ generates $`(ℤ/p^N)^\times`$, then every unit
> of $`ℤ/p^N`$ is $`\mu_N(\bar F)`$ for some $`F\in𝒜_N`$. The same holds for the level-$`n`$
> multipliers $`\mu_n(\bar F)`$, $`n\ge N`$, read modulo $`p^N`$.

*Proof.* Put $`r=\psi_N(i)`$, so $`r^2=-1`$. Then
$`\mu_N(1-p^ki)=(1-p^kr)/(1+p^kr)\equiv1-2p^kr\pmod{p^{k+1}}`$, and $`-2r`$ is a unit, so
$`\mu_N(1-p^ki)`$ is a "digit at level $`k`$". Write a unit as $`u=b^t`$ with
$`b=\mu_N(\bar\kappa)`$ and $`t=m+(p-1)t'`$, $`0\le m\lt p-1`$. By Fermat,
$`b^{(p-1)t'}\equiv1\pmod p`$, and every element $`\equiv1\pmod p`$ is a product
$`\prod_{1\le k\lt N}\mu_N(1-p^ki)^{d_k}`$ with $`0\le d_k\lt p`$, the digits being chosen one
level at a time as in a base-$`p`$ expansion. Multipliers are multiplicative, so
$`u=\mu_N\bigl(\bar\kappa^{\,m}\prod_k(1-p^ki)^{d_k}\bigr)`$. For the second statement, run the
same argument in $`ℤ/p^N`$ on the reductions of the level-$`n`$ multipliers; the first-order
shape $`1+p^k\cdot(\text{unit})+O(p^{k+1})`$ survives the reduction. $`\square`$

### 2. The minor-arc proposition

For $`0\lt\varepsilon\lt1/10`$ let $`K_0=\lceil1/\varepsilon\rceil`$ and, for $`p\in\{5,13\}`$,

```math
c_p=\lceil\log_pK_0\rceil,\quad L_p=6c_p+4,\quad \ell_p=4L_p,\quad A_p=2p(\ell_p^2+1)+2c_p+3,\quad n_p=8(A_p+\ell_p).
```

All of these are $`O(\log^2(1/\varepsilon))`$. Put

- $`\eta=5^{-(A_5+A_{13})}`$;
- $`M=N(D^{(5)})\,N(D^{(13)})`$, where $`D^{(5)}=D_{n_5+4}\,\overline{D_{\ell_5}}`$ for
  $`(\pi,p,\kappa)=(P,5,Q)`$, and $`D^{(13)}`$ is defined in the same way for $`(Q,13,P)`$;
- $`B=(A_5+4+n_5)+(A_{13}+4+n_{13})`$;
- $`R`$ = the set of products $`(F/\bar F)(\bar F'/F')`$ with $`F\in𝒜_{n_p+4}`$ and
  $`F'\in𝒜_{\ell_p}`$, for both values of $`p`$.

> **Proposition A′.** Let $`0\lt\varepsilon,\varpi\lt1/10`$ and $`s_1,t_1,s_2,t_2\le N_0`$. Put
> $`r=\rho(s_1,t_1)-\rho(s_2,t_2)`$. Let $`w\inℂ`$ and $`q\inℤ[i]`$ satisfy
> ```math
> |q-rw|\le\eta/10,\qquad M\mid q,\qquad 2\varpi\le|q|_5+|q|_{13}.
> ```
> Then $`w\in S_{\rho(s,t)\mu}(\varepsilon)`$ for some $`\mu\in R`$ and
> $`s,t\le N_0+\log_5(1/\varpi)+B`$.

In the double-exponential proof the tolerance was $`\eta=5^{-\varepsilon^{-100}}`$, and instead of
$`M\mid q`$ the proposition asked for $`|q|_5+|q|_{13}\le\delta=13^{-c\,\eta^{-5}}`$, which makes
$`q`$ divisible by huge powers of $`\bar P`$ and $`\bar Q`$. Section 5 proves Proposition A′.

### 3. From Proposition A′ to a covering

The rest is the covering argument of the double-exponential proof, with two changes: the
pigeonhole is taken modulo $`M`$, and every orbit rotation $`\rho(s,t)`$ is followed by a rotation
$`\mu\in R`$.

**Confinement.** Let $`G=\lceil\max(20/\eta,\,M,\,1/\varepsilon,\,B)\rceil+66`$ and $`K=G^4`$, so
that $`(K+1)^2>M^2G^2`$. For $`w\inℂ`$, classify the $`(K+1)^2`$ points $`\rho(s,t)w`$
($`s,t\le K`$) by the residue modulo $`M`$ of the nearest Gaussian integer and by the cell of the
fractional offset in a grid of mesh $`1/G`$. Two points $`x=\rho(s_1,t_1)w`$ and
$`y=\rho(s_2,t_2)w`$ fall into the same class, and $`q=[x]-[y]`$ satisfies $`M\mid q`$ and
$`|q-rw|\lt2/G\le\eta/10`$. Fix $`h\ge1`$ and suppose that $`w\notin S_{\rho(s,t)\mu}(\varepsilon)`$
for all $`\mu\in R`$ and $`s,t\le T=K+\log_5(2\cdot13^h)+B`$. Then Proposition A′ with
$`\varpi=13^{-h}/2`$ forces $`|q|_5+|q|_{13}\lt13^{-h}`$, that is, $`\bar P^h\bar Q^h\mid q`$. As in
the double-exponential proof, the common denominator $`L`$ of the orbit differences then places
$`w`$ within $`H=65^{K/2}`$ of the lattice $`(\bar P^h\bar Q^h/L)\,ℤ[i]`$.

**The end game.** Lemmas C and D of the double-exponential proof are unchanged. A finite set
$`U`$ of rational rotations $`a/\bar a`$ covers every disc of radius $`2LH`$, and with
$`\Theta=\{\rho(s,t)\mu:\ s,t\le T,\ \mu\in R\}`$ and $`\nu+\bar\nu=1/L`$, the set
$`\Omega=\Theta U\nu\cup\Theta U\bar\nu\cup U`$ covers $`ℂ`$ once $`h`$ is chosen with
$`|\bar P^h\bar Q^h|>2LH\max|a|`$. The parameter estimates of the double-exponential proof give

```math
\mathrm{minCopies}\,\varepsilon\ \le\ (2(T+1)^2|R|+1)\,|U|\ \le\ |R|\cdot G^{88}.
```

### 4. Sizes

Put $`X=\log(1/\varepsilon)+2`$. Since $`p^{\,c_p-1}\lt K_0\le2/\varepsilon`$, we get $`c_p\le X`$,
hence $`\ell_p\le32X`$, $`A_p\le26700X^2`$ and $`n_p+4\le214000X^2`$. Therefore:

- $`M\le2^{176+192((n_5+4)^2+(n_{13}+4)^2)}\le\exp(2\cdot10^{13}X^4)`$, by $`N(D_N)\le2^{44+96N^2}`$;
- $`20/\eta=20\cdot5^{A_5+A_{13}}=\exp(O(X^2))`$, $`B=O(X^2)`$ and $`1/\varepsilon\le e^X`$;
- $`|R|\le16^{2((n_5+4)+(n_{13}+4))+1}=\exp(O(X^2))`$.

So $`G\le\exp(2\cdot10^{13}X^4+68)`$ and

```math
\mathrm{minCopies}\,\varepsilon\ \le\ |R|\,G^{88}\ \le\ \exp\bigl(10^{16}(\log(1/\varepsilon)+2)^4\bigr),
```

which is at most $`\exp((\log\varepsilon^{-1})^5)`$ once $`\varepsilon\le e^{-10^{18}}`$.

### 5. Proof of Proposition A′

Assume $`|q|_5\ge|q|_{13}`$; the other case is symmetric under
$`(P,5,Q)\leftrightarrow(Q,13,P)`$. Write $`p=5`$, $`\pi=P`$, $`\kappa=Q`$, $`n=n_5`$, $`\ell=\ell_5`$,
$`L=L_5`$ and $`A=A_5`$. Then $`v:=v_{\bar P}(q)\le\log_5(1/\varpi)`$. Since $`D^{(5)}\mid M\mid q`$
and $`\bar P\nmid D^{(5)}`$,

```math
q=\bar P^{\,v}\,D_{n+4}\,D\,q_2,\qquad D=\overline{D_\ell},\qquad \bar P\nmid q_2.
```

**(a) Cells and labels.** Let $`\alpha=n-A`$ and $`g=\bar P^{\alpha}D/P^n`$. The label of
$`x\inℂ`$ is $`\Lambda(x)=\psi_n(\lfloor x/g\rfloor)`$, with the floor taken coordinatewise. If
$`\bar C\mid D`$ and $`j\le\alpha`$, then $`\theta_5^{\,j}(C/\bar C)\,g\,m=G_m/P^{\,n-j}`$ with
$`G_m\inℤ[i]`$, and for an explicit unit $`X_j`$

```math
\mathrm{Re}\bigl(\theta_5^{\,j}(C/\bar C)\,g\,m\bigr)\equiv\mathrm{val}\bigl(X_j\,\mu_n(C)\,\psi_n(m)\bigr)/5^{\,n-j}\pmod 1.
```

The cell has $`|g|^2=N(D)/5^{A}`$. Since $`N(D)\le5^{10(\ell^2+1)}`$ and
$`A=10(\ell^2+1)+2c_5+3`$, we get $`|g|^2\le\varepsilon^2/125`$; also $`|g|\ge5^{-A}\ge10\,\eta`$.

**(b) Step A with digit rotations.** Let $`j=v+n-\alpha+4`$. For $`F\in𝒜_{n+4}`$,

```math
\theta_5^{\,j}\,\frac{F}{\bar F}\,q=\frac{D\,W_F}{\bar P^{\,n-\alpha+4}},\qquad W_F=P^{\,j}F\,\frac{D_{n+4}}{\bar F}\,q_2\inℤ[i],
```

and $`W_F`$ is prime to $`\bar P`$. Modulo $`\bar P^{\,n+4}`$ we have $`W_F=W_1\cdot F/\bar F`$, and
complex conjugation $`ℤ[i]/\bar P^{\,n+4}\congℤ[i]/P^{n+4}`$ turns the factor $`F/\bar F`$ into
$`\mu_{n+4}(\bar F)`$. So by Lemma E the $`W_F`$ run through all units modulo $`\bar P^{\,n+4}`$. As in
step (c) of the double-exponential proof, with $`\bar Q^{\beta}`$ replaced by $`D`$, every label
$`\lambda\inℤ/5^n`$ is then the label of $`\theta_5^{\,j}(F/\bar F)\,rw=x-x'`$ for some $`F`$ and
two points $`x,x'`$ of the orbit

```math
Z=\{\theta_5^{\,a}\theta_{13}^{\,b}\,(F/\bar F)\,w:\ a\le N_0+j,\ b\le N_0,\ F\in𝒜_{n+4}\}.
```

The error $`|rw-q|\le\eta/10\lt0.42\,|g|`$ does not move the cell, and the lattice
$`\bar P^{\alpha}Dℤ[i]=gP^nℤ[i]`$ does not change labels. Here $`q`$ only has to absorb
$`D_{n+4}`$, of norm $`2^{O(n^2)}`$, instead of $`\bar Q^{\,4\cdot5^{n+3}}`$.

**(c) Counting and the digit pigeonhole.** As in (d) and (e) of the double-exponential proof,
$`5^n\le4|\Lambda(Z)|^2`$, and since $`n=8(A+\ell)`$ with $`\ell=4L`$ there is a level
$`s\ge A+\ell`$ with at least $`5^L`$ labels of orbit points that agree modulo $`5^{s-\ell}`$ and
are distinct modulo $`5^s`$. By (a) with $`j=n-s`$, for a rotation $`\nu=C/\bar C`$ with
$`\bar C\mid D`$ the stripe values of $`\theta_5^{\,n-s}\nu x`$ at these points are
$`\tilde\mu\,(\gamma+y/5^\ell)`$ modulo $`1`$, where $`\tilde\mu`$ is an integer lift of
$`\mu_n(C)`$, $`\gamma`$ is fixed, and $`y`$ runs over a set $`𝒴`$ of at least $`5^L`$ residues
distinct modulo $`5^\ell`$.

**(d) The discrete core over the digit family.** By Lemma E, for each unit $`u`$ of $`ℤ/5^\ell`$
there is $`F'_u\in𝒜_\ell`$ with $`\mu_n(\bar F'_u)\equiv u\pmod{5^\ell}`$. Take
$`\nu_u=\bar F'_u/F'_u`$, that is $`C=\bar F'_u`$, so that $`\bar C=F'_u\mid\overline{D_\ell}=D`$.
The lifts $`\tilde\mu_u`$ are pairwise distinct modulo $`5^\ell`$, and there are
$`4\cdot5^{\ell-1}\ge\frac45\,5^\ell`$ of them. Step (f) of the double-exponential proof uses only
these two facts about its multipliers: the phase $`e(m\tilde\mu\gamma)`$ factors out of each
inner sum, and

```math
\sum_u\Bigl|\sum_{y\in𝒴}e(m\tilde\mu_uy/5^\ell)\Bigr|^2\le\sum_{z\bmod5^\ell}\Bigl|\sum_{y\in𝒴}e(mzy/5^\ell)\Bigr|^2 .
```

With $`N=2K_0^2`$ and $`5^L\ge625K_0^6>\frac{25}4N^3`$, the same Fejér-kernel computation shows
that some point $`\tilde\mu_u(\gamma+y/5^\ell)`$ lies within $`\varepsilon/2`$ of $`ℤ`$.

**(e) Conclusion.** Let $`x=\theta_5^{\,a}\theta_{13}^{\,b}(F/\bar F)w`$ be the corresponding orbit
point and $`m=\lfloor x/g\rfloor`$. Since $`|x-gm|\lt\sqrt2\,|g|\le\varepsilon/2`$, we get
$`\|\mathrm{Re}(\theta_5^{\,n-s}\nu_u\,x)\|\lt\varepsilon`$, that is,
$`w\in S_{\rho(a+n-s,\,b)\,\mu}(\varepsilon)`$ with $`\mu=(F/\bar F)\,\nu_u\in R`$. The exponents
satisfy $`a+n-s\le N_0+v+A+4+n`$ and $`b\le N_0`$, both at most $`N_0+\log_5(1/\varpi)+B`$.
$`\square`$

**The single-exponential bound** is the intermediate version in which (b) uses digit rotations
but (d) still uses the cyclic orbit $`\tilde b^{\,t}`$, $`t\lt S=4\cdot5^{\ell-1}`$. Then the cell must
carry $`\bar Q^{S}`$ instead of $`D`$, so $`A\approx2S`$ and $`n\approx16S`$ are polynomial in
$`1/\varepsilon`$, $`M=2^{O(n^2)}`$ and $`\eta=5^{-\varepsilon^{-100}}`$, which gives
$`\exp(\varepsilon^{-201})`$.

## Files

| Path | Lean version | Purpose |
|---|---:|---|
| `lean/` | `v4.33.1` | Formal Conjectures version, pinned to commit `40a8592c...` |
| `lean4web/` | `v4.35.0-rc3` | Standalone mathlib-only proof for Lean4Web (mathlib `5e0c4e52...`) |

`lean/` has three libraries:

| Library | Content |
|---|---|
| `Green41DoubleExponentialFC.lean` | The double-exponential development, copied unchanged from [KitaKen1/green-41-double-exponential](https://github.com/KitaKen1/green-41-double-exponential) (commit `e2b49ac`) |
| `Green41SingleExponential/` | Digit rotations in Step A: the single-exponential bound |
| `Green41QuasiPolynomial/` | Digit rotations in the discrete core: the quasi-polynomial bound |

`lean/Green41SingleExponential/`

| File | Content |
|---|---|
| `DigitCover.lean` | Base-`p` digit covers of `(ZMod (p^N))ˣ` (`exists_mul_digits`) |
| `DigitRotation.lean` | `ω_k` is a level-`k` digit; every unit is a digit multiplier (`exists_digit_multiplier`) |
| `StepAFamily.lean` | Step A for any multiplier family (`stepA_family`) and for digits (`stepA_digit`) |
| `MinorArcDigit.lean` | The minor-arc argument with digit rotations in Step A (`minor_arc_core_digit`) |
| `KL57Digit.lean` | The minor-arc interface with the divisibility `Mdig ε ∣ q` instead of `δ` (`kl57D`) |
| `AssemblyDigit.lean` | Confinement, parameters, and `minCopies ε ≤ \|Rots ε\| · G^88` |
| `FinalSingle.lean` | Size bounds and the single-exponential theorem |

`lean/Green41QuasiPolynomial/`

| File | Content |
|---|---|
| `DiscreteGen.lean` | The discrete core for any family of multipliers distinct modulo `p^ℓ` (`discrete_core_gen`) |
| `CellGen.lean` | Cells `π̄^α D / πⁿ` with a general denominator `D` (`stepA_familyD`, `re_label_formulaD`) |
| `DigitCast.lean` | Level-`n` digit multipliers read modulo `p^ℓ` reach every unit (`exists_digit_multiplier_cast`) |
| `MinorArcQuasi.lean` | The minor-arc argument with digit rotations on both sides (`minor_arc_core_quasi`) |
| `AssemblyGen.lean` | The assembly for any minor-arc interface (`ArcData.minCopies_le_Rots_G_pow`) |
| `KL57Quasi.lean` | Parameters `A, n = O(log²(1/ε))` and the minor-arc interface for them (`dataQ_KL`) |
| `FinalQuasi.lean` | Size bounds and the quasi-polynomial theorems |

`lean4web/Green41QuasiPolynomialLean4Web.lean` is a single file containing the same three parts.
It copies the Formal Conjectures definitions of `pyjamaSet`, `coveringCopies` and `minCopies`
(commit `40a8592c...`) and proves `green_41.variants.double_exponential_bound`,
`green_41.variants.single_exponential_bound` and `green_41.variants.quasi_polynomial_bound`, each
in the form `True ↔ ...`.

## Verification

Formal Conjectures version:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Standalone mathlib/Lean4Web version:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

The proof files contain no `sorry`, `admit`, custom axiom, `native_decide`, or `unsafe` theorem.
Their final `#print axioms` commands report only Lean's standard axioms:

```text
[propext, Classical.choice, Quot.sound]
```

## Status boundary

What is solved here:

```text
There are C and ε₀ > 0 with minCopies ε ≤ exp((log ε⁻¹)^C) for 0 < ε ≤ ε₀
(C = 5, ε₀ = exp(−10^18)); explicitly minCopies ε ≤ exp(10^16 (log(1/ε) + 2)^4) for ε < 1/10.
```

What remains open:

```text
Determine minCopies ε exactly (Green41.green_41).
Is minCopies ε ≤ ε^(−C) for some C (Green41.green_41.variants.polynomial_bound)?
```

The trivial lower bound is of order `1/(2ε)`. The method here cannot give a polynomial bound as
it stands: it needs, for at least `1/ε` residue classes, a family of rotations whose denominators
divide one common denominator `B`, and the pigeonhole step uses at least `|N(B)|` rotations. By
the divisor bound, `|N(B)| ≥ (1/ε)^{c log log(1/ε)}`.

## Sources

- B. Green, *100 open problems*, Problem 41
- [Formal Conjectures: `GreensOpenProblems/41.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/GreensOpenProblems/41.lean)
- N. Kravitz and J. Leng, *Quantitative pyjama*,
  [arXiv:2510.17744](https://arxiv.org/abs/2510.17744)
- F. Manners, *A solution to the pyjama problem*, Invent. Math. 202 (2015)
- D. Gayfulin and N. Moshchevitin, *On Furstenberg's Diophantine result*,
  [arXiv:2301.08212](https://arxiv.org/abs/2301.08212)
- J. Bourgain, E. Lindenstrauss, P. Michel and A. Venkatesh, *Some effective results for ×a×b*,
  Ergodic Theory Dynam. Systems 29 (2009)
- [KitaKen1/green-41-double-exponential](https://github.com/KitaKen1/green-41-double-exponential),
  the double-exponential proof this repository builds on

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra, and Claude Code using Claude Opus 5.5.

## Appendix: History of the bounds

| Date | Upper bound for `minCopies ε` | Source | What changed |
|---|---|---|---|
| 2015 | finite | F. Manners, Invent. Math. 202 | Solves the pyjama problem by topological dynamics; no explicit bound |
| 2025 | `exp exp exp(ε^(−C))` | N. Kravitz and J. Leng, [arXiv:2510.17744](https://arxiv.org/abs/2510.17744) | First quantitative bound, from an analysis of Manners's method using the entropy tools of Bourgain–Lindenstrauss–Michel–Venkatesh |
| 2026-09-25 | `exp exp(ε^(−102))` | [KitaKen1/green-41-double-exponential](https://github.com/KitaKen1/green-41-double-exponential) (Lean; Formal Conjectures PR #6581) | Elementary proof of the minor-arc input (Kravitz–Leng, Proposition 5.7): Step A replaces their Theorem 5.1, and a Fejér-kernel discrete core after Gayfulin–Moshchevitin replaces the entropy input |
| 2026-10 | `exp(ε^(−201))` | this repository (Lean) | Digit rotations in Step A: the condition `\|q\|₅ + \|q\|₁₃ ≤ δ` becomes divisibility by an explicit modulus of size `exp(poly(1/ε))` |
| 2026-10 | `exp(10^16 (log(1/ε) + 2)^4)` | this repository (Lean) | Digit rotations in the discrete core as well: all parameters are `O(log²(1/ε))` |

The trivial lower bound is of order `1/(2ε)`. Whether `ε^(−C)` rotations suffice (Green's
question, `Green41.green_41.variants.polynomial_bound`) is open.
