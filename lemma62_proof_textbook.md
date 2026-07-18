# Lemma 6.2 — Proof as in the Textbook

> **Lemma 6.2.** Let $F$ be an exposed face of $\Omega$, and denote by $\partial F$ its relative boundary. Since $F$ is compact and because of Assumption 6.1 on $\Omega$, we know from Chapter 2 that $R(F)$ is itself a closed set. We have:

$$
\partial R(F) \subset R(\partial F).
$$

---

## Proof

Let $s^{*}$ be an arbitrary element of $\partial R(F)$. We want to show that $s^{*}$ is also an element of $R(\partial F)$.

### Real case

If $s^{*}$ is real, then since $\partial F$ is the union of exposed edges of $\Omega$, it follows from **Lemma 6.1** that $s^{*} \in R(\partial F)$.

### Complex case

Now assume that $s^{*}$ is complex.

Because $R(F)$ is a closed set, we have $\partial R(F) \subset R(F)$, so there exists $\underline{\delta}^{*} \in F$ such that $\delta^{*}(s^{*}) = 0$. We can therefore write

$$
\delta^{*}(s) = (s^{2} + \alpha s + \beta)\,(d_{n-2}s^{n-2} + \dots + d_{1}s + d_{0}),
$$

where

$$
\alpha = -2\,\mathrm{Re}(s^{*}), \qquad \beta = |s^{*}|^{2}.
$$

Let $\mathrm{aff}(F)$ be the affine hull of $F$. Since $F$ is two-dimensional, we can parametrize

$$
\mathrm{aff}(F) = \{\underline{\delta}^{*} + V\lambda \mid \lambda \in \mathbb{R}^{2}\},
$$

where $V$ is a full-rank $(n+1) \times 2$ matrix.

On the other hand, an arbitrary element of the vector space of real polynomials with a root at $s^{*}$ can be written as

$$
P^{*}(s) = (s^{2} + \alpha s + \beta)\big[(\mu_{n-2} + d_{n-2})s^{n-2} + \dots + (\mu_{1} + d_{1})s + (\mu_{0} + d_{0})\big],
$$

or more compactly

$$
\mathcal{P}_{s^{*}} = \{\underline{\delta}^{*} + W\mu \mid \mu \in \mathbb{R}^{n-1}\},
$$

where $W$ is the $(n+1) \times (n-1)$ matrix

$$
W = \begin{bmatrix}
1      & 0      & \dots  & 0 \\
\alpha & 1      & \dots  & 0 \\
\beta  & \alpha & \dots  & 0 \\
0      & \beta  & \dots  & 0 \\
\vdots & \vdots & \ddots & \vdots \\
0      & 0      & \dots  & 1 \\
0      & 0      & \dots  & \alpha \\
0      & 0      & \dots  & \beta
\end{bmatrix}.
$$

The intersection $\mathrm{aff}(F) \cap \mathcal{P}_{s^{*}}$ consists of all $(\lambda, \mu)$ satisfying

$$
\underline{\delta}^{*} + V\lambda = \underline{\delta}^{*} + W\mu,
\qquad\text{or equivalently}\qquad
[\,V,\; -W\,] \begin{bmatrix} \lambda \\ \mu \end{bmatrix} = 0.
\tag{6.10}
$$

Two possibilities must be considered.

---

#### Case A: $[V, -W]$ does **not** have full rank

In this case the space of solutions to (6.10) has dimension either $1$ or $2$.

*If the dimension is $1$*, then $\mathrm{aff}(F) \cap \mathcal{P}_{s^{*}}$ is a straight line. This line must intersect the relative boundary $\partial F$ at some point $\hat{\delta}$. Since $\hat{\delta} \in \mathcal{P}_{s^{*}}$, we have $\hat{\delta}(s^{*}) = 0$, and therefore $s^{*} \in R(\partial F)$.

*If the dimension is $2$*, then $\mathrm{aff}(F) \subset \mathcal{P}_{s^{*}}$, meaning every polynomial in $\mathrm{aff}(F)$ has $s^{*}$ as a root. In particular, for any $\hat{\delta} \in \partial F$ we have $\hat{\delta}(s^{*}) = 0$, so again $s^{*} \in R(\partial F)$.

---

#### Case B: $[V, -W]$ has **full rank**

In this case $\mathrm{aff}(F) \cap \mathcal{P}_{s^{*}}$ is reduced to the single point $\underline{\delta}^{*}$. We now prove that $\underline{\delta}^{*} \in \partial F$, using the fact that $s^{*} \in \partial R(F)$.

Since $s^{*} \in \partial R(F)$, there exists a sequence of complex numbers $\{s_{n}\}$ such that

$$
s_{n} \notin R(F) \quad\text{for all }n,\qquad
s_{n} \longrightarrow s^{*} \;\text{ as }\; n \to +\infty.
$$

In particular,

$$
-2\,\mathrm{Re}(s_{n}) \longrightarrow \alpha,\qquad
|s_{n}|^{2} \longrightarrow \beta \quad\text{as } n \to +\infty.
\tag{6.11}
$$

For each $n$, let $\mathcal{P}_{s_{n}}$ be the vector space of all real polynomials with a root at $s_{n}$. An arbitrary element of $\mathcal{P}_{s_{n}}$ can be expressed as

$$
\begin{aligned}
P(s) = \delta^{*}(s) &+ \bigl(s^{2} - 2\,\mathrm{Re}(s_{n})\,s + |s_{n}|^{2}\bigr)
\bigl(\mu_{n-2}s^{n-2} + \dots + \mu_{1}s + \mu_{0}\bigr) \\
&+ \bigl(-(2\,\mathrm{Re}(s_{n}) + \alpha)s + (|s_{n}|^{2} - \beta)\bigr)
\bigl(d_{n-2}s^{n-2} + \dots + d_{1}s + d_{0}\bigr),
\end{aligned}
$$

or equivalently

$$
\mathcal{P}_{s_{n}} = \{\underline{\delta}^{*} + W_{n}\mu + \nu_{n} \mid \mu \in \mathbb{R}^{n-1}\},
\tag{6.12}
$$

where

$$
W_{n} = \begin{bmatrix}
1                & 0                & \dots  & 0 \\
-2\,\mathrm{Re}(s_{n}) & 1                & \dots  & 0 \\
|s_{n}|^{2}       & -2\,\mathrm{Re}(s_{n}) & \dots  & 0 \\
0                & |s_{n}|^{2}       & \dots  & 0 \\
\vdots           & \vdots           & \ddots & \vdots \\
0                & 0                & \dots  & 1 \\
0                & 0                & \dots  & -2\,\mathrm{Re}(s_{n}) \\
0                & 0                & \dots  & |s_{n}|^{2}
\end{bmatrix},
$$

and

$$
\nu_{n} = \begin{bmatrix}
d_{n-2} & 0 \\
d_{n-3} & d_{n-2} \\
d_{n-4} & d_{n-3} \\
\vdots  & \vdots \\
d_{0}   & d_{1}  \\
0       & d_{0}
\end{bmatrix}
\begin{bmatrix}
-(2\,\mathrm{Re}(s_{n}) + \alpha) \\
|s_{n}|^{2} - \beta
\end{bmatrix}.
\tag{6.13}
$$

Clearly, from (6.11),

$$
W_{n} \longrightarrow W,\qquad
\nu_{n} \longrightarrow 0 \quad\text{as } n \to +\infty.
\tag{6.14}
$$

Since $\det(\cdot)$ is continuous and $\det[V, -W] \neq 0$ (Case B), there exists $n_{1}$ such that $\det[V, -W_{n}] \neq 0$ for all $n \ge n_{1}$.

For every $n$, the intersection $\mathcal{P}_{s_{n}} \cap \mathrm{aff}(F)$ consists of all $(\lambda, \mu)$ satisfying

$$
\underline{\delta}^{*} + W_{n}\mu + \nu_{n} = \underline{\delta}^{*} + V\lambda,
$$

or equivalently

$$
[\,V,\; -W_{n}\,] \begin{bmatrix} \lambda \\ \mu \end{bmatrix} = \nu_{n}.
\tag{6.15}
$$

For $n \ge n_{1}$, the matrix $[V, -W_{n}]$ is invertible, so (6.15) has a unique solution

$$
\begin{bmatrix} \lambda_{n} \\ \mu_{n} \end{bmatrix} = [V, -W_{n}]^{-1}\,\nu_{n}.
\tag{6.16}
$$

From (6.14) we deduce that

$$
\begin{bmatrix} \lambda_{n} \\ \mu_{n} \end{bmatrix} \longrightarrow 0 \quad\text{as } n \to +\infty.
$$

We now show that $\underline{\delta}^{*} \in \partial F$. Consider an arbitrary open neighbourhood in $\mathrm{aff}(F)$:

$$
B_{F}(\underline{\delta}^{*}, \varepsilon) = \{\underline{\delta} \in \mathrm{aff}(F) \mid \|\underline{\delta} - \underline{\delta}^{*}\| < \varepsilon\}.
$$

We must show that $B_{F}(\underline{\delta}^{*}, \varepsilon)$ contains at least one point **not** belonging to $F$.

To do so, consider the intersection of $\mathcal{P}_{s_{n}}$ with $\mathrm{aff}(F)$, namely

$$
\underline{\delta}_{n} = \underline{\delta}^{*} + V\lambda_{n}.
$$

This vector belongs to $\mathrm{aff}(F)$, and since $\lambda_{n} \to 0$, it lies in $B_{F}(\underline{\delta}^{*}, \varepsilon)$ for sufficiently large $n$. Moreover, the polynomial corresponding to $\underline{\delta}_{n}$ has a root at $s_{n}$ (by construction), and we know that $s_{n} \notin R(F)$. Therefore $\underline{\delta}_{n}$ cannot belong to $F$.

Hence every neighbourhood of $\underline{\delta}^{*}$ in $\mathrm{aff}(F)$ contains points outside $F$, so $\underline{\delta}^{*} \in \partial F$. Since $\delta^{*}(s^{*}) = 0$, we have $s^{*} \in R(\partial F)$. ∎

---

### Summary: Role in the Edge Theorem

The Edge Theorem (Theorem 6.1) follows immediately from Lemma 6.1 and Lemma 6.2:

Let $\Omega$ be a polytope with exposed faces $F_{1}, \dots, F_{p_{F}}$. By Lemma 6.1, $R(\Omega) = \bigcup_i R(F_i)$. Then, by Lemma 6.2,

$$
\partial R(\Omega) = \partial\bigcup_i R(F_i)
= \bigcup_i \partial R(F_i)
\subset \bigcup_i R(\partial F_i).
$$

The sets $\partial F_i$ are precisely the exposed edges of $\Omega$, so the boundary of the root space of $\Omega$ is contained in the root space of the exposed edges. ∎
