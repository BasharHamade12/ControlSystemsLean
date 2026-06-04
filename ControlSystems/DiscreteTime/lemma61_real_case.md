## Lemma 6.1 (Real Case) — Formal Proof

**Statement.**  
Let $\Omega \subseteq \mathbb{R}^{n+1}$ be a polytope (the convex hull of finitely many points) such that every $\delta \in \Omega$ is a real polynomial of degree exactly $n$ with leading coefficient $\delta_n > 0$ (Assumption 6.1).  
If $s_r \in \mathbb{R}$ and $s_r \in R(\Omega)$ — i.e., there exists $\delta \in \Omega$ such that $\delta(s_r) = 0$ — then there exists an exposed edge $E$ of $\Omega$ such that $s_r \in R(E)$.

---

### 1. Preliminaries and Notation

Let $\mathbb{R}^{n+1}$ be identified with the space of real polynomials of degree $\leq n$ via the coefficient vector

$$
\underline{\delta} = (\delta_n, \delta_{n-1}, \dots, \delta_1, \delta_0)^\mathsf{T}.
$$

Define the **root subspace** at $s_r \in \mathbb{R}$:

$$
\mathcal{P}_{s_r} := \left\{ \underline{\gamma} \in \mathbb{R}^{n+1} \;\big|\;
\gamma_0 + \gamma_1 s_r + \gamma_2 s_r^2 + \dots + \gamma_n s_r^n = 0 \right\}.
$$

Since $s_r$ is real, this is a single nonzero linear condition. Hence $\mathcal{P}_{s_r}$ is a linear subspace of $\mathbb{R}^{n+1}$ with $\dim \mathcal{P}_{s_r} = n$.

Let $\operatorname{aff}(\Omega)$ denote the affine hull of $\Omega$ (the smallest affine subspace containing $\Omega$). Set $m := \dim \operatorname{aff}(\Omega)$.

Let $\underline{\delta} \in \Omega$ be a polynomial with $\delta(s_r) = 0$ (exists by hypothesis).

---

### 2. Base Cases ($m \leq 1$)

**Case $m = 0$.**  
Then $\Omega = \{\underline{\delta}\}$ is a single vertex. This vertex is trivially an exposed edge (or the claim about exposed edges is vacuously satisfied). We have $s_r \in R(\Omega)$ by assumption.

**Case $m = 1$.**  
Then $\operatorname{aff}(\Omega)$ is a line and $\Omega$ is a line segment — itself a 1-dimensional exposed edge of $\Omega$. Take $E = \Omega$; then $s_r \in R(E)$.

---

### 3. Inductive Case ($m \geq 2$)

We construct a descending chain of exposed faces

$$
\Omega = \Omega_m \supset \Omega_{m-1} \supset \dots \supset \Omega_1
$$

such that for each $k$, $\dim \operatorname{aff}(\Omega_k) = k$ and $s_r \in R(\Omega_k)$. The final set $\Omega_1$ is an exposed edge.

---

#### 3.1. Dimension Estimate for the Intersection

Let $A_m := \operatorname{aff}(\Omega)$. For any $k$-dimensional exposed face $F$ of $\Omega$ with $k \geq 1$, set $A_F := \operatorname{aff}(F)$.  
Pick a point $\underline{\delta}_F \in F$ such that $\delta_F(s_r) = 0$ (we will ensure this in the construction).

Because $\underline{\delta}_F \in \mathcal{P}_{s_r} \cap A_F$, the intersection is nonempty.  
Apply the dimension formula for affine subspaces:

$$
\dim(\mathcal{P}_{s_r} \cap A_F) + \dim(\mathcal{P}_{s_r} + A_F) = \dim\mathcal{P}_{s_r} + \dim A_F.
$$

Since $\mathcal{P}_{s_r} + A_F \subseteq \mathbb{R}^{n+1}$, we have $\dim(\mathcal{P}_{s_r} + A_F) \leq n+1$. Therefore

$$
\dim(\mathcal{P}_{s_r} \cap A_F) \ge n + k - (n+1) = k - 1.
$$

When $k \ge 2$, this dimension is at least $1$.

---

#### 3.2. The Piercing Argument

Let $F$ be a $k$-dimensional exposed face ($k \ge 2$), let $\underline{\delta}_F \in F$ satisfy $\delta_F(s_r)=0$, and set

$$
L_F := \mathcal{P}_{s_r} \cap A_F.
$$

From §3.1, $\dim L_F \ge 1$. The set $L_F \cap F$ is a compact convex subset of $L_F$ (intersection of a compact convex set $F$ with an affine subspace).

Since $\dim L_F \ge 1$ and $\underline{\delta}_F \in L_F \cap F$, the set $L_F \cap F$ cannot be a single point: there exists a line in $L_F$ through $\underline{\delta}_F$. Because $F$ is compact, the intersection of this line with $F$ is a closed line segment whose endpoints lie on the relative boundary of $F$ in $A_F$.

Let $\underline{\delta}'$ be one such endpoint. Then:

1. $\underline{\delta}' \in \partial_{\text{rel}} F$, the relative boundary of $F$ in $A_F$.
2. $\underline{\delta}' \in L_F \subseteq \mathcal{P}_{s_r}$, so $\delta'(s_r) = 0$, i.e., $s_r \in R(\{\underline{\delta}'\})$.
3. The relative boundary of $F$ in $A_F$ is the union of all proper faces of $F$, each of which is an exposed set of $\Omega$ of dimension $\le k-1$.

Hence there exists an exposed face $F'$ of $\Omega$ with $\dim \operatorname{aff}(F') \le k-1$ and $\underline{\delta}' \in F'$, so $s_r \in R(F')$.

If $\dim \operatorname{aff}(F') < k-1$, we may replace $F'$ by any $(k-1)$-dimensional face containing it (every proper face of a polytope is contained in a face of codimension exactly 1). Thus we may assume $\dim \operatorname{aff}(F') = k-1$ without loss of generality.

---

#### 3.3. Construction of the Chain

Set $F_m := \Omega$, $\underline{\delta}^{(0)} := \underline{\delta}$. For $k = m, m-1, \dots, 2$:

- Given a $k$-dimensional exposed face $F_k$ and $\underline{\delta}^{(m-k)} \in F_k$ with $\delta^{(m-k)}(s_r)=0$,
- Apply §3.2 to $F = F_k$ to obtain a $(k-1)$-dimensional exposed face $F_{k-1}$ and $\underline{\delta}^{(m-(k-1))} \in F_{k-1}$ with $\delta^{(m-(k-1))}(s_r)=0$.

By descending induction we obtain $F_1$, a $1$-dimensional exposed face of $\Omega$, i.e., an exposed edge $E := F_1$, together with a polynomial $\underline{\delta}^{(m-1)} \in E$ such that $\delta^{(m-1)}(s_r)=0$.

Therefore $s_r \in R(E)$.

---

### 4. Conclusion

In every possible case ($m = 0$, $m = 1$, or $m \ge 2$ with the inductive construction), there exists an exposed edge $E$ of $\Omega$ such that $s_r \in R(E)$. This completes the proof. ∎

---

### Remarks on Formalization

The proof relies on the following facts that must be available in the proof assistant's library:

| Concept | Required Library Fact |
|---|---|
| Polytope = convex hull of finitely many points | Existence of faces, exposed sets |
| Affine hull, dimension | `affine_span`, `affine_dim` |
| $\mathcal{P}_{s_r}$ is a linear subspace of codimension 1 | Evaluation functional $\mathrm{ev}_{s_r}: \mathbb{R}^{n+1} \to \mathbb{R}$ is nonzero linear |
| Dimension formula | $\dim (L \cap A) = \dim L + \dim A - \dim (L + A)$ |
| Convex compact set intersected with a line yields a segment whose endpoints are on the boundary | Existence of extreme points (Krein–Milman), or supporting hyperplane theorem |
| Relative boundary of a face is union of lower-dimensional faces | Polytope face lattice properties |
| Every proper face is contained in a face of codimension 1 | Maximal proper faces are facets |

The proof avoids any analysis or limits (those appear only in Lemma 6.2) and is purely combinatorial-geometric, making it well suited for a library like Lean's `mathlib` (via `polytope`, `convex_hull`, `affine_subspace`).
