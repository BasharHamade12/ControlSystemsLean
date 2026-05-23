# Proof of Lemma: `descend_to_exposed_edge`

This document provides a mathematical proof for the lemma `descend_to_exposed_edge` as implemented in the Lean project for the Discrete Time Edge Theorem.

## Statement
Let $P \subset \mathbb{R}^{n+1}$ be a polytope defined by the convex hull of a finite set of coefficient vectors. Let $r \in \mathbb{R}$ be a real root. If $F$ is an exposed face of $P$ such that there exists a coefficient vector $\delta \in F$ where the corresponding polynomial $p_\delta$ has $r$ as a root (i.e., $r \in \text{RootSpaceSet } F$), and if $F$ is nontrivial (dimension $\ge 1$), then there exists an **exposed edge** $E$ of $P$ such that $r \in \text{RootSpaceSet } E$.

---

## Mathematical Proof

The proof uses induction on the affine dimension of the exposed face $F$. Let $k = \text{dim}(\text{aff } F)$.

### 1. Base Case: $k = 1$
In the Lean implementation, an exposed face $F$ with $\text{dim}(\text{aff } F) = 1$ is defined as an **exposed edge**. If $F$ contains a point $\delta$ such that $p_\delta(r) = 0$, then by definition $r \in \text{RootSpaceSet } F$. Thus, $F$ itself serves as the required exposed edge $E$.

### 2. Inductive Step: $k \ge 2$
Assume $k \ge 2$. We show that we can find a proper subface $G \subsetneq F$ that is also an exposed face of $P$ and still contains a root of $r$.

#### Step A: Existence of a Root-Preserving Direction
Let $\delta_F \in F$ be such that $p_{\delta_F}(r) = 0$. This point lies in the root space $R_r = \{ \delta \mid p_\delta(r) = 0 \}$, which is a linear subspace of codimension 1 in $\mathbb{R}^{n+1}$.
The intersection $I = \text{aff}(F) \cap R_r$ is an affine subspace containing $\delta_F$. Its dimension satisfies:
$$\dim(I) = \dim(\text{aff } F) + \dim(R_r) - \dim(\text{ambient space}) = k + n - (n + 1) = k - 1$$
Since $k \ge 2$, we have $\dim(I) \ge 1$. There exists a non-zero direction vector $v$ in the direction of $I$. By construction, for any $t \in \mathbb{R}$, the point $\delta_F + t v$ is a root of $r$ and lies in the affine span of $F$.

#### Step B: Intersection with the Boundary of $F$
Because $F$ is an exposed face of a polytope, it is itself a compact convex set. Since $v \neq 0$, the line $L(t) = \delta_F + t v$ must eventually exit $F$. 
By the **Segment-Boundary Intersection Lemma**, there exists a point $\delta_{bound}$ on the frontier of $F$ that lies on the segment between $\delta_F$ and some point outside $F$. This $\delta_{bound}$ is also a root of $r$ because it lies on the line in direction $v$.

#### Step C: Descent to a Lower-Dimensional Face
A point $\delta_{bound}$ on the frontier of an exposed face $F$ belongs to some proper exposed face $G$ of $F$. 
- By the **transitivity of exposed faces**, since $G$ is an exposed face of $F$ and $F$ is an exposed face of $P$, $G$ is also an exposed face of $P$.
- Since $G$ is a proper subface, $\dim(G) < \dim(F)$.
- Since $\delta_{bound} \in G$, we have $r \in \text{RootSpaceSet } G$.

### 3. Conclusion
By repeating this descent (or by induction on $k$), we must eventually reach a face of dimension 1. This face is an exposed edge $E$ of $P$ containing a root of $r$.

---

## Current Implementation Status and Next Steps

The following summarizes the current state of the Lean implementation in `EdgeTheorem.lean` and what remains to be done:

### Completed Steps:
- [x] Dimension check for the base case ($m_F = 1$).
- [x] Dimension calculation for its intersection with the root space (`intersection_affine_dim_ge_one`).
- [x] Proof that $F$ is compact and convex.
- [x] Extraction of the direction $v$ and boundary point existence logic (`segment_boundary_intersection`).
- [x] Definition of `escapes_P_via_exposed_face` to show that leaving $F$ along $\text{aff}(F)$ implies leaving $P.\Omega$.

### Steps to Implement Next:
1. **Prove $\delta_{bound}$ belongs to a proper face $G$**: You need to implement the logic that formalizes that any point on the frontier of $F$ is contained in an exposed face of $F$ of strictly lower dimension.
2. **Transitivity of Exposed Faces**: Prove that `IsExposedFace F G` and `IsExposedFace P F` implies `IsExposedFace P G`. 
3. **Formal Induction/Recursion**: Wrap the logic into a recursive function or an inductive proof that uses the decreasing dimension as a termination measure.
4. **Vertex-to-Edge Lemma**: Handle the case where the descent might skip directly to a vertex (dimension 0). You need a lemma stating that if a vertex of a polytope contains a root, it is also contained in an edge of that polytope (which will then also contain the root).
5. **Non-empty Interior**: Prove that if $P.\Omega$ is $n$-dimensional, its interior is non-empty, which is required for the Hahn-Banach supporting hyperplane argument.
