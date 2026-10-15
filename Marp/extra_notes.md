$$A \subseteq V \text{ is affine iff } \forall x,y \in A, \forall t \in \mathbb{R}, \; (1-t)x + t y \in A$$

$$\mathrm{aff}(S) = \bigcap \{ A \text{ affine subspace} \mid S \subseteq A \}$$


**Step 5 Theorem** (`descend_to_exposed_edge`):

Let $P$ be a polytope, $r \in \mathbb{R}$, $F \subseteq \mathbb{R}^{n+1}$ with:

* $h_{exp} : \mathrm{IsExposedFace}(P,F)$
* $h_{s} : \bar{r} \in R(F)$, $\bar{r} = (r:\mathbb{C})$
* $h_{dim} : \dim \mathrm{dir}(\mathrm{aff}(F)) \geq 2$

Then:
$$\exists E \subseteq \mathbb{R}^{n+1}, \; \mathrm{IsExposedEdge}(P,E) \wedge \bar{r} \in R(E).$$
**Step 5① — Unpack the face root:**

Hypothesis:
$$h_{F} : \bar{r} \in R(F)$$
where $\bar{r} = (r : \mathbb{C})$ and
$$R(F) = \{ s \in \mathbb{C} \mid \exists \delta \in F, \tilde{P}_{\delta}(s) = 0 \}.$$
$$where \ F : Set (CoeffVec \ n) \subseteq \mathbb{R}^{n+1}$$

Unfolding the definition gives a witness:
$$\exists \delta_F \in F, \quad \tilde{P}_{\delta_F}(\bar{r}) = 0.$$

That is `obtain ⟨δ_F, hδ_F_in_F, hδ_F_root⟩ := hs_F`, with:
$$h\delta_{F,in,F} : \delta_F \in F, \qquad h\delta_{F,root} : \mathrm{IsRoot}(\tilde{P}_{\delta_F}, \bar{r}).$$

Convert back to the real slice via `mem_P_sr_of_isRoot`:
$$\delta_F \in P_{s_r}(r) = \{ \delta \mid P_{\delta}(r) = 0 \}.$$

So we now have $\boxed{\delta_F \in F \cap P_{s_r}(r)}$ — a point to run the Step-2/Step-3 machinery on, with $\Omega$ replaced by $F$.


**Step 5② — Relative dimension count:**

Let $U = P_{s_r}(r)$, $\dim U = n$, and $A = \mathrm{aff}(F)$ with $\dim \mathrm{dir}(A) \geq 2$.

Since $\delta_F \in U \cap A$, by `intersection_affine_dim_ge_one`:
$$\dim \mathrm{dir}(\mathrm{aff}(U \cap A)) = \dim(U \cap \mathrm{dir}(A)) \geq n + 2 - (n+1) = 1.$$

I.e. `dim (meetDir n P_sr affF) ≥ 1` — the slice meets $F$ in positive dimension, so Step-3 escape can run inside $F$.


---
**Step 5③ — Escape inside the face:**

Hypotheses: $\delta_F \in F \cap P_{s_r}(r)$ from ①–②, and $\dim \mathrm{dir}(\mathrm{aff}(U \cap A)) \geq 1$.

Then `exists_boundary_point_in_face_rootspace` gives:
$$\exists \delta_{bound} \in F \cap P_{s_r}(r), \quad \delta_{bound} \in \mathrm{frontier}\,F, \quad \delta_{bound} \notin \mathrm{intrinsicInterior}\,F.$$

Mechanism, as in Step 3 with $\Omega$ replaced by $F$:
1. Nonzero $v \in U \cap \mathrm{dir}(A)$ from $\dim \geq 1$.
2. Line $\delta_F + t v \subset U \cap A$.
3. $F$ compact, so $\delta_F + t_{out} v \notin F$ for $t_{out} = (|C|+1)/\|v\|$.
4. Segment $[\delta_F, \delta_F + t_{out} v]$ meets $\mathrm{frontier}\,F$ by connectedness.
5. The crossing point stays in $U$ since the whole line does.

The extra $\notin \mathrm{intrinsicInterior}\,F$ is the relative-boundary condition required as input to Step ④.