## THE EDGE THEOREM

This chapter deals with the robust stability of a polytopic family of polynomials with respect to an arbitrary stability region. Such problems arise in control systems whenever the characteristic polynomial coefficients are linear (including affine) functions of the uncertain parameters and these vary in intervals. The Edge Theorem shows that the root space of the entire family can be obtained from the root set of the exposed edges. Since the exposed edges are one-parameter sets of polynomials, this theorem effectively and constructively reduces the problem of determining the root space under multiple parameter uncertainty to a set of one-parameter root locus problems. The stability testing property of edges is also extended in this chapter to nested polytopic families.

## 6.1 INTRODUCTION

The Edge Theorem, due to Bartlett, Hollot and Lin appeared in 1988, and was largely motivated by a desire to extend Kharitonov's problem by taking dependencies between the coefficients of the polynomial into account and by dealing with general stability regions. As we have seen in Chapter 4 such dependencies arise in most practical situations and require the investigation of the robust stability of a polytopic family of polynomials. The interval family dealt with in Kharitonov's Theorem is a very special case of a polytopic family. The Edge Theorem gives a complete, exact and constructive characterization of the root set of a polytopic family. Such a characterization is of immense value in the analysis and design of control systems. This entire chapter is devoted to this elegant and useful theorem.

A polytopic family of polynomials can be thought of as the convex hull of a finite number of points (polynomials). Mathematically, this can be represented as the family

$$
P (s) = \lambda_ {1} P _ {1} (s) + \dots + \lambda_ {n} P _ {n} (s)
$$

where $ P_{i}(s) $ are fixed real polynomials and the $ \lambda_{i} $ are real with $ \lambda_{i}\geq 0 $ and $ \sum\lambda_{i}=1. $ An alternative representation of a polytopic family, as used in Chapter 4, is of the form

$$
P (s) = a _ {1} Q _ {1} (s) + a _ {2} Q _ {2} (s) + \dots + a _ {m} Q _ {m} (s)
$$

where each real parameter $ a_{i} $ varies independently in the interval $ [\underline{a}_{i},\bar{a}_{i}]. $ In other words, the parameter vector $ \mathbf{a}:=[a_{1},\dots,a_{m}] $ varies in the hypercube

$$
\mathbf {A} := \left\{\mathbf {a}: \underline {{a}} _ {i} \leq a _ {i} \leq a _ {i}, i = 1, \dots , m \right\}
$$

In some problems, a polytopic family may arise because the system characteristic polynomial

$$
\delta (s, \mathbf {p}) := \delta_ {0} (\mathbf {p}) + \delta_ {1} (\mathbf {p}) s + \dots + \delta_ {n} (\mathbf {p}) s ^ {n}
$$

has coefficients $ \delta_{i} (\mathbf{p}) $ which are linear functions of the parameter vector p. If p varies within a hypercube, it generates a polytopic family of characteristic polynomials. In control problems the elements of p could be physical parameters belonging to the plant or design parameters belonging to the controller.

The Edge Theorem gives an elegant solution to the problem of determining the root space of polytopic systems. As a byproduct we therefore can determine the robust stability of such systems also. It establishes the fundamental property that the root space boundary of a polytopic family of polynomials is contained in the root locus evaluated along the exposed edges. In the following section we give the proof of the Edge Theorem. This is followed by some illustrative examples. In the last section we derive an extension of the stability testing property of edges to nested polynomial families which are not polytopic and where the uncertain parameters appear nonlinearly.

## 6.2 THE EDGE THEOREM

Let us consider a family of $ n^{\mathrm{th}} $ degree real polynomials whose typical element is given by

$$
\delta (s) = \delta_ {0} + \delta_ {1} s + \dots + \delta_ {n - 1} s ^ {n - 1} + \delta_ {n} s ^ {n}.
$$

As usual, we identify $ \mathcal{P}_{n} $ the vector space of all real polynomials of degree less than or equal to n with $ \mathbb{R}^{n+1} $ , and we will identify the polynomial in (6.1) with the vector

$$
\underline {{\delta}} := \left[ \delta_ {n}, \delta_ {n - 1}, \dots , \delta_ {1}, \delta_ {0} \right] ^ {T}.
$$

Let $ \Omega\subset\mathbb{R}^{n+1} $ be an m-dimensional polytope, that is, the convex hull of a finite number of points. As a polytope, $ \Omega $ is a closed bounded set and therefore it is compact. We make the assumption that all polynomials in $ \Omega $ have the same degree:

Assumption 6.1. The sign of $ \delta_{n} $ is constant over $ \Omega $ , either always positive or always negative.

Assuming for example that this sign is always positive, and using the fact that $ \Omega $ is compact, it is always possible to find $ \Delta>0 $ such that,

$$
\delta_ {n} > \Delta , \mathrm {f o r e v e r y} \underline {{\delta}} \in \Omega .
$$

A supporting hyperplane H is an affine set of dimension n such that $ \Omega \cap H \neq \emptyset $ and such that every point of $ \Omega $ lies on just one side of H. The exposed sets of $ \Omega $ are

those (convex) sets $ \Omega \cap H $ where H is a supporting hyperplane. The one dimensional exposed sets are called exposed edges, whereas the two-dimensional exposed sets are the exposed faces.

Before proceeding we need to introduce the notion of root space. Consider any $ W\subset\Omega $ . Then $ R(W) $ is said to be the root space of W if,

$$
R (W) = \{s: \delta (s) = 0, \text {f o r s o m e} \underline {{\delta}} \in W \}.
$$

Finally, recall that the boundary of an arbitrary set S of the complex plane is designated by $ \partial S $ . We can now enunciate and prove the Edge Theorem.

## Theorem 6.1 (Edge Theorem)

Let $ \Omega\subset\mathbb{R}^{n+1} $ be a polytope of polynomials which satisfies Assumption 6.1. Then the boundary of $ R(\Omega) $ is contained in the root space of the exposed edges of $ \Omega. $

To prove the theorem we need two lemmas.

Lemma 6.1 If a real $ s_{r} $ belongs to $ R(\Omega) $ , then there exists an exposed edge E of $ \Omega $ such that $ s_{r}\in R(E) $ , and if a complex number $ s_{c} $ belongs to $ R(\Omega) $ , then there exists an exposed face F of $ \Omega $ such that $ s_{c}\in R(F). $

Proof. Consider an arbitrary $ \underline{\delta} $ in $ \Omega $ , and suppose that $ s_{r} $ is a real root of $ \delta(s) $ . We know that the set of all polynomials having $ s_{r} $ among their roots is a vector space $ \mathcal{P}_{s_{r}} $ of dimension n . Let $ aff(\Omega) $ denote the affine hull of $ \Omega $ , that is, the smallest affine subspace containing $ \Omega $ . Now, assume that $ m=dim[aff(\Omega)]\geq 2 $ . Then we have that,

$$
d i m \left[ \mathcal {P} _ {s _ {r}} \cap a f f (\Omega) \right] \geq 1,
$$

and this implies that this set $ \mathcal{P}_{s_{r}}\cap aff(\Omega) $ must pierce the relative boundary of $ \Omega $ This relative boundary however, is the union of some m-1 dimensional polytopes which are all exposed sets of $ \Omega $ . Therefore, at least one of these boundary polytopes $ \Omega_{m-1} $ satisfies,

$$
s _ {r} \in R \left(\Omega_ {m - 1}\right).
$$

If $dim[aff(\Omega_{m-1})]\geq 2$, we see that we can repeat the preceding argument and ultimately we will find a one-dimensional boundary polytope $ \Omega_{1} $ for which $ s_{r}\in R(\Omega_{1}) $ . But $ \Omega_{1} $ is just an exposed edge of $ \Omega $ , so that $ s_{r} $ does indeed belong to the root space of the exposed edges of $ \Omega $ . For the case of a complex root $ s_{c} $ , it suffices to know that the set of all real polynomials having $ s_{c} $ among their roots is a vector space $ \mathcal{P}_{s_{c}} $ of dimension n-1. As a consequence the same reasoning as above holds, yielding eventually an exposed face $ \Omega_{2} $ of $ \Omega $ for which $ s_{c}\in R(\Omega_{2}) $

We illustrate this lemma in Figures 6.1, 6.2, and 6.3 with a three dimensional polytope $ \Omega $ (see Figure 6.1). Here $ \mathcal{P}_{s_{r}} $ is a subspace of dimension 2 and cuts the edges of $ \Omega $ (see Figure 6.2). $ \mathcal{P}_{s_{c}} $ is of dimension 1 and must penetrate a face of $ \Omega $ (see Figure 6.3).

<div style='text-align: center;'><img src='https://maas-watermark-prod-new.cn-wlcb.ufileos.com/ocr%2Fcrop%2F20260416202317df11c33e8d5e4fea%2Fcrop_1_1776342231875.png?UCloudPublicKey=TOKEN_6df395df-5d8c-4f69-90f8-a4fe46088958&Signature=K8UBesKkNiw%2BXM1kLhxOqh5u8Ew%3D&Expires=1776947031' alt='OCR图片'/></div>

<div align="center">

Figure 6.1. Polytope $ \Omega $

</div>

<div style='text-align: center;'><img src='https://maas-watermark-prod-new.cn-wlcb.ufileos.com/ocr%2Fcrop%2F20260416202317df11c33e8d5e4fea%2Fcrop_2_1776342231933.png?UCloudPublicKey=TOKEN_6df395df-5d8c-4f69-90f8-a4fe46088958&Signature=dEvq4WQyaga6FQNW8lwGCkYVzs8%3D&Expires=1776947031' alt='OCR图片'/></div>

<div align="center">

Figure 6.2. $ \mathcal{P}_{s_{r}} $ cuts edges of $ \Omega $

</div>

<div style='text-align: center;'><img src='https://maas-watermark-prod-new.cn-wlcb.ufileos.com/ocr%2Fcrop%2F20260416202317df11c33e8d5e4fea%2Fcrop_1_1776342231980.png?UCloudPublicKey=TOKEN_6df395df-5d8c-4f69-90f8-a4fe46088958&Signature=uBAmP%2FWiBdAVsSbtmQLnfwGns0Y%3D&Expires=1776947031' alt='OCR图片'/></div>

<div align="center">

Figure 6.3. $ \mathcal{P}_{s_{c}} $ penetrates a face of $ \Omega $

</div>

The conclusion of this first lemma is that if $ p_{F} $ is the number of exposed faces, then

$$
R (\Omega) = \bigcup_ {i = 1} ^ {p _ {F}} R \left(F _ {i}\right).
$$

The next lemma focuses now on an exposed face. Let F be an exposed face of $ \Omega $ and let us denote by $ \partial F $ its relative boundary. Since F is a compact set and because of Assumption 6.1 on $ \Omega $ , we know from Chapter 2 that $ R(F) $ is itself a closed set. We have the following.

Lemma 6.2 $ \partial R ( F ) \subset R ( \partial F ). $

Proof. Let $ s^{*} $ be an arbitrary element of $ \partial R(F) $ , we want to show that $ s^{*} $ is also an element of $ R(\partial F) $ . Since $ \partial F $ is the union of exposed edges of $ \Omega $ , it follows from Lemma 6.1 that if $ s^{*} $ is real then $ s^{*} \in R(\partial F) $ .

Now assume that $ s^{*} $ is complex. Since $ R(F) $ is a closed set, $ \partial R(F)\subset R(F) $ , so that it is possible to find $ \underline{\delta}^{*} \in F $ with $ \delta^{*}(s^{*})=0 $ . We can write

$$
\delta^ {*} (s) = \left(s ^ {2} + \alpha s + \beta\right) \left(d _ {n - 2} s ^ {n - 2} + \dots + d _ {1} s + d _ {0}\right)
$$

where $ \alpha=-2\mathrm{Re}(s^{*}) $ and $ \beta=|s^{*}|^{2} $ . Let aff(F) be the affine hull of F. Since F is two-dimensional it is possible to write aff(F) $ = \{\underline{\delta}^{*}+V\lambda ;\lambda\in\mathrm{I R}^{2}\} $ , where V is

some full rank $ ( n+1)\times2 $ matrix. On the other hand, an arbitrary element of the vector space of real polynomials with a root at $ s^{*} $ can be written as

$$
P ^ {*} (s) = \left(s ^ {2} + \alpha s + \beta\right) \left[ \left(\left(\mu_ {n - 2} + d _ {n - 2}\right) s ^ {n - 2} + \dots + \left(\mu_ {1} + d _ {1}\right) s + \left(\mu_ {0} + d _ {0}\right)\right) \right],
$$

or more generally we can write,

$$
\mathcal {P} _ {s ^ {*}} = \left\{\underline {{\delta}} ^ {*} + W \mu : \mu = \left[ \mu_ {n - 2}, \dots , \mu_ {1}, \mu_ {0} \right] ^ {T} \in \mathbb {R} ^ {n - 2} \right\},
$$

where W is the $ ( n+1 ) \times( n-1 ) $ matrix,

$$
W = \left[ \begin{array}{c c c c} 1 & 0 & \dots & 0 \\ \alpha & 1 & \dots & 0 \\ \beta & \alpha & \dots & 0 \\ 0 & \beta & \dots & 0 \\ \vdots & \vdots & \ddots & \vdots \\ 0 & 0 & \dots & 1 \\ 0 & 0 & \dots & \alpha \\ 0 & 0 & \dots & \beta \end{array} \right].
$$

The intersection between $ aff(F) $ and $ \mathcal{P}_{s^{*}} $ contains all $ \lambda, \mu $ satisfying,

$$
\underline {{\delta}} ^ {*} + V \lambda = \underline {{\delta}} ^ {*} + W \mu , \mathrm {o r e q u i v a l e n t l y}, [ V, - W ] \left[ \begin{array}{c} \lambda \\ \mu \end{array} \right] = 0.
$$

Two possibilities have to be considered:

## A. [V,-W] does not have full rank

In this case, the space of solutions to (6.10) is either of dimension 1 or 2. If it is of dimension one, then the intersection $aff(F)\cap \mathcal{P}_{s^{*}}$ is a straight line which must intersect $ \partial F $ at a point $ \hat{\delta} $ . Since $ \hat{\delta}\in \mathcal{P}_{s^{*}} $ $ \hat{\delta}(s^{*})=0 $ , which implies that $ s^{*} \in R(\partial F). $ If the dimension is two then $ aff(F)\subset \mathcal{P}_{s^{*}} $ and for any $ \hat{\delta}\in \partial F $ we have $ \hat{\delta}(s^{*})=0 $ so that clearly $ s^{*} \in R(\partial F). $

## B. $ [ V,-W ] $ has full rank

In this case the intersection $aff(F)\cap \mathcal{P}_{s^{*}}$ is reduced to $ \underline{\delta}^{*} $ . We now prove that $ \underline{\delta}^{*} \in \partial F $ and this is where the fact that $ s^{*} \in \partial R(F) $ is utilized.

Indeed, $ s^{*} \in \partial R(F) $ implies the existence of a sequence of complex numbers $ s_{n} $ such that $ s_{n}\notin R(F) $ for all n and such that $ s_{n}\longrightarrow s^{*} $ as n $ \rightarrow+\infty $ . In particular this implies that,

$$
- 2 R e \left(s _ {n}\right) \longrightarrow \alpha \mathrm {a n d} \left| s _ {n} \right| ^ {2} \longrightarrow \beta \mathrm {a s} n \rightarrow + \infty .
$$

As usual, let $ \mathcal{P}_{s_{n}} $ be the vector space of all real polynomials with a root at $ s_{n} $ . An arbitrary element of $ \mathcal{P}_{s_{n}} $ can be expressed as

$$
\begin{array}{l} P (s) = \delta^ {*} (s) + \left(\left(s ^ {2} - 2 \operatorname {R e} \left(s _ {n}\right) s + \left| s _ {n} \right| ^ {2}\right) \left(\mu_ {n - 2} s ^ {n _ {2}} + \dots + \mu_ {1} s + \mu_ {0}\right) + \right. \\ + \left(- \left(2 \operatorname {R e} \left(s _ {n}\right) + \alpha\right) s + \left(\left| s _ {n} ^ {2} \right| - \beta\right)\right) \left(d _ {n - 2} s ^ {n - 2} + \dots + d _ {1} s + d _ {0}\right), \\ \end{array}
$$

or, similarly

$$
\mathcal {P} _ {s _ {n}} = \left\{\underline {{\delta}} ^ {*} + W _ {n} \mu + \nu_ {n}: \mu = \left[ \mu_ {n - 2}, \dots , \mu_ {1}, \mu_ {0} \right] \in \mathbb {R} ^ {n - 1} \right\}.
$$

where,

$$
W _ {n} = \left[ \begin{array}{c c c c} 1 & 0 & \dots & 0 \\ - 2 R e \left(s _ {n}\right) & 1 & \dots & 0 \\ \left| s _ {n} \right| ^ {2} & - 2 R e \left(s _ {n}\right) & \dots & 0 \\ 0 & \left| s _ {n} \right| ^ {2} & \dots & 0 \\ \vdots & \vdots & \ddots & \vdots \\ 0 & 0 & \dots & 1 \\ 0 & 0 & \dots & - 2 R e \left(s _ {n}\right) \\ 0 & 0 & \dots & \left| s _ {n} \right| ^ {2} \end{array} \right].
$$

and

$$
\nu_ {n} = \left[ \begin{array}{c c} d _ {n - 2} & 0 \\ d _ {n - 3} & d _ {n - 2} \\ d _ {n - 4} & d _ {n - 3} \\ \vdots & \vdots \\ d _ {0} & d _ {1} \\ 0 & d _ {0} \end{array} \right] \left[ \begin{array}{c} - \left(2 R e \left(s _ {n}\right) + \alpha\right) \\ | s _ {n} | ^ {2} - \beta \end{array} \right].
$$

Clearly,

$$
W _ {n} \longrightarrow W \text {a n d} \nu_ {n} \longrightarrow 0 \text {a s} n \rightarrow + \infty .
$$

Now, since $ \det(\cdot) $ is a continuous function and since $ \det[V,-W]\neq0 $ , there must exist $ n_{1} $ such that $ \det[V-W_{n}]\neq0 $ for $ n\geq n_{1} $ . Also, for every n, the intersection between $ \mathcal{P}_{s_{n}} $ and $ aff(F) $ consists of all $ \lambda, \mu $ that satisfy:

$$
\underline {{\delta}} ^ {*} + W _ {n} \mu + \nu_ {n} = \underline {{\delta}} ^ {*} + V \lambda
$$

or equivalently

$$
[ V, - W _ {n} ] \left[ \begin{array}{c} \lambda \\ \mu \end{array} \right] = \nu_ {n}.
$$

For $ n\geq n_{1} $ , the system (6.15) has a unique solution,

$$
\left[ \begin{array}{c} \lambda_ {n} \\ \mu_ {n} \end{array} \right] = [ V, - W _ {n} ] ^ {- 1} \nu_ {n}.
$$

From (6.16) we deduce that $[\lambda_{n}^{T},\mu_{n}^{T}] \longrightarrow 0$ when $n \rightarrow +\infty$.

We now show that $ \underline{\delta}^{*} $ belongs to $ \partial F $ . Let us consider an arbitrary open neighborhood in aff(F),

$$
B _ {F} \left(\underline {{\delta}} ^ {*}, \epsilon\right) = \left\{\underline {{\delta}} \in a f f (F): \| \underline {{\delta}} - \underline {{\delta}} ^ {*} \| < \epsilon \right\},
$$

We must show that $B_{F}(\underline{\delta}^{*},\epsilon)$ contains at least one vector not contained in $F$.

To do so, consider the intersection between $ \mathcal{P}_{s_{n}} $ and $ aff(F) $ , that is the vector $ \underline{\delta}_{n}=\underline{\delta}^{*}+V\lambda_{n} $ . This vector belongs to $ aff(F) $ , and since $ \lambda_{n} $ goes to 0, it belongs to $ B_{F}(\underline{\delta}^{*},\epsilon) $ for n sufficiently large. Moreover, the polynomial corresponding to this vector has a root at $ s_{n} $ and we know that $ s_{n} $ does not belong to $ R(F) $ . Hence it must be the case that $ \underline{\delta}_{n} $ does not belong to F, and this completes the proof of the lemma.

Figures 6.4 and 6.5 illustrate this lemma. The sequence $ s_{n} $ converges to $ s^{*} \in R(F) $ from outside of $ R(F) $ . The corresponding subspaces $ \mathcal{P}_{s_{n}} $ converge to $ \mathcal{P}_{s^{*}} $ from outside F. Thus $ \mathcal{P}_{s^{*}} $ must touch an edge of F.

<div style='text-align: center;'><img src='https://maas-watermark-prod-new.cn-wlcb.ufileos.com/ocr%2Fcrop%2F20260416202317df11c33e8d5e4fea%2Fcrop_1_1776342231987.png?UCloudPublicKey=TOKEN_6df395df-5d8c-4f69-90f8-a4fe46088958&Signature=X5rkbNjJGElpQYbQEajYKhi9E%2BU%3D&Expires=1776947031' alt='OCR图片'/></div>

<div align="center">

Figure 6.4. The sequence $ s_{n}\notin R(F) $ converges to $ s^{*} \in \partial R(F) $

</div>

<div style='text-align: center;'><img src='https://maas-watermark-prod-new.cn-wlcb.ufileos.com/ocr%2Fcrop%2F20260416202317df11c33e8d5e4fea%2Fcrop_1_1776342231997.png?UCloudPublicKey=TOKEN_6df395df-5d8c-4f69-90f8-a4fe46088958&Signature=Mm0%2FmLTeGsm9k%2BoH%2FjMEwmA72FA%3D&Expires=1776947032' alt='OCR图片'/></div>

<div align="center">

Figure 6.5. The sequence $ \mathcal{P}_{s_{n}} \left( \mathcal{P}_{s_{i}} \cap F=\emptyset \right) $ converges to $ \mathcal{P}_{s^{*}} $

</div>

Proof of the Edge Theorem (Theorem 6.1) From (6.5) and Lemma 6.2 we have

$$
\partial R (\Omega) = \partial \bigcup_ {i = 1} ^ {p _ {F}} R \left(F _ {i}\right) = \bigcup_ {i = 1} ^ {p _ {F}} \partial R \left(F _ {i}\right) \subset \bigcup_ {i = 1} ^ {p _ {F}} R \left(\partial F _ {i}\right).
$$

The $ \partial F_{i} $ are precisely the exposed edges of $ \Omega $ and this proves the theorem.

Let us now consider an arbitrary simply connected domain of the complex plane, that is, a subset of the complex plane in which every simple (i.e. without selfcrossings) closed contour encloses only points of the set. We can state the following corollary:

Corollary 6.1 If $ \Gamma\subset C $ is a simply connected domain, then for any polytope satisfying Assumption 6.1, $ R(\Omega) $ is contained in $ \Gamma $ if and only if the root space of all the exposed edges of $ \Omega $ is contained in $ \Gamma. $

## Exposed Edges

In general, a polytope is defined by its vertices and it is not immediately clear how to determine which are the exposed edges of $ \Omega $ . However, it is clear that those exposed edges are part of all pairwise convex combinations of the vertices of $ \Omega $ , and

therefore it is enough to check those. In the representation

$$
\mathcal {P} := \left\{P (s): P (s) = a _ {1} Q _ {1} (s) + a _ {2} Q _ {2} (s) + \dots + a _ {m} Q _ {m} (s), \mathbf {a} \in \mathbf {A} \right\}
$$

where $ \mathbf{a}=[a_{1}, a_{2}, \dots, a_{m}]$ the exposed edges of the polytope $ \mathcal{P} $ are obtained from the exposed edges of the hypercube A to which a belongs. This can be done by fixing all $ a_{i} $ except one, say $ a_{k} $ , at a vertex $ \underline{a}_{i} $ or $ \bar{a}_{i} $ , and letting $ a_{k} $ vary in the interval $ [\underline{a}_{k}, \bar{a}_{k}] $ , and repeating this for $ k=1,\dots,m $ . In general, the number of line segments in the coefficient space generated by this exceeds the number of exposed edges of $ \mathcal{P} $ . Nevertheless, this procedure captures all the exposed edges.

We note that within the assumptions required by this result, stability verification amounts to checking the root-location of line segments of polynomials of the form

$$
P _ {\lambda} (s) = (1 - \lambda) P _ {1} (s) + \lambda P _ {2} (s), \quad \lambda \in [ 0, 1 ].
$$

The root-locus technique can be used for this purpose. Alternatively the Segment Lemma given in Chapter 2 can also be used when the boundary of the domain $ \Gamma $ of interest can be parametrized easily. This theorem is the best result that one can expect at this level of generality, because as we have shown in Chapter 2 a line segment joining two stable polynomials is not necessarily stable. To reiterate, consider the following simple polytope consisting of the segment joining the two points

$$
P _ {1} (s) = 3 s ^ {4} + 3 s ^ {3} + 5 s ^ {2} + 2 s + 1 \mathrm {a n d} P _ {2} (s) = s ^ {4} + s ^ {3} + 5 s ^ {2} + 2 s + 5.
$$

It can be checked that both $ P_{1}(s) $ and $ P_{2}(s) $ are Hurwitz stable and yet the polynomial

$$
\frac {P _ {1} (s) + P _ {2} (s)}{2} \quad \mathrm {h a s a r o o t a t} s = j.
$$

We illustrate the Edge Theorem with some examples.

## 6.3 EXAMPLES

Example 6.1. Consider the interval control system in Figure 6.6:

<div style='text-align: center;'><img src='https://maas-watermark-prod-new.cn-wlcb.ufileos.com/ocr%2Fcrop%2F20260416202317df11c33e8d5e4fea%2Fcrop_1_1776342232019.png?UCloudPublicKey=TOKEN_6df395df-5d8c-4f69-90f8-a4fe46088958&Signature=hZmUbUNSSs7adTKb1SZ3T0B1tQI%3D&Expires=1776947032' alt='OCR图片'/></div>

<div align="center">

Figure 6.6. A gain feedback system (Example 6.1)

</div>

Let

$$
G (s) = \frac {\delta_ {2} s ^ {2} + \delta_ {0}}{s \left(s ^ {2} + \delta_ {1}\right)}
$$

and assume that K=1. Then the characteristic polynomial of this family of systems is the interval polynomial

$$
\delta (s) = s ^ {3} + \delta_ {2} s ^ {2} + \delta_ {1} s + \delta_ {0}
$$

where

$$
\delta_ {2} \in [ 6, 8 ], \quad \delta_ {1} \in [ 1 4, 1 8 ], \quad \delta_ {0} \in [ 9. 5, 1 0. 5 ].
$$

The three variable coefficients form a box with 12 edges in the coefficient space. By the Edge Theorem, the boundary of the root space of the interval polynomial family can be obtained by plotting the root loci along the exposed edges of the box. The root loci of the edges is shown in Figure 6.7. Since the entire root space of the set of characteristic polynomials is found to be in the LHP, the family of feedback systems is robustly stable.

<div style='text-align: center;'><img src='https://maas-watermark-prod-new.cn-wlcb.ufileos.com/ocr%2Fcrop%2F20260416202317df11c33e8d5e4fea%2Fcrop_1_1776342232026.png?UCloudPublicKey=TOKEN_6df395df-5d8c-4f69-90f8-a4fe46088958&Signature=wmNcpUKYSqQQ66f6xernWN0QvO4%3D&Expires=1776947032' alt='OCR图片'/></div>

<div align="center">

Figure 6.7. Root space for K=1 (Example 6.1)

</div>

We remark that the robust stability of this system could have been checked by determining whether the Kharitonov polynomials are stable or not. However the Edge Theorem has given us considerably more information by generating the entire root set. From this set, depicted in Figure 6.7, we can evaluate the performance

<div style='text-align: center;'><img src='https://maas-watermark-prod-new.cn-wlcb.ufileos.com/ocr%2Fcrop%2F20260416202317df11c33e8d5e4fea%2Fcrop_1_1776342232033.png?UCloudPublicKey=TOKEN_6df395df-5d8c-4f69-90f8-a4fe46088958&Signature=sjxeSXy1b8rvSpPGovWMJRB2AzI%3D&Expires=1776947032' alt='OCR图片'/></div>

<div align="center">

Figure 6.8. Root spaces for various K (Example 6.1)

</div>

of the system in terms of such useful quantities as the worst case damping ratio, stability degree (minimum distance of the root set to the imaginary axis), largest damped and undamped natural frequencies, etc.

The movement of the entire root space with respect to the gain K can be studied systematically by repeatedly applying the Edge Theorem for each K. Figure 6.8 shows the movement of the root space with respect to various gains K. It shows that the root space approaches the imaginary axis as the gain K approaches the value 5. The root sets of the Kharitonov polynomials are properly contained in the root space for small values of K. However as K approaches the value where the family is just about to become unstable, the roots of the Kharitonov polynomials move out to the right hand boundary of the root set. These roots are therefore the "first" set of roots of the system to cross the imaginary axis.

Example 6.2. Let us consider the unity feedback discrete time control system with forward transfer function:

$$
G (z) = \frac {\delta_ {1} z + \delta_ {0}}{z ^ {2} \left(z + \delta_ {2}\right)}.
$$

The characteristic polynomial is

$$
\delta (z) = z ^ {3} + \delta_ {2} z ^ {2} + \delta_ {1} z + \delta_ {0}.
$$

Suppose that the coefficients vary in the intervals

$$
\delta_ {2} \in [ 0. 0 4 2, 0. 1 5 8 ], \quad \delta_ {1} \in [ - 0. 0 5 8, 0. 0 5 8 ], \quad \delta_ {0} \in [ - 0. 0 6, 0. 0 5 6 ]
$$

The boundary of the root space of the family can be generated by drawing the root loci along the 12 exposed edges of the box in coefficient space. The root space is inside the unit disc as shown in Figure 6.9. Hence the entire family is Schur stable.

<div style='text-align: center;'><img src='https://maas-watermark-prod-new.cn-wlcb.ufileos.com/ocr%2Fcrop%2F20260416202317df11c33e8d5e4fea%2Fcrop_1_1776342232042.png?UCloudPublicKey=TOKEN_6df395df-5d8c-4f69-90f8-a4fe46088958&Signature=CZAToFSZ9eFMS8r11w19DhwvexY%3D&Expires=1776947032' alt='OCR图片'/></div>

<div align="center">

Figure 6.9. Root space of $ \delta (z) $ (Example 6.2)

</div>

Example 6.3. Consider the interval plant

$$
G (s) = \frac {s + a}{s ^ {2} + b s + c}
$$

where

$$
a \in [ 1, 2 ], \quad b \in [ 9, 1 1 ], \quad c \in [ 1 5, 1 8 ].
$$

The controller is

$$
C (s) = \frac {3 s + 2}{s + 5}.
$$

The closed loop characteristic polynomial is

$$
\begin{array}{l} \delta (s) = \left(s ^ {2} + b s + c\right) (s + 5) + (s + a) (3 s + 2) \\ = a (3 s + 2) + b \left(s ^ {2} + 5 s\right) + c (s + 5) + \left(s ^ {3} + 8 s ^ {2} + 2 s\right). \\ \end{array}
$$

The boundary of the root space of $ \delta(s) $ can be obtained by plotting the root loci along the 12 exposed edges. It can be seen from Figure 6.10 that the family $ \delta(s) $ is stable since the root space is in the left half plane. Hence the given compensator robustly stabilizes the interval plant. From the root set generated we can evaluate the performance of the controller in terms of the worst case damping ratio, the minimum stability degree and the maximum frequency of oscillation.

<div style='text-align: center;'><img src='https://maas-watermark-prod-new.cn-wlcb.ufileos.com/ocr%2Fcrop%2F20260416202317df11c33e8d5e4fea%2Fcrop_1_1776342232056.png?UCloudPublicKey=TOKEN_6df395df-5d8c-4f69-90f8-a4fe46088958&Signature=qSbVUKogfpqjc7RDi9WZaPzovaU%3D&Expires=1776947032' alt='OCR图片'/></div>

<div align="center">

Figure 6.10. Root loci of the edges (Example 6.3)

</div>

The Edge Theorem has many useful applications. For instance, it can be effectively used to determine the coprimeness of two polytopic families of polynomials as shown in the following example.

Example 6.4. Consider the two polynomials

$$
\delta_ {A} (s) = p _ {0} \delta_ {A _ {0}} (s) + p _ {1} \delta_ {A _ {1}} (s) + p _ {2} \delta_ {A _ {2}} (s)
$$

$$
\delta_ {B} (s) = q _ {0} \delta_ {B _ {0}} (s) + q _ {1} \delta_ {B _ {1}} (s) + q _ {2} \delta_ {B _ {2}} (s)
$$

where

$$
\delta_ {A _ {0}} (s) = 0. 2 s ^ {4} + 2 s ^ {3} + 1 0 0 s ^ {2} + 6 0 0 s + 5 0 0 0
$$

$$
\delta_ {A _ {1}} (s) = 0. 3 s ^ {4} + 8 s ^ {3} + 2 0 0 s ^ {2} + 1 0 0 0 s + 1 5 0 0 0
$$

$$
\delta_ {A _ {2}} (s) = 0. 5 s ^ {4} + 2 s ^ {3} + 1 1 5 s ^ {2} + 9 9 8 s + 1 8 1 9 4
$$

$$
\delta_ {B _ {0}} (s) = 0. 1 s ^ {4} + 3 s ^ {3} + 5 0 s ^ {2} + 5 0 0 s + 1 0 0 0
$$

$$
\delta_ {B _ {1}} (s) = 0. 3 s ^ {4} + 3 s ^ {3} + 5 0 s ^ {2} + 5 0 0 s + 2 0 0 0
$$

$$
\delta_ {B _ {2}} (s) = 0. 6 s ^ {4} + 3 s ^ {3} + 8 8. 5 s ^ {2} + 1 9 0. 3 s + 2 2 2 9. 1
$$

and the nominal value of parameters p are

$$
\mathbf {p} ^ {0} = \left[ p _ {0} ^ {0} p _ {1} ^ {0} p _ {2} ^ {0} q _ {0} ^ {0} q _ {1} ^ {0} q _ {2} ^ {0} \right] = \left[ 1 1 1 1 1 1 \right].
$$

<div style='text-align: center;'><img src='https://maas-watermark-prod-new.cn-wlcb.ufileos.com/ocr%2Fcrop%2F20260416202317df11c33e8d5e4fea%2Fcrop_1_1776342232066.png?UCloudPublicKey=TOKEN_6df395df-5d8c-4f69-90f8-a4fe46088958&Signature=p1T0o40Rzto9RUkmQtOCVL4DhdE%3D&Expires=1776947032' alt='OCR图片'/></div>

<div align="center">

Figure 6.11. Roots of $ \delta_{A} ( s ) $ and $ \delta_{B} ( s ) $ (Example 6.4)

</div>

Figure 6.11 shows the roots of the two polynomials at the nominal parameter $ \mathbf{p}=\mathbf{p}^{0} $ . The roots of $ \delta_{A}(s) $ and $ \delta_{B}(s) $ are labeled in the figure as "A" and "B", respectively. Clearly, these two polynomials are coprime as the root sets are disjoint. Now suppose that the parameters $ \mathbf{p} $ and $ \mathbf{q} $ perturb in interval sets. We define perturbation boxes for the parameters $ \mathbf{p} $ and $ \mathbf{q} $ as follows:

$$
\begin{array}{l} \Pi_ {p} := \left\{\left[ p _ {i} - \omega_ {1} \epsilon , p _ {i} + \omega_ {1} \epsilon \right], \quad i = 0, 1, 2 \right\} \\ \Pi_ {q} := \left\{\left[ q _ {i} - \omega_ {2} \epsilon , q _ {i} + \omega_ {2} \epsilon \right], \quad i = 0, 1, 2 \right\} \\ \end{array}
$$

where

$$
[ \omega_ {1} \quad \omega_ {2} ] = [ 1 5 ].
$$

Suppose that we want to determine the maximum value of $ \epsilon $ such that these two families of polynomials remain coprime. This can be accomplished by examining the root space for increment values of $ \epsilon $ . We observe that the root spaces are touching each other at $ \epsilon=0.14 $ . As shown in Figure 6.12, certain polynomials in the $ \delta_{A}(s) $ and $ \delta_{B}(s) $ families share common roots at the " $ ^{*} $ " locations. Therefore, at this point the families cease to be coprime.

<div style='text-align: center;'><img src='https://maas-watermark-prod-new.cn-wlcb.ufileos.com/ocr%2Fcrop%2F20260416202317df11c33e8d5e4fea%2Fcrop_1_1776342232091.png?UCloudPublicKey=TOKEN_6df395df-5d8c-4f69-90f8-a4fe46088958&Signature=w7wokqiaBi752Q2bukz9gzjB%2Bxk%3D&Expires=1776947032' alt='OCR图片'/></div>

<div align="center">

Figure 6.12. Root space of $ \delta_{A} (s) $ and $ \delta_{B} (s) $ for $ \epsilon=0.14 $ (Example 6.4)

</div>

## 6.4 EXTENSIONS OF EDGE RESULTS

An important consequence of the Edge Theorem is that the stability of a polytopic family of polynomials can be ascertained from the stability of its exposed edges. This was exploited to develop robust stability tests for polytopic systems in Chapter 4. In this section we extend this stability testing property of the exposed edges to a larger family. This family consists of a polynomial function of a polytope. The results given here are analogous to the extensions of Kharitonov's Theorem to polynomial functions of interval polynomials, given in the last Chapter.

In the following we assume that an open subset $ S $ of the complex plane is given as the stability region, and stable will mean stability with respect to this region, unless specified otherwise. We shall also assume that all polynomial families under discussion are of constant degree.

Let

$$
\mathcal {P} (s) = \left\{a (s, \mathbf {p}) = \sum_ {j = 0} ^ {n} a _ {j} (\mathbf {p}) s ^ {j}: \mathbf {p} \in \mathbf {P} \right\}
$$

denote a real polytopic family of polynomials. Here $ \mathbf{p}=[p_{1}, p_{2}, \dots, p_{l}]$ is a real vector of uncertain parameters, $ a_{j}(\mathbf{p}) $ are linear functions of $ \mathbf{p} $ and $ \mathbf{P} $ is a convex polytope. We also suppose that

$$
\varphi (z) = \alpha_ {0} + \alpha_ {1} z + \dots + \alpha_ {m} z ^ {m},
$$

is a given polynomial. We ask the question: Under what conditions is the family of polynomials

$$
\varphi (\mathcal {P} (s)) = \left\{\varphi (a (s)): a (s) \in \mathcal {P} (s) \right\}
$$

stable?

Let $ \mathcal{E}_{\mathcal{P}}(s) $ denote the subset of $ \mathcal{P}(s) $ corresponding to the edges of $ \mathcal{P}(s) $ . We know that stability of the edge polynomials $ \mathcal{E}_{\mathcal{P}}(s) $ implies stability of the polynomial family $ \mathcal{P}(s) $ . The next lemma follows from this.

Lemma 6.3 Given the polytopic family (6.18) and a complex number z, the stability of the set of polynomials

$$
\mathcal {P} (s) - z = \left\{a (s) - z: a (s) \in \mathcal {P} (s) \right\}.
$$

is implied by the stability of the family

$$
\mathcal {E} _ {\mathcal {P}} (s) - z = \left\{a (s) - z: a (s) \in \mathcal {E} _ {\mathcal {P}} (s) \right\}.
$$

## Stability domains

Let us consider a one parameter family of polynomials

$$
(1 - \mu) a _ {k} (s) + \mu a _ {j} (s), \quad \mu \in [ 0, 1 ]
$$

corresponding to an edge of P. The image set of this segment at $ s=j\omega $ is a complex plane line segment. As $ \omega $ is swept from $ -\infty $ to $ +\infty $ this segment moves continuously on the complex plane and generates a "thick" curve which partitions the complex plane into a finite number of open disjoint domains. With each of these domains we associate an integer number defined as the number of roots of $ a(s)-z $ in S. This number is independent of the choice of $ a(s) $ in the segment and z in the domain. There is at most one domain, $ \Lambda_{kj} $ , called the stability domain associated with $ a_{k}(s) $ for which the integer number is equal to $ n=\deg(a_{k}) $ . With every element of $ \mathcal{E}_{\mathcal{P}}(s) $ we associate such a stability domain $ \Lambda_{kj} $ of the complex plane and let $ \Lambda $ be the intersection of these domains:

$$
\Lambda = \cap \Lambda_ {k j}.
$$

We will say that a polynomial is $ \Lambda $ -stable if all its roots lie in $ \Lambda $ . Then we have the following result.

Theorem 6.2 Let $ \Lambda\neq\emptyset $ . Then the family (6.20) is stable if and only if $ \varphi(z) $ is $ \Lambda $ -stable.

## Proof.

Sufficiency: The polynomial $ \varphi(z) $ is $ \Lambda $-stable, and so the roots $ z_{1}, z_{2}, \dots, z_{m} $ of $ \varphi(z) $ lie in $ \Lambda $ . Now, stability of $ \varphi(\mathcal{P}(s)) $ is equivalent to stability of $ \mathcal{P}(s)-z_{j}, $ $ j=1,2,\dots,m. $ By Lemma 6.3 stability of $ \mathcal{P}(s)-z_{j} $ follows from the stability of the set $ \mathcal{E}_{\mathcal{P}}(s)-z_{j}. $ But the condition $ z_{j} \in \Lambda $ guarantees stability of each of the sets $ \mathcal{E}_{\mathcal{P}}(s)-z_{j}, $ $ j=1,2,\dots,m. $

Necessity: Stability of $ \varphi(\mathcal{P}(s)) $ implies the stability of $ \mathcal{P}(s)-z_{j}, j=1,2,\cdots,m. $ By Lemma 6.3 the family $ \mathcal{P}(s)-z_{j} $ is stable only if $ \mathcal{E}_{\mathcal{P}}(s)-z_{j} $ is stable. This implies that $ z_{j}\in\Lambda $ , or $ \varphi(z) $ is $ \Lambda $ -stable.

This theorem can be given in the equivalent and more useful form.

Theorem 6.3 The polynomial family $ \varphi(\mathcal{P}(s)) $ is stable if and only if the family

$$
\varphi \left(\mathcal {E} _ {\mathcal {P}} (s)\right) = \left\{\varphi \left(a (s)\right): a (s) \in \mathcal {E} _ {\mathcal {P}} (s) \right\}
$$

corresponding to the edges of $ \mathcal{P} (s) $ , is stable.

The proof of this result follows immediately from Theorem 6.2 and Lemma 6.3 and is left to the reader. The result is an extension of the stability testing property of exposed edges to a case where the uncertain parameters appear nonlinearly in the family.

We considered thus far that the polynomial $ \varphi(z) $ is fixed. Now suppose that $ \varphi(z) $ is an uncertain polynomial, and in particular belongs to a polytope. Let

$$
\Phi (z) := \left\{\varphi (z): \left(\alpha_ {0}, \alpha_ {1}, \alpha_ {2}, \dots , \alpha_ {m}\right) \in \Delta \right\}
$$

where $ \Delta $ is a convex polytope. We are interested in determining conditions under which the polynomial family

$$
\Phi (\mathcal {P} (s)) = \left\{\varphi (a (s)): a (s) \in \mathcal {P} (s), \quad \varphi (z) \in \Phi (z) \right\}
$$

is stable?

The uncertain parameters in the polynomial family (6.24) are the vector p which varies in P and enters the coefficients nonlinearly, and the parameters $ \alpha_{i} $ which vary in $ \Delta $ and enter the coefficients linearly.

Theorem 6.4 Let $ \Lambda\neq\emptyset $ . Then the family $ \Phi(\mathcal{P}(s)) $ is stable if and only if $ \Phi(z) $ is $ \Lambda $ -stable.

Proof. The result follows from Theorem 6.2 and the representation

$$
\Phi \left(\mathcal {P} (s)\right) = \left\{\varphi \left(\mathcal {P} (s)\right): \varphi (z) \in \Phi (z) \right\}.
$$

By applying Theorem 6.3 to the above result we immediately have the following.

Theorem 6.5 The family $ \Phi(\mathcal{P}(s)) $ is stable if and only if $ \Phi(\mathcal{E}_{\mathcal{P}}(z)) $ is $ \Lambda $ -stable.

For each fixed polynomial a(s) in $ \mathcal{E}_{\mathcal{P}}(s) $ $ \Phi(a(s) $ is a polytopic family and therefore its stability can be found by testing its edges. This leads to the next result.

Theorem 6.6 The family of polynomials $ \Phi(\mathcal{P}(s)) $ is stable if and only if each two parameter family of polynomials in $ \mathcal{E}_{\Phi} \left( \mathcal{E}_{\mathcal{P}}(s) \right) $ is stable.

The set $ \mathcal{E}_{\Phi}\left(\mathcal{E}_{\mathcal{P}}(s)\right) $ consists of a finite number of two parameter families corresponding to pairs of edges of P and $ \Delta $ . Let

$$
(1 - \mu) a _ {k} (s) + \mu a _ {j} (s), \quad \mu \in [ 0. 1 ]
$$

correspond to an edge of P and let

$$
(1 - \nu) \varphi_ {u} (z) + \nu \varphi_ {v} (z), \quad \nu \in [ 0. 1 ]
$$

correspond to an edge of $ \Delta $ . Then the family

$$
(1 - \nu) \varphi_ {u} \left((1 - \mu) a _ {k} (s) + \mu a _ {j} (s)\right) + \nu \varphi_ {v} \left((1 - \mu) a _ {k} (s) + \mu a _ {j} (s)\right)
$$

where $(\mu ,\nu)\in [0,1]\times [0,1],$ is a typical element of $ \mathcal{E}_{\Phi}\left(\mathcal{E}_{\mathcal{P}}(s)\right). $

Theorem 6.6 is a generalization of the stability testing property of edges to this new class of polynomial families, containing both linear and nonlinear dependency on uncertain parameters. It shows that the problem is effectively reduced to a set of two-parameter multilinear problems, or double-edge problems.

## 6.4.1 Maximizing the Uncertainty Set

The above results can be used to determine maximal nondestabilizing perturbations. We will consider the situation when $ \mathcal{P}(s) $ or $ \Phi(z) $ are polytopes of fixed shape but

The characteristic polynomial of the family is written as

$$
\delta (s) = \delta_ {4} s ^ {4} + \delta_ {3} s ^ {3} + \delta_ {2} s ^ {2} + \delta_ {1} s + \delta_ {0}.
$$

The associated even and odd polynomials for Kharitonov's test are as follows:

$$
K _ {\min } ^ {\mathrm {e v e n}} (s) = x _ {0} + y _ {2} s ^ {2} + x _ {4} s ^ {4}, \quad K _ {\max } ^ {\mathrm {e v e n}} (s) = y _ {0} + x _ {2} s ^ {2} + y _ {4} s ^ {4},
$$

$$
K _ {\min } ^ {\mathrm {o d d}} (s) = x _ {1} s + y _ {3} s ^ {3}, \quad K _ {\max } ^ {\mathrm {o d d}} (s) = y _ {1} s + x _ {3} s ^ {3}.
$$

The Kharitonov polynomials are:

$$
\begin{array}{l} K ^ {1} (s) = x _ {0} + x _ {1} s + y _ {2} s ^ {2} + y _ {3} s ^ {3} + x _ {4} s ^ {4}, \quad K ^ {2} (s) = x _ {0} + y _ {1} s + y _ {2} s ^ {2} + x _ {3} s ^ {3} + x _ {4} s ^ {4}, \\ K ^ {3} (s) = y _ {0} + x _ {1} s + x _ {2} s ^ {2} + y _ {3} s ^ {3} + y _ {4} s ^ {4}, \quad K ^ {4} (s) = y _ {0} + y _ {1} s + x _ {2} s ^ {2} + x _ {3} s ^ {3} + y _ {4} s ^ {4}. \\ \end{array}
$$

The problem of checking the Hurwitz stability of the family therefore is reduced to that of checking the Hurwitz stability of these four polynomials. This in turn reduces to checking that the coefficients have the same sign (positive, say; otherwise multiply $ \delta(s) $ by -1) and that the following inequalities hold:

$$
K ^ {1} (s) \quad \mathrm {H u r w i t z}: y _ {2} y _ {3} > x _ {1} x _ {4}, \quad x _ {1} y _ {2} y _ {3} > x _ {1} ^ {2} x _ {4} + y _ {3} ^ {2} x _ {0},
$$

$$
K ^ {2} (s) \quad \mathrm {H u r w i t z}: y _ {2} x _ {3} > y _ {1} x _ {4}, \quad y _ {1} y _ {2} x _ {3} > y _ {1} ^ {2} x _ {4} + x _ {3} ^ {2} x _ {0},
$$

$$
K ^ {3} (s) \quad \mathrm {H u r w i t z}: x _ {2} y _ {3} > x _ {1} y _ {4}, \quad x _ {1} x _ {2} y _ {3} > x _ {1} ^ {2} y _ {4} + y _ {3} ^ {2} y _ {0},
$$

$$
K ^ {4} (s) \quad \mathrm {H u r w i t z}: x _ {2} x _ {3} > y _ {1} y _ {4}, \quad y _ {1} x _ {2} x _ {3} > y _ {1} ^ {2} y _ {4} + x _ {3} ^ {2} y _ {0}.
$$

<div align="center">

Example 5.3. Consider the control system shown in Figure 5.5.

</div>

<div style='text-align: center;'><img src='https://maas-watermark-prod-new.cn-wlcb.ufileos.com/ocr%2Fcrop%2F20260416202317df11c33e8d5e4fea%2Fcrop_1_1776342232099.png?UCloudPublicKey=TOKEN_6df395df-5d8c-4f69-90f8-a4fe46088958&Signature=8VdpjcTfMglypkzVRr1haheSEkg%3D&Expires=1776947032' alt='OCR图片'/></div>

<div align="center">

Figure 5.5. Feedback system with controller (Example 5.3)

</div>

The plant is described by the rational transfer function G(s) with numerator and denominator coefficients varying independently in prescribed intervals. We refer to such a family of transfer functions G(s) as an interval plant. In the present example we take

$$
\begin{array}{l} \mathbf {G} (s) := \left\{G (s) = \frac {n _ {2} s ^ {2} + n _ {1} s + n _ {0}}{s ^ {3} + d _ {2} s ^ {2} + d _ {1} s + d _ {0}}: \right. \\ \left. \begin{array}{l l} n _ {0} \in [ 1, 2. 5 ], n _ {1} \in [ 1, 6 ], & n _ {2} \in [ 1, 7 ], \\ d _ {2} \in [ - 1, 1 ], d _ {1} \in [ - 0. 5, 1. 5 ], & d _ {0} \in [ 1, 1. 5 ] \end{array} \right\}. \\ \end{array}
$$

variable size. We start with the case when $ \Phi $ is a single polynomial $ \varphi(z) $ , but $ \mathcal{P} $ is a polytope of variable size defined by

$$
\mathbf {P} (r) = \left\{\mathbf {p}: \mathbf {p} - \mathbf {p} ^ {0} \in r \mathcal {B} \right\}
$$

where $ \mathcal{B} $ is a convex polytope containing the origin. Let

$$
\mathcal {P} _ {r} (s) = \left\{a (s, \mathbf {p}): \mathbf {p} \in \mathbf {P} (r) \right\}
$$

and consider the Hurwitz stability of $ \varphi \left( \mathcal{P}_{r}(s)\right). $ We let $ a^{0}(s)\coloneqq a(s,\mathbf{p}^{0}) $ and assume that $ \varphi \left( a^{0}(s)\right) $ is stable. Our objective is to find the smallest positive $ r_{0} $ such that $ \varphi \left( \mathcal{P}_{r_{0}}(s)\right) $ is not stable. This $ r_{0} $ determines the limit on how much we may enlarge the polytope $ \mathbf{P}(r) $ without losing stability.

Theorem 6.3 can be applied to determine $ r_{0} $ . A typical edge of the family $ \varphi \left( \mathcal{E}_{\mathcal{P}_{r}}(s) \right) $ is of the form

$$
\varphi \left(a ^ {0} (s) + r (1 - \mu) a ^ {k} (s) + r \mu a ^ {j} (s)\right), \quad \mu \in [ 0, 1 ].
$$

Denote by $ r_{kj} $ the smallest positive value of $ r $ such that the family (6.28) is not stable. For each such element of the set $ \varphi \left( \mathcal{E}_{\mathcal{P}_r}(s) \right) $ we can find a corresponding $ r_{kj} $ Let

$$
r _ {0} = \min \left\{r _ {k j} \right\}
$$

where the minimum is taken over all elements of $ \varphi \left( \mathcal{E}_{P_{r}}(s) \right). $

Theorem 6.7 Let the polynomial $ \varphi \left(a^{0}(s)\right) $ be stable. Then $ \varphi \left(\mathcal{P}_{r}(s)\right) $ is stable if and only if $ r<r_{0}. $

This idea can also be applied to the case when $ \varphi(z) $ is not fixed but lies in $ \Phi(z). $ The problem is now to determine the smallest r such that the family $ \Phi(\mathcal{P}_{r}(s)) $ is unstable. We assume that the family $ \Phi\left(a^{0}(s)\right) $ is stable. From Theorem 6.6 we see that we have to check the stability of elements of the set $ \mathcal{E}_{\Phi}\left(\mathcal{E}_{\mathcal{P}_{r}}(s)\right) $ which consists of polynomials of the type

$$
\begin{array}{l} (1 - \nu) \varphi_ {l} \left(a ^ {0} (s) + r (1 - \nu) a ^ {k} (s) + r \mu a ^ {j} (s)\right) \\ + \nu \varphi_ {m} \left(a ^ {0} (s) + r (1 - \mu) a ^ {k} (s) + r \mu a ^ {j} (s)\right) \\ \end{array}
$$

where $ \mu, \nu)\in[0,1]\times[0,1] $ . Denote by $ r_{kj}^{lm} $ the smallest value of r such that (6.29) is not stable. This may be defined for every element of $ \mathcal{E}_{\Phi}\left(\mathcal{E}_{\mathcal{P}_{r}}(s)\right). $

Theorem 6.8 Let the family $ \Phi \left(a^{0}(s)\right) $ be stable. Then $ \Phi(\mathcal{P}_{r}(s)) $ is stable if and only if

$$
r < \min \left\{r _ {k j} ^ {l m} \right\}
$$

where the minimum is taken over all families from $ \mathcal{E}_{\Phi}\left(\mathcal{E}_{\mathcal{P}_r}(s)\right). $

For each value of r the two uncertain parameters $ (\mu,\nu) $ in (6.29) appear multilinearly. Such two-parameter multilinear problems can be solved analytically and are also effectively dealt with using the Mapping Theorem in Chapter 11.

## 6.5 EXERCISES

6. 1 Using the Edge Theorem, check the robust Hurwitz stability of the following family of polynomials. Also show the root cluster of the family.

$$
\delta (s) := s ^ {3} + (a + 3 b) s ^ {2} + c s + d
$$

where a $ \in $ [1,2], b $ \in $ [0,3], c $ \in $ [10,15] and d $ \in $ [9,14].

6. 2 Consider the plant $ G(s) $ and the controller $ C(s) $

$$
G (s) := \frac {s + 1}{s ^ {2} - s - 1} \quad C (s) := \frac {a s + b}{s + c}.
$$

First, choose the controller parameter $ \{a^{0}, b^{0}, c^{0}\} $ so that the closed loop system has its characteristic roots at

$$
- 1 \pm j 1 \mathrm {a n d} - 1 0.
$$

Now for

$$
a \in \left[ a ^ {0} - \frac {\epsilon}{2}, a ^ {0} + \frac {\epsilon}{2} \right], \quad b \in \left[ b ^ {0} - \frac {\epsilon}{2}, b ^ {0} + \frac {\epsilon}{2} \right], \quad c \in \left[ c ^ {0} - \frac {\epsilon}{2}, c ^ {0} + \frac {\epsilon}{2} \right]
$$

find the maximum value $ \epsilon_{\mathrm{m a x}} $ of $ \epsilon $ that robustly maintains closed loop stability. Find the root set of the system when the parameters range over a box with sides $ \frac{\epsilon_{\mathrm{m a x}}}{2}. $

6. 3 Repeat Exercise 6.2 with the additional requirement that the dominant pair of roots remain inside circles of radii 0.5 centered at $ - 1\pm j1. $

6. 4 Consider the discrete time plant $ G ( z ) $ and the controller $ C ( z ) $

$$
G (z) := \frac {z - 1}{z ^ {2} + 2 z + 3}, \quad C (z) := \frac {a z + b}{z + c}
$$

Choose the controller parameter $ \{a^{0}, b^{0}, c^{0}\} $ so that deadbeat control is achieved, namely all the closed loop poles are placed at $ z=0 $ . Use the Edge Theorem, find the maximum range of the controller parameters so that the closed loop poles remain inside the circle of radius 0.5 centered at the origin. Assume that the controller parameters are bounded by the same amount, i.e.,

$$
a \in [ a ^ {0} - \epsilon , a ^ {0} + \epsilon ], \quad b \in [ b ^ {0} - \epsilon , b ^ {0} + \epsilon ], \quad c \in [ c ^ {0} - \epsilon , c ^ {0} + \epsilon ].
$$

Find the root set of the system for the parameters {a,b,c} varying in a box

$$
a \in \left[ a ^ {0} - \frac {\epsilon}{2}, a ^ {0} + \frac {\epsilon}{2} \right], \quad b \in \left[ b ^ {0} - \frac {\epsilon}{2}, b ^ {0} + \frac {\epsilon}{2} \right], \quad c \in \left[ c ^ {0} - \frac {\epsilon}{2}, c ^ {0} + \frac {\epsilon}{2} \right].
$$

## 6.5 Consider the polynomials

$$
s ^ {2} + a _ {1} s + a _ {0} \quad \mathrm {a n d} \quad s ^ {2} + b _ {1} s + b _ {0}
$$

where

$$
\left[ a _ {1} ^ {0}, a _ {0} ^ {0} \right] = [ 2, 2 ], \quad \left[ b _ {1} ^ {0}, b _ {0} ^ {0} \right] = [ 4, 8 ].
$$

Now find the maximum value $ \epsilon_{\mathrm{max}} $ of $ \epsilon $ so that the families remain coprime as $ [a_{1}, a_{0}]$ varies over the box $ [a_{1}^{0}-\epsilon,a_{1}^{0}+\epsilon]\times[a_{0}^{0}-\epsilon,a_{0}^{0}+\epsilon] $ and b varies independently over the box $ [b_{1}^{0}-\epsilon,b_{1}^{0}+\epsilon]\times[b_{0}^{0}-\epsilon,b_{0}^{0}+\epsilon]. $

## 6.6 Repeat Exercise 6.5, this time verifying coprimeness over the right half plane.

6. 7 Consider a unity feedback system with the plant G(s) and C(s) given as

$$
G (s) = \frac {s + b _ {0}}{s ^ {2} + a _ {1} s + a _ {0}} \quad \mathrm {a n d} \quad C (s) = \frac {s + 1}{s + 2}.
$$

Assume that the plant parameters vary independently as:

$$
a _ {0} \in [ 2, 4 ], \quad a _ {1} \in [ 2, 4 ], \quad b _ {0} \in [ 1, 3 ].
$$

Determine the root space of the family of closed loop polynomials using the Edge Theorem.

## 6.8 Consider the two polynomials

$$
A (s) = a _ {2} s ^ {2} + a _ {1} s + a _ {0}
$$

$$
B (s) = b _ {3} s ^ {3} + b _ {2} s ^ {2} + b _ {1} s + b _ {0}
$$

where the nominal values of the parameters are

$$
a _ {0} ^ {0} = 2, a _ {1} = 2, a _ {2} = 1, b _ {0} = 2. 5, b _ {1} = 7, b _ {2} = 4. 5, b _ {3} = 1.
$$

Suppose the parameter perturbations are:

$$
a _ {i} \in [ a _ {i} ^ {0} - \epsilon , a _ {i} ^ {0} + \epsilon ], \qquad i = 0, 1, 2
$$

$$
b _ {j} \in \left[ b _ {j} ^ {0} - \epsilon , b _ {j} ^ {0} + \epsilon \right], \quad j = 0, 1, 2, 3.
$$

Find the maximum value of $ \epsilon $ for which the two polynomial sets remain coprime. Answer: $ \epsilon_{\mathrm{max}}=0.25 $

## 6.9 Let

$$
A (s) = a _ {3} s _ {3} ^ {3} + a _ {2} s ^ {2} + a _ {1} s + a _ {0}
$$

$$
B (s) = b _ {3} s ^ {3} + b _ {2} s ^ {2} + b _ {1} s + b _ {0}
$$

and

$$
\left[ a _ {0} ^ {0}, a _ {1} ^ {0}, a _ {2} ^ {0}, a _ {3} ^ {0}, b _ {0} ^ {0}, b _ {1} ^ {0}, b _ {2} ^ {0}, b _ {3} ^ {0} \right] = [ 1 0 0, 1 0 0, 1 0, 3, 1, 3, 3, 3 ].
$$

Assume that all the coefficients of the above two polynomials are allowed to perturb independently. Find the maximum value of $ \epsilon $ so that the two polynomial families remain coprime when

$$
a _ {i} \in \left[ a _ {i} ^ {0} - \epsilon , a _ {i} ^ {0} + \epsilon \right], \quad i = 0, 1, 2, 3
$$

$$
b _ {j} \in \left[ b _ {j} ^ {0} - \epsilon , b _ {j} ^ {0} + \epsilon \right], \quad j = 0, 1, 2, 3.
$$

Answer: $ \epsilon_{\mathrm{m a x}}=0. 5 2 5 $

6. 10 Repeat Exercise 6.9 with the requirement that the families remain coprime over the right half of the complex plane.

6. 11 Consider the polytopic family $ \mathcal{P} (s) $ consisting of polynomials a(s):

$$
a (s) = s ^ {2} + \left(p _ {1} + p _ {2}\right) s + p _ {1}: \quad p _ {1} \in [ 2, 4 ], p _ {2} \in [ 3, 7 ].
$$

Let

$$
\varphi (z) = z ^ {2} + \alpha_ {1} z + \alpha_ {0}
$$

with $ \alpha_{1}=3 $ $ \alpha_{0}=4 $ . Determine the Hurwitz stability of the family $ \varphi(\mathcal{P}(s)) $

6. 12 In Exercise 6.11 suppose that $ \varphi(z) $ belongs to the family $ \Phi(z) $ defined as

$$
\Phi (z) = \left\{\varphi (z) = z ^ {2} + \alpha_ {1} z + \alpha_ {0}: \alpha_ {1} \in [ 2, 4 ], \alpha_ {0} \in [ 3, 5 ] \right\}.
$$

Determine the Hurwitz stability of the family $ \Phi(\mathcal{P}(s)) $

6. 13 Consider the polynomial $ s^{2}+a_{1} s+a_{0} $ and let the coefficients $ \left(a_{1}, a_{0}\right) $ vary in the convex hull of the points

$$
(0, 0), \quad (0, R), \quad \left(R ^ {2}, 0\right), \quad \left(R ^ {2}, 2 R\right).
$$

Show that the root space of this set is the intersection with the left half plane of the circle of radius R centered at the origin. Describe also the root space of the convex hull of the points

$$
(0, 0), \quad (0, 2 R), \quad \left(R ^ {2}, 0\right), \quad \left(R ^ {2}, 2 R\right).
$$

## 6.6 NOTES AND REFERENCES

The Edge Theorem is due to Bartlett, Hollot and Lin [21]. We note that the weaker and more obvious result in Corollary 6.1, that is, the stability detecting property of the exposed edges, is often referred to, loosely, in the literature as

the Edge Theorem. In fact as we have seen in Chapter 4, Corollary 6.1 applies to complex polytopic polynomial and quasipolynomial families. However, the root space boundary generating property does not necessarily hold in these more general situations. The extensions of the stability testing property of edges to polynomial functions of polytopes, reported in Section 6.4 are due to Kharitonov [146].
