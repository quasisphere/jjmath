# The Riemann mapping theorem

Let $U\subsetneq\mathbb C$ be a nonempty simply connected open set. The Riemann mapping theorem says that $U$ is biholomorphic to the unit disk $\mathbb D$. Here “proper” means only $U\ne\mathbb C$; the domain need not be bounded or relatively compact.

The proof uses the simply connected uniformization theorem, which gives three possible biholomorphic models for $U$: the Riemann sphere, the complex plane, and the unit disk.

@include{lean:JJMath.Uniformization.simplyConnected_riemannSurface_uniformization}

It remains to exclude the first two alternatives. Properness excludes the sphere by a topological argument, while a square-root construction and Liouville's theorem exclude the plane.

## The square-root coordinate

Choose a point $a\in\mathbb C\setminus U$. After translating the domain, assume $a=0$. Since $U$ is simply connected and avoids zero, the squaring cover $z\mapsto z^2$ admits a continuous lift over the identity map on $U$. This gives a branch $f$ satisfying

$$
f(z)^2=z.
$$

The identity makes $f$ injective. It also lets the local inverse theorem promote the initially continuous branch to a holomorphic one: near $z\in U$, the squaring map is locally invertible at $f(z)$ because $f(z)\ne0$, and

$$
f'(z)=\frac{1}{2f(z)}\ne0.
$$

The image $f(U)$ is not dense. Fix $x\in U$. If points of $f(U)$ approached $-f(x)$, openness of $f(U)$ around $f(x)$ and symmetry under negation would force values $f(u)=-f(v)$. Squaring gives $u=v$, and injectivity then gives $f(u)=f(v)$, so $f(u)=0$, contradicting $0\notin U$.

@include{lean:JJMath.Uniformization.exists_injective_planeMap_not_dense_image_of_proper_simplyConnected}

Because $f(U)$ is not dense, some closed disk $\overline{B(c,\varepsilon)}$ with $\varepsilon>0$ misses it. Define

$$
g(z)=\frac{\varepsilon}{f(z)-c}.
$$

Then $g$ is holomorphic and injective on $U$, and the separation from the omitted disk gives $|g(z)|<1$. Thus $U$ carries a bounded nonconstant holomorphic function, in fact an injective holomorphic map into $\mathbb D$.

@include{lean:JJMath.Uniformization.properSimplyConnectedPlaneDomain_has_boundedNonconstantHolomorphicFunction}

## Excluding the sphere and plane

The domain $U$ cannot be compact. If it were, its inclusion into the Hausdorff plane would have compact, hence closed, image. Since $U$ is also open and nonempty, connectedness of $\mathbb C$ would force $U=\mathbb C$.

@include{lean:JJMath.Uniformization.properSimplyConnectedPlaneDomain_not_compactSpace}

Consequently $U$ cannot be biholomorphic to the compact Riemann sphere. If it were biholomorphic to $\mathbb C$, the bounded nonconstant holomorphic function constructed above could be pulled back to a bounded nonconstant entire function. This contradicts Liouville's theorem.

@include{lean:JJMath.Uniformization.complexPlane_has_no_bounded_nonconstant_holomorphicFunction}

The sphere and plane alternatives in simply connected uniformization are therefore impossible. The remaining alternative identifies $U$ biholomorphically with the unit disk.

@include{lean:JJMath.Uniformization.riemannMappingTheorem}
